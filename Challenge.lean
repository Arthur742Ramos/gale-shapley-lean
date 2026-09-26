import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

universe u v

namespace GS.Palomar

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty W]

open Finset

/-- Strict preference lists for the two sides of a matching market. -/
structure ProfileAux (M W : Type*) where
  /-- `prefM m w₁ w₂` means that man `m` strictly prefers `w₁` to `w₂`. -/
  prefM : M → W → W → Prop
  /-- `prefW w m₁ m₂` means that woman `w` strictly prefers `m₁` to `m₂`. -/
  prefW : W → M → M → Prop
  decPrefM : ∀ m w₁ w₂, Decidable (prefM m w₁ w₂)
  decPrefW : ∀ w m₁ m₂, Decidable (prefW w m₁ m₂)
  irreflM : ∀ m w, ¬ prefM m w w
  transM : ∀ m w₁ w₂ w₃, prefM m w₁ w₂ → prefM m w₂ w₃ → prefM m w₁ w₃
  totalM : ∀ m w₁ w₂, w₁ ≠ w₂ → prefM m w₁ w₂ ∨ prefM m w₂ w₁
  irreflW : ∀ w m, ¬ prefW w m m
  transW : ∀ w m₁ m₂ m₃, prefW w m₁ m₂ → prefW w m₂ m₃ → prefW w m₁ m₃
  totalW : ∀ w m₁ m₂, m₁ ≠ m₂ → prefW w m₁ m₂ ∨ prefW w m₂ m₁

/-- A two-sided profile, reusing the project structure with decidable, strict
preferences for each participant. -/
def Profile (M W : Type*) : Type _ := ProfileAux M W

/-- An unmatched option is treated as worse than every acceptable partner. -/
def prefersM (p : Profile M W) (m : M) (w : W) (cur : Option W) : Prop :=
  match cur with
  | none => True
  | some w' => p.prefM m w w'

/-- An unmatched option is treated as worse than every acceptable partner. -/
def prefersW (p : Profile M W) (w : W) (m : M) (cur : Option M) : Prop :=
  match cur with
  | none => True
  | some m' => p.prefW w m m'

/-- A matching represented by mutually consistent optional partner maps. -/
structure MatchingAux (M W : Type*) where
  muM : M → Option W
  muW : W → Option M
  inv1 : ∀ m w, muM m = some w → muW w = some m
  inv2 : ∀ m w, muW w = some m → muM m = some w

/-- A matching is represented by mutually inverse optional partner maps. -/
def Matching (M W : Type*) : Type _ := MatchingAux M W

/-- A pair blocks when both participants strictly prefer each other to their current partners. -/
def IsBlockingPair (p : Profile M W) (mu : Matching M W) (m : M) (w : W) : Prop :=
  prefersM p m w (mu.muM m) ∧ prefersW p w m (mu.muW w)

/-- Preference lists are complete, and `prefersM`/`prefersW` treat `none` as worst.
The stability definition uses that convention directly, so the model carries no
separate acceptability or individual-rationality field. -/
def IsStable (p : Profile M W) (mu : Matching M W) : Prop :=
  ∀ m w, ¬ IsBlockingPair p mu m w

/-- A pair is achievable when some stable matching assigns that woman to the man. -/
def Achievable (p : Profile M W) (m : M) (w : W) : Prop :=
  ∃ μ : Matching M W, IsStable p μ ∧ μ.muM m = some w

/-- A deferred-acceptance configuration: each woman holds at most one proposer, and
`proposed` records all pairs that have already been proposed. -/
structure DAStateAux (M W : Type*) where
  held : W → Option M
  proposed : Finset (M × W)

def DAState (M W : Type*) : Type _ := DAStateAux M W

/-- Unheld men who still have at least one woman to whom they have not proposed. -/
def activeMen (s : DAState M W) : Finset M := by
  classical
  exact Finset.univ.filter (fun m =>
    (∀ w, s.held w ≠ some m) ∧ ∃ w, (m, w) ∉ s.proposed)

/-- The women to whom `m` has not yet proposed. -/
def unproposedWomen (s : DAState M W) (m : M) : Finset W := by
  classical
  exact Finset.univ.filter (fun w => (m, w) ∉ s.proposed)

theorem mem_activeMen_iff (s : DAState M W) (m : M) :
    m ∈ activeMen s ↔ (∀ w, s.held w ≠ some m) ∧ ∃ w, (m, w) ∉ s.proposed := by
  classical
  simp [activeMen]

/-- Every nonempty finite subset has a member preferred to every distinct member. -/
theorem exists_prefM_maximal (p : Profile M W) (m : M) (S : Finset W)
    (hS : S.Nonempty) :
    ∃ w ∈ S, ∀ w' ∈ S, w' ≠ w → p.prefM m w w' := by
  classical
  revert hS
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      intro _
      by_cases hSn : S.Nonempty
      · obtain ⟨b, hbS, hbBest⟩ := ih hSn
        have hab : a ≠ b := by
          intro h
          subst b
          exact ha hbS
        rcases p.totalM m a b hab with habPref | hbaPref
        · refine ⟨a, Finset.mem_insert_self a S, ?_⟩
          intro x hx hxne
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · exact False.elim (hxne rfl)
          · by_cases hxb : x = b
            · subst x
              exact habPref
            · exact p.transM m a b x habPref (hbBest x hxS hxb)
        · refine ⟨b, Finset.mem_insert_of_mem hbS, ?_⟩
          intro x hx hxne
          rcases Finset.mem_insert.mp hx with rfl | hxS
          · exact hbaPref
          · exact hbBest x hxS hxne
      · refine ⟨a, Finset.mem_insert_self a S, ?_⟩
        intro x hx hxne
        rcases Finset.mem_insert.mp hx with rfl | hxS
        · exact False.elim (hxne rfl)
        · exact (hSn ⟨x, hxS⟩).elim

/-- The highest-ranked woman to whom `m` has not yet proposed, if any remain. -/
noncomputable def nextWoman (p : Profile M W) (s : DAState M W) (m : M) : Option W :=
  if h : (unproposedWomen s m).Nonempty then
    some (Classical.choose (exists_prefM_maximal p m (unproposedWomen s m) h))
  else none

theorem nextWoman_spec (p : Profile M W) (s : DAState M W) (m : M)
    (h : (unproposedWomen s m).Nonempty) :
    ∃ w, nextWoman p s m = some w ∧ w ∈ unproposedWomen s m := by
  classical
  refine ⟨Classical.choose (exists_prefM_maximal p m (unproposedWomen s m) h), ?_, ?_⟩
  · simp [nextWoman, h]
  · exact (Classical.choose_spec
      (exists_prefM_maximal p m (unproposedWomen s m) h)).1

/-- One deferred-acceptance proposal step. The active man and his next proposal are
chosen from finite sets; the woman keeps the preferred of her current holder and the
new proposer. -/
noncomputable def DA_step (p : Profile M W) (s : DAState M W) : Option (DAState M W) := by
  classical
  exact if hActive : (activeMen s).Nonempty then
    let m := Classical.choose hActive
    let hm : m ∈ activeMen s := Classical.choose_spec hActive
    let hmAvail : ∃ w, (m, w) ∉ s.proposed := by
      exact (mem_activeMen_iff s m).mp hm |>.2
    let hCandidates : (unproposedWomen s m).Nonempty := by
      let w := Classical.choose hmAvail
      have hw : (m, w) ∉ s.proposed := Classical.choose_spec hmAvail
      exact ⟨w, by simpa [unproposedWomen] using hw⟩
    let hNext := nextWoman_spec p s m hCandidates
    let w := Classical.choose hNext
    let hNextValue : nextWoman p s m = some w := (Classical.choose_spec hNext).1
    let hAvailable : w ∈ unproposedWomen s m := (Classical.choose_spec hNext).2
    let current := (s.held w).getD m
    letI : Decidable (p.prefW w m current) := p.decPrefW w m current
    let kept := if p.prefW w m current then m else current
    some {
      held := fun w' => if w' = w then some kept else s.held w'
      proposed := insert (m, w) s.proposed
    }
  else none

/-- The initial deferred-acceptance configuration has no holders and no proposals. -/
def initialState : DAState M W where
  held := fun _ => none
  proposed := ∅

/-- A state is quiescent when no unheld man has an unproposed woman left. -/
def IsQuiescent (s : DAState M W) : Prop := activeMen s = ∅


/-- The number of proposals that remain possible. -/
def terminationMeasure (s : DAState M W) : Nat :=
  (Finset.univ : Finset (M × W)).card - s.proposed.card

/-- A successful step records its selected man and next woman. -/
theorem DA_step_proposal_info (p : Profile M W) (s s₂ : DAState M W)
    (h : DA_step p s = some s₂) :
    ∃ m w, nextWoman p s m = some w ∧ w ∈ unproposedWomen s m ∧
      (m, w) ∉ s.proposed ∧ s₂.proposed = insert (m, w) s.proposed := by
  classical
  unfold DA_step at h
  split at h
  · simp only [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    let m := Classical.choose ‹(activeMen s).Nonempty›
    have hm : m ∈ activeMen s := Classical.choose_spec ‹(activeMen s).Nonempty›
    have hmAvail : ∃ w, (m, w) ∉ s.proposed := by
      exact (mem_activeMen_iff s m).mp hm |>.2
    have hCandidates : (unproposedWomen s m).Nonempty := by
      rcases hmAvail with ⟨w, hw⟩
      exact ⟨w, by simpa [unproposedWomen] using hw⟩
    let hNext := nextWoman_spec p s m hCandidates
    let w := Classical.choose hNext
    have hNextValue : nextWoman p s m = some w := (Classical.choose_spec hNext).1
    have hAvailable : w ∈ unproposedWomen s m := (Classical.choose_spec hNext).2
    refine ⟨m, w, hNextValue, hAvailable, ?_, rfl⟩
    simpa [unproposedWomen] using hAvailable
  · simp at h

/-- A successful proposal step inserts exactly one fresh pair. -/
theorem DA_step_proposed_shape (p : Profile M W) (s s₂ : DAState M W)
    (h : DA_step p s = some s₂) :
    ∃ m w, (m, w) ∉ s.proposed ∧ s₂.proposed = insert (m, w) s.proposed := by
  obtain ⟨m, w, _, _, hfresh, hshape⟩ := DA_step_proposal_info p s s₂ h
  exact ⟨m, w, hfresh, hshape⟩

/-- A step changes only its selected woman's holder, who either accepts or trades up. -/
theorem DA_step_held_info (p : Profile M W) (s s₂ : DAState M W)
    (h : DA_step p s = some s₂) :
    ∃ m w kept, s₂.held w = some kept ∧
      (∀ w', w' ≠ w → s₂.held w' = s.held w') ∧
      (match s.held w with
       | none => kept = m
       | some old => (kept = m ∧ p.prefW w m old) ∨
           (kept = old ∧ ¬ p.prefW w m old)) ∧
      (m, w) ∉ s.proposed ∧ s₂.proposed = insert (m, w) s.proposed ∧
      (∀ w', s.held w' ≠ some m) ∧ nextWoman p s m = some w := by
  classical
  unfold DA_step at h
  split at h
  · simp only [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    let m := Classical.choose ‹(activeMen s).Nonempty›
    have hm : m ∈ activeMen s := Classical.choose_spec ‹(activeMen s).Nonempty›
    have hmInfo := (mem_activeMen_iff s m).mp hm
    have hmAvail : ∃ w, (m, w) ∉ s.proposed := by
      exact (mem_activeMen_iff s m).mp hm |>.2
    have hCandidates : (unproposedWomen s m).Nonempty := by
      rcases hmAvail with ⟨w, hw⟩
      exact ⟨w, by simpa [unproposedWomen] using hw⟩
    let hNext := nextWoman_spec p s m hCandidates
    let w := Classical.choose hNext
    have hNextValue : nextWoman p s m = some w := (Classical.choose_spec hNext).1
    have hAvailable : w ∈ unproposedWomen s m := (Classical.choose_spec hNext).2
    let current := (s.held w).getD m
    let decision : Decidable (p.prefW w m current) := p.decPrefW w m current
    let kept := @ite M (p.prefW w m current) decision m current
    refine ⟨m, w, kept, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (if w = w then some kept else s.held w) = some kept
      simp
    · intro w' hw'
      change (if w' = w then some kept else s.held w') = s.held w'
      simp [hw']
    · cases hcur : s.held w with
      | none => simp [current, kept, hcur]
      | some old =>
          by_cases hp : p.prefW w m old
          · left
            simp [current, kept, hcur, hp]
          · right
            simp [current, kept, hcur, hp]
    · simpa [unproposedWomen] using hAvailable
    · rfl
    · exact hmInfo.1
    · exact hNextValue
  · cases h

/-- Each successful step increases the proposal count by exactly one. -/
theorem proposed_grows (p : Profile M W) (s s₂ : DAState M W)
    (h : DA_step p s = some s₂) : s₂.proposed.card = s.proposed.card + 1 := by
  obtain ⟨m, w, hfresh, hshape⟩ := DA_step_proposed_shape p s s₂ h
  rw [hshape, card_insert_of_notMem hfresh]

/-- The remaining-pairs measure strictly decreases at every successful step. -/
theorem terminationMeasure_decreases (p : Profile M W) (s s₂ : DAState M W)
    (h : DA_step p s = some s₂) : terminationMeasure s₂ < terminationMeasure s := by
  have hcard := proposed_grows p s s₂ h
  have hbound : s₂.proposed.card ≤ (Finset.univ : Finset (M × W)).card :=
    card_le_card (subset_univ _)
  simp only [terminationMeasure]
  omega

/-- Reachability by zero or more successful DA steps. -/
inductive DAReaches (p : Profile M W) : DAState M W → DAState M W → Prop
  | refl (s) : DAReaches p s s
  | oneStep {s s₂} : DA_step p s = some s₂ → DAReaches p s s₂
  | trans {s t u} : DAReaches p s t → DAReaches p t u → DAReaches p s u

/-- Run deferred acceptance until no man has any unproposed woman left. -/
noncomputable def run (p : Profile M W) (s : DAState M W) : DAState M W :=
  match _h : DA_step p s with
  | none => s
  | some s₂ => run p s₂
termination_by terminationMeasure s
decreasing_by
  exact terminationMeasure_decreases p s s₂ _h

theorem run_reachable (p : Profile M W) (s : DAState M W) :
    DAReaches p s (run p s) := by
  unfold run
  split
  · exact DAReaches.refl _
  · rename_i s₂ hstep
    exact DAReaches.trans (DAReaches.oneStep hstep) (run_reachable p s₂)
termination_by terminationMeasure s
decreasing_by
  exact terminationMeasure_decreases p s _ ‹DA_step p s = some _›

/-- No man is held by two different women in the state. -/
def HeldUnique (s : DAState M W) : Prop :=
  ∀ w₁ w₂ m, s.held w₁ = some m → s.held w₂ = some m → w₁ = w₂

theorem initialState_heldUnique : HeldUnique (initialState : DAState M W) := by
  intro w₁ w₂ m h₁ _
  simp [initialState] at h₁

theorem DA_step_selected_holder_unique (p : Profile M W) (s s₂ : DAState M W)
    (hstep : DA_step p s = some s₂) (hunique : HeldUnique s) :
    ∃ wNew : W,
      (∀ w' m, w' ≠ wNew → s₂.held wNew = some m →
        s₂.held w' = some m → False) ∧
      (∀ w', w' ≠ wNew → s₂.held w' = s.held w') := by
  obtain ⟨mNew, wNew, kept, hheld, hsame, hchoice, _, _, hfree, _⟩ :=
    DA_step_held_info p s s₂ hstep
  refine ⟨wNew, ?_, hsame⟩
  intro w' m hwneq hselected hother
  have hmKept : kept = m := Option.some.inj (hheld.symm.trans hselected)
  have hotherOld : s.held w' = some m := by
    simpa [hsame w' hwneq] using hother
  cases hcur : s.held wNew with
  | none =>
      have hk : kept = mNew := by simpa [hcur] using hchoice
      have hmNew : m = mNew := hmKept.symm.trans hk
      have hbad : s.held w' = some mNew := by simpa [hmNew] using hotherOld
      exact hfree w' hbad
  | some old =>
      have hchoice' := hchoice
      rw [hcur] at hchoice'
      rcases hchoice' with ⟨hk, _⟩ | ⟨hk, _⟩
      · have hmNew : m = mNew := hmKept.symm.trans hk
        have hbad : s.held w' = some mNew := by simpa [hmNew] using hotherOld
        exact hfree w' hbad
      · have hmOld : m = old := hmKept.symm.trans hk
        have hotherOld' : s.held w' = some old := by simpa [hmOld] using hotherOld
        have hwEq := hunique wNew w' old hcur hotherOld'
        exact hwneq hwEq.symm

theorem DA_step_preserves_HeldUnique (p : Profile M W) (s s₂ : DAState M W)
    (hstep : DA_step p s = some s₂) (hunique : HeldUnique s) : HeldUnique s₂ := by
  obtain ⟨wNew, hselectedUnique, hsame⟩ :=
    DA_step_selected_holder_unique p s s₂ hstep hunique
  intro w₁ w₂ m h₁ h₂
  by_cases hw₁ : w₁ = wNew
  · subst w₁
    have hw₂ : w₂ = wNew := by
      by_contra hne
      exact hselectedUnique w₂ m hne h₁ h₂
    exact hw₂.symm
  · by_cases hw₂ : w₂ = wNew
    · subst w₂
      have hw₁' : w₁ = wNew := by
        by_contra hne
        exact hselectedUnique w₁ m hne h₂ h₁
      exact hw₁'
    · have h₁old : s.held w₁ = some m := by simpa [hsame w₁ hw₁] using h₁
      have h₂old : s.held w₂ = some m := by simpa [hsame w₂ hw₂] using h₂
      exact hunique w₁ w₂ m h₁old h₂old

theorem HeldUnique_preserved (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) (hunique : HeldUnique s) : HeldUnique t := by
  induction hreach with
  | refl _ => exact hunique
  | oneStep hstep => exact DA_step_preserves_HeldUnique p _ _ hstep hunique
  | trans _ _ ih₁₂ ih₂₃ => exact ih₂₃ (ih₁₂ hunique)

theorem HeldUnique_of_reaches (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s) : HeldUnique s := by
  exact HeldUnique_preserved p hreach initialState_heldUnique

/-- Turn the terminal holders into the mutually inverse partner maps of a
matching. The reachability proof supplies the invariant that no man is held by
two women. -/
noncomputable def terminalMatching (p : Profile M W) (s : DAState M W)
    (hreach : DAReaches p initialState s) : Matching M W := by
  classical
  let hUnique := HeldUnique_of_reaches p hreach
  refine
    { muM := fun m =>
        if h : ∃ w, s.held w = some m then some (Classical.choose h) else none
      muW := s.held
      inv1 := ?_
      inv2 := ?_ }
  · intro m w hm
    change (if h : ∃ v, s.held v = some m then
      some (Classical.choose h) else none) = some w at hm
    by_cases h : ∃ v, s.held v = some m
    · simp only [dite_eq_left h, Option.some.injEq] at hm
      subst w
      exact Classical.choose_spec h
    · simp [dite_eq_right h] at hm
  · intro m w hw
    let h : ∃ v, s.held v = some m := ⟨w, hw⟩
    change (if h' : ∃ v, s.held v = some m then
      some (Classical.choose h') else none) = some w
    rw [dite_eq_left h]
    have huniq := hUnique (Classical.choose h) w m (Classical.choose_spec h) hw
    simpa using huniq

/-- The men-proposing deferred-acceptance procedure has a stable outcome. -/
theorem galeShapley (p : Profile M W) :
    ∃ μ : Matching M W, IsStable p μ := by
  sorry

/-- The run from the initial state terminates quiescently, and its terminal
matching is stable. -/
theorem daStable (p : Profile M W) :
    let s := run p initialState
    IsQuiescent s ∧
      IsStable p
        (terminalMatching p s (run_reachable p initialState)) := by
  sorry

/-- Whenever a man is matched to w0 by the deferred-acceptance outcome, every stable-achievable partner is weakly below w0 in his preferences. -/
theorem daMenOptimal (p : Profile M W) (m : M) {w₀ : W}
    (hterminal :
      (terminalMatching p (run p initialState)
        (run_reachable p initialState)).muM m = some w₀) :
    ∀ w : W, Achievable p m w → p.prefM m w₀ w ∨ w₀ = w := by
  sorry

end

end GS.Palomar
