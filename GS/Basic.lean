import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic

universe u v

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W]

/-- Strict preference lists for the two sides of a matching market. -/
structure Profile (M W : Type*) where
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
structure Matching (M W : Type*) where
  muM : M → Option W
  muW : W → Option M
  inv1 : ∀ m w, muM m = some w → muW w = some m
  inv2 : ∀ m w, muW w = some m → muM m = some w

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem muM_eq_some_iff_muW (mu : Matching M W) (m : M) (w : W) :
    mu.muM m = some w ↔ mu.muW w = some m :=
  ⟨mu.inv1 m w, mu.inv2 m w⟩

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem muM_none_iff (mu : Matching M W) (m : M) :
    mu.muM m = none ↔ ∀ w, mu.muW w ≠ some m := by
  constructor
  · intro hm w hw
    have hmw := mu.inv2 m w hw
    rw [hm] at hmw
    cases hmw
  · intro h
    cases hm : mu.muM m with
    | none => rfl
    | some w => exact False.elim (h w ((muM_eq_some_iff_muW mu m w).mp hm))

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem muW_none_iff (mu : Matching M W) (w : W) :
    mu.muW w = none ↔ ∀ m, mu.muM m ≠ some w := by
  constructor
  · intro hw m hm
    have hmw := mu.inv1 m w hm
    rw [hw] at hmw
    cases hmw
  · intro h
    cases hw : mu.muW w with
    | none => rfl
    | some m => exact False.elim (h m ((muM_eq_some_iff_muW mu m w).mpr hw))

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem muM_some_ne_none (mu : Matching M W) (m : M) (w : W)
    (h : mu.muM m = some w) : mu.muM m ≠ none := by
  rw [h]
  simp

/-- A pair blocks when both participants strictly prefer each other to their current partners. -/
def IsBlockingPair (p : Profile M W) (mu : Matching M W) (m : M) (w : W) : Prop :=
  prefersM p m w (mu.muM m) ∧ prefersW p w m (mu.muW w)

/-- Preference lists are complete, and `prefersM`/`prefersW` treat `none` as worst.
The stability definition uses that convention directly, so the model carries no
separate acceptability or individual-rationality field. -/
def IsStable (p : Profile M W) (mu : Matching M W) : Prop :=
  ∀ m w, ¬ IsBlockingPair p mu m w

/-- A deferred-acceptance configuration: each woman holds at most one proposer, and
`proposed` records all pairs that have already been proposed. -/
structure DAState (M W : Type*) where
  held : W → Option M
  proposed : Finset (M × W)

/-- Unheld men who still have at least one woman to whom they have not proposed. -/
def activeMen (s : DAState M W) : Finset M := by
  classical
  exact Finset.univ.filter (fun m =>
    (∀ w, s.held w ≠ some m) ∧ ∃ w, (m, w) ∉ s.proposed)

omit [Nonempty M] [Nonempty W] in
theorem mem_activeMen_iff (s : DAState M W) (m : M) :
    m ∈ activeMen s ↔ (∀ w, s.held w ≠ some m) ∧ ∃ w, (m, w) ∉ s.proposed := by
  classical
  simp [activeMen]

/-- The women to whom `m` has not yet proposed. -/
def unproposedWomen (s : DAState M W) (m : M) : Finset W := by
  classical
  exact Finset.univ.filter (fun w => (m, w) ∉ s.proposed)

omit [Fintype M] [Fintype W] [DecidableEq M] [Nonempty M] in
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

omit [Fintype M] [Nonempty M] in
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

omit [Nonempty M] in
/-- Every successful step adds a pair that had not previously been proposed. -/
theorem DA_step_inserts_unproposed (p : Profile M W) (s s₂ : DAState M W)
    (h : DA_step p s = some s₂) :
    ∃ m w, (m, w) ∉ s.proposed ∧ (m, w) ∈ s₂.proposed := by
  classical
  unfold DA_step at h
  split at h
  · simp only [Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    let m := Classical.choose ‹(activeMen s).Nonempty›
    let hm : m ∈ activeMen s := Classical.choose_spec ‹(activeMen s).Nonempty›
    have hmAvail : ∃ w, (m, w) ∉ s.proposed := by
      exact (mem_activeMen_iff s m).mp hm |>.2
    have hCandidates : (unproposedWomen s m).Nonempty := by
      rcases hmAvail with ⟨w, hw⟩
      exact ⟨w, by simpa [unproposedWomen] using hw⟩
    let hNext := nextWoman_spec p s m hCandidates
    let w := Classical.choose hNext
    have hAvailable : w ∈ unproposedWomen s m :=
      (Classical.choose_spec hNext).2
    refine ⟨m, w, ?_, ?_⟩
    · simpa [unproposedWomen] using hAvailable
    · simp only [Finset.mem_insert]
      exact Or.inl rfl
  · simp at h

/-- The initial deferred-acceptance configuration has no holders and no proposals. -/
def initialState : DAState M W where
  held := fun _ => none
  proposed := ∅

/-- A state is quiescent when no unheld man has an unproposed woman left. -/
def IsQuiescent (s : DAState M W) : Prop := activeMen s = ∅

end

namespace GS.Palomar

/-- A two-sided profile, reusing the project structure with decidable, strict
preferences for each participant. -/
def Profile (M W : Type*) : Type _ := _root_.Profile M W

/-- A matching is represented by mutually inverse optional partner maps. -/
def Matching (M W : Type*) : Type _ := _root_.Matching M W

/-- A partner is preferred to being unmatched. -/
def prefersM {M W : Type*} (p : Profile M W) (m : M) (w : W)
    (cur : Option W) : Prop :=
  _root_.prefersM p m w cur

/-- A partner is preferred to being unmatched. -/
def prefersW {M W : Type*} (p : Profile M W) (w : W) (m : M)
    (cur : Option M) : Prop :=
  _root_.prefersW p w m cur

/-- A pair blocks when both participants prefer each other to their current partners. -/
def IsBlockingPair {M W : Type*} (p : Profile M W) (mu : Matching M W)
    (m : M) (w : W) : Prop :=
  prefersM p m w (mu.muM m) ∧ prefersW p w m (mu.muW w)

/-- A matching is stable when it has no blocking pair. -/
def IsStable {M W : Type*} (p : Profile M W) (mu : Matching M W) : Prop :=
  ∀ m w, ¬ IsBlockingPair p mu m w

/-- A partner is achievable when some stable matching assigns that partner. -/
def Achievable {M W : Type*} (p : Profile M W) (m : M) (w : W) : Prop :=
  ∃ mu : Matching M W, IsStable p mu ∧ mu.muM m = some w

end GS.Palomar
