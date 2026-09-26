import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import GS.Basic

universe u v

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty W]

open Finset

/-- The number of proposals that remain possible. -/
def terminationMeasure (s : DAState M W) : Nat :=
  (Finset.univ : Finset (M × W)).card - s.proposed.card

omit [Fintype M] in
/-- The next woman is preferred to every other unproposed candidate. -/
theorem nextWoman_maximal (p : Profile M W) (s : DAState M W) (m : M) (w : W)
    (hnext : nextWoman p s m = some w) :
    w ∈ unproposedWomen s m ∧
      ∀ w' ∈ unproposedWomen s m, w' ≠ w → p.prefM m w w' := by
  classical
  unfold nextWoman at hnext
  split at hnext
  · rename_i hCandidates
    simp only [Option.some.injEq] at hnext
    subst w
    exact Classical.choose_spec
      (exists_prefM_maximal p m (unproposedWomen s m) hCandidates)
  · simp at hnext

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

/-- Successful steps preserve all old proposals. -/
theorem proposed_subset (p : Profile M W) (s s₂ : DAState M W)
    (h : DA_step p s = some s₂) : s.proposed ⊆ s₂.proposed := by
  obtain ⟨m, w, _, hshape⟩ := DA_step_proposed_shape p s s₂ h
  rw [hshape]
  exact subset_insert _ _

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

/-- If a woman already has a holder, a proposal leaves her with that man or a
strictly preferred one. -/
theorem DA_step_women_only_trade_up (p : Profile M W) (s s₂ : DAState M W)
    (hstep : DA_step p s = some s₂) (w : W) (m₁ : M)
    (hheld : s.held w = some m₁) :
    ∃ m₂, s₂.held w = some m₂ ∧ (m₂ = m₁ ∨ p.prefW w m₂ m₁) := by
  obtain ⟨m, wNext, kept, hkept, hsame, hchoice, _, _, _, _⟩ :=
    DA_step_held_info p s s₂ hstep
  by_cases hw : w = wNext
  · subst w
    cases hcur : s.held wNext with
    | none => simp [hcur] at hheld
    | some old =>
        have hold : old = m₁ := Option.some.inj (hcur.symm.trans hheld)
        subst old
        have hchoice' := hchoice
        rw [hcur] at hchoice'
        rcases hchoice' with ⟨hkeptM, hbetter⟩ | ⟨hkeptOld, _⟩
        · exact ⟨kept, hkept, Or.inr (by simpa [hkeptM] using hbetter)⟩
        · exact ⟨kept, hkept, Or.inl hkeptOld⟩
  · refine ⟨m₁, ?_, Or.inl rfl⟩
    rw [hsame w hw]
    exact hheld

/-- Along any sequence of DA steps, a woman who starts with a holder keeps that
man or ends with a strictly preferred holder. -/
theorem women_only_trade_up (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) :
    ∀ w m₁, s.held w = some m₁ →
      ∃ m₂, t.held w = some m₂ ∧ (m₂ = m₁ ∨ p.prefW w m₂ m₁) := by
  induction hreach with
  | refl _ =>
      intro w m₁ hheld
      exact ⟨m₁, hheld, Or.inl rfl⟩
  | oneStep hstep =>
      intro w m₁ hheld
      exact DA_step_women_only_trade_up p _ _ hstep w m₁ hheld
  | trans h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      intro w m₁ hheld
      obtain ⟨m₂, hmid, hrel₁⟩ := ih₁₂ w m₁ hheld
      obtain ⟨m₃, hend, hrel₂⟩ := ih₂₃ w m₂ hmid
      refine ⟨m₃, hend, ?_⟩
      rcases hrel₁ with rfl | hbetter₁
      · exact hrel₂
      · rcases hrel₂ with rfl | hbetter₂
        · exact Or.inr hbetter₁
        · exact Or.inr (p.transW w m₃ m₂ m₁ hbetter₂ hbetter₁)

/-- In every reachable state, earlier proposals are preferred to women not yet
proposed to. -/
def ProposalOrder (p : Profile M W) (s : DAState M W) : Prop :=
  ∀ m w₁ w₂, (m, w₁) ∈ s.proposed → (m, w₂) ∉ s.proposed → p.prefM m w₁ w₂

theorem DA_step_preserves_ProposalOrder (p : Profile M W) (s s₂ : DAState M W)
    (hstep : DA_step p s = some s₂) (horder : ProposalOrder p s) :
    ProposalOrder p s₂ := by
  obtain ⟨mNew, wNew, hnext, _, _, hshape⟩ := DA_step_proposal_info p s s₂ hstep
  intro m w₁ w₂ hmem hnot
  rw [hshape] at hmem hnot
  rcases Finset.mem_insert.mp hmem with hnew | hold
  · rcases Prod.mk.inj hnew with ⟨rfl, rfl⟩
    have hnotOld : (m, w₂) ∉ s.proposed := by
      intro hmemOld
      exact hnot (Finset.mem_insert_of_mem hmemOld)
    have hnewNe : w₂ ≠ w₁ := by
      intro heq
      subst w₂
      exact hnot (by simp)
    have hw₂ : w₂ ∈ unproposedWomen s m := by
      simpa [unproposedWomen] using hnotOld
    exact (nextWoman_maximal p s m w₁ hnext).2 w₂ hw₂ hnewNe
  · have hnotOld : (m, w₂) ∉ s.proposed := by
      intro hmemOld
      exact hnot (Finset.mem_insert_of_mem hmemOld)
    exact horder m w₁ w₂ hold hnotOld

theorem ProposalOrder_preserved (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) : ProposalOrder p s → ProposalOrder p t := by
  induction hreach with
  | refl _ => exact id
  | oneStep hstep => exact DA_step_preserves_ProposalOrder p _ _ hstep
  | trans _ _ ih₁₂ ih₂₃ => intro horder; exact ih₂₃ (ih₁₂ horder)

/-- A later proposal is strictly lower-ranked than every earlier proposal by the
same man. -/
theorem men_propose_decreasing (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s) {m : M} {w₁ w₂ : W}
    (hearlier : (m, w₁) ∈ s.proposed) (hnext : nextWoman p s m = some w₂) :
    p.prefM m w₁ w₂ ∧ w₁ ≠ w₂ ∧ ¬ p.prefM m w₂ w₁ := by
  have hnew := (nextWoman_maximal p s m w₂ hnext).1
  have hnot : (m, w₂) ∉ s.proposed := by
    simpa [unproposedWomen] using hnew
  have horder : ProposalOrder p s :=
    ProposalOrder_preserved p hreach (by
      intro m w₁ w₂ h₁ h₂
      simp [initialState] at h₁)
  have hpreferred := horder m w₁ w₂ hearlier hnot
  have hne : w₁ ≠ w₂ := by
    intro heq
    subst w₂
    exact p.irreflM m w₁ hpreferred
  have hnotReverse : ¬ p.prefM m w₂ w₁ := by
    intro hreverse
    exact p.irreflM m w₁ (p.transM m w₁ w₂ w₁ hpreferred hreverse)
  exact ⟨hpreferred, hne, hnotReverse⟩

/-- Run deferred acceptance until no man has any unproposed woman left. -/
noncomputable def run (p : Profile M W) (s : DAState M W) : DAState M W :=
  match _h : DA_step p s with
  | none => s
  | some s₂ => run p s₂
termination_by terminationMeasure s
decreasing_by
  exact terminationMeasure_decreases p s s₂ _h

theorem DA_step_none_iff_quiescent (p : Profile M W) (s : DAState M W) :
    DA_step p s = none ↔ IsQuiescent s := by
  classical
  unfold DA_step IsQuiescent
  by_cases h : (activeMen s).Nonempty
  · have hne : activeMen s ≠ ∅ := Finset.nonempty_iff_ne_empty.mp h
    simp [h, hne]
  · have he : activeMen s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

theorem run_quiescent (p : Profile M W) (s : DAState M W) : IsQuiescent (run p s) := by
  unfold run
  split
  · rename_i hstep
    exact (DA_step_none_iff_quiescent p s).mp hstep
  · rename_i s₂ hstep
    exact run_quiescent p s₂
termination_by terminationMeasure s
decreasing_by
  exact terminationMeasure_decreases p s _ ‹DA_step p s = some _›

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

/-- Deferred acceptance reaches a quiescent state after finitely many proposals. -/
theorem exists_quiescent (p : Profile M W) :
    ∃ s, IsQuiescent s ∧ s.proposed ⊇ initialState.proposed ∧
      DAReaches p initialState s := by
  refine ⟨run p initialState, run_quiescent p initialState, ?_, run_reachable p initialState⟩
  simp [initialState]

end
