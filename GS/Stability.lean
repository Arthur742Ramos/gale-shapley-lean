import GS.Basic
import GS.Termination

universe u v

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W]

open Finset

/-- No man is held by two different women in the state. -/
def HeldUnique (s : DAState M W) : Prop :=
  ∀ w₁ w₂ m, s.held w₁ = some m → s.held w₂ = some m → w₁ = w₂

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem initialState_heldUnique : HeldUnique (initialState : DAState M W) := by
  intro w₁ w₂ m h₁ _
  simp [initialState] at h₁

omit [Nonempty M] in
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

omit [Nonempty M] in
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

omit [Nonempty M] in
theorem HeldUnique_preserved (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) (hunique : HeldUnique s) : HeldUnique t := by
  induction hreach with
  | refl _ => exact hunique
  | oneStep hstep => exact DA_step_preserves_HeldUnique p _ _ hstep hunique
  | trans _ _ ih₁₂ ih₂₃ => exact ih₂₃ (ih₁₂ hunique)

omit [Nonempty M] in
theorem HeldUnique_of_reaches (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s) : HeldUnique s := by
  exact HeldUnique_preserved p hreach initialState_heldUnique

/-- Every man currently held by a woman has proposed to her. -/
def HeldWasProposed (s : DAState M W) : Prop :=
  ∀ w m, s.held w = some m → (m, w) ∈ s.proposed

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem initialState_heldWasProposed :
    HeldWasProposed (initialState : DAState M W) := by
  intro w m h
  simp [initialState] at h

omit [Nonempty M] in
theorem DA_step_preserves_HeldWasProposed (p : Profile M W)
    (s s₂ : DAState M W) (hstep : DA_step p s = some s₂)
    (hheldProposed : HeldWasProposed s) : HeldWasProposed s₂ := by
  obtain ⟨mNew, wNew, kept, hkept, hsame, hchoice, hfresh, hshape, _, _⟩ :=
    DA_step_held_info p s s₂ hstep
  intro w m hheld
  by_cases hw : w = wNew
  · subst w
    have hmKept : kept = m := Option.some.inj (hkept.symm.trans hheld)
    cases hcur : s.held wNew with
    | none =>
        have hk : kept = mNew := by simpa [hcur] using hchoice
        have hmNew : m = mNew := hmKept.symm.trans hk
        rw [hshape]
        simp [hmNew]
    | some old =>
        have hchoice' := hchoice
        rw [hcur] at hchoice'
        rcases hchoice' with ⟨hk, _⟩ | ⟨hk, _⟩
        · have hmNew : m = mNew := hmKept.symm.trans hk
          rw [hshape]
          simp [hmNew]
        · have hmOld : m = old := hmKept.symm.trans hk
          have holdProposed : (old, wNew) ∈ s.proposed :=
            hheldProposed wNew old hcur
          rw [hshape]
          apply Finset.mem_insert_of_mem
          simpa [hmOld] using holdProposed
  · have hOld : s.held w = some m := by
      simpa [hsame w hw] using hheld
    have hOldProposed : (m, w) ∈ s.proposed := hheldProposed w m hOld
    rw [hshape]
    exact Finset.mem_insert_of_mem hOldProposed

omit [Nonempty M] in
theorem HeldWasProposed_preserved (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) (hheldProposed : HeldWasProposed s) :
    HeldWasProposed t := by
  induction hreach with
  | refl _ => exact hheldProposed
  | oneStep hstep => exact DA_step_preserves_HeldWasProposed p _ _ hstep hheldProposed
  | trans _ _ ih₁₂ ih₂₃ => exact ih₂₃ (ih₁₂ hheldProposed)

omit [Nonempty M] in
theorem HeldWasProposed_of_reaches (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s) : HeldWasProposed s := by
  exact HeldWasProposed_preserved p hreach initialState_heldWasProposed

omit [Fintype M] [Nonempty M] in
/-- If a man prefers `v` to the woman he is proposing to, then he has already
proposed to `v`. -/
theorem preferred_woman_already_proposed (p : Profile M W) (s : DAState M W)
    (m : M) (w : W) (hnext : nextWoman p s m = some w) {v : W}
    (hpref : p.prefM m v w) : (m, v) ∈ s.proposed := by
  by_contra hv
  have hvUnproposed : v ∈ unproposedWomen s m := by
    simpa [unproposedWomen] using hv
  have hvne : v ≠ w := by
    intro heq
    subst v
    exact p.irreflM m w hpref
  have hmax := (nextWoman_maximal p s m w hnext).2 v hvUnproposed hvne
  exact p.irreflM m v (p.transM m v w v hpref hmax)

omit [Fintype M] [Fintype W] [Nonempty M] [Nonempty W] in
/-- If a man has proposed to `w` and strictly prefers `v`, then `v` was also
proposed to. -/
theorem preferred_proposed_woman_already_proposed (p : Profile M W)
    (s : DAState M W) (horder : ProposalOrder p s) {m : M} {w v : W}
    (hw : (m, w) ∈ s.proposed) (hpref : p.prefM m v w) :
    (m, v) ∈ s.proposed := by
  by_contra hv
  have hvne : v ≠ w := by
    intro heq
    subst v
    exact p.irreflM m w hpref
  have hreverse := horder m w v hw hv
  exact p.irreflM m v (p.transM m v w v hpref hreverse)

/-- A woman who has received a proposal never ends up with a man she likes less
than that proposer. -/
def NoRegret (p : Profile M W) (s : DAState M W) : Prop :=
  ∀ m w, (m, w) ∈ s.proposed → ¬ prefersW p w m (s.held w)

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem initialState_noRegret (p : Profile M W) :
    NoRegret p (initialState : DAState M W) := by
  intro m w h
  simp [initialState] at h

omit [Nonempty M] in
theorem DA_step_preserves_NoRegret (p : Profile M W) (s s₂ : DAState M W)
    (hstep : DA_step p s = some s₂) (hregret : NoRegret p s) :
    NoRegret p s₂ := by
  obtain ⟨mNew, wNew, kept, hkept, hsame, hchoice, _, hshape, _, _⟩ :=
    DA_step_held_info p s s₂ hstep
  intro m w hmem
  rw [hshape] at hmem
  rcases Finset.mem_insert.mp hmem with hnew | hold
  · rcases Prod.mk.inj hnew with ⟨hmEq, hwEq⟩
    subst m
    subst w
    cases hcur : s.held wNew with
    | none =>
        have hk : kept = mNew := by simpa [hcur] using hchoice
        rw [hkept, hk]
        simp only [prefersW]
        exact p.irreflW wNew mNew
    | some old =>
        have hchoice' := hchoice
        rw [hcur] at hchoice'
        rcases hchoice' with ⟨hk, _⟩ | ⟨hk, hreject⟩
        · rw [hkept, hk]
          simp only [prefersW]
          exact p.irreflW wNew mNew
        · rw [hkept, hk]
          simp only [prefersW]
          exact hreject
  · by_cases hw : wNew = w
    · subst wNew
      cases hcur : s.held w with
      | none =>
          have hbad := hregret m w hold
          simp [prefersW, hcur] at hbad
      | some old =>
          have hnotOld : ¬ p.prefW w m old := by
            simpa [prefersW, hcur] using hregret m w hold
          obtain ⟨newHolder, hnewHolder, hrel⟩ :=
            DA_step_women_only_trade_up p s s₂ hstep w old hcur
          have hnotNew : ¬ p.prefW w m newHolder := by
            intro hbetter
            rcases hrel with heq | hbetterOld
            · subst newHolder
              exact hnotOld hbetter
            · exact hnotOld (p.transW w m newHolder old hbetter hbetterOld)
          rw [hnewHolder]
          simpa [prefersW] using hnotNew
    · have hold : (m, w) ∈ s.proposed := hold
      have hnotOld := hregret m w hold
      have hnewEq : w ≠ wNew := Ne.symm hw
      rw [hsame w hnewEq]
      exact hnotOld

omit [Nonempty M] in
theorem NoRegret_preserved (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) (hregret : NoRegret p s) : NoRegret p t := by
  induction hreach with
  | refl _ => exact hregret
  | oneStep hstep => exact DA_step_preserves_NoRegret p _ _ hstep hregret
  | trans _ _ ih₁₂ ih₂₃ => exact ih₂₃ (ih₁₂ hregret)

omit [Nonempty M] in
theorem NoRegret_of_reaches (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s) : NoRegret p s := by
  exact NoRegret_preserved p hreach (initialState_noRegret p)

omit [Nonempty M] in
theorem proposals_monotone_on_reaches (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) : s.proposed ⊆ t.proposed := by
  induction hreach with
  | refl _ => exact Subset.rfl
  | oneStep hstep => exact proposed_subset p _ _ hstep
  | trans _ _ ih₁₂ ih₂₃ => exact Subset.trans ih₁₂ ih₂₃

omit [Nonempty M] in
theorem no_regret_after_proposal (p : Profile M W) {s t : DAState M W}
    (hstart : DAReaches p initialState s) (hlater : DAReaches p s t)
    {m : M} {w : W} (hproposal : (m, w) ∈ s.proposed) :
    ¬ prefersW p w m (t.held w) := by
  have hpropSubset := proposals_monotone_on_reaches p hlater
  exact (NoRegret_of_reaches p (DAReaches.trans hstart hlater)) m w
    (hpropSubset hproposal)

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

omit [Nonempty M] in
theorem terminalMatching_inv (p : Profile M W) (s : DAState M W)
    (hreach : DAReaches p initialState s) (m : M) (w : W) :
    (terminalMatching p s hreach).muM m = some w ↔ s.held w = some m := by
  exact muM_eq_some_iff_muW (terminalMatching p s hreach) m w

omit [Nonempty M] [Nonempty W] in
theorem quiescent_unmatched_all_proposed (s : DAState M W)
    (hquiet : IsQuiescent s) (m : M)
    (hfree : ∀ w, s.held w ≠ some m) :
    ∀ w, (m, w) ∈ s.proposed := by
  intro w
  by_contra hnot
  have hmActive : m ∈ activeMen s :=
    (mem_activeMen_iff s m).2 ⟨hfree, ⟨w, hnot⟩⟩
  rw [hquiet] at hmActive
  simp at hmActive

omit [Nonempty M] in
theorem stability_of_quiescent (p : Profile M W) {s : DAState M W}
    (hquiet : IsQuiescent s) (hreach : DAReaches p initialState s) :
    IsStable p (terminalMatching p s hreach) := by
  intro m w hblock
  rcases hblock with ⟨hmPref, hwPref⟩
  have horder : ProposalOrder p s :=
    ProposalOrder_preserved p hreach (by
      intro m w₁ w₂ h₁ _
      simp [initialState] at h₁)
  have hproposal : (m, w) ∈ s.proposed := by
    cases hmu : (terminalMatching p s hreach).muM m with
    | none =>
        have hfree : ∀ v, s.held v ≠ some m := by
          intro v hv
          have hmv := (terminalMatching_inv p s hreach m v).2 hv
          rw [hmu] at hmv
          cases hmv
        exact quiescent_unmatched_all_proposed s hquiet m hfree w
    | some w₀ =>
        have hheld : s.held w₀ = some m :=
          (terminalMatching_inv p s hreach m w₀).mp hmu
        have hproposal₀ := HeldWasProposed_of_reaches p hreach w₀ m hheld
        by_contra hnot
        have horderPref := horder m w₀ w hproposal₀ hnot
        have hmPref' : p.prefM m w w₀ := by
          simpa [prefersM, hmu] using hmPref
        exact p.irreflM m w₀ (p.transM m w₀ w w₀ horderPref hmPref')
  have hnoRegret := NoRegret_of_reaches p hreach m w hproposal
  exact hnoRegret hwPref

/-- A pair is achievable when some stable matching assigns that woman to the man. -/
def Achievable (p : Profile M W) (m : M) (w : W) : Prop :=
  ∃ μ : Matching M W, IsStable p μ ∧ μ.muM m = some w

/-- Along a run, a man who has proposed to his stable partner must still be held
by that partner. -/
def StablePartnerHeld (p : Profile M W) (s : DAState M W) : Prop :=
  ∀ μ : Matching M W, IsStable p μ → ∀ m w,
    (m, w) ∈ s.proposed → μ.muM m = some w → s.held w = some m

omit [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W] in
theorem initialState_stablePartnerHeld (p : Profile M W) :
    StablePartnerHeld p (initialState : DAState M W) := by
  intro μ hstable m w hproposal
  simp [initialState] at hproposal

omit [Nonempty M] in
theorem DA_step_preserves_StablePartnerHeld (p : Profile M W)
    (s s₂ : DAState M W) (hstep : DA_step p s = some s₂)
    (hunique : HeldUnique s) (hheldProposed : HeldWasProposed s)
    (horder : ProposalOrder p s) (hstablePartner : StablePartnerHeld p s) :
    StablePartnerHeld p s₂ := by
  obtain ⟨mNew, wNew, kept, hkept, hsame, hchoice, _, hshape, hfree, hnext⟩ :=
    DA_step_held_info p s s₂ hstep
  intro μ hstable m w hmem hpartner
  have hwomanPartner : μ.muW w = some m := μ.inv1 m w hpartner
  rw [hshape] at hmem
  rcases Finset.mem_insert.mp hmem with hnew | hold
  · rcases Prod.mk.inj hnew with ⟨hmEq, hwEq⟩
    subst m
    subst w
    cases hcur : s.held wNew with
    | none =>
        have hk : kept = mNew := by simpa [hcur] using hchoice
        rw [hkept, hk]
    | some old =>
        have hchoice' := hchoice
        rw [hcur] at hchoice'
        rcases hchoice' with ⟨hk, hprefW⟩ | ⟨hk, hreject⟩
        · rw [hkept, hk]
        · have hnewNe : mNew ≠ old := by
            intro heq
            have hbad : s.held wNew = some mNew := by simpa [heq] using hcur
            exact hfree wNew hbad
          have hprefW' : p.prefW wNew old mNew := by
            rcases p.totalW wNew mNew old hnewNe with hpref | hpref
            · exact False.elim (hreject hpref)
            · exact hpref
          have hblockForOld (hmup : prefersM p old wNew (μ.muM old)) :
              IsBlockingPair p μ old wNew := by
            refine ⟨hmup, ?_⟩
            simpa [prefersW, hwomanPartner] using hprefW'
          cases hμold : μ.muM old with
          | none =>
              have hblock : IsBlockingPair p μ old wNew := by
                apply hblockForOld
                simp [prefersM, hμold]
              exact False.elim (hstable old wNew hblock)
          | some v =>
              have hwomanOld : μ.muW v = some old := μ.inv1 old v hμold
              have hvne : v ≠ wNew := by
                intro hv
                subst v
                exact hnewNe (Option.some.inj (hwomanPartner.symm.trans hwomanOld))
              by_cases hprefOld : p.prefM old wNew v
              · have hblock : IsBlockingPair p μ old wNew := by
                  apply hblockForOld
                  simpa [prefersM, hμold] using hprefOld
                exact False.elim (hstable old wNew hblock)
              · have hprefOld' : p.prefM old v wNew := by
                  rcases p.totalM old wNew v hvne.symm with hpref | hpref
                  · exact False.elim (hprefOld hpref)
                  · exact hpref
                have hproposalOld := hheldProposed wNew old hcur
                have hproposalV : (old, v) ∈ s.proposed :=
                  preferred_proposed_woman_already_proposed p s horder
                    hproposalOld hprefOld'
                have hheldV := hstablePartner μ hstable old v hproposalV hμold
                have hvEq := hunique v wNew old hheldV hcur
                exact False.elim (hvne hvEq)
  · have hheld : s.held w = some m := hstablePartner μ hstable m w hold hpartner
    by_cases hw : w = wNew
    · subst w
      cases hcur : s.held wNew with
      | none => simp [hcur] at hheld
      | some old =>
          have holdEq : old = m := Option.some.inj (hcur.symm.trans hheld)
          subst old
          have hnewNe : mNew ≠ m := by
            intro heq
            subst mNew
            exact hfree wNew hcur
          have hchoice' := hchoice
          rw [hcur] at hchoice'
          rcases hchoice' with ⟨hk, hprefW⟩ | ⟨hk, _⟩
          · have hqPref : prefersM p mNew wNew (μ.muM mNew) := by
              cases hμnew : μ.muM mNew with
              | none => simp [prefersM]
              | some v =>
                  have hwomanNew : μ.muW v = some mNew := μ.inv1 mNew v hμnew
                  have hvne : wNew ≠ v := by
                    intro hv
                    subst v
                    exact hnewNe (Option.some.inj (hwomanNew.symm.trans hwomanPartner))
                  have hnot : ¬ p.prefM mNew v wNew := by
                    intro hpref
                    have hproposalV := preferred_woman_already_proposed
                      p s mNew wNew hnext hpref
                    have hheldV := hstablePartner μ hstable mNew v hproposalV hμnew
                    exact hfree v hheldV
                  rcases p.totalM mNew wNew v hvne with hpref | hpref
                  · simpa [prefersM, hμnew] using hpref
                  · exact False.elim (hnot hpref)
            have hblock : IsBlockingPair p μ mNew wNew := by
              refine ⟨hqPref, ?_⟩
              simpa [prefersW, hwomanPartner] using hprefW
            exact False.elim (hstable mNew wNew hblock)
          · have hk' : kept = m := hk
            rw [hkept, hk']
    · rw [hsame w hw]
      exact hheld

omit [Nonempty M] in
theorem StablePartnerHeld_preserved (p : Profile M W) {s t : DAState M W}
    (hreach : DAReaches p s t) :
    HeldUnique s → HeldWasProposed s → ProposalOrder p s → StablePartnerHeld p s →
      StablePartnerHeld p t := by
  induction hreach with
  | refl _ => intro _ _ _ hinv; exact hinv
  | oneStep hstep =>
      intro hunique hheldProposed horder hstablePartner
      exact DA_step_preserves_StablePartnerHeld p _ _ hstep
        hunique hheldProposed horder hstablePartner
  | trans h₁₂ h₂₃ ih₁₂ ih₂₃ =>
      intro hunique hheldProposed horder hstablePartner
      apply ih₂₃
      · exact HeldUnique_preserved p h₁₂ hunique
      · exact HeldWasProposed_preserved p h₁₂ hheldProposed
      · exact ProposalOrder_preserved p h₁₂ horder
      · exact ih₁₂ hunique hheldProposed horder hstablePartner

omit [Nonempty M] in
theorem StablePartnerHeld_of_reaches (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s) : StablePartnerHeld p s := by
  apply StablePartnerHeld_preserved p hreach
  · exact initialState_heldUnique
  · exact initialState_heldWasProposed
  · intro m w₁ w₂ hproposal _
    simp [initialState] at hproposal
  · exact initialState_stablePartnerHeld p

omit [Nonempty M] in
theorem no_achievable_rejection (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s) {m : M} {w : W}
    (hproposal : (m, w) ∈ s.proposed) (hnotHeld : s.held w ≠ some m) :
    ¬ Achievable p m w := by
  rintro ⟨μ, hstable, hpartner⟩
  have hheld := StablePartnerHeld_of_reaches p hreach μ hstable m w hproposal hpartner
  exact hnotHeld hheld

omit [Nonempty M] in
theorem no_achievable_if_unmatched (p : Profile M W) {s : DAState M W}
    (hquiet : IsQuiescent s) (hreach : DAReaches p initialState s)
    (m : M) (hunmatched : (terminalMatching p s hreach).muM m = none)
    (w : W) : ¬ Achievable p m w := by
  have hfree : ∀ v, s.held v ≠ some m := by
    intro v hv
    have hmv := (terminalMatching_inv p s hreach m v).2 hv
    rw [hunmatched] at hmv
    cases hmv
  have hproposal := quiescent_unmatched_all_proposed s hquiet m hfree w
  exact no_achievable_rejection p hreach hproposal (hfree w)

omit [Nonempty M] in
theorem men_optimal (p : Profile M W) {s : DAState M W}
    (hreach : DAReaches p initialState s)
    (m : M) {w₀ w : W}
    (hterminal : (terminalMatching p s hreach).muM m = some w₀)
    (hachievable : Achievable p m w) :
    p.prefM m w₀ w ∨ w₀ = w := by
  by_cases hproposal : (m, w) ∈ s.proposed
  · by_cases hheld : s.held w = some m
    · have hterminalW := (terminalMatching_inv p s hreach m w).2 hheld
      right
      exact (Option.some.inj (hterminalW.symm.trans hterminal)).symm
    · exact False.elim (no_achievable_rejection p hreach hproposal hheld hachievable)
  · have hheldTerminal : s.held w₀ = some m :=
      (terminalMatching_inv p s hreach m w₀).mp hterminal
    have hproposalTerminal := HeldWasProposed_of_reaches p hreach w₀ m hheldTerminal
    have horder : ProposalOrder p s :=
      ProposalOrder_preserved p hreach (by
        intro m w₁ w₂ h₁ _
        simp [initialState] at h₁)
    exact Or.inl (horder m w₀ w hproposalTerminal hproposal)

end
