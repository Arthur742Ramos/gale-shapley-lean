import GS.Main

universe u v

namespace GS.Palomar

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty W]

/-- The men-proposing deferred-acceptance procedure has a stable outcome. -/
theorem galeShapley (p : Profile M W) :
    ∃ μ : Matching M W, IsStable p μ := by
  exact Implementation.galeShapley p

/-- The terminal matching produced by deferred acceptance is stable. -/
theorem daStable (p : Profile M W) :
    IsStable p (GS.Palomar.terminalMatchingRun p) := by
  exact (Implementation.daStable p).2

/-- Whenever a man is matched to w0 by the deferred-acceptance outcome, every stable-achievable partner is weakly below w0 in his preferences. -/
theorem daMenOptimal (p : Profile M W) (m : M) {w₀ : W}
    (hterminal :
      (GS.Palomar.terminalMatchingRun p).muM m = some w₀) :
    ∀ w : W, Achievable p m w → p.prefM m w₀ w ∨ w₀ = w := by
  exact Implementation.daMenOptimal p m hterminal

end

end GS.Palomar
