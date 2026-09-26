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

/-- The run from the initial state terminates quiescently, and its terminal
matching is stable. -/
theorem daStable (p : Profile M W) :
    let s := run p initialState
    IsQuiescent s ∧
      IsStable p
        (terminalMatching p s (run_reachable p initialState)) := by
  exact Implementation.daStable p

/-- Whenever a man is matched to w0 by the deferred-acceptance outcome, every stable-achievable partner is weakly below w0 in his preferences. -/
theorem daMenOptimal (p : Profile M W) (m : M) {w₀ : W}
    (hterminal :
      (terminalMatching p (run p initialState)
        (run_reachable p initialState)).muM m = some w₀) :
    ∀ w : W, Achievable p m w → p.prefM m w₀ w ∨ w₀ = w := by
  exact Implementation.daMenOptimal p m hterminal

end

end GS.Palomar
