import GS.Basic
import GS.Termination
import GS.Stability

universe u v

namespace GS.Palomar

namespace Implementation

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty W]

/-- The men-proposing deferred-acceptance procedure has a stable outcome. -/
theorem galeShapley (p : Profile M W) :
    ∃ μ : Matching M W, IsStable p μ := by
  obtain ⟨s, hquiet, _, hreach⟩ := exists_quiescent p
  exact ⟨terminalMatching p s hreach,
    stability_of_quiescent p hquiet hreach⟩

/-- The run from the initial state terminates quiescently, and its terminal
matching is stable. -/
theorem daStable (p : Profile M W) :
    let s := run p initialState
    IsQuiescent s ∧
      IsStable p
        (terminalMatching p s (run_reachable p initialState)) := by
  dsimp
  exact ⟨run_quiescent p initialState,
    stability_of_quiescent p (run_quiescent p initialState)
      (run_reachable p initialState)⟩

/-- Every stable-achievable partner is weakly below a man's partner in the
men-proposing deferred-acceptance outcome. -/
theorem daMenOptimal (p : Profile M W) (m : M) {w₀ : W}
    (hterminal :
      (terminalMatching p (run p initialState)
        (run_reachable p initialState)).muM m = some w₀) :
    ∀ w : W, Achievable p m w → p.prefM m w₀ w ∨ w₀ = w := by
  intro w hachievable
  exact men_optimal p (run_reachable p initialState) m hterminal hachievable

end

end Implementation

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty W]

noncomputable def terminalMatchingRun (p : Profile M W) : Matching M W :=
  terminalMatching p (run p initialState) (run_reachable p initialState)

end

end GS.Palomar
