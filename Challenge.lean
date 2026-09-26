import Mathlib.Data.Fintype.Basic

universe u v

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty M] [Nonempty W]

/-- Strict preference lists for the two sides of a matching market. -/
structure Profile (M W : Type*) where
  prefM : M → W → W → Prop
  prefW : W → M → M → Prop
  decPrefM : ∀ m w₁ w₂, Decidable (prefM m w₁ w₂)
  decPrefW : ∀ w m₁ m₂, Decidable (prefW w m₁ m₂)
  irreflM : ∀ m w, ¬ prefM m w w
  transM : ∀ m w₁ w₂ w₃, prefM m w₁ w₂ → prefM m w₂ w₃ → prefM m w₁ w₃
  totalM : ∀ m w₁ w₂, w₁ ≠ w₂ → prefM m w₁ w₂ ∨ prefM m w₂ w₁
  irreflW : ∀ w m, ¬ prefW w m m
  transW : ∀ w m₁ m₂ m₃, prefW w m₁ m₂ → prefW w m₂ m₃ → prefW w m₁ m₃
  totalW : ∀ w m₁ m₂, m₁ ≠ m₂ → prefW w m₁ m₂ ∨ prefW w m₂ m₁

/-- A matching represented by mutually consistent optional partner maps. -/
structure Matching (M W : Type*) where
  muM : M → Option W
  muW : W → Option M
  inv1 : ∀ m w, muM m = some w → muW w = some m
  inv2 : ∀ m w, muW w = some m → muM m = some w

end

namespace GS.Palomar

/-- A two-sided profile with complete strict preferences. -/
def Profile (M W : Type*) : Type _ := _root_.Profile M W

/-- A matching is represented by mutually inverse optional partner maps. -/
def Matching (M W : Type*) : Type _ := _root_.Matching M W

/-- An unmatched option is treated as worse than every partner. -/
def prefersM {M W : Type*} (p : Profile M W) (m : M) (w : W)
    (cur : Option W) : Prop :=
  match cur with
  | none => True
  | some w' => p.prefM m w w'

/-- An unmatched option is treated as worse than every partner. -/
def prefersW {M W : Type*} (p : Profile M W) (w : W) (m : M)
    (cur : Option M) : Prop :=
  match cur with
  | none => True
  | some m' => p.prefW w m m'

/-- A pair blocks when both participants prefer each other to their partners. -/
def IsBlockingPair {M W : Type*} (p : Profile M W) (mu : Matching M W)
    (m : M) (w : W) : Prop :=
  prefersM p m w (mu.muM m) ∧ prefersW p w m (mu.muW w)

/-- A matching is stable when it has no blocking pair. -/
def IsStable {M W : Type*} (p : Profile M W) (mu : Matching M W) : Prop :=
  ∀ m w, ¬ IsBlockingPair p mu m w

/-- A partner is achievable when some stable matching assigns that partner. -/
def Achievable {M W : Type*} (p : Profile M W) (m : M) (w : W) : Prop :=
  ∃ mu : Matching M W, IsStable p mu ∧ mu.muM m = some w

noncomputable def terminalMatchingRun {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty W] (p : Profile M W) : Matching M W := by
  sorry

section

variable {M W : Type*}
  [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
  [Nonempty W]

/-- The men-proposing deferred-acceptance procedure has a stable outcome. -/
theorem galeShapley (p : Profile M W) :
    ∃ μ : Matching M W, IsStable p μ := by
  sorry

/-- The terminal matching produced by deferred acceptance is stable. -/
theorem daStable (p : Profile M W) :
    IsStable p (GS.Palomar.terminalMatchingRun p) := by
  sorry

/-- Whenever a man is matched to w0 by the deferred-acceptance outcome, every stable-achievable partner is weakly below w0 in his preferences. -/
theorem daMenOptimal (p : Profile M W) (m : M) {w₀ : W}
    (hterminal :
      (GS.Palomar.terminalMatchingRun p).muM m = some w₀) :
    ∀ w : W, Achievable p m w → p.prefM m w₀ w ∨ w₀ = w := by
  sorry

end

end GS.Palomar
