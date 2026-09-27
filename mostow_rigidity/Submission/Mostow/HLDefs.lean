import Submission.Mostow.Interfaces

/-!
# Lead-written vocabulary for HL / bounded torsion (definitions and Props only; DO NOT EDIT)
Used by the top-level requests ellipticGap, frameThinDeep, margulisLox, HL_of_boundedTorsion, boundedTorsion.
-/

open LeanEval.Geometry.MostowRigidity MeasureTheory

namespace Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- finite subgroups of `Γ` have uniformly bounded order -/
def BoundedTorsion (Γ : Subgroup (PO n 1)) : Prop :=
  ∃ B : ℕ, ∀ F : Subgroup (PO n 1), F ≤ Γ → Finite F → Nat.card F ≤ B

/-- `g` moves every point of the unit hdist-ball around `z` by less than `η` -/
def NearIdAt (g : PO n 1) (z : E n) (η : ℝ) : Prop :=
  ∀ u : E n, hdist z u ≤ 1 → hdist u (g • u) < η

/-- `g` is loxodromic with boundary fixed points `a ≠ b` (nonzero translation at `a`) -/
def LoxPair (g : PO n 1) (a b : E n) : Prop :=
  a ∈ Sph n ∧ b ∈ Sph n ∧ a ≠ b ∧ bd g a = a ∧ bd g b = b ∧ busemann a (g • (0 : E n)) ≠ 0

/-- classification of fixed-point-free isometries -/
def ClassifyProp (n : ℕ) : Prop :=
  ∀ g : PO n 1, (∀ p : E n, g • p ≠ p) → IsParabolic g ∨ ∃ a b : E n, LoxPair g a b

/-- multiplicity-`N` thick part is cocompact (generalised thickPart_cocompact) -/
def MultThickProp (Γ : Subgroup (PO n 1)) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ N : ℕ, ∃ K : Set (E n), IsCompact K ∧ ∀ u : E n,
    ({γ : Γ | hdist u ((γ : PO n 1) • u) < δ}.Finite ∧
      {γ : Γ | hdist u ((γ : PO n 1) • u) < δ}.ncard ≤ N) → ∃ γ : Γ, (γ : PO n 1) • u ∈ K

/-- statement of `Work.Mostow.margulisCusp` -/
def MargulisCuspProp (n : ℕ) : Prop :=
  ∀ R : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
    ∀ (u ξ : E n) (q δ : Γ), IsParabolic (q : PO n 1) → ξ ∈ Sph n → bd (q : PO n 1) ξ = ξ →
      hdist u ((q : PO n 1) • u) < ε → hdist u ((δ : PO n 1) • u) ≤ R → bd (δ : PO n 1) ξ = ξ

/-- statement of `Work.Mostow.pairStab` -/
def PairStabProp (n : ℕ) : Prop :=
  ∀ ξ η : E n, ξ ∈ Sph n → η ∈ Sph n → ξ ≠ η →
    ∃ p : E n, ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      hdist p (g • p) = |busemann ξ (g • (0 : E n))| ∧
      ∀ ζ ∈ Sph n, ζ ≠ ξ → ζ ≠ η → bd g ζ = ζ → busemann ξ (g • (0 : E n)) = 0

/-- loxodromic analogue of margulisCusp: an R-short element preserves the fixed pair setwise -/
def MargulisLoxProp (n : ℕ) : Prop :=
  ∀ R : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ (Γ : Subgroup (PO n 1)), IsDiscrete (SetLike.coe Γ) →
    ∀ (z x y : E n) (a δ : Γ), LoxPair (a : PO n 1) x y → NearIdAt (a : PO n 1) z η →
      hdist z ((δ : PO n 1) • z) ≤ R →
      (bd (δ : PO n 1) x = x ∧ bd (δ : PO n 1) y = y) ∨ (bd (δ : PO n 1) x = y ∧ bd (δ : PO n 1) y = x)

end

end Submission.Mostow
