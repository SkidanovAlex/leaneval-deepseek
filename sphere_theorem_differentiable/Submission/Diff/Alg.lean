import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Algebraic curvature tensors (lead-written contract module; definitions and `Prop`s only)

Convention (matches `LeanEval.Geometry.SphereTheorem.curv`): for an orthonormal frame `e`,
`R i j k l = ⟪R(eᵢ, eⱼ) eₗ, eₖ⟫`, so `R i j i j` is the sectional curvature of `eᵢ ∧ eⱼ`, and the
unit round sphere has `R = Iso n`, i.e. `R i j k l = δᵢₖ δⱼₗ - δᵢₗ δⱼₖ`. This is the convention of
Brendle–Schoen (arXiv 0705.0766): there `R₁₃₁₃` is the sectional curvature of `e₁ ∧ e₃`.
Under Ricci flow, in an Uhlenbeck frame, `D_t R = ΔR + Q(R)` with `Q` as below.
Sanity check: `Q (Iso n) = 2 (n - 1) • Iso n`.
-/

namespace Submission.Diff.Alg

open Finset

/-- 4-index arrays on `ℝⁿ`: curvature components in an orthonormal frame. -/
abbrev Curv4 (n : ℕ) := Fin n → Fin n → Fin n → Fin n → ℝ

variable {n : ℕ}

/-- Algebraic curvature tensor: antisymmetry in the first pair, pair symmetry, first Bianchi. -/
def IsAlgCurv (R : Curv4 n) : Prop :=
  (∀ i j k l, R j i k l = - R i j k l) ∧ (∀ i j k l, R k l i j = R i j k l) ∧
  (∀ i j k l, R i j k l + R j k i l + R k i j l = 0)

/-- Multilinear evaluation `R(a, b, c, d) = ∑ Rᵢⱼₖₗ aᵢ bⱼ cₖ dₗ`. -/
noncomputable def R4 (R : Curv4 n) (a b c d : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * a i * b j * c k * d l

/-- The curvature tensor of the unit round sphere, `δᵢₖ δⱼₗ - δᵢₗ δⱼₖ`. -/
noncomputable def Iso (n : ℕ) : Curv4 n := fun i j k l =>
  (if i = k then 1 else 0) * (if j = l then 1 else 0) - (if i = l then 1 else 0) * (if j = k then 1 else 0)

/-- Hamilton's quadratic reaction term `Q(R)ᵢⱼₖₗ = RᵢⱼₚqRₖₗₚq + 2 RᵢₚₖqRⱼₚₗq - 2 RᵢₚₗqRⱼₚₖq`. -/
noncomputable def Q (R : Curv4 n) : Curv4 n := fun i j k l =>
  ∑ p, ∑ q, (R i j p q * R k l p q + 2 * R i p k q * R j p l q - 2 * R i p l q * R j p k q)

/-- Nonnegative complex sectional curvature (`PIC2`; Brendle–Schoen's cone `Ĉ`: `M × ℝ²` has
nonnegative isotropic curvature). Real form of `R(ζ, η, ζ̄, η̄) ≥ 0` with `ζ = x + iy`, `η = z + iw`. -/
def InPIC2 (R : Curv4 n) : Prop :=
  ∀ x y z w : Fin n → ℝ,
    0 ≤ R4 R x z x z + R4 R x w x w + R4 R y z y z + R4 R y w y w - 2 * R4 R x y z w

/-- Euclidean dot product on `Fin n → ℝ`. -/
noncomputable def dot (u v : Fin n → ℝ) : ℝ := ∑ i, u i * v i

/-- `u, v` orthonormal. -/
def IsONPair (u v : Fin n → ℝ) : Prop := dot u u = 1 ∧ dot v v = 1 ∧ dot u v = 0

/-- Sectional curvature of the plane of an orthonormal pair. -/
noncomputable def secK (R : Curv4 n) (u v : Fin n → ℝ) : ℝ := R4 R u v u v

/-- `R` is `δ`-pinched: `δ · K(σ') ≤ K(σ)` for all planes `σ, σ'`. -/
def IsPinchedAlg (δ : ℝ) (R : Curv4 n) : Prop :=
  ∀ u v u' v' : Fin n → ℝ, IsONPair u v → IsONPair u' v' → δ * secK R u' v' ≤ secK R u v

/-- Change of orthonormal frame by a matrix `A` (`e'ᵢ = ∑ₐ Aᵢₐ eₐ`). -/
noncomputable def rot (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) : Curv4 n := fun i j k l =>
  ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d

/-- `F` is invariant under Hamilton's ODE `R' = Q(R)` (forward in time). -/
def ODEInvariant (F : Set (Curv4 n)) : Prop :=
  ∀ (T : ℝ) (R : ℝ → Curv4 n), R 0 ∈ F →
    (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt R (Q (R t)) (Set.Ico 0 T) t) →
    ∀ t ∈ Set.Ico 0 T, R t ∈ F

/-- A fibrewise set to which Hamilton's maximum principle applies. -/
def IsInvariantSet (F : Set (Curv4 n)) : Prop :=
  IsClosed F ∧ Convex ℝ F ∧ (∀ R ∈ F, IsAlgCurv R) ∧
    (∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R ∈ F, rot A R ∈ F) ∧ ODEInvariant F

/-- A pinching set (Böhm–Wilking): invariant, and for each `δ < 1` only a bounded part of it is
not `δ`-pinched. -/
def IsPinchingSet (F : Set (Curv4 n)) : Prop :=
  IsInvariantSet F ∧ ∀ δ : ℝ, δ < 1 → Bornology.IsBounded {R | R ∈ F ∧ ¬ IsPinchedAlg δ R}

/-- CONTRACT A1 (Brendle–Schoen Prop. 17, via Böhm–Wilking): every compact set of algebraic
curvature tensors in the interior of `PIC2` lies in a pinching set. -/
def PinchingSetExists (n : ℕ) : Prop :=
  ∀ K : Set (Curv4 n), IsCompact K →
    (∀ R ∈ K, IsAlgCurv R ∧ ∃ ε : ℝ, 0 < ε ∧ InPIC2 (R - ε • Iso n)) →
    ∃ F : Set (Curv4 n), IsPinchingSet F ∧ K ⊆ F

/-- CONTRACT A0 (Brendle–Schoen Cor. 22 + Berger's inequality): strictly quarter-pinched
algebraic curvature tensors lie in the interior of `PIC2`. -/
def QuarterToPIC2 (n : ℕ) : Prop :=
  ∀ R : Curv4 n, IsAlgCurv R → ∀ c : ℝ, 0 < c →
    (∀ u v : Fin n → ℝ, IsONPair u v → c < secK R u v ∧ secK R u v ≤ 4 * c) →
    ∃ ε : ℝ, 0 < ε ∧ InPIC2 (R - ε • Iso n)

/-- Scalar curvature `∑ᵢⱼ Rᵢⱼᵢⱼ`. -/
noncomputable def scalAlg (R : Curv4 n) : ℝ := ∑ i, ∑ j, R i j i j

/-- A time-dependent family `F t` is invariant under `R' = Q(R)`: a solution starting in `F t₀`
at time `t₀` stays in `F t`. -/
def ODEInvariantFamily (F : ℝ → Set (Curv4 n)) : Prop :=
  ∀ (t₀ T : ℝ) (R : ℝ → Curv4 n), R t₀ ∈ F t₀ →
    (∀ t ∈ Set.Ico t₀ T, HasDerivWithinAt R (Q (R t)) (Set.Ico t₀ T) t) →
    ∀ t ∈ Set.Ico t₀ T, R t ∈ F t

/-- Hamilton's hypotheses for a time-dependent family (closed space-time track, convex,
O(n)-invariant fibres of algebraic curvature tensors, ODE-invariant). -/
def IsInvariantFamily (F : ℝ → Set (Curv4 n)) : Prop :=
  IsClosed {p : ℝ × Curv4 n | p.2 ∈ F p.1} ∧ (∀ t, Convex ℝ (F t)) ∧
    (∀ t, ∀ R ∈ F t, IsAlgCurv R) ∧
    (∀ t, ∀ A ∈ Matrix.orthogonalGroup (Fin n) ℝ, ∀ R ∈ F t, rot A R ∈ F t) ∧
    ODEInvariantFamily F

end Submission.Diff.Alg
