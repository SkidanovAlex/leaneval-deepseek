/-
# The flat torus Cauchy problem for the DeTurck (quasilinear parabolic) system

This file fixes the **vocabulary** of the flat analytic core of the short-time existence theorem:
the Cauchy problem for the chart expression of the DeTurck operator
`P(g) = -2 Ric(g) + L_{W(g)} g`, which is a quasilinear parabolic system with *scalar* principal
part `Σ_{cd} g^{cd} ∂_c ∂_d` (the DeTurck cancellation, proved at jet level in
`Work.Diff.STE.DeTurck.pPhi_decomp`).

## The setting

All functions live on the flat torus, realised as `1`-periodic functions on `Fin n → ℝ`
(`n = Module.finrank ℝ E`, the dimension of the manifold).  The unknown is a **matrix-valued**
function on the torus, `u : ℝ → Torus n`, with `Torus n = (Fin n → ℝ) → MatC n` and
`MatC n = Fin n → Fin n → ℂ`.

The unknown is taken ℂ-valued so that the whole of Layer A
(`Submission/Work/Diff/STE/LayerA.lean`: Fourier series, `CSq`, `ENormSq`, Gårding,
Moser/tame estimates, Grönwall) applies verbatim.  The solution is nevertheless *real*: the
nonlinearity is conjugation-equivariant (`ConjEquivNonlin`) and the initial datum is real, so
`conj ∘ u` solves the same problem and `u = conj ∘ u` follows from uniqueness
(`torus_uniqueness`).  This avoids re-deriving every Layer A estimate in real form.

## The nonlinearity

`Φ : (Fin n → ℝ) × Jet n → MatC n` with `Jet n = MatC n × (Fin n → MatC n) × (Fin n → Fin n → MatC n)`
the spatial `2`-jet `(A, L, B) = (u, ∂u, ∂²u)`.  The DeTurck shape is
`Φ (x, (A, L, B)) = secOpFlat A B + N (x, (A, L))`, where the principal coefficient is the *real*
inverse matrix of the real part of `A` (so that Gårding's ellipticity hypothesis
`garding_estimate_vec` applies):

`secOpFlat A B |_{ij} = Σ_{cd} (reMat A)⁻¹_{cd} · B c d i j`.

The jet-level identification of this `Φ` (for the chart matrix of a metric and its background) is
the content of the C1 bridge; see `DESIGN.md`.  Here only the *shape* is used.

## The four analytic pieces (filed separately, each an independent obligation)

1. `galerkin_ode_existence` — for every truncation order `N` the projected ODE
   `c' = projBox N (fourierCoeff (Φ ∘ jet))` has a local solution (Picard–Lindelöf on the
   finite-dimensional space of coefficients supported in the box `box N`).
2. `energy_bound_uniform` — the a priori bound: there are `τ, B > 0`, depending only on `Φ`, on
   the ellipticity bound of `u₀` and on `ENormSqM k u₀`, such that *every* Galerkin solution at
   level `k` stays in the ball `ENormSqM k · ≤ B²` and stays positive definite on `[0, τ]`.
3. `limit_solves` — a subsequence of the Galerkin solutions converges to a smooth solution of the
   PDE on `[0, τ]` (uniform `H^k` bounds + Sobolev embedding + Arzelà–Ascoli, and identification
   of the limit equation by uniqueness of Fourier coefficients).
4. `torus_uniqueness` — two smooth solutions with the same initial datum agree (L² Grönwall on the
   difference; the difference solves a *linear* parabolic system with bounded coefficients).

The assembly of 1–4 into `torus_short_time_existence` is in `TorusCauchy.lean`.
-/

import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pd_periodization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric MeasureTheory

namespace Work.Diff.STE

namespace Flat

noncomputable section

variable {n : ℕ}

/-- Matrices of size `n × n` with complex entries: the values of the torus unknown. -/
abbrev MatC (n : ℕ) := Fin n → Fin n → ℂ

/-- Matrix-valued functions on the flat torus (realised as `1`-periodic functions on `Fin n → ℝ`). -/
abbrev Torus (n : ℕ) := (Fin n → ℝ) → MatC n

/-- The spatial `2`-jet of a matrix-valued function: value, first and second coordinate
derivatives. -/
abbrev Jet (n : ℕ) := MatC n × (Fin n → MatC n) × (Fin n → Fin n → MatC n)

/-- The real matrix underlying a complex matrix. -/
def reMat {n : ℕ} (A : MatC n) : Matrix (Fin n) (Fin n) ℝ := fun i j => (A i j).re

/-- The (entrywise) conjugate of a matrix. -/
def conjMat {n : ℕ} (A : MatC n) : MatC n := fun i j => star (A i j)

@[simp] lemma reMat_apply {n : ℕ} (A : MatC n) (i j : Fin n) : reMat A i j = (A i j).re := rfl

@[simp] lemma conjMat_apply {n : ℕ} (A : MatC n) (i j : Fin n) : conjMat A i j = star (A i j) :=
  rfl

lemma reMat_conjMat {n : ℕ} (A : MatC n) : reMat (conjMat A) = reMat A := by
  funext i j; simp [reMat, conjMat]

/-- Positive definiteness of a complex matrix, meaning that its real part (a real matrix) is
positive definite. -/
def PosDefM {n : ℕ} (A : MatC n) : Prop := Matrix.PosDef (reMat A)

/-- Componentwise coordinate derivative of a matrix-valued function. -/
def pdM {n : ℕ} (c : Fin n) (u : Torus n) : Torus n :=
  fun x i j => pd c (fun y => u y i j) x

/-- The spatial `2`-jet of a matrix-valued function. -/
def jetM {n : ℕ} (u : Torus n) : (Fin n → ℝ) → Jet n :=
  fun x => (u x, fun c => pdM c u x, fun c d => pdM c (pdM d u) x)

/-- **The scalar principal part** of the DeTurck operator in flat coordinates.  The coefficient is
the inverse of the *real part* of the metric matrix, so that it is a real function of `x` and
Gårding's ellipticity hypothesis applies. -/
def secOpFlat {n : ℕ} (A : MatC n) (B : Fin n → Fin n → MatC n) : MatC n :=
  fun i j => ∑ c, ∑ d, (((reMat A)⁻¹) c d : ℂ) * B c d i j

/-- The DeTurck shape of the nonlinearity: a scalar principal part plus a smooth lower-order term
depending on the value and the first jet only.

The smoothness is required only on the set where the metric matrix is nondegenerate: Mathlib's
matrix inverse is (Cramer's rule) `(det A)⁻¹ • A.adjugate` with the value `0` at singular matrices,
so it is *discontinuous* at singular `A` with nonvanishing adjugate, and `secOpFlat` is smooth
exactly on `{det (reMat A) ≠ 0}` (compare `Work.Diff.STE.deTurck.pPhiDom` and
`Work.Diff.STE.deTurck.contDiffOn_pPhi`). -/
def IsDeTurckNonlin {n : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) Φ (Set.univ ×ˢ {w : Jet n | (reMat w.1).det ≠ 0}) ∧
    ∃ N : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n,
      ContDiffOn ℝ (⊤ : ℕ∞) N
          (Set.univ ×ˢ {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) ∧
        (∀ (x : Fin n → ℝ) (A : MatC n) (L : Fin n → MatC n) (B : Fin n → Fin n → MatC n),
          (reMat A).det ≠ 0 → Φ (x, (A, L, B)) = secOpFlat A B + N (x, (A, L))) ∧
        (∀ w : MatC n × (Fin n → MatC n), Periodic1 (fun x : Fin n → ℝ => N (x, w)))

/-- Conjugation equivariance of the nonlinearity.  Together with reality of the initial datum this
forces the solution to be real (via uniqueness). -/
def ConjEquivNonlin {n : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n) : Prop :=
  ∀ x A L B,
    Φ (x, (conjMat A, (fun c => conjMat (L c)), (fun c d => conjMat (B c d))))
      = conjMat (Φ (x, (A, L, B)))

/-- The matrix-valued Fourier series of a coefficient family. -/
def seriesFunM {n : ℕ} (c : (Fin n → ℤ) → MatC n) : Torus n :=
  fun x i j => seriesFun (fun m => c m i j) x

@[simp] lemma seriesFunM_apply {n : ℕ} (c : (Fin n → ℤ) → MatC n) (x : Fin n → ℝ)
    (i j : Fin n) : seriesFunM c x i j = seriesFun (fun m => c m i j) x := rfl

/-- The entrywise Fourier coefficients of a matrix-valued function. -/
def fourierCoeffM {n : ℕ} (u : Torus n) : (Fin n → ℤ) → MatC n :=
  fun k i j => fourierCoeff (fun x => u x i j) k

@[simp] lemma fourierCoeffM_apply {n : ℕ} (u : Torus n) (k : Fin n → ℤ) (i j : Fin n) :
    fourierCoeffM u k i j = fourierCoeff (fun x => u x i j) k := rfl

/-- The `L²` pairing of matrix-valued functions. -/
def L2reM {n : ℕ} (f g : Torus n) : ℝ := ∑ i : Fin n, ∑ j : Fin n, L2re (fun x => f x i j)
  (fun x => g x i j)

/-- **The flat Cauchy problem.** `u` solves the DeTurck system driven by `Φ` on `[0, T)` if `u` is
jointly `C^∞` on `Ico 0 T × univ` (in the sense of `ContDiffOn` on that non-open set, as in
`Submission.Diff.JointSmooth`), `1`-periodic in `x` at every time, and satisfies the pointwise
equation `∂_t u(t,x) = Φ (x, jets of u(t,·) at x)` on `[0, T)`. -/
def SolvesOn {n : ℕ} (Φ : (Fin n → ℝ) × Jet n → MatC n) (T : ℝ) (u : ℝ → Torus n) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0 : ℝ) T ×ˢ Set.univ) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, Periodic1 (u t)) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : Fin n → ℝ,
      HasDerivWithinAt (fun s => u s x) (Φ (x, jetM (u t) x)) (Set.Ico (0 : ℝ) T) t)

/-- **The flat short-time existence theorem** (the analytic core of the DeTurck trick, flat case).
For a nonlinearity of DeTurck shape which is conjugation-equivariant, and a smooth `1`-periodic
positive definite real initial datum, there are `T > 0` and a smooth `1`-periodic real positive
definite solution on `[0, T)`. -/
def TorusShortTimeExistence (n : ℕ) : Prop :=
  ∀ Φ : (Fin n → ℝ) × Jet n → MatC n, IsDeTurckNonlin Φ → ConjEquivNonlin Φ →
    ∀ u₀ : Torus n, ContDiff ℝ (⊤ : ℕ∞) u₀ → Periodic1 u₀ →
      (∀ x i j, (u₀ x i j).im = 0) → (∀ x, PosDefM (u₀ x)) →
      ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → Torus n, SolvesOn Φ T u ∧ u 0 = u₀ ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x, PosDefM (u t x)) ∧
        (∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x i j, (u t x i j).im = 0)

/-! ## The Galerkin (partial Fourier sum) truncation -/

/-- The finite set of frequencies of the Galerkin approximation at order `N`. -/
def box (n N : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(N : ℤ)) N)

/-- The projection onto the frequencies in `box n N`. -/
def projBox {n : ℕ} {α : Type*} [Zero α] (N : ℕ) (c : (Fin n → ℤ) → α) : (Fin n → ℤ) → α :=
  fun k => if k ∈ box n N then c k else 0

@[simp] lemma projBox_apply_of_mem {n : ℕ} {α : Type*} [Zero α] (N : ℕ) (c : (Fin n → ℤ) → α)
    {k : Fin n → ℤ} (hk : k ∈ box n N) : projBox N c k = c k := by
  simp [projBox, hk]

@[simp] lemma projBox_apply_of_not_mem {n : ℕ} {α : Type*} [Zero α] (N : ℕ)
    (c : (Fin n → ℤ) → α)
    {k : Fin n → ℤ} (hk : k ∉ box n N) : projBox N c k = 0 := by
  simp [projBox, hk]

lemma projBox_idem {n : ℕ} {α : Type*} [Zero α] (N : ℕ) (c : (Fin n → ℤ) → α) :
    projBox N (projBox N c) = projBox N c := by
  funext k
  by_cases hk : k ∈ box n N
  · simp [projBox, hk]
  · simp [projBox, hk]

/-- The matrix energy at level `k` of a matrix-valued function: the sum over the entries of the
`H^k` energy of `L²`-norm-squared type. -/
def ENormSqM {n : ℕ} (k : ℕ) (u : Torus n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ENormSq k (fun x => u x i j)

/-- The full (inhomogeneous) matrix energy: the top-order seminorm plus the `L²` norm.  Note that
`ENormSq k` is the *homogeneous* top-order seminorm (it sums over multi-indices of length exactly
`k`), so it carries no information on the size of `u`; every a priori estimate must control
`ENormSqFull k u = ENormSqM k u + ENormSqM 0 u` instead. -/
def ENormSqFull {n : ℕ} (k : ℕ) (u : Torus n) : ℝ := ENormSqM k u + ENormSqM 0 u

/-- The squared `H^k` norm of a coefficient family of matrices. -/
def CSqM {n : ℕ} (k : ℕ) (c : (Fin n → ℤ) → MatC n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, CSq k (fun m => c m i j)

end

end Flat

end Work.Diff.STE
