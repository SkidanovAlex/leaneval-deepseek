/-
# The tame transport of the DeTurck operator: definitions

This module fixes the vocabulary of `Work.Diff.STE.B3.transport_deTurck_tame`, the *L²-tame* form of
the transport statement (as opposed to the pointwise form `transport_deTurck_general`).

Given the B3 data `D`, a chart index `j` and a section `h`, the transport identity reads

`D.R j (P h) a b z = Σ_{pq} A z p q · ∂_p∂_q (D.R j h a b) z + Ψ (z, M z, ∂M z) a b`

on the closed `2σ j`-ball, where `M z = D.mat j h · · z` is the `g₀`-orthonormal-frame chart matrix
of `h` and `∂M` its first jet.  The scalar principal part is the inverse of the coordinate-frame
chart matrix of `h` (frame change: `Gf = Finvf · Mf · Finvfᵀ`, `Work.Diff.STE.B3.Gf_eq_dual`), and
the residual is an explicit smooth function of `(z, M, ∂M)`.

The definitions below are all *nominal*: they are functions of a point `z` and of the values
`V` (the ON-frame chart matrix) and `W` (its first jet), so that the composite
`tmPsi j z (Mf z) (∂Mf z)` is the residual of the transport identity, while `tmPsi` itself is a
smooth function of its three arguments.

The pieces:

* `tmClampBump`, `tmInv` — a smooth *clamped* matrix inverse (the honest inverse on a window of
  determinant values, the identity matrix far from the window);
* `tmGK`, `tmGKi` — the nominal coordinate-frame chart matrix and its clamped inverse;
* `tmDFin`, `tmDGK`, `tmDGKclm` — the derivative of the frame inverse, the nominal first jet of the
  coordinate chart matrix (as a function of `(z, V, W)`) and its continuous-linear-map form (the
  argument of `pN`);
* `tmEight` — the nominal version of the eight lower-order terms of the Leibniz rule
  `Work.Diff.STE.B3.eightTerm`;
* `tmPsi` — the residual `Ψ`;
* `tmPer`, `tmA` — the periodisation of a compactly supported real function and the construction of
  the periodic coefficient matrix `A`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.D.psi.Basic
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. A smoothly clamped matrix inverse -/

/-- The smooth bump used to clamp the matrix inverse: it is `1` on the closed ball of radius
`(b-a)/2` around `(a+b)/2` (so on `[a,b]`) and vanishes outside the ball of radius `b/2` (so away
from `(a/2, b)`). -/
def tmClampBump {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b) : ℝ → ℝ :=
  fun t => (⟨(b - a) / 2, b / 2, by linarith, by linarith⟩ : ContDiffBump ((a + b) / 2)) t

/-- The **clamped inverse** of a matrix: the honest inverse when `det A ∈ [a, b]`, the identity
matrix when `det A` is far from `[a, b]`, interpolated smoothly.  The formula has no junk (the
clamp vanishes near `det = 0`), so it is a smooth function of the matrix entries. -/
def tmInv {n : ℕ} (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (tmClampBump (n := n) a b ha hab A.det) • A⁻¹
    + (1 - tmClampBump (n := n) a b ha hab A.det) • (1 : Matrix (Fin n) (Fin n) ℝ)

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)

/-! ## 2. The nominal coordinate-frame chart matrix and its jet -/

/-- The **nominal coordinate-frame chart matrix**: the coordinate chart matrix of a section whose
ON-frame chart matrix is `V`.  It is the frame-change formula `Gf = Finvf · Mf · Finvfᵀ`
(`Work.Diff.STE.B3.Gf_eq_dual`) with `Mf` replaced by the variable `V`. -/
def tmGK (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (Finvf (I := I) (M := M) D j z) * Matrix.of V
    * (Matrix.of (Finvf (I := I) (M := M) D j z))ᵀ

/-- The clamped inverse of the nominal coordinate chart matrix. -/
def tmGKi (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  tmInv a b ha hab (tmGK (I := I) (M := M) D j z V)

/-- The first derivative of the frame inverse `Finvf`, as a function of `z`. -/
def tmDFin (z : Fin (Module.finrank ℝ E) → ℝ) (c i a : Fin (Module.finrank ℝ E)) : ℝ :=
  Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ => Finvf (I := I) (M := M) D j y i a) z

/-- **The nominal first jet of the coordinate chart matrix**: the derivative `∂_c` of
`tmGK z V`, expressed in terms of the jet `W` of the ON-frame chart matrix.  Since
`Gf_{ik} = Σ_{ab} Finvf_{ia} Mf_{ab} Finvf_{kb}`, the product rule gives three terms: the derivative
of the frame inverse (a fixed function of `z`), the jet `W` of the chart matrix, and the derivative
of the second frame inverse. -/
def tmDGK (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (c i k : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
    (tmDFin (I := I) (M := M) D j z c i a * V a b * Finvf (I := I) (M := M) D j z k b
      + Finvf (I := I) (M := M) D j z i a * W a b c * Finvf (I := I) (M := M) D j z k b
      + Finvf (I := I) (M := M) D j z i a * V a b * tmDFin (I := I) (M := M) D j z c k b)

/-- The nominal first jet of the coordinate chart matrix, as the continuous linear map
`E →L[ℝ] MatE` which `pN` expects: its value on the basis vector `bB c` is `∂_c Gf`. -/
def tmDGKclm (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    E →L[ℝ] Work.Diff.EXT.MatE (E := E) :=
  ∑ c : Fin (Module.finrank ℝ E),
    (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight
      (Matrix.of (fun i k => tmDGK (I := I) (M := M) D j z V W c i k))

/-! ## 3. The nominal eight-term correction -/

/-- **The nominal eight terms**: the lower-order terms of the Leibniz rule for the triple product
`Gf = Finvf · V · Finvfᵀ`, i.e. the version of `Work.Diff.STE.B3.eightTerm` in which the coordinate
chart matrix and its first jet are replaced by the nominal `tmGK z V` and `tmDGK z V W`. -/
def tmEight (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (c d a b : Fin (Module.finrank ℝ E)) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    ( Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Ff (I := I) (M := M) D j y a i)) z
        * tmGK (I := I) (M := M) D j z V i k * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Ff (I := I) (M := M) D j y a i) z
        * tmDGK (I := I) (M := M) D j z V W d i k * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Ff (I := I) (M := M) D j y a i) z
        * tmGK (I := I) (M := M) D j z V i k
        * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Ff (I := I) (M := M) D j y b k) z
      + Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Ff (I := I) (M := M) D j y a i) z
        * tmDGK (I := I) (M := M) D j z V W c i k * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Ff (I := I) (M := M) D j y a i) z
        * tmGK (I := I) (M := M) D j z V i k
        * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i * tmDGK (I := I) (M := M) D j z V W c i k
        * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i * tmDGK (I := I) (M := M) D j z V W d i k
        * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i * tmGK (I := I) (M := M) D j z V i k
        * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Ff (I := I) (M := M) D j y b k)) z )

/-! ## 4. The residual `Ψ` -/

/-- **The residual `Ψ` of the transport identity** as a function of `(z, V, W)`: the part of
`D.R j (P h)` that is not of the form `A ∂∂ (D.R j h)` on the `2σ j`-ball.  It collects

* the terms produced by differentiating the localised weight `wf = ψ j · √dens j` twice;
* the eight-term correction `tmEight` of the Leibniz rule;
* the lower-order part `pN` of the DeTurck operator, in the ON frame.

Its composite `tmPsi z (Mf z) (∂Mf z)` is the residual of the transport identity. -/
def tmPsi (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (a' b' : Fin (Module.finrank ℝ E)) : ℝ :=
  - (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
      tmGKi (I := I) (M := M) D j a b ha hab z V c d
        * (Work.Diff.STE.pdR c (wf (I := I) (M := M) D j) z * W a' b' d
            + Work.Diff.STE.pdR d (wf (I := I) (M := M) D j) z * W a' b' c
            + Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (wf (I := I) (M := M) D j)) z
              * V a' b'))
    - wf (I := I) (M := M) D j z
        * (∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            tmGKi (I := I) (M := M) D j a b ha hab z V c d
              * tmEight (I := I) (M := M) D j z V W c d a' b')
    + wf (I := I) (M := M) D j z
        * (∑ i : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
            Ff (I := I) (M := M) D j z a' i * Ff (I := I) (M := M) D j z b' k
              * (Work.Diff.STE.DeTurck.pN
                  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j) (yf (I := I) (M := M) D j z)).1
                  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j) (yf (I := I) (M := M) D j z)).2.1
                  (Work.Diff.STE.D.chartJetOf (I := I) (M := M) g₀.inner (D.x₀ j) (yf (I := I) (M := M) D j z)).2.2
                  (Matrix.of (tmGK (I := I) (M := M) D j z V))
                  (tmDGKclm (I := I) (M := M) D j z V W) i k))

/-! ## 5. The local coefficient family `γ` -/

/-- The **local coefficient family** of the transport identity: the inverse of the coordinate-frame
chart matrix of `h`, computed from the ON-frame chart matrix `Mf` through the clamped inverse of the
nominal coordinate chart matrix.  This is the coefficient matrix `A` of the transport identity
before the periodisation of Section 6. -/
def tmGamma (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (z : Fin (Module.finrank ℝ E) → ℝ)
    (p q : Fin (Module.finrank ℝ E)) : ℝ :=
  tmGKi (I := I) (M := M) D j a b ha hab z (fun p q => D.mat j h p q z) p q

/-! ## 6. The periodic coefficient matrix `A` -/

/-- The **real periodisation** of a compactly supported smooth function: the real part of the
periodisation of its complexification, so that the Fourier/periodisation lemmas of
`Work.Diff.STE.periodization_contDiff_periodic` apply. -/
def tmPer {n : ℕ} (f : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ :=
  fun z => (∑' m : Fin n → ℤ, ((f (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)).re

/-- **The periodic coefficient matrix** built from a local coefficient family `γ` and a cutoff `φ`:
`A = λ' · 1 + per (φ · (γ - λ' · 1))`.  On the set where `φ = 1` (and outside the fundamental
cube no translate contributes) this is `γ` itself; globally it is smooth and `1`-periodic. -/
def tmA {n : ℕ} (φ : (Fin n → ℝ) → ℝ) (lam' : ℝ) (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) :
    (Fin n → ℝ) → Fin n → Fin n → ℝ :=
  fun z p q =>
    (if p = q then lam' else 0)
      + tmPer (fun w => φ w * (γ w p q - (if p = q then lam' else 0))) z

end Work.Diff.STE.B3
