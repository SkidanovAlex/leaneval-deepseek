/-
# The **nominal residual** of the transport identity

This module fixes the vocabulary used by `Work.Diff.STE.B3.transport_low_jet_bound_uniform`.

`Work.Diff.STE.B3.residualLow` (`B3/TransportDefs.lean`) is the lower-order residual of the
transport identity, written as an explicit function of the *chart matrices* of the section `h`:
the orthonormal-frame chart matrix `Mf` of `h`, the coordinate-frame chart matrix `Gf` of `h` and
their first derivatives, together with the (fixed, `h`-independent) B3 data.

The point of this file is that the residual is a **smooth function of the flat coordinate `z` and
of the two matrices and their first jets**, i.e.

`residualLow D h j z a b = body D j z (Gf z) (∂Gf z) (Mf z) (∂Mf z) a b`,

where

* `body D j z G dG V dV a b` is the *nominal* expression (a copy of the body of `residualLow` with
  the chart matrices and their jets as variables);
* `nG D j z V` is the **nominal coordinate-frame chart matrix**: the frame-change formula
  `Gf = Finvf · Mf · Finvfᵀ` (`Work.Diff.STE.B3.Gf_eq_dual`) with `Mf` replaced by the variable `V`;
* `nDGc D j z V dV` is the **nominal first jet** of `nG D j z V`, expressed through the jet `dV` of
  `V` and the (fixed) derivative of the frame inverse;
* `clmOf dG` turns a family `dG : Fin n → MatE` of coordinate derivatives into the continuous
  linear map `E →L[ℝ] MatE` on which `Work.Diff.STE.DeTurck.pN` is evaluated;
* `nEight` is the nominal version of the eight lower-order terms `Work.Diff.STE.B3.eightTerm`.

Finally `nres D j z V dV a b := body D j z (nG D j z V) (nDGc D j z V dV) V dV a b` is the
**nominal residual**: the residual as a function of `(z, Mf z, ∂Mf z)` only, so that the whole
`h`-dependence enters through the orthonormal-frame chart matrix and its first jet.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

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

noncomputable section

/-- The index type of all component computations. -/
local notation "Idx" => Fin (Module.finrank ℝ E)

/-- **From a family of coordinate derivatives to a continuous linear map.**  If
`dG : Fin n → MatE` is the family `c ↦ ∂_c (something)`, then `clmOf dG : E →L[ℝ] MatE` is the
unique continuous linear map whose value on the basis vector `bB c` is `Matrix.of (dG c)`.  This is
the form in which the first jet of a chart matrix is passed to `Work.Diff.STE.DeTurck.pN`. -/
def clmOf (dG : Idx → Work.Diff.EXT.MatE (E := E)) :
    E →L[ℝ] Work.Diff.EXT.MatE (E := E) :=
  ∑ c : Idx,
    (((Work.Diff.EXT.bB (E := E)).coord c).toContinuousLinearMap).smulRight (dG c)

/-- `clmOf` evaluated on a basis vector: `clmOf dG (bB c) = dG c`. -/
lemma clmOf_bB (dG : Idx → Work.Diff.EXT.MatE (E := E)) (c : Idx) :
    clmOf (E := E) dG (Work.Diff.EXT.bB (E := E) c) = dG c := by
  classical
  have hcoord : ∀ c' : Idx,
      (LinearMap.toContinuousLinearMap ((Work.Diff.EXT.bB (E := E)).coord c'))
        (Work.Diff.EXT.bB (E := E) c) = if c' = c then 1 else 0 := by
    intro c'
    rw [show (LinearMap.toContinuousLinearMap ((Work.Diff.EXT.bB (E := E)).coord c'))
        (Work.Diff.EXT.bB (E := E) c)
        = ((Work.Diff.EXT.bB (E := E)).coord c') (Work.Diff.EXT.bB (E := E) c) from rfl]
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : c = c'
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  simp only [clmOf, sum_apply, ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc'
    rw [hcoord c', if_neg hc', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- **The nominal coordinate-frame chart matrix**: the frame-change formula `Gf = Finvf · Mf · Finvfᵀ`
(`Work.Diff.STE.B3.Gf_eq_dual`) with the orthonormal-frame chart matrix replaced by the variable
`V`.  It is a polynomial (indeed bilinear) function of `V` with coefficients the (fixed) entries of
the frame inverse. -/
def nG (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) (V : Idx → Idx → ℝ) : Idx → Idx → ℝ :=
  fun i k => ∑ a : Idx, ∑ b : Idx,
    Finvf (I := I) (M := M) D j z i a * V a b * Finvf (I := I) (M := M) D j z k b

@[simp] lemma nG_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) (V : Idx → Idx → ℝ) (i k : Idx) :
    nG (I := I) (M := M) D j z V i k
      = ∑ a : Idx, ∑ b : Idx,
        Finvf (I := I) (M := M) D j z i a * V a b * Finvf (I := I) (M := M) D j z k b := rfl

/-- **The nominal first jet of the nominal coordinate-frame chart matrix**, i.e. `∂_c (nG z V)`
computed through the product rule, with the derivative of `V` supplied by the variable `dV` and the
derivative of the (fixed) frame inverse supplied by the data `D`. -/
def nDGc (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) (V : Idx → Idx → ℝ) (dV : Idx → Idx → Idx → ℝ) :
    Idx → Idx → Idx → ℝ :=
  fun c i k => ∑ a : Idx, ∑ b : Idx,
    ( Work.Diff.STE.pdR c (fun y : Idx → ℝ => Finvf (I := I) (M := M) D j y i a) z
        * V a b * Finvf (I := I) (M := M) D j z k b
      + Finvf (I := I) (M := M) D j z i a * dV c a b * Finvf (I := I) (M := M) D j z k b
      + Finvf (I := I) (M := M) D j z i a * V a b
        * Work.Diff.STE.pdR c (fun y : Idx → ℝ => Finvf (I := I) (M := M) D j y k b) z )

/-- **The nominal eight-term correction**: `Work.Diff.STE.B3.eightTerm` with the coordinate-frame
chart matrix `Gf` and its first jet replaced by the nominal `nG z V` and `nDGc z V dV`. -/
def nEight (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) (G : Idx → Idx → ℝ) (dG : Idx → Idx → Idx → ℝ) (c d a b : Idx) : ℝ :=
  ∑ i : Idx, ∑ k : Idx,
    ( Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
          (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y a i)) z * G i k
        * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR c (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y a i) z
        * dG d i k * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR c (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y a i) z
        * G i k
        * Work.Diff.STE.pdR d (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y b k) z
      + Work.Diff.STE.pdR d (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y a i) z
        * dG c i k * Ff (I := I) (M := M) D j z b k
      + Work.Diff.STE.pdR d (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y a i) z
        * G i k
        * Work.Diff.STE.pdR c (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i * dG c i k
        * Work.Diff.STE.pdR d (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i * dG d i k
        * Work.Diff.STE.pdR c (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y b k) z
      + Ff (I := I) (M := M) D j z a i * G i k
        * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
            (fun y : Idx → ℝ => Ff (I := I) (M := M) D j y b k)) z )

/-- **The body of the residual** as a function of the two chart matrices `G` (coordinate frame)
and `V` (orthonormal frame) and of their first jets `dG`, `dV`.  This is the exact body of
`Work.Diff.STE.B3.residualLow`, with the chart matrices and their jets as variables. -/
def body (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (z : Idx → ℝ)
    (G : Idx → Idx → ℝ) (dG : Idx → Idx → Idx → ℝ) (V : Idx → Idx → ℝ)
    (dV : Idx → Idx → Idx → ℝ) (a b : Idx) : ℝ :=
    wf (I := I) (M := M) D j z
        * (∑ i : Idx, ∑ k : Idx, Work.Diff.STE.DeTurck.pN
            (Jets0 (I := I) (M := M) D j z).1 (Jets0 (I := I) (M := M) D j z).2.1
            (Jets0 (I := I) (M := M) D j z).2.2
            (Matrix.of G) (clmOf (E := E) dG) i k
            * (Ff (I := I) (M := M) D j z a i * Ff (I := I) (M := M) D j z b k))
  - wf (I := I) (M := M) D j z
      * ∑ p : Idx, ∑ q : Idx,
          ((Matrix.of (G : Idx → Idx → ℝ))⁻¹) p q
            * nEight (I := I) (M := M) D j z G dG p q a b
  - ∑ p : Idx, ∑ q : Idx,
      ((Matrix.of (G : Idx → Idx → ℝ))⁻¹) p q
        * (2 * Work.Diff.STE.pdR p (wf (I := I) (M := M) D j) z * dV q a b
          + V a b * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (wf (I := I) (M := M) D j)) z)

/-- **The nominal residual**: the residual `Work.Diff.STE.B3.residualLow` as a function of the flat
coordinate `z`, of the orthonormal-frame chart matrix `V` of the section and of its first jet `dV`.
The coordinate-frame chart matrix and its first jet are reconstructed by `nG` resp. `nDGc`. -/
def nres (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (z : Idx → ℝ)
    (V : Idx → Idx → ℝ) (dV : Idx → Idx → Idx → ℝ) (a b : Idx) : ℝ :=
  body (I := I) (M := M) D j z (nG (I := I) (M := M) D j z V)
    (nDGc (I := I) (M := M) D j z V dV) V dV a b

@[simp] lemma nres_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (z : Idx → ℝ) (V : Idx → Idx → ℝ) (dV : Idx → Idx → Idx → ℝ) (a b : Idx) :
    nres (I := I) (M := M) D j z V dV a b
      = body (I := I) (M := M) D j z (nG (I := I) (M := M) D j z V)
          (nDGc (I := I) (M := M) D j z V dV) V dV a b := rfl

/-- The first jet of the coordinate-frame chart matrix of a section, as a family of matrices. -/
def dGf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (z : Idx → ℝ) :
    Idx → Idx → Idx → ℝ :=
  fun c i k => Work.Diff.STE.pdR c (fun y : Idx → ℝ => Gf (I := I) (M := M) D h j y i k) z

/-- The first jet of the orthonormal-frame chart matrix of a section, as a family of matrices. -/
def dMf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀) (z : Idx → ℝ) :
    Idx → Idx → Idx → ℝ :=
  fun c a b => Work.Diff.STE.pdR c (fun y : Idx → ℝ => Mf (I := I) (M := M) D h j y a b) z

/-- The open set of *admissible values of the state* `(z, Mf z, ∂Mf z)`: the flat coordinate lies
in the chart **target** (the region on which the chart inverse `pt j`, the frame matrix `Ff` and
the coordinate-frame chart matrix `Gf` are smooth; membership in the chart *source* alone does not
suffice, since the inverse chart map is junk off the target), the frame matrix `Ff` is invertible
there, and the orthonormal-frame chart matrix itself is invertible. -/
def lowJetDom (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    Set ((Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) :=
  {p | Work.Diff.STE.flatToE (I := I) (D.x₀ j) p.1 ∈ (extChartAt I (D.x₀ j)).target ∧
    (Matrix.of (Ff (I := I) (M := M) D j p.1)).det ≠ 0 ∧ (Matrix.of p.2.1).det ≠ 0}

/-- The compact set of *admissible bounded states*: the flat coordinate lies in the closed `2σ`
ball, the orthonormal-frame chart matrix is symmetric, `λ`-elliptic and entrywise bounded by `K`,
and its first jet is entrywise bounded by `K`. -/
def lowJetBall (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (lam K : ℝ) :
    Set ((Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) :=
  {p | ‖p.1‖ ≤ 2 * D.σ j ∧ (∀ a b, p.2.1 a b = p.2.1 b a) ∧
    (∀ x : Idx → ℝ, lam * ‖x‖ ^ 2 ≤ ∑ a : Idx, ∑ b : Idx, x a * p.2.1 a b * x b) ∧
    (∀ a b, |p.2.1 a b| ≤ K) ∧ (∀ c a b, |p.2.2 c a b| ≤ K)}

/-- The value of the nominal residual, complexified. -/
def nresC (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (a b : Idx)
    (p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) : ℂ :=
  ((nres (I := I) (M := M) D j p.1 p.2.1 p.2.2 a b : ℝ) : ℂ)

@[simp] lemma nresC_apply (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (a b : Idx)
    (p : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ)) :
    nresC (I := I) (M := M) D j a b p
      = ((nres (I := I) (M := M) D j p.1 p.2.1 p.2.2 a b : ℝ) : ℂ) := rfl

end

end Work.Diff.STE.B3
