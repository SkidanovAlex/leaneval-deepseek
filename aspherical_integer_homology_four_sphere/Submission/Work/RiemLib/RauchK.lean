import Submission.Work.RiemLib.RauchGlobal
import Submission.Work.RiemLib.ConjRadius
import Submission.Work.RiemLib.CutPoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Rauch's conjugate-radius theorem for an arbitrary upper curvature bound

`Submission/RauchGlobal.eqOn_zero_of_jacobi` proves Rauch's theorem — *no conjugate point before
`π/2`* — in the project's fixed normalisation `sec ≤ 4`.  Everything in that chain (`Rauch.lean`,
`RauchLocal.lean`, `RauchGlobal.lean`) is *hard-wired* to the constant `4`, through
`chartGram_chartCurv_le` (which uses the `≤ 4` half of `QuarterPinched`).

For the Klingenberg estimate in the form needed by the sphere theorem one needs the **strict**
bound `conj ≥ π/√K` for an upper curvature bound `K < 4` (the rescaling of the pinched metric lands
in `sec ∈ (1, 4/c]`, and `π/√(4/c) > π/2` is what makes the diameter estimate strict).  This file
provides the parametric version: the whole chain is repeated with the constant `4` replaced by an
arbitrary `K > 0`, and with the *upper* curvature bound isolated in a pointwise predicate
`CurvLe cov K` (no lower curvature bound is needed for the conjugate radius bound — Rauch's theorem
is a one-sided comparison).

## Contents

* `CurvLe cov K`: the pointwise sectional curvature bound `sec ≤ K`;
* `sectionalCurvature_le_of_curvLe`, `curvFormVec_le_mul_of_curvLe`,
  `chartGram_chartCurv_le_of_curvLe`: the bound in the chart form used by the Rauch inequality;
* `rauch_inequality_of_hasDerivAt_of_curvLe`, `rauch_sturm_ready_of_hasDerivAt_of_curvLe`,
  `sturm_data_at_of_curvLe`: the Sturm data `(‖J‖)'' + K ‖J‖ ≥ 0`;
* **`eqOn_zero_of_jacobi_of_curvLe`**: Rauch's theorem with the bound `π/√K`;
* **`pi_div_sqrt_le_of_isConjugateTime`**: the conjugate radius is at least `π/√K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.ChartBounds
open Submission.RauchLocal
open Submission.RauchGlobal
open Commons.Analysis.ODE
open Submission.JacobiTensor
open Submission.GeodesicSpeed
open Submission.CutPoint
open Submission.ConjPoint
open Submission.RauchSpeed
open Submission.BonnetMyers
open Submission.Minimal
open scoped ENNReal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.RauchK

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable {K : ℝ}
variable [Nontrivial E] [CompactSpace M]
variable [ContMDiffCovariantDerivative cov ∞]

open Classical in
attribute [local instance] Classical.propDecidable

/-- The tangent space at a point, as a finite-dimensional real vector space (the instance of `E` is
not found for `TangentSpace I x` because of the `def`-unfolding barrier). -/
local instance instFDTangent (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

/-! ## 1. The pointwise upper curvature bound -/

/-- **The pointwise sectional curvature bound `sec ≤ K`.**  The curvature of every tangent plane
spanned by an orthonormal pair `(u,v)` is at most `K`.  This is the *upper* half of
`QuarterPinched`, isolated so that the comparison theorems become parametric in the bound. -/
def CurvLe (cov : CovariantDerivative I E (TangentSpace I (M := M))) (K : ℝ) : Prop :=
  ∀ (x : M) (u v : TangentSpace I x), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
    inner ℝ (curvVec cov x u v v) u ≤ K

/-- The curvature form is the inner product of `R(u,v)v` with `u` (restated here to avoid an
import cycle with `Submission.Rauch`). -/


lemma curvFormVec_eq_inner_curvVec'
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v : TangentSpace I x) :
    curvFormVec cov x u v = inner ℝ (curvVec cov x u v v) u :=
  (inner_curvVec_self cov hcov x u v).symm

/-- A basis of a `2`-dimensional submodule spans it as a subspace of the ambient space
(local copy of the private lemma in `Submission.Curvature`). -/
private lemma span_basis_pair_eq' (x : M) (σ : Submodule ℝ (TangentSpace I x))
    (b : Module.Basis (Fin 2) ℝ σ) :
    Submodule.span ℝ ({(b 0 : TangentSpace I x), (b 1 : TangentSpace I x)} : Set (TangentSpace I x)) = σ := by
  have hrange : Set.range b = ({b 0, b 1} : Set σ) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · exact ⟨1, hz.symm⟩
  have himg : σ.subtype '' Set.range b = ({↑(b 0), ↑(b 1)} : Set (TangentSpace I x)) := by
    rw [hrange]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (congrArg Subtype.val hw)
      · exact Or.inr (congrArg Subtype.val hw)
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨b 0, by simp, hz.symm⟩
      · exact ⟨b 1, by simp, hz.symm⟩
  calc Submodule.span ℝ ({↑(b 0), ↑(b 1)} : Set (TangentSpace I x))
      = Submodule.span ℝ (σ.subtype '' Set.range b) := by rw [himg]
    _ = Submodule.map σ.subtype (Submodule.span ℝ (Set.range b)) := by rw [Submodule.map_span]
    _ = Submodule.map σ.subtype ⊤ := by rw [b.span_eq]
    _ = σ := Submodule.map_subtype_top σ

/-- **The sectional curvature bound in the form of a submodule bound.** -/
theorem sectionalCurvature_le_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) {x : M}
    (σ : Submodule ℝ (TangentSpace I x)) (hσ : Module.finrank ℝ σ = 2) :
    sectionalCurvature cov x σ hσ ≤ K := by
  set e := (stdOrthonormalBasis ℝ σ).reindex (finCongr hσ) with he
  have hee : ∀ i j : Fin 2,
      inner ℝ ((e i : σ) : TangentSpace I x) ((e j : σ) : TangentSpace I x)
        = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have h := (orthonormal_iff_ite.mp e.orthonormal) i j
    simpa [Submodule.coe_inner] using h
  obtain ⟨X, hX, hXx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M)
      ((e 0 : σ) : TangentSpace I x)
  obtain ⟨Y, hY, hYx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M)
      ((e 1 : σ) : TangentSpace I x)
  have h00 : ‖((e 0 : σ) : TangentSpace I x)‖ = 1 := by
    rw [← Submodule.coe_norm]
    exact e.orthonormal.norm_eq_one 0
  have h11 : ‖((e 1 : σ) : TangentSpace I x)‖ = 1 := by
    rw [← Submodule.coe_norm]
    exact e.orthonormal.norm_eq_one 1
  have h01 : inner ℝ ((e 0 : σ) : TangentSpace I x) ((e 1 : σ) : TangentSpace I x) = 0 := by
    simpa using hee 0 1
  have hpin := hK x ((e 0 : σ) : TangentSpace I x) ((e 1 : σ) : TangentSpace I x) h00 h11 h01
  have hgram : gramFormVec x ((e 0 : σ) : TangentSpace I x) ((e 1 : σ) : TangentSpace I x) = 1 := by
    unfold gramFormVec
    rw [h00, h11, h01]
    norm_num
  have hspan : Submodule.span ℝ
      ({((e 0 : σ) : TangentSpace I x), ((e 1 : σ) : TangentSpace I x)} : Set (TangentSpace I x))
      = σ := by
    simpa using span_basis_pair_eq' x σ e.toBasis
  have hG : gramFormVec x ((e 0 : σ) : TangentSpace I x) ((e 1 : σ) : TangentSpace I x) ≠ 0 := by
    rw [hgram]; exact one_ne_zero
  have hK' : sectionalCurvature cov x σ hσ = curvForm cov X Y x := by
    rw [sectionalCurvature_eq_ratio cov hcov hmet σ hσ hspan hG]
    rw [curvFormVec_eq cov hcov hX hY hXx hYx, hgram, div_one]
  rw [← hXx, ← hYx] at hpin
  rw [hK', ← curvFormVec_eq (cov := cov) hcov hX hY (u := X x) (v := Y x) rfl rfl]
  rw [curvFormVec_eq_inner_curvVec' (cov := cov) hcov x (X x) (Y x)]
  exact hpin

/-- **The upper curvature bound for a non-degenerate pair**, in the form used by the Rauch
inequality: `⟪R(X,Y)Y, X⟫ ≤ K · gram(X,Y)`. -/
theorem curvForm_le_mul_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K)
    {X Y : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    {x : M} (hG : gramFormVec x (X x) (Y x) ≠ 0) :
    curvForm cov X Y x ≤ K * gramFormVec x (X x) (Y x) := by
  have hind : LinearIndependent ℝ ![X x, Y x] := linearIndependent_of_gramFormVec_ne_zero hG
  have hrange : Set.range (fun i : Fin 2 => ![X x, Y x] i)
      = ({X x, Y x} : Set (TangentSpace I x)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · exact ⟨1, hz.symm⟩
  have hσ : Module.finrank ℝ (Submodule.span ℝ ({X x, Y x} : Set (TangentSpace I x))) = 2 := by
    have hcard := finrank_span_eq_card hind
    rw [hrange] at hcard
    simpa using hcard
  have hhi := sectionalCurvature_le_of_curvLe (cov := cov) hcov hmet hK
    (Submodule.span ℝ ({X x, Y x} : Set (TangentSpace I x))) hσ
  have hK' : sectionalCurvature cov x (Submodule.span ℝ ({X x, Y x} : Set (TangentSpace I x))) hσ
      = curvForm cov X Y x / gramFormVec x (X x) (Y x) := by
    rw [sectionalCurvature_eq_ratio cov hcov hmet _ hσ rfl hG,
      curvFormVec_eq cov hcov hX hY rfl rfl]
  rw [hK'] at hhi
  have hGpos : 0 < gramFormVec x (X x) (Y x) := by
    have hnn : 0 ≤ gramFormVec x (X x) (Y x) := by
      unfold gramFormVec
      have hcs := abs_real_inner_le_norm (X x) (Y x)
      have hsq : (inner ℝ (X x) (Y x))^2 ≤ ‖X x‖^2 * ‖Y x‖^2 := by
        calc (inner ℝ (X x) (Y x))^2 = |inner ℝ (X x) (Y x)|^2 := by rw [sq_abs]
          _ ≤ (‖X x‖ * ‖Y x‖)^2 := by gcongr
          _ = ‖X x‖^2 * ‖Y x‖^2 := by ring
      linarith
    exact lt_of_le_of_ne hnn (Ne.symm hG)
  rw [div_le_iff₀ hGpos] at hhi
  linarith [hhi]


/-- **The upper curvature bound for unit vectors.** -/
theorem curvFormVec_le_of_unit_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 ≤ K) (x : M) {u w : TangentSpace I x}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    curvFormVec cov x u w ≤ K := by
  rcases eq_or_ne (gramFormVec x u w) 0 with hG | hG
  · have hsq : (inner ℝ u w) ^ 2 = (1 : ℝ) ^ 2 := by
      have h := hG
      unfold gramFormVec at h
      rw [hu, hw] at h
      norm_num at h
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · have hdep : ‖w‖ • u = ‖u‖ • w := by
        have h2 : inner ℝ u w = ‖u‖ * ‖w‖ := by rw [hu, hw, mul_one]; exact heq
        exact (inner_eq_norm_mul_iff_real).mp h2
      have hwu : w = u := by
        rw [hw, hu, one_smul, one_smul] at hdep
        exact hdep.symm
      rw [hwu, curvFormVec_self hcov x u]
      exact hKpos
    · have hdep : ‖w‖ • u = ‖u‖ • (-w) := by
        have h2 : inner ℝ u (-w) = ‖u‖ * ‖(-w)‖ := by
          have hwu : ‖u‖ * ‖(-w)‖ = 1 := by rw [norm_neg, hu, hw, mul_one]
          rw [inner_neg_right, hwu]
          linarith
        simpa using (inner_eq_norm_mul_iff_real).mp h2
      have hwu : -w = u := by
        rw [hw, hu, one_smul, one_smul] at hdep
        exact hdep.symm
      have hw' : w = (-1 : ℝ) • u := by
        rw [neg_smul, one_smul]
        rw [← hwu, neg_neg]
      rw [hw', curvFormVec_smul_right hcov x (-1) u u, curvFormVec_self hcov x u]
      norm_num
      exact hKpos
  · obtain ⟨U, hU, hUx⟩ :=
      Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
    obtain ⟨W, hW, hWx⟩ :=
      Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
    have hb := curvForm_le_mul_of_curvLe (cov := cov) hcov hmet hK hU hW
      (x := x) (by rwa [hUx, hWx])
    rw [← curvFormVec_eq (cov := cov) hcov hU hW (u := u) (v := w) hUx hWx] at hb
    rw [hUx, hWx] at hb
    have hle : gramFormVec x u w ≤ 1 := by
      unfold gramFormVec
      rw [hu, hw]
      nlinarith [sq_nonneg (inner ℝ u w)]
    nlinarith [hb, hle]

/-- **The general upper curvature bound.**  For *any* pair of tangent vectors,
`⟪R(u,v)v, u⟫ ≤ K ‖u‖² ‖v‖²`. -/
theorem curvFormVec_le_mul_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 ≤ K) (x : M) (u v : TangentSpace I x) :
    curvFormVec cov x u v ≤ K * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rcases eq_or_ne ‖u‖ 0 with hu0 | hu0
  · have huz : u = 0 := norm_eq_zero.mp hu0
    rw [huz, curvFormVec_zero_left hcov x v]
    positivity
  rcases eq_or_ne ‖v‖ 0 with hv0 | hv0
  · have hvz : v = 0 := norm_eq_zero.mp hv0
    rw [hvz, curvFormVec_zero_right hcov x u]
    positivity
  have hreg : ‖u‖⁻¹ * ‖v‖⁻¹ ≠ 0 := by
    simp [inv_ne_zero hu0, inv_ne_zero hv0]
  have hbc := curvFormVec_basis_change cov hcov hmet (u := u) (v := v)
    (‖u‖⁻¹) 0 0 (‖v‖⁻¹)
  simp at hbc
  have hu' : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u‖⁻¹),
      inv_mul_cancel₀ hu0]
  have hv' : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖⁻¹),
      inv_mul_cancel₀ hv0]
  have hle := curvFormVec_le_of_unit_of_curvLe hcov hmet hK hKpos x hu' hv'
  have hscale : curvFormVec cov x ((‖u‖⁻¹ : ℝ) • u) ((‖v‖⁻¹ : ℝ) • v)
      = (‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v := hbc
  have hpos : (0:ℝ) < (‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 := by positivity
  have h2 : (‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v ≤ K := by rw [← hscale]; exact hle
  have h3 : ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2)⁻¹ * ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v)
      = curvFormVec cov x u v := by
    field_simp
  calc curvFormVec cov x u v
      = ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2)⁻¹ * ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v) := h3.symm
    _ ≤ ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2)⁻¹ * K := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = K * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
        field_simp

/-- **The upper curvature bound in the chart form used by the Rauch inequality.** -/
theorem chartGram_chartCurv_le_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 ≤ K) (htor : cov.torsion = 0) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (X Y : E) :
    chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) X
      ≤ K * chartGram (I := I) x₀ p X X * chartGram (I := I) x₀ p Y Y := by
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  have h3 : ‖frameVector (I := I) x₀ p X‖ ^ 2 = chartGram (I := I) x₀ p X X := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
  have h4 : ‖frameVector (I := I) x₀ p Y‖ ^ 2 = chartGram (I := I) x₀ p Y Y := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
  have h2 := curvFormVec_le_mul_of_curvLe hcov hmet hK hKpos p (frameVector (I := I) x₀ p X)
    (frameVector (I := I) x₀ p Y)
  rw [h3, h4] at h2
  calc chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) X
      = inner ℝ (curvVec cov p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y)
          (frameVector (I := I) x₀ p Y)) (frameVector (I := I) x₀ p X) := by
        rw [chartGram_apply, curvVec_frameVector_eq (cov := cov) htor x₀ hp X Y]
    _ = curvFormVec cov p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y) :=
        inner_curvVec_self cov hcov p _ _
    _ ≤ K * chartGram (I := I) x₀ p X X * chartGram (I := I) x₀ p Y Y := h2


/-! ## 2. The Rauch inequality and the Sturm data for a general bound -/

/-- **The Rauch (Sturm) inequality** with an arbitrary curvature bound: for a Jacobi field `y` along
a unit-speed chart geodesic, `(√⟨y,y⟩)'' + K √⟨y,y⟩ ≥ 0`, in the equivalent form
`(⟨y,y⟩')²/(2⟨y,y⟩) - 2K⟨y,y⟩ ≤ (⟨y,y⟩)''`. -/
theorem rauch_inequality_of_hasDerivAt_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 ≤ K) (htor : cov.torsion = 0)
    {x₀ : M} {u w y : ℝ → E} {a b : ℝ}
    (hutgt : ∀ t ∈ Ioo a b, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (w t) t)
    (hunit : ∀ t ∈ Ioo a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hpos : ∀ t ∈ Ioo a b,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    ∀ t ∈ Ioo a b,
      (deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t) ^ 2
          / (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
        - 2 * K * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)
        ≤ deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
            (y r) (y r)) s) t := by
  intro t ht
  have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (hutgt t ht)
  have hnb : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    ((hu t ht).continuousAt).preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
  have hun : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1 := hunit t ht
  have hgt : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := hpos t ht
  have hg1 := hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht) (hutgt t ht)
    hstay (hy t ht)
  have hderivg :
      deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t
        = 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (chartCovDeriv cov x₀ u w y t) (y t) := hg1.deriv
  have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        (y r) (y r)) s) =ᶠ[𝓝 t]
      (fun s => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (chartCovDeriv cov x₀ u w y s) (y s)) := by
    filter_upwards [hnb] with s hs
    have hstay' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      ((hu s hs).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt s hs))
    exact (hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu s hs) (hutgt s hs)
      hstay' (hy s hs)).deriv
  have hg2 := hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
    (hutgt t ht) hstay (hy t ht) (hDy t ht)
  have hderiv2 :
      deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t
        = 2 * (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t) (y t)
            + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (chartCovDeriv cov x₀ u w y t) (chartCovDeriv cov x₀ u w y t)) := by
    rw [Filter.EventuallyEq.deriv_eq hcongr]
    have h2 := hg2.const_mul (2 : ℝ)
    exact h2.deriv
  have hD : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      = -chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) :=
    eq_neg_of_add_eq_zero_left (hjac t ht)
  have hcurv := chartGram_chartCurv_le_of_curvLe hcov hmet hK hKpos htor x₀ hp (y t) (w t)
  rw [hun, mul_one] at hcurv
  have hcs := chartGram_sq_le (I := I) x₀ ((extChartAt I x₀).symm (u t))
    (chartCovDeriv cov x₀ u w y t) (y t)
  rw [hderivg, hderiv2, hD, chartGram_neg_fst]
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * chartGram (I := I) x₀
    ((extChartAt I x₀).symm (u t)) (y t) (y t))]
  nlinarith [hcurv, hcs, hgt]

/-- **The Sturm data of Rauch's inequality** for an arbitrary curvature bound `K`: the functions
`g1 = (‖y‖)'`, `g2 = (‖y‖)''` with `g2 + K ‖y‖ ≥ 0`. -/
theorem rauch_sturm_ready_of_hasDerivAt_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 ≤ K) (htor : cov.torsion = 0)
    {x₀ : M} {u w y : ℝ → E} {a b : ℝ}
    (hutgt : ∀ t ∈ Ioo a b, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (w t) t)
    (hunit : ∀ t ∈ Ioo a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hpos : ∀ t ∈ Ioo a b,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    ∃ (g1 g2 : ℝ → ℝ),
      (∀ t ∈ Ioo a b, HasDerivAt (fun s => Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u s)) (y s) (y s))) (g1 t) t) ∧
      (∀ t ∈ Ioo a b, HasDerivAt g1 (g2 t) t) ∧
      (∀ t ∈ Ioo a b, 0 ≤ g2 t + K * Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u t)) (y t) (y t))) := by
  classical
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  set H : ℝ → ℝ := fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (y s) (y s)) with hHdef
  set c : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (chartCovDeriv cov x₀ u w y s) (y s) with hcdef
  set Kloc : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s) (y s)
    + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w y s) (chartCovDeriv cov x₀ u w y s) with hKdef
  have hHderiv : ∀ t ∈ Ioo a b, HasDerivAt H (c t / H t) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
    have hsqrt := hasDerivAt_sqrt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
      (hutgt t ht) hstay (hy t ht) (hpos t ht)
    simpa only [H, c] using hsqrt
  have hcderiv : ∀ t ∈ Ioo a b, HasDerivAt c (Kloc t) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
    simpa only [c, Kloc] using hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet
      (hu t ht) (hutgt t ht) hstay (hy t ht) (hDy t ht)
  refine ⟨fun t => c t / H t, fun t => Kloc t / H t - (c t) ^ 2 / (H t) ^ 3,
    hHderiv, ?_, ?_⟩
  · intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hHne : H t ≠ 0 := ne_of_gt hHpos
    have hdiv := (hcderiv t ht).div (hHderiv t ht) hHne
    refine hdiv.congr_deriv ?_
    have hid : (Kloc t * H t - c t * (c t / H t)) / H t ^ 2
        = Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 := by
      field_simp
    simp only [hid]
  · intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hH2 : H t ^ 2 = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) :=
      Real.sq_sqrt (le_of_lt (hpos t ht))
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
    have hrauch := (rauch_inequality_of_hasDerivAt_of_curvLe (cov := cov) hcov hmet hK hKpos htor
      hutgt hu hunit hy hDy hjac hpos) t ht
    have hderivg : deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s)) t = 2 * c t := by
      have hg1 := hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
        (hutgt t ht) hstay (hy t ht)
      rw [hg1.deriv]
    have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) =ᶠ[𝓝 t] (fun s => 2 * c s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hstay' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
        ((hu s hs).continuousAt).preimage_mem_nhds
          ((isOpen_extChartAt_target x₀).mem_nhds (hutgt s hs))
      rw [(hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu s hs) (hutgt s hs)
        hstay' (hy s hs)).deriv]
    have hderiv2 : deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t = 2 * Kloc t := by
      rw [Filter.EventuallyEq.deriv_eq hcongr]
      have h2 := (hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
        (hutgt t ht) hstay (hy t ht) (hDy t ht)).const_mul (2 : ℝ)
      rw [h2.deriv]
    rw [hderivg, hderiv2, ← hH2] at hrauch
    have hrauch' : 2 * ((c t) ^ 2 / H t ^ 2) - 2 * K * H t ^ 2 ≤ 2 * Kloc t := by
      convert hrauch using 2
      ring
    have hK' : (c t) ^ 2 / H t ^ 2 - K * H t ^ 2 ≤ Kloc t := by linarith
    have hH3pos : 0 < H t ^ 3 := by positivity
    have hkey : (Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + K * H t) * H t ^ 3
        = Kloc t * H t ^ 2 - (c t) ^ 2 + K * H t ^ 4 := by
      field_simp
    have hpoly : 0 ≤ Kloc t * H t ^ 2 - (c t) ^ 2 + K * H t ^ 4 := by
      have hmul : ((c t) ^ 2 / H t ^ 2 - K * H t ^ 2) * H t ^ 2 ≤ Kloc t * H t ^ 2 :=
        mul_le_mul_of_nonneg_right hK' (by positivity)
      have heq : ((c t) ^ 2 / H t ^ 2 - K * H t ^ 2) * H t ^ 2 = (c t) ^ 2 - K * H t ^ 4 := by
        field_simp
      rw [heq] at hmul
      linarith
    have hprod : 0 ≤ (Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + K * H t) * H t ^ 3 := by
      rw [hkey]
      exact hpoly
    have hfin : 0 ≤ Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + K * H t :=
      nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hH3pos
    simpa only [H] using hfin


/-! ## 3. Rauch's theorem and the conjugate radius for a general bound -/

theorem sturm_data_at_of_curvLe (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (hK : CurvLe cov K) (hKpos : 0 < K) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {t : ℝ}
    (hJ : IsJacobiAt cov γ J t) (hpos : 0 < inner ℝ (J t) (J t)) :
    HasDerivAt (fun s => Real.sqrt (inner ℝ (J s) (J s)))
        (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s))) t) t ∧
      HasDerivAt (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s))))
        (deriv (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) t) t ∧
      0 ≤ deriv (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) t
        + K * Real.sqrt (inner ℝ (J t) (J t)) := by
  obtain ⟨x₀, u, w, y, ρ, hρ, hutgt, hu, hγ, hframe, hunit, hy, hDy, hjac⟩ :=
    exists_local_data (cov := cov) hJ
  have ht : t ∈ Ioo (t - ρ) (t + ρ) := ⟨by linarith, by linarith⟩
  -- shrink the interval so that `⟨J,J⟩` stays positive
  have hcont : ContinuousAt (fun s => inner ℝ (J s) (J s)) t :=
    continuousAt_inner_self_of_isJacobiAt (cov := cov) hJ
  have hpos_nhds : {s : ℝ | 0 < inner ℝ (J s) (J s)} ∈ 𝓝 t :=
    hcont.eventually (isOpen_Ioi.mem_nhds hpos)
  obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.mem_nhds_iff.mp hpos_nhds
  have hminpos : 0 < min ρ ρ' := lt_min hρ hρ'pos
  have hI : Ioo (t - min ρ ρ') (t + min ρ ρ') ⊆ Ioo (t - ρ) (t + ρ) :=
    Ioo_subset_Ioo (by linarith [min_le_left ρ ρ']) (by linarith [min_le_left ρ ρ'])
  have hI' : Ioo (t - min ρ ρ') (t + min ρ ρ') ⊆ Metric.ball t ρ' := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hs.1, min_le_right ρ ρ'], by linarith [hs.2, min_le_right ρ ρ']⟩
  have hposI : ∀ s ∈ Ioo (t - min ρ ρ') (t + min ρ ρ'),
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s) := by
    intro s hs
    have h1 : 0 < inner ℝ (J s) (J s) := hρ'sub (hI' hs)
    rw [← hframe s (hI hs), ← chartGram_apply] at h1
    rw [← hγ s (hI hs)]
    exact h1
  -- the Sturm-ready data in the chart
  obtain ⟨g1, g2, hg1, hg2, hineq⟩ :=
    rauch_sturm_ready_of_hasDerivAt_of_curvLe (cov := cov) hcov hmet hK hKpos.le htor
      (fun s hs => hutgt s (hI hs)) (fun s hs => hu s (hI hs))
      (fun s hs => hunit s (hI hs)) (fun s hs => hy s (hI hs)) (fun s hs => hDy s (hI hs))
      (fun s hs => hjac s (hI hs)) hposI
  -- the chart function agrees with the intrinsic one
  have hHpt : ∀ s ∈ Ioo (t - ρ) (t + ρ),
      Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s))
        = Real.sqrt (inner ℝ (J s) (J s)) := by
    intro s hs
    rw [chartGram_apply, ← hγ s hs, hframe s hs]
  have hev : (fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s))) =ᶠ[𝓝 t] (fun s => Real.sqrt (inner ℝ (J s) (J s))) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hHpt s hs
  have htI : t ∈ Ioo (t - min ρ ρ') (t + min ρ ρ') := ⟨by linarith, by linarith⟩
  -- first derivative
  have h1 : HasDerivAt (fun s => Real.sqrt (inner ℝ (J s) (J s))) (g1 t) t :=
    (hev.hasDerivAt_iff).mp (hg1 t htI)
  -- the derivative of the intrinsic function is `g1` near `t`
  have hgd : deriv (fun s => Real.sqrt (inner ℝ (J s) (J s))) =ᶠ[𝓝 t] g1 := by
    filter_upwards [isOpen_Ioo.mem_nhds htI] with s hs
    have hevs : (fun r => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r))) =ᶠ[𝓝 s] (fun r => Real.sqrt (inner ℝ (J r) (J r))) := by
      filter_upwards [isOpen_Ioo.mem_nhds (hI hs)] with r hr
      exact hHpt r hr
    exact ((hevs.hasDerivAt_iff).mp (hg1 s hs)).deriv
  have h2 : HasDerivAt (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) (g2 t) t :=
    (hgd.hasDerivAt_iff).mpr (hg2 t htI)
  have hderiv2 : deriv (deriv (fun s => Real.sqrt (inner ℝ (J s) (J s)))) t = g2 t := h2.deriv
  have hineqt := hineq t htI
  have hval : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
      = Real.sqrt (inner ℝ (J t) (J t)) := hHpt t ht
  rw [hval, ← hderiv2] at hineqt
  exact ⟨by rw [h1.deriv]; exact h1, by rw [hderiv2]; exact h2, hineqt⟩


theorem eqOn_zero_of_jacobi_of_curvLe (hcov : ContMDiffCovariantDerivative cov ∞)
    (hmet : IsMetricCompatible cov) (hK : CurvLe cov K) (hKpos : 0 < K) (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {t₁ a b : ℝ}
    (ha : a < 0) (hb : t₁ < b) (hJ : ∀ t ∈ Ioo a b, IsJacobiAt cov γ J t)
    (ht₁pos : 0 < t₁) (ht₁π : t₁ < Real.pi / Real.sqrt K)
    (h0 : J 0 = 0) (h1 : J t₁ = 0) :
    ∀ t ∈ Icc 0 t₁, J t = 0 := by
  set h : ℝ → ℝ := fun s => Real.sqrt (inner ℝ (J s) (J s)) with hdef
  set g : ℝ → ℝ := deriv h with hgdef
  set G : ℝ → ℝ := deriv g with hGdef
  -- membership of the interval `[0,t₁]` in `(a,b)`
  have hmem : ∀ t ∈ Icc (0:ℝ) t₁, t ∈ Ioo a b := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- continuity of `h` on `[0,t₁]`
  have hcont : ContinuousOn h (Icc (0:ℝ) t₁) := by
    intro t ht
    have hc := continuousAt_sqrt_inner_self_of_isJacobiAt (cov := cov) (hJ t (hmem t ht))
    exact hc.continuousWithinAt
  intro t ht
  by_contra hJt
  -- `h t > 0`
  have hh0 : h 0 = 0 := by simp [hdef, h0]
  have hh1 : h t₁ = 0 := by simp [hdef, h1]
  have hhne : h t ≠ 0 := by
    intro hz
    have h2 : inner ℝ (J t) (J t) = 0 :=
      le_antisymm (Real.sqrt_eq_zero'.mp hz) (real_inner_self_nonneg)
    exact hJt ((inner_self_eq_zero).mp h2)
  have hhpos : 0 < h t := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hhne)
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with hh | hh
    · exact absurd (by rw [← hh]; exact hh0) hhne
    · exact hh
  have htt₁ : t < t₁ := by
    rcases eq_or_lt_of_le ht.2 with hh | hh
    · exact absurd (by rw [hh]; exact hh1) hhne
    · exact hh
  -- the consecutive zeros around `t`
  set A : Set ℝ := {s | s ∈ Icc (0:ℝ) t₁ ∧ h s = 0 ∧ s < t} with hAdef
  set B : Set ℝ := {s | s ∈ Icc (0:ℝ) t₁ ∧ h s = 0 ∧ t < s} with hBdef
  have hAne : A.Nonempty := ⟨0, ⟨⟨le_refl 0, ht₁pos.le⟩, by simp [hdef, h0], ht0⟩⟩
  have hBne : B.Nonempty := ⟨t₁, ⟨⟨ht₁pos.le, le_refl t₁⟩, by simp [hdef, h1], htt₁⟩⟩
  have hAbdd : BddAbove A := ⟨t, fun s hs => le_of_lt hs.2.2⟩
  have hBbdd : BddBelow B := ⟨t, fun s hs => le_of_lt hs.2.2⟩
  set a' : ℝ := sSup A with ha'def
  set b' : ℝ := sInf B with hb'def
  have ha'_le : a' ≤ t := csSup_le hAne (fun s hs => le_of_lt hs.2.2)
  have hb'_le : t ≤ b' := le_csInf hBne (fun s hs => le_of_lt hs.2.2)
  have h0A : (0:ℝ) ∈ A := ⟨⟨le_refl 0, ht₁pos.le⟩, by simp [hdef, h0], ht0⟩
  have ha'0 : 0 ≤ a' := le_csSup hAbdd h0A
  have hb'1 : b' ≤ t₁ := csInf_le (⟨t, fun s hs => le_of_lt hs.2.2⟩)
    (by refine ⟨⟨ht₁pos.le, le_refl t₁⟩, ?_, htt₁⟩; simp [hdef, h1])
  -- `a'` and `b'` are zeros of `h`
  have hcont_a : ContinuousAt h a' := by
    have ha_mem : a' ∈ Ioo a b := ⟨by linarith [ha, ha'0], by linarith [hb, hb'1, htt₁]⟩
    exact continuousAt_sqrt_inner_self_of_isJacobiAt (cov := cov) (hJ a' ha_mem)
  have hcont_b : ContinuousAt h b' := by
    have hb_mem : b' ∈ Ioo a b := ⟨by linarith [ha, ha'0, ha'_le, ht0],
      by linarith [hb, hb'1]⟩
    exact continuousAt_sqrt_inner_self_of_isJacobiAt (cov := cov) (hJ b' hb_mem)
  have ha'_mem : h a' = 0 := by
    rcases eq_or_lt_of_le ha'0 with hh | hh
    · rw [← hh]; simp [hdef, h0]
    · have hclosure : a' ∈ closure A := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨s, hsA, hsa⟩ := exists_lt_of_lt_csSup hAne (show a' - ε < a' by linarith)
        have hsa' : s ≤ a' := le_csSup hAbdd hsA
        exact ⟨s, hsA, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hsa, hsA.2.2]⟩
      by_contra hne
      have hnbhd : {x : ℝ | h x ≠ 0} ∈ 𝓝 a' := hcont_a (isOpen_ne.mem_nhds hne)
      obtain ⟨s, hst, hsA⟩ := mem_closure_iff_nhds.mp hclosure {x : ℝ | h x ≠ 0} hnbhd
      exact hst hsA.2.1
  have hb'_mem : h b' = 0 := by
    rcases eq_or_lt_of_le hb'1 with hh | hh
    · rw [hh]; simp [hdef, h1]
    · have hclosure : b' ∈ closure B := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨s, hsB, hbs⟩ := exists_lt_of_csInf_lt hBne (show b' < b' + ε by linarith)
        have hbs' : b' ≤ s := csInf_le hBbdd hsB
        exact ⟨s, hsB, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hbs, hsB.2.2]⟩
      by_contra hne
      have hnbhd : {x : ℝ | h x ≠ 0} ∈ 𝓝 b' := hcont_b (isOpen_ne.mem_nhds hne)
      obtain ⟨s, hst, hsB⟩ := mem_closure_iff_nhds.mp hclosure {x : ℝ | h x ≠ 0} hnbhd
      exact hst hsB.2.1
  have ha'_lt : a' < t := lt_of_le_of_ne ha'_le (fun hh => hhne (hh ▸ ha'_mem))
  have hlt_b' : t < b' := lt_of_le_of_ne hb'_le (Ne.symm (fun hh => hhne (hh ▸ hb'_mem)))
  have hIab : Ioo a' b' ⊆ Ioo (0:ℝ) t₁ := fun s hs => ⟨by linarith [hs.1, ha'0], by linarith [hs.2, hb'1]⟩
  -- `h > 0` strictly between the consecutive zeros
  have hposab : ∀ s ∈ Ioo a' b', 0 < h s := by
    intro s hs
    have hsne : h s ≠ 0 := by
      intro hsy
      rcases lt_trichotomy s t with hst | hst | hst
      · have hsA : s ∈ A := ⟨⟨le_trans ha'0 hs.1.le, (lt_trans hst htt₁).le⟩, hsy, hst⟩
        have := le_csSup hAbdd hsA
        linarith [this, hs.1]
      · exact hhne (hst ▸ hsy)
      · have hsB : s ∈ B := ⟨⟨(lt_trans ht0 hst).le, le_trans hs.2.le hb'1⟩, hsy, hst⟩
        have := csInf_le hBbdd hsB
        linarith [this, hs.2]
    exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hsne)
  -- the Sturm hypotheses
  have hd1 : ∀ s ∈ Ioo a' b', HasDerivAt h (g s) s := by
    intro s hs
    have hsab : s ∈ Ioo a b := ⟨by linarith [hs.1, ha, ha'0],
      by linarith [hs.2, hb, hb'1, htt₁]⟩
    have hspos : 0 < inner ℝ (J s) (J s) := by
      have h1 := hposab s hs
      simp only [hdef] at h1
      exact Real.sqrt_pos.mp h1
    have hsd := sturm_data_at_of_curvLe (cov := cov) hcov hmet hK hKpos htor (hJ s hsab) hspos
    have := hsd.1
    simpa only [hdef, hgdef] using this
  have hd2 : ∀ s ∈ Ioo a' b', HasDerivAt g (G s) s := by
    intro s hs
    have hsab : s ∈ Ioo a b := ⟨by linarith [hs.1, ha, ha'0],
      by linarith [hs.2, hb, hb'1, htt₁]⟩
    have hspos : 0 < inner ℝ (J s) (J s) := by
      have h1 := hposab s hs
      simp only [hdef] at h1
      exact Real.sqrt_pos.mp h1
    have hsd := sturm_data_at_of_curvLe (cov := cov) hcov hmet hK hKpos htor (hJ s hsab) hspos
    have := hsd.2.1
    simpa only [hdef, hgdef, hGdef] using this
  have hineq : ∀ s ∈ Ioo a' b', 0 ≤ G s + K * h s := by
    intro s hs
    have hsab : s ∈ Ioo a b := ⟨by linarith [hs.1, ha, ha'0],
      by linarith [hs.2, hb, hb'1, htt₁]⟩
    have hspos : 0 < inner ℝ (J s) (J s) := by
      have h1 := hposab s hs
      simp only [hdef] at h1
      exact Real.sqrt_pos.mp h1
    have hsd := sturm_data_at_of_curvLe (cov := cov) hcov hmet hK hKpos htor (hJ s hsab) hspos
    have := hsd.2.2
    simpa only [hdef, hgdef, hGdef] using this
  have hcont_ab : ContinuousOn h (Icc a' b') :=
    hcont.mono (Icc_subset_Icc ha'0 hb'1)
  have hbπ : b' - a' < Real.pi / Real.sqrt K := by
    have : b' - a' ≤ t₁ := by linarith
    linarith
  have hnn : ∀ s ∈ Icc a' b', 0 ≤ h s := fun s _ => Real.sqrt_nonneg _
  have hzero := sturm_eqOn_zero_Icc (lam := K) hKpos (by linarith) hbπ
    hcont_ab ha'_mem hnn hd1 hd2 hineq hb'_mem
  have := hzero ⟨ha'_lt.le, hlt_b'.le⟩
  rw [this] at hhpos
  exact lt_irrefl _ hhpos


/-- **Rauch's theorem, conjugate-radius form, for an arbitrary upper curvature bound.** -/
theorem pi_div_sqrt_le_of_isConjugateTime
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 < K) (htor : cov.torsion = 0)
    {γ : ℝ → M} {t : ℝ} (h : Submission.ConjRadius.IsConjugateTime cov γ t) :
    Real.pi / Real.sqrt K ≤ t := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨htpos, J, hJ, h0, h1, s, hs, hsne⟩ := h
  have hz := eqOn_zero_of_jacobi_of_curvLe (cov := cov) hcov hmet hK hKpos htor
    (show (-1 : ℝ) < 0 by norm_num) (show t < t + 1 by linarith)
    (fun r _ => hJ r) htpos hcon h0 h1
  exact hsne (hz s ⟨hs.1.le, hs.2.le⟩)

theorem rauch_inequality_speed_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 ≤ K) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {c : ℝ}
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2)
    {a b : ℝ} (ha : -2 < a) (hb : b < 2)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hpos : ∀ t ∈ Ioo a b,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    ∀ t ∈ Ioo a b,
      (deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t) ^ 2
          / (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
        - 2 * K * c ^ 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)
        ≤ deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
            (y r) (y r)) s) t := by
  intro t ht
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
  have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (h.2.2.1 t ht2)
  have hnb : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hun : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2 :=
    hspeed t ht2
  have hgt : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := hpos t ht
  -- the first derivative of the squared norm
  have hg1 := hasDerivAt_chartGram_self (cov := cov) hmet h ht2 (hy t ht)
  have hderivg :
      deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t
        = 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (chartCovDeriv cov x₀ u w y t) (y t) := hg1.deriv
  -- `deriv` of the squared norm agrees near `t` with the explicit expression
  have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        (y r) (y r)) s) =ᶠ[𝓝 t]
      (fun s => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (chartCovDeriv cov x₀ u w y s) (y s)) := by
    filter_upwards [hnb] with s hs
    have hs2 : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1, ha], by linarith [hs.2, hb]⟩
    exact (hasDerivAt_chartGram_self (cov := cov) hmet h hs2 (hy s hs)).deriv
  -- the second derivative
  have hg2 := hasDerivAt_deriv_chartGram_self (cov := cov) hmet h ht2 (hy t ht) (hDy t ht)
  have hderiv2 :
      deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t
        = 2 * (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t) (y t)
            + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (chartCovDeriv cov x₀ u w y t) (chartCovDeriv cov x₀ u w y t)) := by
    rw [Filter.EventuallyEq.deriv_eq hcongr]
    have h2 := hg2.const_mul (2 : ℝ)
    exact h2.deriv
  -- the Jacobi equation identifies the second covariant derivative
  have hD : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      = -chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) :=
    eq_neg_of_add_eq_zero_left (hjac t ht)
  -- the curvature bound
  have hcurv := chartGram_chartCurv_le_of_curvLe hcov hmet hK hKpos htor x₀ hp (y t) (w t)
  rw [hun] at hcurv
  -- Cauchy–Schwarz
  have hcs := chartGram_sq_le (I := I) x₀ ((extChartAt I x₀).symm (u t))
    (chartCovDeriv cov x₀ u w y t) (y t)
  rw [hderivg, hderiv2, hD, chartGram_neg_fst]
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * chartGram (I := I) x₀
    ((extChartAt I x₀).symm (u t)) (y t) (y t))]
  nlinarith [hcurv, hcs, hgt]


theorem rauch_sturm_ready_speed_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 ≤ K) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {c : ℝ}
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2)
    {a b : ℝ} (ha : -2 < a) (hb : b < 2)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hpos : ∀ t ∈ Ioo a b,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    ∃ (g1 g2 : ℝ → ℝ),
      (∀ t ∈ Ioo a b, HasDerivAt (fun s => Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u s)) (y s) (y s))) (g1 t) t) ∧
      (∀ t ∈ Ioo a b, HasDerivAt g1 (g2 t) t) ∧
      (∀ t ∈ Ioo a b, 0 ≤ g2 t + K * c ^ 2 * Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u t)) (y t) (y t))) := by
  classical
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  set H : ℝ → ℝ := fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (y s) (y s)) with hHdef
  set ct : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (chartCovDeriv cov x₀ u w y s) (y s) with hcdef
  set Kloc : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s) (y s)
    + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w y s) (chartCovDeriv cov x₀ u w y s) with hKdef
  have hHderiv : ∀ t ∈ Ioo a b, HasDerivAt H (ct t / H t) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
    have hsqrt := hasDerivAt_sqrt_chartGram_self (cov := cov) hmet h ht2 (hy t ht) (hpos t ht)
    simpa only [H, ct] using hsqrt
  have hcderiv : ∀ t ∈ Ioo a b, HasDerivAt ct (Kloc t) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
    simpa only [ct, Kloc] using hasDerivAt_deriv_chartGram_self (cov := cov) hmet h ht2
      (hy t ht) (hDy t ht)
  refine ⟨fun t => ct t / H t, fun t => Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3,
    hHderiv, ?_, ?_⟩
  · -- the second derivative of `H`
    intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hHne : H t ≠ 0 := ne_of_gt hHpos
    have hdiv := (hcderiv t ht).div (hHderiv t ht) hHne
    refine hdiv.congr_deriv ?_
    have hid : (Kloc t * H t - ct t * (ct t / H t)) / H t ^ 2
        = Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 := by
      field_simp
    simp only [hid]
  · -- the inequality `0 ≤ g2 t + K c² √⟨y,y⟩`
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hH2 : H t ^ 2 = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) :=
      Real.sq_sqrt (le_of_lt (hpos t ht))
    -- Rauch's inequality
    have hrauch := rauch_inequality_speed_of_curvLe (cov := cov) (c := c) hcov hmet hK hKpos htor h hspeed
      ha hb hy hDy hjac hpos t ht
    have hderivg : deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s)) t = 2 * ct t := by
      have hg1 := hasDerivAt_chartGram_self (cov := cov) hmet h ht2 (hy t ht)
      rw [hg1.deriv]

    have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) =ᶠ[𝓝 t] (fun s => 2 * ct s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hs2 : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1, ha], by linarith [hs.2, hb]⟩
      rw [(hasDerivAt_chartGram_self (cov := cov) hmet h hs2 (hy s hs)).deriv]

    have hderiv2 : deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t = 2 * Kloc t := by
      rw [Filter.EventuallyEq.deriv_eq hcongr]
      have h2 := (hasDerivAt_deriv_chartGram_self (cov := cov) hmet h ht2 (hy t ht)
        (hDy t ht)).const_mul (2 : ℝ)
      rw [h2.deriv]
    rw [hderivg, hderiv2, ← hH2] at hrauch
    -- `hrauch : (2 ct)² / (2 H²) - 2 K c² H² ≤ 2 K`
    have hrauch' : 2 * ((ct t) ^ 2 / H t ^ 2) - 2 * K * c ^ 2 * H t ^ 2 ≤ 2 * Kloc t := by
      convert hrauch using 2
      field_simp
    have hKloc : (ct t) ^ 2 / H t ^ 2 - K * c ^ 2 * H t ^ 2 ≤ Kloc t := by linarith
    have hH3pos : 0 < H t ^ 3 := by positivity
    have hkey : (Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 + K * c ^ 2 * H t) * H t ^ 3
        = Kloc t * H t ^ 2 - (ct t) ^ 2 + K * c ^ 2 * H t ^ 4 := by
      field_simp
    have hpoly : 0 ≤ Kloc t * H t ^ 2 - (ct t) ^ 2 + K * c ^ 2 * H t ^ 4 := by
      have hmul : ((ct t) ^ 2 / H t ^ 2 - K * c ^ 2 * H t ^ 2) * H t ^ 2
          ≤ Kloc t * H t ^ 2 :=
        mul_le_mul_of_nonneg_right hKloc (by positivity)
      have heq : ((ct t) ^ 2 / H t ^ 2 - K * c ^ 2 * H t ^ 2) * H t ^ 2
          = (ct t) ^ 2 - K * c ^ 2 * H t ^ 4 := by
        field_simp
      rw [heq] at hmul
      linarith
    have hprod : 0 ≤ (Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 + K * c ^ 2 * H t) * H t ^ 3 := by
      rw [hkey]
      exact hpoly
    have hfin : 0 ≤ Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 + K * c ^ 2 * H t :=
      nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hH3pos
    simpa only [H] using hfin




theorem eqOn_zero_Icc_of_pos_speed_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 < K) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {c : ℝ} (hc : 0 < c)
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2)
    {a b : ℝ} (ha2 : -2 < a) (hb2 : b < 2) (hab : a < b) (habπ : b - a < Real.pi / (c * Real.sqrt K))
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hcont : ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc a b))
    (hya : y a = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
    (hyb : y b = 0) :
    ∀ t ∈ Icc a b, y t = 0 := by
  obtain ⟨g1, g2, hg1, hg2, hineq⟩ := rauch_sturm_ready_speed_of_curvLe (cov := cov) (c := c)
    hcov hmet hK hKpos.le htor h hspeed ha2 hb2 hy hDy hjac hpos
  have hsqrtK : Real.sqrt (K * c ^ 2) = Real.sqrt K * c := by
    rw [show K * c ^ 2 = (Real.sqrt K * c) ^ 2 by rw [mul_pow, Real.sq_sqrt hKpos.le],
      Real.sqrt_sq (by positivity)]
  have hsqrt_a : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u a)) (y a) (y a))
      = 0 := by
    rw [hya, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero]
  have hsqrt_b : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u b)) (y b) (y b))
      = 0 := by
    rw [hyb, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero]
  have hzero := sturm_eqOn_zero_Icc (lam := K * c ^ 2) (by positivity) hab
    (by rw [hsqrtK, mul_comm]; exact habπ) hcont hsqrt_a (fun t _ => Real.sqrt_nonneg _) hg1 hg2 hineq
    hsqrt_b
  intro t ht
  have h1 : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) = 0 :=
    hzero ht
  have hGnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
    positivity
  have h2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp h1) hGnn
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha2], by linarith [ht.2, hb2]⟩
  exact (chartGram_self_eq_zero_iff (mem_source_chartCurve (I := I) (h.2.2.1 t ht2)) (y t)).mp h2



theorem jacobiTensor_injective_speed_of_curvLe
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 < K)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {c : ℝ} (hc : 0 < c)
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2)
    {A B t₁ : ℝ} (hA2 : -2 < A) (hA0 : A < 0) (hBt : t₁ < B) (hB2 : B < 2)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Ioo A B,
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Ioo A B, HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
      - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1)
    (ht₁pos : 0 < t₁) (ht₁π : t₁ * c < Real.pi / Real.sqrt K) :
    Function.Injective (Y t₁) := by
  have hspeed' : ∀ t ∈ Ioo A B,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2 :=
    fun t ht => hspeed t ⟨by linarith [ht.1, hA2], by linarith [ht.2, hB2]⟩
  have h0mem : (0 : ℝ) ∈ Ioo A B := ⟨hA0, by linarith⟩
  intro z₁ z₂ hz
  set e : E := z₁ - z₂ with hedef
  set y : ℝ → E := fun s => Y s e with hydef
  have hy0 : y 0 = 0 := by simp only [hydef, hY0, ContinuousLinearMap.zero_apply]
  have hyt : y t₁ = 0 := by simp only [hydef, hedef, map_sub, hz, sub_self]
  -- the derivative of `y` at `0` is `e`
  have hderiv0 : HasDerivAt y e 0 := by
    have hh := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := e) (hY 0 h0mem)
    have hd0 : (U 0) e - (gammaOp (cov := cov) x₀ u w 0) ((Y 0) e) = e := by
      rw [hY0, hU0]
      simp
    exact hh.congr_deriv hd0
  -- the field and its covariant derivative are differentiable on `(0,t₁)`
  have hy : ∀ t ∈ Ioo 0 t₁, HasDerivAt y (deriv y t) t := by
    intro t ht
    have hmem : t ∈ Ioo A B := ⟨by linarith [ht.1], by linarith [ht.2, hBt]⟩
    have hh := hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := e) (hY t hmem)
    simpa only [hydef] using hh.congr_deriv hh.deriv.symm
  have hDy : ∀ t ∈ Ioo 0 t₁, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t := by
    intro t ht
    have hmem : t ∈ Ioo A B := ⟨by linarith [ht.1], by linarith [ht.2, hBt]⟩
    have hh := hasDerivAt_chartCovDeriv_jacobiCol_gen (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (Y := Y) (U := U) (e := e) hmem hY hU
    simpa only [hydef] using hh.congr_deriv hh.deriv.symm
  have hjac : ∀ t ∈ Ioo 0 t₁, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0 := by
    intro t ht
    have hmem : t ∈ Ioo A B := ⟨by linarith [ht.1], by linarith [ht.2, hBt]⟩
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hmem.1, hA2], by linarith [hmem.2, hB2]⟩
    simpa only [hydef] using jacobiEquation_col_gen (cov := cov) (x₀ := x₀) (u := u) (w := w)
      (Y := Y) (U := U) (e := e) hmem hY hU (mem_source_chartCurve (I := I) (h.2.2.1 t ht2))
  -- continuity of the field and the covariant-derivative data on `Icc 0 T`
  have hcont : ∀ {T : ℝ}, T ≤ t₁ → ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc 0 T) := by
    intro T hTle
    have hmem1 : ∀ t ∈ Icc (0:ℝ) T, t ∈ Ioo A B := fun t ht =>
      ⟨by linarith [ht.1, hA0], by linarith [ht.2, hTle, hBt]⟩
    have hmem2 : ∀ t ∈ Icc (0:ℝ) T, t ∈ Ioo (-2 : ℝ) 2 := fun t ht =>
      ⟨by linarith [(hmem1 t ht).1, hA2], by linarith [(hmem1 t ht).2, hB2]⟩
    have hycont : ContinuousOn y (Icc 0 T) := fun t ht =>
      ((hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀) (u := u) (w := w) (a := e)
        (hY t (hmem1 t ht))).continuousAt).continuousWithinAt
    have hucont : ContinuousOn u (Icc 0 T) := fun t ht =>
      ((h.2.2.2.1 t (hmem2 t ht)).continuousAt).continuousWithinAt
    have hgc := continuousOn_chartGram_curve (I := I) (x₀ := x₀)
      (continuousOn_chartCurve hucont (fun t ht => h.2.2.1 t (hmem2 t ht))) hycont hycont
      (fun t ht => mem_source_chartCurve (I := I) (h.2.2.1 t (hmem2 t ht)))
    exact Real.continuous_sqrt.comp_continuousOn hgc
  -- the field is nonzero immediately to the right of `0` when `e ≠ 0`
  by_cases he : e = 0
  · rw [hedef] at he
    exact sub_eq_zero.mp he
  · obtain ⟨δ, hδpos, hδne⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ioo 0 δ, y t ≠ 0 := by
      have hslope : Tendsto (fun t : ℝ => t⁻¹ • (y t - y 0)) (𝓝[>] (0 : ℝ)) (𝓝 e) := by
        simpa only [zero_add] using hderiv0.tendsto_slope_zero_right
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (y t - y 0) ≠ 0 := hslope.eventually_ne he
      have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), y t ≠ 0 := by
        filter_upwards [hev] with t ht hyt
        exact ht (by rw [hyt, hy0, sub_self, smul_zero])
      obtain ⟨d, hd, hdsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev'
      exact ⟨d, hd, fun t ht => hdsub ht⟩
    -- the first zero of `y` in `(0,t₁]`
    have hkey : ∃ T : ℝ, 0 < T ∧ T ≤ t₁ ∧ y T = 0 ∧ ∀ s ∈ Ioo 0 T, y s ≠ 0 := by
      by_cases hcase : ∃ s ∈ Ioo (0:ℝ) t₁, y s = 0
      · obtain ⟨s₀, hs₀, hy₀⟩ := hcase
        set S : Set ℝ := {s | s ∈ Ioo (0:ℝ) t₁ ∧ y s = 0} with hSdef
        have hSne : S.Nonempty := ⟨s₀, by rw [hSdef]; exact ⟨hs₀, hy₀⟩⟩
        have hSbdd : BddBelow S := ⟨0, fun s hs => by rw [hSdef] at hs; exact hs.1.1.le⟩
        set T : ℝ := sInf S with hTdef
        have hTinf : T ≤ s₀ := csInf_le hSbdd (by rw [hSdef]; exact ⟨hs₀, hy₀⟩)
        have hTlt : T < t₁ := lt_of_le_of_lt hTinf hs₀.2
        have hTle : T ≤ t₁ := hTlt.le
        have hTpos : 0 < T := by
          have hle : δ ≤ T := le_csInf hSne (fun s hs => by
            rw [hSdef] at hs
            by_contra hcon
            push Not at hcon
            exact hδne s ⟨hs.1.1, hcon⟩ hs.2)
          linarith
        have hTmem : T ∈ Ioo (0:ℝ) t₁ := ⟨hTpos, hTlt⟩
        have hyT : y T = 0 := by
          by_contra hne
          have hcT : ContinuousAt y T := (hy T hTmem).continuousAt
          have hnb : {s : ℝ | y s ≠ 0} ∈ 𝓝 T := hcT (isOpen_ne.mem_nhds hne)
          rw [Metric.mem_nhds_iff] at hnb
          obtain ⟨ε, hε, hεS⟩ := hnb
          obtain ⟨s, hsS, hTs⟩ := exists_lt_of_csInf_lt hSne (show T < T + ε by linarith)
          have hle : T ≤ s := csInf_le hSbdd hsS
          rw [hSdef] at hsS
          have hlt : dist s T < ε := by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith
          exact hεS hlt hsS.2
        refine ⟨T, hTpos, hTle, hyT, fun s hs hys => ?_⟩
        have hsS : s ∈ S := by rw [hSdef]; exact ⟨⟨hs.1, lt_of_lt_of_le hs.2 hTle⟩, hys⟩
        have := csInf_le hSbdd hsS
        exact absurd hs.2 (not_lt.mpr this)
      · push Not at hcase
        exact ⟨t₁, ht₁pos, le_rfl, hyt,
          fun s hs => hcase s ⟨hs.1, lt_of_lt_of_le hs.2 le_rfl⟩⟩
    obtain ⟨T, hTpos, hTle, hyT, hTne⟩ := hkey
    -- apply the no-interior-zero case on `[0,T]`
    have hTb2 : T < 2 := by linarith [hTle, hBt, hB2]
    have habπ : T - 0 < Real.pi / (c * Real.sqrt K) := by
      have h1 : T * c < Real.pi / Real.sqrt K :=
        calc T * c ≤ t₁ * c := mul_le_mul_of_nonneg_right hTle hc.le
          _ < Real.pi / Real.sqrt K := ht₁π
      rw [sub_zero, lt_div_iff₀ (by positivity : (0:ℝ) < c * Real.sqrt K)]
      have h2 := mul_lt_mul_of_pos_right h1 (Real.sqrt_pos.mpr hKpos)
      rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr hKpos))] at h2
      nlinarith [h2]
    have hpos : ∀ t ∈ Ioo (0:ℝ) T,
        0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
      intro t ht
      have htne : y t ≠ 0 := hTne t ht
      have hmem : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2, hTb2]⟩
      have hsrc : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
        mem_source_chartCurve (I := I) (h.2.2.1 t hmem)
      have hGnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
        rw [chartGram_apply, real_inner_self_eq_norm_sq]
        positivity
      exact lt_of_le_of_ne hGnn
        (fun h0 => htne ((chartGram_self_eq_zero_iff hsrc (y t)).mp h0.symm))
    have hzero := eqOn_zero_Icc_of_pos_speed_of_curvLe (cov := cov) (c := c)
      (hcov := ‹ContMDiffCovariantDerivative cov ∞›) hmet hK hKpos htor h hc hspeed
      (by norm_num : (-2:ℝ) < 0) hTb2 hTpos habπ
      (fun t ht => hy t ⟨ht.1, lt_of_lt_of_le ht.2 hTle⟩)
      (fun t ht => hDy t ⟨ht.1, lt_of_lt_of_le ht.2 hTle⟩)
      (fun t ht => hjac t ⟨ht.1, lt_of_lt_of_le ht.2 hTle⟩)
      (hcont (T := T) hTle) hy0 hpos hyT
    -- contradict the non-vanishing near `0`
    set t' : ℝ := min δ T / 2 with ht'def
    have ht'pos : 0 < t' := by rw [ht'def]; positivity
    have ht'δ : t' < δ := by
      have h1 : min δ T ≤ δ := min_le_left _ _
      rw [ht'def]; linarith
    have ht'T : t' < T := by
      have h1 : min δ T ≤ T := min_le_right _ _
      rw [ht'def]; linarith
    exact absurd (hzero t' ⟨ht'pos.le, ht'T.le⟩) (hδne t' ⟨ht'pos, ht'δ⟩)


theorem jacobiTensor_injective_of_norm_lt_pi_div_sqrt_of_curvLe
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 < K)
    {x₀ : M} {v : E} (hv0 : v ≠ 0)
    (hv : Real.sqrt (chartGram (I := I) x₀ x₀ v v) < Real.pi / Real.sqrt K)
    {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {Y U : ℝ → E →L[ℝ] E}
    (hY : ∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
      HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hU : ∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
      HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
        - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t)
    (hY0 : Y 0 = 0) (hU0 : U 0 = 1) :
    Function.Injective (Y 1) := by
  have hnn : 0 ≤ chartGram (I := I) x₀ x₀ v v := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
    positivity
  have hcpos : 0 < Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
    rw [Real.sqrt_pos]
    exact lt_of_le_of_ne hnn
      (fun h0 => hv0 ((chartGram_self_eq_zero_iff (mem_chart_source H x₀) v).mp h0.symm))
  have hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)
        = (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) ^ 2 := by
    intro t ht
    rw [hasChartGeodesic_chartGram_const hmet x₀ h t ht, Real.sq_sqrt hnn]
  refine jacobiTensor_injective_speed_of_curvLe (cov := cov)
    (x₀ := x₀) (v := v) (u := u) (w := w) (A := -(3/2)) (B := 3/2) (t₁ := 1)
    (c := Real.sqrt (chartGram (I := I) x₀ x₀ v v))
    htor hmet hK hKpos h hcpos hspeed (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun t ht => hY t ⟨ht.1.le, ht.2.le⟩) (fun t ht => hU t ⟨ht.1.le, ht.2.le⟩)
    hY0 hU0 (by norm_num) (by simpa using hv)


theorem not_exists_jacobiTensor_singular_of_norm_lt_pi_div_sqrt_of_curvLe
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 < K)
    {x₀ : M} {v : E} (hv0 : v ≠ 0)
    (hv : Real.sqrt (chartGram (I := I) x₀ x₀ v v) < Real.pi / Real.sqrt K) :
    ¬ ∃ (u w : ℝ → E) (Y U : ℝ → E →L[ℝ] E),
        HasChartGeodesic cov x₀ v u w ∧ Y 0 = 0 ∧ U 0 = 1 ∧ ¬ Function.Injective (Y 1) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt Y (U t - (gammaOp (cov := cov) x₀ u w t).comp (Y t)) t) ∧
        (∀ t ∈ Icc (-(3/2) : ℝ) (3/2),
          HasDerivAt U (-((gammaOp (cov := cov) x₀ u w t).comp (U t))
            - (curvOp (cov := cov) x₀ u w t).comp (Y t)) t) := by
  rintro ⟨u, w, Y, U, hgc, hY0, hU0, hYinj, hY, hU⟩
  exact hYinj (jacobiTensor_injective_of_norm_lt_pi_div_sqrt_of_curvLe (cov := cov) htor hmet
    hK hKpos hv0 hv hgc hY hU hY0 hU0)


theorem forall_not_locally_injective_of_norm_lt_pi_div_sqrt_of_curvLe
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov)
    (hK : CurvLe cov K) (hKpos : 0 < K)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, v ≠ 0 →
      Real.sqrt (chartGram (I := I) x₀ x₀ v v) < Real.pi / Real.sqrt K → ‖v‖ < ρ →
      ¬ (∀ ε : ℝ, 0 < ε → ∃ y z : E, ‖y - v‖ < ε ∧ ‖z - v‖ < ε ∧ y ≠ z ∧
          expMap cov x₀ y = expMap cov x₀ z) := by
  obtain ⟨ρ, hρ, hdata⟩ :=
    exists_jacobiTensor_singular_of_not_locally_injective (cov := cov) htor x₀
  refine ⟨ρ, hρ, fun v hv0 hv hvsmall hnot => ?_⟩
  obtain ⟨u, w, Y, U, hgc, hY0, hU0, hYinj, hY, hU⟩ := hdata v hvsmall hnot
  exact not_exists_jacobiTensor_singular_of_norm_lt_pi_div_sqrt_of_curvLe (cov := cov) htor hmet
    hK hKpos hv0 hv ⟨u, w, Y, U, hgc, hY0, hU0, hYinj, hY, hU⟩


end

end Submission.RauchK