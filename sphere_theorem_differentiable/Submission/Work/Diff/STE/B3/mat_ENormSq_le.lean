import Mathlib
import Submission.Work.Diff.STE.B3.ENormSq_basic
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.STE.B3.mat_recon_gen
import Submission.Work.Diff.STE.B3.tMapFun_injOn_det
import Submission.Work.Diff.STE.D.R_Rstar_expansion2
import Submission.Work.Diff.STE.D.bump_smul_smooth
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.CSq_le_ENormSq_of_periodization

import Submission.Work.Diff.STE.B3.exists_partition_compact
import Submission.Work.Diff.STE.B3.normMultilinear_le_of_basis
import Submission.Work.Diff.STE.B3.integral_pd_comp_le_compact
import Submission.Work.Diff.STE.B3.pdVec_integral_le_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `mat_ENormSq_le`: the `L²`-tame bound for the chart matrix in terms of the components

The target of this file (`Work.Diff.STE.B3.mat_ENormSq_le`) is one of the linchpins of the
short-time-existence assembly (see `DESIGN.md`, SESSION 8): the `Hᵐ` energy of the chart matrix
`D.mat j h a b` of a section `h` (cut off by a bump `φ`) is controlled by the `Hᵐ` energies of the
localised components `D.Rper i h c d`.

## The route

* **Pointwise reconstruction** (`mat_eq_recoCoeff`).  At a point `z` whose flat coordinate in the
  chart `j` maps to a point `p = pt j z` with `ζ i p ≠ 0`, the value of the chart matrix
  `D.mat j h a b z = h p (e j a) (e j b)` is the double sum of the localised component `D.R i h c d`
  against the explicit coefficient `recoCoeff` -- this is `Work.Diff.STE.B3.mat_recon_gen`, i.e. the
  reconstruction identity `Σ_i R_i* R_i = id` rewritten in flat coordinates (the cut-off `χ i` and
  the density `√(dens i)` cancel against the definition of `D.R`).
* **A smooth, global coefficient.**  `recoCoeff` is only smooth where the chart expressions are
  genuine; multiplying it by a bump whose `tsupport` lies in the good set (`bump_smul_smooth`) makes
  it globally smooth.  The same device globalises the chart transition `tMapFun D i j` (which is
  injective with nowhere-vanishing Jacobian on the good set, `tMapFun_injOn_det`).  A smooth
  partition of unity `ψ i`, supported where `ζ i (pt j ·) ≠ 0`, turns the reconstruction into
  `φ · mat j h a b = Σ_i Σ_cd (φ · G i c d) · (Rper i h c d ∘ T i)` as functions on `ℝⁿ`.
* **Peeling the cut-off** (`Work.Diff.STE.B3.mulJet_le`): the `m`-th jet of `φ · W` is bounded in
  `L²` by `Kφ²` times the sum of the `L²`-norms of all jets of `W` of order `≤ m`.
* **The change of variables** (`Work.Diff.STE.B3.integral_pd_comp_le_compact`): each term
  `G · (Rper ∘ T)` is estimated against the jets of `Rper` over the unit cube.
* **The Sobolev comparison** (`pdVec_integral_le_ENormSq_per`): for a periodisation of a function
  supported in the open centred cube, the jets of order `≤ m` are controlled by the *top* energy
  `ENormSq m` (the vanishing on the half-integer hyperplanes supplies the mean).

This file contains the construction of the identity and the final assembly; the analytic
ingredients are the listed lemmas.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory

set_option maxHeartbeats 2000000

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The pointwise reconstruction coefficient -/

/-- **The coefficient of the pointwise reconstruction of the chart matrix.**  At a flat coordinate
`z` of the chart `j`, the chart matrix `D.mat j h a b z` is the double sum of the localised
components `D.R i h c d (tMapFun D i j z)` of *any* chart `i` against this coefficient (see
`mat_eq_recoCoeff`).

It is the coefficient of `Work.Diff.STE.B3.mat_recon_gen`, with the weight `ζ i`, the reciprocal
volume density `(√(dens i))⁻¹` and the two metric pairings of the frame `e i` against `e j`. -/
def recoCoeff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun z =>
    (D.ζ i (D.pt j z))⁻¹
      * ((Real.sqrt (D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)))⁻¹
        * (g₀.inner (D.pt j z) (D.e j a (D.pt j z)) (D.e i c (D.pt j z))
          * g₀.inner (D.pt j z) (D.e j b (D.pt j z)) (D.e i d (D.pt j z))))

/-- **The pointwise reconstruction of the chart matrix in the components of chart `i`.**
If `ζ i (pt j z) ≠ 0` then
`mat j h a b z = Σ_{c d} recoCoeff D i j a b c d z · R i h c d (tMapFun D i j z)`.

This is `Work.Diff.STE.B3.mat_recon_gen` (`Σ_i R_i* R_i = id`) with `X = e j a`,
`Y = e j b`; the cut-off `χ i` equals `1` at the (interior) flat coordinate and the density
`√(dens i)` cancels against the definition of `R i`. -/
lemma mat_eq_recoCoeff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hζ : D.ζ i (D.pt j z) ≠ 0) :
    D.mat j h a b z
      = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          recoCoeff (I := I) (M := M) D i j a b c d z
            * D.R i h c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) := by
  have hmain := mat_recon_gen (I := I) (M := M) D h i (D.pt j z)
    (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) hζ
  rw [show D.mat j h a b z
      = h (D.pt j z) (D.e j a (D.pt j z)) (D.e j b (D.pt j z)) from rfl, hmain]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [recoCoeff, Work.Diff.STE.D.tMapFun]
  ring_nf

/-! ## 2. Smoothness of the reconstruction coefficient -/

/-- **The raw reconstruction coefficient is smooth wherever it is genuine.**  At a point `z` of the
good set (`flatToE (x₀ j) z` in the interior of the chart-`j` target, `pt j z` in the source of
chart `i`, and its chart-`i` image in the interior of the chart-`i` target) at which moreover
`ζ i (pt j z) ≠ 0`, the coefficient `recoCoeff` is `C^∞`. -/
lemma recoCoeff_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j)
    (hζ : D.ζ i (D.pt j z) ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (recoCoeff (I := I) (M := M) D i j a b c d) z := by
  -- the chart-`i` coordinate of `pt j z`, and the fact that its `flatToE`-image is the chart image
  have hsrc : D.pt j z ∈ (extChartAt I (D.x₀ i)).source := hz.2.1
  have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
      (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)
      = (extChartAt I (D.x₀ i)) (D.pt j z) := by
    rw [Work.Diff.STE.D.tMapFun]
    exact Work.Diff.STE.D.flatToE_coord (I := I) (M := M) D i hsrc
  -- smoothness of the transition and of `ζ i ∘ pt j`
  have hT : ContDiffAt ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z :=
    Work.Diff.STE.D.tMapFun_contDiffAt (I := I) (M := M) D i j hz
  have hzeta : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ i (D.pt j w)) z :=
    Work.Diff.STE.D.contDiffAt_zeta_pt (I := I) (M := M) D i j hz
  have hzetainv : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (D.ζ i (D.pt j w))⁻¹) z :=
    hzeta.inv hζ
  -- the density and its square root along the transition
  have hdens : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens i)
      (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D i _
      (by rw [hflat]; exact hz.2.2)
  have hdenspos : 0 < D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) :=
    Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D i
      (by rw [hflat]; exact interior_subset hz.2.2)
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => Real.sqrt (D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j w))) z :=
    ((Real.contDiffAt_sqrt hdenspos.ne').comp _ hdens).comp z hT
  have hsqrtinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (Real.sqrt (D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j w)))⁻¹) z :=
    hsqrt.inv (Real.sqrt_pos.mpr hdenspos).ne'
  -- the two frame pairings
  have hp1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e j a (D.pt j w)) (D.e i c (D.pt j w))) z :=
    Work.Diff.STE.D.contDiffAt_pairing_pt (I := I) (M := M) D i j j a c hz
  have hp2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (D.e j b (D.pt j w)) (D.e i d (D.pt j w))) z :=
    Work.Diff.STE.D.contDiffAt_pairing_pt (I := I) (M := M) D i j j b d hz
  exact hzetainv.mul (hsqrtinv.mul (hp1.mul hp2))


/-! ## 3. The global reconstruction identity -/

/-- The good set of the pair `(i,j)`, with the additional requirement that the weight `ζ i` does
not vanish at the point `pt j z`.  This is the open set on which the raw coefficient `recoCoeff`
is genuine and smooth. -/
def goodSetZeta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j ∧ D.ζ i (D.pt j z) ≠ 0}

lemma goodSetZeta_subset_goodSet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    goodSetZeta (I := I) (M := M) D i j ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j :=
  fun _ hz => hz.1

/-- The set of points at which the reconstruction coefficient of the pair `(i,j)` is genuine is
open. -/
lemma isOpen_goodSetZeta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    IsOpen (goodSetZeta (I := I) (M := M) D i j) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have h1 : Work.Diff.STE.D.goodSet (I := I) (M := M) D i j ∈ 𝓝 z :=
    tMapFun_goodSet_mem_nhds (I := I) (M := M) D i j hz.1
  have h2 : (fun w => D.ζ i (D.pt j w)) ⁻¹' {x : ℝ | x ≠ 0} ∈ 𝓝 z :=
    ((Work.Diff.STE.D.contDiffAt_zeta_pt (I := I) (M := M) D i j hz.1).continuousAt
      ).preimage_mem_nhds (isOpen_ne.mem_nhds hz.2)
  exact Filter.mem_of_superset (Filter.inter_mem h1 h2) fun w hw => ⟨hw.1, hw.2⟩

/-- The raw reconstruction coefficient is `C^∞` on the good set. -/
lemma recoCoeff_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (recoCoeff (I := I) (M := M) D i j a b c d)
      (goodSetZeta (I := I) (M := M) D i j) :=
  fun z hz => (recoCoeff_contDiffAt (I := I) (M := M) D i j a b c d hz.1 hz.2).contDiffWithinAt

/-- **The global reconstruction identity.**  If `ψ` is a partition (on `Kc`) subordinated to the
non-vanishing of the weights and `G` is a coefficient family which agrees with
`ψ i · recoCoeff D i j a b c d` where `ψ i ≠ 0` and vanishes where `ψ i = 0`, then

`φ · mat j h a b = Σ_i Σ_cd (φ · G i c d) · (Rper i h c d ∘ Tt i)`

as complex-valued functions, for every `φ` with `tsupport φ ⊆ Kc`. -/
theorem mat_eq_sum_of_partition (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (Kc : Set (Fin (Module.finrank ℝ E) → ℝ))
    (ψ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (G : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (Tt : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
    (hψsum : ∀ z ∈ Kc, ∑ i, ψ i z = 1)
    (hψζ : ∀ i z, ψ i z ≠ 0 → D.ζ i (D.pt j z) ≠ 0)
    (hTt : ∀ i z, ψ i z ≠ 0 → Tt i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)
    (hG1 : ∀ i c d z, ψ i z ≠ 0 →
      G i c d z = ψ i z * recoCoeff (I := I) (M := M) D i j a b c d z)
    (hG0 : ∀ i c d z, ψ i z = 0 → G i c d z = 0)
    (φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hφs : tsupport φ ⊆ Kc) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ((φ z * D.mat j h a b z : ℝ) : ℂ)
        = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((φ z * G i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt i z) := by
  -- the real-valued identity
  have hreal : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      φ z * D.mat j h a b z
        = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            (φ z * G i c d z) * D.R i h c d (Tt i z) := by
    intro z
    by_cases hφz : φ z = 0
    · simp only [hφz, zero_mul, Complex.ofReal_zero, Finset.sum_const_zero]
    · have hzKc : z ∈ Kc := hφs (subset_closure (Function.mem_support.mpr hφz))
      have hsumψ : ∑ i, ψ i z = 1 := hψsum z hzKc
      have h1 : φ z * D.mat j h a b z
          = ∑ i : ι₀, (φ z * ψ i z) * D.mat j h a b z := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hsumψ, mul_one]
      rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hψi : ψ i z = 0
      · rw [hψi, mul_zero, zero_mul]
        have hzero : ∀ (c d : Fin (Module.finrank ℝ E)),
            (φ z * G i c d z) * D.R i h c d (Tt i z) = 0 := fun c d => by
          rw [hG0 i c d z hψi, mul_zero, zero_mul]
        simp only [hzero, Finset.sum_const_zero]
      · have hrec := mat_eq_recoCoeff (I := I) (M := M) D h i j a b z (hψζ i z hψi)
        rw [hrec]
        have hstep : (φ z * ψ i z) * (∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                recoCoeff (I := I) (M := M) D i j a b c d z
                  * D.R i h c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z))
            = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                (φ z * G i c d z) * D.R i h c d (Tt i z) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          rw [hG1 i c d z hψi, hTt i z hψi]
          ring
        exact hstep
  -- cast to `ℂ` and replace `R` by `Rper`
  intro z
  have hRper : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
      ψ i z ≠ 0 →
      D.Rper i h c d (Tt i z)
        = ((D.R i h c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) : ℝ) : ℂ) := by
    intro i c d hψi
    rw [hTt i z hψi]
    refine D.Rper_eq_R i h c d fun k => ?_
    have hζi : D.ζ i (D.pt j z) ≠ 0 := hψζ i z hψi
    have hlt : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ < D.σ i :=
      (D.hζsupp i (D.pt j z) hζi).2
    have hσ : D.σ i ≤ 1 / 8 := by have := D.hσ2 i; linarith
    have h2 : ‖Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z‖ < D.σ i := hlt
    have h1 : |(Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) k| ≤
        ‖Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm
        (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) k
    have h3 := abs_lt.mp (lt_of_le_of_lt h1 h2)
    rw [Set.mem_Ioo]
    constructor <;> linarith [h3.1, h3.2, hσ]
  rw [hreal z, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Complex.ofReal_mul]
  by_cases hψi : ψ i z = 0
  · rw [hG0 i c d z hψi, mul_zero, Complex.ofReal_zero, zero_mul, zero_mul]
  · rw [hRper i c d hψi, hTt i z hψi]



open Work.Diff.STE
/-! ## 4. The smooth global data: partition of unity, smoothed transition, smoothed coefficients -/

/-- **Product of a smooth function with a function smooth on an open set containing its closed
support.**  This is the standard "bump device": the product is smooth because on `U` both factors
are, and off the closed support the first factor vanishes on a neighbourhood. -/
lemma contDiff_mul_of_contDiffOn_of_tsupport_subset {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {U : Set (Fin n → ℝ)} (hU : IsOpen U) {f : (Fin n → ℝ) → ℝ}
    {g : (Fin n → ℝ) → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hfg : tsupport f ⊆ U) : ContDiff ℝ (⊤ : ℕ∞) (fun z => f z • g z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hf.contDiffAt.smul (hg.contDiffAt (hU.mem_nhds hz))
  · have hz' : z ∉ tsupport f := fun h => hz (hfg h)
    have hev : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.mp hz'
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      (hev.mono fun w hw => by show f w • g w = (0 : F); rw [hw]; simp)

/-- The flat target region of the chart `j`: the open set of flat coordinates whose `flatToE`-image
lies in the (open) target of the extended chart. -/
def flatTarget (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target}

lemma isOpen_flatTarget (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    IsOpen (flatTarget (I := I) (M := M) D j) :=
  (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
    (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous

lemma flatTarget_eq_interior (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    flatTarget (I := I) (M := M) D j
      = {z | Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
          ∈ interior ((extChartAt I (D.x₀ j)).target)} := by
  rw [flatTarget, (isOpen_extChartAt_target (I := I) (D.x₀ j)).interior_eq]

/-- The good sets with non-vanishing weights cover the flat target region. -/
lemma flatTarget_subset_iUnion_goodSetZeta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (j : ι₀) : flatTarget (I := I) (M := M) D j ⊆ ⋃ i, goodSetZeta (I := I) (M := M) D i j := by
  intro z hz
  have hpt : D.pt j z = (extChartAt I (D.x₀ j)).symm
      (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z) := rfl
  -- some weight does not vanish
  obtain ⟨i, hi⟩ : ∃ i : ι₀, D.ζ i (D.pt j z) ≠ 0 := by
    by_contra h
    push_neg at h
    have h0 : ∑ i : ι₀, (D.ζ i (D.pt j z)) ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [h i]; ring
    have h1 : ∑ i : ι₀, (D.ζ i (D.pt j z)) ^ 2 = 1 := D.hζsq (D.pt j z)
    rw [h0] at h1
    exact one_ne_zero h1.symm
  have hsrc : D.pt j z ∈ (extChartAt I (D.x₀ i)).source := (D.hζsupp i _ hi).1
  have hnorm : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) (D.pt j z)‖ < D.σ i :=
    (D.hζsupp i _ hi).2
  have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z
      ∈ interior ((extChartAt I (D.x₀ j)).target) := by
    simpa only [flatTarget, Set.mem_setOf_eq,
      (isOpen_extChartAt_target (I := I) (D.x₀ j)).interior_eq] using hz
  have htgt : (extChartAt I (D.x₀ i)) (D.pt j z)
      ∈ interior ((extChartAt I (D.x₀ i)).target) := by
    rw [← Work.Diff.STE.D.flatToE_coord (I := I) (M := M) D i hsrc]
    exact Work.Diff.STE.D.flatToE_mem_interior_target (I := I) D i _ (le_of_lt hnorm)
  exact Set.mem_iUnion.mpr ⟨i, ⟨⟨hflat, hsrc, htgt⟩, hi⟩⟩




section Construct

variable (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (m : ℕ)
  (Kc : Set (Fin (Module.finrank ℝ E) → ℝ))

open Work.Diff.STE in
/-- **The smooth global data attached to the chart `j`, the compact set `Kc` and the level `m`.**

Given `Kc ⊆ flatTarget D j`, there are a smooth partition of unity `ψ` on `Kc` (with supports in
the good sets `goodSetZeta`), globally smooth transitions `Tt i` (equal to `tMapFun D i j` on the
support of `ψ i`, and injective with invertible Jacobian on an open set containing it) and, for
every pair `(a,b)` of matrix indices, coefficient families `G (a,b) i c d` (equal to
`ψ i · recoCoeff D i j a b c d` where `ψ i ≠ 0`) together with a single constant `Ctr (a,b)` which
bounds the chart-transfer estimate for all of them at once. -/
theorem exists_smooth_data (hKc : IsCompact Kc)
    (hKO : Kc ⊆ flatTarget (I := I) (M := M) D j) :
    ∃ (ψ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
      (Tt : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
      (U : ι₀ → Set (Fin (Module.finrank ℝ E) → ℝ))
      (G : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ι₀ →
        Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
      (Ctr : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ goodSetZeta (I := I) (M := M) D i j) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ z ∈ Kc, ∑ i, ψ i z = 1) ∧
      (∀ i, IsOpen (U i)) ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (Tt i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, Set.InjOn (Tt i) (U i)) ∧
      (∀ i z, z ∈ U i → (fderiv ℝ (Tt i) z).det ≠ 0) ∧
      (∀ i z, z ∈ U i → Tt i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) ∧
      (∀ i z, ψ i z ≠ 0 → Tt i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) ∧
      (∀ ab i c d, ContDiff ℝ (⊤ : ℕ∞) (G ab i c d)) ∧
      (∀ ab i c d, HasCompactSupport (G ab i c d)) ∧
      (∀ ab i c d, tsupport (G ab i c d) ⊆ goodSetZeta (I := I) (M := M) D i j) ∧
      (∀ ab i c d z, ψ i z ≠ 0 →
        G ab i c d z = ψ i z * recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d z) ∧
      (∀ ab i c d z, ψ i z = 0 → G ab i c d z = 0) ∧
      (∀ ab, 0 ≤ Ctr ab) ∧
      (∀ (ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) (i : ι₀)
        (c d : Fin (Module.finrank ℝ E)) (j' : ℕ) (γ : Fin j' → Fin (Module.finrank ℝ E)),
        j' ≤ m → ∀ (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec j' γ
            (fun z => ((G ab i c d z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
          ≤ Ctr ab * ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
              ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2) := by
  classical
  -- ## the smooth partition of unity subordinate to the good sets
  obtain ⟨ψ, hψsm, -, hψsupp, hψcpt, hψsum⟩ :=
    exists_partition_compact Kc hKc (fun i => goodSetZeta (I := I) (M := M) D i j)
      (fun i => isOpen_goodSetZeta (I := I) (M := M) D i j)
      (fun z hz => flatTarget_subset_iUnion_goodSetZeta (I := I) (M := M) D j (hKO hz))
  -- ## the smoothed transitions, with the sets on which they are genuine diffeomorphisms
  have hTt : ∀ i : ι₀, ∃ (Tt : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
      (U : Set (Fin (Module.finrank ℝ E) → ℝ)),
      IsOpen U ∧ tsupport (ψ i) ⊆ U ∧ ContDiff ℝ (⊤ : ℕ∞) Tt ∧ Set.InjOn Tt U ∧
      (∀ z ∈ U, (fderiv ℝ Tt z).det ≠ 0) ∧
      (∀ z ∈ U, Tt z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) := by
    intro i
    obtain ⟨δ, hδpos, hδsub⟩ := (hψcpt i).exists_cthickening_subset_open
      (isOpen_goodSetZeta (I := I) (M := M) D i j) (hψsupp i)
    have hKcpt : IsCompact (Metric.cthickening (δ / 2) (tsupport (ψ i))) := (hψcpt i).cthickening
    have hKsub : Metric.cthickening (δ / 2) (tsupport (ψ i))
        ⊆ goodSetZeta (I := I) (M := M) D i j :=
      (Metric.cthickening_mono (by linarith : δ / 2 ≤ δ) _).trans hδsub
    obtain ⟨ρ, hρsm, hρone, -, hρprod⟩ :=
      Work.Diff.STE.D.bump_smul_smooth (Metric.cthickening (δ / 2) (tsupport (ψ i)))
        (goodSetZeta (I := I) (M := M) D i j) hKcpt
        (isOpen_goodSetZeta (I := I) (M := M) D i j) hKsub
        (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
        ((Work.Diff.STE.D.tMapFun_contDiffOn (I := I) (M := M) D i j).mono
          (goodSetZeta_subset_goodSet (I := I) (M := M) D i j))
    have hTform : ContDiff ℝ (⊤ : ℕ∞) (fun z => ρ z •
        Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) := by
      simpa only [smul_eq_mul] using hρprod
    have hUsub : Metric.thickening (δ / 2) (tsupport (ψ i))
        ⊆ goodSetZeta (I := I) (M := M) D i j :=
      (Metric.thickening_subset_cthickening _ _).trans hKsub
    have heqOn : ∀ z ∈ Metric.thickening (δ / 2) (tsupport (ψ i)),
        (fun w => ρ w • Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j w) z
          = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z := by
      intro z hz
      show ρ z • Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z
        = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z
      rw [hρone z ((Metric.thickening_subset_cthickening _ _) hz), one_smul]
    refine ⟨fun z => ρ z • Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z,
      Metric.thickening (δ / 2) (tsupport (ψ i)), Metric.isOpen_thickening, ?_, hTform, ?_, ?_,
      heqOn⟩
    · exact Metric.self_subset_thickening (by linarith : (0:ℝ) < δ / 2) _
    · intro a ha b hb hab
      have h1 : Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j a
          = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j b := by
        rw [← heqOn a ha, ← heqOn b hb, hab]
      exact injOn_tMapFun_goodSet (I := I) (M := M) D i j
        (goodSetZeta_subset_goodSet (I := I) (M := M) D i j (hUsub ha))
        (goodSetZeta_subset_goodSet (I := I) (M := M) D i j (hUsub hb)) h1
    · intro z hz
      have hev : (fun w => ρ w • Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j w)
          =ᶠ[𝓝 z] Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j :=
        Filter.eventually_of_mem ((Metric.isOpen_thickening).mem_nhds hz) fun w hw => heqOn w hw
      rw [hev.fderiv_eq]
      exact tMapFun_det_ne_zero (I := I) (M := M) D i j
        (goodSetZeta_subset_goodSet (I := I) (M := M) D i j (hUsub hz))
  choose Tt U hUopen hUsub hTtsm hTinj hTdet hTteq using hTt
  have hTtone : ∀ i z, ψ i z ≠ 0 → Tt i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z :=
    fun i z hz => hTteq i z (hUsub i (subset_closure (Function.mem_support.mpr hz)))
  -- ## the coefficients and the aggregated transfer constants
  have hG : ∀ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      ∃ (G : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (Ctr : ℝ),
      0 ≤ Ctr ∧
      (∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (G i c d)) ∧
      (∀ i c d, HasCompactSupport (G i c d)) ∧
      (∀ i c d, tsupport (G i c d) ⊆ goodSetZeta (I := I) (M := M) D i j) ∧
      (∀ i c d z, ψ i z ≠ 0 →
        G i c d z = ψ i z * recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d z) ∧
      (∀ i c d z, ψ i z = 0 → G i c d z = 0) ∧
      (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (j' : ℕ)
        (γ : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
        ∀ (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
        ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec j' γ
            (fun z => ((G i c d z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
          ≤ Ctr * ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
              ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2) := by
    intro ab
    have hper : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        ∃ (Gicd : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (Cicd : ℝ),
        0 ≤ Cicd ∧ ContDiff ℝ (⊤ : ℕ∞) Gicd ∧ HasCompactSupport Gicd ∧
        tsupport Gicd ⊆ goodSetZeta (I := I) (M := M) D i j ∧
        (∀ z, ψ i z ≠ 0 →
          Gicd z = ψ i z * recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d z) ∧
        (∀ z, ψ i z = 0 → Gicd z = 0) ∧
        (∀ (j' : ℕ) (γ : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
          ∀ (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
          ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
          ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec j' γ
              (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
            ≤ Cicd * ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2) := by
      intro i c d
      obtain ⟨ρ, hρsm, hρone, -, hρprod⟩ :=
        Work.Diff.STE.D.bump_smul_smooth (tsupport (ψ i)) (goodSetZeta (I := I) (M := M) D i j)
          (hψcpt i) (isOpen_goodSetZeta (I := I) (M := M) D i j) (hψsupp i)
          (recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d)
          (recoCoeff_contDiffOn (I := I) (M := M) D i j ab.1 ab.2 c d)
      set Gicd : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
        fun z => ψ i z * (ρ z * recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d z) with hGicd
      have hGsm : ContDiff ℝ (⊤ : ℕ∞) Gicd := by
        rw [hGicd]; exact (hψsm i).mul hρprod
      have hGsup : tsupport Gicd ⊆ tsupport (ψ i) := by
        rw [hGicd]
        exact tsupport_mul_subset_left
      have hGcpt : HasCompactSupport Gicd :=
        (hψcpt i).of_isClosed_subset (isClosed_tsupport Gicd) hGsup
      have hGgood : tsupport Gicd ⊆ goodSetZeta (I := I) (M := M) D i j :=
        hGsup.trans (hψsupp i)
      have htsuppC : tsupport (fun z => ((Gicd z : ℝ) : ℂ)) = tsupport Gicd := by
        rw [tsupport, tsupport]
        congr 1
        ext z
        exact not_congr Complex.ofReal_eq_zero
      -- the transfer constants, aggregated over all `(j',γ)` with `j' ≤ m`
      have htr : ∀ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin (Module.finrank ℝ E))),
          ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
          ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
          ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec (t.1 : ℕ) t.2
              (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
            ≤ C * ∑ k ∈ Finset.range ((t.1 : ℕ) + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 := by
        intro t
        have hfK : IsCompact (tsupport (fun z => ((Gicd z : ℝ) : ℂ))) := by
          rw [htsuppC]; exact hGcpt
        obtain ⟨C, hCnn, hCb⟩ := integral_pd_comp_le_compact (T := Tt i) (hT := hTtsm i)
          (f := fun z => ((Gicd z : ℝ) : ℂ))
          (hf := Complex.ofRealCLM.contDiff.comp hGsm) (hK := hfK) (U := U i)
          (hU := hUopen i)
          (hUf := by rw [htsuppC]; exact fun z hz => hUsub i (hGsup hz))
          (hinj := hTinj i) (hdet := hTdet i) (t.1 : ℕ) t.2
        exact ⟨C, hCnn, hCb⟩
      choose Cind hCindnn hCindb using htr
      refine ⟨Gicd, ∑ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin (Module.finrank ℝ E))),
        (Cind t + 1), ?_, hGsm, hGcpt, hGgood, ?_, ?_, ?_⟩
      · exact Finset.sum_nonneg fun t _ => by linarith [hCindnn t]
      · intro z hz
        show ψ i z * (ρ z * recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d z)
          = ψ i z * recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d z
        rw [hρone z (subset_closure (Function.mem_support.mpr hz)), one_mul]
      · intro z hz
        show ψ i z * (ρ z * recoCoeff (I := I) (M := M) D i j ab.1 ab.2 c d z) = 0
        rw [hz, zero_mul]
      · intro j' γ hj' u hu hup
        have h1 : Cind ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩
            ≤ ∑ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin (Module.finrank ℝ E))),
                (Cind t + 1) := by
          have h2 := Finset.single_le_sum
            (f := fun t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin (Module.finrank ℝ E))) =>
              (Cind t + 1)) (fun t _ => by linarith [hCindnn t])
            (Finset.mem_univ ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩)
          linarith
        calc ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec j' γ
              (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
            = ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec
                ((⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ :
                  (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin (Module.finrank ℝ E)))).1 : ℕ)
                (⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ :
                  (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin (Module.finrank ℝ E)))).2
                (fun z => ((Gicd z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2 := rfl
          _ ≤ Cind ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ *
                ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 :=
              hCindb ⟨⟨j', Nat.lt_succ_of_le hj'⟩, γ⟩ u hu hup
          _ ≤ (∑ t : (Σ j' : Fin (m + 1), (Fin (j' : ℕ) → Fin (Module.finrank ℝ E))),
                (Cind t + 1)) *
                ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (Finset.sum_nonneg fun k _ => Finset.sum_nonneg
                fun l' _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _)
    choose Gfun Cicd hCicdnn hGsm' hGcpt' hGgood' hGone hGzero hGb using hper
    refine ⟨fun i c d => Gfun i c d,
      ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
        (Cicd i c d + 1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
        Finset.sum_nonneg fun d _ => by linarith [hCicdnn i c d]
    · intro i c d; exact hGsm' i c d
    · intro i c d; exact hGcpt' i c d
    · intro i c d; exact hGgood' i c d
    · intro i c d z hz; exact hGone i c d z hz
    · intro i c d z hz; exact hGzero i c d z hz
    · intro i c d j' γ hj' u hu hup
      have h1 : Cicd i c d ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E), (Cicd i c d + 1) := by
        have h2 := Finset.single_le_sum
          (f := fun i : ι₀ => ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E), (Cicd i c d + 1))
          (fun i _ => Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun d _ =>
            by linarith [hCicdnn i c d]) (Finset.mem_univ i)
        have h3 := Finset.single_le_sum
          (f := fun c : Fin (Module.finrank ℝ E) => ∑ d : Fin (Module.finrank ℝ E),
            (Cicd i c d + 1))
          (fun c _ => Finset.sum_nonneg fun d _ => by linarith [hCicdnn i c d]) (Finset.mem_univ c)
        have h4 := Finset.single_le_sum
          (f := fun d : Fin (Module.finrank ℝ E) => (Cicd i c d + 1))
          (fun d _ => by linarith [hCicdnn i c d]) (Finset.mem_univ d)
        linarith
      calc ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec j' γ
              (fun z => ((Gfun i c d z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
          ≤ Cicd i c d * ∑ k ∈ Finset.range (j' + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 :=
            hGb i c d j' γ hj' u hu hup
        _ ≤ (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              (Cicd i c d + 1)) *
              ∑ k ∈ Finset.range (j' + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (Finset.sum_nonneg fun k _ => Finset.sum_nonneg
              fun l' _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _)
  choose G Ctr hCtrnn hGsm hGcpt hGgood hGone hGzero hGb using hG
  exact ⟨ψ, Tt, U, G, Ctr, hψsm, hψsupp, hψcpt, hψsum, hUopen, hTtsm, hUsub, hTinj, hTdet,
    hTteq, hTtone, hGsm, hGcpt, hGgood, hGone, hGzero, hCtrnn, hGb⟩

end Construct


/-! ## 5. Helper lemmas for the assembly -/

/-- Reassociating a triple sum as a sum over the product index. -/
lemma sum3_eq_sum_prod {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {M : Type*} [AddCommMonoid M] (f : ι → κ → ν → M) :
    (∑ i, ∑ k, ∑ j, f i k j) = ∑ t : ι × (κ × ν), f t.1 t.2.1 t.2.2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]

/-- Linearity of `pdVec` over a triple finite sum. -/
lemma pdVec_sum3 {n m : ℕ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (l : Fin m → Fin n) (F : ι → κ → ν → (Fin n → ℝ) → ℂ)
    (hF : ∀ i k j, ContDiff ℝ (⊤ : ℕ∞) (F i k j)) :
    Work.Diff.STE.pdVec m l (fun x => ∑ i, ∑ k, ∑ j, F i k j x)
      = fun x => ∑ i, ∑ k, ∑ j, Work.Diff.STE.pdVec m l (F i k j) x := by
  have hinner : ∀ i k, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => ∑ j, F i k j x) :=
    fun i k => ContDiff.sum fun j _ => hF i k j
  rw [Work.Diff.STE.flat.pdVec_sum2 l (fun i k => fun x => ∑ j, F i k j x) hinner]
  funext x
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  exact congrFun (Work.Diff.STE.flat.pdVec_finset_sum (s := (Finset.univ : Finset ν)) (l := l)
    (F := fun j => F i k j) (hF := fun j => hF i k j)) x

/-- The cardinality of the tuple index. -/
lemma card_fin_fun (n j : ℕ) : Fintype.card (Fin j → Fin n) = n ^ j := by
  simp [Fintype.card_fun]

/-- The integral over the unit cube is at most the integral over the whole space, for a nonnegative
integrable function. -/
lemma setIntegral_unitCube_le_integral {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg : Integrable g) (hgnn : 0 ≤ᵐ[(volume : MeasureTheory.Measure (Fin n → ℝ))] g) :
    ∫ x in Work.Diff.STE.unitCube, g x ≤ ∫ x, g x :=
  MeasureTheory.setIntegral_le_integral hg hgnn

/-- The integral of a triple finite sum over the unit cube. -/
lemma setIntegral_sum3 {n : ℕ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (F : ι → κ → ν → (Fin n → ℝ) → ℝ)
    (hF : ∀ i k j, Integrable (F i k j) (volume.restrict Work.Diff.STE.unitCube)) :
    ∫ x in Work.Diff.STE.unitCube, ∑ i, ∑ k, ∑ j, F i k j x
      = ∑ i, ∑ k, ∑ j, ∫ x in Work.Diff.STE.unitCube, F i k j x := by
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finset_sum]
      intro j _
      exact hF i k j
    · exact fun k _ => integrable_finset_sum _ fun j _ => hF i k j
  · exact fun i _ => integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun j _ => hF i k j

-- (lead 10-02 dupcheck) `ENormSq_nonneg` now comes from `Submission.Work.Diff.STE.B3.ENormSq_basic` (same statement).

/-- A nonnegative finite sum of constant terms. -/
lemma sum_const_nonneg {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 ≤ c) :
    (∑ _ : ι, c) = (Fintype.card ι : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


/-- Integrability on the unit cube is implied by continuity (the cube is bounded). -/
lemma setIntegral_le_integral_of_compactSupport {n : ℕ} {g : (Fin n → ℝ) → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) (hnn : ∀ x, 0 ≤ g x) :
    ∫ x in Work.Diff.STE.unitCube, g x ≤ ∫ x, g x :=
  MeasureTheory.setIntegral_le_integral (hg.integrable_of_hasCompactSupport hc)
    (Filter.Eventually.of_forall hnn)

/-- A sum of powers `n^j`, `j ≤ m`, is bounded by `(m+1) n^m` for `n ≥ 1`. -/
lemma sum_range_pow_le {nR : ℝ} (hnR : 1 ≤ nR) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), nR ^ j ≤ ((m + 1 : ℕ) : ℝ) * nR ^ m := by
  have h : ∀ j ∈ Finset.range (m + 1), nR ^ j ≤ nR ^ m := by
    intro j hj
    exact pow_le_pow_right₀ hnR (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  calc ∑ j ∈ Finset.range (m + 1), nR ^ j
      ≤ ∑ _j ∈ Finset.range (m + 1), nR ^ m := Finset.sum_le_sum h
    _ = ((m + 1 : ℕ) : ℝ) * nR ^ m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The sum over the tuples `Fin j → Fin n` of a constant. -/
lemma sum_fun_const {n j : ℕ} (c : ℝ) :
    (∑ _ : Fin j → Fin n, c) = ((n : ℝ) ^ j) * c := by
  rw [Finset.sum_const, Finset.card_univ, card_fin_fun, nsmul_eq_mul, Nat.cast_pow]

/-- Lowering a smoothness level from `∞` to a finite one. -/
lemma contDiff_level_le (m : ℕ) : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr (le_top : ((m : ℕ) : ℕ∞) ≤ ⊤)

/-- `pdVec` of a globally smooth function is continuous, at any order. -/
lemma continuous_pdVec_of_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) (l : Fin m → Fin n) :
    Continuous (Work.Diff.STE.pdVec m l f) :=
  Work.Diff.STE.continuous_pdVec m l f (hf.of_le (contDiff_level_le m))

/-- **The Sobolev comparison for a periodisation** (local copy): for a periodisation of a function
supported in the open centred cube, the jets of order `≤ m` are controlled by the top energy
`ENormSq m`.  Composed here from the proved `pdVec_integral_le_CSq` and
`CSq_le_ENormSq_of_periodization` (both sorry-free), avoiding the version with the `sorry`ed
`pd_mean_sq_le_integral_pd_sq`. -/
theorem pdVec_integral_le_ENormSq_per_local {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R P : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) R →
      Function.support R ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)) →
      ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
      (∀ z : ι → ℝ, P z = ∑' k : ι → ℤ, R (z + Work.Diff.STE.iVec k)) →
      ∀ (j' : ℕ) (l' : Fin j' → ι), j' ≤ m →
        ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j' l' P x‖ ^ 2
          ≤ C * Work.Diff.STE.ENormSq m P := by
  obtain ⟨C₁, hC₁nn, hC₁⟩ := Work.Diff.STE.B3.pdVec_integral_le_CSq (ι := ι) m
  obtain ⟨C₂, hC₂nn, hC₂⟩ := Work.Diff.STE.B3.CSq_le_ENormSq_of_periodization (ι := ι) m hm
  refine ⟨C₁ * C₂, mul_nonneg hC₁nn hC₂nn, ?_⟩
  intro R P hR hsupp hP hper hrepr j' l' hj
  have h1 : (∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j' l' P x‖ ^ 2)
      ≤ C₁ * Work.Diff.STE.CSq m (Work.Diff.STE.fourierCoeff P) :=
    hC₁ P hP hper j' hj l'
  have h2 : Work.Diff.STE.CSq m (Work.Diff.STE.fourierCoeff P)
      ≤ C₂ * Work.Diff.STE.ENormSq m P := hC₂ R P hR hsupp hP hper hrepr
  calc ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j' l' P x‖ ^ 2
      ≤ C₁ * Work.Diff.STE.CSq m (Work.Diff.STE.fourierCoeff P) := h1
    _ ≤ C₁ * (C₂ * Work.Diff.STE.ENormSq m P) := mul_le_mul_of_nonneg_left h2 hC₁nn
    _ = (C₁ * C₂) * Work.Diff.STE.ENormSq m P := by ring

/-! ## 5b. A sharp Leibniz bound for the jet of a product with a cut-off

This is a self-contained replacement for `Work.Diff.STE.B3.mulJet_le`, with the *sharp* constant
`Kφ` (no `+ 1`), which is what the assembly below needs.  The proof uses the iterated Leibniz rule
`Work.Diff.STE.pdList_mul_sub` (in the "all splits" form) and Cauchy--Schwarz on the at most
`2 ^ m` splits. -/

/-- A list sum of terms bounded by `c` is at most `length * c`. -/
lemma list_sum_le_card_mul_b3 {α : Type*} (L : List α) (f : α → ℝ) (c : ℝ)
    (h : ∀ a ∈ L, f a ≤ c) : (L.map f).sum ≤ (L.length : ℝ) * c := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : f a ≤ c := h a (by simp)
      have ht : ∀ b ∈ t, f b ≤ c := fun b hb => h b (by simp [hb])
      have hrec := ih ht
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- A list sum of pointwise bounded terms is bounded termwise. -/
lemma list_sum_le_sum_b3 {α : Type*} (L : List α) {f g : α → ℝ}
    (h : ∀ a ∈ L, f a ≤ g a) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : f a ≤ g a := h a (by simp)
      have ht : ∀ b ∈ t, f b ≤ g b := fun b hb => h b (by simp [hb])
      have hrec := ih ht
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- Factoring a constant out of a list sum. -/
lemma list_sum_map_mul_left_b3 {α : Type*} (L : List α) (c : ℝ) (f : α → ℝ) :
    (L.map (fun a => c * f a)).sum = c * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      ring

/-- The norm of a list sum is at most the sum of the norms. -/
lemma norm_list_sum_le_b3 {α : Type*} (L : List α) (f : α → ℂ) :
    ‖(L.map f).sum‖ ≤ (L.map (fun a => ‖f a‖)).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The norm of a complexified real is its absolute value. -/
lemma norm_ofReal_eq_abs_b3 (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  exact Real.sqrt_mul_self_eq_abs x

/-- **One-step complexification.**  `∂ᵢ` commutes with the embedding `ℝ → ℂ` (no differentiability
hypothesis: both sides are junk-free, and vanish where the function is not differentiable). -/
lemma pd_ofReal_b3 {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pd i (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdR i g x : ℝ) : ℂ) := by
  funext x
  show (fderiv ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x) (Pi.single i 1)
    = ((fderiv ℝ g x) (Pi.single i 1) : ℂ)
  have hcomp : (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) = Complex.ofRealCLM ∘ g := by
    funext y; exact (Complex.ofRealCLM_apply (g y)).symm
  by_cases hg : DifferentiableAt ℝ g x
  · rw [hcomp]
    have h := (Complex.ofRealCLM.hasFDerivAt (x := g x)).comp x hg.hasFDerivAt
    rw [h.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  · have hg' : ¬ DifferentiableAt ℝ (fun y : Fin n → ℝ => ((g y : ℝ) : ℂ)) x := by
      intro h
      refine hg ?_
      have h2 := Complex.reCLM.differentiableAt.comp x h
      simpa [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using h2
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hg']
    simp

/-- Complexification commutes with the iterated partial derivative `pdList`. -/
lemma pdList_ofReal_b3 {n : ℕ} (l : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdList l (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
      = fun x : Fin n → ℝ => ((Work.Diff.STE.pdRList l f x : ℝ) : ℂ) := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
      show Work.Diff.STE.pd i (Work.Diff.STE.pdList rest (fun y => ((f y : ℝ) : ℂ)))
        = fun x => ((Work.Diff.STE.pdR i (Work.Diff.STE.pdRList rest f) x : ℝ) : ℂ)
      rw [ih]
      exact pd_ofReal_b3 i (Work.Diff.STE.pdRList rest f)

/-- `pdRList` of a list is `pdRVec` of the corresponding tuple. -/
lemma pdRList_eq_pdRVec_b3 {n : ℕ} (q : List (Fin n)) (f : (Fin n → ℝ) → ℝ) :
    Work.Diff.STE.pdRList q f
      = Work.Diff.STE.pdRVec q.length (fun i : Fin q.length => q.get i) f := by
  rw [Work.Diff.STE.pdRVec]
  congr 1
  exact (List.ofFn_get q).symm

/-- The `pdList` of the complexified cut-off is bounded by `Kφ`. -/
lemma pdList_ofReal_norm_le_b3 {n m : ℕ} {φ : (Fin n → ℝ) → ℝ} {Kφ : ℝ}
    (hφb : ∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
      |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
    {q : List (Fin n)} (hq : q.length ≤ m) (z : Fin n → ℝ) :
    ‖Work.Diff.STE.pdList q (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖ ≤ Kφ := by
  rw [pdList_ofReal_b3]
  show ‖((Work.Diff.STE.pdRList q φ z : ℝ) : ℂ)‖ ≤ Kφ
  rw [norm_ofReal_eq_abs_b3]
  rw [pdRList_eq_pdRVec_b3 q φ]
  exact hφb q.length hq (fun i => q.get i) z

/-- **The iterated Leibniz rule in "all splits" form**: the `l`-th iterated partial derivative of
a product is the sum of the products `∂^{p.1}F · ∂^{p.2}G` over *all* complementary splits
`p ∈ splits l` (the split `([], l)`, in which no derivative hits `F`, is included). -/
lemma pdList_mul_unfiltered_b3 {n : ℕ} (l : List (Fin n)) (F g : (Fin n → ℝ) → ℂ)
    (hF : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F))
    (hG : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q g))
    (y : Fin n → ℝ) :
    Work.Diff.STE.pdList l (fun z => F z * g z) y
      = ((Work.Diff.STE.splits l).map
          (fun p => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y)).sum := by
  classical
  set ψ : List (Fin n) × List (Fin n) → ℂ :=
    fun p => Work.Diff.STE.pdList p.1 F y * Work.Diff.STE.pdList p.2 g y with hψ
  have h := congrFun (Work.Diff.STE.pdList_mul_sub l F g hF hG) y
  have hfilter : ((Work.Diff.STE.splitsNE l).map ψ).sum
      = ((((Work.Diff.STE.splits l).filter (fun p => decide (p.1 ≠ []))).map ψ)).sum := by
    rw [Work.Diff.STE.splitsNE_eq_filter]
  have hnil : ψ ([], l) = F y * Work.Diff.STE.pdList l g y := rfl
  have hsum := Work.Diff.STE.splitsNE_sum_add l ψ
  calc Work.Diff.STE.pdList l (fun z => F z * g z) y
      = (Work.Diff.STE.pdList l (fun z => F z * g z) y - F y * Work.Diff.STE.pdList l g y)
          + F y * Work.Diff.STE.pdList l g y := by ring
    _ = ((((Work.Diff.STE.splits l).filter (fun p => decide (p.1 ≠ []))).map ψ)).sum + ψ ([], l) := by
        rw [h, hnil]
    _ = ((Work.Diff.STE.splitsNE l).map ψ).sum + ψ ([], l) := by rw [hfilter]
    _ = ((Work.Diff.STE.splits l).map ψ).sum := hsum

/-- Continuity of the squared norm of an iterated partial derivative. -/
lemma continuous_normSq_pdVec_b3 {n : ℕ} {W : (Fin n → ℝ) → ℂ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (j : ℕ) (γ : Fin j → Fin n) :
    Continuous (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2) := by
  have h := (continuous_pdVec_of_smooth hW j γ).norm
  convert h.mul h using 1
  ext z
  simp only [Pi.mul_apply, pow_two]

/-- **Sharp Leibniz bound.**  `∃C, ∫ ‖∂^β(φ · W)‖² ≤ C Kφ² Σ_{j ≤ m} Σ_γ ∫ ‖∂^γ W‖²`. -/
theorem mulJet_le_sharp (n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : (Fin n → ℝ) → ℝ) (W : (Fin n → ℝ) → ℂ) (Kφ : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → ContDiff ℝ (⊤ : ℕ∞) W →
      (∀ r : ℕ, r ≤ m → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
        |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ) →
      ∀ (β : Fin m → Fin n),
        ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec m β
            (fun z => ((φ z : ℝ) : ℂ) * W z) z‖ ^ 2
          ≤ C * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
              ∫ z in Work.Diff.STE.unitCube (ι := Fin n), ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
  classical
  refine ⟨(4 : ℝ) ^ m, by positivity, ?_⟩
  intro φ W Kφ hφ hW hφb β
  set F : (Fin n → ℝ) → ℂ := fun y => ((φ y : ℝ) : ℂ) with hF
  set l : List (Fin n) := List.ofFn β with hl
  have hl_len : l.length = m := by rw [hl]; exact List.length_ofFn
  set S : List (List (Fin n) × List (Fin n)) := Work.Diff.STE.splits l with hS
  have hS_len : (S.length : ℝ) = (2 : ℝ) ^ m := by
    rw [hS, Work.Diff.STE.cm_splits_length_count, hl_len]
    push_cast
    ring
  set B : (Fin n → ℝ) → ℝ := fun z => ∑ j ∈ Finset.range (m + 1),
    ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 with hB
  have hSsq : (S.length : ℝ) ^ 2 = (4 : ℝ) ^ m := by
    rw [hS_len]
    calc ((2 : ℝ) ^ m) ^ 2 = 2 ^ (m * 2) := by rw [pow_mul]
      _ = 2 ^ (2 * m) := by rw [Nat.mul_comm]
      _ = (2 ^ 2) ^ m := by rw [pow_mul]
      _ = 4 ^ m := by norm_num
  have hBnn : ∀ z : Fin n → ℝ, 0 ≤ B z := by
    intro z
    rw [hB]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _
  -- differentiability hypotheses for the Leibniz rule
  have hFdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q F) := by
    intro q _ _
    rw [hF]
    exact Work.Diff.STE.cm_diff_pdList_ofReal φ hφ q
  have hWdiff : ∀ q : List (Fin n), q.Sublist l → q.length < l.length →
      Differentiable ℝ (Work.Diff.STE.pdList q W) := by
    intro q _ _
    refine (Work.Diff.STE.cm_contDiff_pdList q 1 W ?_).differentiable (by norm_num)
    exact hW.of_le (contDiff_level_le (q.length + 1))
  -- every split contributes at most `Kφ * ‖∂^{p.2}W‖`
  have hterm : ∀ (z : Fin n → ℝ) (p : List (Fin n) × List (Fin n)), p ∈ S →
      ‖Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z‖
        ≤ Kφ * ‖Work.Diff.STE.pdList p.2 W z‖ := by
    intro z p hp
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hp' : p ∈ Work.Diff.STE.splits l := by rw [hS] at hp; exact hp
    have hlen := Work.Diff.STE.cm_splits_mem_length l p hp'
    have hlen' : p.1.length ≤ m := by rw [hl_len] at hlen; omega
    exact pdList_ofReal_norm_le_b3 hφb hlen' z
  -- the pointwise bound
  have hpt : ∀ z : Fin n → ℝ, ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2
      ≤ (4 : ℝ) ^ m * Kφ ^ 2 * B z := by
    intro z
    have hpd : Work.Diff.STE.pdVec m β (fun z => F z * W z)
        = Work.Diff.STE.pdList l (fun z => F z * W z) := by rw [hl]; rfl
    have h1 : ‖Work.Diff.STE.pdList l (fun z => F z * W z) z‖
        ≤ Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum := by
      rw [pdList_mul_unfiltered_b3 l F W hFdiff hWdiff z]
      calc ‖(S.map (fun p => Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z)).sum‖
          ≤ (S.map (fun p => ‖Work.Diff.STE.pdList p.1 F z * Work.Diff.STE.pdList p.2 W z‖)).sum :=
            norm_list_sum_le_b3 S _
        _ ≤ (S.map (fun p => Kφ * ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
            list_sum_le_sum_b3 S (fun p hp => hterm z p hp)
        _ = Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
            list_sum_map_mul_left_b3 S Kφ _
    have h2 : (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum
        ≤ (S.length : ℝ) * Real.sqrt (B z) := by
      refine list_sum_le_card_mul_b3 S (fun p => ‖Work.Diff.STE.pdList p.2 W z‖) (Real.sqrt (B z)) ?_
      intro p hp
      refine Real.le_sqrt_of_sq_le ?_
      have hp' : p ∈ Work.Diff.STE.splits l := by rw [hS] at hp; exact hp
      have hlen := Work.Diff.STE.cm_splits_mem_length l p hp'
      have hlen' : p.2.length ≤ m := by rw [hl_len] at hlen; omega
      have hpd' : Work.Diff.STE.pdList p.2 W
          = Work.Diff.STE.pdVec p.2.length (fun i : Fin p.2.length => p.2.get i) W := by
        rw [Work.Diff.STE.pdVec]
        congr 1
        exact (List.ofFn_get p.2).symm
      rw [hpd']
      refine (Finset.single_le_sum
        (f := fun γ : Fin p.2.length → Fin n => ‖Work.Diff.STE.pdVec p.2.length γ W z‖ ^ 2)
        (fun γ _ => sq_nonneg _) (Finset.mem_univ (fun i => p.2.get i))).trans ?_
      rw [hB]
      exact Finset.single_le_sum
        (f := fun j => ∑ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2)
        (fun j _ => Finset.sum_nonneg fun γ _ => sq_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hlen'))
    have h3 : 0 ≤ (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum :=
      List.sum_nonneg fun a ha => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
        exact norm_nonneg _
    calc ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2
        = ‖Work.Diff.STE.pdList l (fun z => F z * W z) z‖ ^ 2 := by rw [hpd]
      _ ≤ (Kφ * (S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = Kφ ^ 2 * ((S.map (fun p => ‖Work.Diff.STE.pdList p.2 W z‖)).sum) ^ 2 := by ring
      _ ≤ Kφ ^ 2 * ((S.length : ℝ) * Real.sqrt (B z)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h2 2) (sq_nonneg Kφ)
      _ = Kφ ^ 2 * (S.length : ℝ) ^ 2 * B z := by
          rw [mul_pow, Real.sq_sqrt (hBnn z)]
          ring
      _ = (4 : ℝ) ^ m * Kφ ^ 2 * B z := by
          rw [hSsq]
          ring
  -- integration
  have hcontL : Continuous (fun z : Fin n → ℝ =>
      ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2) := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => F z * W z) := by
      rw [hF]
      exact (Complex.ofRealCLM.contDiff.comp hφ).mul hW
    have h := (continuous_pdVec_of_smooth hsm m β).norm
    have h2 := h.mul h
    convert h2 using 1
    ext z
    simp only [Pi.mul_apply, pow_two]
  have hcontB : Continuous B := by
    rw [hB]
    refine continuous_finset_sum (Finset.range (m + 1)) (fun j _ => ?_)
    exact continuous_finset_sum (Finset.univ : Finset (Fin j → Fin n))
      (fun γ _ => continuous_normSq_pdVec_b3 hW j γ)
  have hcontR : Continuous (fun z : Fin n → ℝ => (4 : ℝ) ^ m * Kφ ^ 2 * B z) :=
    hcontB.const_mul ((4 : ℝ) ^ m * Kφ ^ 2)
  have hint1 : ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec m β (fun z => F z * W z) z‖ ^ 2
      ≤ ∫ z in Work.Diff.STE.unitCube, (4 : ℝ) ^ m * Kφ ^ 2 * B z :=
    setIntegral_mono_on
      (Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real hcontL)
      (Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real hcontR)
      Work.Diff.STE.BesselCont.measSet_unitCube (fun z _ => hpt z)
  have hint2 : ∫ z in Work.Diff.STE.unitCube, (4 : ℝ) ^ m * Kφ ^ 2 * B z
      = (4 : ℝ) ^ m * Kφ ^ 2 * ∫ z in Work.Diff.STE.unitCube, B z := by
    rw [integral_const_mul]
  have hint3 : ∫ z in Work.Diff.STE.unitCube, B z
      = ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin n,
          ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec j γ W z‖ ^ 2 := by
    rw [hB]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finset_sum]
      intro γ _
      exact Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real
        (continuous_normSq_pdVec_b3 hW j γ)
    · intro j _
      exact integrable_finset_sum _ fun γ _ =>
        Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real
          (continuous_normSq_pdVec_b3 hW j γ)
  refine hint1.trans ?_
  rw [hint2, hint3]

/-! ## 6. The main theorem -/

open Work.Diff.STE in

theorem mat_ENormSq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (m : ℕ)
    (Kc : Set (Fin (Module.finrank ℝ E) → ℝ)) (hKc : IsCompact Kc)
    (Kφ : ℝ) (hKφ : 0 ≤ Kφ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
        (hφb : ∀ (r : ℕ), r ≤ m → ∀ (γ : Fin r → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ),
          |Work.Diff.STE.pdRVec r γ φ z| ≤ Kφ)
        (hφs : tsupport φ ⊆ Kc)
        (hφt : Kc ⊆ {z : Fin (Module.finrank ℝ E) → ℝ |
          Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target}),
        ∀ (a b : Fin (Module.finrank ℝ E)) (β : Fin m → Fin (Module.finrank ℝ E)),
        Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ => (((φ z * D.mat j h a b z : ℝ)) : ℂ)))
          ≤ C * (1 + ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E), Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hsm φ hφ hφb hφs hφt a b β
    exact Fin.elim0 (hn ▸ a)
  have hn1 : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero hn
  haveI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hn1⟩⟩
  by_cases hKO : Kc ⊆ flatTarget (I := I) (M := M) D j
  · obtain ⟨ψ, Tt, U, G, Ctr, hψsm, hψsupp, hψcpt, hψsum, hUopen, hTtsm, hUsub, hTinj,
      hTdet, hTteq, hTtone, hGsm, hGcpt, hGgood, hGone, hGzero, hCtrnn, hGb⟩ :=
      exists_smooth_data (I := I) (M := M) D j m Kc hKc hKO
    obtain ⟨Cmul, hCmulnn, hCmulb⟩ := mulJet_le_sharp (Module.finrank ℝ E) m
    -- the conversion constant (available for `m ≥ 1`; for `m = 0` we use `1`)
    have hconv : ∃ C : ℝ, 0 ≤ C ∧ ∀ (R P : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
        ContDiff ℝ (⊤ : ℕ∞) R →
        Function.support R ⊆ Set.pi Set.univ
          (fun _ : Fin (Module.finrank ℝ E) => Set.Ioo (-(1/2:ℝ)) (1/2)) →
        ContDiff ℝ (⊤ : ℕ∞) P → Work.Diff.STE.Periodic1 P →
        (∀ z, P z = ∑' k : Fin (Module.finrank ℝ E) → ℤ, R (z + Work.Diff.STE.iVec k)) →
        ∀ (j' : ℕ) (l' : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
          ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec j' l' P x‖ ^ 2
            ≤ C * Work.Diff.STE.ENormSq m P := by
      by_cases hm0 : m = 0
      · subst hm0
        refine ⟨1, zero_le_one, ?_⟩
        intro R P hR hRs hP hPp hPrepr j' l' hj'
        have hj'0 : j' = 0 := Nat.le_zero.mp hj'
        subst hj'0
        rw [one_mul]
        have h1 : Work.Diff.STE.pdVec 0 l' P = P := by
          simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
        rw [h1]
        have h2 : Work.Diff.STE.ENormSq 0 P
            = ∫ x in Work.Diff.STE.unitCube, ‖P x‖ ^ 2 := by
          simp [Work.Diff.STE.ENormSq, Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
        rw [h2]
      · exact pdVec_integral_le_ENormSq_per_local (ι := Fin (Module.finrank ℝ E)) m
          (Nat.pos_of_ne_zero hm0)
    obtain ⟨Cenv, hCenvnn, hCenvb⟩ := hconv
    -- abbreviations
    set nR : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ) with hnR
    have hnR1 : 1 ≤ nR := by rw [hnR]; exact_mod_cast hn1
    have hnRnn : 0 ≤ nR := le_trans zero_le_one hnR1
    set Nt : ℝ := ∑ j ∈ Finset.range (m + 1), nR ^ j with hNt
    have hNtnn : 0 ≤ Nt := Finset.sum_nonneg fun j _ => pow_nonneg hnRnn j
    set N1 : ℝ := (Fintype.card ι₀ : ℝ) * nR * nR with hN1
    have hN1nn : 0 ≤ N1 := by rw [hN1]; positivity
    set Call : ℝ := ∑ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      (Ctr ab + 1) with hCall
    have hCallnn : 0 ≤ Call := by
      rw [hCall]; exact Finset.sum_nonneg fun ab _ => by linarith [hCtrnn ab]
    set Cfin : ℝ := Call * (1 + N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1))
      with hCfin
    have hCfinnn : 0 ≤ Cfin := by
      rw [hCfin]
      refine mul_nonneg hCallnn ?_
      have hK : 0 ≤ Kφ ^ 2 + 1 := by linarith [sq_nonneg Kφ]
      have h1 : 0 ≤ N1 * Cmul := mul_nonneg hN1nn hCmulnn
      have h2 : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) := mul_nonneg h1 hK
      have h3 : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) :=
        mul_nonneg h2 (by linarith)
      have h4 : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) :=
        mul_nonneg h3 (by linarith)
      have h5 : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1) :=
        mul_nonneg h4 (by linarith)
      linarith
    refine ⟨Cfin, hCfinnn, ?_⟩
    intro h hsm φ hφ hφb hφs hφt a b β
    -- the reconstruction identity, as a function equality
    have hident : (fun z : Fin (Module.finrank ℝ E) → ℝ => ((φ z * D.mat j h a b z : ℝ) : ℂ))
        = fun z => ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              ((φ z * G (a, b) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt i z) := by
      funext z
      exact mat_eq_sum_of_partition (I := I) (M := M) D h j a b Kc ψ
        (fun i c d => G (a, b) i c d) Tt hψsum
        (fun i w hw => (hψsupp i (subset_closure (Function.mem_support.mpr hw))).2)
        hTtone
        (fun i c d z hz => hGone (a, b) i c d z hz)
        (fun i c d z hz => hGzero (a, b) i c d z hz)
        φ hφs z
    -- the summands, with the cut-off `φ` factored out
    set Z : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℂ
      := fun i c d z => ((G (a, b) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt i z) with hZ
    have hZsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (Z i c d) := by
      intro i c d
      have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z => ((G (a, b) i c d z : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (hGsm (a, b) i c d)
      have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z => D.Rper i h c d (Tt i z)) :=
        (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h c d
          (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm i c d)).1.comp
          (hTtsm i)
      simpa only [hZ, Pi.mul_apply] using h1.mul h2
    have hident' : (fun z : Fin (Module.finrank ℝ E) → ℝ => ((φ z * D.mat j h a b z : ℝ) : ℂ))
        = fun z => ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E), ((φ z : ℝ) : ℂ) * Z i c d z := by
      rw [hident]
      funext z
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun d _ => ?_
      rw [hZ]
      push_cast
      ring
    -- **Step A**: Cauchy–Schwarz over the finite sum and integration
    have hstepA : ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ => ((φ z * D.mat j h a b z : ℝ) : ℂ)) z‖ ^ 2
        ≤ N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              ∫ z in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdVec m β
                  (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2 := by
      rw [hident']
      have hlin : Work.Diff.STE.pdVec m β
            (fun z => ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E), ((φ z : ℝ) : ℂ) * Z i c d z)
          = fun z => ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z :=
        pdVec_sum3 β (fun i c d z => ((φ z : ℝ) : ℂ) * Z i c d z)
          (fun i c d => (Complex.ofRealCLM.contDiff.comp hφ).mul (hZsm i c d))
      rw [hlin]
      have hpt : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          ‖∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2
            ≤ N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2 := by
        intro z
        have h1 : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z)
            = ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t.1 t.2.1 t.2.2 z) z :=
          sum3_eq_sum_prod _
        have h2 : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2)
            = ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t.1 t.2.1 t.2.2 z) z‖ ^ 2 :=
          sum3_eq_sum_prod _
        rw [h1, h2]
        calc ‖∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t.1 t.2.1 t.2.2 z) z‖ ^ 2
            ≤ (∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t.1 t.2.1 t.2.2 z) z‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
          _ ≤ (Fintype.card (ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E))) : ℝ) *
                ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t.1 t.2.1 t.2.2 z) z‖ ^ 2 := by
              simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ι₀ ×
                  (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))))
                (f := fun t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) =>
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t.1 t.2.1 t.2.2 z) z‖))
          _ = N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z t.1 t.2.1 t.2.2 z) z‖ ^ 2 := by
              rw [hN1, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, hnR]
              push_cast
              ring
      have hcontZ' : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2) := by
        intro i c d
        have h := (continuous_pdVec_of_smooth
          ((Complex.ofRealCLM.contDiff.comp hφ).mul (hZsm i c d)) m β).norm
        convert h.mul h using 1
        ext z
        simp only [Pi.mul_apply, pow_two, Complex.ofRealCLM_apply, Function.comp_apply]
      have hcont1 : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ‖∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2) := by
        have hFc : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z) :=
          continuous_finset_sum (Finset.univ : Finset ι₀) (fun i _ =>
            continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun c _ =>
              continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun d _ =>
                continuous_pdVec_of_smooth ((Complex.ofRealCLM.contDiff.comp hφ).mul (hZsm i c d))
                  m β)))
        have h := hFc.norm
        convert h.mul h using 1
        ext z
        simp only [Pi.mul_apply, pow_two, Complex.ofRealCLM_apply, Function.comp_apply]
      have hcont2 : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2) := by
        have hFc : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2) :=
          continuous_finset_sum (Finset.univ : Finset ι₀) (fun i _ =>
            continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun c _ =>
              continuous_finset_sum (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun d _ =>
                hcontZ' i c d)))
        convert continuous_const.mul hFc using 1
        try (ext z; simp only [Pi.mul_apply])
      have hm := setIntegral_mono_on
        (Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real hcont1)
        (Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real hcont2)
        Work.Diff.STE.BesselCont.measSet_unitCube (fun x _ => hpt x)
      have hint : ∫ z in Work.Diff.STE.unitCube, N1 * ∑ i : ι₀,
            ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2
          = N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                ∫ z in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2 := by
        rw [integral_const_mul]
        congr 1
        rw [setIntegral_sum3 (F := fun (i : ι₀) (c d : Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) =>
            ‖Work.Diff.STE.pdVec m β (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2)]
        intro i c d
        exact Work.Diff.STE.csqp_integrableOn_unitCube_of_continuous_real (hcontZ' i c d)
      rw [hint] at hm
      exact hm
    -- **Step C**: the jet-peeling bound, termwise
    have hstepC : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec m β
            (fun z => ((φ z : ℝ) : ℂ) * Z i c d z) z‖ ^ 2
          ≤ Cmul * Kφ ^ 2 * ∑ j ∈ Finset.range (m + 1),
              ∑ γ : Fin j → Fin (Module.finrank ℝ E),
                ∫ z in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec j γ (Z i c d) z‖ ^ 2 :=
      fun i c d => hCmulb φ (Z i c d) Kφ hφ (hZsm i c d) hφb β
    -- **Step D**: the chart transfer, termwise
    have hstepD : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (j' : ℕ)
        (γ : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
        ∫ z in Work.Diff.STE.unitCube,
            ‖Work.Diff.STE.pdVec j' γ (Z i c d) z‖ ^ 2
          ≤ Ctr (a, b) * ∑ k ∈ Finset.range (j' + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2 := by
      intro i c d j' γ hj'
      have hper2 := (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h c d
        (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm i c d))
      have hcontZ : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ‖Work.Diff.STE.pdVec j' γ (Z i c d) z‖ ^ 2) :=
        ((continuous_pdVec_of_smooth (hZsm i c d) j' γ).norm).pow 2
      have hZfun : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          Z i c d z = ((G (a, b) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt i z) := by
        intro z
        rw [hZ]
      have hsub : tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ‖Work.Diff.STE.pdVec j' γ (Z i c d) z‖ ^ 2) ⊆ tsupport (G (a, b) i c d) := by
        have h1 : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ‖Work.Diff.STE.pdVec j' γ (Z i c d) z‖ ^ 2)
            ⊆ Function.support (Work.Diff.STE.pdVec j' γ (Z i c d)) := by
          intro z hz
          rw [Function.mem_support] at hz ⊢
          intro h0
          exact hz (by rw [h0]; simp)
        have h2 : Function.support (Work.Diff.STE.pdVec j' γ (Z i c d))
            ⊆ closure (Function.support (Z i c d)) :=
          Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn γ) (Z i c d)
        have h3 : Function.support (Z i c d) ⊆ Function.support (G (a, b) i c d) := by
          intro z hz
          rw [Function.mem_support] at hz ⊢
          intro h0
          exact hz (by rw [hZfun z, h0]; simp)
        calc tsupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              ‖Work.Diff.STE.pdVec j' γ (Z i c d) z‖ ^ 2)
            = closure (Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ‖Work.Diff.STE.pdVec j' γ (Z i c d) z‖ ^ 2)) := rfl
          _ ⊆ closure (Function.support (Work.Diff.STE.pdVec j' γ (Z i c d))) :=
              closure_mono h1
          _ ⊆ closure (closure (Function.support (Z i c d))) := closure_mono h2
          _ = closure (Function.support (Z i c d)) := closure_closure
          _ ⊆ closure (Function.support (G (a, b) i c d)) := closure_mono h3
          _ = tsupport (G (a, b) i c d) := rfl
      have hcpt : HasCompactSupport (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ‖Work.Diff.STE.pdVec j' γ (Z i c d) z‖ ^ 2) :=
        (hGcpt (a, b) i c d).of_isClosed_subset (isClosed_tsupport _) hsub
      refine (setIntegral_le_integral_of_compactSupport hcontZ hcpt
        (fun x => sq_nonneg _)).trans ?_
      have hGb' := hGb (a, b) i c d j' γ hj' (D.Rper i h c d) hper2.1 hper2.2
      exact hGb'
    -- **Step E**: counting the `(j,γ)` pairs
    have hstepE : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        (∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin (Module.finrank ℝ E),
            Ctr (a, b) * ∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
          ≤ Ctr (a, b) * Nt * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) := by
      intro i c d
      have hinner : ∀ j ∈ Finset.range (m + 1),
          (∑ γ : Fin j → Fin (Module.finrank ℝ E), Ctr (a, b) * ∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
            ≤ Ctr (a, b) * ((nR ^ j) * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) := by
        intro j hj
        have hjle : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hsub : (∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
            ≤ ∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro k hk
            exact Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hk) (Nat.succ_le_succ hjle))
          · intro k _ _
            exact Finset.sum_nonneg fun l' _ =>
              MeasureTheory.integral_nonneg fun x => sq_nonneg _
        have h1 : (∑ γ : Fin j → Fin (Module.finrank ℝ E), Ctr (a, b) * ∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
            = ((nR ^ j) * (Ctr (a, b) * (∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2))) := by
          rw [sum_fun_const]
        rw [h1]
        have h3 : Ctr (a, b) * (∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
            ≤ Ctr (a, b) * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsub (hCtrnn (a, b))
        calc (nR ^ j) * (Ctr (a, b) * (∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2))
            = Ctr (a, b) * ((nR ^ j) * (∑ k ∈ Finset.range (j + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) := by ring
          _ ≤ Ctr (a, b) * ((nR ^ j) * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsub (pow_nonneg hnRnn j))
                (hCtrnn (a, b))
      calc ∑ j ∈ Finset.range (m + 1), ∑ γ : Fin j → Fin (Module.finrank ℝ E),
              Ctr (a, b) * ∑ k ∈ Finset.range (j + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube,
                    ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2
          ≤ ∑ j ∈ Finset.range (m + 1), Ctr (a, b) * ((nR ^ j) *
              (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) :=
            Finset.sum_le_sum hinner
        _ = Ctr (a, b) * (∑ j ∈ Finset.range (m + 1), nR ^ j) *
              (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) := by
            rw [← Finset.mul_sum, ← Finset.sum_mul]
            ring
        _ ≤ Ctr (a, b) * Nt * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) := by
            rw [hNt]
    -- **Step F**: the Sobolev comparison
    have hstepF : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
            ∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
          ≤ Nt * Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d) := by
      intro i c d
      have hper1 := (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h c d
        (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm i c d))
      have hY : (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
            ∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
          ≤ ∑ k ∈ Finset.range (m + 1), ∑ _l' : Fin k → Fin (Module.finrank ℝ E),
              Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l' _ =>
          hCenvb (fun z => ((D.R i h c d z : ℝ) : ℂ)) (D.Rper i h c d)
            (Complex.ofRealCLM.contDiff.comp
              (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsm i c d))
            (fun z hz => D.R_support i h c d (by
              intro h0
              exact (Function.mem_support.mp hz) (by simp [h0])))
            hper1.1 hper1.2 (fun z => rfl) k l'
            (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      refine hY.trans ?_
      have h2 : (∑ k ∈ Finset.range (m + 1), ∑ _l' : Fin k → Fin (Module.finrank ℝ E),
              Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d))
          = (∑ k ∈ Finset.range (m + 1), nR ^ k) *
              (Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
        have h3 : ∀ k ∈ Finset.range (m + 1),
            (∑ _l' : Fin k → Fin (Module.finrank ℝ E),
              Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d))
              = (nR ^ k) * (Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
          intro k _
          rw [sum_fun_const]
        rw [Finset.sum_congr rfl h3, ← Finset.sum_mul]
      rw [h2]
      refine le_of_eq ?_
      rw [hNt]
      try ring
    -- **Step G**: assembly
    have hG1 : ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ => ((φ z * D.mat j h a b z : ℝ) : ℂ)) z‖ ^ 2
        ≤ N1 * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube,
                    ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2))) := by
      refine hstepA.trans (mul_le_mul_of_nonneg_left ?_ hN1nn)
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
        Finset.sum_le_sum fun d _ => ?_
      refine (hstepC i c d).trans (mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hCmulnn (sq_nonneg Kφ)))
      exact (Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun γ _ =>
        hstepD i c d j γ (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans (hstepE i c d)
    have hG2 : N1 * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (∑ k ∈ Finset.range (m + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube,
                    ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)))
        ≤ N1 * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt *
                (Nt * Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d)))) := by
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum
        fun c _ => Finset.sum_le_sum fun d _ => ?_) hN1nn
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hstepF i c d)
        (mul_nonneg (hCtrnn (a, b)) hNtnn)) (mul_nonneg hCmulnn (sq_nonneg Kφ))
    have hG3 : N1 * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt *
                (Nt * Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d))))
        = (N1 * Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))) *
            (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
      have h4 : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv *
            Work.Diff.STE.ENormSq m (D.Rper i h c d)))
            = (Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))) *
                Work.Diff.STE.ENormSq m (D.Rper i h c d) := fun i c d => by ring
      calc N1 * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt *
                (Nt * Cenv * Work.Diff.STE.ENormSq m (D.Rper i h c d))))
          = N1 * (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                (Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))) *
                  Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
              refine congrArg (fun x => N1 * x) ?_
              exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
                Finset.sum_congr rfl fun d _ => h4 i c d
        _ = (N1 * Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))) *
              (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E),
                  Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
              simp only [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
                Finset.sum_congr rfl fun d _ => ?_
              ring
    have hG4 : (N1 * Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))) *
            (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.ENormSq m (D.Rper i h c d))
        ≤ Cfin * (1 + ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
      have hSnn : 0 ≤ ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E),
            Work.Diff.STE.ENormSq m (D.Rper i h c d) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
          Finset.sum_nonneg fun d _ => ENormSq_nonneg m _
      have hCtr_le : Ctr (a, b) ≤ Call := by
        rw [hCall]
        exact (by linarith [hCtrnn (a, b)] :
            Ctr (a, b) ≤ Ctr (a, b) + 1).trans (Finset.single_le_sum
          (f := fun ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) =>
            (Ctr ab + 1)) (fun ab _ => by linarith [hCtrnn ab]) (Finset.mem_univ (a, b)))
      have hK1 : Kφ ^ 2 ≤ Kφ ^ 2 + 1 := by linarith
      have hKnn : (0 : ℝ) ≤ Kφ ^ 2 + 1 := by linarith [sq_nonneg Kφ]
      have hNt1 : Nt ≤ Nt + 1 := by linarith
      have hCe1 : Cenv ≤ Cenv + 1 := by linarith
      have hcoef : N1 * Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))
          ≤ Call * (N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1)) := by
        have hNt2 : 0 ≤ Nt * (Nt * Cenv) := mul_nonneg hNtnn (mul_nonneg hNtnn hCenvnn)
        have ha : N1 * Cmul * Kφ ^ 2 ≤ N1 * Cmul * (Kφ ^ 2 + 1) :=
          mul_le_mul_of_nonneg_left hK1 (mul_nonneg hN1nn hCmulnn)
        have hb : Ctr (a, b) * (Nt * (Nt * Cenv))
            ≤ Call * ((Nt + 1) * ((Nt + 1) * (Cenv + 1))) := by
          refine mul_le_mul hCtr_le ?_ hNt2 hCallnn
          refine mul_le_mul hNt1 ?_ (mul_nonneg hNtnn hCenvnn) (by linarith : (0:ℝ) ≤ Nt + 1)
          exact mul_le_mul hNt1 hCe1 hCenvnn (by linarith : (0:ℝ) ≤ Nt + 1)
        have hNt2' : 0 ≤ Ctr (a, b) * (Nt * (Nt * Cenv)) := mul_nonneg (hCtrnn (a, b)) hNt2
        have hprod := mul_le_mul ha hb hNt2'
          (mul_nonneg (mul_nonneg hN1nn hCmulnn) hKnn)
        calc N1 * Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))
            = (N1 * Cmul * Kφ ^ 2) * (Ctr (a, b) * (Nt * (Nt * Cenv))) := by ring
          _ ≤ (N1 * Cmul * (Kφ ^ 2 + 1)) * (Call * ((Nt + 1) * ((Nt + 1) * (Cenv + 1)))) := hprod
          _ = Call * (N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1)) := by ring
      have hXnn : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1) := by
        have h1 : 0 ≤ N1 * Cmul := mul_nonneg hN1nn hCmulnn
        have h2 : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) := mul_nonneg h1 hKnn
        have h3 : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) := mul_nonneg h2 (by linarith)
        have h4 : 0 ≤ N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) :=
          mul_nonneg h3 (by linarith)
        exact mul_nonneg h4 (by linarith)
      calc (N1 * Cmul * Kφ ^ 2 * (Ctr (a, b) * Nt * (Nt * Cenv))) *
              (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.ENormSq m (D.Rper i h c d))
          ≤ (Call * (N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1))) *
              (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.ENormSq m (D.Rper i h c d)) :=
            mul_le_mul_of_nonneg_right hcoef hSnn
        _ ≤ (Call * (N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1))) *
              (1 + ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.ENormSq m (D.Rper i h c d)) :=
            mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCallnn hXnn)
        _ ≤ (Call * (1 + N1 * Cmul * (Kφ ^ 2 + 1) * (Nt + 1) * (Nt + 1) * (Cenv + 1))) *
              (1 + ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by linarith)
            exact mul_le_mul_of_nonneg_left (by linarith) hCallnn
        _ = Cfin * (1 + ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
            rw [hCfin]
    have hLHS : Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
          (fun z : Fin (Module.finrank ℝ E) → ℝ => ((φ z * D.mat j h a b z : ℝ) : ℂ)))
        = ∫ z in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ => ((φ z * D.mat j h a b z : ℝ) : ℂ)) z‖ ^ 2 := by
      simp [Work.Diff.STE.ENormSq, Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
    rw [hLHS]
    exact hG1.trans (hG2.trans (hG3.trans_le hG4))
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hsm φ hφ hφb hφs hφt a b β
    exact absurd hφt hKO

end Work.Diff.STE.B3
