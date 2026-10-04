import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.mat_ENormSq_le_clean
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.B3.goodSet_smooth_noT2
import Submission.Work.Diff.STE.B3.tMapFun_injOn_det
import Submission.Work.Diff.STE.Lead.Gal.gardADefs
import Submission.Work.Diff.STE.Lead.GalTame.Rper_ENormSq_zero_pdVec_le_top
import Submission.Work.Diff.STE.Lead.GalTame.ENormB_mono_level
import Submission.Work.Diff.STE.Lead.GalTame.Rper_lowJet_le_energy
import Submission.Work.Diff.STE.Lead.GalTame.mulJet_le_sharp_univ
import Submission.Work.Diff.STE.Lead.GalTame.globalSmoothData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory

namespace Work.Diff.STE.Lead.GalTame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-- The good set of the pair `(i,j)` together with the non-vanishing of the weight `ζ i`. -/
def goodSetZeta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j ∧ D.ζ i (D.pt j z) ≠ 0}

lemma goodSetZeta_subset_goodSet (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    goodSetZeta (I := I) (M := M) D i j ⊆ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j :=
  fun _ hz => hz.1

lemma isOpen_goodSetZeta (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀) :
    IsOpen (goodSetZeta (I := I) (M := M) D i j) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have h1 : Work.Diff.STE.D.goodSet (I := I) (M := M) D i j ∈ 𝓝 z :=
    Work.Diff.STE.B3.tMapFun_goodSet_mem_nhds (I := I) (M := M) D i j hz.1
  have h2 : (fun w => D.ζ i (D.pt j w)) ⁻¹' {x : ℝ | x ≠ 0} ∈ 𝓝 z :=
    ((Work.Diff.STE.D.contDiffAt_zeta_pt (I := I) (M := M) D i j hz.1).continuousAt
      ).preimage_mem_nhds (isOpen_ne.mem_nhds hz.2)
  exact Filter.mem_of_superset (Filter.inter_mem h1 h2) fun w hw => ⟨hw.1, hw.2⟩

/-! ## 2. The reconstruction coefficient of the coordinate-frame chart matrix -/

/-- **The coefficient of the pointwise reconstruction of `Gf` in the components of chart `i`.**  At
a flat coordinate `z` of chart `j`, the coordinate-frame chart matrix `Gf D h j z a b` is the double
sum of the localised components `D.R i h c d (tMapFun D i j z)` against this coefficient (see
`Gf_eq_recoCoeff`).  It is the coefficient of `Work.Diff.STE.B3.mat_recon_gen` with `X`, `Y` the
coordinate-frame vectors `cFrame` of chart `j` (rather than the `g₀`-orthonormal frame `D.e j ·`). -/
def recoCoeffGf (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) : (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun z =>
    (D.ζ i (D.pt j z))⁻¹
      * ((Real.sqrt (D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)))⁻¹
        * (g₀.inner (D.pt j z) (Work.Diff.GE.cFrame (I := I) (D.x₀ j) a (D.pt j z))
              (D.e i c (D.pt j z))
          * g₀.inner (D.pt j z) (Work.Diff.GE.cFrame (I := I) (D.x₀ j) b (D.pt j z))
              (D.e i d (D.pt j z))))

/-- **The pointwise reconstruction of the coordinate-frame chart matrix.**  If `ζ i (pt j z) ≠ 0`
then `Gf D h j z a b = Σ_{c d} recoCoeffGf D i j a b c d z · R i h c d (tMapFun D i j z)`.  This is
`Work.Diff.STE.B3.mat_recon_gen` evaluated on the coordinate-frame vectors of chart `j`. -/
lemma Gf_eq_recoCoeff (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ)
    (hζ : D.ζ i (D.pt j z) ≠ 0) :
    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
      = ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
          recoCoeffGf (I := I) (M := M) D i j a b c d z
            * D.R i h c d (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) := by
  have hmain := Work.Diff.STE.B3.mat_recon_gen (I := I) (M := M) D h i (D.pt j z)
    (Work.Diff.GE.cFrame (I := I) (D.x₀ j) a (D.pt j z))
    (Work.Diff.GE.cFrame (I := I) (D.x₀ j) b (D.pt j z)) hζ
  rw [show Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
      = h (D.pt j z) (Work.Diff.GE.cFrame (I := I) (D.x₀ j) a (D.pt j z))
          (Work.Diff.GE.cFrame (I := I) (D.x₀ j) b (D.pt j z)) from by
        simp only [Work.Diff.STE.B3.Gf, Work.Diff.STE.B3.yf,
          Work.Diff.STE.D.chartMatOf_apply, Work.Diff.GE.cFrame_apply, Work.Diff.GE.cBasis,
          Work.Diff.EXT.bB, Work.Diff.STE.B3Data.pt]
        try rfl, hmain]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [recoCoeffGf, Work.Diff.STE.D.tMapFun]
  ring_nf

/-! ## 3. Smoothness of the reconstruction coefficient -/

/-- The metric pairing of the **coordinate-frame** vector of chart `j` against the smooth field
`e i c`, composed with `pt j`, is `C^∞` at a point of `goodSet`. -/
lemma contDiffAt_pairing_cFrame_pt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (i j : ι₀) (a c : Fin (Module.finrank ℝ E))
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ Work.Diff.STE.D.goodSet (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (Work.Diff.GE.cFrame (I := I) (D.x₀ j) a (D.pt j w))
        (D.e i c (D.pt j w))) z := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g₀.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M => TangentSpace I x) := inferInstance
  have hsrc : D.pt j z ∈ (chartAt H (D.x₀ j)).source := by
    have h1 : D.pt j z ∈ (extChartAt I (D.x₀ j)).source :=
      (extChartAt I (D.x₀ j)).map_target (interior_subset hz.1)
    rwa [extChartAt_source] at h1
  have hX : CMDiffAt (⊤ : ℕ∞) (T% (Work.Diff.GE.cFrame (I := I) (D.x₀ j) a)) (D.pt j z) :=
    Submission.Geodesic.contMDiffAt_frameSection (I := I) (D.x₀ j)
      (Work.Diff.GE.cBasis (E := E) a) hsrc
  have hpt := Work.Diff.STE.D.pt_contMDiffAt_of_mem_interior (I := I) D j z hz.1
  have hpair := Work.EXT.ONF.pairing g₀ (D.pt j z) hX ((D.hesm i c).contMDiffAt)
  exact contMDiffAt_iff_contDiffAt.mp (hpair.comp z hpt)

/-- **The reconstruction coefficient is smooth wherever it is genuine.**  At a point of the good set
at which moreover `ζ i (pt j z) ≠ 0`, `recoCoeffGf` is `C^∞`. -/
lemma recoCoeffGf_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : z ∈ goodSetZeta (I := I) (M := M) D i j) :
    ContDiffAt ℝ (⊤ : ℕ∞) (recoCoeffGf (I := I) (M := M) D i j a b c d) z := by
  obtain ⟨hzgood, hζ⟩ := hz
  have hsrc : D.pt j z ∈ (extChartAt I (D.x₀ i)).source := hzgood.2.1
  have hflat : Work.Diff.STE.flatToE (I := I) (D.x₀ i)
      (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z)
      = (extChartAt I (D.x₀ i)) (D.pt j z) := by
    rw [Work.Diff.STE.D.tMapFun]
    exact Work.Diff.STE.D.flatToE_coord (I := I) (M := M) D i hsrc
  have hT : ContDiffAt ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j) z :=
    Work.Diff.STE.D.tMapFun_contDiffAt (I := I) (M := M) D i j hzgood
  have hzeta : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => D.ζ i (D.pt j w)) z :=
    Work.Diff.STE.D.contDiffAt_zeta_pt (I := I) (M := M) D i j hzgood
  have hzetainv : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => (D.ζ i (D.pt j w))⁻¹) z :=
    hzeta.inv hζ
  have hdens : ContDiffAt ℝ (⊤ : ℕ∞) (D.dens i)
      (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) :=
    Work.Diff.STE.D.dens_interior_contDiffAt (I := I) D i _
      (by rw [hflat]; exact hzgood.2.2)
  have hdenspos : 0 < D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) :=
    Work.Diff.STE.B3.dens_pos_of_mem_target (I := I) D i
      (by rw [hflat]; exact interior_subset hzgood.2.2)
  have hsqrt : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => Real.sqrt (D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j w))) z :=
    ((Real.contDiffAt_sqrt hdenspos.ne').comp _ hdens).comp z hT
  have hsqrtinv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => (Real.sqrt (D.dens i (Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j w)))⁻¹) z :=
    hsqrt.inv (Real.sqrt_pos.mpr hdenspos).ne'
  have hp1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (Work.Diff.GE.cFrame (I := I) (D.x₀ j) a (D.pt j w))
        (D.e i c (D.pt j w))) z :=
    contDiffAt_pairing_cFrame_pt (I := I) (M := M) D i j a c hzgood
  have hp2 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w => g₀.inner (D.pt j w) (Work.Diff.GE.cFrame (I := I) (D.x₀ j) b (D.pt j w))
        (D.e i d (D.pt j w))) z :=
    contDiffAt_pairing_cFrame_pt (I := I) (M := M) D i j b d hzgood
  exact hzetainv.mul (hsqrtinv.mul (hp1.mul hp2))

/-- `recoCoeffGf` is `C^∞` on the good set. -/
lemma recoCoeffGf_contDiffOn (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i j : ι₀)
    (a b c d : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (recoCoeffGf (I := I) (M := M) D i j a b c d)
      (goodSetZeta (I := I) (M := M) D i j) :=
  fun _ hz => (recoCoeffGf_contDiffAt (I := I) (M := M) D i j a b c d hz).contDiffWithinAt

/-! ## 4. The global reconstruction identity -/

/-- **The global reconstruction identity for `Gf`.**  If `ψ` is a partition (on `Kc`) subordinated to
the non-vanishing of the weights and `G` is a coefficient family which agrees with
`ψ i · recoCoeffGf D i j a b c d` where `ψ i ≠ 0` and vanishes where `ψ i = 0`, then

`φ · Gf = Σ_i Σ_cd (φ · G i c d) · (Rper i h c d ∘ Tt i)`

as complex-valued functions, for every `φ` with `tsupport φ ⊆ Kc`. -/
theorem Gf_eq_sum_of_partition (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
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
      G i c d z = ψ i z * recoCoeffGf (I := I) (M := M) D i j a b c d z)
    (hG0 : ∀ i c d z, ψ i z = 0 → G i c d z = 0)
    (φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hφs : tsupport φ ⊆ Kc) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      ((φ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b : ℝ) : ℂ)
        = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ((φ z * G i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt i z) := by
  have hreal : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      φ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
        = ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            (φ z * G i c d z) * D.R i h c d (Tt i z) := by
    intro z
    by_cases hφz : φ z = 0
    · simp only [hφz, zero_mul, Finset.sum_const_zero]
    · have hzKc : z ∈ Kc := hφs (subset_closure (Function.mem_support.mpr hφz))
      have hsumψ : ∑ i, ψ i z = 1 := hψsum z hzKc
      have h1 : φ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b
          = ∑ i : ι₀, (φ z * ψ i z) * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hsumψ, mul_one]
      rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hψi : ψ i z = 0
      · rw [hψi, mul_zero, zero_mul]
        have hzero : ∀ (c d : Fin (Module.finrank ℝ E)),
            (φ z * G i c d z) * D.R i h c d (Tt i z) = 0 := fun c d => by
          rw [hG0 i c d z hψi, mul_zero, zero_mul]
        simp only [hzero, Finset.sum_const_zero]
      · have hrec := Gf_eq_recoCoeff (I := I) (M := M) D h i j a b z (hψζ i z hψi)
        rw [hrec]
        have hstep : (φ z * ψ i z) * (∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                recoCoeffGf (I := I) (M := M) D i j a b c d z
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

/-! ## 5. The flat target region and the covering by the good sets -/

/-- The flat target region of the chart `j`: the set of flat coordinates whose `flatToE`-image lies
in the target of the extended chart. -/
def flatTarget (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    Set (Fin (Module.finrank ℝ E) → ℝ) :=
  {z | Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target}

lemma isOpen_flatTarget (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    IsOpen (flatTarget (I := I) (M := M) D j) :=
  (isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
    (Work.Diff.STE.B3.flatToE_contDiff (I := I) (D.x₀ j)).continuous

/-- The good sets with non-vanishing weights cover the flat target region. -/
theorem flatTarget_subset_iUnion_goodSetZeta
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) :
    flatTarget (I := I) (M := M) D j ⊆ ⋃ i, goodSetZeta (I := I) (M := M) D i j := by
  intro z hz
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

/-! ## 6. The whole-space `Hᵐ` energy bound for the cut coordinate-frame chart matrix -/

section Assembly

/-- `pdVec` of a globally smooth function is continuous. -/
private lemma continuous_pdVec_smooth {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) (l : Fin m → Fin n) :
    Continuous (Work.Diff.STE.pdVec m l f) :=
  Work.Diff.STE.continuous_pdVec m l f (hf.of_le (WithTop.coe_le_coe.mpr le_top))

/-- Reassociating a triple sum as a sum over the product index. -/
private lemma sum3_eq_sum_prod {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    {A : Type*} [AddCommMonoid A] (f : ι → κ → ν → A) :
    (∑ i, ∑ k, ∑ j, f i k j) = ∑ t : ι × (κ × ν), f t.1 t.2.1 t.2.2 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]

/-- Linearity of `pdVec` over a triple finite sum. -/
private lemma pdVec_sum3 {n m : ℕ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
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

/-- The sum over the tuples `Fin j → Fin n` of a constant. -/
private lemma sum_fun_const {n j : ℕ} (c : ℝ) :
    (∑ _ : Fin j → Fin n, c) = ((n : ℝ) ^ j) * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, nsmul_eq_mul]
  simp only [Fintype.card_fin, Nat.cast_pow]

/-- The `Hᵐ` energy is nonnegative. -/
private lemma ENormSq_nonneg_loc {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq m f :=
  Finset.sum_nonneg fun l _ => MeasureTheory.integral_nonneg fun x => sq_nonneg _

/-- **Integrability of the squared norm of a jet of a compactly supported smooth function.** -/
private lemma integrable_normSq_pdVec {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hsub : Function.support f ⊆ K) (m : ℕ) (l : Fin m → Fin n) :
    Integrable (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec m l f z‖ ^ 2) := by
  have hcont : Continuous (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec m l f z‖ ^ 2) := by
    have h := (continuous_pdVec_smooth hf m l).norm
    convert h.mul h using 1
    ext z
    simp only [Pi.mul_apply, pow_two]
  refine hcont.integrable_of_hasCompactSupport ?_
  refine IsCompact.of_isClosed_subset hK (isClosed_tsupport _) ?_
  have h1 : Function.support (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec m l f z‖ ^ 2)
      ⊆ Function.support (Work.Diff.STE.pdVec m l f) := by
    intro z hz
    rw [Function.mem_support] at hz ⊢
    intro h0
    exact hz (by rw [h0]; norm_num)
  have h2 : Function.support (Work.Diff.STE.pdVec m l f) ⊆ K := by
    rw [Work.Diff.STE.pdVec]
    exact (Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn l) f).trans
      (closure_minimal hsub hK.isClosed)
  exact closure_minimal (h1.trans h2) hK.isClosed

/-- The integral of a triple finite sum (whole space). -/
private lemma integral_sum3 {n : ℕ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (F : ι → κ → ν → (Fin n → ℝ) → ℝ)
    (hF : ∀ i k j, Integrable (F i k j)) :
    ∫ z : Fin n → ℝ, ∑ i, ∑ k, ∑ j, F i k j z = ∑ i, ∑ k, ∑ j, ∫ z : Fin n → ℝ, F i k j z := by
  rw [MeasureTheory.integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [MeasureTheory.integral_finset_sum]
      intro j _
      exact hF i k j
    · exact fun k _ => integrable_finset_sum _ fun j _ => hF i k j
  · exact fun i _ => integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun j _ => hF i k j

/-- **The whole-space `Hᵐ` energy bound for `χ · Gf`, given a compact set containing the support of
`χ` and lying in the flat target of the chart.**  The constant is uniform in the section `h`, in the
cut-off `χ` and in the frame indices `p q`. -/
theorem Gf_jet_energy_le
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀) (m : ℕ)
    (Kc : Set (Fin (Module.finrank ℝ E) → ℝ)) (hKc : IsCompact Kc)
    (hKO : Kc ⊆ flatTarget (I := I) (M := M) D j) (Mχ : ℝ) (hMχ : 0 ≤ Mχ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (χ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
        (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
        (hχb : ∀ (r : ℕ), r ≤ m → ∀ (γ : Fin r → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ), |Work.Diff.STE.pdRVec r γ χ z| ≤ Mχ)
        (hχts : tsupport χ ⊆ Kc) (p q : Fin (Module.finrank ℝ E)),
        ∑ β : Fin m → Fin (Module.finrank ℝ E),
          ∫ z : Fin (Module.finrank ℝ E) → ℝ,
            ‖Work.Diff.STE.pdVec m β
              (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ((χ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q : ℝ) : ℂ)) z‖ ^ 2
          ≤ C * (1 + D.ENormB m h) := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · refine ⟨0, le_refl 0, ?_⟩
    intro h hsmooth χ hχ hχb hχts p q
    exact Fin.elim0 (hn ▸ p)
  have hn1 : 1 ≤ Module.finrank ℝ E := Nat.pos_of_ne_zero hn
  haveI hne : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hn1⟩⟩
  -- ## the smooth global data attached to the compact set, for every pair of frame indices
  have hdata : ∀ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      ∃ (ψ : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
        (Tt : ι₀ → (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ))
        (U : ι₀ → Set (Fin (Module.finrank ℝ E) → ℝ))
        (G : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (Ctr : ℝ),
        (∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) ∧
        (∀ i, tsupport (ψ i) ⊆ goodSetZeta (I := I) (M := M) D i j) ∧
        (∀ i, HasCompactSupport (ψ i)) ∧
        (∀ z ∈ Kc, ∑ i, ψ i z = 1) ∧
        (∀ i, IsOpen (U i)) ∧
        (∀ i, U i ⊆ goodSetZeta (I := I) (M := M) D i j) ∧
        (∀ i, ContDiff ℝ (⊤ : ℕ∞) (Tt i)) ∧
        (∀ i, tsupport (ψ i) ⊆ U i) ∧
        (∀ i, Set.InjOn (Tt i) (U i)) ∧
        (∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), z ∈ U i →
          (fderiv ℝ (Tt i) z).det ≠ 0) ∧
        (∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), z ∈ U i →
          Tt i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) ∧
        (∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ψ i z ≠ 0 →
          Tt i z = Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j z) ∧
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞) (G i c d)) ∧
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)), HasCompactSupport (G i c d)) ∧
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
          tsupport (G i c d) ⊆ goodSetZeta (I := I) (M := M) D i j) ∧
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ψ i z ≠ 0 → G i c d z = ψ i z * recoCoeffGf (I := I) (M := M) D i j ab.1 ab.2 c d z) ∧
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ψ i z = 0 → G i c d z = 0) ∧
        0 ≤ Ctr ∧
        (∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (j' : ℕ)
          (γ : Fin j' → Fin (Module.finrank ℝ E)), j' ≤ m →
          ∀ (u : (Fin (Module.finrank ℝ E) → ℝ) → ℂ),
          ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
          ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec j' γ
              (fun z => ((G i c d z : ℝ) : ℂ) * u (Tt i z)) z‖ ^ 2
            ≤ Ctr * ∑ k ∈ Finset.range (j' + 1),
                ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                  ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' u x‖ ^ 2) :=
    fun ab => globalSmoothData (n := Module.finrank ℝ E) (Kc := Kc) hKc
      (V := fun i => goodSetZeta (I := I) (M := M) D i j)
      (fun i => isOpen_goodSetZeta (I := I) (M := M) D i j)
      (fun z hz => flatTarget_subset_iUnion_goodSetZeta (I := I) (M := M) D j (hKO hz))
      (fun i => Work.Diff.STE.D.tMapFun (I := I) (M := M) D i j)
      (fun i => (Work.Diff.STE.B3.noT2_tMapFun_contDiffOn (I := I) (M := M) D i j).mono
        (goodSetZeta_subset_goodSet (I := I) (M := M) D i j))
      (fun i => (Work.Diff.STE.B3.injOn_tMapFun_goodSet (I := I) (M := M) D i j).mono
        (goodSetZeta_subset_goodSet (I := I) (M := M) D i j))
      (fun i z hz => Work.Diff.STE.B3.tMapFun_det_ne_zero (I := I) (M := M) D i j
        (goodSetZeta_subset_goodSet (I := I) (M := M) D i j hz))
      (fun i c d => recoCoeffGf (I := I) (M := M) D i j ab.1 ab.2 c d)
      (fun i c d => recoCoeffGf_contDiffOn (I := I) (M := M) D i j ab.1 ab.2 c d)
      m
  choose ψ Tt U G Ctr hψsm hψsupp hψcpt hψsum hUopen hUsub hTtsm hUtsp hTinj hTdet hTteq hTtone
    hGsm hGcpt hGgood hGone hGzero hCtrnn hGb using hdata
  -- ## the constants
  obtain ⟨Clow, hClownn, hClowb⟩ :=
    Rper_lowJet_le_energy (I := I) (M := M) D m (Nat.pos_of_ne_zero hn)
  obtain ⟨Cmul, hMulnn, hMulb⟩ := mulJet_le_sharp_univ (Module.finrank ℝ E) m
  set nR : ℝ := ((Module.finrank ℝ E : ℕ) : ℝ) with hnR
  set Nt : ℝ := ∑ jj ∈ Finset.range (m + 1), nR ^ jj with hNt
  set N1 : ℝ := (Fintype.card ι₀ : ℝ) * nR * nR with hN1
  set Nβ : ℝ := (Fintype.card (Fin m → Fin (Module.finrank ℝ E)) : ℝ) with hNβ
  set Ctot : ℝ := ∑ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), (Ctr ab + 1)
    with hCtot
  have hnRnn : 0 ≤ nR := by rw [hnR]; positivity
  have hNtnn : 0 ≤ Nt := Finset.sum_nonneg fun jj _ => pow_nonneg hnRnn jj
  have hN1nn : 0 ≤ N1 := by rw [hN1]; positivity
  have hNβnn : 0 ≤ Nβ := by rw [hNβ]; positivity
  have hCtotnn : 0 ≤ Ctot := by
    rw [hCtot]
    exact Finset.sum_nonneg fun ab _ => by linarith [hCtrnn ab]
  have hCtrle : ∀ ab : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
      Ctr ab ≤ Ctot := by
    intro ab
    have h2 : Ctr ab ≤ Ctr ab + 1 := by linarith [hCtrnn ab]
    have h3 : Ctr ab + 1 ≤ Ctot := by
      rw [hCtot]
      exact Finset.single_le_sum (f := fun ab' : Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) => (Ctr ab' + 1))
        (fun ab' _ => by linarith [hCtrnn ab']) (Finset.mem_univ ab)
    linarith
  set K₀ : ℝ := N1 * Cmul * Mχ ^ 2 * Ctot * Nt * Nt * Clow with hK₀
  have hK₀nn : 0 ≤ K₀ := by
    rw [hK₀]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg hN1nn hMulnn) (sq_nonneg Mχ)) hCtotnn) hNtnn) hNtnn) hClownn
  refine ⟨K₀ * Nβ, mul_nonneg hK₀nn hNβnn, ?_⟩
  intro h hsmooth χ hχ hχb hχts p q
  -- ## the reconstruction identity, for the frame indices `p q`
  have hident : (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((χ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q : ℝ) : ℂ))
      = fun z => ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E),
            ((χ z * G (p, q) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt (p, q) i z) := by
    funext z
    exact Gf_eq_sum_of_partition (I := I) (M := M) D h j p q Kc (ψ (p, q)) (G (p, q)) (Tt (p, q))
      (hψsum (p, q))
      (fun i w hw => (hψsupp (p, q) i (subset_closure (Function.mem_support.mpr hw))).2)
      (hTtone (p, q))
      (fun i c d w hw => hGone (p, q) i c d w hw)
      (fun i c d w hw => hGzero (p, q) i c d w hw)
      χ hχts z
  -- ## the reconstruction terms
  set W : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun i c d z => ((G (p, q) i c d z : ℝ) : ℂ) *
      D.Rper i h c d (Tt (p, q) i z) with hWdef
  have hWsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞) (W i c d) := by
    intro i c d
    rw [hWdef]
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        ((G (p, q) i c d z : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (hGsm (p, q) i c d)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin (Module.finrank ℝ E) → ℝ =>
        D.Rper i h c d (Tt (p, q) i z)) :=
      (Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData (I := I) (M := M) D h hsmooth
        i c d).1.comp (hTtsm (p, q) i)
    exact h1.mul h2
  have hWcpt : ∀ i c d, HasCompactSupport (W i c d) := by
    intro i c d
    refine (hGcpt (p, q) i c d).of_isClosed_subset (isClosed_tsupport _) ?_
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro z hz
    rw [Function.mem_support] at hz
    by_contra hzG
    refine hz ?_
    show ((G (p, q) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt (p, q) i z) = 0
    rw [image_eq_zero_of_notMem_tsupport hzG]
    simp
  -- ## the per-`β` bound
  have hβ : ∀ β : Fin m → Fin (Module.finrank ℝ E),
      ∫ z : Fin (Module.finrank ℝ E) → ℝ,
          ‖Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              ((χ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q : ℝ) : ℂ)) z‖ ^ 2
        ≤ K₀ * (1 + D.ENormB m h) := by
    intro β
    have hZsm : ∀ i c d, ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ => ((χ z : ℝ) : ℂ) * W i c d z) :=
      fun i c d => (Complex.ofRealCLM.contDiff.comp hχ).mul (hWsm i c d)
    have hZsupp : ∀ i c d, Function.support
        (fun z : Fin (Module.finrank ℝ E) → ℝ => ((χ z : ℝ) : ℂ) * W i c d z) ⊆ Kc := by
      intro i c d z hz
      rw [Function.mem_support] at hz
      by_contra hzK
      have hχz : χ z = 0 := by
        by_contra hne
        exact hzK (hχts (subset_closure (Function.mem_support.mpr hne)))
      exact hz (by rw [hχz]; simp)
    -- **Step A**: Cauchy--Schwarz over the finite index set, and integration
    have hA : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
          ‖Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              ((χ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q : ℝ) : ℂ)) z‖ ^ 2
        ≤ N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2 := by
      rw [hident]
      rw [show (fun z : Fin (Module.finrank ℝ E) → ℝ => ∑ i : ι₀,
            ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ((χ z * G (p, q) i c d z : ℝ) : ℂ) * D.Rper i h c d (Tt (p, q) i z))
          = fun z => ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E), ((χ z : ℝ) : ℂ) * W i c d z from by
        funext z
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun d _ => ?_
        rw [hWdef, Complex.ofReal_mul]
        ring]
      rw [pdVec_sum3 β (fun i c d z => ((χ z : ℝ) : ℂ) * W i c d z)
        (fun i c d => hZsm i c d)]
      have hpt : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
          ‖∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2
            ≤ N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2 := by
        intro z
        have h1 : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z)
            = ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z :=
          sum3_eq_sum_prod _
        have h2 : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2)
            = ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z‖ ^ 2 :=
          sum3_eq_sum_prod _
        rw [h1, h2]
        calc ‖∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
              Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z‖ ^ 2
            ≤ (∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                ‖Work.Diff.STE.pdVec m β
                  (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z‖) ^ 2 := by
              have h3 := norm_sum_le
                (Finset.univ : Finset (ι₀ × (Fin (Module.finrank ℝ E) ×
                  Fin (Module.finrank ℝ E))))
                (fun t => Work.Diff.STE.pdVec m β
                  (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z)
              have h4 : (0 : ℝ) ≤ ∑ t : ι₀ × (Fin (Module.finrank ℝ E) ×
                  Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β
                    (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z‖ :=
                Finset.sum_nonneg fun t _ => norm_nonneg _
              nlinarith [h3, h4, norm_nonneg (∑ t : ι₀ × (Fin (Module.finrank ℝ E) ×
                  Fin (Module.finrank ℝ E)),
                    Work.Diff.STE.pdVec m β
                      (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z)]
          _ ≤ (Fintype.card (ι₀ × (Fin (Module.finrank ℝ E) ×
                  Fin (Module.finrank ℝ E))) : ℝ) *
                ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β
                    (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z‖ ^ 2 :=
              sq_sum_le_card_mul_sum_sq
          _ = N1 * ∑ t : ι₀ × (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)),
                  ‖Work.Diff.STE.pdVec m β
                    (fun z => ((χ z : ℝ) : ℂ) * W t.1 t.2.1 t.2.2 z) z‖ ^ 2 := by
              rw [hN1, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, hnR]
              push_cast
              ring
      have hInt : Integrable (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
            ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2) := by
        have hcont : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2) := by
          refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun c _ =>
            continuous_finset_sum _ fun d _ => ?_
          have hh := (continuous_pdVec_smooth (hZsm i c d) m β).norm
          convert hh.mul hh using 1
          ext z
          simp only [Pi.mul_apply, pow_two]
        refine (hcont.const_mul N1).integrable_of_hasCompactSupport ?_
        refine IsCompact.of_isClosed_subset hKc (isClosed_tsupport _) ?_
        have hsub' : Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
            N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2) ⊆ Kc := by
          intro z hz
          rw [Function.mem_support] at hz
          by_contra hzK
          have hz' : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2) ≠ 0 :=
            fun h0 => hz (by rw [h0, mul_zero])
          apply hz'
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun c _ =>
            Finset.sum_eq_zero fun d _ => ?_
          have hterm : Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z = 0 :=
            Function.notMem_support.mp fun hmem =>
              hzK ((Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn β)
                (fun z => ((χ z : ℝ) : ℂ) * W i c d z)).trans
                (closure_minimal (hZsupp i c d) hKc.isClosed) hmem)
          rw [hterm]
          norm_num
        exact closure_minimal hsub' hKc.isClosed
      have h1 : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
            ‖∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E), ∑ d : Fin (Module.finrank ℝ E),
              Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2
          ≤ ∫ z : Fin (Module.finrank ℝ E) → ℝ,
              N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _) hInt
          (Filter.Eventually.of_forall hpt)
      have h2 : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
              N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E),
                  ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2
          = N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
              ∑ d : Fin (Module.finrank ℝ E),
                ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                  ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        congr 1
        rw [integral_sum3 (F := fun (i : ι₀) (c d : Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ) =>
              ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2)]
        intro i c d
        exact integrable_normSq_pdVec (hZsm i c d) hKc (hZsupp i c d) m β
      exact h1.trans (le_of_eq h2)
    -- **Step C**: the Leibniz bound, termwise
    have hC : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        ∫ z : Fin (Module.finrank ℝ E) → ℝ,
            ‖Work.Diff.STE.pdVec m β (fun z => ((χ z : ℝ) : ℂ) * W i c d z) z‖ ^ 2
          ≤ Cmul * Mχ ^ 2 * ∑ jj ∈ Finset.range (m + 1),
              ∑ γ : Fin jj → Fin (Module.finrank ℝ E),
                ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                  ‖Work.Diff.STE.pdVec jj γ (W i c d) z‖ ^ 2 :=
      fun i c d => hMulb χ (W i c d) Mχ hχ (hWsm i c d) (hWcpt i c d)
        (fun r hr γ z => hχb r hr γ z) β
    -- **Step D**: the transfer bound, termwise
    have hD : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (jj : ℕ)
        (γ : Fin jj → Fin (Module.finrank ℝ E)), jj ≤ m →
        ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec jj γ (W i c d) z‖ ^ 2
          ≤ Ctot * ∑ k ∈ Finset.range (jj + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
              ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2 := by
      intro i c d jj γ hj
      have hR := Work.Diff.STE.Lead.Gal.Rper_contDiff_periodic_of_chartData (I := I) (M := M)
        D h hsmooth i c d
      refine (hGb (p, q) i c d jj γ hj (D.Rper i h c d) hR.1 hR.2).trans ?_
      refine mul_le_mul_of_nonneg_right (hCtrle (p, q)) ?_
      exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l' _ =>
        MeasureTheory.integral_nonneg fun x => sq_nonneg _
    -- **Step E**: counting the `(jj,γ)` pairs
    have hE : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        (∑ jj ∈ Finset.range (m + 1), ∑ γ : Fin jj → Fin (Module.finrank ℝ E),
            Ctot * ∑ k ∈ Finset.range (jj + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
              ∫ x in Work.Diff.STE.unitCube,
                ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
          ≤ Ctot * Nt * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) := by
      intro i c d
      have hinner : ∀ jj ∈ Finset.range (m + 1),
          (∑ γ : Fin jj → Fin (Module.finrank ℝ E),
              Ctot * ∑ k ∈ Finset.range (jj + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
            ≤ Ctot * ((nR ^ jj) * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) := by
        intro jj hj
        have hjle : jj ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hsub : (∑ k ∈ Finset.range (jj + 1),
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
        have h1 : (∑ γ : Fin jj → Fin (Module.finrank ℝ E),
              Ctot * ∑ k ∈ Finset.range (jj + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
            = (nR ^ jj) * (Ctot * (∑ k ∈ Finset.range (jj + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) := by
          rw [sum_fun_const]
        rw [h1]
        have h3 : Ctot * (∑ k ∈ Finset.range (jj + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
            ≤ Ctot * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsub hCtotnn
        calc (nR ^ jj) * (Ctot * (∑ k ∈ Finset.range (jj + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2))
            = Ctot * ((nR ^ jj) * (∑ k ∈ Finset.range (jj + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) := by ring
          _ ≤ Ctot * ((nR ^ jj) * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hsub (pow_nonneg hnRnn jj)) hCtotnn
      calc ∑ jj ∈ Finset.range (m + 1), ∑ γ : Fin jj → Fin (Module.finrank ℝ E),
              Ctot * ∑ k ∈ Finset.range (jj + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2
          ≤ ∑ jj ∈ Finset.range (m + 1), Ctot * ((nR ^ jj) *
              (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)) :=
            Finset.sum_le_sum hinner
        _ = Ctot * (∑ jj ∈ Finset.range (m + 1), nR ^ jj) *
              (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) := by
            rw [← Finset.mul_sum, ← Finset.sum_mul]
            ring
        _ ≤ Ctot * Nt * (∑ k ∈ Finset.range (m + 1),
              ∑ l' : Fin k → Fin (Module.finrank ℝ E),
                ∫ x in Work.Diff.STE.unitCube,
                  ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2) := by
            rw [hNt]
    -- **Step F**: the low jets against the top-order energy
    have hF : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
        (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
            ∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
          ≤ Nt * Clow * Work.Diff.STE.ENormSq m (D.Rper i h c d) := by
      intro i c d
      have hY : (∑ k ∈ Finset.range (m + 1), ∑ l' : Fin k → Fin (Module.finrank ℝ E),
            ∫ x in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec k l' (D.Rper i h c d) x‖ ^ 2)
          ≤ ∑ k ∈ Finset.range (m + 1), ∑ _l' : Fin k → Fin (Module.finrank ℝ E),
              Clow * Work.Diff.STE.ENormSq m (D.Rper i h c d) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l' _ =>
          hClowb h hsmooth i c d k l' (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
      refine hY.trans ?_
      have h2 : (∑ k ∈ Finset.range (m + 1), ∑ _l' : Fin k → Fin (Module.finrank ℝ E),
              Clow * Work.Diff.STE.ENormSq m (D.Rper i h c d))
          = (∑ k ∈ Finset.range (m + 1), nR ^ k) *
              (Clow * Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
        have h3 : ∀ k ∈ Finset.range (m + 1),
            (∑ _l' : Fin k → Fin (Module.finrank ℝ E),
              Clow * Work.Diff.STE.ENormSq m (D.Rper i h c d))
              = (nR ^ k) * (Clow * Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
          intro k _
          rw [sum_fun_const]
        rw [Finset.sum_congr rfl h3, ← Finset.sum_mul]
      rw [h2, hNt]
      exact le_of_eq (by ring)
    -- **Step G**: assembling the per-`β` bound
    have hstep1 : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
          ‖Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              ((χ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q : ℝ) : ℂ)) z‖ ^ 2
        ≤ N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              (Cmul * Mχ ^ 2 * (Ctot * Nt * (Nt * Clow *
                Work.Diff.STE.ENormSq m (D.Rper i h c d)))) := by
      refine hA.trans (mul_le_mul_of_nonneg_left ?_ hN1nn)
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
        Finset.sum_le_sum fun d _ => ?_
      refine (hC i c d).trans (mul_le_mul_of_nonneg_left ?_
        (mul_nonneg hMulnn (sq_nonneg Mχ)))
      refine (Finset.sum_le_sum fun jj hjj => Finset.sum_le_sum fun γ _ =>
        hD i c d jj γ (Nat.le_of_lt_succ (Finset.mem_range.mp hjj))).trans ?_
      refine (hE i c d).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCtotnn hNtnn)
      exact (hF i c d).trans (le_of_eq (by ring))
    have hstep2 : N1 * ∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              (Cmul * Mχ ^ 2 * (Ctot * Nt * (Nt * Clow *
                Work.Diff.STE.ENormSq m (D.Rper i h c d))))
        ≤ K₀ * (1 + D.ENormB m h) := by
      have hsum2 : (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
            ∑ d : Fin (Module.finrank ℝ E),
              (Cmul * Mχ ^ 2 * (Ctot * Nt * (Nt * Clow *
                Work.Diff.STE.ENormSq m (D.Rper i h c d)))))
          = (Cmul * Mχ ^ 2 * (Ctot * Nt * (Nt * Clow))) *
              (∑ i : ι₀, ∑ c : Fin (Module.finrank ℝ E),
                ∑ d : Fin (Module.finrank ℝ E),
                  Work.Diff.STE.ENormSq m (D.Rper i h c d)) := by
        have h4 : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)),
            (Cmul * Mχ ^ 2 * (Ctot * Nt * (Nt * Clow *
              Work.Diff.STE.ENormSq m (D.Rper i h c d))))
              = (Cmul * Mχ ^ 2 * (Ctot * Nt * (Nt * Clow))) *
                  Work.Diff.STE.ENormSq m (D.Rper i h c d) := fun i c d => by ring
        simp only [h4, Finset.mul_sum]
      rw [hsum2, ← Work.Diff.STE.B3Data.ENormB]
      have hEnn : 0 ≤ D.ENormB m h := by
        simp only [Work.Diff.STE.B3Data.ENormB]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
          Finset.sum_nonneg fun d _ => ENormSq_nonneg_loc m _
      calc N1 * ((Cmul * Mχ ^ 2 * (Ctot * Nt * (Nt * Clow))) * D.ENormB m h)
          = K₀ * D.ENormB m h := by rw [hK₀]; ring
        _ ≤ K₀ * (1 + D.ENormB m h) := by
            refine mul_le_mul_of_nonneg_left (by linarith) hK₀nn
    exact hstep1.trans hstep2
  -- ## summing over the multi-indices
  calc ∑ β : Fin m → Fin (Module.finrank ℝ E),
        ∫ z : Fin (Module.finrank ℝ E) → ℝ,
          ‖Work.Diff.STE.pdVec m β
            (fun z : Fin (Module.finrank ℝ E) → ℝ =>
              ((χ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q : ℝ) : ℂ)) z‖ ^ 2
      ≤ ∑ _β : Fin m → Fin (Module.finrank ℝ E), K₀ * (1 + D.ENormB m h) := by
        exact Finset.sum_le_sum fun β _ => hβ β
    _ = (K₀ * Nβ) * (1 + D.ENormB m h) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hNβ]
        ring

end Assembly

/-- **The whole-space (`∫_{ℝⁿ}`) `Hᵐ` energy bound for the cut coordinate-frame chart matrix.**

For a smooth cutoff `χ` with `tsupport χ ⊆ Metric.ball 0 (2 σ_j + 2 δ)` (`δ` the uniform margin
produced below), the `m`-th jet of `χ · Gf` is controlled in `L²(ℝⁿ)` by `1 + D.ENormB m h`, where
`Gf = Work.Diff.STE.B3.Gf D h j` is the **coordinate-frame** chart matrix of the section `h`. -/
theorem ballMatJetGf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) (hk : 1 ≤ k)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K) :
    ∃ (δ : ℝ), 0 < δ ∧
      ∀ (m : ℕ) (hm : m ≤ k), ∀ (Mχ : ℝ), 0 ≤ Mχ → ∃ (C : ℝ), 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
            |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K)
          (j : ι₀)
          (χ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
          (hχ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) χ)
          (hχts : tsupport χ ⊆ Metric.ball 0 (2 * D.σ j + 2 * δ))
          (hχb : ∀ (r : ℕ), r ≤ m → ∀ (γ : Fin r → Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ), |Work.Diff.STE.pdRVec r γ χ z| ≤ Mχ)
          (p q : Fin (Module.finrank ℝ E)),
          ∑ β : Fin m → Fin (Module.finrank ℝ E),
            ∫ z : Fin (Module.finrank ℝ E) → ℝ,
              ‖Work.Diff.STE.pdVec m β
                (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ((χ z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q : ℝ) : ℂ)) z‖ ^ 2
            ≤ C * (1 + D.ENormB m h) := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · refine ⟨1, one_pos, ?_⟩
    intro m hm Mχ hMχ
    refine ⟨0, le_refl 0, ?_⟩
    intro h hsym hsmooth hell hub hjet j χ hχ hχts hχb p q
    exact Fin.elim0 (hn ▸ p)
  obtain ⟨δt, hδtpos, hδt⟩ := Work.Diff.STE.Lead.Gal.gardTargetDelta (I := I) (M := M) D
  refine ⟨δt / 2, half_pos hδtpos, ?_⟩
  intro m hm Mχ hMχ
  have hKc : ∀ jj : ι₀, IsCompact (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
      (2 * D.σ jj + 2 * (δt / 2))) := fun jj => isCompact_closedBall _ _
  have hKO : ∀ jj : ι₀, Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ)
      (2 * D.σ jj + 2 * (δt / 2)) ⊆ flatTarget (I := I) (M := M) D jj := by
    intro jj z hz
    have hz' : ‖z‖ ≤ 2 * D.σ jj + δt := by
      have h1 : ‖z‖ ≤ 2 * D.σ jj + 2 * (δt / 2) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      linarith
    exact hδt jj z hz'
  choose Cj hCjnn hCjb using fun jj : ι₀ =>
    Gf_jet_energy_le (I := I) (M := M) D jj m (Metric.closedBall 0 (2 * D.σ jj + 2 * (δt / 2)))
      (hKc jj) (hKO jj) Mχ hMχ
  refine ⟨∑ jj : ι₀, (Cj jj + 1), ?_, ?_⟩
  · have h1 : 0 ≤ ∑ jj : ι₀, (Cj jj + 1) :=
      Finset.sum_nonneg fun jj _ => by linarith [hCjnn jj]
    exact h1
  · intro h hsym hsmooth hell hub hjet j χ hχ hχts hχb p q
    have hEnn : 0 ≤ D.ENormB m h := by
      simp only [Work.Diff.STE.B3Data.ENormB]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun c _ =>
        Finset.sum_nonneg fun d _ => ENormSq_nonneg_loc m _
    have hle : Cj j ≤ ∑ jj : ι₀, (Cj jj + 1) := by
      have h2 : Cj j ≤ Cj j + 1 := by linarith [hCjnn j]
      have h3 : Cj j + 1 ≤ ∑ jj : ι₀, (Cj jj + 1) := by
        have h4 := Finset.single_le_sum (f := fun jj : ι₀ => (Cj jj + 1))
          (fun jj _ => by linarith [hCjnn jj]) (Finset.mem_univ j)
        simpa using h4
      linarith
    refine (hCjb j h hsmooth χ ?_ (fun r hr γ z => hχb r hr γ z) ?_ p q).trans ?_
    · simpa using hχ
    · intro z hz
      have h1 : ‖z‖ < 2 * D.σ j + 2 * (δt / 2) := by
        simpa only [Metric.mem_ball, dist_zero_right] using hχts hz
      simpa only [Metric.mem_closedBall, dist_zero_right] using le_of_lt h1
    · exact mul_le_mul_of_nonneg_right hle (by linarith)

end Work.Diff.STE.Lead.GalTame
