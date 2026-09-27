import Mathlib
import Submission.Work.Whitney.exists_addDoublePoint_general_chart
import Submission.Work.Whitney.exists_addDoublePoint_smooth_located
import Submission.Work.Whitney.exists_clean_ball

/-!
# Adding one transverse double point in an arbitrary *chart-like* map

`Work.Whitney.exists_addDoublePoint_general_chart_located` glues a cut-off local model into a
smooth immersion, reading the chart coordinates through an `OpenPartialHomeomorph c` which agrees
with `chartAt x` on its source.  This file removes that agreement hypothesis: the only properties
of `c` that the argument uses are that `c` (on its source) and `c.symm` (on its target) are smooth.
The two consequences of chart-agreement that the earlier proof exploited -- the decomposition of
`mfderiv` through the chart, and the injectivity of `mfderiv c` -- are provided here directly from
the smoothness of `c` and `c.symm` (`mfderiv_decomp_of_smooth_chart`,
`mfderiv_injective_of_smooth_chart`).  Nothing else in the proof changes.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- **The chart decomposition of `mfderiv` for an arbitrary smooth chart-like map `c`.**  If `c`
is smooth at every point of its source and `c.symm` is smooth at every point of its target, then at
`y ∈ c.source` the derivative of a smooth map `f` factors through the derivative of `c`, the
remaining factor being the Fréchet derivative of the chart representation `u ↦ f (c.symm u)` of
`f` at `c y`.  (This is `Work.Projection.mfderiv_chartAt_decomp` without the assumption that `c`
comes from `chartAt`.) -/
theorem mfderiv_decomp_of_smooth_chart {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (F : M → EuclideanSpace ℝ (Fin N)) (hF : ContMDiff (𝓡 n) (𝓡 N) ∞ F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hcsm : ∀ y : M, y ∈ c.source → ContMDiffAt (𝓡 n) (𝓡 n) ∞ c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm u)
    (y : M) (hy : y ∈ c.source) :
    mfderiv (𝓡 n) (𝓡 N) F y =
      (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y)) ∘L
      mfderiv (𝓡 n) (𝓡 n) c y := by
  have hFmd : MDifferentiableAt (𝓡 n) (𝓡 N) F y := (hF y).mdifferentiableAt (by simp)
  have hcm : MDifferentiableAt (𝓡 n) (𝓡 n) c y :=
    (hcsm y hy).mdifferentiableAt (by simp)
  have hcm' : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c y) :=
    (hcinv (c y) (c.map_source hy)).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓡 n) (𝓡 N)
      (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) (c y) :=
    MDifferentiableAt.comp_of_eq (c y) hFmd hcm' (c.left_inv hy)
  have hcomp := mfderiv_comp (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 N)
    (f := (c : M → EuclideanSpace ℝ (Fin n)))
    (g := (fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u))) y hg hcm
  have heq : mfderiv (𝓡 n) (𝓡 N)
      ((fun u : EuclideanSpace ℝ (Fin n) => F (c.symm u)) ∘ c) y =
      mfderiv (𝓡 n) (𝓡 N) F y := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [c.open_source.mem_nhds hy] with z hz
    simp only [Function.comp_apply]
    rw [c.left_inv hz]
  rw [← heq, hcomp, mfderiv_eq_fderiv]
  rfl

/-- **`mfderiv c` is injective at every point of a smooth chart-like map's source.**  If `c` is
smooth on its source and `c.symm` is smooth on its target, then `c.symm ∘ c =ᶠ id` near each point
of the source and the chain rule identifies the composite of the derivatives with the identity;
injectivity follows. -/
theorem mfderiv_injective_of_smooth_chart {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hcsm : ∀ y : M, y ∈ c.source → ContMDiffAt (𝓡 n) (𝓡 n) ∞ c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm u)
    (y : M) (hy : y ∈ c.source) :
    Function.Injective (mfderiv (𝓡 n) (𝓡 n) c y) := by
  intro a b hab
  have hcm : MDifferentiableAt (𝓡 n) (𝓡 n) c y := (hcsm y hy).mdifferentiableAt (by simp)
  have hcm' : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c y) :=
    (hcinv (c y) (c.map_source hy)).mdifferentiableAt (by simp)
  have hev : (c.symm ∘ c) =ᶠ[𝓝 y] id := by
    filter_upwards [c.open_source.mem_nhds hy] with z hz
    exact c.left_inv hz
  have hcomp := mfderiv_comp (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 n)
    (f := (c : M → EuclideanSpace ℝ (Fin n)))
    (g := (c.symm : EuclideanSpace ℝ (Fin n) → M)) y hcm' hcm
  have hid : mfderiv (𝓡 n) (𝓡 n) (c.symm ∘ c) y =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 n) y) := by
    rw [Filter.EventuallyEq.mfderiv_eq hev, mfderiv_id]; ext v; rfl
  have hkey : ((mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) ∘L
      (mfderiv (𝓡 n) (𝓡 n) c y)) a = a := by
    rw [← hcomp, hid]; rfl
  have hkeyb : ((mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) ∘L
      (mfderiv (𝓡 n) (𝓡 n) c y)) b = b := by
    rw [← hcomp, hid]; rfl
  have h2 : ((mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) ∘L
        (mfderiv (𝓡 n) (𝓡 n) c y)) a
      = ((mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) ∘L
        (mfderiv (𝓡 n) (𝓡 n) c y)) b := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hab]
  rw [hkey] at h2
  rw [hkeyb] at h2
  exact h2

theorem exists_addDoublePoint_chart_like {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ c.target)
    (hcsm : ∀ y : M, y ∈ c.source →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hcinv : ∀ u : EuclideanSpace ℝ (Fin n), u ∈ c.target →
      ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm u)
    (U : Set M) (hUopen : IsOpen U) (h0U : c.symm 0 ∈ U) (hUsub : U ⊆ c.source)
    (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (2 * n)))
    (hHc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) H)
    (hHaxis : ∀ u, H (u, 0) = f (c.symm u))
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 0 < L)
    (hHinj : Set.InjOn H (Metric.ball 0 ρ))
    (hHimm : ∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z))
    (hHLip : ∀ z ∈ Metric.ball 0 ρ, ∀ z' ∈ Metric.ball 0 ρ, ‖H z - H z'‖ ≤ L * ‖z - z'‖)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hβc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβimm : ∀ u, Function.Injective (fderiv ℝ β u))
    (a b : Fin n → ℝ) (hab : a ≠ b) (hβab : β a = β b)
    (hβuniq : ∀ u v, u ≠ v → β u = β v → (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (R δ η : ℝ) (hR : 0 < R) (hδ : 0 < δ) (hη : 0 < η)
    (hβact : ∀ u, ‖u‖ < R → (β u).2 ≠ 0)
    (hβR : ∀ u, R ≤ ‖u‖ → β u = Work.Whitney.inclModel n u)
    (hβδ : ∀ u, ‖β u - Work.Whitney.inclModel n u‖ ≤ δ)
    (hdet : LinearMap.det (((fderiv ℝ β a).coprod (fderiv ℝ β b)).toLinearMap) ≠ 0)
    (hRa : ‖a‖ < R) (hRb : ‖b‖ < R)
    (hρR : 2 * R + δ ≤ ρ) (hδLη : L * δ < η)
    (hballU : Metric.ball 0 (3 * R) ⊆ c '' U)
    (hsrc : ∀ y : M, ‖c y‖ < 3 * R → y ∈ c.source)
    (hclean : ∀ y : M, ‖c y‖ < R → ∀ z : M, f y = f z → z = y)
    (hsep : ∀ y z : M, ‖c y‖ < R →
      2 * R ≤ ‖c z‖ → f y ≠ f z → η ≤ ‖f y - f z‖) :
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f' ∧
      (∀ z, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f' z)) ∧
      (∀ y : M, R ≤ ‖c y‖ → f' y = f y) ∧
      c p' = Work.Whitney.scaledPt n (Real.sqrt n) a ∧
      c q' = Work.Whitney.scaledPt n (Real.sqrt n) b ∧
      p' ∈ U ∧ q' ∈ U ∧
      f' = (fun y : M => if ‖c y‖ < 2 * R then
        H (Work.Whitney.euclidModel n (Real.sqrt n) β (c y)) else f y) ∧
      Work.Whitney.doubleSet f' = Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')} ∧
      Work.Whitney.doubleDetC f' c p' q' =
        Work.Whitney.doubleDetRep (fun v => H (Work.Whitney.euclidModel n (Real.sqrt n) β v))
          (Work.Whitney.scaledPt n (Real.sqrt n) a) (Work.Whitney.scaledPt n (Real.sqrt n) b) ∧
      Work.Whitney.doubleDetC f' c p' q' ≠ 0 := by

  classical
  -- `n = 0` is vacuous
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    exact absurd (Subsingleton.elim a b) hab
  set lam : ℝ := Real.sqrt n with hlamdef
  have hlam_pos : 0 < lam := by
    rw [hlamdef]; exact Real.sqrt_pos.mpr (by exact_mod_cast hnpos)
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam_pos
  have hsqrt_le : Real.sqrt n ≤ lam := le_of_eq hlamdef.symm
  have hRlt3 : R < 3 * R := by linarith
  have h2Rlt3 : 2 * R < 3 * R := by linarith
  have hRlt2R : R < 2 * R := by linarith
  have h2Rρ : 2 * R ≤ ρ := by linarith
  have hδnn : 0 ≤ δ := le_of_lt hδ
  -- the ball of radius `3R` in the chart lies in the target
  have htarget : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ⊆ c.target := by
    intro w hw
    obtain ⟨z, hzU, hzw⟩ := hballU hw
    rw [← hzw]
    exact c.map_source (hUsub hzU)
  have hA_lt : ‖scaledPt n lam a‖ < R := norm_scaledPt_lt hlam_pos hsqrt_le hRa
  have hB_lt : ‖scaledPt n lam b‖ < R := norm_scaledPt_lt hlam_pos hsqrt_le hRb
  obtain ⟨p', hp'U, hp'A⟩ : ∃ y : M, y ∈ U ∧ c y = scaledPt n lam a :=
    hballU (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  obtain ⟨q', hq'U, hq'B⟩ : ∃ y : M, y ∈ U ∧ c y = scaledPt n lam b :=
    hballU (by rw [Metric.mem_ball, dist_zero_right]; linarith)
  have hp'src : p' ∈ c.source := hUsub hp'U
  have hq'src : q' ∈ c.source := hUsub hq'U
  let Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    euclidModel n lam β
  have hΨdbl : Ψ (c p') = Ψ (c q') := by
    rw [hp'A, hq'B]
    exact (euclidModel_double_point (n := n) (lam := lam) (β := β) (a := a) (b := b)
      hlam_pos hab hβab).1
  have hp'ne : p' ≠ q' := by
    intro hpq
    have h := (euclidModel_double_point (n := n) (lam := lam) (β := β) (a := a) (b := b)
      hlam_pos hab hβab).2
    exact h (by rw [← hp'A, ← hq'B, hpq])
  let f' : M → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => if ‖c y‖ < 2 * R then H (Ψ (c y)) else f y
  have hmem_model : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < 2 * R → Ψ u ∈ Metric.ball 0 ρ := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ‖Ψ u - (u, 0)‖ ≤ δ := norm_euclidModel_sub_axis_le β hlam_pos hsqrt_le hβδ hδnn u
    have h2 : ‖(u, (0 : EuclideanSpace ℝ (Fin n)))‖ = ‖u‖ := by simp
    have h3 : ‖Ψ u‖ ≤ ‖Ψ u - (u, 0)‖ + ‖(u, (0 : EuclideanSpace ℝ (Fin n)))‖ := by
      calc ‖Ψ u‖ = ‖(Ψ u - (u, 0)) + (u, (0 : EuclideanSpace ℝ (Fin n)))‖ := by
            rw [sub_add_cancel]
        _ ≤ ‖Ψ u - (u, 0)‖ + ‖(u, (0 : EuclideanSpace ℝ (Fin n)))‖ := norm_add_le _ _
    linarith
  have hmem_axis : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < 2 * R →
      (u, (0 : EuclideanSpace ℝ (Fin n))) ∈
        Metric.ball (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ρ := by
    intro u hu
    rw [Metric.mem_ball, dist_zero_right]
    have h2 : ‖(u, (0 : EuclideanSpace ℝ (Fin n)))‖ = ‖u‖ := by simp
    linarith
  have hf'_lt : ∀ y : M, ‖c y‖ < 2 * R → f' y = H (Ψ (c y)) := by
    intro y hy
    change (if ‖c y‖ < 2 * R then H (Ψ (c y)) else f y) = H (Ψ (c y))
    rw [if_pos hy]
  have hf'_ge : ∀ y : M, 2 * R ≤ ‖c y‖ → f' y = f y := by
    intro y hy
    change (if ‖c y‖ < 2 * R then H (Ψ (c y)) else f y) = f y
    rw [if_neg (not_lt.mpr hy)]
  have hf'_out : ∀ y : M, R ≤ ‖c y‖ → f' y = f y := by
    intro y hy
    by_cases hlt : ‖c y‖ < 2 * R
    · have hyc : y ∈ c.source := hsrc y (lt_trans hlt h2Rlt3)
      have hΨeq : Ψ (c y) = (c y, 0) :=
        euclidModel_eq_axis β hlam_pos hsqrt_le hR hβR hy
      rw [hf'_lt y hlt, hΨeq, hHaxis (c y), c.left_inv hyc]
    · exact hf'_ge y (le_of_not_gt hlt)
  have hdiffH : Differentiable ℝ H := hHc.differentiable (by simp)
  have hdiffΨ : Differentiable ℝ (euclidModel n lam β) :=
    (contDiff_euclidModel_smooth hβc).differentiable (by simp)
  have hf'_sm : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f' := by
    intro y
    by_cases hlt : ‖c y‖ < 2 * R
    · have hyc : y ∈ c.source := hsrc y (lt_trans hlt h2Rlt3)
      have hcont : ContinuousAt (fun z : M => ‖c z‖) y :=
        continuous_norm.continuousAt.comp
          (c.continuousOn_toFun.continuousAt (c.open_source.mem_nhds hyc))
      have hev : f' =ᶠ[𝓝 y] (fun z => H (Ψ (c z))) := by
        filter_upwards [hcont.preimage_mem_nhds (isOpen_Iio.mem_nhds hlt)] with z hz
        exact hf'_lt z hz
      have hcsmooth : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c y := hcsm y hyc
      have hHΨ : ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ∞ (fun u => H (Ψ u)) (c y) :=
        ((hHc.comp (contDiff_euclidModel_smooth hβc)).contMDiff).contMDiffAt
      exact ContMDiffAt.congr_of_eventuallyEq (hHΨ.comp y hcsmooth) hev
    · have hle : 2 * R ≤ ‖c y‖ := le_of_not_gt hlt
      have hgt : R < ‖c y‖ := lt_of_lt_of_le hRlt2R hle
      have hclosed : IsClosed {z : M | ‖c z‖ ≤ R} :=
        isClosed_setOf_norm_le c (R := R) (r := R) (by linarith) hsrc htarget
      have hopen : IsOpen {z : M | R < ‖c z‖} := by
        have h := hclosed.isOpen_compl
        simpa only [Set.compl_setOf, not_le] using h
      have hev : f' =ᶠ[𝓝 y] f := by
        filter_upwards [hopen.mem_nhds hgt] with z hz
        exact hf'_out z (le_of_lt hz)
      exact ContMDiffAt.congr_of_eventuallyEq hf.contMDiffAt hev
  have hf'_imm : ∀ y : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f' y) := by
    intro y
    by_cases hlt : ‖c y‖ < 2 * R
    · have hyc : y ∈ c.source := hsrc y (lt_trans hlt h2Rlt3)
      have hdec : mfderiv (𝓡 n) (𝓡 (2 * n)) f' y =
          (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u)) (c y)) ∘L
            mfderiv (𝓡 n) (𝓡 n) c y :=
        mfderiv_decomp_of_smooth_chart f' hf'_sm c hcsm hcinv y hyc
      have hev : (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u))
          =ᶠ[𝓝 (c y)] (fun u => H (Ψ u)) := by
        have hyc' : c y ∈ c.target := c.map_source hyc
        have hball : c y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * R) := by
          rw [Metric.mem_ball, dist_zero_right]; exact hlt
        filter_upwards [c.open_target.mem_nhds hyc', Metric.isOpen_ball.mem_nhds hball]
          with u hut hu2
        have hu2' : ‖u‖ < 2 * R := by rwa [Metric.mem_ball, dist_zero_right] at hu2
        have hcu : c (c.symm u) = u := c.right_inv hut
        have : f' (c.symm u) = H (Ψ u) := by
          rw [hf'_lt (c.symm u) (by rw [hcu]; exact hu2'), hcu]
        exact this
      have hA : Function.Injective
          (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u)) (c y)) := by
        rw [Filter.EventuallyEq.fderiv_eq hev]
        have hchain : fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => H (Ψ u)) (c y) =
            (fderiv ℝ H (Ψ (c y))).comp (fderiv ℝ (euclidModel n lam β) (c y)) := by
          rw [show (fun u : EuclideanSpace ℝ (Fin n) => H (Ψ u)) = H ∘ euclidModel n lam β
            from rfl]
          exact fderiv_comp (c y) (hdiffH.differentiableAt) (hdiffΨ.differentiableAt)
        rw [hchain]
        intro a b hab
        have h1 : (fderiv ℝ (euclidModel n lam β) (c y)) a =
            (fderiv ℝ (euclidModel n lam β) (c y)) b :=
          (hHimm (Ψ (c y)) (hmem_model (c y) hlt)) (by simpa using hab)
        exact injective_fderiv_euclidModel hlam_ne hβimm (c y) h1
      have hB : Function.Injective (mfderiv (𝓡 n) (𝓡 n) c y) :=
        mfderiv_injective_of_smooth_chart c hcsm hcinv y hyc
      rw [hdec]
      intro a b hab
      change (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u)) (c y))
          ((mfderiv (𝓡 n) (𝓡 n) c y) a) =
        (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u)) (c y))
          ((mfderiv (𝓡 n) (𝓡 n) c y) b) at hab
      exact hB (hA hab)
    · have hle : 2 * R ≤ ‖c y‖ := le_of_not_gt hlt
      have hgt : R < ‖c y‖ := lt_of_lt_of_le hRlt2R hle
      have hclosed : IsClosed {z : M | ‖c z‖ ≤ R} :=
        isClosed_setOf_norm_le c (R := R) (r := R) (by linarith) hsrc htarget
      have hopen : IsOpen {z : M | R < ‖c z‖} := by
        have h := hclosed.isOpen_compl
        simpa only [Set.compl_setOf, not_le] using h
      have hev : f' =ᶠ[𝓝 y] f := by
        filter_upwards [hopen.mem_nhds hgt] with z hz
        exact hf'_out z (le_of_lt hz)
      rw [Filter.EventuallyEq.mfderiv_eq hev]
      exact himm y
  have hmixed : ∀ y z : M, ‖c y‖ < R → R ≤ ‖c z‖ → f' y = f' z → False := by
    intro y z hyR hzR hfy
    by_cases hz2R : ‖c z‖ < 2 * R
    · have hy2 : ‖c y‖ < 2 * R := by linarith
      have hfy' : f' y = H (Ψ (c y)) := hf'_lt y hy2
      have hfz' : f' z = H (c z, 0) := by
        rw [hf'_lt z hz2R,
          show Ψ (c z) = (c z, 0) from euclidModel_eq_axis β hlam_pos hsqrt_le hR hβR hzR]
      have h1 : H (Ψ (c y)) = H (c z, 0) := by rw [← hfy', ← hfz']; exact hfy
      exact euclidModel_ne_axis_of_lt hlam_pos hβact hβR hyR hzR
        (hHinj (hmem_model (c y) hy2) (hmem_axis (c z) hz2R) h1)
    · have hz2R' : 2 * R ≤ ‖c z‖ := le_of_not_gt hz2R
      have hfyfz : f y ≠ f z := by
        intro hh
        have hzy : z = y := hclean y hyR z hh
        rw [hzy] at hz2R'
        linarith
      have hsep' : η ≤ ‖f y - f z‖ := hsep y z hyR hz2R' hfyfz
      have hy2 : ‖c y‖ < 2 * R := by linarith
      have hyc : y ∈ c.source := hsrc y (by linarith)
      have hfy_eq : f y = H (c y, 0) := by
        rw [hHaxis (c y), c.left_inv hyc]
      have hdev : ‖f' y - f y‖ < η := by
        rw [hf'_lt y hy2, hfy_eq]
        calc ‖H (Ψ (c y)) - H (c y, 0)‖ ≤ L * ‖Ψ (c y) - (c y, 0)‖ :=
              hHLip _ (hmem_model (c y) hy2) _ (hmem_axis (c y) hy2)
          _ ≤ L * δ := mul_le_mul_of_nonneg_left
              (norm_euclidModel_sub_axis_le β hlam_pos hsqrt_le hβδ hδnn (c y)) (le_of_lt hL)
          _ < η := hδLη
      have hfz_eq : f' z = f z := hf'_ge z hz2R'
      have hle : ‖f y - f z‖ ≤ ‖f y - f' y‖ + ‖f' y - f z‖ := by
        rw [show f y - f z = (f y - f' y) + (f' y - f z) by abel]
        exact norm_add_le _ _
      have hz0 : ‖f' y - f z‖ = 0 := by rw [← hfz_eq, hfy, sub_self, norm_zero]
      have hrev : ‖f y - f' y‖ = ‖f' y - f y‖ := norm_sub_rev _ _
      linarith [hsep', hle, hz0, hrev, hdev]
  have hp'lt : ‖c p'‖ < 2 * R := by rw [hp'A]; linarith
  have hq'lt : ‖c q'‖ < 2 * R := by rw [hq'B]; linarith
  have hpq_mem : (p', q') ∈ doubleSet f' := by
    rw [Work.Whitney.mem_doubleSet]
    exact ⟨hp'ne, by rw [hf'_lt p' hp'lt, hf'_lt q' hq'lt]; exact congrArg H hΨdbl⟩
  have hqp_mem : (q', p') ∈ doubleSet f' := by
    rw [Work.Whitney.mem_doubleSet]
    exact ⟨fun h => hp'ne h.symm,
      by rw [hf'_lt q' hq'lt, hf'_lt p' hp'lt]; exact congrArg H hΨdbl.symm⟩
  have hds : doubleSet f' = doubleSet f ∪ {(p', q'), (q', p')} := by
    apply le_antisymm
    · rintro ⟨y, z⟩ h
      rw [Work.Whitney.mem_doubleSet] at h
      obtain ⟨hyz, hfy⟩ := h
      by_cases hyR : ‖c y‖ < R
      · by_cases hzR : ‖c z‖ < R
        · have hy2 : ‖c y‖ < 2 * R := by linarith
          have hz2 : ‖c z‖ < 2 * R := by linarith
          have h1 : H (Ψ (c y)) = H (Ψ (c z)) := by
            rw [← hf'_lt y hy2, ← hf'_lt z hz2]; exact hfy
          have hΨeq : Ψ (c y) = Ψ (c z) :=
            hHinj (hmem_model (c y) hy2) (hmem_model (c z) hz2) h1
          have hcyne : c y ≠ c z := by
            intro hcyz
            refine hyz ?_
            rw [← c.left_inv (hsrc y (by linarith)), ← c.left_inv (hsrc z (by linarith)), hcyz]
          rcases euclidModel_eq_iff (n := n) (lam := lam) (β := β) (a := a) (b := b)
            hlam_pos hβuniq (c y) (c z) hΨeq with heq | ⟨heq1, heq2⟩ | ⟨heq1, heq2⟩
          · exact absurd heq hcyne
          · have hyq : y = p' := by
              rw [← c.left_inv (hsrc y (by linarith)), heq1, ← hp'A]
              exact c.left_inv hp'src
            have hzq : z = q' := by
              rw [← c.left_inv (hsrc z (by linarith)), heq2, ← hq'B]
              exact c.left_inv hq'src
            refine Set.mem_union_right _ ?_
            rw [hyq, hzq]
            exact Set.mem_insert_iff.mpr (Or.inl rfl)
          · have hyq : y = q' := by
              rw [← c.left_inv (hsrc y (by linarith)), heq1, ← hq'B]
              exact c.left_inv hq'src
            have hzq : z = p' := by
              rw [← c.left_inv (hsrc z (by linarith)), heq2, ← hp'A]
              exact c.left_inv hp'src
            refine Set.mem_union_right _ ?_
            rw [hyq, hzq]
            exact Set.mem_insert_iff.mpr (Or.inr rfl)
        · exact (hmixed y z hyR (le_of_not_gt hzR) hfy).elim
      · by_cases hzR : ‖c z‖ < R
        · exact (hmixed z y hzR (le_of_not_gt hyR) hfy.symm).elim
        · refine Set.mem_union_left _ ?_
          rw [Work.Whitney.mem_doubleSet]
          refine ⟨hyz, ?_⟩
          change f y = f z
          rw [← hf'_out y (le_of_not_gt hyR), ← hf'_out z (le_of_not_gt hzR)]
          exact hfy
    · rintro ⟨y, z⟩ h
      rw [Set.mem_union] at h
      rcases h with h | h
      · rw [Work.Whitney.mem_doubleSet] at h
        obtain ⟨hyz, hfy⟩ := h
        have hyz' : y ≠ z := hyz
        have hfy' : f y = f z := hfy
        rw [Work.Whitney.mem_doubleSet]
        change y ≠ z ∧ f' y = f' z
        refine ⟨hyz', ?_⟩
        have hyR : R ≤ ‖c y‖ := by
          by_contra hcon
          exact hyz' (hclean y (lt_of_not_ge hcon) z hfy').symm
        have hzR : R ≤ ‖c z‖ := by
          by_contra hcon
          exact hyz' (hclean z (lt_of_not_ge hcon) y hfy'.symm)
        rw [hf'_out y hyR, hf'_out z hzR]
        exact hfy'
      · rw [Set.mem_insert_iff] at h
        rcases h with h | h
        · rw [h]; exact hpq_mem
        · rw [Set.mem_singleton_iff] at h
          rw [h]; exact hqp_mem
  have hAtgt : scaledPt n lam a ∈ c.target := by
    rw [← hp'A]; exact c.map_source hp'src
  have hBtgt : scaledPt n lam b ∈ c.target := by
    rw [← hq'B]; exact c.map_source hq'src
  have hA2 : ‖scaledPt n lam a‖ < 2 * R := by linarith
  have hB2 : ‖scaledPt n lam b‖ < 2 * R := by linarith
  have hevA : (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u))
      =ᶠ[𝓝 (scaledPt n lam a)] (fun u => H (Ψ u)) := by
    filter_upwards [c.open_target.mem_nhds hAtgt,
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hA2)]
      with u hut hu2
    have hu2' : ‖u‖ < 2 * R := by rwa [Metric.mem_ball, dist_zero_right] at hu2
    have hcu : c (c.symm u) = u := c.right_inv hut
    show f' (c.symm u) = H (Ψ u)
    rw [hf'_lt (c.symm u) (by rw [hcu]; exact hu2'), hcu]
  have hevB : (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u))
      =ᶠ[𝓝 (scaledPt n lam b)] (fun u => H (Ψ u)) := by
    filter_upwards [c.open_target.mem_nhds hBtgt,
      Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; exact hB2)]
      with u hut hu2
    have hu2' : ‖u‖ < 2 * R := by rwa [Metric.mem_ball, dist_zero_right] at hu2
    have hcu : c (c.symm u) = u := c.right_inv hut
    show f' (c.symm u) = H (Ψ u)
    rw [hf'_lt (c.symm u) (by rw [hcu]; exact hu2'), hcu]
  have hdetCEq : Work.Whitney.doubleDetC f' c p' q' =
      Work.Whitney.doubleDetRep (fun v => H (Work.Whitney.euclidModel n (Real.sqrt n) β v))
        (Work.Whitney.scaledPt n (Real.sqrt n) a)
        (Work.Whitney.scaledPt n (Real.sqrt n) b) := by
    rw [Work.Whitney.doubleDetC_def, hp'A, hq'B]
    show Work.Whitney.doubleDetRep (fun u => f' (c.symm u)) (scaledPt n lam a)
          (scaledPt n lam b)
        = Work.Whitney.doubleDetRep (fun v => H (Ψ v)) (scaledPt n lam a)
          (scaledPt n lam b)
    unfold Work.Whitney.doubleDetRep
    rw [Filter.EventuallyEq.fderiv_eq hevA, Filter.EventuallyEq.fderiv_eq hevB]
  have hdetC : Work.Whitney.doubleDetC f' c p' q' ≠ 0 := by
    rw [Work.Whitney.doubleDetC_def]
    rw [Work.Whitney.doubleDetRep_ne_zero_iff]
    have hrange_a : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u))
          (scaledPt n lam a)).range
        = Submodule.map (fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap
            (fderiv ℝ (euclidModel n lam β) (scaledPt n lam a)).range := by
      rw [Filter.EventuallyEq.fderiv_eq hevA]
      rw [show (fun u : EuclideanSpace ℝ (Fin n) => H (Ψ u)) = H ∘ euclidModel n lam β
        from rfl]
      rw [fderiv_comp (scaledPt n lam a) hdiffH.differentiableAt hdiffΨ.differentiableAt]
      rw [Work.Whitney.range_comp_clm]
    have hrange_b : (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => f' (c.symm u))
          (scaledPt n lam b)).range
        = Submodule.map (fderiv ℝ H (Ψ (scaledPt n lam b))).toLinearMap
            (fderiv ℝ (euclidModel n lam β) (scaledPt n lam b)).range := by
      rw [Filter.EventuallyEq.fderiv_eq hevB]
      rw [show (fun u : EuclideanSpace ℝ (Fin n) => H (Ψ u)) = H ∘ euclidModel n lam β
        from rfl]
      rw [fderiv_comp (scaledPt n lam b) hdiffH.differentiableAt hdiffΨ.differentiableAt]
      rw [Work.Whitney.range_comp_clm]
    have hsurj : Function.Surjective (fderiv ℝ H (Ψ (scaledPt n lam a))) := by
      have hinj : Function.Injective
          ((fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap) :=
        hHimm (Ψ (scaledPt n lam a)) (hmem_model (scaledPt n lam a) hA2)
      have hfin : Module.finrank ℝ
            (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =
          Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * n))) := by
        rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
        omega
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
    have hDH : ((fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap).range = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hmodel_sup : (fderiv ℝ (euclidModel n lam β) (scaledPt n lam a)).range ⊔
        (fderiv ℝ (euclidModel n lam β) (scaledPt n lam b)).range = ⊤ :=
      euclidModel_range_sup (n := n) (lam := lam) β a b hlam_pos hβab hdet
    have hmap := Submodule.map_sup
      (fderiv ℝ (euclidModel n lam β) (scaledPt n lam a)).range
      (fderiv ℝ (euclidModel n lam β) (scaledPt n lam b)).range
      (fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap
    have hΨAB : Ψ (scaledPt n lam b) = Ψ (scaledPt n lam a) := by
      rw [← hq'B, ← hp'A]; exact hΨdbl.symm
    rw [hp'A, hq'B, hrange_a, hrange_b, hΨAB]
    change (Submodule.map (fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap
          (fderiv ℝ (euclidModel n lam β) (scaledPt n lam a)).range ⊔
        Submodule.map (fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap
          (fderiv ℝ (euclidModel n lam β) (scaledPt n lam b)).range) = ⊤
    rw [← hmap, hmodel_sup, Submodule.map_top]
    exact hDH
  exact ⟨f', p', q', hf'_sm, hf'_imm, hf'_out, hp'A, hq'B, hp'U, hq'U, rfl,
    hds, hdetCEq, hdetC⟩

end Work.Whitney
