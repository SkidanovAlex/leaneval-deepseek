import Mathlib
import Submission.Work.Whitney.DoublePoint
import Submission.Work.Whitney.LocalModel
import Submission.Work.Whitney.doubleDet_ne_zero_iff
import Submission.Work.Whitney.EuclidModel
import Submission.Work.Whitney.EuclidModelProps
import Submission.Work.Whitney.isClosed_setOf_norm_le
import Submission.Work.Whitney.norm_euclidModel_sub_axis_le
import Submission.Work.Whitney.euclidModel_eq_axis
import Submission.Work.Whitney.euclidModel_range_sup

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- **Gluing a cut-off local model into an immersion adds exactly one transverse double point.**
Given a smooth immersion `f : M → ℝ^{2n}`, a chart `c := chartAt x` at `x ∈ M` (with `hsrc`: every point whose `c`-coordinate is `< 3R` lies in `c.source`, so that the "small ball" region is honest — this is needed because `c` is an `OpenPartialHomeomorph` and its values outside the source are unconstrained), a tubular parametrisation `H` of the chart representation (`H` smooth, injective and immersive on `Metric.ball 0 ρ`, Lipschitz with constant `L` there, equal to `Work.Whitney.chartRepM f x` on the axis `v = 0`), a cut-off local model `β` (`Submission/Work/Whitney/LocalModel.lean`) with exactly one transverse double point at the pair `a ≠ b` of the ball of radius `R`, agreeing with `inclModel n` outside that ball, `δ`-close to it, whose second block is nonzero inside the ball, plus the "cleanness" hypotheses `hclean` (no preimage of a double point of `f` lies in the ball) and `hsep` (the image of the ball is `η`-separated from the image of everything whose `c`-coordinate is `≥ 2R`), the formula `f' y = H (β (c y))` on `{‖c y‖ < 2R} ∩ c.source` and `f' = f` otherwise defines a smooth immersion whose double point set is exactly that of `f` together with the single inserted ordered pair `(p', q')`, and the inserted double point is transverse: its signed determinant, evaluated at the *chart coordinates of its own preimages* (as in `Work.Whitney.doubleDet_ne_zero_iff`), is nonzero. -/
theorem exists_addDoublePoint {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
    (x : M) (U : Set M) (hUopen : IsOpen U) (hxU : x ∈ U)
    (hUsub : U ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (H : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin (2 * n)))
    (hHc : ContDiff ℝ ⊤ H)
    (hHaxis : ∀ u, H (u, 0) = Work.Whitney.chartRepM f x u)
    (ρ L : ℝ) (hρ : 0 < ρ) (hL : 0 < L)
    (hHinj : Set.InjOn H (Metric.ball 0 ρ))
    (hHimm : ∀ z ∈ Metric.ball 0 ρ, Function.Injective (fderiv ℝ H z))
    (hHLip : ∀ z ∈ Metric.ball 0 ρ, ∀ z' ∈ Metric.ball 0 ρ, ‖H z - H z'‖ ≤ L * ‖z - z'‖)
    (β : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ))
    (hβc : ContDiff ℝ ⊤ β) (hβimm : ∀ u, Function.Injective (fderiv ℝ β u))
    (a b : Fin n → ℝ) (hab : a ≠ b) (hβab : β a = β b)
    (hβuniq : ∀ u v, u ≠ v → β u = β v → (u = a ∧ v = b) ∨ (u = b ∧ v = a))
    (R δ η : ℝ) (hR : 0 < R) (hδ : 0 < δ) (hη : 0 < η)
    (hβact : ∀ u, ‖u‖ < R → (β u).2 ≠ 0)
    (hβR : ∀ u, R ≤ ‖u‖ → β u = Work.Whitney.inclModel n u)
    (hβδ : ∀ u, ‖β u - Work.Whitney.inclModel n u‖ ≤ δ)
    (hdet : LinearMap.det (((fderiv ℝ β a).coprod (fderiv ℝ β b)).toLinearMap) ≠ 0)
    (hRa : ‖a‖ < R) (hRb : ‖b‖ < R)
    (hρR : 2 * R + δ ≤ ρ) (hδLη : L * δ < η)
    (hballU : Metric.ball 0 (3 * R) ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) x) '' U)
    (hsrc : ∀ y : M, ‖(chartAt (EuclideanSpace ℝ (Fin n)) x) y‖ < 3 * R →
      y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hclean : ∀ y : M, ‖(chartAt (EuclideanSpace ℝ (Fin n)) x) y‖ < R →
      ∀ z : M, f y = f z → z = y)
    (hsep : ∀ y z : M, ‖(chartAt (EuclideanSpace ℝ (Fin n)) x) y‖ < R →
      2 * R ≤ ‖(chartAt (EuclideanSpace ℝ (Fin n)) x) z‖ → f y ≠ f z → η ≤ ‖f y - f z‖) :
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))) (p' q' : M),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f' ∧
      (∀ z, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f' z)) ∧
      (∀ y : M, R ≤ ‖(chartAt (EuclideanSpace ℝ (Fin n)) x) y‖ → f' y = f y) ∧
      Work.Whitney.doubleSet f' = Work.Whitney.doubleSet f ∪ {(p', q'), (q', p')} ∧
      Work.Whitney.doubleDet f' p' q'
        ((chartAt (EuclideanSpace ℝ (Fin n)) p') p')
        ((chartAt (EuclideanSpace ℝ (Fin n)) q') q') ≠ 0 := by
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
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x with hc
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
  have hΨAB : Ψ (scaledPt n lam b) = Ψ (scaledPt n lam a) := by
    rw [← hq'B, ← hp'A]
    exact hΨdbl.symm
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
      rw [hf'_lt y hlt, hΨeq, hHaxis]
      show f ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm (c y)) = f y
      rw [← hc, c.left_inv hyc]
    · exact hf'_ge y (le_of_not_gt hlt)
  have hev_chartRep : ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ < 2 * R → u ∈ c.target →
      Work.Whitney.chartRepM f' x =ᶠ[𝓝 u] (fun v => H (Ψ v)) := by
    intro u hu hut
    have hu' : u ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (2 * R) := by
      rw [Metric.mem_ball, dist_zero_right]; exact hu
    filter_upwards [c.open_target.mem_nhds hut, Metric.isOpen_ball.mem_nhds hu'] with v hvt hv2
    have hv2' : ‖v‖ < 2 * R := by rwa [Metric.mem_ball, dist_zero_right] at hv2
    have hcv : c (c.symm v) = v := c.right_inv hvt
    show f' ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm v) = H (Ψ v)
    rw [← hc, hf'_lt (c.symm v) (by rw [hcv]; exact hv2'), hcv]
  have hdiffH : Differentiable ℝ H := hHc.differentiable (by simp)
  have hdiffΨ : Differentiable ℝ (euclidModel n lam β) :=
    (contDiff_euclidModel hβc).differentiable (by simp)
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
      have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c y :=
        (contMDiffOn_chart (x := x)).contMDiffAt (c.open_source.mem_nhds hyc)
      have hHΨ : ContMDiffAt (𝓡 n) (𝓡 (2 * n)) ∞ (fun u => H (Ψ u)) (c y) :=
        (((hHc.comp (contDiff_euclidModel hβc)).contMDiff).of_le le_top).contMDiffAt
      exact ContMDiffAt.congr_of_eventuallyEq (hHΨ.comp y hcs) hev
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
            mfderiv (𝓡 n) (𝓡 n) c y := by
        have h := Work.Projection.mfderiv_chartAt_decomp f' hf'_sm x y hyc
        rwa [← hc] at h
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
      have hB : Function.Injective (mfderiv (𝓡 n) (𝓡 n) c y) := by
        intro a b hab
        exact ((mdifferentiable_chart (I := 𝓡 n) x).mfderiv hyc).injective hab
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
        rw [hHaxis]
        show f y = f ((chartAt (EuclideanSpace ℝ (Fin n)) x).symm (c y))
        rw [← hc, c.left_inv hyc]
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
  have hdet' : doubleDet f' p' q' ((chartAt (EuclideanSpace ℝ (Fin n)) p') p')
      ((chartAt (EuclideanSpace ℝ (Fin n)) q') q') ≠ 0 := by
    rw [Work.Whitney.doubleDet_ne_zero_iff f' hf'_sm p' q']
    have hAtgt : scaledPt n lam a ∈ c.target := by
      rw [← hp'A]; exact c.map_source hp'src
    have hBtgt : scaledPt n lam b ∈ c.target := by
      rw [← hq'B]; exact c.map_source hq'src
    have hA2 : ‖scaledPt n lam a‖ < 2 * R := by linarith
    have hB2 : ‖scaledPt n lam b‖ < 2 * R := by linarith
    have hrange : ∀ (u₀ : EuclideanSpace ℝ (Fin n)) (y : M), ‖u₀‖ < 2 * R → u₀ ∈ c.target →
        c y = u₀ →
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f' y).range
          = Submodule.map (fderiv ℝ H (Ψ u₀)).toLinearMap
              (fderiv ℝ (euclidModel n lam β) u₀).range := by
      intro u₀ y hu₀ hu₀t hcy
      have hyc : y ∈ c.source := hsrc y (by rw [hcy]; linarith)
      let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
        fderiv ℝ (Work.Whitney.chartRepM f' x) u₀
      let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        mfderiv (𝓡 n) (𝓡 n) c y
      have hdecB : mfderiv (𝓡 n) (𝓡 (2 * n)) f' y = A ∘L B := by
        have h := Work.Projection.mfderiv_chartAt_decomp f' hf'_sm x y hyc
        rw [← hc] at h
        rw [h, hcy]
        rfl
      have hBtop : B.range = ⊤ :=
        (mdifferentiable_chart (I := 𝓡 n) x).range_mfderiv_eq_top hyc
      rw [hdecB]
      change (A ∘L B).range = Submodule.map (fderiv ℝ H (Ψ u₀)).toLinearMap
          (fderiv ℝ (euclidModel n lam β) u₀).range
      rw [Work.Whitney.range_comp_clm, hBtop, Submodule.map_top]
      change (fderiv ℝ (Work.Whitney.chartRepM f' x) u₀).range
        = Submodule.map (fderiv ℝ H (Ψ u₀)).toLinearMap
            (fderiv ℝ (euclidModel n lam β) u₀).range
      rw [Filter.EventuallyEq.fderiv_eq (hev_chartRep u₀ hu₀ hu₀t)]
      have hfu : fderiv ℝ (fun v : EuclideanSpace ℝ (Fin n) => H (Ψ v)) u₀ =
          (fderiv ℝ H (Ψ u₀)).comp (fderiv ℝ (euclidModel n lam β) u₀) := by
        rw [show (fun u : EuclideanSpace ℝ (Fin n) => H (Ψ u)) = H ∘ euclidModel n lam β
          from rfl]
        exact fderiv_comp u₀ (hdiffH.differentiableAt) (hdiffΨ.differentiableAt)
      rw [hfu]
      change ((fderiv ℝ H (Ψ u₀)).comp (fderiv ℝ (euclidModel n lam β) u₀)).range
        = Submodule.map (fderiv ℝ H (Ψ u₀)).toLinearMap
            (fderiv ℝ (euclidModel n lam β) u₀).range
      rw [Work.Whitney.range_comp_clm]
    have hrange_p := hrange (scaledPt n lam a) p' hA2 hAtgt hp'A
    have hrange_q := hrange (scaledPt n lam b) q' hB2 hBtgt hq'B
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
    rw [hrange_p, hrange_q, hΨAB]
    change (Submodule.map (fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap
          (fderiv ℝ (euclidModel n lam β) (scaledPt n lam a)).range ⊔
        Submodule.map (fderiv ℝ H (Ψ (scaledPt n lam a))).toLinearMap
          (fderiv ℝ (euclidModel n lam β) (scaledPt n lam b)).range) = ⊤
    rw [← hmap, hmodel_sup, Submodule.map_top]
    exact hDH
  exact ⟨f', p', q', hf'_sm, hf'_imm, hf'_out, hds, hdet'⟩

end Work.Whitney
