import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Order.CompletePartialOrder

noncomputable section

open Filter MeasureTheory
open scoped Topology Interval ContDiff

namespace Commons.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

-- E-valued parametric derivative lemmas
lemma volterraFixedPoint_intervalIntegral_hasDerivAt_fixed_upper_of_continuous
    {F F' : ℝ → ℝ → E} {a b x₀ : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u) :
    HasDerivAt (fun x : ℝ => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  let s : Set ℝ := Metric.ball x₀ 1
  have hs : s ∈ 𝓝 x₀ := by
    exact Metric.ball_mem_nhds x₀ zero_lt_one
  have hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a b)) := by
    filter_upwards with x
    have hcont : Continuous (fun t : ℝ => F x t) := by
      exact hF_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (x, t)))
    exact hcont.aestronglyMeasurable
  have hF_int : IntervalIntegrable (F x₀) volume a b := by
    have hcont : Continuous (fun t : ℝ => F x₀ t) := by
      exact hF_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (x₀, t)))
    exact hcont.intervalIntegrable _ _
  have hF'_meas : AEStronglyMeasurable (F' x₀) (volume.restrict (Ι a b)) := by
    have hcont : Continuous (fun t : ℝ => F' x₀ t) := by
      exact hF'_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun t : ℝ => (x₀, t)))
    exact hcont.aestronglyMeasurable
  have hK : IsCompact ((Metric.closedBall x₀ 1) ×ˢ ([[a, b]] : Set ℝ)) :=
    (ProperSpace.isCompact_closedBall x₀ 1).prod isCompact_uIcc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn (fun p : ℝ × ℝ => ‖F' p.1 p.2‖) ((Metric.closedBall x₀ 1) ×ˢ ([[a, b]] : Set ℝ)) by
      exact (continuous_norm.comp hF'_cont).continuousOn)
  let bound : ℝ → ℝ := fun _ => M
  have h_bound : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t := by
    filter_upwards with t ht x hx
    have hx_closed : x ∈ Metric.closedBall x₀ 1 := Metric.ball_subset_closedBall hx
    have ht_closed : t ∈ ([[a, b]] : Set ℝ) := Set.uIoc_subset_uIcc ht
    have hpt : (x, t) ∈ (Metric.closedBall x₀ 1) ×ˢ ([[a, b]] : Set ℝ) := by
      exact ⟨hx_closed, ht_closed⟩
    simpa [bound] using hM (x, t) hpt
  have bound_int : IntervalIntegrable bound volume a b := by
    simpa [bound] using (intervalIntegrable_const (μ := volume) (c := M) : IntervalIntegrable (fun _ : ℝ => M) volume a b)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ x ∈ s, HasDerivAt (fun v : ℝ => F v t) (F' x t) x := by
    filter_upwards with t ht x hx
    exact hF'_isDeriv x t
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℝ) (μ := volume) (E := E) (F := F) (F' := F') (x₀ := x₀) (s := s)
    (a := a) (b := b) (bound := bound) hs hF_meas hF_int hF'_meas h_bound bound_int h_diff
  exact h.2

lemma volterraFixedPoint_intervalIntegral_hasFDerivAt_upper_continuous
    {F : ℝ → ℝ → E} {x₀ b₀ : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ t in b₀..p.2, F p.1 t)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b₀)) (x₀, b₀) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [Prod.fst_add, Prod.snd_add]
  have hnum : (fun h : ℝ × ℝ =>
      (∫ t in b₀..(b₀ + h.2), F (x₀ + h.1) t) - (∫ t in b₀..b₀, F x₀ t) -
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b₀)) h)
      = fun h : ℝ × ℝ => ∫ t in b₀..(b₀ + h.2), (F (x₀ + h.1) t - F x₀ b₀) := by
    ext h
    simp only [ContinuousLinearMap.coe_snd', ContinuousLinearMap.smulRight_apply]
    rw [intervalIntegral.integral_same]
    have hconst : h.2 • F x₀ b₀ = (b₀ + h.2 - b₀) • F x₀ b₀ := by ring_nf
    rw [hconst, ← intervalIntegral.integral_const]
    rw [sub_zero]
    rw [← intervalIntegral.integral_sub]
    · have hprod : Continuous (fun t : ℝ => (x₀ + h.1, t)) :=
        continuous_const.prodMk continuous_id
      exact (hF_cont.comp hprod).intervalIntegrable _ _
    · exact intervalIntegrable_const (μ := volume) (c := F x₀ b₀)
  rw [hnum]
  refine Asymptotics.IsLittleO.of_bound ?_
  intro ε hε
  have hcont : ContinuousAt (fun p : ℝ × ℝ => F p.1 p.2) (x₀, b₀) := hF_cont.continuousAt
  rcases Metric.continuousAt_iff.mp hcont ε hε with ⟨δ, hδpos, hδ⟩
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) hδpos] with h hh
  have hnorm : ‖h‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hmax : max |h.1| |h.2| < δ := by
    simpa [Prod.norm_def, Real.norm_eq_abs] using hnorm
  have h1 : |h.1| < δ := (max_lt_iff.mp hmax).1
  have h2 : |h.2| < δ := (max_lt_iff.mp hmax).2
  have hnorm_le : |h.2| ≤ ‖h‖ := by
    rw [Prod.norm_def, Real.norm_eq_abs]
    exact le_max_right _ _
  have h_bound : ∀ t ∈ Ι b₀ (b₀ + h.2), ‖F (x₀ + h.1) t - F x₀ b₀‖ ≤ ε := by
    intro t ht
    have ht_uIcc : t ∈ [[b₀, b₀ + h.2]] := (Set.uIoc_subset_uIcc) ht
    have ht_bound : |t - b₀| ≤ |h.2| := by
      rcases Set.mem_uIcc.mp ht_uIcc with hcase | hcase
      · have hle : b₀ ≤ t ∧ t ≤ b₀ + h.2 := hcase
        have hpos : 0 ≤ t - b₀ := sub_nonneg.mpr hle.1
        have hle2 : t - b₀ ≤ h.2 := by linarith
        rw [abs_of_nonneg hpos]
        exact hle2.trans (le_abs_self h.2)
      · have hle : b₀ + h.2 ≤ t ∧ t ≤ b₀ := hcase
        have hneg : t - b₀ ≤ 0 := by linarith
        rw [abs_of_nonpos hneg]
        have hneg2 : h.2 ≤ 0 := by linarith
        rw [abs_of_nonpos hneg2]
        linarith
    have hq : dist (x₀ + h.1, t) (x₀, b₀) < δ := by
      simp only [Prod.dist_eq, Real.dist_eq]
      ring_nf
      have : max |h.1| |t - b₀| ≤ max |h.1| |h.2| :=
        max_le (le_max_left _ _) (ht_bound.trans (le_max_right _ _))
      exact lt_of_le_of_lt this hmax
    have hFdist := hδ hq
    have hFle : dist (F (x₀ + h.1) t) (F x₀ b₀) ≤ ε := le_of_lt hFdist
    simpa [dist_eq_norm] using hFle
  calc
    ‖∫ t in b₀..(b₀ + h.2), (F (x₀ + h.1) t - F x₀ b₀)‖
        ≤ ε * |(b₀ + h.2) - b₀| := intervalIntegral.norm_integral_le_of_norm_le_const h_bound
    _ = ε * |h.2| := by ring_nf
    _ ≤ ε * ‖h‖ := by gcongr

lemma volterraFixedPoint_intervalIntegral_hasFDerivAt_upper_of_continuous'
    {F F' : ℝ → ℝ → E} {a b x₀ : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u) :
    HasFDerivAt (fun p : ℝ × ℝ => ∫ t in a..p.2, F p.1 t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (∫ t in a..b, F' x₀ t)
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b)) (x₀, b) := by
  have hA : HasDerivAt (fun x : ℝ => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ :=
    volterraFixedPoint_intervalIntegral_hasDerivAt_fixed_upper_of_continuous hF_cont hF'_cont hF'_isDeriv
  have hG1 : HasFDerivAt (fun p : ℝ × ℝ => ∫ t in a..b, F p.1 t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (∫ t in a..b, F' x₀ t)) (x₀, b) := by
    let I : E := ∫ t in a..b, F' x₀ t
    have hcomp := HasFDerivAt.comp (x := (x₀, b)) (f := Prod.fst)
      (g := fun x : ℝ => ∫ t in a..b, F x t)
      (f' := ContinuousLinearMap.fst ℝ ℝ ℝ)
      (g' := ContinuousLinearMap.toSpanSingleton ℝ I)
      hA.hasFDerivAt (hasFDerivAt_fst (p := (x₀, b)))
    have hder : (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I =
        (ContinuousLinearMap.toSpanSingleton ℝ I).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) := by
      refine ContinuousLinearMap.ext fun h => ?_
      simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [hder]
    change HasFDerivAt ((fun x : ℝ => ∫ t in a..b, F x t) ∘ Prod.fst)
      ((ContinuousLinearMap.toSpanSingleton ℝ I).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) (x₀, b)
    exact hcomp
  have hG2 : HasFDerivAt (fun p : ℝ × ℝ => ∫ t in b..p.2, F p.1 t)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F x₀ b)) (x₀, b) :=
    volterraFixedPoint_intervalIntegral_hasFDerivAt_upper_continuous (x₀ := x₀) (b₀ := b) hF_cont
  have hsum := hG1.add hG2
  have hint : ∀ x a b : ℝ, IntervalIntegrable (fun t : ℝ => F x t) volume a b := by
    intro x a b
    have hprod : Continuous (fun t : ℝ => (x, t)) := continuous_const.prodMk continuous_id
    exact (hF_cont.comp hprod).intervalIntegrable _ _
  have hfun : (fun p : ℝ × ℝ => (∫ t in a..b, F p.1 t) + ∫ t in b..p.2, F p.1 t)
      = fun p : ℝ × ℝ => ∫ t in a..p.2, F p.1 t := by
    ext p
    exact intervalIntegral.integral_add_adjacent_intervals (hint p.1 a b) (hint p.1 b p.2)
  refine hsum.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall (fun p => by exact (congrFun hfun p).symm)

lemma volterraFixedPoint_intervalIntegral_hasDerivAt_upper_piece_of_continuous
    {F F' : ℝ → ℝ → E} {c : ℝ} {y : ℝ → ℝ} {y' : ℝ} {s : ℝ}
    (hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2))
    (hF'_isDeriv : ∀ u t : ℝ, HasDerivAt (fun v : ℝ => F v t) (F' u t) u)
    (hy : HasDerivAt y y' s) (hy_cont : ContinuousAt y s) :
    HasDerivAt (fun u : ℝ => ∫ t in c..(y u), F u t)
      ((∫ t in c..(y s), F' s t) + y' • F s (y s)) s := by
  let b : ℝ := y s
  let I : E := ∫ t in c..b, F' s t
  have hG : HasFDerivAt (fun p : ℝ × ℝ => ∫ t in c..p.2, F p.1 t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F s b)) (s, b) := by
    simpa [b, I] using volterraFixedPoint_intervalIntegral_hasFDerivAt_upper_of_continuous' (a := c) (b := b) (x₀ := s) hF_cont hF'_cont hF'_isDeriv
  have hγ : HasDerivAt (fun u : ℝ => (u, y u)) (1, y') s := by
    simpa using (hasDerivAt_id s).prodMk hy
  have hcomp := HasFDerivAt.comp_hasDerivAt (x := s) hG hγ
  have hval : ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight I
        + (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F s b)) (1, y') = I + y' • F s b := by
    simp [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
  have hcompI := hcomp.congr_deriv hval
  have hfun : (fun u : ℝ => ∫ t in c..(y u), F u t) =
      (fun p : ℝ × ℝ => ∫ t in c..p.2, F p.1 t) ∘ (fun u : ℝ => (u, y u)) := by
    funext u
    rfl
  have hcomp_fun := hcompI.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun u => by exact congrFun hfun u))
  simpa [b, I] using hcomp_fun

-- Partial derivative of K w.r.t. the first variable
lemma volterraFixedPoint_hasDerivAt_partial_fst_triple
    {K : ℝ → ℝ → E → E}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ) :
    ∀ (u t : ℝ) (z : E),
      HasDerivAt (fun v : ℝ => K v t z)
        (fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (u, t, z)
          ((1 : ℝ), (0 : ℝ), (0 : E))) u := by
  intro u t z
  let G : ℝ × ℝ × E → E := fun p => K p.1 p.2.1 p.2.2
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := contDiffOn_univ.mp hK
  have hdiff : DifferentiableAt ℝ G (u, t, z) := by
    exact (hG.contDiffAt (n := (⊤ : ℕ∞)) (x := (u, t, z))).differentiableAt (by norm_num)
  have hGfderiv := hdiff.hasFDerivAt
  have hγ : HasDerivAt (fun v : ℝ => (v, t, z)) ((1 : ℝ), (0 : ℝ), (0 : E)) u := by
    exact (hasDerivAt_id u).prodMk ((hasDerivAt_const u t).prodMk (hasDerivAt_const u z))
  have hcomp := hGfderiv.comp_hasDerivAt u hγ
  have hfun : (fun v : ℝ => K v t z) = G ∘ (fun v : ℝ => (v, t, z)) := by
    funext v; rfl
  have hmain : HasDerivAt (fun v : ℝ => K v t z)
      (fderiv ℝ G (u, t, z) ((1 : ℝ), (0 : ℝ), (0 : E))) u := by
    rw [hfun]
    exact hcomp
  simpa [G] using hmain

lemma volterraFixedPoint_continuous_partial_fst_triple
    {K : ℝ → ℝ → E → E}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ) :
    Continuous (fun p : ℝ × ℝ × E =>
      fderiv ℝ (fun q : ℝ × ℝ × E => K q.1 q.2.1 q.2.2) p
        ((1 : ℝ), (0 : ℝ), (0 : E))) := by
  let G : ℝ × ℝ × E → E := fun p => K p.1 p.2.1 p.2.2
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := contDiffOn_univ.mp hK
  have hfd : Continuous (fun p : ℝ × ℝ × E => fderiv ℝ G p) := by
    exact hG.continuous_fderiv (by simp)
  have hvec : Continuous (fun _ : ℝ × ℝ × E => ((1 : ℝ), (0 : ℝ), (0 : E))) := continuous_const
  have h := hfd.clm_apply hvec
  simpa [G] using h

-- Clamp extension
def volterraFixedPoint_clampIcc (a b x : ℝ) : ℝ := max a (min b x)

lemma volterraFixedPoint_clampIcc_mem_Icc {a b : ℝ} (hab : a ≤ b) (x : ℝ) : volterraFixedPoint_clampIcc a b x ∈ Set.Icc a b := by
  unfold volterraFixedPoint_clampIcc
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma volterraFixedPoint_clampIcc_self {a b : ℝ} (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) : volterraFixedPoint_clampIcc a b x = x := by
  unfold volterraFixedPoint_clampIcc
  rw [min_eq_right hx.2, max_eq_right hx.1]

lemma volterraFixedPoint_continuous_volterraFixedPoint_clampIcc (a b : ℝ) : Continuous (fun x : ℝ => volterraFixedPoint_clampIcc a b x) := by
  unfold volterraFixedPoint_clampIcc
  fun_prop

-- Derivative formula for the Volterra integral, global extension version
lemma volterraFixedPoint_hasDerivAt_volterra_integral_ext
    {K : ℝ → ℝ → E → E} {w : ℝ → E} {a b s : ℝ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ)
    (hw : Continuous w) :
    HasDerivAt (fun u : ℝ => ∫ σ in u..b, K u σ (w σ))
      (- K s s (w s) + ∫ σ in s..b,
        fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (s, σ, w σ)
          ((1 : ℝ), (0 : ℝ), (0 : E))) s := by
  let DK : ℝ → ℝ → E → E := fun u σ z =>
    fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (u, σ, z) ((1 : ℝ), (0 : ℝ), (0 : E))
  let F : ℝ → ℝ → E := fun u σ => K u σ (w σ)
  let F' : ℝ → ℝ → E := fun u σ => DK u σ (w σ)
  have hF_cont : Continuous (fun p : ℝ × ℝ => F p.1 p.2) := by
    have hKc : Continuous (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) :=
      (contDiffOn_univ.mp hK).continuous
    have hγ : Continuous (fun p : ℝ × ℝ => (p.1, p.2, w p.2)) := by fun_prop
    have hcomp := hKc.comp hγ
    convert hcomp using 1
    funext p
    rfl
  have hF'_cont : Continuous (fun p : ℝ × ℝ => F' p.1 p.2) := by
    have hDc : Continuous (fun p : ℝ × ℝ × E => DK p.1 p.2.1 p.2.2) := by
      simpa [DK] using volterraFixedPoint_continuous_partial_fst_triple hK
    have hγ : Continuous (fun p : ℝ × ℝ => (p.1, p.2, w p.2)) := by fun_prop
    have hcomp := hDc.comp hγ
    convert hcomp using 1
    funext p
    rfl
  have hF'_isDeriv : ∀ u σ : ℝ, HasDerivAt (fun v : ℝ => F v σ) (F' u σ) u := by
    intro u σ
    simpa [F, F', DK] using volterraFixedPoint_hasDerivAt_partial_fst_triple hK u σ (w σ)
  have hfix : HasDerivAt (fun u : ℝ => ∫ σ in a..b, F u σ) (∫ σ in a..b, F' s σ) s :=
    volterraFixedPoint_intervalIntegral_hasDerivAt_fixed_upper_of_continuous hF_cont hF'_cont hF'_isDeriv
  have hupper : HasDerivAt (fun u : ℝ => ∫ σ in a..u, F u σ)
      ((∫ σ in a..s, F' s σ) + F s s) s := by
    simpa using volterraFixedPoint_intervalIntegral_hasDerivAt_upper_piece_of_continuous
      (F := F) (F' := F') (c := a) (y := fun u : ℝ => u) (y' := 1) (s := s)
      hF_cont hF'_cont hF'_isDeriv (hasDerivAt_id s) continuousAt_id
  have hdiff : HasDerivAt (fun u : ℝ => (∫ σ in a..b, F u σ) - ∫ σ in a..u, F u σ)
      ((∫ σ in a..b, F' s σ) - ((∫ σ in a..s, F' s σ) + F s s)) s :=
    hfix.sub hupper
  have hfun : (fun u : ℝ => (∫ σ in a..b, F u σ) - ∫ σ in a..u, F u σ)
      = fun u : ℝ => ∫ σ in u..b, F u σ := by
    funext u
    have hcont : Continuous (fun σ : ℝ => F u σ) := by
      exact hF_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun σ : ℝ => (u, σ)))
    have hInt1 : IntervalIntegrable (fun σ : ℝ => F u σ) volume a u := hcont.intervalIntegrable _ _
    have hInt2 : IntervalIntegrable (fun σ : ℝ => F u σ) volume u b := hcont.intervalIntegrable _ _
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := fun σ : ℝ => F u σ) (a := a) (b := u) (c := b) hInt1 hInt2
    rw [← hadj]
    abel
  have hfun' := hdiff.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun u => (congrFun hfun u).symm))
  have hval : (∫ σ in a..b, F' s σ) - ((∫ σ in a..s, F' s σ) + F s s)
      = - F s s + ∫ σ in s..b, F' s σ := by
    have hcontF' : Continuous (fun σ : ℝ => F' s σ) := by
      exact hF'_cont.comp ((continuous_const.prodMk continuous_id) : Continuous (fun σ : ℝ => (s, σ)))
    have hInt1 : IntervalIntegrable (fun σ : ℝ => F' s σ) volume a s := hcontF'.intervalIntegrable _ _
    have hInt2 : IntervalIntegrable (fun σ : ℝ => F' s σ) volume s b := hcontF'.intervalIntegrable _ _
    have hadj := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := fun σ : ℝ => F' s σ) (a := a) (b := s) (c := b) hInt1 hInt2
    rw [← hadj]
    abel
  have hder := hfun'.congr_deriv hval
  simpa [F, F', DK] using hder

lemma volterraFixedPoint_contDiffOn_partial_fst_triple
    {K : ℝ → ℝ → E → E}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × E =>
        fderiv ℝ (fun q : ℝ × ℝ × E => K q.1 q.2.1 q.2.2) p
          ((1 : ℝ), (0 : ℝ), (0 : E))) Set.univ := by
  let G : ℝ × ℝ × E → E := fun p => K p.1 p.2.1 p.2.2
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := contDiffOn_univ.mp hK
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => fderiv ℝ G p) := by
    exact hG.fderiv_right (by simp)
  have hvec : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℝ × ℝ × E => ((1 : ℝ), (0 : ℝ), (0 : E))) := by
    exact contDiff_const
  have hcomp := hfd.clm_apply hvec
  exact contDiffOn_univ.mpr (by simpa [G] using hcomp)

-- Within derivative formula on Icc, using the clamp extension
lemma volterraFixedPoint_hasDerivWithinAt_volterra_integral
    {K : ℝ → ℝ → E → E} {z : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ)
    (hz : ContinuousOn z (Set.Icc a b)) {s : ℝ} (hs : s ∈ Set.Icc a b) :
    HasDerivWithinAt (fun u : ℝ => ∫ σ in u..b, K u σ (z σ))
      (- K s s (z s) + ∫ σ in s..b,
        fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (s, σ, z σ)
          ((1 : ℝ), (0 : ℝ), (0 : E))) (Set.Icc a b) s := by
  let w : ℝ → E := fun x => z (volterraFixedPoint_clampIcc a b x)
  have hw_cont : Continuous w := by
    have hw_on : ContinuousOn w Set.univ := by
      unfold w
      exact hz.comp (volterraFixedPoint_continuous_volterraFixedPoint_clampIcc a b).continuousOn
        (fun x _ => volterraFixedPoint_clampIcc_mem_Icc hab x)
    exact continuousOn_univ.mp hw_on
  have hw_eq : ∀ x ∈ Set.Icc a b, w x = z x := by
    intro x hx
    unfold w
    rw [volterraFixedPoint_clampIcc_self hab hx]
  have hder_ext := volterraFixedPoint_hasDerivAt_volterra_integral_ext (K := K) (w := w) (a := a) (b := b) (s := s) hK hw_cont
  have hder_ext_within : HasDerivWithinAt (fun u : ℝ => ∫ σ in u..b, K u σ (w σ))
      (- K s s (w s) + ∫ σ in s..b,
        fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (s, σ, w σ)
          ((1 : ℝ), (0 : ℝ), (0 : E))) (Set.Icc a b) s := hder_ext.hasDerivWithinAt
  have hfun_eq : (fun u : ℝ => ∫ σ in u..b, K u σ (w σ)) =ᶠ[𝓝[Set.Icc a b] s]
      fun u : ℝ => ∫ σ in u..b, K u σ (z σ) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ_mem : σ ∈ Set.Icc a b := by
      have hu' : u ∈ Set.Icc a b := hu
      rcases hu' with ⟨hua, hub⟩
      rcases Set.mem_uIcc.mp hσ with hcase | hcase
      · exact ⟨hua.trans hcase.1, hcase.2⟩
      · exact ⟨hab.trans hcase.1, hcase.2.trans hub⟩
    simp [hw_eq σ hσ_mem]
  have hx_eq : (fun u : ℝ => ∫ σ in u..b, K u σ (z σ)) s = (fun u : ℝ => ∫ σ in u..b, K u σ (w σ)) s := by
    simp only
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ_mem : σ ∈ Set.Icc a b := by
      rcases hs with ⟨hsa, hsb⟩
      rcases Set.mem_uIcc.mp hσ with hcase | hcase
      · exact ⟨hsa.trans hcase.1, hcase.2⟩
      · exact ⟨hab.trans hcase.1, hcase.2.trans hsb⟩
    simp [hw_eq σ hσ_mem]
  have hder_congr := hder_ext_within.congr_of_eventuallyEq hfun_eq.symm hx_eq
  have hval_eq : (- K s s (w s) + ∫ σ in s..b,
        fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (s, σ, w σ)
          ((1 : ℝ), (0 : ℝ), (0 : E)))
      = - K s s (z s) + ∫ σ in s..b,
        fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (s, σ, z σ)
          ((1 : ℝ), (0 : ℝ), (0 : E)) := by
    have hs' : s ∈ Set.Icc a b := hs
    rw [hw_eq s hs']
    apply congrArg₂ (fun x y => - x + y) rfl
    apply intervalIntegral.integral_congr
    intro σ hσ
    have hσ_mem : σ ∈ Set.Icc a b := by
      rcases hs with ⟨hsa, hsb⟩
      rcases Set.mem_uIcc.mp hσ with hcase | hcase
      · exact ⟨hsa.trans hcase.1, hcase.2⟩
      · exact ⟨hab.trans hcase.1, hcase.2.trans hsb⟩
    simp [hw_eq σ hσ_mem]
  exact hder_congr.congr_deriv hval_eq

def volterraFixedPoint_partialFst (K : ℝ → ℝ → E → E) : ℝ → ℝ → E → E :=
  fun u σ z =>
    fderiv ℝ (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) (u, σ, z)
      ((1 : ℝ), (0 : ℝ), (0 : E))

lemma volterraFixedPoint_hasDerivWithinAt_volterra_integral_volterraFixedPoint_partialFst
    {K : ℝ → ℝ → E → E} {z : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ)
    (hz : ContinuousOn z (Set.Icc a b)) {s : ℝ} (hs : s ∈ Set.Icc a b) :
    HasDerivWithinAt (fun u : ℝ => ∫ σ in u..b, K u σ (z σ))
      (- K s s (z s) + ∫ σ in s..b, volterraFixedPoint_partialFst K s σ (z σ)) (Set.Icc a b) s := by
  simpa [volterraFixedPoint_partialFst] using volterraFixedPoint_hasDerivWithinAt_volterra_integral hab hK hz hs

lemma volterraFixedPoint_contDiffOn_boundary_volterra
    {K : ℝ → ℝ → E → E} {z : ℝ → E} {a b : ℝ} {n : ℕ}
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ)
    (hz : ContDiffOn ℝ n z (Set.Icc a b)) :
    ContDiffOn ℝ n (fun s : ℝ => K s s (z s)) (Set.Icc a b) := by
  let G : ℝ × ℝ × E → E := fun p => K p.1 p.2.1 p.2.2
  have hG : ContDiffOn ℝ n G Set.univ := by
    have hle_inner : (n : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact hK.of_le (WithTop.coe_le_coe.mpr hle_inner)
  have hcurve : ContDiffOn ℝ n (fun s : ℝ => (s, s, z s)) (Set.Icc a b) := by
    exact (contDiffOn_id.prodMk (contDiffOn_id.prodMk hz))
  have hcomp := hG.comp hcurve (by intro s hs; exact Set.mem_univ _)
  convert hcomp using 1
  funext s
  rfl

lemma volterraFixedPoint_contDiffOn_volterra_integral
    {K : ℝ → ℝ → E → E} {z : ℝ → E} {a b : ℝ} {n : ℕ}
    (hab : a ≤ b)
    (hK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => K p.1 p.2.1 p.2.2) Set.univ)
    (hz : ContDiffOn ℝ n z (Set.Icc a b)) :
    ContDiffOn ℝ (n + 1) (fun s : ℝ => ∫ σ in s..b, K s σ (z σ)) (Set.Icc a b) := by
  by_cases hlt : a < b
  · induction n generalizing K z with
    | zero =>
        let R : ℝ → E := fun s => ∫ σ in s..b, K s σ (z σ)
        let DK : ℝ → ℝ → E → E := volterraFixedPoint_partialFst K
        let D : ℝ → E := fun s => - K s s (z s) + ∫ σ in s..b, DK s σ (z σ)
        have hDK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => DK p.1 p.2.1 p.2.2) Set.univ := by
          simpa [DK, volterraFixedPoint_partialFst] using volterraFixedPoint_contDiffOn_partial_fst_triple hK
        have hderiv : ∀ s ∈ Set.Icc a b, HasDerivWithinAt R (D s) (Set.Icc a b) s := by
          intro s hs
          simpa [R, D, DK] using volterraFixedPoint_hasDerivWithinAt_volterra_integral_volterraFixedPoint_partialFst hab hK hz.continuousOn hs
        rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hlt)]
        constructor
        · intro s hs
          exact (hderiv s hs).differentiableWithinAt
        · constructor
          · intro h
            norm_num at h
          · have hderiv_eq : ∀ s ∈ Set.Icc a b, derivWithin R (Set.Icc a b) s = D s := by
              intro s hs
              exact (hderiv s hs).derivWithin ((uniqueDiffOn_Icc hlt).uniqueDiffWithinAt hs)
            have hD_cont : ContinuousOn D (Set.Icc a b) := by
              have hB : ContinuousOn (fun s : ℝ => K s s (z s)) (Set.Icc a b) := by
                have hB' : ContDiffOn ℝ 0 (fun s : ℝ => K s s (z s)) (Set.Icc a b) := by
                  simpa using volterraFixedPoint_contDiffOn_boundary_volterra (K := K) (z := z) (a := a) (b := b) (n := 0) hK (by simpa using hz)
                exact hB'.continuousOn
              have hJ : ContinuousOn (fun s : ℝ => ∫ σ in s..b, DK s σ (z σ)) (Set.Icc a b) := by
                have hderivJ : ∀ s ∈ Set.Icc a b,
                    HasDerivWithinAt (fun u : ℝ => ∫ σ in u..b, DK u σ (z σ))
                      (- DK s s (z s) + ∫ σ in s..b, volterraFixedPoint_partialFst DK s σ (z σ))
                      (Set.Icc a b) s := by
                  intro s hs
                  simpa [DK, volterraFixedPoint_partialFst] using volterraFixedPoint_hasDerivWithinAt_volterra_integral_volterraFixedPoint_partialFst hab hDK hz.continuousOn hs
                exact HasDerivWithinAt.continuousOn hderivJ
              exact hB.neg.add hJ
            exact (contDiffOn_zero.mpr hD_cont).congr (fun s hs => hderiv_eq s hs)
    | succ n ih =>
        let R : ℝ → E := fun s => ∫ σ in s..b, K s σ (z σ)
        let DK : ℝ → ℝ → E → E := volterraFixedPoint_partialFst K
        let D : ℝ → E := fun s => - K s s (z s) + ∫ σ in s..b, DK s σ (z σ)
        have hDK : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => DK p.1 p.2.1 p.2.2) Set.univ := by
          simpa [DK, volterraFixedPoint_partialFst] using volterraFixedPoint_contDiffOn_partial_fst_triple hK
        have hz_cont : ContinuousOn z (Set.Icc a b) := hz.continuousOn
        have hderiv : ∀ s ∈ Set.Icc a b, HasDerivWithinAt R (D s) (Set.Icc a b) s := by
          intro s hs
          simpa [R, D, DK] using volterraFixedPoint_hasDerivWithinAt_volterra_integral_volterraFixedPoint_partialFst hab hK hz_cont hs
        rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hlt)]
        constructor
        · intro s hs
          exact (hderiv s hs).differentiableWithinAt
        · constructor
          · intro h
            norm_num at h
          · have hderiv_eq : ∀ s ∈ Set.Icc a b, derivWithin R (Set.Icc a b) s = D s := by
              intro s hs
              exact (hderiv s hs).derivWithin ((uniqueDiffOn_Icc hlt).uniqueDiffWithinAt hs)
            have hD : ContDiffOn ℝ (n + 1) D (Set.Icc a b) := by
              have hB : ContDiffOn ℝ (n + 1) (fun s : ℝ => K s s (z s)) (Set.Icc a b) := by
                simpa using volterraFixedPoint_contDiffOn_boundary_volterra (K := K) (z := z) (a := a) (b := b) (n := n + 1) hK hz
              have hz_n : ContDiffOn ℝ n z (Set.Icc a b) := by
                exact hz.of_le (by exact_mod_cast Nat.le_succ n)
              have hJ : ContDiffOn ℝ (n + 1) (fun s : ℝ => ∫ σ in s..b, DK s σ (z σ)) (Set.Icc a b) := by
                simpa [DK] using ih (K := DK) (z := z) hDK hz_n
              exact hB.neg.add hJ
            exact hD.congr (fun s hs => hderiv_eq s hs)
  · -- degenerate interval a = b (using hlt : ¬ a < b and hab)
    have hab' : a = b := le_antisymm hab (not_lt.mp hlt)
    subst b
    rw [show Set.Icc a a = ({a} : Set ℝ) by simp]
    intro s hs
    have hs' : s = a := by simpa using hs
    subst s
    exact contDiffWithinAt_singleton







variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma volterraFixedPoint_fderiv_partial_eq_comp_inr
    {G : ℝ → E → E} {s : ℝ} {z : E}
    (hG : DifferentiableAt ℝ (fun p : ℝ × E => G p.1 p.2) (s, z)) :
    fderiv ℝ (fun z : E => G s z) z =
      (fderiv ℝ (fun p : ℝ × E => G p.1 p.2) (s, z)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  let ι : E → ℝ × E := fun y => (s, y)
  have hι_diff : DifferentiableAt ℝ ι z :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := E) s z).differentiableAt
  have hι_deriv : fderiv ℝ ι z = ContinuousLinearMap.inr ℝ ℝ E :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) (E := ℝ) (F := E) s z).fderiv
  have hcomp := fderiv_comp (𝕜 := ℝ) (f := ι) (x := z) (g := fun p : ℝ × E => G p.1 p.2) hG hι_diff
  have hfun : (fun y : E => G s y) = (fun p : ℝ × E => G p.1 p.2) ∘ ι := by
    funext y; rfl
  rw [hfun]
  simpa [ι, hι_deriv] using hcomp

lemma volterraFixedPoint_graph_fderiv_bijective
    {D : ℝ × E →L[ℝ] E} {e : E ≃L[ℝ] E}
    (hD_inr : D.comp (ContinuousLinearMap.inr ℝ ℝ E) = e.toContinuousLinearMap) :
    Function.Bijective ((ContinuousLinearMap.fst ℝ ℝ E).prod D) := by
  let L : ℝ × E →L[ℝ] ℝ × E := (ContinuousLinearMap.fst ℝ ℝ E).prod D
  constructor
  · intro p q hpq
    have h1 : p.1 = q.1 := by
      have := congrArg Prod.fst hpq
      simpa [L] using this
    have h2 : D p = D q := by
      have := congrArg Prod.snd hpq
      simpa [L] using this
    have hp_decomp : D p = D (p.1, 0) + D (0, p.2) := by
      have hsum : p = (p.1, 0) + (0, p.2) := by
        ext <;> simp
      have hD := congrArg D hsum
      rw [map_add] at hD
      simpa using hD
    have hq_decomp : D q = D (q.1, 0) + D (0, q.2) := by
      have hsum : q = (q.1, 0) + (0, q.2) := by
        ext <;> simp
      have hD := congrArg D hsum
      rw [map_add] at hD
      simpa using hD
    have hD0 : D (0, p.2) = D (0, q.2) := by
      have hDp0 : D (p.1, 0) = D (q.1, 0) := by rw [h1]
      have h := h2
      rw [hp_decomp, hq_decomp, hDp0] at h
      exact add_left_cancel h
    have hD0p : D (0, p.2) = e p.2 := by
      change (D.comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 = e p.2
      rw [hD_inr]
      rfl
    have hD0q : D (0, q.2) = e q.2 := by
      change (D.comp (ContinuousLinearMap.inr ℝ ℝ E)) q.2 = e q.2
      rw [hD_inr]
      rfl
    have heq : e p.2 = e q.2 := by rw [← hD0p, ← hD0q, hD0]
    have hpq2 : p.2 = q.2 := e.injective heq
    ext
    · exact h1
    · exact hpq2
  · intro q
    let u : ℝ := q.1
    let v : E := e.symm (q.2 - D (u, 0))
    refine ⟨(u, v), ?_⟩
    have hfirst : (L (u, v)).1 = q.1 := by simp [L, u]
    have hsecond : (L (u, v)).2 = q.2 := by
      change D (u, v) = q.2
      have hD_decomp : D (u, v) = D (u, 0) + D (0, v) := by
        have hsum : (u, v) = (u, 0) + (0, v) := by ext <;> simp
        have hD := congrArg D hsum
        rw [map_add] at hD
        simpa using hD
      have hD0 : D (0, v) = e v := by
        change (D.comp (ContinuousLinearMap.inr ℝ ℝ E)) v = e v
        rw [hD_inr]
        rfl
      have hev : e v = q.2 - D (u, 0) := by
        simp [v]
      rw [hD_decomp, hD0, hev]
      abel
    ext
    · exact hfirst
    · exact hsecond

lemma volterraFixedPoint_local_graph_smooth
    {G : ℝ → E → E} {Z Y : ℝ → E} {a b : ℝ} {n : ℕ} {s0 : ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => G p.1 p.2) Set.univ)
    (hY : ContDiffOn ℝ (n + 1) Y (Set.Icc a b))
    (hZ_cont : ContinuousOn Z (Set.Icc a b))
    (hEq : ∀ s ∈ Set.Icc a b, G s (Z s) = Y s)
    (hInv : ∃ e : E ≃L[ℝ] E, fderiv ℝ (fun z : E => G s0 z) (Z s0) = e.toContinuousLinearMap)
    (hs0 : s0 ∈ Set.Icc a b) :
    ∃ U : Set ℝ, IsOpen U ∧ s0 ∈ U ∧
      ContDiffOn ℝ (n + 1) Z (Set.Icc a b ∩ U) := by
  let Gfun : ℝ × E → E := fun p => G p.1 p.2
  let Φ : ℝ × E → ℝ × E := fun p => (p.1, Gfun p)
  let a0 : ℝ × E := (s0, Z s0)
  have hG_top : ContDiff ℝ (⊤ : ℕ∞) Gfun := contDiffOn_univ.mp hG
  have hleG : (n : WithTop ℕ∞) + 1 ≤ (⊤ : ℕ∞) := by
    have hle_inner : (n : ℕ∞) + 1 ≤ (⊤ : ℕ∞) :=
      ENat.natCast_add_one_le_iff.mpr (ENat.natCast_lt_top n)
    simpa [WithTop.coe_add, WithTop.coe_one] using (WithTop.coe_le_coe.mpr hle_inner)
  have hG_n : ContDiffAt ℝ (n + 1) Gfun a0 := by
    exact hG_top.contDiffAt.of_le hleG
  have hn : ((n : WithTop ℕ∞) + 1) ≠ 0 := by simp
  have hGfun_diff : DifferentiableAt ℝ Gfun a0 := hG_n.differentiableAt hn
  have hΦ_cdAt : ContDiffAt ℝ (n + 1) Φ a0 := by
    exact contDiffAt_fst.prodMk hG_n
  have hΦ_has : HasFDerivAt Φ ((ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ Gfun a0)) a0 := by
    have h1 : HasFDerivAt (fun p : ℝ × E => p.1) (ContinuousLinearMap.fst ℝ ℝ E) a0 := hasFDerivAt_fst
    have h2 : HasFDerivAt Gfun (fderiv ℝ Gfun a0) a0 := hGfun_diff.hasFDerivAt
    have hprod := h1.prodMk h2
    simpa [Φ, Gfun] using hprod
  rcases hInv with ⟨e, he⟩
  have hD_inr : (fderiv ℝ Gfun a0).comp (ContinuousLinearMap.inr ℝ ℝ E) = e.toContinuousLinearMap := by
    have hpart := volterraFixedPoint_fderiv_partial_eq_comp_inr (G := G) (s := s0) (z := Z s0) hGfun_diff
    rw [← hpart]
    exact he
  have hbij := volterraFixedPoint_graph_fderiv_bijective (D := fderiv ℝ Gfun a0) (e := e) hD_inr
  have hInjCLM : ((ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ Gfun a0)).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hbij.1
  have hSurjCLM : ((ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ Gfun a0)).range = ⊤ :=
    LinearMap.range_eq_top.mpr hbij.2
  let Φ' : (ℝ × E) ≃L[ℝ] (ℝ × E) := ContinuousLinearEquiv.ofBijective
    ((ContinuousLinearMap.fst ℝ ℝ E).prod (fderiv ℝ Gfun a0)) hInjCLM hSurjCLM
  have hΦ'_has : HasFDerivAt Φ (Φ' : (ℝ × E) →L[ℝ] (ℝ × E)) a0 := by
    simpa [Φ', ContinuousLinearEquiv.coe_ofBijective] using hΦ_has
  let Φe : OpenPartialHomeomorph (ℝ × E) (ℝ × E) := hΦ_cdAt.toOpenPartialHomeomorph Φ hΦ'_has hn
  have ha_source : a0 ∈ Φe.source := hΦ_cdAt.mem_toOpenPartialHomeomorph_source hΦ'_has hn
  have hΦa_target : Φ a0 ∈ Φe.target := Φe.map_source ha_source
  have hinv_cdAt : ContDiffAt ℝ (n + 1) Φe.symm (Φ a0) :=
    hΦ_cdAt.to_localInverse hΦ'_has hn
  obtain ⟨W₀, hW₀_mem, hW₀_cd⟩ := hinv_cdAt.contDiffOn (m := (n + 1 : ℕ∞)) le_rfl (by intro h; norm_num at h)
  obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp hW₀_mem
  have hW_cd_n : ContDiffOn ℝ (n + 1) Φe.symm W := hW₀_cd.mono hW_sub
  have hΦa_mem_W : Φ a0 ∈ W := hW_mem
  have hpreZ : {s : ℝ | (s, Z s) ∈ Φe.source} ∈ 𝓝[Set.Icc a b] s0 := by
    have hcont : ContinuousWithinAt (fun s : ℝ => (s, Z s)) (Set.Icc a b) s0 := by
      exact continuousWithinAt_id.prodMk (hZ_cont s0 hs0)
    have hsource_nhds : Φe.source ∈ 𝓝 a0 := Φe.open_source.mem_nhds ha_source
    exact hcont.preimage_mem_nhdsWithin hsource_nhds
  have hpreY : {s : ℝ | (s, Y s) ∈ W} ∈ 𝓝[Set.Icc a b] s0 := by
    have hcontY : ContinuousWithinAt (fun s : ℝ => (s, Y s)) (Set.Icc a b) s0 := by
      exact continuousWithinAt_id.prodMk (hY.continuousOn s0 hs0)
    have hW_nhds : W ∈ 𝓝 (Φ a0) := hW_open.mem_nhds hΦa_mem_W
    have hΦa_eq : Φ a0 = (s0, Y s0) := by
      have hEq0 := hEq s0 hs0
      simp [Φ, Gfun, a0, hEq0]
    have hW_nhds' : W ∈ 𝓝 (s0, Y s0) := by simpa [hΦa_eq] using hW_nhds
    exact hcontY.preimage_mem_nhdsWithin hW_nhds'
  have hpre : ({s : ℝ | (s, Z s) ∈ Φe.source} ∩ {s : ℝ | (s, Y s) ∈ W}) ∈ 𝓝[Set.Icc a b] s0 :=
    Filter.inter_mem (f := 𝓝[Set.Icc a b] s0) hpreZ hpreY
  obtain ⟨U, hU_open, hU_mem, hU_sub⟩ := mem_nhdsWithin.mp hpre
  refine ⟨U, hU_open, hU_mem, ?_⟩
  have hψ_cd : ContDiffOn ℝ (n + 1) (fun s : ℝ => (Φe.symm (s, Y s)).2) (Set.Icc a b ∩ U) := by
    have hcurve : ContDiffOn ℝ (n + 1) (fun s : ℝ => (s, Y s)) (Set.Icc a b ∩ U) := by
      have hY_mono : ContDiffOn ℝ (n + 1) Y (Set.Icc a b ∩ U) :=
        hY.mono (by intro s hs; exact hs.1)
      exact contDiffOn_id.prodMk hY_mono
    exact hW_cd_n.snd.comp hcurve (by
      intro s hs
      exact (hU_sub ⟨hs.2, hs.1⟩).2)
  refine hψ_cd.congr ?_
  intro s hs
  have hsrc : (s, Z s) ∈ Φe.source := (hU_sub ⟨hs.2, hs.1⟩).1
  have hΦeq : Φ (s, Z s) = (s, Y s) := by
    simp [Φ, Gfun, a0, hEq s hs.1]
  have hΦe_eq : Φe (s, Z s) = (s, Y s) := by
    simpa [Φe] using hΦeq
  have hleft := Φe.left_inv hsrc
  rw [hΦe_eq] at hleft
  exact (congrArg Prod.snd hleft).symm



lemma contDiffOn_of_continuous_volterra_fixedPoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → E → E} {Θ : ℝ → ℝ → E → E} {Ξ : ℝ → E} {Z : ℝ → E}
    (hZ_cont : ContinuousOn Z (Set.Icc a b))
    (hZ_eq : ∀ s ∈ Set.Icc a b,
      G s (Z s) = (∫ σ in s..b, Θ s σ (Z σ)) + Ξ s)
    (hG_cont : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × E => G p.1 p.2) Set.univ)
    (hΘ_cont : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × E => Θ p.1 p.2.1 p.2.2) Set.univ)
    (hΞ_cont : ContDiffOn ℝ (⊤ : ℕ∞) Ξ Set.univ)
    (hG_partial_inv : ∀ s ∈ Set.Icc a b,
      ∃ e : E ≃L[ℝ] E, fderiv ℝ (fun z : E => G s z) (Z s) = e.toContinuousLinearMap) :
    ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Icc a b) := by
  have hZ_all : ∀ n : ℕ, ContDiffOn ℝ n Z (Set.Icc a b) := by
    intro n
    induction n with
    | zero =>
        exact contDiffOn_zero.mpr hZ_cont
    | succ n ih =>
        let R : ℝ → E := fun s => ∫ σ in s..b, Θ s σ (Z σ)
        let Y : ℝ → E := fun s => R s + Ξ s
        have hR : ContDiffOn ℝ (n + 1) R (Set.Icc a b) := by
          simpa [R] using volterraFixedPoint_contDiffOn_volterra_integral (K := Θ) (z := Z) (a := a) (b := b)
            (n := n) hab hΘ_cont ih
        have hleΞ : (n : WithTop ℕ∞) + 1 ≤ (⊤ : ℕ∞) := by
          have hle_inner : (n : ℕ∞) + 1 ≤ (⊤ : ℕ∞) :=
            ENat.natCast_add_one_le_iff.mpr (ENat.natCast_lt_top n)
          simpa [WithTop.coe_add, WithTop.coe_one] using (WithTop.coe_le_coe.mpr hle_inner)
        have hΞ : ContDiffOn ℝ (n + 1) Ξ (Set.Icc a b) :=
          (hΞ_cont.of_le hleΞ).mono (by intro s hs; exact Set.mem_univ s)
        have hY : ContDiffOn ℝ (n + 1) Y (Set.Icc a b) := by
          simpa [Y] using hR.add hΞ
        have hEq : ∀ s ∈ Set.Icc a b, G s (Z s) = Y s := by
          intro s hs
          simp [Y, R, hZ_eq s hs]
        apply contDiffOn_of_locally_contDiffOn
        intro s hs
        rcases volterraFixedPoint_local_graph_smooth (G := G) (Z := Z) (Y := Y) (a := a) (b := b) (n := n)
          (s0 := s) hG_cont hY hZ_cont hEq (hG_partial_inv s hs) hs with
          ⟨U, hU_open, hsU, hZU⟩
        exact ⟨U, hU_open, hsU, hZU⟩
  exact contDiffOn_infty.mpr hZ_all

end Commons.Analysis.Calculus