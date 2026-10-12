import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# 1D calculus of variations on a half-line (Layer 3, scattering)

This module proves the two workhorses of the *exterior classification* of the
scattering solution profile (needed for `omega_outside_support`, that
`ω(x) = a v / ‖x‖` for `‖x‖ ≥ R`):

1. **DBR0** (`dbr0_ae_eq_zero`): the fundamental lemma of the calculus of
   variations on the half-line `(R, ∞)`: a locally integrable `g` whose
   integral against *every* smooth compactly-supported test function
   `φ` supported inside `(R, ∞)` vanishes is zero almost everywhere.

2. **Classification** (`affine_ae_of_snd_annihilates`): if `u` is locally
   integrable on `(R, ∞)` and `∫ u · χ'' = 0` for every smooth
   compactly-supported `χ` supported inside `(R, ∞)`, then `u` is affine
   (`u x = A + B·x`) almost everywhere on `(R, ∞)`.
-/

noncomputable section

open Filter Metric MeasureTheory Function Set
open scoped ContDiff Topology Real Interval

namespace Submission.BoseGases


/-- **DBR0** (fundamental lemma of the calculus of variations, half-line
version).  If `g` is locally integrable on `(R, ∞)` and its integral against
every smooth compactly-supported test function supported inside `(R, ∞)`
vanishes, then `g = 0` almost everywhere on `(R, ∞)`. -/
theorem dbr0_ae_eq_zero {R : ℝ} {g : ℝ → ℝ}
    (hg : MeasureTheory.LocallyIntegrableOn g (Set.Ioi R) volume)
    (hpair : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ r : ℝ, φ r ≠ 0 → R < r) →
      (∫ x : ℝ in Set.Ioi R, g x * φ x) = 0) :
    ∀ᵐ x : ℝ, R < x → g x = 0 := by
  have hmain := (isOpen_Ioi : IsOpen (Set.Ioi R)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := g) (μ := volume) hg
  refine hmain ?_
  intro φ hφdiff hφcomp hφts
  have hpoint : ∀ r : ℝ, φ r ≠ 0 → R < r := by
    intro r hr
    exact hφts (subset_tsupport φ hr)
  calc
    (∫ x : ℝ, φ x • g x) = (∫ x : ℝ, g x * φ x) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      simp [smul_eq_mul, mul_comm]
    _ = (∫ x : ℝ in Set.Ioi R, g x * φ x) := by
      exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi R)
        (f := fun x : ℝ => g x * φ x) (μ := volume) (by
          intro x hx
          have hφ0 : φ x = 0 := by
            by_contra h
            exact hx (hpoint x h)
          simp [hφ0])).symm
    _ = 0 := hpair φ hφdiff hφcomp hpoint




lemma full_integral_eq_Ioi {R : ℝ} {f : ℝ → ℝ} (hf : ∀ x, x ≤ R → f x = 0) :
    (∫ x : ℝ, f x) = (∫ x in Set.Ioi R, f x) := by
  exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioi R) (f := f) (μ := volume) (by intro x hx; exact hf x (le_of_not_gt hx))).symm

lemma integral_eq_Ioi_of_leR {R : ℝ} {f : ℝ → ℝ} (hf : ∀ x, x ≤ R → f x = 0) :
    (∫ x in Set.Ioi R, f x) = (∫ x : ℝ, f x) :=
  (full_integral_eq_Ioi hf).symm

lemma pointwise_support_of_tsupport {R : ℝ} {φ : ℝ → ℝ} (hφts : tsupport φ ⊆ Set.Ioi R) :
    ∀ r : ℝ, φ r ≠ 0 → R < r := by
  intro r hr
  exact hφts (subset_tsupport φ hr)

/-- product of a continuous multiplier and a continuous compactly supported function is
integrable. -/
lemma integrable_cont_mul {m θ : ℝ → ℝ} (hm : Continuous m) (hθc : Continuous θ)
    (hθcomp : HasCompactSupport θ) : MeasureTheory.Integrable (fun x : ℝ => m x * θ x) := by
  have hprod_cont : Continuous (fun x : ℝ => m x * θ x) := hm.mul hθc
  have hprod_comp : HasCompactSupport (fun x : ℝ => m x * θ x) := by
    refine HasCompactSupport.intro (f := fun x : ℝ => m x * θ x) (K := tsupport θ) hθcomp ?_
    intro x hx
    have hθ0 : θ x = 0 := by
      exact (Function.notMem_support.mp (fun hx2 => hx (subset_tsupport θ hx2)))
    simp [hθ0]
  exact hprod_cont.integrable_of_hasCompactSupport hprod_comp

lemma integrable_u_mul_smooth {R : ℝ} {u φ : ℝ → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn u (Set.Ioi R) volume)
    (hφcont : Continuous φ) (hφcomp : HasCompactSupport φ)
    (hφts : tsupport φ ⊆ Set.Ioi R) :
    MeasureTheory.Integrable (fun x : ℝ => u x * φ x) := by
  let K : Set ℝ := tsupport φ
  have hKcomp : IsCompact K := hφcomp
  have hKsub : K ⊆ Set.Ioi R := hφts
  have huK : MeasureTheory.IntegrableOn u K :=
    (hu.mono_set hKsub).integrableOn_isCompact hKcomp
  have huK' : MeasureTheory.Integrable u (volume.restrict K) := huK
  rcases (hKcomp.exists_bound_of_continuousOn (α := ℝ) (E := ℝ) (f := φ)
      (by exact hφcont.continuousOn)) with ⟨C₀, hC₀⟩
  let C : ℝ := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hφbdd : ∀ x, x ∈ K → |φ x| ≤ C := fun x hx => le_trans (hC₀ x hx) (le_max_left _ _)
  let f : ℝ → ℝ := fun x => u x * φ x
  have hsupp : Function.support f ⊆ K := by
    intro x hx
    have hφx : φ x ≠ 0 := by
      intro hφ0
      exact hx (by simp [f, hφ0])
    exact subset_tsupport φ hφx
  have hfK : MeasureTheory.Integrable f (volume.restrict K) := by
    have huMeas : AEStronglyMeasurable u (volume.restrict K) := huK'.aestronglyMeasurable
    have hφMeas : AEStronglyMeasurable φ (volume.restrict K) := hφcont.aestronglyMeasurable
    have hfmeas : AEStronglyMeasurable f (volume.restrict K) := by
      have hsmul : AEStronglyMeasurable (fun x : ℝ => φ x • u x) (volume.restrict K) :=
        hφMeas.smul huMeas
      have hcongr : (fun x : ℝ => φ x • u x) =ᵐ[volume.restrict K] f := by
        filter_upwards with x
        simp only [f]
        rw [smul_eq_mul, mul_comm]
      exact hsmul.congr hcongr
    have huKnorm : MeasureTheory.Integrable (fun x : ℝ => ‖u x‖) (volume.restrict K) := huK'.norm
    let g : ℝ → ℝ := fun x => C * ‖u x‖
    have hg_int : MeasureTheory.Integrable g (volume.restrict K) := by
      simpa [g] using huKnorm.const_mul C
    refine MeasureTheory.Integrable.mono' hg_int hfmeas ?_
    filter_upwards with x
    by_cases hxK : x ∈ K
    · have hφb := hφbdd x hxK
      have hmain : |u x * φ x| ≤ C * |u x| := by
        calc
          |u x * φ x| = |u x| * |φ x| := by rw [abs_mul]
          _ ≤ |u x| * C := mul_le_mul_of_nonneg_left hφb (abs_nonneg _)
          _ = C * |u x| := by ring
      simpa [f, g, Real.norm_eq_abs] using hmain
    · have hφ0 : φ x = 0 := by
        exact (Function.notMem_support.mp (fun hx2 => hxK (subset_tsupport φ hx2)))
      have hnn : 0 ≤ C * |u x| := mul_nonneg hC0 (abs_nonneg _)
      simpa [f, g, hφ0, Real.norm_eq_abs] using hnn
  exact (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsupp).mp hfK

/-- the second derivative operator is surjective onto test functions with vanishing mean and
first moment -/
lemma snd_surj {R : ℝ} {φ : ℝ → ℝ} (hφc : ContDiff ℝ ∞ φ) (hφsupp : ∀ r, φ r ≠ 0 → R < r)
    (hφcomp : HasCompactSupport φ) (hm0 : (∫ x : ℝ, φ x) = 0)
    (hm1 : (∫ x : ℝ, x * φ x) = 0) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ r, χ r ≠ 0 → R < r) ∧
      (∀ x : ℝ, deriv (deriv χ) x = φ x) := by
  have hφcont : Continuous φ := hφc.continuous
  have hφ_leR : ∀ t : ℝ, t ≤ R → φ t = 0 := fun t ht => by
    by_contra h
    exact (not_lt_of_ge ht) (hφsupp t h)
  rcases (Metric.isCompact_iff_isClosed_bounded.mp hφcomp).2.subset_closedBall (0 : ℝ) with ⟨r, hb⟩
  let M : ℝ := max R (r + 1)
  have hMnot : ∀ t, M ≤ t → t ∉ tsupport φ := by
    intro t ht tmem
    have hbt : |t| ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hb tmem
    have htbig : r + 1 ≤ t := by linarith [le_max_right R (r + 1), ht]
    have habs : t ≤ |t| := le_abs_self t
    linarith
  have hφ_geM : ∀ t, M ≤ t → φ t = 0 := by
    intro t ht
    exact (Function.notMem_support.mp (fun hmem : t ∈ Function.support φ =>
      hMnot t ht (subset_tsupport φ hmem)))
  let G : ℝ → ℝ := fun x => ∫ t in R..x, φ t
  let H : ℝ → ℝ := fun x => ∫ t in R..x, t * φ t
  let χ : ℝ → ℝ := fun x => x * G x - H x
  have hGderiv : deriv G = φ := by
    funext x
    exact hφcont.deriv_integral φ R x
  have hGdiff : Differentiable ℝ G := by
    intro x
    exact (hφcont.integral_hasStrictDerivAt R x).hasDerivAt.differentiableAt
  have hGc : ContDiff ℝ ∞ G := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hGdiff, by simpa [hGderiv] using hφc⟩
  have hφ_mul_id : ContDiff ℝ ∞ (fun t : ℝ => t * φ t) := by
    simpa [mul_comm] using (hφc.mul contDiff_id)
  have hφ_mul_id_cont : Continuous (fun t : ℝ => t * φ t) := hφ_mul_id.continuous
  have hHderiv : deriv H = fun t => t * φ t := by
    funext x
    exact hφ_mul_id_cont.deriv_integral (fun t : ℝ => t * φ t) R x
  have hHdiff : Differentiable ℝ H := by
    intro x
    exact (hφ_mul_id_cont.integral_hasStrictDerivAt R x).hasDerivAt.differentiableAt
  have hHc : ContDiff ℝ ∞ H := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨hHdiff, by simpa [hHderiv] using hφ_mul_id⟩
  let L : ℝ → ℝ := fun x => x * G x
  have hLc : ContDiff ℝ ∞ L := by
    simpa [L, mul_comm] using hGc.mul contDiff_id
  have hχc : ContDiff ℝ ∞ χ := by
    simpa [χ, L] using hLc.sub hHc
  have hG_diffAt (x : ℝ) : DifferentiableAt ℝ G x := hGdiff x
  have hid_diff (x : ℝ) : DifferentiableAt ℝ (fun y : ℝ => y) x :=
    (hasDerivAt_id x).differentiableAt
  have hL_diffAt (x : ℝ) : DifferentiableAt ℝ L x := (hLc.differentiable (by simp)) x
  have hH_diffAt (x : ℝ) : DifferentiableAt ℝ H x := (hHc.differentiable (by simp)) x
  have hderivL (x : ℝ) : deriv L x = G x + x * φ x := by
    calc
      deriv L x = deriv ((fun y : ℝ => y) * G) x := by rfl
      _ = deriv (fun y : ℝ => y) x * G x + (fun y : ℝ => y) x * deriv G x :=
        deriv_mul (hid_diff x) (hG_diffAt x)
      _ = G x + x * φ x := by simp [hGderiv]
  have hderivH (x : ℝ) : deriv H x = x * φ x := by
    exact hφ_mul_id_cont.deriv_integral (fun t : ℝ => t * φ t) R x
  have hderivχ (x : ℝ) : deriv χ x = G x := by
    calc
      deriv χ x = deriv (L - H) x := by rfl
      _ = deriv L x - deriv H x := deriv_sub (hL_diffAt x) (hH_diffAt x)
      _ = (G x + x * φ x) - x * φ x := by rw [hderivL x, hderivH x]
      _ = G x := by ring
  have hχderiv2 (x : ℝ) : deriv (deriv χ) x = φ x := by
    rw [show deriv χ = G from funext hderivχ, show deriv G = φ from hGderiv]
  have hG_leR : ∀ x, x ≤ R → G x = 0 := by
    intro x hx
    by_cases hxR : x = R
    · subst x; simp [G]
    · have hxlt : x < R := lt_of_le_of_ne hx hxR
      dsimp [G]
      rw [intervalIntegral.integral_symm]
      have hzero : (∫ t in x..R, φ t) = 0 := by
        rw [intervalIntegral.integral_of_le hx]
        calc (∫ t in Set.Ioc x R, φ t) = (∫ t in Set.Ioc x R, (0 : ℝ)) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
              intro t ht
              exact hφ_leR t ht.2
          _ = 0 := by simp
      rw [hzero]
      simp
  have hH_leR : ∀ x, x ≤ R → H x = 0 := by
    intro x hx
    by_cases hxR : x = R
    · subst x; simp [H]
    · have hxlt : x < R := lt_of_le_of_ne hx hxR
      dsimp [H]
      rw [intervalIntegral.integral_symm]
      have hzero : (∫ t in x..R, t * φ t) = 0 := by
        rw [intervalIntegral.integral_of_le hx]
        calc (∫ t in Set.Ioc x R, t * φ t) = (∫ t in Set.Ioc x R, (0 : ℝ)) := by
              apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
              intro t ht
              simp [hφ_leR t ht.2]
          _ = 0 := by simp
      rw [hzero]
      simp
  have hφ_support_sub : Function.support φ ⊆ Set.Ioc R M := by
    intro t ht
    constructor
    · exact hφsupp t ht
    · by_contra h
      have hMt : M < t := lt_of_not_ge h
      exact ht (hφ_geM t hMt.le)
  have hG_geM : ∀ x, M ≤ x → G x = 0 := by
    intro x hx
    dsimp [G]
    have hsub : Function.support φ ⊆ Set.Ioc R x := by
      intro t ht
      have ht' := hφ_support_sub ht
      exact ⟨ht'.1, le_trans ht'.2 hx⟩
    calc
      (∫ t in R..x, φ t) = (∫ t : ℝ, φ t) := intervalIntegral.integral_eq_integral_of_support_subset hsub
      _ = 0 := hm0
  have hH_geM : ∀ x, M ≤ x → H x = 0 := by
    intro x hx
    dsimp [H]
    have hsub : Function.support (fun t : ℝ => t * φ t) ⊆ Set.Ioc R x := by
      intro t ht
      have htφ : t ∈ Function.support φ := by
        by_contra hts
        have hφ0 : φ t = 0 := (Function.notMem_support.mp hts)
        exact ht (by simp [hφ0])
      have ht' := hφ_support_sub htφ
      exact ⟨ht'.1, le_trans ht'.2 hx⟩
    calc
      (∫ t in R..x, t * φ t) = (∫ t : ℝ, t * φ t) :=
        intervalIntegral.integral_eq_integral_of_support_subset hsub
      _ = 0 := hm1
  have hχ_leR : ∀ x, x ≤ R → χ x = 0 := by
    intro x hx
    dsimp [χ]
    simp [hG_leR x hx, hH_leR x hx]
  have hχ_geM : ∀ x, M ≤ x → χ x = 0 := by
    intro x hx
    dsimp [χ]
    simp [hG_geM x hx, hH_geM x hx]
  refine ⟨χ, hχc, ?_, ?_, hχderiv2⟩
  · refine HasCompactSupport.intro (f := χ) (K := Set.Icc R M) (isCompact_Icc (a := R) (b := M)) ?_
    intro x hx
    by_cases hxR : x ≤ R
    · exact hχ_leR x hxR
    · have hRM : R ≤ M := le_max_left R (r + 1)
      have hxM : M ≤ x := by
        have hxR' : R ≤ x := (lt_of_not_ge hxR).le
        have hnot : ¬ x ≤ M := by
          intro hxM'
          exact hx ⟨hxR', hxM'⟩
        exact (lt_of_not_ge hnot).le
      exact hχ_geM x hxM
  · intro r hr
    by_contra h
    exact hr (hχ_leR r (le_of_not_gt h))

lemma variance_pos {R r₀ : ℝ} {θ : ℝ → ℝ} (hθnn : ∀ x, 0 ≤ θ x)
    (hθcont : Continuous θ) (hθcomp : HasCompactSupport θ) (hθts : tsupport θ ⊆ Set.Ioi R)
    (hθint : (∫ x : ℝ, θ x) = 1) :
    0 < (∫ x : ℝ, (x - r₀) ^ 2 * θ x) := by
  have hθ_leR : ∀ x, x ≤ R → θ x = 0 := fun x hx => by
    by_contra h
    exact (not_lt_of_ge hx) (pointwise_support_of_tsupport hθts x h)
  let f : ℝ → ℝ := fun x => (x - r₀) ^ 2 * θ x
  have hfnn : ∀ x, 0 ≤ f x := by
    intro x
    exact mul_nonneg (sq_nonneg _) (hθnn x)
  have hfint : MeasureTheory.Integrable f := by
    have hm : Continuous (fun x : ℝ => (x - r₀) ^ 2) := by fun_prop
    simpa [f] using integrable_cont_mul hm hθcont hθcomp
  have hfeq : (∫ x : ℝ, f x) = (∫ x in Set.Ioi R, f x) :=
    full_integral_eq_Ioi (fun x hx => by simp [f, hθ_leR x hx])
  have hnonneg : 0 ≤ (∫ x : ℝ, f x) := by
    exact MeasureTheory.integral_nonneg (fun x => hfnn x)
  by_contra hnot
  have hle : (∫ x : ℝ, f x) ≤ 0 := by
    exact le_of_not_gt (by simpa [f, hfeq] using hnot)
  have hf0 : (∫ x : ℝ, f x) = 0 := le_antisymm hle hnonneg
  have hfae : f =ᵐ[volume] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hfnn) hfint).mp hf0
  have hθ0ae : θ =ᵐ[volume] 0 := by
    have hnull_f : volume {x : ℝ | f x ≠ 0} = 0 := by
      simpa [f, Function.support] using (MeasureTheory.ae_iff.mp hfae)
    have hsubset : {x : ℝ | θ x ≠ 0} ⊆ {x : ℝ | f x ≠ 0} ∪ {r₀} := by
      intro x hx
      by_cases hxr : x = r₀
      · exact Or.inr hxr
      · exact Or.inl (by
          have hsub2 : x - r₀ ≠ 0 := sub_ne_zero.mpr hxr
          have hsq : (x - r₀) ^ 2 ≠ 0 := pow_ne_zero 2 hsub2
          simpa [f] using (mul_ne_zero hsq hx))
    have hnull : volume ({x : ℝ | f x ≠ 0} ∪ {r₀}) = 0 := by
      exact MeasureTheory.measure_union_null hnull_f (measure_singleton r₀)
    apply MeasureTheory.ae_iff.mpr
    simpa using (MeasureTheory.measure_mono_null hsubset hnull)
  have hθint0 : (∫ x : ℝ, θ x) = 0 := MeasureTheory.integral_eq_zero_of_ae hθ0ae
  linarith

lemma exists_test_bump (R : ℝ) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ Set.Ioi R ∧
      (∀ x, 0 ≤ θ x) ∧ (∫ x : ℝ, θ x) = 1 := by
  let c : ℝ := R + 2
  let f : ContDiffBump c := ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩
  let θ : ℝ → ℝ := f.normed volume
  refine ⟨θ, ?_⟩
  constructor
  · exact f.contDiff_normed
  constructor
  · exact f.hasCompactSupport_normed (μ := volume)
  constructor
  · have hts : tsupport θ = Metric.closedBall c 1 := by
      simpa [θ, c] using f.tsupport_normed_eq (μ := volume)
    rw [hts]
    intro x hx
    change R < x
    have hdist : dist x c ≤ 1 := (Metric.mem_closedBall.mp hx)
    have habs : |x - c| ≤ 1 := by simpa [Real.dist_eq] using hdist
    have hge : c - 1 ≤ x := by
      have : x - c ≥ -1 := by linarith [abs_le.mp habs]
      linarith
    dsimp [c] at hge
    linarith
  constructor
  · intro x
    simpa [θ] using (f.nonneg_normed (μ := volume) x)
  · simpa [θ] using f.integral_normed (μ := volume)



lemma integral_lin3 (a b c : ℝ) {f g h : ℝ → ℝ}
    (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g)
    (hh : MeasureTheory.Integrable h) :
    (∫ x : ℝ, (a * f x - b * g x - c * h x)) =
      a * (∫ x : ℝ, f x) - b * (∫ x : ℝ, g x) - c * (∫ x : ℝ, h x) := by
  have hAf : MeasureTheory.Integrable (fun x : ℝ => a * f x) := hf.const_mul a
  have hBg : MeasureTheory.Integrable (fun x : ℝ => b * g x) := hg.const_mul b
  have hCh : MeasureTheory.Integrable (fun x : ℝ => c * h x) := hh.const_mul c
  calc
    (∫ x : ℝ, (a * f x - b * g x - c * h x)) =
        (∫ x : ℝ, (a * f x - b * g x)) - (∫ x : ℝ, c * h x) :=
      MeasureTheory.integral_sub (hAf.sub hBg) hCh
    _ = ((∫ x : ℝ, a * f x) - (∫ x : ℝ, b * g x)) - (∫ x : ℝ, c * h x) := by
      rw [MeasureTheory.integral_sub hAf hBg]
    _ = (a * (∫ x : ℝ, f x) - b * (∫ x : ℝ, g x)) - c * (∫ x : ℝ, h x) := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul]


lemma hasCompactSupport_const_mul {c : ℝ} {θ : ℝ → ℝ} (hθcomp : HasCompactSupport θ) :
    HasCompactSupport (fun x : ℝ => c * θ x) := by
  refine HasCompactSupport.intro (f := fun x : ℝ => c * θ x) (K := tsupport θ) hθcomp ?_
  intro x hx
  have hθ0 : θ x = 0 := by
    exact (Function.notMem_support.mp (fun hx2 => hx (subset_tsupport θ hx2)))
  simp [hθ0]

theorem affine_ae_of_snd_annihilates {R : ℝ} {u : ℝ → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn u (Set.Ioi R) volume)
    (hu0 : ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      (∀ r : ℝ, χ r ≠ 0 → R < r) →
      (∫ x : ℝ in Set.Ioi R, u x * deriv (deriv χ) x) = 0) :
    ∃ A B : ℝ, ∀ᵐ x : ℝ, R < x → u x = A + B * x := by
  obtain ⟨θ, hθc, hθcomp, hθts, hθnn, hθint⟩ := exists_test_bump R
  have hθcont : Continuous θ := hθc.continuous
  have hθsupp : ∀ r, θ r ≠ 0 → R < r := pointwise_support_of_tsupport hθts
  have hθ_leR : ∀ x, x ≤ R → θ x = 0 := fun x hx => by
    by_contra h
    exact (not_lt_of_ge hx) (hθsupp x h)
  let r₀ : ℝ := ∫ x : ℝ, x * θ x
  let D : ℝ := ∫ x : ℝ, (x - r₀)^2 * θ x
  have hDpos : 0 < D := by
    exact variance_pos (r₀ := r₀) hθnn hθcont hθcomp hθts hθint
  have hDne : D ≠ 0 := ne_of_gt hDpos
  let θ₁ : ℝ → ℝ := fun x => (x - r₀) * θ x
  have hθ₁cont : Continuous θ₁ := by
    dsimp [θ₁]
    exact ((continuous_id.sub continuous_const).mul hθcont)
  have hθ₁c : ContDiff ℝ ∞ θ₁ := by
    dsimp [θ₁]
    exact ((contDiff_id.sub (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => r₀)).mul hθc)
  have hθ₁comp : HasCompactSupport θ₁ := by
    refine HasCompactSupport.intro (f := θ₁) (K := tsupport θ) hθcomp ?_
    intro x hx
    have hθ0 : θ x = 0 := by
      exact (Function.notMem_support.mp (fun hx2 => hx (subset_tsupport θ hx2)))
    dsimp [θ₁]
    simp [hθ0]
  have hθ₁_ts0 : tsupport θ₁ ⊆ tsupport θ := by
    apply closure_mono
    intro x hx
    have hθx : θ x ≠ 0 := by
      intro hθ0
      exact hx (by
        dsimp [θ₁]
        simp [hθ0])
    exact hθx
  have hθ₁ts : tsupport θ₁ ⊆ Set.Ioi R := hθ₁_ts0.trans hθts
  have hθ₁supp : ∀ r, θ₁ r ≠ 0 → R < r := pointwise_support_of_tsupport hθ₁ts
  have hθ₁_leR : ∀ x, x ≤ R → θ₁ x = 0 := fun x hx => by
    by_contra h
    exact (not_lt_of_ge hx) (hθ₁supp x h)
  have huθI : MeasureTheory.Integrable (fun x : ℝ => u x * θ x) :=
    integrable_u_mul_smooth hu hθcont hθcomp hθts
  have huθ₁I : MeasureTheory.Integrable (fun x : ℝ => u x * θ₁ x) :=
    integrable_u_mul_smooth hu hθ₁cont hθ₁comp hθ₁ts
  let A₀ : ℝ := ∫ x : ℝ, u x * θ x
  let B₀ : ℝ := (∫ x : ℝ, u x * θ₁ x) / D
  let g : ℝ → ℝ := fun x => u x - A₀ - B₀ * (x - r₀)
  have hpolyLI : MeasureTheory.LocallyIntegrableOn (fun x : ℝ => A₀ + B₀ * (x - r₀))
      (Set.Ioi R) volume := by
    exact (by fun_prop : Continuous fun x : ℝ => A₀ + B₀ * (x - r₀)).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  have hgLI : MeasureTheory.LocallyIntegrableOn g (Set.Ioi R) volume := by
    have hsub : MeasureTheory.LocallyIntegrableOn
        (fun x : ℝ => u x - (A₀ + B₀ * (x - r₀))) (Set.Ioi R) volume := hu.sub hpolyLI
    refine MeasureTheory.LocallyIntegrableOn.congr ?_ hsub
    filter_upwards with x
    ring
  have hmean0 : (∫ x : ℝ, (x - r₀) * θ x) = 0 := by
    have hi1 : MeasureTheory.Integrable (fun x : ℝ => x * θ x) := by
      simpa using integrable_cont_mul (m := fun x : ℝ => x) continuous_id hθcont hθcomp
    have hi2 : MeasureTheory.Integrable (fun x : ℝ => r₀ * θ x) := by
      simpa using integrable_cont_mul (m := fun _ : ℝ => r₀) continuous_const hθcont hθcomp
    calc
      (∫ x : ℝ, (x - r₀) * θ x) = (∫ x : ℝ, x * θ x - r₀ * θ x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        ring
      _ = (∫ x : ℝ, x * θ x) - (∫ x : ℝ, r₀ * θ x) := MeasureTheory.integral_sub hi1 hi2
      _ = (∫ x : ℝ, x * θ x) - r₀ * (∫ x : ℝ, θ x) := by
        rw [integral_const_mul]
      _ = 0 := by
        dsimp [r₀]
        rw [hθint]
        ring
  have hrel : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Set.Ioi R → (∫ x : ℝ, g x * φ x) = 0 := by
    intro φ hφc hφcomp hφts
    have hφcont : Continuous φ := hφc.continuous
    have hφsupp : ∀ r, φ r ≠ 0 → R < r := pointwise_support_of_tsupport hφts
    have hφ_leR : ∀ x, x ≤ R → φ x = 0 := fun x hx => by
      by_contra h
      exact (not_lt_of_ge hx) (hφsupp x h)
    have huφI : MeasureTheory.Integrable (fun x : ℝ => u x * φ x) :=
      integrable_u_mul_smooth hu hφcont hφcomp hφts
    have hφI : MeasureTheory.Integrable φ := hφcont.integrable_of_hasCompactSupport hφcomp
    have hθI : MeasureTheory.Integrable θ := hθcont.integrable_of_hasCompactSupport hθcomp
    have hθ₁I : MeasureTheory.Integrable θ₁ := hθ₁cont.integrable_of_hasCompactSupport hθ₁comp
    have hxφI : MeasureTheory.Integrable (fun x : ℝ => (x - r₀) * φ x) := by
      simpa using integrable_cont_mul (m := fun x : ℝ => x - r₀)
        (continuous_id.sub continuous_const) hφcont hφcomp
    let Pφ : ℝ := ∫ x : ℝ, φ x
    let Lφ : ℝ := ∫ x : ℝ, (x - r₀) * φ x
    let c : ℝ := Lφ / D
    let ψ : ℝ → ℝ := fun x => φ x - Pφ * θ x - c * θ₁ x
    have hψ_leR : ∀ x, x ≤ R → ψ x = 0 := by
      intro x hx
      dsimp [ψ]
      simp [hφ_leR x hx, hθ_leR x hx, hθ₁_leR x hx]
    have hψsupp : ∀ r, ψ r ≠ 0 → R < r := by
      intro r hr
      by_contra h
      exact hr (hψ_leR r (le_of_not_gt h))
    have hψc : ContDiff ℝ ∞ ψ := by
      have h1 : ContDiff ℝ ∞ (fun x : ℝ => Pφ * θ x) := (contDiff_const.mul hθc)
      have h2 : ContDiff ℝ ∞ (fun x : ℝ => c * θ₁ x) := (contDiff_const.mul hθ₁c)
      dsimp [ψ]
      exact ((hφc.sub h1).sub h2)
    have hψcomp : HasCompactSupport ψ := by
      have h1c : HasCompactSupport (fun x : ℝ => Pφ * θ x) := hasCompactSupport_const_mul hθcomp
      have h2c : HasCompactSupport (fun x : ℝ => c * θ₁ x) := hasCompactSupport_const_mul hθ₁comp
      dsimp [ψ]
      exact ((hφcomp.sub h1c).sub h2c)
    have hPψ : (∫ x : ℝ, ψ x) = 0 := by
      have hlin := integral_lin3 (1 : ℝ) Pφ c hφI hθI hθ₁I
      have hrew : (∫ x : ℝ, (1 * φ x - Pφ * θ x - c * θ₁ x)) = (∫ x : ℝ, ψ x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [ψ]
      calc
        (∫ x : ℝ, ψ x) = (∫ x : ℝ, (1 * φ x - Pφ * θ x - c * θ₁ x)) := hrew.symm
        _ = 1 * (∫ x : ℝ, φ x) - Pφ * (∫ x : ℝ, θ x) - c * (∫ x : ℝ, θ₁ x) := hlin
        _ = Pφ - Pφ * (∫ x : ℝ, θ x) - c * (∫ x : ℝ, θ₁ x) := by ring
        _ = 0 := by
          have hθ₁full : (∫ x : ℝ, θ₁ x) = 0 := by
            dsimp [θ₁]
            exact hmean0
          dsimp [Pφ] at *
          rw [hθint, hθ₁full]
          ring
    have hLψ : (∫ x : ℝ, (x - r₀) * ψ x) = 0 := by
      have hA : MeasureTheory.Integrable (fun x : ℝ => (x - r₀) * φ x) := hxφI
      have hB : MeasureTheory.Integrable (fun x : ℝ => (x - r₀) * θ x) := by
        simpa using integrable_cont_mul (m := fun x : ℝ => x - r₀)
          (continuous_id.sub continuous_const) hθcont hθcomp
      have hC : MeasureTheory.Integrable (fun x : ℝ => (x - r₀) * θ₁ x) := by
        simpa using integrable_cont_mul (m := fun x : ℝ => x - r₀)
          (continuous_id.sub continuous_const) hθ₁cont hθ₁comp
      have hlin := integral_lin3 (1 : ℝ) Pφ c hA hB hC
      have hrew : (∫ x : ℝ, (1 * ((x - r₀) * φ x) - Pφ * ((x - r₀) * θ x)
          - c * ((x - r₀) * θ₁ x))) = (∫ x : ℝ, (x - r₀) * ψ x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [ψ]
        ring
      calc
        (∫ x : ℝ, (x - r₀) * ψ x) =
            (∫ x : ℝ, (1 * ((x - r₀) * φ x) - Pφ * ((x - r₀) * θ x)
              - c * ((x - r₀) * θ₁ x))) := hrew.symm
        _ = 1 * (∫ x : ℝ, (x - r₀) * φ x) - Pφ * (∫ x : ℝ, (x - r₀) * θ x)
            - c * (∫ x : ℝ, (x - r₀) * θ₁ x) := hlin
        _ = Lφ - Pφ * (∫ x : ℝ, (x - r₀) * θ x) - c * (∫ x : ℝ, (x - r₀) * θ₁ x) := by ring
        _ = Lφ - Pφ * 0 - c * D := by
          have hB0 : (∫ x : ℝ, (x - r₀) * θ x) = 0 := hmean0
          have hCval : (∫ x : ℝ, (x - r₀) * θ₁ x) = D := by
            dsimp [θ₁, D]
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring
          rw [hB0, hCval]
        _ = 0 := by
          dsimp [c]
          field_simp [hDne]
          ring
    have hMψ : (∫ x : ℝ, x * ψ x) = 0 := by
      have hxψI : MeasureTheory.Integrable (fun x : ℝ => x * ψ x) := by
        simpa using integrable_cont_mul (m := fun x : ℝ => x) continuous_id hψc.continuous hψcomp
      have hLψI : MeasureTheory.Integrable (fun x : ℝ => (x - r₀) * ψ x) := by
        simpa using integrable_cont_mul (m := fun x : ℝ => x - r₀)
          (continuous_id.sub continuous_const) hψc.continuous hψcomp
      have hψI : MeasureTheory.Integrable ψ := hψc.continuous.integrable_of_hasCompactSupport hψcomp
      calc
        (∫ x : ℝ, x * ψ x) = (∫ x : ℝ, ((x - r₀) * ψ x + r₀ * ψ x)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
        _ = (∫ x : ℝ, (x - r₀) * ψ x) + (∫ x : ℝ, r₀ * ψ x) := by
          rw [MeasureTheory.integral_add hLψI (hψI.const_mul r₀)]
        _ = 0 + r₀ * (∫ x : ℝ, ψ x) := by
          rw [hLψ, integral_const_mul]
        _ = 0 := by rw [hPψ]; ring
    rcases snd_surj hψc hψsupp hψcomp hPψ hMψ with ⟨χ, hχc, hχcomp, hχsupp, hχderiv⟩
    have huχ : (∫ x : ℝ in Set.Ioi R, u x * deriv (deriv χ) x) = 0 :=
      hu0 χ hχc hχcomp hχsupp
    have huψ_Ioi : (∫ x : ℝ in Set.Ioi R, u x * ψ x) = 0 := by
      rw [← huχ]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change u x * ψ x = u x * deriv (deriv χ) x
      rw [hχderiv x]
    have huψ_full : (∫ x : ℝ, u x * ψ x) = 0 := by
      rw [full_integral_eq_Ioi (fun x hx => by
        have : ψ x = 0 := hψ_leR x hx
        simp [this])]
      exact huψ_Ioi
    have hUexp : (∫ x : ℝ, u x * ψ x) =
        (∫ x : ℝ, u x * φ x) - Pφ * (∫ x : ℝ, u x * θ x)
          - c * (∫ x : ℝ, u x * θ₁ x) := by
      have hlinU := integral_lin3 (1 : ℝ) Pφ c huφI huθI huθ₁I
      have hrewU : (∫ x : ℝ, (1 * (u x * φ x) - Pφ * (u x * θ x)
          - c * (u x * θ₁ x))) = (∫ x : ℝ, u x * ψ x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [ψ]
        ring
      rw [← hrewU]
      rw [hlinU]
      ring
    have hrelφ : (∫ x : ℝ, u x * φ x) =
        Pφ * A₀ + c * (∫ x : ℝ, u x * θ₁ x) := by
      have hEq : (∫ x : ℝ, u x * φ x) - Pφ * A₀ - c * (∫ x : ℝ, u x * θ₁ x) = 0 := by
        dsimp [A₀]
        rw [← huψ_full, hUexp]
      linarith
    calc
      (∫ x : ℝ, g x * φ x) = (∫ x : ℝ, u x * φ x) - A₀ * (∫ x : ℝ, φ x)
          - B₀ * (∫ x : ℝ, (x - r₀) * φ x) := by
        have hlin := integral_lin3 (1 : ℝ) A₀ B₀ huφI hφI hxφI
        have hrew2 : (∫ x : ℝ, (1 * (u x * φ x) - A₀ * φ x - B₀ * ((x - r₀) * φ x))) =
            (∫ x : ℝ, g x * φ x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [g]
          ring
        rw [← hrew2]
        rw [hlin]
        ring
      _ = 0 := by
        have hU : (∫ x : ℝ, u x * φ x) = Pφ * A₀ + (Lφ / D) * (∫ x : ℝ, u x * θ₁ x) := by
          simpa [c] using hrelφ
        have hBv : B₀ * Lφ = (Lφ / D) * (∫ x : ℝ, u x * θ₁ x) := by
          dsimp [B₀, Lφ]
          field_simp [hDne]
          try ring
        rw [hU]
        dsimp [Pφ, Lφ]
        rw [← hBv]
        ring
  have hg0 : ∀ᵐ x : ℝ, R < x → g x = 0 := by
    have hmain := (isOpen_Ioi : IsOpen (Set.Ioi R)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (f := g) (μ := volume) hgLI
    refine hmain ?_
    intro φ hφc hφcomp hφts
    calc
      (∫ x : ℝ, φ x • g x) = (∫ x : ℝ, g x * φ x) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [smul_eq_mul, mul_comm]
      _ = 0 := hrel φ hφc hφcomp hφts
  refine ⟨A₀ - B₀ * r₀, B₀, ?_⟩
  filter_upwards [hg0] with x hx hR
  have hx0 : u x - A₀ - B₀ * (x - r₀) = 0 := by simpa [g] using (hx hR)
  have huval : u x = A₀ + B₀ * (x - r₀) := by linarith
  calc
    u x = A₀ + B₀ * (x - r₀) := huval
    _ = (A₀ - B₀ * r₀) + B₀ * x := by ring



end Submission.BoseGases
