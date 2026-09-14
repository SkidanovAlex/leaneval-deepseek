import Submission.NBody.LYZLimit
import Submission.NBody.LYZSetup
import Submission.NBody.LYZCone
import Submission.NBody.Assembly
import Submission.Commons.Analysis.Asymptotics.summable_sqrt_log_div_pow
import Submission.Commons.Analysis.InnerProductSpace.half_mul_norm_mul_norm_le_inner_add_smul
import Submission.Commons.Analysis.Asymptotics.tendsto_tsum_nat_add_zero
import Mathlib

/-!
# The assembly of Theorem 1.1 from the Liu--Yan--Zhou construction

This module:
* builds, for every `n`, the `h`-minimiser `γ_n` from the given `x₀` to `x* + 2^n • a` (Tonelli's
  theorem, `exists_minimizer`); collisions of the *initial* configuration are allowed, so all the
  analytic inputs are used in their `(0,T]` form (`LYZIoc`);
* discharges every hypothesis of `exists_lyz_ratio` (the `unif` hypotheses, the numerical data
  `A, B, M, Ψ, Ψb`, the cone data `ν, θ, s₀, x*` from `LYZCone`/`LYZSetup`);
* applies `lyz_holder_bound`, extracts the diagonal subsequence with
  `Commons.Topology.Metric.exists_strictMono_tendstoUniformlyOn_compacts_of_holder`, and feeds it
  to `exists_lyz_limit`;
* converts the limiting curve into a genuine solution of Newton's equations
  (`isNBodySolution_extendLeft_of_minimizers`, using Marchal's theorem for collision freeness).

The only deep input is `MarchalProperty m h`.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- **A curve that is an `h`-minimiser at every scale is a motion.**  This is
`isNBodySolution_extendLeft_of_calibrating` without the calibration function: the only structural
input is that `γ` is an `h`-minimiser on every `[0,T]`, which is what the Liu--Yan--Zhou limiting
construction produces. -/
theorem isNBodySolution_extendLeft_of_minimizers {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    (hN : 0 < N) (hm : ∀ i, 0 < m i) (hh : 0 < h) (hM : MarchalProperty (E := E) m h)
    (hmin : ∀ T : ℝ, 0 < T → IsHMinimizer m h γ 0 T ∧ AbsolutelyContinuousOnInterval γ 0 T) :
    IsNBodySolution m (extendLeft γ) ∧ (∀ t > 0, WithoutCollisions (γ t)) := by
  classical
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) hN hm hh.le
  have hfin : ∀ a b : EN E N, actionPot m h a b < ⊤ :=
    fun a b => lt_of_le_of_lt (hest a b) ENNReal.ofReal_lt_top
  -- Marchal: the curve is collision free for positive times
  have hnc : ∀ t > 0, WithoutCollisions (γ t) := by
    intro t ht
    have h1 : 0 < t + 1 := by linarith
    exact hM γ 0 (t + 1) h1 (hmin _ h1).2 (hmin _ h1).1 t ⟨ht, by linarith⟩
  have hncIcc : ∀ {a b : ℝ}, 0 < a → a ≤ b → ∀ t ∈ Set.Icc a b, WithoutCollisions (γ t) :=
    fun ha _ t ht => hnc t (lt_of_lt_of_le ha ht.1)
  -- the motion equation and the smoothness at each positive time
  have hmotion : ∀ t > 0, iteratedDeriv 2 γ t = ∇_[m] (U m) (γ t) := by
    intro t ht
    obtain ⟨ε, hε0, hεt⟩ := exists_between ht
    have h2pos : 0 < t + 2 := by linarith
    have hmin' : IsHMinimizer m h γ ε (t + 1) :=
      IsHMinimizer.sub (a := 0) (b := t + 2) (c := ε) (d := t + 1) (hmin _ h2pos).2
        (hmin _ h2pos).1 ((hmin _ h2pos).1 ▸ hfin (γ 0) (γ (t + 2))) hε0 (by linarith) (by linarith)
    exact minimizer_iteratedDeriv_two (a := ε) (b := t + 1) hm hh (by linarith)
      ((hmin _ h2pos).2.mono (by
        rw [uIcc_of_le (by linarith : ε ≤ t + 1), uIcc_of_le (by linarith : (0:ℝ) ≤ t + 2)]
        exact Set.Icc_subset_Icc hε0.le (by linarith)))
      (hncIcc hε0 (by linarith)) hmin' (hfin _ _) t ⟨hεt, by linarith⟩
  have hcd : ContDiffOn ℝ 2 γ (Set.Ioi 0) := by
    intro x hx
    obtain ⟨ε, hε0, hεx⟩ := exists_between (show (0:ℝ) < x from hx)
    have h2pos : 0 < x + 2 := by linarith
    have hcd' : ContDiffOn ℝ 2 γ (Set.Ioo ε (x + 1)) :=
      minimizer_contDiffOn_two (a := ε) (b := x + 1) hm hh (by linarith)
        ((hmin _ h2pos).2.mono (by
          rw [uIcc_of_le (by linarith : ε ≤ x + 1), uIcc_of_le (by linarith : (0:ℝ) ≤ x + 2)]
          exact Set.Icc_subset_Icc hε0.le (by linarith)))
        (hncIcc hε0 (by linarith))
        (IsHMinimizer.sub (a := 0) (b := x + 2) (c := ε) (d := x + 1) (hmin _ h2pos).2
          (hmin _ h2pos).1 ((hmin _ h2pos).1 ▸ hfin (γ 0) (γ (x + 2)))
          hε0 (by linarith) (by linarith))
        (hfin _ _)
    exact (hcd'.contDiffAt (IsOpen.mem_nhds isOpen_Ioo ⟨hεx, lt_add_one x⟩)).contDiffWithinAt
  -- continuity at `0`
  have hright : ContinuousWithinAt (extendLeft γ) (Set.Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hcont1 : ContinuousOn γ (Set.Icc 0 1) := by
      have h := (hmin 1 one_pos).2.continuousOn
      rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h
    obtain ⟨δ, hδ, hδp⟩ := (Metric.continuousOn_iff.mp hcont1) 0
      (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) ε hε
    refine ⟨min δ 1, lt_min hδ one_pos, fun t ht htd => ?_⟩
    have ht1 : t < 1 := by
      have := lt_of_lt_of_le htd (min_le_right δ 1)
      rw [Real.dist_eq, sub_zero, abs_lt] at this
      exact this.2
    rcases eq_or_lt_of_le (show (0:ℝ) ≤ t from ht) with h | h
    · have e1 : extendLeft γ t = γ 0 := by rw [← h]; exact extendLeft_of_nonpos le_rfl
      have e2 : extendLeft γ 0 = γ 0 := extendLeft_of_nonpos le_rfl
      rw [e1, e2]
      simpa using hε
    · rw [extendLeft_of_pos h, extendLeft_of_nonpos le_rfl]
      exact hδp t ⟨h.le, ht1.le⟩ (lt_of_lt_of_le htd (min_le_left δ 1))
  have hcontAt : ContinuousAt (extendLeft γ) 0 := by
    have h1 : Tendsto (extendLeft γ) (𝓝[Set.Iic 0] 0) (𝓝 (γ 0)) := by
      refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (extendLeft_of_nonpos ht).symm
    have h2 : Tendsto (extendLeft γ) (𝓝[Set.Ici 0] 0) (𝓝 (γ 0)) := by
      have hr : Tendsto (extendLeft γ) (𝓝[Set.Ici 0] 0) (𝓝 ((extendLeft γ) 0)) := hright
      rw [show (extendLeft γ) 0 = γ 0 from extendLeft_of_nonpos le_rfl] at hr
      exact hr
    have h3 : 𝓝 (0 : ℝ) = 𝓝[Set.Iic 0] 0 ⊔ 𝓝[Set.Ici 0] 0 := by
      have h := nhdsWithinLE_sup_nhdsWithinGE (s := Set.univ) (a := (0 : ℝ))
      rw [Set.univ_inter, Set.univ_inter, nhdsWithin_univ] at h
      exact h.symm
    rw [ContinuousAt, show (extendLeft γ) 0 = γ 0 from extendLeft_of_nonpos le_rfl, h3,
      tendsto_sup]
    exact ⟨h1, h2⟩
  refine ⟨⟨?_, ?_, ?_⟩, hnc⟩
  · intro x hx
    have hev : extendLeft γ =ᶠ[𝓝[Set.Ioi 0] x] γ := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact extendLeft_of_pos hy
    exact (hcd x hx).congr_of_eventuallyEq hev (extendLeft_of_pos hx)
  · exact hcontAt
  · intro t ht
    have hev : ∀ᶠ s in 𝓝 t, extendLeft γ s = γ s := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact extendLeft_of_pos hs
    have hev' : deriv (extendLeft γ) =ᶠ[𝓝 t] deriv γ := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hs] with y hy
      exact extendLeft_of_pos hy
    have h1 : iteratedDeriv 2 (extendLeft γ) t = iteratedDeriv 2 γ t := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
        iteratedDeriv_succ, iteratedDeriv_one]
      exact Filter.EventuallyEq.deriv_eq hev'
    rw [h1, hmotion t ht, extendLeft_of_pos ht]

/-! ## The angle condition of Liu--Yan--Zhou -/

/-- **The cone angle condition.**  If `x* = x + s • a` with `s` large compared with `‖x‖_[m]/ν` and
`b` is a unit vector (in the mass norm) within `θ` of `a` with `K θ ≤ ν/16`, then the angle between
`x*_i - x*_j` and `b_i - b_j` is at most `60°`, in the form
`(1/2) ‖x*_i - x*_j‖ ‖b_i - b_j‖ ≤ ⟪x*_i - x*_j, b_i - b_j⟫`.

This is the geometric input of the potential-integral estimate. -/
lemma cone_angle {m : Fin N → ℝ} {x a xstar : EN E N} {K ν s θ : ℝ}
    (hK : 0 < K) (hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m]) (hν : 0 < ν)
    (hs : 0 < s) (hθ0 : 0 ≤ θ) (hsep : Separated a ν)
    (hX : 100 * K * ‖x‖_[m] ≤ s * ν) (hKθ : K * θ ≤ ν / 16)
    (hxstar : xstar = x + s • a) :
    ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ i j : Fin N, i ≠ j →
      (1 / 2) * (‖xstar i - xstar j‖ * ‖b i - b j‖) ≤ inner ℝ (xstar i - xstar j) (b i - b j) := by
  intro b hb hba i j hij
  have hA : ν ≤ ‖a i - a j‖ := by
    have h := hsep i j hij
    rwa [dist_eq_norm] at h
  -- the displacement of the initial configuration, in the Euclidean norm
  have hXraw : ‖x i - x j‖ ≤ 2 * (K * ‖x‖_[m]) := by
    have h1 : ‖x i - x j‖ ≤ ‖x i‖ + ‖x j‖ := norm_sub_le _ _
    have h2 : ‖x i‖ ≤ K * ‖x‖_[m] := (norm_apply_le_norm x i).trans (hKn x)
    have h3 : ‖x j‖ ≤ K * ‖x‖_[m] := (norm_apply_le_norm x j).trans (hKn x)
    linarith
  have hX50 : 50 * ‖x i - x j‖ ≤ s * ν := by
    have h1 : 50 * (2 * (K * ‖x‖_[m])) ≤ s * ν := by linarith
    linarith
  -- the perturbation of the direction
  have hE : 16 * ‖(b i - b j) - (a i - a j)‖ ≤ Real.sqrt 2 * ν := by
    have h2 : ‖(b i - b j) - (a i - a j)‖ ≤ Real.sqrt 2 * ‖b - a‖ := by
      have h3 : (b i - b j) - (a i - a j) = (b - a) i - (b - a) j := by
        simp only [PiLp.sub_apply]
        abel
      have h4 : ‖(b - a) i - (b - a) j‖ ^ 2 ≤ 2 * ‖b - a‖ ^ 2 := by
        have h5 : ‖(b - a) i - (b - a) j‖ ≤ ‖(b - a) i‖ + ‖(b - a) j‖ := norm_sub_le _ _
        have hsum : ‖(b - a) i‖ ^ 2 + ‖(b - a) j‖ ^ 2 ≤ ‖b - a‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
          have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i, j} : Finset (Fin N)))
            (fun k _ _ => sq_nonneg (‖(b - a) k‖))
          rwa [Finset.sum_pair hij] at hle
        have h6 : (‖(b - a) i‖ + ‖(b - a) j‖) ^ 2 ≤ 2 * ‖b - a‖ ^ 2 := by
          nlinarith [hsum, norm_nonneg ((b - a) i), norm_nonneg ((b - a) j),
            sq_nonneg (‖(b - a) i‖ - ‖(b - a) j‖)]
        calc ‖(b - a) i - (b - a) j‖ ^ 2
            ≤ (‖(b - a) i‖ + ‖(b - a) j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h5 2
          _ ≤ 2 * ‖b - a‖ ^ 2 := h6
      have h5 : (Real.sqrt 2 * ‖b - a‖) ^ 2 = 2 * ‖b - a‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      rw [h3]
      calc ‖(b - a) i - (b - a) j‖ = Real.sqrt (‖(b - a) i - (b - a) j‖ ^ 2) :=
            (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (2 * ‖b - a‖ ^ 2) := Real.sqrt_le_sqrt h4
        _ = Real.sqrt 2 * ‖b - a‖ := by rw [← h5]; exact Real.sqrt_sq (by positivity)
    have h6 : ‖b - a‖ ≤ K * θ :=
      (hKn (b - a)).trans (mul_le_mul_of_nonneg_left hba hK.le)
    have h7 : Real.sqrt 2 * ‖b - a‖ ≤ Real.sqrt 2 * (K * θ) :=
      mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg 2)
    have h8 : Real.sqrt 2 * (K * θ) ≤ Real.sqrt 2 * (ν / 16) :=
      mul_le_mul_of_nonneg_left hKθ (Real.sqrt_nonneg 2)
    have h9 : 16 * (Real.sqrt 2 * (ν / 16)) = Real.sqrt 2 * ν := by ring
    have h10 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    linarith
  have hmain := Commons.Analysis.InnerProductSpace.half_mul_norm_mul_norm_le_inner_add_smul
    (F := E) (X := x i - x j) (A := a i - a j) (E := (b i - b j) - (a i - a j))
    (s := s) (ν := ν) hs hν hA hX50 hE
  have h1 : x i - x j + s • (a i - a j) = xstar i - xstar j := by
    rw [hxstar]
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_sub]
    abel
  have h2 : a i - a j + ((b i - b j) - (a i - a j)) = b i - b j := by abel
  rw [h1, h2] at hmain
  simpa only [mul_assoc] using hmain

/-- **Theorem 1.1 of Maderna--Venturelli, assuming Marchal's theorem.** -/
theorem theorem_1_1_of_marchal (hE : 2 ≤ Module.finrank ℝ E) (hN : 2 ≤ N)
    (m : Fin N → ℝ) (hm : ∀ i, 0 < m i) (x₀ a : EN E N) (a_nc : WithoutCollisions a)
    (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : 0 < h) (hM : MarchalProperty (E := E) m h) :
    ∃ x : ℝ → EN E N, ∃ o : ℝ → EN E N, (o =o[atTop] fun t => t) ∧ x 0 = x₀ ∧
      IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
        ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t := by
  classical
  have hNpos : 0 < N := by omega
  have hh0 : (0 : ℝ) ≤ h := h_pos.le
  obtain ⟨α, β, hα, hβ, hest⟩ := actionPot_le_holder (E := E) (N := N) hNpos hm hh0
  have hΦall : ∀ x y : EN E N, actionPot m h x y < ⊤ :=
    fun x y => lt_of_le_of_lt (hest x y) ENNReal.ofReal_lt_top
  -- a positive lower bound for the masses and the constant `K`
  obtain ⟨cc, hccpos, hmcc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ m i := by
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin N)) m
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    exact ⟨m i₀, hm i₀, fun i => hi₀ i (Finset.mem_univ i)⟩
  set K : ℝ := max 1 (Real.sqrt cc)⁻¹ with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hK1
  have hKn : ∀ y : EN E N, ‖y‖ ≤ K * ‖y‖_[m] := by
    intro y
    have h1 := norm_le_inv_sqrt_mul hccpos hmcc y
    have h2 : (Real.sqrt cc)⁻¹ ≤ K := le_max_right _ _
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (weightedNorm_nonneg m y))
  -- the separation constant `ν` and the cone width `θ`
  obtain ⟨ν₀, hν₀pos, hν₀sep⟩ := exists_separated_of_withoutCollisions a_nc hN
  set ν : ℝ := min ν₀ 1 with hνdef
  have hνpos : 0 < ν := lt_min hν₀pos one_pos
  have hν1 : ν ≤ 1 := min_le_right _ _
  have hν0 : 0 ≤ ν := hνpos.le
  have hνsep : Separated a ν := hν₀sep.mono (min_le_left _ _)
  set θ : ℝ := min 1 (ν / (16 * K)) with hθdef
  have hθpos : 0 < θ := lt_min one_pos (div_pos hνpos (by linarith))
  have hθ0 : 0 ≤ θ := hθpos.le
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hKθ : K * θ ≤ ν / 16 := by
    have h2 : θ ≤ ν / (16 * K) := min_le_right _ _
    have h3 : K * (ν / (16 * K)) = ν / 16 := by
      field_simp
    exact (mul_le_mul_of_nonneg_left h2 hKpos.le).trans_eq h3
  -- the base point `xstar`
  set s₀ : ℝ := max 1 (‖x₀‖_[m] + 100 * K * ‖x₀‖_[m] / ν) with hs₀def
  have hw0 : 0 ≤ ‖x₀‖_[m] := weightedNorm_nonneg m x₀
  have hs₀1 : 1 ≤ s₀ := by rw [hs₀def]; exact le_max_left _ _
  have hs₀pos : 0 < s₀ := lt_of_lt_of_le one_pos hs₀1
  have hKx : 0 ≤ K * ‖x₀‖_[m] := mul_nonneg hKpos.le hw0
  have hs₀K : ‖x₀‖_[m] + 40 * K * ‖x₀‖_[m] / ν ≤ s₀ := by
    have h1 : ‖x₀‖_[m] + 100 * K * ‖x₀‖_[m] / ν ≤ s₀ := le_max_right _ _
    have h2 : 40 * K * ‖x₀‖_[m] / ν ≤ 100 * K * ‖x₀‖_[m] / ν := by
      rw [div_le_div_iff_of_pos_right hνpos]
      nlinarith [hKx]
    exact (add_le_add le_rfl h2).trans h1
  have hs₀K2 : 50 * K * ‖x₀‖_[m] / ν ≤ s₀ := by
    have h1 : ‖x₀‖_[m] + 100 * K * ‖x₀‖_[m] / ν ≤ s₀ := le_max_right _ _
    have h2 : 50 * K * ‖x₀‖_[m] / ν ≤ ‖x₀‖_[m] + 100 * K * ‖x₀‖_[m] / ν := by
      rw [div_le_iff₀ hνpos]
      have h3 : (‖x₀‖_[m] + 100 * K * ‖x₀‖_[m] / ν) * ν
          = ‖x₀‖_[m] * ν + 100 * K * ‖x₀‖_[m] := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hνpos)]
      rw [h3]
      nlinarith [hKx, hw0, hν0]
    exact h2.trans h1
  have hs₀K100 : 100 * K * ‖x₀‖_[m] / ν ≤ s₀ - ‖x₀‖_[m] := by
    have h1 : ‖x₀‖_[m] + 100 * K * ‖x₀‖_[m] / ν ≤ s₀ := le_max_right _ _
    linarith
  set xstar : EN E N := x₀ + s₀ • a with hxstardef
  have hX100 : 100 * K * ‖x₀‖_[m] ≤ s₀ * ν := by
    have h := (div_le_iff₀ hνpos).mp hs₀K100
    nlinarith [h, hw0, hν0]
  -- the cone collision-freeness, separation, and the potential bound
  have hncB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ s : ℝ, 0 ≤ s →
      WithoutCollisions (xstar + s • b) := by
    intro b hb hba s hs
    refine withoutCollisions_cone_ray (m := m) hm hKpos hKn hνpos hνsep a_norm hb hθ0 hba hKθ
      hs₀1 hs₀K hs₀K2 s hs
  have hsepB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ s : ℝ, 0 ≤ s →
      Separated (xstar + s • b) ((9:ℝ) / 10 * ν) := by
    intro b hb hba s hs
    exact separated_cone_ray (m := m) hm hKpos hKn hνpos hνsep a_norm hb hθ0 hba hKθ
      hs₀1 hs₀K hs₀K2 s hs
  have hsepba : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → Separated b ((7:ℝ) / 8 * ν) := by
    intro b hb hba
    have hd : dist b a ≤ (1 / 16) * ν := by
      rw [dist_eq_norm]
      have h1 : ‖b - a‖ ≤ K * ‖b - a‖_[m] := hKn (b - a)
      have h2 : K * ‖b - a‖_[m] ≤ K * θ := mul_le_mul_of_nonneg_left hba hKpos.le
      have h3 : K * θ ≤ ν / 16 := hKθ
      have h4 : (1 / 16) * ν = ν / 16 := by ring
      rw [h4]
      linarith
    have h := Separated.of_dist_le hνsep hd
    have he : ν - 2 * ((1 / 16) * ν) = (7:ℝ) / 8 * ν := by ring
    rwa [he] at h
  have hsepz : Separated xstar ((7:ℝ) / 8 * ν) := by
    have h0 : ‖a - a‖_[m] = 0 := by rw [sub_self, weightedNorm_zero]
    have h := hsepB a a_norm (by rw [h0]; exact hθ0) 0 le_rfl
    have h1 : xstar + (0:ℝ) • a = xstar := by rw [zero_smul, add_zero]
    rw [h1] at h
    refine h.mono ?_
    exact mul_le_mul_of_nonneg_right (by norm_num) hν0
  obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j : Fin N, i ≠ j :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  have hxstar_sep : (9:ℝ) / 20 * ν ≤ ‖xstar‖ := by
    have h0 : ‖a - a‖_[m] = 0 := by rw [sub_self, weightedNorm_zero]
    have h := hsepB a a_norm (by rw [h0]; exact hθ0) 0 le_rfl
    have h1 : xstar + (0:ℝ) • a = xstar := by rw [zero_smul, add_zero]
    rw [h1] at h
    have h2 : (9:ℝ) / 10 * ν ≤ ‖xstar i₀ - xstar j₀‖ := by
      have hh := h i₀ j₀ hij₀
      rwa [dist_eq_norm] at hh
    have h3 : ‖xstar i₀ - xstar j₀‖ ≤ 2 * ‖xstar‖ := by
      have h4 : ‖xstar i₀ - xstar j₀‖ ≤ ‖xstar i₀‖ + ‖xstar j₀‖ := norm_sub_le _ _
      have h5 : ‖xstar i₀‖ ≤ ‖xstar‖ := norm_apply_le_norm xstar i₀
      have h6 : ‖xstar j₀‖ ≤ ‖xstar‖ := norm_apply_le_norm xstar j₀
      linarith
    linarith
  -- the data of the potential estimate
  set M : ℝ := max 1 (max K (K * ‖xstar‖_[m])) with hMdef
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_trans zero_le_one hM1
  have hKM : K ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKz : ‖xstar‖ ≤ M :=
    (hKn xstar).trans ((le_max_right _ _).trans (le_max_right _ _))
  set νu : ℝ := (7:ℝ) / 8 * ν with hνudef
  have hνupos : 0 < νu := by rw [hνudef]; linarith
  have hνu1 : νu ≤ 1 := by rw [hνudef]; linarith
  have hνuz : ∀ T : ℝ, 0 ≤ T → νu ≤ 2 * K * T + 2 * ‖xstar‖ := by
    intro T hT
    have h1 : νu ≤ 2 * ‖xstar‖ := by rw [hνudef]; linarith
    nlinarith [hT, hKpos]
  have hνuM : ∀ T : ℝ, 0 ≤ T → νu ≤ 2 * K * T + 2 * M := by
    intro T hT
    have h1 : νu ≤ 2 * M := by rw [hνudef]; linarith
    nlinarith [hT, hKpos]
  set BΨ : ℝ := lyzB m h N νu M with hBΨdef
  have hBΨkey : (2 * h) * BΨ
      = (∑ i, m i) ^ 2 * (N:ℝ) ^ 2 * νu⁻¹
          * (1 + (Real.log M + |Real.log νu|) / Real.log (2 * M + 1)) := by
    rw [hBΨdef, lyzB]
    have h2h : (2:ℝ) * h ≠ 0 := by positivity
    have hνne : νu ≠ 0 := ne_of_gt hνupos
    field_simp [h2h, hνne]
  have hBΨ0 : 0 ≤ BΨ := by
    rw [hBΨdef, lyzB]
    have hlog : (0:ℝ) < Real.log (2 * M + 1) := Real.log_pos (by linarith)
    have h2 : (0:ℝ) ≤ 1 + (Real.log M + |Real.log νu|) / Real.log (2 * M + 1) := by
      have h3 : 0 ≤ Real.log M := Real.log_nonneg hM1
      have h4 : 0 ≤ (Real.log M + |Real.log νu|) / Real.log (2 * M + 1) :=
        div_nonneg (add_nonneg h3 (abs_nonneg _)) hlog.le
      linarith
    have hA : (0:ℝ) ≤ (2 * h)⁻¹ := inv_nonneg.mpr (mul_nonneg (by norm_num) hh0)
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hA (sq_nonneg _)) (sq_nonneg _))
      (inv_nonneg.mpr hνupos.le)) h2
  have hangle : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ i j : Fin N, i ≠ j →
      (1 / 2) * (‖xstar i - xstar j‖ * ‖b i - b j‖) ≤ inner ℝ (xstar i - xstar j) (b i - b j) :=
    fun b hb hba => cone_angle (m := m) hKpos hKn hνpos hs₀pos hθ0 hνsep hX100 hKθ hxstardef b hb hba
  have hpotB : ∀ b : EN E N, ‖b‖_[m] = 1 → ‖b - a‖_[m] ≤ θ → ∀ T : ℝ, 0 ≤ T →
      ∫ s in (0:ℝ)..T, U m (xstar + s • b) ≤ (2 * h) * BΨ * Real.log (2 * T + 2 * M + 1) := by
    intro b hb hba T hT
    have hKb : ‖b‖ ≤ K := by
      have h1 := hKn b
      rwa [hb, mul_one] at h1
    have h1 := potentialIntegral_le_logB (m := m) (fun i => (hm i).le) hN (z := xstar) (b := b)
      (ν := νu) (K := K) (M := M) (T := T) hνupos hνu1 hK1 hKM hM1 hKb hKz hT
      (fun i j hij => by
        rw [hνudef]
        have h2 := hsepz i j hij
        rwa [dist_eq_norm] at h2)
      (fun i j hij => by
        rw [hνudef]
        have h2 := hsepba b hb hba i j hij
        rwa [dist_eq_norm] at h2)
      (fun i j hij => hangle b hb hba i j hij)
      (hνuz T hT) (hνuM T hT)
    rw [hBΨkey]
    exact h1
  -- the correction functions `Ψ` and `Ψ̄`
  set AΨ : ℝ := max 1 ((Real.sqrt (2 * h))⁻¹ * (actionPot m h x₀ xstar).toReal) with hAΨdef
  have hAΨ0 : 0 ≤ AΨ := le_trans zero_le_one (le_max_left _ _)
  have hAΨφ : (Real.sqrt (2 * h))⁻¹ * (actionPot m h x₀ xstar).toReal ≤ AΨ := le_max_right _ _
  have hsumm : Summable fun k : ℕ => Real.sqrt (lyzPsi AΨ BΨ M ((2:ℝ) ^ k) / (2:ℝ) ^ k) := by
    have h := Commons.Analysis.Asymptotics.summable_sqrt_log_div_pow AΨ BΨ M hAΨ0 hBΨ0 hM0
    simpa only [lyzPsi] using h
  obtain ⟨D, hDpos, hDle⟩ := tsum_sqrt_lyzPsi_div_le AΨ BΨ M hAΨ0 hBΨ0 hM0
  set C : ℝ := max (Real.sqrt 2) D with hCdef
  have hCpos : 0 < C := lt_of_lt_of_le (Real.sqrt_pos.mpr (by norm_num)) (le_max_left _ _)
  have hC0 : 0 ≤ C := hCpos.le
  have hCsqrt2 : Real.sqrt 2 ≤ C := le_max_left _ _
  have hCD : D ≤ C := le_max_right _ _
  set Ψb : ℝ → ℝ := lyzPsibar AΨ BΨ M C with hΨbdef
  have hΨbnn : ∀ t, 0 ≤ Ψb t := fun t => by
    rw [hΨbdef]
    exact mul_nonneg hC0 (Real.sqrt_nonneg _)
  have hslow : ∀ s t : ℝ, 0 < s → s ≤ t → t ≤ 2 * s → Ψb t ≤ 2 * Ψb s := fun s t hs hst ht2 => by
    rw [hΨbdef]
    exact lyzPsibar_le_two hAΨ0 hBΨ0 hM0 hC0 hs hst ht2
  have hrel : ∀ t : ℝ, 0 < t → Real.sqrt (lyzPsi AΨ BΨ M t / t) ≤ Ψb t := fun t ht => by
    rw [hΨbdef]
    exact sqrt_lyzPsi_div_le_lyzPsibar hAΨ0 hBΨ0 hM0 hCsqrt2 ht
  have hΨnn : ∀ T : ℝ, 0 ≤ T → 0 ≤ lyzPsi AΨ BΨ M T :=
    fun T hT => lyzPsi_nonneg hAΨ0 hBΨ0 hM0 hT
  have hΨmono : ∀ T T' : ℝ, 0 ≤ T → T ≤ T' → lyzPsi AΨ BΨ M T ≤ lyzPsi AΨ BΨ M T' :=
    fun T T' hT hTT' => lyzPsi_le_lyzPsi hBΨ0 hM0 hT hTT'
  have htail : ∀ i : ℕ, lyzTail (lyzPsi AΨ BΨ M) i ≤ Ψb ((2:ℝ) ^ i) := by
    intro i
    have h1 : lyzTail (lyzPsi AΨ BΨ M) i
        ≤ D * lyzPsibar AΨ BΨ M C ((2:ℝ) ^ i) / C := hDle i C hCpos
    have h2 : D * lyzPsibar AΨ BΨ M C ((2:ℝ) ^ i) / C
        ≤ lyzPsibar AΨ BΨ M C ((2:ℝ) ^ i) := by
      rw [show D * lyzPsibar AΨ BΨ M C ((2:ℝ) ^ i) / C
          = (D / C) * lyzPsibar AΨ BΨ M C ((2:ℝ) ^ i) by ring]
      exact mul_le_of_le_one_left (mul_nonneg hC0 (Real.sqrt_nonneg _))
        ((div_le_one hCpos).mpr hCD)
    rw [hΨbdef]
    exact h1.trans h2
  have hΨb0 : Filter.Tendsto Ψb Filter.atTop (nhds 0) := by
    rw [hΨbdef]
    exact tendsto_lyzPsibar_zero AΨ BΨ M C
  have hBΨpos : 0 < BΨ := by
    rw [hBΨdef, lyzB]
    have h1 : (0:ℝ) < (∑ i, m i) ^ 2 := by
      have h2 : (0:ℝ) < ∑ i, m i :=
        Finset.sum_pos (fun i _ => hm i) ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      positivity
    have h2 : (0:ℝ) < (N:ℝ) ^ 2 := by positivity
    have h3 : (0:ℝ) < νu⁻¹ := inv_pos.mpr hνupos
    have h4 : (0:ℝ) < 1 + (Real.log M + |Real.log νu|) / Real.log (2 * M + 1) := by
      have h5 : (0:ℝ) < Real.log (2 * M + 1) := Real.log_pos (by linarith)
      have h6 : 0 ≤ Real.log M := Real.log_nonneg hM1
      have h7 : 0 ≤ (Real.log M + |Real.log νu|) / Real.log (2 * M + 1) :=
        div_nonneg (add_nonneg h6 (abs_nonneg _)) h5.le
      linarith
    have h8 : (0:ℝ) < (2 * h)⁻¹ := inv_pos.mpr (by linarith)
    exact mul_pos (mul_pos (mul_pos (mul_pos h8 h1) h2) h3) h4
  -- the threshold `n₀`
  have hpowmono : ∀ a b : ℕ, a ≤ b → (2:ℝ) ^ a ≤ (2:ℝ) ^ b :=
    fun a b hab => pow_le_pow_right₀ (by norm_num) hab
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, s₀ < (2:ℝ) ^ n := by
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).eventually_gt_atTop s₀)
    exact ⟨n, hn n le_rfl⟩
  obtain ⟨n₂, hn₂⟩ : ∃ n : ℕ, s₀ ≤ lyzPsi AΨ BΨ M ((2:ℝ) ^ (n + 1)) := by
    have h3 : Filter.Tendsto (fun n : ℕ => Real.log (2 * (2:ℝ) ^ (n + 1) + 2 * M + 1))
        Filter.atTop Filter.atTop := by
      refine Real.tendsto_log_atTop.comp ?_
      have h5 : Filter.Tendsto (fun n : ℕ => (2:ℝ) ^ (n + 1)) Filter.atTop Filter.atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).comp
          (Filter.tendsto_add_atTop_nat 1)
      have h6 : Filter.Tendsto (fun n : ℕ => 2 * (2:ℝ) ^ (n + 1)) Filter.atTop Filter.atTop :=
        h5.const_mul_atTop (by norm_num : (0:ℝ) < 2)
      have h7 : Filter.Tendsto (fun n : ℕ => 2 * (2:ℝ) ^ (n + 1) + (2 * M + 1))
          Filter.atTop Filter.atTop := tendsto_atTop_add_const_right _ (2 * M + 1) h6
      simpa only [add_assoc] using h7
    have h4 : Filter.Tendsto (fun n : ℕ => BΨ * Real.log (2 * (2:ℝ) ^ (n + 1) + 2 * M + 1))
        Filter.atTop Filter.atTop := h3.const_mul_atTop hBΨpos
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (h4.eventually_ge_atTop s₀)
    refine ⟨n, ?_⟩
    rw [lyzPsi]
    have h5 := hn n le_rfl
    linarith
  obtain ⟨T₃, hT₃⟩ : ∃ T : ℝ, ∀ t ≥ T, lyzPsi AΨ BΨ M t ≤ t / 2 := by
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
      (eventually_lyzPsi_le_mul AΨ BΨ M (by norm_num : (0:ℝ) < 1 / 2))
    exact ⟨T, fun t ht => by have h := hT t ht; linarith⟩
  obtain ⟨n₄, hn₄⟩ : ∃ n : ℕ, 50 * lyzTail (lyzPsi AΨ BΨ M) (n + 1) ≤ θ := by
    have h3 : Filter.Tendsto (fun i : ℕ => lyzTail (lyzPsi AΨ BΨ M) i) Filter.atTop (nhds 0) :=
      Commons.Analysis.Asymptotics.tendsto_tsum_nat_add_zero hsumm
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
      ((tendsto_order.1 h3).2 (θ / 50) (by linarith))
    refine ⟨n, ?_⟩
    have h4 := hn (n + 1) (by omega)
    linarith
  obtain ⟨S₅, hS₅⟩ : ∃ S : ℝ, ∀ t ≥ S, 64 * Ψb t ≤ θ := by
    obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp
      ((tendsto_order.1 hΨb0).2 (θ / 64) (by linarith))
    exact ⟨S, fun t ht => by have h := hS t ht; linarith⟩
  obtain ⟨S₆, hS₆⟩ : ∃ S : ℝ, ∀ t ≥ S, Ψb t ≤ 1 := by
    obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp ((tendsto_order.1 hΨb0).2 1 one_pos)
    exact ⟨S, fun t ht => le_of_lt (hS t ht)⟩
  obtain ⟨M₃, hM₃⟩ : ∃ M' : ℕ, T₃ ≤ (2:ℝ) ^ M' := by
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).eventually_ge_atTop T₃)
    exact ⟨m, hm m le_rfl⟩
  obtain ⟨M₅, hM₅⟩ : ∃ M' : ℕ, S₅ ≤ (2:ℝ) ^ M' := by
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).eventually_ge_atTop S₅)
    exact ⟨m, hm m le_rfl⟩
  obtain ⟨M₆, hM₆⟩ : ∃ M' : ℕ, S₆ ≤ (2:ℝ) ^ M' := by
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).eventually_ge_atTop S₆)
    exact ⟨m, hm m le_rfl⟩
  set n₀ : ℕ := max (max n₁ (max n₂ n₄)) (max M₃ (max M₅ M₆)) with hn₀def
  have hn₀1 : n₁ ≤ n₀ := le_trans (le_max_left n₁ (max n₂ n₄)) (le_max_left _ _)
  have hn₀2 : n₂ ≤ n₀ :=
    le_trans (le_trans (le_max_left n₂ n₄) (le_max_right n₁ (max n₂ n₄))) (le_max_left _ _)
  have hn₀4 : n₄ ≤ n₀ :=
    le_trans (le_trans (le_max_right n₂ n₄) (le_max_right n₁ (max n₂ n₄))) (le_max_left _ _)
  have hn₀3 : M₃ ≤ n₀ := le_trans (le_max_left M₃ (max M₅ M₆)) (le_max_right _ _)
  have hn₀5 : M₅ ≤ n₀ :=
    le_trans (le_trans (le_max_left M₅ M₆) (le_max_right M₃ (max M₅ M₆))) (le_max_right _ _)
  have hn₀6 : M₆ ≤ n₀ :=
    le_trans (le_trans (le_max_right M₅ M₆) (le_max_right M₃ (max M₅ M₆))) (le_max_right _ _)
  have h0lt : s₀ < (2:ℝ) ^ n₀ := lt_of_lt_of_le hn₁ (hpowmono _ _ hn₀1)
  have hx0₀ : s₀ ≤ lyzPsi AΨ BΨ M ((2:ℝ) ^ (n₀ + 1)) :=
    le_trans hn₂ (hΨmono _ _ (by positivity) (hpowmono _ _ (by omega)))
  have hΨhalf : ∀ i : ℕ, n₀ ≤ i → lyzPsi AΨ BΨ M ((2:ℝ) ^ (i + 1)) ≤ (2:ℝ) ^ (i + 1) / 2 := by
    intro i hi
    refine hT₃ _ ?_
    refine le_trans hM₃ (le_trans (hpowmono _ _ hn₀3) (hpowmono _ _ (by omega)))
  have hS₅n₀ : S₅ ≤ (2:ℝ) ^ n₀ := le_trans hM₅ (hpowmono _ _ hn₀5)
  have hS₆n₀ : S₆ ≤ (2:ℝ) ^ n₀ := le_trans hM₆ (hpowmono _ _ hn₀6)
  have hθ50 : 50 * lyzTail (lyzPsi AΨ BΨ M) (n₀ + 1) ≤ θ := by
    refine le_trans ?_ hn₄
    have hmono : lyzTail (lyzPsi AΨ BΨ M) (n₀ + 1) ≤ lyzTail (lyzPsi AΨ BΨ M) (n₄ + 1) :=
      lyzTail_mono hΨnn hsumm (by omega)
    linarith
  have hθΨb : ∀ t : ℝ, (2:ℝ) ^ n₀ ≤ t → 64 * Ψb t ≤ θ := fun t ht => hS₅ t (le_trans hS₅n₀ ht)
  have hΨb1 : ∀ t : ℝ, (2:ℝ) ^ n₀ ≤ t → Ψb t ≤ 1 := fun t ht => hS₆ t (le_trans hS₆n₀ ht)
  -- the family of `h`-minimisers
  have ha0 : ‖a - a‖_[m] = 0 := by rw [sub_self, weightedNorm_zero]
  have hsubθ : ‖a - a‖_[m] ≤ θ := by rw [ha0]; exact hθ0
  have hex : ∀ n : ℕ, ∃ (τ : ℝ) (γ : ℝ → EN E N), 0 < τ ∧ γ 0 = x₀ ∧
      γ τ = xstar + (2:ℝ) ^ n • a ∧ AbsolutelyContinuousOnInterval γ 0 τ ∧
      IsHMinimizer m h γ 0 τ := by
    intro n
    have hy : WithoutCollisions (xstar + (2:ℝ) ^ n • a) :=
      hncB a a_norm hsubθ _ (by positivity)
    have hxy : x₀ ≠ xstar + (2:ℝ) ^ n • a := by
      intro hc
      have hs₀norm : ‖xstar + (2:ℝ) ^ n • a - x₀‖_[m] = s₀ + (2:ℝ) ^ n := by
        rw [hxstardef]
        have h1 : x₀ + s₀ • a + (2:ℝ) ^ n • a - x₀ = (s₀ + (2:ℝ) ^ n) • a := by
          rw [add_smul]
          abel
        rw [h1, weightedNorm_smul (fun i => (hm i).le) _ a, a_norm, mul_one,
          abs_of_pos (by positivity)]
      have hpos : 0 < ‖xstar + (2:ℝ) ^ n • a - x₀‖_[m] := by rw [hs₀norm]; positivity
      rw [hc, sub_self, weightedNorm_zero] at hpos
      linarith
    obtain ⟨τ, hτ, γ, h0, h1, hac, hmin⟩ := exists_minimizer (m := m) (h := h) (x := x₀)
      (y := xstar + (2:ℝ) ^ n • a) hm h_pos hxy hy (hΦall x₀ _)
    refine ⟨τ, γ, hτ, h0, h1, hac, ?_⟩
    show actionOn m h γ 0 τ = actionPot m h (γ 0) (γ τ)
    rw [h0, h1]
    exact hmin
  choose τm γm hτm hm0 hm1 hmAC hmMin using hex
  set Alin : ℝ := 8 * h * lyzScale h (n₀ + 2) with hAlindef
  set Blin : ℝ := 8 * h with hBlindef
  have hAlin0 : 0 ≤ Alin := by
    rw [hAlindef]
    exact mul_nonneg (mul_nonneg (by norm_num) hh0) (lyzScale_nonneg h_pos _)
  have hBlin0 : 0 ≤ Blin := by rw [hBlindef]; linarith
  -- the Liu--Yan--Zhou estimates for each member of the family
  have hLy : ∀ n : ℕ, ∃ σ : ℕ → ℝ,
      σ n₀ ≤ lyzScale h (n₀ + 2) ∧
      (∀ t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τm (max n n₀)),
        Separated (γm (max n n₀) t) ((9:ℝ) / 10 * ν)) ∧
      (∀ t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τm (max n n₀)),
        ‖γm (max n n₀) t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
          ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2) ∧
      (lyzScale h n ≤ τm (max n n₀)) ∧
      (∀ t ∈ Set.Icc 0 (τm (max n n₀)),
        ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖deriv (γm (max n n₀)) u‖_[m] ^ 2)
          ≤ ENNReal.ofReal (Alin + Blin * t)) := by
    intro n
    have hnf : n₀ ≤ max n n₀ := le_max_right n n₀
    have hfin_m : actionOn m h (γm (max n n₀)) 0 (τm (max n n₀)) < ⊤ := by
      rw [hmMin (max n n₀)]
      exact hΦall _ _
    have h0lt_m : ‖γm (max n n₀) 0 - xstar‖_[m] < (2:ℝ) ^ n₀ := by
      rw [hm0 (max n n₀), hxstardef]
      have h3 : x₀ - (x₀ + s₀ • a) = (-s₀) • a := by
        rw [show x₀ - (x₀ + s₀ • a) = -(s₀ • a) by abel]
        simp
      rw [h3, weightedNorm_smul (fun i => (hm i).le) (-s₀) a, a_norm, mul_one, abs_neg,
        abs_of_pos hs₀pos]
      exact h0lt
    have hAφ_m : (Real.sqrt (2 * h))⁻¹ * (actionPot m h (γm (max n n₀) 0) xstar).toReal ≤ AΨ := by
      rw [hm0 (max n n₀)]
      exact hAΨφ
    have hs₀norm : ‖γm (max n n₀) 0 - xstar‖_[m] = s₀ := by
      rw [hm0 (max n n₀), hxstardef]
      have h3 : x₀ - (x₀ + s₀ • a) = (-s₀) • a := by
        rw [show x₀ - (x₀ + s₀ • a) = -(s₀ • a) by abel]
        simp
      rw [h3, weightedNorm_smul (fun i => (hm i).le) (-s₀) a, a_norm, mul_one, abs_neg,
        abs_of_pos hs₀pos]
    have hx0_m : ∀ i : ℕ, n₀ ≤ i → i < max n n₀ →
        ‖γm (max n n₀) 0 - xstar‖_[m] ≤ lyzPsi AΨ BΨ M ((2:ℝ) ^ (i + 1)) := by
      intro i hi _
      rw [hs₀norm]
      exact hx0₀.trans (hΨmono _ _ (by positivity) (hpowmono _ _ (by omega)))
    have hxstar_m : xstar = γm (max n n₀) 0 + s₀ • a := by
      rw [hm0 (max n n₀)]
    have hs₀K_m : ‖γm (max n n₀) 0‖_[m] + 40 * K * ‖γm (max n n₀) 0‖_[m] / ν ≤ s₀ := by
      rw [hm0 (max n n₀)]; exact hs₀K
    have hs₀K2_m : 50 * K * ‖γm (max n n₀) 0‖_[m] / ν ≤ s₀ := by
      rw [hm0 (max n n₀)]; exact hs₀K2
    obtain ⟨σ, hσm, hσv, hσmono, hsepσ, hncσ, hL2σ, hshapeσ, hDlo, hDhi, hintσ⟩ :=
      exists_lyz_ratio (m := m) (h := h) h_pos hm
        (xstar := xstar) (a := a) (ν := ν) (s₀ := s₀) (θ := θ)
        hνpos hνsep a_norm hKpos hKn hKθ hθ0 hθ1
        (A := AΨ) (B := BΨ) (M := M) hAΨ0 hBΨ0 hM0
        (Ψ := lyzPsi AΨ BΨ M) (Ψb := Ψb)
        hΨnn hΨmono hΨbnn hslow hrel hsumm htail
        (n₀ := n₀) (n := max n n₀) hnf hΨb1
        (hτm (max n n₀)) (hmAC (max n n₀)) hfin_m (hmMin (max n n₀)) (hm1 (max n n₀))
        h0lt_m (hΦall _ _) hAφ_m (fun i hi _ => hΨhalf i hi) hx0_m hpotB hncB (fun _ => rfl) hθ50 hθΨb
        hxstar_m hs₀1 hs₀K_m hs₀K2_m
    have hmono_chain : ∀ k : ℕ, n₀ + k ≤ max n n₀ → σ n₀ ≤ σ (n₀ + k) := by
      intro k
      induction k with
      | zero => intro _; rw [Nat.add_zero]
      | succ k ih =>
        intro hk
        have hk' : n₀ + k ≤ max n n₀ := by omega
        have h1 : σ (n₀ + k) ≤ σ ((n₀ + k) + 1) := hσmono (n₀ + k) (by omega) (by omega)
        have h2 := ih hk'
        have h3 : n₀ + (k + 1) = (n₀ + k) + 1 := by omega
        rw [h3]
        exact h2.trans h1
    have hσn₀_le : σ n₀ ≤ τm (max n n₀) := by
      have h := hmono_chain (max n n₀ - n₀) (by omega)
      rw [Nat.add_sub_cancel' hnf] at h
      rwa [hσm] at h
    have hσmem_m : σ n₀ ∈ Set.Icc 0 (τm (max n n₀)) := (hσv n₀ le_rfl hnf).1
    have hσval_m : ‖γm (max n n₀) (σ n₀) - xstar‖_[m] = (2:ℝ) ^ n₀ := (hσv n₀ le_rfl hnf).2.1
    have hσle : σ n₀ ≤ lyzScale h (n₀ + 2) := by
      have hsqrt2h : 0 < Real.sqrt (2 * h) := Real.sqrt_pos.mpr (by linarith)
      have hden : 0 < 1 + Ψb ((2:ℝ) ^ n₀) ^ 2 := by
        have h2 := hΨbnn ((2:ℝ) ^ n₀)
        nlinarith
      have h1 : Real.sqrt (2 * h) * σ n₀
          ≤ (2:ℝ) ^ n₀ * (1 + Ψb ((2:ℝ) ^ n₀) ^ 2) := by
        have h := hDlo (σ n₀) ⟨le_rfl, hσmem_m.2⟩
        rw [hσval_m] at h
        exact (div_le_iff₀ hden).mp h
      have h2 : Ψb ((2:ℝ) ^ n₀) ≤ 1 := hΨb1 _ le_rfl
      have h3 : Real.sqrt (2 * h) * σ n₀ ≤ (2:ℝ) ^ n₀ * 2 := by
        have h7 : (0:ℝ) ≤ (2:ℝ) ^ n₀ := pow_nonneg (by norm_num) n₀
        have h8 : (2:ℝ) ^ n₀ * Ψb ((2:ℝ) ^ n₀) ^ 2 ≤ (2:ℝ) ^ n₀ * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith [h2, hΨbnn ((2:ℝ) ^ n₀)]) h7
        nlinarith [h1, h8]
      have h4 : σ n₀ ≤ 2 * (2:ℝ) ^ n₀ / Real.sqrt (2 * h) := by
        rw [le_div_iff₀ hsqrt2h]
        linarith [h3]
      have h5 : lyzScale h (n₀ + 2) = 2 * (2:ℝ) ^ n₀ / Real.sqrt (2 * h) := by
        rw [lyzScale]
        have h6 : (2:ℝ) ^ (n₀ + 2) = 4 * (2:ℝ) ^ n₀ := by rw [pow_add]; ring
        rw [h6]
        rw [div_eq_div_iff (by positivity : (2:ℝ) * Real.sqrt (2 * h) ≠ 0) (ne_of_gt hsqrt2h)]
        ring
      rw [h5]
      exact h4
    have hint : ∀ t ∈ Set.Icc 0 (τm (max n n₀)),
        ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖deriv (γm (max n n₀)) u‖_[m] ^ 2)
          ≤ ENNReal.ofReal (Alin + Blin * t) := by
      intro t ht
      rcases le_total (σ n₀) t with hts | hts
      · have h1 := hintσ t ⟨hts, ht.2⟩
        refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
        rw [hAlindef, hBlindef]
        nlinarith [h_pos, ht.1, lyzScale_nonneg h_pos (n₀ + 2)]
      · have h1 : (∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖deriv (γm (max n n₀)) u‖_[m] ^ 2))
            ≤ ∫⁻ u in Set.Ioc 0 (σ n₀), ENNReal.ofReal (‖deriv (γm (max n n₀)) u‖_[m] ^ 2) :=
          lintegral_mono_set (fun x hx => ⟨hx.1, le_trans hx.2 hts⟩)
        have h2 : (∫⁻ u in Set.Ioc 0 (σ n₀),
            ENNReal.ofReal (‖deriv (γm (max n n₀)) u‖_[m] ^ 2))
            ≤ ENNReal.ofReal (8 * h * σ n₀) := hintσ (σ n₀) ⟨le_rfl, hσmem_m.2⟩
        have h3 : 8 * h * σ n₀ ≤ 8 * h * lyzScale h (n₀ + 2) :=
          mul_le_mul_of_nonneg_left hσle (by linarith : (0:ℝ) ≤ 8 * h)
        rw [hAlindef, hBlindef]
        refine (h1.trans h2).trans (ENNReal.ofReal_le_ofReal ?_)
        nlinarith [h3, h_pos, ht.1]
    have hscale : lyzScale h n ≤ τm (max n n₀) := by
      have hm_val : ‖γm (max n n₀) (τm (max n n₀)) - xstar‖_[m] = (2:ℝ) ^ (max n n₀) := by
        rw [hm1 (max n n₀), hxstardef]
        have h3 : x₀ + s₀ • a + (2:ℝ) ^ (max n n₀) • a - (x₀ + s₀ • a)
            = (2:ℝ) ^ (max n n₀) • a := by abel
        rw [h3, weightedNorm_smul (fun i => (hm i).le) _ a, a_norm, mul_one,
          abs_of_nonneg (by positivity)]
      have hDhi_m := hDhi (τm (max n n₀)) ⟨hσn₀_le, le_rfl⟩
      rw [hm_val] at hDhi_m
      have h4 : Ψb ((2:ℝ) ^ (max n n₀)) ≤ 1 := hΨb1 _ (hpowmono _ _ hnf)
      have h5 : (2:ℝ) ^ (max n n₀) ≤ Real.sqrt (2 * h) * τm (max n n₀) * 2 := by
        have h7 : (0:ℝ) ≤ Real.sqrt (2 * h) * τm (max n n₀) :=
          mul_nonneg (Real.sqrt_nonneg _) (hτm (max n n₀)).le
        have h9 : Ψb ((2:ℝ) ^ (max n n₀)) ^ 2 ≤ 1 := by
          have h10 := hΨbnn ((2:ℝ) ^ (max n n₀))
          nlinarith [h4, h10]
        have h8 : Real.sqrt (2 * h) * τm (max n n₀) * (1 + Ψb ((2:ℝ) ^ (max n n₀)) ^ 2)
            ≤ Real.sqrt (2 * h) * τm (max n n₀) * 2 := by nlinarith [h9, h7]
        linarith [hDhi_m, h8]
      have h6 : lyzScale h (max n n₀) ≤ τm (max n n₀) := by
        rw [lyzScale, div_le_iff₀ (by positivity : (0:ℝ) < 2 * Real.sqrt (2 * h))]
        nlinarith [h5]
      exact (lyzScale_mono h_pos (le_max_left n n₀)).trans h6
    refine ⟨σ, hσle, ?_, ?_, hscale, hint⟩
    · intro t ht
      exact hsepσ t ⟨le_trans hσle ht.1, ht.2⟩
    · intro t ht
      exact hshapeσ t ⟨le_trans hσle ht.1, ht.2⟩
  choose σf Hf using hLy
  have hsep_f : ∀ n t, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τm (max n n₀)) →
      Separated (γm (max n n₀) t) ((9:ℝ) / 10 * ν) := fun n t ht => (Hf n).2.1 t ht
  have hshape_f : ∀ n t, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τm (max n n₀)) →
      ‖γm (max n n₀) t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
        ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2 :=
    fun n t ht => (Hf n).2.2.1 t ht
  have hscale_f : ∀ n, lyzScale h n ≤ τm (max n n₀) := fun n => (Hf n).2.2.2.1
  have hint_f : ∀ n t, t ∈ Set.Icc 0 (τm (max n n₀)) →
      ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖deriv (γm (max n n₀)) u‖_[m] ^ 2)
        ≤ ENNReal.ofReal (Alin + Blin * t) := fun n t ht => (Hf n).2.2.2.2 t ht
  have hsep_f : ∀ n t, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τm (max n n₀)) →
      Separated (γm (max n n₀) t) ((9:ℝ) / 10 * ν) := fun n t ht => (Hf n).2.1 t ht
  have hshape_f : ∀ n t, t ∈ Set.Icc (lyzScale h (n₀ + 2)) (τm (max n n₀)) →
      ‖γm (max n n₀) t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] ^ 2
        ≤ 2 ^ 22 * Ψb (Real.sqrt (2 * h) * t / 2) ^ 2 * (Real.sqrt (2 * h) * t) ^ 2 :=
    fun n t ht => (Hf n).2.2.1 t ht
  have hscale_f : ∀ n, lyzScale h n ≤ τm (max n n₀) := fun n => (Hf n).2.2.2.1
  have hint_f : ∀ n t, t ∈ Set.Icc 0 (τm (max n n₀)) →
      ∫⁻ u in Set.Ioc 0 t, ENNReal.ofReal (‖deriv (γm (max n n₀)) u‖_[m] ^ 2)
        ≤ ENNReal.ofReal (Alin + Blin * t) := fun n t ht => (Hf n).2.2.2.2 t ht
  -- the uniform Hölder bound
  have hholder := lyz_holder_bound (m := m) hm (τ := fun n => τm (max n n₀))
    (γ := fun n => γm (max n n₀)) (T := lyzScale h) (A := Alin) (B := Blin)
    hAlin0 hBlin0 (lyzScale_mono h_pos) (fun j => lyzScale_nonneg h_pos j) hscale_f
    (fun n => hmAC (max n n₀)) hint_f
  have hu0 : ∀ n, (fun t : ℝ => γm (max n n₀) (min t (lyzScale h n))) 0 = x₀ := by
    intro n
    show γm (max n n₀) (min (0:ℝ) (lyzScale h n)) = x₀
    have h1 : min (0:ℝ) (lyzScale h n) = 0 := min_eq_left (lyzScale_nonneg h_pos n)
    rw [h1]
    exact hm0 (max n n₀)
  have hucont : ∀ n, ContinuousOn (fun t : ℝ => γm (max n n₀) (min t (lyzScale h n)))
      (Set.Ici 0) := by
    intro n
    have hγc : ContinuousOn (γm (max n n₀)) (Set.Icc 0 (lyzScale h n)) := by
      have h := (hmAC (max n n₀)).continuousOn
      rw [uIcc_of_le (by linarith [hτm (max n n₀)] : (0:ℝ) ≤ τm (max n n₀))] at h
      exact h.mono (Set.Icc_subset_Icc_right (hscale_f n))
    have hminc : Continuous (fun t : ℝ => min t (lyzScale h n)) :=
      continuous_id.min continuous_const
    refine hγc.comp hminc.continuousOn ?_
    intro t ht
    exact ⟨le_min ht (lyzScale_nonneg h_pos n), min_le_right _ _⟩
  have hu_holder : ∀ j n (s t : ℝ), s ∈ Set.Icc 0 (lyzScale h j) → t ∈ Set.Icc 0 (lyzScale h j) →
      dist ((fun u : ℝ => γm (max n n₀) (min u (lyzScale h n))) s)
           ((fun u : ℝ => γm (max n n₀) (min u (lyzScale h n))) t)
        ≤ ((Real.sqrt cc)⁻¹ * Real.sqrt (Alin + Blin * lyzScale h j)) * Real.sqrt |s - t| := by
    intro j n s t hs ht
    have h1 := hholder j n s t hs ht
    have h2 : dist ((fun u : ℝ => γm (max n n₀) (min u (lyzScale h n))) s)
        ((fun u : ℝ => γm (max n n₀) (min u (lyzScale h n))) t)
        = ‖γm (max n n₀) (min s (lyzScale h n))
            - γm (max n n₀) (min t (lyzScale h n))‖ := dist_eq_norm _ _
    rw [h2]
    calc ‖γm (max n n₀) (min s (lyzScale h n)) - γm (max n n₀) (min t (lyzScale h n))‖
        ≤ (Real.sqrt cc)⁻¹ * ‖γm (max n n₀) (min s (lyzScale h n))
            - γm (max n n₀) (min t (lyzScale h n))‖_[m] :=
          norm_le_inv_sqrt_mul hccpos hmcc _
      _ ≤ (Real.sqrt cc)⁻¹ * (Real.sqrt (Alin + Blin * lyzScale h j) * Real.sqrt |s - t|) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Real.sqrt_nonneg cc))
      _ = (Real.sqrt cc)⁻¹ * Real.sqrt (Alin + Blin * lyzScale h j) * Real.sqrt |s - t| := by
          ring
  -- the diagonal extraction
  obtain ⟨φ, hφ, G, hGconv, hGcont, hG0⟩ :=
    Commons.Topology.Metric.exists_strictMono_tendstoUniformlyOn_compacts_of_holder
      (u := fun n t => γm (max n n₀) (min t (lyzScale h n))) (T := lyzScale h)
      (M := fun j => (Real.sqrt cc)⁻¹ * Real.sqrt (Alin + Blin * lyzScale h j)) (x₀ := x₀)
      (lyzScale_mono h_pos) (tendsto_lyzScale h_pos) (fun j => lyzScale_nonneg h_pos j)
      (fun j => mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg cc)) (Real.sqrt_nonneg _))
      hu0 hucont hu_holder
  have hGconvγ : ∀ j, TendstoUniformlyOn (fun k => γm (max (φ k) n₀)) G atTop
      (Set.Icc 0 (lyzScale h j)) := by
    intro j
    refine (hGconv j).congr ?_
    filter_upwards [Filter.eventually_ge_atTop j] with k hk
    intro x hx
    have h2 : lyzScale h j ≤ lyzScale h (max (φ k) n₀) :=
      le_trans (lyzScale_mono h_pos (le_trans hk (hφ.id_le k)))
        (lyzScale_mono h_pos (le_max_left _ _))
    have h3 : lyzScale h j ≤ lyzScale h (φ k) := lyzScale_mono h_pos (le_trans hk (hφ.id_le k))
    show γm (max (φ k) n₀) (min x (lyzScale h (φ k))) = γm (max (φ k) n₀) x
    rw [min_eq_left (le_trans hx.2 h3)]
  -- the limiting curve
  have hLim := exists_lyz_limit (m := m) (h := h) hNpos h_pos hm hccpos hmcc
    (x₀ := x₀) (xstar := xstar) (a := a) (ν := (9:ℝ) / 10 * ν)
    (hν := by linarith) (n₀ := n₀)
    (τ := fun n => τm (max n n₀)) (γ := fun n => γm (max n n₀)) (A := Alin) (B := Blin)
    hAlin0 hBlin0 hscale_f (fun n => hmAC (max n n₀))
    (fun n => by rw [hmMin (max n n₀)]; exact hΦall _ _)
    (fun n => hm0 (max n n₀)) (fun n => hmMin (max n n₀)) hint_f hsep_f hΨbnn hshape_f
    hφ hG0 hGcont hGconvγ
  -- the limiting curve is a motion
  have hsol := isNBodySolution_extendLeft_of_minimizers (m := m) (h := h) hNpos hm h_pos hM
    (fun T hT => ⟨(hLim.1 T hT).1, (hLim.1 T hT).2⟩)
  refine ⟨extendLeft G, fun t => G t - (Real.sqrt (2 * h) * t) • a, ?_, ?_, hsol.1, ?_, ?_⟩
  · -- the remainder is `o(t)`
    refine Asymptotics.isLittleO_iff.mpr ?_
    intro c hc
    have hc2 : 0 < c / 2 := by linarith
    have hconst : 0 < (Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h) := by
      have h1 : (0:ℝ) < (Real.sqrt cc)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hccpos)
      have h2 : (0:ℝ) < (2:ℝ) ^ 11 := by norm_num
      have h3 : (0:ℝ) < Real.sqrt (2 * h) := Real.sqrt_pos.mpr (by linarith)
      positivity
    have hsmall : ∀ᶠ t : ℝ in atTop,
        Ψb (Real.sqrt (2 * h) * t / 2)
          < c / (2 * ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h))) := by
      have harg : Filter.Tendsto (fun t : ℝ => Real.sqrt (2 * h) * t / 2) Filter.atTop Filter.atTop := by
        have h0 : (0:ℝ) < Real.sqrt (2 * h) / 2 := by positivity
        have h1 := Filter.Tendsto.const_mul_atTop h0 (Filter.tendsto_id : Filter.Tendsto (fun t : ℝ => t) Filter.atTop Filter.atTop)
        refine h1.congr' ?_
        filter_upwards with t
        simp only [id_eq]
        ring
      have hε : (0:ℝ) < c / (2 * ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h))) := by positivity
      exact harg.eventually (hΨb0.eventually (isOpen_Iio.mem_nhds hε))
    have hbig : ∀ᶠ t : ℝ in atTop, ‖xstar‖ ≤ (c / 2) * t := by
      have h1 : Filter.Tendsto (fun t : ℝ => (c / 2) * t) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop hc2 (Filter.tendsto_id : Filter.Tendsto (fun t : ℝ => t) Filter.atTop Filter.atTop)
      exact h1.eventually_ge_atTop ‖xstar‖
    filter_upwards [hsmall, hbig, Filter.eventually_ge_atTop (lyzScale h (n₀ + 2)),
      Filter.eventually_gt_atTop (0:ℝ)] with t hsmall hbig hscale hpos
    have ht0 : (0:ℝ) ≤ t := hpos.le
    have h1 : ‖G t - (Real.sqrt (2 * h) * t) • a‖
        ≤ (Real.sqrt cc)⁻¹ * (2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * (Real.sqrt (2 * h) * t))
          + ‖xstar‖ := by
      have h2 : G t - (Real.sqrt (2 * h) * t) • a
          = (G t - xstar - (Real.sqrt (2 * h) * t) • a) + xstar := by abel
      rw [h2]
      have h3 := norm_le_inv_sqrt_mul hccpos hmcc (G t - xstar - (Real.sqrt (2 * h) * t) • a)
      have h4 := hLim.2.2 t hscale
      have h5 : (0:ℝ) ≤ (Real.sqrt cc)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg cc)
      calc ‖(G t - xstar - (Real.sqrt (2 * h) * t) • a) + xstar‖
          ≤ ‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖ + ‖xstar‖ := norm_add_le _ _
        _ ≤ (Real.sqrt cc)⁻¹ * ‖G t - xstar - (Real.sqrt (2 * h) * t) • a‖_[m] + ‖xstar‖ := by
            linarith
        _ ≤ (Real.sqrt cc)⁻¹ * (2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2)
              * (Real.sqrt (2 * h) * t)) + ‖xstar‖ := by
            linarith [mul_le_mul_of_nonneg_left h4 h5]
    have h6 : (Real.sqrt cc)⁻¹ * (2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2)
        * (Real.sqrt (2 * h) * t)) ≤ (c / 2) * t := by
      have h7 : Ψb (Real.sqrt (2 * h) * t / 2)
          ≤ c / (2 * ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h))) := le_of_lt hsmall
      have h8 : (0:ℝ) ≤ Real.sqrt (2 * h) * t :=
        mul_nonneg (Real.sqrt_nonneg _) ht0
      have h9 : (Real.sqrt cc)⁻¹ * 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * Real.sqrt (2 * h)
          ≤ (Real.sqrt cc)⁻¹ * 2 ^ 11
            * (c / (2 * ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h)))) * Real.sqrt (2 * h) := by
        have h10 : (0:ℝ) ≤ (Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h) := by positivity
        have h11 := mul_le_mul_of_nonneg_left h7 h10
        calc (Real.sqrt cc)⁻¹ * 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * Real.sqrt (2 * h)
            = ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h)) * Ψb (Real.sqrt (2 * h) * t / 2) := by
              ring
          _ ≤ ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h))
                * (c / (2 * ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h)))) := h11
          _ = (Real.sqrt cc)⁻¹ * 2 ^ 11
                * (c / (2 * ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h)))) * Real.sqrt (2 * h) := by
              ring
      have h12 : (Real.sqrt cc)⁻¹ * 2 ^ 11
            * (c / (2 * ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Real.sqrt (2 * h)))) * Real.sqrt (2 * h)
          = c / 2 := by
        field_simp
        try ring
      have h13 : (Real.sqrt cc)⁻¹ * (2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2)
          * (Real.sqrt (2 * h) * t))
          = ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * Real.sqrt (2 * h)) * t := by
        ring
      rw [h13]
      rw [show (c / 2) * t = (c / 2) * t by rfl]
      calc ((Real.sqrt cc)⁻¹ * 2 ^ 11 * Ψb (Real.sqrt (2 * h) * t / 2) * Real.sqrt (2 * h)) * t
          ≤ (c / 2) * t := by
            rw [h12] at h9
            exact mul_le_mul_of_nonneg_right h9 ht0
        _ = (c / 2) * t := rfl
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    linarith
  · -- `x 0 = x₀`
    rw [extendLeft_of_nonpos le_rfl]
    exact hG0
  · -- collision freeness for `t > 0`
    intro t ht
    rw [extendLeft_of_pos ht]
    rcases lt_or_ge t (lyzScale h (n₀ + 2)) with hcase | hcase
    · have h1 : 0 < lyzScale h (n₀ + 2) := lyzScale_pos h_pos _
      exact hM G 0 (lyzScale h (n₀ + 2)) h1 (hLim.1 _ h1).2 (hLim.1 _ h1).1 t ⟨ht, hcase⟩
    · exact hLim.2.1 t hcase
  · -- the asymptotic expansion
    intro t ht
    rcases eq_or_lt_of_le ht with h0 | h0
    · rw [← h0, extendLeft_of_nonpos le_rfl]
      simp
    · rw [extendLeft_of_pos h0]
      rw [show (Real.sqrt (2 * h) * t) • a + (G t - (Real.sqrt (2 * h) * t) • a) = G t by
        rw [add_comm, sub_add_cancel]]

end Submission.NBody
