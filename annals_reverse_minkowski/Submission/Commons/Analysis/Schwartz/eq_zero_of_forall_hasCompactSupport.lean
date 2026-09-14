import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Calculus.smoothTransition_radial_iteratedFDeriv_bound

open scoped SchwartzMap
open Filter
open scoped ContDiff Topology

set_option linter.unusedSectionVars false

namespace Commons.Analysis.Schwartz

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]


noncomputable def schwartzCutoff (c : ℝ) : E → ℂ :=
  fun x => ((1 - Real.smoothTransition (c * ‖x‖ - 1) : ℝ) : ℂ)

noncomputable def schwartzPsiC (c : ℝ) : E → ℂ :=
  fun x => (Real.smoothTransition (c * ‖x‖ - 1) : ℂ)

lemma schwartzCutoff_scaled_bound (a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ x : E,
      ‖iteratedFDeriv ℝ a (fun y : E => Real.smoothTransition (c * ‖y‖ - 1)) x‖ ≤ C * c ^ a := by
  obtain ⟨M, hMpos, hM⟩ :=
    Commons.Analysis.Calculus.smoothTransition_radial_norm_iteratedFDeriv_bound a
  refine ⟨M + 1, by linarith, ?_⟩
  intro c hc x
  have hF : ContDiff ℝ ((a : ℕ∞) : ℕ∞ω)
      (fun y : E => Real.smoothTransition (‖y‖ - 1)) :=
    (Commons.Analysis.Calculus.smoothTransition_radial_contDiff (E := E)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hfun : (fun y : E => Real.smoothTransition (c * ‖y‖ - 1))
      = (fun y : E => Real.smoothTransition (‖c • y‖ - 1)) := by
    funext y; rw [norm_smul, Real.norm_of_nonneg hc.le]
  rw [hfun, iteratedFDeriv_comp_const_smul (𝕜 := ℝ) c hF]
  simp only
  rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hc.le a)]
  calc c ^ a * ‖iteratedFDeriv ℝ a (fun z : E => Real.smoothTransition (‖z‖ - 1)) (c • x)‖
      ≤ c ^ a * M := mul_le_mul_of_nonneg_left (hM E (c • x)) (pow_nonneg hc.le a)
    _ ≤ (M + 1) * c ^ a := by nlinarith [pow_nonneg hc.le a, hMpos]

lemma schwartzPsiC_psi_smooth (c : ℝ) (hc : 0 < c) :
    ContDiff ℝ ∞ (fun x : E => Real.smoothTransition (c * ‖x‖ - 1)) := by
  have h1 : ContDiff ℝ ∞ (fun y : E => Real.smoothTransition (‖y‖ - 1)) :=
    Commons.Analysis.Calculus.smoothTransition_radial_contDiff (E := E)
  have h2 : ContDiff ℝ ∞ (fun x : E => c • x) := by fun_prop
  have hfun : (fun x : E => Real.smoothTransition (c * ‖x‖ - 1))
      = (fun y : E => Real.smoothTransition (‖y‖ - 1)) ∘ (fun x : E => c • x) := by
    funext x; simp only [Function.comp_apply]; rw [norm_smul, Real.norm_of_nonneg hc.le]
  rw [hfun]; exact h1.comp h2

lemma schwartzPsiC_contDiff (c : ℝ) (hc : 0 < c) : ContDiff ℝ ∞ (schwartzPsiC (E:=E) c) :=
  Complex.ofRealCLM.contDiff.comp (schwartzPsiC_psi_smooth (E:=E) c hc)

lemma schwartzPsiC_norm_le_one (c : ℝ) (x : E) : ‖schwartzPsiC (E:=E) c x‖ ≤ 1 := by
  have h : schwartzPsiC (E:=E) c x = Complex.ofRealLI (Real.smoothTransition (c*‖x‖-1)) := rfl
  rw [h, Complex.ofRealLI.norm_map, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg _)]
  exact Real.smoothTransition.le_one _

lemma schwartzPsiC_iteratedFDeriv_bound (c : ℝ) (hc : 0 < c) (i : ℕ) (x : E) (C : ℝ)
    (hC : ∀ c : ℝ, 0 < c → ∀ x : E,
      ‖iteratedFDeriv ℝ i (fun y : E => Real.smoothTransition (c * ‖y‖ - 1)) x‖ ≤ C * c ^ i) :
    ‖iteratedFDeriv ℝ i (schwartzPsiC (E:=E) c) x‖ ≤ C * c ^ i := by
  have hcomp : ContDiffAt ℝ ∞ (fun y : E => Real.smoothTransition (c * ‖y‖ - 1)) x :=
    (schwartzPsiC_psi_smooth (E:=E) c hc).contDiffAt
  have hEq : schwartzPsiC (E:=E) c = Complex.ofRealLI ∘
      (fun y : E => Real.smoothTransition (c * ‖y‖ - 1)) := by
    funext y; rfl
  rw [hEq, LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI hcomp
    (i := i) (n := ∞) (by exact_mod_cast le_top)]
  exact hC c hc x

lemma schwartzPsiC_eq_zero_of_le (c : ℝ) (hc : 0 < c) {x : E} (hx : ‖x‖ ≤ 1/c) :
    schwartzPsiC (E:=E) c x = 0 := by
  have h2 : ‖x‖ * c ≤ 1 := (le_div_iff₀ hc).mp hx
  have h2' : c * ‖x‖ ≤ 1 := by linarith
  simp only [schwartzPsiC]
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : c * ‖x‖ - 1 ≤ 0)]
  norm_num

lemma schwartzCutoff_eq_zero_of_tail {c : ℝ} (hc : 0 < c) {x : E} (hx : 2 / c < ‖x‖) :
    schwartzCutoff (E := E) c x = 0 := by
  simp only [schwartzCutoff]
  have h1 : (1:ℝ) ≤ c * ‖x‖ - 1 := by
    have h2 : 2 < c * ‖x‖ := by
      have := (div_lt_iff₀ hc).mp hx
      rw [mul_comm] at this; linarith
    linarith
  rw [Real.smoothTransition.one_of_one_le h1]
  norm_num

lemma schwartzCutoff_hasCompactSupport (c : ℝ) (hc : 0 < c) : HasCompactSupport (schwartzCutoff (E := E) c) := by
  refine IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall (0:E) (2/c))
    (isClosed_tsupport _) (closure_minimal ?_ Metric.isClosed_closedBall)
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  rw [not_le] at h
  exact hx (schwartzCutoff_eq_zero_of_tail hc h)

lemma schwartzCutoff_contDiff (c : ℝ) (hc : 0 < c) : ContDiff ℝ ∞ (schwartzCutoff (E := E) c) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_const.sub (schwartzPsiC_psi_smooth (E:=E) c hc)))

lemma schwartzCutoff_hasTemperateGrowth (c : ℝ) (hc : 0 < c) :
    (schwartzCutoff (E := E) c).HasTemperateGrowth :=
  (schwartzCutoff_hasCompactSupport c hc).hasTemperateGrowth (schwartzCutoff_contDiff c hc)

lemma schwartzCutoff_seminorm_sub_le (f : 𝓢(E,ℂ)) (k a : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ c : ℝ, 0 < c → c ≤ 1 →
      SchwartzMap.seminorm ℝ k a
        (f - SchwartzMap.smulLeftCLM ℂ (schwartzCutoff (E:=E) c) f) ≤ A * c := by
  choose C hCpos hC using fun i => schwartzCutoff_scaled_bound (E:=E) i
  set A : ℝ := SchwartzMap.seminorm ℝ (k+1) a f
      + ∑ i ∈ Finset.range a, (a.choose (i+1) : ℝ) * C (i+1)
          * SchwartzMap.seminorm ℝ k (a-(i+1)) f with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    refine add_nonneg (apply_nonneg _ _) ?_
    refine Finset.sum_nonneg fun i hi => ?_
    exact mul_nonneg (mul_nonneg (by positivity) (hCpos (i+1)).le) (apply_nonneg _ _)
  refine ⟨A, hA0, ?_⟩
  intro c hc hc1
  have htg := schwartzCutoff_hasTemperateGrowth (E:=E) c hc
  set w : 𝓢(E,ℂ) := f - SchwartzMap.smulLeftCLM ℂ (schwartzCutoff (E:=E) c) f with hwdef
  have hwfun : ⇑w = fun x => schwartzPsiC (E:=E) c x * (f : E → ℂ) x := by
    funext x
    simp only [hwdef, sub_apply]
    rw [SchwartzMap.smulLeftCLM_apply_apply htg]
    simp only [schwartzCutoff, schwartzPsiC]
    push_cast
    ring
  refine SchwartzMap.seminorm_le_bound ℝ k a w (by positivity) ?_
  intro x
  rw [hwfun]
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := schwartzPsiC (E:=E) c) (g := (f : E → ℂ))
    (schwartzPsiC_contDiff (E:=E) c hc) (f.smooth ⊤) x (n := a) (hn := by exact_mod_cast le_top)
  have step1 : ‖x‖ ^ k * ‖iteratedFDeriv ℝ a (fun y => schwartzPsiC (E:=E) c y * (f:E→ℂ) y) x‖
      ≤ ∑ i ∈ Finset.range (a+1), (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i (schwartzPsiC (E:=E) c) x‖
          * (‖x‖^k * ‖iteratedFDeriv ℝ (a-i) (f:E→ℂ) x‖) := by
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ a (fun y => schwartzPsiC (E:=E) c y * (f:E→ℂ) y) x‖
        ≤ ‖x‖^k * (∑ i ∈ Finset.range (a+1), (a.choose i : ℝ)
            * ‖iteratedFDeriv ℝ i (schwartzPsiC (E:=E) c) x‖
            * ‖iteratedFDeriv ℝ (a-i) (f:E→ℂ) x‖) :=
          mul_le_mul_of_nonneg_left hmul (by positivity)
      _ = ∑ i ∈ Finset.range (a+1), (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i (schwartzPsiC (E:=E) c) x‖
            * (‖x‖^k * ‖iteratedFDeriv ℝ (a-i) (f:E→ℂ) x‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi; ring
  rw [Finset.sum_range_succ', add_comm] at step1
  have hzero : (a.choose 0 : ℝ) * ‖iteratedFDeriv ℝ 0 (schwartzPsiC (E:=E) c) x‖
      * (‖x‖^k * ‖iteratedFDeriv ℝ (a-0) (f:E→ℂ) x‖)
      ≤ c * SchwartzMap.seminorm ℝ (k+1) a f := by
    rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, norm_iteratedFDeriv_zero]
    by_cases hx : ‖x‖ ≤ 1/c
    · rw [schwartzPsiC_eq_zero_of_le c hc hx, norm_zero, zero_mul]
      exact mul_nonneg hc.le (apply_nonneg _ _)
    · rw [not_le] at hx
      have h1 : ‖schwartzPsiC (E:=E) c x‖ ≤ 1 := schwartzPsiC_norm_le_one c x
      have hp : (0:ℝ) < ‖x‖ := by
        have : 0 < 1/c := div_pos one_pos hc
        linarith
      have h3 : ‖x‖^(k+1) * ‖iteratedFDeriv ℝ a (f:E→ℂ) x‖
          ≤ SchwartzMap.seminorm ℝ (k+1) a f := SchwartzMap.le_seminorm ℝ (k+1) a f x
      have h4 : ‖x‖^k * ‖iteratedFDeriv ℝ a (f:E→ℂ) x‖
          ≤ (1/‖x‖) * SchwartzMap.seminorm ℝ (k+1) a f := by
        calc ‖x‖^k * ‖iteratedFDeriv ℝ a (f:E→ℂ) x‖
            = (1/‖x‖) * (‖x‖^(k+1) * ‖iteratedFDeriv ℝ a (f:E→ℂ) x‖) := by
              rw [pow_succ]; field_simp
          _ ≤ (1/‖x‖) * SchwartzMap.seminorm ℝ (k+1) a f :=
              mul_le_mul_of_nonneg_left h3 (div_nonneg zero_le_one hp.le)
      have h5 : (1/‖x‖) ≤ c := by
        rw [div_le_iff₀ hp]
        have := (div_lt_iff₀ hc).mp hx
        rw [mul_comm] at this; linarith
      calc ‖schwartzPsiC (E:=E) c x‖ * (‖x‖^k * ‖iteratedFDeriv ℝ a (f:E→ℂ) x‖)
          ≤ 1 * ((1/‖x‖) * SchwartzMap.seminorm ℝ (k+1) a f) :=
            mul_le_mul h1 h4 (by positivity) (by positivity)
        _ ≤ c * SchwartzMap.seminorm ℝ (k+1) a f := by
            rw [one_mul]
            exact mul_le_mul_of_nonneg_right h5 (apply_nonneg _ _)
  have hrest : (∑ i ∈ Finset.range a, (a.choose (i+1) : ℝ)
        * ‖iteratedFDeriv ℝ (i+1) (schwartzPsiC (E:=E) c) x‖
        * (‖x‖^k * ‖iteratedFDeriv ℝ (a-(i+1)) (f:E→ℂ) x‖))
      ≤ ∑ i ∈ Finset.range a, (a.choose (i+1) : ℝ) * C (i+1) * c
          * SchwartzMap.seminorm ℝ k (a-(i+1)) f := by
    apply Finset.sum_le_sum
    intro i hi
    have hb : ‖iteratedFDeriv ℝ (i+1) (schwartzPsiC (E:=E) c) x‖ ≤ C (i+1) * c^(i+1) :=
      schwartzPsiC_iteratedFDeriv_bound c hc (i+1) x (C (i+1)) (hC (i+1))
    have hc1' : c^(i+1) ≤ c := by
      calc c^(i+1) = c^i * c := pow_succ c i
        _ ≤ 1 * c := mul_le_mul_of_nonneg_right (pow_le_one₀ hc.le hc1) hc.le
        _ = c := one_mul c
    have hb' : ‖iteratedFDeriv ℝ (i+1) (schwartzPsiC (E:=E) c) x‖ ≤ C (i+1) * c := by
      calc ‖iteratedFDeriv ℝ (i+1) (schwartzPsiC (E:=E) c) x‖ ≤ C (i+1) * c^(i+1) := hb
        _ ≤ C (i+1) * c := mul_le_mul_of_nonneg_left hc1' (hCpos (i+1)).le
    have hs : ‖x‖^k * ‖iteratedFDeriv ℝ (a-(i+1)) (f:E→ℂ) x‖
        ≤ SchwartzMap.seminorm ℝ k (a-(i+1)) f := SchwartzMap.le_seminorm ℝ k (a-(i+1)) f x
    have hnn1 : (0:ℝ) ≤ (a.choose (i+1) : ℝ) := by positivity
    have hnn2 : (0:ℝ) ≤ ‖x‖^k * ‖iteratedFDeriv ℝ (a-(i+1)) (f:E→ℂ) x‖ := by positivity
    calc (a.choose (i+1) : ℝ) * ‖iteratedFDeriv ℝ (i+1) (schwartzPsiC (E:=E) c) x‖
          * (‖x‖^k * ‖iteratedFDeriv ℝ (a-(i+1)) (f:E→ℂ) x‖)
        ≤ (a.choose (i+1) : ℝ) * (C (i+1) * c)
          * SchwartzMap.seminorm ℝ k (a-(i+1)) f := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hb' hnn1
          · exact hs
          · exact hnn2
          · exact mul_nonneg hnn1 (mul_nonneg (hCpos (i+1)).le hc.le)
      _ = (a.choose (i+1) : ℝ) * C (i+1) * c * SchwartzMap.seminorm ℝ k (a-(i+1)) f := by ring
  calc ‖x‖^k * ‖iteratedFDeriv ℝ a (fun y => schwartzPsiC (E:=E) c y * (f:E→ℂ) y) x‖
      ≤ (a.choose 0 : ℝ) * ‖iteratedFDeriv ℝ 0 (schwartzPsiC (E:=E) c) x‖
          * (‖x‖^k * ‖iteratedFDeriv ℝ (a-0) (f:E→ℂ) x‖)
        + ∑ i ∈ Finset.range a, (a.choose (i+1) : ℝ)
          * ‖iteratedFDeriv ℝ (i+1) (schwartzPsiC (E:=E) c) x‖
          * (‖x‖^k * ‖iteratedFDeriv ℝ (a-(i+1)) (f:E→ℂ) x‖) := step1
    _ ≤ c * SchwartzMap.seminorm ℝ (k+1) a f
        + ∑ i ∈ Finset.range a, (a.choose (i+1) : ℝ) * C (i+1) * c
          * SchwartzMap.seminorm ℝ k (a-(i+1)) f := add_le_add hzero hrest
    _ = A * c := by
        rw [hAdef, add_mul, Finset.sum_mul]
        rw [show (∑ i ∈ Finset.range a,
                (a.choose (i+1) : ℝ) * C (i+1) * c * SchwartzMap.seminorm ℝ k (a-(i+1)) f)
              = ∑ i ∈ Finset.range a,
                (a.choose (i+1) : ℝ) * C (i+1) * SchwartzMap.seminorm ℝ k (a-(i+1)) f * c
              from Finset.sum_congr rfl (fun i hi => by ring)]
        ring

lemma schwartzCutoff_tsupport_subset (c : ℝ) (hc : 0 < c) :
    tsupport (schwartzCutoff (E:=E) c) ⊆ Metric.closedBall (0:E) (2/c) := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  rw [Function.mem_support] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  rw [not_le] at h
  exact hx (schwartzCutoff_eq_zero_of_tail hc h)

lemma schwartzCutoff_smulLeft_hasCompactSupport (c : ℝ) (hc : 0 < c) (f : 𝓢(E,ℂ)) :
    HasCompactSupport (⇑(SchwartzMap.smulLeftCLM ℂ (schwartzCutoff (E:=E) c) f)) := by
  refine IsCompact.of_isClosed_subset (ProperSpace.isCompact_closedBall (0:E) (2/c))
    (isClosed_tsupport _) ?_
  refine (SchwartzMap.tsupport_smulLeftCLM_subset (schwartzCutoff (E:=E) c) f).trans ?_
  intro x hx
  exact schwartzCutoff_tsupport_subset c hc hx.2

end

/-- A tempered distribution on a finite-dimensional real inner product space which vanishes on
every compactly supported Schwartz function is zero. -/
theorem eq_zero_of_forall_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : TemperedDistribution E ℂ)
    (h : ∀ θ : SchwartzMap E ℂ, HasCompactSupport (⇑θ) → T θ = 0) : T = 0 := by
  ext f
  set v : ℕ → 𝓢(E,ℂ) := fun n => SchwartzMap.smulLeftCLM ℂ (schwartzCutoff (E:=E) (1/((n:ℝ)+1))) f
    with hvdef
  have hvn : ∀ n, HasCompactSupport (⇑(v n)) := fun n => schwartzCutoff_smulLeft_hasCompactSupport _ (by positivity) f
  have htend : Tendsto v atTop (𝓝 f) := by
    rw [WithSeminorms.tendsto_nhds_atTop (schwartz_withSeminorms ℝ E ℂ) v f]
    intro i ε hε
    obtain ⟨k, a⟩ := i
    obtain ⟨A, hA0, hA⟩ := schwartzCutoff_seminorm_sub_le f k a
    obtain ⟨N, hN⟩ := exists_nat_gt (A/ε)
    refine ⟨N, fun n hn => ?_⟩
    have hcn : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    have hcn1 : 1/((n:ℝ)+1) ≤ 1 := by
      have h1 : (1:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast Nat.le_add_left 1 n
      simpa using one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num) h1
    have h1 := hA (1/((n:ℝ)+1)) hcn hcn1
    have h2 : SchwartzMap.seminorm ℝ k a (v n - f)
        = SchwartzMap.seminorm ℝ k a (f - SchwartzMap.smulLeftCLM ℂ
            (schwartzCutoff (E:=E) (1/((n:ℝ)+1))) f) := by
      rw [hvdef]
      simp only
      rw [show v n - f = -(f - SchwartzMap.smulLeftCLM ℂ (schwartzCutoff (E:=E) (1/((n:ℝ)+1))) f)
          from by rw [hvdef]; abel]
      exact map_neg_eq_map _ _
    rw [show schwartzSeminormFamily ℝ E ℂ (k,a) = SchwartzMap.seminorm ℝ k a from rfl]
    rw [h2]
    refine lt_of_le_of_lt h1 ?_
    have hxn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    rw [mul_one_div]
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < (n:ℝ)+1)]
    have hN' : A < ε * (N:ℝ) := by
      rw [div_lt_iff₀ hε] at hN
      rw [mul_comm] at hN; exact hN
    have : ε * (N:ℝ) ≤ ε * ((n:ℝ)+1) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      linarith
    linarith
  have hTtend : Tendsto (fun n => T (v n)) atTop (𝓝 (T f)) :=
    T.continuous.continuousAt.tendsto.comp htend
  have hzero : (fun n => T (v n)) = fun _ => (0:ℂ) := by
    funext n
    exact h (v n) (hvn n)
  have h0 : Tendsto (fun n => T (v n)) atTop (𝓝 0) := by
    rw [hzero]; exact tendsto_const_nhds
  exact tendsto_nhds_unique hTtend h0


end Commons.Analysis.Schwartz