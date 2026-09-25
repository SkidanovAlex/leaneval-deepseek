import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.Analysis.Fourier.tsum_cos_succ_div_sq

open MeasureTheory Set Finset
open scoped Topology Interval

namespace Commons.Analysis.EulerMaclaurin
noncomputable section

def Aq (a : ℝ) : ℝ → ℝ := fun x => (x-a)*(x-a) - (x-a) + 1/6
def bump (x : ℝ) : ℝ := (Int.fract x)^2 - Int.fract x + 1/6

lemma hasDerivAt_Aq (a : ℝ) (x : ℝ) : HasDerivAt (Aq a) (2*(x-a) - 1) x := by
  unfold Aq
  have h1 : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
  have hm : HasDerivAt (fun y : ℝ => (y-a)*(y-a)) (1*(x-a) + (x-a)*1) x := h1.mul h1
  have h := (hm.sub h1).add_const (1/6)
  have : (1 * (x - a) + (x - a) * 1 - 1 : ℝ) = 2*(x-a) - 1 := by ring
  rw [this] at h
  exact h

lemma hasDerivAt_Aq' (a : ℝ) (x : ℝ) : HasDerivAt (fun y : ℝ => 2*(y-a)-1) 2 x := by
  have h1 : HasDerivAt (fun y : ℝ => y - a) 1 x := (hasDerivAt_id x).sub_const a
  have hm := h1.const_mul 2
  have h := hm.sub_const 1
  have : (2 * 1 : ℝ) = 2 := by ring
  rw [this] at h
  exact h

lemma em_interval (a : ℝ) (g g' g'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hcont : Continuous g'') :
    (∫ x in a..(a+1), g x)
      = (g a + g (a+1))/2 - (g' (a+1) - g' a)/12
        + (1/2) * ∫ x in a..(a+1), (Aq a x : ℂ) * g'' x := by
  have hgp : Continuous g' := continuous_iff_continuousAt.mpr (fun x => (h2 x).continuousAt)
  have hcont2 : Continuous (fun x : ℝ => ((2*(x-a)-1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have hIBP1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a+1)
    (u := fun x : ℝ => (Aq a x : ℂ)) (v := g')
    (u' := fun x => ((2*(x-a)-1 : ℝ) : ℂ)) (v' := g'')
    (fun x _ => (hasDerivAt_Aq a x).ofReal_comp) (fun x _ => h2 x)
    (hcont2.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  have hIBP2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := a+1)
    (u := fun x : ℝ => ((2*(x-a)-1 : ℝ) : ℂ)) (v := g)
    (u' := fun _ => (2:ℂ)) (v' := g')
    (fun x _ => (hasDerivAt_Aq' a x).ofReal_comp) (fun x _ => h1 x)
    ((continuous_const).intervalIntegrable _ _) (hgp.intervalIntegrable _ _)
  have h_u_b : (Aq a (a+1) : ℂ) = 1/6 := by unfold Aq; push_cast; ring
  have h_u_a : (Aq a a : ℂ) = 1/6 := by unfold Aq; push_cast; ring
  have h_u'_b : (((2*((a+1)-a)-1 : ℝ)) : ℂ) = 1 := by push_cast; ring
  have h_u'_a : (((2*(a-a)-1 : ℝ)) : ℂ) = -1 := by push_cast; ring
  have h2g : (2:ℂ) * (∫ x in a..(a+1), g x)
      = (∫ x in a..(a+1), (Aq a x : ℂ) * g'' x)
        + g (a+1) + g a - (1/6) * (g' (a+1) - g' a) := by
    rw [hIBP1, hIBP2, h_u_b, h_u_a, h_u'_b, h_u'_a,
        intervalIntegral.integral_const_mul]
    ring
  have hpi : (2:ℂ) ≠ 0 := by norm_num
  have hgoal : (2:ℂ) * (∫ x in a..(a+1), g x)
      = (2:ℂ) * ((g a + g (a+1))/2 - (g' (a+1) - g' a)/12
        + (1/2) * ∫ x in a..(a+1), (Aq a x : ℂ) * g'' x) := by
    rw [h2g]; ring
  exact mul_left_cancel₀ hpi hgoal

lemma em_sub (a : ℝ) (g g' g'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hcont : Continuous g'') :
    g a - (∫ x in a..(a+1), g x)
      = (g a - g (a+1))/2 + (g' (a+1) - g' a)/12
        - (1/2) * ∫ x in a..(a+1), (Aq a x : ℂ) * g'' x := by
  have he := em_interval a g g' g'' h1 h2 hcont
  rw [he]; ring

lemma fract_eq_of_mem_Ico {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ico (n:ℝ) (n+1)) :
    Int.fract x = x - n := by
  have hfloor : ⌊x⌋ = (n:ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast hx.1, by push_cast; exact hx.2⟩
  unfold Int.fract
  rw [hfloor]
  push_cast
  ring

lemma bump_eq_Aq (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (n:ℝ) (n+1)) :
    bump x = Aq n x := by
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hfr : Int.fract x = x - n := fract_eq_of_mem_Ico ⟨hx.1, hlt⟩
    unfold bump Aq
    rw [hfr]
    ring
  · subst heq
    have hf : Int.fract ((n:ℝ) + 1) = 0 := by simp
    unfold bump Aq
    rw [hf]
    push_cast
    ring

lemma em_global (P : ℕ) (g g' g'' : ℝ → ℂ)
    (h1 : ∀ x, HasDerivAt g (g' x) x) (h2 : ∀ x, HasDerivAt g' (g'' x) x)
    (hcont : Continuous g'') :
    (∑ p ∈ Finset.range P, g p) - (∫ x in (0:ℝ)..(P:ℝ), g x)
      = (g 0 - g P)/2 + (g' P - g' 0)/12
        - (1/2) * ∫ x in (0:ℝ)..(P:ℝ), (bump x : ℂ) * g'' x := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun x => (h1 x).continuousAt)
  have hper : ∀ n : ℕ, (g n - (∫ x in (n:ℝ)..((n:ℝ)+1), g x))
      = (g n - g ((n:ℝ)+1))/2 + (g' ((n:ℝ)+1) - g' n)/12
        - (1/2) * ∫ x in (n:ℝ)..((n:ℝ)+1), (bump x : ℂ) * g'' x := by
    intro n
    have hb : (∫ x in (n:ℝ)..((n:ℝ)+1), (bump x : ℂ) * g'' x)
        = ∫ x in (n:ℝ)..((n:ℝ)+1), (Aq n x : ℂ) * g'' x := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxI : x ∈ Set.Icc (n:ℝ) (n+1) := by
        rwa [Set.uIcc_of_le (by linarith : (n:ℝ) ≤ (n:ℝ)+1)] at hx
      change (bump x : ℂ) * g'' x = (Aq n x : ℂ) * g'' x
      rw [bump_eq_Aq n hxI]
    rw [hb, em_sub (n:ℝ) g g' g'' h1 h2 hcont]
  have hL2 : ∑ p ∈ Finset.range P, (g p - (∫ x in (p:ℝ)..((p:ℝ)+1), g x))
      = (∑ p ∈ Finset.range P, g p) - ∫ x in (0:ℝ)..(P:ℝ), g x := by
    rw [Finset.sum_sub_distrib]
    congr 1
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun k : ℕ => (k:ℝ)) (n := P)
      (by intro k hk; exact hgc.intervalIntegrable _ _)
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hR2 : ∑ p ∈ Finset.range P, ((g p - g ((p:ℝ)+1))/2 + (g' ((p:ℝ)+1) - g' p)/12
        - (1/2) * ∫ x in (p:ℝ)..((p:ℝ)+1), (bump x : ℂ) * g'' x)
      = (g 0 - g P)/2 + (g' P - g' 0)/12
        - (1/2) * ∫ x in (0:ℝ)..(P:ℝ), (bump x : ℂ) * g'' x := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have ht1 : ∑ p ∈ Finset.range P, (g p - g ((p:ℝ)+1)) = g 0 - g P := by
      simpa using Finset.sum_range_sub' (fun p : ℕ => g (p:ℝ)) P
    have ht2 : ∑ p ∈ Finset.range P, (g' ((p:ℝ)+1) - g' p) = g' P - g' 0 := by
      simpa using Finset.sum_range_sub (fun p : ℕ => g' (p:ℝ)) P
    have hs1 : ∑ p ∈ Finset.range P, (g p - g ((p:ℝ)+1))/2 = (g 0 - g P)/2 := by
      rw [← Finset.sum_div, ht1]
    have hs2 : ∑ p ∈ Finset.range P, (g' ((p:ℝ)+1) - g' p)/12 = (g' P - g' 0)/12 := by
      rw [← Finset.sum_div, ht2]
    have hs3 : ∑ p ∈ Finset.range P, (1/2) * ∫ x in (p:ℝ)..((p:ℝ)+1), (bump x : ℂ) * g'' x
        = (1/2) * ∫ x in (0:ℝ)..(P:ℝ), (bump x : ℂ) * g'' x := by
      rw [← Finset.mul_sum]
      congr 1
      have hint : ∀ k < P, IntervalIntegrable (fun x => (bump x : ℂ) * g'' x) volume (k:ℝ) ((k:ℝ)+1) := by
        intro k hk
        apply ContinuousOn.intervalIntegrable
        refine ContinuousOn.congr (f := fun x => (Aq k x : ℂ) * g'' x) ?_ ?_
        · exact ((Complex.continuous_ofReal.comp (by unfold Aq; fun_prop)).mul hcont).continuousOn
        · intro x hx
          have hxI : x ∈ Set.Icc (k:ℝ) (k+1) := by
            rwa [Set.uIcc_of_le (by linarith : (k:ℝ) ≤ (k:ℝ)+1)] at hx
          change (bump x : ℂ) * g'' x = (Aq k x : ℂ) * g'' x
          rw [bump_eq_Aq k hxI]
      have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
        (f := fun x => (bump x : ℂ) * g'' x) (a := fun k : ℕ => (k:ℝ)) (n := P)
        (by intro k hk; simpa [Nat.cast_add, Nat.cast_one] using hint k hk)
      simpa [Nat.cast_add, Nat.cast_one] using h
    rw [hs1, hs2, hs3]
  rw [← hL2, ← hR2]
  exact Finset.sum_congr rfl (fun p hp => hper p)


lemma bump_eq_fourier (x : ℝ) :
    bump x = (1/Real.pi^2) * ∑' k : ℕ, Real.cos (2*Real.pi*((k:ℝ)+1)*x) / ((k:ℝ)+1)^2 := by
  have h0 : 0 ≤ 2*Real.pi*Int.fract x := by
    have := Int.fract_nonneg x; positivity
  have h2 : 2*Real.pi*Int.fract x ≤ 2*Real.pi := by
    have := Int.fract_lt_one x
    nlinarith [Real.pi_pos]
  have h := Commons.Analysis.Fourier.tsum_cos_succ_div_sq (θ := 2*Real.pi*Int.fract x) h0 h2
  have hcos : ∀ k : ℕ, Real.cos (2*Real.pi*((k:ℝ)+1)*x)
      = Real.cos (((k:ℝ)+1)*(2*Real.pi*Int.fract x)) := by
    intro k
    have hm : (2*Real.pi*((k:ℝ)+1)*x)
        = ((k:ℝ)+1)*(2*Real.pi*Int.fract x)
          + ((((k+1:ℤ)) * ⌊x⌋ : ℤ) : ℝ) * (2*Real.pi) := by
      have hxf : x = Int.fract x + (⌊x⌋:ℝ) := (Int.fract_add_floor x).symm
      conv_lhs => rw [hxf]
      push_cast
      ring
    rw [hm, Real.cos_add_int_mul_two_pi]
  have hT : (∑' k : ℕ, Real.cos (2*Real.pi*((k:ℝ)+1)*x) / ((k:ℝ)+1)^2)
      = (∑' k : ℕ, Real.cos (((k:ℝ)+1)*(2*Real.pi*Int.fract x)) / ((k:ℝ)+1)^2) := by
    apply tsum_congr; intro k; rw [hcos k]
  rw [hT, h]
  have hpi2 : Real.pi ^ 2 ≠ 0 := pow_ne_zero 2 Real.pi_ne_zero
  field_simp
  unfold bump
  ring

/-- The main term-by-term integration. -/
lemma bump_tsum_integral (P : ℕ) (g'' : ℝ → ℂ) (hcont : Continuous g'') :
    (∫ x in (0:ℝ)..(P:ℝ), (bump x : ℂ) * g'' x)
      = (1/Real.pi^2) * ∑' k : ℕ, (1/((k:ℝ)+1)^2) *
          ∫ x in (0:ℝ)..(P:ℝ), (Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℂ) * g'' x := by
  set s : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc (0:ℝ) (P:ℝ), isCompact_uIcc⟩ with hs
  let F : ℕ → C(ℝ, ℂ) := fun k => ⟨fun x =>
      (((1/Real.pi^2) * (1/((k:ℝ)+1)^2) * Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℝ) : ℂ) * g'' x,
      by fun_prop⟩
  have hsumi : Summable (fun k : ℕ => 1 / ((k:ℝ)+1)^2) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n:ℝ)^2) 1).2
      ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num))
    simpa [Nat.cast_add, Nat.cast_one] using h
  have hbound : Summable (fun k : ℕ => (1/Real.pi^2) * (1/((k:ℝ)+1)^2)
      * ‖(⟨g'', hcont⟩ : C(ℝ, ℂ)).restrict s‖) := by
    have h2 := hsumi.mul_right ‖(⟨g'', hcont⟩ : C(ℝ, ℂ)).restrict s‖
    have h3 := h2.mul_left (1/Real.pi^2)
    refine h3.congr (fun k => ?_)
    ring
  have hsum' : Summable (fun k : ℕ => ‖(F k).restrict s‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hbound
    rw [ContinuousMap.norm_le _ (by positivity)]
    intro y
    have hgM : ‖g'' ((y : ↥(s : Set ℝ)) : ℝ)‖
        ≤ ‖(⟨g'', hcont⟩ : C(ℝ, ℂ)).restrict s‖ := by
      have h := ContinuousMap.norm_coe_le_norm ((⟨g'', hcont⟩ : C(ℝ, ℂ)).restrict s) y
      rwa [ContinuousMap.restrict_apply] at h
    have hcosb : ‖((Real.cos (2*Real.pi*((k:ℝ)+1)*((y : ↥(s : Set ℝ)) : ℝ)) : ℂ))‖ ≤ 1 := by
      rw [show ‖((Real.cos (2*Real.pi*((k:ℝ)+1)*((y : ↥(s : Set ℝ)) : ℝ)) : ℂ))‖
            = |Real.cos (2*Real.pi*((k:ℝ)+1)*((y : ↥(s : Set ℝ)) : ℝ))| from RCLike.norm_ofReal _]
      exact Real.abs_cos_le_one _
    show ‖(((1/Real.pi^2) * (1/((k:ℝ)+1)^2)
        * Real.cos (2*Real.pi*((k:ℝ)+1)*((y : ↥(s : Set ℝ)) : ℝ)) : ℝ) : ℂ)
        * g'' ((y : ↥(s : Set ℝ)) : ℝ)‖ ≤ (1/Real.pi^2) * (1/((k:ℝ)+1)^2)
        * ‖(⟨g'', hcont⟩ : C(ℝ, ℂ)).restrict s‖
    rw [norm_mul,
      show ‖(((1/Real.pi^2) * (1/((k:ℝ)+1)^2)
        * Real.cos (2*Real.pi*((k:ℝ)+1)*((y : ↥(s : Set ℝ)) : ℝ)) : ℝ) : ℂ)‖
        = |(1/Real.pi^2) * (1/((k:ℝ)+1)^2)
        * Real.cos (2*Real.pi*((k:ℝ)+1)*((y : ↥(s : Set ℝ)) : ℝ))| from RCLike.norm_ofReal _,
      abs_mul, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 1/Real.pi^2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/((k:ℝ)+1)^2)]
    calc (1/Real.pi^2) * (1/((k:ℝ)+1)^2)
          * |Real.cos (2*Real.pi*((k:ℝ)+1)*((y : ↥(s : Set ℝ)) : ℝ))|
          * ‖g'' ((y : ↥(s : Set ℝ)) : ℝ)‖
        ≤ (1/Real.pi^2) * (1/((k:ℝ)+1)^2) * 1
          * ‖(⟨g'', hcont⟩ : C(ℝ, ℂ)).restrict s‖ := by
          gcongr
          exact Real.abs_cos_le_one _
      _ = (1/Real.pi^2) * (1/((k:ℝ)+1)^2)
          * ‖(⟨g'', hcont⟩ : C(ℝ, ℂ)).restrict s‖ := by ring
  have htsum := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (a := (0:ℝ)) (b := (P:ℝ)) (f := F) hsum'
  have hFint : ∀ k : ℕ, (∫ x in (0:ℝ)..(P:ℝ), F k x)
      = ((1/Real.pi^2 : ℝ) : ℂ) * ((((1/((k:ℝ)+1)^2 : ℝ)) : ℂ)
          * ∫ x in (0:ℝ)..(P:ℝ), (Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℂ) * g'' x) := by
    intro k
    have h1 : (∫ x in (0:ℝ)..(P:ℝ), F k x)
        = ∫ x in (0:ℝ)..(P:ℝ), ((1/Real.pi^2 : ℝ) : ℂ)
            * ((((1/((k:ℝ)+1)^2 : ℝ)) : ℂ)
              * ((Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℂ) * g'' x)) := by
      apply intervalIntegral.integral_congr; intro x hx
      show F k x = _
      dsimp only [F]
      simp only [ContinuousMap.coe_mk]
      push_cast
      ring
    rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hL : (∑' k : ℕ, ∫ x in (0:ℝ)..(P:ℝ), F k x)
      = (1/Real.pi^2) * ∑' k : ℕ, (1/((k:ℝ)+1)^2) *
          ∫ x in (0:ℝ)..(P:ℝ), (Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℂ) * g'' x := by
    rw [show (∑' k : ℕ, ∫ x in (0:ℝ)..(P:ℝ), F k x)
        = ∑' k : ℕ, ((1/Real.pi^2 : ℝ) : ℂ) * ((((1/((k:ℝ)+1)^2 : ℝ)) : ℂ)
            * ∫ x in (0:ℝ)..(P:ℝ), (Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℂ) * g'' x) from
          tsum_congr hFint]
    rw [tsum_mul_left]
    push_cast
    rfl
  have hR : (∫ x in (0:ℝ)..(P:ℝ), ∑' k : ℕ, F k x)
      = ∫ x in (0:ℝ)..(P:ℝ), (bump x : ℂ) * g'' x := by
    apply intervalIntegral.integral_congr; intro x hx
    change (∑' k : ℕ, F k x) = (bump x : ℂ) * g'' x
    have hpw : (∑' k : ℕ, ((1/Real.pi^2) * (1/((k:ℝ)+1)^2)
        * Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℝ)) = bump x := by
      rw [bump_eq_fourier x, ← tsum_mul_left]
      apply tsum_congr; intro k; ring
    have hFx : (∑' k : ℕ, F k x)
        = (∑' k : ℕ, ((((1/Real.pi^2) * (1/((k:ℝ)+1)^2)
            * Real.cos (2*Real.pi*((k:ℝ)+1)*x) : ℝ)) : ℂ)) * g'' x := by
      rw [← tsum_mul_right]
      apply tsum_congr; intro k
      show F k x = _
      dsimp only [F]
      simp only [ContinuousMap.coe_mk]
    rw [hFx, ← Complex.ofReal_tsum, hpw]
  rw [← hR, ← htsum, hL]


theorem sum_sub_integral_cos_series (P : ℕ) (hP : 1 ≤ P) (g g' g'' : ℝ → ℂ)
    (h1 : ∀ x : ℝ, HasDerivAt g (g' x) x) (h2 : ∀ x : ℝ, HasDerivAt g' (g'' x) x)
    (hcont : Continuous g'') :
    (∑ p ∈ Finset.range P, g p) - ∫ s in (0 : ℝ)..(P : ℝ), g s
      = (g 0 - g P) / 2 + (g' P - g' 0) / 12
        - (1 / (2 * Real.pi ^ 2)) * ∑' k : ℕ, (1 / ((k : ℝ) + 1) ^ 2) *
            ∫ s in (0 : ℝ)..(P : ℝ),
              (Real.cos (2 * Real.pi * ((k : ℝ) + 1) * s) : ℂ) * g'' s := by
  rw [em_global P g g' g'' h1 h2 hcont, bump_tsum_integral P g'' hcont]
  ring

end
end Commons.Analysis.EulerMaclaurin