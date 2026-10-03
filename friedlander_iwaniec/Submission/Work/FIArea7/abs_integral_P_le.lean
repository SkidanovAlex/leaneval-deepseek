import Mathlib
import Submission.Work.FIArea7.Defs

/-!
# The Fourier remainder bound `|∫₀¹ P α K x dx| ≤ 4/(K |sin(α/2)|)`

This file proves the elementary analytic estimate that controls the remainder of the
Fourier expansion of the log-sine series:

`∑_{n=1}^K cos(nα)/n = -log(2|sin(α/2)|) - ∫₀¹ P α K x dx`,

so that the truncation error is a genuine `O(1/(K |sin(α/2)|))`.

The argument avoids the closed form `∫₀¹ P α 0 = -log(2|sin(α/2)|)` entirely: integrating the
telescoping identity `P α K - P α M = ∑_{K<n≤M} x^{n-1} cos(nα)` and pushing `M → ∞` (where
`∫₀¹ P α M → 0` because the integrand is `O(x^M)` while `Q α · ≥ min(1/4, 2 sin²(α/2)) > 0` on
`[0,1]`) expresses `∫₀¹ P α K` as the tail of the cosine series, whose size is controlled by Abel
summation and the Dirichlet kernel bound `|∑_{m≤n} cos(mα)| ≤ 1/|sin(α/2)|`.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Work.FIArea7

noncomputable section

/-! ## The Dirichlet kernel bound -/

/-- **Dirichlet kernel bound**: `|∑_{m=1}^{n} cos(mα)| ≤ 1/|sin(α/2)|`.  -/
lemma abs_sum_cos_Icc_le (α : ℝ) (hs : Real.sin (α / 2) ≠ 0) (n : ℕ) :
    |∑ m ∈ Finset.Icc 1 n, Real.cos ((m : ℝ) * α)| ≤ 1 / |Real.sin (α / 2)| := by
  have hre : ∑ m ∈ Finset.Icc 1 n, Real.cos ((m : ℝ) * α)
      = ∑ i ∈ Finset.range n, Real.cos (α * i + α) := by
    rw [Commons.Analysis.Summation.sum_Icc_one_eq_range]
    refine Finset.sum_congr rfl ?_
    intro i _
    congr 1
    push_cast
    ring
  rw [hre]
  have h := Real.sin_mul_sum_cos n α α
  have hb : |Real.sin ((n : ℝ) * α / 2) * Real.cos (((n : ℝ) - 1) * α / 2 + α)| ≤ 1 := by
    rw [abs_mul]
    calc |Real.sin ((n:ℝ) * α / 2)| * |Real.cos (((n:ℝ) - 1) * α / 2 + α)|
        ≤ 1 * 1 := by
          exact mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
      _ = 1 := by ring
  have h1 : |Real.sin (α / 2)| * |∑ i ∈ Finset.range n, Real.cos (α * i + α)| ≤ 1 := by
    rw [← abs_mul, h]
    exact hb
  have hpos : 0 < |Real.sin (α / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos, mul_comm]
  exact h1

/-! ## Abel summation

We represent the tail of the cosine series in terms of the partial sums
`S n = ∑_{m=1}^n cos(mα)` by summation by parts (`Finset.sum_Ico_by_parts`). -/

/-- **Abel summation identity** for the cosine series. -/
lemma abel_identity (α : ℝ) (K M : ℕ) (hKM : K < M) :
    ∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1)
      = (∑ m ∈ Finset.Icc 1 M, Real.cos ((m:ℝ)*α)) / (M:ℝ)
        - (∑ m ∈ Finset.Icc 1 K, Real.cos ((m:ℝ)*α)) / ((K:ℝ)+1)
        + ∑ j ∈ Finset.Ico (K+1) M,
            (1/(j:ℝ) - 1/((j:ℝ)+1)) * (∑ m ∈ Finset.Icc 1 j, Real.cos ((m:ℝ)*α)) := by
  have hM1 : 1 ≤ M := by omega
  set f : ℕ → ℝ := fun i => 1/((i:ℝ)+1) with hf
  set g : ℕ → ℝ := fun i => Real.cos (((i:ℝ)+1)*α) with hg
  have hG : ∀ n, ∑ i ∈ Finset.range n, g i = ∑ m ∈ Finset.Icc 1 n, Real.cos ((m:ℝ)*α) := by
    intro n
    rw [Commons.Analysis.Summation.sum_Icc_one_eq_range]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [hg]
    congr 1
    push_cast; ring
  have hbp := Finset.sum_Ico_by_parts f g hKM
  simp only [smul_eq_mul] at hbp
  simp only [hG] at hbp
  have hfM : f (M-1) = 1/(M:ℝ) := by
    simp only [hf]
    rw [Nat.cast_sub hM1, Nat.cast_one]
    ring
  have hfK : f K = 1/((K:ℝ)+1) := by simp only [hf]
  rw [hfM, hfK] at hbp
  have hL : ∑ i ∈ Finset.Ico K M, f i * g i
      = ∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [hf, hg]
    ring
  rw [hL] at hbp
  rw [hbp]
  have e1 : (1:ℝ)/(M:ℝ) * (∑ m ∈ Finset.Icc 1 M, Real.cos ((m:ℝ)*α)) = (∑ m ∈ Finset.Icc 1 M, Real.cos ((m:ℝ)*α))/(M:ℝ) := by ring
  have e2 : (1:ℝ)/((K:ℝ)+1) * (∑ m ∈ Finset.Icc 1 K, Real.cos ((m:ℝ)*α)) = (∑ m ∈ Finset.Icc 1 K, Real.cos ((m:ℝ)*α))/((K:ℝ)+1) := by ring
  rw [e1, e2]
  have hkey : ∀ i : ℕ, (f (i+1) - f i) * (∑ m ∈ Finset.Icc 1 (i+1), Real.cos ((m:ℝ)*α))
      = - ((1/((i:ℝ)+1) - 1/(((i:ℝ)+1)+1)) * (∑ m ∈ Finset.Icc 1 (i+1), Real.cos ((m:ℝ)*α))) := by
    intro i
    simp only [hf]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun i _ => hkey i), Finset.sum_neg_distrib]
  have hfin : (∑ x ∈ Finset.Ico K (M-1),
        (1 / (↑x + 1) - 1 / (↑x + 1 + 1)) * ∑ m ∈ Finset.Icc 1 (x + 1), Real.cos (↑m * α))
      = ∑ j ∈ Finset.Ico (K+1) M, (1/↑j - 1/(↑j+1)) * ∑ m ∈ Finset.Icc 1 j, Real.cos (↑m * α) := by
    rw [show (∑ x ∈ Finset.Ico K (M-1), (1 / (↑x + 1) - 1 / (↑x + 1 + 1)) * ∑ m ∈ Finset.Icc 1 (x + 1), Real.cos (↑m * α))
        = ∑ x ∈ Finset.Ico K (M-1), (fun j : ℕ => (1/(j:ℝ) - 1/((j:ℝ)+1)) * (∑ m ∈ Finset.Icc 1 j, Real.cos ((m:ℝ)*α))) (x+1) from by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      push_cast
      ring]
    rw [Finset.sum_Ico_add' (fun j : ℕ => (1/(j:ℝ) - 1/((j:ℝ)+1)) * (∑ m ∈ Finset.Icc 1 j, Real.cos ((m:ℝ)*α))) K (M-1) 1,
      Nat.sub_add_cancel hM1]
  rw [hfin]
  ring

/-- **The tail bound** `|∑_{K<n≤M} cos(nα)/n| ≤ 4/(K |sin(α/2)|)` for `K ≥ 1`, `M > K`. -/
lemma abel_bound (α : ℝ) (hs : Real.sin (α / 2) ≠ 0) (K M : ℕ) (hK : 1 ≤ K) (hKM : K < M) :
    |∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1)|
      ≤ 4 / ((K:ℝ) * |Real.sin (α / 2)|) := by
  set C : ℝ := 1 / |Real.sin (α / 2)| with hCdef
  have hsinpos : 0 < |Real.sin (α / 2)| := abs_pos.mpr hs
  have hS : ∀ n : ℕ, |∑ m ∈ Finset.Icc 1 n, Real.cos ((m:ℝ)*α)| ≤ C := by
    intro n; rw [hCdef]; exact abs_sum_cos_Icc_le α hs n
  have hKpos : (0:ℝ) < (K:ℝ) := by
    have h : 0 < K := by omega
    exact_mod_cast h
  have hMpos : (0:ℝ) < (M:ℝ) := by
    have h : 0 < M := by omega
    exact_mod_cast h
  have hb : ∀ j : ℕ, 1 ≤ j → (0:ℝ) ≤ 1/(j:ℝ) - 1/((j:ℝ)+1) := by
    intro j hj
    have hjpos : (0:ℝ) < (j:ℝ) := by
      have h : 0 < j := by omega
      exact_mod_cast h
    have hle : (j:ℝ) ≤ (j:ℝ)+1 := by linarith
    have hh := one_div_le_one_div_of_le hjpos hle
    linarith
  have hsum_b : ∑ j ∈ Finset.Ico (K+1) M, (1/(j:ℝ) - 1/((j:ℝ)+1)) = 1/((K:ℝ)+1) - 1/(M:ℝ) := by
    have h := Finset.sum_Ico_sub (fun j : ℕ => 1/(j:ℝ)) (show K+1 ≤ M by omega)
    have h2 : ∑ j ∈ Finset.Ico (K+1) M, (1/(j:ℝ) - 1/((j:ℝ)+1))
        = - ∑ j ∈ Finset.Ico (K+1) M, (1/((j:ℝ)+1) - 1/(j:ℝ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun j _ => by ring)
    rw [h2]
    have hc : ∑ j ∈ Finset.Ico (K+1) M, (1/((j:ℝ)+1) - 1/(j:ℝ))
        = ∑ j ∈ Finset.Ico (K+1) M, (1/(((j+1 : ℕ) : ℝ)) - 1/(j:ℝ)) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast
      ring
    rw [hc, h]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [abel_identity α K M hKM]
  set SM := (∑ m ∈ Finset.Icc 1 M, Real.cos ((m:ℝ)*α)) / (M:ℝ) with hSMdef
  set SK := (∑ m ∈ Finset.Icc 1 K, Real.cos ((m:ℝ)*α)) / ((K:ℝ)+1) with hSKdef
  set T := ∑ j ∈ Finset.Ico (K+1) M, (1/(j:ℝ) - 1/((j:ℝ)+1)) * (∑ m ∈ Finset.Icc 1 j, Real.cos ((m:ℝ)*α)) with hTdef
  have hSM : |SM| ≤ C / (M:ℝ) := by
    rw [hSMdef, abs_div, abs_of_pos hMpos]
    exact div_le_div_of_nonneg_right (hS M) (le_of_lt hMpos)
  have hSK : |SK| ≤ C / ((K:ℝ)+1) := by
    rw [hSKdef, abs_div, abs_of_pos (by positivity : (0:ℝ) < (K:ℝ)+1)]
    exact div_le_div_of_nonneg_right (hS K) (by positivity)
  have hT : |T| ≤ C * (1/((K:ℝ)+1) - 1/(M:ℝ)) := by
    rw [hTdef]
    calc |∑ j ∈ Finset.Ico (K+1) M, (1/(j:ℝ) - 1/((j:ℝ)+1)) * (∑ m ∈ Finset.Icc 1 j, Real.cos ((m:ℝ)*α))|
        ≤ ∑ j ∈ Finset.Ico (K+1) M, |(1/(j:ℝ) - 1/((j:ℝ)+1)) * (∑ m ∈ Finset.Icc 1 j, Real.cos ((m:ℝ)*α))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Finset.Ico (K+1) M, (1/(j:ℝ) - 1/((j:ℝ)+1)) * |∑ m ∈ Finset.Icc 1 j, Real.cos ((m:ℝ)*α)| := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [abs_mul, abs_of_nonneg (hb j (by have hh := (Finset.mem_Ico.mp hj).1; omega))]
      _ ≤ ∑ j ∈ Finset.Ico (K+1) M, (1/(j:ℝ) - 1/((j:ℝ)+1)) * C :=
          Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hS j) (hb j (by have hh := (Finset.mem_Ico.mp hj).1; omega)))
      _ = C * (1/((K:ℝ)+1) - 1/(M:ℝ)) := by
          rw [← Finset.sum_mul, hsum_b]; ring
  have htri : |SM - SK + T| ≤ |SM| + |SK| + |T| := by
    have h2 : |SM + -SK| ≤ |SM| + |SK| := by
      have := abs_add_le SM (-SK); simpa using this
    have h1 : |(SM + -SK) + T| ≤ |SM + -SK| + |T| := abs_add_le _ _
    rw [sub_eq_add_neg]
    linarith
  calc |SM - SK + T| ≤ |SM| + |SK| + |T| := htri
    _ ≤ C / (M:ℝ) + C / ((K:ℝ)+1) + C * (1/((K:ℝ)+1) - 1/(M:ℝ)) := by linarith [hSM, hSK, hT]
    _ = 2 * C / ((K:ℝ)+1) := by field_simp; ring
    _ ≤ 4 / ((K:ℝ) * |Real.sin (α / 2)|) := by
        rw [hCdef, one_div]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        field_simp
        nlinarith [hKpos]

/-! ## Lower bound for `Q` and smallness of `∫₀¹ P α M` -/

/-- On `[0,1]` the denominator `Q α ·` is bounded below by `min(1/4, 2 sin²(α/2)) > 0`. -/
lemma Q_ge_min (α : ℝ) (hs : Real.sin (α/2) ≠ 0) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    min (1/4) (2 * Real.sin (α/2)^2) ≤ Q α x := by
  rw [Q_eq]
  have hs2 : 0 < 2 * Real.sin (α/2)^2 := by
    have := sq_pos_of_ne_zero hs; linarith
  rcases le_total x (1/2) with hx2 | hx2
  · calc min (1/4) (2 * Real.sin (α/2)^2) ≤ 1/4 := min_le_left _ _
      _ ≤ (1 - x)^2 := by nlinarith
      _ ≤ (1 - x)^2 + 4*x*Real.sin (α/2)^2 := by nlinarith [hx.1, hs2]
  · calc min (1/4) (2 * Real.sin (α/2)^2) ≤ 2 * Real.sin (α/2)^2 := min_le_right _ _
      _ ≤ 4*x*Real.sin (α/2)^2 := by nlinarith [hx2, hs2]
      _ ≤ (1 - x)^2 + 4*x*Real.sin (α/2)^2 := by nlinarith [sq_nonneg (1-x)]

/-- Pointwise bound `|P α n x| ≤ 2 x^n / min(1/4, 2 sin²(α/2))` on `[0,1]`. -/
lemma abs_P_le (α : ℝ) (hs : Real.sin (α/2) ≠ 0) (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    |P α n x| ≤ 2 * x^n / min (1/4) (2 * Real.sin (α/2)^2) := by
  have hQpos : 0 < Q α x := Q_pos α x hs hx.1 hx.2
  have hd : min (1/4) (2 * Real.sin (α/2)^2) ≤ Q α x := Q_ge_min α hs x hx
  have hdpos : 0 < min (1/4) (2 * Real.sin (α/2)^2) := by
    apply lt_min (by norm_num)
    have := sq_pos_of_ne_zero hs; linarith
  have hx0 : 0 ≤ x := hx.1
  have hnp : 0 ≤ x^n := pow_nonneg hx0 n
  have hnum : |Real.cos (((n:ℝ)+1)*α) - x*Real.cos ((n:ℝ)*α)| ≤ 2 := by
    have h1 : |Real.cos (((n:ℝ)+1)*α)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : |x*Real.cos ((n:ℝ)*α)| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg hx0]
      nlinarith [Real.abs_cos_le_one ((n:ℝ)*α), hx.2, abs_nonneg (Real.cos ((n:ℝ)*α))]
    have h3 : |Real.cos (((n:ℝ)+1)*α) - x*Real.cos ((n:ℝ)*α)|
        ≤ |Real.cos (((n:ℝ)+1)*α)| + |x*Real.cos ((n:ℝ)*α)| := by
      rw [sub_eq_add_neg]
      have := abs_add_le (Real.cos (((n:ℝ)+1)*α)) (-(x*Real.cos ((n:ℝ)*α)))
      simpa using this
    linarith
  rw [P, abs_div, abs_of_pos hQpos, abs_mul, abs_of_nonneg hnp]
  calc x^n * |Real.cos (((n:ℝ)+1)*α) - x*Real.cos ((n:ℝ)*α)| / Q α x
      ≤ x^n * 2 / Q α x := div_le_div_of_nonneg_right (by nlinarith) (le_of_lt hQpos)
    _ ≤ x^n * 2 / min (1/4) (2 * Real.sin (α/2)^2) :=
        div_le_div_of_nonneg_left (mul_nonneg hnp (by norm_num)) hdpos hd
    _ = 2 * x^n / min (1/4) (2 * Real.sin (α/2)^2) := by ring

/-- `P α n` is continuous on `[0,1]` (where `Q α · > 0`). -/
lemma continuousOn_P (α : ℝ) (hs : Real.sin (α/2) ≠ 0) (n : ℕ) :
    ContinuousOn (fun x => P α n x) (Set.uIcc (0:ℝ) 1) := by
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hQ : ∀ x ∈ Set.Icc (0:ℝ) 1, Q α x ≠ 0 := fun x hx => Q_ne_zero α x hs hx.1 hx.2
  simp only [P, Q]
  refine ContinuousOn.div ?_ ?_ hQ
  · fun_prop
  · fun_prop

/-- `|∫₀¹ P α M| ≤ 2/(min(1/4, 2 sin²(α/2)) (M+1))`, hence tends to `0`. -/
lemma integral_P_bound (α : ℝ) (hs : Real.sin (α/2) ≠ 0) (M : ℕ) :
    |∫ x in (0:ℝ)..1, P α M x| ≤ 2 / (min (1/4) (2*Real.sin (α/2)^2) * ((M:ℝ)+1)) := by
  set d := min (1/4) (2 * Real.sin (α/2)^2) with hddef
  have hdpos : 0 < d := by
    rw [hddef]
    apply lt_min (by norm_num)
    have := sq_pos_of_ne_zero hs; linarith
  have hb : ∀ x ∈ Set.Icc (0:ℝ) 1, |P α M x| ≤ 2 * x^M / d := by
    intro x hx; rw [hddef]; exact abs_P_le α hs M x hx
  have hPcont : ContinuousOn (fun x => P α M x) (Set.uIcc (0:ℝ) 1) := continuousOn_P α hs M
  have hIa : IntervalIntegrable (fun x => |P α M x|) volume 0 1 := hPcont.abs.intervalIntegrable
  have hIg : IntervalIntegrable (fun x => 2 * x^M / d) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have h1 : |∫ x in (0:ℝ)..1, P α M x| ≤ ∫ x in (0:ℝ)..1, |P α M x| := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (f := fun x => P α M x) (by norm_num : (0:ℝ) ≤ 1)
  have h2 : ∫ x in (0:ℝ)..1, |P α M x| ≤ ∫ x in (0:ℝ)..1, 2 * x^M / d :=
    intervalIntegral.integral_mono_on (by norm_num) hIa hIg hb
  have h3 : ∫ x in (0:ℝ)..1, 2 * x^M / d = 2 / (d * ((M:ℝ)+1)) := by
    rw [show (∫ x in (0:ℝ)..1, 2 * x^M / d) = ∫ x in (0:ℝ)..1, (2/d) * x^M from
          intervalIntegral.integral_congr (fun x _ => by ring)]
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero M), sub_zero]
    field_simp
  linarith [h1, h2, h3]

/-! ## The integral of the telescoping identity -/

/-- Integrating `P α K - P α M = ∑_{K<n≤M} x^{n-1} cos(nα)` over `[0,1]`. -/
lemma integral_P_diff (α : ℝ) (hs : Real.sin (α/2) ≠ 0) (K M : ℕ) (hKM : K ≤ M) :
    (∫ x in (0:ℝ)..1, P α K x) - (∫ x in (0:ℝ)..1, P α M x)
      = ∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1) := by
  have hpt : ∀ x ∈ Set.uIcc (0:ℝ) 1, P α K x - P α M x
      = ∑ n ∈ Finset.Ico K M, x^n * Real.cos (((n:ℝ)+1)*α) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    have hQ : Q α x ≠ 0 := Q_ne_zero α x hs hx.1 hx.2
    have htel := Finset.sum_Ico_sub (fun n => P α n x) hKM
    have htel' : ∑ i ∈ Finset.Ico K M, (-(x^i * Real.cos (((i:ℝ)+1)*α))) = P α M x - P α K x := by
      rw [← htel]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [P_succ_sub α x i hQ]
      ring
    have h2 : ∑ i ∈ Finset.Ico K M, (x^i * Real.cos (((i:ℝ)+1)*α)) = P α K x - P α M x := by
      have := Finset.sum_neg_distrib (f := fun i => x^i * Real.cos (((i:ℝ)+1)*α)) (s := Finset.Ico K M)
      linarith [htel']
    exact h2.symm
  have hIK : IntervalIntegrable (fun x => P α K x) volume 0 1 := (continuousOn_P α hs K).intervalIntegrable
  have hIM : IntervalIntegrable (fun x => P α M x) volume 0 1 := (continuousOn_P α hs M).intervalIntegrable
  rw [← intervalIntegral.integral_sub hIK hIM, intervalIntegral.integral_congr hpt]
  have hswap := intervalIntegral.integral_finsetSum (μ := volume) (a := (0:ℝ)) (b := 1)
      (s := Finset.Ico K M) (f := fun n x => x^n * Real.cos (((n:ℝ)+1)*α))
      (fun n _ => Continuous.intervalIntegrable
        (show Continuous (fun x : ℝ => x^n * Real.cos (((n:ℝ)+1)*α)) by fun_prop) 0 1)
  rw [hswap]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
  ring

/-! ## The main estimate -/

theorem abs_integral_P_le (α : ℝ) (K : ℕ) (hK : 1 ≤ K) (hs : Real.sin (α / 2) ≠ 0) :
    |∫ x in (0:ℝ)..1, P α K x| ≤ 4 / ((K : ℝ) * |Real.sin (α / 2)|) := by
  set d := min (1/4) (2 * Real.sin (α/2)^2) with hddef
  have hdpos : 0 < d := by
    rw [hddef]
    apply lt_min (by norm_num)
    have := sq_pos_of_ne_zero hs; linarith
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨M, hM⟩ := exists_nat_gt (max (K:ℝ) (2/(d*ε)))
  have hMK : K < M := by
    have h : (K:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_left _ _) hM
    exact_mod_cast h
  have hbig : 2/(d*((M:ℝ)+1)) ≤ ε := by
    have h2 : 2/(d*ε) < (M:ℝ) := lt_of_le_of_lt (le_max_right _ _) hM
    have hde : 0 < d * ε := mul_pos hdpos hε
    rw [div_lt_iff₀ hde] at h2
    rw [div_le_iff₀ (by positivity : 0 < d * ((M:ℝ)+1))]
    nlinarith [h2, (by positivity : (0:ℝ) ≤ (M:ℝ))]
  have hid := integral_P_diff α hs K M (le_of_lt hMK)
  have hbnd := abel_bound α hs K M hK hMK
  have hint : |∫ x in (0:ℝ)..1, P α M x| ≤ 2/(d*((M:ℝ)+1)) := by
    rw [hddef]; exact integral_P_bound α hs M
  have hEq : ∫ x in (0:ℝ)..1, P α K x
      = (∫ x in (0:ℝ)..1, P α M x) + ∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1) := by
    linarith [hid]
  calc |∫ x in (0:ℝ)..1, P α K x|
      = |(∫ x in (0:ℝ)..1, P α M x) + ∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1)| := by rw [hEq]
    _ ≤ |∫ x in (0:ℝ)..1, P α M x| + |∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1)| :=
        abs_add_le (∫ x in (0:ℝ)..1, P α M x)
          (∑ n ∈ Finset.Ico K M, Real.cos (((n:ℝ)+1)*α) / ((n:ℝ)+1))
    _ ≤ 2/(d*((M:ℝ)+1)) + 4/((K:ℝ) * |Real.sin (α / 2)|) := add_le_add hint hbnd
    _ ≤ ε + 4/((K:ℝ) * |Real.sin (α / 2)|) := by linarith
    _ = 4/((K:ℝ) * |Real.sin (α / 2)|) + ε := by ring

end

end Work.FIArea7
