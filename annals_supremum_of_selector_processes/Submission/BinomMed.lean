import Mathlib.Probability.Distributions.SetBernoulli
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
open scoped BigOperators Real
open Finset MeasureTheory intervalIntegral

namespace Submission.BinomMed

/-- derivative of `log (a + b·t)` at x -/
lemma deriv_log_affine {a b x : ℝ} (h : 0 < a + b * x) :
    deriv (fun t : ℝ => Real.log (a + b * t)) x = b * (a + b * x)⁻¹ := by
  rw [show (fun t : ℝ => Real.log (a + b * t)) = Real.log ∘ (fun t : ℝ => a + b * t) by rfl]
  rw [deriv_comp]
  · rw [Real.deriv_log']
    have hb : deriv (fun t : ℝ => a + b * t) x = b := by simp
    rw [hb]
    ring
  · exact Real.differentiableAt_log (ne_of_gt h)
  · fun_prop

/-- the mass density `x^(N-1) (1-x)^(n-N)` -/
noncomputable def mass (n N : ℕ) (x : ℝ) : ℝ := x ^ (N - 1) * (1 - x) ^ (n - N)

lemma continuous_mass (n N : ℕ) : Continuous (mass n N) := by
  unfold mass
  exact (continuous_id.pow _).mul (continuous_const.sub continuous_id |>.pow _)

lemma integrable_mass (n N : ℕ) (a b : ℝ) :
    IntervalIntegrable (mass n N) volume a b :=
  (continuous_mass n N).intervalIntegrable a b

lemma mass_nonneg (n N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ mass n N x := by
  unfold mass
  exact mul_nonneg (pow_nonneg hx0 _) (pow_nonneg (by nlinarith) _)

lemma integral_ge_of_ge_zero (n N : ℕ) {p q : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) :
    ∫ x in (0 : ℝ)..q, mass n N x ≤ ∫ x in (0 : ℝ)..p, mass n N x := by
  have hsplit : ∫ x in (0 : ℝ)..p, mass n N x =
      (∫ x in (0 : ℝ)..q, mass n N x) + ∫ x in q..p, mass n N x := by
    exact (integral_add_adjacent_intervals (integrable_mass n N 0 q)
      (integrable_mass n N q p)).symm
  rw [hsplit]
  exact le_add_of_nonneg_right (by
    refine integral_nonneg hqp ?_
    intro u hu
    exact mass_nonneg n N (by exact le_trans hq0 hu.1) (by exact le_trans hu.2 hp1))

/-! ## Mode-side reflection lemma
For `2 ≤ a ≤ b`, let `m := (a-1)/(a+b-2)` (the mode of `x^(a-1)(1-x)^(b-1)` on [0,1]).
Then `∫₀^m ≤ (1/2)∫₀^1`.  Equivalent: the density is bigger on `[m,1]` than on `[0,m]`,
which follows from `f(2m-x) ≥ f(x)` on `x∈[0,m]` (2m ≤ 1). -/

/-! ### Generic: the mode log-ratio function and its derivative -/

/-- mode log ratio: log of `(2m-x)^c(1-2m+x)^d / (x^c(1-x)^d)` -/
noncomputable def modeL (c d : ℕ) (m : ℝ) (t : ℝ) : ℝ :=
  (c:ℝ) * Real.log (2*m - t) - (c:ℝ) * Real.log t
    + (d:ℝ) * Real.log (1 - 2*m + t) - (d:ℝ) * Real.log (1 - t)

/-- derivative of `modeL c d m` at `t` (valid where all arguments positive) -/
noncomputable def modeLderiv (c d : ℕ) (m : ℝ) (t : ℝ) : ℝ :=
  -(c:ℝ) * (2*m - t)⁻¹ - (c:ℝ) * t⁻¹ + (d:ℝ) * (1 - 2*m + t)⁻¹ + (d:ℝ) * (1 - t)⁻¹

/-- `modeL` has the expected derivative -/
lemma modeL_hasDerivAt {c d : ℕ} {m t : ℝ}
    (h2 : 0 < 2*m - t) (ht0 : 0 < t) (hC : 0 < 1 - 2*m + t) (hD : 0 < 1 - t) :
    HasDerivAt (modeL c d m) (modeLderiv c d m t) t := by
  unfold modeL modeLderiv
  have hA : HasDerivAt (fun t : ℝ => Real.log (2*m - t)) (-(2*m - t)⁻¹) t := by
    have hinner : HasDerivAt (fun t : ℝ => 2*m - t) (-1) t := by
      exact HasDerivAt.const_sub (2*m) (hasDerivAt_id t)
    have hlog : HasDerivAt (fun y : ℝ => Real.log y) ((2*m - t)⁻¹) (2*m - t) := by
      simpa using Real.hasDerivAt_log (by linarith : 2*m - t ≠ 0)
    convert hlog.comp t hinner using 1 <;> try rfl
    ring_nf
  have hB : HasDerivAt (fun t : ℝ => Real.log t) (t⁻¹) t := by
    simpa using Real.hasDerivAt_log (by linarith : t ≠ 0)
  have hC' : HasDerivAt (fun t : ℝ => Real.log (1 - 2*m + t)) ((1 - 2*m + t)⁻¹) t := by
    have hinner : HasDerivAt (fun t : ℝ => (1 - 2*m) + t) 1 t := by
      simpa [add_comm, add_left_comm, add_assoc] using (hasDerivAt_id t).const_add (1 - 2*m)
    have hlog : HasDerivAt (fun y : ℝ => Real.log y) ((1 - 2*m + t)⁻¹) (1 - 2*m + t) := by
      simpa using Real.hasDerivAt_log (by linarith : 1 - 2*m + t ≠ 0)
    convert hlog.comp t hinner using 1 <;> try rfl
    ring_nf
  have hD : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - t)⁻¹) t := by
    have hinner : HasDerivAt (fun t : ℝ => (1:ℝ) - t) (-1) t := by
      exact HasDerivAt.const_sub (1:ℝ) (hasDerivAt_id t)
    have hlog : HasDerivAt (fun y : ℝ => Real.log y) ((1 - t)⁻¹) (1 - t) := by
      simpa using Real.hasDerivAt_log (by linarith : 1 - t ≠ 0)
    convert hlog.comp t hinner using 1 <;> try rfl
    ring_nf
  convert (((hA.const_mul (c:ℝ)).sub (hB.const_mul (c:ℝ))).add
      ((hC'.const_mul (d:ℝ)).sub (hD.const_mul (d:ℝ)))) using 1 <;> try rfl
  · funext t; simp [Pi.sub_apply, Pi.add_apply]; ring
  · ring

/-- derivative of the mode log-ratio ≤ 0 on (0,m) when `m = c/(c+d)`, `1 ≤ c ≤ d` -/
lemma modeLderiv_nonpos {c d : ℕ} (hc : (1:ℕ) ≤ c) (hcd : c ≤ d)
    {m t : ℝ} (hm : m = (c:ℝ)/((c:ℝ)+(d:ℝ)))
    (ht0 : 0 < t) (htm : t < m) :
    modeLderiv c d m t ≤ 0 := by
  have hcdR : (c:ℝ) ≤ (d:ℝ) := by exact_mod_cast hcd
  have hcR : (0:ℝ) < c := by exact_mod_cast (Nat.succ_le_iff.mp hc)
  have hden : 0 < (c:ℝ) + (d:ℝ) := by positivity
  have hmpos : 0 < m := by rw [hm]; positivity
  have hm12 : m ≤ (1:ℝ)/2 := by
    rw [hm, div_le_iff₀ hden]
    nlinarith
  have hAarg : 0 < 2*m - t := by nlinarith
  have hCarg : 0 < 1 - 2*m + t := by nlinarith
  have hDarg : 0 < 1 - t := by nlinarith
  have hId : (c:ℝ) * m * (1 - 2*m + t) * (1 - t) - (d:ℝ) * (1 - m) * t * (2*m - t)
      = ((c:ℝ) + (d:ℝ)) * (1 - 2*m) * (m - t)^2 := by
    rw [hm]
    field_simp
    ring
  have hmain : (d:ℝ) * (1 - m) * t * (2*m - t) ≤ (c:ℝ) * m * (1 - 2*m + t) * (1 - t) := by
    rw [← sub_nonneg]
    rw [hId]
    exact mul_nonneg (mul_nonneg (by positivity : 0 ≤ (c:ℝ) + (d:ℝ)) (by nlinarith : 0 ≤ 1 - 2*m))
      (sq_nonneg (m - t))
  unfold modeLderiv
  -- reduce to hmain via algebra:
  have hA1 : (2*m - t) ≠ 0 := by linarith
  have hA2 : t ≠ 0 := by linarith
  have hA3 : (1 - 2*m + t) ≠ 0 := by linarith
  have hA4 : (1 - t) ≠ 0 := by linarith
  have hposA : 0 < (1 - 2*m + t) * (1 - t) := by positivity
  have hposB : 0 < t * (2*m - t) := by positivity
  -- divide hmain by the positive products: A := (1-2m+t)(1-t), B := t(2m-t)
  -- hmain: d(1-m)·B ≤ c·m·A ; multiply by 2 and use A,B to make the claim
  have h2main : (d:ℝ) * (2 - 2*m) * (t * (2*m - t)) ≤ (c:ℝ) * (2*m) * ((1 - 2*m + t) * (1 - t)) := by
    nlinarith [hmain]
  have hcl : (d:ℝ) * (2 - 2*m) / ((1 - 2*m + t) * (1 - t)) ≤
      (c:ℝ) * (2*m) / (t * (2*m - t)) := by
    rw [div_le_div_iff₀ hposA hposB]
    exact h2main
  -- rewrite the target with divisions and combine reciprocal pairs
  have hsum1 : (c:ℝ) * (2*m - t)⁻¹ + (c:ℝ) * t⁻¹ = (c:ℝ) * (2*m) * (t * (2*m - t))⁻¹ := by
    field_simp [hA1, hA2]
    ring
  have hsum2 : (d:ℝ) * (1 - 2*m + t)⁻¹ + (d:ℝ) * (1 - t)⁻¹ =
      (d:ℝ) * (2 - 2*m) * ((1 - 2*m + t) * (1 - t))⁻¹ := by
    field_simp [hA3, hA4]
    ring
  calc
    (-(c:ℝ) * (2*m - t)⁻¹ - (c:ℝ) * t⁻¹ + (d:ℝ) * (1 - 2*m + t)⁻¹ + (d:ℝ) * (1 - t)⁻¹)
        = -((c:ℝ) * (2*m - t)⁻¹ + (c:ℝ) * t⁻¹) + ((d:ℝ) * (1 - 2*m + t)⁻¹ + (d:ℝ) * (1 - t)⁻¹) := by ring
    _ = -(c:ℝ) * (2*m) * (t * (2*m - t))⁻¹ + (d:ℝ) * (2 - 2*m) * ((1 - 2*m + t) * (1 - t))⁻¹ := by
      rw [hsum1, hsum2]
      ring
    _ ≤ 0 := by
      -- d(2-2m)·A⁻¹ ≤ c·2m·B⁻¹ from hcl; express as divisions:
      have hxeq : -(c:ℝ) * (2*m) * (t * (2*m - t))⁻¹ + (d:ℝ) * (2 - 2*m) * ((1 - 2*m + t) * (1 - t))⁻¹ =
          -((c:ℝ) * (2*m) / (t * (2*m - t))) + ((d:ℝ) * (2 - 2*m) / ((1 - 2*m + t) * (1 - t))) := by
        field_simp [hA2, hA1, hA3, hA4]
      rw [hxeq]
      linarith [hcl]

/-- continuity of `fun t => Real.log (A + B*t)` where `A + B*t ≠ 0` on a set -/
lemma continuousOn_log_affine {A B : ℝ} {s : Set ℝ}
    (hpos : ∀ t ∈ s, A + B * t ≠ 0) : ContinuousOn (fun t : ℝ => Real.log (A + B * t)) s := by
  refine ContinuousOn.log ?_ ?_
  · -- affine continuous
    exact (continuousOn_const.add (continuousOn_id.const_mul B))
  · intro t ht
    exact hpos t ht

/-- continuity of the mode log-ratio on (0,m] -/
lemma modeL_continuousOn {c d : ℕ} {m : ℝ} (hm0 : 0 < m) (hm12 : m ≤ (1:ℝ)/2) :
    ContinuousOn (modeL c d m) (Set.Ioc 0 m) := by
  unfold modeL
  have hA : ContinuousOn (fun t : ℝ => (c:ℝ) * Real.log (2*m - t)) (Set.Ioc 0 m) := by
    simpa [sub_eq_add_neg, mul_neg, add_comm, add_left_comm, add_assoc] using
      ((continuousOn_log_affine (A := 2*m) (B := -1) (s := Set.Ioc 0 m)) (by
        intro t ht
        exact ne_of_gt (by nlinarith [hm0, ht.2]))).const_mul (c:ℝ)
  have hB : ContinuousOn (fun t : ℝ => (c:ℝ) * Real.log t) (Set.Ioc 0 m) := by
    simpa [one_mul, zero_add] using
      ((continuousOn_log_affine (A := 0) (B := 1) (s := Set.Ioc 0 m)) (by
        intro t ht
        have hpos : 0 < 0 + 1 * t := by simpa [one_mul] using ht.1
        exact ne_of_gt hpos)).const_mul (c:ℝ)
  have hC : ContinuousOn (fun t : ℝ => (d:ℝ) * Real.log (1 - 2*m + t)) (Set.Ioc 0 m) := by
    simpa [one_mul, add_comm, add_left_comm, add_assoc] using
      ((continuousOn_log_affine (A := 1 - 2*m) (B := 1) (s := Set.Ioc 0 m)) (by
        intro t ht
        exact ne_of_gt (by nlinarith [ht.1, hm12]))).const_mul (d:ℝ)
  have hD : ContinuousOn (fun t : ℝ => (d:ℝ) * Real.log (1 - t)) (Set.Ioc 0 m) := by
    simpa [sub_eq_add_neg, mul_neg, add_comm, add_left_comm, add_assoc] using
      ((continuousOn_log_affine (A := 1) (B := -1) (s := Set.Ioc 0 m)) (by
        intro t ht
        exact ne_of_gt (by nlinarith [ht.2, hm12]))).const_mul (d:ℝ)
  convert ((hA.sub hB).add (hC.sub hD)) using 1 <;> try rfl
  funext t
  simp [Pi.sub_apply, Pi.add_apply]
  ring

lemma modeL_antitone {c d : ℕ} (hc : (1:ℕ) ≤ c) (hcd : c ≤ d)
    {m : ℝ} (hm : m = (c:ℝ)/((c:ℝ)+(d:ℝ))) :
    AntitoneOn (modeL c d m) (Set.Ioc 0 m) := by
  have hden : 0 < (c:ℝ) + (d:ℝ) := by positivity
  have hcdR : (c:ℝ) ≤ (d:ℝ) := by exact_mod_cast hcd
  have hm0 : 0 < m := by rw [hm]; positivity
  have hm12 : m ≤ (1:ℝ)/2 := by
    rw [hm, div_le_iff₀ hden]
    nlinarith
  apply antitoneOn_of_deriv_nonpos
  · exact convex_Ioc 0 m
  · -- continuity on (0,m]
    exact modeL_continuousOn hm0 hm12
  · -- differentiability on interior (0,m)
    intro t ht
    have ht' : t ∈ Set.Ioo 0 m := by simpa [interior_Ioc] using ht
    have ht0 : 0 < t := ht'.1
    have htm : t < m := ht'.2
    have h2 : 0 < 2*m - t := by nlinarith
    have hC : 0 < 1 - 2*m + t := by nlinarith
    have hD : 0 < 1 - t := by nlinarith [hm12]
    exact (modeL_hasDerivAt h2 ht0 hC hD).differentiableAt.differentiableWithinAt
  · -- deriv ≤ 0 on interior (0,m)
    intro t ht
    have ht' : t ∈ Set.Ioo 0 m := by simpa [interior_Ioc] using ht
    have hpos : 0 < t := ht'.1
    have htm : t < m := ht'.2
    have hder : deriv (modeL c d m) t = modeLderiv c d m t := by
      have h2 : 0 < 2*m - t := by nlinarith
      have hC : 0 < 1 - 2*m + t := by nlinarith
      have hD : 0 < 1 - t := by nlinarith [hm12]
      exact (modeL_hasDerivAt h2 hpos hC hD).deriv
    rw [hder]
    exact modeLderiv_nonpos hc hcd hm hpos htm

/-- `modeL` is nonnegative on (0,m]: `m = c/(c+d)`, `1 ≤ c ≤ d` -/
lemma modeL_nonneg {c d : ℕ} (hc : (1:ℕ) ≤ c) (hcd : c ≤ d)
    {m x : ℝ} (hm : m = (c:ℝ)/((c:ℝ)+(d:ℝ)))
    (hx0 : 0 < x) (hxm : x ≤ m) :
    0 ≤ modeL c d m x := by
  have hden : 0 < (c:ℝ) + (d:ℝ) := by positivity
  have hm0 : 0 < m := by rw [hm]; positivity
  have hmem : x ∈ Set.Ioc 0 m := ⟨hx0, hxm⟩
  have hmemm : m ∈ Set.Ioc 0 m := ⟨hm0, le_rfl⟩
  have hant := modeL_antitone hc hcd hm
  have hle : modeL c d m m ≤ modeL c d m x := hant hmem hmemm hxm
  have hLm : modeL c d m m = 0 := by
    unfold modeL
    rw [show 2*m - m = m by ring]
    rw [show 1 - 2*m + m = 1 - m by ring]
    ring
  rw [hLm] at hle
  exact hle

lemma mode_pointwise {c d : ℕ} (hc : (1:ℕ) ≤ c) (hcd : c ≤ d)
    {m x : ℝ} (hm : m = (c:ℝ)/((c:ℝ)+(d:ℝ)))
    (hx0 : 0 ≤ x) (hxm : x ≤ m) :
    x ^ c * (1 - x) ^ d ≤ (2*m - x) ^ c * (1 - 2*m + x) ^ d := by
  have hcdR : (c:ℝ) ≤ (d:ℝ) := by exact_mod_cast hcd
  have hcR : (0:ℝ) < c := by exact_mod_cast (Nat.succ_le_iff.mp hc)
  have hden : 0 < (c:ℝ) + (d:ℝ) := by positivity
  have hmpos : 0 < m := by rw [hm]; positivity
  have hm12 : m ≤ (1:ℝ)/2 := by
    rw [hm, div_le_iff₀ hden]
    nlinarith
  -- first handle x = 0
  by_cases hx0' : x = 0
  · subst x
    -- 0^c·1^d = 0 ≤ (2m)^c(1-2m)^d
    have hnon : 0 ≤ 1 - 2*m := by nlinarith
    have h1 : 0 ≤ (2*m) ^ c * (1 - 2*m) ^ d := by
      exact mul_nonneg (pow_nonneg (by nlinarith) _) (pow_nonneg hnon _)
    -- LHS: 0^c · 1^d with c ≥ 1 gives 0
    have hc1 : 1 ≤ c := hc
    rw [zero_pow (by omega : c ≠ 0)]
    simp
    exact h1
  · -- 0 < x ≤ m
    have hxpos : 0 < x := lt_of_le_of_ne hx0 (by exact Ne.symm hx0')
    by_cases hxm' : x = m
    · subst x
      rw [show 2*m - m = m by ring]
      rw [show 1 - 2*m + m = 1 - m by ring]
    · -- 0 < x < m : use the log-antitone
      have hxm'' : x < m := lt_of_le_of_ne hxm hxm'
      have hxpos' : 0 < x := hxpos
      have harg1 : 0 < 2*m - x := by nlinarith
      have harg2 : 0 < x := hxpos
      have harg3 : 0 < 1 - 2*m + x := by
        have hm12' : m ≤ (1:ℝ)/2 := hm12
        nlinarith
      have harg4 : 0 < 1 - x := by nlinarith
      have hL0 : 0 ≤ modeL c d m x := modeL_nonneg hc hcd hm hxpos (le_of_lt hxm'')
      unfold modeL at hL0
      -- bridge: log((2m-x)^c (1-2m+x)^d) ≥ log(x^c (1-x)^d)
      have hlogY : Real.log ((2*m - x) ^ c * (1 - 2*m + x) ^ d)
          = (c:ℝ) * Real.log (2*m - x) + (d:ℝ) * Real.log (1 - 2*m + x) := by
        rw [Real.log_mul (by positivity : (2*m - x)^c ≠ 0) (by positivity : (1 - 2*m + x)^d ≠ 0)]
        rw [Real.log_pow, Real.log_pow]
      have hlogX : Real.log (x ^ c * (1 - x) ^ d)
          = (c:ℝ) * Real.log x + (d:ℝ) * Real.log (1 - x) := by
        rw [Real.log_mul (by positivity : x^c ≠ 0) (by positivity : (1-x)^d ≠ 0)]
        rw [Real.log_pow, Real.log_pow]
      -- from hL0 we have c log(2m-x) - c log x + d log(1-2m+x) - d log(1-x) ≥ 0
      have hmainlog : (c:ℝ) * Real.log (2*m - x) + (d:ℝ) * Real.log (1 - 2*m + x) ≥
          (c:ℝ) * Real.log x + (d:ℝ) * Real.log (1 - x) := by
        nlinarith
      -- express with logs of products
      have hprod : Real.log (x ^ c * (1 - x) ^ d) ≤ Real.log ((2*m - x) ^ c * (1 - 2*m + x) ^ d) := by
        rw [hlogY, hlogX]
        linarith
      -- exponentiate
      have hYpos : 0 < (2*m - x) ^ c * (1 - 2*m + x) ^ d := by positivity
      have hXpos : 0 < x ^ c * (1 - x) ^ d := by positivity
      have hexp := Real.exp_le_exp.mpr hprod
      rw [Real.exp_log hYpos, Real.exp_log hXpos] at hexp
      exact hexp


/-! ### The mode-side integral inequality (median ≥ mode) -/



noncomputable def modeVal (a b : ℕ) : ℝ := (a - 1 : ℝ) / ((a : ℝ) + (b : ℝ) - 2)

/-- `∫₀^m f ≤ (1/2)∫₀^1 f` where `m` is the mode and `f = x^(a-1)(1-x)^(b-1)`,
with `2 ≤ a ≤ b`.  Here `mass (a+b-1) a x = x^(a-1) (1-x)^(b-1)`. -/
lemma half_mass_mode (a b : ℕ) (ha2 : 2 ≤ a) (hab : a ≤ b) :
    (∫ x in (0 : ℝ)..modeVal a b, mass (a + b - 1) a x) ≤
      (1/2 : ℝ) * ∫ x in (0 : ℝ)..1, mass (a + b - 1) a x := by
  let c : ℕ := a - 1
  let d : ℕ := b - 1
  let m : ℝ := (c : ℝ) / ((c : ℝ) + (d : ℝ))
  have hc1 : (1:ℕ) ≤ c := by dsimp [c]; omega
  have hcd : c ≤ d := by dsimp [c, d]; omega
  have hcRpos : (0:ℝ) < c := by exact_mod_cast (Nat.succ_le_iff.mp hc1)
  have hdRpos : (0:ℝ) < d := lt_of_lt_of_le hcRpos (by exact_mod_cast hcd)
  have hdenpos : 0 < (c:ℝ) + (d:ℝ) := by positivity
  have hm0 : 0 < m := by dsimp [m]; positivity
  have hm12 : m ≤ (1:ℝ)/2 := by
    dsimp [m]
    rw [div_le_iff₀ hdenpos]
    have hcdR : (c:ℝ) ≤ (d:ℝ) := by exact_mod_cast hcd
    nlinarith
  have hmass : ∀ x : ℝ, mass (a + b - 1) a x = x ^ c * (1 - x) ^ d := by
    intro x
    unfold mass
    dsimp [c, d]
    have hsub : (a + b - 1) - a = b - 1 := by omega
    rw [hsub]
  have hsub1 (k : ℕ) (hk : 1 ≤ k) : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have hnat : (k - 1 : ℕ) + 1 = k := Nat.sub_add_cancel hk
    have hc : (((k - 1 : ℕ) : ℝ) + 1) = (k : ℝ) := by exact_mod_cast hnat
    linarith
  have hmodes : m = modeVal a b := by
    dsimp [m, modeVal, c, d]
    rw [hsub1 a (by omega), hsub1 b (by omega)]
    ring_nf
  have hpos2m : 0 < 2*m := by nlinarith
  have h2m_le_1 : 2*m ≤ 1 := by nlinarith [hm12]
  -- ∫₀^m f ≤ ∫_m^{2m} f: reflect x ↦ 2m−x and use the pointwise inequality
  have hmono : (∫ x in (0 : ℝ)..m, mass (a + b - 1) a x) ≤
      ∫ x in m..2*m, mass (a + b - 1) a x := by
    have hinteq : ∫ x in m..2*m, mass (a + b - 1) a x =
        ∫ x in (0 : ℝ)..m, mass (a + b - 1) a (2*m - x) := by
      rw [integral_comp_sub_left (fun u : ℝ => mass (a + b - 1) a u) (2*m)]
      congr 1 <;> ring
    rw [hinteq]
    refine integral_mono_on (by linarith) ?_ ?_ ?_
    · exact integrable_mass (a + b - 1) a 0 m
    · exact (((continuous_mass (a + b - 1) a).comp
        (continuous_const.sub continuous_id)).intervalIntegrable 0 m)
    · intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hxm : x ≤ m := hx.2
      have hpw : x ^ c * (1 - x) ^ d ≤ (2*m - x) ^ c * (1 - 2*m + x) ^ d := by
        exact mode_pointwise hc1 hcd (rfl : m = (c:ℝ)/((c:ℝ)+(d:ℝ))) hx0 hxm
      calc
        mass (a + b - 1) a x = x ^ c * (1 - x) ^ d := by rw [hmass]
        _ ≤ (2*m - x) ^ c * (1 - 2*m + x) ^ d := hpw
        _ = mass (a + b - 1) a (2*m - x) := by
          rw [hmass]
          congr 1 <;> ring
  have hhalf : (2:ℝ) * (∫ x in (0 : ℝ)..m, mass (a + b - 1) a x) ≤
      ∫ x in (0 : ℝ)..(2*m), mass (a + b - 1) a x := by
    have hsplit : ∫ x in (0 : ℝ)..(2*m), mass (a + b - 1) a x =
        (∫ x in (0 : ℝ)..m, mass (a + b - 1) a x) +
          ∫ x in m..2*m, mass (a + b - 1) a x := by
      exact (integral_add_adjacent_intervals (integrable_mass (a + b - 1) a 0 m)
        (integrable_mass (a + b - 1) a m (2*m))).symm
    rw [hsplit]
    nlinarith [hmono]
  have h2m0 : 0 ≤ 2*m := by nlinarith
  have hlast : ∫ x in (0 : ℝ)..(2*m), mass (a + b - 1) a x ≤
      ∫ x in (0 : ℝ)..1, mass (a + b - 1) a x := by
    exact integral_ge_of_ge_zero (a + b - 1) a h2m0 h2m_le_1 (by norm_num)
  -- conclude: A ≤ (1/2) B
  have hA : (∫ x in (0 : ℝ)..m, mass (a + b - 1) a x) ≤
      (1/2 : ℝ) * ∫ x in (0 : ℝ)..1, mass (a + b - 1) a x := by
    nlinarith [hhalf, hlast]
  -- rewrite the mode: upper limit m = modeVal a b
  rwa [hmodes] at hA

/-! ## The binomial tail and its incomplete-Beta integral representation -/

/-- `k·C(n,k) = n·C(n-1,k-1)` -/
lemma choose_mul_self (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    n.choose k * k = n * (n - 1).choose (k - 1) := by
  have hn1 : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have hk1 : (k - 1) + 1 = k := Nat.sub_add_cancel hk
  have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  rw [hn1, hk1] at h
  exact h.symm

/-- `(n-k)·C(n,k) = n·C(n-1,k)` -/
lemma choose_mul_sub (n k : ℕ) (hn : 1 ≤ n) :
    n.choose k * (n - k) = n * (n - 1).choose k := by
  have hn1 : (n - 1) + 1 = n := Nat.sub_add_cancel hn
  have h1 := Nat.add_one_mul_choose_eq (n - 1) k
  rw [hn1] at h1
  have h2 := Nat.choose_succ_right_eq n k
  rw [h2] at h1
  exact h1.symm

/-- derivative of one binomial probability term -/
lemma term_hasDerivAt (n k : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k))
      ((n.choose k : ℝ) *
        (((k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k))
          - (((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1)))) x := by
  have hpk : HasDerivAt (fun x : ℝ => x ^ k) ((k : ℝ) * x ^ (k - 1)) x := by
    simpa using (hasDerivAt_pow k x)
  have hpow : HasDerivAt (fun y : ℝ => y ^ (n - k))
      (((n - k : ℕ) : ℝ) * (1 - x) ^ ((n - k) - 1)) (1 - x) := by
    simpa using (hasDerivAt_pow (n - k) (1 - x))
  have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by
    simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
  have h1k : HasDerivAt (fun x : ℝ => (1 - x) ^ (n - k))
      (-(((n - k : ℕ) : ℝ) * (1 - x) ^ (n - k - 1))) x := by
    convert (hpow.comp x h1) using 1 <;> try rfl
    ring
  have hc : HasDerivAt (fun x : ℝ => (n.choose k : ℝ) * x ^ k)
      ((n.choose k : ℝ) * ((k : ℝ) * x ^ (k - 1))) x := by
    simpa [mul_assoc] using (hpk.const_mul (n.choose k : ℝ))
  have hprod := hc.mul h1k
  convert hprod using 1 <;> try rfl
  ring

/-- binomial tail probability `Σ_{k=N}^n C(n,k) p^k (1-p)^(n-k)` -/
noncomputable def binTail (n N : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc N n, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- the derivative of the binomial tail telescopes to the boundary term -/
lemma tail_deriv_sum (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n) (x : ℝ) :
    (∑ k ∈ Finset.Icc N n,
      (n.choose k : ℝ) * ((k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
        - ((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1)))
      = (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) * x ^ (N - 1) * (1 - x) ^ (n - N) := by
  let P : ℕ → ℝ := fun j =>
    (n : ℝ) * ((n - 1).choose (j - 1) : ℝ) * x ^ (j - 1) * (1 - x) ^ (n - j)
  have hterm : ∀ k ∈ Finset.Icc N n,
      (n.choose k : ℝ) * ((k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
        - ((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1)) = P k - P (k + 1) := by
    intro k hk
    have hkN : 1 ≤ k := le_trans hN (Finset.mem_Icc.mp hk).1
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hck1 : (n.choose k : ℝ) * (k : ℝ) = (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) := by
      exact_mod_cast (choose_mul_self n k hn hkN)
    have hck2 : (n.choose k : ℝ) * (((n - k : ℕ) : ℝ)) = (n : ℝ) * ((n - 1).choose k : ℝ) := by
      exact_mod_cast (choose_mul_sub n k hn)
    have hk1exp : (k + 1) - 1 = k := by omega
    have hexp : (n - k - 1) = n - (k + 1) := by omega
    calc
      (n.choose k : ℝ) * ((k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
          - ((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1))
          = (n.choose k : ℝ) * (k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
            - (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1) := by
              ring
      _ = (n : ℝ) * ((n - 1).choose (k - 1) : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
          - (n : ℝ) * ((n - 1).choose k : ℝ) * x ^ k * (1 - x) ^ (n - k - 1) := by
              rw [hck1, hck2]
      _ = P k - P (k + 1) := by
              dsimp [P]
              simp [hk1exp, hexp]
  have htel := Finset.sum_Icc_sub hNn P
  calc
    (∑ k ∈ Finset.Icc N n,
      (n.choose k : ℝ) * ((k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
        - ((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1)))
        = ∑ k ∈ Finset.Icc N n, (P k - P (k + 1)) := by
          exact Finset.sum_congr rfl hterm
    _ = -(P (n + 1) - P N) := by
          have h2 : (∑ k ∈ Finset.Icc N n, (P k - P (k + 1))) =
              - (∑ k ∈ Finset.Icc N n, (P (k + 1) - P k)) := by
            rw [← Finset.sum_neg_distrib]
            congr 1
            funext k
            ring
          rw [h2, htel]
    _ = P N := by
          have hPn1 : P (n + 1) = 0 := by
            dsimp [P]
            have hchoose : (n - 1).choose n = 0 := Nat.choose_eq_zero_of_lt (by omega)
            simp [hchoose]
          rw [hPn1]
          ring
    _ = (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) * x ^ (N - 1) * (1 - x) ^ (n - N) := by
          dsimp [P]

/-- derivative of the binomial tail = the incomplete-Beta boundary term -/
lemma tail_hasDerivAt (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n) (x : ℝ) :
    HasDerivAt (binTail n N)
      ((n : ℝ) * ((n - 1).choose (N - 1) : ℝ) * mass n N x) x := by
  change HasDerivAt (fun x : ℝ => ∑ k ∈ Finset.Icc N n, (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k))
      ((n : ℝ) * ((n - 1).choose (N - 1) : ℝ) * mass n N x) x
  have hF : (fun x : ℝ => ∑ k ∈ Finset.Icc N n, (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k))
      = ∑ k ∈ Finset.Icc N n, (fun x : ℝ => (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)) := by
    funext x
    simp
  rw [hF]
  have hsum : HasDerivAt
      (∑ k ∈ Finset.Icc N n, fun x : ℝ => (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k))
      (∑ k ∈ Finset.Icc N n,
        (n.choose k : ℝ) * ((k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
          - ((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1))) x := by
    exact HasDerivAt.sum (u := Finset.Icc N n) (fun k hk => term_hasDerivAt n k x)
  have hte := tail_deriv_sum n N hn hN hNn x
  have hval : (∑ k ∈ Finset.Icc N n,
        (n.choose k : ℝ) * ((k : ℝ) * x ^ (k - 1) * (1 - x) ^ (n - k)
          - ((n - k : ℕ) : ℝ) * x ^ k * (1 - x) ^ (n - k - 1)))
      = (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) * mass n N x := by
    rw [hte]
    unfold mass
    ring
  simpa [hval] using hsum

/-- the binomial tail is its derivative integrated: incomplete Beta identity -/
lemma binTail_integral (n N : ℕ) (hn : 1 ≤ n) (hN : 1 ≤ N) (hNn : N ≤ n) (p : ℝ) :
    binTail n N p = (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) *
      ∫ x in (0 : ℝ)..p, mass n N x := by
  have hder : ∀ x ∈ Set.uIcc (0 : ℝ) p, DifferentiableAt ℝ (binTail n N) x := by
    intro x hx
    exact (tail_hasDerivAt n N hn hN hNn x).differentiableAt
  have hderfun : deriv (binTail n N) =
      fun x : ℝ => (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) * mass n N x := by
    funext x
    exact (tail_hasDerivAt n N hn hN hNn x).deriv
  have hint : IntervalIntegrable (deriv (binTail n N)) volume (0 : ℝ) p := by
    rw [hderfun]
    exact ((continuous_mass n N).const_mul ((n : ℝ) * ((n - 1).choose (N - 1) : ℝ))).intervalIntegrable 0 p
  have hftc := intervalIntegral.integral_deriv_eq_sub hder hint
  have htail0 : binTail n N 0 = 0 := by
    unfold binTail
    refine Finset.sum_eq_zero ?_
    intro k hk
    have hkN : 1 ≤ k := le_trans hN (Finset.mem_Icc.mp hk).1
    have hk0 : k ≠ 0 := by omega
    simp [hk0, zero_pow hk0]
  calc
    binTail n N p = (binTail n N p - binTail n N 0) := by rw [htail0]; ring
    _ = ∫ x in (0 : ℝ)..p, deriv (binTail n N) x := by
      exact (intervalIntegral.integral_deriv_eq_sub hder hint).symm
    _ = (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) *
          ∫ x in (0 : ℝ)..p, mass n N x := by
      rw [hderfun]
      simp [intervalIntegral.integral_const_mul]

/-! ### Mean-side reflection lemma (median ≤ mean)
For `1 ≤ a ≤ b`, with `c := a/b`, `m := c/(1+c) = a/(a+b)` the mean of
`x^(a-1)(1-x)^(b-1)`, one has `∫₀^m ≥ (1/2)∫₀^1`.
The core is the pointwise inequality
`c^(2a) (1-t)^(a-1) t^(b-1) ≤ t^(a-1)(1-t)^(b-1) D^(a+b)`, `D = c²(1-t)+t`,
valid on `0 ≤ t ≤ m`, proved via the log-ratio `meanL` below. -/

/-- mean reflection log-ratio (≥ 0 on (0,m]) -/
noncomputable def meanL (a b : ℕ) (c : ℝ) (t : ℝ) : ℝ :=
  ((b - a : ℕ) : ℝ) * (Real.log (1 - t) - Real.log t)
    + ((a + b : ℕ) : ℝ) * Real.log (c ^ 2 * (1 - t) + t)
    - ((2 * a : ℕ) : ℝ) * Real.log c

/-- derivative of `meanL` -/
noncomputable def meanLderiv (a b : ℕ) (c : ℝ) (t : ℝ) : ℝ :=
  -((b - a : ℕ) : ℝ) * ((1 - t)⁻¹ + t⁻¹)
    + ((a + b : ℕ) : ℝ) * (1 - c ^ 2) * (c ^ 2 * (1 - t) + t)⁻¹

/-- `meanL` has the expected derivative -/
lemma meanL_hasDerivAt {a b : ℕ} {c t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hD : 0 < c ^ 2 * (1 - t) + t) :
    HasDerivAt (meanL a b c) (meanLderiv a b c t) t := by
  unfold meanL meanLderiv
  have h1 : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-(1 - t)⁻¹) t := by
    have hinner : HasDerivAt (fun t : ℝ => 1 - t) (-1) t := by
      exact HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id t)
    have hlog : HasDerivAt (fun y : ℝ => Real.log y) ((1 - t)⁻¹) (1 - t) := by
      simpa using Real.hasDerivAt_log (by linarith : 1 - t ≠ 0)
    convert hlog.comp t hinner using 1 <;> try rfl
    ring
  have h2 : HasDerivAt (fun t : ℝ => Real.log t) (t⁻¹) t := by
    simpa using Real.hasDerivAt_log (by linarith : t ≠ 0)
  have h3 : HasDerivAt (fun t : ℝ => Real.log (c ^ 2 * (1 - t) + t))
      ((1 - c ^ 2) * (c ^ 2 * (1 - t) + t)⁻¹) t := by
    have hD' : 0 < c ^ 2 + (1 - c ^ 2) * t := by nlinarith
    have hinner : HasDerivAt (fun t : ℝ => c ^ 2 + (1 - c ^ 2) * t) (1 - c ^ 2) t := by
      have hb : HasDerivAt (fun x : ℝ => c ^ 2 + (1 - c ^ 2) * id x) ((1 - c ^ 2) * 1) t :=
        ((hasDerivAt_id t).const_mul (1 - c ^ 2)).const_add (c ^ 2)
      convert hb using 1 <;> try rfl
      ring
    have hlog : HasDerivAt (fun y : ℝ => Real.log y) ((c ^ 2 + (1 - c ^ 2) * t)⁻¹)
        (c ^ 2 + (1 - c ^ 2) * t) := by
      simpa using Real.hasDerivAt_log (ne_of_gt hD')
    have hc := hlog.comp t hinner
    convert hc using 1 <;> try rfl
    · funext x
      congr 1
      ring
    · ring
  have hA : HasDerivAt (fun t : ℝ => ((b - a : ℕ) : ℝ) * (Real.log (1 - t) - Real.log t))
      (((b - a : ℕ) : ℝ) * (-(1 - t)⁻¹ - t⁻¹)) t := by
    convert ((h1.sub h2).const_mul ((b - a : ℕ) : ℝ)) using 1 <;> try rfl
  have hB : HasDerivAt (fun t : ℝ => ((a + b : ℕ) : ℝ) * Real.log (c ^ 2 * (1 - t) + t))
      (((a + b : ℕ) : ℝ) * ((1 - c ^ 2) * (c ^ 2 * (1 - t) + t)⁻¹)) t := by
    simpa [mul_assoc] using (h3.const_mul ((a + b : ℕ) : ℝ))
  have hC : HasDerivAt (fun t : ℝ => ((2 * a : ℕ) : ℝ) * Real.log c) 0 t := by
    simpa using (hasDerivAt_const t (((2 * a : ℕ) : ℝ) * Real.log c))
  convert ((hA.add hB).sub hC) using 1 <;> try rfl
  ring

/-- `(b-a)·D - (a+b)(1-c²)t(1-t) = (a+b)(1-c²)(t-m)²` (with `D = c²(1-t)+t`,
`c = a/b`, `m = a/(a+b)`) -/
lemma mean_square_identity {a b : ℕ} (hab : a ≤ b) {c t m : ℝ}
    (hc : c = (a : ℝ) / (b : ℝ)) (hm : m = (a : ℝ) / ((a : ℝ) + (b : ℝ)))
    (hb0 : (b : ℝ) ≠ 0) :
    ((b - a : ℕ) : ℝ) * (c ^ 2 * (1 - t) + t) - ((a : ℝ) + (b : ℝ)) * (1 - c ^ 2) * t * (1 - t)
      = ((a : ℝ) + (b : ℝ)) * (1 - c ^ 2) * (t - m) ^ 2 := by
  rw [hc, hm]
  rw [Nat.cast_sub hab]
  field_simp [hb0]
  ring

/-- derivative of the mean log-ratio ≤ 0 on (0,1) -/
lemma meanLderiv_nonpos {a b : ℕ} (hab : a ≤ b)
    {c t : ℝ} (hc : c = (a : ℝ) / (b : ℝ))
    (hb0 : (b : ℝ) ≠ 0) (hc2 : c ^ 2 ≤ 1)
    (ht0 : 0 < t) (htm : t < 1) (hD : 0 < c ^ 2 * (1 - t) + t) :
    meanLderiv a b c t ≤ 0 := by
  have ht1t : 0 < t * (1 - t) := by
    have h1t : 0 < 1 - t := sub_pos.mpr htm
    positivity
  have hc2' : 0 ≤ 1 - c ^ 2 := by nlinarith
  have hK : 0 ≤ ((b - a : ℕ) : ℝ) * (c ^ 2 * (1 - t) + t)
      - ((a : ℝ) + (b : ℝ)) * (1 - c ^ 2) * t * (1 - t) := by
    rw [mean_square_identity hab hc rfl hb0]
    have h1 : 0 ≤ ((a : ℝ) + (b : ℝ)) := by positivity
    exact mul_nonneg (mul_nonneg h1 hc2') (sq_nonneg _)
  have hinv : (1 - t)⁻¹ + t⁻¹ = (t * (1 - t))⁻¹ := by
    field_simp [ne_of_gt ht0, ne_of_gt (sub_pos.mpr htm)]
    ring
  unfold meanLderiv
  have hcl : ((a : ℝ) + (b : ℝ)) * (1 - c ^ 2) * (c ^ 2 * (1 - t) + t)⁻¹
      ≤ ((b - a : ℕ) : ℝ) * ((1 - t)⁻¹ + t⁻¹) := by
    rw [hinv]
    change ((a : ℝ) + (b : ℝ)) * (1 - c ^ 2) / (c ^ 2 * (1 - t) + t)
        ≤ ((b - a : ℕ) : ℝ) / (t * (1 - t))
    rw [le_div_iff₀ ht1t]
    rw [div_mul_eq_mul_div]
    rw [div_le_iff₀ hD]
    linarith [hK]
  rw [Nat.cast_add]
  linarith [hcl]

/-- continuity of the mean log-ratio on (0,m] -/
lemma meanL_continuousOn {a b : ℕ} {c m : ℝ} (hc0 : 0 < c) (hc2 : c ^ 2 ≤ 1)
    (hm0 : 0 < m) (hm1 : m < 1) :
    ContinuousOn (meanL a b c) (Set.Ioc 0 m) := by
  unfold meanL
  have hsub : ContinuousOn (fun t : ℝ => Real.log (1 - t)) (Set.Ioc 0 m) := by
    have hmain := (continuousOn_log_affine (A := 1) (B := -1) (s := Set.Ioc 0 m)) (by
      intro t ht
      have htm : t ≤ m := ht.2
      have h1 : 0 < 1 - m := sub_pos.mpr hm1
      have hpos : 0 < 1 + -1 * t := by nlinarith [h1, htm]
      exact ne_of_gt hpos)
    convert hmain using 1
    funext x
    congr 1
    ring
  have hid : ContinuousOn (fun t : ℝ => Real.log t) (Set.Ioc 0 m) := by
    have hmain := (continuousOn_log_affine (A := 0) (B := 1) (s := Set.Ioc 0 m)) (by
      intro t ht
      exact ne_of_gt (by simpa using ht.1))
    convert hmain using 1
    funext x
    congr 1
    ring
  have hD : ContinuousOn (fun t : ℝ => Real.log (c ^ 2 * (1 - t) + t)) (Set.Ioc 0 m) := by
    have hmain := (continuousOn_log_affine (A := c ^ 2) (B := 1 - c ^ 2) (s := Set.Ioc 0 m)) (by
      intro t ht
      have hrest : 0 ≤ (1 - c ^ 2) * t := mul_nonneg (sub_nonneg.mpr hc2) (le_of_lt ht.1)
      have hcsq : 0 < c ^ 2 := pow_pos hc0 2
      have hpos : 0 < c ^ 2 + (1 - c ^ 2) * t := by nlinarith
      exact ne_of_gt hpos)
    convert hmain using 1
    funext x
    congr 1
    ring
  have hA : ContinuousOn (fun t : ℝ => ((b - a : ℕ) : ℝ) * (Real.log (1 - t) - Real.log t))
      (Set.Ioc 0 m) := by
    simpa [mul_sub] using (hsub.sub hid).const_mul ((b - a : ℕ) : ℝ)
  have hB : ContinuousOn (fun t : ℝ => ((a + b : ℕ) : ℝ) * Real.log (c ^ 2 * (1 - t) + t))
      (Set.Ioc 0 m) := by
    simpa [mul_assoc] using hD.const_mul ((a + b : ℕ) : ℝ)
  have hC : ContinuousOn (fun t : ℝ => ((2 * a : ℕ) : ℝ) * Real.log c) (Set.Ioc 0 m) := by
    exact continuousOn_const
  convert ((hA.add hB).sub hC) using 1 <;> try rfl

/-- the mean log-ratio is antitone on (0,m] -/
lemma meanL_antitone {a b : ℕ} (hab : a ≤ b)
    {c m : ℝ} (hc : c = (a : ℝ) / (b : ℝ)) (hb0 : (b : ℝ) ≠ 0)
    (hc0 : 0 < c) (hc2 : c ^ 2 ≤ 1) (hm0 : 0 < m) (hm1 : m < 1) :
    AntitoneOn (meanL a b c) (Set.Ioc 0 m) := by
  apply antitoneOn_of_deriv_nonpos
  · exact convex_Ioc 0 m
  · exact meanL_continuousOn hc0 hc2 hm0 hm1
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 m := by simpa [interior_Ioc] using ht
    have ht0 : 0 < t := ht'.1
    have htm : t < m := ht'.2
    have ht1 : t < 1 := lt_trans htm hm1
    have hD : 0 < c ^ 2 * (1 - t) + t := by
      have hrest : 0 ≤ (1 - c ^ 2) * t := mul_nonneg (sub_nonneg.mpr hc2) (le_of_lt ht0)
      have hcsq : 0 < c ^ 2 := pow_pos hc0 2
      nlinarith
    exact (meanL_hasDerivAt ht0 ht1 hD).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : t ∈ Set.Ioo 0 m := by simpa [interior_Ioc] using ht
    have ht0 : 0 < t := ht'.1
    have htm : t < m := ht'.2
    have ht1 : t < 1 := lt_trans htm hm1
    have hD : 0 < c ^ 2 * (1 - t) + t := by
      have hrest : 0 ≤ (1 - c ^ 2) * t := mul_nonneg (sub_nonneg.mpr hc2) (le_of_lt ht0)
      have hcsq : 0 < c ^ 2 := pow_pos hc0 2
      nlinarith
    have hder : deriv (meanL a b c) t = meanLderiv a b c t := by
      exact (meanL_hasDerivAt ht0 ht1 hD).deriv
    rw [hder]
    exact meanLderiv_nonpos hab hc hb0 hc2 ht0 ht1 hD

/-- `meanL` vanishes at the mean `m = c/(1+c)` (when `c = a/b`, `m = a/(a+b)`) -/
lemma meanL_at_mean (a b : ℕ) (hab : a ≤ b) {c : ℝ} (hc0 : 0 < c) :
    meanL a b c (c / (1 + c)) = 0 := by
  have h1c : 1 + c ≠ 0 := by positivity
  have h1cpos : 0 < 1 + c := by positivity
  have hA : 1 - c / (1 + c) = 1 / (1 + c) := by
    field_simp [h1c]
    ring
  have hB : c ^ 2 * (1 / (1 + c)) + c / (1 + c) = c := by
    field_simp [h1c]
    ring
  unfold meanL
  rw [hA, hB]
  have h1 : Real.log (1 / (1 + c)) = -Real.log (1 + c) := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt h1cpos)]
    simp
  have h2 : Real.log (c / (1 + c)) = Real.log c - Real.log (1 + c) := by
    rw [Real.log_div (ne_of_gt hc0) (ne_of_gt h1cpos)]
  have hmain : Real.log (1 / (1 + c)) - Real.log (c / (1 + c)) + Real.log c = 0 := by
    rw [h1, h2]
    ring
  rw [Nat.cast_sub hab]
  -- goal: (b - a)*(log(1/(1+c)) - log(c/(1+c))) + (a+b)*log c - 2a*log c = 0 with (b-a) = (b:ℝ)-(a:ℝ)
  have hdiff : Real.log (1 / (1 + c)) - Real.log (c / (1 + c)) = -Real.log c := by
    have htmp := hmain
    linarith
  rw [hdiff]
  rw [Nat.cast_add, Nat.cast_mul]
  ring

/-- the mean log-ratio is nonnegative on (0,m] -/
lemma meanL_nonneg {a b : ℕ} (hab : a ≤ b)
    {c x m : ℝ} (hc : c = (a : ℝ) / (b : ℝ)) (hb0 : (b : ℝ) ≠ 0)
    (hc0 : 0 < c) (hc2 : c ^ 2 ≤ 1)
    (hmm : m = c / (1 + c)) (hx0 : 0 < x) (hxm : x ≤ m) :
    0 ≤ meanL a b c x := by
  have hm0 : 0 < m := by rw [hmm]; positivity
  have hm1 : m < 1 := by
    rw [hmm]
    have h1c : 0 < 1 + c := by positivity
    rw [div_lt_one h1c]
    linarith
  have hmem : x ∈ Set.Ioc 0 m := ⟨hx0, hxm⟩
  have hmemm : m ∈ Set.Ioc 0 m := ⟨hm0, le_rfl⟩
  have hant := meanL_antitone hab hc hb0 hc0 hc2 hm0 hm1
  have hle : meanL a b c m ≤ meanL a b c x := hant hmem hmemm hxm
  have hLm : meanL a b c m = 0 := by
    rw [hmm]
    exact meanL_at_mean a b hab hc0
  rw [hLm] at hle
  exact hle

/-- core reflection inequality for the mean (0 ≤ t ≤ m, `m = c/(1+c)`, `c = a/b ≤ 1`) -/
lemma mean_refl_ineq {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb2 : 2 ≤ b) {c t : ℝ}
    (hc : c = (a : ℝ) / (b : ℝ)) (hb0 : (b : ℝ) ≠ 0) (hc0 : 0 < c)
    (ht0 : 0 ≤ t) (htm : t ≤ c / (1 + c)) :
    c ^ (2 * a) * (1 - t) ^ (a - 1) * t ^ (b - 1)
      ≤ t ^ (a - 1) * (1 - t) ^ (b - 1) * (c ^ 2 * (1 - t) + t) ^ (a + b) := by
  by_cases htz : t = 0
  · subst t
    have hb1 : b - 1 ≠ 0 := by omega
    rw [zero_pow hb1]
    simp
    change 0 ≤ (0 : ℝ) ^ (a - 1) * (c ^ 2) ^ (a + b)
    exact mul_nonneg (by
      by_cases ha0 : a - 1 = 0
      · rw [ha0, pow_zero]; norm_num
      · rw [zero_pow ha0]) (pow_nonneg (sq_nonneg c) (a + b))
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (by exact Ne.symm htz)
    have h1c : 0 < 1 + c := by positivity
    have hm1 : c / (1 + c) < 1 := by
      rw [div_lt_one h1c]
      linarith
    have ht1 : t < 1 := lt_of_le_of_lt htm hm1
    have hDpos : 0 < c ^ 2 * (1 - t) + t := by positivity
    have h1tpos : 0 < 1 - t := sub_pos.mpr ht1
    have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    have hc1 : c ≤ 1 := by
      have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      rw [hc]
      rw [div_le_iff₀ hbpos]
      simpa using habR
    have hc2 : c ^ 2 ≤ 1 := by
      have hcnonneg : 0 ≤ c := le_of_lt hc0
      have hmul := mul_le_mul hc1 hc1 hcnonneg (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    have hL0 : 0 ≤ meanL a b c t := meanL_nonneg hab hc hb0 hc0 hc2 rfl htpos htm
    have hlogA : Real.log (t ^ (a - 1) * (1 - t) ^ (b - 1) * (c ^ 2 * (1 - t) + t) ^ (a + b))
        = ((a - 1 : ℕ) : ℝ) * Real.log t + ((b - 1 : ℕ) : ℝ) * Real.log (1 - t)
          + ((a + b : ℕ) : ℝ) * Real.log (c ^ 2 * (1 - t) + t) := by
      rw [Real.log_mul (by positivity : t ^ (a - 1) * (1 - t) ^ (b - 1) ≠ 0)
          (by positivity : (c ^ 2 * (1 - t) + t) ^ (a + b) ≠ 0)]
      rw [Real.log_mul (by positivity : t ^ (a - 1) ≠ 0) (by positivity : (1 - t) ^ (b - 1) ≠ 0)]
      rw [Real.log_pow, Real.log_pow, Real.log_pow]
    have hlogB : Real.log (c ^ (2 * a) * (1 - t) ^ (a - 1) * t ^ (b - 1))
        = ((2 * a : ℕ) : ℝ) * Real.log c + ((a - 1 : ℕ) : ℝ) * Real.log (1 - t)
          + ((b - 1 : ℕ) : ℝ) * Real.log t := by
      rw [Real.log_mul (by positivity : c ^ (2 * a) * (1 - t) ^ (a - 1) ≠ 0)
          (by positivity : t ^ (b - 1) ≠ 0)]
      rw [Real.log_mul (by positivity : c ^ (2 * a) ≠ 0) (by positivity : (1 - t) ^ (a - 1) ≠ 0)]
      rw [Real.log_pow, Real.log_pow, Real.log_pow]
    have hrel : Real.log (c ^ (2 * a) * (1 - t) ^ (a - 1) * t ^ (b - 1))
        - Real.log (t ^ (a - 1) * (1 - t) ^ (b - 1) * (c ^ 2 * (1 - t) + t) ^ (a + b))
        + meanL a b c t = 0 := by
      rw [hlogB, hlogA]
      unfold meanL
      rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_sub hab]
      rw [Nat.cast_add]
      rw [Nat.cast_mul]
      ring
    have hle_log : Real.log (c ^ (2 * a) * (1 - t) ^ (a - 1) * t ^ (b - 1))
        ≤ Real.log (t ^ (a - 1) * (1 - t) ^ (b - 1) * (c ^ 2 * (1 - t) + t) ^ (a + b)) := by
      linarith [hrel, hL0]
    have hBpos : 0 < c ^ (2 * a) * (1 - t) ^ (a - 1) * t ^ (b - 1) := by positivity
    have hApos : 0 < t ^ (a - 1) * (1 - t) ^ (b - 1) * (c ^ 2 * (1 - t) + t) ^ (a + b) := by positivity
    have hexp := Real.exp_le_exp.mpr hle_log
    rw [Real.exp_log hBpos, Real.exp_log hApos] at hexp
    exact hexp

/-- `D(t) = c²(1-t)+t` -/
noncomputable def meanD (c t : ℝ) : ℝ := c ^ 2 * (1 - t) + t

/-- the reflection `x ↦ c²(1-x)/(c²(1-x)+x)` in odds space -/
noncomputable def meanX (c t : ℝ) : ℝ := c ^ 2 * (1 - t) / meanD c t

/-- minus the derivative of `meanX` -/
noncomputable def meanJ (c t : ℝ) : ℝ := c ^ 2 / (meanD c t) ^ 2

lemma meanD_pos {c t : ℝ} (hc0 : 0 < c) (ht0 : 0 ≤ t) (htm : t ≤ c / (1 + c)) :
    0 < meanD c t := by
  have h1c : 0 < 1 + c := by positivity
  have hm1 : c / (1 + c) < 1 := by
    rw [div_lt_one h1c]
    linarith
  have h1t : 0 < 1 - t := by
    have htm1 : t < 1 := lt_of_le_of_lt htm hm1
    linarith
  unfold meanD
  nlinarith [mul_pos (sq_pos_of_pos hc0) h1t]

lemma meanX_mem {c t : ℝ} (hc0 : 0 < c) (ht0 : 0 ≤ t) (htm : t ≤ c / (1 + c)) :
    0 ≤ meanX c t ∧ meanX c t ≤ 1 := by
  have h1c : 0 < 1 + c := by positivity
  have hm1 : c / (1 + c) < 1 := by
    rw [div_lt_one h1c]
    linarith
  have ht1 : t < 1 := lt_of_le_of_lt htm hm1
  have hD : 0 < meanD c t := meanD_pos hc0 ht0 htm
  have hnum0 : 0 ≤ c ^ 2 * (1 - t) := mul_nonneg (sq_nonneg c) (by linarith)
  constructor
  · unfold meanX
    exact div_nonneg hnum0 (le_of_lt hD)
  · unfold meanX
    rw [div_le_iff₀ hD]
    unfold meanD
    nlinarith

/-- the reflected mass is no larger: pointwise mean-side comparison -/
lemma mean_pointwise (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb2 : 2 ≤ b) {c t : ℝ}
    (hc : c = (a : ℝ) / (b : ℝ)) (hb0 : (b : ℝ) ≠ 0) (hc0 : 0 < c)
    (ht0 : 0 ≤ t) (htm : t ≤ c / (1 + c)) :
    mass (a + b - 1) a (meanX c t) * meanJ c t ≤ mass (a + b - 1) a t := by
  have hsub : (a + b - 1) - a = b - 1 := by omega
  have hmass (y : ℝ) : mass (a + b - 1) a y = y ^ (a - 1) * (1 - y) ^ (b - 1) := by
    unfold mass
    rw [hsub]
  by_cases htz : t = 0
  · subst t
    -- LHS = 0
    have hX : meanX c 0 = 1 := by
      unfold meanX meanD
      have hc2nz : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc0)
      calc
        c ^ 2 * (1 - 0) / (c ^ 2 * (1 - 0) + 0) = c ^ 2 / c ^ 2 := by ring
        _ = 1 := by rw [div_self hc2nz]
    have hmass1 : mass (a + b - 1) a 1 = 0 := by
      rw [hmass 1]
      have hz : (0 : ℝ) ^ (b - 1) = 0 := zero_pow (by omega : b - 1 ≠ 0)
      rw [show 1 - 1 = (0 : ℝ) by norm_num, hz]
      ring
    have hR : 0 ≤ mass (a + b - 1) a 0 := by
      rw [hmass 0]
      have h1 : 0 ≤ (0 : ℝ) ^ (a - 1) := by
        by_cases ha0 : a - 1 = 0
        · rw [ha0, pow_zero]; norm_num
        · rw [zero_pow ha0]
      have h2 : 0 ≤ ((1 - 0 : ℝ)) ^ (b - 1) := pow_nonneg (by norm_num) _
      exact mul_nonneg h1 h2
    calc
      mass (a + b - 1) a (meanX c 0) * meanJ c 0
          = mass (a + b - 1) a 1 * meanJ c 0 := by rw [hX]
      _ = 0 := by rw [hmass1]; ring
      _ ≤ mass (a + b - 1) a 0 := hR
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (by exact Ne.symm htz)
    have h1c : 0 < 1 + c := by positivity
    have hm1 : c / (1 + c) < 1 := by rw [div_lt_one h1c]; linarith
    have ht1 : t < 1 := lt_of_le_of_lt htm hm1
    have hD : 0 < meanD c t := meanD_pos hc0 ht0 htm
    have h1t : 0 < 1 - t := sub_pos.mpr ht1
    have h1mX : 1 - meanX c t = t / meanD c t := by
      unfold meanX meanD
      have hD' : c ^ 2 * (1 - t) + t ≠ 0 := by simpa [meanD] using (ne_of_gt hD)
      field_simp [hD']
      ring
    have hbpos : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    have hc1 : c ≤ 1 := by
      have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      rw [hc]
      rw [div_le_iff₀ hbpos]
      simpa using habR
    have hc2 : c ^ 2 ≤ 1 := by
      have hcnonneg : 0 ≤ c := le_of_lt hc0
      have hmul := mul_le_mul hc1 hc1 hcnonneg (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    have hL0 : 0 ≤ meanL a b c t := meanL_nonneg hab hc hb0 hc0 hc2 rfl htpos htm
    have hXpos : 0 < meanX c t := by
      unfold meanX
      positivity
    have h1Xpos : 0 < 1 - meanX c t := by
      rw [h1mX]
      positivity
    have hJpos : 0 < meanJ c t := by
      unfold meanJ
      positivity
    -- positivity of the two mass values:
    have hLXpos : 0 < mass (a + b - 1) a (meanX c t) * meanJ c t := by
      rw [hmass (meanX c t)]
      have h1 : 0 < meanX c t ^ (a - 1) := pow_pos hXpos _
      have h2 : 0 < (1 - meanX c t) ^ (b - 1) := pow_pos h1Xpos _
      have h3 : 0 < meanJ c t := hJpos
      positivity
    have hRXpos : 0 < mass (a + b - 1) a t := by
      rw [hmass t]
      have h1 : 0 < t ^ (a - 1) := pow_pos htpos _
      have h2 : 0 < (1 - t) ^ (b - 1) := pow_pos h1t _
      positivity
    -- log of the LHS mass·J expanded:
    have hlogL : Real.log (mass (a + b - 1) a (meanX c t) * meanJ c t)
        = ((2 * a : ℕ) : ℝ) * Real.log c + ((a - 1 : ℕ) : ℝ) * Real.log (1 - t)
          + ((b - 1 : ℕ) : ℝ) * Real.log t
          - ((a + b : ℕ) : ℝ) * Real.log (meanD c t) := by
      rw [hmass (meanX c t)]
      rw [Real.log_mul (by positivity : meanX c t ^ (a - 1) * (1 - meanX c t) ^ (b - 1) ≠ 0) (ne_of_gt hJpos)]
      rw [Real.log_mul (by positivity : meanX c t ^ (a - 1) ≠ 0) (by positivity : (1 - meanX c t) ^ (b - 1) ≠ 0)]
      rw [Real.log_pow, Real.log_pow]
      -- ln(meanX) & ln(1−meanX) & ln meanJ:
      have hlogX : Real.log (meanX c t) = 2 * Real.log c + Real.log (1 - t) - Real.log (meanD c t) := by
        unfold meanX
        rw [Real.log_div (by positivity : c ^ 2 * (1 - t) ≠ 0) (ne_of_gt hD)]
        rw [Real.log_mul (by positivity : c ^ 2 ≠ 0) (by positivity : 1 - t ≠ 0)]
        rw [Real.log_pow]
        ring
      have hlog1X : Real.log (1 - meanX c t) = Real.log t - Real.log (meanD c t) := by
        rw [h1mX]
        rw [Real.log_div (ne_of_gt htpos) (ne_of_gt hD)]
      have hlogJ : Real.log (meanJ c t) = 2 * Real.log c - 2 * Real.log (meanD c t) := by
        unfold meanJ
        rw [Real.log_div (by positivity : c ^ 2 ≠ 0) (by positivity : (meanD c t) ^ 2 ≠ 0)]
        rw [Real.log_pow, Real.log_pow]
        ring
      rw [hlogX, hlog1X, hlogJ]
      rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ b),
          Nat.cast_add, Nat.cast_mul]
      ring
    have hlogR : Real.log (mass (a + b - 1) a t)
        = ((a - 1 : ℕ) : ℝ) * Real.log t + ((b - 1 : ℕ) : ℝ) * Real.log (1 - t) := by
      rw [hmass t]
      rw [Real.log_mul (by positivity : t ^ (a - 1) ≠ 0) (by positivity : (1 - t) ^ (b - 1) ≠ 0)]
      rw [Real.log_pow, Real.log_pow]
    have hml : meanL a b c t = Real.log (mass (a + b - 1) a t) - Real.log (mass (a + b - 1) a (meanX c t) * meanJ c t) := by
      rw [hlogR, hlogL]
      unfold meanL
      rw [show Real.log (meanD c t) = Real.log (c ^ 2 * (1 - t) + t) by rfl]
      rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_sub (by omega : 1 ≤ b), Nat.cast_sub hab]
      rw [Nat.cast_add, Nat.cast_mul]
      ring
    have hlogle : Real.log (mass (a + b - 1) a (meanX c t) * meanJ c t)
        ≤ Real.log (mass (a + b - 1) a t) := by
      rw [hml] at hL0
      linarith
    have hexp := Real.exp_le_exp.mpr hlogle
    rw [Real.exp_log hLXpos, Real.exp_log hRXpos] at hexp
    exact hexp

/-- derivative of the reflection `meanX` -/
lemma meanX_hasDerivAt {c t : ℝ} (hD : meanD c t ≠ 0) :
    HasDerivAt (fun t : ℝ => meanX c t) (-(c ^ 2 / (meanD c t) ^ 2)) t := by
  unfold meanX
  have hnum : HasDerivAt (fun t : ℝ => c ^ 2 * (1 - t)) (-c ^ 2) t := by
    have hb := (HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id t)).const_mul (c ^ 2)
    convert hb using 1 <;> try rfl
    ring
  have hden : HasDerivAt (fun t : ℝ => c ^ 2 * (1 - t) + t) (1 - c ^ 2) t := by
    convert hnum.add (hasDerivAt_id t) using 1 <;> try rfl
    ring
  change HasDerivAt (fun t : ℝ => c ^ 2 * (1 - t) / (c ^ 2 * (1 - t) + t))
      (-(c ^ 2 / (meanD c t) ^ 2)) t
  have hD' : c ^ 2 * (1 - t) + t ≠ 0 := by simpa [meanD] using hD
  have hdiv := hnum.div hden hD'
  convert hdiv using 1 <;> try rfl
  rw [show meanD c t = c ^ 2 * (1 - t) + t by rfl]
  ring

/-- `meanX` is continuous on `[0,m]` -/
lemma meanX_continuousOn {c m : ℝ} (hc0 : 0 < c) (hm0 : 0 ≤ m)
    (hmm1 : m ≤ c / (1 + c)) : ContinuousOn (meanX c) (Set.uIcc 0 m) := by
  have hmem (t : ℝ) (ht : t ∈ Set.uIcc 0 m) : t ∈ Set.Icc 0 m := by
    simpa [Set.uIcc_of_le hm0] using ht
  have hDnz : ∀ t ∈ Set.uIcc 0 m, meanD c t ≠ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (hmem t ht).1
    have htm : t ≤ m := (hmem t ht).2
    exact ne_of_gt (meanD_pos hc0 ht0 (le_trans htm hmm1))
  have hnum : ContinuousOn (fun t : ℝ => c ^ 2 * (1 - t)) (Set.uIcc 0 m) := by
    have hlin : ContinuousOn (fun t : ℝ => 1 - t) (Set.uIcc 0 m) :=
      continuousOn_const.sub continuousOn_id
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlin.const_mul (c ^ 2)
  have hden : ContinuousOn (meanD c) (Set.uIcc 0 m) := by
    have hlin : ContinuousOn (fun t : ℝ => 1 - t) (Set.uIcc 0 m) :=
      continuousOn_const.sub continuousOn_id
    have h1 : ContinuousOn (fun t : ℝ => c ^ 2 * (1 - t) + t) (Set.uIcc 0 m) :=
      (hlin.const_mul (c ^ 2)).add continuousOn_id
    convert h1 using 1
    funext t
    unfold meanD
    rfl
  convert hnum.div hden hDnz using 1
  funext t
  unfold meanX
  rfl

/-- `meanJ` is continuous on `[0,m]` -/
lemma meanJ_continuousOn {c m : ℝ} (hc0 : 0 < c) (hm0 : 0 ≤ m)
    (hmm1 : m ≤ c / (1 + c)) : ContinuousOn (meanJ c) (Set.uIcc 0 m) := by
  have hmem (t : ℝ) (ht : t ∈ Set.uIcc 0 m) : t ∈ Set.Icc 0 m := by
    simpa [Set.uIcc_of_le hm0] using ht
  have hDnz : ∀ t ∈ Set.uIcc 0 m, meanD c t ≠ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (hmem t ht).1
    have htm : t ≤ m := (hmem t ht).2
    exact ne_of_gt (meanD_pos hc0 ht0 (le_trans htm hmm1))
  have hden : ContinuousOn (fun t : ℝ => (meanD c t) ^ 2) (Set.uIcc 0 m) := by
    have hlin : ContinuousOn (fun t : ℝ => 1 - t) (Set.uIcc 0 m) :=
      continuousOn_const.sub continuousOn_id
    have h1 : ContinuousOn (fun t : ℝ => c ^ 2 * (1 - t) + t) (Set.uIcc 0 m) :=
      (hlin.const_mul (c ^ 2)).add continuousOn_id
    have hD : ContinuousOn (fun t : ℝ => meanD c t) (Set.uIcc 0 m) := by
      convert h1 using 1
      funext t
      unfold meanD
      rfl
    convert (hD.pow 2) using 1
    funext t
    rfl
  have hden0 : ∀ t ∈ Set.uIcc 0 m, (meanD c t) ^ 2 ≠ 0 := by
    intro t ht
    exact pow_ne_zero 2 (hDnz t ht)
  have hmain : ContinuousOn (fun t : ℝ => c ^ 2 / (meanD c t) ^ 2) (Set.uIcc 0 m) := by
    exact continuousOn_const.div hden hden0
  convert hmain using 1
  funext t
  unfold meanJ
  rfl

/-- endpoints of the reflection -/
lemma meanX_zero {c : ℝ} (hc0 : 0 < c) : meanX c 0 = 1 := by
  unfold meanX meanD
  have hc2nz : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc0)
  calc
    c ^ 2 * (1 - 0) / (c ^ 2 * (1 - 0) + 0) = c ^ 2 / c ^ 2 := by ring
    _ = 1 := by rw [div_self hc2nz]

lemma meanX_fix {c m : ℝ} (hc0 : 0 < c) (hm : m = c / (1 + c)) : meanX c m = m := by
  have h1c : 1 + c ≠ 0 := by positivity
  subst m
  unfold meanX meanD
  have hA : 1 - c / (1 + c) = 1 / (1 + c) := by
    field_simp [h1c]
    ring
  rw [hA]
  field_simp [h1c]
  ring

/-- `∫₀^m ≥ (1/2)∫₀^1` at the mean `m = a/(a+b)`, for `1 ≤ a ≤ b` -/
lemma mean_mass_lower (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass (a + b - 1) a x
      ≤ ∫ x in (0 : ℝ)..((a : ℝ) / ((a : ℝ) + (b : ℝ))), mass (a + b - 1) a x := by
  by_cases hb1 : b = 1
  · subst b
    have ha1 : a = 1 := by omega
    subst a
    norm_num
    have hmass (x : ℝ) : mass 1 1 x = 1 := by
      unfold mass
      simp
    have htop : (∫ x in (0 : ℝ)..1, mass 1 1 x) = 1 := by
      have hc : (∫ x in (0 : ℝ)..1, mass 1 1 x) = ∫ x in (0 : ℝ)..1, (1 : ℝ) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        exact hmass x
      rw [hc]
      simp [intervalIntegral.integral_const]
    have hbot : (∫ x in (0 : ℝ)..(1 / 2 : ℝ), mass 1 1 x) = 1 / 2 := by
      have hc : (∫ x in (0 : ℝ)..(1 / 2 : ℝ), mass 1 1 x) = ∫ x in (0 : ℝ)..(1 / 2 : ℝ), (1 : ℝ) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        exact hmass x
      rw [hc]
      simp [intervalIntegral.integral_const]
    rw [htop, hbot]
    norm_num
  · have hb2 : 2 ≤ b := by omega
    let c : ℝ := (a : ℝ) / (b : ℝ)
    have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (show (b : ℕ) ≠ 0 by omega)
    have hbpos : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
    have hc0 : 0 < c := by
      dsimp [c]
      exact div_pos (by exact_mod_cast (show 0 < a by omega)) hbpos
    have hc : c = (a : ℝ) / (b : ℝ) := rfl
    let m : ℝ := c / (1 + c)
    have hmm1 : m ≤ c / (1 + c) := le_rfl
    have hm0 : 0 ≤ m := by dsimp [m]; positivity
    have hm : m = (a : ℝ) / ((a : ℝ) + (b : ℝ)) := by
      dsimp [m, c]
      have habpos : 0 < (a : ℝ) + (b : ℝ) := by positivity
      field_simp [hb0, ne_of_gt habpos]
      ring
    have hmle1 : m ≤ 1 := by
      dsimp [m]
      have h1c : 0 < 1 + c := by positivity
      exact div_le_one_of_le₀ (by linarith) (le_of_lt h1c)
    have hmem (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) m) : t ∈ Set.Icc 0 m := by
      simpa [Set.uIcc_of_le hm0] using ht
    have hXm : meanX c m = m := meanX_fix hc0 rfl
    have hX0 : meanX c 0 = 1 := meanX_zero hc0
    -- substitution for the reflection
    have hsubst : ∀ t ∈ Set.uIcc (0 : ℝ) m,
        HasDerivAt (fun t : ℝ => meanX c t) (-meanJ c t) t := by
      intro t ht
      have htm : t ≤ m := (hmem t ht).2
      have hDnz : meanD c t ≠ 0 :=
        ne_of_gt (meanD_pos hc0 (hmem t ht).1 (le_trans htm hmm1))
      have hd := meanX_hasDerivAt hDnz
      simpa [meanJ] using hd
    have hcontf' : ContinuousOn (fun t : ℝ => -meanJ c t) (Set.uIcc (0 : ℝ) m) :=
      (meanJ_continuousOn hc0 hm0 hmm1).neg
    have hsubint := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := m)
      (f := fun t : ℝ => meanX c t) (f' := fun t : ℝ => -meanJ c t)
      (g := mass (a + b - 1) a) hsubst hcontf' (continuous_mass (a + b - 1) a)
    -- hsubint : ∫ t in 0..m, (mass∘meanX)(t)·(−meanJ t) = ∫ y in meanX 0..meanX m, mass
    rw [hX0, hXm] at hsubint
    simp only [Function.comp_apply] at hsubint
    have hnegL : (∫ x in (0 : ℝ)..m, mass (a + b - 1) a (meanX c x) * (-meanJ c x))
        = - (∫ x in (0 : ℝ)..m, mass (a + b - 1) a (meanX c x) * meanJ c x) := by
      have hcong : (∫ x in (0 : ℝ)..m, mass (a + b - 1) a (meanX c x) * (-meanJ c x))
          = ∫ x in (0 : ℝ)..m, -(mass (a + b - 1) a (meanX c x) * meanJ c x) := by
        refine intervalIntegral.integral_congr ?_
        intro x hx
        ring
      rw [hcong]
      exact intervalIntegral.integral_neg
    have h1m : (∫ x in (1 : ℝ)..m, mass (a + b - 1) a x)
        = - (∫ x in m..(1 : ℝ), mass (a + b - 1) a x) := by
      exact intervalIntegral.integral_symm m 1
    rw [hnegL, h1m] at hsubint
    -- hsubint : -∫₀ᵐ (mass∘X)·J = -∫ₘ¹ mass
    have hB : (∫ x in m..(1 : ℝ), mass (a + b - 1) a x)
        = ∫ t in (0 : ℝ)..m, mass (a + b - 1) a (meanX c t) * meanJ c t := by
      linarith
    have hcontL : ContinuousOn (fun t : ℝ => mass (a + b - 1) a (meanX c t) * meanJ c t)
        (Set.uIcc (0 : ℝ) m) := by
      have hXc := meanX_continuousOn hc0 hm0 hmm1
      have hJc := meanJ_continuousOn hc0 hm0 hmm1
      have hf : ContinuousOn (fun t : ℝ => mass (a + b - 1) a (meanX c t)) (Set.uIcc (0 : ℝ) m) := by
        exact ((continuous_mass (a + b - 1) a).continuousOn).comp hXc (by intro t ht; exact Set.mem_univ _)
      exact hf.mul hJc
    have hmono : (∫ t in (0 : ℝ)..m, mass (a + b - 1) a (meanX c t) * meanJ c t)
        ≤ ∫ t in (0 : ℝ)..m, mass (a + b - 1) a t := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
      · exact ContinuousOn.intervalIntegrable hcontL
      · exact integrable_mass (a + b - 1) a 0 m
      · intro x hx
        exact mean_pointwise a b ha hab hb2 hc hb0 hc0 hx.1 (le_trans hx.2 hmm1)
    have hBleA : (∫ x in m..(1 : ℝ), mass (a + b - 1) a x)
        ≤ ∫ x in (0 : ℝ)..m, mass (a + b - 1) a x := by
      rw [hB]
      exact hmono
    have hsplit : (∫ x in (0 : ℝ)..1, mass (a + b - 1) a x)
        = (∫ x in (0 : ℝ)..m, mass (a + b - 1) a x)
          + (∫ x in m..(1 : ℝ), mass (a + b - 1) a x) := by
      exact (integral_add_adjacent_intervals (integrable_mass (a + b - 1) a 0 m)
        (integrable_mass (a + b - 1) a m 1)).symm
    have hT : (∫ x in (0 : ℝ)..1, mass (a + b - 1) a x)
        ≤ 2 * ∫ x in (0 : ℝ)..m, mass (a + b - 1) a x := by
      rw [hsplit]
      nlinarith [hBleA]
    have hfin : (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1, mass (a + b - 1) a x)
        ≤ ∫ x in (0 : ℝ)..m, mass (a + b - 1) a x := by
      nlinarith [hT]
    rwa [hm] at hfin

/-! ## BetaHalf: the binomial tail integral at `p = N/n` -/

/-- full binomial expansion sum: `Σ_{k=0}^n C(n,k) p^k (1-p)^(n-k) = 1` -/
lemma binom_full (n : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.Icc 0 n, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) = 1 := by
  have hIcc : Finset.Icc 0 n = Finset.range (n + 1) := by
    ext k
    simp [Finset.mem_Icc]
  calc
    (∑ k ∈ Finset.Icc 0 n, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
        = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
          rw [hIcc]
    _ = ∑ m ∈ Finset.range (n + 1), p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by
          have hp : p + (1 - p) = 1 := by ring
          rw [hp]
          simp

/-- the binomial tail at `p = 1` is 1 -/
lemma binTail_at_one (n N : ℕ) (hNn : N ≤ n) : binTail n N 1 = 1 := by
  unfold binTail
  have hmem : n ∈ Finset.Icc N n := by
    simp [Finset.mem_Icc]
    exact hNn
  rw [Finset.sum_eq_single n]
  · -- the k = n term
    have hnn : n - n = 0 := by omega
    have hc : (n.choose n : ℝ) = 1 := by simp
    rw [hnn, hc]
    norm_num
  · intro k hk hkn
    have hklt : k < n := lt_of_le_of_ne (Finset.mem_Icc.mp hk).2 hkn
    have hpow : n - k ≠ 0 := by omega
    have hz : (1 - 1 : ℝ) ^ (n - k) = 0 := by
      rw [show (1 : ℝ) - 1 = 0 by norm_num]
      exact zero_pow hpow
    calc
      (n.choose k : ℝ) * 1 ^ k * (1 - 1) ^ (n - k) = (n.choose k : ℝ) * 1 ^ k * 0 := by rw [hz]
      _ = 0 := by ring
  · intro hnnotin
    exact False.elim (hnnotin hmem)

/-- BetaHalf, mean side: when `2N ≤ n+1` -/
lemma betaHalf_mean (n N : ℕ) (hN1 : 1 ≤ N) (hNn : N ≤ n) (hSmall : 2 * N ≤ n + 1) :
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x
      ≤ ∫ x in (0 : ℝ)..((N : ℝ) / (n : ℝ)), mass n N x := by
  have hn1 : 1 ≤ n := le_trans hN1 hNn
  have harg : N + (n + 1 - N) - 1 = n := by omega
  have hAb : N ≤ n + 1 - N := by omega
  have hmm := mean_mass_lower N (n + 1 - N) hN1 hAb
  rw [harg] at hmm
  have hnat : N + (n + 1 - N) = n + 1 := by omega
  have hden : (N : ℝ) + (((n + 1 - N : ℕ) : ℝ)) = ((n + 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_add]
    exact_mod_cast hnat
  rw [hden] at hmm
  have hq : 0 ≤ (N : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
  have hNn0 : 0 ≤ (N : ℝ) := by positivity
  have hbp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hbq : 0 < (n : ℝ) := by positivity
  have hqp : (N : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ (N : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ hbp hbq]
    have hmul : (N : ℝ) * (n : ℝ) ≤ (N : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      have h1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
      exact mul_le_mul_of_nonneg_left h1 hNn0
    simpa [Nat.cast_add, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hp1 : (N : ℝ) / (n : ℝ) ≤ 1 := by
    have hNnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    rw [div_le_one hbq]
    exact hNnR
  have hext : ∫ x in (0 : ℝ)..((N : ℝ) / ((n + 1 : ℕ) : ℝ)), mass n N x
      ≤ ∫ x in (0 : ℝ)..((N : ℝ) / (n : ℝ)), mass n N x := by
    exact integral_ge_of_ge_zero n N hq hqp hp1
  exact le_trans hmm hext

/-- `mass n N (1-u) = (1-u)^(N-1) u^(n-N)` -/
lemma mass_comp_sub_one (n N : ℕ) (u : ℝ) : mass n N (1 - u) = (1 - u) ^ (N - 1) * u ^ (n - N) := by
  unfold mass
  have hbase : 1 - (1 - u) = u := by ring
  rw [hbase]

/-- `mass n (n-N+1) u = u^(n-N) (1-u)^(N-1)` for `1 ≤ N ≤ n` -/
lemma mass_compl (n N : ℕ) (hN1 : 1 ≤ N) (hNn : N ≤ n) (u : ℝ) :
    mass n (n - N + 1) u = u ^ (n - N) * (1 - u) ^ (N - 1) := by
  unfold mass
  have h1 : (n - N + 1) - 1 = n - N := by omega
  have h2 : n - (n - N + 1) = N - 1 := by omega
  rw [h1, h2]

/-- BetaHalf, mode side: when `n+1 < 2N` -/
lemma betaHalf_mode (n N : ℕ) (hN1 : 1 ≤ N) (hNn1 : N ≤ n - 1) (hBig : n + 1 < 2 * N) :
    (∫ x in ((N : ℝ) / (n : ℝ))..1, mass n N x) ≤
      (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x := by
  have hn1 : 1 ≤ n := by omega
  let M : ℕ := n - N
  have hM1 : 1 ≤ M := by dsimp [M]; omega
  have hMa : M + 1 ≤ n - M := by dsimp [M]; omega
  have hMle : M ≤ n := by dsimp [M]; omega
  have harg : (M + 1) + (n - M) - 1 = n := by dsimp [M]; omega
  have hmm := half_mass_mode (M + 1) (n - M) (by omega) hMa
  rw [harg] at hmm
  have hmode : modeVal (M + 1) (n - M) = (M : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    unfold modeVal
    have hnum : ↑(M + 1) - 1 = (M : ℝ) := by
      rw [Nat.cast_add]
      norm_num
    have hden : ↑(M + 1) + ↑(n - M) - 2 = ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub hMle]
      rw [show ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num]
      norm_num
      ring
    rw [hnum, hden]
  rw [hmode] at hmm
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hbn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hbn : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hle1 : (M : ℝ) / (n : ℝ) ≤ (M : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    rw [div_le_div_iff₀ hbn hbn1]
    have h1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    exact mul_le_mul_of_nonneg_left h1 hM0
  have hq0 : 0 ≤ (M : ℝ) / (n : ℝ) := by positivity
  have hp1 : (M : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hbn1]
    exact_mod_cast (by dsimp [M]; omega)
  have hext : ∫ x in (0 : ℝ)..((M : ℝ) / (n : ℝ)), mass n (M + 1) x
      ≤ ∫ x in (0 : ℝ)..((M : ℝ) / ((n - 1 : ℕ) : ℝ)), mass n (M + 1) x := by
    exact integral_ge_of_ge_zero n (M + 1) hq0 hle1 hp1
  have hle2 : ∫ x in (0 : ℝ)..((M : ℝ) / (n : ℝ)), mass n (M + 1) x
      ≤ (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n (M + 1) x := by
    exact le_trans hext hmm
  have hqle1 : (N : ℝ) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hbn]
    exact_mod_cast (by omega : N ≤ n)
  have hlim : 1 - (N : ℝ) / (n : ℝ) = (M : ℝ) / (n : ℝ) := by
    have hc : ((n - N : ℕ) : ℝ) = (n : ℝ) - (N : ℝ) := by
      rw [Nat.cast_sub (by omega : N ≤ n)]
    dsimp [M]
    rw [hc]
    field_simp [ne_of_gt hbn]
  have hNn : N ≤ n := by omega
  have hpoint : ∀ u : ℝ, mass n N (1 - u) = mass n (M + 1) u := by
    intro u
    dsimp [M]
    rw [mass_comp_sub_one]
    rw [mass_compl n N hN1 hNn]
    ring
  have h2 : (∫ u in (0 : ℝ)..(1 - (N : ℝ) / (n : ℝ)), mass n N (1 - u))
      = ∫ x in ((N : ℝ) / (n : ℝ))..1, mass n N x := by
    rw [intervalIntegral.integral_comp_sub_left (mass n N) (1 : ℝ)]
    congr 1 <;> ring
  have h3 : (∫ x in ((N : ℝ) / (n : ℝ))..1, mass n N x)
      = ∫ u in (0 : ℝ)..((M : ℝ) / (n : ℝ)), mass n (M + 1) u := by
    have h2' : (∫ x in ((N : ℝ) / (n : ℝ))..1, mass n N x)
        = ∫ u in (0 : ℝ)..(1 - (N : ℝ) / (n : ℝ)), mass n N (1 - u) := h2.symm
    rw [h2']
    rw [hlim]
    refine intervalIntegral.integral_congr ?_
    intro x hx
    exact hpoint x
  have h5 : (∫ x in (0 : ℝ)..1, mass n (M + 1) x) = ∫ x in (0 : ℝ)..1, mass n N x := by
    have hc1 : (∫ x in (0 : ℝ)..1, mass n (M + 1) x)
        = ∫ x in (0 : ℝ)..1, mass n N (1 - x) := by
      refine intervalIntegral.integral_congr ?_
      intro x hx
      exact (hpoint x).symm
    rw [hc1]
    rw [intervalIntegral.integral_comp_sub_left (mass n N) (1 : ℝ)]
    congr 1 <;> ring
  calc
    (∫ x in ((N : ℝ) / (n : ℝ))..1, mass n N x)
        = ∫ u in (0 : ℝ)..((M : ℝ) / (n : ℝ)), mass n (M + 1) u := h3
    _ ≤ (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n (M + 1) x := hle2
    _ = (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x := by rw [h5]
/-- half the total mass lies left of `N/n` -/
lemma betaHalf (n N : ℕ) (hN1 : 1 ≤ N) (hNn : N ≤ n) :
    (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x
      ≤ ∫ x in (0 : ℝ)..((N : ℝ) / (n : ℝ)), mass n N x := by
  by_cases hNn' : N = n
  · subst N
    have hlim : (n : ℝ) / (n : ℝ) = 1 := by
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      exact div_self hn0
    rw [hlim]
    have hnn : 0 ≤ ∫ x in (0 : ℝ)..1, mass n n x := by
      refine integral_nonneg (by norm_num) ?_
      intro x hx
      exact mass_nonneg n n hx.1 hx.2
    nlinarith
  · by_cases hSmall : 2 * N ≤ n + 1
    · exact betaHalf_mean n N hN1 hNn hSmall
    · have hNn1 : N ≤ n - 1 := by omega
      have hBig : n + 1 < 2 * N := by omega
      have hmode := betaHalf_mode n N hN1 hNn1 hBig
      have hsplit : (∫ x in (0 : ℝ)..1, mass n N x)
          = (∫ x in (0 : ℝ)..((N : ℝ) / (n : ℝ)), mass n N x)
            + (∫ x in ((N : ℝ) / (n : ℝ))..1, mass n N x) := by
        exact (integral_add_adjacent_intervals (integrable_mass n N 0 ((N : ℝ) / (n : ℝ)))
          (integrable_mass n N ((N : ℝ) / (n : ℝ)) 1)).symm
      have hfin : (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x
          ≤ ∫ x in (0 : ℝ)..((N : ℝ) / (n : ℝ)), mass n N x := by
        rw [hsplit]
        nlinarith [hmode]
      exact hfin

/-- the mean `np` is a median of the binomial distribution -/
theorem median_lower (n N : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hN : (N : ℝ) ≤ (n : ℝ) * p) :
    (1 / 2 : ℝ) ≤ ∑ k ∈ Finset.Icc N n, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
  by_cases hN0 : N = 0
  · subst N
    have hf := binom_full n p
    rw [hf]
    norm_num
  · have hN1 : 1 ≤ N := by omega
    have hn_ne0 : n ≠ 0 := by
      intro hnz
      have hN0' : (N : ℝ) ≤ 0 := by simpa [hnz] using hN
      have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn_ne0
    have hn1 : 1 ≤ n := hnpos
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hnpos
    have hnp : (n : ℝ) * p < (n : ℝ) := by
      have h := (mul_lt_mul_of_pos_left hp1 hn0)
      simpa using h
    have hNltn : (N : ℝ) < (n : ℝ) := by linarith
    have hNn1 : N ≤ n - 1 := by
      have hNn' : N < n := by exact_mod_cast hNltn
      omega
    have hNn : N ≤ n := by omega
    have hqle : (N : ℝ) / (n : ℝ) ≤ p := by
      rw [div_le_iff₀ hn0]
      simpa [mul_comm] using hN
    have hq0 : 0 ≤ (N : ℝ) / (n : ℝ) := by positivity
    have hq1 : (N : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hn0]
      exact_mod_cast hNn
    have hp1' : p ≤ 1 := le_of_lt hp1
    have hbeta := betaHalf n N hN1 hNn
    have hmono : ∫ x in (0 : ℝ)..((N : ℝ) / (n : ℝ)), mass n N x
        ≤ ∫ x in (0 : ℝ)..p, mass n N x := by
      exact integral_ge_of_ge_zero n N hq0 hqle hp1'
    have hhalf : (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x
        ≤ ∫ x in (0 : ℝ)..p, mass n N x := by
      exact le_trans hbeta hmono
    have hnC : 0 ≤ (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hhalf hnC
    have htail := binTail_integral n N hn1 hN1 hNn p
    have htail1 := binTail_integral n N hn1 hN1 hNn (1 : ℝ)
    have htail1v : binTail n N 1 = 1 := binTail_at_one n N hNn
    have hnC1 : (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) *
          ∫ x in (0 : ℝ)..1, mass n N x = 1 := by
      rw [← htail1, htail1v]
    have hleft : (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) *
          ((1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x) = 1 / 2 := by
      have hcalc : (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) *
            ((1 / 2 : ℝ) * ∫ x in (0 : ℝ)..1, mass n N x)
          = (1 / 2 : ℝ) * ((n : ℝ) * ((n - 1).choose (N - 1) : ℝ) *
              ∫ x in (0 : ℝ)..1, mass n N x) := by ring
      rw [hcalc, hnC1]
      ring
    have hright : (n : ℝ) * ((n - 1).choose (N - 1) : ℝ) *
          ∫ x in (0 : ℝ)..p, mass n N x = binTail n N p := htail.symm
    have hmul' : (1 / 2 : ℝ) ≤ binTail n N p := by
      -- hmul : nC·((1/2)∫₀¹) ≤ nC·∫₀^p:
      rw [hleft, hright] at hmul
      exact hmul
    exact hmul'
