import Mathlib
import Submission.Work.Resample.sliceB1defs

/-!
# The Gaussian tail bound `Work.Resample.buGaussTail`

Outside the window `|h| ≤ m = egM p α = ⌊√p/(2α)⌋ + 1` the weights
`egW s t α ℓ h = exp (-(π α² ((th/s + β_ℓ)² - (β_{ℓ+h})²)))` decay like a Gaussian, and the whole
tail is at most `3·2^{-p}` (for `p ≥ 100`, `α ≥ 2`).

The proof has four independent ingredients, proved above in this file:

* `buQineq` — the pointwise exponent inequality `|h|(|h|-1) ≤ (th/s + β_ℓ)² - (β_{ℓ+h})²` for
  `h ≠ 0`.  It follows by writing `th/s + β_ℓ = β_{ℓ+h} + D` with the *integer*
  `D = ⌊t(ℓ+h)/s + 1/2⌋ - ⌊tℓ/s + 1/2⌋` and using `|D| ≥ |h|` (which holds because `t/s > 1`)
  together with `|β| ≤ 1/2`.  In particular `egW ≤ exp (-(C (|h|² - |h|)))` with `C = π α²`.
* `buTailSumm` — the truncated series over `ℤ` is summable (dominated by a Gaussian).
* `buTailGeom` — the abstract tail estimate: for `C > 0`, `m ≥ 1`, `C(2m+1) ≥ 1` and
  `p log 2 + log (4/3) ≤ C m (m+1)`, `∑'_{|h|>m} exp (-(C (|h|²-|h|))) ≤ 3·2^{-p}`
  (geometric comparison with ratio `ρ = exp (-(C(2m+1))) ≤ 1/2`).
* `egM_numeric` — `α · egM p α ≥ √p/2` and hence `π α² m² ≥ π p/4 > p log 2 + log (4/3)`.

The theorem is then a comparison of `tsum`s: `|egW| = egW`, dominated by the model series.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Resample

open Work.ResMath

/-! ## The pointwise exponent inequality -/

/-- The quadratic inequality driving the Gaussian tail bound: for an integer shift `h ≠ 0` the
exponent increment of the weight `egW` dominates `|h|(|h|-1)`.

Writing `D = ⌊t(ℓ+h)/s + 1/2⌋ - ⌊tℓ/s + 1/2⌋ ∈ ℤ` one has `th/s + β_ℓ = β_{ℓ+h} + D`, so the
difference of the two squares is `D² + 2 D β_{ℓ+h} ≥ D² - |D| ≥ |h|(|h|-1)`, where the last step
uses `|D| ≥ |h|` (true because `t/s > 1`) and `|β| ≤ 1/2`. -/
theorem buQineq (s t : ℕ) (hs : 0 < s) (hst : s < t) (ℓ : Fin s) (h : ℤ) (hh : h ≠ 0) :
    (h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1)
      ≤ ((t : ℝ) * (h : ℝ) / s + Work.ResMath.betaI s t (ℓ : ℤ)) ^ 2
        - (Work.ResMath.betaI s t ((ℓ : ℤ) + h)) ^ 2 := by
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have htR : (s:ℝ) < (t:ℝ) := by exact_mod_cast hst
  set a : ℤ := ⌊(t:ℝ) * (ℓ:ℤ) / s + 1/2⌋ with ha
  set b : ℤ := ⌊(t:ℝ) * (((ℓ:ℤ) + h : ℤ) : ℝ) / s + 1/2⌋ with hb
  have hb1 : Work.ResMath.betaI s t (ℓ:ℤ) = (t:ℝ) * (ℓ:ℤ) / s - (a:ℝ) := by
    simp only [Work.ResMath.betaI]; rw [← ha]
  have hb2 : Work.ResMath.betaI s t ((ℓ:ℤ) + h)
      = (t:ℝ) * (((ℓ:ℤ) + h : ℤ) : ℝ) / s - (b:ℝ) := by
    simp only [Work.ResMath.betaI]; rw [← hb]
  have hkey : (t:ℝ) * (h:ℝ) / s + Work.ResMath.betaI s t (ℓ:ℤ)
      = Work.ResMath.betaI s t ((ℓ:ℤ)+h) + ((b - a : ℤ) : ℝ) := by
    rw [hb1, hb2]; push_cast; ring
  have hmh : (h.natAbs : ℝ) = |(h:ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hD : (h.natAbs : ℝ) ≤ |((b - a : ℤ) : ℝ)| := by
    have hcase : 1 ≤ h ∨ h ≤ -1 := by omega
    rcases hcase with hge | hle
    · have hgeR : (0:ℝ) ≤ (h:ℝ) := by
        have : (0:ℤ) ≤ h := by omega
        exact_mod_cast this
      have harg : (t:ℝ) * (ℓ:ℤ) / s + 1/2 + (t:ℝ) * (h:ℝ) / s
          = (t:ℝ) * (((ℓ:ℤ) + h : ℤ) : ℝ) / s + 1/2 := by push_cast; ring
      have hfloor : a + ⌊(t:ℝ) * (h:ℝ) / s⌋ ≤ b := by
        have h1 := Int.le_floor_add ((t:ℝ) * (ℓ:ℤ) / s + 1/2) ((t:ℝ) * (h:ℝ)/s)
        rw [harg, ← ha, ← hb] at h1
        exact h1
      have hh2 : h ≤ ⌊(t:ℝ) * (h:ℝ) / s⌋ := by
        rw [Int.le_floor, le_div_iff₀ hsR]
        nlinarith [htR, hgeR]
      have hfloorR : (a:ℝ) + (⌊(t:ℝ) * (h:ℝ) / s⌋ : ℝ) ≤ (b:ℝ) := by exact_mod_cast hfloor
      have hh2R : (h:ℝ) ≤ (⌊(t:ℝ) * (h:ℝ) / s⌋ : ℝ) := by exact_mod_cast hh2
      rw [hmh, abs_of_nonneg hgeR]
      have : (h:ℝ) ≤ ((b - a : ℤ) : ℝ) := by push_cast; linarith
      rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ ((b - a : ℤ) : ℝ))]
    · have hltR : (h:ℝ) < 0 := by
        have : h < (0:ℤ) := by omega
        exact_mod_cast this
      have hpos : (0:ℝ) < (-(h:ℝ)) := by linarith
      have harg : (t:ℝ) * (((ℓ:ℤ) + h : ℤ) : ℝ) / s + 1/2 + (t:ℝ) * (-(h:ℝ)) / s
          = (t:ℝ) * (ℓ:ℤ) / s + 1/2 := by push_cast; ring
      have hfloor : b + ⌊(t:ℝ) * (-(h:ℝ)) / s⌋ ≤ a := by
        have h1 := Int.le_floor_add ((t:ℝ) * (((ℓ:ℤ) + h : ℤ) : ℝ) / s + 1/2)
          ((t:ℝ) * (-(h:ℝ))/s)
        rw [harg, ← hb, ← ha] at h1
        exact h1
      have hh2 : -h ≤ ⌊(t:ℝ) * (-(h:ℝ)) / s⌋ := by
        rw [Int.le_floor, le_div_iff₀ hsR]
        rw [show ((-h : ℤ) : ℝ) = -(h:ℝ) by push_cast; ring]
        nlinarith [htR, hpos]
      have hfloorR : (b:ℝ) + (⌊(t:ℝ) * (-(h:ℝ)) / s⌋ : ℝ) ≤ (a:ℝ) := by exact_mod_cast hfloor
      have hh2R : (-(h:ℝ)) ≤ (⌊(t:ℝ) * (-(h:ℝ)) / s⌋ : ℝ) := by
        have : ((-h : ℤ) : ℝ) ≤ ((⌊(t:ℝ) * (-(h:ℝ)) / s⌋ : ℤ) : ℝ) := by exact_mod_cast hh2
        simpa using this
      have hneg : ((b - a : ℤ) : ℝ) ≤ (h:ℝ) := by push_cast; linarith
      rw [hmh, abs_of_neg hltR]
      rw [abs_of_nonpos (by linarith : ((b - a : ℤ) : ℝ) ≤ 0)]
      linarith
  have hQ : ((t:ℝ)*(h:ℝ)/s + Work.ResMath.betaI s t (ℓ:ℤ))^2
        - (Work.ResMath.betaI s t ((ℓ:ℤ)+h))^2
      = ((b - a : ℤ) : ℝ)^2 + 2 * (((b - a : ℤ)) : ℝ) * Work.ResMath.betaI s t ((ℓ:ℤ)+h) := by
    rw [hkey]; ring
  rw [hQ]
  have hβ : |Work.ResMath.betaI s t ((ℓ:ℤ)+h)| ≤ 1/2 := Work.ResMath.betaI_abs_le _ _ _
  have hDnn : (0:ℝ) ≤ |((b - a : ℤ) : ℝ)| := abs_nonneg _
  have hm1 : (1:ℝ) ≤ (h.natAbs : ℝ) := by
    have : (1:ℕ) ≤ h.natAbs := by
      have := Int.natAbs_pos.mpr hh; omega
    exact_mod_cast this
  have h1 : -|((b - a : ℤ) : ℝ)| ≤ 2 * ((b - a : ℤ) : ℝ) * Work.ResMath.betaI s t ((ℓ:ℤ)+h) := by
    have habs : |2 * ((b - a : ℤ) : ℝ) * Work.ResMath.betaI s t ((ℓ:ℤ)+h)|
        ≤ |((b - a : ℤ) : ℝ)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (2:ℝ) by norm_num)]
      nlinarith [hβ, hDnn]
    linarith [neg_abs_le (2 * ((b - a : ℤ) : ℝ) * Work.ResMath.betaI s t ((ℓ:ℤ)+h))]
  have hmul : |((b - a : ℤ) : ℝ)| * (|((b - a : ℤ) : ℝ)| - 1)
      ≤ ((b - a : ℤ) : ℝ)^2 + 2 * ((b - a : ℤ) : ℝ) * Work.ResMath.betaI s t ((ℓ:ℤ)+h) := by
    have hsqa : ((b - a : ℤ) : ℝ)^2 = |((b - a : ℤ) : ℝ)|^2 := (sq_abs _).symm
    rw [hsqa]
    nlinarith [h1, hD, sq_nonneg (|((b - a : ℤ) : ℝ)| - (h.natAbs : ℝ))]
  nlinarith [hmul, hD, hm1, hDnn]

/-! ## Summability of the tail series -/

/-- The truncated Gaussian tail series over `ℤ` is summable: outside the window `|h| ≤ m` the
summand is bounded by a constant multiple of a Gaussian, and Gaussians are summable on `ℤ`
(Mathlib's `HurwitzKernelBounds.summable_f_int`). -/
theorem buTailSumm (C : ℝ) (hC : 0 < C) (m : ℕ) :
    Summable (fun h : ℤ => if m < h.natAbs then
      Real.exp (-(C * ((h.natAbs : ℝ) ^ 2 - (h.natAbs : ℝ)))) else 0) := by
  have hg : Summable (fun h : ℤ => Real.exp (C/2) * Real.exp (-(C/2) * (h:ℝ)^2)) := by
    have ht : 0 < (C/2)/Real.pi := div_pos (by linarith) Real.pi_pos
    have h := (HurwitzKernelBounds.summable_f_int 0 0 ht).mul_left (Real.exp (C/2))
    refine h.congr fun b => ?_
    simp only [HurwitzKernelBounds.f_int, pow_zero, one_mul]
    congr 1
    rw [Real.exp_injective.eq_iff]
    field_simp
    ring
  refine Summable.of_norm_bounded hg (fun h => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
  split_ifs with hh
  · have h1 : (h.natAbs : ℝ) = |(h:ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have hah : (h:ℝ)^2 = ((h.natAbs:ℝ))^2 := by rw [h1, ← sq_abs]
    rw [hah, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((h.natAbs:ℝ) - 1), hC.le]
  · positivity

/-! ## The abstract geometric tail estimate -/

/-- **The Gaussian tail bound.** For `C > 0`, `m ≥ 1` with `1 ≤ C (2m+1)` and
`p log 2 + log (4/3) ≤ C m (m+1)`, the truncated series `∑_{|h| > m} exp (-(C (|h|² - |h|)))` is at
most `3·2^{-p}`.  The tail is a geometric series with ratio `ρ = exp (-(C (2m+1))) ≤ 1/2`; each
side contributes at most `2 A ≤ 2·(3/4)·2^{-p}` with `A = exp (-(C m (m+1)))`. -/
theorem buTailGeom (C : ℝ) (hC : 0 < C) (m p : ℕ) (hm : 1 ≤ m)
    (hrat : 1 ≤ C * (2 * (m : ℝ) + 1))
    (hexp : (p : ℝ) * Real.log 2 + Real.log (4 / 3) ≤ C * (m : ℝ) * ((m : ℝ) + 1)) :
    ∑' h : ℤ, (if m < h.natAbs then Real.exp (-(C * ((h.natAbs : ℝ) ^ 2 - (h.natAbs : ℝ)))) else 0)
      ≤ 3 / (2 : ℝ) ^ p := by
  set F : ℤ → ℝ := fun h => if m < h.natAbs then Real.exp (-(C * ((h.natAbs : ℝ) ^ 2 - (h.natAbs : ℝ)))) else 0 with hF
  set G : ℕ → ℝ := fun n => if m < n then Real.exp (-(C * ((n : ℝ) ^ 2 - (n : ℝ)))) else 0 with hG
  set H : ℕ → ℝ := fun n => if m < n+1 then Real.exp (-(C * (((n+1 : ℕ) : ℝ) ^ 2 - ((n+1 : ℕ) : ℝ)))) else 0 with hH
  set A : ℝ := Real.exp (-(C * (m:ℝ) * ((m:ℝ)+1))) with hAdef
  set ρ : ℝ := Real.exp (-(C * (2*(m:ℝ)+1))) with hρdef
  have hApos : 0 < A := by rw [hAdef]; exact Real.exp_pos _
  have hρpos : 0 < ρ := by rw [hρdef]; exact Real.exp_pos _
  have hρle : ρ ≤ 1/2 := by
    rw [hρdef]
    have h1 : -(C * (2*(m:ℝ)+1)) ≤ -1 := by linarith [hrat]
    have h2 : Real.exp (-(C * (2*(m:ℝ)+1))) ≤ Real.exp (-1) := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-1) ≤ (1/2:ℝ) := by
      rw [Real.exp_neg]
      have h4 : (2:ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
      have h5 : 1 / Real.exp 1 ≤ 1 / (2:ℝ) := one_div_le_one_div_of_le (by norm_num) h4
      simpa [one_div] using h5
    linarith
  have h1mρ : (1/2:ℝ) ≤ 1 - ρ := by linarith
  have hρnorm : ‖ρ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hρpos]; linarith
  have hρsumm : Summable (fun k : ℕ => A * ρ^k) :=
    (summable_geometric_iff_norm_lt_one.mpr hρnorm).mul_left A
  have hρbound : (∑' k : ℕ, A * ρ^k) ≤ 2 * A := by
    have hρtsum : (∑' k : ℕ, A * ρ^k) = A * (1-ρ)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hρnorm]
    rw [hρtsum]
    have h6 : ((1/2:ℝ))⁻¹ = 2 := by norm_num
    have h5 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1/2) h1mρ
    rw [one_div, one_div, h6] at h5
    nlinarith [h5, hApos]
  have hterm : ∀ k : ℕ, Real.exp (-(C * (((k:ℝ) + (m:ℝ) + 1)^2 - ((k:ℝ) + (m:ℝ) + 1)))) ≤ A * ρ^k := by
    intro k
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have hid : ((k:ℝ)+(m:ℝ)+1)^2 - ((k:ℝ)+(m:ℝ)+1)
        = (m:ℝ)*((m:ℝ)+1) + (k:ℝ)*(2*(m:ℝ)+1) + (k:ℝ)^2 := by ring
    rw [hid]
    have harg : -(C * ((m:ℝ)*((m:ℝ)+1) + (k:ℝ)*(2*(m:ℝ)+1) + (k:ℝ)^2))
        ≤ -(C*(m:ℝ)*((m:ℝ)+1)) + (k:ℝ) * (-(C*(2*(m:ℝ)+1))) := by
      nlinarith [hC.le, hk, sq_nonneg (k:ℝ)]
    calc Real.exp (-(C * ((m:ℝ)*((m:ℝ)+1) + (k:ℝ)*(2*(m:ℝ)+1) + (k:ℝ)^2)))
        ≤ Real.exp (-(C*(m:ℝ)*((m:ℝ)+1)) + (k:ℝ) * (-(C*(2*(m:ℝ)+1)))) :=
          Real.exp_le_exp.mpr harg
      _ = Real.exp (-(C*(m:ℝ)*((m:ℝ)+1))) * (Real.exp (-(C*(2*(m:ℝ)+1))))^k := by
          rw [Real.exp_add, Real.exp_nat_mul]
      _ = A * ρ^k := by rw [hAdef, hρdef]
  have hsumm : Summable F := by rw [hF]; exact buTailSumm C hC m
  have hinj2 : Function.Injective (fun n : ℕ => (-(↑n + 1) : ℤ)) := by
    intro a b h; simp only [neg_inj] at h; omega
  have hx : ∀ n : ℕ, (-(↑n+1) : ℤ) = -(↑(n+1)) := by intro n; push_cast; ring
  have hFG : ∀ n : ℕ, F ↑n = G n := by
    intro n
    simp only [hF, hG, Int.natAbs_natCast]
  have hFH : ∀ n : ℕ, F (-(↑n+1)) = H n := by
    intro n
    simp only [hF, hH, hx n, Int.natAbs_neg, Int.natAbs_natCast]
  have hGsumm : Summable G :=
    (hsumm.comp_injective (Nat.cast_injective (R := ℤ))).congr hFG
  have hHsumm : Summable H := (hsumm.comp_injective hinj2).congr hFH
  have hmain1 : (∑' n : ℕ, G n) ≤ ∑' k : ℕ, A * ρ^k := by
    have hfin : (∑ i ∈ Finset.range (m+1), G i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [hG, if_neg (show ¬ (m < i) by omega)]
    rw [← hGsumm.sum_add_tsum_nat_add (m+1), hfin, zero_add]
    have hshift : Summable (fun k : ℕ => G (k + (m+1))) :=
      hGsumm.comp_injective (fun a b h => Nat.add_right_cancel h)
    refine Summable.tsum_le_tsum (fun k => ?_) hshift hρsumm
    simp only [hG, if_pos (show m < k + (m + 1) by omega)]
    push_cast
    rw [show ((k:ℝ) + ((m:ℝ) + 1)) = (k:ℝ) + (m:ℝ) + 1 by ring]
    exact hterm k
  have hmain2 : (∑' n : ℕ, H n) ≤ ∑' k : ℕ, A * ρ^k := by
    have hfin : (∑ i ∈ Finset.range m, H i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [hH, if_neg (show ¬ (m < i+1) by omega)]
    rw [← hHsumm.sum_add_tsum_nat_add m, hfin, zero_add]
    have hshift : Summable (fun k : ℕ => H (k + m)) :=
      hHsumm.comp_injective (fun a b h => Nat.add_right_cancel h)
    refine Summable.tsum_le_tsum (fun k => ?_) hshift hρsumm
    simp only [hH, if_pos (show m < (k + m) + 1 by omega)]
    push_cast
    exact hterm k
  have htotal : (∑' h : ℤ, F h) ≤ 4 * A := by
    have h1 : (∑' n : ℕ, F ↑n) = ∑' n : ℕ, G n := tsum_congr hFG
    have h2 : (∑' n : ℕ, F (-(↑n+1))) = ∑' n : ℕ, H n := tsum_congr hFH
    rw [tsum_of_nat_of_neg_add_one (hsumm.comp_injective (Nat.cast_injective (R := ℤ)))
      (hsumm.comp_injective hinj2), h1, h2]
    linarith [hmain1, hmain2, hρbound]
  have hAfin : 4 * A ≤ 3 / (2:ℝ)^p := by
    have hA : A ≤ (3/4) * ((2:ℝ)^p)⁻¹ := by
      rw [hAdef]
      have h1 : -(C * (m:ℝ) * ((m:ℝ)+1)) ≤ -((p:ℝ)*Real.log 2 + Real.log (4/3)) := by
        linarith [hexp]
      have h2 : Real.exp (-(C * (m:ℝ) * ((m:ℝ)+1)))
          ≤ Real.exp (-((p:ℝ)*Real.log 2 + Real.log (4/3))) := Real.exp_le_exp.mpr h1
      have h3 : Real.exp (-((p:ℝ)*Real.log 2 + Real.log (4/3))) = (3/4) * ((2:ℝ)^p)⁻¹ := by
        rw [show -((p:ℝ)*Real.log 2 + Real.log (4/3)) = -((p:ℝ)*Real.log 2) + -(Real.log (4/3))
              by ring,
            Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_nat_mul,
            Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_log (by norm_num : (0:ℝ) < 4/3)]
        field_simp
      linarith
    rw [div_eq_mul_inv]
    nlinarith [hA]
  linarith [htotal, hAfin]

/-! ## The numeric facts about `egM` -/

/-- The two numeric conditions needed by `buTailGeom` at `C = π α²`, `m = egM p α`:
`1 ≤ π α² (2m+1)` and `p log 2 + log (4/3) ≤ π α² m (m+1)`.
Both follow from `α · egM p α ≥ √p/2` (i.e. `√p < Nat.sqrt p + 1` and the division estimate
`egM p α ≥ (Nat.sqrt p + 1)/(2α)`) and `π/4 > log 2`. -/
theorem egM_numeric (p α : ℕ) (hα : 2 ≤ α) (hp : 100 ≤ p) :
    1 ≤ Real.pi * (α : ℝ) ^ 2 * (2 * (egM p α : ℝ) + 1) ∧
    (p : ℝ) * Real.log 2 + Real.log (4 / 3)
      ≤ Real.pi * (α : ℝ) ^ 2 * (egM p α : ℝ) * ((egM p α : ℝ) + 1) := by
  have hm1 : (1:ℝ) ≤ (egM p α : ℝ) := by
    have : 1 ≤ egM p α := by simp [egM]
    exact_mod_cast this
  have hαR : (2:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
  have hpR : (100:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hαpos : (0:ℝ) < (α:ℝ) := by linarith
  have hα2 : (4:ℝ) ≤ (α:ℝ)^2 := by nlinarith
  have hpi_gt : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
  constructor
  · have h1 : (12:ℝ) ≤ (α:ℝ)^2 * (2 * (egM p α : ℝ) + 1) := by
      have h3 : (3:ℝ) ≤ 2 * (egM p α : ℝ) + 1 := by linarith
      nlinarith [hα2, h3]
    nlinarith [h1, hpi_gt, Real.pi_pos]
  · have hM : (egM p α : ℝ) = ((Nat.sqrt p / (2*α) : ℕ) : ℝ) + 1 := by simp [egM]
    have h2 : Nat.sqrt p % (2*α) < 2*α := Nat.mod_lt _ (by omega)
    have h2R : ((Nat.sqrt p % (2*α) : ℕ) : ℝ) ≤ 2*(α:ℝ) - 1 := by
      have hle : Nat.sqrt p % (2*α) ≤ 2*α - 1 := Nat.le_sub_one_of_lt h2
      have hc : ((Nat.sqrt p % (2*α) : ℕ) : ℝ) ≤ ((2*α - 1 : ℕ) : ℝ) := by exact_mod_cast hle
      have hs : ((2*α - 1 : ℕ) : ℝ) = 2*(α:ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ 2*α by omega)]
        push_cast
        ring
      linarith [hc, hs]
    have hbq : (Nat.sqrt p : ℝ)
        ≤ (2*(α:ℝ)) * ((Nat.sqrt p / (2*α) : ℕ) : ℝ) + (2*(α:ℝ) - 1) := by
      have e3 := congrArg (fun x : ℕ => (x:ℝ)) (Nat.div_add_mod (Nat.sqrt p) (2*α))
      push_cast at e3
      linarith [e3, h2R]
    have hq : ((Nat.sqrt p : ℝ) + 1)/(2*(α:ℝ)) ≤ ((Nat.sqrt p / (2*α) : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(α:ℝ))]
      linarith [hbq]
    have hαM : ((Nat.sqrt p : ℝ) + 1)/2 ≤ (α:ℝ) * (egM p α : ℝ) := by
      rw [hM]
      have heq : (α:ℝ) * (((Nat.sqrt p : ℝ) + 1)/(2*(α:ℝ))) = ((Nat.sqrt p : ℝ) + 1)/2 := by
        field_simp
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg α)
    have hsqrt_lt : Real.sqrt (p:ℝ) < (Nat.sqrt p : ℝ) + 1 := by
      have h : (p:ℝ) < ((Nat.sqrt p : ℝ) + 1)^2 := by
        have h0 := Nat.lt_succ_sqrt p
        have hcast : (p:ℝ) < (((Nat.sqrt p).succ * (Nat.sqrt p).succ : ℕ) : ℝ) := by
          exact_mod_cast h0
        push_cast at hcast
        linarith [hcast]
      calc Real.sqrt (p:ℝ) < Real.sqrt (((Nat.sqrt p:ℝ) + 1)^2) :=
            Real.sqrt_lt_sqrt (by positivity) h
        _ = (Nat.sqrt p : ℝ) + 1 := Real.sqrt_sq (by positivity)
    have hαM2 : (p:ℝ)/4 < (α:ℝ)^2 * (egM p α : ℝ)^2 := by
      have h1 : Real.sqrt (p:ℝ)/2 < (α:ℝ) * (egM p α : ℝ) := by linarith
      have hnn : (0:ℝ) ≤ Real.sqrt (p:ℝ)/2 := by positivity
      have h4 : (Real.sqrt (p:ℝ)/2)^2 < ((α:ℝ) * (egM p α : ℝ))^2 :=
        pow_lt_pow_left₀ h1 hnn (by norm_num)
      have h3 : (Real.sqrt (p:ℝ))^2 = (p:ℝ) := Real.sq_sqrt (Nat.cast_nonneg p)
      have h5 : (Real.sqrt (p:ℝ)/2)^2 = (p:ℝ)/4 := by
        rw [div_pow, h3]; norm_num
      have h6 : ((α:ℝ) * (egM p α : ℝ))^2 = (α:ℝ)^2 * (egM p α : ℝ)^2 := by ring
      linarith [h4, h5, h6]
    have hlog43 : Real.log (4/3) ≤ 1/3 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4/3)
      linarith
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    have hkey : (p:ℝ) * Real.log 2 + Real.log (4/3) ≤ Real.pi * (p:ℝ)/4 := by
      nlinarith [hpR, hlog2, hlog43, hpi_gt]
    have hα2nn : (0:ℝ) ≤ (α:ℝ)^2 := by positivity
    have hMnn : (0:ℝ) ≤ (egM p α : ℝ) := by positivity
    have hstep : Real.pi * (p:ℝ)/4 ≤ Real.pi * ((α:ℝ)^2 * (egM p α : ℝ)^2) := by
      nlinarith [hαM2, Real.pi_pos]
    calc (p:ℝ) * Real.log 2 + Real.log (4/3) ≤ Real.pi * (p:ℝ)/4 := hkey
      _ ≤ Real.pi * ((α:ℝ)^2 * (egM p α : ℝ)^2) := hstep
      _ ≤ Real.pi * (α:ℝ)^2 * (egM p α : ℝ) * ((egM p α : ℝ) + 1) := by
          nlinarith [hα2nn, hMnn, Real.pi_pos]

/-- Gaussian tail bound outside the window `|h| ≤ m = egM p α`.

NOTE (for the prover): the useful exponent inequality is NOT `quad_ineq` (which carries the extra
factor `t/s - 1` and is too weak here) but the estimate
`|h|·(|h|-1) ≤ (t h/s + β_ℓ)² - (β_{ℓ+h})²` for `h ≠ 0` (using `t/s > 1` and `|β| ≤ 1/2`; it also
shows every weight lies in `(0,1)`), together with `α · egM p α ≥ √p / 2` for `p ≥ 25` and
`π/4 > ln 2`. -/
theorem buGaussTail (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p)
    (ℓ : Fin s) :
    ∑' h : ℤ, (if Work.Resample.egM p α < h.natAbs then |Work.Resample.egW s t α (ℓ : ℤ) h| else 0)
      ≤ 3 / (2 : ℝ) ^ p := by
  have hC : 0 < Real.pi * (α:ℝ)^2 := by positivity
  set F : ℤ → ℝ := fun h => if egM p α < h.natAbs then |egW s t α (ℓ : ℤ) h| else 0 with hFdef
  set G : ℤ → ℝ := fun h => if egM p α < h.natAbs then
      Real.exp (-(Real.pi * (α:ℝ)^2 * ((h.natAbs:ℝ)^2 - (h.natAbs:ℝ)))) else 0 with hGdef
  have hsummG : Summable G := by rw [hGdef]; exact buTailSumm _ hC _
  have hpoint : ∀ h : ℤ, F h ≤ G h := by
    intro h
    simp only [hFdef, hGdef]
    by_cases hh : egM p α < h.natAbs
    · rw [if_pos hh, if_pos hh]
      have hne : h ≠ 0 := by
        intro h0
        rw [h0] at hh
        simp [egM] at hh
      have hQ := buQineq s t (by omega) hst ℓ h hne
      have hX : ((h.natAbs:ℝ))^2 - (h.natAbs:ℝ) = (h.natAbs:ℝ) * ((h.natAbs:ℝ) - 1) := by ring
      rw [hX]
      simp only [egW]
      rw [abs_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_exp.mpr
      have hpos : (0:ℝ) ≤ Real.pi * (α:ℝ)^2 := by positivity
      nlinarith [hQ, hpos]
    · rw [if_neg hh, if_neg hh]
  have hsummF : Summable F :=
    Summable.of_nonneg_of_le (g := F) (f := G)
      (fun h => by simp only [hFdef]; split_ifs <;> positivity) hpoint hsummG
  have hle : (∑' h : ℤ, F h) ≤ ∑' h : ℤ, G h := Summable.tsum_le_tsum hpoint hsummF hsummG
  have hnum := egM_numeric p α hα hp
  have hGbound : (∑' h : ℤ, G h) ≤ 3/(2:ℝ)^p := by
    rw [hGdef]
    exact buTailGeom (Real.pi * (α:ℝ)^2) hC (egM p α) p (by simp [egM]) hnum.1 hnum.2
  linarith [hle, hGbound]

end Work.Resample
