import Mathlib
import Submission.Work.Resample.sliceB1defs
import Submission.Work.ResMath.summable_exp_neg_affine_sq

namespace Work.Resample

open HvdH

/-!
# Pointwise decay and summability of the Gaussian weights `egW`

Auxiliary elementary inequalities for the proof of `Work.Resample.egW_decay`.
-/

/-- Wide case: for `τ > 1`, `m ≥ 1`, `|x| ≥ τ m - 1/2` and `|y| ≤ 1/2` one has
`m (m-1) ≤ x² - y²`. -/
lemma key_wide {τ m x y : ℝ} (hτ : 1 < τ) (hm : 1 ≤ m) (hx : τ * m - 1/2 ≤ |x|)
    (hy : |y| ≤ 1/2) : m * (m - 1) ≤ x ^ 2 - y ^ 2 := by
  have hu0 : 0 ≤ τ * m - 1/2 := by nlinarith
  have hx2 : (τ * m - 1/2) ^ 2 ≤ x ^ 2 := by
    have h : (τ * m - 1/2) ^ 2 ≤ |x| ^ 2 := pow_le_pow_left₀ hu0 hx 2
    rwa [sq_abs] at h
  have hy2 : y ^ 2 ≤ 1/4 := by
    have h := pow_le_pow_left₀ (abs_nonneg y) hy 2
    rw [sq_abs] at h
    linarith
  have hpoly : m * (m - 1) ≤ (τ * m - 1/2) ^ 2 - 1/4 := by
    nlinarith [hτ, hm, mul_pos (by linarith : (0:ℝ) < τ - 1) (by nlinarith : (0:ℝ) < (τ+1)*m - 1)]
  linarith

/-- Narrow case, positive shift: `q = x - y ≥ 1`, `x ≥ τ - 1/2`, `y ≥ -1/2`. -/
lemma key_narrow_pos {a τ x y : ℝ} {q : ℤ} (ha : 1 ≤ a) (hθa : 1/a ≤ τ - 1)
    (hq : 1 ≤ q) (hxy : x - y = (q:ℝ)) (hx : τ - 1/2 ≤ x) (hy : -(1/2) ≤ y) :
    2/a ≤ x ^ 2 - y ^ 2 := by
  have ha0 : 0 < a := by linarith
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · have hqR : (q:ℝ) = 1 := by exact_mod_cast hq1.symm
    have hyx : y = x - 1 := by linarith
    have h2 : 2*(τ-1) ≤ x^2 - y^2 := by rw [hyx]; nlinarith
    have h3 : 2/a ≤ 2*(τ-1) := by
      rw [div_le_iff₀ ha0]
      have h1 : 1 ≤ (τ-1)*a := by
        have := mul_le_mul_of_nonneg_right hθa (le_of_lt ha0)
        rwa [div_mul_cancel₀ _ (ne_of_gt ha0)] at this
      linarith
    linarith
  · have hq2R : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
    have hxq : x = (q:ℝ) + y := by linarith
    have h2 : (q:ℝ)^2 - (q:ℝ) ≤ x^2 - y^2 := by
      rw [hxq]; nlinarith [mul_le_mul_of_nonneg_left hy (by linarith : (0:ℝ) ≤ (q:ℝ))]
    have h3 : 2 ≤ (q:ℝ)^2 - (q:ℝ) := by nlinarith
    have h4 : 2/a ≤ 2 := by rw [div_le_iff₀ ha0]; linarith
    linarith

/-- Narrow case, negative shift: `q = x - y ≤ -1`, `x ≤ -(τ - 1/2)`, `y ≤ 1/2`. -/
lemma key_narrow_neg {a τ x y : ℝ} {q : ℤ} (ha : 1 ≤ a) (hθa : 1/a ≤ τ - 1)
    (hq : q ≤ -1) (hxy : x - y = (q:ℝ)) (hx : x ≤ -(τ - 1/2)) (hy : y ≤ 1/2) :
    2/a ≤ x ^ 2 - y ^ 2 := by
  have ha0 : 0 < a := by linarith
  rcases eq_or_lt_of_le hq with hq1 | hq2
  · have hqR : (q:ℝ) = -1 := by exact_mod_cast hq1
    have hyx : y = x + 1 := by linarith
    have h2 : 2*(τ-1) ≤ x^2 - y^2 := by rw [hyx]; nlinarith
    have h3 : 2/a ≤ 2*(τ-1) := by
      rw [div_le_iff₀ ha0]
      have h1 : 1 ≤ (τ-1)*a := by
        have := mul_le_mul_of_nonneg_right hθa (le_of_lt ha0)
        rwa [div_mul_cancel₀ _ (ne_of_gt ha0)] at this
      linarith
    linarith
  · have hq2' : q ≤ -2 := by omega
    have hq2R : (q:ℝ) ≤ -2 := by exact_mod_cast hq2'
    have hxq : x = (q:ℝ) + y := by linarith
    have hq0 : (q:ℝ) ≤ 0 := by linarith
    have h2 : (q:ℝ)^2 + (q:ℝ) ≤ x^2 - y^2 := by
      rw [hxq]; nlinarith [mul_le_mul_of_nonpos_left hy hq0]
    have h3 : 2 ≤ (q:ℝ)^2 + (q:ℝ) := by nlinarith
    have h4 : 2/a ≤ 2 := by rw [div_le_iff₀ ha0]; linarith
    linarith

/-- The tail bound `exp (-(π α² m (m-1))) ≤ exp (-2π m²)` for `|h| = m ≥ 2`, `α ≥ 2`. -/
lemma exp_dom {α : ℕ} (hα : 2 ≤ α) {m : ℝ} (hm : 2 ≤ m) :
    Real.exp (-(Real.pi*(α:ℝ)^2*(m*(m-1)))) ≤ Real.exp (-(2*Real.pi)*m^2) := by
  rw [Real.exp_le_exp]
  have hαR : (2:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
  have hm0 : 0 < m := by linarith
  have h1 : 2*((α:ℝ)^2 - 2) ≤ m*((α:ℝ)^2 - 2) := mul_le_mul_of_nonneg_right hm (by nlinarith)
  have hkey : (α:ℝ)^2 ≤ m*((α:ℝ)^2 - 2) := by nlinarith [h1, sq_nonneg ((α:ℝ)-2), hαR]
  have hnn : 0 ≤ Real.pi*m*((α:ℝ)^2*(m-1) - 2*m) :=
    mul_nonneg (le_of_lt (mul_pos Real.pi_pos hm0)) (by nlinarith [hkey])
  nlinarith [hnn, Real.pi_pos, hm0]

/-- Pointwise decay of the Gaussian weights `egW`.  Write `n = ℓ+h`, `q = rnd(t n/s) - rnd(t ℓ/s) ∈ ℤ`
and `β_n = betaI s t n`; then `t h/s + β_ℓ = q + β_n`, so
`egW s t α ℓ h = exp (-πα²(q² + 2qβ_n)) = exp (-πα² q(q+2β_n))`.
For `h ≥ 1` one has `q ∈ {⌊th/s⌋, ⌊th/s⌋+1}` (from `⌊a+u⌋ = ⌊a⌋ + ⌊{a}+u⌋`), hence
`q ≥ ⌊th/s⌋ ≥ |h|` whenever `|h| ≥ 2` (because `t > s`), and in the only case `q = 1`
(`th/s < 2`), `β_n ≥ th/s - 3/2`, so `q(q+2β_n) ≥ 2(th/s - 1)`.  The mirrored argument
covers `h ≤ -1`, and `|β_n| ≤ 1/2` gives `q(q+2β_n) ≥ |q|(|q|-1)`.  With `α² θ ≥ p/α² > 1`
(where `θ = t/s - 1 ≥ p/α⁴`) this yields exponent `≥ 2π` for `|h| = 1` and
`≥ πα²|h|(|h|-1) ≥ 4π|h|` for `|h| ≥ 2`, whence the pointwise bounds and summability. -/
theorem egW_decay (s t α p : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hαp : α ^ 2 < p)
    (hθ : (p : ℝ) / (α : ℝ) ^ 4 ≤ (t : ℝ) / s - 1) (ℓ : ℤ) :
    (∀ h : ℤ, h ≠ 0 → |Work.Resample.egW s t α ℓ h| ≤
      (if h.natAbs = 1 then Real.exp (-2 * Real.pi)
       else Real.exp (-(Real.pi * (α : ℝ) ^ 2 * ((h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1)))))) ∧
    Summable (fun h : ℤ => Work.Resample.egW s t α ℓ h) := by
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast (by omega : 0 < s)
  have htR : (0:ℝ) < (t:ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hτ : 1 < (t:ℝ)/s := by
    rw [lt_div_iff₀ hsR, one_mul]
    exact_mod_cast hst
  have hαR : (0:ℝ) < (α:ℝ) := by exact_mod_cast (by omega : 0 < α)
  have ha1 : (1:ℝ) ≤ (α:ℝ)^2 := by
    have : (2:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
    nlinarith
  have hθa : 1/(α:ℝ)^2 ≤ (t:ℝ)/s - 1 := by
    have h2 : (1:ℝ) < (p:ℝ)/(α:ℝ)^2 := by
      rw [lt_div_iff₀ (by positivity : (0:ℝ) < (α:ℝ)^2), one_mul]
      exact_mod_cast hαp
    have heq : (p:ℝ)/(α:ℝ)^4 = (p:ℝ)/(α:ℝ)^2/(α:ℝ)^2 := by
      rw [div_div, show (α:ℝ)^2 * (α:ℝ)^2 = (α:ℝ)^4 by ring]
    have h4 : (p:ℝ)/(α:ℝ)^2/(α:ℝ)^2 ≤ (t:ℝ)/s - 1 := heq ▸ hθ
    have h5 : 1/(α:ℝ)^2 < (p:ℝ)/(α:ℝ)^2/(α:ℝ)^2 :=
      div_lt_div_of_pos_right h2 (by positivity)
    linarith
  have hpid : Real.pi * (α:ℝ)^2 * (2/(α:ℝ)^2) = 2*Real.pi := by
    have : (α:ℝ)^2 ≠ 0 := by positivity
    field_simp
  have hpoint : ∀ h : ℤ, h ≠ 0 → |egW s t α ℓ h| ≤
      (if h.natAbs = 1 then Real.exp (-2 * Real.pi)
       else Real.exp (-(Real.pi * (α : ℝ) ^ 2 * ((h.natAbs : ℝ) * ((h.natAbs : ℝ) - 1))))) := by
    intro h hh
    set x : ℝ := (t : ℝ) * (h : ℝ) / (s : ℝ) + Work.ResMath.betaI s t ℓ with hxdef
    set y : ℝ := Work.ResMath.betaI s t (ℓ + h) with hydef
    set q : ℤ := HvdH.rnd ((t : ℝ) * (((ℓ + h : ℤ)) : ℝ) / (s : ℝ)) -
        HvdH.rnd ((t : ℝ) * (ℓ : ℝ) / (s : ℝ)) with hqdef
    have hxyR : x - y = (q : ℝ) := by
      simp only [hxdef, hydef, hqdef]
      simp only [Work.ResMath.betaI, HvdH.rnd]
      have hcast : (t : ℝ) * (((ℓ + h : ℤ)) : ℝ) / (s : ℝ)
          = (t : ℝ) * (ℓ : ℝ) / (s : ℝ) + (t : ℝ) * (h : ℝ) / (s : ℝ) := by push_cast; ring
      rw [hcast]; push_cast; ring
    have hyb : |y| ≤ 1/2 := by rw [hydef]; exact Work.ResMath.betaI_abs_le s t (ℓ + h)
    have hxval : x = (t : ℝ) / (s : ℝ) * (h : ℝ) + Work.ResMath.betaI s t ℓ := by
      rw [hxdef]; ring
    have hW : egW s t α ℓ h = Real.exp (-(Real.pi * (α : ℝ) ^ 2 * (x ^ 2 - y ^ 2))) := by
      rw [egW, ← hxdef, ← hydef]
    have hWpos : 0 ≤ egW s t α ℓ h := by rw [hW]; exact Real.exp_nonneg _
    rw [abs_of_nonneg hWpos, hW]
    by_cases h1 : h.natAbs = 1
    · rw [if_pos h1]
      apply Real.exp_le_exp.mpr
      rcases (Int.natAbs_eq_iff.mp h1) with hh1 | hh1
      · have hxge : (t : ℝ) / s - 1 / 2 ≤ x := by
          simp only [hxval, hh1, Int.cast_one, mul_one]
          have := Work.ResMath.betaI_abs_le s t ℓ
          linarith [neg_abs_le (Work.ResMath.betaI s t ℓ)]
        have hyge : -(1 / 2) ≤ y := by
          have := Work.ResMath.betaI_abs_le s t (ℓ + h)
          rw [hydef]
          linarith [neg_abs_le (Work.ResMath.betaI s t (ℓ + h))]
        have hq1le : (1 : ℤ) ≤ q := by
          have hqposR : (0 : ℝ) < (q : ℝ) := by
            have hyub : y ≤ 1 / 2 := by linarith [le_abs_self y, hyb]
            rw [← hxyR]; linarith
          have hqpos : (0 : ℤ) < q := by exact_mod_cast hqposR
          omega
        have hbnd := key_narrow_pos ha1 hθa hq1le hxyR hxge hyge
        have hmul := mul_le_mul_of_nonneg_left hbnd (by positivity : (0:ℝ) ≤ Real.pi * (α:ℝ)^2)
        rw [hpid] at hmul
        linarith
      · have hxle : x ≤ -((t : ℝ) / s - 1 / 2) := by
          simp only [hxval, hh1, Int.cast_neg, Int.cast_one, mul_neg, mul_one]
          have := Work.ResMath.betaI_abs_le s t ℓ
          linarith [le_abs_self (Work.ResMath.betaI s t ℓ)]
        have hyle : y ≤ 1 / 2 := by linarith [le_abs_self y, hyb]
        have hqneg : q ≤ -1 := by
          have hqnegR : (q : ℝ) < 0 := by
            have hyge : -(1/2:ℝ) ≤ y := by linarith [neg_abs_le y, hyb]
            rw [← hxyR]; linarith
          have : q < 0 := by exact_mod_cast hqnegR
          omega
        have hbnd := key_narrow_neg ha1 hθa hqneg hxyR hxle hyle
        have hmul := mul_le_mul_of_nonneg_left hbnd (by positivity : (0:ℝ) ≤ Real.pi * (α:ℝ)^2)
        rw [hpid] at hmul
        linarith
    · rw [if_neg h1]
      apply Real.exp_le_exp.mpr
      have hm2 : 2 ≤ h.natAbs := by
        have : 0 < h.natAbs := Int.natAbs_pos.mpr hh
        omega
      have hmR : (1:ℝ) ≤ (h.natAbs:ℝ) := by
        have : (1:ℕ) ≤ h.natAbs := by omega
        exact_mod_cast this
      have hxw : (t:ℝ)/s*(h.natAbs:ℝ) - 1/2 ≤ |x| := by
        have hhabs : |(h:ℝ)| = (h.natAbs:ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
        have hA : |(t:ℝ)*(h:ℝ)/(s:ℝ)| = (t:ℝ)/s*(h.natAbs:ℝ) := by
          rw [show (t:ℝ)*(h:ℝ)/(s:ℝ) = (t:ℝ)/s*(h:ℝ) by ring, abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < (t:ℝ)/s), hhabs]
        have hb : |Work.ResMath.betaI s t ℓ| ≤ 1/2 := Work.ResMath.betaI_abs_le s t ℓ
        have htri : |(t:ℝ)*(h:ℝ)/(s:ℝ)| ≤
            |(t:ℝ)*(h:ℝ)/(s:ℝ) + Work.ResMath.betaI s t ℓ| + |Work.ResMath.betaI s t ℓ| := by
          have := abs_add_le ((t:ℝ)*(h:ℝ)/(s:ℝ) + Work.ResMath.betaI s t ℓ)
            (-(Work.ResMath.betaI s t ℓ))
          rwa [add_neg_cancel_right, abs_neg] at this
        have hxabs : |x| = |(t:ℝ)*(h:ℝ)/(s:ℝ) + Work.ResMath.betaI s t ℓ| := by rw [hxdef]
        rw [hA] at htri
        rw [hxabs]
        linarith
      have hbnd := key_wide hτ hmR hxw hyb
      have hmul := mul_le_mul_of_nonneg_left hbnd (by positivity : (0:ℝ) ≤ Real.pi*(α:ℝ)^2)
      linarith
  have hsumm : Summable (fun h : ℤ => Real.exp (-(2 * Real.pi) * (h : ℝ) ^ 2)) :=
    Work.ResMath.summable_exp_neg_mul_sq_int (c := 2 * Real.pi) (by positivity)
  refine ⟨hpoint, Summable.of_norm_bounded hsumm ?_⟩
  intro h
  rw [Real.norm_eq_abs]
  by_cases h0 : h = 0
  · subst h0
    have hz : egW s t α ℓ 0 = 1 := by
      rw [egW]
      have h26 : Work.ResMath.betaI s t (ℓ + 0) = Work.ResMath.betaI s t ℓ := by simp
      rw [show (t:ℝ)*((0:ℤ):ℝ)/(s:ℝ) + Work.ResMath.betaI s t ℓ = Work.ResMath.betaI s t ℓ by simp,
        h26]
      simp
    rw [hz]; simp
  · by_cases h1 : h.natAbs = 1
    · have hp1 := hpoint h h0
      rw [if_pos h1] at hp1
      have habs : (h:ℝ)^2 = 1 := by
        have hh : (h.natAbs:ℝ) = |(h:ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        have h1' : (h.natAbs:ℝ) = 1 := by rw [h1]; norm_num
        calc (h:ℝ)^2 = |(h:ℝ)|^2 := (sq_abs _).symm
          _ = (h.natAbs:ℝ)^2 := by rw [hh]
          _ = 1 := by rw [h1']; norm_num
      rw [habs, mul_one, ← neg_mul]
      exact hp1
    · have hp1 := hpoint h h0
      rw [if_neg h1] at hp1
      have hm2 : 2 ≤ h.natAbs := by
        have : 0 < h.natAbs := Int.natAbs_pos.mpr h0
        omega
      have hmR : (2:ℝ) ≤ (h.natAbs:ℝ) := by exact_mod_cast hm2
      have hdom := exp_dom hα hmR
      have hsq : (h.natAbs:ℝ)^2 = (h:ℝ)^2 := by
        have hh : (h.natAbs:ℝ) = |(h:ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
        rw [hh, sq_abs]
      rw [hsq] at hdom
      linarith [hp1, hdom]

end Work.Resample
