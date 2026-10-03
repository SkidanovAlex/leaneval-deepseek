import Mathlib
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.JacTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary half-integer arithmetic -/

/-- For odd `n`, `2 * ((n-1)/2) = n - 1`. -/
private lemma half_two_mul {n : ℤ} (hn : Odd n) : 2 * ((n - 1) / 2) = n - 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show (2*k+1-1 : ℤ) = 2*k by ring, Int.mul_ediv_cancel_left _ (by norm_num)]

/-- For odd `x, y`, `((xy-1)/2) = 2*(((x-1)/2)*((y-1)/2)) + (x-1)/2 + (y-1)/2`. -/
private lemma half_mul_half {x y : ℤ} (hx : Odd x) (hy : Odd y) :
    ((x * y - 1) / 2) = 2 * ((x - 1) / 2 * ((y - 1) / 2)) + (x - 1) / 2 + (y - 1) / 2 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  have e1 : (2*a+1-1 : ℤ) / 2 = a := by
    rw [show (2*a+1-1 : ℤ) = 2*a by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  have e2 : (2*b+1-1 : ℤ) / 2 = b := by
    rw [show (2*b+1-1 : ℤ) = 2*b by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  have e3 : ((2*a+1)*(2*b+1)-1 : ℤ) / 2 = 2*(a*b) + a + b := by
    rw [show ((2*a+1)*(2*b+1)-1 : ℤ) = 2*(2*(a*b)+a+b) by ring,
      Int.mul_ediv_cancel_left _ (by norm_num)]
  rw [e1, e2, e3]

/-- For odd `x, y` with `x ≡ y (mod 4)`, the halves `(x-1)/2`, `(y-1)/2` have the same parity. -/
private lemma half_sub_half_even {x y : ℤ} (hx : Odd x) (hy : Odd y) (h : x % 4 = y % 4) :
    Even ((x - 1) / 2 - (y - 1) / 2) := by
  have h4 : (x - y) % 4 = 0 := (Int.emod_eq_emod_iff_emod_sub_eq_zero (n := 4)).mp h
  obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero h4
  have hx1 : x - 1 = (y - 1) + 2 * (2 * t) := by omega
  rw [hx1, Int.add_mul_ediv_left _ _ (by norm_num : (2:ℤ) ≠ 0)]
  exact ⟨t, by ring⟩

/-- The square of an odd integer is `1` modulo `8`. -/
private lemma eight_dvd_sq_sub_one {x : ℤ} (hx : Odd x) : (8:ℤ) ∣ x^2 - 1 := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨w, hw⟩ := Int.even_mul_succ_self t
  refine ⟨w, ?_⟩
  linear_combination 4 * hw

/-! ## 2. The `χ₈` factor -/

/-- `χ₈(1 - 4k) = (-1)^k`. -/
private lemma chi8_one_sub_four (k : ℤ) :
    ZMod.χ₈ ((1 - 4*k : ℤ) : ZMod 8) = ((Int.negOnePow k : ℤˣ) : ℤ) := by
  have key : ((1 - 4*k : ℤ) : ZMod 8) = (if k % 2 = 0 then (1 : ZMod 8) else 5) := by
    rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h | h
    · rw [if_pos h]
      have h2 : ((1 - 4*k : ℤ) : ZMod 8) = (((1:ℤ)) : ZMod 8) := by
        rw [show (1 - 4*k : ℤ) = 1 + 8 * (-(k/2)) by omega]
        rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
        exact ⟨k/2, by ring⟩
      simpa using h2
    · rw [if_neg (by omega)]
      have h2 : ((1 - 4*k : ℤ) : ZMod 8) = (((5:ℤ)) : ZMod 8) := by
        rw [show (1 - 4*k : ℤ) = 5 + 8 * (-((k+1)/2)) by omega]
        rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
        exact ⟨(k+1)/2, by ring⟩
      simpa using h2
  rw [key]
  by_cases h : k % 2 = 0
  · rw [if_pos h]
    have : Int.negOnePow k = 1 := Int.negOnePow_even k (Int.even_iff.mpr h)
    rw [this]; decide
  · rw [if_neg h]
    have : Int.negOnePow k = -1 := Int.negOnePow_odd k (Int.odd_iff.mpr (by omega))
    rw [this]; decide

/-- **The `χ₈` factor of (★).**  For odd `u, r₁`, even `v₁, s` and `m = u r₁ - v₁ s`,
`χ₈(m r₁ u) = (-1)^{v₁ s/4}`. -/
private lemma chi8_part (u v₁ r₁ s m : ℤ) (hu : Odd u) (hr₁ : Odd r₁) (hv₁ : Even v₁)
    (hs : Even s) (hm : m = u * r₁ - v₁ * s) :
    ZMod.χ₈ ((m * r₁ * u : ℤ) : ZMod 8) = ((Int.negOnePow ((v₁ * s) / 4) : ℤˣ) : ℤ) := by
  set K : ℤ := (v₁ * s) / 4 with hKdef
  have h4 : (4:ℤ) ∣ v₁ * s := by
    obtain ⟨a, ha⟩ := hv₁; obtain ⟨b, hb⟩ := hs
    exact ⟨a*b, by rw [ha, hb]; ring⟩
  have hK4 : K * 4 = v₁ * s := by rw [hKdef]; exact Int.ediv_mul_cancel h4
  have hkey : ((m*r₁*u : ℤ) : ZMod 8) = ((1 - 4*((u*r₁)*K) : ℤ) : ZMod 8) := by
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
    obtain ⟨w, hw⟩ := eight_dvd_sq_sub_one (hu.mul hr₁)
    refine ⟨-w, ?_⟩
    rw [hm, ← hK4]
    linear_combination -hw
  rw [hkey, chi8_one_sub_four]
  have hev : Even ((u*r₁) * K - K) := by
    have : (u*r₁) * K - K = (u*r₁ - 1) * K := by ring
    rw [this]
    exact (hu.mul hr₁).sub_odd odd_one |>.mul_right _
  exact congrArg (fun u : ℤˣ => (u : ℤ)) ((Int.negOnePow_eq_iff _ _).mpr hev)

/-- `((-1)^K)^α = (-1)^{αK}`. -/
private lemma negOnePow_pow (K : ℤ) (α : ℕ) :
    (Int.negOnePow K : ℤˣ) ^ α = Int.negOnePow ((α : ℤ) * K) := by
  rw [show (Int.negOnePow K : ℤˣ) = (-1:ℤˣ)^K from rfl,
    show Int.negOnePow ((α : ℤ) * K) = (-1:ℤˣ)^((α : ℤ) * K) from rfl,
    zpow_mul', zpow_natCast]

/-- Integer form of `negOnePow_pow`. -/
private lemma pow_part (K : ℤ) (α : ℕ) :
    (((Int.negOnePow K : ℤˣ) : ℤ)) ^ α = ((Int.negOnePow ((α : ℤ) * K) : ℤˣ) : ℤ) := by
  rw [← Units.val_pow_eq_pow_val]
  exact congrArg (fun u : ℤˣ => (u : ℤ)) (negOnePow_pow K α)

/-! ## 3. The reciprocity sign `(-1)^{((r₁-1)/2)((m-1)/2)+((|r₁|-1)/2)}` -/

/-- The reciprocity sign: replacing `(m-1)/2` by `(u-1)/2 + (r₁-1)/2` (mod `2`). -/
private lemma h2_part (u r₁ m : ℤ) (hu : Odd u) (hr₁ : Odd r₁) (hm : Odd m)
    (h4m : (4:ℤ) ∣ m - u*r₁) :
    Even ((r₁ - 1) / 2 * ((m - 1) / 2) - ((u - 1) / 2 * ((r₁ - 1) / 2) + (r₁ - 1) / 2)) := by
  have hm4 : m % 4 = (u*r₁) % 4 :=
    (Int.emod_eq_emod_iff_emod_sub_eq_zero (n := 4)).mpr (Int.emod_eq_zero_of_dvd h4m)
  have h1 : Even ((m - 1)/2 - ((u*r₁) - 1)/2) := half_sub_half_even hm (hu.mul hr₁) hm4
  have h2id : ((u*r₁) - 1)/2 = 2 * ((u-1)/2 * ((r₁-1)/2)) + (u-1)/2 + (r₁-1)/2 :=
    half_mul_half hu hr₁
  have heq : (m - 1)/2 - ((u*r₁) - 1)/2
      = (m-1)/2 - (u-1)/2 - (r₁-1)/2 - 2*((u-1)/2*((r₁-1)/2)) := by
    rw [h2id]; ring
  rw [heq] at h1
  rw [show (r₁-1)/2 * ((m-1)/2) - ((u-1)/2*((r₁-1)/2) + (r₁-1)/2)
        = (r₁-1)/2 * ((m-1)/2 - (u-1)/2 - 1) by ring]
  have hB : Even ((m-1)/2 - (u-1)/2 - 1 - ((r₁-1)/2 - 1) - 2*((u-1)/2*((r₁-1)/2))) := by
    rw [show (m-1)/2 - (u-1)/2 - 1 - ((r₁-1)/2 - 1) - 2*((u-1)/2*((r₁-1)/2))
        = (m-1)/2 - (u-1)/2 - (r₁-1)/2 - 2*((u-1)/2*((r₁-1)/2)) by ring]
    exact h1
  obtain ⟨x, hx⟩ := hB
  obtain ⟨y, hy⟩ := Int.even_mul_succ_self ((r₁-1)/2 - 1)
  refine ⟨(r₁-1)/2 * x + (r₁-1)/2*((u-1)/2*((r₁-1)/2)) + y, ?_⟩
  have hB' : (m-1)/2 - (u-1)/2 - 1
      = ((r₁-1)/2 - 1) + (2*x + 2*((u-1)/2*((r₁-1)/2))) := by omega
  rw [hB', mul_add, show (r₁-1)/2 * ((r₁-1)/2 - 1) = y + y from by rw [← hy]; ring]
  ring

/-! ## 4. The Hilbert symbols -/

/-- `HilbertInf x y = (-1)^{[x<0][y<0]}`. -/
private lemma hilbertInf_eq_negOnePow (x y : ℤ) :
    HilbertInf x y = ((Int.negOnePow (negI x * negI y) : ℤˣ) : ℤ) := by
  rw [hilbertInf_eq_negI]
  rcases (by unfold negI; split <;> simp : negI x = 0 ∨ negI x = 1) with h | h <;>
    rcases (by unfold negI; split <;> simp : negI y = 0 ∨ negI y = 1) with h' | h' <;>
    rw [h, h'] <;> norm_num

/-- Two-fold product of `negOnePow`s. -/
private lemma negOnePow_prod2 (p q : ℤ) :
    ((Int.negOnePow p : ℤˣ) : ℤ) * ((Int.negOnePow q : ℤˣ) : ℤ)
      = ((Int.negOnePow (p + q) : ℤˣ) : ℤ) := by
  rw [← Units.val_mul, ← Int.negOnePow_add]

/-- Four-fold product of `negOnePow`s. -/
private lemma negOnePow_prod4 (p q r t : ℤ) :
    ((Int.negOnePow p : ℤˣ) : ℤ) * ((Int.negOnePow q : ℤˣ) : ℤ)
      * ((Int.negOnePow r : ℤˣ) : ℤ) * ((Int.negOnePow t : ℤˣ) : ℤ)
      = ((Int.negOnePow (p + q + r + t) : ℤˣ) : ℤ) := by
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul,
      ← Int.negOnePow_add, ← Int.negOnePow_add, ← Int.negOnePow_add]

/-- Three-fold product of `negOnePow`s. -/
private lemma negOnePow_prod3 (p q r : ℤ) :
    ((Int.negOnePow p : ℤˣ) : ℤ) * ((Int.negOnePow q : ℤˣ) : ℤ) * ((Int.negOnePow r : ℤˣ) : ℤ)
      = ((Int.negOnePow (p + q + r) : ℤˣ) : ℤ) := by
  rw [← Units.val_mul, ← Units.val_mul, ← Int.negOnePow_add, ← Int.negOnePow_add]

/-- **The Hilbert product** `(r₁,m)_∞(v₁,m)_∞(v₁,r₁)_∞(u,v₁)_∞` of (★). -/
private lemma hilbert_part (u v₁ r₁ m : ℤ) :
    HilbertInf r₁ m * HilbertInf v₁ m * HilbertInf v₁ r₁ * HilbertInf u v₁
      = ((Int.negOnePow (negI r₁ * negI m + negI v₁ * negI m + negI v₁ * negI r₁
          + negI u * negI v₁) : ℤˣ) : ℤ) := by
  rw [hilbertInf_eq_negOnePow, hilbertInf_eq_negOnePow, hilbertInf_eq_negOnePow,
      hilbertInf_eq_negOnePow, negOnePow_prod4]

/-- `(x,y)_∞` depends only on the signs of `x` and `y`. -/
private lemma hilbertInf_eq_of_neg_iff {x x' y y' : ℤ} (hx : x < 0 ↔ x' < 0)
    (hy : y < 0 ↔ y' < 0) : HilbertInf x y = HilbertInf x' y' := by
  have h : (x < 0 ∧ y < 0) ↔ (x' < 0 ∧ y' < 0) := and_congr hx hy
  unfold HilbertInf
  by_cases hh : x < 0 ∧ y < 0
  · rw [if_pos hh, if_pos (h.mp hh)]
  · rw [if_neg hh, if_neg (fun h' => hh (h.mpr h'))]

private lemma hilbertInf_pos_mul (c x y : ℤ) (hc : 0 < c) :
    HilbertInf (c * x) y = HilbertInf x y := by
  refine hilbertInf_eq_of_neg_iff ?_ Iff.rfl
  constructor <;> intro h <;> nlinarith

private lemma hilbertInf_pos_mul_right (c x y : ℤ) (hc : 0 < c) :
    HilbertInf x (c * y) = HilbertInf x y := by
  refine hilbertInf_eq_of_neg_iff Iff.rfl ?_
  constructor <;> intro h <;> nlinarith

/-! ## 5. The quadrant sign `ε` -/

/-- **The quadrant sign** `ε` of (★), as a `(-1)`-power. -/
private lemma multEps_part (u v₁ r₁ s ρ m : ℤ) (hρ : 0 < ρ) (hv₁0 : v₁ ≠ 0) (hr₁0 : r₁ ≠ 0)
    (hm : m = u * r₁ - v₁ * s) :
    MultEps (⟨u, ρ * v₁⟩ : GaussianInt) ⟨ρ * r₁, s⟩
      = ((Int.negOnePow (negI u * negI v₁
          + (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁)) : ℤˣ) : ℤ) := by
  have hcond : (u * (ρ * r₁) > (ρ * v₁) * s) ↔ 0 < m := by
    rw [hm]; constructor <;> intro h <;> nlinarith
  show (if u * (ρ * r₁) > (ρ * v₁) * s then HilbertInf u (ρ*v₁) * HilbertInf (ρ*r₁) (-(ρ*v₁))
        else HilbertInf u (ρ*v₁) * HilbertInf (-(ρ*r₁)) (ρ*v₁))
      = ((Int.negOnePow (negI u * negI v₁
          + (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁)) : ℤˣ) : ℤ)
  by_cases h : 0 < m
  · rw [if_pos (hcond.mpr h), if_pos h]
    rw [hilbertInf_pos_mul_right ρ u v₁ hρ,
        show -(ρ * v₁) = ρ * (-v₁) by ring,
        hilbertInf_pos_mul_right ρ (ρ*r₁) (-v₁) hρ,
        hilbertInf_pos_mul ρ r₁ (-v₁) hρ,
        hilbertInf_eq_negOnePow, hilbertInf_eq_negOnePow, negI_neg hv₁0, negOnePow_prod2]
  · rw [if_neg (fun hc => h (hcond.mp hc)), if_neg h]
    rw [show -(ρ * r₁) = ρ * (-r₁) by ring,
        hilbertInf_pos_mul_right ρ (ρ * -r₁) v₁ hρ,
        hilbertInf_pos_mul ρ (-r₁) v₁ hρ,
        hilbertInf_pos_mul_right ρ u v₁ hρ,
        hilbertInf_eq_negOnePow, hilbertInf_eq_negOnePow, negI_neg hr₁0, negOnePow_prod2]

/-! ## 6. The multiplier exponent `θ = ((u-1)(ρr₁-1) - ρv₁s)/4 - (u-1)/2·(ρ-1)/2` -/

private lemma negOnePow_mul_odd (ρ Z : ℤ) (hρ : Odd ρ) :
    (Int.negOnePow (ρ * Z) : ℤˣ) = (Int.negOnePow Z : ℤˣ) := by
  rw [Int.negOnePow_eq_iff]
  have : ρ * Z - Z = (ρ - 1) * Z := by ring
  rw [this]
  exact (hρ.sub_odd odd_one).mul_right _

/-- **The multiplier exponent**: `θ = ρ·((u-1)/2·(r₁-1)/2 - v₁s/4)`. -/
private lemma E_part (u r₁ s v₁ ρ : ℤ) (hu : Odd u) (hr₁ : Odd r₁) (hρodd : Odd ρ)
    (hv₁ : Even v₁) (hs : Even s) :
    ((Int.negOnePow (((u - 1) * (ρ * r₁ - 1) - (ρ * v₁) * s) / 4
        - (u - 1) / 2 * ((ρ - 1) / 2)) : ℤˣ) : ℤ)
      = ((Int.negOnePow ((u - 1) / 2 * ((r₁ - 1) / 2) - (v₁ * s) / 4) : ℤˣ) : ℤ) := by
  set a : ℤ := (u - 1) / 2 with ha
  set b : ℤ := (ρ * r₁ - 1) / 2 with hb
  set c : ℤ := (ρ - 1) / 2 with hc
  set ar : ℤ := (r₁ - 1) / 2 with har
  set K : ℤ := (v₁ * s) / 4 with hK
  have hu1 : 2 * a = u - 1 := by rw [ha]; exact half_two_mul hu
  have hb1 : 2 * b = ρ * r₁ - 1 := by
    rw [hb, mul_comm 2]
    exact Int.ediv_mul_cancel (even_iff_two_dvd.mp ((hρodd.mul hr₁).sub_odd odd_one))
  have hc1 : 2 * c = ρ - 1 := by rw [hc]; exact half_two_mul hρodd
  have har1 : 2 * ar = r₁ - 1 := by rw [har]; exact half_two_mul hr₁
  have hK4 : v₁ * s = 4 * K := by
    rw [hK]
    have h4 : (4:ℤ) ∣ v₁ * s := by
      obtain ⟨x, hx⟩ := hv₁; obtain ⟨y, hy⟩ := hs
      exact ⟨x*y, by rw [hx, hy]; ring⟩
    linarith [Int.ediv_mul_cancel h4]
  have hsub : ((u - 1) * (ρ * r₁ - 1) - (ρ * v₁) * s) / 4 = a * b - ρ * K := by
    apply Int.ediv_eq_of_eq_mul_right (by norm_num : (4:ℤ) ≠ 0)
    rw [show (ρ*v₁)*s = ρ*(v₁*s) by ring, hK4, ← hu1, ← hb1]
    ring
  have hC : b = ρ * ar + c := by
    apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2:ℤ) ≠ 0)
    rw [show ρ*r₁ - 1 = ρ*(r₁-1) + (ρ-1) by ring, ← har1, ← hc1]
    ring
  have hexp : a * b - ρ * K - a * c = ρ * (a * ar - K) := by rw [hC]; ring
  rw [hsub, hexp]
  exact congrArg (fun x : ℤˣ => (x : ℤ)) (negOnePow_mul_odd ρ (a * ar - K) hρodd)

/-! ## 7. The three parity claims -/

/-- `(α+1)·(v₁s/4)` is even, because `α` is the exact `2`-adic valuation of `v₁`. -/
private lemma claimA (v₁ s v' : ℤ) (α : ℕ) (hv₁ : Even v₁) (hs : Even s)
    (hα : v₁ = 2^α * v') (hv' : Odd v') : Even (((α : ℤ) + 1) * ((v₁ * s) / 4)) := by
  have hK : (v₁ * s) / 4 = (v₁/2) * (s/2) := by
    obtain ⟨a, ha⟩ := even_iff_two_dvd.mp hv₁
    obtain ⟨b, hb⟩ := even_iff_two_dvd.mp hs
    rw [ha, hb, show (2*a)*(2*b) = 4*(a*b) by ring]
    rw [Int.mul_ediv_cancel_left (a*b) (by norm_num : (4:ℤ) ≠ 0)]
    rw [Int.mul_ediv_cancel_left a (by norm_num : (2:ℤ) ≠ 0),
        Int.mul_ediv_cancel_left b (by norm_num : (2:ℤ) ≠ 0)]
  rcases α with _ | _ | k
  · exfalso
    have h : v₁ = v' := by simpa using hα
    exact (Int.not_even_iff_odd.mpr hv') (h ▸ hv₁)
  · rw [hK]; exact ⟨(v₁/2)*(s/2), by ring⟩
  · rw [hK]
    have h4 : (4:ℤ) ∣ v₁ := by
      refine ⟨2^k * v', ?_⟩
      rw [hα]; ring
    obtain ⟨t, ht⟩ := h4
    have hvt : v₁ / 2 = 2*t := by omega
    rw [hvt]
    exact ⟨(((k+1+1 : ℕ) : ℤ) + 1) * t * (s/2), by ring⟩

/-- `(r₁-1)/2 + (|r₁|-1)/2 ≡ [r₁ < 0]` (mod `2`). -/
private lemma claimB (r₁ : ℤ) (hr₁ : Odd r₁) :
    Even ((r₁-1)/2 + ((r₁.natAbs : ℤ) - 1)/2 - negI r₁) := by
  obtain ⟨t, rfl⟩ := hr₁
  have e1 : (2*t+1-1 : ℤ)/2 = t := by
    rw [show (2*t+1-1 : ℤ) = 2*t by ring, Int.mul_ediv_cancel_left _ (by norm_num)]
  rcases lt_trichotomy t 0 with h | h | h
  · have hnat : ((2*t+1).natAbs : ℤ) = -(2*t+1) := by
      rw [← Int.natAbs_neg (2*t+1), Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ -(2*t+1))]
    have e3 : (-(2*t+1) - 1 : ℤ)/2 = -(t+1) := by
      rw [show (-(2*t+1)-1 : ℤ) = 2*(-(t+1)) by ring,
        Int.mul_ediv_cancel_left _ (by norm_num)]
    rw [e1, hnat, e3, negI, if_pos (by omega)]
    exact ⟨-1, by ring⟩
  · rw [h]; norm_num [negI]
  · have hnat : ((2*t+1).natAbs : ℤ) = 2*t+1 := by
      rw [Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ 2*t+1)]
    rw [e1, hnat, e1, negI, if_neg (by omega)]
    exact ⟨t, by ring⟩

/-- The bookkeeping identity between the Hilbert product and the quadrant sign. -/
private lemma claimC (u v₁ r₁ m : ℤ) (hv₁ : v₁ ≠ 0) (hr₁ : r₁ ≠ 0) (hm0 : m ≠ 0) :
    Even (negI r₁ * negI m + negI v₁ * negI m + negI v₁ * negI r₁ + negI u * negI v₁
      - (negI u * negI v₁
          + (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁))
      - negI r₁) := by
  have hif : (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁)
      = (1 - negI m) * (negI r₁ * (1 - negI v₁)) + negI m * ((1 - negI r₁) * negI v₁) := by
    by_cases h : 0 < m
    · have hm : negI m = 0 := by unfold negI; rw [if_neg (by omega : ¬ m < 0)]
      rw [if_pos h, hm]; ring
    · have hm : negI m = 1 := by unfold negI; rw [if_pos (by omega : m < 0)]
      rw [if_neg h, hm]; ring
  rw [hif]
  refine ⟨negI r₁ * negI m + negI v₁ * negI r₁ - negI r₁, ?_⟩
  ring

/-- **(★) the 2-adic core of the Jacobi–Kubota multiplier rule (20.4).**

Let `u` be odd, `v₁ ≠ 0` even, `r₁` odd, `s` even, `ρ > 0` odd, `v₁ = 2^α v'` with `v'` odd,
`m = u r₁ - v₁ s`, and let `(u,v₁) = (v₁,r₁) = 1`.  Then

`χ₈(m r₁ u)^α · (-1)^{(r₁-1)/2·(m-1)/2 + (|r₁|-1)/2} · (r₁,m)_∞(v',m)_∞(v',r₁)_∞(u,v')_∞
   = ε · (-1)^{((u-1)(ρr₁-1) - ρv₁s)/4 - (u-1)/2·(ρ-1)/2}`

where `ε = ε(w,z) = MultEps w z` is the quadrant sign (20.5)/(20.6) for `w = u + iρv₁`,
`z = ρr₁ + is`, and `(x,y)_∞ = HilbertInf x y` is the Hilbert symbol at `∞` (17.7).

This is the arithmetic content of (20.4) after all the *odd* Jacobi symbols have been paired off
by quadratic reciprocity: the left side collects the three factors involving `χ₈` (from peeling
the powers of `2` off `v₁`) and the two reciprocity signs, the right side the quadrant sign `ε`
and the exponent `θ = ν' - e` of the multiplier.  Every quantity is a `±1` depending only on
`(u,v₁,r₁,s,ρ,m)` mod 8 and their signs.  Verified exhaustively in Python (primary `w`,
primitive `z ≡ 1 (mod 2)`, coordinates in `[-13,13]`, 22200 cases, and by the reviewers with
much larger ranges): no counterexample.

Suggestion for the proof: the identity is a case analysis on the signs of `u,v₁,r₁,m` and the
residues of `u,v₁,r₁,s,ρ,m` mod 8; each factor is a `±1` determined by that data.  Useful
pieces: `ZMod.χ₈_int_eq_if_mod_eight`, `ZMod.χ₄_int_eq_if_mod_four`,
`Int.negOnePow_eq_iff` (`a.negOnePow = b.negOnePow ↔ Even (a-b)`), `Int.negOnePow_mul_self`,
`hilbertInf_eq_negI`, `negI_mul` (all in `JacTools`), together with
`m * r₁ * u ≡ 1 - u * r₁ * v₁ * s (mod 8)`. -/
theorem star_identity (u v₁ r₁ s v' : ℤ) (α : ℕ) (ρ m : ℤ)
    (hu : Odd u) (hv₁ : Even v₁) (hv₁0 : v₁ ≠ 0) (hα : v₁ = 2 ^ α * v')
    (hv' : Odd v') (hr₁ : Odd r₁) (hs : Even s) (hρ : 0 < ρ) (hρodd : Odd ρ)
    (hm : m = u * r₁ - v₁ * s) (hcv : IsCoprime u v₁) (hcr : IsCoprime v₁ r₁) :
    (ZMod.χ₈ ((m * r₁ * u : ℤ) : ZMod 8) : ℤ) ^ α
        * ((Int.negOnePow ((r₁ - 1) / 2 * ((m - 1) / 2) + ((r₁.natAbs : ℤ) - 1) / 2) : ℤˣ) : ℤ)
        * (HilbertInf r₁ m * HilbertInf v' m * HilbertInf v' r₁ * HilbertInf u v')
      = (MultEps (⟨u, ρ * v₁⟩ : GaussianInt) ⟨ρ * r₁, s⟩ : ℤ)
        * ((Int.negOnePow (((u - 1) * (ρ * r₁ - 1) - (ρ * v₁) * s) / 4
              - (u - 1) / 2 * ((ρ - 1) / 2)) : ℤˣ) : ℤ) := by
  have h4vs : (4:ℤ) ∣ v₁ * s := by
    obtain ⟨x, hx⟩ := hv₁; obtain ⟨y, hy⟩ := hs
    exact ⟨x*y, by rw [hx, hy]; ring⟩
  have h4m : (4:ℤ) ∣ m - u * r₁ := by
    rw [hm]
    obtain ⟨w, hw⟩ := h4vs
    exact ⟨-w, by linear_combination -hw⟩
  have hm_odd : Odd m := by
    rw [hm]; exact (hu.mul hr₁).sub_even (hv₁.mul_right s)
  have hm0 : m ≠ 0 := by rintro rfl; norm_num at hm_odd
  have hr₁0 : r₁ ≠ 0 := by rintro rfl; norm_num at hr₁
  have hsign : (v' < 0) ↔ (v₁ < 0) := by
    have hpos : (0:ℤ) < 2^α := by positivity
    rw [hα]; constructor <;> intro h <;> nlinarith
  have hB : ((Int.negOnePow ((r₁ - 1) / 2 * ((m - 1) / 2)
          + ((r₁.natAbs : ℤ) - 1) / 2) : ℤˣ) : ℤ)
      = ((Int.negOnePow ((u - 1) / 2 * ((r₁ - 1) / 2) + (r₁ - 1) / 2
          + ((r₁.natAbs : ℤ) - 1) / 2) : ℤˣ) : ℤ) :=
    congrArg (fun x : ℤˣ => (x : ℤ)) ((Int.negOnePow_eq_iff _ _).mpr (by
      rw [show ((r₁ - 1) / 2 * ((m - 1) / 2) + ((r₁.natAbs : ℤ) - 1) / 2)
            - ((u - 1) / 2 * ((r₁ - 1) / 2) + (r₁ - 1) / 2 + ((r₁.natAbs : ℤ) - 1) / 2)
          = (r₁ - 1) / 2 * ((m - 1) / 2)
            - ((u - 1) / 2 * ((r₁ - 1) / 2) + (r₁ - 1) / 2) by ring]
      exact h2_part u r₁ m hu hr₁ hm_odd h4m))
  rw [chi8_part u v₁ r₁ s m hu hr₁ hv₁ hs hm,
      hilbertInf_eq_of_neg_iff hsign Iff.rfl,
      hilbertInf_eq_of_neg_iff hsign Iff.rfl,
      hilbertInf_eq_of_neg_iff Iff.rfl hsign,
      pow_part ((v₁*s)/4) α,
      hilbert_part u v₁ r₁ m,
      hB,
      multEps_part u v₁ r₁ s ρ m hρ hv₁0 hr₁0 hm,
      E_part u r₁ s v₁ ρ hu hr₁ hρodd hv₁ hs,
      negOnePow_prod3, negOnePow_prod2]
  refine congrArg (fun x : ℤˣ => (x : ℤ)) ?_
  rw [Int.negOnePow_eq_iff]
  have hcomb : Even ((((α:ℤ) + 1) * ((v₁*s)/4))
      + ((r₁ - 1)/2 + ((r₁.natAbs:ℤ) - 1)/2 - negI r₁)
      + ((negI r₁ * negI m + negI v₁ * negI m + negI v₁ * negI r₁ + negI u * negI v₁)
          - (negI u * negI v₁
              + (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁))
          - negI r₁)) :=
    ((claimA v₁ s v' α hv₁ hs hα hv').add (claimB r₁ hr₁)).add
      (claimC u v₁ r₁ m hv₁0 hr₁0 hm0)
  have hgoal : Even ((↑α * (v₁ * s / 4)
        + ((u - 1) / 2 * ((r₁ - 1) / 2) + (r₁ - 1) / 2 + (↑r₁.natAbs - 1) / 2)
        + (negI r₁ * negI m + negI v₁ * negI m + negI v₁ * negI r₁ + negI u * negI v₁))
      - ((negI u * negI v₁
            + (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁))
          + ((u - 1) / 2 * ((r₁ - 1) / 2) - v₁ * s / 4))) := by
    rw [show ((↑α * (v₁ * s / 4)
          + ((u - 1) / 2 * ((r₁ - 1) / 2) + (r₁ - 1) / 2 + (↑r₁.natAbs - 1) / 2)
          + (negI r₁ * negI m + negI v₁ * negI m + negI v₁ * negI r₁ + negI u * negI v₁))
        - ((negI u * negI v₁
              + (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁))
            + ((u - 1) / 2 * ((r₁ - 1) / 2) - v₁ * s / 4)))
        = ((↑α + 1) * (v₁ * s / 4)
            + ((r₁ - 1) / 2 + (↑r₁.natAbs - 1) / 2 - negI r₁)
            + (negI r₁ * negI m + negI v₁ * negI m + negI v₁ * negI r₁ + negI u * negI v₁
                - (negI u * negI v₁
                    + (if 0 < m then negI r₁ * (1 - negI v₁) else (1 - negI r₁) * negI v₁))
                - negI r₁))
          + 2 * negI r₁ by ring]
    exact hcomb.add (even_two_mul (negI r₁))
  exact hgoal

end

end Work.FIArea7
