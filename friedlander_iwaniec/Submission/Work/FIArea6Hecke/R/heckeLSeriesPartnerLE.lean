/-
# `Work.FIArea6Hecke.R.heckeLSeriesPartnerLE`

The Euler-product comparison between the Hecke `L`-series of a strict character `χ` mod `4d` and
its conductor partner `χ₀`: for `re s > 1`

  `L(s,ψ_χ) = L(s,ψ_{χ₀})·∏_{p ∣ 4d}((1 - c₁(p)p^{-s})(1 - c₂(p)p^{-s}))`

with `‖c₁ p‖ ≤ 1`, `‖c₂ p‖ ≤ 1`.

The proof is a *local* comparison of Euler factors.  For a rational prime `p`:

* if `p ∣ 4d`, then `λ_χ(p^e) = 0` for every `e ≥ 1` (`χ` vanishes off the units mod `4d` and every
  primary `z` of norm `p^e` is divisible by a Gaussian prime over `p`, hence is not a unit mod
  `4d`), so the local factor of `L(s,ψ_χ)` is `1`, while the local factor of `L(s,ψ_{χ₀})` is
  `1/((1-c₁(p)p^{-s})(1-c₂(p)p^{-s}))` by the local recursion `λ_{χ₀}(p^{e+2}) = λ_{χ₀}(p)·λ_{χ₀}(p^{e+1})
  - (λ_{χ₀}(p)² - λ_{χ₀}(p²))λ_{χ₀}(p^e)`;
* if `p ∤ 4d`, then every primary `z` of norm `p^e` is a unit modulo `4d`, so `χ₀ z = χ z` and the
  local factors agree.

The two `HasProd` statements are combined with the `HasProd` of the finite correction family and
`HasProd.unique`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea6Hecke.R.heckeLamPrimePowZeroBad
import Submission.Work.FIArea6Hecke.R.heckeLamPrimePowEqGood
import Submission.Work.FIArea6Hecke.R.hasProdCorrFamily
import Submission.Work.FIArea6Hecke.R.geoGenFunc
import Submission.Work.FIArea5.S16Hecke.Basic

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIArea5.S16Hecke

noncomputable section

/-- The `j`-th coefficient of the polynomial `(1 - a u)(1 - b u)`, i.e. of the reversed reciprocal
polynomial of the local factor `1/((1-a u)(1-b u))`. -/
def betaC (a b : ℂ) (j : ℕ) : ℂ :=
  if j = 0 then 1 else if j = 1 then -(a + b) else if j = 2 then a * b else 0

@[simp] lemma betaC_zero (a b : ℂ) : betaC a b 0 = 1 := rfl
@[simp] lemma betaC_one (a b : ℂ) : betaC a b 1 = -(a + b) := rfl
@[simp] lemma betaC_two (a b : ℂ) : betaC a b 2 = a * b := rfl
lemma betaC_eq_zero {a b : ℂ} {j : ℕ} (hj : 3 ≤ j) : betaC a b j = 0 := by
  rw [betaC]
  simp only [if_neg (by omega : ¬ j = 0), if_neg (by omega : ¬ j = 1), if_neg (by omega : ¬ j = 2)]

/-- The correction factor attached to the rational prime `p` at the point `s`. -/
def corrFacP (c₁ c₂ : ℕ → ℂ) (s : ℂ) (p : ℕ) : ℂ :=
  (1 - c₁ p * (p : ℂ) ^ (-s)) * (1 - c₂ p * (p : ℂ) ^ (-s))

/-! ## The local complex analysis -/

/-- `1/(p^{e s}) = (p^{-s})^e`: rewriting the local Euler factors of the Hecke `L`-series in terms
of the variable `u = p^{-s}` used by the correction product. -/
lemma cpow_inv_mul_eq (p e : ℕ) (s : ℂ) (hp : p ≠ 0) :
    (((p : ℂ) ^ ((e : ℂ) * s)))⁻¹ = (((p : ℂ) ^ (-s))) ^ e := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [Complex.cpow_def, if_neg hp', Complex.cpow_def, if_neg hp', ← Complex.exp_neg]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- The norm of the local variable `u = p^{-s}`. -/
lemma norm_cpow_neg_natCast {p : ℕ} (hp : 0 < p) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re]

/-- **Summability of a local Euler factor.**  For a character bounded by `1` and `re s > 1`, the
local series `Σ_e λ(p^e)u^e` (`u = p^{-s}`) converges absolutely: `‖λ(p^e)‖ ≤ 4(e+1)` while
`‖u‖ = p^{-re s} < 1`. -/
lemma summable_localFactor (chi : GaussianInt → ℂ) (m : ℤ) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) (p : ℕ) (hp : p.Prime) :
    Summable (fun e : ℕ => heckeLam chi m (p ^ e) * ((p : ℂ) ^ (-s)) ^ e) := by
  have hp0 : 0 < p := hp.pos
  set r : ℝ := (p : ℝ) ^ (-s.re) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = r := by
    rw [norm_cpow_neg_natCast hp0, hr]
  have hr1 : r < 1 := by
    rw [hr, Real.rpow_lt_one_iff (Nat.cast_nonneg p)]
    exact Or.inr (Or.inl ⟨by exact_mod_cast hp.one_lt, by linarith⟩)
  have hcard' : ∀ e : ℕ, (p ^ e).divisors.card = e + 1 := by
    intro e
    rw [Nat.divisors_prime_pow hp e, Finset.card_map, Finset.card_range]
  have hdom : Summable (fun e : ℕ => 4 * ((e : ℝ) + 1) * r ^ e) := by
    have h1 : Summable (fun e : ℕ => (e : ℝ) ^ 1 * r ^ e) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
    have h2 : Summable (fun e : ℕ => r ^ e) :=
      summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)
    have h3 : Summable (fun e : ℕ => (e : ℝ) ^ 1 * r ^ e + r ^ e) := h1.add h2
    refine (h3.mul_left 4).congr fun e => ?_
    simp only [pow_one]
    ring
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun e => norm_nonneg _) ?_ hdom)
  intro e
  rw [norm_mul, norm_pow, hnorm]
  have h1 : ‖heckeLam chi m (p ^ e)‖ ≤ 4 * ((e : ℝ) + 1) := by
    have hb' := heckeLam_bound chi m hb (n := p ^ e) (Nat.one_le_pow e p hp.pos)
    rw [hcard' e] at hb'
    push_cast at hb'
    linarith
  calc ‖heckeLam chi m (p ^ e)‖ * r ^ e ≤ (4 * ((e : ℝ) + 1)) * r ^ e :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg hr0 e)
    _ = 4 * ((e : ℝ) + 1) * r ^ e := by ring

/-! ## Evaluating the local convolution at a prime power -/

/-- The `e`-th coefficient of `(Σ_e x_e u^e)·(1 - (a+b)u + ab u²)`, in the shape delivered by
`localPrimeExists`. -/
lemma sum_betaC_range (a b : ℂ) (x : ℕ → ℂ) {e : ℕ} (he : 2 ≤ e) :
    ∑ j ∈ Finset.range (e + 1), betaC a b j * x (e - j)
      = x e - (a + b) * x (e - 1) + (a * b) * x (e - 2) := by
  have hsub : Finset.range 3 ⊆ Finset.range (e + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub (fun j _ hj => by
    rw [Finset.mem_range] at hj
    simp [betaC_eq_zero (show 3 ≤ j by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, betaC]
  norm_num
  ring

lemma sum_betaC_range_one (a b : ℂ) (x : ℕ → ℂ) :
    ∑ j ∈ Finset.range 2, betaC a b j * x (1 - j) = x 1 - (a + b) * x 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, betaC]
  norm_num
  ring

lemma sum_betaC_range_zero (a b : ℂ) (x : ℕ → ℂ) :
    ∑ j ∈ Finset.range 1, betaC a b j * x (0 - j) = x 0 := by
  simp only [Finset.sum_range_one, betaC]
  norm_num

/-! ## The local factor at a prime dividing `4d` -/

/-- **The local factor identity at a prime `p ∣ 4d`.**  Suppose the local convolution identity of
`localPrimeExists` holds at `p` (with roots `a`, `b`) and `λ_χ(p^e) = 0` for all `e ≥ 1`.  Then the
`p`-Euler factor of `L(s,ψ_{χ₀})`, multiplied by the correction `(1-a u)(1-b u)` (`u = p^{-s}`),
is `1`: the sequence `e ↦ λ_{χ₀}(p^e)` satisfies the two-term recursion with characteristic
polynomial `(1-a u)(1-b u)`. -/
lemma localFactor_at_bad {chi chi₀ : GaussianInt → ℂ} {m : ℤ} {p : ℕ} (hp : p.Prime)
    {a b : ℂ} {s : ℂ} (hs : 1 < s.re) (hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1)
    (h1 : chi 1 = 1) (h10 : chi₀ 1 = 1)
    (hloc : ∀ e : ℕ, heckeLam chi m (p ^ e) =
      ∑ j ∈ Finset.range (e + 1), betaC a b j * heckeLam chi₀ m (p ^ (e - j)))
    (hzero : ∀ e : ℕ, 1 ≤ e → heckeLam chi m (p ^ e) = 0) :
    (∑' e : ℕ, heckeLam chi₀ m (p ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
      * ((1 - a * (p : ℂ) ^ (-s)) * (1 - b * (p : ℂ) ^ (-s))) = 1 := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hrew : (∑' e : ℕ, heckeLam chi₀ m (p ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
      = ∑' e : ℕ, heckeLam chi₀ m (p ^ e) * ((p : ℂ) ^ (-s)) ^ e := by
    refine tsum_congr fun e => ?_
    rw [div_eq_mul_inv, cpow_inv_mul_eq p e s hp0]
  rw [hrew]
  have h0 : heckeLam chi₀ m (p ^ 0) = 1 := by
    rw [pow_zero, heckeLam_one, h10]
  have h1' : heckeLam chi₀ m (p ^ 1) = a + b := by
    have h := hloc 1
    rw [sum_betaC_range_one a b (fun e : ℕ => heckeLam chi₀ m (p ^ e))] at h
    have hz := hzero 1 le_rfl
    rw [hz, h0, mul_one] at h
    have h' : heckeLam chi₀ m (p ^ 1) - (a + b) = 0 := h.symm
    linear_combination h'
  have hrec : ∀ e : ℕ, heckeLam chi₀ m (p ^ (e + 2))
      = (a + b) * heckeLam chi₀ m (p ^ (e + 1)) - (a * b) * heckeLam chi₀ m (p ^ e) := by
    intro e
    have h := hloc (e + 2)
    rw [sum_betaC_range a b (fun e : ℕ => heckeLam chi₀ m (p ^ e)) (e := e + 2) (by omega)] at h
    rw [show e + 2 - 1 = e + 1 by omega, show e + 2 - 2 = e by omega] at h
    have hz := hzero (e + 2) (by omega)
    rw [hz] at h
    have h' : heckeLam chi₀ m (p ^ (e + 2))
        - ((a + b) * heckeLam chi₀ m (p ^ (e + 1)) - (a * b) * heckeLam chi₀ m (p ^ e)) = 0 := by
      rw [h]; ring
    exact sub_eq_zero.mp h'
  have hsum : Summable (fun e : ℕ => heckeLam chi₀ m (p ^ e) * ((p : ℂ) ^ (-s)) ^ e) :=
    summable_localFactor chi₀ m hb hs p hp
  have hgen := geoGenFunc (fun e : ℕ => heckeLam chi₀ m (p ^ e)) ((p : ℂ) ^ (-s)) a b h0 h1' hrec hsum
  rw [show (1 - a * (p : ℂ) ^ (-s)) * (1 - b * (p : ℂ) ^ (-s))
      = 1 - (a + b) * ((p : ℂ) ^ (-s)) + (a * b) * ((p : ℂ) ^ (-s)) ^ 2 by ring]
  exact hgen

/-! ## The assembly -/

end

end Work.FIArea6Hecke.R
