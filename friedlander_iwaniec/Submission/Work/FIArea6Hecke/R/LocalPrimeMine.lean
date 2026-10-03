/-
# `Work.FIArea6Hecke.R.LocalPrimeMine`

An independent proof of the local prime-power comparison

  `λ_χ(p^e) = Σ_{j ≤ e} β(j) λ_{χ₀}(p^{e-j})`,  `β = (1-a u)(1-b u)|_{u^j}`,

used in `heckeLSeriesPartnerLE`.  Written as an insurance copy while the delegated
`localPrimeExists` was in flight.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea6Hecke.R.heckeLamPrimePowEqGood
import Submission.Work.FIArea6Hecke.area5_6_of_S16Core

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIArea5.S16Hecke
open Work.FIPlan

noncomputable section

/-- The coefficient array of `(1-a u)(1-b u)`. -/
def betaM (a b : ℂ) (j : ℕ) : ℂ :=
  if j = 0 then 1 else if j = 1 then -(a + b) else if j = 2 then a * b else 0

lemma betaM_eq_zero {a b : ℂ} {j : ℕ} (hj : 3 ≤ j) : betaM a b j = 0 := by
  rw [betaM]
  simp only [if_neg (by omega : ¬ j = 0), if_neg (by omega : ¬ j = 1), if_neg (by omega : ¬ j = 2)]

lemma betaM_zero_zero {j : ℕ} (hj : j ≠ 0) : betaM (0 : ℂ) 0 j = 0 := by
  rw [betaM]
  by_cases h1 : j = 1
  · subst h1; norm_num
  · by_cases h2 : j = 2
    · subst h2; norm_num
    · simp only [if_neg hj, if_neg h1, if_neg h2]

lemma betaM_sum_range (a b : ℂ) (x : ℕ → ℂ) {e : ℕ} (he : 2 ≤ e) :
    ∑ j ∈ Finset.range (e + 1), betaM a b j * x (e - j)
      = x e - (a + b) * x (e - 1) + (a * b) * x (e - 2) := by
  have hsub : Finset.range 3 ⊆ Finset.range (e + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  rw [← Finset.sum_subset hsub (fun j _ hj => by
    rw [Finset.mem_range] at hj
    simp [betaM_eq_zero (show 3 ≤ j by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, betaM]
  norm_num
  ring

lemma betaM_sum_range_one (a b : ℂ) (x : ℕ → ℂ) :
    ∑ j ∈ Finset.range 2, betaM a b j * x (1 - j) = x 1 - (a + b) * x 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, betaM]
  norm_num
  ring

lemma betaM_sum_range_zero (a b : ℂ) (x : ℕ → ℂ) :
    ∑ j ∈ Finset.range 1, betaM a b j * x (0 - j) = x 0 := by
  simp only [Finset.sum_range_one, betaM]
  norm_num

lemma betaM_sum_zero_zero (x : ℕ → ℂ) (e : ℕ) :
    ∑ j ∈ Finset.range (e + 1), betaM (0 : ℂ) 0 j * x (e - j) = x e := by
  rw [Finset.sum_eq_single 0]
  · simp [betaM]
  · intro j _ hje
    rw [betaM_zero_zero hje, zero_mul]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

/-! ## The three evaluations in the shape of the statement -/

lemma betaSum_range (a b : ℂ) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℕ) {e : ℕ} (he : 2 ≤ e) :
    ∑ j ∈ Finset.range (e + 1), betaM a b j * heckeLam chi m (p ^ (e - j))
      = heckeLam chi m (p ^ e) - (a + b) * heckeLam chi m (p ^ (e - 1))
        + (a * b) * heckeLam chi m (p ^ (e - 2)) := by
  simpa using betaM_sum_range a b (fun k : ℕ => heckeLam chi m (p ^ k)) he

lemma betaSum_one (a b : ℂ) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℕ) :
    ∑ j ∈ Finset.range 2, betaM a b j * heckeLam chi m (p ^ (1 - j))
      = heckeLam chi m (p ^ 1) - (a + b) * heckeLam chi m (p ^ 0) := by
  simpa using betaM_sum_range_one a b (fun k : ℕ => heckeLam chi m (p ^ k))

lemma betaSum_zero (a b : ℂ) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℕ) :
    ∑ j ∈ Finset.range 1, betaM a b j * heckeLam chi m (p ^ (0 - j))
      = heckeLam chi m (p ^ 0) := by
  simpa using betaM_sum_range_zero a b (fun k : ℕ => heckeLam chi m (p ^ k))

lemma betaSum_zero_zero (chi : GaussianInt → ℂ) (m : ℤ) (p e : ℕ) :
    ∑ j ∈ Finset.range (e + 1), betaM (0 : ℂ) 0 j * heckeLam chi m (p ^ (e - j))
      = heckeLam chi m (p ^ e) := by
  simpa using betaM_sum_zero_zero (fun k : ℕ => heckeLam chi m (p ^ k)) e

/-- **Vanishing at a prime dividing the conductor.** -/
lemma lamZeroMine (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : IsCharMod4dStrict d chi) {p : ℕ} (hp : p.Prime) (hpd : p ∣ 4 * d) {e : ℕ}
    (he : 1 ≤ e) : heckeLam chi m (p ^ e) = 0 := by
  classical
  haveI : NeZero (4 * d) := ⟨by omega⟩
  unfold heckeLam
  refine Finset.sum_eq_zero (fun z hz => ?_)
  rw [Finset.mem_filter] at hz
  obtain ⟨-, -, hzgn⟩ := hz
  have hnotu : ¬ IsUnitMod4d d z := by
    intro hU
    have hcop := (GaussUnit.isUnitMod4d_iff_coprime (d := d) z).mp hU
    rw [hzgn] at hcop
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (dvd_pow_self p (by omega)) hpd) hcop
  rw [psi, hchi.2 z hnotu, zero_mul]

/-- A square root of modulus at most one. -/
lemma existsSqMine (x : ℂ) (hx : ‖x‖ ≤ 1) : ∃ ζ : ℂ, ζ ^ 2 = x ∧ ‖ζ‖ ≤ 1 := by
  have hr : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  refine ⟨(Real.sqrt ‖x‖ : ℂ) * Complex.exp ((Complex.arg x / 2 : ℝ) * Complex.I), ?_, ?_⟩
  · have hsq : ((Real.sqrt ‖x‖ : ℂ)) ^ 2 = (‖x‖ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hr]
    have hexp : (Complex.exp ((Complex.arg x / 2 : ℝ) * Complex.I)) ^ 2
        = Complex.exp ((Complex.arg x : ℂ) * Complex.I) := by
      rw [← Complex.exp_nat_mul]
      norm_num
      congr 1
      ring
    rw [mul_pow, hsq, hexp, Complex.norm_mul_exp_arg_mul_I]
  · have h1 : ‖Complex.exp ((Complex.arg x / 2 : ℝ) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I (Complex.arg x / 2)
    rw [norm_mul, h1, mul_one]
    have h2 : ‖((Real.sqrt ‖x‖ : ℝ) : ℂ)‖ = Real.sqrt ‖x‖ := by
      simp [abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [h2]
    exact Real.sqrt_le_one.mpr hx

lemma geo_zero (x y : ℂ) : geo x y 0 = 1 := by simp [geo]

lemma geoInert_even (x : ℂ) (μ : ℕ) : geoInert x (μ + μ) = x ^ μ := by
  simp only [geoInert]
  rw [if_pos ⟨μ, rfl⟩, show (μ + μ) / 2 = μ by omega]

lemma geoInert_odd (x : ℂ) {e : ℕ} (h : ¬ Even e) : geoInert x e = 0 := by
  simp [geoInert, h]

lemma not_even_sub_two {e : ℕ} (he : ¬ Even e) (h3 : 3 ≤ e) : ¬ Even (e - 2) := by
  rw [Nat.not_even_iff_odd] at he ⊢
  obtain ⟨k, hk⟩ := he
  exact ⟨k - 1, by omega⟩

/-- **The local prime-power comparison.**  For every rational prime `p` there are complex numbers
`a`, `b` of modulus at most one such that, for every `e`,
`λ_χ(p^e) = Σ_{j ≤ e} β(j)λ_{χ₀}(p^{e-j})` with `β` the coefficient array of `(1-a u)(1-b u)`. -/
theorem localPrimeExistsMine (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (M : GaussianInt)
    (chi₀ : GaussianInt → ℂ) (m : ℤ)
    (hchi : IsCharMod4dStrict d chi)
    (hpart : IsConductorPartner d chi M chi₀)
    (p : ℕ) (hp : p.Prime) :
    ∃ a b : ℂ, ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ ∀ e : ℕ,
      heckeLam chi m (p ^ e) =
        ∑ j ∈ Finset.range (e + 1), betaM a b j * heckeLam chi₀ m (p ^ (e - j)) := by
  classical
  have hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1 := hpart.2.2.2.2.1
  have hmul0 : ∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w := hpart.2.2.2.1
  have h10 : chi₀ 1 = 1 := hpart.2.2.1
  have hchi1 : chi 1 = 1 := hchi.1.1
  have hL1 : heckeLam chi m 1 = 1 := by rw [heckeLam_one, hchi1]
  have hR1 : heckeLam chi₀ m 1 = 1 := by rw [heckeLam_one, h10]
  rcases eq_or_ne p 2 with rfl | hp2
  · -- `p = 2`
    refine ⟨0, 0, by norm_num, by norm_num, fun e => ?_⟩
    rw [betaSum_zero_zero chi₀ m 2 e]
    rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [pow_zero, hL1, hR1]
    · rw [lamZeroMine d hd chi m hchi (by norm_num) (dvd_mul_of_dvd_left (by norm_num : (2:ℕ) ∣ 4) d) he,
        heckeLam_even chi₀ m ⟨2 ^ (e - 1), by rw [← two_mul, ← pow_succ']; congr 1; omega⟩]
  · -- `p` odd
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
    have hp43 : p % 4 = 1 ∨ p % 4 = 3 := Nat.odd_mod_four_iff.mp hodd
    by_cases hpd : p ∣ 4 * d
    · -- `p ∣ 4d`: `λ_χ(p^e) = 0` for `e ≥ 1`
      have hzero : ∀ e : ℕ, 1 ≤ e → heckeLam chi m (p ^ e) = 0 :=
        fun e he => lamZeroMine d hd chi m hchi hp hpd he
      rcases hp43 with h1 | h3
      · -- split prime: `p = π·π'`
        obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp h1
        refine ⟨psi chi₀ m π, psi chi₀ m π', norm_psi_le_one chi₀ m hb π,
          norm_psi_le_one chi₀ m hb π', fun e => ?_⟩
        have hgeo : ∀ ν : ℕ, heckeLam chi₀ m (p ^ ν) = geo (psi chi₀ m π) (psi chi₀ m π') ν :=
          fun ν => heckeLam_splitSum chi₀ m p hp.pos hmul0 h10 π π' hπ hπ' hgπ hgπ' hclass ν
        rcases Nat.eq_zero_or_pos e with rfl | he
        · rw [pow_zero, hL1, betaSum_zero (psi chi₀ m π) (psi chi₀ m π') chi₀ m p, pow_zero, hR1]
        · rcases Nat.eq_or_lt_of_le he with he1 | he2
          · subst he1
            rw [hzero 1 le_rfl,
              betaSum_one (psi chi₀ m π) (psi chi₀ m π') chi₀ m p, hgeo 1, hgeo 0, geo_one,
              geo_zero]
            ring
          · rw [hzero e he, betaSum_range (psi chi₀ m π) (psi chi₀ m π') chi₀ m p he2,
              hgeo e, hgeo (e - 1), hgeo (e - 2)]
            have hrec := geo_rec (psi chi₀ m π) (psi chi₀ m π') (e - 2)
            rw [show e - 2 + 2 = e by omega, show e - 2 + 1 = e - 1 by omega, geo_one, geo_two]
              at hrec
            have hxy : (psi chi₀ m π + psi chi₀ m π') ^ 2
                - (psi chi₀ m π ^ 2 + psi chi₀ m π * psi chi₀ m π' + psi chi₀ m π' ^ 2)
                = psi chi₀ m π * psi chi₀ m π' := by ring
            rw [hxy] at hrec
            linear_combination -hrec
      · -- inert prime: `p = -q`
        obtain ⟨hqp, -, hqgn, hclass⟩ := inertPrimaryClass p hp h3
        have hbnd : ‖psi chi₀ m (-(p : GaussianInt))‖ ≤ 1 :=
          norm_psi_le_one chi₀ m hb (-(p : GaussianInt))
        obtain ⟨ζ, hζ2, hζ⟩ := existsSqMine _ hbnd
        refine ⟨ζ, -ζ, hζ, by simpa using hζ, fun e => ?_⟩
        have hgeo : ∀ ν : ℕ,
            heckeLam chi₀ m (p ^ ν) = geoInert (psi chi₀ m (-(p : GaussianInt))) ν :=
          fun ν => heckeLam_inertSum chi₀ m p hp.pos hmul0 h10 (-(p : GaussianInt)) hqp hqgn
            hclass ν
        have hgx : geoInert (psi chi₀ m (-(p : GaussianInt))) 0 = 1 := by simp [geoInert]
        have hg1 : geoInert (psi chi₀ m (-(p : GaussianInt))) 1 = 0 :=
          geoInert_odd _ (by norm_num)
        rcases Nat.eq_zero_or_pos e with rfl | he
        · rw [pow_zero, hL1, betaSum_zero ζ (-ζ) chi₀ m p, pow_zero, hR1]
        · rcases Nat.eq_or_lt_of_le he with he1 | he2
          · subst he1
            rw [hzero 1 le_rfl, betaSum_one ζ (-ζ) chi₀ m p, hgeo 1, hgeo 0, hg1, hgx]
            ring
          · rw [hzero e he, betaSum_range ζ (-ζ) chi₀ m p he2,
              hgeo e, hgeo (e - 1), hgeo (e - 2)]
            rw [show ζ + -ζ = 0 by ring,
              show ζ * -ζ = -psi chi₀ m (-(p : GaussianInt)) by
                rw [show ζ * -ζ = -(ζ ^ 2) by ring, hζ2]]
            rw [zero_mul, sub_zero]
            rcases Nat.even_or_odd e with hev | hodd
            · obtain ⟨μ, rfl⟩ := hev
              have hμ : 1 ≤ μ := by omega
              rw [show μ + μ - 2 = (μ - 1) + (μ - 1) by omega, geoInert_even _ μ,
                geoInert_even _ (μ - 1)]
              have hpow : psi chi₀ m (-(p : GaussianInt)) ^ μ
                  = psi chi₀ m (-(p : GaussianInt)) * psi chi₀ m (-(p : GaussianInt)) ^ (μ - 1) := by
                conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
                rw [pow_succ]
                ring
              rw [hpow]
              ring_nf
            · have hodd' : ¬ Even e := Nat.not_even_iff_odd.mpr hodd
              have h3e : 3 ≤ e := by
                obtain ⟨k, hk⟩ := hodd
                omega
              rw [geoInert_odd _ hodd', geoInert_odd _ (not_even_sub_two hodd' h3e)]
              ring
    · -- `p ∤ 4d`
      refine ⟨0, 0, by norm_num, by norm_num, fun e => ?_⟩
      rw [betaSum_zero_zero chi₀ m p e, heckeLamPrimePowEqGood d hd chi M chi₀ m hchi hpart p hp hpd e]

/-- **The generating function of a two-term recursion.**  A sequence satisfying
`a (e+2) = (c₁+c₂)a (e+1) - c₁c₂ a e` with `a 0 = 1`, `a 1 = c₁ + c₂` and summable terms
`a e · u^e` has generating function `1/((1-c₁u)(1-c₂u))`. -/
theorem geoGenMine (a : ℕ → ℂ) (u c₁ c₂ : ℂ)
    (h0 : a 0 = 1) (h1 : a 1 = c₁ + c₂)
    (hrec : ∀ e : ℕ, a (e + 2) = (c₁ + c₂) * a (e + 1) - (c₁ * c₂) * a e)
    (hsum : Summable (fun e : ℕ => a e * u ^ e)) :
    (∑' e : ℕ, a e * u ^ e) * (1 - (c₁ + c₂) * u + (c₁ * c₂) * u ^ 2) = 1 := by
  let g : ℕ → ℂ := fun e => a e * u ^ e
  change (∑' e : ℕ, g e) * (1 - (c₁ + c₂) * u + (c₁ * c₂) * u ^ 2) = 1
  have hsumg : Summable g := hsum
  have hg0 : g 0 = 1 := by
    simp only [g, h0, pow_zero, mul_one]
  have hg1 : g 1 = (c₁ + c₂) * u := by
    simp only [g, h1, pow_one]
  have hrecg : ∀ e : ℕ, g (e + 2) = (c₁ + c₂) * u * g (e + 1) - (c₁ * c₂) * u ^ 2 * g e := by
    intro e
    simp only [g, hrec e]
    ring
  have hsh1 : Summable fun e : ℕ => g (e + 1) :=
    hsumg.comp_injective (fun a b h => by simpa using h)
  have hsh2 : Summable fun e : ℕ => g (e + 2) :=
    hsumg.comp_injective (fun a b h => by simpa using h)
  set T : ℂ := ∑' e : ℕ, g e with hT
  set T1 : ℂ := ∑' e : ℕ, g (e + 1) with hT1
  set T2 : ℂ := ∑' e : ℕ, g (e + 2) with hT2
  have e1 : T = 1 + T1 := by
    rw [hT, hsumg.tsum_eq_zero_add, hg0, hT1]
  have e2 : T1 = (c₁ + c₂) * u + T2 := by
    rw [hT1, hsh1.tsum_eq_zero_add, hg1, hT2]
  have e3 : T2 = (c₁ + c₂) * u * T1 - (c₁ * c₂) * u ^ 2 * T := by
    have hA : Summable fun e : ℕ => (c₁ + c₂) * u * g (e + 1) := hsh1.mul_left _
    have hB : Summable fun e : ℕ => (c₁ * c₂) * u ^ 2 * g e := hsumg.mul_left _
    have hcongr : (fun e : ℕ => g (e + 2))
        = fun e : ℕ => (c₁ + c₂) * u * g (e + 1) - (c₁ * c₂) * u ^ 2 * g e := funext hrecg
    rw [hT2, hcongr, Summable.tsum_sub hA hB, tsum_mul_left, tsum_mul_left, hT1, hT]
  have h1' : T - 1 - T1 = 0 := by rw [e1]; ring
  have h2' : T1 - (c₁ + c₂) * u - T2 = 0 := by rw [e2]; ring
  have h3' : T2 - ((c₁ + c₂) * u * T1 - (c₁ * c₂) * u ^ 2 * T) = 0 := by rw [e3]; ring
  linear_combination h1' + h2' + h3' - ((c₁ + c₂) * u) * h1'

end

end Work.FIArea6Hecke.R
