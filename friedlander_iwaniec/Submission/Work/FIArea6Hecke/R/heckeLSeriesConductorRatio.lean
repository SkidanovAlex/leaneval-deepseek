import Mathlib
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea6Hecke.R.heckeLSeriesPartnerLE
import Submission.Work.FIArea6Hecke.R.LocalPrimeMine
import Submission.Work.FIArea6Hecke.R.heckeLamPrimePowZeroBad
import Submission.Work.FIArea6Hecke.R.heckeLamPrimePowEqGood
import Submission.Work.FIArea6Hecke.R.hasProdCorrFamily

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIArea5.S16Hecke
open Work.FIPlan

noncomputable section

/-! ## Elementary facts about the conductor partner

The partner `χ₀` is a character of the unit group `(ℤ[i]/M)^*` extended by zero.  Two facts are
used below: on the units of `(ℤ[i]/M)^*` its values have modulus **exactly** `1` (they are roots of
unity), and off the units they vanish.  Consequently `ψ_{χ₀}(z) = χ₀(z)(z/|z|)^m` has modulus `1`
or vanishes at every `z ≠ 0`. -/

/-- The unit factor `z/|z|` of the Größencharacter has modulus exactly `1` at a nonzero `z`. -/
lemma norm_div_sqrt_zpow_eq_one {z : GaussianInt} (hz : z ≠ 0) (k : ℤ) :
    ‖(z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ)) ^ k‖ = 1 := by
  have hne : z.toComplex ≠ 0 :=
    fun h => hz (GaussianInt.toComplex_injective (h.trans GaussianInt.toComplex_zero.symm))
  have h1 : ‖z.toComplex / ((Real.sqrt (gnorm z : ℝ)) : ℂ)‖ = 1 := by
    rw [norm_div, norm_toComplex]
    have h2 : ‖((Real.sqrt (gnorm z : ℝ) : ℝ) : ℂ)‖ = Real.sqrt (gnorm z : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [h2, div_self]
    rw [← norm_toComplex, norm_ne_zero_iff]
    exact hne
  rw [norm_zpow, h1, one_zpow]

/-- **Values of the partner on units have modulus exactly one.**  If `z` is invertible modulo `M`
(`IsUnitMod M z`) and `χ₀` is multiplicative with `χ₀ 1 = 1`, `M`-periodic and bounded by `1`, then
`‖χ₀ z‖ = 1`.  Indeed `z w ≡ 1 (M)` gives `χ₀ z · χ₀ w = 1`, so both factors have modulus `1`. -/
lemma norm_chi₀_eq_one_of_unitMod {M : GaussianInt} {chi₀ : GaussianInt → ℂ}
    (h1 : chi₀ 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w)
    (hper : ∀ z w : GaussianInt, M ∣ (z - w) → chi₀ z = chi₀ w)
    (hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1)
    {z : GaussianInt} (hz : IsUnitMod M z) : ‖chi₀ z‖ = 1 := by
  obtain ⟨w, hw⟩ := hz
  have hzw : chi₀ (z * w) = 1 := by rw [hper (z * w) 1 hw, h1]
  have hprod : ‖chi₀ z‖ * ‖chi₀ w‖ = 1 := by
    rw [← norm_mul, ← hmul z w, hzw, norm_one]
  have hkey : 1 ≤ ‖chi₀ z‖ := by
    calc (1 : ℝ) = ‖chi₀ z‖ * ‖chi₀ w‖ := hprod.symm
      _ ≤ ‖chi₀ z‖ * 1 := mul_le_mul_of_nonneg_left (hb w) (norm_nonneg _)
      _ = ‖chi₀ z‖ := mul_one _
  exact le_antisymm (hb z) hkey

/-- **Dichotomy for the partner.**  For every `z`, either `‖χ₀ z‖ = 1` (when `z` is a unit modulo
`M`) or `χ₀ z = 0` (when it is not). -/
lemma chi₀_norm_eq_one_or_eq_zero {M : GaussianInt} {chi₀ : GaussianInt → ℂ}
    (h1 : chi₀ 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w)
    (hper : ∀ z w : GaussianInt, M ∣ (z - w) → chi₀ z = chi₀ w)
    (hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1)
    (hz0 : ∀ z : GaussianInt, ¬ IsUnitMod M z → chi₀ z = 0)
    (z : GaussianInt) : ‖chi₀ z‖ = 1 ∨ chi₀ z = 0 := by
  by_cases h : IsUnitMod M z
  · exact Or.inl (norm_chi₀_eq_one_of_unitMod h1 hmul hper hb h)
  · exact Or.inr (hz0 z h)

/-- **Dichotomy for the Größencharacter of the partner** at a nonzero argument. -/
lemma psi_norm_eq_one_or_eq_zero {M : GaussianInt} {chi₀ : GaussianInt → ℂ}
    (h1 : chi₀ 1 = 1)
    (hmul : ∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w)
    (hper : ∀ z w : GaussianInt, M ∣ (z - w) → chi₀ z = chi₀ w)
    (hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1)
    (hz0 : ∀ z : GaussianInt, ¬ IsUnitMod M z → chi₀ z = 0)
    (m : ℤ) {z : GaussianInt} (hz : z ≠ 0) :
    ‖psi chi₀ m z‖ = 1 ∨ psi chi₀ m z = 0 := by
  rcases chi₀_norm_eq_one_or_eq_zero h1 hmul hper hb hz0 z with hn | h0
  · exact Or.inl (by
      rw [psi, norm_mul, hn, one_mul]
      exact norm_div_sqrt_zpow_eq_one hz m)
  · exact Or.inr (by rw [psi, h0, zero_mul])

/-! ## The strengthened local prime-power comparison

This is `localPrimeExistsMine` with the extra conclusion that each root has modulus **exactly** one
or vanishes.  The construction of the roots is unchanged; the extra information comes from the
dichotomy `psi_norm_eq_one_or_eq_zero` above. -/

/-- **The local prime-power comparison, with `= 1 ∨ = 0` roots.**  For every rational prime `p`
there are complex numbers `a`, `b`, each of modulus exactly one or zero, such that for every `e`,
`λ_χ(p^e) = Σ_{j ≤ e} β(j)λ_{χ₀}(p^{e-j})` with `β` the coefficient array of `(1-a u)(1-b u)`. -/
theorem localPrimeExistsMineStrong (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (M : GaussianInt)
    (chi₀ : GaussianInt → ℂ) (m : ℤ)
    (hchi : IsCharMod4dStrict d chi)
    (hpart : IsConductorPartner d chi M chi₀)
    (p : ℕ) (hp : p.Prime) :
    ∃ a b : ℂ, (‖a‖ = 1 ∨ a = 0) ∧ (‖b‖ = 1 ∨ b = 0) ∧ ∀ e : ℕ,
      heckeLam chi m (p ^ e) =
        ∑ j ∈ Finset.range (e + 1), betaM a b j * heckeLam chi₀ m (p ^ (e - j)) := by
  classical
  have hb : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1 := hpart.2.2.2.2.1
  have hmul0 : ∀ z w : GaussianInt, chi₀ (z * w) = chi₀ z * chi₀ w := hpart.2.2.2.1
  have h10 : chi₀ 1 = 1 := hpart.2.2.1
  have hper : ∀ z w : GaussianInt, M ∣ (z - w) → chi₀ z = chi₀ w := hpart.2.2.2.2.2.1
  have hz0 : ∀ z : GaussianInt, ¬ IsUnitMod M z → chi₀ z = 0 := hpart.2.2.2.2.2.2.1
  have hpsi : ∀ {z : GaussianInt}, z ≠ 0 → ‖psi chi₀ m z‖ = 1 ∨ psi chi₀ m z = 0 :=
    fun {z} hz => psi_norm_eq_one_or_eq_zero h10 hmul0 hper hb hz0 m hz
  have hchi1 : chi 1 = 1 := hchi.1.1
  have hL1 : heckeLam chi m 1 = 1 := by rw [heckeLam_one, hchi1]
  have hR1 : heckeLam chi₀ m 1 = 1 := by rw [heckeLam_one, h10]
  have hgnorm0 : gnorm (0 : GaussianInt) = 0 := by simp [gnorm]
  rcases eq_or_ne p 2 with rfl | hp2
  · -- `p = 2`
    refine ⟨0, 0, Or.inr rfl, Or.inr rfl, fun e => ?_⟩
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
        have hπne : π ≠ 0 := by
          intro h; rw [h] at hgπ; rw [hgnorm0] at hgπ
          exact hp.ne_zero hgπ.symm
        have hπ'ne : π' ≠ 0 := by
          intro h; rw [h] at hgπ'; rw [hgnorm0] at hgπ'
          exact hp.ne_zero hgπ'.symm
        refine ⟨psi chi₀ m π, psi chi₀ m π', hpsi hπne, hpsi hπ'ne, fun e => ?_⟩
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
        have hpcast : (p : GaussianInt) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hnegne : -(p : GaussianInt) ≠ 0 := neg_ne_zero.mpr hpcast
        have hbnd : ‖psi chi₀ m (-(p : GaussianInt))‖ ≤ 1 :=
          norm_psi_le_one chi₀ m hb (-(p : GaussianInt))
        obtain ⟨ζ, hζ2, hζ⟩ := existsSqMine _ hbnd
        have hsq : ζ * ζ = psi chi₀ m (-(p : GaussianInt)) := by
          rw [← pow_two]; exact hζ2
        have hζprop : ‖ζ‖ = 1 ∨ ζ = 0 := by
          rcases hpsi hnegne with h1' | h0'
          · left
            have hnorm : ‖ζ‖ ^ 2 = 1 := by
              have h2 : ‖ζ ^ 2‖ = 1 := by rw [hζ2, h1']
              rwa [norm_pow] at h2
            nlinarith [norm_nonneg ζ, sq_nonneg (‖ζ‖ - 1)]
          · right
            exact mul_self_eq_zero.mp (by rw [hsq, h0'])
        have hζnegprop : ‖-ζ‖ = 1 ∨ -ζ = 0 := by
          rcases hζprop with h | h
          · exact Or.inl (by rw [norm_neg, h])
          · exact Or.inr (by rw [h, neg_zero])
        refine ⟨ζ, -ζ, hζprop, hζnegprop, fun e => ?_⟩
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
            rcases Nat.even_or_odd e with hev | heo
            · obtain ⟨μ, rfl⟩ := hev
              have hμ : 1 ≤ μ := by omega
              rw [show μ + μ - 2 = (μ - 1) + (μ - 1) by omega, geoInert_even _ μ,
                geoInert_even _ (μ - 1)]
              have hpow : psi chi₀ m (-(p : GaussianInt)) ^ μ
                  = psi chi₀ m (-(p : GaussianInt))
                    * psi chi₀ m (-(p : GaussianInt)) ^ (μ - 1) := by
                conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
                rw [pow_succ]
                ring
              rw [hpow]
              ring_nf
            · have heo' : ¬ Even e := Nat.not_even_iff_odd.mpr heo
              have h3e : 3 ≤ e := by
                obtain ⟨k, hk⟩ := heo
                omega
              rw [geoInert_odd _ heo', geoInert_odd _ (not_even_sub_two heo' h3e)]
              ring
    · -- `p ∤ 4d`
      refine ⟨0, 0, Or.inr rfl, Or.inr rfl, fun e => ?_⟩
      rw [betaSum_zero_zero chi₀ m p e,
        heckeLamPrimePowEqGood d hd chi M chi₀ m hchi hpart p hp hpd e]

/-! ## The main statement -/

/-- **The Euler-factor ratio between a strict character and its conductor partner.**

Let `χ` be strict mod `4d` and let `χ₀` (mod `M`, `M ∣ 4d`) be its conductor partner
(`IsConductorPartner d chi M chi₀`, as produced by `heckeConductorDataUnit`).  Then the two Hecke
`L`-series differ by a finite product of local factors at the rational primes dividing `4d`:

  `L(s,ψ_χ) = L(s,ψ_{χ₀})·∏_{p∈S}(1-c₁(p)p^{-s})(1-c₂(p)p^{-s})`,  `re s > 1`,

with `‖cᵢ(p)‖ = 1` or `cᵢ(p) = 0` on `S`.

This is the strict (`= 1 ∨ 0`) upgrade of the proved `heckeLSeriesPartnerLE` / `heckeLSeriesPartnerOdd`
(which give `‖cᵢ(p)‖ ≤ 1`); the `= 1 ∨ 0` form is what the lower bound at `re s = -2` needs (with
`≤ 1` a factor `1 - c·2^{-w}` with `‖c‖ = 1/4` vanishes at `γ = 0`).  Why the ratio is a polynomial
with coefficients of modulus `1`: the series run over *primary* elements, so the `(1+i)`-Euler
factor is absent from both; a prime ideal `𝔭 ∣ 4d` with `𝔭 ∤ M` has `χ(z_𝔭) = 0` (as
`z_𝔭 ∉ U(4d)`) but `χ₀(z_𝔭) ≠ 0`, contributing a *numerator* `(1-ψ₀(𝔭)N𝔭^{-s})`; for `p` split
this is `(1-ψ₀(𝔭)p^{-s})(1-ψ₀(𝔭̄)p^{-s})`, for `p` inert
`(1-ψ₀(𝔭)p^{-2s}) = (1-ζp^{-s})(1+ζp^{-s})` with `ζ² = ψ₀(𝔭)`.  Since the partner is unitary
(`‖χ₀‖ ≤ 1` and multiplicativity), all these numbers have modulus `1`.

Note: `χ₀` is a character of modulus `M`, not `IsCharMod4dStrict d`, so the existing Euler-product
machinery (`heckeLSeries_eulerProduct`) does not apply to it directly; the identity has to be
proved at the level of the coefficients `heckeLam` (e.g. via `heckeLam_localRec` /
`localFactor_eq_decomp`), matching the local factors prime by prime. -/
theorem heckeLSeriesConductorRatio (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (M : GaussianInt)
    (chi₀ : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hpart : Work.FIArea6Hecke.R.IsConductorPartner d chi M chi₀) :
    ∃ (S : Finset ℕ) (c₁ c₂ : ℕ → ℂ),
      (∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0)) ∧
      (∀ s : ℂ, 1 < s.re →
        Work.FIArea5.S16Hecke.heckeLSeries chi m s =
          Work.FIArea5.S16Hecke.heckeLSeries chi₀ m s *
            ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))) := by
  classical
  -- at each prime, the local roots delivered by `localPrimeExistsMineStrong`
  let c₁ : ℕ → ℂ := fun p =>
    if hp : p.Prime then (localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose else 0
  let c₂ : ℕ → ℂ := fun p =>
    if hp : p.Prime then
      ((localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose_spec).choose else 0
  have hc₁ : ∀ p (hp : p.Prime),
      c₁ p = (localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose := by
    intro p hp
    dsimp only [c₁]
    rw [dif_pos hp]
  have hc₂ : ∀ p (hp : p.Prime),
      c₂ p = ((localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose_spec).choose := by
    intro p hp
    dsimp only [c₂]
    rw [dif_pos hp]
  have hspec : ∀ p (hp : p.Prime),
      (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0) ∧ ∀ e : ℕ,
        heckeLam chi m (p ^ e) =
          ∑ j ∈ Finset.range (e + 1), betaC (c₁ p) (c₂ p) j * heckeLam chi₀ m (p ^ (e - j)) := by
    intro p hp
    have h := (localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose_spec.choose_spec
    rw [hc₁ p hp, hc₂ p hp]
    exact h
  refine ⟨(4 * d).primeFactors, c₁, c₂, ?_, ?_⟩
  · intro p hpS
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hp4 : p ∣ 4 * d := Nat.dvd_of_mem_primeFactors hpS
    exact ⟨hpp, hp4, (hspec p hpp).1, (hspec p hpp).2.1⟩
  · intro s hs
    have hA := heckeLSeries_eulerProduct_hasProd chi m hchi.1.1 hchi.1.2.1 hchi.1.2.2.1 hs
    have hB := heckeLSeries_eulerProduct_hasProd chi₀ m hpart.2.2.1 hpart.2.2.2.1
      hpart.2.2.2.2.1 hs
    have hC : HasProd (fun p : Nat.Primes => if (p : ℕ) ∈ (4 * d).primeFactors then
        corrFacP c₁ c₂ s (p : ℕ) else 1)
        (∏ p ∈ (4 * d).primeFactors, corrFacP c₁ c₂ s p) := by
      simpa only [corrFacP] using
        hasProdCorrFamily (4 * d).primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
          c₁ c₂ s
    -- the local factor of `χ` is `1` at the primes dividing `4d`
    have hAone : ∀ p : Nat.Primes, (p : ℕ) ∈ (4 * d).primeFactors →
        (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s))) = 1 := by
      intro p hpS
      have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors hpS
      have hp4 : (p : ℕ) ∣ 4 * d := Nat.dvd_of_mem_primeFactors hpS
      have hrew : (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          = ∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) * (((p : ℕ) : ℂ) ^ (-s)) ^ e := by
        refine tsum_congr fun e => ?_
        rw [div_eq_mul_inv, cpow_inv_mul_eq (p : ℕ) e s hpp.ne_zero]
      rw [hrew, tsum_eq_single 0 (fun b hb => by
        rw [heckeLamPrimePowZeroBad d hd chi m hchi (p : ℕ) hpp hp4 b (Nat.pos_of_ne_zero hb),
          zero_mul])]
      simp [heckeLam_one, hchi.1.1]
    -- and the local factor of `χ₀` times the correction is `1` there
    have hBone : ∀ p : Nat.Primes, (p : ℕ) ∈ (4 * d).primeFactors →
        (∑' e : ℕ, heckeLam chi₀ m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          * corrFacP c₁ c₂ s (p : ℕ) = 1 := by
      intro p hpS
      have hpp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors hpS
      have hp4 : (p : ℕ) ∣ 4 * d := Nat.dvd_of_mem_primeFactors hpS
      have hl : ∀ e : ℕ, heckeLam chi m ((p : ℕ) ^ e) =
          ∑ j ∈ Finset.range (e + 1), betaC (c₁ (p : ℕ)) (c₂ (p : ℕ)) j
            * heckeLam chi₀ m ((p : ℕ) ^ (e - j)) := (hspec (p : ℕ) hpp).2.2
      have hz : ∀ e : ℕ, 1 ≤ e → heckeLam chi m ((p : ℕ) ^ e) = 0 :=
        fun e he => heckeLamPrimePowZeroBad d hd chi m hchi (p : ℕ) hpp hp4 e he
      have key := localFactor_at_bad hpp hs hpart.2.2.2.2.1 hchi.1.1 hpart.2.2.1 hl hz
      simpa only [corrFacP] using key
    -- the pointwise comparison of the local factors
    have hpt : ∀ p : Nat.Primes,
        (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          = (∑' e : ℕ, heckeLam chi₀ m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
            * (if (p : ℕ) ∈ (4 * d).primeFactors then corrFacP c₁ c₂ s (p : ℕ) else 1) := by
      intro p
      by_cases hmem : (p : ℕ) ∈ (4 * d).primeFactors
      · rw [if_pos hmem, hAone p hmem, hBone p hmem]
      · rw [if_neg hmem, mul_one]
        have hp4 : ¬ (p : ℕ) ∣ 4 * d := fun hdiv =>
          hmem (Nat.mem_primeFactors.mpr ⟨p.2, hdiv, by omega⟩)
        refine tsum_congr fun e => ?_
        rw [heckeLamPrimePowEqGood d hd chi M chi₀ m hchi hpart (p : ℕ) p.2 hp4 e]
    have hBC := hB.mul hC
    have hA' : HasProd (fun p : Nat.Primes =>
        ∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
        (heckeLSeries chi₀ m s * ∏ p ∈ (4 * d).primeFactors, corrFacP c₁ c₂ s p) :=
      hBC.congr_fun fun p => hpt p
    simpa only [corrFacP] using HasProd.unique hA hA'

end

end Work.FIArea6Hecke.R
