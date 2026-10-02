import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.Setup
import Submission.Commons.NumberTheory.Linnik.exists_prime_lt_rpow_of_primeSum_pos
import Submission.Commons.NumberTheory.Linnik.tentWeight_bounds

/-!
# `Assembly` — Heath-Brown's §13 reduction (the main argument of Area 2)

From the two inputs of `Submission.Work.LinnikAreas.Setup`

* `ClassIdentityHyp` — the box-restricted explicit formula for the class prime sum, uniform in `q`
  (Heath-Brown's Lemma 13.1, with the far zeros kept as an explicit error term), and
* `FarBoundHyp` — the smallness of the mass of the far zeros (Heath-Brown's Lemma 13.2),

we deduce `Work.LinnikContract.Area2`: if the signed sum of the boxed zero-sums over the
non-principal characters stays below `K² - ε`, then the progression `a mod q` contains a prime
`p ≤ q^{11/2}`.

The arithmetic is the classical one: writing `PS` for the tent-weighted prime sum,
`𝓛⁻¹ PS ≥ K²/φ(q) - φ(q)⁻¹ (box sum) - φ(q)⁻¹ (far mass) - O(1/(φ(q)𝓛))`,
and the hypothesis bounds the box sum by `K² - ε`; choosing `R = R(ε/4)` and then `q₀` large
enough that the explicit-formula error and the prime-power tail together are below `ε/2`
makes `PS > 0`, so that a prime of the window `(q^{4.9}, q^{5.5}]` in the class exists.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- The tent-weighted prime sum over the class `a mod q`, for primes `≤ X`
(`L = 11/2`, `K = 3/10`). -/
abbrev primeSum (q X a : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 X).filter (fun p => p.Prime ∧ p ≡ a [MOD q]),
    (Real.log (p : ℝ) / (p : ℝ)) *
      Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10) (Real.log (p : ℝ) / Real.log (q : ℝ))

/-- The signed box sum `Σ_{χ ≠ 1} Re(χ̄(a) · boxSum q L K R χ)`. -/
abbrev boxSigned (q : ℕ) [NeZero q] (R : ℝ) (a : ℕ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
    ((starRingEnd ℂ) (χ (a : ZMod q)) * boxSum q (11/2) (3/10) R χ).re

/-- Total mass of the far zeros over all non-principal characters mod `q`. -/
abbrev farTotalMass (q : ℕ) [NeZero q] (R : ℝ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), farSum q (11/2) (3/10) R χ

lemma farTotalMass_nonneg (q : ℕ) [NeZero q] (R : ℝ) : 0 ≤ farTotalMass q R :=
  Finset.sum_nonneg fun χ _ => farSum_nonneg q (11/2) (3/10) R χ

lemma primeSum_nonneg (q X a : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ primeSum q X a := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hp1 : 1 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
  have hpr : (p : ℝ) > 0 := by exact_mod_cast (by omega : 0 < p)
  have hw : 0 ≤ Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
      (Real.log (p : ℝ) / Real.log (q : ℝ)) :=
    (Commons.NumberTheory.Linnik.tentWeight_bounds (L := 11/2) (K := 3/10)
      (by norm_num) (by norm_num)).1 _
  positivity


lemma filter_Icc_eq_filter_range (q X a : ℕ) :
    (Finset.Icc 1 X).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q])
      = (Finset.range (X + 1)).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by omega, h3⟩
  · rintro ⟨h2, h3⟩
    have hp2 : 2 ≤ p := h3.1.two_le
    exact ⟨⟨by omega, by omega⟩, h3⟩

/-- **The main argument of Area 2.**  From the uniform box-restricted explicit formula
(`ClassIdentityHyp`) and the smallness of the mass of the far zeros (`FarBoundHyp`) we obtain
Heath-Brown's §13 reduction. -/
theorem area2_of_classIdentity (hid : ClassIdentityHyp) (hfar : FarBoundHyp) :
    Work.LinnikContract.Area2 := by
  intro ε hε
  obtain ⟨C, hCpos, hidC⟩ := hid
  have hε4 : 0 < ε / 4 := by linarith only [hε]
  obtain ⟨R, hRpos, q₁, hq₁⟩ := hfar (ε / 4) hε4
  have hlogtop : Filter.Tendsto (fun q : ℕ => Real.log (q : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hlogtop.eventually_ge_atTop (4 * C / ε))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hlogtop.eventually_ge_atTop (1 / ε))
  have hrpow : Filter.Tendsto (fun q : ℕ => (q : ℝ) ^ (-((29 : ℝ) / 20))) Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (y := (29 : ℝ) / 20) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hδ : (0 : ℝ) < 1 / (4 * C) := by positivity
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp
    (hrpow.eventually (IsOpen.mem_nhds isOpen_Iio hδ))
  refine ⟨R, hRpos, max (max N₁ N₂) (max N₃ (max q₁ 2)), ?_⟩
  intro q hq hqne a hcop hB
  have hN₁' : N₁ ≤ q := by
    have h1 : N₁ ≤ max N₁ N₂ := le_max_left _ _
    have h2 : max N₁ N₂ ≤ max (max N₁ N₂) (max N₃ (max q₁ 2)) := le_max_left _ _
    exact le_trans h1 (le_trans h2 hq)
  have hN₂' : N₂ ≤ q := by
    have h1 : N₂ ≤ max N₁ N₂ := le_max_right _ _
    have h2 : max N₁ N₂ ≤ max (max N₁ N₂) (max N₃ (max q₁ 2)) := le_max_left _ _
    exact le_trans h1 (le_trans h2 hq)
  have hN₃' : N₃ ≤ q := by
    have h1 : N₃ ≤ max N₃ (max q₁ 2) := le_max_left _ _
    have h2 : max N₃ (max q₁ 2) ≤ max (max N₁ N₂) (max N₃ (max q₁ 2)) := le_max_right _ _
    exact le_trans h1 (le_trans h2 hq)
  have hq₁' : q₁ ≤ q := by
    have h1 : q₁ ≤ max q₁ 2 := le_max_left _ _
    have h2 : max q₁ 2 ≤ max N₃ (max q₁ 2) := le_max_right _ _
    have h3 : max N₃ (max q₁ 2) ≤ max (max N₁ N₂) (max N₃ (max q₁ 2)) := le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 hq))
  have hq2 : 2 ≤ q := by
    have h1 : 2 ≤ max q₁ 2 := le_max_right _ _
    have h2 : max q₁ 2 ≤ max N₃ (max q₁ 2) := le_max_right _ _
    have h3 : max N₃ (max q₁ 2) ≤ max (max N₁ N₂) (max N₃ (max q₁ 2)) := le_max_right _ _
    exact le_trans h1 (le_trans h2 (le_trans h3 hq))
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hφpos : 0 < (q.totient : ℝ) := by
    have h : 0 < q.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast h
  have hfarq : farTotalMass q R ≤ ε / 4 := hq₁ q hq₁'
  have hsmall1 : C / Real.log (q : ℝ) ≤ ε / 4 := by
    have h4 : 4 * C ≤ ε * Real.log (q : ℝ) := by
      have := (div_le_iff₀ hε).mp (hN₁ q hN₁')
      linarith only [this]
    rw [div_le_div_iff₀ hlogq (by norm_num : (0 : ℝ) < 4)]
    linarith only [h4]
  set Y : ℝ := C * (q.totient : ℝ) * (q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ) with hY
  have hsmall2 : Y ≤ ε / 4 := by
    have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hφle : (q.totient : ℝ) ≤ (q : ℝ) := by
      have h : q.totient ≤ q := Nat.totient_le q
      exact_mod_cast h
    have hrpowq : (q : ℝ) ^ (-((29 : ℝ) / 20)) < 1 / (4 * C) := hN₃ q hN₃'
    have hqinv : 4 * C * (q : ℝ) ^ (-((29 : ℝ) / 20)) < 1 := by
      have := mul_lt_mul_of_pos_left hrpowq (by positivity : (0 : ℝ) < 4 * C)
      have he : 4 * C * (1 / (4 * C)) = 1 := by field_simp
      rwa [he] at this
    have hsplit : (q : ℝ) * (q : ℝ) ^ (-((49 : ℝ) / 20)) = (q : ℝ) ^ (-((29 : ℝ) / 20)) := by
      have h1 : (1 : ℝ) + -((49 : ℝ) / 20) = -((29 : ℝ) / 20) := by norm_num
      have h2 := Real.rpow_add hqpos (1 : ℝ) (-((49 : ℝ) / 20))
      rw [h1, Real.rpow_one] at h2
      exact h2.symm
    have hbound : C * (q.totient : ℝ) * (q : ℝ) ^ (-((49 : ℝ) / 20))
        ≤ C * (q : ℝ) ^ (-((29 : ℝ) / 20)) := by
      have hrp : 0 ≤ (q : ℝ) ^ (-((49 : ℝ) / 20)) := le_of_lt (Real.rpow_pos_of_pos hqpos _)
      have hφle' : C * (q.totient : ℝ) ≤ C * (q : ℝ) := by nlinarith only [hφle, hCpos]
      calc C * (q.totient : ℝ) * (q : ℝ) ^ (-((49 : ℝ) / 20))
          = (C * (q.totient : ℝ)) * (q : ℝ) ^ (-((49 : ℝ) / 20)) := rfl
        _ ≤ (C * (q : ℝ)) * (q : ℝ) ^ (-((49 : ℝ) / 20)) :=
            mul_le_mul_of_nonneg_right hφle' hrp
        _ = C * ((q : ℝ) * (q : ℝ) ^ (-((49 : ℝ) / 20))) := by rw [mul_assoc]
        _ = C * (q : ℝ) ^ (-((29 : ℝ) / 20)) := by rw [hsplit]
    have hlogbig : 1 ≤ ε * Real.log (q : ℝ) := by
      have h := hN₂ q hN₂'
      have he := (div_le_iff₀ hε).mp h
      linarith only [he]
    have hstep1 : Y ≤ (1 / 4) / Real.log (q : ℝ) := by
      rw [hY, div_le_div_iff₀ hlogq hlogq]
      have hY2 : C * (q : ℝ) ^ (-((29 : ℝ) / 20)) < 1 / 4 := by linarith only [hqinv]
      have hY1 : C * (q.totient : ℝ) * (q : ℝ) ^ (-((49 : ℝ) / 20)) < 1 / 4 :=
        lt_of_le_of_lt hbound hY2
      nlinarith only [hY1, hlogq, hqinv, hbound]
    have hstep2 : (1 / 4) / Real.log (q : ℝ) ≤ ε / 4 := by
      rw [div_le_div_iff₀ hlogq (by norm_num : (0 : ℝ) < 4)]
      linarith only [hlogbig]
    exact le_trans hstep1 hstep2
  set X : ℕ := Nat.ceil ((q : ℝ) ^ ((11 : ℝ) / 2)) with hXdef
  have hXq : (q : ℝ) ^ ((11 : ℝ) / 2) ≤ (X : ℝ) := by
    rw [hXdef]; exact Nat.le_ceil _
  set PSc : ℂ := ∑ p ∈ (Finset.Icc 1 X).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]),
      ((Real.log (p : ℝ) / (p : ℝ) : ℝ) : ℂ) *
        ((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
          (Real.log (p : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) with hPSc
  set Sc : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      (starRingEnd ℂ) (χ (a : ZMod q)) * boxSum q (11/2) (3/10) R χ with hSc
  have hPSc_eq : PSc = ((primeSum q X a : ℝ) : ℂ) := by
    rw [hPSc, primeSum, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun p _ => (Complex.ofReal_mul _ _).symm
  have hSc_re : Sc.re = boxSigned q R a := by
    rw [hSc, boxSigned, Complex.re_sum]
  set Z : ℂ := ((Real.log (q : ℝ) : ℂ))⁻¹ * PSc
      - ((((3 / 10 : ℝ) ^ 2) / (q.totient : ℝ) : ℝ) : ℂ)
      + ((q.totient : ℂ))⁻¹ * Sc with hZ
  have hidq : ‖Z‖ ≤ C / ((q.totient : ℝ) * Real.log (q : ℝ))
      + (q.totient : ℝ)⁻¹ * farTotalMass q R
      + C * (q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ) := by
    have h := hidC q hq2 R hRpos a hcop X hXq
    rw [show -((49 : ℝ) / 10) / 2 = -((49 : ℝ) / 20) by norm_num] at h
    simpa only [hZ, hPSc, hSc, farTotalMass] using h
  have hneg : -‖Z‖ ≤ Z.re := by
    have h := Complex.re_le_norm (-Z)
    simp only [Complex.neg_re, norm_neg] at h
    linarith only [h]
  have hZre : Z.re = (Real.log (q : ℝ))⁻¹ * primeSum q X a
      - ((3 / 10 : ℝ) ^ 2) / (q.totient : ℝ) + (q.totient : ℝ)⁻¹ * boxSigned q R a := by
    have hl : ((Real.log (q : ℝ) : ℂ))⁻¹ = (((Real.log (q : ℝ))⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_inv]
    have h3 : (((q.totient : ℂ))⁻¹ * Sc).re = (q.totient : ℝ)⁻¹ * boxSigned q R a := by
      conv_lhs =>
        rw [show ((q.totient : ℂ)) = (((q.totient : ℝ)) : ℂ) by push_cast; ring]
      rw [← Complex.ofReal_inv, Complex.re_ofReal_mul, hSc_re]
    rw [hZ, hPSc_eq, hl]
    rw [Complex.add_re, Complex.sub_re]
    rw [h3]
    simp only [Complex.re_ofReal_mul, Complex.ofReal_re]
  have key : (Real.log (q : ℝ))⁻¹ * primeSum q X a
      ≥ ((3 / 10 : ℝ) ^ 2) / (q.totient : ℝ) - (q.totient : ℝ)⁻¹ * boxSigned q R a
        - (C / ((q.totient : ℝ) * Real.log (q : ℝ))
            + (q.totient : ℝ)⁻¹ * farTotalMass q R
            + C * (q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by
    have h := hneg
    rw [hZre] at h
    linarith only [hqne, hidq, hneg, hZre]
  have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφpos
  have hlogqne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlogq
  set W : ℝ := (q.totient : ℝ) * ((Real.log (q : ℝ))⁻¹ * primeSum q X a) with hW
  have key2 : W
      ≥ ((3 / 10 : ℝ) ^ 2) - boxSigned q R a - C / Real.log (q : ℝ) - farTotalMass q R - Y := by
    have hm := mul_le_mul_of_nonneg_left key (le_of_lt hφpos)
    have e : (q.totient : ℝ) * (((3 / 10 : ℝ) ^ 2) / (q.totient : ℝ)
          - (q.totient : ℝ)⁻¹ * boxSigned q R a
          - (C / ((q.totient : ℝ) * Real.log (q : ℝ))
              + (q.totient : ℝ)⁻¹ * farTotalMass q R
              + C * (q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)))
        = ((3 / 10 : ℝ) ^ 2) - boxSigned q R a - C / Real.log (q : ℝ) - farTotalMass q R - Y := by
      rw [hY]
      field_simp
      ring
    rw [e] at hm
    exact hm
  have hposPS : 0 < primeSum q X a := by
    have hcore : ((3 / 10 : ℝ) ^ 2) - boxSigned q R a > ε := by linarith only [hB, hqne]
    have h1 : C / Real.log (q : ℝ) + farTotalMass q R + Y ≤ 3 * (ε / 4) := by linarith only [hqne, hfarq, hsmall1, hsmall2]
    have hbig : 0 < W := by linarith only [key2, hcore, h1, hε, hqne, hB, hfarq, hsmall1, hsmall2]
    have h2 : 0 < (Real.log (q : ℝ))⁻¹ * primeSum q X a := by
      by_contra hc
      have hc' : (Real.log (q : ℝ))⁻¹ * primeSum q X a ≤ 0 := le_of_not_gt hc
      nlinarith only [hbig, hc', hφpos, hW, hc]
    have h3 : 0 < Real.log (q : ℝ) * ((Real.log (q : ℝ))⁻¹ * primeSum q X a) :=
      mul_pos hlogq h2
    rwa [← mul_assoc, mul_inv_cancel₀ hlogqne, one_mul] at h3
  have hpos' : 0 < ∑ p ∈ (Finset.range (X + 1)).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]),
      (Real.log (p : ℝ) / (p : ℝ)) *
        Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
          (Real.log (p : ℝ) / Real.log (q : ℝ)) := by
    rw [← filter_Icc_eq_filter_range q X a]
    exact hposPS
  obtain ⟨p, hp, hmod, hlt⟩ := Commons.NumberTheory.Linnik.exists_prime_lt_rpow_of_primeSum_pos
    (q := q) (a := a) (X := X) hq2 (L := 11/2) (K := 3/10)
    (by norm_num) (by norm_num) hpos'
  exact ⟨p, hp, hmod, le_of_lt hlt⟩

end Work.LinnikAreas
