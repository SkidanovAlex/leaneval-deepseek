import Mathlib
import Submission.Work.FIArea6Hecke.R.HasConductorFEDefs
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea6Hecke.R.gaussCriterionOfPrimitiveAt
import Submission.Work.FIArea6Hecke.R.conductorGaussSumDualityClean
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.heckeUnitLift
import Submission.Work.FIArea6Hecke.R.gnorm_lt_of_dvd_of_not_dvd
import Submission.Work.FIArea6Hecke.R.heckeLSeriesConductorRatio
import Submission.Work.FIArea6Hecke.R.fullHeckeLSeriesOrbit
import Submission.Work.FIArea6Hecke.R.mellin_allZTheta
import Submission.Work.FIArea6Hecke.R.levelThetaFE
import Submission.Work.FIArea6Hecke.R.HeckeCompletionAll
import Submission.Work.FIArea6Hecke.R2.eulerCorrTrivial
import Submission.Work.FIArea6Hecke.R.allZThetaLawClean
import Submission.Work.FIArea6Hecke.R.AllZThetaDefs
import Submission.Work.FIArea6Hecke.R.allZTheta_meas_li
import Submission.Work.FIArea6Hecke.R.allZTheta_exp_decay
import Submission.Work.FIArea6Hecke.R.thetaLamAgree
import Submission.Work.FIArea5.S16Hecke.h1166TwistDefs
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_conj
import Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive
import Submission.Work.FIArea4.GaussMoebiusCore
import Submission.Work.FIArea6Hecke.R.conductorPartnerUnitAgree
import Submission.Work.FIArea6Hecke.R.conductorPartnerUnitAgreeNoHnt

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.RC

open Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIPlan
open Work.FIArea5.S16Hecke

noncomputable section

/-! ## Elementary auxiliary facts -/

/-- A unit modulo `4d` is a unit modulo any divisor `M` of `4d`. -/
lemma isUnitMod_of_dvd_4d {d : ℕ} {M z : GaussianInt}
    (hM : M ∣ ((((4 * d : ℕ) : ℤ)) : GaussianInt))
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : IsUnitMod M z := by
  obtain ⟨w, hw⟩ := hz
  exact ⟨w, dvd_trans hM hw⟩

/-- A unit of `ℤ[i]` is a unit modulo any modulus. -/
lemma isUnitMod_of_isUnit {M z : GaussianInt} (hz : IsUnit z) : IsUnitMod M z := by
  obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.mp hz
  exact ⟨w, by rw [hw, sub_self]; exact dvd_zero M⟩

/-- `gnorm M = 1` forces `M` to be a unit of `ℤ[i]`. -/
lemma isUnit_of_gnorm_eq_one {z : GaussianInt} (h : Work.FIPlan.gnorm z = 1) : IsUnit z :=
  Zsqrtd.norm_eq_one_iff.mp h

/-- Cancellation of the Euler product against the `2`-adic factor. -/
lemma mul_inv_cancel_right' {A L D E : ℂ} (hE : E ≠ 0) :
    A * L * D⁻¹ = A * (L * E) * (D⁻¹ * E⁻¹) := by
  rw [show A * (L * E) * (D⁻¹ * E⁻¹) = A * L * (E * E⁻¹) * D⁻¹ by ring,
    mul_inv_cancel₀ hE, mul_one]

/-- `gnorm` of a natural number embedded in `ℤ[i]` is its square. -/
lemma gnorm_natCast' (n : ℕ) : Work.FIPlan.gnorm (((n : ℕ) : ℤ) : GaussianInt) = n ^ 2 := by
  have hcast : (((n : ℕ) : ℤ) : GaussianInt) = ((n : ℕ) : GaussianInt) := rfl
  rw [hcast]
  simp only [Work.FIPlan.gnorm, Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast]
  ring

/-! ## Elementary analytic and Gaussian-integer helpers -/

/-- `0 ^ k = 0` for the `ℤ`-exponent convention used by `fullHeckeLSeries`, `k ≥ 1`. -/
private lemma zero_zpow_of_one_le {k : ℕ} (hk : 1 ≤ k) : (0 : ℂ) ^ (k : ℤ) = 0 := by
  rw [zpow_natCast, zero_pow (by omega)]

/-- The all-`z` theta series only depends on the weight away from `0`, provided `k ≥ 1`. -/
private lemma allZTheta_congr_off_zero {f g : GaussianInt → ℂ} (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ z : GaussianInt, z ≠ 0 → f z = g z) (u : ℝ) :
    allZTheta f k u = allZTheta g k u := by
  rw [allZTheta, allZTheta]
  refine tsum_congr (fun z => ?_)
  by_cases hz : z = 0
  · subst hz
    have htc : GaussianInt.toComplex (0 : GaussianInt) = 0 := by
      simp [GaussianInt.toComplex_def]
    have h0k : (0 : ℂ) ^ k = 0 := zero_pow (by omega)
    rw [htc, h0k]
    ring
  · rw [h z hz]

/-- The complete Hecke series only depends on the weight away from `0`, provided `k ≥ 1`. -/
private lemma fullHeckeLSeries_congr_off_zero {f g : GaussianInt → ℂ} (k : ℕ) (hk : 1 ≤ k)
    (h : ∀ z : GaussianInt, z ≠ 0 → f z = g z) (t : ℂ) :
    fullHeckeLSeries f (k : ℤ) t = fullHeckeLSeries g (k : ℤ) t := by
  rw [fullHeckeLSeries, fullHeckeLSeries]
  refine tsum_congr (fun z => ?_)
  by_cases hz : z = 0
  · subst hz
    have htc : GaussianInt.toComplex (0 : GaussianInt) = 0 := by
      simp [GaussianInt.toComplex_def]
    have h0k : (0 : ℂ) ^ (k : ℤ) = 0 := zero_zpow_of_one_le hk
    rw [htc, zero_div, h0k]
    ring
  · rw [h z hz]

/-- A Gaussian integer whose fourth power is `1` has `4j`-th power `1` after mapping to `ℂ`. -/
private lemma toComplex_pow_eq_one {u : GaussianInt} (hu : u ^ 4 = 1) (j : ℕ) :
    (GaussianInt.toComplex u) ^ (4 * j) = 1 := by
  rw [pow_mul, show (GaussianInt.toComplex u) ^ 4 = 1 by rw [← map_pow, hu, map_one], one_pow]

/-- `i ^ k = 1` forces `4 ∣ k`. -/
private lemma four_dvd_of_I_pow_eq_one {k : ℕ} (h : (Complex.I : ℂ) ^ k = 1) : 4 ∣ k := by
  have hmod : k % 4 = 0 := by
    have h' := h
    rw [Complex.I_pow_eq_pow_mod] at h'
    rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h0 | h1 | h2 | h3
    · exact h0
    · exact absurd (congrArg Complex.re h') (by simp [Complex.I_re, h1])
    · exact absurd (congrArg Complex.re h') (by norm_num [Complex.I_sq, h2])
    · exact absurd (congrArg Complex.re h') (by simp [Complex.I_pow_three, Complex.I_re, h3])
  exact Nat.dvd_of_mod_eq_zero hmod

/-! ## Auxiliary statements delegated to the fleet -/

/-- **The Euler-factor ratio between a strict character and its conductor partner, confined to the
odd rational primes dividing `4d`**, with the strong coefficient condition `‖cᵢ p‖ = 1 ∨ cᵢ p = 0`
(the odd-prime version of `heckeLSeriesConductorRatio`). -/
theorem heckeLSeriesConductorRatioOdd (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (M : GaussianInt) (chi₀ : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hpart : IsConductorPartner d chi M chi₀) :
    ∃ (S : Finset ℕ) (c₁ c₂ : ℕ → ℂ),
      (∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ p ≠ 2 ∧
        (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0)) ∧
      (∀ s : ℂ, 1 < s.re →
        Work.FIArea5.S16Hecke.heckeLSeries chi m s =
          Work.FIArea5.S16Hecke.heckeLSeries chi₀ m s *
            ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))) := by
  classical
  let c₁ : ℕ → ℂ := fun p =>
    if hp : p.Prime then (localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose
    else 0
  let c₂ : ℕ → ℂ := fun p =>
    if hp : p.Prime then
      ((localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose_spec).choose else 0
  have hc₁ : ∀ p (hp : p.Prime),
      c₁ p = (localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose := by
    intro p hp; dsimp only [c₁]; rw [dif_pos hp]
  have hc₂ : ∀ p (hp : p.Prime),
      c₂ p = ((localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose_spec).choose := by
    intro p hp; dsimp only [c₂]; rw [dif_pos hp]
  have hspec : ∀ p (hp : p.Prime),
      (‖c₁ p‖ = 1 ∨ c₁ p = 0) ∧ (‖c₂ p‖ = 1 ∨ c₂ p = 0) ∧ ∀ e : ℕ,
        heckeLam chi m (p ^ e) =
          ∑ j ∈ Finset.range (e + 1), betaC (c₁ p) (c₂ p) j * heckeLam chi₀ m (p ^ (e - j)) := by
    intro p hp
    have h := (localPrimeExistsMineStrong d hd chi M chi₀ m hchi hpart p hp).choose_spec.choose_spec
    rw [hc₁ p hp, hc₂ p hp]
    exact h
  let S : Finset ℕ := (4 * d).primeFactors.filter (fun p => p ≠ 2)
  have hSdef : S = (4 * d).primeFactors.filter (fun p => p ≠ 2) := rfl
  have hSprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp; rw [hSdef] at hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hS4 : ∀ p ∈ S, p ∣ 4 * d := by
    intro p hp; rw [hSdef] at hp
    exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hS2 : ∀ p ∈ S, p ≠ 2 := by
    intro p hp; rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).2
  refine ⟨S, c₁, c₂, ?_, ?_⟩
  · intro p hp
    exact ⟨hSprime p hp, hS4 p hp, hS2 p hp, (hspec p (hSprime p hp)).1,
      (hspec p (hSprime p hp)).2.1⟩
  · intro s hs
    have hA := heckeLSeries_eulerProduct_hasProd chi m hchi.1.1 hchi.1.2.1 hchi.1.2.2.1 hs
    have hB := heckeLSeries_eulerProduct_hasProd chi₀ m hpart.2.2.1 hpart.2.2.2.1
      hpart.2.2.2.2.1 hs
    have hC : HasProd (fun p : Nat.Primes => if (p : ℕ) ∈ S then
        corrFacP c₁ c₂ s (p : ℕ) else 1)
        (∏ p ∈ S, corrFacP c₁ c₂ s p) := by
      simpa only [corrFacP] using
        hasProdCorrFamily S (fun p hp => hSprime p hp) c₁ c₂ s
    have hAone : ∀ p : Nat.Primes, (p : ℕ) ∈ S →
        (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s))) = 1 := by
      intro p hpS
      have hpp : (p : ℕ).Prime := hSprime _ hpS
      have hp4 : (p : ℕ) ∣ 4 * d := hS4 _ hpS
      have hrew : (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          = ∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) * ((((p : ℕ) : ℂ) ^ (-s)) ^ e) := by
        refine tsum_congr fun e => ?_
        rw [div_eq_mul_inv, cpow_inv_mul_eq (p : ℕ) e s hpp.ne_zero]
      rw [hrew, tsum_eq_single 0 (fun b hb => by
        rw [heckeLamPrimePowZeroBad d hd chi m hchi (p : ℕ) hpp hp4 b (Nat.pos_of_ne_zero hb),
          zero_mul])]
      simp [heckeLam_one, hchi.1.1]
    have hBone : ∀ p : Nat.Primes, (p : ℕ) ∈ S →
        (∑' e : ℕ, heckeLam chi₀ m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          * corrFacP c₁ c₂ s (p : ℕ) = 1 := by
      intro p hpS
      have hpp : (p : ℕ).Prime := hSprime _ hpS
      have hp4 : (p : ℕ) ∣ 4 * d := hS4 _ hpS
      have hl : ∀ e : ℕ, heckeLam chi m ((p : ℕ) ^ e) =
          ∑ j ∈ Finset.range (e + 1), betaC (c₁ (p : ℕ)) (c₂ (p : ℕ)) j
            * heckeLam chi₀ m ((p : ℕ) ^ (e - j)) := (hspec (p : ℕ) hpp).2.2
      have hz : ∀ e : ℕ, 1 ≤ e → heckeLam chi m ((p : ℕ) ^ e) = 0 :=
        fun e he => heckeLamPrimePowZeroBad d hd chi m hchi (p : ℕ) hpp hp4 e he
      have key := localFactor_at_bad hpp hs hpart.2.2.2.2.1 hchi.1.1 hpart.2.2.1 hl hz
      simpa only [corrFacP] using key
    have hpt : ∀ p : Nat.Primes,
        (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          = (∑' e : ℕ, heckeLam chi₀ m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
            * (if (p : ℕ) ∈ S then corrFacP c₁ c₂ s (p : ℕ) else 1) := by
      intro p
      by_cases hmem : (p : ℕ) ∈ S
      · rw [if_pos hmem, hAone p hmem, hBone p hmem]
      · rw [if_neg hmem, mul_one]
        by_cases hp2 : (p : ℕ) = 2
        · rw [hp2, localFactorTwo_eq_one chi m hchi.1.1 hs,
            localFactorTwo_eq_one chi₀ m hpart.2.2.1 hs]
        · have hp4 : ¬ (p : ℕ) ∣ 4 * d := fun hdiv => hmem (by
            rw [hSdef]
            exact Finset.mem_filter.mpr
              ⟨Nat.mem_primeFactors.mpr ⟨p.2, hdiv, by omega⟩, hp2⟩)
          refine tsum_congr fun e => ?_
          rw [heckeLamPrimePowEqGood d hd chi M chi₀ m hchi hpart (p : ℕ) p.2 hp4 e]
    have hBC := hB.mul hC
    have hA' : HasProd (fun p : Nat.Primes =>
        ∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
        (heckeLSeries chi₀ m s * ∏ p ∈ S, corrFacP c₁ c₂ s p) :=
      hBC.congr_fun fun p => hpt p
    simpa only [corrFacP] using HasProd.unique hA hA'

/-- `conj (x ^ conj s) = conj x ^ s`. -/
private lemma conj_cpow (x : ℂ) (hx : x.arg ≠ Real.pi) (s : ℂ) :
    (starRingEnd ℂ) (x ^ ((starRingEnd ℂ) s)) = (starRingEnd ℂ) x ^ s := by
  have h := Complex.cpow_conj x s hx
  rw [h, Complex.conj_conj]

/-- `conj (c ^ conj s) = c ^ s` for a non-negative real `c`. -/
private lemma conj_cpow_ofReal (c : ℝ) (hc : 0 ≤ c) (s : ℂ) :
    (starRingEnd ℂ) ((c : ℂ) ^ ((starRingEnd ℂ) s)) = (c : ℂ) ^ s := by
  rw [conj_cpow _ _ s, Complex.conj_ofReal]
  exact Complex.arg_ofReal_of_nonneg hc ▸ (Ne.symm Real.pi_ne_zero)

/-- `conj (n ^ conj s) = n ^ s` for a natural number `n`. -/
private lemma conj_cpow_natCast (n : ℕ) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-((starRingEnd ℂ) s))) = (n : ℂ) ^ (-s) := by
  have hx : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero
  have h := Complex.cpow_conj (n : ℂ) (-s) hx
  rw [map_neg, Complex.conj_natCast] at h
  rw [h, Complex.conj_conj]

/-- The conjugate of the finite product of inverse local factors. -/
private lemma conj_prod_localFactors (S : Finset ℕ) (c₁ c₂ : ℕ → ℂ) (s : ℂ) :
    (starRingEnd ℂ) (∏ p ∈ S,
        ((1 - c₁ p * ((p : ℂ) ^ (-((starRingEnd ℂ) s))))
          * (1 - c₂ p * ((p : ℂ) ^ (-((starRingEnd ℂ) s)))))⁻¹)
      = ∏ p ∈ S,
        ((1 - (starRingEnd ℂ) (c₁ p) * ((p : ℂ) ^ (-s)))
          * (1 - (starRingEnd ℂ) (c₂ p) * ((p : ℂ) ^ (-s))))⁻¹ := by
  rw [map_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  simp only [map_inv₀, map_mul, map_sub, map_one, conj_cpow_natCast]

/-- Conjugation of the Hecke `L`-series. -/
private lemma conj_heckeLSeries (chi : GaussianInt → ℂ) (k : ℕ) (s : ℂ) :
    (starRingEnd ℂ) (Work.FIArea5.S16Hecke.heckeLSeries
        (fun z : GaussianInt => (starRingEnd ℂ) (chi z)) (k : ℤ) ((starRingEnd ℂ) s))
      = Work.FIArea5.S16Hecke.heckeLSeries chi (-(k : ℤ)) s := by
  have h := Work.FIArea5.S16Hecke.heckeLSeries_conj
    (fun z : GaussianInt => (starRingEnd ℂ) (chi z)) k s
  rw [show (fun z : GaussianInt => star ((starRingEnd ℂ) (chi z))) = chi from
    funext (fun z => by simp)] at h
  exact h.symm

/-- `s ↦ conj (f (conj s))` is entire when `f` is. -/
private lemma analyticOn_conj_comp (f : ℂ → ℂ) (h : AnalyticOn ℂ f Set.univ) :
    AnalyticOn ℂ (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) Set.univ := by
  have hdiff : Differentiable ℂ f := differentiableOn_univ.mp h.differentiableOn
  have hd : Differentiable ℂ (fun s => (starRingEnd ℂ) (f ((starRingEnd ℂ) s))) := by
    intro x
    have h1 : DifferentiableAt ℂ ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ))
        ((starRingEnd ℂ) ((starRingEnd ℂ) x)) := (hdiff ((starRingEnd ℂ) x)).conj_conj
    simpa [Function.comp_def] using h1
  exact DifferentiableOn.analyticOn (differentiableOn_univ.mpr hd) isOpen_univ

/-- **The conjugation transfer for the strong conductor equation.** -/
theorem hasConductorFE_conj (d : ℕ) (chi : GaussianInt → ℂ) (k : ℕ) :
    HasConductorFE d (fun z => star (chi z)) (k : ℤ) → HasConductorFE d chi (-(k : ℤ)) := by
  intro h
  unfold HasConductorFE at h ⊢
  simp only [Complex.star_def] at h ⊢
  obtain ⟨X, c₁, c₂, S, Phi, W, hX1, hX2, hS, hWne, hPhi, hFE, hagree⟩ := h
  have hXpi : (0 : ℝ) ≤ X / Real.pi := div_nonneg (by linarith) Real.pi_nonneg
  refine ⟨X, (fun p => (starRingEnd ℂ) (c₁ p)), (fun p => (starRingEnd ℂ) (c₂ p)), S,
    (fun s => (starRingEnd ℂ) (Phi ((starRingEnd ℂ) s))), (starRingEnd ℂ) W,
    hX1, hX2, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hS p hp
    refine ⟨h1, h2, ?_, ?_⟩
    · rcases h3 with h3 | h3
      · exact Or.inl (by rw [Complex.norm_conj, h3])
      · exact Or.inr (by simp [h3])
    · rcases h4 with h4 | h4
      · exact Or.inl (by rw [Complex.norm_conj, h4])
      · exact Or.inr (by simp [h4])
  · exact (map_ne_zero (starRingEnd ℂ)).mpr hWne
  · exact analyticOn_conj_comp Phi hPhi
  · intro s
    have h1 := hFE ((starRingEnd ℂ) s)
    have h2 := congrArg (starRingEnd ℂ) h1
    rw [map_mul] at h2
    simp only [map_sub, map_one, Complex.conj_conj] at h2 ⊢
    exact h2
  · intro s hs
    beta_reduce
    have hre : 1 + |(((k : ℤ)) : ℝ)| / 2 < ((starRingEnd ℂ) s).re := by
      rw [Complex.conj_re]
      simpa only [Int.cast_neg, abs_neg] using hs
    have hsrc := hagree ((starRingEnd ℂ) s) hre
    rw [hsrc, map_mul, map_mul, map_mul]
    have hG : (starRingEnd ℂ)
          (Complex.Gamma ((starRingEnd ℂ) s + ((|(((k : ℤ)) : ℝ)| / 2 : ℝ) : ℂ)))
        = Complex.Gamma (s + ((|((-(k : ℤ)) : ℝ)| / 2 : ℝ) : ℂ)) := by
      rw [← Complex.Gamma_conj, map_add, Complex.conj_conj, Complex.conj_ofReal]
      congr 1
      rw [abs_neg]
    have hL := conj_heckeLSeries chi k s
    have hprod := conj_prod_localFactors S c₁ c₂ s
    rw [conj_cpow_ofReal (X / Real.pi) hXpi s, hG, hL, hprod]
    simp only [Int.cast_neg, abs_neg]

/-- **The all-`z` theta transfer.**  From a theta transformation law at level `N(M)` for the
all-`z` theta series of a character `χ₀` of modulus `M`, the completion
`(√(N M)/π)^s Γ(s+k/2)·fullHeckeLSeries χ₀ k s / 4` is entire and self-dual.  The degenerate case
(the theta series vanishing identically) is handled by taking `Φ := 0`; it forces the `L`-series to
vanish, so the agreement still holds. -/
theorem allZThetaFE (M : GaussianInt) (hM : M ≠ 0)
    (chi₀ : GaussianInt → ℂ) (k : ℕ) (A : ℂ) (hA : A ≠ 0)
    (hmeas : AEMeasurable (allZTheta chi₀ k) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hli : MeasureTheory.LocallyIntegrableOn (allZTheta chi₀ k) (Set.Ioi (0 : ℝ)))
    (hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
        ‖allZTheta chi₀ k u‖ ≤ C * Real.exp (-Real.pi * u))
    (hmellin : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
      mellin (allZTheta chi₀ k) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
          fullHeckeLSeries chi₀ (k : ℤ) (s - (k : ℂ) / 2))
    (hlaw : ∀ u : ℝ, 0 < u → allZTheta chi₀ k u =
        A * ((u : ℂ) ^ (-(k : ℤ) - 1)) *
          star (allZTheta chi₀ k (1 / ((Work.FIPlan.gnorm M : ℕ) * u)))) :
    ∃ (Phi : ℂ → ℂ) (W : ℂ), W ≠ 0 ∧ AnalyticOn ℂ Phi Set.univ ∧
      (∀ s : ℂ, Phi s = W * star (Phi (star (1 - s)))) ∧
      (∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        Phi s = (((Real.sqrt ((Work.FIPlan.gnorm M : ℕ) : ℝ)) / Real.pi : ℝ) : ℂ) ^ s *
          Complex.Gamma (s + ((k : ℝ) / 2 : ℝ)) *
          (fullHeckeLSeries chi₀ (k : ℤ) s / 4)) := by
  have hMgn : 0 < Work.FIPlan.gnorm M :=
    Nat.pos_of_ne_zero (fun h => hM (eq_zero_of_gnorm_eq_zero h))
  have hR : (0 : ℝ) < ((Work.FIPlan.gnorm M : ℕ) : ℝ) := by exact_mod_cast hMgn
  by_cases hzero : ∀ u : ℝ, 0 < u → allZTheta chi₀ k u = 0
  · refine ⟨fun _ => 0, 1, one_ne_zero, analyticOn_const, ?_, ?_⟩
    · intro s; simp
    · intro s hs
      have hL := L_eq_zero_of_theta_eq_zero hmellin hzero s hs
      rw [hL]; ring
  · push_neg at hzero
    obtain ⟨u₁, hu₁, hne⟩ := hzero
    have hconst := levelConstOfLaw ((Work.FIPlan.gnorm M : ℕ) : ℝ) hR
        (allZTheta chi₀ k) k A hlaw ⟨u₁, hu₁, hne⟩
    have hXi := levelXi_eq_mellin ((Work.FIPlan.gnorm M : ℕ) : ℝ) hR
        (allZTheta chi₀ k) k A hlaw hmeas hli hdec
    have hlam := thetaLamAgree ((Work.FIPlan.gnorm M : ℕ) : ℝ) hR
        (allZTheta chi₀ k) k A (fullHeckeLSeries chi₀ (k : ℤ)) hmellin hXi
    have hfe := levelLam_fe ((Work.FIPlan.gnorm M : ℕ) : ℝ) hR
        (allZTheta chi₀ k) k A hconst
    obtain ⟨_, _, hAan, hEan⟩ := levCutFacts
        ((Work.FIPlan.gnorm M : ℕ) : ℝ) hR (allZTheta chi₀ k) k hmeas hli hdec
    have hXiAn : AnalyticOn ℂ (thetaXi ((Work.FIPlan.gnorm M : ℕ) : ℝ)
        (allZTheta chi₀ k) k A) Set.univ := by
      refine hAan.add ?_
      exact ((analyticOn_const (v := A)).mul
        (analyticOn_const_cpow_affine
          (((Work.FIPlan.gnorm M : ℕ) : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr hR.ne') k)).mul hEan
    have hLamAn : AnalyticOn ℂ (thetaLam ((Work.FIPlan.gnorm M : ℕ) : ℝ)
        (allZTheta chi₀ k) k A) Set.univ :=
      analyticOn_thetaLam ((Work.FIPlan.gnorm M : ℕ) : ℝ) hR (allZTheta chi₀ k) k A hXiAn
    refine ⟨fun s => (4 : ℂ)⁻¹ * thetaLam ((Work.FIPlan.gnorm M : ℕ) : ℝ)
          (allZTheta chi₀ k) k A s,
      A * ((((Real.sqrt ((Work.FIPlan.gnorm M : ℕ) : ℝ)) : ℝ)) : ℂ) ^ (k + 1), ?_, ?_, ?_, ?_⟩
    · exact mul_ne_zero hA
        (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hR).ne'))
    · exact (analyticOn_const (v := (4 : ℂ)⁻¹)).mul hLamAn
    · intro s
      dsimp only
      have h := hfe s
      have h4 : star ((4 : ℂ)⁻¹) = (4 : ℂ)⁻¹ := by rw [star_inv₀]; norm_num
      rw [h, star_mul, h4]
      ring
    · intro s hs
      dsimp only
      have h := hlam s hs
      have hcast : (((k : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) / 2 := by push_cast; ring
      rw [h, ← hcast]
      ring

/-- **The all-`z` theta transformation law.**  From a Gauss sum of the weight `χ₀` supported on
`M ℤ[i]` and satisfying the duality `condGaussSum M χ₀ (M γ) = N(M)·τ·conj (χ₀ γ̄)`, the all-`z`
theta series obeys the theta transformation law at level `N(M)`.  This is
`Work.FIArea6Hecke.azc_allZThetaLaw` with its (unused) non-vanishing hypothesis dropped. -/
theorem allZThetaLaw' (M : GaussianInt) (hM : M ≠ 0)
    (chi₀ : GaussianInt → ℂ) (m : ℕ) (hchi : IsCharModStrict M chi₀) (τ : ℂ) (hτ : τ ≠ 0)
    (hsupp : ∀ ξ : GaussianInt, ¬ (M ∣ ξ) → condGaussSum M chi₀ ξ = 0)
    (hdual : ∀ γ : GaussianInt, condGaussSum M chi₀ (M * γ) =
      ((gnorm M : ℕ) : ℂ) * τ * star (chi₀ (gconjInt γ))) :
    ∃ A : ℂ, A ≠ 0 ∧ ∀ u : ℝ, 0 < u →
      allZTheta chi₀ m u = A * ((u : ℂ) ^ (-(m : ℤ) - 1)) *
        star (allZTheta chi₀ m (1 / ((gnorm M : ℕ) * u))) := by
  refine ⟨((gnorm M : ℕ) : ℂ) ^ (-(m : ℤ) - 1) * τ * (-Complex.I) ^ m * ((M : ℂ)) ^ m,
    ?_, ?_⟩
  · have hq : 0 < gnorm M := Work.FIArea4.gnorm_pos hM
    have hqR : (0 : ℝ) < ((gnorm M : ℕ) : ℝ) := by exact_mod_cast hq
    have hqC : (((gnorm M : ℕ)) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hqR)
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ hτ) ?_) ?_
    · exact zpow_ne_zero _ hqC
    · exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
    · refine pow_ne_zero _ ?_
      rw [Ne, GaussianInt.toComplex_eq_zero]
      exact hM
  · intro u hu
    have hdual_u := Work.FIArea6Hecke.azc_allZ_poisson_dual M chi₀ m τ hM hchi hsupp hdual hu
    rw [Work.FIArea6Hecke.azc_allZ_poisson_form M chi₀ hM m hchi hu, hdual_u]
    have huz : (u : ℂ) ^ (-(m : ℤ) - 1) = ((u : ℂ) ^ (m + 1))⁻¹ := by
      rw [show (-(m : ℤ) - 1) = -(((m + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    have hqz : ((((gnorm M : ℕ)) : ℂ)) ^ (-(m : ℤ) - 1) =
        ((((gnorm M : ℕ)) : ℂ) ^ (m + 1))⁻¹ := by
      rw [show (-(m : ℤ) - 1) = -(((m + 1 : ℕ)) : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    rw [huz, hqz, Work.FIArea6Hecke.azc_lvl]
    have hq : 0 < gnorm M := Work.FIArea4.gnorm_pos hM
    have hqR : (0 : ℝ) < ((gnorm M : ℕ) : ℝ) := by exact_mod_cast hq
    have hqC : (((gnorm M : ℕ)) : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast]
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt hqR)
    have huC : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
    have hup : (u : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ huC
    have hqp : (((gnorm M : ℕ)) : ℂ) ^ (m + 1) ≠ 0 := pow_ne_zero _ hqC
    have hqm : (((gnorm M : ℕ)) : ℂ) ^ m ≠ 0 := pow_ne_zero _ hqC
    rw [div_pow]
    field_simp
    ring

/-- **The core assembly of the conductor-normalised Hecke functional equation.**  Given a strict
character `χ'` whose Hecke `L`-series equals that of `χ`, a conductor partner `χ₀` at modulus `M`,
the Gauss-sum duality data `(τ, hsupp, hdual)` and the analytic inputs for the all-`z` theta
series of `χ₀`, together with the normalisation `unitSum χ₀ k = 4`, the target holds. -/
theorem conductorFECore (d : ℕ) (hd : 1 ≤ d) (chi' : GaussianInt → ℂ) (k : ℕ)
    (hchi' : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi')
    (M : GaussianInt) (chi₀ : GaussianInt → ℂ) (hM0 : M ≠ 0)
    (hpart : IsConductorPartner d chi' M chi₀)
    (τ : ℂ) (hτ : τ ≠ 0)
    (hsupp : ∀ ξ : GaussianInt, ¬ (M ∣ ξ) → condGaussSum M chi₀ ξ = 0)
    (hdual : ∀ γ : GaussianInt, condGaussSum M chi₀ (M * γ) =
      ((Work.FIPlan.gnorm M : ℕ) : ℂ) * τ * star (chi₀ (gconjInt γ)))
    (hmeas : AEMeasurable (allZTheta chi₀ k) (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (hli : MeasureTheory.LocallyIntegrableOn (allZTheta chi₀ k) (Set.Ioi (0 : ℝ)))
    (hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
        ‖allZTheta chi₀ k u‖ ≤ C * Real.exp (-Real.pi * u))
    (hmellin : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
      mellin (allZTheta chi₀ k) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
          fullHeckeLSeries chi₀ (k : ℤ) (s - (k : ℂ) / 2))
    (hunitSum : Work.FIArea5.S16Hecke.unitSum chi₀ k = 4) :
    HasConductorFE d chi' (k : ℤ) := by
  have hStrict : IsCharModStrict M chi₀ :=
    ⟨hpart.2.2.1, hpart.2.2.2.1, hpart.2.2.2.2.1, hpart.2.2.2.2.2.1, hpart.2.2.2.2.2.2.1⟩
  have hpsi2 : ‖psi chi₀ (k : ℤ) oneAddI‖ = 1 ∨ psi chi₀ (k : ℤ) oneAddI = 0 :=
    psi_norm_eq_one_or_eq_zero hpart.2.2.1 hpart.2.2.2.1 hpart.2.2.2.2.2.1 hpart.2.2.2.2.1
      hpart.2.2.2.2.2.2.1 (k : ℤ) (by decide : Work.FIArea5.S16Hecke.oneAddI ≠ 0)
  obtain ⟨S, c₁, c₂, hS, hEul⟩ :=
    heckeLSeriesConductorRatioOdd d hd chi' M chi₀ (k : ℤ) hchi' hpart
  have hkey : ∀ s : ℂ, 1 < s.re →
      Work.FIArea5.S16Hecke.heckeLSeries chi' (k : ℤ) s *
        (∏ p ∈ insert 2 S,
          ((1 - (if p = 2 then psi chi₀ (k : ℤ) oneAddI else c₁ p) * ((p : ℂ) ^ (-s))) *
            (1 - (if p = 2 then 0 else c₂ p) * ((p : ℂ) ^ (-s))))⁻¹)
      = fullHeckeLSeries chi₀ (k : ℤ) s / 4 := by
    intro s hs1
    have h2S : (2 : ℕ) ∉ S := fun h => (hS 2 h).2.2.1 rfl
    have hnorm2 : ‖((2 : ℂ) ^ (-s))‖ < 1 := by
      have h2c : ‖((2 : ℂ) ^ (-s))‖ = (2 : ℝ) ^ (-s.re) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
          Complex.norm_natCast_cpow_of_pos (by norm_num : (0 : ℕ) < 2), Complex.neg_re]
        norm_num
      rw [h2c]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hD : (1 - psi chi₀ (k : ℤ) oneAddI * ((2 : ℂ) ^ (-s))) ≠ 0 := by
      intro h
      have hc : ‖psi chi₀ (k : ℤ) oneAddI * ((2 : ℂ) ^ (-s))‖ = 1 := by
        rw [(sub_eq_zero.mp h).symm, norm_one]
      have hb : ‖psi chi₀ (k : ℤ) oneAddI * ((2 : ℂ) ^ (-s))‖ < 1 := by
        rw [norm_mul]
        rcases hpsi2 with h2 | h2
        · rw [h2, one_mul]; exact hnorm2
        · rw [h2, norm_zero, zero_mul]; norm_num
      linarith
    have hEne : (∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) *
        (1 - c₂ p * ((p : ℂ) ^ (-s))))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
      have hpP : p.Prime := (hS p hp).1
      have hp2 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpP.one_lt
      have hn : ‖((p : ℂ) ^ (-s))‖ < 1 := by
        rw [Complex.norm_natCast_cpow_of_pos hpP.pos, Complex.neg_re]
        exact Real.rpow_lt_one_of_one_lt_of_neg hp2 (by linarith)
      have hbnd : ∀ c : ℂ, (‖c‖ = 1 ∨ c = 0) → ‖c * ((p : ℂ) ^ (-s))‖ < 1 := by
        intro c hc
        rw [norm_mul]
        rcases hc with hc | hc
        · rw [hc, one_mul]; exact hn
        · rw [hc, norm_zero, zero_mul]; norm_num
      refine mul_ne_zero ?_ ?_
      · intro h
        have hc : ‖c₁ p * ((p : ℂ) ^ (-s))‖ = 1 := by rw [(sub_eq_zero.mp h).symm, norm_one]
        linarith [hbnd (c₁ p) (hS p hp).2.2.2.1, hc]
      · intro h
        have hc : ‖c₂ p * ((p : ℂ) ^ (-s))‖ = 1 := by rw [(sub_eq_zero.mp h).symm, norm_one]
        linarith [hbnd (c₂ p) (hS p hp).2.2.2.2, hc]
    have hunitSumZ : (∑ ε ∈ Work.FIArea5.S16Hecke.units4, chi₀ ε * (ε.toComplex) ^ (k : ℤ)) = 4 := by
      rw [← hunitSum]
      unfold Work.FIArea5.S16Hecke.unitSum
      refine Finset.sum_congr rfl (fun ε hε => ?_)
      rw [zpow_natCast]
    have horb := Work.FIArea6Hecke.R.fullHeckeLSeriesOrbit chi₀ (k : ℤ)
      hpart.2.2.1 hpart.2.2.2.1 hpart.2.2.2.2.1 s hs1
    rw [hunitSumZ] at horb
    have hprod : (∏ p ∈ insert 2 S,
          ((1 - (if p = 2 then psi chi₀ (k : ℤ) oneAddI else c₁ p) * ((p : ℂ) ^ (-s))) *
            (1 - (if p = 2 then 0 else c₂ p) * ((p : ℂ) ^ (-s))))⁻¹)
        = (1 - psi chi₀ (k : ℤ) oneAddI * ((2 : ℂ) ^ (-s)))⁻¹ *
          (∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) *
            (1 - c₂ p * ((p : ℂ) ^ (-s)))))⁻¹ := by
      rw [Finset.prod_insert h2S]
      have hcong : (∏ p ∈ S,
            ((1 - (if p = 2 then psi chi₀ (k : ℤ) oneAddI else c₁ p) * ((p : ℂ) ^ (-s))) *
              (1 - (if p = 2 then 0 else c₂ p) * ((p : ℂ) ^ (-s))))⁻¹)
          = (∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) *
              (1 - c₂ p * ((p : ℂ) ^ (-s)))))⁻¹ := by
        rw [Finset.prod_inv_distrib]
        congr 1
        refine Finset.prod_congr rfl (fun p hp => ?_)
        have hp2 : p ≠ 2 := fun h => h2S (h ▸ hp)
        rw [if_neg hp2, if_neg hp2]
      rw [hcong, if_pos rfl, if_pos rfl]
      simp only [zero_mul, sub_zero, mul_one]
      rfl
    have h1 : Work.FIArea6Hecke.R.fullHeckeLSeries chi₀ (k : ℤ) s / 4 =
        Work.FIArea5.S16Hecke.heckeLSeries chi₀ (k : ℤ) s /
          (1 - psi chi₀ (k : ℤ) oneAddI * ((2 : ℂ) ^ (-s))) := by
      rw [div_eq_div_iff (by norm_num : (4 : ℂ) ≠ 0) hD]
      rw [mul_comm (Work.FIArea5.S16Hecke.heckeLSeries chi₀ (k : ℤ) s) 4]
      exact horb
    have h2 : Work.FIArea5.S16Hecke.heckeLSeries chi₀ (k : ℤ) s =
        Work.FIArea5.S16Hecke.heckeLSeries chi' (k : ℤ) s *
          (∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) *
            (1 - c₂ p * ((p : ℂ) ^ (-s)))))⁻¹ := by
      rw [hEul s hs1, mul_assoc, mul_inv_cancel₀ hEne, mul_one]
    rw [hprod, h1, h2]
    ring
  obtain ⟨C, hC, hlaw⟩ := allZThetaLaw' M hM0 chi₀ k hStrict τ hτ hsupp hdual
  obtain ⟨Phi, W, hW, hAn, hFE, hAgr⟩ :=
    allZThetaFE M hM0 chi₀ k C hC hmeas hli hdec hmellin hlaw
  refine ⟨Real.sqrt (Work.FIPlan.gnorm M : ℝ),
    (fun p => if p = 2 then psi chi₀ (k : ℤ) oneAddI else c₁ p),
    (fun p => if p = 2 then 0 else c₂ p), insert 2 S, Phi, W, ?_, ?_, ?_, hW, hAn, hFE, ?_⟩
  · refine Real.one_le_sqrt.mpr ?_
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Work.FIArea4.gnorm_ne_zero hM0)
  · have hdvd := Work.FIArea4.gnorm_dvd hpart.1
    rw [gnorm_natCast' (4 * d)] at hdvd
    have hle : Work.FIPlan.gnorm M ≤ (4 * d) ^ 2 := Nat.le_of_dvd (by positivity) hdvd
    calc Real.sqrt (Work.FIPlan.gnorm M : ℝ) ≤ Real.sqrt (((4 * d) ^ 2 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by exact_mod_cast hle)
      _ = 4 * (d : ℝ) := by
          rw [show ((((4 * d) ^ 2 : ℕ)) : ℝ) = ((4 * d : ℝ)) ^ 2 by push_cast; ring,
            Real.sqrt_sq (by positivity)]
  · intro p hp
    rw [Finset.mem_insert] at hp
    rcases hp with rfl | hpS
    · exact ⟨Nat.prime_two, ⟨2 * d, by ring⟩, by simpa using hpsi2, by simp⟩
    · obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hS p hpS
      exact ⟨hp1, hp2, by simpa [hp3] using hp4, by simpa [hp3] using hp5⟩
  · intro s hs
    have hs' : 1 + (k : ℝ) / 2 < s.re := by
      have hm : |(((k : ℤ)) : ℝ)| = (k : ℝ) := by simp
      simpa [hm] using hs
    have hs1 : 1 < s.re := by
      have : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      linarith
    have hkabs : |(((k : ℤ)) : ℝ)| = (k : ℝ) := by simp
    rw [hAgr s hs', ← hkey s hs1, hkabs]
    ring

/-- Transport of the conductor-normalised functional equation along an equality of Hecke
`L`-series. -/
lemma hasConductorFE_congr {d : ℕ} {k : ℕ} {chi chi' : GaussianInt → ℂ}
    (h : ∀ s : ℂ, Work.FIArea5.S16Hecke.heckeLSeries chi' (k : ℤ) s =
      Work.FIArea5.S16Hecke.heckeLSeries chi (k : ℤ) s)
    (H : HasConductorFE d chi' (k : ℤ)) : HasConductorFE d chi (k : ℤ) := by
  obtain ⟨X, c₁, c₂, S, Phi, W, hX1, hX2, hS, hW, hAn, hFE, hagr⟩ := H
  exact ⟨X, c₁, c₂, S, Phi, W, hX1, hX2, hS, hW, hAn, hFE,
    fun s hs => by rw [← h s]; exact hagr s hs⟩

/-- **The non-trivial case**: `χ` is non-trivial on a primary unit modulo `4d`. -/
lemma nontrivialCase (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (k : ℕ)
    (hchi : IsCharMod4dStrict d chi)
    (htriv : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      IsUnitMod4d d z ∧ chi z ≠ 1)
    (hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      IsUnitMod4d d z ∧ psi chi (k : ℤ) z ≠ 1) :
    HasConductorFE d chi (k : ℤ) := by
  have hchiT : IsCharMod4dStrict d (twist chi k) := twist_isCharMod4dStrict d hd chi k hchi
  have htrivT : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      IsUnitMod4d d z ∧ twist chi k z ≠ 1 := by
    obtain ⟨z, hz1, hz2, hz3⟩ := htriv
    exact ⟨z, hz1, hz2, by rw [twist_eq_of_isPrimary chi k hz1]; exact hz3⟩
  obtain ⟨M, chi₀, hpart, hprimU, hg, hagree⟩ :=
    Work.FIArea6Hecke.R.conductorPartnerUnitAgree d hd (twist chi k) hchiT htrivT
  have hM0 : M ≠ 0 := hpart.2.1
  have hStrict : IsCharModStrict M chi₀ :=
    ⟨hpart.2.2.1, hpart.2.2.2.1, hpart.2.2.2.2.1, hpart.2.2.2.2.2.1, hpart.2.2.2.2.2.2.1⟩
  obtain ⟨z0, hz0i, hz0u, hz0ne⟩ := htrivT
  have hz0uM : IsUnitMod M z0 := isUnitMod_of_dvd_4d hpart.1 hz0u
  have hntM : ∃ z : GaussianInt, IsUnitMod M z ∧ chi₀ z ≠ 1 :=
    ⟨z0, hz0uM, by rw [hagree z0 hz0u hz0uM]; exact hz0ne⟩
  have hnotUnit : ¬ IsUnit M := by
    intro hU
    obtain ⟨z1, hz1u, hz1ne⟩ := hntM
    obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.mp hU
    have hdvd : M ∣ (z1 - 1) := ⟨w * (z1 - 1), by rw [← mul_assoc, ← hw, one_mul]⟩
    refine hz1ne ?_
    rw [hpart.2.2.2.2.2.1 z1 1 hdvd, hpart.2.2.1]
  have hchi0 : chi₀ 0 = 0 := by
    have h0 : ¬ IsUnitMod M 0 := by
      rintro ⟨w, hw⟩
      rw [zero_mul, zero_sub] at hw
      exact hnotUnit (isUnit_iff_dvd_one.mpr (dvd_neg.mp hw))
    exact hpart.2.2.2.2.2.2.1 0 h0
  have hunitSum : Work.FIArea5.S16Hecke.unitSum chi₀ k = 4 := by
    rw [← Work.FIArea5.S16Hecke.twist_unitSum d hd chi k hchi.1]
    unfold Work.FIArea5.S16Hecke.unitSum
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu4 : IsUnitMod4d d u :=
      isUnitMod_of_isUnit (isUnit_of_gnorm_eq_one (gnorm_of_mem_units4 hu))
    have huM : IsUnitMod M u := isUnitMod_of_isUnit (isUnit_of_gnorm_eq_one (gnorm_of_mem_units4 hu))
    rw [hagree u hu4 huM]
  obtain ⟨τ, hτ, hsupp, hdual⟩ := conductorGaussSumDualityClean M hM0 hg chi₀ hStrict hprimU hntM
  have hchibd : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1 := hpart.2.2.2.2.1
  obtain ⟨hmeas, hli⟩ := allZTheta_meas_li chi₀ k hchibd
  obtain ⟨Cdec, _hCdec0, u₀, hu₀, hdec0⟩ := allZTheta_exp_decay chi₀ k hchibd hchi0
  have hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖allZTheta chi₀ k u‖ ≤ C * Real.exp (-Real.pi * u) := ⟨Cdec, u₀, hu₀, hdec0⟩
  have hmellin : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
      mellin (allZTheta chi₀ k) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
          fullHeckeLSeries chi₀ (k : ℤ) (s - (k : ℂ) / 2) :=
    fun s hs => mellin_allZTheta chi₀ k hchibd hchi0 hs
  exact hasConductorFE_congr (fun s => congrFun (Work.FIArea6Hecke.heckeLSeries_twist chi k) s)
    (conductorFECore d hd (twist chi k) k hchiT M chi₀ hM0 hpart τ hτ hsupp hdual
      hmeas hli hdec hmellin hunitSum)


/-- **The trivial case**: `χ` is trivial on the primary units modulo `4d`.  Then `χ` agrees with
the constant weight `1` on the primary units, so its Hecke `L`-series differs from the one of the
constant weight only by the finite Euler correction at the odd primes dividing `4d`.  The constant
weight itself is handled by the level-one theta series: the `2`-adic Euler factor has coefficient
`ψ(1+i) = i^k`, which is a fourth root of unity. -/
lemma trivialCase (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (k : ℕ)
    (hchi : IsCharMod4dStrict d chi)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → IsUnitMod4d d z → chi z = 1)
    (hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ IsUnitMod4d d z ∧
      psi chi (k : ℤ) z ≠ 1) :
    HasConductorFE d chi (k : ℤ) := by
  -- `k ≥ 1`: at `k = 0` the Größencharacter is `χ` itself, trivial on the primary units
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · exfalso
      obtain ⟨z, hz1, hz2, hz3⟩ := hnt
      refine hz3 ?_
      rw [hk0, psi]
      simp only [Nat.cast_zero, zpow_zero, mul_one]
      exact htriv z hz1 hz2
    · exact hkpos
  by_cases h4 : 4 ∣ k
  · -- ## Case `4 ∣ k`: the constant weight at level `1`
    let chiD : GaussianInt → ℂ := fun z => if z = 0 then 0 else 1
    have hchiDbd : ∀ z : GaussianInt, ‖chiD z‖ ≤ 1 := by
      intro z
      by_cases hz : z = 0 <;> simp [chiD, hz]
    have hchiD0 : chiD 0 = 0 := by simp [chiD]

    have hfun : ∀ u : ℝ, allZTheta (fun _ : GaussianInt => (1 : ℂ)) k u = allZTheta chiD k u :=
      fun u => allZTheta_congr_off_zero k hk (fun z hz => by simp [chiD, hz]) u
    have hfull : ∀ t : ℂ, fullHeckeLSeries chiD (k : ℤ) t =
        fullHeckeLSeries (fun _ : GaussianInt => (1 : ℂ)) (k : ℤ) t :=
      fun t => fullHeckeLSeries_congr_off_zero k hk (fun z hz => by simp [chiD, hz]) t
    obtain ⟨hmeasD, hliD⟩ := allZTheta_meas_li chiD k hchiDbd
    have hmeas1 : AEMeasurable (allZTheta (fun _ : GaussianInt => (1 : ℂ)) k)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
      rw [show allZTheta (fun _ : GaussianInt => (1 : ℂ)) k = allZTheta chiD k from
        funext hfun]
      exact hmeasD
    have hli1 : MeasureTheory.LocallyIntegrableOn
        (allZTheta (fun _ : GaussianInt => (1 : ℂ)) k) (Set.Ioi (0 : ℝ)) := by
      rw [show allZTheta (fun _ : GaussianInt => (1 : ℂ)) k = allZTheta chiD k from
        funext hfun]
      exact hliD
    obtain ⟨Cd, _hCd, u₀, hu₀, hdecD⟩ := allZTheta_exp_decay chiD k hchiDbd hchiD0
    have hdec1 : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
        ‖allZTheta (fun _ : GaussianInt => (1 : ℂ)) k u‖ ≤ C * Real.exp (-Real.pi * u) :=
      ⟨Cd, u₀, hu₀, fun u hu => by rw [hfun u]; exact hdecD u hu⟩
    have hmellin1 : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        mellin (allZTheta (fun _ : GaussianInt => (1 : ℂ)) k) s = Complex.Gamma s *
          ((Real.pi : ℂ) ^ (-s)) *
          fullHeckeLSeries (fun _ : GaussianInt => (1 : ℂ)) (k : ℤ) (s - (k : ℂ) / 2) := by
      intro s hs
      rw [show allZTheta (fun _ : GaussianInt => (1 : ℂ)) k = allZTheta chiD k from
          funext hfun, mellin_allZTheta chiD k hchiDbd hchiD0 hs, hfull]
    have hpart1 : IsConductorPartner d chi (1 : GaussianInt) (fun _ : GaussianInt => (1 : ℂ)) :=
      Work.FIArea6Hecke.R2.one_isConductorPartner d chi htriv
    have hStrict1 : IsCharModStrict (1 : GaussianInt) (fun _ : GaussianInt => (1 : ℂ)) :=
      ⟨rfl, fun _ _ => by simp, fun _ => by simp, fun _ _ _ => rfl,
        fun z hz => absurd ⟨(0 : GaussianInt), one_dvd _⟩ hz⟩

    have hcond1 : ∀ ξ : GaussianInt,
        condGaussSum (1 : GaussianInt) (fun _ : GaussianInt => (1 : ℂ)) ξ = 1 := by
      intro ξ
      rw [condGaussSum, gnorm_one]
      norm_num
    have hsupp1 : ∀ ξ : GaussianInt, ¬ ((1 : GaussianInt) ∣ ξ) →
        condGaussSum (1 : GaussianInt) (fun _ : GaussianInt => (1 : ℂ)) ξ = 0 :=
      fun ξ hξ => absurd (one_dvd ξ) hξ
    have hdual1 : ∀ γ : GaussianInt,
        condGaussSum (1 : GaussianInt) (fun _ : GaussianInt => (1 : ℂ)) (1 * γ) =
          ((gnorm (1 : GaussianInt) : ℕ) : ℂ) * (1 : ℂ) *
            star ((fun _ : GaussianInt => (1 : ℂ)) (gconjInt γ)) := by
      intro γ
      rw [one_mul, hcond1 γ, gnorm_one]
      simp
    have hunitSum1 : unitSum (fun _ : GaussianInt => (1 : ℂ)) k = 4 := by
      obtain ⟨j, rfl⟩ := h4
      rw [unitSum, units4, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [one_mul]
      rw [toComplex_pow_eq_one (by decide : (1 : GaussianInt) ^ 4 = 1) j,
        toComplex_pow_eq_one (by decide : (-1 : GaussianInt) ^ 4 = 1) j,
        toComplex_pow_eq_one (by decide : (⟨0, 1⟩ : GaussianInt) ^ 4 = 1) j,
        toComplex_pow_eq_one (by decide : (⟨0, -1⟩ : GaussianInt) ^ 4 = 1) j]
      norm_num
    exact conductorFECore d hd chi k hchi 1 (fun _ : GaussianInt => (1 : ℂ)) one_ne_zero
      hpart1 1 one_ne_zero hsupp1 hdual1 hmeas1 hli1 hdec1 hmellin1 hunitSum1
  · -- ## Case `¬ 4 ∣ k`: the twist has a genuine conductor
    have hchiT : IsCharMod4dStrict d (twist chi k) := twist_isCharMod4dStrict d hd chi k hchi
    obtain ⟨M, chi₀, hpart, hprimU, hagree, hwit⟩ :=
      Work.FIArea6Hecke.R.conductorPartnerUnitAgreeNoHnt d hd (twist chi k) hchiT
    have hM0 : M ≠ 0 := hpart.2.1
    have hStrict : IsCharModStrict M chi₀ :=
      ⟨hpart.2.2.1, hpart.2.2.2.1, hpart.2.2.2.2.1, hpart.2.2.2.2.2.1, hpart.2.2.2.2.2.2.1⟩

    -- `M` is not a unit: otherwise `χ₀ ≡ 1`, forcing `twist χ k i = 1` and hence `4 ∣ k`
    have hgn : 2 ≤ gnorm M := by
      by_contra hlt
      push_neg at hlt
      have hg1 : gnorm M = 1 := by
        have hpos : gnorm M ≠ 0 := Work.FIArea4.gnorm_ne_zero hM0
        omega
      have hunit : IsUnit M := isUnit_of_gnorm_eq_one hg1
      obtain ⟨w, hw⟩ := isUnit_iff_dvd_one.mp hunit
      have hconst : ∀ z : GaussianInt, chi₀ z = 1 := by
        intro z
        have hdvd : M ∣ (z - 1) := ⟨w * (z - 1), by rw [← mul_assoc, ← hw, one_mul]⟩
        rw [hpart.2.2.2.2.2.1 z 1 hdvd, hpart.2.2.1]
      have hi4 : IsUnitMod4d d (⟨0, 1⟩ : GaussianInt) :=
        isUnitMod_of_isUnit
          (isUnit_of_gnorm_eq_one (by decide : gnorm (⟨0, 1⟩ : GaussianInt) = 1))
      have hiM : IsUnitMod M (⟨0, 1⟩ : GaussianInt) :=
        isUnitMod_of_isUnit
          (isUnit_of_gnorm_eq_one (by decide : gnorm (⟨0, 1⟩ : GaussianInt) = 1))
      have htw : twist chi k (⟨0, 1⟩ : GaussianInt) = 1 := by
        rw [← hagree (⟨0, 1⟩ : GaussianInt) hi4 hiM]
        exact hconst _
      have htk := term_k hchi.1 k 1 (by norm_num)
      rw [pow_one, htw, one_mul] at htk
      have hIk : (Complex.I : ℂ) ^ k = 1 := by
        simpa [GaussianInt.toComplex_def] using htk
      exact h4 (four_dvd_of_I_pow_eq_one hIk)
    have hnotUnit : ¬ IsUnit M := by
      intro hU
      have h1 : gnorm M = 1 := Zsqrtd.norm_eq_one_iff.mpr hU
      omega
    have hntM : ∃ z : GaussianInt, IsUnitMod M z ∧ chi₀ z ≠ 1 := hwit hgn
    obtain ⟨τ, hτ, hsupp, hdual⟩ :=
      conductorGaussSumDualityClean M hM0 hgn chi₀ hStrict hprimU hntM
    have hchi0 : chi₀ 0 = 0 := by
      have h0 : ¬ IsUnitMod M 0 := by
        rintro ⟨w, hw⟩
        rw [zero_mul, zero_sub] at hw
        exact hnotUnit (isUnit_iff_dvd_one.mpr (dvd_neg.mp hw))
      exact hpart.2.2.2.2.2.2.1 0 h0
    have hunitSum : unitSum chi₀ k = 4 := by
      rw [← Work.FIArea5.S16Hecke.twist_unitSum d hd chi k hchi.1]
      unfold unitSum
      refine Finset.sum_congr rfl (fun u hu => ?_)
      have hu4 : IsUnitMod4d d u :=
        isUnitMod_of_isUnit (isUnit_of_gnorm_eq_one (gnorm_of_mem_units4 hu))
      have huM : IsUnitMod M u :=
        isUnitMod_of_isUnit (isUnit_of_gnorm_eq_one (gnorm_of_mem_units4 hu))
      rw [hagree u hu4 huM]
    have hchibd : ∀ z : GaussianInt, ‖chi₀ z‖ ≤ 1 := hpart.2.2.2.2.1
    obtain ⟨hmeas, hli⟩ := allZTheta_meas_li chi₀ k hchibd
    obtain ⟨Cdec, _hCdec0, u₀, hu₀, hdec0⟩ := allZTheta_exp_decay chi₀ k hchibd hchi0
    have hdec : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
        ‖allZTheta chi₀ k u‖ ≤ C * Real.exp (-Real.pi * u) := ⟨Cdec, u₀, hu₀, hdec0⟩
    have hmellin : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
        mellin (allZTheta chi₀ k) s = Complex.Gamma s * ((Real.pi : ℂ) ^ (-s)) *
            fullHeckeLSeries chi₀ (k : ℤ) (s - (k : ℂ) / 2) :=
      fun s hs => mellin_allZTheta chi₀ k hchibd hchi0 hs
    exact hasConductorFE_congr (fun s => congrFun (Work.FIArea6Hecke.heckeLSeries_twist chi k) s)
      (conductorFECore d hd (twist chi k) k hchiT M chi₀ hM0 hpart τ hτ hsupp hdual
        hmeas hli hdec hmellin hunitSum)

lemma hasConductorFE_nonneg (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (k : ℕ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea5.S16Hecke.psi chi (k : ℤ) z ≠ 1) :
    HasConductorFE d chi (k : ℤ) := by
  by_cases htriv : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1
  · exact nontrivialCase d hd chi k hchi htriv hnt
  · push_neg at htriv
    exact trivialCase d hd chi k hchi htriv hnt

theorem conductorFECleanNoDep (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hnt : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
      Work.FIArea5.S16Hecke.psi chi m z ≠ 1) :
    Work.FIArea6Hecke.R.HasConductorFE d chi m := by
  by_cases hm : 0 ≤ m
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    exact hasConductorFE_nonneg d hd chi k hchi hnt
  · push_neg at hm
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k : ℤ) := ⟨m.natAbs, by omega⟩
    have hnt' : ∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
        Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧
        Work.FIArea5.S16Hecke.psi (fun z : GaussianInt => star (chi z)) (k : ℤ) z ≠ 1 := by
      obtain ⟨z, hz1, hz2, hz3⟩ := hnt
      refine ⟨z, hz1, hz2, fun h => hz3 ?_⟩
      have hpc : psi chi (-(k : ℤ)) z =
          star (psi (fun z : GaussianInt => star (chi z)) (k : ℤ) z) := by
        have h2 := Work.FIArea5.S16Hecke.psi_conj (fun z : GaussianInt => star (chi z)) k z
        rw [show (fun z : GaussianInt => star (star (chi z))) = chi from
          funext (fun z => star_star (chi z))] at h2
        exact h2
      rw [h, star_one] at hpc
      exact hpc
    have hmain := hasConductorFE_nonneg d hd (fun z : GaussianInt => star (chi z)) k
      (Work.FIArea6Hecke.R.isCharMod4dStrict_conj hchi) hnt'
    exact hasConductorFE_conj d chi k (by simpa using hmain)

end

end Work.FIArea6Hecke.RC
