import Mathlib
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.WBOmega6

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary helpers -/

/-- A primary Gaussian integer has nonzero real part (it is odd). -/
private lemma re_ne_zero_of_primary (z : GaussianInt) (h : Work.FIPlan.IsPrimary z) :
    z.re ≠ 0 := by
  obtain ⟨ho, _, _⟩ := h
  obtain ⟨k, hk⟩ := ho
  intro h0
  rw [h0] at hk
  omega

/-- If `ω₀` is the (unique) class with `z₁ ≡ ω₀ z₂ (mod q)` and both norms `|z₁|², |z₂|²` are
units modulo `q`, then `ω₀` is a unit. -/
private lemma isUnit_omega_of_unique {q : ℕ} [NeZero q] (z1 z2 : GaussianInt) (ω₀ : ZMod q)
    (huniq : ∀ ω : ZMod q, (((z1.re : ZMod q) = ω * (z2.re : ZMod q)) ∧
        ((z1.im : ZMod q) = ω * (z2.im : ZMod q))) ↔ ω = ω₀)
    (h1 : Nat.Coprime (Work.FIPlan.gnorm z1) q) (h2 : Nat.Coprime (Work.FIPlan.gnorm z2) q) :
    IsUnit ω₀ := by
  obtain ⟨hR, hI⟩ := (huniq ω₀).mpr rfl
  have hg1 : IsUnit (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod q) :=
    (ZMod.isUnit_iff_coprime _ _).mpr h1
  have hg2 : IsUnit (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod q) :=
    (ZMod.isUnit_iff_coprime _ _).mpr h2
  have hnorm1 : (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod q)
      = (z1.re : ZMod q) ^ 2 + (z1.im : ZMod q) ^ 2 := by
    have h := Work.FIArea7.norm_eq z1
    have hc : (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod q)
        = ((z1.re ^ 2 + z1.im ^ 2 : ℤ) : ZMod q) := by
      rw [← h]; push_cast; rfl
    rw [hc]; push_cast; ring
  have hnorm2 : (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod q)
      = (z2.re : ZMod q) ^ 2 + (z2.im : ZMod q) ^ 2 := by
    have h := Work.FIArea7.norm_eq z2
    have hc : (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod q)
        = ((z2.re ^ 2 + z2.im ^ 2 : ℤ) : ZMod q) := by
      rw [← h]; push_cast; rfl
    rw [hc]; push_cast; ring
  have hsq : ω₀ * ω₀ * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod q)
      = (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod q) := by
    rw [hnorm2]
    calc ω₀ * ω₀ * ((z2.re : ZMod q) ^ 2 + (z2.im : ZMod q) ^ 2)
        = (ω₀ * (z2.re : ZMod q)) ^ 2 + (ω₀ * (z2.im : ZMod q)) ^ 2 := by ring
      _ = (z1.re : ZMod q) ^ 2 + (z1.im : ZMod q) ^ 2 := by rw [← hR, ← hI]
      _ = (((Work.FIPlan.gnorm z1 : ℕ)) : ZMod q) := hnorm1.symm
  have hunit2 : IsUnit (ω₀ * ω₀) := by
    have hthis : IsUnit (ω₀ * ω₀ * (((Work.FIPlan.gnorm z2 : ℕ)) : ZMod q)) := by
      rw [hsq]; exact hg1
    exact (IsUnit.mul_iff.mp hthis).1
  exact (IsUnit.mul_iff.mp hunit2).1

/-! ## The pair identity -/

theorem WUniOmega6Inner_pair_eq (X : ℕ) (z1 z2 : GaussianInt) (β : GaussianInt → ℂ)
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2)
    (h8r : z1.re ≡ z2.re [ZMOD 8]) (h8i : z1.im ≡ z2.im [ZMOD 8])
    (hX : 1 ≤ X)
    (hcop : ∀ b e : ℕ, b ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1) →
        4 * b * e ∣ Work.FIPlan.absDelta z1 z2 → e ≤ X →
        Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e)) :
    (β z1 * star (β z2))
      * (((Work.FIArea7.WUniInner X (fun d => Work.FIArea7.ratioSym z1 z2 d)
          (Work.FITop4.logFac6 z1 z2) (Work.FIPlan.absDelta z1 z2) : ℝ) : ℂ))
    = Work.FIArea7.WUniOmega6Inner X z1 z2 β := by
  by_cases hM0 : Work.FIPlan.absDelta z1 z2 = 0
  · -- the degenerate case `|∆| = 0`: the logarithmic factor vanishes, and with it both sides
    have hL : Work.FITop4.logFac6 z1 z2 = 0 := by
      rw [Work.FITop4.logFac6, hM0]
      simp
    rw [WUniInner, WUniOmega6Inner, hL]
    simp
  · have hM : 0 < Work.FIPlan.absDelta z1 z2 := Nat.pos_of_ne_zero hM0
    rw [WUniInner, WUniOmega6Inner]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    obtain ⟨heIcc, hecond⟩ := Finset.mem_filter.mp he
    obtain ⟨h4be, heX⟩ := hecond
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp heIcc).1
    have hbe0 : 0 < 4 * b * e := by positivity
    haveI : NeZero (4 * b * e) := ⟨hbe0.ne'⟩
    haveI : NeZero (Work.FIPlan.absDelta z1 z2) := ⟨hM.ne'⟩
    haveI : NeZero e := ⟨by omega⟩
    -- elementary coprimalities
    have hcopM : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) :=
      Work.FIArea7.coprime_gnorm_absDelta hP1 hP2 hs1 hs2 hc hM
    have hcopR : Nat.Coprime ((star z1 * z2).re).natAbs (Work.FIPlan.absDelta z1 z2) := by
      have h := Work.FIArea7.coprime_re_absDelta hP1 hP2 hs1 hs2 hc hM
      rwa [show (z1.re * z2.re + z1.im * z2.im).natAbs = ((star z1 * z2).re).natAbs by
        rw [Work.FIArea7.re_star_mul_coords]] at h
    have heM : e ∣ Work.FIPlan.absDelta z1 z2 := dvd_trans ⟨4 * b, by ring⟩ h4be
    have h2eM : 2 * e ∣ Work.FIPlan.absDelta z1 z2 := dvd_trans ⟨2 * b, by ring⟩ h4be
    have h4eM : 4 * e ∣ Work.FIPlan.absDelta z1 z2 := dvd_trans ⟨b, by ring⟩ h4be
    have hcopq1 : Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e) := hcopM.coprime_dvd_right h4be
    have hcope : Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e) := hcop b e hb h4be heX
    -- positivity of M/(4e)
    have hposd : 0 < Work.FIPlan.absDelta z1 z2 / (4 * e) := by
      obtain ⟨k, hk⟩ := h4eM
      rw [hk, Nat.mul_div_cancel_left _ (by positivity : 0 < 4 * e)]
      have hk0 : k ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hk; omega
      omega
    haveI : NeZero (Work.FIPlan.absDelta z1 z2 / (4 * e)) := ⟨hposd.ne'⟩
    haveI : NeZero (2 * e) := ⟨by positivity⟩
    -- Step A: ratioSym (M/(4e)) = ratioSym (M*e)
    have hdt : (Work.FIPlan.absDelta z1 z2 / (4 * e)) * (2 * e) ^ 2
        = Work.FIPlan.absDelta z1 z2 * e := by
      obtain ⟨k, hk⟩ := h4eM
      rw [hk, Nat.mul_div_cancel_left _ (by positivity : 0 < 4 * e)]
      ring
    have h1sq : Nat.Coprime (Work.FIPlan.gnorm z1)
        ((Work.FIPlan.absDelta z1 z2 / (4 * e)) * (2 * e) ^ 2) := by
      rw [hdt]; exact Nat.Coprime.mul_right hcopM (Nat.Coprime.coprime_dvd_right heM hcopM)
    have h2sq : Nat.Coprime (((star z1 * z2).re).natAbs) (2 * e) := hcopR.coprime_dvd_right h2eM
    have hsqrule := ratioSym_mul_sq z1 z2
      (d := Work.FIPlan.absDelta z1 z2 / (4 * e)) (t := 2 * e) h1sq h2sq
    have hA : ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2 / (4 * e))
        = ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2 * e) := by
      rw [← hdt]; exact hsqrule.symm
    -- Step B: ratioSym (M*e) = ratioSym M * ratioSym e
    have hB : ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2 * e)
        = ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2) * ratioSym z1 z2 e :=
      ratioSym_mul z1 z2 (d := Work.FIPlan.absDelta z1 z2) (e := e)
        (Nat.Coprime.mul_right hcopM (Nat.Coprime.coprime_dvd_right heM hcopM))
    -- Step C: ratioSym M = reflSign * JKCoeff-product
    have htw : twCorr z1 z2 = 1 := twCorr_eq_one_of_sameClass8 z1 z2 hP1 hP2 h8r h8i
    have hcc : IsCoprime ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)
        ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact hcopM
    have hC : ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2)
        = reflSign z1 z2 * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs) :=
      ratioSym_absDelta_eq_general z1 z2 hP1 hP2 hs1 hs2 hc hcc h8r h8i htw
        (re_ne_zero_of_primary z1 hP1) (re_ne_zero_of_primary z2 hP2) hM
    -- Step D: the unique ω₀ and its unit-ness
    have h4beZ : (((4 * b * e : ℕ)) : ℤ) ∣ Work.FIPlan.Delta z1 z2 := by
      have h1 : (((4 * b * e : ℕ)) : ℤ).natAbs ∣ (Work.FIPlan.Delta z1 z2).natAbs := by
        rw [Int.natAbs_natCast]
        rwa [Work.FIPlan.absDelta] at h4be
      exact Int.natAbs_dvd_natAbs.mp h1
    obtain ⟨ω₀, hω₀, huniq0⟩ :=
      Work.FIArea7.existsUnique_omega_of_dvd_delta (q := 4 * b * e) hbe0 z1 z2 hcope h4beZ
    have huniq : ∀ ω : ZMod (4 * b * e),
        (((z1.re : ZMod (4 * b * e)) = ω * (z2.re : ZMod (4 * b * e))) ∧
          ((z1.im : ZMod (4 * b * e)) = ω * (z2.im : ZMod (4 * b * e)))) ↔ ω = ω₀ :=
      fun ω => ⟨fun hω => huniq0 ω hω, fun hω => by rw [hω]; exact hω₀⟩
    have hunit : IsUnit ω₀ := isUnit_omega_of_unique z1 z2 ω₀ huniq hcopq1 hcope
    have he_dvd : e ∣ 4 * b * e := ⟨4 * b, by ring⟩
    have hE : ratioSym z1 z2 e = jacobiSym (ω₀.val : ℤ) e :=
      ratioSym_eq_jacobiSym_omega (q := 4 * b * e) (e := e) he_dvd hunit huniq hcope
    have homega : omegaDetect (4 * b * e) e z1 z2 = (jacobiSym (ω₀.val : ℤ) e : ℂ) :=
      omegaDetect_eq_of_unique (4 * b * e) e z1 z2 huniq
    -- the core identity
    have hJK := jkcoeff_pair_mul z1 z2 β
    set K : ℤ := jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs with hK
    have hCc : ((ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2) : ℤ) : ℂ)
        = (reflSign z1 z2 : ℂ) * ((K : ℤ) : ℂ) := by
      rw [hC]; push_cast [hK]; ring
    have hcore : (β z1 * star (β z2))
        * ((ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2 / (4 * e)) : ℤ) : ℂ)
        = (reflSign z1 z2 : ℂ) * omegaDetect (4 * b * e) e z1 z2
          * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
          * (betaPrime β z1 * star (betaPrime β z2)) := by
      rw [hA, hB, hE, homega]
      push_cast
      rw [hCc]
      rw [show (β z1 * star (β z2)) * ((reflSign z1 z2 : ℂ) * ((K : ℤ) : ℂ)
            * (jacobiSym (ω₀.val : ℤ) e : ℂ))
          = (reflSign z1 z2 : ℂ) * (jacobiSym (ω₀.val : ℤ) e : ℂ)
            * (((K : ℤ) : ℂ) * (β z1 * star (β z2))) by ring]
      rw [hJK]
      ring
    -- assemble
    rw [show (β z1 * star (β z2))
          * ((ArithmeticFunction.moebius b : ℂ) / (b : ℂ)
            * ((ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2 / (4 * e)) : ℤ) : ℂ)
            * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ))
        = ((ArithmeticFunction.moebius b : ℂ) / (b : ℂ))
            * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)
            * ((β z1 * star (β z2))
              * ((ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2 / (4 * e)) : ℤ) : ℂ)) by ring]
    rw [hcore]
    ring

end

end Work.FIArea7
