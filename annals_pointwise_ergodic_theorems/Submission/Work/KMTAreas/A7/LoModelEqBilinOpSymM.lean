import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedWinDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## Elementary pieces: the delta kernel, the height-`0` multiplier and Poisson summation -/

/-- The Kronecker delta kernel at `(0,0)`: the kernel of the *untwisted* product `(u·v)`. -/
private def lmebDelta : ℤ → ℤ → ℂ := fun a b => if a = 0 ∧ b = 0 then 1 else 0

/-- `bilinOp` with the delta kernel is the pointwise product. -/
private lemma lmeb_bilinOp_delta (u v : ℤ → ℂ) (x : ℤ) :
    Work.KMTAreas.A7.bilinOp lmebDelta u v x = u x * v x := by
  rw [Work.KMTAreas.A7.bilinOp]
  have hzero : ∀ a b : ℤ, ¬(a = 0 ∧ b = 0) → lmebDelta a b = 0 := by
    intro a b hab
    simp [lmebDelta, hab]
  have hinner : ∀ a : ℤ, (∑' b : ℤ, lmebDelta a b * u (x - a) * v (x - b))
      = if a = 0 then u x * v x else 0 := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [tsum_eq_single (0 : ℤ)]
      · simp [lmebDelta]
      · intro b hb
        rw [hzero 0 b (by simp [hb])]
        ring
    · have h0 : ∀ b : ℤ, lmebDelta a b * u (x - a) * v (x - b) = 0 := by
        intro b
        rw [hzero a b (fun hc => ha hc.1)]
        ring
      rw [tsum_congr h0, tsum_zero, if_neg ha]
  rw [tsum_congr hinner, tsum_eq_single (0 : ℤ)]
  · rw [if_pos rfl]
  · intro a ha
    exact if_neg ha

/-- The symbol of the delta kernel is `1`. -/
private lemma lmeb_symSeq2_delta (x y : ℝ) :
    symSeq2 lmebDelta x y = 1 := by
  have hzero : ∀ p q : ℤ, ¬(p = 0 ∧ q = 0) → lmebDelta p q = 0 := by
    intro p q hpq
    simp [lmebDelta, hpq]
  rw [symSeq2, tsum_eq_single (0 : ℤ)]
  · rw [tsum_eq_single (0 : ℤ)]
    · simp [lmebDelta, eeC]
    · intro q hq
      rw [hzero 0 q (fun hc => hq hc.2)]
      simp
  · intro p hp
    have h0 : ∀ q : ℤ, lmebDelta p q * eeC ((p : ℝ) * x + (q : ℝ) * y) = 0 := by
      intro q
      rw [hzero p q (fun hc => hp hc.1)]
      simp
    rw [tsum_congr h0, tsum_zero]

/-- The delta kernel is `ℓ¹`. -/
private lemma lmeb_summable_delta :
    Summable fun p : ℤ × ℤ => ‖lmebDelta p.1 p.2‖ := by
  refine summable_of_ne_finset_zero (s := {(0, 0)})
    (fun p hp => ?_)
  have hp' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun hc => hp (by simp [Prod.ext_iff, hc.1, hc.2])
  simp [lmebDelta, hp']

/-- The `ℓ¹` mass of the delta kernel is `1`. -/
private lemma lmeb_tsum_delta : (∑' p : ℤ × ℤ, ‖lmebDelta p.1 p.2‖) = 1 := by
  rw [tsum_eq_single ((0 : ℤ), (0 : ℤ))]
  · simp [lmebDelta]
  · intro p hp
    have hp' : ¬ (p.1 = 0 ∧ p.2 = 0) := fun hc => hp (by simp [Prod.ext_iff, hc.1, hc.2])
    simp [lmebDelta, hp']

/-- **The height-`0` IW multiplier is the plain convolution with the height-`0` kernel**:
`T^{0}_φ = T_{φ}` (`iwArithFreqs ρ 0 = {0} = diffFreqs ρ 0`). -/
private lemma lmeb_Tle_zero_eq_convOp (ρ : ℝ) (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    Tle ρ 0 φ f = convOp (tmKer ρ 0 φ) f := by
  funext x
  have hd : Work.KMTAreas.A7.diffFreqs ρ 0 = iwArithFreqs ρ 0 := by
    rw [Work.KMTAreas.A7.diffFreqs, if_pos rfl]
  rw [Tle, ← hd]
  rfl

/-- **Poisson summation for `cw`**: `symSeq (cw m) x = periodize m (x mod 1)`. -/
private lemma lmeb_symSeq_cw_eq_periodize {m : ℝ → ℂ} (hm : ContDiff ℝ 2 m)
    (hcs : HasCompactSupport m) (x : ℝ) :
    symSeq (cw m) x = periodize m ((x : ℝ) : Circ) := by
  rw [symSeq, ← symp_cw_tsum_fourier hm hcs ((x : ℝ) : Circ)]
  exact tsum_congr (fun j => by rw [fourier_coe_one' j x])

/-- **`tmKer` at height `0` is the Fourier coefficient family of the bump**. -/
private lemma lmeb_tmKer_zero_eq_cw (ρ : ℝ) {φ : ℝ → ℂ} (hφ : Integrable φ) :
    tmKer ρ 0 φ = cw φ := by
  funext j
  have hfreq : Work.KMTAreas.A7.diffFreqs ρ 0 = ({(0 : Circ)} : Finset Circ) := by
    rw [Work.KMTAreas.A7.diffFreqs, if_pos rfl, Work.KMTAreas.A7.iwArithFreqs_zero]
  have hsym : iwSymbolSet ({(0 : Circ)} : Finset Circ) (periodize φ) = periodize φ := by
    funext ξ
    simp [iwSymbolSet]
  rw [tmKer, hfreq, hsym]
  exact fourierCoeff_periodize_eq_cw hφ j

/-- **The symbol of the height-`0` multiplier is the periodised bump.** -/
private lemma lmeb_symSeq_tmKer_zero (ρ : ℝ) {φ : ℝ → ℂ} (hint : Integrable φ)
    (hcd : ContDiff ℝ 2 φ) (hcs : HasCompactSupport φ) (x : ℝ) :
    symSeq (tmKer ρ 0 φ) x = periodize φ ((x : ℝ) : Circ) := by
  rw [lmeb_tmKer_zero_eq_cw ρ hint]
  exact lmeb_symSeq_cw_eq_periodize hcd hcs x

/-- The symbol of a *separable* kernel is the product of the two one-dimensional symbols. -/
private lemma lmeb_symSeq2_sep {A B : ℤ → ℂ} (hA : Summable fun j : ℤ => ‖A j‖)
    (hB : Summable fun j : ℤ => ‖B j‖) (x y : ℝ) :
    symSeq2 (fun a b => A a * B b) x y = symSeq A x * symSeq B y := by
  have h1 : Summable (fun p : ℤ => A p * eeC ((p : ℝ) * x)) :=
    Summable.of_norm_bounded hA (fun p => by rw [norm_mul, norm_eeC, mul_one])
  have h2 : Summable (fun q : ℤ => B q * eeC ((q : ℝ) * y)) :=
    Summable.of_norm_bounded hB (fun q => by rw [norm_mul, norm_eeC, mul_one])
  have hprod : Summable (fun z : ℤ × ℤ =>
      (A z.1 * eeC ((z.1 : ℝ) * x)) * (B z.2 * eeC ((z.2 : ℝ) * y))) :=
    Summable.of_norm_bounded
      (hA.mul_of_nonneg hB (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      (fun z => by rw [norm_mul, norm_mul, norm_mul, norm_eeC, norm_eeC]; simp)
  calc symSeq2 (fun a b => A a * B b) x y
      = ∑' p : ℤ, ∑' q : ℤ, (A p * eeC ((p : ℝ) * x)) * (B q * eeC ((q : ℝ) * y)) := by
        rw [symSeq2]
        refine tsum_congr (fun p => tsum_congr (fun q => ?_))
        rw [eeC_add]
        ring
    _ = (∑' p : ℤ, A p * eeC ((p : ℝ) * x))
          * (∑' q : ℤ, B q * eeC ((q : ℝ) * y)) := by
        rw [Summable.tsum_mul_tsum h1 h2 hprod]
        exact (Summable.tsum_prod hprod).symm
    _ = symSeq A x * symSeq B y := by rw [symSeq, symSeq]

/-- **The arithmetic kernel at exact heights `(0,0)` is the separable window kernel**
(the only arithmetic frequency is `0`, where `m_Ẑ(0,0) = 1`). -/
private lemma lmeb_arithKerM_zero (ρ : ℝ) (P : Polynomial ℤ) (k₁ k₂ : ℕ) :
    arithKerM ρ P 0 0 k₁ k₂
      = fun a b => cw (mStarF (uScale ρ (max k₁ k₂))) a
          * cw (mStargF P.natDegree (uScale ρ (max k₁ k₂))) b := by
  have hlcl : lcL 0 0 k₁ k₂ = max k₁ k₂ := by
    simp [lcL]
  have hmZ : mZ P (arithQ ρ 0) (0 : Circ) (0 : Circ) = 1 := by
    have h1 : ∀ n : ℕ, fourier (T := 1) (n : ℤ) ((0 : Circ))
        * fourier (T := 1) (P.eval (n : ℤ)) ((0 : Circ)) = 1 := by
      intro n
      rw [fourier_eval_zero, fourier_eval_zero, mul_one]
    have h2 : (∑ n ∈ Finset.range (arithQ ρ 0),
        fourier (T := 1) (n : ℤ) ((0 : Circ))
          * fourier (T := 1) (P.eval (n : ℤ)) ((0 : Circ))) = (arithQ ρ 0 : ℂ) := by
      rw [Finset.sum_congr rfl (fun n _ => h1 n)]
      simp
    rw [mZ, h2]
    exact inv_mul_cancel₀ (by exact_mod_cast (ne_of_gt (arithQ_pos ρ 0)))
  funext a b
  rw [arithKerM, hlcl, arithKernelEx]
  have hfreq : Work.KMTAreas.A7.diffFreqs ρ 0 = ({(0 : Circ)} : Finset Circ) := by
    rw [Work.KMTAreas.A7.diffFreqs, if_pos rfl, Work.KMTAreas.A7.iwArithFreqs_zero]
  rw [show (max (0 : ℕ) 0) = 0 from rfl, hfreq, Finset.sum_singleton, Finset.sum_singleton, hmZ]
  simp only [fourier_eval_zero, one_mul, mul_one]

/-! ## Flatness: the window is `1` on the support of the modulated bump -/

/-- Flatness in the first variable: on the guard, the periodised window `η_{≤-2u}` is `1` on the
support of the periodised modulated bump `φ_{N,t}`. -/
private lemma lmeb_flat_fst (N k₁ u : ℕ) (hu : 1 ≤ u)
    (h : k₁ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) (t x : ℝ) :
    periodize (mStarF u) ((x : ℝ) : Circ) * periodize (varphiNt N k₁ t) ((x : ℝ) : Circ)
      = periodize (varphiNt N k₁ t) ((x : ℝ) : Circ) := by
  by_cases h0 : periodize (varphiNt N k₁ t) ((x : ℝ) : Circ) = 0
  · rw [h0, mul_zero]
  · obtain ⟨θ, hθ, hθξ⟩ :=
      symp_supportedInArc_periodize_varphiNt N k₁ u hu h t _ h0
    have h1 : periodize (mStarF u) ((x : ℝ) : Circ) = 1 := by
      rw [← hθξ]
      exact symp_periodize_mStarF_eq_one u hu hθ
    rw [h1, one_mul]

/-- Flatness in the second variable: on the guard, the periodised window `η_{≤-2du}` is `1` on the
support of the periodised modulated bump `φ̃_{N,t}`. -/
private lemma lmeb_flat_snd (P : Polynomial ℤ) (d N k₂ u : ℕ) (hd : 1 ≤ d) (hu : 1 ≤ u)
    (h : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) (t x : ℝ) :
    periodize (mStargF d u) ((x : ℝ) : Circ) * periodize (varphitildeNt P d N k₂ t) ((x : ℝ) : Circ)
      = periodize (varphitildeNt P d N k₂ t) ((x : ℝ) : Circ) := by
  by_cases h0 : periodize (varphitildeNt P d N k₂ t) ((x : ℝ) : Circ) = 0
  · rw [h0, mul_zero]
  · obtain ⟨θ, hθ, hθξ⟩ :=
      symp_supportedInArc_periodize_varphitildeNt P d N k₂ u hd hu h t _ h0
    have h1 : periodize (mStargF d u) ((x : ℝ) : Circ) = 1 := by
      rw [← hθξ]
      exact symp_periodize_mStargF_eq_one d u hd hu hθ
    rw [h1, one_mul]

/-! ## Measurability helpers -/

private lemma lmeb_measurable_symSeq_family3 (κ : ℝ → ℤ → ℂ)
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun w : ℝ × ℝ × ℝ => symSeq (κ w.1) w.2.1) := by
  rw [show (fun w : ℝ × ℝ × ℝ => symSeq (κ w.1) w.2.1) = fun w : ℝ × ℝ × ℝ =>
      ∑' j : ℤ, κ w.1 j * eeC ((j : ℝ) * w.2.1) from by
    funext w; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun w : ℝ × ℝ × ℝ => κ w.1 j) := (hκ j).comp measurable_fst
  have h2 : Measurable (fun w : ℝ × ℝ × ℝ => eeC ((j : ℝ) * w.2.1)) :=
    (continuous_eeC.comp (by fun_prop)).measurable
  exact h1.mul h2

private lemma lmeb_measurable_symSeq_family3' (κ : ℝ → ℤ → ℂ)
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) :
    Measurable (fun w : ℝ × ℝ × ℝ => symSeq (κ w.1) w.2.2) := by
  rw [show (fun w : ℝ × ℝ × ℝ => symSeq (κ w.1) w.2.2) = fun w : ℝ × ℝ × ℝ =>
      ∑' j : ℤ, κ w.1 j * eeC ((j : ℝ) * w.2.2) from by
    funext w; rw [symSeq]]
  refine Measurable.tsum (L := SummationFilter.unconditional ℤ) (fun j => ?_)
  have h1 : Measurable (fun w : ℝ × ℝ × ℝ => κ w.1 j) := (hκ j).comp measurable_fst
  have h2 : Measurable (fun w : ℝ × ℝ × ℝ => eeC ((j : ℝ) * w.2.2)) :=
    (continuous_eeC.comp (by fun_prop)).measurable
  exact h1.mul h2

/-! ## The model symbol at `(0,0)` is the `t`-integral of the two bump symbols -/

/-- **The §6 model symbol at arithmetic heights `(0,0)`**: the window factor `m_* ⊗ m̃_*` is
`1` on the support of the modulated bumps, so the symbol collapses to the product of the two
height-`0` bump symbols. -/
private lemma lmeb_symM_zero_eq (ρ : ℝ) (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (hd : 1 ≤ P.natDegree) (hu : 1 ≤ uScale ρ (max k₁ k₂))
    (h₁ : k₁ + 2 * uScale ρ (max k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (h₂ : k₂ + 2 * uScale ρ (max k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    symM ρ P N 0 0 k₁ k₂
      = fun x y : ℝ => ∫ t in (1 / 2 : ℝ)..1,
          symSeq (tmKer ρ 0 (varphiNt N k₁ t)) x
            * symSeq (tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t)) y := by
  funext x y
  rw [symM]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  have hA : symSeq2 (arithKerM ρ P 0 0 k₁ k₂) x y
      = periodize (mStarF (uScale ρ (max k₁ k₂))) ((x : ℝ) : Circ)
        * periodize (mStargF P.natDegree (uScale ρ (max k₁ k₂))) ((y : ℝ) : Circ) := by
    rw [lmeb_arithKerM_zero ρ P k₁ k₂]
    rw [lmeb_symSeq2_sep (symp_summable_cw_mStarF (uScale ρ (max k₁ k₂)))
      (symp_summable_cw_mStargF P.natDegree (uScale ρ (max k₁ k₂))) x y]
    rw [lmeb_symSeq_cw_eq_periodize (symp_contDiff_mStarF _)
        (symp_hasCompactSupport_mStarF _) x,
      lmeb_symSeq_cw_eq_periodize (symp_contDiff_mStargF (P.natDegree) _)
        (symp_hasCompactSupport_mStargF (P.natDegree) _) y]
  have hB : symSeq (tmKer ρ 0 (varphiNt N k₁ t)) x
      = periodize (varphiNt N k₁ t) ((x : ℝ) : Circ) :=
    lmeb_symSeq_tmKer_zero ρ
      ((contDiff_varphiNt N k₁ t).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_varphiNt N k₁ t))
      (contDiff_varphiNt N k₁ t) (hasCompactSupport_varphiNt N k₁ t) x
  have hC : symSeq (tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t)) y
      = periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) : Circ) :=
    lmeb_symSeq_tmKer_zero ρ
      (symp_integrable_varphitildeNt P P.natDegree N k₂ t)
      (symp_contDiff_varphitildeNt P P.natDegree N k₂ t)
      (symp_hasCompactSupport_varphitildeNt P P.natDegree N k₂ t) y
  rw [hA, hB, hC]
  have hre : periodize (mStarF (uScale ρ (max k₁ k₂))) ((x : ℝ) : Circ)
        * periodize (mStargF P.natDegree (uScale ρ (max k₁ k₂))) ((y : ℝ) : Circ)
        * periodize (varphiNt N k₁ t) ((x : ℝ) : Circ)
        * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) : Circ)
      = (periodize (mStarF (uScale ρ (max k₁ k₂))) ((x : ℝ) : Circ)
            * periodize (varphiNt N k₁ t) ((x : ℝ) : Circ))
          * (periodize (mStargF P.natDegree (uScale ρ (max k₁ k₂))) ((y : ℝ) : Circ)
            * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) : Circ)) := by
    ring
  rw [hre, lmeb_flat_fst N k₁ (uScale ρ (max k₁ k₂)) hu h₁ t x,
    lmeb_flat_snd P P.natDegree N k₂ (uScale ρ (max k₁ k₂)) hd hu h₂ t y]

/-! ## The coefficient kernel of the model symbol -/

/-- **The coefficient kernel of the model symbol at `(0,0)`** is the `t`-integral of the composed
kernel with the *delta* kernel. -/
private lemma lmeb_coeff2_symM_zero (ρ : ℝ) (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (hd : 1 ≤ P.natDegree) (hu : 1 ≤ uScale ρ (max k₁ k₂))
    (h₁ : k₁ + 2 * uScale ρ (max k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (h₂ : k₂ + 2 * uScale ρ (max k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat)
    {κ₁ κ₂ : ℝ → ℤ → ℂ}
    (hκ₁ : ∀ t : ℝ, κ₁ t = tmKer ρ 0 (varphiNt N k₁ t))
    (hκ₂ : ∀ t : ℝ, κ₂ t = tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t))
    {B₁ B₂ : ℝ} (hB₁ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      Summable (fun j : ℤ => ‖κ₁ t j‖) ∧ (∑' j : ℤ, ‖κ₁ t j‖) ≤ B₁)
    (hB₂ : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      Summable (fun j : ℤ => ‖κ₂ t j‖) ∧ (∑' j : ℤ, ‖κ₂ t j‖) ≤ B₂)
    (hm₁ : ∀ j : ℤ, Measurable (fun t : ℝ => κ₁ t j))
    (hm₂ : ∀ j : ℤ, Measurable (fun t : ℝ => κ₂ t j)) :
    coeff2 (symM ρ P N 0 0 k₁ k₂)
      = fun a b : ℤ => ∫ t in (1 / 2 : ℝ)..1,
          kernComp lmebDelta (κ₁ t) (κ₂ t) a b := by
  have hsym : symM ρ P N 0 0 k₁ k₂
      = fun x y : ℝ => ∫ t in (1 / 2 : ℝ)..1, symSeq (κ₁ t) x * symSeq (κ₂ t) y := by
    rw [lmeb_symM_zero_eq ρ P N k₁ k₂ hd hu h₁ h₂]
    funext x y
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [← hκ₁ t, ← hκ₂ t]
  have hmeas : Measurable (fun w : ℝ × ℝ × ℝ =>
      symSeq (κ₁ w.1) w.2.1 * symSeq (κ₂ w.1) w.2.2) :=
    (lmeb_measurable_symSeq_family3 κ₁ hm₁).mul (lmeb_measurable_symSeq_family3' κ₂ hm₂)
  have hbound : ∀ t, t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ x y : ℝ,
      ‖symSeq (κ₁ t) x * symSeq (κ₂ t) y‖ ≤ B₁ * B₂ := by
    intro t ht x y
    have h1 : ‖symSeq (κ₁ t) x‖ ≤ B₁ := le_trans (norm_symSeq_le (hB₁ t ht).1 x) (hB₁ t ht).2
    have h2 : ‖symSeq (κ₂ t) y‖ ≤ B₂ := le_trans (norm_symSeq_le (hB₂ t ht).1 y) (hB₂ t ht).2
    calc ‖symSeq (κ₁ t) x * symSeq (κ₂ t) y‖
        = ‖symSeq (κ₁ t) x‖ * ‖symSeq (κ₂ t) y‖ := norm_mul _ _
      _ ≤ B₁ * B₂ := mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
  funext a b
  rw [hsym]
  rw [coeff2IntegralSwapSym
    (fun t x y : ℝ => symSeq (κ₁ t) x * symSeq (κ₂ t) y) hmeas hbound a b]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
  have h1 : (fun x y : ℝ => symSeq (κ₁ t) x * symSeq (κ₂ t) y)
      = (fun x y : ℝ => symSeq2 lmebDelta x y * symSeq (κ₁ t) x * symSeq (κ₂ t) y) := by
    funext x y
    rw [lmeb_symSeq2_delta, one_mul]
  rw [h1, SymSeq2_kernComp_coeff lmebDelta (κ₁ t) (κ₂ t) lmeb_summable_delta
    ((hB₁ t ht).1.of_norm) ((hB₂ t ht).1.of_norm) a b]

theorem LoModelEqBilinOpSymM (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ) (k₁ k₂ n : ℕ) (x : ℤ)
    (hd : 1 ≤ P.natDegree)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : Work.KMTAreas.A7.loGuard ρ C₀ a 0 0 k₁ k₂ n)
    (hC2 : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) :
    Work.KMTAreas.A7.loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp (fun u v =>
          Work.KMTPlan.A6.coeff2 (Work.KMTPlan.A6.symM ρ P (Nat.floor (a n)) 0 0 k₁ k₂) u v)
          f g x := by
  obtain ⟨Cf, hfC⟩ := hf
  obtain ⟨Cg, hgC⟩ := hg
  have hCf : 0 ≤ Cf := le_trans (norm_nonneg _) (hfC 0)
  have hCg : 0 ≤ Cg := le_trans (norm_nonneg _) (hgC 0)
  set N : ℕ := Nat.floor (a n) with hN
  obtain ⟨B₁, hB₁0, hB₁⟩ := uniform_tmKer_varphiNt ρ 0 N k₁
  obtain ⟨B₂, hB₂0, hB₂⟩ := uniform_tmKer_varphitildeNt ρ P 0 N k₂
  have hu : 1 ≤ uScale ρ (max k₁ k₂) := symp_one_le_uScale ρ hρ.le (max k₁ k₂)
  have hm1 : k₁ ≤ max k₁ k₂ := le_max_left _ _
  have hm2 : k₂ ≤ max k₁ k₂ := le_max_right _ _
  have hk₁ : k₁ + 2 * uScale ρ (max k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    omega
  have hk₂ : k₂ + 2 * uScale ρ (max k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    omega
  have hmκ₁ : ∀ j : ℤ, Measurable (fun t : ℝ => tmKer ρ 0 (varphiNt N k₁ t) j) :=
    fun j => measurable_tmKer_varphiNt ρ 0 N k₁ j
  have hmκ₂ : ∀ j : ℤ, Measurable
      (fun t : ℝ => tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t) j) :=
    fun j => measurable_tmKer_varphitildeNt ρ P 0 N k₂ j
  have hker : coeff2 (symM ρ P N 0 0 k₁ k₂)
      = fun a b : ℤ => ∫ t in (1 / 2 : ℝ)..1,
          kernComp lmebDelta (tmKer ρ 0 (varphiNt N k₁ t))
            (tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t)) a b :=
    lmeb_coeff2_symM_zero ρ P N k₁ k₂ hd hu hk₁ hk₂ (κ₁ := fun t : ℝ => tmKer ρ 0 (varphiNt N k₁ t))
      (κ₂ := fun t : ℝ => tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t))
      (fun t => rfl) (fun t => rfl) hB₁ hB₂ hmκ₁ hmκ₂
  have hLHS : loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
      = ∫ t in (1 / 2 : ℝ)..1,
          bilinOp lmebDelta (convOp (tmKer ρ 0 (varphiNt N k₁ t)) f)
            (convOp (tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t)) g) x := by
    rw [loModelTuple, if_pos h]
    simp only [← hN]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [lmeb_Tle_zero_eq_convOp, lmeb_Tle_zero_eq_convOp]
    exact (lmeb_bilinOp_delta _ _ _).symm
  have hIoc₁ : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Summable fun j : ℤ => ‖tmKer ρ 0 (varphiNt N k₁ t) j‖ :=
    fun t ht => (hB₁ t ⟨le_of_lt ht.1, ht.2⟩).1
  have hIoc₂ : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Summable fun j : ℤ => ‖tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t) j‖ :=
    fun t ht => (hB₂ t ⟨le_of_lt ht.1, ht.2⟩).1
  have hb₁ : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      (∑' j : ℤ, ‖tmKer ρ 0 (varphiNt N k₁ t) j‖) ≤ B₁ :=
    fun t ht => (hB₁ t ⟨le_of_lt ht.1, ht.2⟩).2
  have hb₂ : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      (∑' j : ℤ, ‖tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t) j‖) ≤ B₂ :=
    fun t ht => (hB₂ t ⟨le_of_lt ht.1, ht.2⟩).2
  have hm₁ : ∀ j : ℤ, AEMeasurable
      (fun t : ℝ => (fun s : ℝ => tmKer ρ 0 (varphiNt N k₁ s)) t j) volume :=
    fun j => (hmκ₁ j).aemeasurable
  have hm₂ : ∀ j : ℤ, AEMeasurable
      (fun t : ℝ => (fun s : ℝ => tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ s)) t j) volume :=
    fun j => (hmκ₂ j).aemeasurable
  calc loModelTuple ρ P C₀ a f g 0 0 k₁ k₂ n x
      = ∫ t in (1 / 2 : ℝ)..1,
          bilinOp lmebDelta (convOp (tmKer ρ 0 (varphiNt N k₁ t)) f)
            (convOp (tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t)) g) x := hLHS
    _ = bilinOp (fun a b : ℤ => ∫ t in (1 / 2 : ℝ)..1,
          kernComp lmebDelta (tmKer ρ 0 (varphiNt N k₁ t))
            (tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ t)) a b) f g x :=
        (bilinOp_intervalIntegral lmebDelta (fun s : ℝ => tmKer ρ 0 (varphiNt N k₁ s))
          (fun s : ℝ => tmKer ρ 0 (varphitildeNt P P.natDegree N k₂ s)) f g 1 B₁ B₂ Cf Cg x
          lmeb_summable_delta (le_of_eq lmeb_tsum_delta) hIoc₁ hIoc₂ hb₁ hb₂ hfC hgC hCf hCg
          (by norm_num) hB₁0 hB₂0 hm₁ hm₂)
    _ = bilinOp (fun u v => coeff2 (symM ρ P N 0 0 k₁ k₂) u v) f g x := by
        congr 1
        funext a b
        exact (congrFun (congrFun hker a) b).symm

end

end Work.KMTAreas.A7
