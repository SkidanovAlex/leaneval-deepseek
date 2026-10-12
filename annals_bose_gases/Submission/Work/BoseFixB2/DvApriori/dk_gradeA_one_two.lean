import ChallengeDeps
import Mathlib.Data.Int.Star
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.DvApriori.boxFormB_congr_of_eqOn_abox
import Submission.Work.BoseFixB2.DvApriori.sum_Icc_cast_eq_sum_range
import Submission.Work.BoseFixB2.DvApriori.sum_Icc_zero_pred_eq_sum_range
import Submission.Work.BoseFixB2.Polar.polB_symm
import Submission.Work.BoseFixB2.Sector.normB_secProj_sum
import Submission.Work.BoseFixB2.Sector.secProj_contDiff_symm
import Submission.Work.BoseFixB2.Sector.secProj_orthogonal
import Submission.Work.BoseKinLoc.Sector.boxFormB_eq_zero_of_eq_zero_on_abox
import Submission.Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric
open Finset

namespace Work.BoseFixB2.DvApriori

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix Work.UBB Work.UBBInputs3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

variable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
  {Φ : Submission.BoseGases.X n → ℝ}

/-! ## 0. TEMPORARY placeholders (to be replaced by imports of the delegated lemmas) -/

/-! ## 1. Elementary facts -/

/-- `normB` is nonnegative: it is the box integral of a square. -/
lemma normB_nonneg (Ψ : Submission.BoseGases.X n → ℝ) : 0 ≤ Work.BoseBoxFix.normB v μ n Ψ := by
  simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  exact MeasureTheory.integral_nonneg (fun x => sq_nonneg (Ψ x))

/-- The real part of a sum of real coercions. -/
lemma re_sum_ofReal {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, ((f i : ℝ) : ℂ)).re = ∑ i ∈ s, f i := by
  rw [← Complex.ofReal_sum s f, Complex.ofReal_re]

/-- `gradePsi` vanishes at negative integers. -/
lemma gradePsi_eq_zero_of_neg (ℓ : ℝ) (i : ℤ) (hi : i < 0) :
    Work.BoseFixB2.gradePsi v h μ n ℓ Φ i = 0 := by
  rw [Work.BoseFixB2.gradePsi, if_neg]
  exact fun hc => absurd hc.1 (not_le.mpr hi)

/-- `gradePsi` vanishes beyond the particle number. -/
lemma gradePsi_eq_zero_of_gt (ℓ : ℝ) (i : ℤ) (hi : (n : ℤ) < i) :
    Work.BoseFixB2.gradePsi v h μ n ℓ Φ i = 0 := by
  rw [Work.BoseFixB2.gradePsi, if_neg]
  exact fun hc => absurd hc.2 (not_le.mpr hi)

/-- The explicit value of `gradePsi` on the sector range. -/
lemma gradePsi_apply (ℓ : ℝ) {i : ℤ} (h0 : 0 ≤ i) (hn : i ≤ (n : ℤ)) :
    Work.BoseFixB2.gradePsi v h μ n ℓ Φ i
      = ((Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ i))
          / Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) : ℝ) : ℂ) := by
  rw [Work.BoseFixB2.gradePsi, if_pos ⟨h0, hn⟩]

/-- The explicit value of `vecZ` on the sector range. -/
lemma vecZ_apply (ℓ : ℝ) {i : ℤ} (h0 : 0 ≤ i) (hn : i ≤ (n : ℤ)) :
    Work.BoseFixB2.vecZ ℓ Φ i = Work.BoseFixB2.secProj ℓ i.toNat Φ := by
  rw [Work.BoseFixB2.vecZ, if_pos ⟨h0, hn⟩]

/-- Conjugation does not change `gradePsi` on the sector range (it is real-valued there). -/
lemma star_gradePsi (ℓ : ℝ) {i : ℤ} (h0 : 0 ≤ i) (hn : i ≤ (n : ℤ)) :
    star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ i)
      = ((Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ i))
          / Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) : ℝ) : ℂ) := by
  rw [Work.BoseFixB2.gradePsi, if_pos ⟨h0, hn⟩]
  exact Complex.conj_ofReal _

/-- `secProj` of a smooth state is smooth (no symmetry hypothesis needed). -/
lemma secProj_contDiff' {ℓ : ℝ} (hℓ : 0 < ℓ) {k : ℕ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.secProj ℓ k Φ) := by
  have hsum : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => ∑ S ∈ (Finset.range n).powersetCard k, Work.BoseFixB2.jointProj ℓ S Φ x) :=
    ContDiff.sum (fun S _ => Work.BoseFixB2.Sector.jointProj_contDiff hℓ S hΦ)
  rw [Work.BoseFixB2.secProj, Finset.sum_fn]
  exact hsum

/-- `vecZ` of a smooth state is smooth. -/
lemma contDiff_vecZ {ℓ : ℝ} (hℓ : 0 < ℓ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.BoseFixB2.vecZ ℓ Φ i) := by
  by_cases hc : 0 ≤ i ∧ i ≤ (n : ℤ)
  · rw [Work.BoseFixB2.vecZ, if_pos hc]
    exact secProj_contDiff' hℓ hΦ
  · rw [Work.BoseFixB2.vecZ, if_neg hc]
    exact contDiff_const

/-! ## 2. Box-locality of `wordB`, and vanishing of `polB` at zero box norm -/

/-- `wordB` sees only the restriction of the state to the box. -/
lemma wordB_congr_of_eqOn_abox (hℓ : 0 < Work.BoseFixB2.fsSide v μ)
    {Ψ Ω : Submission.BoseGases.X n → ℝ}
    (hh : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ), Ψ x = Ω x) :
    Work.BoseBoxFix.wordB v h μ n Ψ = Work.BoseBoxFix.wordB v h μ n Ω := by
  simp only [Work.BoseBoxFix.wordB]
  exact boxFormB_congr_of_eqOn_abox hℓ hh

/-- **The polarised box word vanishes in an argument of vanishing box norm.**

`normB Ψ = 0` forces `Ψ = 0` pointwise on the box (`eq_zero_on_abox_of_sqNormB_eq_zero`,
using continuity of `Ψ`), and `wordB` is box-local, so `wordB (Ψ ± Ω) = wordB Ω`. -/
lemma polB_eq_zero_of_normB_eq_zero (hℓ : 0 < Work.BoseFixB2.fsSide v μ)
    {Ψ Ω : Submission.BoseGases.X n → ℝ}
    (hΨc : Continuous Ψ) (h0 : Work.BoseBoxFix.normB v μ n Ψ = 0) :
    Work.BoseFixB2.polB v h μ n Ψ Ω = 0 := by
  have h0' : Work.BoseKinLoc.sqNormB n (Work.BoseFixB2.fsSide v μ) Ψ = 0 := h0
  have hzero : ∀ x ∈ Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ), Ψ x = 0 :=
    Work.BoseKinLoc.Sector.eq_zero_on_abox_of_sqNormB_eq_zero hℓ hΨc h0'
  have h1 : Work.BoseBoxFix.wordB v h μ n (fun x => Ψ x + Ω x)
      = Work.BoseBoxFix.wordB v h μ n Ω :=
    wordB_congr_of_eqOn_abox hℓ (fun x hx => by rw [hzero x hx, zero_add])
  have h2 : Work.BoseBoxFix.wordB v h μ n (fun x => Ψ x - Ω x)
      = Work.BoseBoxFix.wordB v h μ n Ω := by
    refine (wordB_congr_of_eqOn_abox hℓ (fun x hx => by rw [hzero x hx, zero_sub])).trans ?_
    exact Work.BoseFixB2.Polar.PolB.wordB_neg v h μ n Ω
  rw [Work.BoseFixB2.polB, h1, h2]
  ring

/-! ## 3. Symmetry of `gradeA` -/

/-- `gradeA` is symmetric (it is real-valued, and `polB` is symmetric). -/
lemma gradeA_comm {ℓ : ℝ} (hℓ : 0 < ℓ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (i j : ℤ) :
    Work.BoseFixB2.gradeA v h μ n ℓ Φ j i = Work.BoseFixB2.gradeA v h μ n ℓ Φ i j := by
  by_cases hc : 0 ≤ i ∧ i ≤ (n : ℤ) ∧ 0 ≤ j ∧ j ≤ (n : ℤ)
      ∧ 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ i)
      ∧ 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ j)
  · obtain ⟨hi0, hin, hj0, hjn, hpi, hpj⟩ := hc
    rw [Work.BoseFixB2.gradeA, if_pos ⟨hj0, hjn, hi0, hin, hpj, hpi⟩,
      Work.BoseFixB2.gradeA, if_pos ⟨hi0, hin, hj0, hjn, hpi, hpj⟩]
    rw [Complex.ofReal_inj]
    rw [Work.BoseFixB2.Polar.polB_symm (h := h) (μ := μ) (n := n)
      (hΦ := contDiff_vecZ hℓ hΦ j) (hΨ := contDiff_vecZ hℓ hΦ i)]
    ring
  · rw [Work.BoseFixB2.gradeA, if_neg ?_, Work.BoseFixB2.gradeA, if_neg hc]
    intro hsw
    exact hc ⟨hsw.2.2.1, hsw.2.2.2.1, hsw.1, hsw.2.1, hsw.2.2.2.2.2, hsw.2.2.2.2.1⟩

/-! ## 4. The matrix elements of `gradeA` against the profile -/

/-- **The forward matrix element.**  For sector indices `k, k+m ∈ [0,n]`,

`star ψ_k · 𝒜_{k,k+m} · ψ_{k+m} = ⟨1_{n₊=k}Φ, H_Λ 1_{n₊=k+m}Φ⟩/‖Φ‖²`. -/
lemma term_fwd {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓs : 0 < Work.BoseFixB2.fsSide v μ)
    (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {m k : ℕ} (hm : k + m ≤ n) :
    star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ))
        * Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ))
        * Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))
      = ((Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
            (Work.BoseFixB2.secProj ℓ (k + m) Φ) / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ) := by
  have hkn : k ≤ n := le_trans (Nat.le_add_right k m) hm
  have h0k : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hnk : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkn
  have hzm : ((k + m : ℕ) : ℤ) = (k : ℤ) + (m : ℤ) := Int.natCast_add k m
  have h0km : (0 : ℤ) ≤ (k : ℤ) + (m : ℤ) := by rw [← hzm]; exact Int.natCast_nonneg _
  have hnkm : (k : ℤ) + (m : ℤ) ≤ (n : ℤ) := by rw [← hzm]; exact_mod_cast hm
  have hZk : Work.BoseFixB2.vecZ ℓ Φ (k : ℤ) = Work.BoseFixB2.secProj ℓ k Φ := by
    rw [vecZ_apply ℓ h0k hnk, Int.toNat_natCast]
  have hZkm : Work.BoseFixB2.vecZ ℓ Φ ((k : ℤ) + (m : ℤ))
      = Work.BoseFixB2.secProj ℓ (k + m) Φ := by
    rw [vecZ_apply ℓ h0km hnkm, ← hzm, Int.toNat_natCast]
  have hsk : star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ))
      = ((Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ k Φ))
          / Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) : ℝ) : ℂ) := by
    rw [star_gradePsi ℓ h0k hnk, hZk]
  have hPkm : Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))
      = ((Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ (k + m) Φ))
          / Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) : ℝ) : ℂ) := by
    rw [gradePsi_apply ℓ h0km hnkm, hZkm]
  by_cases hz1 : 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ k Φ)
  · by_cases hz2 : 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ (k + m) Φ)
    · have hA : Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ))
          = Complex.ofReal (Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
              (Work.BoseFixB2.secProj ℓ (k + m) Φ)
              / (Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ k Φ))
                  * Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ (k + m) Φ)))) := by
        have hcond : (0 : ℤ) ≤ (k : ℤ) ∧ (k : ℤ) ≤ (n : ℤ) ∧ (0 : ℤ) ≤ (k : ℤ) + (m : ℤ)
            ∧ (k : ℤ) + (m : ℤ) ≤ (n : ℤ)
            ∧ 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ (k : ℤ))
            ∧ 0 < Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.vecZ ℓ Φ ((k : ℤ) + (m : ℤ))) :=
          ⟨h0k, hnk, h0km, hnkm, by rw [hZk]; exact hz1, by rw [hZkm]; exact hz2⟩
        rw [Work.BoseFixB2.gradeA, if_pos hcond, hZk, hZkm]
      have hsq : Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
            * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
          = Work.BoseBoxFix.normB v μ n Φ := by
        simpa [pow_two] using Real.sq_sqrt (normB_nonneg Φ)
      have hreal : (Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ k Φ))
                / Real.sqrt (Work.BoseBoxFix.normB v μ n Φ))
              * (Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
                  (Work.BoseFixB2.secProj ℓ (k + m) Φ)
                  / (Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ k Φ))
                      * Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ (k + m) Φ))))
              * (Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ (k + m) Φ))
                / Real.sqrt (Work.BoseBoxFix.normB v μ n Φ))
          = Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
              (Work.BoseFixB2.secProj ℓ (k + m) Φ) / Work.BoseBoxFix.normB v μ n Φ := by
        set a : ℝ := Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ k Φ))
          with ha
        set b : ℝ := Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) with hb
        set c : ℝ := Real.sqrt (Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ (k + m) Φ))
          with hc
        set p : ℝ := Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
          (Work.BoseFixB2.secProj ℓ (k + m) Φ) with hp
        have ha0 : a ≠ 0 := by rw [ha]; exact Real.sqrt_ne_zero'.mpr hz1
        have hc0 : c ≠ 0 := by rw [hc]; exact Real.sqrt_ne_zero'.mpr hz2
        have hb0 : b ≠ 0 := by rw [hb]; exact Real.sqrt_ne_zero'.mpr hpos
        have hsq' : b * b = Work.BoseBoxFix.normB v μ n Φ := by rw [hb]; exact hsq
        rw [div_mul_div_comm, div_mul_div_comm]
        rw [show (b * (a * c)) * b = (a * c) * (b * b) by ring]
        rw [show (a * p) * c = (a * c) * p by ring]
        rw [mul_div_mul_left p (b * b) (mul_ne_zero ha0 hc0), hsq']
      rw [hsk, hPkm, hA, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_inj]
      exact hreal
    · have h0km' : Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ (k + m) Φ) = 0 :=
        le_antisymm (not_lt.mp hz2) (normB_nonneg _)
      have hA0 : Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ)) = 0 := by
        rw [Work.BoseFixB2.gradeA, if_neg]
        intro hcon
        have hcon' := hcon.2.2.2.2.2
        rw [hZkm] at hcon'
        exact hz2 hcon'
      have hpzero : Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
          (Work.BoseFixB2.secProj ℓ (k + m) Φ) = 0 := by
        rw [Work.BoseFixB2.Polar.polB_symm (hΦ := secProj_contDiff' hℓ hΦ)
          (hΨ := secProj_contDiff' hℓ hΦ)]
        exact polB_eq_zero_of_normB_eq_zero hℓs
          (secProj_contDiff' hℓ hΦ).continuous h0km'
      rw [hA0, hpzero]
      simp
  · have h0k' : Work.BoseBoxFix.normB v μ n (Work.BoseFixB2.secProj ℓ k Φ) = 0 :=
      le_antisymm (not_lt.mp hz1) (normB_nonneg _)
    have hA0 : Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ)) = 0 := by
      rw [Work.BoseFixB2.gradeA, if_neg]
      intro hcon
      have hcon' := hcon.2.2.2.2.1
      rw [hZk] at hcon'
      exact hz1 hcon'
    have hpzero : Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
        (Work.BoseFixB2.secProj ℓ (k + m) Φ) = 0 :=
      polB_eq_zero_of_normB_eq_zero hℓs
        (secProj_contDiff' hℓ hΦ).continuous h0k'
    rw [hA0, hpzero]
    simp

/-- **The backward matrix element:** `star ψ_{k+m} · 𝒜_{k+m,k} · ψ_k` equals the same number,
by symmetry of `𝒜`. -/
lemma term_bwd {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓs : 0 < Work.BoseFixB2.fsSide v μ)
    (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {m k : ℕ} (hm : k + m ≤ n) :
    star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)))
        * Work.BoseFixB2.gradeA v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)) (k : ℤ)
        * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ)
      = ((Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
            (Work.BoseFixB2.secProj ℓ (k + m) Φ) / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ) := by
  have hkn : k ≤ n := le_trans (Nat.le_add_right k m) hm
  have h0k : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
  have hnk : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hkn
  have hzm : ((k + m : ℕ) : ℤ) = (k : ℤ) + (m : ℤ) := Int.natCast_add k m
  have h0km : (0 : ℤ) ≤ (k : ℤ) + (m : ℤ) := by rw [← hzm]; exact Int.natCast_nonneg _
  have hnkm : (k : ℤ) + (m : ℤ) ≤ (n : ℤ) := by rw [← hzm]; exact_mod_cast hm
  have hsym : Work.BoseFixB2.gradeA v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)) (k : ℤ)
      = Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ)) :=
    gradeA_comm (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hΦ
      (k : ℤ) ((k : ℤ) + (m : ℤ))
  have hsk : star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ))
      = Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ) := by
    rw [star_gradePsi ℓ h0k hnk, gradePsi_apply ℓ h0k hnk]
  have hskm : star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)))
      = Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)) := by
    rw [star_gradePsi ℓ h0km hnkm, gradePsi_apply ℓ h0km hnkm]
  rw [hsym, ← term_fwd (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hℓs hpos hΦ hm,
    hsk, hskm]
  ring

/-! ## 5. The `dSup` evaluations -/

/-- **The forward `dSup`.**  `dSup` at shift `m ≥ 1` is the sum of the sector pairs
`(k, k+m)`, `k = 0, …, n-m`. -/
lemma dSup_fwd {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓs : 0 < Work.BoseFixB2.fsSide v μ)
    (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {m : ℕ} (hm : 1 ≤ m) :
    Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n ℓ Φ) (Work.BoseFixB2.fsNn v μ n)
        (Work.BoseFixB2.gradePsi v h μ n ℓ Φ) (m : ℤ)
      = ∑ k ∈ Finset.range (n - (m - 1)),
          (Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
            (Work.BoseFixB2.secProj ℓ (k + m) Φ) / Work.BoseBoxFix.normB v μ n Φ) := by
  have hnn : n + 1 ≤ Work.BoseFixB2.fsNn v μ n := by
    simpa only [Work.BoseFixB2.fsNn] using
      Work.BoseFixB2.succ_le_gradeNn n (𝓜 := Work.BoseFixB2.fsM v μ)
  have hsub : (n : ℤ) - 1 ≤ ((Work.BoseFixB2.fsNn v μ n : ℕ) : ℤ) - 1 := by
    have h : (n : ℤ) + 1 ≤ ((Work.BoseFixB2.fsNn v μ n : ℕ) : ℤ) := by exact_mod_cast hnn
    linarith
  have hvan : ∀ t : ℤ, t ∉ Finset.Icc (0 : ℤ) ((n : ℤ) - 1) →
      star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ t)
        * Work.BoseFixB2.gradeA v h μ n ℓ Φ t (t + (m : ℤ))
        * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (t + (m : ℤ)) = 0 := by
    intro t ht
    rcases lt_or_ge t 0 with ht0 | ht0
    · rw [gradePsi_eq_zero_of_neg ℓ t ht0]; simp
    · have htn : (n : ℤ) ≤ t := by
        by_contra hcon
        exact ht (Finset.mem_Icc.mpr ⟨ht0, by omega⟩)
      have hgt : (n : ℤ) < t + (m : ℤ) := by omega
      rw [gradePsi_eq_zero_of_gt ℓ (t + (m : ℤ)) hgt]; simp
  have h1 : (∑ i ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
        star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ i)
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ i (i + (m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (i + (m : ℤ)))
      = ∑ i ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1),
        star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ i)
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ i (i + (m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (i + (m : ℤ)) := by
    rw [Work.UBBInputs3.iRange]
    exact Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside _
      (le_refl (0 : ℤ)) hsub hvan
  have h2 : (∑ i ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1),
        star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ i)
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ i (i + (m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (i + (m : ℤ)))
      = ∑ k ∈ Finset.range n, (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ))
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))) :=
    sum_Icc_zero_pred_eq_sum_range _ n
  have h3 : (∑ k ∈ Finset.range n, (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ))
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))))
      = ∑ k ∈ Finset.range (n - (m - 1)),
          (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ))
            * Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ))
            * Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    · intro k hk hk'
      rw [Finset.mem_range] at hk hk'
      have hkm : n < k + m := by omega
      have hlt : (n : ℤ) < (k : ℤ) + (m : ℤ) := by
        have h1 : (n : ℤ) < ((k + m : ℕ) : ℤ) := by exact_mod_cast hkm
        rwa [Int.natCast_add] at h1
      rw [gradePsi_eq_zero_of_gt ℓ ((k : ℤ) + (m : ℤ)) hlt]
      simp
  have h4 : (∑ k ∈ Finset.range (n - (m - 1)),
          (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ))
            * Work.BoseFixB2.gradeA v h μ n ℓ Φ (k : ℤ) ((k : ℤ) + (m : ℤ))
            * Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))))
      = ∑ k ∈ Finset.range (n - (m - 1)),
          ((Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
            (Work.BoseFixB2.secProj ℓ (k + m) Φ) / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun k hk => term_fwd (v := v) (h := h) (μ := μ) (n := n)
      (Φ := Φ) hℓ hℓs hpos hΦ (m := m) (k := k) ?_)
    rw [Finset.mem_range] at hk
    omega
  simp only [Work.UBBInputs3.dSup]
  rw [h1, h2, h3, h4]
  exact re_sum_ofReal _ _

/-- **The backward `dSup`.**  The same sum, coming from the shifts `i ↦ i-m`. -/
lemma dSup_bwd {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓs : 0 < Work.BoseFixB2.fsSide v μ)
    (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {m : ℕ} (hm : 1 ≤ m) :
    Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n ℓ Φ) (Work.BoseFixB2.fsNn v μ n)
        (Work.BoseFixB2.gradePsi v h μ n ℓ Φ) (-(m : ℤ))
      = ∑ k ∈ Finset.range (n - (m - 1)),
          (Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
            (Work.BoseFixB2.secProj ℓ (k + m) Φ) / Work.BoseBoxFix.normB v μ n Φ) := by
  have hnn : n + 1 ≤ Work.BoseFixB2.fsNn v μ n := by
    simpa only [Work.BoseFixB2.fsNn] using
      Work.BoseFixB2.succ_le_gradeNn n (𝓜 := Work.BoseFixB2.fsM v μ)
  have hsub : (n : ℤ) ≤ ((Work.BoseFixB2.fsNn v μ n : ℕ) : ℤ) - 1 := by
    have h : (n : ℤ) + 1 ≤ ((Work.BoseFixB2.fsNn v μ n : ℕ) : ℤ) := by exact_mod_cast hnn
    linarith
  have hvan : ∀ t : ℤ, t ∉ Finset.Icc (m : ℤ) (n : ℤ) →
      star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ t)
        * Work.BoseFixB2.gradeA v h μ n ℓ Φ t (t + -(m : ℤ))
        * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (t + -(m : ℤ)) = 0 := by
    intro t ht
    rcases lt_or_ge t (m : ℤ) with ht0 | ht0
    · have hneg : t + -(m : ℤ) < 0 := by omega
      rw [gradePsi_eq_zero_of_neg ℓ (t + -(m : ℤ)) hneg]; simp
    · have htn : (n : ℤ) < t := by
        by_contra hcon
        exact ht (Finset.mem_Icc.mpr ⟨ht0, by omega⟩)
      rw [gradePsi_eq_zero_of_gt ℓ t htn]; simp
  have h1 : (∑ i ∈ Work.UBBInputs3.iRange (Work.BoseFixB2.fsNn v μ n),
        star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ i)
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ i (i + -(m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (i + -(m : ℤ)))
      = ∑ i ∈ Finset.Icc (m : ℤ) (n : ℤ),
        star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ i)
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ i (i + -(m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (i + -(m : ℤ)) := by
    rw [Work.UBBInputs3.iRange]
    exact Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside _
      (Int.natCast_nonneg m) hsub hvan
  have h2 : (∑ i ∈ Finset.Icc (m : ℤ) (n : ℤ),
        star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ i)
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ i (i + -(m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (i + -(m : ℤ)))
      = ∑ k ∈ Finset.range (n + 1 - m),
        (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)))
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))
              (((k : ℤ) + (m : ℤ)) + -(m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (((k : ℤ) + (m : ℤ)) + -(m : ℤ))) :=
    sum_Icc_cast_eq_sum_range _ m n
  have h3 : (∑ k ∈ Finset.range (n + 1 - m),
        (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)))
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ ((k : ℤ) + (m : ℤ))
              (((k : ℤ) + (m : ℤ)) + -(m : ℤ))
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (((k : ℤ) + (m : ℤ)) + -(m : ℤ))))
      = ∑ k ∈ Finset.range (n + 1 - m),
        (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)))
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)) (k : ℤ)
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ((k : ℤ) + (m : ℤ)) + -(m : ℤ) = (k : ℤ) by ring]
  have h4 : n + 1 - m = n - (m - 1) := by omega
  have h5 : (∑ k ∈ Finset.range (n - (m - 1)),
        (star (Work.BoseFixB2.gradePsi v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)))
          * Work.BoseFixB2.gradeA v h μ n ℓ Φ ((k : ℤ) + (m : ℤ)) (k : ℤ)
          * Work.BoseFixB2.gradePsi v h μ n ℓ Φ (k : ℤ)))
      = ∑ k ∈ Finset.range (n - (m - 1)),
          ((Work.BoseFixB2.polB v h μ n (Work.BoseFixB2.secProj ℓ k Φ)
            (Work.BoseFixB2.secProj ℓ (k + m) Φ) / Work.BoseBoxFix.normB v μ n Φ : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun k hk => term_bwd (v := v) (h := h) (μ := μ) (n := n)
      (Φ := Φ) hℓ hℓs hpos hΦ (m := m) (k := k) ?_)
    rw [Finset.mem_range] at hk
    omega
  simp only [Work.UBBInputs3.dSup]
  rw [h1, h2, h3, h4, h5]
  exact re_sum_ofReal _ _

/-! ## 6. The target -/

theorem dk_gradeA_one_two {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hav : 0 < _root_.BoseGases.a v) {μ : ℝ} (hμ : 0 < μ) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hpos : 0 < Work.BoseBoxFix.normB v μ n Φ) : Work.UBBInputs3.dk (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.BoseFixB2.fsNn v μ n) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) 1 = Work.BoseFixB2.dOne v h μ n (Work.BoseFixB2.fsSide v μ) Φ ∧ Work.UBBInputs3.dk (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (Work.BoseFixB2.fsNn v μ n) (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) 2 = Work.BoseFixB2.dTwo v h μ n (Work.BoseFixB2.fsSide v μ) Φ := by
  have hℓ : 0 < Work.BoseFixB2.fsSide v μ := Work.BoseBox.sideAt_pos hμ hav
  constructor
  · have h1 : Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
          (Work.BoseFixB2.fsNn v μ n)
          (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) 1
        = ∑ k ∈ Finset.range n,
            (Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 1) Φ)
              / Work.BoseBoxFix.normB v μ n Φ) := by
      simpa using dSup_fwd (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hℓ hpos hΦ
        (m := 1) le_rfl
    have h2 : Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
          (Work.BoseFixB2.fsNn v μ n)
          (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (-1)
        = ∑ k ∈ Finset.range n,
            (Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 1) Φ)
              / Work.BoseBoxFix.normB v μ n Φ) := by
      simpa using dSup_bwd (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hℓ hpos hΦ
        (m := 1) le_rfl
    have hS : (∑ k ∈ Finset.range n,
          (Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 1) Φ)
            / Work.BoseBoxFix.normB v μ n Φ))
        = (∑ k ∈ Finset.range n,
            Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 1) Φ))
          / Work.BoseBoxFix.normB v μ n Φ :=
      (Finset.sum_div _ _ _).symm
    rw [Work.UBBInputs3.dk, if_neg (by norm_num : ¬((1 : ℤ) = 0)), h1, h2]
    rw [Work.BoseFixB2.dOne, hS]
    ring
  · have h1 : Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
          (Work.BoseFixB2.fsNn v μ n)
          (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) 2
        = ∑ k ∈ Finset.range (n - 1),
            (Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 2) Φ)
              / Work.BoseBoxFix.normB v μ n Φ) := by
      simpa using dSup_fwd (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hℓ hpos hΦ
        (m := 2) (by norm_num)
    have h2 : Work.UBBInputs3.dSup (Work.BoseFixB2.gradeA v h μ n (Work.BoseFixB2.fsSide v μ) Φ)
          (Work.BoseFixB2.fsNn v μ n)
          (Work.BoseFixB2.gradePsi v h μ n (Work.BoseFixB2.fsSide v μ) Φ) (-2)
        = ∑ k ∈ Finset.range (n - 1),
            (Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 2) Φ)
              / Work.BoseBoxFix.normB v μ n Φ) := by
      simpa using dSup_bwd (v := v) (h := h) (μ := μ) (n := n) (Φ := Φ) hℓ hℓ hpos hΦ
        (m := 2) (by norm_num)
    have hS : (∑ k ∈ Finset.range (n - 1),
          (Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 2) Φ)
            / Work.BoseBoxFix.normB v μ n Φ))
        = (∑ k ∈ Finset.range (n - 1),
            Work.BoseFixB2.polB v h μ n
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) k Φ)
              (Work.BoseFixB2.secProj (Work.BoseFixB2.fsSide v μ) (k + 2) Φ))
          / Work.BoseBoxFix.normB v μ n Φ :=
      (Finset.sum_div _ _ _).symm
    rw [Work.UBBInputs3.dk, if_neg (by norm_num : ¬((2 : ℤ) = 0)), h1, h2]
    rw [Work.BoseFixB2.dTwo, hS]
    ring

end Work.BoseFixB2.DvApriori
