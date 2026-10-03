import Submission.Work.FIArea2.CCountPoissonDefs
import Submission.Work.FIArea2.Adm_iff_dvd
import Submission.Work.FIArea2.Kpar_bound
import Submission.Work.FIArea2.PsiC_contDiff_hasCompactSupport
import Submission.Work.FIArea2.tsum_Gh_eq_class_tsums
import Submission.Work.FIArea2.Gsum_class_sum
import Submission.Work.FIArea2.summable_ft2coset
import Submission.Work.FIArea2.inv_mul_secScale
import Submission.Work.FIArea2.ft2real_PsiC_eq

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

namespace CcountSmooth

/-- `(Zc w z₁ · Zc w z₂)` is the product of the two real `Z`-values. -/
lemma Zc_mul_re (w z1 z2 : GaussianInt) :
    (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re
      = (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ) := by
  simp only [Work.FITop3.Zc, Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul,
    sub_zero]

/-- `Adm` in the modulus form in which (6.10) states the congruence. -/
lemma Adm_iff_mod (z1 z2 : GaussianInt) (p : ℤ × ℤ) :
    Adm z1 z2 p ↔ (Xof z1 z2 p).re % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0 ∧
      (Xof z1 z2 p).im % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0 := by
  simp only [Adm, Int.dvd_iff_emod_eq_zero]

/-- The class sum of `Gh` over an admissible class is the Poisson sum of the smooth phase. -/
lemma class_tsum_Gh (F : ℝ → ℝ) (z1 z2 : GaussianInt) (γ : ℕ × ℕ)
    (hγ : Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))) :
    (∑' c : ℤ × ℤ, Gh F z1 z2 (cosetVec (Work.FIPlan.absDelta z1 z2) γ c))
      = ∑' c : ℤ × ℤ, PsiC F z1 z2
          (cosetPt (Work.FIPlan.absDelta z1 z2) ((γ.1 : ℤ), (γ.2 : ℤ)) c) := by
  apply tsum_congr
  intro c
  rw [Gh_of_adm ((Adm_cosetVec z1 z2 γ c).mpr hγ), cosetPt_eq_cosetVec]

/-- An inadmissible class contributes nothing. -/
lemma class_tsum_Gh_of_not_adm (F : ℝ → ℝ) (z1 z2 : GaussianInt) (γ : ℕ × ℕ)
    (hγ : ¬ Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))) :
    (∑' c : ℤ × ℤ, Gh F z1 z2 (cosetVec (Work.FIPlan.absDelta z1 z2) γ c)) = 0 := by
  rw [show (fun c : ℤ × ℤ => Gh F z1 z2 (cosetVec (Work.FIPlan.absDelta z1 z2) γ c))
      = fun _ => 0 from funext (fun c => Gh_of_not_adm
        (fun h => hγ ((Adm_cosetVec z1 z2 γ c).mp h)))]
  exact tsum_zero

/-- **The support condition of the lattice sum**: an admissible lattice point with non-vanishing
phase lies in the truncation box `Kbox Pa z₁ z₂` of (6.7). -/
lemma Gh_support (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hbox : ∀ w : GaussianInt, F (Work.FIPlan.gnorm w) ≠ 0 → w ∈ Work.FITop.boxM Pa) :
    ∀ p : ℤ × ℤ, Adm z1 z2 p → PsiC F z1 z2 ((p.1 : ℝ), (p.2 : ℝ)) ≠ 0 →
      p ∈ Kbox Pa z1 z2 := by
  intro p hadm hne
  have hex : ∃ w : GaussianInt, Work.FIPlan.cForm w z1 = p.1 * p.1 ∧
      Work.FIPlan.cForm w z2 = p.2 * p.2 :=
    (exists_cForm_eq_iff z1 z2 hΔ p.1 p.2).mpr (by
      rw [← Xof_eq]
      exact (Adm_iff_dvd z1 z2 p).mp hadm)
  have hFne : F (gphase z1 z2 ((p.1 : ℝ), (p.2 : ℝ))) ≠ 0 := by
    intro h
    exact hne (by rw [PsiC_apply, h]; simp)
  rw [gphase_wOf z1 z2 hΔ hex] at hFne
  have hwbox : wOf z1 z2 p.1 p.2 ∈ Work.FITop.boxM Pa := hbox _ hFne
  have hb := Kpar_bound Pa z1 z2 hwbox (cForm_wOf hex).1 (cForm_wOf hex).2
  simp only [Kbox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hb.1, hb.2.1⟩, ⟨hb.2.2.1, hb.2.2.2⟩⟩

/-- **(6.7) plus the truncation**: the `w`-sum of (5.27) is the `ℤ²`-sum of the
admissibility-restricted lattice phase. -/
lemma Ccount_eq_tsum_Gh (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hF : ContDiff ℝ 4 F) (hcs : HasCompactSupport F)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hbox : ∀ w : GaussianInt, F (Work.FIPlan.gnorm w) ≠ 0 → w ∈ Work.FITop.boxM Pa) :
    ((Ccount Pa (fun n => F n) z1 z2 : ℝ) : ℂ) = ∑' p : ℤ × ℤ, Gh F z1 z2 p := by
  have hm : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    simpa [Work.FIPlan.absDelta, Int.natAbs_eq_zero] using hΔ
  -- the truncation set `S` of (6.7)
  have hS_mem : ∀ p : ℤ × ℤ, p ∈ (Kbox Pa z1 z2).filter (fun p =>
      (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
          - (p.2 : GaussianInt) ^ 2 * z1
        ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox (Work.FITop.radM Pa)) ↔
      p.1 ∈ Finset.Icc (-(Kpar Pa z1 z2 : ℤ)) (Kpar Pa z1 z2 : ℤ) ∧
      p.2 ∈ Finset.Icc (-(Kpar Pa z1 z2 : ℤ)) (Kpar Pa z1 z2 : ℤ) ∧
      (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
          - (p.2 : GaussianInt) ^ 2 * z1
        ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox (Work.FITop.radM Pa) := by
    intro p
    simp only [Finset.mem_filter, Kbox, Finset.mem_product]
    tauto
  have hK : ∀ w ∈ Work.FIPlan.gBox (Work.FITop.radM Pa), ∀ c1 c2 : ℤ,
      Work.FIPlan.cForm w z1 = c1 * c1 → Work.FIPlan.cForm w z2 = c2 * c2 →
      -(Kpar Pa z1 z2 : ℤ) ≤ c1 ∧ c1 ≤ (Kpar Pa z1 z2 : ℤ) ∧
      -(Kpar Pa z1 z2 : ℤ) ≤ c2 ∧ c2 ≤ (Kpar Pa z1 z2 : ℤ) := by
    intro w hw c1 c2 h1 h2
    exact Kpar_bound Pa z1 z2 hw h1 h2
  have hstep1 : (∑ w ∈ Work.FITop.boxM Pa, F (Work.FIPlan.gnorm w)
        * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re)
      = ∑ p ∈ (Kbox Pa z1 z2).filter (fun p =>
          (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
              - (p.2 : GaussianInt) ^ 2 * z1
            ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox (Work.FITop.radM Pa)),
          F (Work.FIPlan.gnorm (wOf z1 z2 p.1 p.2)) := by
    rw [show (∑ w ∈ Work.FITop.boxM Pa, F (Work.FIPlan.gnorm w)
          * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re)
        = ∑ w ∈ Work.FIPlan.gBox (Work.FITop.radM Pa), (fun n => F n) (Work.FIPlan.gnorm w)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ) from by
      simp only [Work.FITop.boxM]
      apply Finset.sum_congr rfl
      intro w _
      rw [Zc_mul_re, mul_assoc]]
    exact sum_gBox_eq_sum_congruences (Work.FITop.radM Pa) (fun n => F n) z1 z2 hΔ
      (Kpar Pa z1 z2) _ hK hS_mem
  -- rewrite the summand of `S` as the lattice phase
  have hstep2 : ((∑ p ∈ (Kbox Pa z1 z2).filter (fun p =>
          (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
              - (p.2 : GaussianInt) ^ 2 * z1
            ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox (Work.FITop.radM Pa)),
          F (Work.FIPlan.gnorm (wOf z1 z2 p.1 p.2)) : ℝ) : ℂ)
      = ∑ p ∈ (Kbox Pa z1 z2).filter (fun p =>
          (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
              - (p.2 : GaussianInt) ^ 2 * z1
            ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox (Work.FITop.radM Pa)),
          PsiC F z1 z2 ((p.1 : ℝ), (p.2 : ℝ)) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨-, -, hdvd, -⟩ := (hS_mem p).mp hp
    have hex : ∃ w : GaussianInt, Work.FIPlan.cForm w z1 = p.1 * p.1 ∧
        Work.FIPlan.cForm w z2 = p.2 * p.2 :=
      (exists_cForm_eq_iff z1 z2 hΔ p.1 p.2).mpr hdvd
    rw [PsiC_apply, gphase_wOf z1 z2 hΔ hex]
  -- extend the truncated sum to the full box
  have hstep3 : (∑ p ∈ (Kbox Pa z1 z2).filter (fun p =>
          (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
              - (p.2 : GaussianInt) ^ 2 * z1
            ∧ wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox (Work.FITop.radM Pa)),
          PsiC F z1 z2 ((p.1 : ℝ), (p.2 : ℝ)))
      = ∑ p ∈ Kbox Pa z1 z2, Gh F z1 z2 p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hadm : Adm z1 z2 p
    · have hdvd : (Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
          - (p.2 : GaussianInt) ^ 2 * z1 := by
        have h := (Adm_iff_dvd z1 z2 p).mp hadm
        rwa [Xof_eq] at h
      by_cases hb : wOf z1 z2 p.1 p.2 ∈ Work.FIPlan.gBox (Work.FITop.radM Pa)
      · rw [if_pos ⟨hdvd, hb⟩, Gh_of_adm hadm]
      · rw [if_neg (fun h => hb h.2), Gh_of_adm hadm, PsiC_apply]
        have hex : ∃ w : GaussianInt, Work.FIPlan.cForm w z1 = p.1 * p.1 ∧
            Work.FIPlan.cForm w z2 = p.2 * p.2 :=
          (exists_cForm_eq_iff z1 z2 hΔ p.1 p.2).mpr hdvd
        rw [gphase_wOf z1 z2 hΔ hex]
        have hzero : F (Work.FIPlan.gnorm (wOf z1 z2 p.1 p.2)) = 0 := by
          by_contra hc
          exact hb (hbox _ hc)
        rw [hzero, Complex.ofReal_zero]
    · have hnot : ¬ ((Work.FIPlan.Delta z1 z2 : GaussianInt) ∣ (p.1 : GaussianInt) ^ 2 * z2
          - (p.2 : GaussianInt) ^ 2 * z1) := by
        intro h
        exact hadm ((Adm_iff_dvd z1 z2 p).mpr (by rw [Xof_eq]; exact h))
      rw [if_neg (fun h => hnot h.1), Gh_of_not_adm hadm]
  -- the finite box sum is the full `ℤ²`-sum
  have hsupp := Gh_support Pa F z1 z2 hΔ hbox
  have hstep4 : (∑ p ∈ Kbox Pa z1 z2, Gh F z1 z2 p) = ∑' p : ℤ × ℤ, Gh F z1 z2 p := by
    symm
    apply tsum_eq_sum
    intro p hp
    by_cases hadm : Adm z1 z2 p
    · rw [Gh_of_adm hadm]
      by_contra hne
      exact hp (hsupp p hadm hne)
    · exact Gh_of_not_adm hadm
  rw [show ((Ccount Pa (fun n => F n) z1 z2 : ℝ) : ℂ)
      = ((∑ w ∈ Work.FITop.boxM Pa, F (Work.FIPlan.gnorm w)
        * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re : ℝ) : ℂ) from rfl]
  rw [hstep1, hstep2, hstep3, hstep4]
/-- The scalar bookkeeping of (6.9): the two factors `|Δ|⁻¹` (from the Poisson summation on
each coset) and `s₁s₂` (from the change of variables) together are
`|z₁z₂|^{-1/2} = gnorm(z₁z₂)^{-1/4}`, the prefactor of (6.13). -/
lemma poisson_final (z1 z2 : GaussianInt) (hm : Work.FIPlan.absDelta z1 z2 ≠ 0) (X : ℂ) :
    (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)⁻¹ * ((((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) : ℂ)) * X)
      = ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) * X := by
  have hcR : (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)⁻¹ * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * (Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ))
      = (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4)) := by
    rw [← inv_mul_secScale z1 z2 hm]
    field_simp
  have hcc : (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)⁻¹ * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) : ℂ)) = ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) := by
    rw [show (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)⁻¹ * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) : ℂ))
        = (((((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)⁻¹ * (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * (Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ)) : ℝ) : ℂ) from by
      push_cast
      ring]
    rw [hcR]
  rw [← mul_assoc, hcc]

/-- **(6.9), the Poisson side**: the admissibility-restricted lattice sum is the sum over the
frequencies `h ∈ ℤ²` of the Fourier integral `Fint` times the arithmetic sum `Gsum` of (6.10). -/
lemma tsum_Gh_eq_poisson (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hF : ContDiff ℝ 4 F) (hcs : HasCompactSupport F)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hbox : ∀ w : GaussianInt, F (Work.FIPlan.gnorm w) ≠ 0 → w ∈ Work.FITop.boxM Pa) :
    (∑' p : ℤ × ℤ, Gh F z1 z2 p)
      = ((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) * ∑' h : ℤ × ℤ, Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2)
              (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
              (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))) * Work.FIArea2.Gsum z1 z2 h.1 h.2 := by
  have hm : Work.FIPlan.absDelta z1 z2 ≠ 0 := by
    simpa [Work.FIPlan.absDelta, Int.natAbs_eq_zero] using hΔ
  have hm1 : 1 ≤ Work.FIPlan.absDelta z1 z2 := Nat.one_le_iff_ne_zero.mpr hm
  obtain ⟨hPsiC, hcsC⟩ := PsiC_contDiff_hasCompactSupport F z1 z2 hF hcs hΔ
  have hsupp := Gh_support Pa F z1 z2 hΔ hbox
  -- (A) the class decomposition
  rw [tsum_Gh_eq_class_tsums Pa F z1 z2 hm hsupp]
  -- (B) only the admissible classes contribute
  rw [show (∑ γ ∈ Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2), ∑' c : ℤ × ℤ, Gh F z1 z2 (cosetVec (Work.FIPlan.absDelta z1 z2) γ c))
      = ∑ γ ∈ Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2),
          (if Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ)) then ∑' c : ℤ × ℤ, PsiC F z1 z2
              (cosetPt (Work.FIPlan.absDelta z1 z2) ((γ.1 : ℤ), (γ.2 : ℤ)) c) else 0) from
    Finset.sum_congr rfl (fun γ _ => by
      by_cases hγ : Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))
      · rw [if_pos hγ, class_tsum_Gh F z1 z2 γ hγ]
      · rw [if_neg hγ, class_tsum_Gh_of_not_adm F z1 z2 γ hγ])]
  rw [← Finset.sum_filter]
  -- (C) Poisson summation on each class, and interchange of the class and frequency sums
  rw [show (∑ γ ∈ (Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)).filter
            (fun γ => Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))), ∑' c : ℤ × ℤ, PsiC F z1 z2
              (cosetPt (Work.FIPlan.absDelta z1 z2) ((γ.1 : ℤ), (γ.2 : ℤ)) c))
      = ∑ γ ∈ (Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)).filter
            (fun γ => Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))),
          (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ^ 2)⁻¹ *
            (∑' h : ℤ × ℤ, ft2coset (PsiC F z1 z2) (Work.FIPlan.absDelta z1 z2)
              ((γ.1 : ℤ), (γ.2 : ℤ)) h) from
    Finset.sum_congr rfl (fun γ _ => poisson_coset_2d (PsiC F z1 z2) hPsiC hcsC
      (Work.FIPlan.absDelta z1 z2) hm1 ((γ.1 : ℤ), (γ.2 : ℤ)))]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum
    (f := fun (γ : ℕ × ℕ) (h : ℤ × ℤ) => ft2coset (PsiC F z1 z2)
      (Work.FIPlan.absDelta z1 z2) ((γ.1 : ℤ), (γ.2 : ℤ)) h)
    (fun γ _ => summable_ft2coset (PsiC F z1 z2) hPsiC hcsC
      (Work.FIPlan.absDelta z1 z2) hm1 ((γ.1 : ℤ), (γ.2 : ℤ)))]
  -- (D) the summand of the frequency sum
  have hterm : ∀ h : ℤ × ℤ,
      (∑ γ ∈ (Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)).filter
            (fun γ => Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))),
          ft2coset (PsiC F z1 z2) (Work.FIPlan.absDelta z1 z2) ((γ.1 : ℤ), (γ.2 : ℤ)) h)
      = (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * Gsum z1 z2 h.1 h.2) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) * Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))) := by
    intro h
    have h1 : (∑ γ ∈ (Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)).filter
            (fun γ => Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))),
          ft2coset (PsiC F z1 z2) (Work.FIPlan.absDelta z1 z2) ((γ.1 : ℤ), (γ.2 : ℤ)) h)
        = (∑ γ ∈ (Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)).filter
            (fun γ => Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))), eGam (Work.FIPlan.absDelta z1 z2) γ h.1 h.2)
          * ft2real (PsiC F z1 z2) ((h.1 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) ((h.2 : ℝ) / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro γ _
      rw [ft2coset_eq_exp_mul_ft2real]
      congr 1
      congr 1
      push_cast
      ring
    have h2 : (∑ γ ∈ (Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2)).filter
            (fun γ => Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))), eGam (Work.FIPlan.absDelta z1 z2) γ h.1 h.2)
        = ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * Gsum z1 z2 h.1 h.2 := by
      rw [Finset.sum_filter]
      rw [show (∑ γ ∈ Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2),
            (if Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ)) then
              eGam (Work.FIPlan.absDelta z1 z2) γ h.1 h.2 else 0))
          = ∑ γ ∈ Finset.range (Work.FIPlan.absDelta z1 z2)
          ×ˢ Finset.range (Work.FIPlan.absDelta z1 z2),
            (if (Xof z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))).re % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
                  ∧ (Xof z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))).im % ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) = 0
              then eGam (Work.FIPlan.absDelta z1 z2) γ h.1 h.2 else 0) from
        Finset.sum_congr rfl (fun γ _ => by
          by_cases hc : Adm z1 z2 ((γ.1 : ℤ), (γ.2 : ℤ))
          · rw [if_pos hc, if_pos ((Adm_iff_mod z1 z2 _).mp hc)]
          · rw [if_neg hc, if_neg (fun hh => hc ((Adm_iff_mod z1 z2 _).mpr hh))])]
      exact Gsum_class_sum z1 z2 hm h.1 h.2
    rw [h1, h2, ft2real_PsiC_eq F z1 z2 hm (h.1 : ℝ) (h.2 : ℝ)]
    push_cast
    ring
  rw [tsum_congr hterm]
  -- (E) the final scalar bookkeeping
  rw [show (∑' h : ℤ × ℤ, (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * Gsum z1 z2 h.1 h.2) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) * Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))))
      = (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) : ℂ)) * ∑' h : ℤ × ℤ, Gsum z1 z2 h.1 h.2 * Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) from by
    rw [show (∑' h : ℤ × ℤ, (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * Gsum z1 z2 h.1 h.2) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) * Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))))
        = ∑' h : ℤ × ℤ, (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℂ) * ((Work.FIArea2.secScale₁ z1 z2 * Work.FIArea2.secScale₂ z1 z2 : ℝ) : ℂ)) * (Gsum z1 z2 h.1 h.2 * Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ)))) from
      tsum_congr (fun h => by push_cast; ring)]
    rw [tsum_mul_left]]
  rw [tsum_congr (fun h => mul_comm _ _)]
  exact poisson_final z1 z2 hm (∑' h : ℤ × ℤ, Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℕ) : ℝ))) (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) * Real.sqrt ((Work.FIPlan.gnorm z1 : ℕ) : ℝ))) * Gsum z1 z2 h.1 h.2)

end CcountSmooth

open CcountSmooth

/-- **Friedlander-Iwaniec (6.9)**, in the smooth form in which section 6 applies it.  For a C^4
function `F` of compact support (`F` plays the role of the majorant, applied to `|w|^2`; the frozen
`IsMajorant`'s discrete `f : Z -> R` is turned into such an `F` by
`Work.FIArea2.smooth_ext_of_isMajorant`), for `z1, z2` in `Z[i]` with `Delta(z1,z2) = Im(conj z1 * z2) != 0`,
and under the support condition that every `w` with `F(|w|^2) != 0` lies in the box `boxM Pa` of (4.18),

  `C(z1,z2) = |z1 z2|^{-1/2} * sum_{h1,h2} F(h1 |Delta z2|^{-1/2}, h2 |Delta z1|^{-1/2}) * G(h1,h2)`

where `C(z1,z2) = sum_w F(|w|^2) * Z(Re w z1) * Z(Re w z2)` is (5.27) (the left-hand side here equals
`Work.FIArea2.Ccount Pa (fun n => F n) z1 z2`), `F(u1,u2)` is the Fourier integral `Fint` of (6.8),
`G` is the arithmetic sum `Gsum` of (6.10), `|z|` is the *modulus* so that
`|Delta z_j|^{-1/2} = 1 / sqrt(|Delta| * sqrt(gnorm z_j))`, and the series over `h` in `Z^2` is
absolutely convergent; the `h = 0` term is `|z1 z2|^{-1/2} * F(0,0) * G_0`, i.e. (6.13).

Route: (1) `Work.FIArea2.sum_gBox_eq_sum_congruences` re-parametrises the `w`-sum as a sum over the
pairs `(c1,c2)` in `Z^2` with `Delta | c1^2 z2 - c2^2 z1` and `wOf z1 z2 c1 c2` in `boxM Pa` of
`F(|wOf|^2)`, and `Work.FIArea2.gphase_wOf` identifies `|wOf z1 z2 c1 c2|^2` with
`gphase z1 z2 (c1,c2)`, so the summand is the value at `(c1,c2)` of `phi = F composed with gphase z1 z2`
(`Work.FIArea2.phiOf`); (2) split the sum over `Z^2` into the residue classes `(gamma1,gamma2)` modulo
`m = |Delta|` -- a class contributes iff `gamma1^2 z2 = gamma2^2 z1 (mod m)`, by (6.4) -- and apply the
two-dimensional Poisson summation `Work.FIArea2.poisson_coset_2d` to each admissible class, using
`Work.FIArea2.ft2coset_eq_exp_mul_ft2real`; (3) sum over the classes, using the definition of `Gsum`
to recognise `sum_{gamma admissible} e((gamma1 h1 + gamma2 h2)/m) = m * G(h1,h2)`; (4) identify
`ft2real phi(h1/m, h2/m)` with `s1 s2 * Fint F gamma (-h1 |Delta z2|^{-1/2}, -h2 |Delta z1|^{-1/2})`
via `Work.FIArea2.sec6_change_of_variables` and `Work.FIArea2.Fint_eq_ft2real`, using
`s_j / m = |Delta z_{3-j}|^{-1/2}` and `m^{-1} s1 s2 = |z1 z2|^{-1/2}`; (5) absolute convergence of the
`h`-series follows from integrating by parts twice in each variable (available from `ContDiff 4`). -/
theorem Ccount_smooth_eq_poisson (Pa : Work.FITop.Params) (F : ℝ → ℝ) (z1 z2 : GaussianInt)
    (hF : ContDiff ℝ 4 F) (hcs : HasCompactSupport F)
    (hΔ : Work.FIPlan.Delta z1 z2 ≠ 0)
    (hbox : ∀ w : GaussianInt, F (Work.FIPlan.gnorm w) ≠ 0 → w ∈ Work.FITop.boxM Pa) :
    ((∑ w ∈ Work.FITop.boxM Pa, F (Work.FIPlan.gnorm w)
        * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re : ℝ) : ℂ)
      = (((((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4) : ℝ)) : ℂ)
          * ∑' h : ℤ × ℤ, Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2)
              (-(h.1 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z2 : ℕ) : ℝ))))
              (-(h.2 : ℝ) / Real.sqrt (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.sqrt (((Work.FIPlan.gnorm z1 : ℕ) : ℝ))))
            * Work.FIArea2.Gsum z1 z2 h.1 h.2 := by
  rw [show ((∑ w ∈ Work.FITop.boxM Pa, F (Work.FIPlan.gnorm w)
        * (Work.FITop3.Zc w z1 * Work.FITop3.Zc w z2).re : ℝ) : ℂ)
      = ((Ccount Pa (fun n => F n) z1 z2 : ℝ) : ℂ) from rfl]
  rw [Ccount_eq_tsum_Gh Pa F z1 z2 hF hcs hΔ hbox]
  exact tsum_Gh_eq_poisson Pa F z1 z2 hF hcs hΔ hbox

end

end Work.FIArea2
