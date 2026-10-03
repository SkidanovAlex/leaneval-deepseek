import Mathlib
import Submission.Work.KMTPlan.A6.lowModel_eq_bilinOp_symM
import Submission.Work.KMTAreas.A7.integral_bilinOp_convOp_comm
import Submission.Work.KMTPlan.A6.vpc_summable_arithKernel_cw
import Submission.Work.KMTPlan.A6.Tle_piExact_eq_convOp
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTPlan.A6

open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger
open Work.Analysis.EndVar
open Work.KMTContract

noncomputable section

/-! ## Auxiliary -/

theorem one_le_uScale (ρ : ℝ) (hρ : 0 < ρ) (L : ℕ) : 1 ≤ Work.KMTAreas.A7.uScale ρ L := by
  have h0 : (0 : ℝ) ≤ 2 * ρ * (L : ℝ) := by positivity
  have h1 : (((1 : ℤ) : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
    have h := Real.one_le_rpow (x := (2 : ℝ)) (z := 2 * ρ * (L : ℝ)) (by norm_num) h0
    simpa using h
  have h3 : (1 : ℤ) ≤ ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := Int.le_floor.mpr h1
  unfold Work.KMTAreas.A7.uScale Work.Analysis.EndVar.scaleCount
  simp only [Nat.cast_one, one_mul]
  exact (Int.le_toNat (le_trans (by norm_num : (0:ℤ) ≤ 1) h3)).mpr h3

/-! ## The periodisation of the modulated `d`-fold bump is bounded -/

/-- **`MemLp (periodize (φ̃_{N,t})) ⊤`.**  The modulated `d`-fold bump `φ̃_{N,t}` is `C²`, of
compact support and bounded by `2`; the periodisation of such a bump is bounded, hence in
`L^∞(ℝ/ℤ)`. -/
theorem memLp_periodize_varphitildeNt_aux (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    MemLp (periodize (varphitildeNt P d N k t)) ⊤ circleMeasure := by
  have hmeas : Measurable (varphitildeNt P d N k t) :=
    (contDiff_varphitildeNt_aux P d N k t).continuous.measurable
  obtain ⟨R₀, hR₀⟩ :=
    exists_abs_le_of_hasCompactSupport (hasCompactSupport_varphitildeNt_aux P d N k t)
  refine memLp_periodize hmeas (R := max R₀ 0) (C := 2) (le_max_right R₀ 0) ?_ ?_
  · intro y hy
    exact hR₀ y (le_of_lt (lt_of_le_of_lt (le_max_left R₀ 0) hy))
  · intro y
    rw [varphitildeNt, norm_mul, norm_ee, mul_one, varphitildeN]
    split_ifs with hk
    · exact le_trans (norm_kmtEta_le _) (by norm_num)
    · calc ‖kmtEta _ - kmtEta _‖ ≤ ‖kmtEta _‖ + ‖kmtEta _‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (norm_kmtEta_le _) (norm_kmtEta_le _)
        _ = 2 := by norm_num

/-! ## `ℓ²` sequences on `ℤ` are bounded, and the Fubini identity for `ℓ²` inputs -/

/-- An `ℓ²` sequence on `ℤ` (i.e. an element of `L²(ℤ)` for the counting measure) is bounded:
`‖f y‖ ≤ sqrt (∑' j, ‖f j‖²)`, because the single term `‖f y‖²` is dominated by the full sum. -/
theorem exists_norm_bound_of_memLp_count_aux {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℤ, ‖f y‖ ≤ C := by
  have hmem : Memℓp f (2 : ℝ≥0∞) := memlpOfMemLpCount (by norm_num) (by norm_num) hf
  have hfsum : Summable (fun j : ℤ => ‖f j‖ ^ 2) := by
    have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hmem
    simpa using h
  refine ⟨Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2), Real.sqrt_nonneg _, fun y => ?_⟩
  exact (Real.le_sqrt (norm_nonneg _) (tsum_nonneg (fun j => by positivity))).mpr
    (hfsum.le_tsum y (fun j _ => by positivity))

/-- **The Fubini identity of §6 for `ℓ²` inputs.**  Same as
`Work.KMTAreas.A7.integral_bilinOp_convOp_comm` but with the two inputs only assumed to lie in
`ℓ²(ℤ)`; the pointwise boundedness needed by the bounded version is deduced from `ℓ²` (a single
term is dominated by the sum). -/
theorem integral_bilinOp_convOp_comm_memLp_aux (K : ℤ → ℤ → ℂ) (κ κ' : ℝ → ℤ → ℂ)
    (f g : ℤ → ℂ) (B1 B2 : ℝ) (x : ℤ)
    (hK : Summable (fun p : ℤ × ℤ => ‖K p.1 p.2‖))
    (hκ : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ t j‖))
    (hκ' : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, Summable (fun j : ℤ => ‖κ' t j‖))
    (hκb : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ t j‖) ≤ B1)
    (hκb' : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, (∑' j : ℤ, ‖κ' t j‖) ≤ B2)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hmκ : ∀ j : ℤ, Measurable (fun t : ℝ => κ t j))
    (hmκ' : ∀ j : ℤ, Measurable (fun t : ℝ => κ' t j)) :
    (∫ t in (1/2 : ℝ)..1, Work.KMTAreas.A7.bilinOp K
        (Work.KMTAreas.A7.convOp (κ t) f) (Work.KMTAreas.A7.convOp (κ' t) g) x)
      = Work.KMTAreas.A7.bilinOp (fun a b : ℤ =>
          ∫ t in (1/2 : ℝ)..1, Work.KMTAreas.A7.kernComp K (κ t) (κ' t) a b) f g x := by
  obtain ⟨Cf, hCf, hfb⟩ := exists_norm_bound_of_memLp_count_aux hf
  obtain ⟨Cg, hCg, hgb⟩ := exists_norm_bound_of_memLp_count_aux hg
  exact Work.KMTAreas.A7.integral_bilinOp_convOp_comm K κ κ' f g
    (∑' p : ℤ × ℤ, ‖K p.1 p.2‖) B1 B2 Cf Cg x hK (le_refl _) hκ hκ' hκb hκb'
    hfb hgb hCf hCg (tsum_nonneg (fun p => norm_nonneg _)) hB1 hB2 hmκ hmκ'

/-! ## The main identity -/

theorem mdlPart_eq_bilinOp_maeKmod (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) (f g : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hnA₁ : Work.Analysis.IonescuWainger.NonAliasing
        (-(Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    (hnA₂ : Work.Analysis.IonescuWainger.NonAliasing
        (-(Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ))
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hcore : Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
          (Nat.floor (a n))
        ∧ Work.KMTAreas.A7.splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
        ∧ Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)))
    (hΦ₁ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Work.Analysis.IonescuWainger.SupportedInArc
        (-(Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ) - 1)
        (Work.Analysis.IonescuWainger.periodize
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)))
    (hΦ₂ : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, Work.Analysis.IonescuWainger.SupportedInArc
        (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)) - 1)
        (Work.Analysis.IonescuWainger.periodize
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)))
    (x : ℤ) :
    Work.KMTPlan.A6.mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp (Work.KMTPlan.A6.maeKmod ρ P a l₁ l₂ k₁ k₂ n) f g x := by
  classical
  have h12 : (1/2 : ℝ) ≤ 1 := by norm_num
  have hu1 : 1 ≤ Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) := one_le_uScale ρ hρ _
  have hdu : (1 : ℤ) ≤ (P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ) := by
    have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
      have h : (1 : ℕ) ≤ P.natDegree := le_trans (by norm_num) hd
      exact_mod_cast h
    have hu0 : (0 : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ) := by positivity
    nlinarith
  have hcU : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ))) ≤ 1 / 2 := by
    have hle : (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ))) ≤ (-1 : ℤ) := by nlinarith
    calc (2 : ℝ) ^ (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
        ≤ (2 : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ (a := (2:ℝ)) (by norm_num) hle
      _ = 1 / 2 := by norm_num
  have hnA₂' : Work.Analysis.IonescuWainger.NonAliasing
      (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) := by
    have hle : (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ))) ≤ -(Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ) := by nlinarith
    exact NonAliasing.mono hle (fun y hy => hy) hnA₂
  have hKsum : Summable (fun p : ℤ × ℤ => ‖maeTwKernel ρ P l₁ l₂
      (mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) (mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) p.1 p.2‖) := by
    have h₁ : Summable (fun j : ℤ => ‖cw (mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖) := by
      obtain ⟨C, _hC, hdec⟩ := cw_etaCut_decay (-(2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
      exact kernel_l1_of_decay (C := C) (fun j => by simpa only [mStarF] using hdec j)
    have h₂ : Summable (fun j : ℤ => ‖cw (mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) j‖) := by
      obtain ⟨C, _hC, hdec⟩ := cw_etaCut_decay (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
      exact kernel_l1_of_decay (C := C) (fun j => by simpa only [mStargF] using hdec j)
    exact vpc_summable_arithKernel_cw ρ P l₁ l₂ h₁ h₂
  obtain ⟨B₁, hB₁0, hB₁⟩ := uniform_tmKer_varphiNt ρ l₁ (Nat.floor (a n)) k₁
  obtain ⟨B₂, hB₂0, hB₂⟩ := uniform_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂
  have hκ : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      Summable (fun j : ℤ => ‖maeKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) j‖) := by
    intro t ht
    simpa only [maeKer, tmKer] using (hB₁ t (Set.Ioc_subset_Icc_self ht)).1
  have hκb : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      (∑' j : ℤ, ‖maeKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) j‖) ≤ B₁ := by
    intro t ht
    simpa only [maeKer, tmKer] using (hB₁ t (Set.Ioc_subset_Icc_self ht)).2
  have hκ' : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      Summable (fun j : ℤ => ‖maeKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) j‖) := by
    intro t ht
    simpa only [maeKer, tmKer] using (hB₂ t (Set.Ioc_subset_Icc_self ht)).1
  have hκb' : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      (∑' j : ℤ, ‖maeKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) j‖) ≤ B₂ := by
    intro t ht
    simpa only [maeKer, tmKer] using (hB₂ t (Set.Ioc_subset_Icc_self ht)).2
  have hm₁ : ∀ j : ℤ, Measurable (fun t : ℝ => maeKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) j) := by
    intro j; simpa only [maeKer, tmKer] using measurable_tmKer_varphiNt ρ l₁ (Nat.floor (a n)) k₁ j
  have hm₂ : ∀ j : ℤ, Measurable
      (fun t : ℝ => maeKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) j) := by
    intro j; simpa only [maeKer, tmKer] using measurable_tmKer_varphitildeNt ρ P l₂ (Nat.floor (a n)) k₂ j
  have hpt : ∀ t ∈ Set.uIcc (1/2 : ℝ) 1,
      Btwist ρ P l₁ l₂ (mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) (mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (Tle ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f))
        (Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x
      = bilinOp (maeTwKernel ρ P l₁ l₂ (mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) (mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))))
          (convOp (maeKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t)) f)
          (convOp (maeKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) g) x := by
    intro t ht
    rw [Set.uIcc_of_le h12] at ht
    have hG : mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g
        = piExact (kmtPj ρ) l₂ (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ))) g := rfl
    have hφmem : MemLp (periodize (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) ⊤ circleMeasure :=
      memLp_periodize_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) k₂ t
    have hGfun : Tle ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
          (piExact (kmtPj ρ) l₂ (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ))) g)
        = convOp (maeKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) g :=
      Tle_piExact_eq_convOp ρ hρ hρ1 l₂ (-((P.natDegree : ℤ) * (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
        (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) hcU hg hnA₂' hφmem (hΦ₂ t ht)
    rw [mae_Tle_mdlF_eq_convOp ρ hρ hρ1 (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ (Nat.floor (a n)) k₁ hu1 t hf hnA₁ (hΦ₁ t ht),
      hG, hGfun, Btwist_eq_bilinOp_maeTwKernel]
  simp only [mdlPart]
  rw [if_pos hcore]
  rw [intervalIntegral.integral_congr hpt]
  rw [integral_bilinOp_convOp_comm_memLp_aux
      (K := maeTwKernel ρ P l₁ l₂ (mStarF (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) (mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))))
      (κ := fun t => maeKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t))
      (κ' := fun t => maeKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t))
      f g B₁ B₂ x hKsum hκ hκ' hκb hκb' hf hg hB₁0 hB₂0 hm₁ hm₂]
  rfl

end

end Work.KMTPlan.A6
