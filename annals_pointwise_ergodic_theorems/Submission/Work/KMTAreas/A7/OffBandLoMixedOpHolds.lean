/-
# The crude `ℓ^p` bound for the §6 model operator `loMixedOp` of the mixed range (Area A7)

`Work.KMTAreas.A7.loMixedOp ρ P N l₂ k₁ k₂ f g` is the `t`-average
`∫_{1/2}^1 smallBtwist ρ P 0 l₂ (mStarF u) (mStargF P.natDegree u)
  (Tm ρ 0 (varphiNt N k₁ t) f) (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) dt`,
`u = loMixedU ρ P.natDegree l₂ k₁ k₂`.  This module proves

  `‖loMixedOp ρ P N l₂ k₁ k₂ f g‖_{ℓ^{(p₁⁻¹+p₂⁻¹)⁻¹}} ≤ C ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`

with a constant `C` depending only on `(P, p₁, p₂, ρ, B)`, uniformly over `l₂,k₁,k₂ ≤ B`,
`1 ≤ N ≤ 2^B`, and for **all** `f, g : ℤ → ℂ` (no `MemLp`/boundedness hypothesis).  This is the
crude companion of `Work.KMTAreas.A7.OffBandVarpPieceLp` and a piece of
`Work.KMTAreas.A7.LoMixedOffBandHolds`.

## Route

* `Tm ρ l F h = iwConv (diffFreqs ρ l) (periodize F) h` is the convolution with the kernel
  `κ_j = iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize F)) j`, whose `ℓ¹` mass is bounded by
  `(4 · (#diffFreqs ρ l · S) + 1) · ∑' ‖kmtKernWeight‖` whenever `∫‖F‖ ≤ S` and `∫‖F''‖ ≤ S`
  (`iwKernel_decay_of_bump`).  Young's inequality for convolution (`offYoung_conv_count_le`) then
  gives the `ℓ^p` bound `eLpNorm_Tm_le_of_bump_data`.
* The bump data for `varphiNt N k t` and `varphitildeNt P d N k t` are uniform in `t ∈ [1/2,1]`
  (`varphiNt_bounds`, `Work.KMTPlan.A6.varphitildeNt_bounds`); taking the supremum over the finite
  rectangle `N ≤ 2^B`, `k ≤ B` gives the uniform constants of the two families.
* `smallBtwist ρ P 0 l₂ m₁ m₂ = bilinOp (smallArithKernel … · cw m₁ · cw m₂)`, and
  `BilinOpLp` bounds `bilinOp` by the `ℓ¹(ℤ²)` mass of its kernel; that mass is
  `≤ #(diffFreqs ρ 0) · #(diffFreqs ρ l₂) · (∑'‖cw m₁‖) · (∑'‖cw m₂‖)`
  (`norm_smallArithKernel_le`), and the two `cw`-masses are bounded uniformly in the window
  (`vpc_exists_cw_mStarF_tsum_le`, `exists_cw_mStargF_tsum_le`).
* Finally `eLpNorm_lintegral_le` moves the `eLpNorm` outside the `t`-integral.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedDefs
import Submission.Work.KMTAreas.A7.SmallJointDefs
import Submission.Work.KMTAreas.A7.bump_Tm_bounded
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt
import Submission.Work.KMTAreas.A7.eLpNorm_lintegral_le
import Submission.Work.A7.exists_cw_mStargF_tsum_le
import Submission.Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
import Submission.Work.KMTAreas.A4.offYoung
import Submission.Work.KMTAreas.A7.FibrePlumbing
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## 1. The `ℓ¹` mass of the `Tm` kernel from bump data -/

/-- The total mass of the comparison weight `kmtKernWeight`. -/
noncomputable def kmtTotalMass : ℝ := ∑' j : ℤ, ‖kmtKernWeight j‖

theorem kmtTotalMass_nonneg : 0 ≤ kmtTotalMass := tsum_nonneg (fun j => norm_nonneg _)

theorem kmtTotalMass_ne_zero : kmtTotalMass ≠ 0 := by
  have h : (0 : ℝ) < ‖kmtKernWeight 0‖ := by
    rw [norm_kmtKernWeight]
    norm_num
  exact ne_of_gt (lt_of_lt_of_le h (Summable.le_tsum summable_kmtKernWeight 0
    (fun j _ => norm_nonneg _)))

/-- **The `ℓ¹` mass of the kernel of the exact-height multiplier `Tm ρ l F`.** -/
theorem tmMass_le_of_bump (ρ : ℝ) (l : ℕ) {F : ℝ → ℂ} {S : ℝ} (hS : 0 ≤ S)
    (hcd : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (h1 : (∫ y, ‖F y‖) ≤ S) (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S) :
    (∑' j : ℤ,
        ENNReal.ofReal ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize F)) j‖)
      ≤ ENNReal.ofReal ((4 * (((diffFreqs ρ l).card : ℝ) * S) + 1) * kmtTotalMass) := by
  have hC0 : (0 : ℝ) ≤ 4 * (((diffFreqs ρ l).card : ℝ) * S) + 1 := by positivity
  have hdec : ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize F)) j‖
        ≤ (4 * (((diffFreqs ρ l).card : ℝ) * S) + 1) * ‖kmtKernWeight j‖ :=
    fun j => iwKernel_decay_of_bump (diffFreqs ρ l) hcd hcs hS h1 h2 j
  calc (∑' j : ℤ, ENNReal.ofReal ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize F)) j‖)
      ≤ ∑' j : ℤ, ENNReal.ofReal
          ((4 * (((diffFreqs ρ l).card : ℝ) * S) + 1) * ‖kmtKernWeight j‖) :=
        ENNReal.tsum_le_tsum (fun j => ENNReal.ofReal_le_ofReal (hdec j))
    _ = ∑' j : ℤ, ENNReal.ofReal (4 * (((diffFreqs ρ l).card : ℝ) * S) + 1)
          * ENNReal.ofReal ‖kmtKernWeight j‖ := by
        refine tsum_congr (fun j => ?_)
        rw [ENNReal.ofReal_mul hC0]
    _ = ENNReal.ofReal (4 * (((diffFreqs ρ l).card : ℝ) * S) + 1)
          * ∑' j : ℤ, ENNReal.ofReal ‖kmtKernWeight j‖ := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (4 * (((diffFreqs ρ l).card : ℝ) * S) + 1)
          * ENNReal.ofReal kmtTotalMass := by
        rw [kmtTotalMass,
          ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) summable_kmtKernWeight]
    _ = ENNReal.ofReal ((4 * (((diffFreqs ρ l).card : ℝ) * S) + 1) * kmtTotalMass) :=
        (ENNReal.ofReal_mul hC0).symm

/-- **The `ℓ^p` bound for the exact-height multiplier `Tm ρ l F` from bump data.** -/
theorem eLpNorm_Tm_le_of_bump_data (ρ : ℝ) (l : ℕ) {F : ℝ → ℂ} {S : ℝ} (hS : 0 ≤ S)
    (hcd : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (h1 : (∫ y, ‖F y‖) ≤ S) (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S)
    {p : ℝ} (hp : 1 ≤ p) (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => Tm ρ l F f x) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal ((4 * (((diffFreqs ρ l).card : ℝ) * S) + 1) * kmtTotalMass)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) Measure.count := by
  have hTm : (fun x : ℤ => Tm ρ l F f x)
      = fun n : ℤ =>
          ∑' z : ℤ, iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize F)) z * f (n - z) := by
    funext n
    rw [Tm, iwConv_apply]
    simp only [smul_eq_mul]
  rw [hTm]
  refine (Work.KMTAreas.A4.offYoung_conv_count_le hp
    (fun z : ℤ => iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize F)) z) f).trans ?_
  exact mul_le_mul' (tmMass_le_of_bump ρ l hS hcd hcs h1 h2) le_rfl

/-- `eLpNorm` of the `enorm`-valued function is bounded by the `eLpNorm` of the function. -/
theorem eLpNorm_enorm_le {q : ENNReal} {F : ℤ → ℂ} {X : ENNReal}
    (h : MeasureTheory.eLpNorm F q Measure.count ≤ X) :
    MeasureTheory.eLpNorm (fun x : ℤ => ‖F x‖ₑ) q Measure.count ≤ X :=
  (eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ => ‖F x‖ₑ) (g := F) (fun x => le_of_eq (enorm_eq_self _))).trans h

/-! ## 2. The kernel of `smallBtwist` and its `ℓ¹(ℤ²)` mass -/

/-- The kernel of the twisted bilinear multiplier `smallBtwist ρ P 0 l₂ m₁ m₂`. -/
noncomputable def smallBtwistK (ρ : ℝ) (P : Polynomial ℤ) (l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) :
    ℤ → ℤ → ℂ :=
  fun a b => smallArithKernel ρ P (arithQ ρ (max 0 l₂)) 0 l₂ a b * cw m₁ a * cw m₂ b

/-- **The `ℓ¹(ℤ²)` mass of the `smallBtwist` kernel.** -/
theorem smallBtwistK_mass_le (ρ : ℝ) (P : Polynomial ℤ) (l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (h₁ : Summable (fun j : ℤ => ‖cw m₁ j‖)) (h₂ : Summable (fun j : ℤ => ‖cw m₂ j‖))
    (hC₁ : (∑' j : ℤ, ‖cw m₁ j‖) ≤ C₁) (hC₂ : (∑' j : ℤ, ‖cw m₂ j‖) ≤ C₂) :
    Summable (fun q : ℤ × ℤ => ‖smallBtwistK ρ P l₂ m₁ m₂ q.1 q.2‖) ∧
      (∑' q : ℤ × ℤ, ‖smallBtwistK ρ P l₂ m₁ m₂ q.1 q.2‖)
        ≤ ((diffFreqs ρ 0).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) * C₁ * C₂ := by
  set cc : ℝ := ((diffFreqs ρ 0).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) with hcc
  have hcc0 : 0 ≤ cc := by rw [hcc]; positivity
  have hpt : ∀ a b : ℤ, ‖smallBtwistK ρ P l₂ m₁ m₂ a b‖ ≤ cc * ‖cw m₁ a‖ * ‖cw m₂ b‖ := by
    intro a b
    have h1' := norm_smallArithKernel_le ρ P (arithQ ρ (max 0 l₂)) 0 l₂ a b
    rw [smallBtwistK, norm_mul, norm_mul, hcc]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h1' (norm_nonneg _)) (norm_nonneg _)
  have hfinite : ∀ u : Finset (ℤ × ℤ),
      ∑ q ∈ u, ‖smallBtwistK ρ P l₂ m₁ m₂ q.1 q.2‖ ≤ cc * C₁ * C₂ := by
    intro u
    set U₁ : Finset ℤ := u.image Prod.fst with hU₁
    set U₂ : Finset ℤ := u.image Prod.snd with hU₂
    set X₁ : ℝ := ∑ a ∈ U₁, ‖cw m₁ a‖ with hX₁
    set X₂ : ℝ := ∑ b ∈ U₂, ‖cw m₂ b‖ with hX₂
    have hX₁0 : 0 ≤ X₁ := by rw [hX₁]; exact Finset.sum_nonneg (fun a _ => norm_nonneg _)
    have hX₂0 : 0 ≤ X₂ := by rw [hX₂]; exact Finset.sum_nonneg (fun b _ => norm_nonneg _)
    have hle1 : X₁ ≤ C₁ := by rw [hX₁]; exact (h₁.sum_le_tsum U₁ (fun i _ => norm_nonneg _)).trans hC₁
    have hle2 : X₂ ≤ C₂ := by rw [hX₂]; exact (h₂.sum_le_tsum U₂ (fun i _ => norm_nonneg _)).trans hC₂
    have hsub : u ⊆ U₁ ×ˢ U₂ := by
      intro q hq
      rw [Finset.mem_product]
      exact ⟨Finset.mem_image.mpr ⟨q, hq, rfl⟩, Finset.mem_image.mpr ⟨q, hq, rfl⟩⟩
    have hident : ∑ q ∈ U₁ ×ˢ U₂, cc * ‖cw m₁ q.1‖ * ‖cw m₂ q.2‖ = cc * X₁ * X₂ := by
      rw [Finset.sum_product]
      have hinner : ∀ a : ℤ, (∑ b ∈ U₂, cc * ‖cw m₁ a‖ * ‖cw m₂ b‖) = (cc * ‖cw m₁ a‖) * X₂ := by
        intro a
        rw [hX₂, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun a _ => hinner a)]
      rw [← Finset.sum_mul, hX₁, ← Finset.mul_sum]
    calc ∑ q ∈ u, ‖smallBtwistK ρ P l₂ m₁ m₂ q.1 q.2‖
        ≤ ∑ q ∈ u, cc * ‖cw m₁ q.1‖ * ‖cw m₂ q.2‖ :=
          Finset.sum_le_sum (fun q _ => hpt q.1 q.2)
      _ ≤ ∑ q ∈ U₁ ×ˢ U₂, cc * ‖cw m₁ q.1‖ * ‖cw m₂ q.2‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
      _ = cc * X₁ * X₂ := hident
      _ ≤ cc * C₁ * C₂ := by
          have hkey : X₁ * X₂ ≤ C₁ * C₂ := mul_le_mul hle1 hle2 hX₂0 hC₁0
          have h1 : cc * (X₁ * X₂) ≤ cc * (C₁ * C₂) :=
            mul_le_mul_of_nonneg_left hkey hcc0
          have h2 : cc * X₁ * X₂ = cc * (X₁ * X₂) := by ring
          have h3 : cc * C₁ * C₂ = cc * (C₁ * C₂) := by ring
          rw [h2, h3]
          exact h1
  have hnn : ∀ q : ℤ × ℤ, 0 ≤ ‖smallBtwistK ρ P l₂ m₁ m₂ q.1 q.2‖ := fun q => norm_nonneg _
  exact ⟨summable_of_sum_le hnn hfinite, Real.tsum_le_of_sum_le hnn hfinite⟩

/-- **The `ℓ^p` bound for `smallBtwist` at `l₁ = 0`.** -/
theorem eLpNorm_smallBtwist_le (ρ : ℝ) (P : Polynomial ℤ) (l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (p₁ p₂ q : ENNReal) (hp : p₁⁻¹ + p₂⁻¹ = q⁻¹) (hq : 1 ≤ q) (M : ℝ)
    (hsum : Summable (fun x : ℤ × ℤ => ‖smallBtwistK ρ P l₂ m₁ m₂ x.1 x.2‖))
    (hM : (∑' x : ℤ × ℤ, ‖smallBtwistK ρ P l₂ m₁ m₂ x.1 x.2‖) ≤ M) (h k : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => smallBtwist ρ P 0 l₂ m₁ m₂ h k x) q Measure.count
      ≤ ENNReal.ofReal M * (MeasureTheory.eLpNorm h p₁ Measure.count
          * MeasureTheory.eLpNorm k p₂ Measure.count) := by
  rw [smallBtwist_eq_bilinOp]
  refine (BilinOpLp (K := smallBtwistK ρ P l₂ m₁ m₂) (p := q) hp hq hsum h k).trans ?_
  rw [mul_assoc]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hM) le_rfl

/-! ## 3. Uniform bump data on the finite parameter rectangle -/

/-- The finite rectangle `N ≤ 2^B`, `k ≤ B` of parameters. -/
def rectParam (B : ℕ) : Finset (ℕ × ℕ) := (Finset.range (2 ^ B + 1)) ×ˢ (Finset.range (B + 1))

theorem rectParam_nonempty (B : ℕ) : (rectParam B).Nonempty :=
  ⟨(0, 0), by simp [rectParam]⟩

theorem mem_rectParam {B N k : ℕ} (hN : N ≤ 2 ^ B) (hk : k ≤ B) : (N, k) ∈ rectParam B := by
  simp only [rectParam, Finset.mem_product, Finset.mem_range]
  omega

/-- The `f`-side bump constant, from `varphiNt_bounds`. -/
noncomputable def phiS (N k : ℕ) : ℝ :=
  Classical.choose (Classical.choose_spec (varphiNt_bounds N k))

theorem phiS_nonneg (N k : ℕ) : 0 ≤ phiS N k :=
  (Classical.choose_spec (Classical.choose_spec (varphiNt_bounds N k))).1

theorem phiS_data (N k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    ContDiff ℝ 2 (fun ξ => varphiNt N k t ξ) ∧
      HasCompactSupport (fun ξ => varphiNt N k t ξ) ∧
      (∫ y, ‖varphiNt N k t y‖) ≤ phiS N k ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) ≤ phiS N k := by
  have h := (Classical.choose_spec (Classical.choose_spec (varphiNt_bounds N k))).2 t ht
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The `g`-side bump constant, from `Work.KMTPlan.A6.varphitildeNt_bounds`. -/
noncomputable def psiS (P : Polynomial ℤ) (N k : ℕ) : ℝ :=
  Classical.choose (Work.KMTPlan.A6.varphitildeNt_bounds P P.natDegree N k)

theorem psiS_nonneg (P : Polynomial ℤ) (N k : ℕ) : 0 ≤ psiS P N k :=
  (Classical.choose_spec (Work.KMTPlan.A6.varphitildeNt_bounds P P.natDegree N k)).1

theorem psiS_data (P : Polynomial ℤ) (N k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    ContDiff ℝ 2 (fun ξ => varphitildeNt P P.natDegree N k t ξ) ∧
      HasCompactSupport (fun ξ => varphitildeNt P P.natDegree N k t ξ) ∧
      (∫ y, ‖varphitildeNt P P.natDegree N k t y‖) ≤ psiS P N k ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNt P P.natDegree N k t ξ) y‖) ≤ psiS P N k :=
  (Classical.choose_spec (Work.KMTPlan.A6.varphitildeNt_bounds P P.natDegree N k)).2 t ht

/-- The supremum of the `f`-side bump constants over the rectangle. -/
noncomputable def supPhi (B : ℕ) : ℝ :=
  (rectParam B).sup' (rectParam_nonempty B) (fun p => phiS p.1 p.2)

/-- The supremum of the `g`-side bump constants over the rectangle. -/
noncomputable def supPsi (P : Polynomial ℤ) (B : ℕ) : ℝ :=
  (rectParam B).sup' (rectParam_nonempty B) (fun p => psiS P p.1 p.2)

theorem phiS_le_supPhi (B N k : ℕ) (hN : N ≤ 2 ^ B) (hk : k ≤ B) : phiS N k ≤ supPhi B := by
  rw [supPhi]
  exact Finset.le_sup' (fun p : ℕ × ℕ => phiS p.1 p.2) (mem_rectParam hN hk)

theorem psiS_le_supPsi (P : Polynomial ℤ) (B N k : ℕ) (hN : N ≤ 2 ^ B) (hk : k ≤ B) :
    psiS P N k ≤ supPsi P B := by
  rw [supPsi]
  exact Finset.le_sup' (fun p : ℕ × ℕ => psiS P p.1 p.2) (mem_rectParam hN hk)

theorem supPhi_nonneg (B : ℕ) : 0 ≤ supPhi B :=
  (phiS_nonneg 0 0).trans (phiS_le_supPhi B 0 0 (by positivity) (Nat.zero_le _))

theorem supPsi_nonneg (P : Polynomial ℤ) (B : ℕ) : 0 ≤ supPsi P B :=
  (psiS_nonneg P 0 0).trans (psiS_le_supPsi P B 0 0 (by positivity) (Nat.zero_le _))

/-! ## 4. The uniform `cw`-mass constants -/

/-- The uniform mass constant of `cw (mStarF u)`. -/
noncomputable def mStarMass : ℝ := Classical.choose Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le

theorem mStarMass_pos : 0 < mStarMass :=
  (Classical.choose_spec Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le).1

theorem cw_mStarF_tsum_le (u : ℕ) : (∑' j : ℤ, ‖cw (mStarF u) j‖) ≤ mStarMass :=
  ((Classical.choose_spec Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le).2 u).2

/-- The uniform mass constant of `cw (mStargF d u)`. -/
noncomputable def mStargMass (d : ℕ) (hd : 1 ≤ d) : ℝ :=
  Classical.choose (Work.A7.exists_cw_mStargF_tsum_le d hd)

theorem mStargMass_pos (d : ℕ) (hd : 1 ≤ d) : 0 < mStargMass d hd :=
  (Classical.choose_spec (Work.A7.exists_cw_mStargF_tsum_le d hd)).1

theorem cw_mStargF_tsum_le (d : ℕ) (hd : 1 ≤ d) (u : ℕ) :
    (∑' j : ℤ, ‖cw (mStargF d u) j‖) ≤ mStargMass d hd :=
  (Classical.choose_spec (Work.A7.exists_cw_mStargF_tsum_le d hd)).2 u



/-! ## 5. The target -/

theorem OffBandLoMixedOpHolds (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (p₁ p₂ : ENNReal) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₂ k₁ k₂ N : ℕ) (f g : ℤ → ℂ),
      l₂ ≤ B → k₁ ≤ B → k₂ ≤ B → 1 ≤ N → N ≤ 2 ^ B →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.loMixedOp ρ P N l₂ k₁ k₂ f g)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
  classical
  have hd1 : 1 ≤ P.natDegree := by omega
  obtain ⟨Cmf, hCmfpos, hCmf⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  obtain ⟨Cmg, hCmgpos, hCmg⟩ := Work.A7.exists_cw_mStargF_tsum_le P.natDegree hd1
  set q : ENNReal := (p₁⁻¹ + p₂⁻¹)⁻¹ with hqdef
  have hq : 1 ≤ q := ENNReal.one_le_inv.mpr hsum
  have hCmf0 : (0 : ℝ) ≤ Cmf := hCmfpos.le
  have hCmg0 : (0 : ℝ) ≤ Cmg := hCmgpos.le
  set Card0 : ℝ := ((diffFreqs ρ 0).card : ℝ) with hCard0
  set CardB : ℝ := ((iwArithFreqs ρ B).card : ℝ) with hCardB
  have hCard00 : (0 : ℝ) ≤ Card0 := by rw [hCard0]; positivity
  have hCardB0 : (0 : ℝ) ≤ CardB := by rw [hCardB]; positivity
  have hkmt0 : 0 ≤ kmtTotalMass := kmtTotalMass_nonneg
  set Af : ℝ := (4 * (Card0 * supPhi B) + 1) * kmtTotalMass with hAf
  set Ag : ℝ := (4 * (CardB * supPsi P B) + 1) * kmtTotalMass with hAg
  set Cm : ℝ := Card0 * CardB * Cmf * Cmg with hCm
  set BIG : ℝ := Cm * Af * Ag with hBIG
  have hAfpos : 0 < Af := by
    rw [hAf]
    have h1 : (0 : ℝ) ≤ Card0 * supPhi B := mul_nonneg hCard00 (supPhi_nonneg B)
    have h2 : 0 < 4 * (Card0 * supPhi B) + 1 := by linarith
    exact mul_pos h2 (lt_of_le_of_ne hkmt0 (Ne.symm kmtTotalMass_ne_zero))
  have hAgpos : 0 < Ag := by
    rw [hAg]
    have h1 : (0 : ℝ) ≤ CardB * supPsi P B := mul_nonneg hCardB0 (supPsi_nonneg P B)
    have h2 : 0 < 4 * (CardB * supPsi P B) + 1 := by linarith
    exact mul_pos h2 (lt_of_le_of_ne hkmt0 (Ne.symm kmtTotalMass_ne_zero))
  have hCm0 : 0 ≤ Cm := by
    rw [hCm]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCard00 hCardB0) hCmf0) hCmg0
  refine ⟨max 1 BIG, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro l₂ k₁ k₂ N f g hl₂ hk₁ hk₂ hN1 hNB
  have hcardl : ((diffFreqs ρ l₂).card : ℝ) ≤ CardB := by
    have h1 : diffFreqs ρ l₂ ⊆ iwArithFreqs ρ l₂ := by
      rw [diffFreqs]
      split_ifs with h
      · subst h; exact subset_rfl
      · exact Finset.sdiff_subset
    have h2 : iwArithFreqs ρ l₂ ⊆ iwArithFreqs ρ B := iwArithFreqs_mono hρ hρ1 hl₂
    rw [hCardB]
    exact_mod_cast Finset.card_le_card (h1.trans h2)
  set E : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
      * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hE
  have hper : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          ‖smallBtwist ρ P 0 l₂ (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
            (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
            (Tm ρ 0 (varphiNt N k₁ t) f) (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x‖ₑ)
        q MeasureTheory.Measure.count ≤ ENNReal.ofReal BIG * E := by
    intro t htIoc
    have ht : t ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_of_lt htIoc.1, htIoc.2⟩
    have hp1R : (1 : ℝ) ≤ p₁.toReal := by
      have h := ENNReal.toReal_mono (ne_of_lt htp₁) hp₁.le
      simpa using h
    have hp2R : (1 : ℝ) ≤ p₂.toReal := by
      have h := ENNReal.toReal_mono (ne_of_lt htp₂) hp₂.le
      simpa using h
    set Tf : ℝ := (4 * (((diffFreqs ρ 0).card : ℝ) * phiS N k₁) + 1) * kmtTotalMass with hTf
    set Tg : ℝ := (4 * (((diffFreqs ρ l₂).card : ℝ) * psiS P N k₂) + 1) * kmtTotalMass with hTg
    have hTf0 : 0 ≤ Tf := by
      rw [hTf]
      have h1 : (0 : ℝ) ≤ 4 * (((diffFreqs ρ 0).card : ℝ) * phiS N k₁) + 1 := by
        have := phiS_nonneg N k₁; positivity
      exact mul_nonneg h1 hkmt0
    have hTg0 : 0 ≤ Tg := by
      rw [hTg]
      have h1 : (0 : ℝ) ≤ 4 * (((diffFreqs ρ l₂).card : ℝ) * psiS P N k₂) + 1 := by
        have := psiS_nonneg P N k₂; positivity
      exact mul_nonneg h1 hkmt0
    have hTm₁ : MeasureTheory.eLpNorm (Tm ρ 0 (varphiNt N k₁ t) f) p₁ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Tf * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
      have hmain := eLpNorm_Tm_le_of_bump_data (ρ := ρ) (l := 0)
        (F := fun ξ => varphiNt N k₁ t ξ) (S := phiS N k₁) (phiS_nonneg N k₁)
        (phiS_data N k₁ ht).1 (phiS_data N k₁ ht).2.1 (phiS_data N k₁ ht).2.2.1
        (phiS_data N k₁ ht).2.2.2 (p := p₁.toReal) hp1R f
      rw [hTf]
      rwa [ENNReal.ofReal_toReal (ne_of_lt htp₁)] at hmain
    have hTm₂ : MeasureTheory.eLpNorm
          (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) p₂ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Tg * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
      have hmain := eLpNorm_Tm_le_of_bump_data (ρ := ρ) (l := l₂)
        (F := fun ξ => varphitildeNt P P.natDegree N k₂ t ξ) (S := psiS P N k₂)
        (psiS_nonneg P N k₂) (psiS_data P N k₂ ht).1 (psiS_data P N k₂ ht).2.1
        (psiS_data P N k₂ ht).2.2.1 (psiS_data P N k₂ ht).2.2.2 (p := p₂.toReal) hp2R g
      rw [hTg]
      rwa [ENNReal.ofReal_toReal (ne_of_lt htp₂)] at hmain
    have hmass := smallBtwistK_mass_le (ρ := ρ) (P := P) (l₂ := l₂)
      (m₁ := mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
      (m₂ := mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
      (hC₁0 := hCmf0) (hC₂0 := hCmg0)
      (h₁ := summable_norm_cw_mStarF _) (h₂ := summable_norm_cw_mStargF P _)
      (hC₁ := (hCmf _).2) (hC₂ := hCmg _)
    have hMmass : (∑' x : ℤ × ℤ, ‖smallBtwistK ρ P l₂
          (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
          (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)) x.1 x.2‖) ≤ Cm := by
      rw [hCm]
      have h1 : ((diffFreqs ρ 0).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
          ≤ ((diffFreqs ρ 0).card : ℝ) * ((iwArithFreqs ρ B).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcardl (by positivity)
      have h2 : ((diffFreqs ρ 0).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) * Cmf
          ≤ ((diffFreqs ρ 0).card : ℝ) * ((iwArithFreqs ρ B).card : ℝ) * Cmf :=
        mul_le_mul_of_nonneg_right h1 hCmf0
      exact hmass.2.trans (mul_le_mul_of_nonneg_right h2 hCmg0)
    have hbilin : MeasureTheory.eLpNorm (fun x : ℤ =>
          smallBtwist ρ P 0 l₂ (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
            (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
            (Tm ρ 0 (varphiNt N k₁ t) f) (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x)
        q MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Cm * (ENNReal.ofReal Tf * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
            * (ENNReal.ofReal Tg
              * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)) := by
      refine (eLpNorm_smallBtwist_le (ρ := ρ) (P := P) (l₂ := l₂)
        (m₁ := mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
        (m₂ := mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
        p₁ p₂ q ?_ hq (∑' x : ℤ × ℤ, ‖smallBtwistK ρ P l₂
            (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
            (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)) x.1 x.2‖) ?_ le_rfl
        (Tm ρ 0 (varphiNt N k₁ t) f) (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g)).trans
        (mul_le_mul' (ENNReal.ofReal_le_ofReal hMmass) (mul_le_mul' hTm₁ hTm₂))
      · rw [hqdef, inv_inv]
      · exact hmass.1
    have hTfle : Tf ≤ Af := by
      rw [hTf, hAf, hCard0]
      have h1 : phiS N k₁ ≤ supPhi B := phiS_le_supPhi B N k₁ hNB hk₁
      have h2 : ((diffFreqs ρ 0).card : ℝ) * phiS N k₁
          ≤ ((diffFreqs ρ 0).card : ℝ) * supPhi B :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h3 : 4 * (((diffFreqs ρ 0).card : ℝ) * phiS N k₁) + 1
          ≤ 4 * (((diffFreqs ρ 0).card : ℝ) * supPhi B) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right h3 hkmt0
    have hTgle : Tg ≤ Ag := by
      have hc : ((diffFreqs ρ l₂).card : ℝ) * psiS P N k₂ ≤ CardB * supPsi P B := by
        rw [hCardB]
        have h1 : psiS P N k₂ ≤ supPsi P B := psiS_le_supPsi P B N k₂ hNB hk₂
        have h2 : ((diffFreqs ρ l₂).card : ℝ) * psiS P N k₂
            ≤ ((diffFreqs ρ l₂).card : ℝ) * supPsi P B :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        exact h2.trans (mul_le_mul_of_nonneg_right hcardl (supPsi_nonneg P B))
      rw [hTg, hAg]
      have h3 : 4 * (((diffFreqs ρ l₂).card : ℝ) * psiS P N k₂) + 1
          ≤ 4 * (CardB * supPsi P B) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right h3 hkmt0
    have hnum : Cm * Tf * Tg ≤ BIG := by
      rw [hBIG]
      have hCmAf0 : 0 ≤ Cm * Af := mul_nonneg hCm0 hAfpos.le
      have h1 : Cm * Tf ≤ Cm * Af := mul_le_mul_of_nonneg_left hTfle hCm0
      exact mul_le_mul h1 hTgle hTg0 hCmAf0
    have hEq : ENNReal.ofReal Cm * (ENNReal.ofReal Tf
          * MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count
          * (ENNReal.ofReal Tg * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count))
        = ENNReal.ofReal (Cm * Tf * Tg) * E := by
      rw [hE]
      rw [show ENNReal.ofReal (Cm * Tf * Tg)
            = ENNReal.ofReal Cm * ENNReal.ofReal Tf * ENNReal.ofReal Tg from by
        rw [ENNReal.ofReal_mul (mul_nonneg hCm0 hTf0), ENNReal.ofReal_mul hCm0]]
      ring
    have hrest : ENNReal.ofReal (Cm * Tf * Tg) * E ≤ ENNReal.ofReal BIG * E :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hnum) le_rfl
    rw [eLpNorm_enorm (hf := AEStronglyMeasurable.of_discrete)]
    exact hbilin.trans (hEq.le.trans hrest)
  have hInt : MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
        ‖smallBtwist ρ P 0 l₂ (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
          (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
          (Tm ρ 0 (varphiNt N k₁ t) f) (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x‖ₑ)
      q MeasureTheory.Measure.count ≤ ENNReal.ofReal BIG * E :=
    eLpNorm_lintegral_le q hq _ _ hper
  have hmono : ∀ x : ℤ, ‖loMixedOp ρ P N l₂ k₁ k₂ f g x‖ₑ
      ≤ ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
          ‖smallBtwist ρ P 0 l₂ (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂))
            (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂))
            (Tm ρ 0 (varphiNt N k₁ t) f) (Tm ρ l₂ (varphitildeNt P P.natDegree N k₂ t) g) x‖ₑ := by
    intro x
    rw [loMixedOp, intervalIntegral.integral_of_le (by norm_num : (1/2 : ℝ) ≤ 1)]
    exact enorm_integral_le_lintegral_enorm _
  have hlast : ENNReal.ofReal BIG * E ≤ ENNReal.ofReal (max 1 BIG) * E :=
    mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right 1 BIG)) le_rfl
  exact (eLpNorm_mono_enorm (hf := by pw_aesm) hmono).trans (hInt.trans hlast)

end

end Work.KMTAreas.A7
