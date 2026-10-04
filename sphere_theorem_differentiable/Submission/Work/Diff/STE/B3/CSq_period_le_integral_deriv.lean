import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `Hˢ` norm of a periodisation is bounded by the physical derivatives of the summand

For a smooth `φ : (ι → ℝ) → ℂ` supported in the open cube `(-1/2,1/2)^ι`, the periodisation
`P φ = ∑' m : ι → ℤ, φ (· + m)` is a smooth `1`-periodic function, and the weighted `ℓ²` norm of
its Fourier coefficients is bounded by the *physical* `L²` norms of the iterated partial
derivatives of `φ` (over all of `ℝ^ι`, where they are compactly supported):

`CSq s (fourierCoeff (P φ)) ≤ Cₛ * Σ_{m ≤ s} Σ_{l : Fin m → ι} ∫ ‖∂^l φ‖²`.

## Route

* `CSq_le_ENormSq` bounds `CSq s (fourierCoeff (P φ))` by `2 ^ s (ENormSq s (P φ) + ENormSq 0 (P φ))`.
* On the unit cube `∂^l (P φ)` is the sum of the `2 ^ card ι` translates `∂^l φ (· + n)`,
  `n ∈ csqp_boxIdx ι = {-1,0}^ι` (`csqp_periodization_eventuallyEq_sum_boxIdx` +
  `csqp_pdVec_congr` + `csqp_pdVec_finset_sum`), so
  `‖∂^l (P φ)‖² ≤ card ι * Σ_n ‖∂^l φ (· + n)‖²`
  (Cauchy–Schwarz for a finite sum).
* Integrating over the unit cube, substituting `y ↦ y + n` in each term
  (`fcp_setIntegral_comp_add`) and enlarging the domain to all of `ℝ^ι`
  (`setIntegral_le_integral`) gives
  `ENormSq m (P φ) ≤ (card ι)² * Σ_{l : Fin m → ι} ∫ ‖∂^l φ‖²`.
* The block `m = s` (respectively `m = 0`) is a sub-sum of the nonnegative sum over `m ∈ range (s+1)`.
-/

noncomputable section

namespace Work.Diff.STE.B3

open MeasureTheory BigOperators

set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Integrability of the derivatives of a cube-supported function -/

/-- The closed unit cube `[-1/2,1/2]^ι` is compact. -/
lemma steB3_isCompact_closedCube :
    IsCompact (Set.pi Set.univ (fun _ : ι => Set.Icc (-(1/2:ℝ)) (1/2))) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

/-- The squared norm of an iterated partial derivative of a smooth function supported in the open
unit cube is integrable on all of `ℝ^ι`: it is continuous and compactly supported. -/
lemma steB3_integrable_normSq_pdVec {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : Function.support φ ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (m : ℕ) (l : Fin m → ι) :
    Integrable (fun x : ι → ℝ => ‖pdVec m l φ x‖ ^ 2) volume := by
  have hcont : Continuous (fun x : ι → ℝ => ‖pdVec m l φ x‖ ^ 2) :=
    (((csqp_contDiff_pdList_top (List.ofFn l) hφ).continuous).norm.pow 2)
  refine hcont.integrable_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact steB3_isCompact_closedCube ?_)
  intro x hx
  have hne : pdVec m l φ x ≠ 0 := by
    intro h0
    exact hx (by show ‖pdVec m l φ x‖ ^ 2 = 0; rw [h0]; simp)
  exact csqp_support_pdVec_subset_closedCube hsupp m l hne

/-- Change of variables `y ↦ y + c` in a set integral of a real-valued function. -/
lemma steB3_setIntegral_comp_add_real (c : ι → ℝ) (s : Set (ι → ℝ)) (G : (ι → ℝ) → ℝ) :
    ∫ y in s, G (y + c) = ∫ z in (fun y : ι → ℝ => y + c) '' s, G z := by
  haveI : (MeasureSpace.volume : Measure (ι → ℝ)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi ι
  exact ((measurePreserving_add_right (MeasureSpace.volume : Measure (ι → ℝ)) c).setIntegral_image_emb
    (MeasurableEquiv.addRight c).measurableEmbedding G s).symm

/-! ## 2. The energy of the periodisation, estimated by the derivatives of `φ` -/

/-- On the unit cube the iterated partial derivative `∂^l` of the periodisation is the sum of the
`2 ^ card ι` translates of `∂^l φ`. -/
lemma steB3_pdVec_periodization_eq_sum {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : Function.support φ ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (m : ℕ) (l : Fin m → ι) :
    ∀ x ∈ unitCube (ι := ι),
      pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) x
        = ∑ n ∈ csqp_boxIdx ι, pdVec m l φ (x + iVec n) := by
  intro x hx
  have hev := csqp_periodization_eventuallyEq_sum_boxIdx hsupp hx
  have h1 : pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) x
      = pdVec m l (fun y : ι → ℝ => ∑ n ∈ csqp_boxIdx ι, φ (y + iVec n)) x :=
    csqp_pdVec_congr l hev
  rw [h1]
  rw [csqp_pdVec_finset_sum l (csqp_boxIdx ι) (fun n y => φ (y + iVec n)) x
    (fun n _ => hφ.comp (contDiff_id.add contDiff_const))]
  exact Finset.sum_congr rfl (fun n _ => csqp_pdVec_comp_add_right l φ (iVec n) x)

/-- The `Hᵐ` energy of the periodisation of a smooth cube-supported `φ` is bounded by the `L²`
norms of the `m`-th partial derivatives of `φ` over all of `ℝ^ι`. -/
lemma steB3_ENormSq_periodization_le_integral {φ : (ι → ℝ) → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : Function.support φ ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (m : ℕ) :
    ENormSq m (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n))
      ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2
          * ∑ l : Fin m → ι, ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 := by
  have hPcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) :=
    csqp_periodization_contDiff hφ hsupp
  have hterm : ∀ l : Fin m → ι,
      ∫ x in unitCube (ι := ι),
          ‖pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) x‖ ^ 2
        ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 * ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 := by
    intro l
    -- pointwise Cauchy-Schwarz on the finite sum over the box
    have hcontpd : Continuous (fun x : ι → ℝ => pdVec m l φ x) :=
      (csqp_contDiff_pdList_top (List.ofFn l) hφ).continuous
    have hpt : ∀ x ∈ unitCube (ι := ι),
        ‖pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) x‖ ^ 2
          ≤ ((csqp_boxIdx ι).card : ℝ)
              * ∑ n ∈ csqp_boxIdx ι, ‖pdVec m l φ (x + iVec n)‖ ^ 2 := by
      intro x hx
      rw [steB3_pdVec_periodization_eq_sum hφ hsupp m l x hx]
      calc ‖∑ n ∈ csqp_boxIdx ι, pdVec m l φ (x + iVec n)‖ ^ 2
          ≤ (∑ n ∈ csqp_boxIdx ι, ‖pdVec m l φ (x + iVec n)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ ((csqp_boxIdx ι).card : ℝ)
              * ∑ n ∈ csqp_boxIdx ι, ‖pdVec m l φ (x + iVec n)‖ ^ 2 :=
            sq_sum_le_card_mul_sum_sq
    have hcontR : Continuous (fun x : ι → ℝ =>
        ((csqp_boxIdx ι).card : ℝ) * ∑ n ∈ csqp_boxIdx ι, ‖pdVec m l φ (x + iVec n)‖ ^ 2) :=
      continuous_const.mul (continuous_finsetSum _
        (fun n _ => ((hcontpd.comp (continuous_id.add continuous_const)).norm.pow 2)))
    have hInt1 : IntegrableOn
        (fun x : ι → ℝ => ‖pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) x‖ ^ 2)
        (unitCube (ι := ι)) volume :=
      csqp_integrableOn_unitCube_of_continuous_real
        (((csqp_contDiff_pdList_top (List.ofFn l) hPcd).continuous).norm.pow 2)
    have hInt2 : IntegrableOn (fun x : ι → ℝ =>
        ((csqp_boxIdx ι).card : ℝ) * ∑ n ∈ csqp_boxIdx ι, ‖pdVec m l φ (x + iVec n)‖ ^ 2)
        (unitCube (ι := ι)) volume :=
      csqp_integrableOn_unitCube_of_continuous_real hcontR
    have hmono := setIntegral_mono_on hInt1 hInt2 BesselCont.measSet_unitCube hpt
    have hsplit : ∫ x in unitCube (ι := ι),
        ((csqp_boxIdx ι).card : ℝ) * ∑ n ∈ csqp_boxIdx ι, ‖pdVec m l φ (x + iVec n)‖ ^ 2
        = ((csqp_boxIdx ι).card : ℝ) * ∑ n ∈ csqp_boxIdx ι,
            ∫ x in unitCube (ι := ι), ‖pdVec m l φ (x + iVec n)‖ ^ 2 := by
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum]
      intro n _
      exact csqp_integrableOn_unitCube_of_continuous_real
        ((hcontpd.comp (continuous_id.add continuous_const)).norm.pow 2)
    have htr : ∀ n ∈ csqp_boxIdx ι,
        ∫ x in unitCube (ι := ι), ‖pdVec m l φ (x + iVec n)‖ ^ 2
          ≤ ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 := by
      intro n _
      rw [steB3_setIntegral_comp_add_real (iVec n) (unitCube (ι := ι))
        (fun z : ι → ℝ => ‖pdVec m l φ z‖ ^ 2)]
      exact setIntegral_le_integral (steB3_integrable_normSq_pdVec hφ hsupp m l)
        (Filter.Eventually.of_forall (fun x => by positivity))
    calc ∫ x in unitCube (ι := ι),
          ‖pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) x‖ ^ 2
        ≤ ∫ x in unitCube (ι := ι),
            ((csqp_boxIdx ι).card : ℝ)
              * ∑ n ∈ csqp_boxIdx ι, ‖pdVec m l φ (x + iVec n)‖ ^ 2 := hmono
      _ = ((csqp_boxIdx ι).card : ℝ) * ∑ n ∈ csqp_boxIdx ι,
            ∫ x in unitCube (ι := ι), ‖pdVec m l φ (x + iVec n)‖ ^ 2 := hsplit
      _ ≤ ((csqp_boxIdx ι).card : ℝ) * ∑ n ∈ csqp_boxIdx ι,
            ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum htr) (by positivity)
      _ = ((csqp_boxIdx ι).card : ℝ) * (((csqp_boxIdx ι).card : ℝ)
            * ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((csqp_boxIdx ι).card : ℝ) ^ 2 * ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 := by ring
  calc ENormSq m (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n))
      = ∑ l : Fin m → ι, ∫ x in unitCube (ι := ι),
          ‖pdVec m l (fun z : ι → ℝ => ∑' n : ι → ℤ, φ (z + iVec n)) x‖ ^ 2 := rfl
    _ ≤ ∑ l : Fin m → ι,
          ((csqp_boxIdx ι).card : ℝ) ^ 2 * ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 :=
        Finset.sum_le_sum (fun l _ => hterm l)
    _ = ((csqp_boxIdx ι).card : ℝ) ^ 2
          * ∑ l : Fin m → ι, ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 := by
        rw [Finset.mul_sum]

/-! ## 3. The target theorem -/

theorem CSq_period_le_integral_deriv {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : (ι → ℝ) → ℂ),
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ →
      (Function.support φ ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2))) →
      Work.Diff.STE.CSq s
          (Work.Diff.STE.fourierCoeff (fun z => ∑' m : ι → ℤ, φ (z + Work.Diff.STE.iVec m)))
        ≤ C * ∑ m ∈ Finset.range (s+1), ∑ l : Fin m → ι,
            ∫ x : ι → ℝ, ‖Work.Diff.STE.pdVec m l φ x‖ ^ 2 := by
  classical
  obtain ⟨C₀, hC₀nn, hC₀⟩ := CSq_le_ENormSq (ι := ι) s
  refine ⟨C₀ * (2 * ((csqp_boxIdx ι).card : ℝ) ^ 2), by positivity, ?_⟩
  intro φ hφ hsupp
  have hφ' : ContDiff ℝ (⊤ : ℕ∞) φ := hφ
  have hPcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m)) :=
    csqp_periodization_contDiff hφ' hsupp
  have hPper : Periodic1 (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m)) :=
    periodization_periodic φ
  have hmain : CSq s (fourierCoeff (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m)))
      ≤ C₀ * (ENormSq s (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m))
          + ENormSq 0 (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m))) :=
    hC₀ _ (hPcd.of_le (by exact_mod_cast le_top)) hPper
  have hEs := steB3_ENormSq_periodization_le_integral hφ' hsupp s
  have hE0 := steB3_ENormSq_periodization_le_integral hφ' hsupp 0
  set T : ℝ := ∑ m ∈ Finset.range (s+1), ∑ l : Fin m → ι,
      ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 with hT
  have htermnn : ∀ m : ℕ, 0 ≤ ∑ l : Fin m → ι, ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 :=
    fun m => Finset.sum_nonneg (fun l _ => integral_nonneg (fun x => by positivity))
  have hsT : ∑ l : Fin s → ι, ∫ x : ι → ℝ, ‖pdVec s l φ x‖ ^ 2 ≤ T := by
    rw [hT]
    exact Finset.single_le_sum (fun m _ => htermnn m)
      (Finset.mem_range.mpr (by omega))
  have h0T : ∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖pdVec 0 l φ x‖ ^ 2 ≤ T := by
    rw [hT]
    exact Finset.single_le_sum (fun m _ => htermnn m)
      (Finset.mem_range.mpr (by omega))
  have hN : (0 : ℝ) ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 := by positivity
  calc CSq s (fourierCoeff (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m)))
      ≤ C₀ * (ENormSq s (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m))
          + ENormSq 0 (fun z : ι → ℝ => ∑' m : ι → ℤ, φ (z + iVec m))) := hmain
    _ ≤ C₀ * (((csqp_boxIdx ι).card : ℝ) ^ 2
            * (∑ l : Fin s → ι, ∫ x : ι → ℝ, ‖pdVec s l φ x‖ ^ 2)
          + ((csqp_boxIdx ι).card : ℝ) ^ 2
            * (∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖pdVec 0 l φ x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add hEs hE0) hC₀nn
    _ ≤ C₀ * (2 * ((csqp_boxIdx ι).card : ℝ) ^ 2) * T := by
        have h1 : ((csqp_boxIdx ι).card : ℝ) ^ 2
              * (∑ l : Fin s → ι, ∫ x : ι → ℝ, ‖pdVec s l φ x‖ ^ 2)
            ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 * T := mul_le_mul_of_nonneg_left hsT hN
        have h2 : ((csqp_boxIdx ι).card : ℝ) ^ 2
              * (∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖pdVec 0 l φ x‖ ^ 2)
            ≤ ((csqp_boxIdx ι).card : ℝ) ^ 2 * T := mul_le_mul_of_nonneg_left h0T hN
        have h3 : ((csqp_boxIdx ι).card : ℝ) ^ 2
              * (∑ l : Fin s → ι, ∫ x : ι → ℝ, ‖pdVec s l φ x‖ ^ 2)
            + ((csqp_boxIdx ι).card : ℝ) ^ 2
              * (∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖pdVec 0 l φ x‖ ^ 2)
            ≤ 2 * ((csqp_boxIdx ι).card : ℝ) ^ 2 * T := by linarith
        calc C₀ * (((csqp_boxIdx ι).card : ℝ) ^ 2
              * (∑ l : Fin s → ι, ∫ x : ι → ℝ, ‖pdVec s l φ x‖ ^ 2)
            + ((csqp_boxIdx ι).card : ℝ) ^ 2
              * (∑ l : Fin 0 → ι, ∫ x : ι → ℝ, ‖pdVec 0 l φ x‖ ^ 2))
            ≤ C₀ * (2 * ((csqp_boxIdx ι).card : ℝ) ^ 2 * T) :=
              mul_le_mul_of_nonneg_left h3 hC₀nn
          _ = C₀ * (2 * ((csqp_boxIdx ι).card : ℝ) ^ 2) * T := by ring

end Work.Diff.STE.B3
