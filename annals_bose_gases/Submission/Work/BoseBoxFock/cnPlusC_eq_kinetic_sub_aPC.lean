import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.cIPn_sum_aPC_re
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.cnPlusC_eq_kinetic_sub_aPC`

The **kinetic-minus-slot-pairing** form of the complex excited count:

    `cnPlusC ℓ Φ = n·∫_{abox} ‖Φ‖² − ∫_{abox} re (star Φ · Σ_j aPC_j Φ)`

for a continuous, compactly supported, box-supported state `Φ`.  This is the "one-body"
half of the sector-Parseval identity in its sharp (non-rounded) form: writing
`Q_jΦ = Φ − P_jΦ` pointwise,

    `star Φ · (Σ_j Q_jΦ) = n·(star Φ · Φ) − star Φ · (Σ_j P_jΦ)`,

so taking real parts and integrating, the identity is

    `Σ_j ‖Q_jΦ‖² = n·‖Φ‖² − Σ_j Re(Φ, P_jΦ)`,

i.e. the orthogonality `⟨P_jΦ, Q_jΦ⟩ = 0` (the peel of `cIPn_sum_aPC_re`) rewritten with the
slot mean on the right-hand side instead of the slot complement.  The analytic work
(measurability/bounds of `aPC`, and the orthogonality) is inherited from
`Submission/Work/BoseBoxFock/cIPn_sum_aPC_re.lean`; what is added here is the elementary
but fiddly bookkeeping passing between the pairing `cIPn` and the two box integrals.

Everything is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped Topology BigOperators ComplexConjugate

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. A boundedness lemma for continuous compactly supported states -/

/-- A continuous compactly supported complex function on the configuration space is globally
bounded.  (Derived from `IsCompact.exists_bound_of_continuousOn` on `tsupport f`, where `f`
vanishes by definition outside the support.) -/
theorem exists_bound_of_continuous_hasCompactSupport {n : ℕ} {f : Work.BoseDict.Xn n → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ tsupport f
  · exact le_trans (hC x hx) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx]; simp

/-! ## 2. The real part of a Bochner integral on the configuration space -/

/-- The real part of a `ℂ`-valued Bochner integral over a set of configurations is the
integral of the real part.  (Twin of `Work.BoseBoxFock.setIntegral_re_complex`, which is
stated on the one-particle space `EuclideanSpace ℝ (Fin 3)`.) -/
theorem setIntegral_re_complex_xn {n : ℕ} (s : Set (Work.BoseDict.Xn n)) (f : Work.BoseDict.Xn n → ℂ)
    (hf : IntegrableOn f s volume) : (∫ y in s, f y).re = ∫ y in s, (f y).re := by
  have h := integral_re (𝕜 := ℂ) (μ := (volume : Measure (Work.BoseDict.Xn n)).restrict s)
    (f := f) hf
  simpa using h.symm

/-! ## 3. The main identity -/

theorem cnPlusC_eq_kinetic_sub_aPC {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Work.BoseDict.Xn n → ℂ} (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ)
    (hΦsupp : Function.support Φ ⊆ Submission.BoseGases.abox n ℓ) :
    Work.BoseBoxFock.cnPlusC ℓ Φ
      = (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, ‖Φ x‖ ^ 2)
        - (∫ x in Submission.BoseGases.abox n ℓ,
            star (Φ x) * (∑ j : Fin n, Work.BoseBoxFock.aPC ℓ j Φ x)).re := by
  obtain ⟨C, hC0, hCb⟩ := exists_bound_of_continuous_hasCompactSupport hΦ hΦc
  -- `Φ` is an `L^∞` state, so the pairing identity `cIPn_sum_aPC_re` applies
  have hMemLp : MemLp Φ (⊤ : ENNReal) (volume : Measure (Work.BoseDict.Xn n)) :=
    hΦ.memLp_of_hasCompactSupport hΦc
  have hcn := cIPn_sum_aPC_re (d := n) hℓ Φ hMemLp hΦsupp
  rw [← hcn]
  -- ## measurability and bounds on the box
  have hAesmΦ : AEStronglyMeasurable Φ (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    hΦ.stronglyMeasurable.aestronglyMeasurable.restrict
  have hAesm_aPC : ∀ j : Fin n, AEStronglyMeasurable (aPC ℓ j Φ)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
    fun j => (aPC_aestronglyMeasurable_of_stronglyMeasurable j hΦ.stronglyMeasurable).restrict
  have hbnd_aPC : ∀ j : Fin n, ∀ x, ‖aPC ℓ j Φ x‖ ≤ C :=
    fun j => norm_aPC_le hℓ j hC0 hCb
  have hAesm_A : AEStronglyMeasurable
      (fun x : Work.BoseDict.Xn n => ∑ j : Fin n, aPC ℓ j Φ x)
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun j _ => hAesm_aPC j)
    exact h.congr (Filter.Eventually.of_forall (fun x => by simp only [Finset.sum_apply]))
  have hAesm_g : AEStronglyMeasurable
      (fun x : Work.BoseDict.Xn n => ∑ j : Fin n, (Φ x - aPC ℓ j Φ x))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin n))
      (fun j _ => hAesmΦ.sub (hAesm_aPC j))
    exact h.congr (Filter.Eventually.of_forall (fun x => by simp [Finset.sum_apply]))
  have hbnd_A : ∀ x : Work.BoseDict.Xn n, ‖∑ j : Fin n, aPC ℓ j Φ x‖ ≤ n * C := by
    intro x
    calc ‖∑ j : Fin n, aPC ℓ j Φ x‖
        ≤ ∑ j : Fin n, ‖aPC ℓ j Φ x‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, C := Finset.sum_le_sum (fun j _ => hbnd_aPC j x)
      _ = n * C := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hbnd_g : ∀ x : Work.BoseDict.Xn n,
      ‖∑ j : Fin n, (Φ x - aPC ℓ j Φ x)‖ ≤ n * (C + C) := by
    intro x
    calc ‖∑ j : Fin n, (Φ x - aPC ℓ j Φ x)‖
        ≤ ∑ j : Fin n, ‖Φ x - aPC ℓ j Φ x‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, (C + C) := Finset.sum_le_sum
          (fun j _ => le_trans (norm_sub_le _ _) (add_le_add (hCb x) (hbnd_aPC j x)))
      _ = n * (C + C) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- ## integrability of the three integrands on the (finite-measure) box
  have hIntL : IntegrableOn
      (fun x => star (Φ x) * (∑ j : Fin n, (Φ x - aPC ℓ j Φ x)))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hAesmΦ.star.mul hAesm_g) (C * (n * (C + C))) ?_
    filter_upwards with x
    rw [norm_mul, norm_star]
    exact mul_le_mul (hCb x) (hbnd_g x) (norm_nonneg _) hC0
  have hIntR : IntegrableOn
      (fun x => star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x))
      (Submission.BoseGases.abox n ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      (hAesmΦ.star.mul hAesm_A) (C * (n * C)) ?_
    filter_upwards with x
    rw [norm_mul, norm_star]
    exact mul_le_mul (hCb x) (hbnd_A x) (norm_nonneg _) hC0
  have hIntSq : IntegrableOn (fun x => ‖Φ x‖ ^ 2) (Submission.BoseGases.abox n ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
      ((hΦ.norm.pow 2).aestronglyMeasurable).restrict (C * C) ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [hCb x, hC0, norm_nonneg (Φ x)]
  -- ## rewrite the pairing as a box integral (`Φ` vanishes off the box)
  have h1 : Work.BoseDict.cIPn n Φ (fun x => ∑ j : Fin n, (Φ x - aPC ℓ j Φ x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          star (Φ x) * (∑ j : Fin n, (Φ x - aPC ℓ j Φ x)) := by
    rw [Work.BoseDict.cIPn]
    exact (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hx0 : Φ x = 0 := by
        by_contra h
        exact hx (hΦsupp ((Function.mem_support).mpr h))
      rw [hx0]; simp)).symm
  -- ## pass to real parts
  have h2 : (∫ x in Submission.BoseGases.abox n ℓ,
        star (Φ x) * (∑ j : Fin n, (Φ x - aPC ℓ j Φ x))).re
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (star (Φ x) * (∑ j : Fin n, (Φ x - aPC ℓ j Φ x))).re :=
    setIntegral_re_complex_xn _ _ hIntL
  -- ## the pointwise algebraic identity
  have hpt : ∀ x : Work.BoseDict.Xn n,
      (star (Φ x) * (∑ j : Fin n, (Φ x - aPC ℓ j Φ x))).re
      = (n : ℝ) * ‖Φ x‖ ^ 2
        - (star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x)).re := by
    intro x
    have hsplit : star (Φ x) * (∑ j : Fin n, (Φ x - aPC ℓ j Φ x))
        = (n : ℂ) * (star (Φ x) * Φ x) - star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x) := by
      rw [Finset.mul_sum]
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum]
    rw [hsplit, Complex.sub_re]
    congr 1
    rw [show star (Φ x) = (starRingEnd ℂ) (Φ x) from rfl, Complex.conj_mul']
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h3 : (∫ x in Submission.BoseGases.abox n ℓ,
        (star (Φ x) * (∑ j : Fin n, (Φ x - aPC ℓ j Φ x))).re)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          ((n : ℝ) * ‖Φ x‖ ^ 2 - (star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x)).re) :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- ## split the integral
  have h4 : (∫ x in Submission.BoseGases.abox n ℓ,
          ((n : ℝ) * ‖Φ x‖ ^ 2 - (star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x)).re))
      = (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, ‖Φ x‖ ^ 2)
        - ∫ x in Submission.BoseGases.abox n ℓ,
            (star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x)).re := by
    have h := MeasureTheory.integral_sub (f := fun x => (n : ℝ) * ‖Φ x‖ ^ 2)
      (g := fun x => (star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x)).re)
      (hIntSq.const_mul (n : ℝ)) hIntR.re
    rw [MeasureTheory.integral_const_mul] at h
    exact h
  have h5 : (∫ x in Submission.BoseGases.abox n ℓ,
          (star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x)).re)
      = (∫ x in Submission.BoseGases.abox n ℓ,
          star (Φ x) * (∑ j : Fin n, aPC ℓ j Φ x)).re :=
    (setIntegral_re_complex_xn _ _ hIntR).symm
  rw [h1, h2, h3, h4, h5]

end Work.BoseBoxFock
