import Mathlib
import Submission.Work.NN.Core.czB_C0_defs
import Submission.Work.NN.Core.czPair

namespace Work.NN.Core

open MeasureTheory Set
open scoped NNReal ENNReal

set_option maxHeartbeats 2000000

/-- **Integrability of the product of the Bochner–Martinelli kernel (in its first variable)
with a continuous compactly supported function.** -/
lemma czBPair_integrable_fst_prod {n : ℕ} (hn : 0 < n) (j : Fin n)
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable (fun p : (Fin n → ℂ) × (Fin n → ℂ) =>
      Work.CR.Flat.Cauchy.bmKernel j p.1 * h p) (volume.prod volume) := by
  obtain ⟨M, hM⟩ := hh.bounded_above_of_compact_support hhc
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM (0, 0))
  set K : Set ((Fin n → ℂ) × (Fin n → ℂ)) := tsupport h with hKdef
  have hK : IsCompact K := hhc
  set P1 : Set (Fin n → ℂ) := Prod.fst '' K with hP1def
  set P2 : Set (Fin n → ℂ) := Prod.snd '' K with hP2def
  have hP1 : IsCompact P1 := hK.image continuous_fst
  have hP2 : IsCompact P2 := hK.image continuous_snd
  have hf1 : Integrable
      (P1.indicator (fun x : Fin n → ℂ => ‖Work.CR.Flat.Cauchy.bmKernel j x‖)) := by
    refine (integrable_indicator_iff hP1.isClosed.measurableSet).mpr ?_
    exact ((Work.CR.Flat.Cauchy.locallyIntegrable_bmKernel hn j).integrableOn_isCompact hP1).norm
  have hg1 : Integrable (P2.indicator (fun _ : Fin n → ℂ => (1:ℝ))) := by
    refine (integrable_indicator_iff hP2.isClosed.measurableSet).mpr ?_
    exact integrableOn_const hP2.measure_lt_top.ne
  have hD : Integrable (fun p : (Fin n → ℂ) × (Fin n → ℂ) =>
      M * ((P1.indicator (fun x : Fin n → ℂ => ‖Work.CR.Flat.Cauchy.bmKernel j x‖)) p.1
            * (P2.indicator (fun _ : Fin n → ℂ => (1:ℝ))) p.2)) :=
    (Integrable.mul_prod hf1 hg1).const_mul M
  refine hD.mono' ?_ ?_
  · exact (((Work.CR.Flat.Cauchy.measurable_bmKernel j).comp measurable_fst).mul
      hh.measurable).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun a => ?_
    by_cases ha : a ∈ K
    · have h1 : a.1 ∈ P1 := ⟨a, ha, rfl⟩
      have h2 : a.2 ∈ P2 := ⟨a, ha, rfl⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
      simp only [mul_one]
      have hb : ‖h a‖ ≤ M := hM a
      have hk : 0 ≤ ‖Work.CR.Flat.Cauchy.bmKernel j a.1‖ := norm_nonneg _
      rw [norm_mul]
      nlinarith [hb, hk, hM0]
    · have h0 : h a = 0 := image_eq_zero_of_notMem_tsupport (by rwa [hKdef] at ha)
      rw [h0, mul_zero, norm_zero]
      exact mul_nonneg hM0 (mul_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
        (Set.indicator_nonneg (fun _ _ => by norm_num) _))

/-- **Translation of the singular inner integral.**  `∫ ζ, K_j(ζ - z) a ζ = ∫ x, K_j x a(z+x)`. -/
lemma czBPair_inner_translate {n : ℕ} (j : Fin n) (a : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ)
      = ∫ x, Work.CR.Flat.Cauchy.bmKernel j x * a (z + x) := by
  rw [← MeasureTheory.integral_add_left_eq_self
        (fun ζ : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ) z]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [add_sub_cancel_left]

/-- **Integrability of the singular inner integral multiplied by a compactly supported function.** -/
lemma czBPair_inner_integrable {n : ℕ} (hn : 0 < n) (j : Fin n)
    {a b : (Fin n → ℂ) → ℂ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun z : Fin n → ℂ =>
      (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ) * b z) := by
  set hh : (Fin n → ℂ) × (Fin n → ℂ) → ℂ := fun p => a (p.2 + p.1) * b p.2 with hhdef
  have hhcont : Continuous hh := by
    rw [hhdef]
    exact (ha.comp (continuous_snd.add continuous_fst)).mul (hb.comp continuous_snd)
  have hhcs : HasCompactSupport hh := by
    rw [hhdef]
    set Sa : Set (Fin n → ℂ) := tsupport a with hSadef
    set Sb : Set (Fin n → ℂ) := tsupport b with hSbdef
    have hSa : IsCompact Sa := hac
    have hSb : IsCompact Sb := hbc
    have hdiff : IsCompact
        ((fun q : (Fin n → ℂ) × (Fin n → ℂ) => q.1 - q.2) '' (Sa ×ˢ Sb)) :=
      (hSa.prod hSb).image (continuous_fst.sub continuous_snd)
    refine HasCompactSupport.of_support_subset_isCompact (hdiff.prod hSb) ?_
    intro p hp
    rw [Function.mem_support] at hp
    have hprod : a (p.2 + p.1) * b p.2 ≠ 0 := hp
    rw [mul_ne_zero_iff] at hprod
    obtain ⟨ha1, hb1⟩ := hprod
    have h2 : p.2 + p.1 ∈ Sa := subset_tsupport a (Function.mem_support.mpr ha1)
    have h3 : p.2 ∈ Sb := subset_tsupport b (Function.mem_support.mpr hb1)
    refine ⟨⟨(p.2 + p.1, p.2), ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rwa [hSadef]
    · rwa [hSbdef]
    · show (p.2 + p.1) - p.2 = p.1
      abel
    · rwa [hSbdef]
  have hint := czBPair_integrable_fst_prod hn j hhcont hhcs
  have h2 := hint.integral_prod_right
  refine h2.congr (Filter.Eventually.of_forall fun z => ?_)
  show (∫ x : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel j x * hh (x, z))
      = (∫ ζ : Fin n → ℂ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * a ζ) * b z
  have hpt : (fun x : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j x * hh (x, z))
      = fun x => (Work.CR.Flat.Cauchy.bmKernel j x * a (z + x)) * b z := by
    funext x; rw [hhdef]; ring
  rw [hpt, MeasureTheory.integral_mul_const]
  rw [← czBPair_inner_translate j a z]

/-- **Oddness of the Bochner–Martinelli kernel identifies the adjoint field `czV`.** -/
lemma czBPair_odd {n : ℕ} (j : Fin n) (φ : Fin n → (Fin n → ℂ) → ℂ) (ζ : Fin n → ℂ) :
    (∫ z, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * star (Work.NN.Core.czTheta φ z))
      = - Work.NN.Core.czV φ ζ j := by
  rw [Work.NN.Core.czV_apply]
  rw [← MeasureTheory.integral_neg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  have hker : Work.CR.Flat.Cauchy.bmKernel j (ζ - z)
      = - Work.CR.Flat.Cauchy.bmKernel j (z - ζ) := by
    have h : ζ - z = -(z - ζ) := by abel
    rw [h, Work.CR.Flat.Cauchy.bmKernel_neg]
  rw [hker]; ring

theorem czB_C0_pairing {n : ℕ} (hn : 0 < n)
    {ψ : Fin n → (Fin n → ℂ) → ℂ} {φ : Fin n → (Fin n → ℂ) → ℂ}
    (hψ : ∀ j, Continuous (ψ j)) (hψc : ∀ j, HasCompactSupport (ψ j))
    (hu : ContDiff ℝ 1 (Work.CR.Flat.Cauchy.bmPotential ψ))
    (hφ : ∀ i, ContDiff ℝ 1 (φ i)) (hφc : ∀ i, HasCompactSupport (φ i)) :
    ∑ i, ∫ z, Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential ψ) z * star (φ i z)
      = ∑ l, ∫ w, ψ l w * Work.NN.Core.czV φ w l := by
  have hθcont : Continuous (Work.NN.Core.czTheta φ) := by
    unfold Work.NN.Core.czTheta
    exact continuous_finsetSum _ (fun i _ => Work.CR.Flat.Cauchy.continuous_dbarCoord (hφ i) i)
  have hθcs : HasCompactSupport (Work.NN.Core.czTheta φ) := by
    unfold Work.NN.Core.czTheta
    have h := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun i (y : Fin n → ℂ) => Work.CR.Flat.dbarCoord i (φ i) y)
      (fun i _ => Work.NN.Core.hasCompactSupport_dbarCoordAux (hφc i) i)
    have h' : (∑ i, (fun y : Fin n → ℂ => Work.CR.Flat.dbarCoord i (φ i) y))
        = fun z => ∑ i, Work.CR.Flat.dbarCoord i (φ i) z := by
      funext z; simp [Finset.sum_apply]
    rwa [h'] at h
  have hbcont : Continuous (fun z => star (Work.NN.Core.czTheta φ z)) := hθcont.star
  have hbcs : HasCompactSupport (fun z => star (Work.NN.Core.czTheta φ z)) :=
    hasCompactSupport_star_comp hθcs
  -- Step 1: integration by parts for `∂_i`
  have hIBP : ∀ i : Fin n,
      (∫ z, Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential ψ) z * star (φ i z))
        = -∫ z, Work.CR.Flat.Cauchy.bmPotential ψ z
            * star (Work.CR.Flat.dbarCoord i (φ i) z) := by
    intro i
    have hg : ContDiff ℝ 1 (fun z => star (φ i z)) := Complex.conjCLE.contDiff.comp (hφ i)
    have hgc : HasCompactSupport (fun z => star (φ i z)) := hasCompactSupport_star_comp (hφc i)
    have hibp := Work.NN.Core.ibp_dCoord i hu hg hgc
    have hcongr : (fun x => Work.CR.Flat.Cauchy.bmPotential ψ x
          * Work.CR.Flat.dCoord i (fun z => star (φ i z)) x)
        = fun x => Work.CR.Flat.Cauchy.bmPotential ψ x
            * star (Work.CR.Flat.dbarCoord i (φ i) x) := by
      funext x
      rw [Work.NN.Core.dCoord_star i (φ i) x ((hφ i).differentiable (by norm_num) x)]
    rw [hcongr] at hibp
    have := congrArg Neg.neg hibp
    rw [neg_neg] at this
    exact this.symm
  -- Step 2: combine the pieces into `-∫ u · star θ`
  have hInt1 : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      Integrable (fun z => Work.CR.Flat.Cauchy.bmPotential ψ z
        * star (Work.CR.Flat.dbarCoord i (φ i) z)) := by
    intro i _
    refine (hu.continuous.mul
      ((continuous_star).comp (Work.CR.Flat.Cauchy.continuous_dbarCoord (hφ i) i)))
      |>.integrable_of_hasCompactSupport ?_
    exact hasCompactSupport_star_comp
      (Work.NN.Core.hasCompactSupport_dbarCoordAux (hφc i) i) |>.mul_left
  have hLHS : (∑ i, ∫ z, Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential ψ) z
        * star (φ i z))
      = -∫ z, Work.CR.Flat.Cauchy.bmPotential ψ z * star (Work.NN.Core.czTheta φ z) := by
    rw [Finset.sum_congr rfl (fun i _ => hIBP i), Finset.sum_neg_distrib]
    congr 1
    rw [← MeasureTheory.integral_finsetSum (s := Finset.univ) hInt1]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (∑ i, Work.CR.Flat.Cauchy.bmPotential ψ z
        * star (Work.CR.Flat.dbarCoord i (φ i) z))
      = Work.CR.Flat.Cauchy.bmPotential ψ z * star (Work.NN.Core.czTheta φ z)
    rw [Work.NN.Core.czTheta_apply, star_sum, ← Finset.mul_sum]
  -- Step 3: expand `u = bmPotential ψ`
  have hExpand :
      (∫ z, Work.CR.Flat.Cauchy.bmPotential ψ z * star (Work.NN.Core.czTheta φ z))
        = ∑ j, ∫ z, (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * ψ j ζ)
            * star (Work.NN.Core.czTheta φ z) := by
    have hpw : ∀ z, Work.CR.Flat.Cauchy.bmPotential ψ z * star (Work.NN.Core.czTheta φ z)
        = ∑ j, (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * ψ j ζ)
            * star (Work.NN.Core.czTheta φ z) := by
      intro z
      show (∑ j, ∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * ψ j ζ)
            * star (Work.NN.Core.czTheta φ z)
        = ∑ j, (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * ψ j ζ)
            * star (Work.NN.Core.czTheta φ z)
      rw [Finset.sum_mul]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpw)]
    rw [MeasureTheory.integral_finsetSum]
    intro j _
    exact czBPair_inner_integrable hn j (hψ j) (hψc j) hbcont hbcs
  -- Step 4: Fubini pairing and oddness
  have hPerJ : ∀ j : Fin n,
      (∫ z, (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * ψ j ζ)
            * star (Work.NN.Core.czTheta φ z))
        = -∫ ζ, ψ j ζ * Work.NN.Core.czV φ ζ j := by
    intro j
    have hcp := czPair hn j (hψ j) (hψc j) hbcont hbcs
    rw [show (fun z => (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * ψ j ζ)
          * star (Work.NN.Core.czTheta φ z))
        = fun z => star (Work.NN.Core.czTheta φ z)
          * (∫ ζ, Work.CR.Flat.Cauchy.bmKernel j (ζ - z) * ψ j ζ) from by
      funext z; ring]
    rw [hcp]
    rw [show (∫ ζ, ψ j ζ * (∫ z, Work.CR.Flat.Cauchy.bmKernel j (ζ - z)
          * star (Work.NN.Core.czTheta φ z)))
        = ∫ ζ, ψ j ζ * (- Work.NN.Core.czV φ ζ j) from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
      dsimp only
      rw [czBPair_odd j φ ζ]]
    rw [show (fun ζ : Fin n → ℂ => ψ j ζ * (- Work.NN.Core.czV φ ζ j))
        = fun ζ => -(ψ j ζ * Work.NN.Core.czV φ ζ j) from by
      funext ζ; ring]
    rw [MeasureTheory.integral_neg]
  rw [hLHS, hExpand]
  rw [Finset.sum_congr rfl (fun j _ => hPerJ j), Finset.sum_neg_distrib, neg_neg]

end Work.NN.Core
