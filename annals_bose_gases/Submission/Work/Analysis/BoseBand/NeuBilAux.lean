import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.neuFrac_bilinear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.Analysis.BoseBand.NeuBilAux`

The three auxiliary facts about the polar form
`Work.BoseFixB2.DvApriori.neuBil` of the anchored box Neumann-resolvent fraction
`Work.BoseKinLoc.neuFrac ℓ a² 0` which turn it into a *continuous linear functional of its
second argument*:
` neuBil`, its finite-sum expansion, its sup-norm Lipschitz bound on the cube `acube ℓ`, and
the resulting continuity of `y ↦ neuBil ℓ a² 0 c (G · y)`.

This file is self-contained (it imports only the frozen vocabulary and the complete
`neuFrac_bilinear`), so the off-diagonal band argument of
`Submission.Work.Analysis.BoseBand.neuWord_fibre_offdiag` does not depend on the state of the
`DvApriori` development.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

namespace Work.Analysis.BoseBand

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Submission.BoseGases

/-! ## 1. The volume of the anchored cube -/

/-- The Lebesgue volume of the anchored cube `acube ℓ`, as a real number. -/
noncomputable def acubeVol (ℓ : ℝ) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin 3))).real (Submission.BoseGases.acube ℓ)

lemma acubeVol_nonneg (ℓ : ℝ) : 0 ≤ acubeVol ℓ := by
  rw [acubeVol]
  exact MeasureTheory.measureReal_nonneg

lemma acubeVol_eq {ℓ : ℝ} (hℓ : 0 < ℓ) : acubeVol ℓ = ℓ ^ 3 := by
  rw [acubeVol, MeasureTheory.Measure.real, Submission.BoseGases.acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity)]

/-- The integral of a constant over the anchored cube. -/
lemma integral_const_acube {ℓ : ℝ} (c : ℝ) :
    (∫ z in Submission.BoseGases.acube ℓ, c) = c * acubeVol ℓ := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, acubeVol, mul_comm]

/-- `∫_{acube ℓ} u² ≤ M²ℓ³` as soon as `|u| ≤ M` on `acube ℓ`. -/
lemma integral_sq_le_of_abs_le {ℓ M : ℝ} (hℓ : 0 < ℓ) (hM : 0 ≤ M)
    {u : EuclideanSpace ℝ (Fin 3) → ℝ} (hu : Continuous u)
    (hb : ∀ z ∈ Submission.BoseGases.acube ℓ, |u z| ≤ M) :
    ∫ z in Submission.BoseGases.acube ℓ, (u z) ^ 2 ≤ M ^ 2 * ℓ ^ 3 := by
  have hs : MeasurableSet (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_measurable ℓ
  have hcs : IsCompact (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_compact hℓ
  have hf : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) => (u z) ^ 2)
      (Submission.BoseGases.acube ℓ) volume :=
    (hu.pow 2).continuousOn.integrableOn_compact hcs
  have hg : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin 3) => M ^ 2)
      (Submission.BoseGases.acube ℓ) volume :=
    continuous_const.continuousOn.integrableOn_compact hcs
  have h1 : ∫ z in Submission.BoseGases.acube ℓ, (u z) ^ 2
      ≤ ∫ z in Submission.BoseGases.acube ℓ, M ^ 2 := by
    refine MeasureTheory.setIntegral_mono_on hf hg hs (fun z hz => ?_)
    have h := mul_self_le_mul_self (abs_nonneg (u z)) (hb z hz)
    have h2 : (u z) ^ 2 = |u z| * |u z| := by rw [← sq_abs (u z), pow_two]
    have h3 : M ^ 2 = M * M := pow_two M
    rw [h2, h3]
    exact h
  rw [integral_const_acube, acubeVol_eq hℓ] at h1
  exact h1

/-! ## 2. The finite-sum expansion of `neuBil` in its second slot -/

theorem neuBil_sum_expansion {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) {ι : Type*}
    (s : Finset ι) (A : ι → ℝ) (b : ι → EuclideanSpace ℝ (Fin 3) → ℝ)
    {c : EuclideanSpace ℝ (Fin 3) → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hb : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (b i)) :
    Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => ∑ k ∈ s, A k * b k z)
      = ∑ k ∈ s, A k * Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (b k) := by
  classical
  revert hb
  refine Finset.induction_on s ?_ ?_
  · intro hb
    simp only [Finset.sum_empty]
    exact Work.BoseFixB2.DvApriori.neuBil_zero_right ℓ a2 0 c
  · intro i s hi ih hb
    have hbi : ContDiff ℝ (⊤ : ℕ∞) (b i) := hb i (Finset.mem_insert_self i s)
    have hbs : ∀ j ∈ s, ContDiff ℝ (⊤ : ℕ∞) (b j) :=
      fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hsumc : ContDiff ℝ (⊤ : ℕ∞) (fun z => ∑ k ∈ s, A k * b k z) := by
      refine ContDiff.sum ?_
      intro k hk
      exact contDiff_const.mul (hbs k hk)
    have hfun : (fun z => ∑ k ∈ insert i s, A k * b k z)
        = fun z => A i * b i z + ∑ k ∈ s, A k * b k z := by
      funext z
      rw [Finset.sum_insert hi]
    rw [hfun, Finset.sum_insert hi]
    rw [Work.BoseFixB2.DvApriori.neuBil_add_right hℓ ha2 0 hc
      (contDiff_const.mul hbi) hsumc]
    rw [Work.BoseFixB2.DvApriori.neuBil_smul_right hℓ ha2 0 (A i) hc hbi]
    rw [ih hbs]

/-! ## 3. The sup-norm Lipschitz bound for `neuBil` on the cube -/

theorem neuBil_sup_lipschitz {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2)
    {S δ : ℝ} (hS : 0 < S) (hδ : 0 ≤ δ)
    {c f g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hc : Continuous c) (hf : Continuous f) (hg : Continuous g)
    (hcS : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z| ≤ S)
    (hfS : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z| ≤ S)
    (hgS : ∀ z ∈ Submission.BoseGases.acube ℓ, |g z| ≤ S)
    (hfg : ∀ z ∈ Submission.BoseGases.acube ℓ, |f z - g z| ≤ δ) :
    |Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c f
        - Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c g|
      ≤ 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1) * Real.sqrt (ℓ ^ 3) * δ := by
  have h2S : 0 ≤ 2 * S := by linarith
  have hℓ3nn : 0 ≤ ℓ ^ 3 := by positivity
  have hRpos : 0 < 2 * S * Real.sqrt (ℓ ^ 3) + 1 := by
    have h := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * S) (Real.sqrt_nonneg (ℓ ^ 3))
    linarith
  have hbound : ∀ u : EuclideanSpace ℝ (Fin 3) → ℝ, Continuous u →
      (∀ z ∈ Submission.BoseGases.acube ℓ, |u z| ≤ 2 * S) →
      ∫ z in Submission.BoseGases.acube ℓ, (u z) ^ 2
        ≤ (2 * S * Real.sqrt (ℓ ^ 3) + 1) ^ 2 := by
    intro u hu hb
    refine le_trans (integral_sq_le_of_abs_le hℓ h2S hu hb) ?_
    have h0 : 0 ≤ 2 * S * Real.sqrt (ℓ ^ 3) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have h1 : 2 * S * Real.sqrt (ℓ ^ 3) ≤ 2 * S * Real.sqrt (ℓ ^ 3) + 1 := by linarith
    calc (2 * S) ^ 2 * ℓ ^ 3 = (2 * S) ^ 2 * (Real.sqrt (ℓ ^ 3)) ^ 2 := by
          rw [Real.sq_sqrt hℓ3nn]
      _ = (2 * S * Real.sqrt (ℓ ^ 3)) ^ 2 := by ring
      _ ≤ (2 * S * Real.sqrt (ℓ ^ 3) + 1) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have hcf : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z + f z| ≤ 2 * S := by
    intro z hz
    calc |c z + f z| ≤ |c z| + |f z| := abs_add_le _ _
      _ ≤ S + S := add_le_add (hcS z hz) (hfS z hz)
      _ = 2 * S := by ring
  have hcg : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z + g z| ≤ 2 * S := by
    intro z hz
    calc |c z + g z| ≤ |c z| + |g z| := abs_add_le _ _
      _ ≤ S + S := add_le_add (hcS z hz) (hgS z hz)
      _ = 2 * S := by ring
  have hdf : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z - f z| ≤ 2 * S := by
    intro z hz
    have h1 : |c z - f z| ≤ |c z| + |f z| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (c z) (-(f z))
    calc |c z - f z| ≤ |c z| + |f z| := h1
      _ ≤ S + S := add_le_add (hcS z hz) (hfS z hz)
      _ = 2 * S := by ring
  have hdg' : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z - g z| ≤ 2 * S := by
    intro z hz
    have h1 : |c z - g z| ≤ |c z| + |g z| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (c z) (-(g z))
    calc |c z - g z| ≤ |c z| + |g z| := h1
      _ ≤ S + S := add_le_add (hcS z hz) (hgS z hz)
      _ = 2 * S := by ring
  have h1 := hbound (fun z => c z + f z) (hc.add hf) hcf
  have h2 := hbound (fun z => c z + g z) (hc.add hg) hcg
  have h3 := hbound (fun z => c z - f z) (hc.sub hf) hdf
  have h4 := hbound (fun z => c z - g z) (hc.sub hg) hdg'
  have hli := Work.BoseFixB2.DvApriori.neuBil_lipschitz_right (ℓ := ℓ) (a2 := a2)
    (R := 2 * S * Real.sqrt (ℓ ^ 3) + 1) hℓ ha2 hRpos 0 hc hf hg
    (by rw [Work.BoseFixB2.Sector.lamBox_zero_eq_acube]; exact h1)
    (by rw [Work.BoseFixB2.Sector.lamBox_zero_eq_acube]; exact h2)
    (by rw [Work.BoseFixB2.Sector.lamBox_zero_eq_acube]; exact h3)
    (by rw [Work.BoseFixB2.Sector.lamBox_zero_eq_acube]; exact h4)
  have hdg : ∫ z in Submission.BoseGases.acube ℓ, (f z - g z) ^ 2 ≤ δ ^ 2 * ℓ ^ 3 :=
    integral_sq_le_of_abs_le hℓ hδ (hf.sub hg) hfg
  have hsqrt : Real.sqrt (∫ z in Submission.BoseGases.acube ℓ, (f z - g z) ^ 2)
      ≤ δ * Real.sqrt (ℓ ^ 3) := by
    refine le_trans ((Real.sqrt_le_sqrt_iff (by positivity)).mpr hdg) ?_
    rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ]
  rw [Work.BoseFixB2.Sector.lamBox_zero_eq_acube] at hli
  refine le_trans hli ?_
  have h3nn : 0 ≤ 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1) :=
    mul_nonneg (by norm_num) (by linarith [Real.sqrt_nonneg (ℓ ^ 3)])
  calc 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1)
        * Real.sqrt (∫ z in Submission.BoseGases.acube ℓ, (f z - g z) ^ 2)
      ≤ 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1) * (δ * Real.sqrt (ℓ ^ 3)) :=
        mul_le_mul_of_nonneg_left hsqrt h3nn
    _ = 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1) * Real.sqrt (ℓ ^ 3) * δ := by ring

/-! ## 4. Continuity of `y ↦ neuBil c (G · y)` on the cube -/

theorem continuousOn_neuBil_family {ℓ a2 R : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 < a2) (hR : 0 < R)
    {c : EuclideanSpace ℝ (Fin 3) → ℝ} (hc : Continuous c)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : Continuous fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2)
    (hcR : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z| ≤ R)
    (hGR : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ y ∈ Submission.BoseGases.acube ℓ, |G z y| ≤ R) :
    ContinuousOn (fun y => Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y))
      (Submission.BoseGases.acube ℓ) := by
  set S : ℝ := 2 * R + 1 with hSdef
  have hSpos : 0 < S := by rw [hSdef]; linarith
  have hcS : ∀ z ∈ Submission.BoseGases.acube ℓ, |c z| ≤ S := by
    intro z hz
    rw [hSdef]
    linarith [hcR z hz]
  have hGS : ∀ z ∈ Submission.BoseGases.acube ℓ, ∀ y ∈ Submission.BoseGases.acube ℓ,
      |G z y| ≤ S := by
    intro z hz y hy
    rw [hSdef]
    linarith [hGR z hz y hy]
  set K : ℝ := 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1) * Real.sqrt (ℓ ^ 3) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : 0 < 2 * S * Real.sqrt (ℓ ^ 3) + 1 := by
      have h := mul_nonneg (by linarith : (0:ℝ) ≤ 2 * S) (Real.sqrt_nonneg (ℓ ^ 3))
      linarith
    have h2 : 0 < Real.sqrt (ℓ ^ 3) := Real.sqrt_pos.mpr (by positivity)
    exact mul_pos (mul_pos (by norm_num) h1) h2
  -- uniform continuity of the kernel on the compact product cube
  have hΛ : IsCompact (Submission.BoseGases.acube ℓ) :=
    Submission.BoseGases.acube_compact hℓ
  have huc : UniformContinuousOn
      (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => G p.1 p.2)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) :=
    (hΛ.prod hΛ).uniformContinuousOn_of_continuous hG.continuousOn
  rw [Metric.continuousOn_iff]
  intro y₀ hy₀ ε hε
  set δL : ℝ := ε / (K + 1) with hδLdef
  have hδLpos : 0 < δL := by rw [hδLdef]; exact div_pos hε (by linarith)
  have hKδL : K * δL < ε := by
    rw [hδLdef, mul_div_assoc', div_lt_iff₀ (by linarith : (0:ℝ) < K + 1)]
    nlinarith
  obtain ⟨η, hηpos, hη⟩ := (Metric.uniformContinuousOn_iff.mp huc) δL hδLpos
  refine ⟨η, hηpos, fun y hy hyη => ?_⟩
  have hfg : ∀ z ∈ Submission.BoseGases.acube ℓ, |G z y - G z y₀| ≤ δL := by
    intro z hz
    have hp1 : (z, y) ∈ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ :=
      ⟨hz, hy⟩
    have hp2 : (z, y₀) ∈ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ :=
      ⟨hz, hy₀⟩
    have hdist : dist (z, y) (z, y₀) < η := by
      rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : (0:ℝ) ≤ dist y y₀)]
      exact hyη
    have := hη (z, y) hp1 (z, y₀) hp2 hdist
    simpa only [Real.dist_eq] using this.le
  have hmain := neuBil_sup_lipschitz (ℓ := ℓ) (a2 := a2) (S := S) (δ := δL) hℓ ha2
    hSpos hδLpos.le hc (hG.comp (continuous_id.prodMk continuous_const))
    (hG.comp (continuous_id.prodMk continuous_const)) hcS
    (fun z hz => hGS z hz y hy) (fun z hz => hGS z hz y₀ hy₀) hfg
  have hlt : |Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y)
      - Work.BoseFixB2.DvApriori.neuBil ℓ a2 0 c (fun z => G z y₀)| < ε := by
    have hK : 3 * (2 * S * Real.sqrt (ℓ ^ 3) + 1) * Real.sqrt (ℓ ^ 3) = K := hKdef.symm
    rw [hK] at hmain
    exact lt_of_le_of_lt hmain hKδL
  simpa only [Real.dist_eq] using hlt

end Work.Analysis.BoseBand
