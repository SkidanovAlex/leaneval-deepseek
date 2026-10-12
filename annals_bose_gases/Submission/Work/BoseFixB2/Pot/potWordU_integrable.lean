import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixB2.Defs
import Submission.Work.BoseFixB2.Pot.aemeasurable_wPairC_prod
import Submission.Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU
import Submission.Work.BoseFixB2.Pot.lintegral_coord_abox
import Submission.Work.BoseFixB2.Pot.lintegral_pair_abox
import Submission.Work.BoseFixB2.Pot.lintegral_wPairC_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Pot.potWordU_integrable`

Integrability of the multiplicative part of FS `eq:Def_HB`,
`Work.BoseKinLoc.potWordU n v (g₀ v h) ℓ μ 0`, over the centred box `abox n ℓ`, for
*every* box side `ℓ : ℝ` — in particular with **no diluteness hypothesis** relating the
support radius `R` of `v` to `ℓ`.

That is the point of the statement: the corpus' pointwise bounds (`abs_potWordU_le`,
`abs_wLoc_pair_le`) need `R ≤ ℓ·chiR0`, and they are *false* for `R > ℓ`: the quotient
`v(z)/(χ⋆χ)_ℓ(z)` blows up like `(ℓ−‖z‖)^{−(2k+2)}` near the sphere `‖z‖ = ℓ` where the
denominator vanishes.  What is true — and what is used here — is the **exact cancellation
of the two `χ_ℓ` factors with the denominator**, an identity about the *joint* integral
and not a pointwise bound:

    ∫⁻_{(a,b)} ‖χ_ℓ(a)·h(a−b)/(χ⋆χ)_ℓ(a−b)·χ_ℓ(b)‖ₑ
      = ∫⁻_z ofReal(ℓ³·(χ⋆χ)_ℓ(z))·ofReal(|h z|/(χ⋆χ)_ℓ(z)) ≤ ofReal(ℓ³·∫|h|),

because `c·(|h z|/c) ≤ |h z|` pointwise (Lean's `x/0 = 0` handles `c = 0`).  This is
`Work.BoseFixB2.Pot.lintegral_wPairC_le`, whose engine is the upstream volume identity
`Submission.BoseGases.integral_pair_scale`.

Everything is therefore formulated in `∫⁻` (ENNReal) language — the Bochner integral of a
non-integrable function is `0` and would make the intermediate steps vacuous — and the box
integrals are evaluated by the peeling lemmas
`Work.BoseFixB2.Pot.lintegral_coord_abox` (one coordinate) and
`Work.BoseFixB2.Pot.lintegral_pair_abox` (two coordinates).

Structure of the argument:

* `n = 0`: `potWordU 0` is identically zero (both sums are empty);
* `ℓ ≤ 0`: `abox n ℓ` is null (`acube ℓ = ∅` for `ℓ < 0`, `= {0}` for `ℓ = 0`);
* `ℓ > 0`: rewrite `potWordU` through `wLoc ℓ · 0 = wPairC`, dominate
  `‖potWordU x‖ₑ ≤ ‖μ‖ₑ·ΣᵢQ(xᵢ) + Σ_{i<j}‖wPairC ℓ v (xᵢ)(xⱼ)‖ₑ` with
  `Q a = ∫⁻_y ‖wPairC ℓ g₀ a y‖ₑ`, and evaluate the two lintegrals by peeling and
  the master inequality.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Work.BoseFixB2.Pot

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- With translation parameter `u = 0` the localisation kernel `wLoc` is the
χ-renormalised two-body kernel `wPairC`. -/
lemma wLoc_zero_eq_wPairC (ℓ : ℝ) (h : ℝ³ → ℝ) (a b : ℝ³) :
    Submission.BoseGases.wLoc ℓ h 0 a b = Submission.BoseGases.wPairC ℓ h a b := by
  rw [Submission.BoseGases.wPairC_apply]
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

theorem potWordU_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hv1 : MeasureTheory.MemLp v 1) {μ : ℝ} {n : ℕ} (ℓ : ℝ) : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x) (Submission.BoseGases.abox n ℓ) := by
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hg_int : MeasureTheory.Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- ## `n = 0`: the word vanishes identically
    subst hn
    have h0 : ∀ x : Submission.BoseGases.X 0,
        Work.BoseKinLoc.potWordU 0 v (Submission.BoseGases.g0 v h) ℓ μ 0 x = 0 := by
      intro x
      haveI : IsEmpty {ij : Fin 0 × Fin 0 // ij.1 < ij.2} :=
        ⟨fun ij => absurd ij.1.1.isLt (by omega)⟩
      rw [Work.BoseKinLoc.potWordU]
      simp
    exact (MeasureTheory.integrable_zero (Submission.BoseGases.X 0) ℝ
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X 0)).restrict
        (Submission.BoseGases.abox 0 ℓ))).congr
      (Filter.Eventually.of_forall (fun x => (h0 x).symm))
  · rcases le_or_gt ℓ 0 with hℓ | hℓ
    · -- ## `ℓ ≤ 0`: the box is null
      have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))
          (Submission.BoseGases.abox n ℓ) = 0 := by
        rcases lt_or_eq_of_le hℓ with hlt | heq
        · have hemp : Submission.BoseGases.abox n ℓ = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro x hx
            rw [Submission.BoseGases.mem_abox_iff] at hx
            have hmem := hx ⟨0, hn⟩
            rw [Submission.BoseGases.mem_acube_iff] at hmem
            have h2 := hmem 0
            rw [Set.mem_Icc] at h2
            linarith [h2.1, h2.2]
          rw [hemp, measure_empty]
        · subst heq
          have hn' : n ≠ 0 := ne_of_gt hn
          rw [Submission.BoseGases.abox_volume n 0 le_rfl,
            show (((0 : ℝ) ^ 3) ^ n) = 0 by
              rw [zero_pow (by norm_num), zero_pow hn']]
          simp
      change MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X n =>
          Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))
      rw [MeasureTheory.Measure.restrict_eq_zero.mpr hvol]
      exact MeasureTheory.integrable_zero_measure
    · -- ## `0 < ℓ`: the main case
      have hℓnn : (0 : ℝ) ≤ ℓ := le_of_lt hℓ
      -- the pointwise rewrite of `potWordU`
      have hpot : ∀ x : Submission.BoseGases.X n,
          Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x
            = -μ * (∑ i : Fin n, ∫ y : ℝ³,
                Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) (x i) y)
              + ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
                  Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2) := by
        intro x
        rw [Work.BoseKinLoc.potWordU]
        congr 1
        · congr 1
          apply Finset.sum_congr rfl
          intro i _
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (fun y => wLoc_zero_eq_wPairC ℓ (Submission.BoseGases.g0 v h) (x i) y)
        · apply Finset.sum_congr rfl
          intro ij _
          exact wLoc_zero_eq_wPairC ℓ v (x ij.1.1) (x ij.1.2)
      set Q : ℝ³ → ENNReal := fun a =>
        ∫⁻ y : ℝ³, ‖Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) a y‖ₑ with hQ
      have hwmeas : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ³ × ℝ³ =>
            Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2)
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
            (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
        aemeasurable_wPairC_prod hg_int.aestronglyMeasurable
      have hvmeas : MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ³ × ℝ³ => Submission.BoseGases.wPairC ℓ v p.1 p.2)
          ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
            (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
        aemeasurable_wPairC_prod hv_int.aestronglyMeasurable
      have hQ_meas : MeasureTheory.AEStronglyMeasurable Q
          (MeasureTheory.volume : MeasureTheory.Measure ℝ³) := by
        rw [hQ]
        exact (AEMeasurable.lintegral_prod_right' hwmeas.enorm).aestronglyMeasurable
      -- enlarging the cube-restricted integral
      have hcube_le : ∀ f : ℝ³ → ENNReal,
          (∫⁻ x : ℝ³ in Submission.BoseGases.acube ℓ, f x) ≤ (∫⁻ x : ℝ³, f x) := by
        intro f
        refine (lintegral_mono_set (Set.subset_univ (Submission.BoseGases.acube ℓ))).trans ?_
        exact le_of_eq (by simp [Measure.restrict_univ])
      -- the peeled bounds
      have hQint : (∫⁻ a : ℝ³, Q a
          ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
            (Submission.BoseGases.acube ℓ))) ≤ (∫⁻ a : ℝ³, Q a
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)) := hcube_le Q
      have hQfull : (∫⁻ a : ℝ³, Q a ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³))
          = (∫⁻ p : ℝ³ × ℝ³,
              ‖Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2‖ₑ
              ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
                (MeasureTheory.volume : MeasureTheory.Measure ℝ³))) := by
        rw [hQ]
        exact (MeasureTheory.lintegral_prod
          (f := fun p : ℝ³ × ℝ³ =>
            ‖Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) p.1 p.2‖ₑ)
          hwmeas.enorm).symm
      have hQbd : (∫⁻ a : ℝ³, Q a ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³))
          ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) := by
        rw [hQfull]
        exact lintegral_wPairC_le hℓ hg_int
      have hvbd : (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
            ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
            ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
              (Submission.BoseGases.acube ℓ))
            ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
              (Submission.BoseGases.acube ℓ)))
          ≤ ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |v z|) := by
        have hstep : (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
              ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
              ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                (Submission.BoseGases.acube ℓ))
              ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                (Submission.BoseGases.acube ℓ)))
            ≤ (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
                ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
                ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)
                ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)) := by
          calc (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
                ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
                ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                  (Submission.BoseGases.acube ℓ))
                ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                  (Submission.BoseGases.acube ℓ)))
              ≤ (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
                  ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
                  ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                    (Submission.BoseGases.acube ℓ))
                  ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
                hcube_le (fun a : ℝ³ => ∫⁻ b : ℝ³ in Submission.BoseGases.acube ℓ,
                  ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ)
            _ ≤ (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
                  ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
                  ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)
                  ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
                lintegral_mono
                  (fun a => hcube_le (fun b : ℝ³ => ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ))
        have hfull : (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
              ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)
              ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³))
            = (∫⁻ p : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC ℓ v p.1 p.2‖ₑ
                ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
                  (MeasureTheory.volume : MeasureTheory.Measure ℝ³))) :=
          (MeasureTheory.lintegral_prod
            (f := fun p : ℝ³ × ℝ³ => ‖Submission.BoseGases.wPairC ℓ v p.1 p.2‖ₑ)
            hvmeas.enorm).symm
        exact le_trans hstep (le_trans (le_of_eq hfull)
          (lintegral_wPairC_le hℓ hv_int))
      -- a.e. measurability of the two families of summands
      have hQcomp : ∀ i : Fin n, AEMeasurable (fun x : Submission.BoseGases.X n => Q (x i))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) := by
        intro i
        exact ((hQ_meas.comp_quasiMeasurePreserving (qmp_coord_X i)).aemeasurable).restrict
      have hWmeas : ∀ i j : Fin n, i ≠ j → AEMeasurable
          (fun x : Submission.BoseGases.X n =>
            ‖Submission.BoseGases.wPairC ℓ v (x i) (x j)‖ₑ)
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) := by
        intro i j hij
        exact (((aesm_wLoc_pair_X (ℓ := ℓ) (u := 0) hv_int.aestronglyMeasurable
          i j hij).aemeasurable.enorm).congr
          (Filter.Eventually.of_forall (fun x => by
            simp only [wLoc_zero_eq_wPairC ℓ v (x i) (x j)]))).restrict
      -- the two finite lintegrals
      have hQi : ∀ i : Fin n, (∫⁻ x : Submission.BoseGases.X n, Q (x i)
          ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ))) < ⊤ := by
        intro i
        calc (∫⁻ x : Submission.BoseGases.X n, Q (x i)
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)))
            = ((MeasureTheory.volume : MeasureTheory.Measure ℝ³)
                (Submission.BoseGases.acube ℓ)) ^ (n - 1)
              * (∫⁻ a : ℝ³, Q a
                  ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                    (Submission.BoseGases.acube ℓ))) :=
              lintegral_coord_abox hℓ i hQ_meas
          _ ≤ ((MeasureTheory.volume : MeasureTheory.Measure ℝ³)
                (Submission.BoseGases.acube ℓ)) ^ (n - 1)
              * (∫⁻ a : ℝ³, Q a ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
              mul_le_mul_right hQint _
          _ ≤ ((MeasureTheory.volume : MeasureTheory.Measure ℝ³)
                (Submission.BoseGases.acube ℓ)) ^ (n - 1)
              * ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) :=
              mul_le_mul_right hQbd _
          _ < ⊤ := ENNReal.mul_lt_top
              (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn))
              ENNReal.ofReal_lt_top
      have hWij : ∀ i j : Fin n, i ≠ j →
          (∫⁻ x : Submission.BoseGases.X n,
              ‖Submission.BoseGases.wPairC ℓ v (x i) (x j)‖ₑ
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ))) < ⊤ := by
        intro i j hij
        calc (∫⁻ x : Submission.BoseGases.X n,
                ‖Submission.BoseGases.wPairC ℓ v (x i) (x j)‖ₑ
                ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ)))
            = ((MeasureTheory.volume : MeasureTheory.Measure ℝ³)
                (Submission.BoseGases.acube ℓ)) ^ (n - 2)
              * (∫⁻ a : ℝ³, ∫⁻ b : ℝ³,
                  ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ
                  ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                    (Submission.BoseGases.acube ℓ))
                  ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
                    (Submission.BoseGases.acube ℓ))) :=
              lintegral_pair_abox
                (φ := fun a b => ‖Submission.BoseGases.wPairC ℓ v a b‖ₑ) hℓ hij
                hvmeas.enorm.aestronglyMeasurable
          _ ≤ ((MeasureTheory.volume : MeasureTheory.Measure ℝ³)
                (Submission.BoseGases.acube ℓ)) ^ (n - 2)
              * ENNReal.ofReal (ℓ ^ 3 * ∫ z : ℝ³, |v z|) := mul_le_mul_right hvbd _
          _ < ⊤ := ENNReal.mul_lt_top
              (ENNReal.pow_lt_top (Submission.BoseGases.acube_lt_top ℓ hℓnn))
              ENNReal.ofReal_lt_top
      -- the pointwise domination
      have hpt : ∀ x : Submission.BoseGases.X n,
          ENNReal.ofReal ‖Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x‖
            ≤ ‖μ‖ₑ * (∑ i : Fin n, Q (x i))
              + ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
                  ‖Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)‖ₑ := by
        intro x
        have h1 : ENNReal.ofReal ‖Work.BoseKinLoc.potWordU n v
            (Submission.BoseGases.g0 v h) ℓ μ 0 x‖
            = ‖Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x‖ₑ := by
          rw [Real.norm_eq_abs, ← Real.enorm_eq_ofReal_abs]
        rw [h1, hpot x]
        refine le_trans (enorm_add_le _ _) (add_le_add ?_ (enorm_sum_le _ _))
        rw [enorm_mul, enorm_neg]
        refine mul_le_mul_right ?_ _
        refine le_trans (enorm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
        rw [hQ]
        exact MeasureTheory.enorm_integral_le_lintegral_enorm _
      -- finiteness of the dominated lintegral
      have hQmeas_sum : AEMeasurable
          (fun x : Submission.BoseGases.X n => ‖μ‖ₑ * (∑ i : Fin n, Q (x i)))
          ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) := by
        refine (AEMeasurable.const_mul (Finset.aemeasurable_sum Finset.univ
          (fun i _ => hQcomp i)) ‖μ‖ₑ).congr ?_
        filter_upwards with x
        simp only [Finset.sum_apply]
      have hDfin : (∫⁻ x : Submission.BoseGases.X n,
            (‖μ‖ₑ * (∑ i : Fin n, Q (x i))
              + ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
                  ‖Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)‖ₑ)
            ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) < ⊤ := by
        have hfirst : (∫⁻ x : Submission.BoseGases.X n, ‖μ‖ₑ * (∑ i : Fin n, Q (x i))
            ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) < ⊤ := by
          rw [MeasureTheory.lintegral_const_mul' (‖μ‖ₑ) _ (by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_ne_top)]
          refine ENNReal.mul_lt_top ?_ ?_
          · simpa only [Real.enorm_eq_ofReal_abs] using
              (ENNReal.ofReal_lt_top : ENNReal.ofReal |μ| < ⊤)
          · rw [MeasureTheory.lintegral_finsetSum']
            · exact ENNReal.sum_lt_top.mpr (fun i _ => hQi i)
            · exact fun i _ => hQcomp i
        have hsecond : (∫⁻ x : Submission.BoseGases.X n,
              ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
                  ‖Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)‖ₑ
            ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ))) < ⊤ := by
          rw [MeasureTheory.lintegral_finsetSum']
          · exact ENNReal.sum_lt_top.mpr
              (fun ij _ => hWij ij.1.1 ij.1.2 (ne_of_lt ij.2))
          · exact fun ij _ => hWmeas ij.1.1 ij.1.2 (ne_of_lt ij.2)
        calc (∫⁻ x : Submission.BoseGases.X n,
              (‖μ‖ₑ * (∑ i : Fin n, Q (x i))
                + ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
                    ‖Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)‖ₑ)
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)))
            = (∫⁻ x : Submission.BoseGases.X n, ‖μ‖ₑ * (∑ i : Fin n, Q (x i))
                ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ)))
              + (∫⁻ x : Submission.BoseGases.X n,
                  ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
                    ‖Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)‖ₑ
                ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ))) := by
              rw [MeasureTheory.lintegral_add_left' hQmeas_sum]
          _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hfirst, hsecond⟩
      -- conclude
      change MeasureTheory.Integrable
        (fun x : Submission.BoseGases.X n =>
          Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x)
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ))
      refine ⟨?_, ?_⟩
      · exact (aestronglyMeasurable_potWordU (u := 0)
          hv_int.aestronglyMeasurable hg_int.aestronglyMeasurable).mono_measure
          Measure.restrict_le_self
      · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
        calc (∫⁻ x : Submission.BoseGases.X n,
              ENNReal.ofReal ‖Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x‖
              ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                (Submission.BoseGases.abox n ℓ)))
            ≤ (∫⁻ x : Submission.BoseGases.X n,
                (‖μ‖ₑ * (∑ i : Fin n, Q (x i))
                  + ∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
                      ‖Submission.BoseGases.wPairC ℓ v (x ij.1.1) (x ij.1.2)‖ₑ)
                ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ))) := lintegral_mono hpt
          _ < ⊤ := hDfin

end Work.BoseFixB2.Pot
