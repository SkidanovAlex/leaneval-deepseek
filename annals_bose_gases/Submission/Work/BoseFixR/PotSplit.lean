import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixR.CombBlockSplit
import Submission.Work.BoseFixR.PotWordUBlockSplit
import Submission.Work.BoseFixR.PotWordUIntegrableLoc
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixR.PotSplit` — the potential word splits over the blocks

The commissioned statement is the potential-energy half of the exact block decomposition of
the box word:

    ∫_{Λ^j}∫_{Λ^k} (bfL Φ y z)² · potWordU k v g ℓ μ 0 z
  + ∫_{Λ^k}∫_{Λ^j} (bfR Φ z y)² · potWordU j v g ℓ μ 0 y
  ≤ ∫_{Λ^{k+j}} (Φ x)² · potWordU (k+j) v g ℓ μ 0 x

with a **single** box side `ℓ` on both sides (the box word `potWordU` carries no side of its
own, so there is no volume-factor mismatch here, unlike in `SplitTwo`).

## Why it holds

`potWordU N v g ℓ μ u x = -μ Σ_i ∫_y wLoc ℓ g u (x_i) y + Σ_{i<j} wLoc ℓ v u (x_i) (x_j)`
is *block additive up to the cross pairs*: for a configuration `x` of `k+j` particles,

    potWordU (k+j) x = potWordU k (firstBlock x) + potWordU j (lastBlock x) + cross x,
    cross x = Σ_{i<k, j≥k} wLoc ℓ v 0 (x_i) (x_j) ≥ 0,

the cross terms being `≥ 0` because `0 ≤ v` and both `χ` and `(χ⋆χ)_ℓ` are nonnegative.
Since `(Φ x)² ≥ 0`, the pointwise inequality

    (Φ x)² · potWordU k (firstBlock x) + (Φ x)² · potWordU j (lastBlock x) ≤ (Φ x)² · potWordU (k+j) x

follows.  The two iterated integrals on the left are rewritten as integrals over `abox (k+j) ℓ`
by the restricted Fubini lemmas `aboxFubini`/`aboxFubini_swapped` (`Submission/Work/AboxBlockSplit.lean`),
which need the integrability of the integrands; the latter is provided by
`Work.BoseFixR.PotWordUIntegrableLoc` (the bare word is integrable on the box for *locally*
integrable `v, g`) together with the boundedness of `Φ²` on the compact box and the transport
of integrability along the block-split equivalence.
-/

noncomputable section

open MeasureTheory Metric
open scoped Topology

namespace Work.BoseFixR

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `mergeBlock` is the re-assembly of the two blocks; it is measurable. -/
lemma measurable_mergeBlock (k j : ℕ) : Measurable (Submission.BoseGases.mergeBlock k j) := by
  rw [measurable_pi_iff]
  intro i
  rcases h : Submission.BoseGases.finSplit k j i with i1 | j2
  · simp only [Submission.BoseGases.mergeBlock, h, Sum.elim_inl]
    exact (measurable_pi_apply i1).comp measurable_fst
  · simp only [Submission.BoseGases.mergeBlock, h, Sum.elim_inr]
    exact (measurable_pi_apply j2).comp measurable_snd

/-- An almost-everywhere statement about the product of the two restricted block volumes follows
from its pointwise version on the two boxes. -/
lemma ae_prod_restrict_abox {k j : ℕ} {ℓ : ℝ}
    {p : Submission.BoseGases.X k × Submission.BoseGases.X j → Prop}
    (h : ∀ z y, z ∈ Submission.BoseGases.abox k ℓ → y ∈ Submission.BoseGases.abox j ℓ →
      p (z, y)) :
    ∀ᵐ q ∂((volume : Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k ℓ)).prod
        ((volume : Measure (Submission.BoseGases.X j)).restrict
          (Submission.BoseGases.abox j ℓ)), p q := by
  rw [Measure.prod_restrict]
  exact (ae_restrict_iff'
    ((Submission.BoseGases.abox_measurable k ℓ).prod
      (Submission.BoseGases.abox_measurable j ℓ))).mpr
    (Filter.Eventually.of_forall (fun q hq => h q.1 q.2 hq.1 hq.2))

/-- `comb` is `mergeBlock`. -/
lemma comb_eq_mergeBlock {k j : ℕ} (z : Submission.BoseGases.X k)
    (y : Submission.BoseGases.X j) :
    comb z y = Submission.BoseGases.mergeBlock k j (z, y) := by
  apply (Submission.BoseGases.blockSplitEquiv k j).injective
  rw [CombBlockSplit z y, Submission.BoseGases.blockSplitEquiv_apply, Prod.mk.injEq]
  exact ⟨(Submission.BoseGases.mergeBlock_first k j z y).symm,
    (Submission.BoseGases.mergeBlock_last k j z y).symm⟩

theorem PotSplit {k j : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hv : 0 ≤ v) (hvi : MeasureTheory.LocallyIntegrable v) (hgi : MeasureTheory.LocallyIntegrable g)
    {Φ : Submission.BoseGases.X (k + j) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    (∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
        (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v g ℓ μ 0 z)
      + (∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
        (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v g ℓ μ 0 y)
      ≤ ∫ x in Submission.BoseGases.abox (k + j) ℓ,
          (Φ x) ^ 2 * Work.BoseKinLoc.potWordU (k + j) v g ℓ μ 0 x := by
  -- ## 0. integrability of the bare words (delegated)
  have hIk : IntegrableOn (fun z : Submission.BoseGases.X k =>
      Work.BoseKinLoc.potWordU k v g ℓ μ 0 z) (Submission.BoseGases.abox k ℓ) volume :=
    PotWordUIntegrableLoc (N := k) (ℓ := ℓ) (μ := μ) hℓ hvi hgi
  have hIj : IntegrableOn (fun z : Submission.BoseGases.X j =>
      Work.BoseKinLoc.potWordU j v g ℓ μ 0 z) (Submission.BoseGases.abox j ℓ) volume :=
    PotWordUIntegrableLoc (N := j) (ℓ := ℓ) (μ := μ) hℓ hvi hgi
  have hIkj : IntegrableOn (fun x : Submission.BoseGases.X (k + j) =>
      Work.BoseKinLoc.potWordU (k + j) v g ℓ μ 0 x)
      (Submission.BoseGases.abox (k + j) ℓ) volume :=
    PotWordUIntegrableLoc (N := k + j) (ℓ := ℓ) (μ := μ) hℓ hvi hgi
  -- ## 1. the pointwise block splitting of the word (delegated)
  have hsplit : ∀ x : Submission.BoseGases.X (k + j),
      Work.BoseKinLoc.potWordU (k + j) v g ℓ μ 0 x
        = Work.BoseKinLoc.potWordU k v g ℓ μ 0 (Submission.BoseGases.firstBlock k j x)
          + Work.BoseKinLoc.potWordU j v g ℓ μ 0 (Submission.BoseGases.lastBlock k j x)
          + ∑ i : Fin k, ∑ i' : Fin j,
              Submission.BoseGases.wLoc ℓ v 0 (Submission.BoseGases.firstBlock k j x i)
                (Submission.BoseGases.lastBlock k j x i') :=
    fun x => PotWordUBlockSplit x
  -- ## 2. `Φ` is bounded on the compact box
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x ∈ Submission.BoseGases.abox (k + j) ℓ, ‖Φ x‖ ≤ M := by
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact (k + j) hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox (k + j) ℓ) (f := Φ) hΦ.continuous.continuousOn
    exact ⟨C, hC⟩
  -- ## 3. the three integrands
  set A : Submission.BoseGases.X (k + j) → ℝ :=
    fun x => (Φ x) ^ 2 * Work.BoseKinLoc.potWordU k v g ℓ μ 0 (Submission.BoseGases.firstBlock k j x)
    with hAdef
  set B : Submission.BoseGases.X (k + j) → ℝ :=
    fun x => (Φ x) ^ 2 * Work.BoseKinLoc.potWordU j v g ℓ μ 0 (Submission.BoseGases.lastBlock k j x)
    with hBdef
  set C : Submission.BoseGases.X (k + j) → ℝ :=
    fun x => (Φ x) ^ 2 * Work.BoseKinLoc.potWordU (k + j) v g ℓ μ 0 x with hCdef
  -- ## 4. integrability of `C`
  have hCint : IntegrableOn C (Submission.BoseGases.abox (k + j) ℓ) volume := by
    rw [hCdef]
    refine Integrable.bdd_mul (c := M ^ 2) hIkj ?_ ?_
    · exact (hΦ.continuous.measurable.pow_const 2).aemeasurable.aestronglyMeasurable
    · refine (ae_restrict_iff' (Submission.BoseGases.abox_measurable (k + j) ℓ)).mpr ?_
      filter_upwards with x hx
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg (Φ x)) (hM x hx) 2
  -- ## 5. integrability of `A` and `B` (transport to the product of the two block boxes)
  have hAint : IntegrableOn A (Submission.BoseGases.abox (k + j) ℓ) volume := by
    set μk : Measure (Submission.BoseGases.X k) :=
      (volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)
      with hμk
    set μj : Measure (Submission.BoseGases.X j) :=
      (volume : Measure (Submission.BoseGases.X j)).restrict (Submission.BoseGases.abox j ℓ)
      with hμj
    set A' : Submission.BoseGases.X k × Submission.BoseGases.X j → ℝ :=
      fun p => (Φ (Submission.BoseGases.mergeBlock k j p)) ^ 2
        * Work.BoseKinLoc.potWordU k v g ℓ μ 0 p.1 with hA'def
    have hone : Integrable (fun _ : Submission.BoseGases.X j => (1 : ℝ)) μj := by
      rw [hμj]
      exact (integrable_const_iff).2 (Or.inr ⟨by
        rw [Measure.restrict_apply_univ]
        exact Submission.BoseGases.abox_lt_top j ℓ hℓ.le⟩)
    have hbase : Integrable (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
        Work.BoseKinLoc.potWordU k v g ℓ μ 0 p.1) (μk.prod μj) := by
      have h := Integrable.mul_prod hIk hone
      simpa using h
    have hA' : Integrable A' (μk.prod μj) := by
      rw [hA'def]
      refine Integrable.bdd_mul (c := M ^ 2) hbase ?_ ?_
      · exact AEMeasurable.aestronglyMeasurable (((hΦ.continuous.measurable.comp
          (measurable_mergeBlock k j)).pow_const 2).aemeasurable)
      · refine ae_prod_restrict_abox (fun z y hz hy => ?_)
        have hmem : Submission.BoseGases.mergeBlock k j (z, y) ∈
            Submission.BoseGases.abox (k + j) ℓ :=
          (Submission.BoseGases.mem_abox_split k j ℓ _).mpr
            ⟨by rwa [Submission.BoseGases.mergeBlock_first],
             by rwa [Submission.BoseGases.mergeBlock_last]⟩
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hM _ hmem) 2
    have hiff := (Submission.BoseGases.aboxSplit_measurePreserving_restrict k j ℓ).integrable_comp_emb
      (Submission.BoseGases.blockSplitEquiv k j).measurableEmbedding (g := A')
    refine (hiff.mpr hA').congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Function.comp_apply, hA'def, hAdef, Submission.BoseGases.blockSplitEquiv_apply,
      Submission.BoseGases.mergeBlock_eq]
  have hBint : IntegrableOn B (Submission.BoseGases.abox (k + j) ℓ) volume := by
    set μk : Measure (Submission.BoseGases.X k) :=
      (volume : Measure (Submission.BoseGases.X k)).restrict (Submission.BoseGases.abox k ℓ)
      with hμk
    set μj : Measure (Submission.BoseGases.X j) :=
      (volume : Measure (Submission.BoseGases.X j)).restrict (Submission.BoseGases.abox j ℓ)
      with hμj
    set B' : Submission.BoseGases.X k × Submission.BoseGases.X j → ℝ :=
      fun p => (Φ (Submission.BoseGases.mergeBlock k j p)) ^ 2
        * Work.BoseKinLoc.potWordU j v g ℓ μ 0 p.2 with hB'def
    have hone : Integrable (fun _ : Submission.BoseGases.X k => (1 : ℝ)) μk := by
      rw [hμk]
      exact (integrable_const_iff).2 (Or.inr ⟨by
        rw [Measure.restrict_apply_univ]
        exact Submission.BoseGases.abox_lt_top k ℓ hℓ.le⟩)
    have hbase : Integrable (fun p : Submission.BoseGases.X k × Submission.BoseGases.X j =>
        Work.BoseKinLoc.potWordU j v g ℓ μ 0 p.2) (μk.prod μj) := by
      have h := Integrable.mul_prod hone hIj
      simpa using h
    have hB' : Integrable B' (μk.prod μj) := by
      rw [hB'def]
      refine Integrable.bdd_mul (c := M ^ 2) hbase ?_ ?_
      · exact AEMeasurable.aestronglyMeasurable (((hΦ.continuous.measurable.comp
          (measurable_mergeBlock k j)).pow_const 2).aemeasurable)
      · refine ae_prod_restrict_abox (fun z y hz hy => ?_)
        have hmem : Submission.BoseGases.mergeBlock k j (z, y) ∈
            Submission.BoseGases.abox (k + j) ℓ :=
          (Submission.BoseGases.mem_abox_split k j ℓ _).mpr
            ⟨by rwa [Submission.BoseGases.mergeBlock_first],
             by rwa [Submission.BoseGases.mergeBlock_last]⟩
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hM _ hmem) 2
    have hiff := (Submission.BoseGases.aboxSplit_measurePreserving_restrict k j ℓ).integrable_comp_emb
      (Submission.BoseGases.blockSplitEquiv k j).measurableEmbedding (g := B')
    refine (hiff.mpr hB').congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Function.comp_apply, hB'def, hBdef, Submission.BoseGases.blockSplitEquiv_apply,
      Submission.BoseGases.mergeBlock_eq]
  -- ## 6. the pointwise inequality `A + B ≤ C`
  have hchiU_nn : ∀ a : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.chiU ℓ 0 a := by
    intro a
    simpa [Submission.BoseGases.chiU] using
      Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • a - (0 : EuclideanSpace ℝ (Fin 3)))
  have hwLoc_nn : ∀ a b : EuclideanSpace ℝ (Fin 3), 0 ≤ Submission.BoseGases.wLoc ℓ v 0 a b := by
    intro a b
    rw [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled]
    exact mul_nonneg (mul_nonneg (hchiU_nn a)
      (div_nonneg (hv _) (Submission.BoseGases.convScale_nonneg ℓ _))) (hchiU_nn b)
  have hcross_nn : ∀ x : Submission.BoseGases.X (k + j),
      0 ≤ ∑ i : Fin k, ∑ i' : Fin j,
          Submission.BoseGases.wLoc ℓ v 0 (Submission.BoseGases.firstBlock k j x i)
            (Submission.BoseGases.lastBlock k j x i') := by
    intro x
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun i' _ => hwLoc_nn _ _))
  have hpt : ∀ x : Submission.BoseGases.X (k + j), A x + B x ≤ C x := by
    intro x
    have hcross := hcross_nn x
    have hsq : 0 ≤ (Φ x) ^ 2 := sq_nonneg _
    have h := mul_nonneg hsq hcross
    simp only [hAdef, hBdef, hCdef, hsplit x]
    nlinarith [h]
  -- ## 7. rewrite the two iterated integrals as integrals over the full box
  have hkey1 : ∀ (y : Submission.BoseGases.X j) (z : Submission.BoseGases.X k),
      (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v g ℓ μ 0 z
        = A (Submission.BoseGases.mergeBlock k j (z, y)) := by
    intro y z
    simp only [hAdef, bfL_eq_comb, comb_eq_mergeBlock,
      Submission.BoseGases.mergeBlock_first]
  have hkey2 : ∀ (z : Submission.BoseGases.X k) (y : Submission.BoseGases.X j),
      (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v g ℓ μ 0 y
        = B (Submission.BoseGases.mergeBlock k j (z, y)) := by
    intro z y
    simp only [hBdef, bfR_eq_comb, comb_eq_mergeBlock,
      Submission.BoseGases.mergeBlock_last]
  have hT1 : (∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
        (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v g ℓ μ 0 z)
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ, A x := by
    calc (∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
          (Work.BoseFixR.bfL Φ y z) ^ 2 * Work.BoseKinLoc.potWordU k v g ℓ μ 0 z)
        = ∫ y in Submission.BoseGases.abox j ℓ, ∫ z in Submission.BoseGases.abox k ℓ,
            A (Submission.BoseGases.mergeBlock k j (z, y)) := by
          apply integral_congr_ae
          filter_upwards with y
          exact integral_congr_ae (Filter.Eventually.of_forall (fun z => hkey1 y z))
      _ = ∫ x in Submission.BoseGases.abox (k + j) ℓ, A x :=
          Submission.BoseGases.aboxFubini_swapped (N1 := k) (N2 := j) ℓ A hAint
  have hT2 : (∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
        (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v g ℓ μ 0 y)
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ, B x := by
    calc (∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
          (Work.BoseFixR.bfR Φ z y) ^ 2 * Work.BoseKinLoc.potWordU j v g ℓ μ 0 y)
        = ∫ z in Submission.BoseGases.abox k ℓ, ∫ y in Submission.BoseGases.abox j ℓ,
            B (Submission.BoseGases.mergeBlock k j (z, y)) := by
          apply integral_congr_ae
          filter_upwards with z
          exact integral_congr_ae (Filter.Eventually.of_forall (fun y => hkey2 z y))
      _ = ∫ x in Submission.BoseGases.abox (k + j) ℓ, B x :=
          Submission.BoseGases.aboxFubini (N1 := k) (N2 := j) ℓ B hBint
  -- ## 8. conclude
  rw [hT1, hT2]
  have hadd : (∫ x in Submission.BoseGases.abox (k + j) ℓ, A x)
      + (∫ x in Submission.BoseGases.abox (k + j) ℓ, B x)
      = ∫ x in Submission.BoseGases.abox (k + j) ℓ, (A x + B x) :=
    (integral_add hAint hBint).symm
  rw [hadd]
  exact integral_mono (hAint.add hBint) hCint hpt

end Work.BoseFixR
