import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.CentredGap
import Submission.PotWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Block split of the centred analysis box (abox) — measure & slicing infrastructure

The FS small-box group trick (thm:smallbox: `e_B(n, μ) ≥ m·e_B(n', μ) + e_B(n'', μ)`)
and the per-sector superadditivity of the corpus analysis energy
`E_s(Φ) = kinWord N s Φ + qLHSword(N, s, μ, wPairC, wPairC∘g0) Φ` need the block
splitting of the centred box `abox (N1+N2) s` into the two blocks of particles:
the `SubaddVol`/`EneuSuperadd` machinery does this for the *plain* box
`box N L` (`blockSplitEquiv`, `blockSplit_measurePreserving_restrict`), this
module transcribes it to `abox` and adds the pointwise/expectation
decomposition of the corpus words `kinWord` and `qLHSword`.

All statements are per-sector (fixed particle numbers), matching the corpus
objects used by `smallBoxEnergy_fs_form` etc.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Geometry: the block split of the centred box -/

/-- `x ∈ abox (N1+N2) s` iff both particle blocks lie in their centred boxes. -/
lemma mem_abox_split (N1 N2 : ℕ) (s : ℝ) (x : X (N1+N2)) :
    x ∈ abox (N1+N2) s ↔ firstBlock N1 N2 x ∈ abox N1 s ∧ lastBlock N1 N2 x ∈ abox N2 s := by
  constructor
  · intro hx
    constructor
    · intro i; exact hx (Fin.castAdd N2 i)
    · intro j; exact hx (Fin.natAdd N1 j)
  · rintro ⟨hu, hw⟩ i
    cases h : finSplit N1 N2 i with
    | inl i1 =>
        have hi : i = Fin.castAdd N2 i1 := by
          have h1 : finSplit N1 N2 i = finSplit N1 N2 (Fin.castAdd N2 i1) := by
            rw [h, finSplit_castAdd]
          exact (finSplit N1 N2).injective h1
        rw [hi]
        exact hu i1
    | inr j2 =>
        have hi : i = Fin.natAdd N1 j2 := by
          have h1 : finSplit N1 N2 i = finSplit N1 N2 (Fin.natAdd N1 j2) := by
            rw [h, finSplit_natAdd]
          exact (finSplit N1 N2).injective h1
        rw [hi]
        exact hw j2

/-- The block-split equivalence sends the product of the block boxes to the
full centred box. -/
lemma preimage_abox (N1 N2 : ℕ) (s : ℝ) :
    (blockSplitEquiv N1 N2) ⁻¹' ((abox N1 s) ×ˢ (abox N2 s)) = abox (N1+N2) s := by
  ext x
  rw [Set.mem_preimage]
  rw [blockSplitEquiv_apply]
  rw [Set.mem_prod]
  exact (mem_abox_split N1 N2 s x).symm

/-- The product of the block-restricted volumes is the restriction of the
product volume to the product of the block boxes. -/
lemma vol_prod_restrict_abox (N1 N2 : ℕ) (s : ℝ) :
    ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) =
      ((volume : Measure (X N1 × X N2)).restrict ((abox N1 s) ×ˢ (abox N2 s))) := by
  rw [Measure.prod_restrict]
  rfl

/-- The volume restricted to the full centred box is carried by the block
split onto the product of the block-restricted volumes. -/
lemma aboxSplit_measurePreserving_restrict (N1 N2 : ℕ) (s : ℝ) :
    MeasurePreserving (blockSplitEquiv N1 N2)
      (volume.restrict (abox (N1+N2) s))
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
  have hmp : MeasurePreserving (blockSplitEquiv N1 N2)
      (volume : Measure (X (N1+N2))) (volume : Measure (X N1 × X N2)) :=
    blockSplitEquiv_measurePreserving N1 N2
  have hres := hmp.restrict_preimage_emb (blockSplitEquiv N1 N2).measurableEmbedding
    ((abox N1 s) ×ˢ (abox N2 s))
  simpa [preimage_abox, vol_prod_restrict_abox] using hres

/-- A product integral over the full centred box factorises over the two
blocks (no integrability hypotheses). -/
lemma aboxIntegral_prod_fun {N1 N2 : ℕ} (s : ℝ) (a : X N1 → ℝ) (b : X N2 → ℝ) :
    (∫ x in abox (N1+N2) s, a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x)) =
      (∫ u in abox N1 s, a u) * (∫ w in abox N2 s, b w) := by
  have hc := (aboxSplit_measurePreserving_restrict N1 N2 s).integral_comp
    (blockSplitEquiv N1 N2).measurableEmbedding (fun p : X N1 × X N2 => a p.1 * b p.2)
  calc
    (∫ x in abox (N1+N2) s, a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x))
        = ∫ x : X (N1+N2), (fun p : X N1 × X N2 => a p.1 * b p.2)
            (blockSplitEquiv N1 N2 x) ∂(volume.restrict (abox (N1+N2) s)) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [blockSplitEquiv_apply]
    _ = ∫ p : X N1 × X N2, a p.1 * b p.2
          ∂((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := hc
    _ = (∫ u in abox N1 s, a u) * (∫ w in abox N2 s, b w) := by
          rw [MeasureTheory.integral_prod_mul (μ := volume.restrict (abox N1 s))
            (ν := volume.restrict (abox N2 s))]

/-! ## Restricted Fubini over the block split -/

/-- Integrability of a product over the two blocks lifts to the full centred box. -/
lemma integrableOn_prod_abox {N1 N2 : ℕ} (s : ℝ) {a : X N1 → ℝ} {b : X N2 → ℝ}
    (ha : IntegrableOn a (abox N1 s) volume) (hb : IntegrableOn b (abox N2 s) volume) :
    IntegrableOn (fun x : X (N1+N2) => a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x))
      (abox (N1+N2) s) volume := by
  have hres := aboxSplit_measurePreserving_restrict N1 N2 s
  have hf : Integrable (fun p : X N1 × X N2 => a p.1 * b p.2)
      ((volume.restrict (abox N1 s)).prod (volume.restrict (abox N2 s))) := by
    exact Integrable.mul_prod ha hb
  change Integrable (fun x : X (N1+N2) => a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x))
      (volume.restrict (abox (N1+N2) s))
  have hpt : (fun x : X (N1+N2) => a (firstBlock N1 N2 x) * b (lastBlock N1 N2 x)) =
      fun x => (fun p : X N1 × X N2 => a p.1 * b p.2) (blockSplitEquiv N1 N2 x) := by
    funext x
    rw [blockSplitEquiv_apply]
  rw [hpt]
  exact (hres.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding
      (g := fun p : X N1 × X N2 => a p.1 * b p.2)).mpr hf

/-- Restricted Fubini (u-outer order): the integral over the full centred box
of `G` equals the iterated integral of `G ∘ merge`. -/
lemma aboxFubini {N1 N2 : ℕ} (s : ℝ) (G : X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (abox (N1 + N2) s) volume) :
    (∫ u in abox N1 s, ∫ w in abox N2 s, G (mergeBlock N1 N2 (u, w))) =
      ∫ x in abox (N1 + N2) s, G x := by
  let μ1 : Measure (X N1) := volume.restrict (abox N1 s)
  let μ2 : Measure (X N2) := volume.restrict (abox N2 s)
  have hGe : Integrable (fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))
      (μ1.prod μ2) := by
    have hmp : MeasurePreserving (blockSplitEquiv N1 N2)
        (volume.restrict (abox (N1 + N2) s)) (μ1.prod μ2) := by
      simpa [μ1, μ2] using aboxSplit_measurePreserving_restrict N1 N2 s
    have hif := (hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding
      (g := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p)))
    apply hif.1
    change Integrable (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x)))
      (volume.restrict (abox (N1 + N2) s))
    have hpt : (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))) = G := by
      funext x
      rw [blockSplitEquiv_apply]
      exact congrArg G (mergeBlock_eq N1 N2 x)
    rw [hpt]
    exact hG
  calc
    (∫ u in abox N1 s, ∫ w in abox N2 s, G (mergeBlock N1 N2 (u, w)))
        = ∫ p : X N1 × X N2, G (mergeBlock N1 N2 p) ∂(μ1.prod μ2) := by
          exact (integral_prod (μ := μ1) (ν := μ2)
            (f := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p)) hGe).symm
    _ = ∫ x in abox (N1 + N2) s, G x := by
          have hEq : (∫ p : X N1 × X N2, G (mergeBlock N1 N2 p) ∂(μ1.prod μ2))
              = ∫ x : X (N1+N2), G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))
                  ∂(volume.restrict (abox (N1 + N2) s)) := by
            exact ((aboxSplit_measurePreserving_restrict N1 N2 s).integral_comp
              (blockSplitEquiv N1 N2).measurableEmbedding
              (fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))).symm
          rw [hEq]
          apply integral_congr_ae
          filter_upwards with x
          rw [blockSplitEquiv_apply]
          exact congrArg G (mergeBlock_eq N1 N2 x)

/-- Restricted Fubini (w-outer order): the integral over the full centred box
of `G` equals the iterated integral over `w ∈ abox N2 s` (outer) and
`u ∈ abox N1 s` (inner) of `G ∘ merge`. -/
lemma aboxFubini_swapped {N1 N2 : ℕ} (s : ℝ) (G : X (N1 + N2) → ℝ)
    (hG : IntegrableOn G (abox (N1 + N2) s) volume) :
    (∫ w in abox N2 s, ∫ u in abox N1 s, G (mergeBlock N1 N2 (u, w))) =
      ∫ x in abox (N1 + N2) s, G x := by
  let μ1 : Measure (X N1) := volume.restrict (abox N1 s)
  let μ2 : Measure (X N2) := volume.restrict (abox N2 s)
  have hGe : Integrable (fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))
      (μ1.prod μ2) := by
    have hmp : MeasurePreserving (blockSplitEquiv N1 N2)
        (volume.restrict (abox (N1 + N2) s)) (μ1.prod μ2) := by
      simpa [μ1, μ2] using aboxSplit_measurePreserving_restrict N1 N2 s
    have hif := (hmp.integrable_comp_emb (blockSplitEquiv N1 N2).measurableEmbedding
      (g := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p)))
    apply hif.1
    change Integrable (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x)))
      (volume.restrict (abox (N1 + N2) s))
    have hpt : (fun x : X (N1+N2) => G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))) = G := by
      funext x
      rw [blockSplitEquiv_apply]
      exact congrArg G (mergeBlock_eq N1 N2 x)
    rw [hpt]
    exact hG
  have hQ : Integrable (fun q : X N2 × X N1 => G (mergeBlock N1 N2 q.swap)) (μ2.prod μ1) := by
    simpa [Function.comp_def, Prod.swap_prod_mk] using hGe.swap
  calc
    (∫ w in abox N2 s, ∫ u in abox N1 s, G (mergeBlock N1 N2 (u, w)))
        = ∫ q : X N2 × X N1, G (mergeBlock N1 N2 q.swap) ∂(μ2.prod μ1) := by
          exact (integral_prod (μ := μ2) (ν := μ1)
            (f := fun q : X N2 × X N1 => G (mergeBlock N1 N2 q.swap)) hQ).symm
    _ = ∫ p : X N1 × X N2, G (mergeBlock N1 N2 p) ∂(μ1.prod μ2) := by
          exact MeasureTheory.integral_prod_swap (μ := μ1) (ν := μ2)
            (f := fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))
    _ = ∫ x in abox (N1 + N2) s, G x := by
          have hEq : (∫ p : X N1 × X N2, G (mergeBlock N1 N2 p) ∂(μ1.prod μ2))
              = ∫ x : X (N1+N2), G (mergeBlock N1 N2 (blockSplitEquiv N1 N2 x))
                  ∂(volume.restrict (abox (N1 + N2) s)) := by
            exact ((aboxSplit_measurePreserving_restrict N1 N2 s).integral_comp
              (blockSplitEquiv N1 N2).measurableEmbedding
              (fun p : X N1 × X N2 => G (mergeBlock N1 N2 p))).symm
          rw [hEq]
          apply integral_congr_ae
          filter_upwards with x
          rw [blockSplitEquiv_apply]
          exact congrArg G (mergeBlock_eq N1 N2 x)

end BoseGases

end Submission
