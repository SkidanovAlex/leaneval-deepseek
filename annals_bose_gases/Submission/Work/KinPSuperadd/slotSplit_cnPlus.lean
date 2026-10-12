import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.cnPlus_nonpos
import Submission.Work.KinPSuperadd.fubini_aQ_fst
import Submission.Work.KinPSuperadd.fubini_aQ_snd
import Submission.Work.KinPSuperadd.integrableSlice_fst
import Submission.Work.KinPSuperadd.integrableSlice_snd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SlotSplit` for the excited-particle count `cnPlus`

`cnPlus s Φ = Σ_i ∫_{abox N s} (QᵢΦ)²` is the number of excited particles of
the state `Φ` on the centred box `abox N s = (acube s)^N`.  The point of this
chapter (`KinPSuperadd/Defs.lean`) is that `cnPlus` is a **sum of one-particle
forms over the slots**, so it is *block-splittable* in the sense of `SlotSplit`:
for every decomposition `N₁ + N₂` of the particle number and every smooth `Φ`,

    cnPlus s Φ
      = ∫_{w ∈ abox N₂ s} cnPlus s (fun u ↦ Φ (merge(u,w)))
      + ∫_{u ∈ abox N₁ s} cnPlus s (fun w ↦ Φ (merge(u,w))) ,

with the two slice integrals integrable.

## Proof

For `s ≤ 0` the centred box is trivial (`acube s ⊆ {0}`), so `abox N s` is a
null set for `N ≥ 1` and `cnPlus s Φ = 0` for *every* state
(`KinPSuperadd.cnPlus_nonpos`); both sides of the identity then vanish.

For `0 < s`, `aQ s i` is a one-slot operator: for a slot `j` of the first block,
`Function.update` commutes with `mergeBlock` (`mergeBlock_update_fst`), hence

    Q_{Fin.castAdd N₂ j} Φ (merge(u,w)) = Q_j (fun u' ↦ Φ (merge(u',w))) u ,

and symmetrically for the second block (`aQ_slice_fst`, `aQ_slice_snd`).  Writing
`cnPlus` as the sum over all `N₁ + N₂` slots and splitting the index set with
`Fin.sum_univ_add`, each term is an integral over the full box of a function of
the block coordinates, which Fubini for the measure-preserving block split
(`aboxFubini_swapped`, `aboxFubini`) turns into the iterated integral; summing
over the slots and applying the slice identities gives the claim.  The two
integrability fields are the Fubini marginals of `x ↦ (Q_iΦ x)²`, which is
integrable over the compact box by `integrableOn_sq_aQ`
(`integrableSlice_fst`, `integrableSlice_snd`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Work.KinPSuperadd

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## Updating one block of a merged configuration -/

/-- Updating slot `j` of the first block commutes with the block concatenation:
`merge (update u j y, w) = update (merge (u,w)) (castAdd N₂ j) y`. -/
lemma mergeBlock_update_fst (N1 N2 : ℕ) (u : X N1) (w : X N2) (j : Fin N1) (y : ℝ³) :
    mergeBlock N1 N2 (Function.update u j y, w) =
      Function.update (mergeBlock N1 N2 (u, w)) (Fin.castAdd N2 j) y := by
  ext k
  cases h : finSplit N1 N2 k with
  | inl i =>
      have hk : k = Fin.castAdd N2 i := (finSplit N1 N2).injective (by rw [h, finSplit_castAdd])
      subst hk
      simp [mergeBlock, Function.update, Fin.castAdd_inj]
  | inr i =>
      have hk : k = Fin.natAdd N1 i := (finSplit N1 N2).injective (by rw [h, finSplit_natAdd])
      subst hk
      simp [mergeBlock, Function.update]

/-- Updating slot `j` of the second block commutes with the block concatenation:
`merge (u, update w j y) = update (merge (u,w)) (natAdd N₁ j) y`. -/
lemma mergeBlock_update_snd (N1 N2 : ℕ) (u : X N1) (w : X N2) (j : Fin N2) (y : ℝ³) :
    mergeBlock N1 N2 (u, Function.update w j y) =
      Function.update (mergeBlock N1 N2 (u, w)) (Fin.natAdd N1 j) y := by
  ext k
  cases h : finSplit N1 N2 k with
  | inl i =>
      have hk : k = Fin.castAdd N2 i := (finSplit N1 N2).injective (by rw [h, finSplit_castAdd])
      subst hk
      simp [mergeBlock, Function.update]
  | inr i =>
      have hk : k = Fin.natAdd N1 i := (finSplit N1 N2).injective (by rw [h, finSplit_natAdd])
      subst hk
      simp [mergeBlock, Function.update, Fin.natAdd_inj]

/-! ## The one-slot (`aP`/`aQ`) slice identities -/

/-- First-block slice of `aP`: `P` commutes with freezing the other block. -/
lemma aP_slice_fst (s : ℝ) (N1 N2 : ℕ) (j : Fin N1) (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) :
    aP s (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w)) =
      aP s j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  unfold aP
  simp only [mergeBlock_update_fst]

/-- First-block slice of `aQ`: `Q` commutes with freezing the other block. -/
lemma aQ_slice_fst (s : ℝ) (N1 N2 : ℕ) (j : Fin N1) (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) :
    aQ s (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w)) =
      aQ s j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u := by
  unfold aQ
  rw [aP_slice_fst]

/-- Second-block slice of `aP`. -/
lemma aP_slice_snd (s : ℝ) (N1 N2 : ℕ) (j : Fin N2) (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) :
    aP s (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w)) =
      aP s j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  unfold aP
  simp only [mergeBlock_update_snd]

/-- Second-block slice of `aQ`. -/
lemma aQ_slice_snd (s : ℝ) (N1 N2 : ℕ) (j : Fin N2) (Φ : X (N1+N2) → ℝ)
    (u : X N1) (w : X N2) :
    aQ s (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w)) =
      aQ s j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w := by
  unfold aQ
  rw [aP_slice_snd]

/-! ## The slice integrability in the sliced coordinates -/

/-- `SlotSplit.int₁` for `cnPlus` at `0 < s`: the first-block slice of the
excited-particle count is integrable over the second block's box. -/
lemma integrableOn_slice_fst {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) (j : Fin N1)
    {Φ : X (N1 + N2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun w : X N2 => ∫ u in abox N1 s,
        (aQ s j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u)^2) (abox N2 s) volume :=
  (integrableSlice_fst hs j hΦc).congr (by
    filter_upwards with w
    apply integral_congr_ae
    filter_upwards with u
    rw [aQ_slice_fst])

/-- `SlotSplit.int₂` for `cnPlus` at `0 < s`. -/
lemma integrableOn_slice_snd {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) (j : Fin N2)
    {Φ : X (N1 + N2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun u : X N1 => ∫ w in abox N2 s,
        (aQ s j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w)^2) (abox N1 s) volume :=
  (integrableSlice_snd hs j hΦc).congr (by
    filter_upwards with u
    apply integral_congr_ae
    filter_upwards with w
    rw [aQ_slice_snd])

/-! ## The block split of `cnPlus` on a positive side -/

/-- The block decomposition of the excited-particle count for `0 < s`. -/
lemma cnPlus_split_pos {N1 N2 : ℕ} {s : ℝ} (hs : 0 < s) {Φ : X (N1 + N2) → ℝ}
    (hΦc : Continuous Φ) :
    cnPlus s Φ
      = (∫ w in abox N2 s, cnPlus s (fun u => Φ (mergeBlock N1 N2 (u, w))))
        + (∫ u in abox N1 s, cnPlus s (fun w => Φ (mergeBlock N1 N2 (u, w)))) := by
  -- first block
  have hA : (∑ j : Fin N1, ∫ x in abox (N1 + N2) s,
        (aQ s (Fin.castAdd N2 j) Φ x)^2)
      = ∫ w in abox N2 s, cnPlus s (fun u => Φ (mergeBlock N1 N2 (u, w))) := by
    calc
      (∑ j : Fin N1, ∫ x in abox (N1 + N2) s, (aQ s (Fin.castAdd N2 j) Φ x)^2)
          = ∑ j : Fin N1, ∫ w in abox N2 s, ∫ u in abox N1 s,
              (aQ s (Fin.castAdd N2 j) Φ (mergeBlock N1 N2 (u, w)))^2 :=
            Finset.sum_congr rfl (fun j _ => fubini_aQ_fst hs j hΦc)
      _ = ∑ j : Fin N1, ∫ w in abox N2 s,
              (∫ u in abox N1 s,
                (aQ s j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u)^2) := by
            apply Finset.sum_congr rfl
            intro j _
            apply integral_congr_ae
            filter_upwards with w
            apply integral_congr_ae
            filter_upwards with u
            rw [aQ_slice_fst]
      _ = ∫ w in abox N2 s, ∑ j : Fin N1,
              (∫ u in abox N1 s,
                (aQ s j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u)^2) :=
            (integral_finsetSum Finset.univ
              (fun j _ => integrableOn_slice_fst hs j hΦc)).symm
      _ = ∫ w in abox N2 s, cnPlus s (fun u => Φ (mergeBlock N1 N2 (u, w))) := rfl
  -- second block
  have hB : (∑ j : Fin N2, ∫ x in abox (N1 + N2) s,
        (aQ s (Fin.natAdd N1 j) Φ x)^2)
      = ∫ u in abox N1 s, cnPlus s (fun w => Φ (mergeBlock N1 N2 (u, w))) := by
    calc
      (∑ j : Fin N2, ∫ x in abox (N1 + N2) s, (aQ s (Fin.natAdd N1 j) Φ x)^2)
          = ∑ j : Fin N2, ∫ u in abox N1 s, ∫ w in abox N2 s,
              (aQ s (Fin.natAdd N1 j) Φ (mergeBlock N1 N2 (u, w)))^2 :=
            Finset.sum_congr rfl (fun j _ => fubini_aQ_snd hs j hΦc)
      _ = ∑ j : Fin N2, ∫ u in abox N1 s,
              (∫ w in abox N2 s,
                (aQ s j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w)^2) := by
            apply Finset.sum_congr rfl
            intro j _
            apply integral_congr_ae
            filter_upwards with u
            apply integral_congr_ae
            filter_upwards with w
            rw [aQ_slice_snd]
      _ = ∫ u in abox N1 s, ∑ j : Fin N2,
              (∫ w in abox N2 s,
                (aQ s j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w)^2) :=
            (integral_finsetSum Finset.univ
              (fun j _ => integrableOn_slice_snd hs j hΦc)).symm
      _ = ∫ u in abox N1 s, cnPlus s (fun w => Φ (mergeBlock N1 N2 (u, w))) := rfl
  calc cnPlus s Φ
      = ∑ i : Fin (N1 + N2), ∫ x in abox (N1 + N2) s, (aQ s i Φ x)^2 := rfl
    _ = (∑ j : Fin N1, ∫ x in abox (N1 + N2) s, (aQ s (Fin.castAdd N2 j) Φ x)^2)
        + (∑ j : Fin N2, ∫ x in abox (N1 + N2) s, (aQ s (Fin.natAdd N1 j) Φ x)^2) :=
          Fin.sum_univ_add _
    _ = (∫ w in abox N2 s, cnPlus s (fun u => Φ (mergeBlock N1 N2 (u, w))))
        + (∫ u in abox N1 s, cnPlus s (fun w => Φ (mergeBlock N1 N2 (u, w)))) := by
          rw [hA, hB]

/-! ## The target -/

theorem slotSplit_cnPlus (s : ℝ) :
    @Work.KinPSuperadd.SlotSplit s
      (fun (N : ℕ) (Φ : Submission.BoseGases.X N → ℝ)
        => @Submission.BoseGases.cnPlus s N Φ) := by
  by_cases hs : 0 < s
  · refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      exact cnPlus_split_pos hs hΦ.continuous
    · intro N1 N2 Φ hΦ
      have h1 : (fun w : X N2 => cnPlus s (fun u => Φ (mergeBlock N1 N2 (u, w))))
          = (fun w : X N2 => ∑ j : Fin N1, (∫ u in abox N1 s,
              (aQ s j (fun u' => Φ (mergeBlock N1 N2 (u', w))) u)^2)) := rfl
      rw [h1]
      exact integrable_finsetSum Finset.univ
        (fun j _ => integrableOn_slice_fst (N1 := N1) (N2 := N2) hs j hΦ.continuous)
    · intro N1 N2 Φ hΦ
      have h1 : (fun u : X N1 => cnPlus s (fun w => Φ (mergeBlock N1 N2 (u, w))))
          = (fun u : X N1 => ∑ j : Fin N2, (∫ w in abox N2 s,
              (aQ s j (fun w' => Φ (mergeBlock N1 N2 (u, w'))) w)^2)) := rfl
      rw [h1]
      exact integrable_finsetSum Finset.univ
        (fun j _ => integrableOn_slice_snd (N1 := N1) (N2 := N2) hs j hΦ.continuous)
  · have hsle : s ≤ 0 := le_of_not_gt hs
    refine ⟨?_, ?_, ?_⟩
    · intro N1 N2 Φ hΦ
      simp [cnPlus_nonpos hsle]
    · intro N1 N2 Φ hΦ
      simp [cnPlus_nonpos hsle]
    · intro N1 N2 Φ hΦ
      simp [cnPlus_nonpos hsle]

end Work.KinPSuperadd
