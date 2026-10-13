/-
  WilE7 (`Work.WilE7.BandAux.BandDefsTwo`): the semi-Pfaffian presentation of the *band cell*
  between two sheets belonging to **two different** strata.

  Given two strata `S₁ S₂ : Stratum p (m+1)` and a `SemiPf` set `Z` defining the base cell
  `C = π_p (connectedComponentIn Z.set u₀)`, together with continuous sheets
  `s₁ j : C → ℝ^{m+1}` covering `S₁.X.set` and `s₂ j : C → ℝ^{m+1}` covering `S₂.X.set`,
  the *two-strata band cell* between the sheets `i` (of `S₁`) and `j` (of `S₂`) is

    `bandtwo i j = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧
        (s₁ i (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) < (s₂ j (Fin.init y)) (Fin.last m)}`.

  This file builds the `SemiPf` set

    `bandS3two Z S₁ S₂ : SemiPf (bandDim p m)`

  which is the double fibre product `(Z ×_C S₁.X) ×_C (Z ×_C S₂.X)` — the two `Z`-blocks glued
  along the full diagonal, so that the two fibre products share their base — with an extra
  vertical coordinate `t`, cut by the two inequalities `v₂ < t < v₂'`.  It is the two-strata
  refinement of `Work.WilE7.bandS3` in `Submission/Work/WilE7/BandAux/BandDefs.lean`; the
  ambient coordinate layout (and hence `bandZ1`, `bandZ2`, `bandT`, `bandExtract`, `bandPerm`)
  is *identical*, only the fourth block is constrained by `S₂` instead of `S₁`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.BandAux.bandComponent

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open Work.WilE7 WilkiesDesign WilkiesDesign.E

/-! ## §1. The construction -/

/-- The fibre product `Z ×_{ℝ^p} S₁.X` and `Z ×_{ℝ^p} S₂.X`, glued along the diagonal of the
`Z`-coordinates: the two strata occupy the second and the fourth block. -/
noncomputable def bandW2two {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (S₁ S₂ : Stratum p (m + 1)) : SemiPf (bandK p m) :=
  fiberProdZ (p := p + (m + 1)) (q := p + (m + 1)) (bandW1 Z S₁) (bandW1 Z S₂)

/-- The double fibre product with the vertical coordinate appended. -/
noncomputable def bandPaddedtwo {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (S₁ S₂ : Stratum p (m + 1)) : SemiPf (bandDim p m) :=
  SemiPf.prod (bandW2two Z S₁ S₂) bandCube1

/-- The `SemiPf` set of the two-strata band: the double fibre product with the vertical
coordinate, cut by `v₂ < t < v₂'`. -/
noncomputable def bandS3two {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (S₁ S₂ : Stratum p (m + 1)) : SemiPf (bandDim p m) :=
  SemiPf.addConds (bandPaddedtwo Z S₁ S₂) []
    [bandPlow p m (bandPaddedtwo Z S₁ S₂).r, bandPhigh p m (bandPaddedtwo Z S₁ S₂).r]

/-- Reindexing `bandS3two` along a permutation of the ambient coordinates does not change its
format (the ambient dimension is preserved: `(p+1) + bandFib p m = bandDim p m`). -/
theorem bandS3two_reindex_fmt {p m : ℕ} (Z : SemiPf (p + (m + 1)))
    (S₁ S₂ : Stratum p (m + 1)) (e : Fin (bandDim p m) ≃ Fin ((p + 1) + bandFib p m)) :
    (SemiPf.reindex e (bandS3two Z S₁ S₂)).fmt = (bandS3two Z S₁ S₂).fmt := by
  simp only [SemiPf.fmt, SemiPf.reindex, bandFib, bandDim, bandK]
  omega

/-! ## §2. The point set -/

theorem bandPaddedtwo_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S₁ S₂ : Stratum p (m + 1)) :
    (bandPaddedtwo Z S₁ S₂).set = {w : Fin (bandDim p m) → ℝ |
      projFirst (bandK p m) 1 w ∈ (bandW2two Z S₁ S₂).set ∧
      projSnd (bandK p m) 1 w ∈ cubeC 1} := by
  rw [bandPaddedtwo, prodSet, bandCube1_set]

theorem bandW2two_eq {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S₁ S₂ : Stratum p (m + 1))
    (u : Fin (bandK p m) → ℝ) :
    u ∈ (bandW2two Z S₁ S₂).set ↔
      projFirst ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
          u ∈ (bandW1 Z S₁).set ∧
      projSnd ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1)))
          u ∈ (bandW1 Z S₂).set ∧
      projFirst (p + (m + 1)) (p + (m + 1))
          (projFirst ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1))) u) =
        projFirst (p + (m + 1)) (p + (m + 1))
          (projSnd ((p + (m + 1)) + (p + (m + 1))) (p + (m + 1) + (p + (m + 1))) u) := by
  rw [bandW2two, fiberProdZ_set (p := p + (m + 1)) (q := p + (m + 1)) (bandW1 Z S₁)
    (bandW1 Z S₂)]
  rfl

/-- **The point set of `bandS3two`.**  Membership is: `z₁, z₁' ∈ Z.set`, `z₂ ∈ S₁.X.set`,
`z₂' ∈ S₂.X.set`, both fibres over the same base as `z₁` (via the diagonal `z₁ = z₁'`),
`|t| ≤ 1` and `v₂ < t < v₂'`. -/
theorem bandS3two_mem_iff {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S₁ S₂ : Stratum p (m + 1))
    (w : Fin (bandDim p m) → ℝ) :
    w ∈ (bandS3two Z S₁ S₂).set ↔
      bandZ1 w ∈ Z.set ∧ bandZ2 w ∈ S₁.X.set ∧ bandZ1' w ∈ Z.set ∧ bandZ2' w ∈ S₂.X.set ∧
      projFirst p (m + 1) (bandZ1 w) = projFirst p (m + 1) (bandZ2 w) ∧
      projFirst p (m + 1) (bandZ1' w) = projFirst p (m + 1) (bandZ2' w) ∧
      bandZ1 w = bandZ1' w ∧
      |bandT w| ≤ 1 ∧ bandV2 w < bandT w ∧ bandT w < bandV2' w := by
  rw [bandS3two, SemiPf.addConds_set]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.not_mem_nil, IsEmpty.forall_iff,
    List.mem_cons, forall_eq_or_imp, forall_const, and_true]
  rw [eaEval_bandPlow, eaEval_bandPhigh]
  rw [bandPaddedtwo_eq]
  simp only [Set.mem_ofPred_eq]
  rw [bandW2two_eq]
  rw [bandW1_eq, bandW1_eq]
  rw [bandZ1_projFirst, bandZ2_projSnd, bandZ1'_projFirst, bandZ2'_projSnd]
  rw [bandT_eq, mem_cubeC_one]
  simp only [sub_pos] at *
  tauto

/-! ## §3. The parametrised points of `bandS3two` -/

/-- The parametrised point lies in `bandS3two` whenever its data satisfy the two sheet
conditions (one for each stratum) and the strict inequalities. -/
theorem bandPt_mem_two {p m : ℕ} (Z : SemiPf (p + (m + 1))) (S₁ S₂ : Stratum p (m + 1))
    (u : Fin (p + (m + 1)) → ℝ) (hu : u ∈ Z.set) (v v' : Fin (m + 1) → ℝ) (t : ℝ)
    (hv : Fin.append (projFirst p (m + 1) u) v ∈ S₁.X.set)
    (hv' : Fin.append (projFirst p (m + 1) u) v' ∈ S₂.X.set)
    (ht : |t| ≤ 1) (h1 : v (Fin.last m) < t) (h2 : t < v' (Fin.last m)) :
    bandPt u v v' t ∈ (bandS3two Z S₁ S₂).set := by
  rw [bandS3two_mem_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [bandZ1_bandPt]
  · rwa [bandZ2_bandPt]
  · rwa [bandZ1'_bandPt]
  · rwa [bandZ2'_bandPt]
  · rw [bandZ1_bandPt, bandZ2_bandPt, projFirst_append]
  · rw [bandZ1'_bandPt, bandZ2'_bandPt, projFirst_append]
  · rw [bandZ1_bandPt, bandZ1'_bandPt]
  · rw [bandT_bandPt]; exact ht
  · rw [bandV2_bandPt, bandT_bandPt]; exact h1
  · rw [bandT_bandPt, bandV2'_bandPt]; exact h2

end Work.WilE7
