import Mathlib
import Submission.Work.Drive.encodedGenericAlt
import Submission.Work.Drive.refTripleClause
import Submission.Work.Drive.endsHomotopyClauses
import Submission.Work.Drive.classTripleOdd
import Submission.Work.Drive.exists_linPlaneCharts_hgen
import Submission.Work.Drive.endTripleReg_cyclic

/-!
# A **clean** copy of `hasClassLinearization_of_endData` (`Drive/hasClassLinearizationAlt.lean`)

Verbatim copy of `Submission/Work/Drive/hasClassLinearization_of_endData.lean` with the single
research input §2.1 replaced by its **proved** version
`Work.Drive.exists_homotopy_meet3Hyp_encodedAlt` (`Drive/encodedGenericAlt.lean`).  The original file
calls the `sorry`-stub `Work.Drive.exists_homotopy_meet3Hyp_encoded` (`Drive/encodedGeneric.lean`), so
its `#print axioms` contains `sorryAx`; this copy is **axiom-clean**, and therefore usable on the
critical path (`Work.Drive.exists_classRowFamily`, the `hn2` producer) until the stub itself is
replaced.  All the auxiliary declarations are renamed with the suffix `Alt` to avoid a clash with the
original when both are imported.  Owner of the original: the `hodd` lane.
-/

/-!
# The assembly of `HasClassLinearization` from the class-level end data (`NOTES_LEAD_hodd_blockT6.md` §2.5)

**Statement stub.**  The three clauses of `Work.Drive.HasClassLinearization` are handled by
`Work.Drive.exists_homotopy_meet3Hyp_encodedAlt` (§2.1) applied to the three *clause homotopies*
`clauseHomot P Ξ t φ c hc H0 k` of `refTripleClause.lean`:

| clause `l` | loop chart `A` | plane chart `B` | the two ends of `clauseHomot · l` |
| --- | --- | --- | --- |
| `0` | `P̂₁` | `P̂₂` | `P̂₀` (at `s = 0`) and `lin₀` (at `s = 1`) |
| `1` | `lin₀` | `P̂₂` | `P̂₁` and `lin₁` |
| `2` | `lin₁` | `lin₀` | `P̂₂` and `lin₂` |

where `P̂ k = planeClassMap (pertChart Ξ (P k) (blk k t))` (the perturbed design plane) and
`lin k = planeClassMap (diskPlane (linPlaneChart (φ k) c hc))`.  The hypotheses are the class-level
regularities of the seven pairs/triples that occur (the lead's list:
`PairReg P̂₁P̂₂`, `lin₀P̂₂`, `lin₀lin₁`; `EndTripleReg {P̂₀P̂₁P̂₂}`, `{lin₀P̂₁P̂₂}`, `{lin₁lin₀P̂₂}`,
`{lin₂lin₀lin₁}`); `EndTripleReg` is fully symmetric in its three arguments (it is cyclic —
`Drive/endTripleReg_cyclic` — and it transposes), which covers the reorderings the three clauses need.

Besides them the assembly carries the **fold data** of the two families of presentations
(`NOTES_LEAD_hodd_faces.md` §1–§2): `hPfold : ∀ k, FoldFlat (P̂ k)` for the perturbed design planes and
`hLfold : ∀ k, FoldFlat (lin k)` for the linear disk models.  Each is a **theorem** in the design
(`mfderiv_planeClassMap_chartPert_diskPlane_single` resp. `mfderiv_planeClassMap_diskPlane_single`),
so the producer discharges them; the three clauses consume the twelve instantiations
`(FoldFlat A, FoldFlat B, FoldFlat (end at 0), FoldFlat (end at 1))`.

The conclusion is `HasClassLinearization P′` for `P′ k = pertChart Ξ (P k) (blk k t)`, hence
`Odd (classTripleSet P′).ncard` by `Work.Drive.odd_ncard_classTripleSet_of_hasClassLinearization`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
attribute [local instance] Work.Drive.projTimesLineCharted
  Work.Drive.isManifold_projTimesLineCharted

/-! ## 0. Two permutation lemmas for the class-level regularities -/

section

set_option backward.isDefEq.respectTransparency false

/-- **`PairReg` is symmetric** in its two arguments (the union of the two ranges is commutative and the
common-value condition is symmetric). -/
theorem pairReg_commAltAlt {A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : Work.Drive.PairReg A B) : Work.Drive.PairReg B A := by
  intro y y' hyy
  rw [sup_comm]
  exact h y' y hyy.symm

/-- **`EndTripleReg` is invariant under the swap of its last two arguments**; with
`Work.Drive.endTripleReg_cyclic` this generates all six reorderings of the three class maps (the
conditions are conjunctions which are symmetric in the three slots). -/
theorem endTripleReg_swap23Alt {F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : Work.Drive.EndTripleReg F A B) : Work.Drive.EndTripleReg F B A := by
  intro y₀ y₁ y₂ hFB hFA
  obtain ⟨hF, hA, hB, hI⟩ := h y₀ y₂ y₁ hFA hFB
  exact ⟨hF, hB, hA, by rw [← hI]; ac_rfl⟩

/-- The two parametrisations of the plane square agree (`pt2` of `meet32_bordism_invariance` and
`mk2` of the disk presentations).  Local copy, because `Drive/meet3Hyp_encodedChains.lean` (which holds
`pt2_eq_mk2`) declares `mk3` and cannot be imported together with `classTripleOdd`. -/
theorem pt2_eq_mk2_localAltAlt (a b : ℝ) : pt2 a b = mk2 a b := by
  ext i
  fin_cases i <;> simp [pt2, mk2]

end

/-- **`HasClassLinearization` from the class-level end data** (`NOTES_LEAD_hodd_blockT6.md` §2.5). -/
theorem hasClassLinearization_of_endDataAlt
    (Q₀ : ℂ → CappingSpace) (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hP : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P k))
    (hPseam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → P k (seamInv2 y) = P k y)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (hΞ : ChartPert Q₀ 4 Ξ)
    (t : EuclideanSpace ℝ (Fin 12))
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (φ k) c hc z ≠ linCommonPt φ c hc hrank)
    (H0 : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (hH0sm : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (clauseB H0 k))
    (hH00 : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      H0 k (0, y) = planeClassMap (P k) y)
    (hH01 : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      H0 k (1, y) = planeClassMap (diskPlane (linPlaneChart (φ k) c hc)) y)
    (hH0seam : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
      onSeam2 y → H0 k (s, seamInv2 y) = H0 k (s, y))
    {c₀ : ℝ} (hc₀0 : 0 < c₀) (hc₀1 : c₀ < 1)
    (hpair12 : PairReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))))
    (hpairL0P2 : PairReg (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))))
    (hpairL0L1 : PairReg (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))))
    (hend012 : EndTripleReg (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 0 t) (P 0 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))))
    (hendL012 : EndTripleReg (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))))
    (hendL10P2 : EndTripleReg (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))))
    (hendLLL : EndTripleReg (planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))))
    (hPfold : ∀ k : Fin 3,
      FoldFlat (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y))))
    (hLfold : ∀ k : Fin 3,
      FoldFlat (planeClassMap (diskPlane (linPlaneChart (φ k) c hc)))) :
    HasClassLinearization (fun k y => Ξ (blk k t) (P k y)) := by
  -- ## the two families of class maps: the perturbed design planes and the linear disk models
  have hPhat : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y))) := by
    intro k y
    exact contMDiffAt_cls_of_contMDiff_gen (k := 2)
      (hΞ.2.1.comp (contMDiff_const.prodMk (hP k))) y
  have hLin : ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (planeClassMap (diskPlane (linPlaneChart (φ k) c hc))) :=
    fun k y => contMDiffAt_cls_of_contMDiff_gen
      (contMDiff_diskPlane (linPlaneChart_contMDiff (φ k) c hc)) y
  have hPhat_seam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      planeClassMap (fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y')) (seamInv2 y)
        = planeClassMap (fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk k t) (P k y')) y := by
    intro k y hy
    simp only [planeClassMap]
    rw [hPseam k y hy]
  have hLin_seam : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      planeClassMap (diskPlane (linPlaneChart (φ k) c hc)) (seamInv2 y)
        = planeClassMap (diskPlane (linPlaneChart (φ k) c hc)) y := by
    intro k y hy
    simp only [planeClassMap]
    rw [diskPlane_seamInv2 (Q := linPlaneChart (φ k) c hc)
      (fun z hz => linPlaneChart_neg (φ k) c hc hz) hy]
  -- ## the chain smoothness of the clause homotopies
  have hchain : ∀ k : Fin 3, ContMDiff (𝓡 3) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 3) => clauseHomot P Ξ t φ c hc H0 k (x 2, mk2 (x 0) (x 1))) := by
    intro k
    have hfun : (fun x : EuclideanSpace ℝ (Fin 3) =>
        clauseHomot P Ξ t φ c hc H0 k (x 2, mk2 (x 0) (x 1)))
        = clauseChain P Ξ t φ c hc H0 k := by
      funext x
      exact clauseHomot_chain P Ξ t φ c hc H0 k x
    rw [hfun]
    exact contMDiff_clauseChain P Ξ t φ c hc H0 k hP hΞ (hH0sm k) hΞ.1 (hH00 k) (hH01 k)
  -- ## the clause homotopies are constant for `s ≤ 0` and for `s ≥ 1`
  have hHom0 : ∀ (k : Fin 3) (s : ℝ), s ≤ 0 → ∀ y : EuclideanSpace ℝ (Fin 2),
      clauseHomot P Ξ t φ c hc H0 k (s, y) = clauseHomot P Ξ t φ c hc H0 k (0, y) := by
    intro k s hs y
    simp only [clauseHomot, if_pos (show s ≤ 1 / 3 by linarith),
      if_pos (show (0 : ℝ) ≤ 1 / 3 by norm_num), Prod.fst, Prod.snd,
      mul_zero, sub_zero, one_smul, clauseRho_one,
      clauseRho_eq_one (show (9 : ℝ) / 10 ≤ 1 - 3 * s by linarith)]
  have hHom1 : ∀ (k : Fin 3) (s : ℝ), 1 ≤ s → ∀ y : EuclideanSpace ℝ (Fin 2),
      clauseHomot P Ξ t φ c hc H0 k (s, y) = clauseHomot P Ξ t φ c hc H0 k (1, y) := by
    intro k s hs y
    simp only [clauseHomot, if_neg (show ¬ (s ≤ 1 / 3) by linarith),
      if_neg (show ¬ ((1 : ℝ) ≤ 1 / 3) by norm_num),
      if_neg (show ¬ (s ≤ 2 / 3) by linarith),
      if_neg (show ¬ ((1 : ℝ) ≤ 2 / 3) by norm_num), Prod.fst, Prod.snd]
  -- ## the end-triple data, in the form the homotopy-genericity lemma consumes
  have h012 : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) =>
        clauseHomot P Ξ t φ c hc H0 0 (0, y))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) := by
    simpa only [clauseHomot_zero P Ξ t φ c hc H0 0] using hend012
  have hL012 : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) =>
        clauseHomot P Ξ t φ c hc H0 0 (1, y))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) := by
    simpa only [clauseHomot_one P Ξ t φ c hc H0 0] using hendL012
  -- clause `1`: the reorderings of the two triples `{P̂₁,lin₀,P̂₂}` and `{lin₁,lin₀,P̂₂}`
  have hP1L0P2 : Work.Drive.EndTripleReg
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) :=
    endTripleReg_swap23Alt (endTripleReg_cyclic hendL012)
  have hL10P2 : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) =>
        clauseHomot P Ξ t φ c hc H0 1 (0, y))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) := by
    simpa only [clauseHomot_zero P Ξ t φ c hc H0 1] using hP1L0P2
  have hL10P2' : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) =>
        clauseHomot P Ξ t φ c hc H0 1 (1, y))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) := by
    simpa only [clauseHomot_one P Ξ t φ c hc H0 1] using hendL10P2
  -- clause `2`: the reorderings of the two triples `{P̂₂,lin₀,lin₁}` and `{lin₂,lin₀,lin₁}`
  have hP2L0L1 : Work.Drive.EndTripleReg
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y)))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))) :=
    endTripleReg_swap23Alt (endTripleReg_cyclic (endTripleReg_cyclic hendL10P2))
  have hP2L0L1' : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) =>
        clauseHomot P Ξ t φ c hc H0 2 (0, y))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))) := by
    simpa only [clauseHomot_zero P Ξ t φ c hc H0 2] using hP2L0L1
  have hLLL : Work.Drive.EndTripleReg (fun y : EuclideanSpace ℝ (Fin 2) =>
        clauseHomot P Ξ t φ c hc H0 2 (1, y))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))) := by
    simpa only [clauseHomot_one P Ξ t φ c hc H0 2] using hendLLL
  -- ## the fold data of the two ends of each clause homotopy
  have hHomfold0 : ∀ k : Fin 3, FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) =>
      clauseHomot P Ξ t φ c hc H0 k (0, y)) := by
    intro k
    rw [clauseHomot_zero P Ξ t φ c hc H0 k]
    exact hPfold k
  have hHomfold1 : ∀ k : Fin 3, FoldFlat (fun y : EuclideanSpace ℝ (Fin 2) =>
      clauseHomot P Ξ t φ c hc H0 k (1, y)) := by
    intro k
    rw [clauseHomot_one P Ξ t φ c hc H0 k]
    exact hLfold k
  -- ## the three applications of the homotopy-genericity lemma
  -- clause `0`: the loop chart is `P̂₁`, the plane chart `P̂₂`
  obtain ⟨Ha, hHa0, hHa1, hMa⟩ := exists_homotopy_meet3Hyp_encodedAlt
    (H := clauseHomot P Ξ t φ c hc H0 0)
    (A := planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
    (B := planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y)))
    hc₀0 hc₀1 (hchain 0) (hPhat 1) (hPhat 2)
    (fun s y hy => clauseHomot_seam P Ξ t φ c hc H0 0 hPseam (hH0seam 0) hy)
    (hPhat_seam 1) (hPhat_seam 2) (hHom0 0) (hHom1 0) hpair12 h012 hL012
    (hPfold 1) (hPfold 2) (hHomfold0 0) (hHomfold1 0)
  -- clause `1`: the loop chart is `lin₀`, the plane chart `P̂₂`
  obtain ⟨Hb, hHb0, hHb1, hMb⟩ := exists_homotopy_meet3Hyp_encodedAlt
    (H := clauseHomot P Ξ t φ c hc H0 1)
    (A := planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
    (B := planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y)))
    hc₀0 hc₀1 (hchain 1) (hLin 0) (hPhat 2)
    (fun s y hy => clauseHomot_seam P Ξ t φ c hc H0 1 hPseam (hH0seam 1) hy)
    (hLin_seam 0) (hPhat_seam 2) (hHom0 1) (hHom1 1) hpairL0P2 hL10P2 hL10P2'
    (hLfold 0) (hPfold 2) (hHomfold0 1) (hHomfold1 1)
  -- clause `2`: the loop chart is `lin₁`, the plane chart `lin₀`
  obtain ⟨Hc, hHc0, hHc1, hMc⟩ := exists_homotopy_meet3Hyp_encodedAlt
    (H := clauseHomot P Ξ t φ c hc H0 2)
    (A := planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
    (B := planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)))
    hc₀0 hc₀1 (hchain 2) (hLin 0) (hLin 1)
    (fun s y hy => clauseHomot_seam P Ξ t φ c hc H0 2 hPseam (hH0seam 2) hy)
    (hLin_seam 0) (hLin_seam 1)
    (hHom0 2) (hHom1 2) hpairL0L1 hP2L0L1' hLLL
    (hLfold 0) (hLfold 1) (hHomfold0 2) (hHomfold1 2)
  -- ## the assembly
  refine ⟨φ, c, hc, hrank, hgen, ![Ha, Hb, Hc], c₀, hc₀0, hc₀1, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    fin_cases k
    · funext y
      show Ha (0, y) = planeClassMap (fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk 0 t) (P 0 y')) y
      rw [hHa0 y]
      exact congrFun (clauseHomot_zero P Ξ t φ c hc H0 0) y
    · funext y
      show Hb (0, y) = planeClassMap (fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y')) y
      rw [hHb0 y]
      exact congrFun (clauseHomot_zero P Ξ t φ c hc H0 1) y
    · funext y
      show Hc (0, y) = planeClassMap (fun y' : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y')) y
      rw [hHc0 y]
      exact congrFun (clauseHomot_zero P Ξ t φ c hc H0 2) y
  · intro k
    fin_cases k
    · funext y
      show Ha (1, y) = planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)) y
      rw [hHa1 y]
      exact congrFun (clauseHomot_one P Ξ t φ c hc H0 0) y
    · funext y
      show Hb (1, y) = planeClassMap (diskPlane (linPlaneChart (φ 1) c hc)) y
      rw [hHb1 y]
      exact congrFun (clauseHomot_one P Ξ t φ c hc H0 1) y
    · funext y
      show Hc (1, y) = planeClassMap (diskPlane (linPlaneChart (φ 2) c hc)) y
      rw [hHc1 y]
      exact congrFun (clauseHomot_one P Ξ t φ c hc H0 2) y
  · show Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encodedChains
      (fun x => Ha (x 2, pt2 (x 0) (x 1)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 1 t) (P 1 y)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) c₀)
    exact hMa
  · show Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encodedChains
      (fun x => Hb (x 2, pt2 (x 0) (x 1)))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => Ξ (blk 2 t) (P 2 y))) c₀)
    exact hMb
  · show Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ) (encodedChains
      (fun x => Hc (x 2, pt2 (x 0) (x 1)))
      (planeClassMap (diskPlane (linPlaneChart (φ 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (φ 1) c hc))) c₀)
    exact hMc


end

end Work.Drive
