/-
# `BridgeSquare/Endgame.lean` — the last step: from the three fibre identities to the challenge theorem

This file contains the *assembly* of the whole project, from the single remaining mathematical
input — the three chain-level fibre identities `Work.BridgeSquare.SignedFibreIdentA/B/T` (proved in
the areas `fibreLoopIdentA`, `fibreLoopIdentB`, `planeIdentT`) — to the unconditional challenge
statement

  `∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere`.

The chain of implications is

```
SignedFibreIdentA/B/T ──► SubtorusBoundaries ──► SubtorusNull   (a)
                                                     │
                        cuspMap_surjective (c)       ▼
                            └──────────► cuspPair_surjective ──► hsurj, hker
                                                                   │
                             Work.Final.FinalInputsP  ◄─────────────┘
                                     │
                                     ▼
              Work.Final.aspherical_integer_homology_four_sphere_P
```

Nothing here is new mathematics: the point of the file is that every step is *named*, so that the
last input can be plugged in once (`finalInputsPOf`), and so that the residual is visibly a single
statement.  `SubtorusNull` is the null-homology `H_k(s_v) = 0` (`k = 1, 2`) of the fibre subtorus of
the `v`-th cusp; `SubtorusBoundaries` says that the three singular chains of `M̄` pushed forward from
the `Δ`-generators of `H_1(T²)`, `H_2(T²)` are boundaries.

## Why not the bridge square

The bridge square `Work.FinalWire.SquareOf` of the delivered `Work.FinalWire.pieceData_of
Work.MbarHomology.eA` is *not* provable: its `D.eN k` ends in the `Classical.choice`-witness
`(HomologyBiprod …).some`, so the square is independent of the axioms (see `NOTES.md` §2 —
`Work.BridgeSquare.pieceData_eN_unfold`, `squareAt_iff_conj`).  The redesign of
`Submission/Work/NOTES_LEAD_aspherical_bridge.md` replaces it by the two *properties* `hsurj`,
`hker` of the actual Mayer–Vietoris map, for which `Work.Final.FinalInputsP` is the wiring; the
consumer `Work.HomologyMV.mv_homology_of_props` builds the square for the opaque data by
construction, so no identification has to be exhibited.  This is strictly stronger: it makes the
challenge statement unconditional without any bridge square.
-/
import Mathlib
import Submission.Work.BridgeSquare.CuspSection
import Submission.Work.BridgeSquare.Data
import Submission.Work.BridgeSquare.FibreData
import Submission.Work.BridgeSquare.subtorusBoundaries_of_fibreIdent
import Submission.Work.BridgeSquare.cuspPair_surjective
import Submission.Work.BridgeSquare.hsurj_of_cuspPairSurj
import Submission.Work.BridgeSquare.hker_of_cuspPairSurj
import Submission.Work.BridgeSquare.subtorusNull_of_boundaries
import Submission.Work.BridgeSquare.FinalInputsPChallenge
import Submission.Work.FinalWire.Concrete
import Submission.Work.RTOwed.FinalInstance

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.BridgeSquare

noncomputable section

/-! ## §1  The three chain-level fibre identities, in the exact shape of their statements -/

/-- The singular `k`-chains of `M̄`. -/
abbrev MCh (k : ℕ) : ModuleCat ℤ := (singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).X k

/-- **The `κ_{v,2}`-fibre identity** (statement of the area `fibreLoopIdentA`): the `Δ`-generator
`a` of `H_1(T²)`, pushed to `M̄` along the subtorus map `F_v`, differs from the *cellular* fibre
loop `Gen.fibreLoop` (pushed through `Ψ_M`) by a boundary, up to sign. -/
def SignedFibreIdentA : Prop :=
  ∀ v : Fin 5, ∃ (s : ℤ) (y : ↥(MCh 2)),
    (s = 1 ∨ s = -1) ∧
    (singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1 y
      = singA v - s • (PsiM.f 1) (fibreLoopVec v 0)

/-- **The `κ_{v,3}`-fibre identity** (statement of the area `fibreLoopIdentB`). -/
def SignedFibreIdentB : Prop :=
  ∀ v : Fin 5, ∃ (s : ℤ) (y : ↥(MCh 2)),
    (s = 1 ∨ s = -1) ∧
    (singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1 y
      = singB v - s • (PsiM.f 1) (fibreLoopVec v 1)

/-- **The `κ_{v,2}∧κ_{v,3}`-plane identity** (statement of the area `planeIdentT`). -/
def SignedFibreIdentT : Prop :=
  ∀ v : Fin 5, ∃ (s : ℤ) (y : ↥(MCh 3)),
    (s = 1 ∨ s = -1) ∧
    (singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 3 2 y
      = singT v - s • (PsiM.f 2) (planeCycleVec v 0)

/-- **The single remaining mathematical input**: the three fibre identities. -/
def FibreIdents : Prop := SignedFibreIdentA ∧ SignedFibreIdentB ∧ SignedFibreIdentT

/-! ## §2  The fibre identities give the three boundary statements

This is `Work.BridgeSquare.subtorusBoundaries_of_fibreIdent` with the sign kept: the witness of the
signed identity is corrected by `s • Ψ_M(W)` instead of `Ψ_M(W)`, where `W` is the cellular
null-homology of the fibre loop (`Gen.fibreLoop_bd`, `Gen.planeCycle_bd`) and `Ψ_M` is a chain map
(`Work.BridgeSquare.PsiM_d_fibreWit`, `PsiM_d_planeWit`). -/

/-- Absorb the sign: the signed fibre identities imply the three boundary statements.

The two cases `s = 1` and `s = -1` are separated so that only `one_smul` / `neg_one_smul` (and no
`map_smul` across the `ℤ`-scalar instances of a `ModuleCat`) are used. -/
theorem subtorusBoundaries_of_signed
    (hA : SignedFibreIdentA) (hB : SignedFibreIdentB) (hT : SignedFibreIdentT) :
    SubtorusBoundaries := by
  have keyA : ∀ v : Work.Space.Cusp, ∃ (s : ℤ) (y : ↥(MCh 2)), (s = 1 ∨ s = -1) ∧
      ((singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1) y
        = singA v - s • (PsiM.f 1) (fibreLoopVec v 0) := hA
  have keyB : ∀ v : Work.Space.Cusp, ∃ (s : ℤ) (y : ↥(MCh 2)), (s = 1 ∨ s = -1) ∧
      ((singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 2 1) y
        = singB v - s • (PsiM.f 1) (fibreLoopVec v 1) := hB
  have keyT : ∀ v : Work.Space.Cusp, ∃ (s : ℤ) (y : ↥(MCh 3)), (s = 1 ∨ s = -1) ∧
      ((singCxFun.obj (TopCat.of Work.FoldInst.Mbar)).d 3 2) y
        = singT v - s • (PsiM.f 2) (planeCycleVec v 0) := hT
  intro v
  obtain ⟨sA, yA, hsA, hyA⟩ := keyA v
  obtain ⟨sB, yB, hsB, hyB⟩ := keyB v
  obtain ⟨sT, yT, hsT, hyT⟩ := keyT v
  refine ⟨?_, ?_, ?_⟩
  · rcases hsA with h | h
    · subst h
      refine ⟨yA + PsiM.f 2 (fibreWitVec v 0), ?_⟩
      rw [map_add, hyA, PsiM_d_fibreWit v 0, one_smul, sub_add_cancel]
    · subst h
      refine ⟨yA - PsiM.f 2 (fibreWitVec v 0), ?_⟩
      rw [map_sub, hyA, PsiM_d_fibreWit v 0, neg_one_zsmul, sub_eq_add_neg]
      abel
  · rcases hsB with h | h
    · subst h
      refine ⟨yB + PsiM.f 2 (fibreWitVec v 1), ?_⟩
      rw [map_add, hyB, PsiM_d_fibreWit v 1, one_smul, sub_add_cancel]
    · subst h
      refine ⟨yB - PsiM.f 2 (fibreWitVec v 1), ?_⟩
      rw [map_sub, hyB, PsiM_d_fibreWit v 1, neg_one_zsmul, sub_eq_add_neg]
      abel
  · rcases hsT with h | h
    · subst h
      refine ⟨yT + PsiM.f 3 (planeWitVec v 0), ?_⟩
      rw [map_add, hyT, PsiM_d_planeWit v, one_smul, sub_add_cancel]
    · subst h
      refine ⟨yT - PsiM.f 3 (planeWitVec v 0), ?_⟩
      rw [map_sub, hyT, PsiM_d_planeWit v, neg_one_zsmul, sub_eq_add_neg]
      abel

/-- **The three fibre identities give the single remaining input `SubtorusNull`.** -/
theorem subtorusNull_of_signed (hA : SignedFibreIdentA) (hB : SignedFibreIdentB)
    (hT : SignedFibreIdentT) : SubtorusNull (rt := Work.RTOwed.rtData) :=
  subtorusNull_of_boundaries (subtorusBoundaries_of_signed hA hB hT)

/-- The same, from the bundled statement. -/
theorem subtorusNull_of_fibreIdents (h : FibreIdents) : SubtorusNull (rt := Work.RTOwed.rtData) :=
  subtorusNull_of_signed h.1 h.2.1 h.2.2

/-! ## §3  The final wiring -/

/-- The concrete `eA` of the area `MbarHomology`, in the `EAConcrete` spelling. -/
abbrev mbarEA : Work.FinalWire.EAConcrete := Work.MbarHomology.eA

/-- The piece data of the concrete assembly. -/
abbrev pieceDataC : Work.HomologyIso.PieceData (rt := Work.RTOwed.rtData) :=
  Work.FinalWire.pieceData_of (rt := Work.RTOwed.rtData) mbarEA

/-- The surjectivity of the cusp pair, from `SubtorusNull`. -/
theorem cuspPair_surj_of_subtorusNull (hnull : SubtorusNull (rt := Work.RTOwed.rtData)) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 3 →
      Function.Surjective (cuspPair (rt := Work.RTOwed.rtData) k).hom :=
  fun k h1 h3 => cuspPair_surjective hnull k ⟨h1, h3⟩

/-- **`Work.Final.FinalInputsP` from `SubtorusNull`.**  This is the whole project in one
definition: the assembled space, the smoothness and the curvature bound are the delivered
instances, `L` is `Work.HomologyIso.mhatLES`, the two `Nonempty` identifications are the delivered
`Work.HomologyIso.eM`/`eN` of the piece data, and `hsurj`/`hker` come from the surjectivity of the
cusp pair, i.e. from (c) `Work.BridgeSquare.cuspMap_surjective` and (a) `SubtorusNull`. -/
@[instance_reducible]
def finalInputsPOf (hnull : SubtorusNull (rt := Work.RTOwed.rtData)) :
    Work.Final.FinalInputsP where
  rt := Work.RTOwed.rtData
  cov_smooth := inferInstance
  curvLe := Work.CurvModels.curvLe_of_models (rt := Work.RTOwed.rtData)
  L := Work.HomologyIso.mhatLES (rt := Work.RTOwed.rtData)
  eM := fun k => ⟨Work.HomologyIso.eM (rt := Work.RTOwed.rtData) pieceDataC k⟩
  eN := fun k => ⟨Work.HomologyIso.eN (rt := Work.RTOwed.rtData) pieceDataC k⟩
  hsurj := hsurj_of_cuspPairSurj
    (fun k => ⟨Work.HomologyIso.eM (rt := Work.RTOwed.rtData) pieceDataC k⟩)
    (fun k => ⟨Work.HomologyIso.eN (rt := Work.RTOwed.rtData) pieceDataC k⟩)
    (cuspPair_surj_of_subtorusNull hnull)
  hker := hker_of_cuspPairSurj
    (fun k => ⟨Work.HomologyIso.eM (rt := Work.RTOwed.rtData) pieceDataC k⟩)
    (fun k => ⟨Work.HomologyIso.eN (rt := Work.RTOwed.rtData) pieceDataC k⟩)
    (cuspPair_surj_of_subtorusNull hnull)
  hX := Work.HomologyIso.mhatLES_hX (rt := Work.RTOwed.rtData)

/-- **THE CHALLENGE THEOREM, unconditional as soon as `SubtorusNull` is proved.** -/
theorem aspherical_integer_homology_four_sphere_of_subtorusNull
    (hnull : SubtorusNull (rt := Work.RTOwed.rtData)) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  @Work.Final.aspherical_integer_homology_four_sphere_P (finalInputsPOf hnull)

/-- **THE CHALLENGE THEOREM, from the three chain-level fibre identities.** -/
theorem aspherical_integer_homology_four_sphere_of_fibreIdents
    (hA : SignedFibreIdentA) (hB : SignedFibreIdentB) (hT : SignedFibreIdentT) :
    ∃ M : Closed4Manifold, M.IsAspherical ∧ M.IsIntegerHomologySphere :=
  aspherical_integer_homology_four_sphere_of_subtorusNull
    (subtorusNull_of_signed hA hB hT)

end

end Work.BridgeSquare
