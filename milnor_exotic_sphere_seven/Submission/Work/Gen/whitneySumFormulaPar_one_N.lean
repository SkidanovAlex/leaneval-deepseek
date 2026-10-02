import Mathlib
import Submission.Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines
import Submission.Work.Kunneth.kunnethCP
import Submission.Work.LerayHirsch.exists_tautSection
import Submission.Work.Whitney.SectionStability
import Submission.Work.Gen.chernRootTwistTop
import Submission.Work.Gen.eSymDef
import Submission.Work.Gen.chernRoot_split
import Submission.Work.Gen.cruxUpToConstant_of_root
import Submission.Work.Gen.splitCruxConstant_eq_one
import Submission.Work.Gen.whitneySumFormulaPar_one_N_of_splitCrux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Gen

/-!
# The `(1,N)` family of the Whitney sum formula over paracompact Hausdorff bases

## State of this module (see `NOTES_whitney_one_N.md` in this directory for the full analysis)

The target `Work.Gen.whitneySumFormulaPar_one_N` is **equivalent**, given the lemmas already proved
in this workspace, to the *split case* `Work.LerayHirsch.WhitneySumFormulaSplit` — the Whitney
formula for a complex line bundle and an explicit iterated direct sum of complex line bundles over a
paracompact Hausdorff base.

The equivalence is proved in the tree in both directions:

* `Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines` (proved, axiom-clean; its two side
  conditions `Work.LerayHirsch.KunnethCP` and the paracompactness of the projectivisation are
  `Work.Kunneth.kunnethCP` and `Work.LerayHirsch.paracompactSpace_projSpace`) — the split case
  implies the whole `(1,N)` family, by pulling back along the flag bundle of the second summand and
  reading the identity back with the injectivity of `π^*` (Leray–Hirsch).  This reduction is
  `whitneySumFormulaPar_one_N_of_splitLines` below.
* conversely the split case is the instance `Z₂ = lineSumCore n M` of the target.

## Which degrees are available, and where the content is

Write `(m₁,m₂)@k` for the Whitney formula in degree `k`.

* `(1,N)@0`: trivial.
* `(1,N)@k`, `1 ≤ k ≤ N-1`: from `(1,k)@k` by iterated *peeling*
  (`Work.Gen.chernClass_whitneySum_peelStep_snd`, packaged as
  `Work.Gen.chernClass_whitneySum_one_family`, proved).
* `(1,N)@(N+1)` (the **top** degree): `Work.Whitney.chernClass_whitneySum_top`
  (= `Work.Whitney.TopClassMul`), proved and axiom-clean in this tree.
* `(1,N)@k`, `k ≥ N+2`: both sides vanish.

So the *single* remaining degree is `k = N`, i.e.

  `Core(N)`:  `c_N(L ⊕ F) = c_N(F) + c₁(L) ⌣ c_{N-1}(F)` for `rank F = N`,

which is exactly the split case (equivalently: `c(⊕ᵢ Lᵢ) = ∏ᵢ (1 + c₁(Lᵢ))`).
The proof of `Core(N)` needs the multiplicativity of the total Chern class beyond the top degree;
the obstruction and the partial results obtained (descent + Gysin divisibility; the `ℂP¹`
coefficient-extraction trick, which is circular with the twist formula) are recorded in
`NOTES_whitney_one_N.md`.
-/

noncomputable section

open Work.TangentClasses Work.Thom

/-- **The `(1,N)` family of the Whitney sum formula, from the split case.**

This is the (proved) bridge `Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines` of the
LERAYHIRSCH chapter, with its two side conditions discharged from the tree: `KunnethCP` is
`Work.Kunneth.kunnethCP` (KUNNETH chapter) and the paracompactness of a projectivisation is
`Work.LerayHirsch.paracompactSpace_projSpace`. -/
theorem whitneySumFormulaPar_one_N_of_splitLines
    (hsplit : Work.LerayHirsch.WhitneySumFormulaSplit) :
    ∀ N : ℕ, Work.LerayHirsch.WhitneySumFormulaPar 1 N :=
  Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines Work.Kunneth.kunnethCP
    (fun Z => Work.LerayHirsch.paracompactSpace_projSpace Z) hsplit


/-- **The Chern-root relation in the form consumed by the `ψ`-analysis**, for every `n`
(the case `n = 0` is degenerate: the projectivisation of the rank-`0` bundle is empty and the
left-hand side is an empty sum, so both sides lie in a subsingleton). -/
theorem chernRoot_split_all {n : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    [T2Space B] {ι : Type} [Fintype ι]
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.LerayHirsch.lhMap (Work.LerayHirsch.lineSumCore n M) n
        (fun i => ((-1 : ℤ) ^ (n + 1 + (i : ℕ))) • Work.Gen.eSym n M (n - (i : ℕ)))
      = Work.LerayHirsch.zetaPow (Work.LerayHirsch.lineSumCore n M) n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    -- `n = 0`: the projectivisation of the rank-`0` bundle is empty (its punctured total space is,
    -- because the fibre is the zero space), so both sides lie in a subsingleton.
    have hempty : IsEmpty ↥(Work.Thom.zeroComplement
        (Work.Thom.realification (Work.LerayHirsch.lineSumCore 0 M))) :=
      ⟨fun p => (Work.Thom.mem_zeroComplement p.1).mp p.2 (Subsingleton.elim _ _)⟩
    have hP : IsEmpty (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore 0 M)) :=
      ⟨fun q => Quotient.inductionOn q (fun p => isEmptyElim p)⟩
    have hS : Subsingleton (Work.Thom.Coh ℤ (2 * 0)
        (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore 0 M))) :=
      Work.LerayHirsch.subsingleton_cohomology_of_isEmpty 0
    rw [Work.LerayHirsch.lhMap_apply, Work.LerayHirsch.zetaPow_zero, Finset.sum_eq_zero]
    · exact Subsingleton.elim _ _
    · intro x hx
      simp at hx
  · exact Work.Gen.chernRoot_split hn M

/-- **The split crux**: for `n` complex line bundles over a paracompact Hausdorff base, the
second-highest Chern class of their direct sum is the `(n-1)`-st elementary symmetric class of the
first Chern classes.  Assembled from `Work.Gen.cruxUpToConstant_of_root` (the `ψ`-analysis, which
pins the class up to a universal constant `δ n`) and `Work.Gen.splitCruxConstant_eq_one` (the test
on the tautological hyperplane class over `P(ℂ^n)`, which evaluates that constant to `1`). -/
theorem splitCrux (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
      = Work.Gen.eSym n M (n - 1) := by
  obtain ⟨δ, hδ⟩ := Work.Gen.cruxUpToConstant_of_root (fun n => chernRoot_split_all)
  have h1 : ∀ m : ℕ, δ m = 1 := Work.Gen.splitCruxConstant_eq_one δ hδ
  rw [hδ n M, h1 n, one_zsmul]

theorem whitneySumFormulaPar_one_N :
    ∀ N : ℕ, Work.LerayHirsch.WhitneySumFormulaPar 1 N :=
  Work.Gen.whitneySumFormulaPar_one_N_of_splitCrux (fun n => splitCrux n)

end

end Work.Gen
