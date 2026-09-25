import Mathlib
import Submission.Work.Tower.MinkowskiGS.Defs
import Submission.Work.CFT.MinkowskiCut
import Submission.Work.CFT.Kummer.All
import Submission.Work.CFT.KochTransfer.kochTransfer

/-!
# From Koch's fact (a) to the class-group relation bound

`Work.CFT.MinkowskiCut.finrank_H2Fp_le_classGroupRank_add_two_of_totallyReal_cubic` says that for a
totally real cubic field `F`, Koch's fact (a) for **any** abstract group `G` (a group with an
injective Shafarevich map `H²(G,𝔽₃) ↪ 𝓒_∅`) gives

`dim_{𝔽₃} H²(G,𝔽₃) ≤ dim_{𝔽₃} Cl_F[3] + 2`.

This file packages that observation into the form consumed by the tower endgame
(`Work.Tower.MinkowskiGS.ClassGroupRelationBound`) by two routes:

* directly, from `KochInjectionInput` — fact (a) at the finite maximal `T`-split level, where the
  group is `Gal(K/F)` itself
  (`Work.Tower.MinkowskiGS.classGroupRelationBound_of_kochInjectionInput`);

* from `AbstractKochInput` — the `∃ G` form of fact (a) plus the (non-arithmetic) group-theoretic
  cutting data `KochTransfer 3 G` and `SplittingCut F G`, which identify the maximal `T`-split
  group `Gal(K/F)` with `G ⧸ N` for the normal closure `N` of at most `|T|` elements and count the
  cost in relations
  (`Work.Tower.MinkowskiGS.classGroupRelationBound_of_abstractKochInput`).

In both cases the only arithmetic input is Koch's fact (a): no class-group rank formula (b′), and
hence no Artin reciprocity, is used.
-/

open NumberField
open scoped Classical nonZeroDivisors

noncomputable section

namespace Work
namespace Tower
namespace MinkowskiGS

open Work.CFT.ShafarevichCore

/-- **Fact (a) at the finite maximal `T`-split level implies the class-group relation bound.**

For the maximal `T`-split finite level `K`, fact (a) gives
`H²(Gal(K/F), 𝔽₃) ↪ 𝓒_∅`, whence (proved Kummer computation + Dirichlet for a totally real cubic
field) `dim H² ≤ dim Cl_F[3] + 2`; adding the `|T|` of the Frobenius classes is free here. -/
theorem classGroupRelationBound_of_kochInjectionInput (h : KochInjectionInput) :
    ClassGroupRelationBound := by
  intro F _ _ _ hdeg K _ _ _ _ _ hKur h3 T hfrob hmax
  have hb := Work.CFT.MinkowskiCut.finrank_H2Fp_le_classGroupRank_add_two_of_totallyReal_cubic
    F hdeg (Gal(K/F)) (h F hdeg K hKur h3 T hfrob hmax)
  exact le_trans hb (Nat.le_add_right _ _)

/-- **The `∃ G` form of fact (a) plus the cutting data implies the class-group relation bound.**

This is the `Work.CFT.MinkowskiCut`-style reduction with the abstract group `G` of
`AbstractKochInput`: fact (a) bounds `dim H²(G,𝔽₃) ≤ dim Cl_F[3] + 2`, the cutting identifies the
maximal `T`-split level with `G ⧸ N` (`N` the normal closure of `k ≤ |T|` elements, generator rank
preserved), and Koch's transfer adds the `k` relations. -/
theorem classGroupRelationBound_of_abstractKochInput (h : AbstractKochInput) :
    ClassGroupRelationBound := by
  intro F _ _ _ hdeg K _ _ _ _ _ hKur h3 T hfrob hmax
  obtain ⟨G, instG, hKoch, hinj, hcut⟩ := h F hdeg
  letI := instG
  obtain ⟨N, hN, k, g, hk, hNg, _hgen, ⟨e⟩⟩ := hcut K hKur h3 T hfrob hmax
  haveI := hN
  -- fact (a) for `G`, via `MinkowskiCut`
  have hG : Module.finrank (ZMod 3) (Work.CFT.Kummer.H2Fp 3 G) ≤
      Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) + 2 :=
    Work.CFT.MinkowskiCut.finrank_H2Fp_le_classGroupRank_add_two_of_totallyReal_cubic
      F hdeg G hinj
  -- Koch's transfer: killing `k` elements of `G` adds at most `k` relations
  have h1 : Module.finrank (ZMod 3) (Work.CFT.Kummer.H2Fp 3 (G ⧸ N)) ≤
      Module.finrank (ZMod 3) (Work.CFT.Kummer.H2Fp 3 G) + k := hKoch N k g hNg
  -- transport along `G ⧸ N ≃* Gal(K/F)`
  have h2 : Module.finrank (ZMod 3) (Work.CFT.Kummer.H2Fp 3 (G ⧸ N)) =
      Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) := by
    rw [Work.Tower.Shafarevich.proPRelationRank]
    exact Work.CFT.Kummer.finrank_H2Fp_mulEquiv e
  have h3 : Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F)) ≤
      Module.finrank (ZMod 3) (Work.CFT.Kummer.H2Fp 3 G) + k := by
    rw [← h2]; exact h1
  calc Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F))
      ≤ Module.finrank (ZMod 3) (Work.CFT.Kummer.H2Fp 3 G) + k := h3
    _ ≤ (Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) + 2) + k :=
        Nat.add_le_add_right hG k
    _ ≤ Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) + 2 + T.card := by
        omega

end MinkowskiGS
end Tower
end Work
