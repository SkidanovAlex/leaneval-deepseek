import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.EMFG.skeletonAux
import Submission.Work.EMFG.killChain
import Submission.Work.EMFG.skeletonKernelAndSurj
import Submission.Work.EMFG.commonPiOneKillConnected
import Submission.Work.EMFG.killChain_extend
import Submission.Work.Serre.SPC.piOne_killStep
import Submission.Work.Serre.SPC.skeleton_pathConnected
import Submission.Work.Serre.Assembly.serreK2IntSharp
import Submission.Work.Serre.Assembly.hZeroOfPiZeroInt
import Submission.Work.Serre.bijective_piMapN_of_joined
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.Stems.homotopyGroup_prod

set_option synthInstance.maxHeartbeats 400000


/-!
# The `k = 1` comparison step of the Serre finiteness argument

Let `A` be an abelian group, `N ≥ 2`, and let `Z` and `P` be two *range models* of `K(A,1)` up to
degree `N`, i.e. spaces all of whose homotopy groups in degrees `2, …, N` are trivial and whose `π₁`
is isomorphic to `A` (`Work.Serre.IsEMSpaceUpTo A 1 N`).  This file proves that their integral
homology in degrees `≤ N` agrees:

`∀ i ≤ N, HZ Z i ≅ HZ P i`,  where `HZ X i` is the `i`-th integral homology of `X`.

The argument is the classical one, in the style of Serre's comparison of two Postnikov-type models:

* the `1`-skeleton `Γ := Skeleton Z z₀` (a wedge of circles, one per based loop of `Z`) maps onto
  both `Z` and `P` — via `skeletonMap Z z₀` and via a loop map `skeletonLoopMap z₀ p₀ Λ` built out
  of the group isomorphism `Λ : π₁ Z ≃* π₁ P` furnished by the two model structures — with the same
  `π₁`-kernel (`Work.EMFG.skeletonKernelAndSurj`);
* the common kernel can be killed simultaneously for the two maps, giving a space `Y` with two
  `π₁`-bijections `Y → Z`, `Y → P` (`Work.EMFG.commonPiOneKillConnected`);
* both maps extend over the chain `killChain Y (N-1)` that kills `π₂, …, π_N`
  (`Work.EMFG.killChain_extend`), and on the resulting space the extensions induce isomorphisms on
  all `π_i`, `i ≤ N` (`Work.EMFG.piBij_killChain`);
* the `π`-isomorphism theorem for integral homology (`Work.Serre.Assembly.serreK2IntSharp`, with the
  degree-`0` case `Work.Serre.Assembly.hZeroOfPiZeroInt`) upgrades this to an isomorphism on homology
  in all degrees `≤ N`.
-/

open scoped Topology Topology.Homotopy unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.EMFG

noncomputable section

/-- `killChain Y k` is path connected when `Y` is: the chain is built from `Y` by attaching cells of
dimension `≥ 2`, and `Work.Serre.killCells_step` exhibits every point as joined to a point of the
previous stage. -/
theorem killChain_pathConnected (Y : Type) [TopologicalSpace Y] [PathConnectedSpace Y] (k : ℕ) :
    PathConnectedSpace (killChain Y k) := by
  induction k with
  | zero => exact ‹PathConnectedSpace Y›
  | succ k ih =>
      haveI := ih
      have h : ∀ p : killChain Y (k+1), ∃ y : killChain Y k, Joined p (Work.Serre.killIncl (k+1) (killChain Y k) y) :=
        (Work.Serre.killCells_step (k+1) (killChain Y k)).2.2
      refine pathConnectedSpace_iff_zerothHomotopy.mpr
        ⟨⟨ZerothHomotopy.mk ((Work.Serre.killIncl (k+1) (killChain Y k)) (killChainUp Y k (Classical.arbitrary Y)))⟩, ⟨fun a b => ?_⟩⟩
      obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective a
      obtain ⟨y, rfl⟩ := ZerothHomotopy.mk_surjective b
      obtain ⟨x', hx'⟩ := h x
      obtain ⟨y', hy'⟩ := h y
      have hxy : Joined ((Work.Serre.killIncl (k+1) (killChain Y k)) x')
          ((Work.Serre.killIncl (k+1) (killChain Y k)) y') :=
        (PathConnectedSpace.joined x' y').map (Work.Serre.killIncl (k+1) (killChain Y k)).continuous
      obtain ⟨γ⟩ := hx'.trans (hxy.trans hy'.symm)
      exact ZerothHomotopy.sound γ

set_option backward.isDefEq.respectTransparency false in
/-- **A map that is an isomorphism on `π₁` extends over the kill chain and is an isomorphism on all
`π_i`, `i ≤ N`.**  `f'` extends `f` over `killChain Y (N-1)`; since the chain has the same `π₀` and
`π₁` as `Y` while its `π_i` for `2 ≤ i ≤ N` are trivial, and since `Z` also has trivial `π_i` in
that range, the extension is bijective on `π_i` for every `i ≤ N` and every base point. -/
theorem piBij_killChain {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (N : ℕ)
    (y₀ : Y) (f : C(Y, Z)) (f' : C(killChain Y (N-1), Z))
    (hcomp : ∀ y, f' (killChainUp Y (N-1) y) = f y)
    (hup : ∀ i ≤ 1, ∀ p : Y, Function.Bijective (Work.Serre.piMapN (killChainUp Y (N-1)) i p))
    (hfbij : Function.Bijective (Work.Serre.piMapN f 1 y₀))
    (hkill : ∀ (p : killChain Y (N-1)) (i : ℕ), 2 ≤ i → i ≤ N →
      Subsingleton (HomotopyGroup (Fin i) (killChain Y (N-1)) p))
    (htriv : ∀ (p : Z) (i : ℕ), 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) Z p))
    [PathConnectedSpace (killChain Y (N-1))] [PathConnectedSpace Z] :
    ∀ j ≤ N, ∀ x : killChain Y (N-1), Function.Bijective (Work.Serre.piMapN f' j x) := by
  haveI hzh : Subsingleton (ZerothHomotopy (killChain Y (N-1))) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp (inferInstance : PathConnectedSpace _)).2
  haveI hzz : Subsingleton (ZerothHomotopy Z) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp (inferInstance : PathConnectedSpace Z)).2
  haveI h0a : Subsingleton (HomotopyGroup (Fin 0) (killChain Y (N-1)) (killChainUp Y (N-1) y₀)) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := killChain Y (N-1))
      (x := killChainUp Y (N-1) y₀)).injective.subsingleton
  haveI h0b : Subsingleton (HomotopyGroup (Fin 0) Z (f' (killChainUp Y (N-1) y₀))) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := Z)
      (x := f' (killChainUp Y (N-1) y₀))).injective.subsingleton
  intro j hj x
  have hb0 : Function.Bijective (Work.Serre.piMapN f' j (killChainUp Y (N-1) y₀)) := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      exact ⟨fun a _ _ => Subsingleton.elim a _, fun b => ⟨default, Subsingleton.elim _ b⟩⟩
    · rcases Nat.eq_or_lt_of_le (show 1 ≤ j from hpos) with h1 | h2
      · subst h1
        have hthis : Function.Bijective (Work.Serre.piMapN (f'.comp (killChainUp Y (N-1))) 1 y₀) := by
          rw [show f'.comp (killChainUp Y (N-1)) = f from ContinuousMap.ext hcomp]
          exact hfbij
        have hcomp2 : (Work.Serre.piMapN f' 1 (killChainUp Y (N-1) y₀)) ∘
              (Work.Serre.piMapN (killChainUp Y (N-1)) 1 y₀)
            = Work.Serre.piMapN (f'.comp (killChainUp Y (N-1))) 1 y₀ :=
          funext fun a => (Work.Serre.piMapN_comp (killChainUp Y (N-1)) f' 1 y₀ a).symm
        rw [← hcomp2] at hthis
        exact Work.Serre.CWModel.bijective_of_comp_of_surjective hthis (hup 1 le_rfl y₀).2
      · haveI : Subsingleton (HomotopyGroup (Fin j) (killChain Y (N-1)) (killChainUp Y (N-1) y₀)) :=
          hkill _ j (by omega) (by omega)
        haveI : Subsingleton (HomotopyGroup (Fin j) Z (f' (killChainUp Y (N-1) y₀))) :=
          htriv _ j (by omega) (by omega)
        exact ⟨fun a _ _ => Subsingleton.elim a _, fun b => ⟨default, Subsingleton.elim _ b⟩⟩
  exact Work.Serre.bijective_piMapN_of_joined f'
    (PathConnectedSpace.joined (killChainUp Y (N-1) y₀) x) j hb0

set_option backward.isDefEq.respectTransparency false in
/-- **The `k = 1` comparison.**  Two range models `Z`, `P` of `K(A,1)` up to degree `N` have
isomorphic integral homology in all degrees `i ≤ N`. -/
theorem kOneComparison (A : Type) [AddCommGroup A] (N : ℕ)
    (Z : Type) [TopologicalSpace Z] (z₀ : Z)
    (hZ : Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N Z z₀)
    (P : Type) [TopologicalSpace P] (p₀ : P)
    (hP : Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N P p₀) :
    ∀ i : ℕ, i ≤ N → Nonempty (Work.PiS.HZ Z i ≅ Work.PiS.HZ P i) := by
  classical
  haveI hZpc : PathConnectedSpace Z :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero z₀
      (hZ.2 0 (by norm_num) (Or.inl (by norm_num)))
  haveI hPpc : PathConnectedSpace P :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero p₀
      (hP.2 0 (by norm_num) (Or.inl (by norm_num)))
  -- triviality of the higher homotopy of the two models at *every* base point
  have hZtriv : ∀ (p : Z) (i : ℕ), 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) Z p) := by
    intro p i hi hiN
    have h := Work.Serre.subsingleton_homotopyGroup_of_joined (PathConnectedSpace.joined z₀ p) (i-1)
      (show Subsingleton (HomotopyGroup (Fin (i-1+1)) Z z₀) from by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]
        exact hZ.2 i (by omega) (Or.inr hiN))
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using h
  have hPtriv : ∀ (p : P) (i : ℕ), 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) P p) := by
    intro p i hi hiN
    have h := Work.Serre.subsingleton_homotopyGroup_of_joined (PathConnectedSpace.joined p₀ p) (i-1)
      (show Subsingleton (HomotopyGroup (Fin (i-1+1)) P p₀) from by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ i)]
        exact hP.2 i (by omega) (Or.inr hiN))
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ i)] using h
  -- the `1`-skeleton of `Z` maps onto both `Z` and `P` with the same `π₁`-kernel
  obtain ⟨hsurj_g, hsurj_h, hker⟩ :=
    Work.EMFG.skeletonKernelAndSurj A N Z z₀ hZ P p₀ hP
  haveI hcn : PathConnectedSpace (Work.Serre.SPC.Skeleton Z z₀) :=
    Work.Serre.SPC.skeleton_pathConnected Z z₀
  -- kill the common kernel of the two maps
  obtain ⟨Y, tY, y₀, f, gg, hYpc, hfbij, hgbij⟩ :=
    Work.EMFG.commonPiOneKillConnected (Work.Serre.SPC.skeletonBase Z z₀)
      (Work.Serre.SPC.skeletonMap Z z₀)
      (skeletonLoopMap z₀ p₀ (hZ.1.some.trans hP.1.some.symm)) hsurj_g hsurj_h hker
  letI := tY
  haveI := hYpc
  -- extend both maps over the chain killing `π₂, …, π_N`
  obtain ⟨f', hf'_comp, hf'_up, hf'_kill⟩ := Work.EMFG.killChain_extend y₀ f N hZtriv
  obtain ⟨g'', hg''_comp, hg''_up, hg''_kill⟩ := Work.EMFG.killChain_extend y₀ gg N hPtriv
  haveI hY'pc : PathConnectedSpace (killChain Y (N-1)) := killChain_pathConnected Y (N-1)
  haveI hY'ne : Nonempty (killChain Y (N-1)) := ⟨killChainUp Y (N-1) y₀⟩
  have hbij_f' : ∀ j ≤ N, ∀ x : killChain Y (N-1), Function.Bijective (Work.Serre.piMapN f' j x) :=
    piBij_killChain N y₀ f f' hf'_comp hf'_up hfbij hf'_kill hZtriv
  have hbij_g'' : ∀ j ≤ N, ∀ x : killChain Y (N-1), Function.Bijective (Work.Serre.piMapN g'' j x) :=
    piBij_killChain N y₀ gg g'' hg''_comp hg''_up hgbij hg''_kill hPtriv
  -- upgrade to homology isomorphisms in degrees `≤ N`
  have hZiso : ∀ j ≤ N, Nonempty (Work.PiS.HZ (killChain Y (N-1)) j ≅ Work.PiS.HZ Z j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (killChain Y (N-1))) (TopCat.of Z) (TopCat.ofHom f')) 0) :=
        Work.Serre.Assembly.hZeroOfPiZeroInt f' (fun x => hbij_f' 0 (by omega) x)
      exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (killChain Y (N-1))) (TopCat.of Z) (TopCat.ofHom f')) 0)⟩
    · haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (killChain Y (N-1))) (TopCat.of Z) (TopCat.ofHom f')) j) :=
        Work.Serre.Assembly.serreK2IntSharp f' (N+1)
          (fun k hk x => hbij_f' k (by omega) x) j hpos (by omega)
      exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (killChain Y (N-1))) (TopCat.of Z) (TopCat.ofHom f')) j)⟩
  have hPiso : ∀ j ≤ N, Nonempty (Work.PiS.HZ (killChain Y (N-1)) j ≅ Work.PiS.HZ P j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (killChain Y (N-1))) (TopCat.of P) (TopCat.ofHom g'')) 0) :=
        Work.Serre.Assembly.hZeroOfPiZeroInt g'' (fun x => hbij_g'' 0 (by omega) x)
      exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (killChain Y (N-1))) (TopCat.of P) (TopCat.ofHom g'')) 0)⟩
    · haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
          (TopCat.of (killChain Y (N-1))) (TopCat.of P) (TopCat.ofHom g'')) j) :=
        Work.Serre.Assembly.serreK2IntSharp g'' (N+1)
          (fun k hk x => hbij_g'' k (by omega) x) j hpos (by omega)
      exact ⟨asIso (HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℤ
        (TopCat.of (killChain Y (N-1))) (TopCat.of P) (TopCat.ofHom g'')) j)⟩
  intro i hi
  obtain ⟨e1⟩ := hZiso i hi
  obtain ⟨e2⟩ := hPiso i hi
  exact ⟨e1.symm ≪≫ e2⟩

end

end Work.EMFG
