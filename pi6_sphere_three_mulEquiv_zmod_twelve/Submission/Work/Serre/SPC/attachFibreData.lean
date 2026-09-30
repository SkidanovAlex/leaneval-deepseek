import Mathlib
import Submission.Work.Serre.SPC.Defs
import Submission.Work.Serre.Assembly.pullbackFst_serre
import Submission.Work.Serre.cylRelPi
import Submission.Work.Cohomology.epsilonNaturality
import Submission.Work.Cohomology.free_and_vanishing_ball_compl

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option synthInstance.maxHeartbeats 400000



open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

set_option linter.style.haveILetI false

namespace Work.Serre.SPC

noncomputable section

/-! ## The fibre of the base change

An element of the fibre of `Work.StemsB.pullbackFst g p` over a point `y : Γ` is a pair
`(x, e) ∈ Γ × E` with `g x = p e` and `x = y`, so forgetting the `Γ`-coordinate (which is forced to
be `y`) identifies it with the fibre of `p` over `g y`.  This is the homeomorphism along which the
connectivity data is transported. -/

/-- **The fibre of the base change over `y` is the fibre of `p` over `g y`.** -/
def fibrePullbackFstHomeo {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Γ] (g : C(Γ, B)) (p : C(E, B)) (y : Γ) :
    Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y ≃ₜ Work.StemsB.fibre p (g y) where
  toFun x := ⟨x.1.1.2, by rw [← x.1.2]; exact congrArg g x.2⟩
  invFun e := ⟨⟨(y, e.1), e.2.symm⟩, rfl⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
    exact x.2.symm
  right_inv e := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-! ## `π₀` a point implies path connected

The zeroth homotopy group `π₀ X = HomotopyGroup (Fin 0) X x₀` is the set of path components of `X`
based at `x₀`: the class of a `0`-cube is the class of the point it is concentrated at, and two
such classes agree exactly when the two points are joined by a path.  Hence a space whose `π₀` is a
point is path connected, and Mathlib's instance makes its augmentation `H₀(-;ℤ) ⟶ ℤ` an
isomorphism. -/

/-- Two points of a space whose `π₀` classes agree are joined by a path: the homotopy of `0`-cubes
is a path in the ambient space. -/
theorem attachJoinedOfGenLoopZero {X : Type} [TopologicalSpace X] {x p q : X}
    (h : GenLoop.Homotopic (Work.Serre.genLoopZero X x p) (Work.Serre.genLoopZero X x q)) :
    Joined p q := by
  obtain ⟨H⟩ := h
  exact ⟨Path.mk ⟨fun t => H (t, fun _ => 0),
    H.continuous.comp (continuous_id.prodMk continuous_const)⟩
    (H.map_zero_left (fun _ => 0)) (H.map_one_left (fun _ => 0))⟩

/-- **`π₀` as the set of path components.** -/
theorem attachGenLoopZero_eq_iff {X : Type} [TopologicalSpace X] {x p q : X} :
    ((⟦Work.Serre.genLoopZero X x p⟧ : HomotopyGroup (Fin 0) X x)
        = ⟦Work.Serre.genLoopZero X x q⟧) ↔ Joined p q :=
  ⟨fun h => attachJoinedOfGenLoopZero (Quotient.exact h),
    fun h => Quotient.sound (Work.Serre.genLoopZero_homotopic h.some)⟩

/-- **A space whose `π₀` is trivial is path connected.** -/
theorem pathConnectedSpace_of_subsingleton_pi0 {X : Type} [TopologicalSpace X] (x₀ : X)
    (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) : PathConnectedSpace X where
  nonempty := ⟨x₀⟩
  joined p q := attachGenLoopZero_eq_iff.mp
    (h.elim (⟦Work.Serre.genLoopZero X x₀ p⟧ : HomotopyGroup (Fin 0) X x₀)
      (⟦Work.Serre.genLoopZero X x₀ q⟧ : HomotopyGroup (Fin 0) X x₀))

/-! ## The augmentation is invariant under homeomorphism

The augmentation `H₀(-;ℤ) ⟶ ℤ` is natural (`Work.Cohomology.epsilonNaturality`), so along a
homeomorphism — which induces an isomorphism on `H₀` — it is an isomorphism on one side if and only
if it is on the other. -/

/-- **`IsIso` of the augmentation is invariant under homeomorphism.** -/
theorem isIso_epsilon_of_homeo {X Y : TopCat.{0}} (e : X ≃ₜ Y)
    (h : IsIso (TopCat.singularHomology₀ε Y (ModuleCat.of ℤ ℤ))) :
    IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) := by
  have hnat := Work.Cohomology.epsilonNaturality X Y (TopCat.isoOfHomeo e).hom
  have hf : IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ X Y (TopCat.isoOfHomeo e).hom) 0) := inferInstance
  rw [← hnat]
  exact IsIso.comp_isIso' hf h

/-- **The fibre data of the base change of a Serre fibration along a map with path connected
source.**  Let `p : E → B` be a Serre fibration whose fibre over `b₀` is homologically
`f`-connected (`H_j(F;ℤ) = 0` for `0 < j < f`) and whose `π₀` is a point (`hfib0`).  Let `Γ` be path
connected, `g : Γ → B` with `g γ₀ = b₀`.  Then the fibre of the base change
`Work.StemsB.pullbackFst g p : Γ ×_B E → Γ` over an arbitrary point `y` has the same connectivity
data: its reduced homology vanishes below `f` and its augmentation `H_0 → ℤ` is an isomorphism.

(`FibreTransport` transfers the data from `b₀` to `g y` along the image of a path from `γ₀` to `y`,
which exists because `Γ` is path connected; the fibre of the base change over `y` is homeomorphic
to the fibre of `p` over `g y` — the mirror of `Work.Serre.pbFibreHomeo`, which is stated for cube
bases and is only a template — and `IsZero`/`IsIso` transport along that homeomorphism.  For the
`H_0` clause, convert `Subsingleton (HomotopyGroup (Fin 0) (fibre p b₀) ⟨e₀,he₀⟩)` into
`IsIso (TopCat.singularHomology₀ε ...)` via `PathConnectedSpace`.) -/
theorem attachFibreData {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (b₀ : B) (e₀ : E) (he₀ : p e₀ = b₀)
    (f : ℕ) (htr : Work.Serre.SPC.FibreTransport)
    (hfib : ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p b₀))).homology j))
    (hfib0 : Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p b₀) ⟨e₀, he₀⟩))
    {Γ : Type} [TopologicalSpace Γ] [PathConnectedSpace Γ] (γ₀ : Γ) (g : C(Γ, B))
    (hbase : g γ₀ = b₀) :
    (∀ y : Γ, ∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y))).homology j)) ∧
    (∀ y : Γ, CategoryTheory.IsIso (TopCat.singularHomology₀ε
      (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackFst g p) y)) (ModuleCat.of ℤ ℤ))) := by
  haveI hpc : PathConnectedSpace (Work.StemsB.fibre p b₀) :=
    pathConnectedSpace_of_subsingleton_pi0 ⟨e₀, he₀⟩ hfib0
  have hε₀ : IsIso (TopCat.singularHomology₀ε (TopCat.of (Work.StemsB.fibre p b₀))
      (ModuleCat.of ℤ ℤ)) := inferInstance
  -- the connectivity data at the fibre over `g y`, transferred from `b₀` along the image of a path
  -- from `γ₀` to `y` (`FibreTransport`)
  have htr' : ∀ y : Γ, (∀ j : ℕ, 0 < j → j < f → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.fibre p (g y)))).homology j)) ∧
      CategoryTheory.IsIso (TopCat.singularHomology₀ε
        (TopCat.of (Work.StemsB.fibre p (g y))) (ModuleCat.of ℤ ℤ)) := by
    intro y
    obtain ⟨γ⟩ := PathConnectedSpace.joined γ₀ y
    have h1 : (g.comp γ.toContinuousMap) 0 = b₀ := by
      simp only [ContinuousMap.comp_apply]
      rw [show γ.toContinuousMap 0 = γ₀ from γ.source', hbase]
    have h2 : (g.comp γ.toContinuousMap) 1 = g y := by
      simp only [ContinuousMap.comp_apply]
      rw [show γ.toContinuousMap 1 = y from γ.target']
    exact htr p hp f b₀ (g y) (g.comp γ.toContinuousMap) h1 h2 hfib hε₀
  constructor
  · -- vanishing of the reduced homology, transported to the fibre of the base change
    intro y j hj0 hjf
    exact Work.Cohomology.isZero_homology_of_homeomorph (fibrePullbackFstHomeo g p y) j
      ((htr' y).1 j hj0 hjf)
  · -- the augmentation, transported along the same homeomorphism
    intro y
    exact isIso_epsilon_of_homeo (fibrePullbackFstHomeo g p y) (htr' y).2

end

end Work.Serre.SPC
