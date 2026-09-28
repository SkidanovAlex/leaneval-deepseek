import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.tower_fibre_pi_bijective
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.Serre.Models
import Submission.Work.Serre.MapPathDefs
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathQ_fibreHomeo
import Submission.Work.FGThm.killAbove
import Submission.Work.FGThm.mpathHomotopyEquiv
import Submission.Work.FGThm.groupFG_pi_of_hurewicz

set_option linter.style.haveILetI false

/-!
# Serre's theorem: simply connected + f.g. integral homology ⇒ f.g. homotopy groups

Area **FGTHM**.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology unitInterval

namespace Work.FGThm

noncomputable section

/-! ## Finiteness of integral homology transfers along homotopy equivalences -/

abbrev HZi (X : TopCat) (n : ℕ) : ModuleCat ℤ :=
  (Work.Cohomology.singularChains ℤ X).homology n

abbrev hzMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    HZi (TopCat.of X) n ⟶ HZi (TopCat.of Y) n :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) n

theorem hzMap_homotopy_left {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    hzMap e.toFun n ≫ hzMap e.invFun n = 𝟙 (HZi (TopCat.of X) n) := by
  obtain ⟨H⟩ := e.left_inv
  have key := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom (e.invFun.comp e.toFun)) (g := TopCat.ofHom (ContinuousMap.id X))
    H (ModuleCat.of ℤ ℤ) n
  rw [← HomologicalComplex.homologyMap_comp]
  have hcomp : (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)) ≫
      (Work.Cohomology.chainMap ℤ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom e.invFun)) =
      Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of X)
        (TopCat.ofHom (e.invFun.comp e.toFun)) := by
    simp only [Work.Cohomology.chainMap, Functor.map_comp, TopCat.ofHom_comp]
  rw [hcomp, key, TopCat.ofHom_id, CategoryTheory.Functor.map_id]
  exact HomologicalComplex.homologyMap_id _ n

theorem hzMap_homotopy_right {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    hzMap e.invFun n ≫ hzMap e.toFun n = 𝟙 (HZi (TopCat.of Y) n) := by
  obtain ⟨H⟩ := e.right_inv
  have key := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom (e.toFun.comp e.invFun)) (g := TopCat.ofHom (ContinuousMap.id Y))
    H (ModuleCat.of ℤ ℤ) n
  rw [← HomologicalComplex.homologyMap_comp]
  have hcomp : (Work.Cohomology.chainMap ℤ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom e.invFun)) ≫
      (Work.Cohomology.chainMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom e.toFun)) =
      Work.Cohomology.chainMap ℤ (TopCat.of Y) (TopCat.of Y)
        (TopCat.ofHom (e.toFun.comp e.invFun)) := by
    simp only [Work.Cohomology.chainMap, Functor.map_comp, TopCat.ofHom_comp]
  rw [hcomp, key, TopCat.ofHom_id, CategoryTheory.Functor.map_id]
  exact HomologicalComplex.homologyMap_id _ n

theorem moduleFinite_homology_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Module.Finite ℤ (HZi (TopCat.of X) n) ↔ Module.Finite ℤ (HZi (TopCat.of Y) n) := by
  haveI : IsIso (hzMap e.toFun n) :=
    ⟨hzMap e.invFun n, hzMap_homotopy_left e n, hzMap_homotopy_right e n⟩
  exact ⟨fun _ => Module.Finite.equiv (asIso (hzMap e.toFun n)).toLinearEquiv,
    fun _ => Module.Finite.equiv (asIso (hzMap e.toFun n)).symm.toLinearEquiv⟩

theorem fgUpTo_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (N : ℕ) :
    Work.PiS.FGUpTo X N ↔ Work.PiS.FGUpTo Y N := by
  constructor
  · intro h i hi
    exact (moduleFinite_homology_of_homotopyEquiv e i).mp (h i hi)
  · intro h i hi
    exact (moduleFinite_homology_of_homotopyEquiv e i).mpr (h i hi)

theorem fgUpTo_mono {X : Type} [TopologicalSpace X] {N M : ℕ} (hNM : N ≤ M)
    (h : Work.PiS.FGUpTo X M) : Work.PiS.FGUpTo X N :=
  fun i hi => h i (le_trans hi hNM)

theorem simplyConn_of_isEMSpaceUpTo {A : Type} [AddCommGroup A] {m N : ℕ} (hm : 2 ≤ m)
    {X : Type} [TopologicalSpace X] {x : X}
    (h : Work.Serre.IsEMSpaceUpTo A m (by omega) N X x) : Work.PiS.SimplyConn X x :=
  ⟨h.2 0 (by omega) (Or.inl (by omega)), h.2 1 (by omega) (Or.inl (by omega))⟩

theorem groupFG_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : Group.FG G) : Group.FG H := by
  haveI := h
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

noncomputable def indexCastMulEquiv {X : Type} [TopologicalSpace X] (x : X) {n m : ℕ} (h : n = m)
    [Nonempty (Fin n)] [Nonempty (Fin m)] :
    HomotopyGroup (Fin n) X x ≃* HomotopyGroup (Fin m) X x := by
  subst h
  exact MulEquiv.refl _

theorem groupFG_indexCast {X : Type} [TopologicalSpace X] (x : X) {n m : ℕ} (h : n = m)
    [Nonempty (Fin n)] [Nonempty (Fin m)] (hfg : Group.FG (HomotopyGroup (Fin n) X x)) :
    Group.FG (HomotopyGroup (Fin m) X x) :=
  groupFG_of_mulEquiv (indexCastMulEquiv x h) hfg

/-- The canonical group isomorphism `G ≃* Multiplicative (Additive G)`. -/
def canonMulEquivMultiplicativeAdditive (G : Type) [CommGroup G] :
    G ≃* Multiplicative (Additive G) where
  toFun g := Multiplicative.ofAdd (Additive.ofMul g)
  invFun m := Additive.ofMul.symm (Multiplicative.ofAdd.symm m)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **A range model packaged as an `IsEMSpaceUpTo`**: `IsRangeKModel` plus the identification of
`π_m` with `A` at the (successor) degree `m` gives the `IsEMSpaceUpTo` interface. -/
theorem isEMSpaceUpTo_of_rangeModel {A : Type} [AddCommGroup A] {m N : ℕ} (hm : 0 < m)
    [Nonempty (Fin m)] {Z : Type} [TopologicalSpace Z] (z : Z) (hmN : m ≤ N)
    (h1 : Nonempty (HomotopyGroup (Fin m) Z z ≃* Multiplicative A))
    (h2 : ∀ i : ℕ, i ≠ m → i ≤ N → Subsingleton (HomotopyGroup (Fin i) Z z)) :
    Work.Serre.IsEMSpaceUpTo A m hm N Z z :=
  ⟨h1, fun i hi hj => h2 i hi (by
    rcases hj with h | h
    · exact le_trans (le_of_lt h) hmN
    · exact h)⟩

/-! ## The step and the assembly -/

/-- **The assembly of `Work.PiS.SerreFGTheorem`** from the three independent lemmas
`killAbove` (the truncation tower of the step), `mpathHomotopyEquiv` (the total space of the
mapping path fibration is homotopy equivalent to the source) and `groupFG_pi_of_hurewicz` (the
Hurewicz embedding in the first non-vanishing degree). -/
theorem serreFGTheorem_of
    (killAbove : ∀ (k N : ℕ) (hk : 2 ≤ k) (hN : k ≤ N)
        (X : Type) [TopologicalSpace X] (x₀ : X),
      (∀ j : ℕ, j < k → Subsingleton (HomotopyGroup (Fin j) X x₀)) →
      ∃ (Z : Type) (_ : TopologicalSpace Z) (inc : C(X, Z)),
        Work.RatHurewicz.IsRangeKModel k N (inc x₀) ∧
        (∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j)
          (Work.RatHurewicz.homotopyFibre inc x₀)
          (Work.RatHurewicz.homotopyFibreBasepoint inc x₀))) ∧
        (∀ n : ℕ, k ≤ n → n + 1 ≤ N → Nonempty (HomotopyGroup (Fin (n + 1))
          (Work.RatHurewicz.homotopyFibre inc x₀)
          (Work.RatHurewicz.homotopyFibreBasepoint inc x₀) ≃*
          HomotopyGroup (Fin (n + 1)) X x₀)) ∧
        Function.Surjective (Work.StemsB.πmap inc (k - 1) x₀))
    (mpathHomotopyEquiv : ∀ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)),
      Nonempty (ContinuousMap.HomotopyEquiv (Work.Serre.mpath p) E))
    (groupFG_pi_of_hurewicz : ∀ {X : Type} [TopologicalSpace X] (x : X) (n : ℕ),
      (∀ i : ℕ, i < n + 1 + 1 → Subsingleton (HomotopyGroup (Fin i) X x)) →
      Module.Finite ℤ (Work.PiS.HZ X (n + 1 + 1)) →
      Group.FG (HomotopyGroup (Fin (n + 1 + 1)) X x))
    (hSSS : Work.PiS.SerreFGThreeForTwo) (hEM : Work.PiS.EMHomologyFG) :
    Work.PiS.SerreFGTheorem := by
  -- a map inducing finitely generated homology one degree back
  have hMpath : ∀ {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (N : ℕ),
      Work.PiS.FGUpTo E N → Work.PiS.FGUpTo (Work.Serre.mpath p) N := by
    intro E B _ _ p N h
    obtain ⟨e⟩ := mpathHomotopyEquiv p
    exact (fgUpTo_of_homotopyEquiv e N).mpr h
  intro X tX x hsimple hfg j
  -- the target degree is `j + 2`; write it as `j + 1 + 1`
  -- the killed step
  have hStep : ∀ (d : ℕ) (Y : Type) (tY : TopologicalSpace Y) (y : Y),
      (∀ i : ℕ, i < d + 1 + 1 → Subsingleton (HomotopyGroup (Fin i) Y y)) →
      Work.PiS.FGUpTo Y (3 * j + 2 - 2 * d) → d + 1 ≤ j →
      ∃ (Y' : Type) (_ : TopologicalSpace Y') (y' : Y'),
        (∀ i : ℕ, i < d + 1 + 1 + 1 → Subsingleton (HomotopyGroup (Fin i) Y' y')) ∧
        Work.PiS.FGUpTo Y' (3 * j + 2 - 2 * (d + 1)) ∧
        Nonempty (HomotopyGroup (Fin (j + 1 + 1)) Y' y' ≃*
          HomotopyGroup (Fin (j + 1 + 1)) Y y) := by
    intro d Y tY y hconn hYfg hdj
    letI := tY
    -- the new range
    set Nk : ℕ := 3 * j + 2 - 2 * (d + 1) with hNk
    -- `π_k(Y)` is finitely generated
    have hk2 : 2 ≤ d + 1 + 1 := by omega
    have hfin : Module.Finite ℤ (Work.PiS.HZ Y (d + 1 + 1)) := hYfg (d + 1 + 1) (by omega)
    have hfgY : Group.FG (HomotopyGroup (Fin (d + 1 + 1)) Y y) :=
      groupFG_pi_of_hurewicz y d hconn hfin
    -- the truncation tower with parameter `Nk + 2`
    obtain ⟨Z, tZ, inc, hmodel, hfib, hmu, hsurj⟩ :=
      killAbove (d + 1 + 1) (Nk + 2) hk2 (by omega) Y y hconn
    letI := tZ
    -- `π_k(Z)` is finitely generated (surjection from `π_k(Y)`)
    have hfgZ : Group.FG (HomotopyGroup (Fin (d + 1 + 1)) Z (inc y)) := by
      haveI : Group.FG (HomotopyGroup (Fin ((d + 1 + 1) - 1 + 1)) Y y) :=
        groupFG_indexCast y (by omega) hfgY
      have hZ0 : Group.FG (HomotopyGroup (Fin ((d + 1 + 1) - 1 + 1)) Z (inc y)) :=
        Group.fg_of_surjective (f := Work.StemsB.πmap inc ((d + 1 + 1) - 1) y) hsurj
      exact groupFG_indexCast (inc y) (by omega) hZ0
    -- the module structure
    haveI : Module.Finite ℤ (Additive (HomotopyGroup (Fin (d + 1 + 1)) Z (inc y))) :=
      Module.Finite.iff_addGroup_fg.mpr (GroupFG.iff_add_fg.mp hfgZ)
    -- `Z` is a range model of `K(π_k Y, k)`
    have hEMmodel : Work.Serre.IsEMSpaceUpTo
        (Additive (HomotopyGroup (Fin (d + 1 + 1)) Z (inc y)))
        (d + 1 + 1) (by omega) (Nk + 2) Z (inc y) :=
      isEMSpaceUpTo_of_rangeModel (by omega) (inc y) (by omega)
        ⟨canonMulEquivMultiplicativeAdditive _⟩
        (fun i _ hiN => hmodel i hiN ‹i ≠ d + 1 + 1›)
    -- homology of `Z` in range
    have hZfg : Work.PiS.FGUpTo Z (Nk + 1) :=
      hEM (Additive (HomotopyGroup (Fin (d + 1 + 1)) Z (inc y))) (d + 1 + 1) hk2
        (Nk + 1) Z (inc y) hEMmodel
    -- the fibre direction of `hSSS` on the mapping path fibration
    have hsc : Work.PiS.SimplyConn Z (inc y) :=
      simplyConn_of_isEMSpaceUpTo hk2 hEMmodel
    have hE : Work.PiS.FGUpTo (Work.Serre.mpath inc) Nk :=
      hMpath inc Nk (fgUpTo_mono (by omega) hYfg)
    have hFib : Work.PiS.FGUpTo (Work.StemsB.fibre (Work.Serre.mpathQ inc) (inc y)) Nk :=
      (hSSS (Work.Serre.mpath inc) Z (Work.Serre.mpathQ inc) (Work.Serre.mpathOf inc y)
        (fun n => Work.Serre.mpathQ_hasHLP inc (Fin n → I)) hsc).2.2 Nk hZfg hE
    -- transfer to the homotopy fibre
    have hY'fg : Work.PiS.FGUpTo (Work.RatHurewicz.homotopyFibre inc y) Nk := by
      obtain ⟨e⟩ := Work.Serre.mpathQ_fibreHomeo inc y
      exact (fgUpTo_of_homotopyEquiv e.toHomotopyEquiv Nk).mp hFib
    refine ⟨Work.RatHurewicz.homotopyFibre inc y, inferInstance,
      Work.RatHurewicz.homotopyFibreBasepoint inc y, ?_, ?_, ?_⟩
    · intro i hi
      exact hfib i (by omega)
    · exact hNk ▸ hY'fg
    · -- the isomorphism on the target degree
      have hn : d + 1 + 1 ≤ j + 1 := by omega
      have hnN : j + 1 + 1 ≤ Nk + 2 := by omega
      exact hmu (j + 1) hn hnN
  -- the induction
  have main : ∀ d : ℕ, d ≤ j → ∃ (Y : Type) (_ : TopologicalSpace Y) (y : Y),
      (∀ i : ℕ, i < d + 1 + 1 → Subsingleton (HomotopyGroup (Fin i) Y y)) ∧
      Work.PiS.FGUpTo Y (3 * j + 2 - 2 * d) ∧
      Nonempty (HomotopyGroup (Fin (j + 1 + 1)) Y y ≃* HomotopyGroup (Fin (j + 1 + 1)) X x) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨X, tX, x, ?_, ?_, ?_⟩
      · intro i hi
        rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
        · exact hsimple.1
        · exact hsimple.2
      · simpa using hfg (3 * j + 2)
      · exact ⟨MulEquiv.refl _⟩
    | succ d ih =>
      intro hd
      obtain ⟨Y, tY, y, hconn, hYfg, hiso⟩ := ih (by omega)
      obtain ⟨Y', tY', y', hconn', hY'fg, hiso'⟩ := hStep d Y tY y hconn hYfg (by omega)
      obtain ⟨e1⟩ := hiso'
      obtain ⟨e2⟩ := hiso
      exact ⟨Y', tY', y', hconn', hY'fg, ⟨e1.trans e2⟩⟩
  obtain ⟨Y, tY, y, hconn, hYfg, hiso⟩ := main j le_rfl
  letI := tY
  -- Hurewicz in the last degree
  have hfin : Module.Finite ℤ (Work.PiS.HZ Y (j + 1 + 1)) := hYfg (j + 1 + 1) (by omega)
  have hfgY : Group.FG (HomotopyGroup (Fin (j + 1 + 1)) Y y) :=
    groupFG_pi_of_hurewicz y j hconn hfin
  obtain ⟨e⟩ := hiso
  exact groupFG_of_mulEquiv e hfgY

/-- **Serre's theorem**: a simply connected space with finitely generated integral homology in
every degree has finitely generated homotopy groups. -/
theorem serreFGTheorem (hSSS : Work.PiS.SerreFGThreeForTwo) (hEM : Work.PiS.EMHomologyFG) :
    Work.PiS.SerreFGTheorem :=
  serreFGTheorem_of killAbove mpathHomotopyEquiv groupFG_pi_of_hurewicz hSSS hEM

end
end Work.FGThm
