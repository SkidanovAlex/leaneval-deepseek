import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.CompressionGeometry
import Submission.Work.RatHurewicz.pinchedMap_nullHomotopic
import Submission.Work.RatHurewicz.RelPiPathDefs
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.RatHurewicz.PairShiftBijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `π₁` of the homotopy fibre of an inclusion, when `π₂` of the ambient space vanishes

Let `A ⊆ Y`, `i = setIncl A`, and let `E = homotopyFibre i a₀` be the homotopy fibre of the
inclusion, with base point `bp = (a₀, const)`.  The `n`-th homotopy group of `E` at `bp` is the
`n`-th relative homotopy group of the pair `(Y,A)` (`Work.RatHurewicz.RelHomotopyGroup`, classically
`π_{n+1}(Y,A)`), and this file proves the **low-degree** piece of the long exact sequence of the
pair, which is *not* covered by `Work.RatHurewicz.pair_les` (whose exactness statements start in
degree `2`):

  if `π₁(A) → π₁(Y)` is injective and `π₂(Y) = 0`, then `RelHomotopyGroup (setIncl A) a₀ 1 = 0`.

## The argument

It is the classical geometric one.  Write a loop of `E` at `bp` as the family `x ↦ (a x, λ_x)`
of pairs of a loop `a` of `A` and a path `λ_x` of `Y` from `i a₀` to `i (a x)`.

* The *square* `β (x,t) = λ_x t` (`relSquare`) has its bottom side and its two lateral sides
  constant at `i a₀`, and its top side equal to `i ∘ α`, where `α = p ∘ γ` is the projection of the
  loop (`p = homotopyFibreFst`).  Reading the square with the two coordinates interchanged and
  reversing the homotopy (`relSquareHom`) therefore exhibits a null-homotopy of `i ∘ α`; by
  injectivity of `π₁(A) → π₁(Y)` (`hinj`) the loop `α` is null-homotopic in `A`
  (`relProj_class_eq_one`).
* The fully relative homotopy lifting property of the Serre fibration `p : E → A`
  (`Work.RatHurewicz.fibreHrel`), with the lateral boundary prescribed to be constantly `bp`,
  lifts that null-homotopy to a homotopy of `γ` *relative to its endpoints* to a loop `ρ` of the
  fibre `F = p ⁻¹' {p bp}` of `p` (`relLoopHom`).
* `π₁(F) = π₂(Y) = 0`, because the loop space shift `pairShiftHom 0 : π₂(Y) → π₁(F)` is a bijection
  (`Work.RatHurewicz.pairShiftHom_bijective`, `piOne_fibre_subsingleton`), so `ρ` and hence `γ` is
  null-homotopic.

## Main declarations

* `Work.Serre.relSquare`, `Work.Serre.relSquareHom`, `Work.Serre.relSquareHom_class`,
  `Work.Serre.relProj_class_eq_one` — the square of a loop of the homotopy fibre and the
  null-homotopy of its projection;
* `Work.Serre.piOne_fibre_subsingleton` — `π₁` of the fibre of `p` is trivial when `π₂(Y) = 0`;
* `Work.Serre.relLoopHom` — the homotopy carried by a lifted homotopy;
* `Work.Serre.relPi_one_subsingleton` — the target.
-/

namespace Work.Serre

open scoped Topology Topology.Homotopy unitInterval
open Work.StemsB

noncomputable section

set_option maxHeartbeats 1000000

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-- The homotopy fibre of the inclusion `A ↪ Y` at `a₀`, abbreviated. -/
abbrev relFibre (a₀ : ↥A) : Type := Work.RatHurewicz.homotopyFibre (Work.RatHurewicz.setIncl A) a₀

/-- The projection `E → A` of the homotopy fibre of `A ↪ Y`. -/
abbrev relProj (a₀ : ↥A) : C(relFibre (A := A) a₀, ↥A) :=
  Work.RatHurewicz.homotopyFibreFst (Work.RatHurewicz.setIncl A) a₀

/-- The base point `(a₀, const)` of the homotopy fibre of `A ↪ Y`. -/
abbrev relBase (a₀ : ↥A) : relFibre (A := A) a₀ :=
  Work.RatHurewicz.homotopyFibreBasepoint (Work.RatHurewicz.setIncl A) a₀

/-- The coordinate swap `(x, t) ↦ (t, x)` on `I^{Fin 1} × I`, as a continuous map. -/
abbrev relSwap : C((Fin 1 → I) × I, I × (Fin 1 → I)) :=
  (ContinuousMap.snd : C((Fin 1 → I) × I, I)).prodMk
    (ContinuousMap.fst : C((Fin 1 → I) × I, Fin 1 → I))

/-- Evaluation of a loop at `1`, as a continuous map. -/
abbrev relEvalOne : C(Fin 1 → I, (Fin 1 → I) × I) :=
  (ContinuousMap.id (Fin 1 → I)).prodMk (ContinuousMap.const (Fin 1 → I) (1 : I))

/-- **The homotopy from `γ` to the endpoint loop `ρ` of a lifted homotopy `G`**, relative to the
boundary: `(u, x) ↦ G (x, u)`. -/
def relLoopHom (a₀ : ↥A) (γ ρ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
    (G : C((Fin 1 → I) × I, relFibre (A := A) a₀))
    (h0 : ∀ x, G (x, 0) = γ.1 x) (h1 : ∀ x, G (x, 1) = ρ.1 x)
    (hbd : ∀ (x : CubeBdry 1) (t : I), G (x.1, t) = relBase (A := A) a₀) :
    ContinuousMap.HomotopyRel γ.1 ρ.1 (Cube.boundary (Fin 1)) where
  toFun q := G (q.2, q.1)
  continuous_toFun := G.continuous.comp (by fun_prop)
  map_zero_left x := h0 x
  map_one_left x := h1 x
  prop' u x hx := (hbd ⟨x, hx⟩ u).trans (γ.2 x hx).symm

/-! ## The square attached to a loop of the homotopy fibre -/

/-- The underlying path of a point of the homotopy fibre: the second coordinate. -/
abbrev relPathCM (a₀ : ↥A) (e : relFibre (A := A) a₀) : C(I, Y) := e.1.2.1

/-- **The square of a loop of the homotopy fibre**: for `γ : Ω^{1} E bp` the map
`(x,t) ↦ (γ x).1.2.1 t : I × I → Y`. -/
def relSquare (a₀ : ↥A) (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀)) :
    C((Fin 1 → I) × I, Y) :=
  ((Work.RatHurewicz.fibreCMFamily a₀).comp γ.1).uncurry

@[simp]
theorem relSquare_apply (a₀ : ↥A) (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
    (x : Fin 1 → I) (t : I) : relSquare a₀ γ (x, t) = relPathCM a₀ (γ x) t := rfl

/-- The bottom side of the square is constant at `i a₀`. -/
theorem relSquare_zero (a₀ : ↥A) (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
    (x : Fin 1 → I) : relSquare a₀ γ (x, 0) = Work.RatHurewicz.setIncl A a₀ :=
  Work.RatHurewicz.fibreCM_zero (γ x)

/-- The top side of the square is the projection of the loop. -/
theorem relSquare_one (a₀ : ↥A) (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
    (x : Fin 1 → I) :
    relSquare a₀ γ (x, 1) = Work.RatHurewicz.setIncl A (relProj (A := A) a₀ (γ x)) :=
  Work.RatHurewicz.fibreCM_one (γ x)

/-- The lateral sides of the square are constant at `i a₀`. -/
theorem relSquare_bdry (a₀ : ↥A) (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
    {x : Fin 1 → I} (hx : x ∈ Cube.boundary (Fin 1)) (t : I) :
    relSquare a₀ γ (x, t) = Work.RatHurewicz.setIncl A a₀ := by
  have hx' : γ x = relBase (A := A) a₀ := γ.2 x hx
  simp only [relSquare_apply, hx', relBase, relPathCM]
  rfl

/-! ## The induced null-homotopy of the projected loop -/

/-- **The square, with its coordinates interchanged, is a null-homotopy of the projection of the
loop**: the family `(u,x) ↦ β (x, u)` runs from the constant loop to `i ∘ α`, with the lateral
boundary fixed.  (The other orientation is obtained by `.symm`.) -/
def relSquareHom (a₀ : ↥A) (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀)) :
    ContinuousMap.HomotopyRel
      (GenLoop.const : Ω^ (Fin 1) Y (Work.RatHurewicz.setIncl A a₀)).1
      (genLoopMap (Work.RatHurewicz.setIncl A) 1
        (genLoopMap (relProj (A := A) a₀) 1 γ)).1 (Cube.boundary (Fin 1)) where
  toFun q := relSquare a₀ γ (q.2, q.1)
  continuous_toFun := (relSquare a₀ γ).continuous.comp (by fun_prop)
  map_zero_left x := by
    show relSquare a₀ γ (x, 0) = _
    rw [relSquare_zero]
    rfl
  map_one_left x := by
    show relSquare a₀ γ (x, 1) = _
    rw [relSquare_one]
    rfl
  prop' u x hx := by
    show relSquare a₀ γ (x, u) = _
    rw [relSquare_bdry a₀ γ hx u]
    rfl

/-- **The class of the projection of a loop of the homotopy fibre is trivial in the ambient
space.** -/
theorem relSquareHom_class (a₀ : ↥A)
    (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀)) :
    (⟦genLoopMap (Work.RatHurewicz.setIncl A) 1
        (genLoopMap (relProj (A := A) a₀) 1 γ)⟧ :
      HomotopyGroup (Fin 1) Y (Work.RatHurewicz.setIncl A a₀))
      = (1 : HomotopyGroup (Fin 1) Y (Work.RatHurewicz.setIncl A a₀)) := by
  refine (Quotient.sound ?_).trans HomotopyGroup.one_def.symm
  exact ⟨(relSquareHom a₀ γ).symm⟩

/-- **The projected loop of a loop of the homotopy fibre is null-homotopic in `A`**, by injectivity
of `π₁(A) → π₁(Y)`. -/
theorem relProj_class_eq_one (a₀ : ↥A)
    (hinj : Function.Injective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) 0 a₀))
    (γ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀)) :
    (⟦genLoopMap (relProj (A := A) a₀) 1 γ⟧ : HomotopyGroup (Fin 1) ↥A a₀)
      = (1 : HomotopyGroup (Fin 1) ↥A a₀) := by
  refine hinj ?_
  have key : (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) 0 a₀)
      ⟦genLoopMap (relProj (A := A) a₀) 1 γ⟧
      = (1 : HomotopyGroup (Fin 1) Y (Work.RatHurewicz.setIncl A a₀)) := by
    show (⟦genLoopMap (Work.RatHurewicz.setIncl A) 1
        (genLoopMap (relProj (A := A) a₀) 1 γ)⟧ :
      HomotopyGroup (Fin 1) Y (Work.RatHurewicz.setIncl A a₀))
      = (1 : HomotopyGroup (Fin 1) Y (Work.RatHurewicz.setIncl A a₀))
    exact relSquareHom_class a₀ γ
  rw [key, map_one]

/-! ## Triviality of `π₁` of the fibre -/

/-- **`π₁` of the fibre of the projection is trivial**, because `π₂(Y) = 0` and the loop-space
shift `pairShiftHom 0 : π₂(Y) → π₁(F)` is a bijection. -/
theorem piOne_fibre_subsingleton (a₀ : ↥A)
    (hY2 : Subsingleton (HomotopyGroup (Fin 2) Y (Work.RatHurewicz.setIncl A a₀))) :
    Subsingleton (HomotopyGroup (Fin 1)
      (fibre (relProj (A := A) a₀) (relProj (A := A) a₀ (relBase (A := A) a₀)))
      (fibrePoint (relProj (A := A) a₀) (relBase (A := A) a₀))) := by
  have hbij := Work.RatHurewicz.pairShiftHom_bijective (Work.RatHurewicz.setIncl A) a₀ 0
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hbij.2 x
  obtain ⟨b, rfl⟩ := hbij.2 y
  rw [@Subsingleton.elim _ hY2 a b]

/-! ## The main theorem -/

theorem relPi_one_subsingleton {Y : Type} [TopologicalSpace Y] {A : Set Y} (a₀ : ↥A)
    (hinj : Function.Injective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) 0 a₀))
    (hY2 : Subsingleton (HomotopyGroup (Fin 2) Y (Work.RatHurewicz.setIncl A a₀))) :
    Subsingleton (Work.RatHurewicz.RelHomotopyGroup (Work.RatHurewicz.setIncl A) a₀ 1) := by
  classical
  have hF := piOne_fibre_subsingleton (A := A) a₀ hY2
  have key : ∀ z : HomotopyGroup (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀),
      z = (1 : HomotopyGroup (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀)) := by
    intro z
    refine Quotient.inductionOn z (fun γ => ?_)
    -- (1) the projected loop is null-homotopic in `A`
    have hα : (⟦genLoopMap (relProj (A := A) a₀) 1 γ⟧ : HomotopyGroup (Fin 1) ↥A a₀)
        = (1 : HomotopyGroup (Fin 1) ↥A a₀) := relProj_class_eq_one (A := A) a₀ hinj γ
    have hΘ : GenLoop.Homotopic (genLoopMap (relProj (A := A) a₀) 1 γ)
        (GenLoop.const : Ω^ (Fin 1) ↥A a₀) := by
      have h : (⟦genLoopMap (relProj (A := A) a₀) 1 γ⟧ : HomotopyGroup (Fin 1) ↥A a₀)
          = ⟦(GenLoop.const : Ω^ (Fin 1) ↥A a₀)⟧ := by
        rw [hα, HomotopyGroup.one_def]
      exact Quotient.exact h
    obtain ⟨Θ⟩ := hΘ
    -- (2) lift the null-homotopy along the fibration `E → A`
    let Hbase : C((Fin 1 → I) × I, ↥A) :=
      ⟨fun q => Θ (q.2, q.1), Θ.continuous_toFun.comp relSwap.continuous⟩
    have hHbase0 : ∀ x : Fin 1 → I, Hbase (x, 0) = relProj (A := A) a₀ (γ x) :=
      fun x => Θ.map_zero_left x
    have hHbase_bdry : ∀ (x : CubeBdry 1) (t : I), Hbase (x.1, t) = a₀ := by
      intro x t
      have h1 : Hbase (x.1, t) = (genLoopMap (relProj (A := A) a₀) 1 γ).1 x.1 :=
        Θ.prop t x.1 x.2
      rw [h1, show (genLoopMap (relProj (A := A) a₀) 1 γ).1 x.1
            = relProj (A := A) a₀ (γ x.1) from rfl,
        show γ x.1 = relBase (A := A) a₀ from γ.2 x.1 x.2]
      rfl
    obtain ⟨G, hGp, hG0, hGbd⟩ :=
      Work.RatHurewicz.fibreHrel (Work.RatHurewicz.setIncl A) a₀ 1 Hbase γ.1
        (ContinuousMap.ext (fun x : Fin 1 → I => by
          change relProj (A := A) a₀ (γ x) = Hbase (x, 0)
          exact (hHbase0 x).symm))
        (ContinuousMap.const (CubeBdry 1 × I) (relBase (A := A) a₀))
        (ContinuousMap.ext (fun q : CubeBdry 1 × I => by
          change relProj (A := A) a₀ (relBase (A := A) a₀) = Hbase (q.1.1, q.2)
          rw [show relProj (A := A) a₀ (relBase (A := A) a₀) = a₀ from rfl,
            hHbase_bdry q.1 q.2]))
        (by intro x; exact (γ.2 x.1 x.2).symm)
    -- (3) the endpoint of the lifted homotopy is a loop of the fibre
    let ρcm : C(Fin 1 → I, relFibre (A := A) a₀) := G.comp relEvalOne
    have hρcm : ∀ x, ρcm x = G (x, 1) := fun x => rfl
    have hρbdry : ∀ x ∈ Cube.boundary (Fin 1), ρcm x = relBase (A := A) a₀ := by
      intro x hx
      rw [hρcm]
      exact hGbd ⟨x, hx⟩ 1
    let ρ : Ω^ (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀) := ⟨ρcm, hρbdry⟩
    have hρ_apply : ∀ x, ρ x = G (x, 1) := fun x => rfl
    -- (4) `γ` is homotopic to `ρ`
    have hγρ : (⟦γ⟧ : HomotopyGroup (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
        = ⟦ρ⟧ := by
      have hhom : ContinuousMap.HomotopyRel γ.1 ρ.1 (Cube.boundary (Fin 1)) :=
        relLoopHom (A := A) a₀ γ ρ G hG0 (fun x => (hρ_apply x).symm) hGbd
      exact Quotient.sound (show GenLoop.Homotopic γ ρ from ⟨hhom⟩)
    -- (5) `ρ` lies in the fibre, where `π₁` is trivial
    have hρfib : ∀ x, relProj (A := A) a₀ (ρ x)
        = relProj (A := A) a₀ (relBase (A := A) a₀) := by
      intro x
      have h1 : relProj (A := A) a₀ (G (x, 1)) = Hbase (x, 1) :=
        congrFun (congrArg DFunLike.coe hGp) (x, 1)
      have h2 : Hbase (x, 1) = a₀ := Θ.map_one_left x
      rw [hρ_apply x, h1, h2,
        show relProj (A := A) a₀ (relBase (A := A) a₀) = a₀ from rfl]
    let ρF : Ω^ (Fin 1) (fibre (relProj (A := A) a₀)
          (relProj (A := A) a₀ (relBase (A := A) a₀)))
        (fibrePoint (relProj (A := A) a₀) (relBase (A := A) a₀)) :=
      ⟨⟨fun x => ⟨ρ x, hρfib x⟩, Continuous.subtype_mk ρ.1.continuous hρfib⟩,
        fun x hx => Subtype.ext (by
          show ρ x = relBase (A := A) a₀
          exact (hρ_apply x).trans (hGbd ⟨x, hx⟩ 1))⟩
    have hρ1 : (⟦ρ⟧ : HomotopyGroup (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
        = (1 : HomotopyGroup (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀)) := by
      have hρ_eq : genLoopMap (Work.StemsB.fibreIncl (relProj (A := A) a₀)
            (relProj (A := A) a₀ (relBase (A := A) a₀))) 1 ρF = ρ := by
        apply GenLoop.ext
        intro x
        rfl
      have hconv : (⟦ρ⟧ : HomotopyGroup (Fin 1) (relFibre (A := A) a₀) (relBase (A := A) a₀))
          = Work.StemsB.πmap (Work.StemsB.fibreIncl (relProj (A := A) a₀)
                (relProj (A := A) a₀ (relBase (A := A) a₀))) 0
              (Work.StemsB.fibrePoint (relProj (A := A) a₀) (relBase (A := A) a₀)) ⟦ρF⟧ :=
        (congrArg Quotient.mk'' hρ_eq).symm
      have h1 : (⟦ρF⟧ : HomotopyGroup (Fin 1)
            (fibre (relProj (A := A) a₀) (relProj (A := A) a₀ (relBase (A := A) a₀)))
            (fibrePoint (relProj (A := A) a₀) (relBase (A := A) a₀)))
          = (1 : HomotopyGroup (Fin 1)
            (fibre (relProj (A := A) a₀) (relProj (A := A) a₀ (relBase (A := A) a₀)))
            (fibrePoint (relProj (A := A) a₀) (relBase (A := A) a₀))) :=
        @Subsingleton.elim _ hF _ _
      refine hconv.trans ((congrArg (Work.StemsB.πmap
        (Work.StemsB.fibreIncl (relProj (A := A) a₀)
          (relProj (A := A) a₀ (relBase (A := A) a₀))) 0
        (Work.StemsB.fibrePoint (relProj (A := A) a₀) (relBase (A := A) a₀))) h1).trans ?_)
      exact map_one _
    exact hγρ.trans hρ1
  exact subsingleton_of_forall_eq 1 key

end

end Work.Serre
