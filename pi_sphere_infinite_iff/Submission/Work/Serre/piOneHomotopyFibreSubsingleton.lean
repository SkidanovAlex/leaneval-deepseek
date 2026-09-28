import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.isSerreFibration_homotopyFibreFst
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.RatHurewicz.PairShiftBijective
import Submission.Work.RatHurewicz.PairLESCrux
import Submission.Work.StemsB.PiMap

/-!
# `π₁` of the homotopy fibre of a general map vanishes under the classical low-degree hypotheses

Generalisation of `Work.Serre.relPi_one_subsingleton` (the case `i = setIncl A : ↥A → Y`) to an
arbitrary continuous map `i : C(A, X)`: the homotopy fibre `F = homotopyFibre i a₀` has trivial `π₁`
as soon as

* `π₁(i)` is injective, and
* the fibre inclusion `π₁(ΩX) → π₁(F)` of the projection `homotopyFibreFst i a₀ : F → A` is the
  zero map.  This holds in either of the two classical situations:
  - `π₂(X, i a₀) = 0` (`piOneHomotopyFibreSubsingleton`, since `π₁(ΩX) ≅ π₂(X)`), or
  - `π₂(i)` is surjective (`piOneHomotopyFibreSubsingleton_of_surjective`, since then the
    connecting map `π₂(A) → π₁(ΩX)` is onto and its image is the kernel of the fibre inclusion).

The proof of the common core `piOne_of_fibreIncl_zero` is the classical one, verbatim from
`relPi_one_subsingleton`:

* a loop `γ` of `F` gives a square `β(x,t) = (γ x)'s path at time t`, whose read-out with the
  coordinates interchanged is a null-homotopy of `i ∘ (fst ∘ γ)`; by injectivity of `π₁(i)` the
  projected loop `fst ∘ γ` is null-homotopic in `A`;
* the relative homotopy lifting property of the Serre fibration `homotopyFibreFst i a₀`
  (`Work.RatHurewicz.fibreHrel`) lifts that null-homotopy to a homotopy from `γ` to a loop `ρ` of
  the fibre `ΩX`;
* that loop lies in the image of `π₁(ΩX) → π₁(F)`, which is zero by hypothesis, so `ρ` and hence
  `γ` is null-homotopic.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Serre

open Work.StemsB

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

variable {X : Type} [TopologicalSpace X] {A : Type} [TopologicalSpace A]

/-- The fibre of the projection `homotopyFibreFst i a₀ : homotopyFibre i a₀ → A`. -/
private abbrev fibOf (i : C(A, X)) (a₀ : A) : Type _ :=
  fibre (Work.RatHurewicz.homotopyFibreFst i a₀)
    ((Work.RatHurewicz.homotopyFibreFst i a₀) (Work.RatHurewicz.homotopyFibreBasepoint i a₀))

/-- The base point of that fibre. -/
private abbrev fibOfPt (i : C(A, X)) (a₀ : A) : fibOf i a₀ :=
  fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
    (Work.RatHurewicz.homotopyFibreBasepoint i a₀)

/-! ## The path component of a point of the homotopy fibre, as a continuous family -/

/-- The path component of a point of the homotopy fibre `homotopyFibre i a₀`, as a continuous map
`I → X`. -/
private def cmPath {i : C(A, X)} {a₀ : A} (p : Work.RatHurewicz.homotopyFibre i a₀) : C(I, X) :=
  p.1.2.1

private theorem cmPath_zero {i : C(A, X)} {a₀ : A}
    (p : Work.RatHurewicz.homotopyFibre i a₀) : cmPath p 0 = i a₀ := p.1.2.2

private theorem cmPath_one {i : C(A, X)} {a₀ : A}
    (p : Work.RatHurewicz.homotopyFibre i a₀) : cmPath p 1 = i p.1.1 := p.2

/-- The path component, as a continuous map out of the homotopy fibre. -/
private def cmFamily (i : C(A, X)) (a₀ : A) :
    C(Work.RatHurewicz.homotopyFibre i a₀, C(I, X)) where
  toFun p := cmPath p
  continuous_toFun :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

@[simp]
private theorem cmFamily_apply (i : C(A, X)) (a₀ : A)
    (p : Work.RatHurewicz.homotopyFibre i a₀) : cmFamily i a₀ p = cmPath p := rfl

/-! ## The square attached to a loop of the homotopy fibre -/

/-- The coordinate swap `(x, t) ↦ (t, x)`. -/
private abbrev swapC : C((Fin 1 → I) × I, I × (Fin 1 → I)) :=
  (ContinuousMap.snd : C((Fin 1 → I) × I, I)).prodMk
    (ContinuousMap.fst : C((Fin 1 → I) × I, Fin 1 → I))

/-- Evaluation at `1`. -/
private abbrev evalOneC : C(Fin 1 → I, (Fin 1 → I) × I) :=
  (ContinuousMap.id (Fin 1 → I)).prodMk (ContinuousMap.const (Fin 1 → I) (1 : I))

/-- **The square of a loop of the homotopy fibre**: for `γ : Ω^{1} F bp` the map
`(x,t) ↦ (γ x).1.2.1 t`. -/
private def sq (i : C(A, X)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) : C((Fin 1 → I) × I, X) :=
  ((cmFamily i a₀).comp γ.1).uncurry

@[simp]
private theorem sq_apply (i : C(A, X)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) (x : Fin 1 → I) (t : I) :
    sq i a₀ γ (x, t) = cmPath (γ x) t := rfl

private theorem sq_zero (i : C(A, X)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) (x : Fin 1 → I) :
    sq i a₀ γ (x, 0) = i a₀ := cmPath_zero (γ x)

private theorem sq_one (i : C(A, X)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) (x : Fin 1 → I) :
    sq i a₀ γ (x, 1) = i (Work.RatHurewicz.homotopyFibreFst i a₀ (γ x)) := cmPath_one (γ x)

private theorem sq_bdry (i : C(A, X)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
    {x : Fin 1 → I} (hx : x ∈ Cube.boundary (Fin 1)) (t : I) : sq i a₀ γ (x, t) = i a₀ := by
  have hx' : γ x = Work.RatHurewicz.homotopyFibreBasepoint i a₀ := γ.2 x hx
  rw [show sq i a₀ γ (x, t) = (γ x).1.2.1 t from rfl, hx']
  rw [show (Work.RatHurewicz.homotopyFibreBasepoint i a₀).1.2.1
    = ContinuousMap.const I (i a₀) from rfl]
  rfl

/-! ## The induced null-homotopy of the projected loop -/

/-- **The square, with the coordinates interchanged, is a null-homotopy of the projection of the
loop.** -/
private def sqHom (i : C(A, X)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :
    ContinuousMap.HomotopyRel
      (GenLoop.const : Ω^ (Fin 1) X (i a₀)).1
      (genLoopMap i 1
        (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)).1
      (Cube.boundary (Fin 1)) where
  toFun q := sq i a₀ γ (q.2, q.1)
  continuous_toFun := (sq i a₀ γ).continuous.comp (by fun_prop)
  map_zero_left x := by
    show sq i a₀ γ (x, 0) = _
    rw [sq_zero]
    rfl
  map_one_left x := by
    show sq i a₀ γ (x, 1) = _
    rw [sq_one]
    rfl
  prop' u x hx := by
    show sq i a₀ γ (x, u) = _
    rw [sq_bdry i a₀ γ hx u]
    rfl

private theorem sqHom_class (i : C(A, X)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :
    (⟦genLoopMap i 1 (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)⟧ :
      HomotopyGroup (Fin 1) X (i a₀)) = (1 : HomotopyGroup (Fin 1) X (i a₀)) := by
  refine (Quotient.sound ?_).trans HomotopyGroup.one_def.symm
  exact ⟨(sqHom i a₀ γ).symm⟩

/-- **The projected loop of a loop of the homotopy fibre is null-homotopic in `A`**, by injectivity
of `π₁(i)`. -/
private theorem proj_class_eq_one (i : C(A, X)) (a₀ : A)
    (hinj : Function.Injective (πmap i 0 a₀))
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :
    (⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧ :
      HomotopyGroup (Fin 1) A a₀) = (1 : HomotopyGroup (Fin 1) A a₀) := by
  refine hinj ?_
  have key : (πmap i 0 a₀)
      ⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧
      = (1 : HomotopyGroup (Fin 1) X (i a₀)) := by
    show (⟦genLoopMap i 1
        (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)⟧ :
      HomotopyGroup (Fin 1) X (i a₀)) = (1 : HomotopyGroup (Fin 1) X (i a₀))
    exact sqHom_class i a₀ γ
  rw [key, map_one]

/-! ## Triviality of `π₁` of the fibre of the projection -/

/-- **`π₁` of the fibre of the projection is trivial** when `π₂(X) = 0` and the loop-space shift
`pairShiftHom 0 : π₂(X) → π₁(ΩX)` is a bijection. -/
private theorem fibre_piOne_subsingleton (i : C(A, X)) (a₀ : A)
    (hX2 : Subsingleton (HomotopyGroup (Fin 2) X (i a₀))) :
    Subsingleton (HomotopyGroup (Fin 1) (fibOf i a₀) (fibOfPt i a₀)) := by
  have hbij := Work.RatHurewicz.pairShiftHom_bijective i a₀ 0
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hbij.2 x
  obtain ⟨b, rfl⟩ := hbij.2 y
  rw [@Subsingleton.elim _ hX2 a b]

/-! ## The common core -/

/-- **`π₁` of the homotopy fibre vanishes** when `π₁(i)` is injective and the fibre inclusion
`π₁(ΩX) → π₁(F)` is the zero map. -/
theorem piOne_of_fibreIncl_zero (i : C(A, X)) (a₀ : A)
    (hinj : Function.Injective (πmap i 0 a₀))
    (hzero : ∀ y : HomotopyGroup (Fin 1) (fibOf i a₀) (fibOfPt i a₀),
      πmap (fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
        ((Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) 0 (fibOfPt i a₀) y = 1) :
    Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
  classical
  have key : ∀ z : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀), z = 1 := by
    intro z
    refine Quotient.inductionOn z (fun γ => ?_)
    -- (1) the projected loop is null-homotopic in `A`
    have hα : (⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧ :
        HomotopyGroup (Fin 1) A a₀) = (1 : HomotopyGroup (Fin 1) A a₀) :=
      proj_class_eq_one i a₀ hinj γ
    have hΘ : GenLoop.Homotopic (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)
        (GenLoop.const : Ω^ (Fin 1) A a₀) := by
      have h : (⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧ :
          HomotopyGroup (Fin 1) A a₀)
          = ⟦(GenLoop.const : Ω^ (Fin 1) A a₀)⟧ := by
        rw [hα, HomotopyGroup.one_def]
      exact Quotient.exact h
    obtain ⟨Θ⟩ := hΘ
    -- (2) lift the null-homotopy along the fibration `F → A`
    let Hbase : C((Fin 1 → I) × I, A) :=
      ⟨fun q => Θ (q.2, q.1), Θ.continuous_toFun.comp swapC.continuous⟩
    have hHbase0 : ∀ x : Fin 1 → I, Hbase (x, 0) =
        Work.RatHurewicz.homotopyFibreFst i a₀ (γ x) := fun x => Θ.map_zero_left x
    have hHbase_bdry : ∀ (x : CubeBdry 1) (t : I), Hbase (x.1, t) = a₀ := by
      intro x t
      have h1 : Hbase (x.1, t)
          = (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ).1 x.1 :=
        Θ.prop t x.1 x.2
      rw [h1, show (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ).1 x.1
            = Work.RatHurewicz.homotopyFibreFst i a₀ (γ x.1) from rfl,
        show γ x.1 = Work.RatHurewicz.homotopyFibreBasepoint i a₀ from γ.2 x.1 x.2]
      rfl
    obtain ⟨G, hGp, hG0, hGbd⟩ :=
      Work.RatHurewicz.fibreHrel i a₀ 1 Hbase γ.1
        (ContinuousMap.ext (fun x : Fin 1 → I => by
          change Work.RatHurewicz.homotopyFibreFst i a₀ (γ x) = Hbase (x, 0)
          exact (hHbase0 x).symm))
        (ContinuousMap.const (CubeBdry 1 × I) (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
        (ContinuousMap.ext (fun q : CubeBdry 1 × I => by
          change Work.RatHurewicz.homotopyFibreFst i a₀
            (Work.RatHurewicz.homotopyFibreBasepoint i a₀) = Hbase (q.1.1, q.2)
          rw [show Work.RatHurewicz.homotopyFibreFst i a₀
              (Work.RatHurewicz.homotopyFibreBasepoint i a₀) = a₀ from rfl, hHbase_bdry q.1 q.2]))
        (by intro x; exact (γ.2 x.1 x.2).symm)
    -- (3) the endpoint loop of the lift
    let ρcm : C(Fin 1 → I, Work.RatHurewicz.homotopyFibre i a₀) := G.comp evalOneC
    have hρcm : ∀ x, ρcm x = G (x, 1) := fun x => rfl
    have hρbdry : ∀ x ∈ Cube.boundary (Fin 1),
        ρcm x = Work.RatHurewicz.homotopyFibreBasepoint i a₀ := by
      intro x hx
      rw [hρcm]
      exact hGbd ⟨x, hx⟩ 1
    let ρ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀) := ⟨ρcm, hρbdry⟩
    have hρ_apply : ∀ x, ρ x = G (x, 1) := fun x => rfl
    -- (4) `γ` is homotopic to `ρ`
    have hγρ : (⟦γ⟧ : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) = ⟦ρ⟧ := by
      have hhom : ContinuousMap.HomotopyRel γ.1 ρ.1 (Cube.boundary (Fin 1)) :=
        { toFun := fun q => G (q.2, q.1)
          continuous_toFun := G.continuous.comp (by fun_prop)
          map_zero_left := fun x => hG0 x
          map_one_left := fun x => (hρ_apply x).symm
          prop' := fun u x hx => (hGbd ⟨x, hx⟩ u).trans (γ.2 x hx).symm }
      exact Quotient.sound (show GenLoop.Homotopic γ ρ from ⟨hhom⟩)
    -- (5) `ρ` lies in the fibre, whose `π₁` maps to zero in `π₁(F)`
    have hρfib : ∀ x, Work.RatHurewicz.homotopyFibreFst i a₀ (ρ x)
        = Work.RatHurewicz.homotopyFibreFst i a₀
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀) := by
      intro x
      have h1 : Work.RatHurewicz.homotopyFibreFst i a₀ (G (x, 1)) = Hbase (x, 1) :=
        congrFun (congrArg DFunLike.coe hGp) (x, 1)
      have h2 : Hbase (x, 1) = a₀ := Θ.map_one_left x
      rw [hρ_apply x, h1, h2,
        show Work.RatHurewicz.homotopyFibreFst i a₀
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀) = a₀ from rfl]
    let ρF : Ω^ (Fin 1) (fibOf i a₀) (fibOfPt i a₀) :=
      ⟨⟨fun x => ⟨ρ x, hρfib x⟩, Continuous.subtype_mk ρ.1.continuous hρfib⟩,
        fun x hx => Subtype.ext (by
          show ρ x = Work.RatHurewicz.homotopyFibreBasepoint i a₀
          exact (hρ_apply x).trans (hGbd ⟨x, hx⟩ 1))⟩
    have hρ1 : (⟦ρ⟧ : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
        = (1 : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
      have hρ_eq : genLoopMap (fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
            ((Work.RatHurewicz.homotopyFibreFst i a₀)
              (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) 1 ρF = ρ := by
        apply GenLoop.ext
        intro x
        rfl
      have hconv : (⟦ρ⟧ : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
          = πmap (fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
                ((Work.RatHurewicz.homotopyFibreFst i a₀)
                  (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) 0
              (fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
                (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) ⟦ρF⟧ :=
        (congrArg Quotient.mk'' hρ_eq).symm
      rw [hconv]
      exact hzero ⟦ρF⟧
    exact hγρ.trans hρ1
  exact ⟨fun x y => (key x).trans (key y).symm⟩

/-! ## The two classical specialisations -/

/-- **`π₁` of the homotopy fibre vanishes when `π₂(X, i a₀) = 0`.**  Generalisation of
`Work.Serre.relPi_one_subsingleton` to an arbitrary map. -/
theorem piOneHomotopyFibreSubsingleton (i : C(A, X)) (a₀ : A)
    (hinj : Function.Injective (πmap i 0 a₀))
    (hX2 : Subsingleton (HomotopyGroup (Fin 2) X (i a₀))) :
    Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
  refine piOne_of_fibreIncl_zero i a₀ hinj (fun y => ?_)
  have hsub := fibre_piOne_subsingleton i a₀ hX2
  haveI := hsub
  rw [Subsingleton.elim y (1 : HomotopyGroup (Fin 1) (fibOf i a₀) (fibOfPt i a₀))]
  exact map_one _

/-- **The fibre inclusion is trivial on `π₁` when `π₂(i)` is surjective.** -/
private theorem piMap_fibreIncl_eq_one_of_surjective (i : C(A, X)) (a₀ : A)
    (h : Function.Surjective (πmap i 1 a₀)) :
    ∀ y : HomotopyGroup (Fin 1) (fibOf i a₀) (fibOfPt i a₀),
      πmap (fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
        ((Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) 0 (fibOfPt i a₀) y = 1 := by
  intro y
  have hF := Work.StemsB.les_exact_F (Work.RatHurewicz.homotopyFibreFst i a₀)
    (Work.RatHurewicz.homotopyFibreBasepoint i a₀) (Work.RatHurewicz.fibreHrel i a₀) 0
  obtain ⟨w, hw⟩ := (Work.RatHurewicz.pairShiftHom_bijective i a₀ 0).2 y
  obtain ⟨v, hv⟩ := h w
  refine (hF y).mpr ⟨v, ?_⟩
  show Work.RatHurewicz.fibreDMap i a₀ 0 v = y
  rw [Work.RatHurewicz.fibreDMap_eq_pairShiftHom i a₀ 0, MonoidHom.comp_apply, hv, hw]

/-- **`π₁` of the homotopy fibre vanishes when `π₂(i)` is surjective.**  (Then the connecting map
`π₂(A) → π₁(ΩX)` is onto, so the fibre inclusion is zero on `π₁`.) -/
theorem piOneHomotopyFibreSubsingleton_of_surjective (i : C(A, X)) (a₀ : A)
    (hinj : Function.Injective (πmap i 0 a₀))
    (hsurj : Function.Surjective (πmap i 1 a₀)) :
    Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :=
  piOne_of_fibreIncl_zero i a₀ hinj (piMap_fibreIncl_eq_one_of_surjective i a₀ hsurj)

end

end Work.Serre
