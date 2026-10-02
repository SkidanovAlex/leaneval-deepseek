import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.Excision
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.RatHurewicz.LESConsequences

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

open scoped Topology Topology.Homotopy unitInterval
open Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Type} [TopologicalSpace A]

/-! ## Auxiliary lemmas for the relative homotopy data of the mapping-cylinder inclusion

These are the tools with which `Work.Serre.cylRelPi` is assembled; none of them mentions the
mapping cylinder except `cylMoveHomotopy`, `cylIncl_comp_homotopyFibreFst_homotopic_const` and
`bijective_piMapN_cylIncl`. -/

/-! ### The push-up homotopy of the mapping cylinder, as an explicit homotopy -/

/-- The push-up homotopy of the mapping cylinder `s ↦ 1 - s` (`cylMove`), packaged as a homotopy
from `cylInr f ∘ cylRetract f` to the identity of `cyl f`.  (`Work.Serre.cylHomotopyEquiv`
constructs exactly this homotopy inside its proof; here it is made available as a term.) -/
def cylMoveHomotopy {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) :
    ((cylInr f).comp (cylRetract f)).Homotopy (ContinuousMap.id (cyl f)) where
  toContinuousMap := ⟨fun p : I × cyl f => cylMove f (p.2, unitIntervalOneSub p.1),
    (cylMove f).continuous.comp
      (continuous_snd.prodMk (continuous_unitIntervalOneSub.comp continuous_fst))⟩
  map_zero_left := fun y => by simp [cylMove_one]
  map_one_left := fun y => by simp [cylMove_zero]

/-! ### A map homotopic to a constant induces the trivial map on homotopy groups -/

/-- **The induced map on homotopy groups of a map homotopic to a constant is trivial.**  The
homotopy moves the value at the base point, so this is a statement about the base point change
`Work.Stems.Pinch.transport`: `transport p (πmap g n x a) = πmap (const y) n x a = 1` for
`p = homotopyPath H x`, whence `πmap g n x a = transport p.symm 1 = 1`. -/
theorem πmap_eq_one_of_homotopic_const {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(X, Y)) (n : ℕ) (x : X) (h : ∃ y : Y, g.Homotopic (ContinuousMap.const X y))
    (a : HomotopyGroup (Fin (n+1)) X x) : Work.StemsB.πmap g n x a = 1 := by
  obtain ⟨y, ⟨H⟩⟩ := h
  have h1 : Work.Stems.Pinch.transport (N := Fin (n+1)) (Work.Stems.Pinch.homotopyPath H x)
      (HomotopyGroup.map g a) = 1 := by
    rw [Work.Stems.Pinch.transport_map (N := Fin (n+1)) H x a]
    show Work.StemsB.πmap (ContinuousMap.const X y) n x a = 1
    exact Work.StemsB.πmap_const y n x a
  have h2 : Work.Stems.Pinch.transport (N := Fin (n+1))
      (Work.Stems.Pinch.homotopyPath H x).symm
      (1 : HomotopyGroup (Fin (n+1)) Y y) = 1 := by
    have hh := Work.Stems.Pinch.transport_map (N := Fin (n+1)) H.symm x
      (1 : HomotopyGroup (Fin (n+1)) X x)
    rw [Work.Stems.Pinch.homotopyPath_symm] at hh
    rw [show HomotopyGroup.map (ContinuousMap.const X y) (1 : HomotopyGroup (Fin (n+1)) X x) = 1
        from map_one (HomotopyGroup.mapHom (ContinuousMap.const X y)),
      show HomotopyGroup.map g (1 : HomotopyGroup (Fin (n+1)) X x) = 1
        from map_one (HomotopyGroup.mapHom g)] at hh
    exact hh
  change HomotopyGroup.map g a = 1
  rw [← Work.Stems.Pinch.transport_symm_apply (N := Fin (n+1))
    (Work.Stems.Pinch.homotopyPath H x) (HomotopyGroup.map g a)]
  rw [h1]
  exact h2

/-! ### The composite `cylIncl f ∘ homotopyFibreFst` is null-homotopic -/

/-- **The composite of the inclusion of the bottom of the mapping cylinder with the projection of
its homotopy fibre is null-homotopic**: a point of the homotopy fibre is a pair `(x, γ)` with `γ` a
path from `cylIncl f x₀` to `cylIncl f x`, and `t ↦ γ t` is a homotopy from the constant map at
`cylIncl f x₀` to `(cylIncl f) ∘ (homotopyFibreFst (cylIncl f) x₀)`. -/
theorem cylIncl_comp_homotopyFibreFst_homotopic_const
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (x₀ : X) :
    ∃ y : cyl f,
      (ContinuousMap.const (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀) y).Homotopic
        ((cylIncl f).comp (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)) := by
  refine ⟨cylIncl f x₀, ⟨{ toContinuousMap := ?_, map_zero_left := ?_, map_one_left := ?_ }⟩⟩
  · refine ⟨fun q : I × Work.RatHurewicz.homotopyFibre (cylIncl f) x₀ => q.2.1.2.1 q.1, ?_⟩
    have hp : Continuous fun p : Work.RatHurewicz.homotopyFibre (cylIncl f) x₀ => p.1.2.1 :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)
    exact continuous_eval.comp ((hp.comp continuous_snd).prodMk continuous_fst)
  · intro p
    exact p.1.2.2
  · intro p
    exact p.2

/-! ### `π_j` of the inclusion of the bottom of the mapping cylinder -/

/-- **The inclusion of the bottom copy of the mapping cylinder induces a bijection on `π_j`
(`j ≥ 1`) whenever `f` does.**  The composite `cylRetract f ∘ cylIncl f` is `f`
(`Work.Serre.cylRetract_cylIncl`), so `π_j(f) = π_j(cylRetract f) ∘ π_j(cylIncl f)`; the left hand
side is a bijection by hypothesis and `π_j(cylRetract f)` is one by the homotopy equivalence
`cyl f ≃ Y`, whence so is the middle map.  The bijectivity of `π_j(cylRetract f)` is obtained from
the explicit homotopies `cylMoveHomotopy f : cylInr f ∘ cylRetract f ~ id` (which gives injectivity
via the base point change `Work.Stems.Pinch.transport_map`) and
`cylRetract f ∘ cylInr f = id` (which gives surjectivity). -/
theorem bijective_piMapN_cylIncl {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (j : ℕ) (hj : 1 ≤ j) (y : X)
    (h : Function.Bijective (piMapN f j y)) :
    Function.Bijective (piMapN (cylIncl f) j y) := by
  haveI : Nonempty (Fin j) := ⟨⟨0, hj⟩⟩
  have H := cylMoveHomotopy f
  -- the diagonal map on `W` is injective and surjective
  have hgf_inj : Function.Injective
      (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) ((cylInr f).comp (cylRetract f))) := by
    intro u v huv
    have h1 : Work.Stems.Pinch.transport (N := Fin j)
        (Work.Stems.Pinch.homotopyPath H (cylIncl f y))
        (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) ((cylInr f).comp (cylRetract f)) u)
        = u := (Work.Stems.Pinch.transport_map (N := Fin j) H (cylIncl f y) u).trans
          (HomotopyGroup.map_id (N := Fin j) (x := cylIncl f y) u)
    have h2 : Work.Stems.Pinch.transport (N := Fin j)
        (Work.Stems.Pinch.homotopyPath H (cylIncl f y))
        (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) ((cylInr f).comp (cylRetract f)) v)
        = v := (Work.Stems.Pinch.transport_map (N := Fin j) H (cylIncl f y) v).trans
          (HomotopyGroup.map_id (N := Fin j) (x := cylIncl f y) v)
    exact h1.symm.trans (huv ▸ h2)
  have hgf_surj : Function.Surjective
      (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) ((cylInr f).comp (cylRetract f))) := by
    intro z
    refine ⟨Work.Stems.Pinch.transport (N := Fin j)
      (Work.Stems.Pinch.homotopyPath H (cylIncl f y)) z, ?_⟩
    have h1 : Work.Stems.Pinch.transport (N := Fin j)
        (Work.Stems.Pinch.homotopyPath H (cylIncl f y))
        (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) ((cylInr f).comp (cylRetract f))
          (Work.Stems.Pinch.transport (N := Fin j)
            (Work.Stems.Pinch.homotopyPath H (cylIncl f y)) z))
        = Work.Stems.Pinch.transport (N := Fin j)
            (Work.Stems.Pinch.homotopyPath H (cylIncl f y)) z :=
      (Work.Stems.Pinch.transport_map (N := Fin j) H (cylIncl f y)
        (Work.Stems.Pinch.transport (N := Fin j)
          (Work.Stems.Pinch.homotopyPath H (cylIncl f y)) z)).trans
        (HomotopyGroup.map_id (N := Fin j) (x := cylIncl f y)
          (Work.Stems.Pinch.transport (N := Fin j)
            (Work.Stems.Pinch.homotopyPath H (cylIncl f y)) z))
    have key := congrArg (Work.Stems.Pinch.transport (N := Fin j)
      (Work.Stems.Pinch.homotopyPath H (cylIncl f y)).symm) h1
    rw [Work.Stems.Pinch.transport_symm_apply (N := Fin j)
        (Work.Stems.Pinch.homotopyPath H (cylIncl f y))
        (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) ((cylInr f).comp (cylRetract f))
          (Work.Stems.Pinch.transport (N := Fin j)
            (Work.Stems.Pinch.homotopyPath H (cylIncl f y)) z)),
      Work.Stems.Pinch.transport_symm_apply (N := Fin j)
        (Work.Stems.Pinch.homotopyPath H (cylIncl f y)) z] at key
    exact key
  -- the inward map `cylInr f` is injective
  have hms_inj : Function.Injective (HomotopyGroup.map (N := Fin j)
      (x := cylRetract f (cylIncl f y)) (cylInr f)) := by
    intro c c' hcc'
    have h := congrArg (HomotopyGroup.map (N := Fin j)
      (x := cylInr f (cylRetract f (cylIncl f y))) (cylRetract f)) hcc'
    rw [← HomotopyGroup.map_comp (N := Fin j) (x := cylRetract f (cylIncl f y)) (cylInr f)
        (cylRetract f) c,
      ← HomotopyGroup.map_comp (N := Fin j) (x := cylRetract f (cylIncl f y)) (cylInr f)
        (cylRetract f) c'] at h
    have h1 : HomotopyGroup.map (N := Fin j) (x := cylRetract f (cylIncl f y))
        ((cylRetract f).comp (cylInr f)) c = c :=
      (rfl : HomotopyGroup.map (N := Fin j) (x := cylRetract f (cylIncl f y))
          ((cylRetract f).comp (cylInr f)) c
        = HomotopyGroup.map (N := Fin j) (x := cylRetract f (cylIncl f y))
            (ContinuousMap.id Y) c).trans
        (HomotopyGroup.map_id (N := Fin j) (x := cylRetract f (cylIncl f y)) c)
    have h2 : HomotopyGroup.map (N := Fin j) (x := cylRetract f (cylIncl f y))
        ((cylRetract f).comp (cylInr f)) c' = c' :=
      (rfl : HomotopyGroup.map (N := Fin j) (x := cylRetract f (cylIncl f y))
          ((cylRetract f).comp (cylInr f)) c'
        = HomotopyGroup.map (N := Fin j) (x := cylRetract f (cylIncl f y))
            (ContinuousMap.id Y) c').trans
        (HomotopyGroup.map_id (N := Fin j) (x := cylRetract f (cylIncl f y)) c')
    rw [h1, h2] at h
    exact h
  -- `cylRetract f` induces a bijection on `π_j`
  have hmr_inj : Function.Injective
      (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) (cylRetract f)) := by
    intro u v huv
    exact hgf_inj (by
      have h := congrArg (HomotopyGroup.map (N := Fin j)
        (x := cylRetract f (cylIncl f y)) (cylInr f)) huv
      rw [← HomotopyGroup.map_comp (N := Fin j) (x := cylIncl f y) (cylRetract f) (cylInr f),
        ← HomotopyGroup.map_comp (N := Fin j) (x := cylIncl f y) (cylRetract f) (cylInr f)] at h
      exact h)
  have hmr_surj : Function.Surjective
      (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) (cylRetract f)) := by
    intro z
    obtain ⟨a, ha⟩ := hgf_surj (HomotopyGroup.map (N := Fin j)
      (x := cylRetract f (cylIncl f y)) (cylInr f) z)
    rw [HomotopyGroup.map_comp (N := Fin j) (x := cylIncl f y) (cylRetract f) (cylInr f)] at ha
    exact ⟨a, hms_inj ha⟩
  -- the composite `π_j(f) = π_j(cylRetract f) ∘ π_j(cylIncl f)`
  have hcomp : ∀ a : HomotopyGroup (Fin j) X y,
      HomotopyGroup.map (N := Fin j) (x := y) f a
        = HomotopyGroup.map (N := Fin j) (x := cylIncl f y) (cylRetract f)
          (HomotopyGroup.map (N := Fin j) (x := y) (cylIncl f) a) := by
    intro a
    exact (rfl : HomotopyGroup.map (N := Fin j) (x := y) ((cylRetract f).comp (cylIncl f)) a
        = HomotopyGroup.map (N := Fin j) (x := y) f a).symm.trans
      (HomotopyGroup.map_comp (N := Fin j) (x := y) (cylIncl f) (cylRetract f) a)
  have hf : Function.Bijective (HomotopyGroup.map (N := Fin j) (x := y) f) := h
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hab' : HomotopyGroup.map (N := Fin j) (x := y) (cylIncl f) a
        = HomotopyGroup.map (N := Fin j) (x := y) (cylIncl f) b := hab
    exact hf.1 (by rw [hcomp a, hcomp b, hab'])
  · intro z
    obtain ⟨b, hb⟩ := hf.2 (HomotopyGroup.map (N := Fin j) (x := cylIncl f y) (cylRetract f) z)
    refine ⟨b, hmr_inj ?_⟩
    show HomotopyGroup.map (N := Fin j) (x := cylIncl f y) (cylRetract f)
        (HomotopyGroup.map (N := Fin j) (x := y) (cylIncl f) b)
      = HomotopyGroup.map (N := Fin j) (x := cylIncl f y) (cylRetract f) z
    rw [← hcomp b, hb]

/-! ### `π₀`-injectivity in geometric form -/

/-- The `0`-cube of `X` at the base point `x₀` whose value is `a` (the boundary of the `0`-cube is
empty, so there is no boundary condition).  Its class in `HomotopyGroup (Fin 0) X x₀` is the path
component of `a`. -/
def genLoopZero (X : Type) [TopologicalSpace X] (x₀ a : X) : Ω^ (Fin 0) X x₀ :=
  ⟨ContinuousMap.const (Fin 0 → I) a, fun y hy => absurd hy (by simp [Cube.boundary])⟩

/-- Two such `0`-cubes are homotopic as soon as their values are joined by a path. -/
theorem genLoopZero_homotopic {X : Type} [TopologicalSpace X] {x₀ a b : X} (p : Path a b) :
    GenLoop.Homotopic (genLoopZero X x₀ a) (genLoopZero X x₀ b) :=
  ⟨{ toFun := fun q : I × (Fin 0 → I) => p q.1
     continuous_toFun := p.continuous.comp continuous_fst
     map_zero_left := fun u => p.source
     map_one_left := fun u => p.target
     prop' := fun t u hu => absurd hu (by simp [Cube.boundary]) }⟩

/-- The map induced by `f` on `π₀` sends the class of `a` to the class of `f a`. -/
theorem piMapN_zero_genLoopZero {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x₀ a : X) :
    piMapN f 0 x₀ ⟦genLoopZero X x₀ a⟧ = ⟦genLoopZero Y (f x₀) (f a)⟧ := by
  rw [piMapN_apply_mk]
  refine congrArg (Quotient.mk _) (Subtype.ext ?_)
  exact ContinuousMap.ext (fun u => rfl)

/-- **Injectivity of `π₀(f)` in geometric form**: if `f x₀` and `f x` are joined in `Y`, then `x₀`
and `x` are joined in `X`. -/
theorem joined_of_piMapN_zero_injective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x₀ : X) (hinj : Function.Injective (piMapN f 0 x₀)) {x : X}
    (h : Joined (f x₀) (f x)) : Joined x₀ x := by
  obtain ⟨γ⟩ := h
  have h1 : (piMapN f 0 x₀ ⟦genLoopZero X x₀ x⟧ : HomotopyGroup (Fin 0) Y (f x₀))
      = piMapN f 0 x₀ ⟦genLoopZero X x₀ x₀⟧ := by
    rw [piMapN_zero_genLoopZero f x₀ x, piMapN_zero_genLoopZero f x₀ x₀]
    exact Quotient.sound (genLoopZero_homotopic γ.symm)
  have h2 : (⟦genLoopZero X x₀ x⟧ : HomotopyGroup (Fin 0) X x₀)
      = ⟦genLoopZero X x₀ x₀⟧ := hinj h1
  obtain ⟨H⟩ := Quotient.exact h2
  have hpath : Path x x₀ :=
    { toContinuousMap := ⟨fun t => H (t, fun _ => 0),
        H.continuous_toFun.comp (continuous_id.prodMk continuous_const)⟩
      source' := H.map_zero_left (fun _ => 0)
      target' := H.map_one_left (fun _ => 0) }
  exact Joined.symm ⟨hpath⟩

/-! ### The fibre inclusion is trivial on `π₁` when `π₂` of the map is onto -/

/-- **If `π₂(i)` is surjective, the inclusion of the fibre of `homotopyFibreFst i a₀` induces the
zero map on `π₁`.**  By exactness at `π₁` of the fibre (`Work.StemsB.les_exact_F` at `k = 0`) its
kernel is the image of the connecting map `fibreDMap i a₀ 0`; that connecting map is
`pairShiftHom i a₀ 0 ∘ πmap i 1 a₀` (`Work.RatHurewicz.fibreDMap_eq_pairShiftHom`), a bijection
composed with a surjection, hence surjective, so the kernel is everything. -/
theorem piMap_fibreIncl_eq_one_of_surjective {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A)
    (h : Function.Surjective (Work.StemsB.πmap i 1 a₀)) :
    ∀ y : HomotopyGroup (Fin 1) (Work.StemsB.fibre (Work.RatHurewicz.homotopyFibreFst i a₀)
        ((Work.RatHurewicz.homotopyFibreFst i a₀) (Work.RatHurewicz.homotopyFibreBasepoint i a₀)))
      (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)),
      Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
        ((Work.RatHurewicz.homotopyFibreFst i a₀) (Work.RatHurewicz.homotopyFibreBasepoint i a₀)))
        0 (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) y = 1 := by
  intro y
  have hF := Work.StemsB.les_exact_F (Work.RatHurewicz.homotopyFibreFst i a₀)
    (Work.RatHurewicz.homotopyFibreBasepoint i a₀) (Work.RatHurewicz.fibreHrel i a₀) 0
  obtain ⟨w, hw⟩ := (Work.RatHurewicz.pairShiftHom_bijective i a₀ 0).2 y
  obtain ⟨v, hv⟩ := h w
  refine (hF y).mpr ⟨v, ?_⟩
  show Work.RatHurewicz.fibreDMap i a₀ 0 v = y
  rw [Work.RatHurewicz.fibreDMap_eq_pairShiftHom i a₀ 0, MonoidHom.comp_apply, hv, hw]

/-! ### `π₁` of the homotopy fibre -/

/-- The path coordinate of a point of the homotopy fibre of `i`, as a continuous map `I → Y`. -/
def cylRelCMFamily (i : C(A, Y)) (a₀ : A) :
    C(Work.RatHurewicz.homotopyFibre i a₀, C(I, Y)) where
  toFun p := p.1.2.1
  continuous_toFun := continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)

/-- The coordinate swap `(x,t) ↦ (t,x)` on `I^{Fin 1} × I`. -/
abbrev cylRelSwap : C((Fin 1 → I) × I, I × (Fin 1 → I)) :=
  (ContinuousMap.snd : C((Fin 1 → I) × I, I)).prodMk
    (ContinuousMap.fst : C((Fin 1 → I) × I, Fin 1 → I))

/-- Evaluation of a loop at `1`. -/
abbrev cylRelEvalOne : C(Fin 1 → I, (Fin 1 → I) × I) :=
  (ContinuousMap.id (Fin 1 → I)).prodMk (ContinuousMap.const (Fin 1 → I) (1 : I))

/-- **The square of a loop of the homotopy fibre**: for `γ : Ω¹ E bp` the map
`(x,t) ↦ (γ x).1.2.1 t : I × I → Y`. -/
def cylRelSquare (i : C(A, Y)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :
    C((Fin 1 → I) × I, Y) :=
  ((cylRelCMFamily i a₀).comp γ.1).uncurry

@[simp]
theorem cylRelSquare_apply (i : C(A, Y)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) (x : Fin 1 → I) (t : I) :
    cylRelSquare i a₀ γ (x, t) = (γ x).1.2.1 t := rfl

/-- The bottom side of the square is constant at `i a₀`. -/
theorem cylRelSquare_zero (i : C(A, Y)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) (x : Fin 1 → I) :
    cylRelSquare i a₀ γ (x, 0) = i a₀ := (γ x).1.2.2

/-- The top side of the square is the projection of the loop. -/
theorem cylRelSquare_one (i : C(A, Y)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) (x : Fin 1 → I) :
    cylRelSquare i a₀ γ (x, 1) = i (Work.RatHurewicz.homotopyFibreFst i a₀ (γ x)) := (γ x).2

/-- The lateral sides of the square are constant at `i a₀`. -/
theorem cylRelSquare_bdry (i : C(A, Y)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
    {x : Fin 1 → I} (hx : x ∈ Cube.boundary (Fin 1)) (t : I) :
    cylRelSquare i a₀ γ (x, t) = i a₀ := by
  have hx' : γ x = Work.RatHurewicz.homotopyFibreBasepoint i a₀ := γ.2 x hx
  simp only [cylRelSquare_apply, hx']
  rfl

/-- **The homotopy from `γ` to the endpoint loop `ρ` of a lifted homotopy `G`, relative to the
boundary**: `(u,x) ↦ G (x,u)`. -/
def cylRelLoopHom (i : C(A, Y)) (a₀ : A)
    (γ ρ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
    (G : C((Fin 1 → I) × I, Work.RatHurewicz.homotopyFibre i a₀))
    (h0 : ∀ x, G (x, 0) = γ.1 x) (h1 : ∀ x, G (x, 1) = ρ.1 x)
    (hbd : ∀ (x : Work.StemsB.CubeBdry 1) (t : I),
      G (x.1, t) = Work.RatHurewicz.homotopyFibreBasepoint i a₀) :
    ContinuousMap.HomotopyRel γ.1 ρ.1 (Cube.boundary (Fin 1)) where
  toFun q := G (q.2, q.1)
  continuous_toFun := G.continuous.comp (by fun_prop)
  map_zero_left x := h0 x
  map_one_left x := h1 x
  prop' u x hx := (hbd ⟨x, hx⟩ u).trans (γ.2 x hx).symm

/-- **The square, with its coordinates interchanged, is a null-homotopy of the projection of the
loop**: the family `(u,x) ↦ γ(x,u)` runs from the constant loop to `i ∘ (homotopyFibreFst i a₀ ∘ γ)`,
with the lateral boundary fixed. -/
def cylRelSquareHom (i : C(A, Y)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :
    ContinuousMap.HomotopyRel
      (GenLoop.const : Ω^ (Fin 1) Y (i a₀)).1
      (genLoopMap i 1 (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)).1
      (Cube.boundary (Fin 1)) where
  toFun q := cylRelSquare i a₀ γ (q.2, q.1)
  continuous_toFun := (cylRelSquare i a₀ γ).continuous.comp (by fun_prop)
  map_zero_left x := by
    show cylRelSquare i a₀ γ (x, 0) = _
    rw [cylRelSquare_zero]
    rfl
  map_one_left x := by
    show cylRelSquare i a₀ γ (x, 1) = _
    rw [cylRelSquare_one]
    rfl
  prop' u x hx := by
    show cylRelSquare i a₀ γ (x, u) = _
    rw [cylRelSquare_bdry i a₀ γ hx u]
    rfl

/-- **The class of the projection of a loop of the homotopy fibre is trivial in the ambient
space.** -/
theorem cylRelSquareHom_class (i : C(A, Y)) (a₀ : A)
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :
    (⟦genLoopMap i 1 (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)⟧
      : HomotopyGroup (Fin 1) Y (i a₀)) = (1 : HomotopyGroup (Fin 1) Y (i a₀)) := by
  refine (Quotient.sound ?_).trans HomotopyGroup.one_def.symm
  exact ⟨(cylRelSquareHom i a₀ γ).symm⟩

/-- **The projected loop of a loop of the homotopy fibre is null-homotopic in `A`**, by injectivity
of `π₁(A) → π₁(Y)`. -/
theorem cylRelProj_class_eq_one (i : C(A, Y)) (a₀ : A)
    (hinj : Function.Injective (Work.StemsB.πmap i 0 a₀))
    (γ : Ω^ (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :
    (⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧
      : HomotopyGroup (Fin 1) A a₀) = (1 : HomotopyGroup (Fin 1) A a₀) := by
  refine hinj ?_
  have key : (Work.StemsB.πmap i 0 a₀)
      ⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧
      = (1 : HomotopyGroup (Fin 1) Y (i a₀)) := by
    show (⟦genLoopMap i 1 (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)⟧
      : HomotopyGroup (Fin 1) Y (i a₀)) = (1 : HomotopyGroup (Fin 1) Y (i a₀))
    exact cylRelSquareHom_class i a₀ γ
  rw [key]
  exact (map_one (Work.StemsB.πmap i 0 a₀)).symm

/-- `π₁` of the homotopy fibre of `i` at `a₀` is trivial when `π₁(i)` is injective and the fibre of
the projection `homotopyFibreFst i a₀` induces the zero map on `π₁`.
This generalises `Work.Serre.relPi_one_subsingleton`.

Given a loop `γ` of the homotopy fibre, the transposed square `cylRelSquareHom` exhibits a
null-homotopy of its projection in `Y`, so that projection is null-homotopic in `A` by `hinj`; the
homotopy lifting property of the Serre fibration `homotopyFibreFst i a₀`
(`Work.RatHurewicz.fibreHrel`) then lifts that null-homotopy to a homotopy of `γ` to a loop `ρ`
lying in the fibre, where `hzero` kills it. -/
theorem subsingleton_pi_one_homotopyFibre {Y : Type} [TopologicalSpace Y] {A : Type}
    [TopologicalSpace A] (i : C(A, Y)) (a₀ : A)
    (hinj : Function.Injective (Work.StemsB.πmap i 0 a₀))
    (hzero : ∀ y : HomotopyGroup (Fin 1)
        (Work.StemsB.fibre (Work.RatHurewicz.homotopyFibreFst i a₀)
          ((Work.RatHurewicz.homotopyFibreFst i a₀)
            (Work.RatHurewicz.homotopyFibreBasepoint i a₀)))
        (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)),
      Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
        ((Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)))
        0 (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) y = 1) :
    Subsingleton (HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
  classical
  have key : ∀ z : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀),
      z = (1 : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
    intro z
    refine Quotient.inductionOn z (fun γ => ?_)
    -- (1) the projected loop is null-homotopic in `A`
    have hα : (⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧
        : HomotopyGroup (Fin 1) A a₀) = (1 : HomotopyGroup (Fin 1) A a₀) :=
      cylRelProj_class_eq_one i a₀ hinj γ
    have hΘ : GenLoop.Homotopic (genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ)
        (GenLoop.const : Ω^ (Fin 1) A a₀) := by
      have h : (⟦genLoopMap (Work.RatHurewicz.homotopyFibreFst i a₀) 1 γ⟧
          : HomotopyGroup (Fin 1) A a₀) = ⟦(GenLoop.const : Ω^ (Fin 1) A a₀)⟧ := by
        rw [hα, HomotopyGroup.one_def]
      exact Quotient.exact h
    obtain ⟨Θ⟩ := hΘ
    -- (2) lift the null-homotopy along the fibration `E → A`
    let Hbase : C((Fin 1 → I) × I, A) :=
      ⟨fun q => Θ (q.2, q.1), Θ.continuous_toFun.comp cylRelSwap.continuous⟩
    have hHbase0 : ∀ x : Fin 1 → I,
        Hbase (x, 0) = Work.RatHurewicz.homotopyFibreFst i a₀ (γ x) :=
      fun x => Θ.map_zero_left x
    have hHbase_bdry : ∀ (x : Work.StemsB.CubeBdry 1) (t : I), Hbase (x.1, t) = a₀ := by
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
        (ContinuousMap.const (Work.StemsB.CubeBdry 1 × I)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
        (ContinuousMap.ext (fun q : Work.StemsB.CubeBdry 1 × I => by
          change Work.RatHurewicz.homotopyFibreFst i a₀
              (Work.RatHurewicz.homotopyFibreBasepoint i a₀) = Hbase (q.1.1, q.2)
          rw [show Work.RatHurewicz.homotopyFibreFst i a₀
                (Work.RatHurewicz.homotopyFibreBasepoint i a₀) = a₀ from rfl,
            hHbase_bdry q.1 q.2]))
        (by intro x; exact (γ.2 x.1 x.2).symm)
    -- (3) the endpoint of the lifted homotopy is a loop of the fibre
    let ρcm : C(Fin 1 → I, Work.RatHurewicz.homotopyFibre i a₀) := G.comp cylRelEvalOne
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
        cylRelLoopHom i a₀ γ ρ G hG0 (fun x => (hρ_apply x).symm) hGbd
      exact Quotient.sound (show GenLoop.Homotopic γ ρ from ⟨hhom⟩)
    -- (5) `ρ` lies in the fibre, where the inclusion of the fibre is trivial and `π₁` vanishes
    have hρfib : ∀ x, Work.RatHurewicz.homotopyFibreFst i a₀ (ρ x)
        = Work.RatHurewicz.homotopyFibreFst i a₀
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀) := by
      intro x
      have h1 : Work.RatHurewicz.homotopyFibreFst i a₀ (G (x, 1)) = Hbase (x, 1) :=
        congrFun (congrArg DFunLike.coe hGp) (x, 1)
      have h2 : Hbase (x, 1) = a₀ := Θ.map_one_left x
      rw [hρ_apply x, h1, h2, show Work.RatHurewicz.homotopyFibreFst i a₀
            (Work.RatHurewicz.homotopyFibreBasepoint i a₀) = a₀ from rfl]
    let ρF : Ω^ (Fin 1) (Work.StemsB.fibre (Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreFst i a₀
            (Work.RatHurewicz.homotopyFibreBasepoint i a₀)))
        (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) :=
      ⟨⟨fun x => ⟨ρ x, hρfib x⟩, Continuous.subtype_mk ρ.1.continuous hρfib⟩,
        fun x hx => Subtype.ext (by
          show ρ x = Work.RatHurewicz.homotopyFibreBasepoint i a₀
          exact (hρ_apply x).trans (hGbd ⟨x, hx⟩ 1))⟩
    have hρ1 : (⟦ρ⟧ : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
        (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
        = (1 : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
          (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
      have hρ_eq : genLoopMap (Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
            (Work.RatHurewicz.homotopyFibreFst i a₀
              (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) 1 ρF = ρ := by
        apply GenLoop.ext
        intro x
        rfl
      have hconv : (⟦ρ⟧ : HomotopyGroup (Fin 1) (Work.RatHurewicz.homotopyFibre i a₀)
            (Work.RatHurewicz.homotopyFibreBasepoint i a₀))
          = Work.StemsB.πmap (Work.StemsB.fibreIncl (Work.RatHurewicz.homotopyFibreFst i a₀)
              (Work.RatHurewicz.homotopyFibreFst i a₀
                (Work.RatHurewicz.homotopyFibreBasepoint i a₀))) 0
              (Work.StemsB.fibrePoint (Work.RatHurewicz.homotopyFibreFst i a₀)
                (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) ⟦ρF⟧ :=
        (congrArg Quotient.mk'' hρ_eq).symm
      exact hconv.trans (hzero ⟦ρF⟧)
    exact hγρ.trans hρ1
  exact subsingleton_of_forall_eq 1 key

/-! ## The target -/

/-- **The relative homotopy data of the mapping-cylinder inclusion.**

Let `f : X → Y`, `x₀ : X`, `W = cyl f` and `i = cylIncl f : C(X, W)` (the bottom copy `X × {0}` of
the mapping cylinder, `Submission/Work/Serre/C1Cyl.lean`).  Assume `πₖ(f)` is bijective at every
base point for `k < n + 2`.  Then, for the homotopy fibre `F = homotopyFibre i x₀` of `i`:
* `RelHomotopyGroup i x₀ k = π_k(F)` is trivial for `k ≤ n`, and
* the projection `homotopyFibreFst i x₀ : F → X` induces the zero map on `π_{n+1}`.

Reasoning: `W ≃ Y` (`cylHomotopyEquiv`) and the composite `X --i--> W ≃ Y` is `f`
(`cylRetract_cylIncl`), so `π_*(F)` is `π_*` of the homotopy fibre of `f`
(`Work.RatHurewicz.homotopyFibreMap`, `Work.Stems.mulEquiv_of_homotopyEquiv`), and the π-bijectivity
of `f` (with the fibration sequence `Work.StemsB.fibrationLES_of_serre`) kills those groups in
degrees `k ≤ n`: for `j ≤ n` surjectivity of `π_{j+1}(X) → π_{j+1}(Y)` and injectivity of
`π_j(X) → π_j(Y)` together give `π_j(F) = 0` (the fibration sequence is exact at `π_j(F)`).
The second clause is the exactness of the pair sequence (`Work.RatHurewicz.pair_les`) at `π_{n+1}(X)`:
the image of the projection is the kernel of `π_{n+1}(X) → π_{n+1}(W)`, which is injective because
it is `π_{n+1}(f)` up to the identifications (for the low degrees `n = 0, 1` use the fibration
sequence directly rather than `pair_les`, which requires `1 ≤ k`). -/
theorem cylRelPi {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x₀ : X) (n : ℕ)
    (h : ∀ (i : ℕ), i < n + 2 → ∀ y : X, Function.Bijective (piMapN f i y)) :
    (∀ k : ℕ, k + 1 ≤ n + 1 → Subsingleton
        (Work.RatHurewicz.RelHomotopyGroup (cylIncl f) x₀ k)) ∧
    (∀ a : Work.RatHurewicz.RelHomotopyGroup (cylIncl f) x₀ (n+1),
      piMapN (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀) (n+1)
        (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀) a = 1) := by
  classical
  -- `π_m` of the inclusion `cylIncl f`, for `m ≤ n`
  have hbij : ∀ m : ℕ, m ≤ n → Function.Bijective (Work.StemsB.πmap (cylIncl f) m x₀) :=
    fun m hm => bijective_piMapN_cylIncl f (m+1) (by omega) x₀ (h (m+1) (by omega) x₀)
  -- the composite `cylIncl f ∘ homotopyFibreFst` is null-homotopic
  have hnull : ∃ y : cyl f,
      ((cylIncl f).comp (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)).Homotopic
        (ContinuousMap.const _ y) :=
    (cylIncl_comp_homotopyFibreFst_homotopic_const f x₀).imp (fun y hy => hy.symm)
  -- the projection of the homotopy fibre is trivial on `π_{m+1}` for `m ≤ n`
  have hfst : ∀ (m : ℕ), m ≤ n → ∀ a : HomotopyGroup (Fin (m+1))
        (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀)
        (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀),
      Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀) m
        (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀) a = 1 := by
    intro m hm a
    refine (hbij m hm).1 ?_
    have hc : Work.StemsB.πmap
        ((cylIncl f).comp (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)) m
        (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀) a
        = Work.StemsB.πmap (cylIncl f) m x₀
          (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀) m
            (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀) a) :=
      (Work.StemsB.πmap_comp_apply (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)
        (cylIncl f) m (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀) a)
    rw [← hc]
    exact πmap_eq_one_of_homotopic_const _ m _ hnull a
  refine ⟨?_, ?_⟩
  · intro k hk
    have hkn : k ≤ n := by omega
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- `k = 0`: the homotopy fibre is path connected
      subst hk0
      have hpc : PathConnectedSpace (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀) := by
        refine pathConnectedSpace_homotopyFibre (cylIncl f) x₀ ?_ (hbij 0 (by omega)).2
        intro a ha
        obtain ⟨γ⟩ := ha
        exact joined_of_piMapN_zero_injective f x₀ (h 0 (by omega) x₀).1
          ⟨γ.map (cylRetract f).continuous⟩
      haveI : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀)) :=
        (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
      exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy
        (X := Work.RatHurewicz.homotopyFibre (cylIncl f) x₀)
        (x := Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀)).injective
          (Subsingleton.elim _ _)⟩
    · rcases eq_or_lt_of_le (show 1 ≤ k from hkpos) with hk1 | hk2
      · -- `k = 1`
        subst hk1
        refine subsingleton_pi_one_homotopyFibre (cylIncl f) x₀ (hbij 0 (by omega)).1 ?_
        exact piMap_fibreIncl_eq_one_of_surjective (cylIncl f) x₀ (hbij 1 hkn).2
      · -- `k ≥ 2`: the pair sequence
        have hk1' : 1 ≤ k := by omega
        obtain ⟨del, d, h1, h2, h3, h4⟩ :=
          Work.RatHurewicz.pair_les (cylIncl f) x₀ (k-1) (by omega)
        -- the connecting map `π_{k+1}(cyl f) → π_k(F)` is trivial
        have hd : ∀ z : HomotopyGroup (Fin ((k-1)+2)) (cyl f) (cylIncl f x₀), d z = 1 :=
          fun z => (h3 z).mpr ((hbij ((k-1)+1) (by omega)).2 z)
        -- the projection `π_k(F) → π_k(X)` is trivial
        have hkey : ∀ y : Work.RatHurewicz.RelHomotopyGroup (cylIncl f) x₀ ((k-1)+1),
            y = 1 := by
          intro y
          obtain ⟨z, hz⟩ := (h4 y).mp (hfst (k-1) (by omega) y)
          rw [← hz, hd z]
        rw [show k = (k-1)+1 from (Nat.sub_add_cancel hk1').symm]
        exact ⟨fun y y' => by rw [hkey y, hkey y']⟩
  · -- the projection is trivial on `π_{n+1}`
    intro a
    exact hfst n le_rfl a

end

end Work.Serre
