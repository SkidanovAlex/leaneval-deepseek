import Mathlib
import Submission.Work.Stems.Pi
import Submission.Work.Stems.Pinch
import Submission.Work.Stems.HomotopyGroupMap
import Submission.Work.Stems.subsingleton_of_infinite

/-!
# Homotopy equivalences induce isomorphisms of homotopy groups

If `e : X ≃ₕ Y` is a homotopy equivalence and `x : X`, then `πₙ(X, x) ≃* πₙ(Y, e x)`.

The proof uses the base point change `Pinch.transport` along the paths traced by the base point
under the homotopies `e.invFun ∘ e.toFun ~ id` and `e.toFun ∘ e.invFun ~ id`
(`Pinch.transport_map`), together with the fact that `Pinch.transport p.symm` is inverse to
`Pinch.transport p` (`Pinch.pinch_symm_pinch`).

For an infinite index type `N` the boundary of the cube is dense and every generalized loop is
homotopic to a constant, so both groups are subsingletons.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap

namespace Work.Stems

open Pinch

/-- The finite index case. -/
theorem mulEquiv_of_homotopyEquiv_finite {N X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [DecidableEq N] [Nonempty N] [Fintype N]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y (e.toFun x)) := by
  obtain ⟨h1⟩ := e.left_inv
  obtain ⟨h2⟩ := e.right_inv
  -- the transport along the reverse of the path traced by `h1` is `map (e.invFun ∘ e.toFun)`
  have hmapg : ∀ a : HomotopyGroup N X x,
      Pinch.transport (N := N) (homotopyPath h1 x).symm a
        = HomotopyGroup.map (N := N) (e.invFun.comp e.toFun) (x := x) a := by
    intro a
    have h := transport_map (N := N) h1.symm x a
    rw [homotopyPath_symm, HomotopyGroup.map_id (N := N)] at h
    exact h
  -- the transport along the reverse of the path traced by `h2` is `map (e.toFun ∘ e.invFun)`
  have hmapf : ∀ b : HomotopyGroup N Y (e.toFun x),
      Pinch.transport (N := N) (homotopyPath h2 (e.toFun x)).symm b
        = HomotopyGroup.map (N := N) (e.toFun.comp e.invFun) (x := e.toFun x) b := by
    intro b
    have h := transport_map (N := N) h2.symm (e.toFun x) b
    rw [homotopyPath_symm, HomotopyGroup.map_id (N := N)] at h
    exact h
  -- hence `map (g ∘ f)` is bijective
  have hgf_surj : Function.Surjective
      (HomotopyGroup.map (N := N) (e.invFun.comp e.toFun) (x := x)) := by
    intro c
    refine ⟨Pinch.transport (N := N) (homotopyPath h1 x) c, ?_⟩
    rw [← hmapg (Pinch.transport (N := N) (homotopyPath h1 x) c)]
    exact transport_symm_apply (N := N) (p := homotopyPath h1 x) c
  have hgf_inj : Function.Injective
      (HomotopyGroup.map (N := N) (e.invFun.comp e.toFun) (x := x)) := by
    intro a a' haa'
    have h := congrArg (Pinch.transport (N := N) (homotopyPath h1 x)) haa'
    rw [← hmapg a, ← hmapg a'] at h
    rw [transport_symm_apply' (N := N) (p := homotopyPath h1 x),
      transport_symm_apply' (N := N) (p := homotopyPath h1 x)] at h
    exact h
  -- and `map (f ∘ g)` is bijective
  have hfg_inj : Function.Injective
      (HomotopyGroup.map (N := N) (e.toFun.comp e.invFun) (x := e.toFun x)) := by
    intro b b' hbb'
    have h := congrArg (Pinch.transport (N := N) (homotopyPath h2 (e.toFun x))) hbb'
    rw [← hmapf b, ← hmapf b'] at h
    rw [transport_symm_apply' (N := N) (p := homotopyPath h2 (e.toFun x)),
      transport_symm_apply' (N := N) (p := homotopyPath h2 (e.toFun x))] at h
    exact h
  have hfg_surj : Function.Surjective
      (HomotopyGroup.map (N := N) (e.toFun.comp e.invFun) (x := e.toFun x)) := by
    intro d
    refine ⟨Pinch.transport (N := N) (homotopyPath h2 (e.toFun x)) d, ?_⟩
    rw [← hmapf (Pinch.transport (N := N) (homotopyPath h2 (e.toFun x)) d)]
    exact transport_symm_apply (N := N) (p := homotopyPath h2 (e.toFun x)) d
  -- `map g` is injective (from `map (f ∘ g)` injective) and surjective (from `map (g ∘ f)`)
  have hg_inj : Function.Injective (HomotopyGroup.map (N := N) e.invFun (x := e.toFun x)) := by
    intro b b' hbb'
    have h := congrArg (HomotopyGroup.map (N := N) e.toFun (x := e.invFun (e.toFun x))) hbb'
    have h2b : HomotopyGroup.map (N := N) e.toFun (x := e.invFun (e.toFun x))
        (HomotopyGroup.map (N := N) e.invFun (x := e.toFun x) b)
        = HomotopyGroup.map (N := N) (e.toFun.comp e.invFun) (x := e.toFun x) b :=
      (HomotopyGroup.map_comp (N := N) (x := e.toFun x) e.invFun e.toFun b).symm
    have h2b' : HomotopyGroup.map (N := N) e.toFun (x := e.invFun (e.toFun x))
        (HomotopyGroup.map (N := N) e.invFun (x := e.toFun x) b')
        = HomotopyGroup.map (N := N) (e.toFun.comp e.invFun) (x := e.toFun x) b' :=
      (HomotopyGroup.map_comp (N := N) (x := e.toFun x) e.invFun e.toFun b').symm
    rw [h2b, h2b'] at h
    exact hfg_inj h
  have hg_surj : Function.Surjective (HomotopyGroup.map (N := N) e.invFun (x := e.toFun x)) := by
    intro c
    have hc : HomotopyGroup.map (N := N) (e.invFun.comp e.toFun) (x := x)
        (Pinch.transport (N := N) (homotopyPath h1 x) c) = c :=
      hmapg (Pinch.transport (N := N) (homotopyPath h1 x) c) ▸
        transport_symm_apply (N := N) (p := homotopyPath h1 x) c
    refine ⟨HomotopyGroup.map (N := N) e.toFun (x := x) (Pinch.transport (N := N) (homotopyPath h1 x) c), ?_⟩
    rw [← HomotopyGroup.map_comp (N := N) (x := x) e.toFun e.invFun, hc]
  have hg_bij : Function.Bijective (HomotopyGroup.map (N := N) e.invFun (x := e.toFun x)) :=
    ⟨hg_inj, hg_surj⟩
  -- finally `map f` is bijective
  refine ⟨MulEquiv.ofBijective (HomotopyGroup.mapHom e.toFun) ⟨?_, ?_⟩⟩
  · intro a a' haa'
    have haa'' : HomotopyGroup.map (N := N) e.toFun (x := x) a
        = HomotopyGroup.map (N := N) e.toFun (x := x) a' := haa'
    have h := congrArg (HomotopyGroup.map (N := N) e.invFun (x := e.toFun x)) haa''
    rw [← HomotopyGroup.map_comp (N := N) (x := x) e.toFun e.invFun,
      ← HomotopyGroup.map_comp (N := N) (x := x) e.toFun e.invFun] at h
    exact hgf_inj h
  · intro b
    obtain ⟨a, ha⟩ := hgf_surj (HomotopyGroup.map (N := N) e.invFun (x := e.toFun x) b)
    refine ⟨a, ?_⟩
    rw [HomotopyGroup.map_comp (N := N) (x := x) e.toFun e.invFun] at ha
    exact hg_inj ha


/-- **A homotopy equivalence induces an isomorphism of homotopy groups.** -/
theorem mulEquiv_of_homotopyEquiv {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DecidableEq N] [Nonempty N] (e : ContinuousMap.HomotopyEquiv X Y) (x : X) :
    Nonempty (HomotopyGroup N X x ≃* HomotopyGroup N Y (e.toFun x)) := by
  by_cases hfin : Finite N
  · haveI : Fintype N := Fintype.ofFinite N
    exact mulEquiv_of_homotopyEquiv_finite e x
  · haveI : Infinite N := not_finite_iff_infinite.mp hfin
    haveI hX : Subsingleton (HomotopyGroup N X x) :=
      subsingleton_of_infinite (N := N) (X := X) x
    haveI hY : Subsingleton (HomotopyGroup N Y (e.toFun x)) :=
      subsingleton_of_infinite (N := N) (X := Y) (e.toFun x)
    exact ⟨{ toFun := fun _ => 1
             invFun := fun _ => 1
             left_inv := fun a => Subsingleton.elim _ _
             right_inv := fun b => Subsingleton.elim _ _
             map_mul' := fun _ _ => (mul_one 1).symm }⟩

end Work.Stems
