import Mathlib
import Submission.Work.Stems.Hurewicz
import Submission.Work.StemsB.PiMap
import Submission.Work.Stems.HurewiczSphere
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMODD

noncomputable section

open scoped Topology Topology.Homotopy unitInterval

/-- The collapse of the cube to the sphere, regarded as a generalized loop based at the image of
the base point of the cube. -/
def sphereCollapseLoop (n : ℕ) (hn : 1 ≤ n) :
    Ω^ (Fin n) (Work.Stems.sphere n) (Work.Stems.collapseMap n hn 0) :=
  ⟨Work.Stems.collapseMap n hn,
    fun q hq => Work.Stems.collapseMap_boundary n hn hq⟩

/-- **Casting a class of a cube across an equality of base points.**  If two cubes have the same
underlying map but different (equal) base points, the transport of the class of one is the class of
the other. -/
theorem sphereHomotopyGroupCast_mk_eq {m : ℕ} {X : Type} [TopologicalSpace X] {x y : X}
    (h : x = y) (γx : Ω^ (Fin (m + 1)) X x) (γy : Ω^ (Fin (m + 1)) X y) (hu : γx.1 = γy.1) :
    Work.StemsB.homotopyGroupCast h m (⟦γx⟧ : HomotopyGroup (Fin (m + 1)) X x) = ⟦γy⟧ := by
  subst h
  rw [Work.StemsB.homotopyGroupCast_rfl]
  show (⟦γx⟧ : HomotopyGroup (Fin (m + 1)) X x) = ⟦γy⟧
  rw [show γx = γy from Subtype.ext hu]

/-- **Realisation of a homotopy class by a sphere map.** For `n ≥ 1`, a non-trivial class `a ∈ π_{n+1}(X,x₀)` is realised by a map `f : S^{n+1} → X` sending a point `s₀` to `x₀` and being non-trivial on `π_{n+1}`. (Route: `Work.Stems.cubeLift (n+1) h (Quotient.out a)` descends the cube representing `a` to the sphere, with `s₀ = Work.Stems.collapseMap (n+1) h 0`; `πmap` of the class of the collapse cube is the class of `Quotient.out a = a ≠ 1`, cf. `Work.Serre.exists_bijective_piMapN` in `Submission/Work/Serre/serreS2OfC0C2oddS1.lean` for the same computation.) -/
theorem sphereClassReal (n : ℕ) (hn : 1 ≤ n) {X : Type} [TopologicalSpace X] {x₀ : X}
    (a : HomotopyGroup (Fin (n + 1)) X x₀) (ha : a ≠ 1) :
    ∃ (f : C(Work.Stems.sphere (n + 1), X)) (s₀ : Work.Stems.sphere (n + 1)),
      f s₀ = x₀ ∧
      ∃ c : HomotopyGroup (Fin (n + 1)) (Work.Stems.sphere (n + 1)) s₀,
        Work.StemsB.πmap f n s₀ c ≠ 1 := by
  have h1 : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
  obtain ⟨γ, hγ⟩ : ∃ γ : Ω^ (Fin (n + 1)) X x₀,
      (⟦γ⟧ : HomotopyGroup (Fin (n + 1)) X x₀) = a :=
    ⟨Quotient.out a, Quotient.out_eq a⟩
  refine ⟨Work.Stems.cubeLift (n + 1) h1 γ,
    Work.Stems.collapseMap (n + 1) h1 0, ?_, ?_⟩
  · -- the map is based: it sends the collapse of `0` to `x₀`
    have hcomp := Work.Stems.cubeLift_comp (n + 1) h1 γ
    have hval : (Work.Stems.cubeLift (n + 1) h1 γ)
        (Work.Stems.collapseMap (n + 1) h1 0) = γ.1 0 := by
      have h := congrFun (congrArg DFunLike.coe hcomp) 0
      simpa [ContinuousMap.comp_apply] using h
    rw [hval, γ.2 0 (Work.Stems.zero_mem_cubeBoundary (n + 1) h1)]
  · -- the collapse class is sent to the class of the cube representing `a`
    set s₀ := Work.Stems.collapseMap (n + 1) h1 0 with hs₀def
    set f := Work.Stems.cubeLift (n + 1) h1 γ with hfdef
    set x := f s₀ with hxdef
    have hs : x = x₀ := by
      have hcomp := Work.Stems.cubeLift_comp (n + 1) h1 γ
      have hval : f s₀ = γ.1 0 := by
        have h := congrFun (congrArg DFunLike.coe hcomp) 0
        simpa [f, s₀, ContinuousMap.comp_apply] using h
      rw [hxdef, hval, γ.2 0 (Work.Stems.zero_mem_cubeBoundary (n + 1) h1)]
    -- the same cube, now regarded as based at `x`
    let γ' : Ω^ (Fin (n + 1)) X x := ⟨γ.1, fun q hq => (γ.2 q hq).trans hs.symm⟩
    let α' : HomotopyGroup (Fin (n + 1)) X x := ⟦γ'⟧
    have hcast : Work.StemsB.homotopyGroupCast hs n α' = a :=
      (sphereHomotopyGroupCast_mk_eq hs γ' γ rfl).trans hγ
    refine ⟨⟦sphereCollapseLoop (n + 1) h1⟧, ?_⟩
    have hFc : Work.StemsB.πmap f n s₀
        (⟦sphereCollapseLoop (n + 1) h1⟧ :
          HomotopyGroup (Fin (n + 1)) (Work.Stems.sphere (n + 1)) s₀) = α' := by
      rw [Work.StemsB.πmap_apply_mk]
      show (⟦Work.StemsB.genLoopMap f (n + 1) (sphereCollapseLoop (n + 1) h1)⟧ :
        HomotopyGroup (Fin (n + 1)) X x) = α'
      have hcomp := Work.Stems.cubeLift_comp (n + 1) h1 γ
      have hgen : Work.StemsB.genLoopMap f (n + 1) (sphereCollapseLoop (n + 1) h1) = γ' := by
        apply Subtype.ext
        apply ContinuousMap.ext
        intro t
        change f ((sphereCollapseLoop (n + 1) h1) t) = γ' t
        change f ((Work.Stems.collapseMap (n + 1) h1) t) = γ.1 t
        simpa [f, ContinuousMap.comp_apply] using congrFun (congrArg DFunLike.coe hcomp) t
      rw [hgen]
    rw [hFc]
    intro h
    exact ha (by rw [← hcast, h, map_one])

end

end Work.Pi6.EMODD
