import Mathlib
import Submission.Work.Serre.CWModel.Defs
import Submission.Work.Serre.CWModel.Descent
import Submission.Work.Serre.CWModel.Gen
import Submission.Work.Serre.CWModel.killSub
import Submission.Work.Serre.CWModel.sphereExtend

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The killing step of the model tower

Attaching, for every element of the kernel of `π_{n+2}(g)`, one `(n+3)`-cell along the sphere map
representing it, and extending `g` over that cell by a null-homotopy of `g` composed with that map
(which exists precisely because the class lies in the kernel), makes `π_{n+2}(g)` injective while
leaving `π_{j+1}(g)` for `j ≤ n` alone.
-/

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

namespace Work.Serre.CWModel

noncomputable section

/-- **The killing step.** -/
def killStep {B : Type} [TopologicalSpace B] {b₀ : B} {n : ℕ} (s : StG B b₀ n) : StA B b₀ (n + 1) := by
  classical
  -- the kernel of `π_{n+2}(g)`, as an index type
  let ι := {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ // piMapN s.g (n + 2) s.y₀ α = 1}
  let sv : ι → HomotopyGroup (Fin (n + 2)) s.Y s.y₀ := fun k => k.1
  let f : ι → C(cellSphere (n + 1), s.Y) := fun k => killFamily (n + 1) s.Y s.y₀ (sv k)
  -- the attaching maps are null-homotopic after composition with `g`
  have hnull : ∀ k : ι, (s.g.comp (f k)).Homotopic
      (ContinuousMap.const (cellSphere (n + 1)) (s.g s.y₀)) := by
    intro k
    have hker : piMapN s.g (n + 2) s.y₀ (sv k) = 1 := k.2
    have hn : 1 ≤ n + 2 := by omega
    have hcube : GenLoop.Homotopic (Work.StemsB.genLoopMap s.g (n + 2) (Quotient.out (sv k)))
        (GenLoop.const (N := Fin (n + 2)) (X := B) (x := s.g s.y₀)) := by
      have h1 : (Quotient.mk _ (Work.StemsB.genLoopMap s.g (n + 2) (Quotient.out (sv k))) :
            HomotopyGroup (Fin (n + 2)) B (s.g s.y₀))
          = Quotient.mk (GenLoop.Homotopic.setoid (Fin (n + 2)) (s.g s.y₀))
              (GenLoop.const (N := Fin (n + 2)) (X := B) (x := s.g s.y₀)) := by
        rw [← piMapN_apply_mk, Quotient.out_eq (sv k), hker]
        exact HomotopyGroup.one_def (N := Fin (n + 2)) (X := B) (x := s.g s.y₀)
      exact Quotient.exact h1
    have h2 := cubeLift_homotopic hn hcube
    rw [Work.Serre.cubeLift_genLoopMap, cubeLift_const] at h2
    exact h2
  -- the extensions over the cells
  let G : ι → C(cellDisk (n + 1), B) := fun k =>
    Classical.choose (sphereExtend (s.g.comp (f k)) (hnull k).some.toContinuousMap (s.g s.y₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
  have hG : ∀ (k : ι) (z : cellSphere (n + 1)),
      G k (cellSphereToDisk (n + 1) z) = s.g (f k z) := by
    intro k z
    have hspec := Classical.choose_spec (sphereExtend (s.g.comp (f k)) (hnull k).some.toContinuousMap
      (s.g s.y₀) (hnull k).some.map_zero_left (hnull k).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  let g' : C(attachCells (n + 1) s.Y ι f, B) := attachG (n + 1) s.Y ι f s.g G hG
  have hgl : ∀ y, g' (attachIncl (n + 1) s.Y ι f y) = s.g y := fun y => attachG_incl _ _ _ _ _ _ _ y
  haveI hconn : PathConnectedSpace s.Y := s.conn
  refine { Y := attachCells (n + 1) s.Y ι f
           inst := inferInstance
           y₀ := attachIncl (n + 1) s.Y ι f s.y₀
           g := g'
           gbase := (hgl s.y₀).trans s.gbase
           conn := pathConnectedSpace_attachCells (n + 1) s.Y ι f
           bij := ?_ }
  -- the homotopy groups
  have hcomp : ∀ a, piMapN s.g (n + 2) s.y₀ a
      = piMapN g' (n + 2) (attachIncl (n + 1) s.Y ι f s.y₀)
          (piMapN (attachIncl (n + 1) s.Y ι f) (n + 2) s.y₀ a) := by
    intro a
    exact piMapN_comp (attachIncl (n + 1) s.Y ι f) g' (n + 2) s.y₀ a
  -- everything in the kernel dies
  have hkill : ∀ α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀, piMapN s.g (n + 2) s.y₀ α = 1 →
      piMapN (attachIncl (n + 1) s.Y ι f) (n + 2) s.y₀ α = 1 := by
    intro α hα
    exact killSub s.Y s.y₀ ι sv ⟨α, hα⟩
  have hmul : ∀ {Z : Type} [TopologicalSpace Z] (q : C(s.Y, Z))
      (a b : HomotopyGroup (Fin (n + 2)) s.Y s.y₀),
      piMapN q (n + 2) s.y₀ (a * b) = piMapN q (n + 2) s.y₀ a * piMapN q (n + 2) s.y₀ b :=
    fun q a b => map_mul (Work.StemsB.πmap q (n + 1) s.y₀) a b
  have hinv : ∀ {Z : Type} [TopologicalSpace Z] (q : C(s.Y, Z))
      (a : HomotopyGroup (Fin (n + 2)) s.Y s.y₀),
      piMapN q (n + 2) s.y₀ a⁻¹ = (piMapN q (n + 2) s.y₀ a)⁻¹ :=
    fun q a => map_inv (Work.StemsB.πmap q (n + 1) s.y₀) a
  intro j hj
  by_cases hjn : j + 1 ≤ n + 1
  · -- degrees below the top: the inclusion is an isomorphism
    have hbij : Function.Bijective (piMapN s.g (j + 1) s.y₀) := s.bij j (by omega)
    have hkey : piMapN s.g (j + 1) s.y₀ = fun a =>
        piMapN g' (j + 1) (attachIncl (n + 1) s.Y ι f s.y₀)
          (piMapN (attachIncl (n + 1) s.Y ι f) (j + 1) s.y₀ a) := by
      funext a
      exact piMapN_comp (attachIncl (n + 1) s.Y ι f) g' (j + 1) s.y₀ a
    have hbij' : Function.Bijective (fun a =>
        piMapN g' (j + 1) (attachIncl (n + 1) s.Y ι f s.y₀)
          (piMapN (attachIncl (n + 1) s.Y ι f) (j + 1) s.y₀ a)) := hkey ▸ hbij
    have hsurj : Function.Surjective (piMapN (attachIncl (n + 1) s.Y ι f) (j + 1) s.y₀) :=
      (attachIncl_piMap_bijective_of_compress (n + 1) s.Y ι f s.y₀ (j + 1) (by omega) hjn).2
    exact bijective_of_comp_of_surjective hbij' hsurj
  · -- the top degree: `π_{n+2}(g')`
    have hje : j = n + 1 := by omega
    rw [hje]
    have hsf : Function.Surjective (piMapN (attachIncl (n + 1) s.Y ι f) (n + 2) s.y₀) :=
      surjective_πmap_attachIncl (n + 1) s.Y ι f s.y₀
    have hcomp' : ∀ a, piMapN s.g (n + 2) s.y₀ a
        = piMapN g' (n + 2) (attachIncl (n + 1) s.Y ι f s.y₀)
            (piMapN (attachIncl (n + 1) s.Y ι f) (n + 2) s.y₀ a) := hcomp
    refine ⟨?_, ?_⟩
    · -- injectivity: everything in the kernel of `π_{n+2}(g)` dies
      intro a b hab
      obtain ⟨α, rfl⟩ := hsf a
      obtain ⟨β, rfl⟩ := hsf b
      have hαβ : piMapN s.g (n + 2) s.y₀ α = piMapN s.g (n + 2) s.y₀ β := by
        rw [hcomp' α, hcomp' β]
        exact hab
      have hker : piMapN s.g (n + 2) s.y₀ (α * β⁻¹) = 1 := by
        rw [hmul s.g α β⁻¹, hinv s.g β, hαβ, mul_inv_cancel]
      have hkill1 := hkill (α * β⁻¹) hker
      have : piMapN (attachIncl (n + 1) s.Y ι f) (n + 2) s.y₀ α
          = piMapN (attachIncl (n + 1) s.Y ι f) (n + 2) s.y₀ β := by
        refine mul_inv_eq_one.mp ?_
        rw [← hinv (attachIncl (n + 1) s.Y ι f) β, ← hmul (attachIncl (n + 1) s.Y ι f) α β⁻¹]
        exact hkill1
      rw [this]
    · -- surjectivity: `s.surj` combined with the surjectivity of the inclusion
      intro y
      obtain ⟨α, hα⟩ := s.surj y
      exact ⟨piMapN (attachIncl (n + 1) s.Y ι f) (n + 2) s.y₀ α, by
        rw [← hcomp' α]
        exact hα⟩

end

end Work.Serre.CWModel
