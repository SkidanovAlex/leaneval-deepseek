import Mathlib
import Submission.Work.ORTorsion.Defs
import Submission.Work.ORTorsion.Descent.DiagAct
import Submission.Work.ORTorsion.Descent.diagAct_eq_instDiagD
import Submission.Work.ORTorsion.Descent.diagAct_eq_instDiagTop

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.ORTorsion.Descent

-- Proof sketch that works: `↥(D H)` is semisimple (`TorsionData.semisimple`), so every
-- module over it is projective; in particular `↥(D ⊤)` is projective over `↥(D H)`, giving
-- via `Module.projective_of_isSemisimpleRing` a linear `s : ↥(D ⊤) →ₗ[↥(D H)] (↥(D ⊤) →₀ ↥(D H))`
-- with a left inverse `r`.  For `m : V ⊗[K] ↥(D ⊤)` with `z := (id ⊗ s) m`, one has
-- `(id ⊗ r) z = m`; expanding `z` in the coordinates `(id ⊗ (Finsupp.lapply b)) z` and using
-- that the diagonal action commutes with `id ⊗ f` for `↥(D H)`-linear `f`, injectivity on
-- `V ⊗[K] ↥(D H)` transfers (take a finite representation of `m` as a sum of pure tensors).
open scoped TensorProduct
open Work.ORTorsion

theorem injective_of_injective_DH {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*}
    [Ring U] [Algebra K U] (L : TorsionData K G U) {V : Type*} [AddCommGroup V]
    [Module K V] [Module (MonoidAlgebra K G) V] [IsScalarTower K (MonoidAlgebra K G) V]
    (H : Subgroup G) (x : MonoidAlgebra K H)
    (hx : Function.Injective (fun m : V ⊗[K] ↥(L.D H) => x • m)) :
    Function.Injective (fun m : V ⊗[K] ↥(L.D ⊤) => mapToG H x • m) := by
  classical
  haveI hss : IsSemisimpleRing ↥(L.D H) := L.semisimple H
  -- `↥(L.D ⊤)` is projective over `↥(L.D H)`: extract a splitting `s` of the
  -- evaluation map `r = Finsupp.linearCombination ↥(L.D H) id`.
  obtain ⟨s, hs⟩ := Module.projective_def.mp
    (Module.projective_of_isSemisimpleRing ↥(L.D H) ↥(L.D ⊤))
  -- The hypothesis, recast for the `K[H]`-action `diagAct`.
  have hxd : Function.Injective (fun m : V ⊗[K] ↥(L.D H) => diagAct L H ↥(L.D H) x m) := by
    have hfun : (fun m : V ⊗[K] ↥(L.D H) => diagAct L H ↥(L.D H) x m)
        = (fun m : V ⊗[K] ↥(L.D H) => x • m) := by
      funext m; exact diagAct_eq_instDiagD L H x m
    rw [hfun]; exact hx
  suffices hm : ∀ m : V ⊗[K] ↥(L.D ⊤), diagAct L H ↥(L.D ⊤) x m = 0 → m = 0 by
    intro m n hmn
    have hmn' : diagAct L H ↥(L.D ⊤) x m = diagAct L H ↥(L.D ⊤) x n := by
      rw [diagAct_eq_instDiagTop L H x m, diagAct_eq_instDiagTop L H x n]; exact hmn
    have h : diagAct L H ↥(L.D ⊤) x (m - n) = 0 := by
      rw [map_sub, hmn', sub_self]
    exact sub_eq_zero.mp (hm (m - n) h)
  intro m hm
  let sK : ↥(L.D ⊤) →ₗ[K] (↥(L.D ⊤) →₀ ↥(L.D H)) := s.restrictScalars K
  let rK : (↥(L.D ⊤) →₀ ↥(L.D H)) →ₗ[K] ↥(L.D ⊤) :=
    (Finsupp.linearCombination ↥(L.D H) id).restrictScalars K
  let z : V ⊗[K] (↥(L.D ⊤) →₀ ↥(L.D H)) := TensorProduct.map (LinearMap.id : V →ₗ[K] V) sK m
  -- `z` is killed by the diagonal action of `x` on `V ⊗[K] (↥(L.D ⊤) →₀ ↥(L.D H))`
  have hz : diagAct L H (↥(L.D ⊤) →₀ ↥(L.D H)) x z = 0 := by
    have h1 := diagAct_map (V := V) L H (M := ↥(L.D ⊤))
      (N := (↥(L.D ⊤) →₀ ↥(L.D H))) s x m
    rw [hm, map_zero] at h1
    exact h1.symm
  -- each coordinate `(id ⊗ (Finsupp.lapply b)) z` is killed by `x` on `V ⊗[K] ↥(L.D H)`
  have hcoord : ∀ b : ↥(L.D ⊤),
      diagAct L H ↥(L.D H) x
        (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
          ((Finsupp.lapply b : (↥(L.D ⊤) →₀ ↥(L.D H)) →ₗ[↥(L.D H)] ↥(L.D H)).restrictScalars K) z)
      = 0 := by
    intro b
    have h1 := diagAct_map (V := V) L H (M := (↥(L.D ⊤) →₀ ↥(L.D H)))
      (N := ↥(L.D H)) (Finsupp.lapply b) x z
    rw [hz, map_zero] at h1
    exact h1.symm
  have hcoord0 : ∀ b : ↥(L.D ⊤),
      TensorProduct.map (LinearMap.id : V →ₗ[K] V)
        ((Finsupp.lapply b : (↥(L.D ⊤) →₀ ↥(L.D H)) →ₗ[↥(L.D H)] ↥(L.D H)).restrictScalars K) z
      = 0 := by
    intro b
    refine hxd ?_
    change (diagAct L H ↥(L.D H) x) (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
        ((Finsupp.lapply b : (↥(L.D ⊤) →₀ ↥(L.D H)) →ₗ[↥(L.D H)] ↥(L.D H)).restrictScalars K) z)
      = (diagAct L H ↥(L.D H) x) 0
    rw [map_zero]
    exact hcoord b
  -- hence `z = 0`, using `V ⊗[K] (ι →₀ M) ≅ ι →₀ V ⊗[K] M`
  have hz0 : z = 0 := by
    have hw : TensorProduct.finsuppRight K K V ↥(L.D H) ↥(L.D ⊤) z = 0 := by
      ext b
      rw [TensorProduct.finsuppRight_apply]
      exact hcoord0 b
    exact (TensorProduct.finsuppRight K K V ↥(L.D H) ↥(L.D ⊤)).injective (by rw [hw, map_zero])
  have hrs : rK.comp sK = (LinearMap.id : ↥(L.D ⊤) →ₗ[K] ↥(L.D ⊤)) := by
    apply LinearMap.ext
    intro b
    exact hs b
  -- `m = (id ⊗ r) z = 0`
  have hmz : m = TensorProduct.map (LinearMap.id : V →ₗ[K] V) rK z := by
    have key : TensorProduct.map (LinearMap.id : V →ₗ[K] V) rK z = m := by
      show (TensorProduct.map (LinearMap.id : V →ₗ[K] V) rK)
        (TensorProduct.map (LinearMap.id : V →ₗ[K] V) sK m) = m
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, hrs,
        TensorProduct.map_id, LinearMap.id_apply]
    exact key.symm
  rw [hmz, hz0, map_zero]

end Work.ORTorsion.Descent
