import Mathlib
import Submission.Work.RatHurewicz.excisionTransfer
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.StemsB.PiMap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre.RangeOne

open scoped Topology

/-- **The compression property of the range implies bijectivity on `π_{≤ M-2}`.**

Let `f : X → Y` be a topological embedding and suppose that the pair `(Y, range f)` has the
compression property (tom Dieck 6.7.5(1), `Work.RatHurewicz.CompressRel`) in all dimensions
`d ≤ M`.  Then `f` induces a bijection `π_j(X,x) → π_j(Y,f x)` for every `j` with `j + 2 ≤ M`.

The proof factors `f` as the homeomorphism `hf.toHomeomorph : X ≃ₜ range f` followed by the
inclusion `range f ↪ Y`: `Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel` gives the
bijectivity of the second map in the stated range, and the first is a homeomorphism, hence
bijective on all homotopy groups (`Work.Serre.bijective_πmap_of_comp_eq_id_gen`).  No hypothesis
on the connectivity of `X` or on `π₀` is needed. -/
theorem piMap_bijective_of_compress {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (hf : Topology.IsEmbedding (f : X → Y)) (M : ℕ)
    (hcomp : ∀ d, d ≤ M → Work.RatHurewicz.CompressRel Y (Set.range (f : X → Y)) d) :
    ∀ j : ℕ, j + 2 ≤ M → ∀ x : X, Function.Bijective (Work.StemsB.πmap f j x) := by
  intro j hj x
  let A : Set Y := Set.range (f : X → Y)
  let e : C(X, A) := ⟨hf.toHomeomorph, hf.toHomeomorph.continuous⟩
  let eInv : C(A, X) := ⟨hf.toHomeomorph.symm, hf.toHomeomorph.symm.continuous⟩
  have h1 : eInv.comp e = ContinuousMap.id X := by
    refine ContinuousMap.ext fun y => ?_
    exact hf.toHomeomorph.symm_apply_apply y
  have h2 : e.comp eInv = ContinuousMap.id A := by
    refine ContinuousMap.ext fun y => ?_
    exact hf.toHomeomorph.apply_symm_apply y
  have hAbij : Function.Bijective (Work.StemsB.πmap e j x) :=
    Work.Serre.bijective_πmap_of_comp_eq_id_gen e eInv h1 h2 j x
  have hBbij : Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.setIncl A) j (e x)) :=
    Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel (A := A) (e x) M hcomp j hj
  have hcompmap : (Work.RatHurewicz.setIncl A).comp e = f := rfl
  have hbijComp : Function.Bijective
      (Work.StemsB.πmap ((Work.RatHurewicz.setIncl A).comp e) j x) := by
    rw [show ⇑(Work.StemsB.πmap ((Work.RatHurewicz.setIncl A).comp e) j x)
        = fun a => Work.StemsB.πmap (Work.RatHurewicz.setIncl A) j (e x)
            (Work.StemsB.πmap e j x a) from
      funext fun a => Work.StemsB.πmap_comp_apply e (Work.RatHurewicz.setIncl A) j x a]
    exact hBbij.comp hAbij
  have hfun : ⇑(Work.StemsB.πmap f j x)
      = fun a => Work.StemsB.homotopyGroupCast
          (congrArg (fun k : C(X, Y) => k x) hcompmap) j
          (Work.StemsB.πmap ((Work.RatHurewicz.setIncl A).comp e) j x a) :=
    funext fun a => (Work.StemsB.πmap_congr hcompmap j x a).symm
  rw [hfun]
  exact (Work.StemsB.homotopyGroupCast _ j).bijective.comp hbijComp

end Work.Serre.RangeOne
