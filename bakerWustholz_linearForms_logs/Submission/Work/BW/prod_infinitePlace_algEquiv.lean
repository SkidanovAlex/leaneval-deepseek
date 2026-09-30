import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField in
/-- The archimedean part `∏_v (supᵢ v(p_i)) ^ (mult v)` of the place-weighted (unnormalized)
height of a tuple over a number field is invariant under `ℚ`-algebra isomorphisms of number
fields. -/
theorem prod_infinitePlace_algEquiv {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    (e : K ≃ₐ[ℚ] K') {ι : Type*} [Fintype ι] (p : ι → K) :
    (∏ v : InfinitePlace K', (⨆ i, v (e (p i))) ^ v.mult) =
      ∏ v : InfinitePlace K, (⨆ i, v (p i)) ^ v.mult := by
  classical
  -- Precomposition with the ring equivalence `e` gives a bijection between the infinite places of
  -- `K'` and those of `K`, namely `w ↦ w.comap e`.
  let E : InfinitePlace K' ≃ InfinitePlace K :=
    { toFun := fun w => w.comap (e : K →+* K')
      invFun := fun v => v.comap (e.symm : K' →+* K)
      left_inv := by
        intro w
        show (w.comap (e : K →+* K')).comap (e.symm : K' →+* K) = w
        rw [← InfinitePlace.comap_comp,
          show (e : K →+* K').comp (e.symm : K' →+* K) = RingHom.id K' from by ext x; simp,
          InfinitePlace.comap_id]
      right_inv := by
        intro v
        show (v.comap (e.symm : K' →+* K)).comap (e : K →+* K') = v
        rw [← InfinitePlace.comap_comp,
          show (e.symm : K' →+* K).comp (e : K →+* K') = RingHom.id K from by ext x; simp,
          InfinitePlace.comap_id] }
  rw [← Equiv.prod_comp E (fun v : InfinitePlace K => (⨆ i, v (p i)) ^ v.mult)]
  apply Finset.prod_congr rfl
  intro w _
  -- `comap` preserves the multiplicity and evaluates as `(w.comap e) x = w (e x)`.
  have hm : (E w).mult = w.mult := by
    show (w.comap (e : K →+* K')).mult = w.mult
    unfold InfinitePlace.mult
    congr 1
    exact propext (InfinitePlace.isReal_comap_iff e.toRingEquiv)
  have hv : ∀ i, (E w) (p i) = w (e (p i)) := by
    intro i
    show (w.comap (e : K →+* K')) (p i) = w (e (p i))
    rw [InfinitePlace.comap_apply]
    rfl
  simp only [hv, hm]

end Work.BW
