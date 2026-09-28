import Mathlib
import Submission.Work.HP.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HP.NA

/-- Given `u v : ι → ℤ`, a coordinate `i0` at which `u i0` is a unit of `ZMod (p^r)`, and
`c` satisfying `c * u i0 = v i0`, any `t` in the range of the coefficient functional
`w i = v i - c * u i` can be written as `∑ a i * v i` for some `a` with `∑ a i * u i = 0`.
The witness is obtained from a preimage `b` of `t` under `w` by shifting the `i0`-coordinate. -/
theorem exists_witness_of_mem_range {ι : Type*} [Fintype ι] {p r : ℕ}
    (u v : ι → ℤ) (i0 : ι) (hu0 : IsUnit ((u i0 : ZMod (p ^ r)))) {c t : ZMod (p ^ r)}
    (hc : c * ((u i0 : ℤ) : ZMod (p ^ r)) = ((v i0 : ℤ) : ZMod (p ^ r)))
    (ht : t ∈ LinearMap.range (Fintype.linearCombination (ZMod (p ^ r))
        (fun i => ((v i : ℤ) : ZMod (p ^ r)) - c * ((u i : ℤ) : ZMod (p ^ r))))) :
    ∃ a : ι → ZMod (p ^ r),
      (∑ i, a i * ((u i : ℤ) : ZMod (p ^ r)) = 0) ∧
      (∑ i, a i * ((v i : ℤ) : ZMod (p ^ r))) = t := by
  classical
  obtain ⟨b, hb⟩ := ht
  obtain ⟨e, he⟩ := hu0.exists_right_inv
  have he' : e * ((u i0 : ℤ) : ZMod (p ^ r)) = 1 := by rw [mul_comm]; exact he
  set U : ZMod (p ^ r) := ∑ i, b i * ((u i : ℤ) : ZMod (p ^ r)) with hU
  refine ⟨fun i => b i + (if i = i0 then (-U) * e else 0), ?_, ?_⟩
  · have hsingle : ∑ i, (if i = i0 then (-U) * e else 0) * ((u i : ℤ) : ZMod (p ^ r))
        = ((-U) * e) * ((u i0 : ℤ) : ZMod (p ^ r)) := by
      rw [show (∑ i, (if i = i0 then (-U) * e else 0) * ((u i : ℤ) : ZMod (p ^ r)))
            = ∑ i, (if i = i0 then ((-U) * e) * ((u i : ℤ) : ZMod (p ^ r)) else 0) from
          Finset.sum_congr rfl (fun i _ => by split <;> simp)]
      rw [Finset.sum_ite_eq']
      simp
    simp only [add_mul, Finset.sum_add_distrib]
    rw [← hU, hsingle]
    rw [show ((-U) * e) * ((u i0 : ℤ) : ZMod (p ^ r)) = -U by
      rw [mul_assoc, he', mul_one]]
    abel
  · have hsingle2 : ∑ i, (if i = i0 then (-U) * e else 0) * ((v i : ℤ) : ZMod (p ^ r))
        = ((-U) * e) * ((v i0 : ℤ) : ZMod (p ^ r)) := by
      rw [show (∑ i, (if i = i0 then (-U) * e else 0) * ((v i : ℤ) : ZMod (p ^ r)))
            = ∑ i, (if i = i0 then ((-U) * e) * ((v i : ℤ) : ZMod (p ^ r)) else 0) from
          Finset.sum_congr rfl (fun i _ => by split <;> simp)]
      rw [Finset.sum_ite_eq']
      simp
    have hb'' : ∑ i, b i * (((v i : ℤ) : ZMod (p ^ r)) - c * ((u i : ℤ) : ZMod (p ^ r))) = t := by
      rw [← hb, Fintype.linearCombination_apply]
      simp [smul_eq_mul]
    have hsplit : ∑ i, b i * (((v i : ℤ) : ZMod (p ^ r)) - c * ((u i : ℤ) : ZMod (p ^ r)))
        = (∑ i, b i * ((v i : ℤ) : ZMod (p ^ r))) - c * U := by
      rw [show (∑ i, b i * (((v i : ℤ) : ZMod (p ^ r)) - c * ((u i : ℤ) : ZMod (p ^ r))))
            = ∑ i, (b i * ((v i : ℤ) : ZMod (p ^ r)) - b i * (c * ((u i : ℤ) : ZMod (p ^ r)))) from
          Finset.sum_congr rfl (fun i _ => by rw [mul_sub])]
      rw [Finset.sum_sub_distrib]
      rw [show (∑ i, b i * (c * ((u i : ℤ) : ZMod (p ^ r))))
            = c * (∑ i, b i * ((u i : ℤ) : ZMod (p ^ r))) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring]
    have hv : ((-U) * e) * ((v i0 : ℤ) : ZMod (p ^ r)) = -(c * U) := by
      have hc' : ((v i0 : ℤ) : ZMod (p ^ r)) = c * ((u i0 : ℤ) : ZMod (p ^ r)) := by rw [← hc]
      rw [hc']
      calc ((-U) * e) * (c * ((u i0 : ℤ) : ZMod (p ^ r)))
          = ((-U) * (e * ((u i0 : ℤ) : ZMod (p ^ r)))) * c := by ring
        _ = ((-U) * 1) * c := by rw [he']
        _ = -(c * U) := by ring
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hsingle2, hv, ← hb'', hsplit, sub_eq_add_neg]

end Work.HP.NA
