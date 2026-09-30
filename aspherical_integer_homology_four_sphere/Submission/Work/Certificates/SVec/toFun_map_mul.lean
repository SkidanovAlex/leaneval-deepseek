import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SVec

theorem toFun_map_mul {n : ℕ} (v : List (Fin n × ℤ)) (c : ℤ) :
    toFun (v.map (fun p => (p.1, p.2 * c))) = c • toFun v := by
  funext i
  simp only [toFun, List.map_map, Pi.smul_apply, smul_eq_mul]
  rw [List.map_congr_left (l := v)
      (f := (fun p => if p.1 = i then p.2 else 0) ∘ (fun p => (p.1, p.2 * c)))
      (g := fun p => (if p.1 = i then p.2 else 0) * c)
      (fun a _ => by by_cases h : a.1 = i <;> simp [h])]
  rw [List.sum_map_mul_right, mul_comm]

end Work.Certificates.SVec
