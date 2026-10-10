import Mathlib
import Submission.Work.MotAS.azThetaDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS.Az

/-- Naturality of the AS invariant quadric: `kleinQAS` is a polynomial expression with integer
coefficients in `a`, `b` and the coordinates, hence commutes with every ring homomorphism. -/
private theorem map_kleinQAS_local {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b : R) (u : Fin 5 → R) :
    φ (Work.MotAS.kleinQAS a b u)
      = Work.MotAS.kleinQAS (φ a) (φ b) (fun i => φ (u i)) := by
  simp only [Work.MotAS.kleinQAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
    map_one, map_zero, map_neg] <;> ring

/-- Naturality of the polar form `kleinBilinAS` of the AS quadric. -/
private theorem map_kleinBilinAS_local {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b : R) (u v : Fin 5 → R) :
    φ (Work.MotAS.kleinBilinAS a b u v)
      = Work.MotAS.kleinBilinAS (φ a) (φ b) (fun i => φ (u i)) (fun i => φ (v i)) := by
  have h : (fun i => φ ((u + v) i)) = (fun i => φ (u i)) + (fun i => φ (v i)) := by
    funext i
    simp only [Pi.add_apply, map_add]
  simp only [Work.MotAS.kleinBilinAS, map_sub]
  rw [map_kleinQAS_local φ a b (u + v), h, map_kleinQAS_local φ a b u,
    map_kleinQAS_local φ a b v]

/-- Transport of the AS stereographic map along an arbitrary ring homomorphism.
Route: `fin_cases i`, unfold `kleinStereoAS`, `kleinQAS`, `kleinBilinAS`, then
`simp only [..., Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Pi.add_apply,
Pi.sub_apply, Pi.mul_apply, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat] <;> ring`.
(If `map_kleinQAS`/`map_kleinBilinAS` are available in the import closure, the proof is a two-line
`funext` + rewrite; do not add dependencies beyond the ones given.) -/
theorem map_kleinStereoAS {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (P V : Fin 5 → R) (i : Fin 5) :
    φ (Work.MotAS.kleinStereoAS a b P V i)
      = Work.MotAS.kleinStereoAS (φ a) (φ b) (fun j => φ (P j)) (fun j => φ (V j)) i := by
  simp only [Work.MotAS.kleinStereoAS, Pi.sub_apply, Pi.mul_apply, map_sub, map_mul]
  rw [map_kleinQAS_local φ a b V, map_kleinBilinAS_local φ a b P V]

end Work.MotAS.Az
