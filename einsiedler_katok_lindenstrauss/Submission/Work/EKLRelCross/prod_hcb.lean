import Mathlib
import Submission.Work.EKLContract.All

/-!
# `U_(ab) = U_cb · ⟨U_ab, U_ac⟩` (EKL Lemma 4.4, the factorisation)

EKL's horospherical subgroup for the ordered triple `(a, c, b)` is
`U_(ab) = ⟨U_ab, U_ac, U_cb⟩` (`Work.EKLContract.Upar`).  This file proves that it is the
*set product* of its `U_cb`-factor with the two-dimensional group `⟨U_ab, U_ac⟩`:

  every `h ∈ U_(ab)` can be written `h = g * u` with `g ∈ U_cb` and `u ∈ ⟨U_ab, U_ac⟩`.

Equivalently the subgroup `U_cb` *normalises* `⟨U_ab, U_ac⟩`, so that the product is a subgroup;
the concrete content is the single matrix identity (`uij_ac_mul_uij_cb`)

  `u_ac(t) · u_cb(s) = u_cb(s) · u_ab(s t) · u_ac(t)`.

Indeed `U_cb` centralises the transvection `u_ab` (`[E_cb, E_ab] = 0`) and acts on `u_ac` by
adding a multiple of `E_ab` (`[E_cb, E_ac] = -E_ab`), so the commutator of the two factors stays
inside `⟨U_ab, U_ac⟩`.  Concretely, in the parametrisation
`uparShape p q r = u_ac(q) * u_cb(r) * u_ab(p)` of `U_(ab)` (`isHoro_Upar.lean`),

  `uparShape p q r = u_cb(r) · (u_ab(r q) * u_ac(q) * u_ab(p))`,

and the second factor lies in `⟨U_ab, U_ac⟩`.
-/

open Work.EKLContract Work.EKLContract.Lemmas

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLRelCross

/-- **The commutation identity**: the transvection `u_cb(s)` moves across `u_ac(t)` at the price
of the correction term `u_ab(s t)`

  `u_ac(t) · u_cb(s) = u_cb(s) · u_ab(s t) · u_ac(t)`.

Because `[E_cb, E_ac] = E_ab` and `[E_cb, E_ab] = 0` (with `a`, `b`, `c` pairwise distinct),
the commutator `u_cb(s) u_ac(t) u_cb(s)⁻¹ u_ac(t)⁻¹ = u_ab(s t)` lands back in `⟨U_ab, U_ac⟩`. -/
theorem uij_ac_mul_uij_cb {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (s t : ℝ) :
    uij hac t * uij hcb s = uij hcb s * uij hab (s * t) * uij hac t := by
  have hPQ : Matrix.single a c t * Matrix.single c b s = Matrix.single a b (t * s) :=
    Matrix.single_mul_single_same t a c b s
  have hQR : Matrix.single c b s * Matrix.single a b (s * t) = 0 :=
    Matrix.single_mul_single_of_ne s c b a hab.symm (s * t)
  have hQP : Matrix.single c b s * Matrix.single a c t = 0 :=
    Matrix.single_mul_single_of_ne s c b a hab.symm t
  have hRP : Matrix.single a b (s * t) * Matrix.single a c t = 0 :=
    Matrix.single_mul_single_of_ne (s * t) a b a hab.symm t
  apply Work.EKLContract.ext_toMat
  simp only [Work.EKLContract.toMat_mul, horoUij_toMat]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hPQ, hQR, hQP, hRP,
    add_zero]
  rw [mul_comm t s]
  abel

/-- **Factorisation of a general element of `U_(ab)`**: writing
`uparShape p q r = u_ac(q) u_cb(r) u_ab(p)`, we have

  `uparShape p q r = u_cb(r) · (u_ab(r q) · u_ac(q) · u_ab(p))`.

The `U_cb`-factor has been pulled to the left, and the remainder is a product of transvections
`u_ab`, `u_ac`, hence lies in `⟨U_ab, U_ac⟩`. -/
theorem uparShape_eq_hcb_mul {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (p q r : ℝ) :
    uparShape hab hac hcb p q r =
      uij hcb r * (uij hab (r * q) * uij hac q * uij hab p) := by
  unfold uparShape
  rw [uij_ac_mul_uij_cb hab hac hcb r q]
  group

/-- **`Work.EKLRelCross.prod_hcb`** — EKL's `U_(ab) = U_cb · ⟨U_ab, U_ac⟩`: every element of
`U_(ab) = ⟨U_ab, U_ac, U_cb⟩` is a product `g * u` of an element `g` of the root group `U_cb`
with an element `u` of the two-dimensional group `⟨U_ab, U_ac⟩`. -/
theorem prod_hcb (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (h : Work.EKLContract.SL3) (hh : h ∈ Work.EKLContract.Upar hab hac hcb) :
    ∃ g ∈ Work.EKLContract.Uij hcb,
      ∃ u ∈ (Work.EKLContract.Uij hab ⊔ Work.EKLContract.Uij hac : Subgroup Work.EKLContract.SL3),
        h = g * u := by
  rw [Upar_eq_uparShapeSub, mem_uparShapeSub] at hh
  obtain ⟨p, q, r, rfl⟩ := hh
  refine ⟨uij hcb r, Subgroup.subset_closure ⟨r, rfl⟩,
          uij hab (r * q) * uij hac q * uij hab p, ?_, ?_⟩
  · exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨r * q, rfl⟩))
                           (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨q, rfl⟩)))
                  (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨p, rfl⟩))
  · exact uparShape_eq_hcb_mul hab hac hcb p q r

end Work.EKLRelCross
