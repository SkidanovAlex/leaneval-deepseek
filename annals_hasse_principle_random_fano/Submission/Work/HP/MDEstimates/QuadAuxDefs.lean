import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.Q44Geom.Setup

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial

namespace Work.HP.MDEstimates

/-!
# Auxiliary objects for the quadric lattice count (`quadLatCount`)

`Q : MvPolynomial (Fin 5) ℚ` is a homogeneous quadratic form.  We use

* `polQ Q x y = (Q(x+y) - Q(x) - Q(y))/2`, the polar bilinear form;
* `polarLM Q`, the coefficient matrix of the polar form, acting on `ℚ^5`;
* `radSub Q = ker (polarLM Q)`, the radical, and `radLatSub Q`, its integer points;
* `coneQ Q = {v | Q(v) = 0}` (the cone) and `coneZ Q` its integer points;
* `Qset Q s`, the set counted by `quadLatCount`.
-/

/-- The polar form of `Q`, defined by polarisation: `Q(x+y) = Q(x) + Q(y) + 2 polQ Q x y`. -/
def polQ (Q : MvPolynomial (Fin 5) ℚ) (x y : Fin 5 → ℚ) : ℚ :=
  (MvPolynomial.eval (x + y) Q - MvPolynomial.eval x Q - MvPolynomial.eval y Q) / 2

/-- The radical of the polar form: the vectors `v` with `polQ Q v · = 0`. -/
def radQ (Q : MvPolynomial (Fin 5) ℚ) : Set (Fin 5 → ℚ) :=
  {v | ∀ w : Fin 5 → ℚ, polQ Q v w = 0}

/-- The matrix of the polar form of `Q`: the coefficient of `w_i` in `polQ Q v w`, namely
`(Σ_j c_{ij} v_j + c_{ii} v_i)/2`, where `c_{ij}` is the coefficient of `X_i X_j` in `Q`.
(Across the diagonal this is `c_{ij}/2`; on the diagonal it is `c_{ii}`.) -/
def polarLM (Q : MvPolynomial (Fin 5) ℚ) : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun v := fun i =>
    ((∑ j : Fin 5, (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) * v j)
      + (Q.coeff (Finsupp.single i 1 + Finsupp.single i 1)) * v i) / 2
  map_add' v w := by
    funext i
    have h1 : (∑ j : Fin 5, (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) * (v j + w j))
        = (∑ j : Fin 5, (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) * v j)
          + ∑ j : Fin 5, (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) * w j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Pi.add_apply, h1]
    ring
  map_smul' c v := by
    funext i
    have h1 : (∑ j : Fin 5, (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) * (c * v j))
        = c * ∑ j : Fin 5, (Q.coeff (Finsupp.single i 1 + Finsupp.single j 1)) * v j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h1]
    ring

/-- The radical, as a `ℚ`-submodule. -/
def radSub (Q : MvPolynomial (Fin 5) ℚ) : Submodule ℚ (Fin 5 → ℚ) := LinearMap.ker (polarLM Q)

/-- The integer points of the radical. -/
def radLatSub (Q : MvPolynomial (Fin 5) ℚ) : Submodule ℤ (Fin 5 → ℤ) :=
  Submodule.comap Work.Q44Geom.toRatLM ((radSub Q).restrictScalars ℤ)

/-- The rational points of the cone `V(Q)`. -/
def coneQ (Q : MvPolynomial (Fin 5) ℚ) : Set (Fin 5 → ℚ) := {v | MvPolynomial.eval v Q = 0}

/-- The integer points of the cone `V(Q)`. -/
def coneZ (Q : MvPolynomial (Fin 5) ℚ) : Set (Fin 5 → ℤ) :=
  {v | MvPolynomial.eval (fun i => ((v i : ℤ) : ℚ)) Q = 0}

/-- The integer vectors of the radical. -/
def radLat (Q : MvPolynomial (Fin 5) ℚ) : Set (Fin 5 → ℤ) :=
  {v | (fun i => ((v i : ℤ) : ℚ)) ∈ radQ Q}

/-- The counting set of `quadLatCount`: primitive rank-`3` sublattices of `ℤ^5` with
successive minima bounded by `s` on which `Q` vanishes identically. -/
def Qset (Q : MvPolynomial (Fin 5) ℚ) (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | Work.HP.IsPrimLat L ∧ Work.HP.rk L = 3 ∧
    (∀ j : Fin 3, Work.HP.lam L (j.val + 1) ≤ s j) ∧
    (∀ x : Fin 5 → ℤ, x ∈ L → MvPolynomial.eval (fun i => ((x i : ℤ) : ℚ)) Q = 0)}

end Work.HP.MDEstimates
