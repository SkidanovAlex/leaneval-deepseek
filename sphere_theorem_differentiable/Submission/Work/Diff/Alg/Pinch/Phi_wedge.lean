import Mathlib
import Submission.Work.Diff.Alg.Pinch.Qop
import Submission.Work.Diff.Alg.q2p_transform
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.Phi_wedge_aux
import Submission.Work.Diff.Alg.Pinch.cR4_wedge_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Phi` of a wedge is the (real) isotropic curvature form

`Phi R X Y = ∑ Rᵢⱼₖₗ Xᵢⱼ Yₖₗ` (`Qop.lean`) is the ℂ-bilinear form of the curvature array `R` on
pair-indexed vectors.  For the alternating vector `ζ ∧ η` the value on `(ζ ∧ η, conj (ζ ∧ η))` is
`4` times the real isotropic curvature `EFun` of the complex `2`-plane spanned by `ζ, η` (four times
because the sum runs over ordered pairs, while the unitary/isotropic form is the sum over `i < j`).

The proof splits the computation into two independent pieces.

* **Wedge expansion** (`Phi_wedge_wedge_aux`): `Phi R (ζ ∧ η) (ζ' ∧ η') = 4 · cR4 R ζ η ζ' η'`.
  Expanding the two alternating combinations gives four sums; the antisymmetries of `R` in the first
  and in the last index pair (`IsAlgCurv.1` and `IsAlgCurv_antisym₃₄`) identify the last three with
  `±` the first, hence the factor `4`.
* **Reality** (`cR4_wedge_real`, delegated module `Pinch/cR4_wedge_real.lean`) : `cR4 R ζ η (star ζ) (star η)` is `(EFun R … : ℂ)`.  Its real
  part is `cR4_re` (`Q2P.transform`); its imaginary part vanishes because `star` acts on `cR4` by
  conjugation (`cR4_star`) and `cR4` is invariant under `(a,b,c,d) ↦ (c,d,a,b)` (`cR4_pair`), so
  `star (cR4 R ζ η ζ̄ η̄) = cR4 R ζ η ζ̄ η̄`.

Since `bar (ζ ∧ η) = ζ̄ ∧ η̄` (`bar_wedgeF`), the two pieces combine into the statement.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open Work.Diff.Alg (cR4)
open Work.Diff.Alg.Q2P (IsAlgCurv_antisym₃₄)

variable {n : ℕ}

/-! ## Reduction of a four-fold sum against an antisymmetrized pair of indices -/

/-- `∑ F a b c d (ζa ηb − ζb ηa) = 2 ∑ F a b c d (ζa ηb)` for `F` antisymmetric in the first pair.
The summands are ordered so that the pair `(c,d)` is summed inside; only the antisymmetry in the
first index pair is used. -/
private theorem sum4_alt₁ {ζ η : Fin n → ℂ} {F : Fin n → Fin n → Fin n → Fin n → ℂ}
    (hF : ∀ a b c d, F b a c d = - F a b c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ a * η b - ζ b * η a))
      = 2 * ∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ a * η b) := by
  have hA : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ a * η b - ζ b * η a))
      = (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ a * η b))
        - (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ b * η a)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hzero : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ b * η a))
      + (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ a * η b)) = 0 := by
    rw [sum4_swap12C (F := fun i j k l => F i j k l * (ζ j * η i))]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    refine Finset.sum_eq_zero (fun c _ => ?_)
    refine Finset.sum_eq_zero (fun d _ => ?_)
    rw [hF a b c d]
    ring
  have hB : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ b * η a))
      = - (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ a * η b)) :=
    eq_neg_iff_add_eq_zero.mpr hzero
  rw [hA, hB]
  ring

/-- `∑ F a b c d (ζc ηd − ζd ηc) = 2 ∑ F a b c d (ζc ηd)` for `F` antisymmetric in the last pair. -/
private theorem sum4_alt₂ {ζ η : Fin n → ℂ} {F : Fin n → Fin n → Fin n → Fin n → ℂ}
    (hF : ∀ a b c d, F a b d c = - F a b c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ c * η d - ζ d * η c))
      = 2 * ∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ c * η d) := by
  have hA : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ c * η d - ζ d * η c))
      = (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ c * η d))
        - (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ d * η c)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  have hzero : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ d * η c))
      + (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ c * η d)) = 0 := by
    rw [sum4_swap34C (F := fun i j k l => F i j k l * (ζ l * η k))]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero (fun a _ => ?_)
    refine Finset.sum_eq_zero (fun b _ => ?_)
    refine Finset.sum_eq_zero (fun c _ => ?_)
    refine Finset.sum_eq_zero (fun d _ => ?_)
    rw [hF a b c d]
    ring
  have hB : (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ d * η c))
      = - (∑ a, ∑ b, ∑ c, ∑ d, F a b c d * (ζ c * η d)) :=
    eq_neg_iff_add_eq_zero.mpr hzero
  rw [hA, hB]
  ring

/-! ## The two halves -/

/-- **Wedge expansion.** `Phi` of a pair of wedges is `4` times the complexified curvature form. -/
private theorem Phi_wedge_wedge_aux (R : Curv4 n) (hR : IsAlgCurv R) (ζ η ζ' η' : Fin n → ℂ) :
    Phi R (wedgeF ζ η) (wedgeF ζ' η') = 4 * cR4 R ζ η ζ' η' := by
  have h0 : Phi R (wedgeF ζ η) (wedgeF ζ' η')
      = ∑ a, ∑ b, ∑ c, ∑ d,
          (R a b c d : ℂ) * (ζ a * η b - ζ b * η a) * (ζ' c * η' d - ζ' d * η' c) := by
    rw [Phi_quad]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    simp [wedgeF]
  have h1 : (∑ a, ∑ b, ∑ c, ∑ d,
        (R a b c d : ℂ) * (ζ a * η b - ζ b * η a) * (ζ' c * η' d - ζ' d * η' c))
      = ∑ a, ∑ b, ∑ c, ∑ d,
          ((R a b c d : ℂ) * (ζ' c * η' d - ζ' d * η' c)) * (ζ a * η b - ζ b * η a) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  have hF1 : ∀ a b c d : Fin n,
      (R b a c d : ℂ) * (ζ' c * η' d - ζ' d * η' c)
        = - ((R a b c d : ℂ) * (ζ' c * η' d - ζ' d * η' c)) := by
    intro a b c d
    rw [hR.1 a b c d]
    push_cast
    ring
  have h2 : (∑ a, ∑ b, ∑ c, ∑ d,
        ((R a b c d : ℂ) * (ζ' c * η' d - ζ' d * η' c)) * (ζ a * η b))
      = ∑ a, ∑ b, ∑ c, ∑ d,
          ((R a b c d : ℂ) * (ζ a * η b)) * (ζ' c * η' d - ζ' d * η' c) := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  have hF2 : ∀ a b c d : Fin n,
      (R a b d c : ℂ) * (ζ a * η b) = - ((R a b c d : ℂ) * (ζ a * η b)) := by
    intro a b c d
    rw [IsAlgCurv_antisym₃₄ hR a b c d]
    push_cast
    ring
  have h3 : (∑ a, ∑ b, ∑ c, ∑ d, (R a b c d : ℂ) * (ζ a * η b) * (ζ' c * η' d))
      = cR4 R ζ η ζ' η' := by
    rw [cR4]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    apply Finset.sum_congr rfl; intro d _
    ring
  rw [h0, h1,
    sum4_alt₁ (F := fun a b c d => (R a b c d : ℂ) * (ζ' c * η' d - ζ' d * η' c)) hF1,
    h2, sum4_alt₂ (F := fun a b c d => (R a b c d : ℂ) * (ζ a * η b)) hF2, h3]
  ring

/-! ## The target -/

theorem Phi_wedge (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (ζ η : Fin n → ℂ) :
    Work.Diff.Alg.Pinch.Phi R (Work.Diff.Alg.Pinch.wedgeF ζ η) (Work.Diff.Alg.Pinch.bar (Work.Diff.Alg.Pinch.wedgeF ζ η))
      = 4 * (Work.Diff.Alg.Q2P.EFun R (Work.Diff.Alg.Q2P.cRe ζ) (Work.Diff.Alg.Q2P.cIm ζ) (Work.Diff.Alg.Q2P.cRe η) (Work.Diff.Alg.Q2P.cIm η) : ℂ) := by
  rw [bar_wedgeF, Phi_wedge_wedge_aux R hR ζ η (star ζ) (star η), cR4_wedge_real n R hR ζ η]

end Work.Diff.Alg.Pinch
