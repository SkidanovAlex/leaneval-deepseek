import Mathlib.Analysis.CStarAlgebra.Module.Constructions
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-
# `Work.BoseBoxFock.creC_sum_norm_sq`

The algebraic identity behind the "summed creation operator" norm computation:

for a finite family of annihilation/creation pairs `a l`, `ad l` on a complex
inner product space, satisfying `ad l` is the (formal) adjoint of `a l` and the
canonical commutation relations `[a i, ad j] = δ_{ij}`, and for real weights
`φ l`, one has

  `‖∑_l φ_l · ad_l w‖² = ‖∑_l φ_l · a_l w‖² + (∑_l φ_l²) ‖w‖²`.

Writing `A = ∑_l φ_l a_l` and `C = ∑_l φ_l ad_l` (both linear maps), the two
ingredients are

* `⟪C u, v⟫ = ⟪u, A v⟫` (adjointness of the sums, from `hadj` and realness of `φ`),
* `A ∘ C = C ∘ A + (∑_l φ_l²) · 1` (the CCR summed with weights);

then `‖C w‖² = ⟪C w, C w⟫ = ⟪w, A C w⟫ = ⟪w, C A w⟫ + (∑φ_l²)‖w‖² = ‖A w‖² + …`.
-/

namespace Work.BoseBoxFock

open scoped BigOperators

theorem creC_sum_norm_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {X : Type*} [Fintype X] [DecidableEq X] (a ad : X → H →ₗ[ℂ] H) (φ : X → ℝ) (w : H)
    (hadj : ∀ (i : X) (u v : H), inner ℂ (a i u) v = inner ℂ u (ad i v))
    (hccr : ∀ i j, (a i).comp (ad j) = (ad j).comp (a i) + (if i = j then 1 else 0)) :
    ‖∑ l, ((φ l : ℝ) : ℂ) • ad l w‖ ^ 2
      = ‖∑ l, ((φ l : ℝ) : ℂ) • a l w‖ ^ 2 + (∑ l, φ l ^ 2) * ‖w‖ ^ 2 := by
  -- the two summed operators
  let A : Module.End ℂ H := ∑ l, ((φ l : ℝ) : ℂ) • a l
  let C : Module.End ℂ H := ∑ l, ((φ l : ℝ) : ℂ) • ad l
  have hA_apply : ∀ u : H, A u = ∑ l, ((φ l : ℝ) : ℂ) • a l u := by
    intro u
    change (∑ l, ((φ l : ℝ) : ℂ) • a l) u = ∑ l, ((φ l : ℝ) : ℂ) • a l u
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
  have hC_apply : ∀ u : H, C u = ∑ l, ((φ l : ℝ) : ℂ) • ad l u := by
    intro u
    change (∑ l, ((φ l : ℝ) : ℂ) • ad l) u = ∑ l, ((φ l : ℝ) : ℂ) • ad l u
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply]
  -- `hadj` is symmetric: `ad i` is also *left*-adjoint to `a i`
  have hadj' : ∀ i (u v : H), inner ℂ (ad i u) v = inner ℂ u (a i v) := by
    intro i u v
    rw [← inner_conj_symm (ad i u) v, ← hadj i v u, inner_conj_symm u (a i v)]
  -- adjointness of the summed operators
  have hpair : ∀ u v : H, inner ℂ (C u) v = inner ℂ u (A v) := by
    intro u v
    rw [hC_apply u, hA_apply v, sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [inner_smul_left, inner_smul_right, hadj' l u v, Complex.conj_ofReal]
  have hpair' : ∀ u v : H, inner ℂ (A u) v = inner ℂ u (C v) := by
    intro u v
    rw [← inner_conj_symm (A u) v, ← hpair v u, inner_conj_symm u (C v)]
  -- the commutator relation, evaluated pointwise
  have hterm : ∀ l m, a l (ad m w) - ad m (a l w) = (if l = m then w else 0) := by
    intro l m
    have h := congrArg (fun T : Module.End ℂ H => T w) (hccr l m)
    simp only [LinearMap.comp_apply, LinearMap.add_apply] at h
    rw [h, add_sub_cancel_left]
    split_ifs with hlm <;> simp
  -- `A (C w)` expanded
  have hAC : A (C w) = ∑ l, ∑ m, (((φ l : ℝ) : ℂ) * ((φ m : ℝ) : ℂ)) • a l (ad m w) := by
    rw [hA_apply]
    apply Finset.sum_congr rfl
    intro l _
    rw [hC_apply, map_sum]
    simp only [map_smul, Finset.smul_sum, smul_smul]
  -- `C (A w)` expanded
  have hCA : C (A w) = ∑ m, ∑ l, (((φ m : ℝ) : ℂ) * ((φ l : ℝ) : ℂ)) • ad m (a l w) := by
    rw [hC_apply]
    apply Finset.sum_congr rfl
    intro m _
    rw [hA_apply, map_sum]
    simp only [map_smul, Finset.smul_sum, smul_smul]
  -- `C (A w)` with the summation indices aligned with `hAC`
  have hCA' : C (A w) = ∑ l, ∑ m, (((φ l : ℝ) : ℂ) * ((φ m : ℝ) : ℂ)) • ad m (a l w) := by
    rw [hCA, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    apply Finset.sum_congr rfl; intro m _
    rw [mul_comm]
  -- the commutator `A C - C A`, termwise
  have hdiff : A (C w) - C (A w)
      = ∑ l, ∑ m, (((φ l : ℝ) : ℂ) * ((φ m : ℝ) : ℂ)) •
          (a l (ad m w) - ad m (a l w)) := by
    rw [hAC, hCA', ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro l _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _
    rw [smul_sub]
  -- and its value: `(∑ φ²) • w`
  have hval : ∑ l, ∑ m, (((φ l : ℝ) : ℂ) * ((φ m : ℝ) : ℂ)) •
        (a l (ad m w) - ad m (a l w)) = ((∑ l, φ l ^ 2 : ℝ) : ℂ) • w := by
    simp only [hterm, smul_ite, smul_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_smul]
    congr 1
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro l _
    rw [← sq, ← Complex.ofReal_pow]
  -- hence the commutator identity
  have hkey : A (C w) = C (A w) + ((∑ l, φ l ^ 2 : ℝ) : ℂ) • w := by
    have h : A (C w) - C (A w) = ((∑ l, φ l ^ 2 : ℝ) : ℂ) • w := by rw [hdiff, hval]
    rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  -- the same identity, in inner-product form
  have hcomplex : inner ℂ (C w) (C w)
      = inner ℂ (A w) (A w) + ((∑ l, φ l ^ 2 : ℝ) : ℂ) * inner ℂ w w := by
    calc inner ℂ (C w) (C w) = inner ℂ w (A (C w)) := by rw [hpair w (C w)]
      _ = inner ℂ w (C (A w) + ((∑ l, φ l ^ 2 : ℝ) : ℂ) • w) := by rw [hkey]
      _ = inner ℂ w (C (A w)) + ((∑ l, φ l ^ 2 : ℝ) : ℂ) * inner ℂ w w := by
            rw [inner_add_right, inner_smul_right]
      _ = inner ℂ (A w) (A w) + ((∑ l, φ l ^ 2 : ℝ) : ℂ) * inner ℂ w w := by
            rw [hpair' w (A w)]
  -- pass to real norms
  have hnorm : ((‖C w‖ ^ 2 : ℝ) : ℂ)
      = (((‖A w‖ ^ 2) + (∑ l, φ l ^ 2) * ‖w‖ ^ 2 : ℝ) : ℂ) := by
    have key : ∀ z : H, ((‖z‖ ^ 2 : ℝ) : ℂ) = inner ℂ z z := fun z =>
      (Complex.ofReal_pow (‖z‖) 2).trans (inner_self_eq_norm_sq_to_K z).symm
    rw [key, hcomplex, ← key (A w), ← key w, ← Complex.ofReal_mul, ← Complex.ofReal_add]
  have hreal : ‖C w‖ ^ 2 = ‖A w‖ ^ 2 + (∑ l, φ l ^ 2) * ‖w‖ ^ 2 :=
    Complex.ofReal_injective hnorm
  rw [← hC_apply w, ← hA_apply w]
  exact hreal

end Work.BoseBoxFock
