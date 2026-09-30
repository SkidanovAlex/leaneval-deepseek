import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic
import Submission.Work.BW.hset_zero_cosets_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-!
# `chainIdeal_le_ptIdeal_gone`

The neutral point `gone N = 0·γ` of `G = G_a × G_m^N` lies on `Z(I_r)` for every `r ≤ N+2`, hence
`I_r ≤ ptIdeal N (conePt N (gone N))`.

The mathematical content is the identity

`eval (conePt N y) (applyH w t (homog D P)) = eval y (applyW w t P)`

(dehomogenisation intertwines the homogeneous derivation `derH` with the affine one `derC`).  It is
proved here through the `ℂ`-algebra map

`dehom N : MR N →ₐ[ℂ] MvPolynomial (Fin (N+1)) ℂ`, `X_{i0} ↦ 1`, `X_{i1} ↦ Y_i`,

which satisfies `dehom N (pderiv (i,1) R) = pderiv i (dehom N R)`, `dehom N (derH v R) = derC v
(dehom N R)`, `dehom N (homog D S) = S` and `eval (conePt N y) R = eval y (dehom N R)`.
-/

open MvPolynomial

/-- Variable substitution dehomogenising the cone: `X_{i0} ↦ 1`, `X_{i1} ↦ Y_i`. -/
noncomputable def dehomVar {N : ℕ} : Fin (N + 1) × Fin 2 → MvPolynomial (Fin (N + 1)) ℂ :=
  fun v => if v.2 = 0 then 1 else MvPolynomial.X v.1

/-- The dehomogenisation map `MR N →ₐ[ℂ] MvPolynomial (Fin (N+1)) ℂ`, a left inverse of `homog`. -/
noncomputable def dehom (N : ℕ) : MR N →ₐ[ℂ] MvPolynomial (Fin (N + 1)) ℂ :=
  MvPolynomial.aeval (dehomVar (N := N))

lemma dehom_X_zero (N : ℕ) (i : Fin (N + 1)) :
    dehom N (MvPolynomial.X (i, 0)) = 1 := by
  simp [dehom, dehomVar]

lemma dehom_X_one (N : ℕ) (i : Fin (N + 1)) :
    dehom N (MvPolynomial.X (i, 1)) = MvPolynomial.X i := by
  simp [dehom, dehomVar]

lemma dehom_C (N : ℕ) (c : ℂ) : dehom N (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [dehom]

/-- The dehomogenisation is compatible with the partial derivative in the `X_{i1}` direction. -/
lemma dehom_pderiv_X (N : ℕ) (n : Fin (N+1) × Fin 2) (k : Fin (N+1)) :
    dehom N (MvPolynomial.pderiv (k,1) (MvPolynomial.X n)) =
      MvPolynomial.pderiv k (dehom N (MvPolynomial.X n)) := by
  obtain ⟨i, b⟩ := n
  fin_cases b
  · change dehom N (MvPolynomial.pderiv (k,1) (MvPolynomial.X (i,0))) =
      MvPolynomial.pderiv k (dehom N (MvPolynomial.X (i,0)))
    rw [dehom_X_zero]
    rw [MvPolynomial.pderiv_X_of_ne (i := (k,1)) (j := (i,0)) (by simp)]
    simp
  · change dehom N (MvPolynomial.pderiv (k,1) (MvPolynomial.X (i,1))) =
      MvPolynomial.pderiv k (dehom N (MvPolynomial.X (i,1)))
    rw [dehom_X_one]
    by_cases h : i = k
    · subst h
      rw [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_self]
      simp
    · rw [MvPolynomial.pderiv_X_of_ne (i := (k,1)) (j := (i,1)) (by simpa using h)]
      rw [MvPolynomial.pderiv_X_of_ne (i := k) (j := i) h]
      simp

/-- The dehomogenisation intertwines `pderiv (k,1)` on the cone with `pderiv k` downstairs. -/
lemma dehom_pderiv_one (N : ℕ) (R : MR N) (k : Fin (N + 1)) :
    dehom N (MvPolynomial.pderiv (k, 1) R) = MvPolynomial.pderiv k (dehom N R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
      have h1 : dehom N (MvPolynomial.pderiv (k,1) (p * MvPolynomial.X n))
          = MvPolynomial.pderiv k (dehom N p) * dehom N (MvPolynomial.X n)
            + dehom N p * dehom N (MvPolynomial.pderiv (k,1) (MvPolynomial.X n)) := by
        rw [pderiv_mul, map_add, map_mul, map_mul, hp]
      have h2 : MvPolynomial.pderiv k (dehom N (p * MvPolynomial.X n))
          = MvPolynomial.pderiv k (dehom N p * dehom N (MvPolynomial.X n)) := by rw [map_mul]
      rw [h1, h2, pderiv_mul, dehom_pderiv_X]

/-- Dehomogenisation carries the homogeneous derivation `derH v` to the affine one `derC v`. -/
lemma dehom_derH (N : ℕ) (v : Fin (N+1) → ℂ) (R : MR N) :
    dehom N (derH v R) = derC v (dehom N R) := by
  simp only [derH, derC, map_add, map_sum]
  congr 1
  · rw [map_mul, map_mul, dehom_pderiv_one, dehom_X_zero, dehom_C, mul_one]
  · apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, map_mul, dehom_pderiv_one, dehom_X_one, dehom_C]

lemma dehom_derH_iterate (N : ℕ) (v : Fin (N+1) → ℂ) (n : ℕ) (R : MR N) :
    dehom N ((derH v)^[n] R) = (derC v)^[n] (dehom N R) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', dehom_derH, ih]

lemma dehom_foldr {N q : ℕ} (w : Fin q → Fin (N+1) → ℂ) (t : Fin q → ℕ) :
    ∀ (L : List (Fin q)) (R : MR N),
      dehom N (L.foldr (fun m Q => (derH (w m))^[t m] Q) R)
        = L.foldr (fun m Q => (derC (w m))^[t m] Q) (dehom N R) := by
  intro L
  induction L with
  | nil => intro R; simp
  | cons m L ih =>
      intro R
      simp only [List.foldr_cons]
      rw [dehom_derH_iterate, ih]

/-- Dehomogenisation carries `applyH w t` (the `δ^t` of the cone) to `applyW w t`. -/
lemma dehom_applyH {N q : ℕ} (w : Fin q → Fin (N+1) → ℂ) (t : Fin q → ℕ) (R : MR N) :
    dehom N (applyH w t R) = applyW w t (dehom N R) := by
  unfold applyH applyW
  exact dehom_foldr w t (List.finRange q) R

lemma monomial_eq_prod {N : ℕ} (a : Fin (N+1) →₀ ℕ) (c : ℂ) :
    MvPolynomial.monomial a c = MvPolynomial.C c * ∏ i : Fin (N+1), MvPolynomial.X i ^ (a i) := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod]
  exact Finset.prod_subset (Finset.subset_univ _)
    (fun i _ hi => by simp [Finsupp.notMem_support_iff.mp hi])

/-- Dehomogenisation inverts the homogenisation `homog D`. -/
lemma dehom_homog (N : ℕ) (D : Fin (N+1) → ℕ) (S : MvPolynomial (Fin (N+1)) ℂ) :
    dehom N (homog D S) = S := by
  conv_rhs => rw [MvPolynomial.as_sum S]
  rw [homog, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_mul, dehom_C, monomial_eq_prod]
  congr 1
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_mul, map_pow, map_pow, dehom_X_one, dehom_X_zero]
  simp

/-- Evaluating at the cone point over `y` is `dehom` followed by evaluating at `y`. -/
lemma eval_dehom (N : ℕ) (y : Fin (N+1) → ℂ) (R : MR N) :
    MvPolynomial.eval (conePt N y) R = MvPolynomial.eval y (dehom N R) := by
  rw [← MvPolynomial.aeval_eq_eval (conePt N y), ← MvPolynomial.aeval_eq_eval y]
  rw [show dehom N R = MvPolynomial.aeval (dehomVar (N:=N)) R from rfl]
  rw [MvPolynomial.comp_aeval_apply (dehomVar (N := N)) (MvPolynomial.aeval y) R]
  have hfun : (fun v => MvPolynomial.aeval y (dehomVar (N:=N) v)) = conePt N y := by
    funext v
    obtain ⟨i, b⟩ := v
    fin_cases b
    · change MvPolynomial.aeval y (dehomVar (N:=N) (i,0)) = conePt N y (i,0)
      simp [dehomVar, conePt]
    · change MvPolynomial.aeval y (dehomVar (N:=N) (i,1)) = conePt N y (i,1)
      simp [dehomVar, conePt]
  rw [hfun]

/-- The dehomogenised generators of `I_r` vanish at the cone point over `gone N`. -/
lemma eval_transl_applyH_homog_gone {N q : ℕ} (P : MvPolynomial (Fin (N + 1)) ℂ)
    (D : Fin (N + 1) → ℕ) (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ) (s : ℕ)
    (t : Fin q → ℕ) :
    MvPolynomial.eval (conePt N (gone N))
        (transl (ptTheta θ s) (applyH w t (homog D P))) =
      MvPolynomial.eval (ptTheta θ s) (applyW w t P) := by
  rw [(transl_basic (ptTheta θ s) (ptTheta θ s)).1 (conePt N (gone N))
        (applyH w t (homog D P))]
  rw [(transl_basic (ptTheta θ s) (ptTheta θ s)).2.1 (gone N)]
  rw [hsc_gmul_gone_right (ptTheta θ s)]
  rw [eval_dehom, dehom_applyH, dehom_homog]

/-- The neutral point `gone N = 0·γ` of `G` lies on `Z(I_r)` for every `r ≤ N+2`: every generator
`τ_{sγ} δ^t P^h` of `I_r` has `s ≤ ∑_{m<r-1} Sq m ≤ ∑_{m<N+1} Sq m` and `|t| ≤ ∑_{m<r-1} Tq m ≤
∑_{m<N+1} Tq m`, so the hypothesis `hvan` (plus `transl_basic`/`derH_basic` and
`gmul (ptTheta θ s) (gone N) = ptTheta θ s`) evaluates it to `0` at the cone point over `gone N`.
Consequently `I_r ≤ ptIdeal N (conePt N (gone N))`. -/
theorem chainIdeal_le_ptIdeal_gone {N q : ℕ} (P : MvPolynomial (Fin (N + 1)) ℂ)
    (D : Fin (N + 1) → ℕ) (hdeg : ∀ i, P.degreeOf i ≤ D i)
    (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ) (Sq Tq : ℕ → ℕ) (r : ℕ) (hr : r ≤ N + 2)
    (hvan : ∀ s, s ≤ ∑ m ∈ Finset.range (N + 1), Sq m → ∀ t : Fin q → ℕ,
      ∑ k, t k ≤ ∑ m ∈ Finset.range (N + 1), Tq m →
      MvPolynomial.eval (ptTheta θ s) (applyW w t P) = 0) :
    chainIdeal w θ D P (∑ m ∈ Finset.range (r - 1), Sq m) (∑ m ∈ Finset.range (r - 1), Tq m) ≤
      ptIdeal N (conePt N (gone N)) := by
  have _hdeg : ∀ i, P.degreeOf i ≤ D i := hdeg
  have hsub : Finset.range (r - 1) ⊆ Finset.range (N + 1) := by
    rw [Finset.range_subset]
    intro x hx
    rw [Finset.mem_range]
    omega
  have hSq : ∑ m ∈ Finset.range (r - 1), Sq m ≤ ∑ m ∈ Finset.range (N + 1), Sq m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
  have hTq : ∑ m ∈ Finset.range (r - 1), Tq m ≤ ∑ m ∈ Finset.range (N + 1), Tq m :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
  rw [chainIdeal, Ideal.span_le]
  rintro F ⟨s, t, hs, ht, rfl⟩
  simp only [SetLike.mem_coe, ptIdeal, RingHom.mem_ker]
  rw [eval_transl_applyH_homog_gone]
  exact hvan s (le_trans hs hSq) t (le_trans ht hTq)

end Work.BW
