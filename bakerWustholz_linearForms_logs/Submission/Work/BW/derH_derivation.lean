import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! # `derH` is a derivation with constant coefficients

`derH w` is the homogeneous (multidegree-preserving) invariant derivation
`w₀ X₀₀ ∂_{X₀₁} + ∑ᵢ wᵢ X_{i1} ∂_{X_{i1}}` of `(P¹)^{N+1}`, and `applyH w t` is the
composition of its iterates. This file proves that `derH` is additive, satisfies Leibniz,
is `ℂ`-linear, kills `1`, is (as a derivation) independent of the parameter `w` so that any
two commute, and that consequently `derH (w k)` raises the `k`-th exponent of `applyH`.

The proof packages `derH w` as a genuine `Derivation ℂ (MR N) (MR N)` (a `ℂ`-sum of the
`ℂ`-linear derivations `C (w j) * X (mulV j) • pderiv (j,1)`), which gives additivity,
Leibniz and `ℂ`-linearity for free; commutativity is a finite check against the generators
`X u`, and the shift identity follows from the fold structure of `applyH`. -/

open MvPolynomial (C X pderiv)

/-- The variable by which `derH v` multiplies in the direction `(j,1)`: `X_{00}` for `j = 0`
(a translation along the `G_a` factor) and `X_{j1}` otherwise. -/
private def mulV {N : ℕ} (j : Fin (N + 1)) : Fin (N + 1) × Fin 2 :=
  if j = 0 then (0, 0) else (j, 1)

/-- `derH v` written as a single sum over `Fin (N+1)`. -/
private lemma derH_eq_sum {N : ℕ} (v : Fin (N + 1) → ℂ) (F : MR N) :
    derH v F = ∑ j : Fin (N + 1), C (v j) * X (mulV j) * pderiv (j, 1) F := by
  rw [derH, Fin.sum_univ_succ]
  simp only [mulV, ite_true, Fin.succ_ne_zero]
  simp

/-- Value of `derH v` on a coordinate variable. -/
private lemma derH_X {N : ℕ} (v : Fin (N + 1) → ℂ) (u : Fin (N + 1) × Fin 2) :
    derH v (X u) = if u.2 = 1 then C (v u.1) * X (mulV u.1) else 0 := by
  obtain ⟨j0, b⟩ := u
  rw [derH_eq_sum]
  simp only [MvPolynomial.pderiv_X]
  by_cases hb : b = 1
  · subst hb
    rw [Finset.sum_eq_single j0]
    · rw [Pi.single_eq_same]; simp
    · intro x _ hx
      rw [Pi.single_eq_of_ne (by intro h; exact hx (Prod.ext_iff.mp h).1.symm)]; simp
    · intro h; exact absurd (Finset.mem_univ j0) h
  · rw [Finset.sum_eq_zero]
    · simp [hb]
    · intro x _
      rw [Pi.single_eq_of_ne (by intro h; exact hb (congrArg Prod.snd h))]; simp

private lemma derH_X_mulV {N : ℕ} (v : Fin (N + 1) → ℂ) (j : Fin (N + 1)) :
    derH v (X (mulV j)) = if j = 0 then 0 else C (v j) * X (mulV j) := by
  rw [derH_X]
  by_cases hj : j = 0
  · subst hj; simp [mulV]
  · simp [mulV, hj]

private lemma derH_zero {N : ℕ} (v : Fin (N + 1) → ℂ) : derH v 0 = 0 := by simp [derH]

private lemma derH_C_mul {N : ℕ} (v : Fin (N + 1) → ℂ) (c : ℂ) (F : MR N) :
    derH v (C c * F) = C c * derH v F := by
  simp only [derH, MvPolynomial.pderiv_C_mul]
  rw [mul_add, Finset.mul_sum]
  ring_nf

/-- `derH v` as a genuine derivation. -/
private noncomputable def derHd {N : ℕ} (v : Fin (N + 1) → ℂ) :
    Derivation ℂ (MR N) (MR N) :=
  ∑ j : Fin (N + 1), (C (v j) * X (mulV j)) • pderiv (j, 1)

private lemma sum_deriv_apply {N : ℕ} (s : Finset (Fin (N + 1)))
    (D : Fin (N + 1) → Derivation ℂ (MR N) (MR N)) (F : MR N) :
    (∑ i ∈ s, D i) F = ∑ i ∈ s, D i F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

private lemma derHd_apply {N : ℕ} (v : Fin (N + 1) → ℂ) (F : MR N) :
    derHd v F = derH v F := by
  rw [derH_eq_sum, derHd, sum_deriv_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Derivation.smul_apply, smul_eq_mul]

private lemma derH_leibniz {N : ℕ} (v : Fin (N + 1) → ℂ) (a b : MR N) :
    derH v (a * b) = derH v a * b + a * derH v b := by
  rw [← derHd_apply, ← derHd_apply, ← derHd_apply, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

private lemma derH_add {N : ℕ} (v : Fin (N + 1) → ℂ) (F G : MR N) :
    derH v (F + G) = derH v F + derH v G := by
  rw [← derHd_apply, ← derHd_apply, ← derHd_apply, Derivation.map_add]

private lemma derH_comm {N : ℕ} (v v' : Fin (N + 1) → ℂ) (F : MR N) :
    derH v (derH v' F) = derH v' (derH v F) := by
  have h : ⁅derHd v, derHd v'⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro u
    simp only [Derivation.commutator_apply, derHd_apply, Derivation.zero_apply]
    by_cases h2 : u.2 = 1
    · by_cases h1 : u.1 = 0
      · rw [derH_X v' u, derH_X v u, ite_eq_left h2, ite_eq_left h2, derH_C_mul, derH_C_mul,
          derH_X_mulV, derH_X_mulV, ite_eq_left h1, ite_eq_left h1]
        simp
      · rw [derH_X v' u, derH_X v u, ite_eq_left h2, ite_eq_left h2, derH_C_mul, derH_C_mul,
          derH_X_mulV, derH_X_mulV, ite_eq_right h1, ite_eq_right h1]
        ring
    · rw [derH_X v' u, derH_X v u, ite_eq_right h2, ite_eq_right h2, derH_zero, derH_zero]
      ring
  have h2 : derH v (derH v' F) - derH v' (derH v F) = 0 := by
    have hh := Derivation.commutator_apply (D1 := derHd v) (D2 := derHd v') F
    rw [h, Derivation.zero_apply, derHd_apply, derHd_apply, derHd_apply, derHd_apply] at hh
    exact hh.symm
  exact sub_eq_zero.mp h2

/-- `derH v` is `ℂ`-linear (for the `MR N`-module structure induced by its `ℂ`-algebra
structure). -/
private lemma derH_smul {N : ℕ} (v : Fin (N + 1) → ℂ) (c : ℂ) (F : MR N) :
    derH v (c • F) = c • derH v F := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, derH_C_mul]

/-- `derH v` kills `1`. -/
private lemma derH_one {N : ℕ} (v : Fin (N + 1) → ℂ) : derH v (1 : MR N) = 0 := by
  simp [derH]

/-! ### The fold structure of `applyH` -/

private lemma derH_iterate_add {N : ℕ} (v : Fin (N + 1) → ℂ) (k : ℕ) (F G : MR N) :
    (derH v)^[k] (F + G) = (derH v)^[k] F + (derH v)^[k] G := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Function.iterate_succ_apply']; rw [ih, derH_add]

private lemma derH_pow_comm {N : ℕ} (v v' : Fin (N + 1) → ℂ)
    (hcomm : ∀ F, derH v (derH v' F) = derH v' (derH v F)) (k : ℕ) (F : MR N) :
    derH v ((derH v')^[k] F) = (derH v')^[k] (derH v F) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]

/-- The composition of the derivations `derH (w m)` with multiplicities `t m`, over a list
`l` (the definitional unfolding of `applyH` for `l = List.finRange q`). -/
private noncomputable def apFold {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (t : Fin q → ℕ) (F : MR N) : MR N :=
  l.foldr (fun m Q => (derH (w m))^[t m] Q) F

private lemma applyH_eq_apFold {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ)
    (F : MR N) : applyH w t F = apFold w (List.finRange q) t F := rfl

private lemma apFold_cons {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (m : Fin q)
    (l : List (Fin q)) (t : Fin q → ℕ) (F : MR N) :
    apFold w (m :: l) t F = (derH (w m))^[t m] (apFold w l t F) := rfl

private lemma apFold_congr {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    {u v : Fin q → ℕ} (h : ∀ m ∈ l, u m = v m) (F : MR N) :
    apFold w l u F = apFold w l v F := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [apFold_cons]
    rw [h m (by simp), ih (fun j hj => h j (by simp [hj]))]

private lemma apFold_eq_self {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (t : Fin q → ℕ) (F : MR N) (h : ∀ m ∈ l, t m = 0) : apFold w l t F = F := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [apFold_cons]
    rw [h m (by simp), ih (fun j hj => h j (by simp [hj]))]
    simp

private lemma apFold_add {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (t : Fin q → ℕ) (F G : MR N) :
    apFold w l t (F + G) = apFold w l t F + apFold w l t G := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [apFold_cons, ih, derH_iterate_add]

private lemma apFold_derH_comm {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    {m : Fin q} (hm : m ∉ l) (t : Fin q → ℕ) (F : MR N) :
    derH (w m) (apFold w l t F) = apFold w l t (derH (w m) F) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hm' : m ∉ l := fun h => hm (List.mem_cons_of_mem j h)
    have hmj : m ≠ j := fun h => hm (h ▸ List.mem_cons_self)
    simp only [apFold_cons]
    rw [derH_pow_comm (w m) (w j) (fun F => derH_comm _ _ F) (t j) (apFold w l t F), ih hm']

private lemma apFold_derH_iterate_comm {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ)
    (l : List (Fin q)) {m : Fin q} (hm : m ∉ l) (t : Fin q → ℕ) (k : ℕ) (F : MR N) :
    (derH (w m))^[k] (apFold w l t F) = apFold w l t ((derH (w m))^[k] F) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, apFold_derH_comm w l hm]

private lemma apFold_comp {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (hl : l.Nodup) (t t' : Fin q → ℕ) (F : MR N) :
    apFold w l t (apFold w l t' F) = apFold w l (t + t') F := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    have hml : m ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    simp only [apFold_cons, Pi.add_apply]
    rw [← apFold_derH_iterate_comm w l hml t (t' m), ← Function.iterate_add_apply, ih hl']

private lemma apFold_single {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (hl : l.Nodup) {m : Fin q} (hm : m ∈ l) (F : MR N) :
    apFold w l (Pi.single m 1) F = derH (w m) F := by
  induction l with
  | nil => simp at hm
  | cons j l ih =>
    have hj : j ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    simp only [apFold_cons]
    by_cases hjm : j = m
    · subst hjm
      rw [Pi.single_eq_same]
      rw [apFold_eq_self w l (Pi.single j 1) F (fun k hk => by
        rw [Pi.single_eq_of_ne (by intro h; exact hj (h ▸ hk))])]
      simp
    · rw [Pi.single_eq_of_ne (by intro h; exact hjm h)]
      simp only [Function.iterate_zero_apply]
      exact ih hl' (by rcases List.mem_cons.mp hm with h | h
                       · exact absurd h.symm hjm
                       · exact h)

/-- The formal derivatives compose: `applyH w t ∘ applyH w t' = applyH w (t + t')`. -/
private lemma applyH_compose {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t t' : Fin q → ℕ)
    (F : MR N) : applyH w t (applyH w t' F) = applyH w (t + t') F := by
  rw [applyH_eq_apFold, applyH_eq_apFold, applyH_eq_apFold,
    apFold_comp w (List.finRange q) (List.nodup_finRange q)]

private lemma applyH_single {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (m : Fin q) (F : MR N) :
    applyH w (Pi.single m 1) F = derH (w m) F := by
  rw [applyH_eq_apFold]
  exact apFold_single w (List.finRange q) (List.nodup_finRange q) (List.mem_finRange m) F

/-- `derH` (the homogeneous invariant derivation `w₀X₀₀∂_{X₀₁} + ∑ wᵢX_{i1}∂_{X_{i1}}`) is a
derivation with constant coefficients: additive, Leibniz, `ℂ`-linear, kills `1`, and any two
`derH`'s commute; consequently `derH (w k)` shifts `applyH w t` by `e_k`. -/
theorem derH_derivation {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) :
    (∀ (i : Fin q) (F G : MR N), derH (w i) (F * G) = derH (w i) F * G + F * derH (w i) G) ∧
    (∀ (i : Fin q) (F G : MR N), derH (w i) (F + G) = derH (w i) F + derH (w i) G) ∧
    (∀ (i : Fin q) (c : ℂ) (F : MR N), derH (w i) (c • F) = c • derH (w i) F) ∧
    (∀ i : Fin q, derH (w i) 1 = 0) ∧
    (∀ (i j : Fin q) (F : MR N), derH (w i) (derH (w j) F) = derH (w j) (derH (w i) F)) ∧
    (∀ (t : Fin q → ℕ) (k : Fin q) (F : MR N),
      derH (w k) (applyH w t F) = applyH w (t + Pi.single k 1) F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i F G; exact derH_leibniz (w i) F G
  · intro i F G; exact derH_add (w i) F G
  · intro i c F; exact derH_smul (w i) c F
  · intro i; exact derH_one (w i)
  · intro i j F; exact derH_comm (w i) (w j) F
  · intro t k F
    rw [← applyH_single w k (applyH w t F), applyH_compose, add_comm]

end Work.BW
