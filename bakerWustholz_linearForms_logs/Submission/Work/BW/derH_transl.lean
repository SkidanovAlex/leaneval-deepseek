import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! ### B1 `derH_transl`: the invariant derivation commutes with translation

Node `derH_transl` of the block-B split of `zero_estimate_stepwise` (see DESIGN_B.md, item B1;
it is the third of the three B1 commutation statements, together with `transl_basic` and
`derH_basic`).

`transl g` is the pull-back `F ↦ F ∘ (g ⋆ ·)` on the homogeneous coordinate ring, realised as
`MvPolynomial.aeval (uT g)` for the variable substitution `uT g`

* `X_{i0} ↦ X_{i0}`,
* `X_{01} ↦ X_{01} + g₀ X_{00}`,
* `X_{i1} ↦ gᵢ X_{i1}`  (`i = j.succ`),

and `derH w = w₀ X_{00} ∂_{X_{01}} + ∑ᵢ wᵢ X_{i1} ∂_{X_{i1}}` is the invariant derivation with Lie
vector `w`.  Since `G = G_a × G_m^N` is abelian, the flows of `w` and of `g` commute, so `derH w`
commutes with `transl g`.

The proof is a chain-rule computation.  `derH w` is `ℂ`-linear, so it suffices to know, for the two
relevant variables `X_{01}` (with `c = 1`) and `X_{i1}` (`i = j.succ`, with `c = gᵢ`),

`∂_{X_k}(transl g F) = c · transl g (∂_{X_k} F)`.

This is the multivariate chain rule for `pderiv` under an `aeval` substitution `u` whose derivative
along `X_k` is concentrated at `X_k` itself: if `∂_{X_k}(u i) = c · δ_{ik}` then
`∂_{X_k}(aeval u F) = c · aeval u (∂_{X_k} F)`.  We prove that general statement (`pderiv_aeval_eq`)
by `MvPolynomial.induction_on`, and then verify its hypothesis for `u = uT g`. -/

namespace Work.BW

/-- The variable substitution defining `transl g`, named so that `transl g = aeval (uT g)` holds by
definitional equality. -/
private noncomputable def uT {N : ℕ} (g : Fin (N + 1) → ℂ) : Fin (N + 1) × Fin 2 → MR N :=
  fun v => if v.2 = 0 then MvPolynomial.X v
    else if v.1 = 0 then MvPolynomial.X v + MvPolynomial.C (g 0) * MvPolynomial.X (0, 0)
    else MvPolynomial.C (g v.1) * MvPolynomial.X v

/-- `aeval u` sends `∂_k X_i` to `δ_{ik}`. -/
private lemma aeval_pderiv_X {R : Type*} [CommSemiring R] {σ : Type*} [DecidableEq σ]
    (u : σ → MvPolynomial σ R) (k i : σ) :
    MvPolynomial.aeval (R := R) u (MvPolynomial.pderiv k (MvPolynomial.X i)) =
      Pi.single (M := fun _ => MvPolynomial σ R) k (1 : MvPolynomial σ R) i := by
  rw [MvPolynomial.pderiv_X]
  simp only [Pi.single_apply]
  split_ifs <;> simp

/-- Multivariate chain rule, in the case that the derivative of the substitution `u` in the
direction `k` is concentrated at `k` with constant coefficient `c`:
`∂_k (aeval u F) = c · aeval u (∂_k F)`. -/
private lemma pderiv_aeval_eq {R : Type*} [CommSemiring R] {σ : Type*} [DecidableEq σ]
    (u : σ → MvPolynomial σ R) (k : σ) (c : R)
    (h : ∀ i, MvPolynomial.pderiv k (u i) =
      MvPolynomial.C c * Pi.single (M := fun _ => MvPolynomial σ R) k (1 : MvPolynomial σ R) i)
    (F : MvPolynomial σ R) :
    MvPolynomial.pderiv k (MvPolynomial.aeval (R := R) u F)
      = MvPolynomial.C c * MvPolynomial.aeval (R := R) u (MvPolynomial.pderiv k F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X p i hp =>
      simp only [MvPolynomial.pderiv_mul, map_mul, map_add, MvPolynomial.aeval_X,
        hp, h i, aeval_pderiv_X u k i]
      ring

/-- The chain-rule hypothesis for `uT g` and the variable `X_{01}` (with `c = 1`). -/
private lemma uT_pderiv_zero_one {N : ℕ} (g : Fin (N + 1) → ℂ) :
    ∀ i, MvPolynomial.pderiv (0,1) (uT g i) =
      MvPolynomial.C (1 : ℂ) * Pi.single (M := fun _ => MR N) (0,1) (1 : MR N) i := by
  intro i
  obtain ⟨a, b⟩ := i
  fin_cases b
  · simp [uT, MvPolynomial.pderiv_X]
  · obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ a
    · simp [uT, MvPolynomial.pderiv_X]
    · simp [uT, MvPolynomial.pderiv_X]

/-- The chain-rule hypothesis for `uT g` and the variable `X_{i1}` (`i = j.succ`), with
`c = g i.succ`. -/
private lemma uT_pderiv_succ {N : ℕ} (g : Fin (N + 1) → ℂ) (i : Fin N) :
    ∀ j, MvPolynomial.pderiv (i.succ,1) (uT g j) =
      MvPolynomial.C (g i.succ) * Pi.single (M := fun _ => MR N) (i.succ,1) (1 : MR N) j := by
  intro j
  obtain ⟨a, b⟩ := j
  obtain rfl | ⟨b', rfl⟩ := Fin.eq_zero_or_eq_succ b
  · simp [uT, MvPolynomial.pderiv_X]
  obtain rfl | ⟨a', rfl⟩ := Fin.eq_zero_or_eq_succ a
  · simp [uT, MvPolynomial.pderiv_X]
  rw [uT]
  simp only [Fin.succ_ne_zero, ite_false]
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X]
  by_cases h : a' = i
  · subst h; simp [Subsingleton.elim b' 0]
  · rw [Pi.single_eq_of_ne (show (a'.succ, b'.succ) ≠ (i.succ, (1 : Fin 2)) by simp [h])]
    simp

/-- B1c (Philippon 4.3).  The invariant derivation `derH w` commutes with every translation
`transl g`: `τ_g(δ_w F) = δ_w(τ_g F)`.  Proof: `transl g = aeval (uT g)`; the two chain-rule
identities `∂_{01}∘τ_g = τ_g∘∂_{01}` and `∂_{X_{i1}}∘τ_g = gᵢ · τ_g∘∂_{X_{i1}}` reduce the claim to
the definition of `derH w`, and the remaining products are rearranged by commutativity. -/
lemma derH_transl {N : ℕ} (w g : Fin (N + 1) → ℂ) (F : MR N) :
    transl g (derH w F) = derH w (transl g F) := by
  have hU0 : uT g (0,0) = MvPolynomial.X (0,0) := by simp [uT]
  have hU1 : ∀ i : Fin N, uT g (i.succ, 1) =
      MvPolynomial.C (g i.succ) * MvPolynomial.X (i.succ, 1) := fun i => by simp [uT]
  rw [show transl g = MvPolynomial.aeval (uT g) from rfl]
  have chain01 : MvPolynomial.pderiv (0,1) (MvPolynomial.aeval (uT g) F)
      = MvPolynomial.aeval (uT g) (MvPolynomial.pderiv (0,1) F) := by
    simpa using pderiv_aeval_eq (uT g) (0,1) 1 (uT_pderiv_zero_one g) F
  have chainS : ∀ i : Fin N,
      MvPolynomial.pderiv (i.succ,1) (MvPolynomial.aeval (uT g) F)
        = MvPolynomial.C (g i.succ) * MvPolynomial.aeval (uT g) (MvPolynomial.pderiv (i.succ,1) F) :=
    fun i => pderiv_aeval_eq (uT g) (i.succ,1) (g i.succ) (uT_pderiv_succ g i) F
  simp only [derH, map_add, map_mul, map_sum, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
    MvPolynomial.algebraMap_eq, chain01, chainS, hU0, hU1]
  rw [add_right_inj]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Work.BW
