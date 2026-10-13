/-
  annals_wilkies_conjecture, AREA E3, `Realify`: the derivative of `S.ev`.

  `S.ev Q x = MvPolynomial.eval (Sum.elim x (fun j => S.psi j x)) Q` is the evaluation of the
  EA polynomial `Q` along the separable chain `S`.  The chain function of the `j`-th atom is
  `ψ_j = φ_j ∘ ℓ_j` with `ℓ_j x = ∑ i, a_{j i} x_i + b_j` affine, and `φ_j` satisfies its
  differential relation `φ_j' = R_j ∘ φ_j` on the domain `S.dom j`, which by hypothesis contains
  `ℓ_j x`.  Hence `∂ψ_j/∂x_i = a_{j i} · R_j(ψ_j)` at `x`, and the chain rule gives

      `d (S.ev Q) x = ∑ i, S.ev (S.d i Q) x · dx_i`,

  i.e. the symbolic operator `S.d` of `Sep.lean` computes the Fréchet derivative.  This is the
  local-chain analogue of `Work.WilE3.API.hasFDerivAt_eaEval`, and it is the vocabulary lemma
  that licenses using the symbolic Jacobian `S.ev (S.d j (f i))` for the realified systems of
  `Realify/Defs.lean` (where `φ = Real.tan` is only *locally* a solution of `φ' = 1 + φ²`).

  Strategy: `S.ev Q` is the composition of the polynomial function `y ↦ MvPolynomial.eval y Q`
  with the "branch" map `β x = Sum.elim x (fun j => ψ_j x)`.  The general multivariate chain rule
  `Work.WilE9.EaD.mvPoly_eval_hasFDerivAt` gives the derivative of the first factor, and
  `HasDerivAt.comp_hasFDerivAt` that of each coordinate of `β`; composing and reindexing the two
  resulting sums identifies the derivative with `grad S Q x`.
-/
import Mathlib
import Submission.Work.WilE3.Realify.Defs
import Submission.Work.WilE9.EaD.mvPoly_eval_hasFDerivAt

namespace Work.WilE3.Realify

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

variable {n r : ℕ}

/-! ## §1. The affine forms `ℓ_j` and the chain functions `ψ_j` -/

/-- The affine form `ℓ_j x = ∑ i, a_{j i} x_i + b_j` of the `j`-th atom of a separable chain. -/
private def sepEll (S : SepChainLocal n r) (j : Fin r) (x : Fin n → ℝ) : ℝ :=
  ∑ i, S.a j i * x i + S.b j

/-- The linear part of `ℓ_j`, as a continuous linear map. -/
private def sepEllLin (S : SepChainLocal n r) (j : Fin r) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, S.a j i • ContinuousLinearMap.proj i

private lemma sepEllLin_apply (S : SepChainLocal n r) (j : Fin r) (v : Fin n → ℝ) :
    sepEllLin S j v = ∑ i, S.a j i * v i := by
  simp [sepEllLin]

/-- The derivative of the affine form `ℓ_j`. -/
private lemma sepEll_hasFDerivAt (S : SepChainLocal n r) (j : Fin r) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => sepEll S j y) (sepEllLin S j) x := by
  have h : (fun y : Fin n → ℝ => sepEll S j y) = fun y => sepEllLin S j y + S.b j := by
    funext y; rw [sepEllLin_apply]; simp [sepEll]
  rw [h]
  exact (ContinuousLinearMap.hasFDerivAt (sepEllLin S j) (x := x)).add_const (S.b j)

/-- The chain function `ψ_j = φ_j ∘ ℓ_j` is differentiable at `x` as soon as `ℓ_j x ∈ S.dom j`,
with derivative `R_j(ψ_j x) · dℓ_j`.  This is the only place where the local differential
relation `S.hderiv` is used. -/
private lemma sepPsi_hasFDerivAt (S : SepChainLocal n r) (j : Fin r) (x : Fin n → ℝ)
    (hx : sepEll S j x ∈ S.dom j) :
    HasFDerivAt (fun y => S.psi j y) (((S.R j).eval (fun _ => S.psi j x)) • sepEllLin S j) x := by
  have hfun : (fun y : Fin n → ℝ => S.psi j y) = S.phi j ∘ sepEll S j := by
    funext y; rfl
  rw [hfun]
  exact HasDerivAt.comp_hasFDerivAt x (S.hderiv j (sepEll S j x) hx) (sepEll_hasFDerivAt S j x)

/-! ## §2. The branch map `β x = (x, ψ x)` -/

/-- The branch map `x ↦ Sum.elim x (fun j => ψ_j x)` into `(Fin n ⊕ Fin r) → ℝ`, whose
coordinates are the variables and the chain functions.  Its derivative has the coordinate
projections in the `inl` slots and `R_j(ψ_j x) · dℓ_j` in the `inr` slots. -/
private lemma sepBranch_hasFDerivAt (S : SepChainLocal n r) (x : Fin n → ℝ)
    (hx : ∀ j, sepEll S j x ∈ S.dom j) :
    HasFDerivAt (fun y : Fin n → ℝ => Sum.elim y (fun j => S.psi j y))
      (ContinuousLinearMap.pi (Sum.elim
        (fun i => (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
        (fun j => ((S.R j).eval (fun _ => S.psi j x)) • sepEllLin S j))) x := by
  rw [hasFDerivAt_pi]
  intro s
  rcases s with i | j
  · simpa using hasFDerivAt_apply i x
  · simpa using sepPsi_hasFDerivAt S j x (hx j)

/-! ## §3. Evaluating the symbolic derivative `S.d i Q` -/

/-- `S.ev (S.d i Q) x`, expanded: the `inl i` partial derivative of `Q`, plus for every atom `j`
the factor `a_{j i} R_j(ψ_j)` times the partial derivative in that atom. -/
private lemma sepEv_d (S : SepChainLocal n r) (Q : EAPoly n r) (x : Fin n → ℝ) (i : Fin n) :
    S.ev (S.d i Q) x
      = MvPolynomial.eval (Sum.elim x (fun j => S.psi j x)) (MvPolynomial.pderiv (Sum.inl i) Q)
        + ∑ j : Fin r, S.a j i * (S.R j).eval (fun _ => S.psi j x) *
            MvPolynomial.eval (Sum.elim x (fun j => S.psi j x)) (MvPolynomial.pderiv (Sum.inr j) Q) := by
  simp only [SepChainLocal.d, SepChainLocal.ev, map_add, map_sum, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, SepChainLocal.Rpoly, MvPolynomial.eval_rename]
  have hsum : (∑ x_1 : Fin r,
        S.a x_1 i * (MvPolynomial.eval ((Sum.elim x fun j => S.psi j x) ∘ fun _ => Sum.inr x_1)) (S.R x_1) *
          (MvPolynomial.eval (Sum.elim x fun j => S.psi j x)) ((MvPolynomial.pderiv (Sum.inr x_1)) Q))
      = ∑ j : Fin r, S.a j i * (MvPolynomial.eval (fun _ => S.psi j x)) (S.R j) *
          (MvPolynomial.eval (Sum.elim x fun j => S.psi j x)) ((MvPolynomial.pderiv (Sum.inr j)) Q) := by
    apply Finset.sum_congr rfl
    intro j _
    have hc : ((Sum.elim x fun j => S.psi j x) ∘ (fun _ : Fin 1 => Sum.inr j)) =
        (fun _ => S.psi j x) := by
      funext t; simp [Function.comp_apply]
    rw [hc]
  rw [hsum]

/-! ## §4. A double-sum reindexing -/

/-- Interchange the `j`- and `i`-sums in `∑ j, B_j (c_j ∑ i, a_{j i} v_i)`. -/
private lemma sepSum_reindex {n r : ℕ} (a : Fin r → Fin n → ℝ) (c B : Fin r → ℝ)
    (v : Fin n → ℝ) :
    (∑ j : Fin r, B j * (c j * ∑ i, a j i * v i))
      = ∑ i : Fin n, (∑ j : Fin r, a j i * c j * B j) * v i := by
  rw [show (∑ j : Fin r, B j * (c j * ∑ i, a j i * v i))
      = ∑ j : Fin r, ∑ i : Fin n, (a j i * c j * B j) * v i from ?_]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-! ## §5. Identifying the chain-rule derivative with `grad` -/

/-- The derivative supplied by the chain rule — the derivative of the polynomial function
composed with the derivative of the branch map — is `grad S Q x`. -/
private lemma sepDeriv_eq (S : SepChainLocal n r) (Q : EAPoly n r) (x : Fin n → ℝ) :
    ContinuousLinearMap.comp
      (∑ s : Fin n ⊕ Fin r,
        (MvPolynomial.eval (Sum.elim x (fun j => S.psi j x)) (MvPolynomial.pderiv s Q)) •
        (ContinuousLinearMap.proj s : ((Fin n ⊕ Fin r) → ℝ) →L[ℝ] ℝ))
      (ContinuousLinearMap.pi (Sum.elim
        (fun i => (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
        (fun j => ((S.R j).eval (fun _ => S.psi j x)) • sepEllLin S j)))
    = grad S Q x := by
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, grad_apply]
  rw [Fintype.sum_sum_type]
  simp only [ContinuousLinearMap.pi_apply, Sum.elim_inl, Sum.elim_inr, sepEllLin_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hR : (∑ a : Fin n, S.ev (S.d a Q) x * v a)
      = ∑ a : Fin n,
          ((MvPolynomial.eval (Sum.elim x fun j => S.psi j x))
              ((MvPolynomial.pderiv (Sum.inl a)) Q)
            + ∑ j : Fin r, S.a j a * (MvPolynomial.eval fun _ => S.psi j x) (S.R j) *
                (MvPolynomial.eval (Sum.elim x fun j => S.psi j x))
                  ((MvPolynomial.pderiv (Sum.inr j)) Q)) * v a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [sepEv_d]
  rw [hR]
  have hR2 : (∑ a : Fin n,
          ((MvPolynomial.eval (Sum.elim x fun j => S.psi j x))
              ((MvPolynomial.pderiv (Sum.inl a)) Q)
            + ∑ j : Fin r, S.a j a * (MvPolynomial.eval fun _ => S.psi j x) (S.R j) *
                (MvPolynomial.eval (Sum.elim x fun j => S.psi j x))
                  ((MvPolynomial.pderiv (Sum.inr j)) Q)) * v a)
      = (∑ a : Fin n, (MvPolynomial.eval (Sum.elim x fun j => S.psi j x))
            ((MvPolynomial.pderiv (Sum.inl a)) Q) * v a)
        + ∑ a : Fin n, (∑ j : Fin r, S.a j a *
              (MvPolynomial.eval fun _ => S.psi j x) (S.R j) *
              (MvPolynomial.eval (Sum.elim x fun j => S.psi j x))
                ((MvPolynomial.pderiv (Sum.inr j)) Q)) * v a := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [add_mul]
  rw [hR2]
  congr 1
  exact sepSum_reindex (fun j i => S.a j i)
    (fun j => (MvPolynomial.eval (fun _ => S.psi j x)) (S.R j))
    (fun j => (MvPolynomial.eval (Sum.elim x fun j => S.psi j x))
      ((MvPolynomial.pderiv (Sum.inr j)) Q)) v

/-- **The chain rule along a local separable chain.**  Away from the poles of the chain functions
(`hx`), the symbolic Jacobian of `Sep.lean` computes the Fréchet derivative of the evaluation map
`S.ev Q`. -/
theorem SepChainLocal_fderiv_ev {n r : ℕ} (S : Work.WilE3.SepChainLocal n r)
    (Q : WilkiesDesign.E.EAPoly n r) (x : Fin n → ℝ)
    (hx : ∀ j, (∑ i, S.a j i * x i + S.b j) ∈ S.dom j) :
    HasFDerivAt (S.ev Q) (Work.WilE3.Realify.grad S Q x) x := by
  have hx' : ∀ j, sepEll S j x ∈ S.dom j := fun j => hx j
  have hβ := sepBranch_hasFDerivAt S x hx'
  have hev := Work.WilE9.EaD.mvPoly_eval_hasFDerivAt Q (Sum.elim x (fun j => S.psi j x))
  have hcomp := hev.comp x hβ
  have hfun : S.ev Q = (fun y : Fin n ⊕ Fin r → ℝ => MvPolynomial.eval y Q) ∘
      (fun y : Fin n → ℝ => Sum.elim y (fun j => S.psi j y)) := by
    funext y; rfl
  rw [hfun]
  exact hcomp.congr_fderiv (sepDeriv_eq S Q x)

end

end Work.WilE3.Realify
