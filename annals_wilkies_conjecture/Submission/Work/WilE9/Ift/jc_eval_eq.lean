import Mathlib
import Submission.Work.WilE9.Ift.Basic
import Submission.Work.WilE9.Mat.adjugate_mulVec_of_mulVec_eq

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical Topology
namespace Work.WilE9.Ift
open WilkiesDesign WilkiesDesign.E

/-! ## §1  `eaEval` as a ring homomorphism -/

/-- `eaEval c · z` as a ring homomorphism (it is `MvPolynomial.eval` at the point
`Sum.elim z (fun j => exp (ℓ_j z))`). -/
def eaEv {k r : ℕ} (c : EAChain k r) (z : Fin k → ℝ) : EAPoly k r →+* ℝ :=
  MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z))

theorem eaEv_apply {k r : ℕ} (c : EAChain k r) (z : Fin k → ℝ) (Q : EAPoly k r) :
    eaEv c z Q = eaEval c Q z := rfl

/-! ## §2  The derivative of a polynomial function -/

/-- The evaluation of the "delta" polynomial `Pi.single i 1`. -/
theorem eval_piSingleJC {σ : Type*} [DecidableEq σ] (x : σ → ℝ) (i n : σ) :
    MvPolynomial.eval x
        (Pi.single (M := fun _ => MvPolynomial σ ℝ) i (1 : MvPolynomial σ ℝ) n)
      = Pi.single (M := fun _ => ℝ) i (1 : ℝ) n := by
  by_cases h : n = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- The derivative of a multivariate polynomial function: for `p : MvPolynomial σ ℝ` the map
`y ↦ p.eval y` has derivative `∑ i, (pderiv i p).eval x • proj i` at `x`. -/
theorem mvPolyEval_fderiv {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℝ) (x : σ → ℝ) :
    HasFDerivAt (fun y : σ → ℝ => MvPolynomial.eval y p)
      (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) x := by
  classical
  refine MvPolynomial.induction_on (motive := fun q => HasFDerivAt
    (fun y : σ → ℝ => MvPolynomial.eval y q)
    (∑ i, (MvPolynomial.eval x (MvPolynomial.pderiv i q)) •
      (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) x) p ?_ ?_ ?_
  · intro a
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (MvPolynomial.C a)) = fun _ => a := by
      funext y; simp
    rw [hfun]
    have hsum : (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i (MvPolynomial.C a))) •
        (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) = 0 := by
      simp [MvPolynomial.pderiv_C]
    rw [hsum]
    exact hasFDerivAt_const a x
  · intro p q hp hq
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (p + q))
        = (fun y : σ → ℝ => MvPolynomial.eval y p)
          + (fun y : σ → ℝ => MvPolynomial.eval y q) := by
      funext y; simp [MvPolynomial.eval_add]
    rw [hfun]
    refine (hp.add hq).congr_fderiv ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add (MvPolynomial.pderiv i) p q, MvPolynomial.eval_add, add_smul]
  · intro p n hp
    have hfun : (fun y : σ → ℝ => MvPolynomial.eval y (p * MvPolynomial.X n))
        = (fun y : σ → ℝ => MvPolynomial.eval y p) * (fun y : σ → ℝ => y n) := by
      funext y; simp [MvPolynomial.eval_mul, MvPolynomial.eval_X]
    rw [hfun]
    have hn : HasFDerivAt (fun y : σ → ℝ => y n)
        (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ) x := hasFDerivAt_apply n x
    refine (hp.mul hn).congr_fderiv ?_
    have hsplit : (∑ i : σ,
          (MvPolynomial.eval x (MvPolynomial.pderiv i (p * MvPolynomial.X n))) •
            (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
        = (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i p) * x n) •
              (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
          + (∑ i : σ, (MvPolynomial.eval x p * Pi.single (M := fun _ => ℝ) i (1 : ℝ) n) •
              (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MvPolynomial.pderiv_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
        MvPolynomial.eval_mul, MvPolynomial.eval_X, MvPolynomial.pderiv_X, eval_piSingleJC,
        add_smul]
    have hfac : (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i p) * x n) •
          (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
        = x n • (∑ i : σ, (MvPolynomial.eval x (MvPolynomial.pderiv i p)) •
            (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [smul_smul, mul_comm]
    have hdelta : (∑ i : σ,
          (MvPolynomial.eval x p * Pi.single (M := fun _ => ℝ) i (1 : ℝ) n) •
            (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ))
        = MvPolynomial.eval x p • (ContinuousLinearMap.proj n : (σ → ℝ) →L[ℝ] ℝ) := by
      rw [Finset.sum_eq_single n]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero, zero_smul]
      · intro h; exact absurd (Finset.mem_univ n) h
    rw [hsplit, hfac, hdelta, add_comm]

/-! ## §3  The derivative of the "branch" map `x ↦ (x, exp ∘ ℓ x)` -/

theorem branch_fderiv {N r : ℕ} (c : EAChain N r) (v : Fin N → ℝ) :
    HasFDerivAt (fun x : Fin N → ℝ => Sum.elim x (fun j => Real.exp (c.ell j x)))
      (ContinuousLinearMap.pi (fun s : Fin N ⊕ Fin r =>
        Sum.elim (fun i => (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ))
          (fun j => Real.exp (c.ell j v) •
            (∑ i, c.a j i • (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ))) s)) v := by
  rw [hasFDerivAt_pi]
  intro s
  rcases s with i | j
  · simpa using (hasFDerivAt_apply i v :
      HasFDerivAt (fun x : Fin N → ℝ => x i) (ContinuousLinearMap.proj i) v)
  · simp only [Sum.elim_inr]
    have hell : HasFDerivAt (fun x : Fin N → ℝ => c.ell j x)
        (∑ i, c.a j i • (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) v := by
      have h : (fun x : Fin N → ℝ => c.ell j x)
          = fun x => (∑ i, c.a j i •
              (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) x + c.b j := by
        funext x; simp [EAChain.ell]
      rw [h]
      exact (ContinuousLinearMap.hasFDerivAt _).add_const (c.b j)
    exact (Real.hasDerivAt_exp (c.ell j v)).comp_hasFDerivAt v hell

/-! ## §4  The ambient chain rule: `eaD` computes `fderiv` -/

theorem eaEval_eaD_eval {N r : ℕ} (c : EAChain N r) (Q : EAPoly N r) (v : Fin N → ℝ)
    (i : Fin N) :
    MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v))) (eaD c i Q)
      = MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
          (MvPolynomial.pderiv (Sum.inl i) Q)
        + ∑ j, c.a j i * Real.exp (c.ell j v) *
            MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
              (MvPolynomial.pderiv (Sum.inr j) Q) := by
  simp only [eaD, map_add, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Sum.elim_inr]

/-- The symbolic derivative `eaD c i` computes the partial derivative of `eaEval c Q`. -/
theorem eaEval_fderiv {N r : ℕ} (c : EAChain N r) (Q : EAPoly N r) (v : Fin N → ℝ) :
    HasFDerivAt (fun w : Fin N → ℝ => eaEval c Q w)
      (∑ i, (eaEval c (eaD c i Q) v) •
        (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)) v := by
  classical
  have heval := mvPolyEval_fderiv Q (Sum.elim v (fun j => Real.exp (c.ell j v)))
  have hbr := branch_fderiv c v
  have hcomp := heval.comp v hbr
  have hfun : (fun w : Fin N → ℝ => eaEval c Q w)
      = (fun y : Fin N ⊕ Fin r → ℝ => MvPolynomial.eval y Q) ∘
          (fun x : Fin N → ℝ => Sum.elim x (fun j => Real.exp (c.ell j x))) := rfl
  rw [hfun]
  refine hcomp.congr_fderiv ?_
  ext w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.pi_apply, smul_eq_mul]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply, smul_eq_mul, eaEval]
  have hR : (∑ i : Fin N, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
        (eaD c i Q) * w i)
      = ∑ i : Fin N, (MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
              (MvPolynomial.pderiv (Sum.inl i) Q)
          + ∑ j : Fin r, c.a j i * Real.exp (c.ell j v) *
              MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
                (MvPolynomial.pderiv (Sum.inr j) Q)) * w i :=
    Finset.sum_congr rfl fun i _ => by simp only [eaEval_eaD_eval c Q v i]
  rw [hR]
  have hswap : (∑ j : Fin r, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
          (MvPolynomial.pderiv (Sum.inr j) Q) *
        (Real.exp (c.ell j v) * ∑ i : Fin N, c.a j i * w i))
      = ∑ i : Fin N, ∑ j : Fin r,
          MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
            (MvPolynomial.pderiv (Sum.inr j) Q) *
          (Real.exp (c.ell j v) * (c.a j i * w i)) := by
    have h1 : ∀ j : Fin r, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
          (MvPolynomial.pderiv (Sum.inr j) Q) *
        (Real.exp (c.ell j v) * ∑ i : Fin N, c.a j i * w i)
        = ∑ i : Fin N, MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
            (MvPolynomial.pderiv (Sum.inr j) Q) *
          (Real.exp (c.ell j v) * (c.a j i * w i)) := by
      intro j
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_comm]
  rw [hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_mul, Finset.sum_mul]
  exact congrArg
    (fun t => MvPolynomial.eval (Sum.elim v (fun j => Real.exp (c.ell j v)))
      (MvPolynomial.pderiv (Sum.inl i) Q) * w i + t)
    (Finset.sum_congr rfl fun j _ => by ring)

/-! ## §5  `Fin.append` as a linear map -/

/-- `(v, w) ↦ Fin.append v w`, as a continuous linear map. -/
def appCLM (n q : ℕ) : ((Fin n → ℝ) × (Fin q → ℝ)) →L[ℝ] (Fin (n + q) → ℝ) :=
  ContinuousLinearMap.pi fun s : Fin (n + q) =>
    Fin.append
      (fun i : Fin n =>
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin q → ℝ)))
      (fun l : Fin q =>
        (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp
          (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin q → ℝ)))
      s

@[simp] theorem appCLM_apply (n q : ℕ) (v : Fin n → ℝ) (w : Fin q → ℝ) :
    appCLM n q (v, w) = Fin.append v w := by
  ext s
  refine Fin.addCases (fun i => ?_) (fun l => ?_) s <;>
    simp [appCLM, ContinuousLinearMap.pi_apply]

/-! ## §6  The chain rule along the solution graph -/

/-- Chain rule: the derivative of `x' ↦ eaEval c P (Fin.append x' (y x'))` at `x`, split into
the base and the fibre directions. -/
theorem chain_rule {n q r : ℕ} (c : EAChain (n + q) r) (P : EAPoly (n + q) r)
    (y : (Fin n → ℝ) → (Fin q → ℝ)) (x : Fin n → ℝ)
    (hy : HasFDerivAt y (fderiv ℝ y x) x) :
    HasFDerivAt (fun x' : Fin n → ℝ => eaEval c P (Fin.append x' (y x')))
      ((∑ i : Fin n, (eaEval c (eaD c (Fin.castAdd q i) P) (Fin.append x (y x))) •
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l : Fin q, (eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x))) •
            ((ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x)))) x := by
  classical
  -- (i) The derivative of the graph map `x' ↦ Fin.append x' (y x')`, in the ambient coordinates.
  have hA : HasFDerivAt (fun x' : Fin n → ℝ => Fin.append x' (y x'))
      ((appCLM n q).comp
        ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x))) x := by
    refine hasFDerivAt_pi'' (fun s => ?_)
    refine Fin.addCases (motive := fun s => HasFDerivAt
      (fun x' : Fin n → ℝ => Fin.append x' (y x') s)
      ((ContinuousLinearMap.proj s).comp ((appCLM n q).comp
        ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x)))) x)
      (fun i' => ?_) (fun l' => ?_) s
    · have hev : (fun x' : Fin n → ℝ => Fin.append x' (y x') (Fin.castAdd q i')) =ᶠ[𝓝 x]
          (⇑(ContinuousLinearMap.proj i' : (Fin n → ℝ) →L[ℝ] ℝ)) := by
        filter_upwards with u
        rw [Fin.append_left]
        rfl
      refine ((ContinuousLinearMap.hasFDerivAt
        (ContinuousLinearMap.proj i' : (Fin n → ℝ) →L[ℝ] ℝ)).congr_of_eventuallyEq hev).congr_fderiv ?_
      ext u
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.one_apply, appCLM_apply, Fin.append_left]
    · have hcomp : HasFDerivAt ((ContinuousLinearMap.proj l' : (Fin q → ℝ) →L[ℝ] ℝ) ∘ y)
          ((ContinuousLinearMap.proj l' : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x)) x :=
        (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj l')).comp x hy
      have hev : (fun x' : Fin n → ℝ => Fin.append x' (y x') (Fin.natAdd n l')) =ᶠ[𝓝 x]
          ((ContinuousLinearMap.proj l' : (Fin q → ℝ) →L[ℝ] ℝ) ∘ y) := by
        filter_upwards with u
        rw [Fin.append_right]
        rfl
      refine (hcomp.congr_of_eventuallyEq hev).congr_fderiv ?_
      ext u
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.one_apply, appCLM_apply, Fin.append_right]
  -- (ii) The derivative of `eaEval c P` at the ambient point.
  have hL : HasFDerivAt (fun w : Fin (n + q) → ℝ => eaEval c P w)
      (∑ s : Fin (n + q), (eaEval c (eaD c s P) (Fin.append x (y x))) •
        (ContinuousLinearMap.proj s : (Fin (n + q) → ℝ) →L[ℝ] ℝ)) (Fin.append x (y x)) :=
    eaEval_fderiv c P _
  -- The same statement, with the point written as the value of the graph map.
  have hL' : HasFDerivAt (fun w : Fin (n + q) → ℝ => eaEval c P w)
      (∑ s : Fin (n + q), (eaEval c (eaD c s P) (Fin.append x (y x))) •
        (ContinuousLinearMap.proj s : (Fin (n + q) → ℝ) →L[ℝ] ℝ))
      ((fun x' : Fin n → ℝ => Fin.append x' (y x')) x) := hL
  -- (iii) Chain rule.
  have hK : HasFDerivAt ((fun w : Fin (n + q) → ℝ => eaEval c P w) ∘
      (fun x' : Fin n → ℝ => Fin.append x' (y x')))
      (((∑ s : Fin (n + q), (eaEval c (eaD c s P) (Fin.append x (y x))) •
          (ContinuousLinearMap.proj s : (Fin (n + q) → ℝ) →L[ℝ] ℝ)).comp
        ((appCLM n q).comp
          ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x))))) x :=
    hL'.comp x hA
  -- (iv) Identify the ambient sum with the base and fibre sums.
  have hCLM : ((∑ s : Fin (n + q), (eaEval c (eaD c s P) (Fin.append x (y x))) •
        (ContinuousLinearMap.proj s : (Fin (n + q) → ℝ) →L[ℝ] ℝ)).comp
      ((appCLM n q).comp
        ((1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)).prod (fderiv ℝ y x))))
      = (∑ i : Fin n, (eaEval c (eaD c (Fin.castAdd q i) P) (Fin.append x (y x))) •
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l : Fin q, (eaEval c (eaD c (Fin.natAdd n l) P) (Fin.append x (y x))) •
            ((ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x))) := by
    ext u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, add_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.one_apply, appCLM_apply]
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun i' _ => ?_)
      rw [Fin.append_left]
    · refine Finset.sum_congr rfl (fun l' _ => ?_)
      rw [Fin.append_right]
  rw [hCLM] at hK
  exact hK

/-! ## §7  First-order implicit differentiation -/

/-- **First-order implicit differentiation, in `EAChain` form.** If `y` is differentiable at
`x₀` and solves `F(x,y) = 0` with invertible fibre Jacobian near `x₀`, then the *cleared*
first derivative `jc c F l i` evaluates to `Q · ∂y_l/∂x_i` along the solution.  This is the
base case of the recursion `iftP`. -/
theorem jc_eval_eq {n q r : ℕ} (c : WilkiesDesign.E.EAChain (n + q) r)
    (F : Fin q → WilkiesDesign.E.EAPoly (n + q) r) (y : (Fin n → ℝ) → (Fin q → ℝ))
    (x₀ : Fin n → ℝ) (i : Fin n) (l : Fin q)
    (hy : HasFDerivAt y (fderiv ℝ y x₀) x₀) (hs : Work.WilE9.IsSoln c F y x₀) :
    WilkiesDesign.E.eaEval c (Work.WilE9.jc c F l i) (Fin.append x₀ (y x₀)) =
      fderiv ℝ y x₀ (Pi.single i 1) l *
        WilkiesDesign.E.eaEval c (Work.WilE9.jQ c F) (Fin.append x₀ (y x₀)) := by
  classical
  -- ### Step 1: the linear system `A v = w` coming from `F(x, y x) = 0`
  have hsys : ∀ j : Fin q,
      (∑ l' : Fin q, eaEval c (eaD c (Fin.natAdd n l') (F j)) (Fin.append x₀ (y x₀))
          * (fderiv ℝ y x₀ (Pi.single i 1)) l')
        = - eaEval c (eaD c (Fin.castAdd q i) (F j)) (Fin.append x₀ (y x₀)) := by
    intro j
    have hd := chain_rule c (F j) y x₀ hy
    have hev : (fun x : Fin n → ℝ => eaEval c (F j) (Fin.append x (y x))) =ᶠ[𝓝 x₀]
        fun _ => (0 : ℝ) := hs.1.mono (fun x hx => hx j)
    have hzero : fderiv ℝ (fun x : Fin n → ℝ => eaEval c (F j) (Fin.append x (y x))) x₀ = 0 := by
      rw [Filter.EventuallyEq.fderiv_eq hev]
      exact (hasFDerivAt_const (0 : ℝ) x₀).fderiv
    have hL0 : ((∑ i' : Fin n,
          (eaEval c (eaD c (Fin.castAdd q i') (F j)) (Fin.append x₀ (y x₀))) •
            (ContinuousLinearMap.proj i' : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l' : Fin q,
          (eaEval c (eaD c (Fin.natAdd n l') (F j)) (Fin.append x₀ (y x₀))) •
            ((ContinuousLinearMap.proj l' : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x₀)))) = 0 := by
      rw [← hd.fderiv, hzero]
    have hval : ((∑ i' : Fin n,
          (eaEval c (eaD c (Fin.castAdd q i') (F j)) (Fin.append x₀ (y x₀))) •
            (ContinuousLinearMap.proj i' : (Fin n → ℝ) →L[ℝ] ℝ))
        + (∑ l' : Fin q,
          (eaEval c (eaD c (Fin.natAdd n l') (F j)) (Fin.append x₀ (y x₀))) •
            ((ContinuousLinearMap.proj l' : (Fin q → ℝ) →L[ℝ] ℝ).comp (fderiv ℝ y x₀))))
        (Pi.single i 1) = 0 := by
      rw [hL0, zero_apply]
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.proj_apply] at hval
    have h1 : (∑ i' : Fin n,
        (eaEval c (eaD c (Fin.castAdd q i') (F j)) (Fin.append x₀ (y x₀))) *
          (Pi.single i 1 : Fin n → ℝ) i')
        = eaEval c (eaD c (Fin.castAdd q i) (F j)) (Fin.append x₀ (y x₀)) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h1] at hval
    linarith
  -- ### Step 2: Cramer's rule
  set A : Matrix (Fin q) (Fin q) ℝ :=
    (jm c F).map (fun P => eaEval c P (Fin.append x₀ (y x₀))) with hA
  have hAentry : ∀ j l' : Fin q,
      A j l' = eaEval c (eaD c (Fin.natAdd n l') (F j)) (Fin.append x₀ (y x₀)) := by
    intro j l'
    rw [hA]
    simp only [Matrix.map_apply, jm, Matrix.of_apply]
  have hmulvec : A.mulVec (fderiv ℝ y x₀ (Pi.single i 1))
      = fun j => - eaEval c (jb c F j i) (Fin.append x₀ (y x₀)) := by
    funext j
    show (∑ l' : Fin q, A j l' * (fderiv ℝ y x₀ (Pi.single i 1)) l')
        = - eaEval c (jb c F j i) (Fin.append x₀ (y x₀))
    have h1 : (∑ l' : Fin q, A j l' * (fderiv ℝ y x₀ (Pi.single i 1)) l')
        = ∑ l' : Fin q, eaEval c (eaD c (Fin.natAdd n l') (F j)) (Fin.append x₀ (y x₀))
            * (fderiv ℝ y x₀ (Pi.single i 1)) l' :=
      Finset.sum_congr rfl (fun l' _ => by rw [hAentry j l'])
    rw [h1, hsys j]
    rfl
  have hcr := Mat.adjugate_mulVec_of_mulVec_eq A (fderiv ℝ y x₀ (Pi.single i 1))
    (fun j => - eaEval c (jb c F j i) (Fin.append x₀ (y x₀))) hmulvec
  have hcrl : (∑ j : Fin q, A.adjugate l j * (- eaEval c (jb c F j i) (Fin.append x₀ (y x₀))))
      = A.det * (fderiv ℝ y x₀ (Pi.single i 1)) l := by
    have hthis := congrFun hcr l
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hthis
    exact hthis
  -- ### Step 3: the determinant and the adjugate commute with evaluation
  have hdet : A.det = eaEval c (jQ c F) (Fin.append x₀ (y x₀)) := by
    have h := RingHom.map_det (eaEv c (Fin.append x₀ (y x₀))) (jm c F)
    rw [show A = (eaEv c (Fin.append x₀ (y x₀))).mapMatrix (jm c F) from rfl, ← h]
    rfl
  have hadj : ∀ j : Fin q, eaEv c (Fin.append x₀ (y x₀)) ((jm c F).adjugate l j)
      = A.adjugate l j := by
    intro j
    have h := RingHom.map_adjugate (eaEv c (Fin.append x₀ (y x₀))) (jm c F)
    have h1 := congrFun (congrFun h l) j
    rw [RingHom.mapMatrix_apply] at h1
    rw [show A = (eaEv c (Fin.append x₀ (y x₀))).mapMatrix (jm c F) from rfl, ← h1]
    rw [Matrix.map_apply]
  -- ### Step 4: assembly
  have hLH : eaEval c (jc c F l i) (Fin.append x₀ (y x₀))
      = ∑ j : Fin q, A.adjugate l j * (- eaEval c (jb c F j i) (Fin.append x₀ (y x₀))) := by
    change eaEv c (Fin.append x₀ (y x₀)) (jc c F l i)
      = ∑ j : Fin q, A.adjugate l j * (- eaEv c (Fin.append x₀ (y x₀)) (jb c F j i))
    simp only [jc, map_neg, map_sum, map_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hadj j, mul_neg]
  rw [hLH, hcrl, hdet, mul_comm]

end Work.WilE9.Ift
