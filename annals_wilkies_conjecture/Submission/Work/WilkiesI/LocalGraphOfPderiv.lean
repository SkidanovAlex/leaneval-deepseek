import Mathlib
import Submission.Work.Wilkies.Defs

noncomputable section
open Classical
open scoped Topology

namespace Work.WilkiesI

/-!
# The zero locus of a polynomial with a non-vanishing last partial derivative is a graph

This file proves `Work.WilkiesI.LocalGraphOfPderiv`: if `P` is a real polynomial in `m + 1`
variables, `p` is a point with `P p = 0`, and the last partial derivative of `P` does not vanish at
`p`, then locally around `p` the zero set of `P` is the graph of a continuous function of the first
`m` coordinates.

The proof is an application of the implicit function theorem to the polynomial function
`f z = P (Fin.snoc z.1 z.2)`, combined with an explicit computation of the derivative of `eval`
along a coordinate update (which identifies the partial derivative in the last direction with
`pderiv (Fin.last m) P`).
-/

/-! ## Derivative of `MvPolynomial.eval` along a coordinate update -/

/-- The directional derivative of `x ↦ P x` in the direction of the `i`-th coordinate equals
`eval x (pderiv i P)`. -/
theorem hasDerivAt_eval_update {σ : Type*} [DecidableEq σ]
    (P : MvPolynomial σ ℝ) (x : σ → ℝ) (i : σ) :
    HasDerivAt (fun y : ℝ => MvPolynomial.eval (Function.update x i y) P)
      (MvPolynomial.eval x (MvPolynomial.pderiv i P)) (x i) := by
  refine MvPolynomial.induction_on
    (motive := fun P => HasDerivAt (fun y : ℝ => MvPolynomial.eval (Function.update x i y) P)
      (MvPolynomial.eval x (MvPolynomial.pderiv i P)) (x i)) P ?_ ?_ ?_
  · intro a
    have h : (fun y : ℝ => MvPolynomial.eval (Function.update x i y) (MvPolynomial.C a))
        = (fun _ : ℝ => a) := by
      funext y; rw [MvPolynomial.eval_C]
    rw [h, MvPolynomial.pderiv_C]
    simpa using hasDerivAt_const (x i) a
  · intro p q hp hq
    have h : (fun y : ℝ => MvPolynomial.eval (Function.update x i y) (p + q))
        = (fun y : ℝ => MvPolynomial.eval (Function.update x i y) p)
          + (fun y : ℝ => MvPolynomial.eval (Function.update x i y) q) := by
      funext y; simp [MvPolynomial.eval_add]
    rw [h]
    have h2 : MvPolynomial.eval x (MvPolynomial.pderiv i (p + q))
        = MvPolynomial.eval x (MvPolynomial.pderiv i p)
          + MvPolynomial.eval x (MvPolynomial.pderiv i q) := by
      rw [Derivation.map_add, MvPolynomial.eval_add]
    rw [h2]
    exact hp.add hq
  · intro p n hp
    by_cases hn : n = i
    · subst n
      have hg : HasDerivAt (fun y : ℝ => MvPolynomial.eval (Function.update x i y)
          (MvPolynomial.X i)) 1 (x i) := by
        have h' : (fun y : ℝ => MvPolynomial.eval (Function.update x i y) (MvPolynomial.X i))
            = id := by
          funext y; simp [MvPolynomial.eval_X, Function.update_self]
        rw [h']; exact hasDerivAt_id (x i)
      have hmul := hp.mul hg
      convert hmul using 1
      · funext y; simp [MvPolynomial.eval_mul]
      · simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self, MvPolynomial.eval_add,
          MvPolynomial.eval_mul, MvPolynomial.eval_X, Function.update_eq_self] <;> ring
    · have hg : HasDerivAt (fun y : ℝ => MvPolynomial.eval (Function.update x i y)
          (MvPolynomial.X n)) 0 (x i) := by
        have h' : (fun y : ℝ => MvPolynomial.eval (Function.update x i y) (MvPolynomial.X n))
            = fun _ : ℝ => x n := by
          funext y; rw [MvPolynomial.eval_X, Function.update_of_ne hn]
        rw [h']; exact hasDerivAt_const (x i) (x n)
      have hmul := hp.mul hg
      convert hmul using 1
      · funext y; simp [MvPolynomial.eval_mul]
      · simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne hn, MvPolynomial.eval_add,
          MvPolynomial.eval_mul, MvPolynomial.eval_X, Function.update_eq_self,
          Function.update_of_ne hn] <;> ring

/-- The same statement written with `Fin.snoc`: the derivative in the last coordinate is
`eval (Fin.snoc t y) (pderiv (Fin.last m) P)`. -/
theorem hasDerivAt_eval_snoc {m : ℕ} (P : MvPolynomial (Fin (m+1)) ℝ) (t : Fin m → ℝ)
    (y : ℝ) :
    HasDerivAt (fun y' : ℝ => MvPolynomial.eval (Fin.snoc (α := fun _ => ℝ) t y') P)
      (MvPolynomial.eval (Fin.snoc (α := fun _ => ℝ) t y)
        (MvPolynomial.pderiv (Fin.last m) P)) y := by
  have h := hasDerivAt_eval_update P (Fin.snoc (α := fun _ => ℝ) t y) (Fin.last m)
  have hfun : (fun y' : ℝ => MvPolynomial.eval
        (Function.update (Fin.snoc (α := fun _ => ℝ) t y) (Fin.last m) y') P)
      = (fun y' : ℝ => MvPolynomial.eval (Fin.snoc (α := fun _ => ℝ) t y') P) := by
    funext y'; rw [Fin.update_snoc_last]
  rw [hfun, Fin.snoc_last] at h
  exact h

/-! ## The local graph theorem -/

theorem LocalGraphOfPderiv {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) (p : Fin (m + 1) → ℝ) (hp : (MvPolynomial.eval p) P = 0) (hgrad : (MvPolynomial.eval p) (MvPolynomial.pderiv (Fin.last m) P) ≠ 0) : ∃ (U : Set (Fin m → ℝ)) (g : (Fin m → ℝ) → ℝ) (δ : ℝ), 0 < δ ∧ IsOpen U ∧ (∀ t : Fin m → ℝ, (∀ i, |t i - (Fin.init p) i| < δ) → t ∈ U) ∧ ContinuousOn g U ∧ g (Fin.init p) = p (Fin.last m) ∧ {x : Fin (m + 1) → ℝ | (MvPolynomial.eval x) P = 0 ∧ ∀ i, |x i - p i| < δ} = {x : Fin (m + 1) → ℝ | Fin.init x ∈ U ∧ x (Fin.last m) = g (Fin.init x) ∧ ∀ i, |x i - p i| < δ} := by
  let f : ((Fin m → ℝ) × ℝ) → ℝ := fun z =>
    MvPolynomial.eval (Fin.snoc (α := fun _ => ℝ) z.1 z.2) P
  let u : (Fin m → ℝ) × ℝ := (Fin.init p, p (Fin.last m))
  have hana : AnalyticAt ℝ f u := by
    show AnalyticAt ℝ (fun z : (Fin m → ℝ) × ℝ =>
      MvPolynomial.eval (Fin.snoc (α := fun _ => ℝ) z.1 z.2) P) (Fin.init p, p (Fin.last m))
    have hcoord : ∀ i : Fin (m+1), AnalyticAt ℝ
        (fun z : (Fin m → ℝ) × ℝ => Fin.snoc (α := fun _ => ℝ) z.1 z.2 i)
        (Fin.init p, p (Fin.last m)) := by
      intro i
      cases i using Fin.lastCases with
      | last => simpa [Fin.snoc_last] using (ContinuousLinearMap.analyticAt
          (ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ) (Fin.init p, p (Fin.last m)))
      | cast j =>
          have hfun : (fun z : (Fin m → ℝ) × ℝ =>
              Fin.snoc (α := fun _ => ℝ) z.1 z.2 (Fin.castSucc j)) = (fun z => z.1 j) := by
            funext z; rw [Fin.snoc_castSucc]
          rw [hfun]
          have h2 := ContinuousLinearMap.analyticAt
            ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ))
            (Fin.init p, p (Fin.last m))
          convert h2 using 1
          ext z
          simp [ContinuousLinearMap.proj_apply]
    have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℝ) (A := ℝ) (B := ℝ) hcoord P
    simpa [MvPolynomial.aeval_eq_eval] using h
  have hstrict : HasStrictFDerivAt f (fderiv ℝ f u) u := hana.hasStrictFDerivAt
  have hderiv : HasDerivAt (fun y : ℝ => f (u.1, y))
      ((MvPolynomial.eval p) (MvPolynomial.pderiv (Fin.last m) P)) u.2 := by
    have h := hasDerivAt_eval_snoc P (Fin.init p) (p (Fin.last m))
    simpa [f, u, Fin.snoc_init_self] using h
  have hfac : HasFDerivAt (fun y : ℝ => f (u.1, y))
      (ContinuousLinearMap.toSpanSingleton ℝ
        ((MvPolynomial.eval p) (MvPolynomial.pderiv (Fin.last m) P))) u.2 :=
    hasDerivAt_iff_hasFDerivAt.mp hderiv
  have hinner : HasFDerivAt (fun y : ℝ => (u.1, y))
      (ContinuousLinearMap.inr ℝ (Fin m → ℝ) ℝ) u.2 := by
    have h0 : HasFDerivAt (fun y : ℝ => (u.1, y))
        ((0 : ℝ →L[ℝ] (Fin m → ℝ)).prod (ContinuousLinearMap.id ℝ ℝ)) u.2 :=
      (hasFDerivAt_const (u.1) u.2).prodMk (hasFDerivAt_id u.2)
    have heq : ((0 : ℝ →L[ℝ] (Fin m → ℝ)).prod (ContinuousLinearMap.id ℝ ℝ))
        = ContinuousLinearMap.inr ℝ (Fin m → ℝ) ℝ := by
      ext y <;> simp [ContinuousLinearMap.prod_apply]
    rwa [heq] at h0
  have hcomp := hstrict.hasFDerivAt.comp u.2 hinner
  have hcomp' : HasFDerivAt (fun y : ℝ => f (u.1, y))
      ((fderiv ℝ f u) ∘L (ContinuousLinearMap.inr ℝ (Fin m → ℝ) ℝ)) u.2 := by
    convert hcomp using 1
    funext y; rfl
  have huniq : (fderiv ℝ f u) ∘L (ContinuousLinearMap.inr ℝ (Fin m → ℝ) ℝ)
      = ContinuousLinearMap.toSpanSingleton ℝ
          ((MvPolynomial.eval p) (MvPolynomial.pderiv (Fin.last m) P)) :=
    hcomp'.unique hfac
  have hif : ((fderiv ℝ f u) ∘L (ContinuousLinearMap.inr ℝ (Fin m → ℝ) ℝ)).IsInvertible := by
    rw [huniq]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (f := ContinuousLinearMap.toSpanSingleton ℝ
        ((MvPolynomial.eval p) (MvPolynomial.pderiv (Fin.last m) P)))
      (g := ContinuousLinearMap.toSpanSingleton ℝ
        (((MvPolynomial.eval p) (MvPolynomial.pderiv (Fin.last m) P))⁻¹)) ?_ ?_
    · ext y
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      rw [mul_assoc, inv_mul_cancel₀ hgrad, mul_one]
    · ext y
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
      rw [mul_assoc, mul_inv_cancel₀ hgrad, mul_one]
  let ψ : (Fin m → ℝ) → ℝ := hstrict.implicitFunctionOfProdDomain hif
  let φ := hstrict.implicitFunctionDataOfProdDomain hif
  let Φ : OpenPartialHomeomorph ((Fin m → ℝ) × ℝ) (ℝ × (Fin m → ℝ)) :=
    φ.toOpenPartialHomeomorph
  have hψ_fun : ∀ x : Fin m → ℝ, ψ x = (Φ.symm (f u, x)).2 := by
    intro x
    simp only [ψ, Φ, φ, HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
      ImplicitFunctionData.implicitFunction_apply]
  have hψ_at : ψ u.1 = u.2 := by
    have h := (hstrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain hif).self_of_nhds
    exact h.mp rfl
  have hUopen : IsOpen {x : Fin m → ℝ | (f u, x) ∈ Φ.target} :=
    IsOpen.preimage (continuous_const.prodMk continuous_id) Φ.open_target
  have hcont : ContinuousOn ψ {x : Fin m → ℝ | (f u, x) ∈ Φ.target} := by
    have h1 : ContinuousOn (fun x : Fin m → ℝ => Φ.symm (f u, x))
        {x : Fin m → ℝ | (f u, x) ∈ Φ.target} :=
      Φ.continuousOn_symm.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun x hx => hx)
    have h2 : ContinuousOn (fun x : Fin m → ℝ => (Φ.symm (f u, x)).2)
        {x : Fin m → ℝ | (f u, x) ∈ Φ.target} :=
      continuous_snd.continuousOn.comp h1 (fun x _ => Set.mem_univ _)
    rw [show ψ = (fun x : Fin m → ℝ => (Φ.symm (f u, x)).2) from funext (fun x => hψ_fun x)]
    exact h2
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    Metric.eventually_nhds_iff.mp (hstrict.eventually_apply_eq_iff_implicitFunctionOfProdDomain hif)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    Metric.eventually_nhds_iff.mp (hstrict.eventually_apply_implicitFunctionOfProdDomain hif)
  have hmem : u.1 ∈ {x : Fin m → ℝ | (f u, x) ∈ Φ.target} := by
    have h := ImplicitFunctionData.map_pt_mem_toOpenPartialHomeomorph_target φ
    simpa [Φ, φ, u] using h
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hmem)
  let δ : ℝ := min (min δ₁ δ₂) ε
  have hδpos : 0 < δ := by
    simp only [δ]
    exact lt_min (lt_min hδ₁pos hδ₂pos) hεpos
  have hfu : f u = 0 := by
    simp only [f, u]
    rw [Fin.snoc_init_self, hp]
  refine ⟨{x : Fin m → ℝ | (f u, x) ∈ Φ.target}, ψ, δ, hδpos, hUopen, ?_, hcont, ?_, ?_⟩
  · intro t ht
    have hd : dist t (Fin.init p) < δ := by
      rw [dist_pi_lt_iff hδpos]
      intro i
      simpa [Real.dist_eq] using ht i
    have hd' : dist t (Fin.init p) < ε :=
      lt_of_lt_of_le hd (by simp only [δ]; exact min_le_right _ _)
    exact hε (Metric.mem_ball.mpr (by simpa [u] using hd'))
  · simpa [u] using hψ_at
  · ext x
    constructor
    · intro hx
      obtain ⟨hx0, hxc⟩ := hx
      have hinitd : dist (Fin.init x) (Fin.init p) < δ := by
        rw [dist_pi_lt_iff hδpos]
        intro i
        have := hxc (Fin.castSucc i)
        simpa [Real.dist_eq, Fin.init] using this
      have hlastd : dist (x (Fin.last m)) (p (Fin.last m)) < δ := by
        have := hxc (Fin.last m)
        simpa [Real.dist_eq] using this
      have hvd : dist (Fin.init x, x (Fin.last m)) u < δ := by
        show dist (Fin.init x, x (Fin.last m)) (Fin.init p, p (Fin.last m)) < δ
        rw [Prod.dist_eq]
        exact max_lt hinitd hlastd
      have hinU : Fin.init x ∈ {y : Fin m → ℝ | (f u, y) ∈ Φ.target} := by
        refine hε (Metric.mem_ball.mpr ?_)
        exact lt_of_lt_of_le hinitd (by simp only [δ]; exact min_le_right _ _)
      have hfx : f (Fin.init x, x (Fin.last m)) = (MvPolynomial.eval x) P := by
        simp only [f]
        rw [Fin.snoc_init_self]
      have hle₁ : δ ≤ δ₁ := by simp only [δ]; exact le_trans (min_le_left _ _) (min_le_left _ _)
      have hiff := hδ₁ (lt_of_lt_of_le hvd hle₁)
      have hval : ψ (Fin.init x) = x (Fin.last m) := hiff.mp (by rw [hfx, hx0, hfu])
      exact ⟨hinU, hval.symm, hxc⟩
    · intro hx
      obtain ⟨_hinU, hval, hxc⟩ := hx
      have hinitd : dist (Fin.init x) (Fin.init p) < δ := by
        rw [dist_pi_lt_iff hδpos]
        intro i
        have := hxc (Fin.castSucc i)
        simpa [Real.dist_eq, Fin.init] using this
      have hle₂ : δ ≤ δ₂ := by simp only [δ]; exact le_trans (min_le_left _ _) (min_le_right _ _)
      have hd₂ : dist (Fin.init x) u.1 < δ₂ := lt_of_lt_of_le hinitd hle₂
      have happ : f (Fin.init x, ψ (Fin.init x)) = f u := hδ₂ hd₂
      have hfx : f (Fin.init x, x (Fin.last m)) = (MvPolynomial.eval x) P := by
        simp only [f]
        rw [Fin.snoc_init_self]
      refine ⟨?_, hxc⟩
      rw [← hfx, hval, happ, hfu]

end Work.WilkiesI
