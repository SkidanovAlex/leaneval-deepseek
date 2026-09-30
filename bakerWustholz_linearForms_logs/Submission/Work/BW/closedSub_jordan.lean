import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.eval_gpow_eq
import Submission.Work.BW.expPoly_indep

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B2a: the Jordan splitting for `G_a × G_m^N`

Node `closedSub_jordan` of the split of `zero_estimate_stepwise` (block B2 of DESIGN_B.md): a
Zariski-closed subgroup `H` of `G = G_a × G_m^N` contains the torus part `(0, y)` of each of its
elements `(a, y) = a₀ × (y_1, …, y_N)`, and contains the whole `G_a`-line `{(b, 1, …, 1)}` as soon
as some element of `H` has `a₀ ≠ 0`.

Proof.  Let `f` be a polynomial vanishing on `H` and let `(a₀, y) ∈ H` with `y_i ≠ 0`.  The
`t`-th powers `(a₀, y)^t = (t·a₀, y₁^t, …, y_N^t)` lie in `H` (`gpow`, `gpow_zero`, `gpow_succ`),
so `t ↦ f((a₀,y)^t)` vanishes for every `t : ℕ`.  Expanding `eval` in monomials
(`eval_gpow_eq`), grouping the monomials `m` of `f` by their character value
`lam = ∏_i y_i^{m_{i.succ}}` and normalising, this reads

  `∑ m, (z m)^t * (Q m).eval t = 0`  with  `Q m = monomial (m 0) (f.coeff m * a₀^{m 0})`,

an identity of exponential polynomials.  Linear independence of the monomials `t ↦ lam^t * N(t)`
(`expPoly_indep`, applied after regrouping the fibres with `fiber_eval_pow`) kills every fibre sum
`QA lam = ∑_{z m = lam} Q m`.  Evaluating the resulting identities
`∑_lam mu_lam (QA lam).eval c = 0` at `c = 0`, `mu_lam = lam` yields `f(0, y) = 0` (the torus
part of `(a₀, y)` is in `H`), and at `c = b/a₀`, `mu_lam = 1` (using `a₀ ≠ 0`) yields
`f(b, 1, …, 1) = 0` for all `b`.

Here `Submission.Work.BW.eval_gpow_eq` and `Submission.Work.BW.expPoly_indep` are the two
delegated auxiliary lemmas; the rest of the argument (fibre regrouping, the group powers and the
two evaluations) is in this file.  The lemmas `gpow`, `gpow_zero`, `gpow_succ` and `jordan_aux`
are reusable by the sibling nodes B2b (`closedSub_torus`) and B2c (`closedSub_structure`).
-/

namespace Work.BW

open Polynomial

/-! ### Auxiliary lemmas -/

/-- Regrouping a sum over the fibres of a map `z : ι → ℂ`: the value at `x` of the exponential
polynomial attached to the fibre sums `∑_{z m = lam} Q m` equals `∑ m (z m)^t * (Q m)(x)`. -/
lemma fiber_eval_pow {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℂ)
    (Q : ι → Polynomial ℂ) (t : ℕ) (x : ℂ) :
    ∑ lam ∈ s.image z, lam ^ t * (∑ m ∈ s.filter (fun m => z m = lam), Q m).eval x
      = ∑ m ∈ s, z m ^ t * (Q m).eval x := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := s.image z) (g := z)
    (f := fun m => z m ^ t * (Q m).eval x) (fun m hm => Finset.mem_image_of_mem z hm)]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [(Finset.mem_filter.mp hm).2]

/-- `t`-th power of the point `a` of `G = G_a × G_m^N` in the group law
`(u, y) · (v, z) = (u + v, y z)`. -/
noncomputable def gpow {N : ℕ} (a : Fin (N + 1) → ℂ) (t : ℕ) : Fin (N + 1) → ℂ :=
  Fin.cons ((t : ℂ) * a 0) (fun i : Fin N => a i.succ ^ t)

lemma gpow_zero {N : ℕ} (a : Fin (N + 1) → ℂ) : gpow a 0 = gone N := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [gpow, gone]

lemma gpow_succ {N : ℕ} (a : Fin (N + 1) → ℂ) (t : ℕ) :
    gpow a (t + 1) = gmul a (gpow a t) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp only [gpow, gmul, Fin.cons_zero, Nat.cast_add, Nat.cast_one]
    ring
  · intro j
    simp only [gpow, gmul, Fin.cons_succ, pow_succ]
    ring

/-- If `f` vanishes at the `t`-th powers `(t·a₀, y₁^t, …, y_N^t)` of the point `(a₀, y)` of
`G = G_a × G_m^N` (with all `y i ≠ 0`) for every `t : ℕ`, then `f` vanishes at the torus point
`(0, y)`, and — provided `a₀ ≠ 0` — at every point `(b, 1, …, 1)`.

Indeed, `t ↦ f((a₀,y)^t) = ∑_lam lam^t Q_lam(t)` is an exponential polynomial in `t` (the
`lam` being the finitely many values `∏_i y_i^{m_i}` over the monomials `m` of `f`, all non-zero
since `y_i ≠ 0`, and `Q_lam(t) = ∑_{∏ y^{m_i} = lam} f_m a₀^{m_0} t^{m_0}`); it vanishes on all of
`ℕ`, so every `Q_lam` is zero.  Evaluating `∑_lam mu_lam Q_lam(c)` at `c = 0`, `mu_lam = lam`
gives `f(0, y) = 0`, and at `c = b/a₀`, `mu_lam = 1` gives `f(b, 1, …, 1) = 0`. -/
lemma jordan_aux {N : ℕ} (f : MvPolynomial (Fin (N + 1)) ℂ) (y : Fin N → ℂ)
    (hy : ∀ i : Fin N, y i ≠ 0) (a0 : ℂ)
    (hvan : ∀ t : ℕ, MvPolynomial.eval (Fin.cons ((t : ℂ) * a0) (fun i : Fin N => y i ^ t)) f
      = 0) :
    MvPolynomial.eval (Fin.cons (0 : ℂ) y) f = 0 ∧
      (a0 ≠ 0 → ∀ b : ℂ, MvPolynomial.eval (Fin.cons b (fun _ : Fin N => (1 : ℂ))) f = 0) := by
  classical
  set z : (Fin (N + 1) →₀ ℕ) → ℂ := fun m => ∏ i : Fin N, y i ^ (m i.succ) with hz
  set Q : (Fin (N + 1) →₀ ℕ) → Polynomial ℂ :=
    fun m => Polynomial.monomial (m 0) (f.coeff m * a0 ^ (m 0)) with hQ
  set QA : ℂ → Polynomial ℂ :=
    fun lam => ∑ m ∈ f.support.filter (fun m => z m = lam), Q m with hQA
  -- the characters `z m` are non-zero
  have hz0 : ∀ m ∈ f.support, z m ≠ 0 := by
    intro m _
    rw [hz]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hy i)
  -- the identity of exponential polynomials
  have h1 : ∀ t : ℕ, ∑ m ∈ f.support, z m ^ t * (Q m).eval (t : ℂ) = 0 := by
    intro t
    have h := hvan t
    rw [eval_gpow_eq] at h
    rw [← h]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hz, hQ, Polynomial.eval_monomial]
  -- fibre regrouping
  have hconv : ∀ (t : ℕ) (x : ℂ),
      ∑ lam ∈ f.support.image z, lam ^ t * (QA lam).eval x
        = ∑ m ∈ f.support, z m ^ t * (Q m).eval x := by
    intro t x
    rw [hQA]
    exact fiber_eval_pow f.support z Q t x
  -- independence kills each fibre sum
  have h2 : ∀ lam ∈ f.support.image z, QA lam = 0 := by
    have hsum : ∀ t : ℕ, ∑ lam ∈ f.support.image z, lam ^ t * (QA lam).eval (t : ℂ) = 0 := by
      intro t
      rw [← h1 t, hconv t (t : ℂ)]
    exact expPoly_indep (f.support.image z) (fun lam : ℂ => lam) QA
      (fun lam hlam => by
        obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hlam
        exact hz0 m hm)
      (fun _ _ _ _ heq => heq)
      hsum
  constructor
  · -- the torus part: evaluate `∑_lam lam * (QA lam).eval 0`
    have hsum0 : ∑ lam ∈ f.support.image z, lam * (QA lam).eval (0 : ℂ) = 0 := by
      refine Finset.sum_eq_zero fun lam hlam => ?_
      rw [h2 lam hlam]
      simp
    have hL : MvPolynomial.eval (Fin.cons (0 : ℂ) y) f
        = ∑ m ∈ f.support, f.coeff m * (0 : ℂ) ^ (m 0) * ∏ i : Fin N, y i ^ (m i.succ) := by
      rw [MvPolynomial.eval_eq']
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    have hchain : ∑ lam ∈ f.support.image z, lam * (QA lam).eval (0 : ℂ)
        = ∑ m ∈ f.support, f.coeff m * (0 : ℂ) ^ (m 0) * ∏ i : Fin N, y i ^ (m i.succ) := by
      rw [show ∑ lam ∈ f.support.image z, lam * (QA lam).eval (0 : ℂ)
            = ∑ m ∈ f.support, z m * (Q m).eval (0 : ℂ) from by simpa using hconv 1 0]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hz, hQ, Polynomial.eval_monomial]
      have h00 : a0 ^ (m 0) * (0 : ℂ) ^ (m 0) = (0 : ℂ) ^ (m 0) := by
        rw [← mul_pow, mul_zero]
      calc (∏ i : Fin N, y i ^ (m i.succ)) * ((f.coeff m * a0 ^ (m 0)) * (0 : ℂ) ^ (m 0))
          = (∏ i : Fin N, y i ^ (m i.succ)) *
              (f.coeff m * (a0 ^ (m 0) * (0 : ℂ) ^ (m 0))) := by ring
        _ = (∏ i : Fin N, y i ^ (m i.succ)) * (f.coeff m * (0 : ℂ) ^ (m 0)) := by rw [h00]
        _ = f.coeff m * (0 : ℂ) ^ (m 0) * ∏ i : Fin N, y i ^ (m i.succ) := by ring
    rw [hL, ← hchain]
    exact hsum0
  · -- the `G_a`-line: evaluate `∑_lam (QA lam).eval (b/a₀)`
    intro ha0 b
    have hsum2 : ∑ lam ∈ f.support.image z, (QA lam).eval (b / a0) = 0 := by
      refine Finset.sum_eq_zero fun lam hlam => ?_
      rw [h2 lam hlam]
      simp
    have hL2 : MvPolynomial.eval (Fin.cons b (fun _ : Fin N => (1 : ℂ))) f
        = ∑ m ∈ f.support, f.coeff m * b ^ (m 0) := by
      rw [MvPolynomial.eval_eq']
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, one_pow]
      simp
    have hchain2 : ∑ lam ∈ f.support.image z, (QA lam).eval (b / a0)
        = ∑ m ∈ f.support, f.coeff m * b ^ (m 0) := by
      rw [show ∑ lam ∈ f.support.image z, (QA lam).eval (b / a0)
            = ∑ m ∈ f.support, (Q m).eval (b / a0) from by simpa using hconv 0 (b / a0)]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hQ, Polynomial.eval_monomial]
      have hdiv : a0 ^ (m 0) * (b / a0) ^ (m 0) = b ^ (m 0) := by
        rw [← mul_pow, mul_div_cancel₀ b ha0]
      calc (f.coeff m * a0 ^ (m 0)) * (b / a0) ^ (m 0)
          = f.coeff m * (a0 ^ (m 0) * (b / a0) ^ (m 0)) := by ring
        _ = f.coeff m * b ^ (m 0) := by rw [hdiv]
    rw [hL2, ← hchain2]
    exact hsum2

/-! ### B2a -/

/-- B2a (Jordan splitting for `G_a × G_m^N`). A Zariski-closed subgroup `H` contains the torus
part `(0, y)` of each of its elements `(a, y)`, and contains `G_a × 1` as soon as some element has
`a ≠ 0`. Proof: for `f` vanishing on `H`, `n ↦ f((a,y)^n)` is an exponential polynomial
`∑_λ λⁿ Q_λ(n)`; independence of `n^k λⁿ` (cf. `expPoly_zeros`) kills each `Q_λ`, then evaluate
`∑_λ μ_λ Q_λ(c)` at `c = b/a, μ = 1` and at `c = 0, μ_λ = λ`. Size 1.5–2.5k. -/
theorem closedSub_jordan {N : ℕ} (H : Set (Fin (N + 1) → ℂ)) (hH : IsClosedSubG H)
    (a : Fin (N + 1) → ℂ) (ha : a ∈ H) :
    (Fin.cons (0 : ℂ) (fun i : Fin N => a i.succ) : Fin (N + 1) → ℂ) ∈ H ∧
      (a 0 ≠ 0 → ∀ b : ℂ, (Fin.cons b (fun _ : Fin N => (1 : ℂ)) : Fin (N + 1) → ℂ) ∈ H) := by
  classical
  obtain ⟨hInG, hgone, hmul, hinv, S, hS⟩ := hH
  have hy : ∀ i : Fin N, a i.succ ≠ 0 := hInG a ha
  -- the powers `(a, y)^t` all lie in `H`
  have hpow : ∀ t : ℕ, gpow a t ∈ H := by
    intro t
    induction t with
    | zero => rw [gpow_zero]; exact hgone
    | succ t ih => rw [gpow_succ]; exact hmul a ha (gpow a t) ih
  -- hence every defining polynomial of `H` vanishes at all the powers
  have key : ∀ f ∈ S, MvPolynomial.eval (Fin.cons (0 : ℂ) (fun i : Fin N => a i.succ)) f = 0 ∧
      (a 0 ≠ 0 → ∀ b : ℂ,
        MvPolynomial.eval (Fin.cons b (fun _ : Fin N => (1 : ℂ))) f = 0) := by
    intro f hf
    refine jordan_aux f (fun i : Fin N => a i.succ) hy (a 0) ?_
    intro t
    have hmem := hpow t
    rw [hS] at hmem
    simpa only [gpow] using hmem.2 f hf
  constructor
  · rw [hS]
    refine ⟨?_, fun f hf => (key f hf).1⟩
    intro i
    simpa using hy i
  · intro ha0 b
    rw [hS]
    refine ⟨?_, fun f hf => (key f hf).2 ha0 b⟩
    intro i
    simp

end Work.BW
