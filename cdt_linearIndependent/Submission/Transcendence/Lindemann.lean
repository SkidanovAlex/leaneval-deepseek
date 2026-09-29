import Mathlib
import Submission.Transcendence.Hermite
import Submission.Commons.FieldTheory.Minpoly.ConjRoots.trace_rat_poly

/-!
# Lindemann's theorem: the conjugate-root infrastructure (first step)

Hermite's theorem (`Submission.Transcendence.Hermite`) proved `e` transcendental
by feeding the *integer* exponents `0,1,…,N` into the analytic machinery.
Lindemann's theorem — `cexp z` transcendental for algebraic `z ≠ 0` — needs the
same machinery with exponents that are *algebraic numbers*: the numbers
`0, z, 2z, …, dz` and their `ℚ`-conjugates.  This module lays the algebraic
footing:

* `conjRoots z` — the multiset of `ℚ`-conjugates of an algebraic `z : ℂ`
  (the roots of `minpoly ℚ z` in `ℂ`, with multiplicity);
* `z` is among its own conjugates;
* every conjugate is a root of the minimal polynomial, and conversely;
* the minimal polynomial splits over `ℂ` as the product of the linear factors
  over the conjugates (`map_minpoly_eq_prod_X_sub_C`) — the source of all
  "rational symmetric function" facts about the conjugates (coefficients of
  that product lie in `ℚ`).

The next steps (future sessions) replace the root set `1,…,N` of §5 of the
Hermite module by this conjugate multiset (scaled by the exponents of the
algebraic relation of `eᶻ`), giving Lindemann's theorem, and hence
`Transcendental ℚ (log q)` for rational `q ≠ 0, 1` — the `m = n` corner of
Theorem C of Calegari–Dimitrov–Tang.
-/

noncomputable section

open Complex Polynomial
open scoped BigOperators

namespace Submission.Transcendence

/-- The `ℚ`-conjugates of an algebraic `z : ℂ`: the roots (with multiplicity)
in `ℂ` of the minimal polynomial of `z` over `ℚ`. -/
def conjRoots (z : ℂ) : Multiset ℂ :=
  (minpoly ℚ z).aroots ℂ

/-- An algebraic number is one of its own conjugates. -/
lemma mem_conjRoots_self {z : ℂ} (hz : IsAlgebraic ℚ z) : z ∈ conjRoots z := by
  have hzi : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp hz
  rw [conjRoots, Polynomial.mem_aroots]
  exact ⟨minpoly.ne_zero hzi, minpoly.aeval ℚ z⟩

/-- Every conjugate is a root of the minimal polynomial. -/
lemma aeval_mem_conjRoots {z w : ℂ} (hw : w ∈ conjRoots z) :
    aeval w (minpoly ℚ z) = 0 := by
  rw [conjRoots, Polynomial.mem_aroots] at hw
  exact hw.2

/-- Conversely, a root of the minimal polynomial is a conjugate. -/
lemma conjRoots_of_aeval {z w : ℂ} (hz : IsAlgebraic ℚ z)
    (hw : aeval w (minpoly ℚ z) = 0) : w ∈ conjRoots z := by
  have hzi : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp hz
  rw [conjRoots, Polynomial.mem_aroots]
  exact ⟨minpoly.ne_zero hzi, hw⟩

/-- The minimal polynomial of an algebraic number splits over `ℂ` into the
product of the linear factors over its conjugates:

`minpoly ℚ z = ∏_{w ∈ conjRoots z} (X − w)`   (as polynomials over ℂ).

This is the *rational symmetric function* fact: the elementary symmetric
polynomials in the conjugates are (up to sign) the `ℚ`-coefficients of the
minimal polynomial. -/
theorem map_minpoly_eq_prod_X_sub_C {z : ℂ} (hz : IsAlgebraic ℚ z) :
    (minpoly ℚ z).map (algebraMap ℚ ℂ) =
      ((conjRoots z).map (fun r => X - C r)).prod := by
  have hzi : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp hz
  -- both sides are polynomials over ℂ, equal as functions
  apply Polynomial.funext
  intro x
  -- right hand side evaluated at x:
  have hR : eval x (((conjRoots z).map (fun r => X - C r)).prod) =
      ((conjRoots z).map (fun r => x - r)).prod := by
    rw [Polynomial.eval_multiset_prod]
    simp [conjRoots]
  -- left hand side evaluated at x:
  have hL : eval x ((minpoly ℚ z).map (algebraMap ℚ ℂ)) =
      (((minpoly ℚ z).aroots ℂ).map (fun r => x - r)).prod := by
    rw [← Polynomial.eval₂_eq_eval_map, ← Polynomial.aeval_def]
    have hsplit : ((minpoly ℚ z).map (algebraMap ℚ ℂ)).Splits := by
      exact IsAlgClosed.splits ((minpoly ℚ z).map (algebraMap ℚ ℂ))
    rw [Polynomial.Splits.aeval_eq_prod_aroots_of_monic hsplit (minpoly.monic hzi) x]
  rw [hL, hR]
  rfl


/-! ## 2.  The exponent set `{0, z, …, m·z}`

If `β = cexp z` is algebraic of degree `d`, a minimal polynomial of `β` gives
an integral relation `Σⱼ bⱼ·βʲ = 0`, i.e. `Σⱼ bⱼ·cexp(j•z) = 0` over the
exponent set `{j·z : j = 0,…,m}`.  This section records that finite object
and its small API: membership of `0` and `z`, the `m+1` distinct exponents
(when `z ≠ 0`), and the rewriting of the relation as a polynomial evaluation
at `β` (the analogue of `aeval_sum_exp` in the Hermite module).
-/

/-- The exponent set `{0·z, 1·z, …, m·z}` as a finite set of complex numbers. -/
def expSet (z : ℂ) (m : ℕ) : Finset ℂ :=
  (Finset.range (m + 1)).image fun j : ℕ => j • z

/-- `0 = 0·z` is among the exponents. -/
lemma zero_mem_expSet (z : ℂ) (m : ℕ) : (0 : ℂ) ∈ expSet z m := by
  rw [expSet, Finset.mem_image]
  refine ⟨0, by simp, by simp⟩

/-- `z = 1·z` is among the exponents as soon as `m ≥ 1`. -/
lemma self_mem_expSet (z : ℂ) {m : ℕ} (hm : 1 ≤ m) : z ∈ expSet z m := by
  rw [expSet, Finset.mem_image]
  refine ⟨1, ?_, by simp⟩
  rw [Finset.mem_range]
  omega

/-- For `z ≠ 0`, the map `j ↦ j•z` is injective (no torsion in `ℂ`). -/
lemma nsmul_injective_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    Function.Injective fun j : ℕ => j • z := by
  intro j k hjk
  have hjk' : (j : ℂ) * z = (k : ℂ) * z := by
    simpa [nsmul_eq_mul] using hjk
  have hc : (j : ℂ) = (k : ℂ) := mul_right_cancel₀ hz hjk'
  exact_mod_cast hc

/-- For `z ≠ 0` the exponents `0, z, …, m·z` are `m+1` distinct complex
numbers. -/
lemma card_expSet (z : ℂ) (m : ℕ) (hz : z ≠ 0) : (expSet z m).card = m + 1 := by
  rw [expSet]
  rw [Finset.card_image_of_injOn]
  · simp
  · exact (nsmul_injective_of_ne_zero hz).injOn

/-- A linear relation over the exponents is exactly a polynomial evaluated at
`β = cexp z`:

`(aeval β) (Σⱼ bⱼ·Xʲ) = Σⱼ bⱼ·cexp(j•z)`. -/
lemma aeval_sum_exp_of_expSet (z : ℂ) (m : ℕ) (b : ℕ → ℂ) :
    Polynomial.aeval (cexp z) (∑ j ∈ Finset.range (m + 1), C (b j) * X ^ j) =
      ∑ j ∈ Finset.range (m + 1), b j * cexp (j • z) := by
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j hj
  calc
    (Polynomial.aeval (cexp z)) (C (b j) * X ^ j)
        = (Polynomial.aeval (cexp z)) (C (b j)) * (Polynomial.aeval (cexp z)) (X ^ j) := by
          rw [Polynomial.aeval_mul]
    _ = b j * (cexp z) ^ j := by
          simp [Polynomial.aeval_C]
    _ = b j * cexp (j • z) := by
          rw [← Complex.exp_nsmul z j]



/-! ## 3.  The auxiliary polynomial and its high-order vanishing

Mirroring §2–§3 of the Hermite module (`hermitePoly`, `sumIDeriv_hermite_*`),
define the auxiliary polynomial for Lindemann's theorem: `X^(p−1)` times, for
every `j = 1,…,m`, the `p`-th powers of the linear factors over the
`ℚ`-conjugates of the exponent `j·z`:

`f(x) = x^(p−1) · ∏_{j=1}^m ∏_{w ∈ conjRoots(j·z)} (x − w)ᵖ`.

It vanishes to order `p` at every conjugate of every positive exponent, and
to order `p−1` at `0`.  (The arithmetic consequences — factorial divisibility
of `sumIDeriv` values, mirroring the Hermite module — come in the next pitch.)
-/

/-- The auxiliary polynomial of Lindemann's theorem (product form over the
conjugate multisets). -/
def auxPoly (z : ℂ) (m p : ℕ) : ℂ[X] :=
  X ^ (p - 1) *
    ∏ j ∈ Finset.Icc 1 m, ((conjRoots (j • z)).map (fun w => (X - C w) ^ p)).prod

/-- In the factor belonging to the exponent `j·z`, the linear factor
`(X − w)` for a conjugate `w` of `j·z` appears to the power `p`, so it
divides the whole auxiliary polynomial. -/
lemma auxPoly_dvd_conjFactor {z w : ℂ} {m p : ℕ} (j : ℕ) (hj : j ∈ Finset.Icc 1 m)
    (hw : w ∈ conjRoots (j • z)) : (X - C w) ^ p ∣ auxPoly z m p := by
  let F : ℂ → ℂ[X] := fun w0 => (X - C w0) ^ p
  have hs : conjRoots (j • z) = w ::ₘ (conjRoots (j • z)).erase w :=
    (Multiset.cons_erase hw).symm
  have hG : ((conjRoots (j • z)).map F).prod =
      (X - C w) ^ p * (((conjRoots (j • z)).erase w).map F).prod := by
    rw [hs, Multiset.map_cons, Multiset.prod_cons]
    rw [Multiset.erase_cons_head]
  -- isolate the j-factor inside the outer product over Icc 1 m
  have hjprod : (∏ j0 ∈ Finset.Icc 1 m, ((conjRoots (j0 • z)).map F).prod) =
      ((conjRoots (j • z)).map F).prod *
        (∏ j0 ∈ (Finset.Icc 1 m).erase j, ((conjRoots (j0 • z)).map F).prod) := by
    have h := Finset.prod_erase_mul (Finset.Icc 1 m)
      (fun j0 => ((conjRoots (j0 • z)).map F).prod) hj
    -- h : (∏ erase)·G j = ∏ over Icc 1 m
    rw [← h, mul_comm]
  refine ⟨X ^ (p - 1) * (((conjRoots (j • z)).erase w).map F).prod *
      (∏ j0 ∈ (Finset.Icc 1 m).erase j, ((conjRoots (j0 • z)).map F).prod), ?_⟩
  unfold auxPoly
  rw [hjprod, hG]
  ring

/-- Main vanishing lemma: at a conjugate `w` of the exponent `j·z`
(`1 ≤ j ≤ m`), every derivative of order `< p` of the auxiliary polynomial
vanishes. -/
lemma auxPoly_vanishes_at_conj {z w : ℂ} {m p : ℕ} (j : ℕ) (hj : j ∈ Finset.Icc 1 m)
    (hw : w ∈ conjRoots (j • z)) {k : ℕ} (hk : k < p) :
    (aeval w) ((⇑derivative)^[k] (auxPoly z m p)) = 0 := by
  obtain ⟨q, hq⟩ := auxPoly_dvd_conjFactor (z := z) (w := w) (m := m) (p := p) j hj hw
  exact Polynomial.aeval_iterate_derivative_of_lt (R := ℂ) (A := ℂ)
    (auxPoly z m p) p w (by simpa using hq) hk

/-- The factor `X^(p−1)` is explicit in the auxiliary polynomial. -/
lemma auxPoly_dvd_at_zero (z : ℂ) (m p : ℕ) : X ^ (p - 1) ∣ auxPoly z m p := by
  unfold auxPoly
  exact dvd_mul_right _ _

/-- At `0`, derivatives of order `< p − 1` of the auxiliary polynomial
vanish (multiplicity `p−1` at the origin). -/
lemma auxPoly_vanishes_at_zero (z : ℂ) (m p : ℕ) {k : ℕ} (hk : k < p - 1) :
    (aeval (0 : ℂ)) ((⇑derivative)^[k] (auxPoly z m p)) = 0 := by
  obtain ⟨q, hq⟩ := auxPoly_dvd_at_zero z m p
  exact Polynomial.aeval_iterate_derivative_of_lt (R := ℂ) (A := ℂ)
    (auxPoly z m p) (p - 1) (0 : ℂ) (by simpa using hq) hk



/-! ## 4.  Norm estimates for the analytic bound

`P_le_explicit` (Hermite module, §5e) bounds `‖P(fₚ, s)‖` in terms of
`‖s‖` and a pointwise bound of `fₚ` on the disk around `0` of radius `‖s‖`.
For Lindemann the analytic points are the *exponents* `s = j·z`
(`j = 1,…,m`), whose norms are controlled by `‖z‖·m`:

`‖j·z‖ = j·‖z‖ ≤ m·‖z‖`.

**Caveat.** The *conjugates* `w ∈ conjRoots (j·z)` do **not** satisfy
`‖w‖ ≤ ‖z‖·m` in general (e.g. `z = (2−√2)/2` has conjugate
`(2+√2)/2 > ‖z‖`), so conjugate norms must instead be controlled through
the minimal polynomial (coefficients, via `map_minpoly_eq_prod_X_sub_C`)
when the arithmetic step needs them; only the exponent points feed
`P_le_explicit` directly.
-/

/-- The norm of a natural multiple: `‖j·z‖ = j·‖z‖`. -/
lemma norm_nsmul_eq (j : ℕ) (z : ℂ) : ‖j • z‖ = (j : ℝ) * ‖z‖ := by
  rw [nsmul_eq_mul, norm_mul]
  simp

/-- For an exponent `j·z` with `j ≤ m`, `‖j·z‖ ≤ ‖z‖·m` (the bound that
`P_le_explicit` is applied with). -/
lemma exp_norm_le (z : ℂ) {m j : ℕ} (hj : j ≤ m) : ‖j • z‖ ≤ (m : ℝ) * ‖z‖ := by
  have h1 : ‖j • z‖ = (j : ℝ) * ‖z‖ := norm_nsmul_eq j z
  rw [h1]
  have hj' : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
  have hn0 : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith



/-! ## 5.  Pointwise bound of the auxiliary polynomial on a disk

To run the analytic part (`P_le_explicit`, Hermite module §5e) at the exponent
points `s = j·z`, one needs a pointwise bound of `auxPoly z m p` on the disk
`{‖z₀‖ ≤ R}` with `R = m·‖z‖` (see `exp_norm_le`).  The bound absorbs every
conjugate into one finite constant (a product of `R + ‖w‖` over all
conjugates of all exponents) — no conjugate-norm estimate is needed.
-/

/-- Norm of a product over a multiset of complex numbers. -/
lemma norm_multiset_prod (s : Multiset ℂ) : ‖s.prod‖ = (s.map fun a => ‖a‖).prod := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro a s ih
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    rw [norm_mul, ih]

/-- Power distributes over a multiset product. -/
lemma multiset_prod_map_pow (s : Multiset ℂ) (f : ℂ → ℝ) (n : ℕ) :
    ((s.map fun a => f a ^ n).prod) = ((s.map f).prod) ^ n := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro a s ih
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ih]
    rw [mul_pow]

/-- A product of nonnegative reals over a multiset is nonnegative. -/
lemma multiset_prod_nonneg {s : Multiset ℝ} (h : ∀ a ∈ s, 0 ≤ a) : 0 ≤ s.prod := by
  have : ∀ t : Multiset ℝ, (∀ a ∈ t, 0 ≤ a) → 0 ≤ t.prod := by
    intro t
    refine Multiset.induction_on t ?_ ?_
    · intro h
      simp
    · intro a t' ih h
      rw [Multiset.prod_cons]
      exact mul_nonneg (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))
  exact this s h


/-- Norm of the evaluation at `z0` of a multiset product of powered linear
factors `(X − w)ᵖ`: it is the product of `‖z0 − w‖ᵖ`. -/
lemma multiset_linear_eval_norm (s : Multiset ℂ) (p : ℕ) (z0 : ℂ) :
    ‖(((s.map fun w => (X - C w) ^ p)).prod).eval z0‖ =
      ((s.map fun w => ‖z0 - w‖ ^ p)).prod := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro w s ih
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    rw [eval_mul, norm_mul]
    rw [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [norm_pow]
    rw [ih]

/-- Monotonicity of products over a multiset (nonnegative, pointwise). -/
lemma multiset_map_prod_le_prod {α : Type*} {s : Multiset α} (f g : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) (hfg : ∀ a ∈ s, f a ≤ g a) :
    (s.map f).prod ≤ (s.map g).prod := by
  have : ∀ t : Multiset α, (∀ a ∈ t, 0 ≤ f a) → (∀ a ∈ t, f a ≤ g a) →
      (t.map f).prod ≤ (t.map g).prod := by
    intro t
    refine Multiset.induction_on t ?_ ?_
    · intro h1 h2
      simp
    · intro a t' ih h1 h2
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
      exact mul_le_mul (h2 a (by simp))
        (ih (fun b hb => h1 b (by simp [hb])) (fun b hb => h2 b (by simp [hb])))
        (multiset_prod_nonneg (s := (t'.map f)) (by
          intro b hb
          rcases Multiset.mem_map.mp hb with ⟨a₀, ha₀, rfl⟩
          exact h1 a₀ (by simp [ha₀])))
        (le_trans (h1 a (by simp)) (h2 a (by simp)))
  exact this s hf hfg



/-- Pointwise bound: for `‖z₀‖ ≤ R` (with `0 ≤ R`),

`‖(auxPoly z m p).eval z₀‖ ≤ ((R+1) · ∏_{j=1}^m ∏_{w ∈ conjRoots(j·z)} (R + ‖w‖))ᵖ`.

The product over the conjugates is a fixed finite constant (independent of
`p`), so this is the `Cᵖ`-type pointwise bound that `P_le_explicit` consumes
(with `R = m·‖z‖` by `exp_norm_le`). -/
lemma auxPoly_eval_bound (z : ℂ) (m : ℕ) (p : ℕ) {R : ℝ} (hR : 0 ≤ R) {z0 : ℂ}
    (hz0 : ‖z0‖ ≤ R) :
    ‖(auxPoly z m p).eval z0‖ ≤
      ((R + 1) * ∏ j ∈ Finset.Icc 1 m, ((conjRoots (j • z)).map (fun w => R + ‖w‖)).prod) ^ p := by
  let PR : ℝ := ∏ j ∈ Finset.Icc 1 m, ((conjRoots (j • z)).map (fun w => R + ‖w‖)).prod
  have hPR0 : 0 ≤ PR := by
    dsimp [PR]
    exact Finset.prod_nonneg (fun j hj =>
      multiset_prod_nonneg (s := (conjRoots (j • z)).map (fun w => R + ‖w‖)) (by
        intro b hb
        rcases Multiset.mem_map.mp hb with ⟨w, hw, rfl⟩
        exact add_nonneg hR (norm_nonneg w)))
  -- evaluation identity
  have hOuter : ‖(auxPoly z m p).eval z0‖ =
      ‖z0‖ ^ (p - 1) * ∏ j ∈ Finset.Icc 1 m,
        (((conjRoots (j • z)).map (fun w => ‖z0 - w‖ ^ p)).prod) := by
    unfold auxPoly
    rw [eval_mul]
    rw [norm_mul]
    rw [eval_pow, eval_X]
    rw [norm_pow]
    rw [Polynomial.eval_prod]
    rw [norm_prod]
    apply congrArg (fun t : ℝ => ‖z0‖ ^ (p - 1) * t)
    apply Finset.prod_congr
    · rfl
    · intro (j : ℕ) hj
      exact multiset_linear_eval_norm (conjRoots (j • z)) p z0
  calc
    ‖(auxPoly z m p).eval z0‖
        = ‖z0‖ ^ (p - 1) * ∏ j ∈ Finset.Icc 1 m,
            (((conjRoots (j • z)).map (fun w => ‖z0 - w‖ ^ p)).prod) := hOuter
    _ ≤ ‖z0‖ ^ (p - 1) * ∏ j ∈ Finset.Icc 1 m,
            (((conjRoots (j • z)).map (fun w => (R + ‖w‖) ^ p)).prod) := by
          apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg z0) (p - 1))
          refine Finset.prod_le_prod₀ ?_ ?_
          · intro j hj
            exact multiset_prod_nonneg (s := ((conjRoots (j • z)).map fun w => ‖z0 - w‖ ^ p)) (by
              intro b hb
              rcases Multiset.mem_map.mp hb with ⟨w, hw, rfl⟩
              positivity)
          · intro j hj
            exact multiset_map_prod_le_prod (fun w => ‖z0 - w‖ ^ p) (fun w => (R + ‖w‖) ^ p)
              (fun w hw => by positivity) (fun w hw => by
                have h1 : ‖z0 - w‖ ≤ R + ‖w‖ := by
                  have h2 : ‖z0 - w‖ ≤ ‖z0‖ + ‖w‖ := norm_sub_le z0 w
                  have h3 : ‖z0‖ + ‖w‖ ≤ R + ‖w‖ := by nlinarith
                  exact le_trans h2 h3
                exact pow_le_pow_left₀ (by positivity) h1 p)
    _ = ‖z0‖ ^ (p - 1) * (∏ j ∈ Finset.Icc 1 m,
            (((conjRoots (j • z)).map (fun w => R + ‖w‖)).prod)) ^ p := by
          congr 1
          rw [show (∏ j ∈ Finset.Icc 1 m,
                  (((conjRoots (j • z)).map (fun w => (R + ‖w‖) ^ p)).prod)) =
                (∏ j ∈ Finset.Icc 1 m,
                  (((conjRoots (j • z)).map (fun w => R + ‖w‖)).prod) ^ p) by
                refine Finset.prod_congr rfl ?_
                intro j hj
                exact multiset_prod_map_pow (conjRoots (j • z)) (fun w => R + ‖w‖) p]
          rw [Finset.prod_pow]
    _ = ‖z0‖ ^ (p - 1) * PR ^ p := by
          dsimp [PR]
    _ ≤ R ^ (p - 1) * PR ^ p := by
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z0) hz0 (p - 1))
            (pow_nonneg hPR0 p)
    _ ≤ ((R + 1) * PR) ^ p := by
          have hRp : R ^ (p - 1) ≤ (R + 1) ^ p := by
            have h1 : R ^ (p - 1) ≤ (R + 1) ^ (p - 1) :=
              pow_le_pow_left₀ hR (by linarith) (p - 1)
            have h2 : (R + 1) ^ (p - 1) ≤ (R + 1) ^ p :=
              pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _)
            exact le_trans h1 h2
          calc
            R ^ (p - 1) * PR ^ p ≤ (R + 1) ^ p * PR ^ p := by
              exact mul_le_mul_of_nonneg_right hRp (pow_nonneg hPR0 p)
            _ = ((R + 1) * PR) ^ p := by rw [← mul_pow]
    _ ≤ ((R + 1) * ∏ j ∈ Finset.Icc 1 m, ((conjRoots (j • z)).map (fun w => R + ‖w‖)).prod) ^ p := by
          simpa [PR]



/-- Analytic constant of the auxiliary polynomial for the exponents
`{j·z : j ≤ m}`: pointwise bound of `auxPoly z m ·` on the disk of radius
`m·‖z‖` absorbed into one number (independent of the exponent and of `p`). -/
noncomputable def auxBoundC (z : ℂ) (m : ℕ) : ℝ :=
  ((Real.exp ((m : ℝ) * ‖z‖)) ^ 2 * ((m : ℝ) * ‖z‖) + 1) *
    max ((((m : ℝ) * ‖z‖) + 1) *
      ∏ j ∈ Finset.Icc 1 m,
        ((conjRoots (j • z)).map (fun w => ((m : ℝ) * ‖z‖) + ‖w‖)).prod) 1

/-- The `P`-bound at the exponent points, matching `exp_norm_le`: for
`j ≤ m` and `p ≠ 0`,

`‖P(auxPoly z m p, j·z)‖ ≤ (auxBoundC z m)ᵖ`. -/
lemma P_auxPoly_bound (z : ℂ) (m : ℕ) {p : ℕ} (hp : p ≠ 0) {j : ℕ} (hj : j ≤ m) :
    ‖P (auxPoly z m p) (j • z)‖ ≤ (auxBoundC z m) ^ p := by
  let R : ℝ := (m : ℝ) * ‖z‖
  let c0 : ℝ := (R + 1) *
    ∏ j ∈ Finset.Icc 1 m, ((conjRoots (j • z)).map (fun w => R + ‖w‖)).prod
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hc00 : 0 ≤ c0 := by
    dsimp [c0]
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg (fun j0 hj0 =>
        multiset_prod_nonneg (s := (conjRoots (j0 • z)).map (fun w => R + ‖w‖)) (by
          intro b hb
          rcases Multiset.mem_map.mp hb with ⟨w, hw, rfl⟩
          exact add_nonneg hR0 (norm_nonneg w)))
  have hs_le : ‖j • z‖ ≤ R := by
    dsimp [R]
    exact exp_norm_le z hj
  have hre : (j • z).re ≤ R := le_trans (re_le_norm (j • z)) hs_le
  have hc : ∀ q : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      ‖(auxPoly z m q).eval (x • (j • z))‖ ≤ c0 ^ q := by
    intro q x hx
    have hz0 : ‖x • (j • z)‖ ≤ R := by
      have h1 : ‖x • (j • z)‖ = x * ‖j • z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hx.1.le]
      rw [h1]
      have hx1 : x ≤ 1 := hx.2
      nlinarith [hs_le, norm_nonneg (j • z)]
    exact (auxPoly_eval_bound z m q hR0 hz0).trans (by
      dsimp [c0]
      exact le_rfl)
  have hb := P_le_explicit (f := fun q : ℕ => auxPoly z m q) (s := (j • z)) c0 hc
  have hexp1 : Real.exp ((j • z).re) ≤ Real.exp R := Real.exp_le_exp.mpr hre
  have hexp2 : Real.exp ‖j • z‖ ≤ Real.exp R := Real.exp_le_exp.mpr hs_le
  have hmain : ‖P (auxPoly z m p) (j • z)‖ ≤
      Real.exp R * (Real.exp R * |c0| ^ p * R) := by
    refine (hb p).trans ?_
    gcongr
  have hfinal : Real.exp R * (Real.exp R * |c0| ^ p * R) ≤ (auxBoundC z m) ^ p := by
    have hB1 : 1 ≤ max c0 1 := le_max_right c0 1
    have hB0 : 0 ≤ max c0 1 := le_trans (by norm_num) hB1
    have hA1 : 1 ≤ (Real.exp R) ^ 2 * R + 1 := by
      have h0 : 0 ≤ (Real.exp R) ^ 2 * R := mul_nonneg (sq_nonneg _) hR0
      linarith
    have hA0 : 0 ≤ (Real.exp R) ^ 2 * R + 1 := le_trans (by norm_num) hA1
    have hc0le : |c0| ≤ max c0 1 := by
      rw [abs_of_nonneg hc00]
      exact le_max_left c0 1
    calc
      Real.exp R * (Real.exp R * |c0| ^ p * R)
          = (Real.exp R) ^ 2 * R * |c0| ^ p := by ring
      _ ≤ ((Real.exp R) ^ 2 * R + 1) * (max c0 1) ^ p := by
            have h1 : |c0| ^ p ≤ (max c0 1) ^ p :=
              pow_le_pow_left₀ (abs_nonneg c0) hc0le p
            calc
              (Real.exp R) ^ 2 * R * |c0| ^ p
                  ≤ (Real.exp R) ^ 2 * R * (max c0 1) ^ p := by
                    exact mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg _) hR0)
              _ ≤ ((Real.exp R) ^ 2 * R + 1) * (max c0 1) ^ p := by
                    exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hB0 p)
      _ ≤ (((Real.exp R) ^ 2 * R + 1) * max c0 1) ^ p := by
            have hAp : (Real.exp R) ^ 2 * R + 1 ≤ ((Real.exp R) ^ 2 * R + 1) ^ p :=
              le_self_pow₀ hA1 hp
            calc
              ((Real.exp R) ^ 2 * R + 1) * (max c0 1) ^ p
                  ≤ ((Real.exp R) ^ 2 * R + 1) ^ p * (max c0 1) ^ p := by
                    exact mul_le_mul_of_nonneg_right hAp (pow_nonneg hB0 p)
              _ = (((Real.exp R) ^ 2 * R + 1) * max c0 1) ^ p := by rw [mul_pow]
      _ = (auxBoundC z m) ^ p := by
            dsimp [auxBoundC, R, c0]
  exact le_trans hmain hfinal



/-! ## 6.  The exact exponent identity

If `β = cexp z` is algebraic, a polynomial relation on `β` becomes, via
`aeval_sum_exp_of_expSet`, an exponential relation
`Σⱼ bⱼ·cexp(j·z) = 0` over the exponent set.  Feeding that relation to the
generic Hermite identity at the exponent points `j·z` gives the exponent-side
analogue of `hermJ_mul_factorial`:

`Σⱼ bⱼ·F(j·z) = −Σⱼ bⱼ·P(auxPoly z m p, j·z)`,  `F = sumIDeriv (auxPoly z m p)`.

The *arithmetic* step (next pitch) will replace the left-hand side by a
conjugate-symmetric object (sums of `F`-values over conjugates, where the
factorial divisibility of `sumIDeriv` behaves rationally).
-/

/-- The exact exponent identity: from `Σⱼ bⱼ·cexp(j·z) = 0`,

`Σⱼ bⱼ·F(j·z) = −Σⱼ bⱼ·P(auxPoly z m p, j·z)` with `F = sumIDeriv (auxPoly z m p)`. -/
lemma exponent_identity (z : ℂ) (m p : ℕ) (b : ℕ → ℂ)
    (hrel : ∑ j ∈ Finset.range (m + 1), b j * cexp (j • z) = 0) :
    (∑ j ∈ Finset.range (m + 1), b j * (sumIDeriv (auxPoly z m p)).eval (j • z)) =
      -∑ j ∈ Finset.range (m + 1), b j * P (auxPoly z m p) (j • z) := by
  exact hermite_identity_at (auxPoly z m p) b m (fun j : ℕ => j • z) hrel



/-- An algebraic relation on `β = cexp z` (a polynomial `q` of degree ≤ `m`
vanishing at `β`) becomes an exponential relation over the exponent set:

`Σⱼ (q.coeff j)·cexp(j·z) = 0`. -/
lemma relation_of_aeval (z : ℂ) (m : ℕ) (q : ℂ[X]) (hdeg : q.natDegree ≤ m)
    (hq : Polynomial.aeval (cexp z) q = 0) :
    ∑ j ∈ Finset.range (m + 1), (q.coeff j) * cexp (j • z) = 0 := by
  have hA : Polynomial.aeval (cexp z) q = q.eval (cexp z) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    simp
  have hB : q.eval (cexp z) = ∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * cexp (j • z) := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self q.natDegree) (cexp z)]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [← Complex.exp_nsmul z j]
  have hsmall : (∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * cexp (j • z)) = 0 := by
    rw [← hB, ← hA]
    exact hq
  have hsub : Finset.range (q.natDegree + 1) ⊆ Finset.range (m + 1) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hzero : ∀ x ∈ Finset.range (m + 1), x ∉ Finset.range (q.natDegree + 1) →
      q.coeff x * cexp (x • z) = 0 := by
    intro x hx hxn
    have hlt : q.natDegree < x := by
      rw [Finset.mem_range] at hxn
      omega
    have hc : q.coeff x = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    simp [hc]
  have hext : (∑ j ∈ Finset.range (m + 1), q.coeff j * cexp (j • z)) =
      (∑ j ∈ Finset.range (q.natDegree + 1), q.coeff j * cexp (j • z)) := by
    exact (Finset.sum_subset (s₁ := Finset.range (q.natDegree + 1))
      (s₂ := Finset.range (m + 1)) hsub hzero).symm
  rw [hext]
  exact hsmall


/-! ## 7.  The auxiliary polynomial has rational coefficients

The auxiliary polynomial of §3 was defined as a product over *conjugates*.
By the splitting identity (`map_minpoly_eq_prod_X_sub_C`) each conjugate-class
factor equals the (mapped) minimal polynomial, so the whole product is the
image of an explicit `ℚ`-polynomial.  This is the "rational symmetric
functions" content behind the arithmetic step: evaluations of `sumIDeriv` at
conjugate points will be sums of conjugates of values of a `ℚ`-polynomial.
-/

/-- Power distributes over a multiset product of polynomials. -/
lemma multiset_prod_map_pow_poly (s : Multiset ℂ) (f : ℂ → ℂ[X]) (n : ℕ) :
    ((s.map fun a => (f a) ^ n).prod) = ((s.map f).prod) ^ n := by
  refine Multiset.induction_on s ?_ ?_
  · simp
  · intro a s ih
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ih]
    rw [mul_pow]

/-- The rational-coefficient version of the auxiliary polynomial:
`X^(p−1) · ∏_{j=1}^m (minpoly ℚ (j·z))ᵖ`, whose image in `ℂ[X]` is
`auxPoly z m p`. -/
def auxPolyQ (z : ℂ) (m p : ℕ) : ℚ[X] :=
  X ^ (p - 1) * ∏ j ∈ Finset.Icc 1 m, (minpoly ℚ (j • z)) ^ p

/-- `auxPoly z m p` is the image of the rational polynomial `auxPolyQ z m p`
(for algebraic `z`). -/
lemma auxPoly_eq_map_auxPolyQ {z : ℂ} (m p : ℕ) (hz : IsAlgebraic ℚ z) :
    auxPoly z m p = (auxPolyQ z m p).map (algebraMap ℚ ℂ) := by
  have hfac : ∀ j ∈ Finset.Icc 1 m,
      ((conjRoots (j • z)).map (fun w => (X - C w) ^ p)).prod =
        ((minpoly ℚ (j • z)).map (algebraMap ℚ ℂ)) ^ p := by
    intro j hj
    have hzj : IsAlgebraic ℚ (j • z) := IsAlgebraic.nsmul hz j
    calc
      ((conjRoots (j • z)).map (fun w => (X - C w) ^ p)).prod
          = ((conjRoots (j • z)).map (fun w => (X - C w))).prod ^ p := by
              exact multiset_prod_map_pow_poly (conjRoots (j • z)) (fun w => X - C w) p
      _ = ((minpoly ℚ (j • z)).map (algebraMap ℚ ℂ)) ^ p := by
              rw [map_minpoly_eq_prod_X_sub_C hzj]
  unfold auxPoly auxPolyQ
  rw [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_X]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro j hj
  rw [Polynomial.map_pow]
  exact hfac j hj



/-!
## 8.  ⚠ SUPERSEDED PLAN — read §11 first.

The "pinned arithmetic target" of this section (and §8b) is **not**
implementable as stated (see §11 for why: the direct exponential relation
does not give a conjugate-symmetric relation, so the pinned identity
`Σⱼ bⱼ·Tⱼ = −Σⱼ bⱼ·P(auxPoly)(j•z)` is false when conjugates are
nontrivial).  The correct route to Lindemann's theorem is the Lemma A /
orbit-relation structure of §11.  The §1–§7 and §9–§10 content of this file
remains valid (the analytic `P` machinery, Hermite identities, conjugate
splitting, trace/norm rationality) and is reused there.  This section is kept
only as a historical record of the earlier (incorrect) design.
-/
/-!

**Situation.**  Suppose `β = cexp z` is algebraic (`z` algebraic, `z ≠ 0`), with
integral relation `Σ_{j=0}^{m} b_j·βʲ = 0` (`b₀ ≠ 0`, `b_m ≠ 0`; via the
minimal polynomial of `β`).  By `relation_of_aeval` this is
`Σ_j b_j·cexp(j•z) = 0` over the exponents `j·z` (`j = 0,…,m`).  Write

* `A = auxPolyQ z m p : ℚ[X] = X^(p-1) · ∏_{j=1}^m (minpoly ℚ (j·z))ᵖ`
  (so `auxPoly z m p = A.map (algebraMap ℚ ℂ)`, §7);
* `G := sumIDeriv A : ℚ[X]`, `F := sumIDeriv (auxPoly z m p) = G.map φ`,
  `φ = algebraMap ℚ ℂ`.

**Why conjugates.**  The value `F(j·z)` is *not* rational, but for each
`j = 1,…,m` the trace over the conjugates of the exponent is:

`Tⱼ := ∑_{w ∈ conjRoots (j·z)} F(w)`  (equivalently, since `G ∈ ℚ[X]`, the sum
of the conjugates of the algebraic number `G(j·z)`).

**Pinned arithmetic claim (the target the delegation batch below serves).**
For every sufficiently large prime `p` (larger than a bound depending only on
`z` and `m`):

1. *(rationality)* each `Tⱼ / (p−1)!` is a rational number
   (`∃ rⱼ : ℚ, (rⱼ : ℂ) = Tⱼ / (p−1)!`), and likewise for the exponent-`0`
   term `T₀ = F(0)` (there `conjRoots 0 = {0}`);
2. *(p-integrality and p-adic shape)* in lowest terms `Tⱼ/(p−1)! = aⱼ/bⱼ`
   with `p ∤ bⱼ`, and for `j ≥ 1`: `p | aⱼ` (high multiplicity `p` at each
   conjugate of `j·z`), while for `j = 0`: `p ∤ a₀` (multiplicity `p−1` at
   `0` — the analogue of `Fₚ(0)/(p−1)! ≡ h(0)ᵖ ≢ 0 (mod p)` in Hermite);
3. consequently `J := Σ_{j=0}^{m} b_j·Tⱼ/(p−1)!` is a rational `p`-adic unit
   (in particular `J ≠ 0` as a complex number), of the form predicted by the
   Hermite template, while the analytic side (`P_auxPoly_bound` matched to
   `exp_norm_le`, the relation identity, and the prime/tendsto machinery)
   bounds its modulus by `Cᵖ/(p−1)! < 1` — the contradiction.

**Honest scope note.**  Item 1 is the trace/norm rationality batch below.
Item 2 is where the *classical Lindemann (equivalently
Lindemann–Weierstrass / E₀-)* arithmetic lives: factorial divisibility of
`sumIDeriv` values *over conjugate sums* at algebraic points — deeper than the
integer-point arithmetic of the Hermite module, and the natural place for the
`Algebra.trace`-based proofs plus the queued delegation.  The exponent
identity `exponent_identity` (piece (i)) is the analytic side of this J; the
arithmetic side is what item 2 pins.  Once items 1–2 stand, the assembly is
mechanical: `J ≠ 0`, `|J| ≥ 1` vs `|J| < 1`.

**Delegation batch (issued in parallel with this section):**
generic `ℚ`-trace/norm facts over `minpoly`-conjugates (see the requests):
trace-rationality of `ℚ`-polynomial values over the conjugates, and
norm-rationality of the same.
-/



/-!
## 8b.  ⚠ SUPERSEDED PLAN — see §11.  (Historical record of the earlier, incorrect design; do not implement.)
-/


/-! /-!
## 8b.  Item 2 pinned: p-adic shape of the conjugate traces (statement only)

**Setting (fixed data).**  `z : ℂ` algebraic, `z ≠ 0`; a relation degree
`m ≥ 1` with integer coefficients `b : ℕ → ℤ` (`b₀ ≠ 0`, `b_m ≠ 0`) and
`Σ_{j=0}^{m} b_j·cexp(j•z) = 0`; primes `p`.  Recall (§7, §8):
`A := auxPolyQ z m p`, `G := sumIDeriv A : ℚ[X]`,
`F := sumIDeriv (auxPoly z m p) = G.map (algebraMap ℚ ℂ)`, and the traces

`T₀ := F(0)`  and, for `j = 1,…,m`,
`Tⱼ := Σ_{w ∈ conjRoots (j•z)} F(w)`   (a rational by item 1, §8).

**Why the classical (Hermite–Lindemann) argument makes the traces integers
modulo `p`.**  After clearing denominators of `z` (one fixed integer `D`
makes every conjugate of every `j·z`, `1 ≤ j ≤ m`, an algebraic integer),
each factor `∏_{w ∈ conjRoots(j·z)} (X − C w)` is the minimal polynomial of
the algebraic integer `j·z` — a monic polynomial with **integer** coefficients
— so a ℤ-scaled auxiliary polynomial lives in `ℤ[X]` and the
`aeval_sumIDeriv(_of_pos)` factorial identities (Hermite §3) apply at every
conjugate point `w`.  Evaluating at the algebraic-integer points `w` and
summing over the conjugate orbit turns those identities into **integer**
identities for the traces `T₀` and `Tⱼ` — the analogue of
`sumIDeriv_hermite_zero/pos` — giving the mod-`p` split below.  (Formalizing
this ℤ[X] scaling and the trace-to-integer step is the content of item 2.)

**Pinned statements (item 2).**

(2j) for `j = 1,…,m`:  `Tⱼ = (p−1)!·rⱼ` for a rational `rⱼ` which is
`p`-integral and divisible by `p` in `ℤ_(p)`:
`∃ (a : ℤ) (b : ℕ), rⱼ = a / b ∧ ¬ (p : ℕ) ∣ b ∧ (p : ℕ) ∣ a`   [a may be 0].

(20) for the origin: `T₀ = (p−1)!·r₀` with `r₀` a `p`-unit:
`∃ (a : ℤ) (b : ℕ), r₀ = a / b ∧ ¬ (p : ℕ) ∣ b ∧ ¬ (p : ℕ) ∣ a`
(the multiplicity `p−1` at `0`, mirroring
`Fₚ(0)/(p−1)! ≡ h(0)ᵖ ≢ 0 (mod p)` in Hermite).

(2J) with `p > max |b₀|` (and `p` above a fixed bound depending on `z, m`):
`J := Σ_{j=0}^{m} b_j·rⱼ` is a `p`-unit rational, in particular `J ≠ 0`
(complex norm `‖(J : ℂ)‖ ≥ 1`); while the analytic side gives
`(J : ℂ)·(p−1)! = −Σ_j b_j·P(auxPoly z m p, j•z)` (exponent identity §6) and
`|J| ≤ (auxBoundC z m)ᵖ/(p−1)! < 1` for large primes
(`P_auxPoly_bound` §5b + `pow_div_factorial_pred_eventually_lt`) — the
contradiction.  Hence `cexp z` is transcendental (`Transcendental ℚ (cexp z)`
for algebraic `z ≠ 0`).

**Proof status.**  (2j),(20),(2J) are pinned targets; their proofs are the
next pitches (ℤ[X] scaling via the denominator clearing, trace-to-integer,
and the prime selection), built on the landed trace/norm delegation
(`Commons.FieldTheory.Minpoly.ConjRoots.trace_rat_poly`,
`norm_rat_poly`) once those children report.
-/


-/





/-! ## 9.  Conjugate traces are rational (`trace_rat_poly` application; reusable for Lemma A's trace sums)

With `trace_rat_poly` (commons, from the delegation batch) the trace object
`Tⱼ = Σ_{w ∈ conjRoots (j·z)} F(w)` is rational for every exponent class,
because `F = sumIDeriv (auxPoly z m p)` is the image of the rational
`G = sumIDeriv (auxPolyQ z m p)` (§7).  This is item 1 of the pinned target
(§8); the p-adic shape (items 2j/20) is the next step.
-/

/-- The conjugate trace of the `sumIDeriv` values of the auxiliary polynomial
over the conjugates of the exponent `j·z`. -/
def traceF (z : ℂ) (m p : ℕ) (j : ℕ) : ℂ :=
  ((conjRoots (j • z)).map (fun w => (sumIDeriv (auxPoly z m p)).eval w)).sum

/-- `sumIDeriv (auxPoly z m p)` is the image of the rational polynomial
`sumIDeriv (auxPolyQ z m p)`. -/
lemma sumIDeriv_auxPoly_map {z : ℂ} (m p : ℕ) (hz : IsAlgebraic ℚ z) :
    sumIDeriv (auxPoly z m p) =
      (sumIDeriv (auxPolyQ z m p)).map (algebraMap ℚ ℂ) := by
  rw [auxPoly_eq_map_auxPolyQ m p hz]
  rw [Polynomial.sumIDeriv_map]

/-- Item 1: the trace `Tⱼ = Σ_{w ∈ conjRoots (j·z)} F(w)` is a rational
number, for every exponent class `j`. -/
lemma traceF_rat {z : ℂ} (hz : IsAlgebraic ℚ z) (m p : ℕ) (j : ℕ) :
    ∃ r : ℚ, traceF z m p j = (r : ℂ) := by
  have hzj : IsAlgebraic ℚ (j • z) := IsAlgebraic.nsmul hz j
  have hG : sumIDeriv (auxPoly z m p) =
      (sumIDeriv (auxPolyQ z m p)).map (algebraMap ℚ ℂ) := sumIDeriv_auxPoly_map m p hz
  obtain ⟨r, hr⟩ := Commons.FieldTheory.Minpoly.ConjRoots.trace_rat_poly hzj
    (sumIDeriv (auxPolyQ z m p))
  refine ⟨r, ?_⟩
  unfold traceF
  exact (congrArg (fun h : ℂ[X] => ((conjRoots (j • z)).map (fun w => h.eval w)).sum) hG).trans hr


/-! ## 10.  Denominator clearing: one scalar makes all `j•z` algebraic integers

The p-adic argument needs every conjugate of every exponent `j·z`
(`j = 1,…,m`) to be an algebraic integer after one fixed clearing.  The
`ℤ`-denominator machinery (`Algebra.natDenominator`) supplies the clearing:
an algebraic number times its natural denominator is integral over `ℤ`, and
clearing `z` clears all `j·z` at once (`j·(d·z) = d·(j·z)`).
-/

/-- Every algebraic `z : ℂ` has a nonzero natural denominator `d` with
`d•z` integral over `ℤ`. -/
lemma exists_algebraicInt_scalar {z : ℂ} (hz : IsAlgebraic ℚ z) :
    ∃ d : ℕ, d ≠ 0 ∧ IsIntegral ℤ (d • z) := by
  have hzZ : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℂ)).mpr hz
  refine ⟨Algebra.natDenominator z, IsAlgebraic.natDenominator_ne_zero hzZ, ?_⟩
  exact Algebra.isIntegral_natDenominator_smul z

/-- Natural scalar multiples commute: `d•(j•z) = j•(d•z)`. -/
lemma nsmul_comm_nsmul (d j : ℕ) (z : ℂ) : d • (j • z) = j • (d • z) := by
  rw [nsmul_eq_mul d (j • z), nsmul_eq_mul j z, nsmul_eq_mul j (d • z), nsmul_eq_mul d z]
  ring

/-- One fixed clearing denominator works for all exponents `j·z`,
`1 ≤ j ≤ m`. -/
lemma exists_algebraicInt_scalar_all {z : ℂ} (hz : IsAlgebraic ℚ z) (m : ℕ) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ j ∈ Finset.Icc 1 m, IsIntegral ℤ (d • (j • z)) := by
  obtain ⟨d, hd0, hd⟩ := exists_algebraicInt_scalar hz
  refine ⟨d, hd0, ?_⟩
  intro j hj
  rw [nsmul_comm_nsmul d j z]
  exact IsIntegral.nsmul hd j




/-! ## 11.  Corrected roadmap for the arithmetic step (supersedes §8/§8b)

**The pinned targets of §8/§8b are mathematically unsound and must not be
implemented as stated.**  The relation available from algebraicity of
`β = cexp z` is the *direct* exponential relation
`Σⱼ bⱼ·cexp(j•z) = 0` (coefficients `bⱼ = q.coeff j` of the minimal
polynomial of `β`; `relation_of_aeval` §6).  `exponent_identity` §6 turns it
into `Σⱼ bⱼ·F(j•z) = −Σⱼ bⱼ·P(auxPoly z m p)(j•z)` — an identity at the
*points* `j•z`.  But the arithmetic objects of §8/§8b are the conjugate
*trace sums* `Tⱼ = Σ_{w∈conjRoots(j•z)} F(w)`; the pinned identity of item
(2J), `Σⱼ bⱼ·Tⱼ = −Σⱼ bⱼ·P(auxPoly z m p)(j•z)`, would require `Tⱼ = F(j•z)`
for every `j`, i.e. `conjRoots(j•z) = {j•z}` — false whenever `j•z` is not
rational (e.g. `z = √2`).  No conjugate-symmetric relation
`Σⱼ bⱼ·(Σ_{w∈conjRoots(j•z)} e^w) = 0` follows from the direct one (the
exponentials of the conjugates of `j•z` are new complex numbers unrelated to
`cexp(j•z)`), so items (2j),(20),(2J) — and the trace object `traceF` §9 —
are *not* the arithmetic of the direct-Lindemann contradiction.

**The correct classical structure** (this is the roadmap; source:
Lindemann–Weierstrass as in Wikipedia / Lang / Baker, restricted to the
`m = n` corner of Theorem C of CDT):

*Step 0 (reduction).*  `Transcendental ℚ (cexp z)` for algebraic `z ≠ 0`
follows from the **integer-coefficient linear-independence lemma
(Lemma B)**: if `γ₁,…,γₙ` are distinct algebraic numbers and `b₁,…,bₙ ∈ ℤ`
are not all zero then `Σₖ bₖ·e^{γₖ} ≠ 0`.  Indeed an algebraic `β = cexp z`
with minimal polynomial `q` gives `Σⱼ bⱼ·e^{j•z} = 0` over the *distinct*
algebraic exponents `j•z` (`z ≠ 0`), with `b₀ = q.eval 0 ≠ 0`.

*Step 1 (Lemma A = orbit relations).*  Lemma B is proved from the
**orbit-relation lemma (Lemma A)**: if the exponents are grouped into
classes that are full `ℚ`-conjugacy orbits (`conjRoots`-classes; two classes
are equal or disjoint — `conjRoots_eq_of_mem_both` below — and a nonzero
number's orbit avoids `0` — `zero_not_mem_conjRoots`) and the (integer)
coefficient is *constant on each class*, then the relation is trivial.
Lemma A's proof: with `H = ∏` over all exponents `(x−α)` (`∈ ℚ[x]`, by
Galois closure) and `ℓ` clearing denominators to algebraic integers, define
`fᵢ = ℓ^(n·p)·Hᵖ/(x−αᵢ)` (each exponent keeps multiplicity `p`, the
`i`-th loses one power).  For `Jᵢ = Σₖ βₖ·P(fᵢ,αₖ)` (βₖ = the class
coefficient of `αₖ`) the relation makes `Jᵢ = −ΣⱼΣₖ βₖ·fᵢ⁽ʲ⁾(αₖ)`; the
arithmetic (`fᵢ⁽ʲ⁾(αₖ)` vanishes for `j < p` except the diagonal
`j = p−1, k = i`, where it is `(p−1)!·ℓᵖ·δᵢᵖ` with `δᵢ = ∏_{k≠i}(ℓαᵢ−ℓαₖ)`
a nonzero algebraic integer) makes each `Jᵢ` a nonzero algebraic integer
divisible by `(p−1)!`; the *symmetric-function step* (expansion
`fᵢ(x) = Σₘ gₘ(αᵢ)·xᵐ`, `gₘ ∈ ℤ[y]` independent of `i`, from
`fᵢ = ℓ^(n·p)·(H(x)−H(αᵢ))/(x−αᵢ)`; then each class-sum
`Σ_{k∈class} fᵢ⁽ʲ⁾(αₖ) = Σₘ gₘ⁽ʲ⁾(αᵢ)·(power sum over the class)` with
rational power sums by `trace_rat_poly`) gives `Jᵢ = G(αᵢ)` for one
`G ∈ ℚ[x]` independent of `i`; hence `∏ᵢ Jᵢ = ∏ᵢ G(αᵢ) ∈ ℚ` (rational by
`norm_rat_poly`, since the exponents partition into `conjRoots`-classes), a
nonzero algebraic integer divisible by `(p−1)!ⁿ`, so
`|∏ᵢ Jᵢ| ≥ (p−1)!ⁿ`; while the analytic bound (the `P` machinery of
Hermite §1/§5e applied to the family `fᵢ`, exactly as `P_auxPoly_bound`
§5b) gives `|Jᵢ| ≤ Cᵖ` uniformly, so `|∏ᵢ Jᵢ| ≤ C^(n·p) < (p−1)!ⁿ` for
large primes — contradiction.

*Step 2 (Lemma B from Lemma A, tailored to exponents `j•z`).*  Either the
general `S_N`-product symmetrization (Wikipedia Lemma B), or the
conjugate-product trick specialised to our family: for the embeddings
`σ₁=id,…,σ_r` of `ℚ(z)` (so `zᵢ = σᵢ(z)` are the distinct conjugates of
`z`), `0 = ∏ᵢ (Σⱼ bⱼ·e^{j•zᵢ})` expands to a *finite integer* linear
combination of `e^{Σᵢ jᵢ zᵢ}` which is *constant on each Galois orbit of the
exponents `Σᵢ jᵢ·zᵢ`* (permutation of the `zᵢ`'s only relabels the
multi-indices `(jᵢ)`), i.e. a Lemma-A orbit relation; a lexicographic
(maximal-exponent) argument shows at least one grouped coefficient is
nonzero, so Lemma A applies — contradiction.  This also explains why
§1–§10 of this file (the `P`/analytic machinery, the `Hermite` factorial
arithmetic, `sumIDeriv`, `P_auxPoly_bound`-type estimates, and the conjugate
splitting facts) survive: Lemma A's analytic side *is* that machinery, and
Lemma A's arithmetic side is the factorial/divisibility arithmetic at
algebraic-integer points plus the trace/norm rationality already committed
to the Commons (`trace_rat_poly`, `norm_rat_poly`) and the conjRoots
partition facts proved below.

*Step 3 (corollaries).*  From `Transcendental ℚ (cexp z)` (algebraic
`z ≠ 0`): `Transcendental ℚ (log q)` for rational `q ∉ {0,1}` (apply with
`z = log q`, since `cexp(log q) = q` is algebraic), hence the `m = n`
corner `Irrational (log(1+1/m)²)` of `cdt_theoremC_irr`
(`log(1+1/m) ≠ 0` by `Helpers.log_one_add_inv_int_ne_zero`); and
`Transcendental ℚ π` (if `π` algebraic, apply with `z = i·π`, since
`cexp(iπ) = −1`).
-/

/-- A nonzero algebraic number has no zero among its conjugates. -/
lemma zero_not_mem_conjRoots {x : ℂ} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    0 ∉ conjRoots x := by
  unfold conjRoots
  rw [Polynomial.mem_aroots]
  intro h
  rcases h with ⟨hnz, hz⟩
  have hxI : IsIntegral ℚ x := (isAlgebraic_iff_isIntegral).mp hx
  have hc0 : (minpoly ℚ x).coeff 0 = 0 := by
    have hA := coeff_zero_eq_aeval_zero' (R := ℚ) (A := ℂ) (p := minpoly ℚ x)
    have hh : aeval (0 : ℂ) (minpoly ℚ x) = 0 := by simpa using hz
    exact (algebraMap ℚ ℂ).injective (by simpa [hA] using hh)
  have hXdvd : X ∣ (minpoly ℚ x) := by
    rw [Polynomial.X_dvd_iff]
    exact hc0
  obtain ⟨h, hmin⟩ := hXdvd
  have hh0 : h ≠ 0 := by
    intro hh
    apply (minpoly.ne_zero hxI)
    rw [hmin, hh]
    simp
  have hxh : Polynomial.aeval x h = 0 := by
    have hxmin : Polynomial.aeval x (minpoly ℚ x) = 0 := minpoly.aeval ℚ x
    rw [hmin, Polynomial.aeval_mul, Polynomial.aeval_X] at hxmin
    exact (mul_eq_zero.mp hxmin).resolve_left hx0
  have hdvd : minpoly ℚ x ∣ h := minpoly.dvd ℚ x hxh
  have hdeg : h.natDegree < (minpoly ℚ x).natDegree := by
    rw [hmin, Polynomial.natDegree_X_mul hh0]
    omega
  have hdegle : (minpoly ℚ x).natDegree ≤ h.natDegree := by
    exact Polynomial.natDegree_le_of_dvd hdvd hh0
  omega

/-- Conjugate classes that share an element are equal (conjugacy partitions
the algebraic numbers into classes that are equal or disjoint). -/
lemma conjRoots_eq_of_mem_both {z w u : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w)
    (huz : u ∈ conjRoots z) (huw : u ∈ conjRoots w) : conjRoots z = conjRoots w := by
  unfold conjRoots at huz huw ⊢
  have hzI : IsIntegral ℚ z := (isAlgebraic_iff_isIntegral).mp hz
  have hwI : IsIntegral ℚ w := (isAlgebraic_iff_isIntegral).mp hw
  have huz' : aeval u (minpoly ℚ z) = 0 := (Polynomial.mem_aroots.mp huz).2
  have huw' : aeval u (minpoly ℚ w) = 0 := (Polynomial.mem_aroots.mp huw).2
  have hu_alg : IsAlgebraic ℚ u := ⟨minpoly ℚ z, minpoly.ne_zero hzI, huz'⟩
  have huI : IsIntegral ℚ u := (isAlgebraic_iff_isIntegral).mp hu_alg
  have hz_eq : minpoly ℚ z = minpoly ℚ u :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hzI) huz' (minpoly.monic hzI)
  have hw_eq : minpoly ℚ w = minpoly ℚ u :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hwI) huw' (minpoly.monic hwI)
  rw [hz_eq, ← hw_eq]

/-- The conjugate class of zero is the singleton `{0}`. -/
lemma conjRoots_zero : conjRoots (0 : ℂ) = {0} := by
  unfold conjRoots
  rw [minpoly.zero]
  simp [Polynomial.aroots_def]


end Submission.Transcendence
