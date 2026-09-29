import Mathlib
import Submission.CDT.OrdAtT
import Submission.CDT.EulerIndicial
import Submission.Commons.Algebra.Polynomial.euler_cascade_dvd

/-!
# The Frobenius local theorem for a linear differential operator

Setting: `f ∈ K(X)` is a nonzero rational function, `α ∈ K`, `N = ord_α f`.  For
a polynomial coefficient `A j = z^{(e j)} · B j` (`z = X - C α`, `e j : ℕ`,
`B j ∈ K[X]`), the operator `∑_j C(A j)·(d/dx)^{(e j)} f` has order exactly `N`
at `α`, provided the indicial value
`σ = ∑_j (N)_{e j} · B j(α)` is nonzero.

The mechanism: the Frobenius cascade (`Commons.Algebra.Polynomial.euler_cascade_dvd`)
gives `ord_α (z^j f^{(j)} - (N)_j f) ≥ N + 1`; summing with the regular
coefficients `B j` and extracting `σ` as the leading term reduces everything to
the strict-dominance rule for `ordAtT`.

Exported statements:
* `residual_bound` — the cascade bound `ord_α(z^j f^{(j)} - (N)_j f) ≥ N+1`
  for `f = p/q` (the concrete form, via `euler_cascade_dvd`);
* `ordAtT_iterate_dRat_ge` — `ord_α f^{(j)} ≥ N - j`;
* `frobenius_tie` — the exact-order theorem above (the "tie case");
* `frobenius_order_ge` — the one-sided bound `ord_α(∑_j A_j f^{(e j)}) ≥ M`,
  valid with no indicial hypothesis.
-/

open Classical

noncomputable section

namespace Submission.CDT

open Polynomial

set_option linter.unusedSimpArgs false

variable {K : Type*} [Field K]

/-- The "residue" of the Frobenius cascade: `z^j f^{(j)} - (N)_j f`.  Its order
at `α` is at least `N + 1` when `N = ord_α f`. -/
def resFun (α : K) (f : RatFunc K) (N : ℤ) (j : ℕ) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j) * (dRat^[j] f)
    - algebraMap (Polynomial K) (RatFunc K)
        (Polynomial.C ((fallFact N j : ℤ) : K)) * f

/-- The `min`-type multiplicative lower bound for `ordAtT`. -/
lemma ordAtT_mul_ge {α : K} {x y : RatFunc K} {m n : ℤ}
    (hx : (m : WithTop ℤ) ≤ ordAtT α x) (hy : (n : WithTop ℤ) ≤ ordAtT α y) :
    ((m + n : ℤ) : WithTop ℤ) ≤ ordAtT α (x * y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  rw [ordAtT_mul α hx0 hy0, ordAtT_of_ne hx0, ordAtT_of_ne hy0, ← WithTop.coe_add,
    WithTop.coe_le_coe]
  have hx' : m ≤ ordAt α x := by
    rw [ordAtT_of_ne hx0, WithTop.coe_le_coe] at hx; exact hx
  have hy' : n ≤ ordAt α y := by
    rw [ordAtT_of_ne hy0, WithTop.coe_le_coe] at hy; exact hy
  linarith

/-- Multiplying by a polynomial coefficient does not lower the order. -/
lemma le_ordAtT_algebraMap_mul {α : K} {c : Polynomial K} {x : RatFunc K} {N : ℤ}
    (h : (N : WithTop ℤ) ≤ ordAtT α x) :
    (N : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) c * x) := by
  rcases eq_or_ne c 0 with h0 | h0
  · rw [h0, map_zero, zero_mul]; simp
  · have h0' : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) c) := by
      rw [ordAtT_algebraMap h0]; exact_mod_cast Nat.cast_nonneg _
    have hm := ordAtT_mul_ge h0' h
    simpa using hm

/-- `ordAtT` of the linear factor `X - C α` is `1`. -/
lemma ordAtT_X_sub_C (α : K) :
    ordAtT α (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)) = 1 := by
  have hz : (Polynomial.X - Polynomial.C α : Polynomial K) ≠ 0 := Polynomial.X_sub_C_ne_zero α
  rw [ordAtT_algebraMap hz, Polynomial.rootMultiplicity_X_sub_C_self]
  rfl

/-- The linear factor is nonzero in `K(X)`. -/
lemma algebraMap_X_sub_C_ne_zero (α : K) :
    algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α) ≠ 0 := by
  intro h
  exact Polynomial.X_sub_C_ne_zero α ((RatFunc.algebraMap_injective K) (by rw [h, map_zero]))

/-- `ordAtT` of a power of the linear factor. -/
lemma ordAtT_X_sub_C_pow (α : K) (n : ℕ) :
    ordAtT α (algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ n))
      = ((n : ℤ) : WithTop ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hz : (((Polynomial.X - Polynomial.C α) ^ n) : Polynomial K) ≠ 0 :=
      pow_ne_zero n (Polynomial.X_sub_C_ne_zero α)
    rw [ordAtT_algebraMap hz, Polynomial.rootMultiplicity_X_sub_C_pow]

/-- `ordAt α (algebraMap (X - C α)) = 1`. -/
lemma ordAt_X_sub_C (α : K) : ordAt α (algebraMap (Polynomial K) (RatFunc K)
    (Polynomial.X - Polynomial.C α)) = 1 := by
  rw [ordAt_algebraMap, Polynomial.rootMultiplicity_X_sub_C_self]; norm_num

/-- The divisibility-to-order transfer: if `(X - C α)^m ∣ u` then
`algebraMap u / algebraMap v` has order at least `m - ord_α v`. -/
lemma ordAtT_div_ge {α : K} {u v : Polynomial K} (hv : v ≠ 0) {m : ℕ}
    (hu : (Polynomial.X - Polynomial.C α) ^ m ∣ u) :
    ((((m : ℤ) - (Polynomial.rootMultiplicity α v : ℤ)) : ℤ) : WithTop ℤ)
      ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) u
          / algebraMap (Polynomial K) (RatFunc K) v) := by
  rcases eq_or_ne u 0 with h0 | h0
  · rw [h0, map_zero, zero_div]; simp
  have hv' : algebraMap (Polynomial K) (RatFunc K) v ≠ 0 := by simpa using hv
  have hu' : algebraMap (Polynomial K) (RatFunc K) u ≠ 0 := by simpa using h0
  rw [ordAtT_of_ne (div_ne_zero hu' hv'), ordAt_div α hu' hv', ordAt_algebraMap,
    ordAt_algebraMap]
  rw [WithTop.coe_le_coe]
  have hm : m ≤ Polynomial.rootMultiplicity α u := by
    rw [Polynomial.le_rootMultiplicity_iff h0]; exact hu
  have hmZ : (m : ℤ) ≤ (Polynomial.rootMultiplicity α u : ℤ) := by exact_mod_cast hm
  linarith

/-- Root multiplicity of a power (unconditional). -/
lemma rootMultiplicity_pow' {α : K} (q : Polynomial K) (n : ℕ) :
    Polynomial.rootMultiplicity α (q ^ n) = n * Polynomial.rootMultiplicity α q := by
  rcases eq_or_ne q 0 with rfl | hq
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [zero_pow (Nat.pos_iff_ne_zero.mp hn)]; simp
  · induction n with
    | zero => simp
    | succ m ih =>
        rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero m hq) hq), ih]
        ring

/-- **The Frobenius residual bound.**  For `f = p/q ∈ K(X)` nonzero and
`N = ord_α f`, the residue `z^j f^{(j)} - (N)_j f` has order at least `N + 1`. -/
theorem residual_bound {α : K} {p q : Polynomial K} (hp : p ≠ 0) (hq : q ≠ 0) (j : ℕ) :
    ((((Polynomial.rootMultiplicity α p : ℤ) - (Polynomial.rootMultiplicity α q : ℤ) + 1 : ℤ))
        : WithTop ℤ)
      ≤ ordAtT α (resFun α
          (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q)
          ((Polynomial.rootMultiplicity α p : ℤ) - (Polynomial.rootMultiplicity α q : ℤ)) j) := by
  set N : ℤ := (Polynomial.rootMultiplicity α p : ℤ) - (Polynomial.rootMultiplicity α q : ℤ)
    with hNdef
  set F : ℕ → Polynomial K := fun k => Polynomial.C ((fallFact N k : ℤ) : K) with hFdef
  set D : ℕ → Polynomial K := DbN (Polynomial.X - Polynomial.C α) p q F with hDdef
  have hF0 : F 0 = 1 := by simp [hFdef]
  have hFc : ∀ k, (F k).derivative = 0 := by intro k; simp [hFdef]
  have hFrec : ∀ k, F (k + 1) = F k * (Polynomial.C ((N : ℤ) : K) - (k : Polynomial K)) := by
    intro k
    have h1 : ((fallFact N (k + 1) : ℤ) : K)
        = (((fallFact N k : ℤ) : K)) * ((N : K) - (k : K)) := by
      rw [fallFact_succ]; push_cast; ring
    simp only [hFdef]
    rw [h1, ← Polynomial.C_eq_natCast, ← map_sub, ← map_mul]
  have hDrec : ∀ k, D (k + 1) = F k * q ^ k
        * ((Polynomial.X - Polynomial.C α) * (p.derivative * q - p * q.derivative)
            - Polynomial.C ((N : ℤ) : K) * (p * q))
      + (Polynomial.X - Polynomial.C α) * (D k).derivative * q
      - ((k : Polynomial K) + 1) * (Polynomial.X - Polynomial.C α) * (D k) * q.derivative
      - (k : Polynomial K) * (D k) * q := by
    intro k
    rw [hDdef]
    exact DbN_rec (Polynomial.X - Polynomial.C α) (by simp) p q (Polynomial.C ((N : ℤ) : K))
      F hF0 hFc hFrec k
  have hDexpl : ∀ k, D k = (Polynomial.X - Polynomial.C α) ^ k
        * (Nat.rec (motive := fun _ => Polynomial K) p
            (fun m ih => ih.derivative * q - Polynomial.C ((m : ℕ) + 1 : K) * (ih * q.derivative)) k)
      - F k * (p * q ^ k) := by
    intro k
    have hd : dnum p q k = Nat.rec (motive := fun _ => Polynomial K) p
        (fun m ih => ih.derivative * q - Polynomial.C ((m : ℕ) + 1 : K) * (ih * q.derivative)) k := by
      induction k with
      | zero => rfl
      | succ m ih =>
          rw [dnum_succ, ih, Nat.add_one, Nat.cast_succ]
    rw [hDdef]
    unfold DbN
    rw [hd]
  have hdiv : ∀ k, (Polynomial.X - Polynomial.C α)
      ^ (Polynomial.rootMultiplicity α p + k * Polynomial.rootMultiplicity α q + 1) ∣ D k :=
    fun k => Commons.Algebra.Polynomial.euler_cascade_dvd
      (Polynomial.X - Polynomial.C α) (by simp) p q α rfl
      (Polynomial.C ((N : ℤ) : K)) F hF0 hFc hFrec (by rw [hNdef])
      D hDexpl hDrec k
  have hkey : resFun α
        (algebraMap (Polynomial K) (RatFunc K) p / algebraMap (Polynomial K) (RatFunc K) q) N j
      = algebraMap (Polynomial K) (RatFunc K) (D j)
        / algebraMap (Polynomial K) (RatFunc K) (q ^ (j + 1)) := by
    unfold resFun
    rw [dRat_iterate_dnum p q hq j, hDdef]
    unfold DbN
    simp only [hFdef, map_mul, map_sub, map_pow]
    have hq1 : algebraMap (Polynomial K) (RatFunc K) q ≠ 0 := by simpa using hq
    field_simp
    ring
  rw [hkey]
  have hb := ordAtT_div_ge (α := α) (u := D j) (v := q ^ (j + 1)) (pow_ne_zero _ hq) (hdiv j)
  have hqp : Polynomial.rootMultiplicity α (q ^ (j + 1))
      = (j + 1) * Polynomial.rootMultiplicity α q := rootMultiplicity_pow' q (j + 1)
  have hfin : ((((Polynomial.rootMultiplicity α p : ℤ) - (Polynomial.rootMultiplicity α q : ℤ)
          + 1 : ℤ)) : WithTop ℤ)
      = ((((Polynomial.rootMultiplicity α p + j * Polynomial.rootMultiplicity α q + 1 : ℕ) : ℤ)
          - (Polynomial.rootMultiplicity α (q ^ (j + 1)) : ℤ) : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_eq_coe, hqp]
    push_cast
    ring
  rw [hfin]
  exact hb

/-- **The derivative lowers the order by at most `j`.** -/
theorem ordAtT_iterate_dRat_ge {α : K} {f : RatFunc K} (hf : f ≠ 0) {N : ℤ}
    (hN : ordAt α f = N) {j : ℕ}
    (hres : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (resFun α f N j)) :
    ((N - j : ℤ) : WithTop ℤ) ≤ ordAtT α (dRat^[j] f) := by
  rcases eq_or_ne (dRat^[j] f) 0 with h0 | h0
  · rw [h0]; simp
  have hz : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero j (algebraMap_X_sub_C_ne_zero α)
  have hsplit : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j)
        * (dRat^[j] f)
      = resFun α f N j
        + algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((fallFact N j : ℤ) : K)) * f := by
    unfold resFun; ring
  have hCf : (N : WithTop ℤ) ≤ ordAtT α
      (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((fallFact N j : ℤ) : K)) * f) := by
    rcases eq_or_ne ((fallFact N j : ℤ) : K) 0 with h0' | h0'
    · rw [h0', Polynomial.C_0, map_zero, zero_mul]; simp
    · have hC0 : (Polynomial.C ((fallFact N j : ℤ) : K) : Polynomial K) ≠ 0 := by
        rwa [Polynomial.C_ne_zero]
      have hC0' : algebraMap (Polynomial K) (RatFunc K)
          (Polynomial.C ((fallFact N j : ℤ) : K)) ≠ 0 := RatFunc.algebraMap_ne_zero hC0
      rw [ordAtT_mul α hC0' hf, ordAtT_algebraMap hC0,
        rootMultiplicity_C_ne_zero h0' α]
      simp [ordAtT_of_ne hf, hN]
  have hNle : (N : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K)
      ((Polynomial.X - Polynomial.C α) ^ j) * (dRat^[j] f)) := by
    rw [hsplit]
    refine le_trans (le_min ?_ hCf) (ordAtT_add_ge α _ _)
    exact le_trans (by rw [WithTop.coe_le_coe]; omega) hres
  rw [ordAtT_mul α hz h0, ordAtT_X_sub_C_pow, ordAtT_of_ne h0, ← WithTop.coe_add,
    WithTop.coe_le_coe] at hNle
  rw [ordAtT_of_ne h0, WithTop.coe_le_coe]
  omega


/-! ## The Frobenius local theorems -/

/-- **The Frobenius tie case.**  If the indicial value
`σ = ∑_j (N)_{e j} · B_j(α)` is nonzero, then `∑_j C(z^{e j} B_j) · f^{(e j)}`
has order exactly `N` at `α`. -/
theorem frobenius_tie {α : K} {f : RatFunc K} (hf : f ≠ 0) {N : ℤ} (hN : ordAt α f = N)
    {ι : Type*} (s : Finset ι) (B : ι → Polynomial K) (e : ι → ℕ)
    (hres : ∀ j ∈ s, ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (resFun α f N (e j)))
    (hσ : (∑ j ∈ s, (fallFact N (e j) : K) * (B j).eval α) ≠ 0) :
    ordAtT α (∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K)
        ((Polynomial.X - Polynomial.C α) ^ e j * B j) * (dRat^[e j] f)) = (N : WithTop ℤ) := by
  classical
  set Sig : K := ∑ j ∈ s, (fallFact N (e j) : K) * (B j).eval α with hSig
  set Pp : Polynomial K := ∑ j ∈ s, B j * Polynomial.C ((fallFact N (e j) : ℤ) : K) with hPp
  have hPev : Pp.eval α = Sig := by
    rw [hPp, hSig, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C]; ring
  have hσne : Sig ≠ 0 := by rw [hSig]; exact hσ
  obtain ⟨C', hC'⟩ : (Polynomial.X - Polynomial.C α) ∣ Pp - Polynomial.C Sig := by
    rw [← hPev]; exact Polynomial.X_sub_C_dvd_sub_C_eval
  have hterm : ∀ j, algebraMap (Polynomial K) (RatFunc K)
        ((Polynomial.X - Polynomial.C α) ^ e j * B j) * (dRat^[e j] f)
      = algebraMap (Polynomial K) (RatFunc K)
          (B j * Polynomial.C ((fallFact N (e j) : ℤ) : K)) * f
        + algebraMap (Polynomial K) (RatFunc K) (B j) * resFun α f N (e j) := by
    intro j
    unfold resFun
    rw [map_mul, map_mul]
    ring
  have hA : ∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K)
        ((Polynomial.X - Polynomial.C α) ^ e j * B j) * (dRat^[e j] f)
      = algebraMap (Polynomial K) (RatFunc K) Pp * f
        + ∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K) (B j) * resFun α f N (e j) := by
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, ← Finset.sum_mul,
      hPp, ← map_sum]
  have hCs : algebraMap (Polynomial K) (RatFunc K) Pp * f
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C Sig) * f
        + algebraMap (Polynomial K) (RatFunc K) (Pp - Polynomial.C Sig) * f := by
    conv_lhs => rw [show Pp = Polynomial.C Sig + (Pp - Polynomial.C Sig) by ring]
    rw [map_add, add_mul]
  have hsum : ∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K)
        ((Polynomial.X - Polynomial.C α) ^ e j * B j) * (dRat^[e j] f)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C Sig) * f
        + (∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K) (B j) * resFun α f N (e j)
            + algebraMap (Polynomial K) (RatFunc K) (Pp - Polynomial.C Sig) * f) := by
    rw [hA, hCs]; ring
  have hSigval : ordAtT α (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C Sig) * f)
      = (N : WithTop ℤ) := by
    have hC0' : (Polynomial.C Sig : Polynomial K) ≠ 0 := by
      rwa [Polynomial.C_ne_zero]
    rw [ordAtT_mul α (RatFunc.algebraMap_ne_zero hC0') hf, ordAtT_algebraMap hC0',
      rootMultiplicity_C_ne_zero hσne α]
    simp [ordAtT_of_ne hf, hN]
  have hrest : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
      (∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K) (B j) * resFun α f N (e j)
        + algebraMap (Polynomial K) (RatFunc K) (Pp - Polynomial.C Sig) * f) := by
    have h1 : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
        (∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K) (B j) * resFun α f N (e j)) := by
      refine le_ordAtT_finset_sum (fun j hj => ?_)
      have hb : ((0 : ℤ) : WithTop ℤ) ≤ ordAtT α
          (algebraMap (Polynomial K) (RatFunc K) (B j)) := by
        rcases eq_or_ne (B j) 0 with h0 | h0
        · rw [h0, map_zero]; simp
        · rw [ordAtT_algebraMap h0]; exact_mod_cast Nat.cast_nonneg _
      have := ordAtT_mul_ge hb (hres j hj)
      simpa using this
    have h2 : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
        (algebraMap (Polynomial K) (RatFunc K) (Pp - Polynomial.C Sig) * f) := by
      rw [hC']
      have hfN : (N : WithTop ℤ) ≤ ordAtT α f := by rw [ordAtT_of_ne hf, hN]
      have hz1 : (1 : WithTop ℤ) ≤ ordAtT α
          (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)) :=
        le_of_eq (ordAtT_X_sub_C α).symm
      have hstep : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α
          (algebraMap (Polynomial K) (RatFunc K) C' * f
            * algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)) :=
        ordAtT_mul_ge (le_ordAtT_algebraMap_mul (c := C') hfN) hz1
      simpa [map_mul, mul_comm, mul_left_comm, mul_assoc] using hstep
    exact le_trans (le_min h1 h2) (ordAtT_add_ge α _ _)
  rw [hsum]
  exact ordAtT_add_eq_of_le_succ hSigval hrest

/-- **The one-sided bound**: `ord_α(∑_j C(A_j) f^{(e j)}) ≥ M` as soon as
`M ≤ ord_α A_j + (N - e j)` for every `j ∈ s` (with `N = ord_α f`). -/
theorem frobenius_order_ge {α : K} {f : RatFunc K} {N M : ℤ}
    {ι : Type*} (s : Finset ι) (A : ι → Polynomial K) (e : ι → ℕ) (c : ι → ℤ)
    (hA : ∀ j ∈ s, (c j : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) (A j)))
    (hder : ∀ j ∈ s, (((N - (e j) : ℤ)) : WithTop ℤ) ≤ ordAtT α (dRat^[e j] f))
    (hM : ∀ j ∈ s, M ≤ c j + (N - (e j))) :
    (M : WithTop ℤ) ≤ ordAtT α (∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K) (A j)
        * (dRat^[e j] f)) := by
  refine le_ordAtT_finset_sum (fun j hj => ?_)
  have hmul := ordAtT_mul_ge (hA j hj) (hder j hj)
  refine le_trans ?_ hmul
  rw [WithTop.coe_le_coe]
  exact hM j hj

/-- **Exact order of the iterated derivative** for a pole (`N < 0`): the `j`-th
derivative of a rational function of exact order `N < 0` has exact order
`N - j`. -/
theorem ordAtT_iterate_dRat_eq {α : K} [CharZero K] {f : RatFunc K} (hf : f ≠ 0) {N : ℤ}
    (hN : ordAt α f = N) (hNneg : N < 0) {j : ℕ}
    (hres : ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (resFun α f N j)) :
    ordAtT α (dRat^[j] f) = ((N - (j : ℤ) : ℤ) : WithTop ℤ) := by
  have hfz : (fallFact N j : ℤ) ≠ 0 := by
    rw [fallFact, Finset.prod_ne_zero_iff]
    intro i hi
    rw [Finset.mem_range] at hi
    omega
  have hfk : ((fallFact N j : ℤ) : K) ≠ 0 := by
    rw [Int.cast_ne_zero]; exact hfz
  have hx : ordAtT α (algebraMap (Polynomial K) (RatFunc K)
      (Polynomial.C ((fallFact N j : ℤ) : K)) * f) = (N : WithTop ℤ) := by
    have hC0 : (Polynomial.C ((fallFact N j : ℤ) : K) : Polynomial K) ≠ 0 := by
      rwa [Polynomial.C_ne_zero]
    rw [ordAtT_mul α (RatFunc.algebraMap_ne_zero hC0) hf, ordAtT_algebraMap hC0,
      rootMultiplicity_C_ne_zero hfk α]
    simp [ordAtT_of_ne hf, hN]
  have hsplit : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j)
        * (dRat^[j] f)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C ((fallFact N j : ℤ) : K)) * f
        + resFun α f N j := by
    unfold resFun; ring
  have hz : ordAtT α (algebraMap (Polynomial K) (RatFunc K)
      ((Polynomial.X - Polynomial.C α) ^ j) * (dRat^[j] f)) = (N : WithTop ℤ) := by
    rw [hsplit]
    exact ordAtT_add_eq_of_le_succ hx hres
  have hz0 : algebraMap (Polynomial K) (RatFunc K) ((Polynomial.X - Polynomial.C α) ^ j) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero j (Polynomial.X_sub_C_ne_zero α))
  have hfj : dRat^[j] f ≠ 0 := by
    intro h0
    rw [h0, mul_zero, ordAtT_zero] at hz
    exact WithTop.coe_ne_top hz.symm
  rw [ordAtT_mul α hz0 hfj, ordAtT_X_sub_C_pow, ordAtT_of_ne hfj, ← WithTop.coe_add,
    WithTop.coe_eq_coe] at hz
  rw [ordAtT_of_ne hfj, WithTop.coe_eq_coe]
  omega

/-- **The Frobenius unique-minimum case.**  If the "indicial exponents"
`c j + (N - e j)` have a unique minimum at `j₀`, the operator has order exactly
`c j₀ + (N - e j₀)` at `α` (for a pole `N < 0`). -/
theorem frobenius_unique {α : K} [CharZero K] {f : RatFunc K} (hf : f ≠ 0) {N : ℤ}
    (hN : ordAt α f = N) (hNneg : N < 0) {ι : Type*} (s : Finset ι)
    (A : ι → Polynomial K) (e : ι → ℕ) (c : ι → ℤ)
    (hA : ∀ j ∈ s, ordAtT α (algebraMap (Polynomial K) (RatFunc K) (A j)) = (c j : WithTop ℤ))
    (hres : ∀ j ∈ s, ((N + 1 : ℤ) : WithTop ℤ) ≤ ordAtT α (resFun α f N (e j)))
    {j₀ : ι} (hj₀ : j₀ ∈ s)
    (hmin : ∀ j ∈ s, j ≠ j₀ → c j₀ + (N - (e j₀)) < c j + (N - (e j))) :
    ordAtT α (∑ j ∈ s, algebraMap (Polynomial K) (RatFunc K) (A j) * (dRat^[e j] f))
      = (((c j₀ + (N - (e j₀))) : ℤ) : WithTop ℤ) := by
  have hA0 : A j₀ ≠ 0 := by
    intro h0
    have h := hA j₀ hj₀
    rw [h0, map_zero, ordAtT_zero] at h
    exact WithTop.coe_ne_top h.symm
  have hdj := ordAtT_iterate_dRat_eq hf hN hNneg (hres j₀ hj₀)
  have hdj0 : dRat^[e j₀] f ≠ 0 := by
    intro h0
    rw [h0, ordAtT_zero] at hdj
    exact WithTop.coe_ne_top hdj.symm
  refine ordAtT_finset_sum_eq hj₀ ?_ ?_
  · rw [ordAtT_mul α (RatFunc.algebraMap_ne_zero hA0) hdj0, hA j₀ hj₀, hdj,
      ← WithTop.coe_add]
  · intro j hj hjj
    have hAj : (c j : WithTop ℤ) ≤ ordAtT α (algebraMap (Polynomial K) (RatFunc K) (A j)) :=
      le_of_eq (hA j hj).symm
    have hdj' := ordAtT_iterate_dRat_ge hf hN (hres j hj)
    have hmul := ordAtT_mul_ge hAj hdj'
    have hlt := hmin j hj hjj
    refine le_trans ?_ hmul
    rw [WithTop.coe_le_coe]; omega

end Submission.CDT
