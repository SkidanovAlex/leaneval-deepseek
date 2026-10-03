/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs
import Submission.Work.Peluse.Ulower.boxSumPow_split

/-!
# The concatenation chapter `Work.Peluse.SwapC`

Vocabulary of the regime-swap + dense-concatenation route to `∀ t ≥ 1, lemma51P t`
(design: `Submission/Work/Peluse/P2P3_LEAD.md`); the vocabulary itself is frozen in
`Submission/Work/Peluse/Holds/SwapDefs.lean` (namespace `Work.Peluse.LadderP.Swap`):
`pdir`, `pbox`, `pboxSum`, `avg`, `denseAvg`, `slotSet`, `slotCard`, `slotAt`, `genPair`.

This file adds the two layers every node of the chapter is phrased against:

* the slot direction `pdir q₁ q₂ m = q₁(m₁+1) − q₂(m₂+1)` and its *raw* case `q₂ = 0`
  (`pdir_zero_right`, `pdir_zero_left`);
* the uniform average `avg` and its plumbing (`avg_nonneg`, `avg_le_of_forall_le`,
  `le_of_le_avg`, `avg_mul_card`, `avg_const`);
* the **multiset box sum** `mCubeSum`: `pboxSum` with the slot multisets `q₁ k[M] − q₂ k[M]`
  abstracted to an arbitrary finite index type `X` and an arbitrary direction map
  `ν k : X → ℤ`.  The bridge is `pboxSum_eq_mCubeSum` (`X := Fin M × Fin M`,
  `ν k m := pdir (q₁ k) (q₂ k) m`) and its norm form `pbox_eq_mCubeSum`.

The two helpers of the chapter, `pbox_peel` (the inductive formula for `pboxSum`) and
`pboxSum_real_nonneg` (`pboxSum` is a nonnegative real for `1 ≤ d`), are stated as separate
nodes, as are KKL Lemma 6.1 (`concatStep`) and KKL Proposition 6.2 (`concatAll`).

## Main definitions

* `Work.Peluse.SwapC.mCubeSum`

## Main results

* `Work.Peluse.SwapC.pboxSum_eq_mCubeSum`, `Work.Peluse.SwapC.pbox_eq_mCubeSum`
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## 0. The direction of a slot -/

/-- The slot `q₁[M] − q₂[M]` has a *raw* degeneration: with `q₂ = 0` the direction does not
depend on the second part of the index. -/
lemma pdir_zero_right (q : ℤ) {M : ℕ} (m : Fin M × Fin M) :
    pdir q 0 m = q * (((m.1 : ℕ) : ℤ) + 1) := by
  simp [pdir]

/-- `pdir` with the first coefficient zero. -/
lemma pdir_zero_left (q : ℤ) {M : ℕ} (m : Fin M × Fin M) :
    pdir 0 q m = -(q * (((m.2 : ℕ) : ℤ) + 1)) := by
  simp [pdir]

/-- The raw slot, on a plain pair. -/
lemma pdir_zero_right_pair (q : ℤ) {M : ℕ} (a b : Fin M) :
    pdir q 0 (a, b) = q * (((a : ℕ) : ℤ) + 1) := by
  simp [pdir]

/-- The definition of `pdir`, unfolded. -/
lemma pdir_def (q₁ q₂ : ℤ) {M : ℕ} (m : Fin M × Fin M) :
    pdir q₁ q₂ m = q₁ * (((m.1 : ℕ) : ℤ) + 1) - q₂ * (((m.2 : ℕ) : ℤ) + 1) := rfl

/-! ## 1. The uniform average `avg` -/

lemma avg_eq_inv_card_mul {I : Type} [Fintype I] (F : I → ℝ) :
    avg F = ((Fintype.card I : ℝ))⁻¹ * ∑ i, F i := rfl

lemma avg_nonneg {I : Type} [Fintype I] {F : I → ℝ} (h : ∀ i, 0 ≤ F i) : 0 ≤ avg F := by
  rw [avg]
  exact mul_nonneg (inv_nonneg.mpr (by positivity)) (Finset.sum_nonneg fun i _ => h i)

lemma avg_const {I : Type} [Fintype I] [Nonempty I] (c : ℝ) : avg (fun _ : I => c) = c := by
  have hc : ((Fintype.card I : ℝ)) ≠ 0 := by
    have : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  rw [avg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

lemma avg_le_of_forall_le {I : Type} [Fintype I] [Nonempty I] {F : I → ℝ} {c : ℝ}
    (h : ∀ i, F i ≤ c) : avg F ≤ c := by
  have hc : (0 : ℝ) < (Fintype.card I : ℝ) := by
    have : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast this
  have h1 : ∑ i, F i ≤ (Fintype.card I : ℝ) * c := by
    calc ∑ i, F i ≤ ∑ _i : I, c := Finset.sum_le_sum fun i _ => h i
      _ = (Fintype.card I : ℝ) * c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [avg]
  calc ((Fintype.card I : ℝ))⁻¹ * ∑ i, F i
      ≤ ((Fintype.card I : ℝ))⁻¹ * ((Fintype.card I : ℝ) * c) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = c := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

lemma avg_lt_of_forall_lt {I : Type} [Fintype I] [Nonempty I] {F : I → ℝ} {c : ℝ}
    (h : ∀ i, F i < c) : avg F < c := by
  have hc : (0 : ℝ) < (Fintype.card I : ℝ) := by
    have : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast this
  have h1 : ∑ i, F i < (Fintype.card I : ℝ) * c := by
    have : ∑ i, F i < ∑ _i : I, c := by
      refine Finset.sum_lt_sum (fun i _ => le_of_lt (h i)) ?_
      obtain ⟨i⟩ := ‹Nonempty I›
      exact ⟨i, Finset.mem_univ i, h i⟩
    calc ∑ i, F i < ∑ _i : I, c := this
      _ = (Fintype.card I : ℝ) * c := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [avg]
  calc ((Fintype.card I : ℝ))⁻¹ * ∑ i, F i
      < ((Fintype.card I : ℝ))⁻¹ * ((Fintype.card I : ℝ) * c) :=
        mul_lt_mul_of_pos_left h1 (by positivity)
    _ = c := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul]

/-- From a lower bound for the average we get a lower bound for one term. -/
lemma le_of_le_avg {I : Type} [Fintype I] [Nonempty I] {F : I → ℝ} {δ : ℝ}
    (h : δ ≤ avg F) : ∃ i, δ ≤ F i := by
  by_contra hcon
  have hcon' : ∀ i, F i < δ := fun i => lt_of_not_ge (fun hle => hcon ⟨i, hle⟩)
  exact absurd h (not_le.mpr (avg_lt_of_forall_lt hcon'))

/-- The average, multiplied through by the number of terms. -/
lemma avg_mul_card {I : Type} [Fintype I] [Nonempty I] (F : I → ℝ) :
    avg F * (Fintype.card I : ℝ) = ∑ i, F i := by
  have hc : ((Fintype.card I : ℝ)) ≠ 0 := by
    have : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
    exact_mod_cast Nat.pos_iff_ne_zero.mp this
  calc avg F * (Fintype.card I : ℝ)
      = (((Fintype.card I : ℝ))⁻¹ * (Fintype.card I : ℝ)) * ∑ i, F i := by
        rw [avg]; ring
    _ = ∑ i, F i := by rw [inv_mul_cancel₀ hc, one_mul]

/-- `δ ≤ avg F`, multiplied through by the number of terms. -/
lemma mul_card_le_sum {I : Type} [Fintype I] [Nonempty I] {F : I → ℝ} {δ : ℝ}
    (h : δ ≤ avg F) : δ * (Fintype.card I : ℝ) ≤ ∑ i, F i := by
  rw [← avg_mul_card F]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- `avg` is monotone. -/
lemma avg_le_avg {I : Type} [Fintype I] [Nonempty I] {F G : I → ℝ} (h : ∀ i, F i ≤ G i) :
    avg F ≤ avg G := by
  rw [avg, avg]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i) (by positivity)

/-- `avg` over a product is the iterated `avg`. -/
lemma avg_prod {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (F : A × B → ℝ) : avg F = avg (fun a : A => avg (fun b : B => F (a, b))) := by
  have h1 : avg F
      = ((Fintype.card A : ℝ) * (Fintype.card B : ℝ))⁻¹ * ∑ a : A, ∑ b : B, F (a, b) := by
    rw [avg, Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul]
  have h2 : avg (fun a : A => avg (fun b : B => F (a, b)))
      = ((Fintype.card A : ℝ))⁻¹ * ∑ a : A, ((Fintype.card B : ℝ))⁻¹ * ∑ b : B, F (a, b) := by
    rw [avg]
    rfl
  rw [h1, h2]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_inv_rev]
  ring

/-! ## 2. The multiset box sum -/

/-- The **multiset box sum** of order `d` over the index type `X` with directions
`ν k : X → ℤ`: the cube average `(1/|S|) (|X|^{-2})^d ∑_{h,h' ∈ X^d} ∑_x ∏_ω C^{|ω|} F_ω (x + …)`.
It is `pboxSum` with the slot multisets `q₁ k[M] − q₂ k[M]` abstracted away; see
`pboxSum_eq_mCubeSum`. -/
def mCubeSum (d : ℕ) (X : Type) [Fintype X] (ν : Fin d → X → ℤ) (S : Finset ℤ)
    (F : (Fin d → Bool) → ℤ → ℂ) : ℂ :=
  ((S.card : ℂ))⁻¹ * (((Fintype.card X : ℂ))⁻¹) ^ (2 * d) *
    ∑ h : Fin d → X, ∑ h' : Fin d → X,
      ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (F ω (x + cornerShift (fun k => ν k (h k)) (fun k => ν k (h' k)) ω))

/-- `pboxSum` is the multiset box sum over `X = Fin M × Fin M` with the slot direction
`m ↦ pdir (q₁ k) (q₂ k) m`. -/
lemma pboxSum_eq_mCubeSum (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    pboxSum d q₁ q₂ M S f
      = mCubeSum d (Fin M × Fin M) (fun k m => pdir (q₁ k) (q₂ k) m) S (fun _ => f) := by
  have hcard : (Fintype.card (Fin M × Fin M) : ℂ) = (M : ℂ) ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring
  have hbase : (((M : ℂ) ^ 4)⁻¹) = (((M : ℂ) ^ 2)⁻¹) ^ 2 := by
    rw [show (M : ℂ) ^ 4 = ((M : ℂ) ^ 2) ^ 2 by ring, inv_pow]
  have hpow : (((M : ℂ) ^ 4)⁻¹) ^ d = (((M : ℂ) ^ 2)⁻¹) ^ (2 * d) := by
    rw [hbase, ← pow_mul]
  simp only [pboxSum, mCubeSum, hcard, hpow]

/-- The norm form of `pboxSum_eq_mCubeSum`. -/
lemma pbox_eq_mCubeSum (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    pbox d q₁ q₂ M S f
      = ‖mCubeSum d (Fin M × Fin M) (fun k m => pdir (q₁ k) (q₂ k) m) S (fun _ => f)‖ := by
  rw [pbox, pboxSum_eq_mCubeSum]

/-- `pbox` is a modulus, hence nonnegative. -/
lemma pbox_nonneg (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    0 ≤ pbox d q₁ q₂ M S f :=
  norm_nonneg _

/-- `pbox` unfolded. -/
lemma pbox_eq_norm (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    pbox d q₁ q₂ M S f = ‖pboxSum d q₁ q₂ M S f‖ := rfl

/-! ## 3. The iterated symmetric difference

The object produced by peeling `k` slots one after another: the `Δ'`-differences applied in the
order in which the peels consume the slots (`sh 0` outermost), matching `boxSumPow_split`'s
convention.  It is the conjugate of `Work.Peluse.Ulower.iterDelta` (whose step is
`F (· + h) * star (F (· + h'))`), and `pbox` is unchanged by conjugation; the point of having it
here is that the peel identity is then a *single* statement. -/

/-- `Δ'_{(sh 0)}(Δ'_{(sh 1)}(⋯ Δ'_{sh (k-1)} F))`, first pair outermost. -/
def iterDeltaP : (k : ℕ) → (Fin k → ℤ × ℤ) → (ℤ → ℂ) → (ℤ → ℂ) :=
  Nat.rec (motive := fun k => (Fin k → ℤ × ℤ) → (ℤ → ℂ) → (ℤ → ℂ))
    (fun _ F => F)
    (fun k ih sh F => fun x =>
      star (ih (fun i => sh i.succ) F (x + (sh 0).1)) * ih (fun i => sh i.succ) F (x + (sh 0).2))

lemma iterDeltaP_zero (sh : Fin 0 → ℤ × ℤ) (F : ℤ → ℂ) : iterDeltaP 0 sh F = F := rfl

lemma iterDeltaP_succ (k : ℕ) (sh : Fin (k + 1) → ℤ × ℤ) (F : ℤ → ℂ) :
    iterDeltaP (k + 1) sh F = fun x =>
      star (iterDeltaP k (fun i => sh i.succ) F (x + (sh 0).1)) *
        iterDeltaP k (fun i => sh i.succ) F (x + (sh 0).2) := rfl

/-- One step of `iterDeltaP` is `DeltaP`. -/
lemma iterDeltaP_one (sh : Fin 1 → ℤ × ℤ) (F : ℤ → ℂ) :
    iterDeltaP 1 sh F = DeltaP (sh 0).1 (sh 0).2 F := by
  funext x
  rw [iterDeltaP_succ, iterDeltaP_zero]
  rfl

/-- `iterDeltaP` peels off its first pair: the first pair is applied outermost. -/
lemma iterDeltaP_succ_eq (k : ℕ) (sh : Fin (k + 1) → ℤ × ℤ) (F : ℤ → ℂ) :
    iterDeltaP (k + 1) sh F
      = DeltaP (sh 0).1 (sh 0).2 (iterDeltaP k (fun i => sh i.succ) F) := by
  funext x
  rw [iterDeltaP_succ]
  rfl

/-! ## 4. The asymmetric cube term

`∏_{ω : Fin d → Bool} C^{|ω|} f (y + ω · dvec)`, i.e. the cube term with the lower corner at `y`;
`Work.Peluse.BoxNorm` uses the same object (with the two shift tuples identified).  KKL's
expansions are phrased with it: `pboxSum_asym_eq` rewrites the (symmetric) box sum into it, and
`asymCube_eq_mul` splits off the `ω = 0` corner, which is the point at which the Cauchy–Schwarz
inequality in the base variable is applied in `concatStep`. -/

/-- The asymmetric cube term of order `d` at base `y` with increment tuple `dvec`. -/
def asymCube {d : ℕ} (dvec : Fin d → ℤ) (f : ℤ → ℂ) (y : ℤ) : ℂ :=
  ∏ ω : Fin d → Bool, (star^[weight ω]) (f (y + cornerShift dvec (fun _ => 0) ω))

lemma asymCube_zero (dvec : Fin 0 → ℤ) (f : ℤ → ℂ) (y : ℤ) : asymCube dvec f y = f y := by
  rw [asymCube]
  simp [cornerShift, weight]

/-- The `ω = 0` corner of the asymmetric cube term is `f y`; the rest is the product over the
nonzero sign patterns. -/
lemma asymCube_eq_mul (d : ℕ) (dvec : Fin d → ℤ) (f : ℤ → ℂ) (y : ℤ) :
    asymCube dvec f y
      = f y * ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
          (star^[weight ω]) (f (y + cornerShift dvec (fun _ => 0) ω)) := by
  rw [asymCube, ← Finset.prod_erase_mul Finset.univ
    (fun ω => (star^[weight ω]) (f (y + cornerShift dvec (fun _ => 0) ω)))
    (Finset.mem_univ (0 : Fin d → Bool))]
  have h0 : (star^[weight (0 : Fin d → Bool)]) (f (y + cornerShift dvec (fun _ => 0) 0)) = f y := by
    have hw : weight (0 : Fin d → Bool) = 0 := by
      rw [weight]; simp
    have hc : cornerShift dvec (fun _ => 0) (0 : Fin d → Bool) = 0 := by
      rw [cornerShift]; simp
    rw [hw, hc, Function.iterate_zero_apply, add_zero]
  rw [h0, mul_comm]

/-- The gauge of the asymmetric cube term: everything except the root factor `f y`. -/
def asymGauge {d : ℕ} (dvec : Fin d → ℤ) (f : ℤ → ℂ) (y : ℤ) : ℂ :=
  ∏ ω ∈ Finset.univ.erase (0 : Fin d → Bool),
    (star^[weight ω]) (f (y + cornerShift dvec (fun _ => 0) ω))

lemma asymCube_eq_gauge (d : ℕ) (dvec : Fin d → ℤ) (f : ℤ → ℂ) (y : ℤ) :
    asymCube dvec f y = f y * asymGauge dvec f y := by
  rw [asymCube_eq_mul, asymGauge]

/-- The **gauge of the asymmetric form of `pboxSum`**: `pboxSum` is `∑'_y f y · pboxGauge y`
(`pboxGauge_tsum`), and this gauge is the object to which the Cauchy–Schwarz inequality in the base
variable is applied in `concatStep` (KKL Lemma 6.1). -/
def pboxGauge (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) (y : ℤ) : ℂ :=
  (((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d) *
    ∑ H : Fin d → Fin M × Fin M, ∑ H' : Fin d → Fin M × Fin M,
      asymGauge (fun k => pdir (q₁ k) (q₂ k) (H k) - pdir (q₁ k) (q₂ k) (H' k)) f y

end

end Work.Peluse.SwapC
