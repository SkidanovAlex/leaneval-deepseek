/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.cubeTerm_cons
import Submission.Work.Peluse.BoxNorm.cubeTerm_tsum_finite
import Submission.Work.Peluse.BoxNorm.sum_pairs_star_eq_normSq

/-!
# The box-norm power is a nonnegative real

Peluse's box norm `‖f‖_{□^t_{Q₁,…,Q_t}(S)}` is defined as the `2^t`-th root of the cube average

`(1/|S|) ∑_x E_{h_i,h_i' ∈ Q_i} Δ'_{(h_1,h_1'),…,(h_t,h_t')} f (x)`

(Definition 2.1 of S. Peluse, Forum of Math. Pi **8** (2020), e16).  For this to be a norm, the
averaged quantity must be a *nonnegative real*; this file proves exactly that, i.e. that the complex
number `boxSumPow t Q S f` of `Work.Peluse` is the (real) number `boxNormPow t Q S f = ‖boxSumPow …‖`.

The proof is the "sum of squares" identity behind the Gowers box norm.  Splitting off the first
coordinate of both shift tuples, `h = (a, hs)`, `h' = (b, hs')`, the cube term factorises as

`∏_{ω : Fin (t+1) → Bool} C^{|ω|} f (x + ω·h + (1-ω)·h')
   = Φ(x + b) · conj (Φ(x + a))`,

where `Φ(u) = ∏_{τ : Fin t → Bool} C^{|τ|} f (u + τ·hs + (1-τ)·hs')` is the cube term of one lower
dimension; summing over `a, b ∈ Q 0` and `x` produces `∑_x ‖∑_a Φ(x + a)‖² ≥ 0`.

## Main results

* `Work.Peluse.BoxNorm.rawSum_eq_cubeNormSqSum` : the raw cube average is a sum of squares;
* `Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow` : `boxSumPow t Q S f = boxNormPow t Q S f`.

## Reference

S. Peluse, *Bounds for sets with no polynomial progressions*, Definition 2.1 and Lemma 2.3.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.BoxNorm

noncomputable section

open Finset

namespace Aux

/-- `Fin.consEquiv` as an equality of functions. -/
lemma consEquiv_eq_cons {k : ℕ} {α : Fin (k+1) → Type*} (a : α 0)
    (h : (i : Fin k) → α i.succ) :
    Fin.consEquiv α (a, h) = Fin.cons a h := by
  funext i
  rw [Fin.consEquiv_apply]

/-- Splitting the product over `Fin (k+1) → Bool` into the two faces `ω 0 = false`, `ω 0 = true`. -/
lemma prod_cons_equiv {k : ℕ} (F : ((Fin (k+1)) → Bool) → ℂ) :
    ∏ ω : Fin (k+1) → Bool, F ω = ∏ b : Bool, ∏ τ : Fin k → Bool, F (Fin.cons b τ) := by
  rw [← Equiv.prod_comp (Fin.consEquiv (fun _ : Fin (k+1) => Bool)) F]
  rw [Fintype.prod_prod_type]
  simp only [consEquiv_eq_cons]

/-- Splitting a sum over `(i : Fin (k+1)) → {x // x ∈ Q i}` into its first coordinate `a ∈ Q 0`
and its tail `hs`. -/
lemma sum_cons_equiv {k : ℕ} {Q : Fin (k+1) → Finset ℤ}
    (F : ((i : Fin (k+1)) → {x : ℤ // x ∈ Q i}) → ℂ) :
    ∑ h, F h = ∑ hs : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
      ∑ a : ({y : ℤ // y ∈ Q 0}), F (Fin.cons a hs) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun i => {x : ℤ // x ∈ Q i})) F]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [consEquiv_eq_cons]

/-- The value function of `Fin.cons` on subtypes. -/
lemma cons_val {k : ℕ} {Q : Fin (k+1) → Finset ℤ} (a : {y : ℤ // y ∈ Q 0})
    (hs : (i : Fin k) → {x : ℤ // x ∈ Q i.succ}) :
    (fun i : Fin (k+1) =>
        (Fin.cons (α := fun j : Fin (k+1) => {x : ℤ // x ∈ Q j}) a hs i).1)
      = Fin.cons a.1 (fun i : Fin k => (hs i).1) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Rotating a triple sum so that the last index becomes the first. -/
lemma rotate3_finset {A B X : Type*} [Fintype A] [Fintype B] (I : Finset X)
    (F : A → B → X → ℂ) :
    (∑ a, ∑ b, ∑ x ∈ I, F a b x) = ∑ x ∈ I, ∑ a, ∑ b, F a b x := by
  have h1 : ∀ b, (∑ a, ∑ x ∈ I, F a b x) = ∑ x ∈ I, ∑ a, F a b x := fun b => Finset.sum_comm
  calc ∑ a, ∑ b, ∑ x ∈ I, F a b x
      = ∑ b, ∑ a, ∑ x ∈ I, F a b x := Finset.sum_comm
    _ = ∑ b, ∑ x ∈ I, ∑ a, F a b x := by simp only [h1]
    _ = ∑ x ∈ I, ∑ b, ∑ a, F a b x := Finset.sum_comm
    _ = ∑ x ∈ I, ∑ a, ∑ b, F a b x := by
          refine Finset.sum_congr rfl (fun x _ => Finset.sum_comm)

/-- Brings the two `A`-sums (the first coordinates `a`, `b` of the two shift tuples) to the
inside, past the tail sums and the `x`-sum. -/
lemma reorder_pair {A H X : Type*} [Fintype A] [Fintype H] (I : Finset X)
    (G : H → A → H → A → X → ℂ) :
    (∑ hs, ∑ a, ∑ hs', ∑ b, ∑ x ∈ I, G hs a hs' b x)
      = ∑ hs, ∑ hs', ∑ x ∈ I, ∑ a, ∑ b, G hs a hs' b x := by
  have s1 : ∀ hs, (∑ a, ∑ hs', ∑ b, ∑ x ∈ I, G hs a hs' b x)
      = ∑ hs', ∑ a, ∑ b, ∑ x ∈ I, G hs a hs' b x := by
    intro hs
    exact Finset.sum_comm
  refine Finset.sum_congr rfl (fun hs _ => ?_)
  refine (s1 hs).trans ?_
  refine Finset.sum_congr rfl (fun hs' _ => ?_)
  exact rotate3_finset I (fun a b x => G hs a hs' b x)

end Aux

open Aux

/-! ## The raw cube average -/

/-- The inner (unnormalised) sum defining the `2^t`-th power of the box norm: the average over the
shift tuples `h`, `h'` of the cube term, summed over `x ∈ ℤ`.  This is the factor of
`Work.Peluse.prodCubeSum` carrying the whole content. -/
def rawSum (t : ℕ) (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) : ℂ :=
  ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
    ∑' x : ℤ, ∏ ω : Fin t → Bool,
      (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))

/-- The normalising constant of the box norm, as a real number. -/
def boxScaling (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) : ℝ :=
  ((S.card : ℝ))⁻¹ * (∏ i, (((Q i).card : ℝ))⁻¹) * (∏ i, (((Q i).card : ℝ))⁻¹)

/-- A bound for the size of the shifts `cornerShift h h' ω`, uniform in `h, h' ∈ ∏ Q_i` and `ω`. -/
def rad (t : ℕ) (Q : Fin t → Finset ℤ) (N : ℕ) : ℕ :=
  N + ∑ i, (Q i).sum (fun z => z.natAbs)

/-- The range of the `x`-sum: `x ↦ ∏_ω f (x + cornerShift h h' ω)` is supported in it. -/
def ball (t : ℕ) (Q : Fin t → Finset ℤ) (N : ℕ) : Finset ℤ :=
  Finset.Icc (-((rad t Q N : ℕ) : ℤ)) ((rad t Q N : ℕ) : ℤ)

/-- The cube term of one lower dimension, with the tail tuples `hs`, `hs'` of the two shift
tuples fixed: `Φ(u) = ∏_{τ : Fin k → Bool} C^{|τ|} f (u + cornerShift hs hs' τ)`. -/
def redCube {k : ℕ} (Q : Fin (k+1) → Finset ℤ)
    (hs hs' : (i : Fin k) → {x : ℤ // x ∈ Q i.succ}) (f : ℤ → ℂ) (u : ℤ) : ℂ :=
  ∏ τ : Fin k → Bool,
    (star^[weight τ]) (f (u + cornerShift (fun i => (hs i).1) (fun i => (hs' i).1) τ))

/-- The sum of squares that the raw box sum equals. -/
def normSqSum {k : ℕ} (Q : Fin (k+1) → Finset ℤ) (f : ℤ → ℂ) (N : ℕ) : ℝ :=
  ∑ hs : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
    ∑ hs' : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
      ∑ x ∈ ball (k+1) Q N,
        ‖∑ a : ({y : ℤ // y ∈ Q 0}), redCube Q hs hs' f (x + (a : ℤ))‖ ^ 2

lemma normSqSum_nonneg {k : ℕ} (Q : Fin (k+1) → Finset ℤ) (f : ℤ → ℂ) (N : ℕ) :
    0 ≤ normSqSum Q f N := by
  refine Finset.sum_nonneg (fun hs _ => Finset.sum_nonneg (fun hs' _ => ?_))
  exact Finset.sum_nonneg (fun x _ => sq_nonneg _)

lemma boxScaling_nonneg (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) :
    0 ≤ boxScaling t Q S := by
  rw [boxScaling]
  positivity


/-- The cube term of the box sum, as a function of the two shift tuples and `x`. -/
def cubeTermZ {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ)
    (h h' : (i : Fin t) → {x : ℤ // x ∈ Q i}) (x : ℤ) : ℂ :=
  ∏ ω : Fin t → Bool,
    (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω))

/-- The unnormalised box sum is a nonnegative real: it is a sum of squares. -/
theorem rawSum_eq_cubeNormSqSum {k : ℕ} (Q : Fin (k+1) → Finset ℤ) (f : ℤ → ℂ) {N : ℕ}
    (hN : SupportIn f N) :
    rawSum (k+1) Q f = ((normSqSum Q f N : ℝ) : ℂ) := by
  have hterm : ∀ (h h' : (i : Fin (k+1)) → {x : ℤ // x ∈ Q i}),
      (∑' x : ℤ, cubeTermZ Q f h h' x) = ∑ x ∈ ball (k+1) Q N, cubeTermZ Q f h h' x :=
    fun h h' => cubeTerm_tsum_finite Q f hN h h'
  have hsplit1 : ∀ h : (i : Fin (k+1)) → {x : ℤ // x ∈ Q i},
      (∑ h' : (i : Fin (k+1)) → {x : ℤ // x ∈ Q i},
          ∑ x ∈ ball (k+1) Q N, cubeTermZ Q f h h' x)
        = ∑ hs' : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
            ∑ b : ({y : ℤ // y ∈ Q 0}),
              ∑ x ∈ ball (k+1) Q N, cubeTermZ Q f h (Fin.cons b hs') x :=
    fun h => sum_cons_equiv (fun h' => ∑ x ∈ ball (k+1) Q N, cubeTermZ Q f h h' x)
  have hsplit2 : (∑ h : (i : Fin (k+1)) → {x : ℤ // x ∈ Q i},
        ∑ hs' : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
          ∑ b : ({y : ℤ // y ∈ Q 0}),
            ∑ x ∈ ball (k+1) Q N, cubeTermZ Q f h (Fin.cons b hs') x)
      = ∑ hs : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
          ∑ a : ({y : ℤ // y ∈ Q 0}),
            ∑ hs' : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
              ∑ b : ({y : ℤ // y ∈ Q 0}),
                ∑ x ∈ ball (k+1) Q N,
                  cubeTermZ Q f (Fin.cons a hs) (Fin.cons b hs') x :=
    sum_cons_equiv (fun h => ∑ hs' : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
          ∑ b : ({y : ℤ // y ∈ Q 0}),
            ∑ x ∈ ball (k+1) Q N, cubeTermZ Q f h (Fin.cons b hs') x)
  have hreorder : (∑ hs : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
          ∑ a : ({y : ℤ // y ∈ Q 0}),
            ∑ hs' : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
              ∑ b : ({y : ℤ // y ∈ Q 0}),
                ∑ x ∈ ball (k+1) Q N,
                  cubeTermZ Q f (Fin.cons a hs) (Fin.cons b hs') x)
      = ∑ hs : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
          ∑ hs' : ((i : Fin k) → {x : ℤ // x ∈ Q i.succ}),
            ∑ x ∈ ball (k+1) Q N,
              ∑ a : ({y : ℤ // y ∈ Q 0}),
                ∑ b : ({y : ℤ // y ∈ Q 0}),
                  cubeTermZ Q f (Fin.cons a hs) (Fin.cons b hs') x :=
    reorder_pair (ball (k+1) Q N)
      (fun hs a hs' b x => cubeTermZ Q f (Fin.cons a hs) (Fin.cons b hs') x)
  have hfactor : ∀ (hs hs' : (i : Fin k) → {x : ℤ // x ∈ Q i.succ}) (x : ℤ),
      (∑ a : ({y : ℤ // y ∈ Q 0}), ∑ b : ({y : ℤ // y ∈ Q 0}),
          cubeTermZ Q f (Fin.cons a hs) (Fin.cons b hs') x)
        = ∑ a : ({y : ℤ // y ∈ Q 0}), ∑ b : ({y : ℤ // y ∈ Q 0}),
            redCube Q hs hs' f (x + (b : ℤ)) * star (redCube Q hs hs' f (x + (a : ℤ))) := by
    intro hs hs' x
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    have h := cubeTerm_cons (k := k) (a := (a : ℤ)) (b := (b : ℤ))
      (h := fun i => (hs i).1) (h' := fun i => (hs' i).1) f x
    rw [cubeTermZ, redCube, redCube]
    simp only [Aux.cons_val a hs, Aux.cons_val b hs'] at h ⊢
    exact h
  have hnorm : ∀ (hs hs' : (i : Fin k) → {x : ℤ // x ∈ Q i.succ}) (x : ℤ),
      (∑ a : ({y : ℤ // y ∈ Q 0}), ∑ b : ({y : ℤ // y ∈ Q 0}),
          redCube Q hs hs' f (x + (b : ℤ)) * star (redCube Q hs hs' f (x + (a : ℤ))))
        = ((‖∑ a : ({y : ℤ // y ∈ Q 0}), redCube Q hs hs' f (x + (a : ℤ))‖ ^ 2 : ℝ)
            : ℂ) :=
    fun hs hs' x => sum_pairs_star_eq_normSq (fun a : {y : ℤ // y ∈ Q 0} =>
      redCube Q hs hs' f (x + (a : ℤ)))
  change (∑ h : (i : Fin (k+1)) → {x : ℤ // x ∈ Q i},
      ∑ h' : (i : Fin (k+1)) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, cubeTermZ Q f h h' x) = _
  simp only [hterm]
  refine ((Finset.sum_congr rfl (fun h _ => hsplit1 h)).trans hsplit2).trans ?_
  refine hreorder.trans ?_
  refine (Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ =>
    Finset.sum_congr rfl (fun x _ => hfactor hs hs' x)))).trans ?_
  refine (Finset.sum_congr rfl (fun hs _ => Finset.sum_congr rfl (fun hs' _ =>
    Finset.sum_congr rfl (fun x _ => hnorm hs hs' x)))).trans ?_
  rw [normSqSum]
  simp only [← Complex.ofReal_sum]

/-- The box sum is its normalising constant times the raw cube average. -/
lemma boxSumPow_eq_scaling (t : ℕ) (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxSumPow t Q S f = (boxScaling t Q S : ℂ) * rawSum t Q f := by
  rw [boxSumPow, prodCubeSum, rawSum, boxScaling]
  push_cast
  ring

/-- For finitely supported `f`, the `2^t`-th power of the Gowers box norm
`‖f‖_{□^t_{Q₁,…,Q_t}(S)}` is a nonnegative real number, so that the complex cube average
`boxSumPow` coincides with its own modulus `boxNormPow`. -/
theorem boxSumPow_eq_boxNormPow {t : ℕ} (ht : 1 ≤ t) {Q : Fin t → Finset ℤ} {S : Finset ℤ}
    {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxSumPow t Q S f = (Work.Peluse.boxNormPow t Q S f : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  obtain ⟨N, hN⟩ := hf
  have h1 : boxSumPow (k+1) Q S f = (boxScaling (k+1) Q S : ℂ) * rawSum (k+1) Q f :=
    boxSumPow_eq_scaling (k+1) Q S f
  have h2 : rawSum (k+1) Q f = ((normSqSum Q f N : ℝ) : ℂ) := rawSum_eq_cubeNormSqSum Q f hN
  have h3 : boxSumPow (k+1) Q S f
      = ((boxScaling (k+1) Q S * normSqSum Q f N : ℝ) : ℂ) := by
    rw [h1, h2, ← Complex.ofReal_mul]
  have hnn : (0 : ℝ) ≤ boxScaling (k+1) Q S * normSqSum Q f N :=
    mul_nonneg (boxScaling_nonneg (k+1) Q S) (normSqSum_nonneg Q f N)
  have hnorm : boxNormPow (k+1) Q S f = boxScaling (k+1) Q S * normSqSum Q f N := by
    rw [boxNormPow, h3]
    exact Complex.norm_of_nonneg hnn
  rw [hnorm]
  exact h3

end

end Work.Peluse.BoxNorm
