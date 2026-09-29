import Mathlib
import Submission.Work.ConvR.basic

/-!
# `negaMul` is bilinear (and symmetric) — the ConvR linearity package

`negaMul r a b` is the product in the synthetic ring `ℝ = ℂ[y]/(y^r+1)`:

`negaMul r a b k = ∑ i ∑ j, [i+j=k] a i b j - [i+j=k+r] a i b j`.

Here we show that it is ℂ-bilinear in each argument and symmetric.  The key observation is
that the piecewise kernel is a *scalar* depending only on `i, j` (and `k`), with all
`r`-dependence absorbed into it, so that for fixed `k` the expression is a linear functional
of `a` (resp. of `b`).
-/

namespace Work.ConvR

open HvdH

/-- The bilinear kernel of `negaMul`: `[i+j=k] - [i+j=k+r]`. -/
noncomputable def negK (r : ℕ) (k : Fin r) (i j : Fin r) : ℂ :=
  (if (i : ℕ) + (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) -
    (if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then (1 : ℂ) else 0)

/-- `negaMul` is a linear functional of its first argument with weights
`∑ j, negK r k i j * b j`. -/
noncomputable def coefL (r : ℕ) (k : Fin r) (b : Fin r → ℂ) : Fin r → ℂ :=
  fun i => ∑ j, negK r k i j * b j

/-- `negaMul` is a linear functional of its second argument with weights
`∑ i, negK r k i j * a i`. -/
noncomputable def coefR (r : ℕ) (k : Fin r) (a : Fin r → ℂ) : Fin r → ℂ :=
  fun j => ∑ i, negK r k i j * a i

/-- A coordinate-weighted linear functional `a ↦ ∑ i, w i * a i` on `Fin n → ℂ`. -/
noncomputable def linfun {n : ℕ} (w : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun a := ∑ i, w i * a i
  map_add' a a' := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Pointwise form of the kernel identity: the piecewise definition of `negaMul` is the
product of the scalar kernel `negK` with `a i * b j`. -/
lemma negT_point (r : ℕ) (k : Fin r) (i j : Fin r) (a b : Fin r → ℂ) :
    (if (i : ℕ) + (j : ℕ) = (k : ℕ) then a i * b j
     else if (i : ℕ) + (j : ℕ) = (k : ℕ) + r then -(a i * b j) else 0)
    = negK r k i j * (a i * b j) := by
  have hr : 0 < r := by have := k.isLt; omega
  unfold negK
  by_cases h1 : (i : ℕ) + (j : ℕ) = (k : ℕ)
  · have h2 : ¬ ((i : ℕ) + (j : ℕ) = (k : ℕ) + r) := by omega
    rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2]
    ring
  · by_cases h2 : (i : ℕ) + (j : ℕ) = (k : ℕ) + r
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]
      ring
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
      ring

lemma negaMul_apply (r : ℕ) (k : Fin r) (a b : Fin r → ℂ) :
    negaMul r a b k = ∑ i, ∑ j, negK r k i j * (a i * b j) := by
  unfold negaMul
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  exact negT_point r k i j a b

/-- The kernel is symmetric in `i, j`. -/
lemma negK_comm (r : ℕ) (k : Fin r) (i j : Fin r) : negK r k i j = negK r k j i := by
  unfold negK
  rw [Nat.add_comm (j : ℕ) (i : ℕ)]

lemma negaMul_eq_linfun_left (r : ℕ) (k : Fin r) (a b : Fin r → ℂ) :
    negaMul r a b k = linfun (coefL r k b) a := by
  rw [negaMul_apply]
  show (∑ i, ∑ j, negK r k i j * (a i * b j)) = ∑ i, (∑ j, negK r k i j * b j) * a i
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma negaMul_eq_linfun_right (r : ℕ) (k : Fin r) (a b : Fin r → ℂ) :
    negaMul r a b k = linfun (coefR r k a) b := by
  rw [negaMul_apply]
  show (∑ i, ∑ j, negK r k i j * (a i * b j)) = ∑ j, (∑ i, negK r k i j * a i) * b j
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- `negaMul` is symmetric. -/
lemma negaMul_comm (r : ℕ) (a b : Fin r → ℂ) : negaMul r a b = negaMul r b a := by
  funext k
  rw [negaMul_apply, negaMul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [← negK_comm r k i j]
  ring

lemma negaMul_add_left (r : ℕ) (a a' b : Fin r → ℂ) :
    negaMul r (a + a') b = negaMul r a b + negaMul r a' b := by
  funext k
  rw [Pi.add_apply, negaMul_eq_linfun_left r k (a + a') b,
      map_add (linfun (coefL r k b)) a a',
      ← negaMul_eq_linfun_left r k a b, ← negaMul_eq_linfun_left r k a' b]

lemma negaMul_add_right (r : ℕ) (a b b' : Fin r → ℂ) :
    negaMul r a (b + b') = negaMul r a b + negaMul r a b' := by
  funext k
  rw [Pi.add_apply, negaMul_eq_linfun_right r k a (b + b'),
      map_add (linfun (coefR r k a)) b b',
      ← negaMul_eq_linfun_right r k a b, ← negaMul_eq_linfun_right r k a b']

lemma negaMul_smul_left (r : ℕ) (c : ℂ) (a b : Fin r → ℂ) :
    negaMul r (c • a) b = c • negaMul r a b := by
  funext k
  rw [Pi.smul_apply, smul_eq_mul, negaMul_eq_linfun_left r k (c • a) b,
      map_smul (linfun (coefL r k b)) c a,
      ← negaMul_eq_linfun_left r k a b, smul_eq_mul]

lemma negaMul_smul_right (r : ℕ) (c : ℂ) (a b : Fin r → ℂ) :
    negaMul r a (c • b) = c • negaMul r a b := by
  funext k
  rw [Pi.smul_apply, smul_eq_mul, negaMul_eq_linfun_right r k a (c • b),
      map_smul (linfun (coefR r k a)) c b,
      ← negaMul_eq_linfun_right r k a b, smul_eq_mul]

lemma negaMul_sum_left (r : ℕ) {ι : Type} (s : Finset ι) (f : ι → Fin r → ℂ) (b : Fin r → ℂ) :
    negaMul r (∑ i ∈ s, f i) b = ∑ i ∈ s, negaMul r (f i) b := by
  funext k
  rw [Finset.sum_apply, negaMul_eq_linfun_left r k (∑ i ∈ s, f i) b,
      map_sum (linfun (coefL r k b)) f s]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (negaMul_eq_linfun_left r k (f i) b).symm

lemma negaMul_sum_right (r : ℕ) {ι : Type} (s : Finset ι) (a : Fin r → ℂ) (g : ι → Fin r → ℂ) :
    negaMul r a (∑ i ∈ s, g i) = ∑ i ∈ s, negaMul r a (g i) := by
  funext k
  rw [Finset.sum_apply, negaMul_eq_linfun_right r k a (∑ i ∈ s, g i),
      map_sum (linfun (coefR r k a)) g s]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact (negaMul_eq_linfun_right r k a (g i)).symm

theorem negaMulLin :
    (∀ (r : ℕ) (a b : Fin r → ℂ), HvdH.negaMul r a b = HvdH.negaMul r b a) ∧
    (∀ (r : ℕ) (a a' b : Fin r → ℂ),
      HvdH.negaMul r (a + a') b = HvdH.negaMul r a b + HvdH.negaMul r a' b) ∧
    (∀ (r : ℕ) (a b b' : Fin r → ℂ),
      HvdH.negaMul r a (b + b') = HvdH.negaMul r a b + HvdH.negaMul r a b') ∧
    (∀ (r : ℕ) (c : ℂ) (a b : Fin r → ℂ),
      HvdH.negaMul r (c • a) b = c • HvdH.negaMul r a b) ∧
    (∀ (r : ℕ) (c : ℂ) (a b : Fin r → ℂ),
      HvdH.negaMul r a (c • b) = c • HvdH.negaMul r a b) ∧
    (∀ (r : ℕ) {ι : Type} (s : Finset ι) (f : ι → Fin r → ℂ) (b : Fin r → ℂ),
      HvdH.negaMul r (∑ i ∈ s, f i) b = ∑ i ∈ s, HvdH.negaMul r (f i) b) ∧
    (∀ (r : ℕ) {ι : Type} (s : Finset ι) (a : Fin r → ℂ) (g : ι → Fin r → ℂ),
      HvdH.negaMul r a (∑ i ∈ s, g i) = ∑ i ∈ s, HvdH.negaMul r a (g i)) :=
  ⟨negaMul_comm, negaMul_add_left, negaMul_add_right, negaMul_smul_left, negaMul_smul_right,
   negaMul_sum_left, negaMul_sum_right⟩

end Work.ConvR
