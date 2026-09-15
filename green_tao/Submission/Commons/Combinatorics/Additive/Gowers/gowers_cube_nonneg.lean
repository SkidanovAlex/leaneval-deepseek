import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Combinatorics.Additive.Gowers

open scoped BigOperators

/-- Splitting the last coordinate of a tuple: `(Fin (n+1) → α) ≃ (Fin n → α) × α`. -/
private def finSnocEquiv (n : ℕ) (α : Type*) : (Fin (n+1) → α) ≃ (Fin n → α) × α where
  toFun ω := (Fin.init ω, ω (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv ω := by simp
  right_inv p := by ext <;> simp

/-- The cube translate splits as the sum over the first `d` coordinates plus the last one. -/
private lemma finSum_snoc {G : Type*} [AddCommMonoid G] (d : ℕ)
    (h' : Fin d → G) (t : G) (ω' : Fin d → Bool) (b : Bool) :
    (∑ i : Fin (d+1),
        (if (Fin.snoc ω' b : Fin (d+1) → Bool) i then
          (Fin.snoc h' t : Fin (d+1) → G) i else 0))
      = (∑ i : Fin d, (if ω' i then h' i else 0)) + (if b then t else 0) := by
  rw [Fin.sum_univ_castSucc]
  simp

/-- Product over the last `Bool` coordinate. -/
private lemma prod_bool_snoc {G : Type*} [AddCommGroup G] (f : G → ℝ) (d : ℕ)
    (h' : Fin d → G) (t x : G) (ω' : Fin d → Bool) :
    (∏ b : Bool, f (x + ∑ i : Fin (d+1),
        (if (Fin.snoc ω' b : Fin (d+1) → Bool) i then
          (Fin.snoc h' t : Fin (d+1) → G) i else 0)))
      = f (x + ((∑ i : Fin d, (if ω' i then h' i else 0)) + t))
        * f (x + (∑ i : Fin d, (if ω' i then h' i else 0))) := by
  rw [Fintype.prod_bool]
  rw [finSum_snoc d h' t ω' true, finSum_snoc d h' t ω' false]
  simp

/-- The cube product over `d+1` coordinates of the direction `Fin.snoc h' t` factors as the
product of the `d`-coordinate cube at `x` and at `x + t`. -/
private lemma prod_snoc {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℝ) (d : ℕ)
    (h' : Fin d → G) (t x : G) :
    (∏ ω : Fin (d+1) → Bool,
        f (x + ∑ i : Fin (d+1), (if ω i then (Fin.snoc h' t : Fin (d+1) → G) i else 0)))
      = (∏ ω : Fin d → Bool, f (x + ∑ i : Fin d, (if ω i then h' i else 0)))
        * (∏ ω : Fin d → Bool, f ((x + t) + ∑ i : Fin d, (if ω i then h' i else 0))) := by
  classical
  rw [show (∏ ω : Fin (d+1) → Bool,
        f (x + ∑ i : Fin (d+1), (if ω i then (Fin.snoc h' t : Fin (d+1) → G) i else 0)))
      = ∏ p : (Fin d → Bool) × Bool,
        f (x + ∑ i : Fin (d+1), (if (Fin.snoc p.1 p.2 : Fin (d+1) → Bool) i then
          (Fin.snoc h' t : Fin (d+1) → G) i else 0)) from by
        exact (Fintype.prod_equiv (finSnocEquiv d Bool).symm _ _ (fun p => rfl)).symm]
  rw [Fintype.prod_prod_type]
  rw [Finset.prod_congr rfl (fun ω' _ => prod_bool_snoc f d h' t x ω')]
  rw [Finset.prod_congr rfl (fun ω' _ => by
        have h : x + ((∑ i : Fin d, (if ω' i then h' i else 0)) + t)
               = (x + t) + ∑ i : Fin d, (if ω' i then h' i else 0) := by abel
        rw [mul_comm, h])]
  rw [Finset.prod_mul_distrib]

/-- The automorphism identity behind the cube: `∑_t ∑_x A x · A (x+t) = (∑_x A x)^2`. -/
private lemma sum_shift_autocorr {G : Type*} [AddCommGroup G] [Fintype G] (A : G → ℝ) :
    (∑ t : G, ∑ x : G, A x * A (x + t)) = (∑ x : G, A x)^2 := by
  calc
    (∑ t : G, ∑ x : G, A x * A (x + t))
        = ∑ x : G, ∑ t : G, A x * A (x + t) := Finset.sum_comm
    _ = ∑ x : G, A x * (∑ t : G, A (x + t)) := by
          apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum]
    _ = ∑ x : G, A x * (∑ u : G, A u) := by
          apply Finset.sum_congr rfl; intro x _
          congr 1
          exact Equiv.sum_comp (Equiv.addLeft x) A
    _ = (∑ x : G, A x) * (∑ u : G, A u) := by rw [Finset.sum_mul]
    _ = (∑ x : G, A x)^2 := by ring

/-- One diagonalising step: the `(d+1)`-fold cube sum equals the sum over the `d`-fold
directions of a square. -/
private lemma gowers_decomp {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℝ) (d : ℕ) :
    (∑ h : Fin (d+1) → G, ∑ x : G,
        ∏ ω : Fin (d+1) → Bool,
          f (x + ∑ i : Fin (d+1), (if ω i then h i else 0)))
  = ∑ h' : Fin d → G, (∑ x : G,
        ∏ ω : Fin d → Bool,
          f (x + ∑ i : Fin d, (if ω i then h' i else 0)))^2 := by
  classical
  rw [show (∑ h : Fin (d+1) → G, ∑ x : G, ∏ ω : Fin (d+1) → Bool,
        f (x + ∑ i : Fin (d+1), (if ω i then h i else 0)))
      = ∑ p : (Fin d → G) × G, ∑ x : G, ∏ ω : Fin (d+1) → Bool,
        f (x + ∑ i : Fin (d+1), (if ω i then (Fin.snoc p.1 p.2 : Fin (d+1) → G) i else 0)) from
        (Fintype.sum_equiv (finSnocEquiv d G).symm _ _ (fun p => rfl)).symm]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro h' _
  have hinner : (∑ t : G, ∑ x : G, ∏ ω : Fin (d+1) → Bool,
        f (x + ∑ i : Fin (d+1), (if ω i then (Fin.snoc h' t : Fin (d+1) → G) i else 0)))
      = ∑ t : G, ∑ x : G,
          (∏ ω : Fin d → Bool, f (x + ∑ i : Fin d, (if ω i then h' i else 0)))
          * (∏ ω : Fin d → Bool, f ((x + t) + ∑ i : Fin d, (if ω i then h' i else 0))) := by
    apply Finset.sum_congr rfl; intro t _
    apply Finset.sum_congr rfl; intro x _
    exact prod_snoc f d h' t x
  rw [hinner]
  exact sum_shift_autocorr
    (fun y : G => ∏ ω : Fin d → Bool, f (y + ∑ i : Fin d, (if ω i then h' i else 0)))

theorem gowers_cube_nonneg {G : Type*} [AddCommGroup G] [Fintype G] (f : G → ℝ) (d : ℕ) :
    0 ≤ ∑ h : Fin (d+1) → G, ∑ x : G,
        ∏ ω : Fin (d+1) → Bool,
          f (x + ∑ i : Fin (d+1), (if ω i then h i else 0)) := by
  rw [gowers_decomp f d]
  exact Finset.sum_nonneg (fun h' _ => sq_nonneg _)

end Commons.Combinatorics.Additive.Gowers