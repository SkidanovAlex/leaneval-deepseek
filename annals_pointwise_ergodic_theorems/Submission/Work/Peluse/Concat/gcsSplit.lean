import Mathlib
import Submission.Work.Peluse.Concat.GowersDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Concat

noncomputable section

variable {X : Type} [Fintype X]

/-! ## Elementary auxiliary lemmas -/

/-- `↑(‖w‖ ^ 2) = w * star w` in `ℂ`. -/
lemma ofReal_sq_norm (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := by
  rw [Complex.sq_norm, Complex.star_def]
  exact (Complex.mul_conj w).symm

/-- Reindexing a double sum over a product type as a nested sum. -/
lemma sum_prod_pair {A B M : Type} [Fintype A] [Fintype B] [AddCommMonoid M]
    (g : A → B → M) : (∑ a, ∑ b, g a b) = ∑ p : A × B, g p.1 p.2 :=
  (Fintype.sum_prod_type (f := fun p : A × B => g p.1 p.2)).symm

/-- Factoring a product of two sums, with a `star` on the second factor. -/
lemma mul_star_sum_eq {A : Type} [Fintype A] (a b : A → ℂ) :
    (∑ u, a u) * star (∑ u, b u) = ∑ u0, ∑ u1, a u0 * star (b u1) := by
  rw [star_sum Finset.univ b, Finset.sum_mul]
  exact Finset.sum_congr rfl
    (fun u0 _ => Finset.mul_sum Finset.univ (fun u1 => star (b u1)) (a u0))

/-- Splitting the four-fold sum of the split cube product into a `p`-sum of a `u0`-sum times
the conjugate of a `u1`-sum (Fubini plus factoring). -/
lemma sum_uv_yy_factor {t : ℕ} (A B : X → (Fin t → X) → (Fin t → X) → ℂ) :
    (∑ u0 : X, ∑ u1 : X, ∑ y0 : Fin t → X, ∑ y1 : Fin t → X,
        A u0 y0 y1 * star (B u1 y0 y1))
      = ∑ p : (Fin t → X) × (Fin t → X),
          (∑ u : X, A u p.1 p.2) * star (∑ u : X, B u p.1 p.2) := by
  calc (∑ u0 : X, ∑ u1 : X, ∑ y0 : Fin t → X, ∑ y1 : Fin t → X,
        A u0 y0 y1 * star (B u1 y0 y1))
      = ∑ u0 : X, ∑ u1 : X, ∑ p : (Fin t → X) × (Fin t → X),
          A u0 p.1 p.2 * star (B u1 p.1 p.2) := by
        refine Finset.sum_congr rfl (fun u0 _ => Finset.sum_congr rfl (fun u1 _ => ?_))
        exact sum_prod_pair (fun y0 y1 => A u0 y0 y1 * star (B u1 y0 y1))
    _ = ∑ u0 : X, ∑ p : (Fin t → X) × (Fin t → X), ∑ u1 : X,
          A u0 p.1 p.2 * star (B u1 p.1 p.2) :=
        Finset.sum_congr rfl (fun u0 _ => Finset.sum_comm)
    _ = ∑ p : (Fin t → X) × (Fin t → X), ∑ u0 : X, ∑ u1 : X,
          A u0 p.1 p.2 * star (B u1 p.1 p.2) := Finset.sum_comm
    _ = ∑ p : (Fin t → X) × (Fin t → X),
          (∑ u : X, A u p.1 p.2) * star (∑ u : X, B u p.1 p.2) :=
        Finset.sum_congr rfl (fun p _ =>
          (mul_star_sum_eq (fun u => A u p.1 p.2) (fun u => B u p.1 p.2)).symm)

/-- **Part 1 of `gcsSplit`**: the identity. -/
lemma cubeSum_eq_split (t : ℕ)
    (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ) :
    cubeSum F = ∑ p : (Fin t → X) × (Fin t → X),
      (∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
          (F (Fin.cons false ω') (Fin.cons u (mix ω' p.1 p.2))))
        * star (∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
          (F (Fin.cons true ω') (Fin.cons u (mix ω' p.1 p.2)))) := by
  have hsplit : cubeSum F = ∑ u0 : X, ∑ u1 : X, ∑ y0 : Fin t → X, ∑ y1 : Fin t → X,
      cubeProd F (Fin.cons u0 y0) (Fin.cons u1 y1) := by
    rw [cubeSum_split]
    simp only [Fintype.sum_prod_type]
  have hterm : ∀ (u0 u1 : X) (y0 y1 : Fin t → X),
      cubeProd F (Fin.cons u0 y0) (Fin.cons u1 y1)
        = (∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons false ω') (Fin.cons u0 (mix ω' y0 y1))))
          * star (∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons true ω') (Fin.cons u1 (mix ω' y0 y1)))) := by
    intro u0 u1 y0 y1
    rw [cubeProd_split]
    exact prod_star_pair _ _ _
  rw [hsplit]
  simp only [hterm]
  exact sum_uv_yy_factor _ _

/-- The complex identity behind **Part 2 of `gcsSplit`**: the sum of the squared norms of the
`u`-averages is the sum of the cube sums of the `u0,u1`-products. -/
lemma sum_normSq_eq_sum_cubeSum {t : ℕ} {ι : Type} [Fintype ι]
    (z : ((Fin t → X) × (Fin t → X)) → ℂ)
    (w : ((Fin t → X) × (Fin t → X)) → ι → ℂ)
    (G : ι → ι → (Fin t → Bool) → (Fin t → X) → ℂ)
    (hz : ∀ p, z p = ∑ u, w p u)
    (hc : ∀ u0 u1 : ι, cubeSum (G u0 u1) = ∑ p, w p u0 * star (w p u1)) :
    ((∑ p, ‖z p‖ ^ 2 : ℝ) : ℂ) = ∑ u0 : ι, ∑ u1 : ι, cubeSum (G u0 u1) := by
  rw [Complex.ofReal_sum]
  calc (∑ p, ((‖z p‖ ^ 2 : ℝ) : ℂ))
      = ∑ p, z p * star (z p) :=
        Finset.sum_congr rfl (fun p _ => ofReal_sq_norm _)
    _ = ∑ p, ∑ u0 : ι, ∑ u1 : ι, w p u0 * star (w p u1) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [hz p]
        exact mul_star_sum_eq (w p) (w p)
    _ = ∑ u0 : ι, ∑ p, ∑ u1 : ι, w p u0 * star (w p u1) := Finset.sum_comm
    _ = ∑ u0 : ι, ∑ u1 : ι, ∑ p, w p u0 * star (w p u1) :=
        Finset.sum_congr rfl (fun u0 _ => Finset.sum_comm)
    _ = ∑ u0 : ι, ∑ u1 : ι, cubeSum (G u0 u1) :=
        Finset.sum_congr rfl (fun u0 _ => Finset.sum_congr rfl (fun u1 _ =>
          (hc u0 u1).symm))

/-- **Part 2 of `gcsSplit`**: the Gowers--Cauchy--Schwarz inequality. -/
lemma sum_normSq_le_cubeSum {t : ℕ} {ι : Type} [Fintype ι]
    (z : ((Fin t → X) × (Fin t → X)) → ℂ)
    (w : ((Fin t → X) × (Fin t → X)) → ι → ℂ)
    (G : ι → ι → (Fin t → Bool) → (Fin t → X) → ℂ)
    (hz : ∀ p, z p = ∑ u, w p u)
    (hc : ∀ u0 u1 : ι, cubeSum (G u0 u1) = ∑ p, w p u0 * star (w p u1)) :
    (∑ p, ‖z p‖ ^ 2) ≤ ∑ u0 : ι, ∑ u1 : ι, ‖cubeSum (G u0 u1)‖ := by
  have hmain := sum_normSq_eq_sum_cubeSum z w G hz hc
  calc (∑ p, ‖z p‖ ^ 2)
      = ((∑ p, ‖z p‖ ^ 2 : ℝ) : ℂ).re := (Complex.ofReal_re _).symm
    _ = (∑ u0 : ι, ∑ u1 : ι, cubeSum (G u0 u1)).re := by rw [hmain]
    _ = ∑ u0 : ι, ∑ u1 : ι, (cubeSum (G u0 u1)).re := by
        rw [Complex.re_sum]
        exact Finset.sum_congr rfl (fun u0 _ => Complex.re_sum _ _)
    _ ≤ ∑ u0 : ι, ∑ u1 : ι, ‖cubeSum (G u0 u1)‖ :=
        Finset.sum_le_sum (fun u0 _ => Finset.sum_le_sum (fun u1 _ => Complex.re_le_norm _))

/-- The Gowers--Cauchy--Schwarz inequality for the flat cube sum: the `ℓ²`-sum of the
`u`-averages of the two halves is bounded by the sum of the `cubeSum`s of the pairwise products. -/
lemma cubeSum_ineq (t : ℕ)
    (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ) (b : Bool) :
    (∑ p : (Fin t → X) × (Fin t → X),
        ‖∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
            (F (Fin.cons b ω') (Fin.cons u (mix ω' p.1 p.2)))‖ ^ 2)
      ≤ ∑ u0 : X, ∑ u1 : X,
          ‖cubeSum (fun (ω' : Fin t → Bool) => fun (y : Fin t → X) =>
              F (Fin.cons b ω') (Fin.cons u0 y)
                * star (F (Fin.cons b ω') (Fin.cons u1 y)))‖ := by
  have hcube : ∀ u0 u1 : X,
      cubeSum (fun (ω' : Fin t → Bool) => fun (y : Fin t → X) =>
          F (Fin.cons b ω') (Fin.cons u0 y) * star (F (Fin.cons b ω') (Fin.cons u1 y)))
        = ∑ p : (Fin t → X) × (Fin t → X),
            (∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
                (F (Fin.cons b ω') (Fin.cons u0 (mix ω' p.1 p.2))))
            * star (∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
                (F (Fin.cons b ω') (Fin.cons u1 (mix ω' p.1 p.2)))) := by
    intro u0 u1
    simp only [cubeSum, cubeProd]
    trans ∑ x0 : Fin t → X, ∑ x1 : Fin t → X,
        (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (F (Fin.cons b ω) (Fin.cons u0 (mix ω x0 x1))))
        * star (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (F (Fin.cons b ω) (Fin.cons u1 (mix ω x0 x1))))
    · refine Finset.sum_congr rfl (fun x0 _ => Finset.sum_congr rfl (fun x1 _ => ?_))
      exact prod_star_pair (fun ω => F (Fin.cons b ω) (Fin.cons u0 (mix ω x0 x1)))
        (fun ω => F (Fin.cons b ω) (Fin.cons u1 (mix ω x0 x1)))
        (fun ω => Work.Peluse.weight ω)
    · exact sum_prod_pair (fun x0 x1 =>
        (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (F (Fin.cons b ω) (Fin.cons u0 (mix ω x0 x1))))
        * star (∏ ω : Fin t → Bool, (star^[Work.Peluse.weight ω])
            (F (Fin.cons b ω) (Fin.cons u1 (mix ω x0 x1)))))
  exact sum_normSq_le_cubeSum
    (fun p => ∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
        (F (Fin.cons b ω') (Fin.cons u (mix ω' p.1 p.2))))
    (fun p u => ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
        (F (Fin.cons b ω') (Fin.cons u (mix ω' p.1 p.2))))
    (fun u0 u1 ω' y => F (Fin.cons b ω') (Fin.cons u0 y)
        * star (F (Fin.cons b ω') (Fin.cons u1 y)))
    (fun p => rfl) hcube

/-! ## The requested lemma -/

theorem gcsSplit :
    (∀ (X : Type) [Fintype X] (t : ℕ) (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ),
        Work.Peluse.Concat.cubeSum F = ∑ p : (Fin t → X) × (Fin t → X),
          (∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons false ω') (Fin.cons u (Work.Peluse.Concat.mix ω' p.1 p.2))))
            * star (∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
              (F (Fin.cons true ω') (Fin.cons u (Work.Peluse.Concat.mix ω' p.1 p.2)))))
    ∧ (∀ (X : Type) [Fintype X] (t : ℕ)
        (F : (Fin (t+1) → Bool) → (Fin (t+1) → X) → ℂ) (b : Bool),
        (∑ p : (Fin t → X) × (Fin t → X),
            ‖∑ u : X, ∏ ω' : Fin t → Bool, (star^[Work.Peluse.weight ω'])
                (F (Fin.cons b ω') (Fin.cons u (Work.Peluse.Concat.mix ω' p.1 p.2)))‖ ^ 2)
          ≤ ∑ u0 : X, ∑ u1 : X,
              ‖Work.Peluse.Concat.cubeSum (fun (ω' : Fin t → Bool) => fun (y : Fin t → X) =>
                  F (Fin.cons b ω') (Fin.cons u0 y)
                    * star (F (Fin.cons b ω') (Fin.cons u1 y)))‖) := by
  constructor
  · intro X hX t F
    exact @cubeSum_eq_split X hX t F
  · intro X hX t F b
    exact @cubeSum_ineq X hX t F b

end

end Work.Peluse.Concat
