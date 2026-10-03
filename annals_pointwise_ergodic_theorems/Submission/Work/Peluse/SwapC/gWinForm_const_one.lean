import Mathlib
import Submission.Work.Peluse.SwapC.GDefs

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-- `Bool` is equivalent to the two-element type `Fin 1 → Bool` via the constant functions. -/
private def boolFunEquiv : Bool ≃ (Fin 1 → Bool) where
  toFun b := fun _ => b
  invFun f := f 0
  left_inv b := rfl
  right_inv f := by funext i; fin_cases i; rfl

/-- A sum over a single-coordinate index tuple depends only on the coordinate, so it may be
reindexed as a sum over that coordinate type. -/
private lemma sum_gIdx_one (Y : Fin 1 → Type*) [∀ i, Fintype (Y i)] (H : Y 0 → ℂ) :
    ∑ z : GIdx 1 Y, H (z 0) = ∑ a : Y 0, H a := by
  refine Fintype.sum_equiv (Equiv.piUnique (fun i : Fin 1 => Y i)) (fun z => H (z 0)) H ?_
  intro z
  rfl

/-- Iterated sums commute: the (finite) coordinate sums may be taken after the window sum. -/
private lemma sum_comm3 {ι κ : Type*} [Fintype ι] [Fintype κ] (W : Finset ℤ)
    (f : ι → κ → ℤ → ℂ) :
    (∑ a : ι, ∑ b : κ, ∑ x ∈ W, f a b x) = ∑ x ∈ W, ∑ a : ι, ∑ b : κ, f a b x := by
  have h1 : (∑ a : ι, ∑ b : κ, ∑ x ∈ W, f a b x)
      = ∑ b : κ, ∑ a : ι, ∑ x ∈ W, f a b x := by
    simpa only using Finset.sum_comm (s := (Finset.univ : Finset ι))
      (t := (Finset.univ : Finset κ)) (f := fun a b => ∑ x ∈ W, f a b x)
  have h2 : (∑ b : κ, ∑ a : ι, ∑ x ∈ W, f a b x)
      = ∑ b : κ, ∑ x ∈ W, ∑ a : ι, f a b x := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simpa only using Finset.sum_comm (s := (Finset.univ : Finset ι)) (t := W)
      (f := fun a x => f a b x)
  have h3 : (∑ b : κ, ∑ x ∈ W, ∑ a : ι, f a b x)
      = ∑ x ∈ W, ∑ b : κ, ∑ a : ι, f a b x := by
    simpa only using Finset.sum_comm (s := (Finset.univ : Finset κ)) (t := W)
      (f := fun b x => ∑ a : ι, f a b x)
  have h4 : (∑ x ∈ W, ∑ b : κ, ∑ a : ι, f a b x)
      = ∑ x ∈ W, ∑ a : ι, ∑ b : κ, f a b x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simpa only using Finset.sum_comm (s := (Finset.univ : Finset κ))
      (t := (Finset.univ : Finset ι)) (f := fun b a => f a b x)
  rw [h1, h2, h3, h4]

theorem gWinForm_const_one (Y : Fin 1 → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin 1) → Y i → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    Work.Peluse.SwapC.gWinForm 1 Y β W (fun _ => g)
      = ((∑ x ∈ W, ‖∑ a : Y 0, g (x + β 0 a)‖ ^ 2 : ℝ) : ℂ) := by
  rw [Work.Peluse.SwapC.gWinForm]
  -- the product over the two Boolean functions `Fin 1 → Bool`
  have hprod : ∀ (z z' : GIdx 1 Y) (x : ℤ),
      (∏ ω : Fin 1 → Bool, star^[Work.Peluse.weight ω] (g (x + gtotal β (gcorner z z' ω))))
        = g (x + β 0 (z' 0)) * star (g (x + β 0 (z 0))) := by
    intro z z' x
    rw [← Equiv.prod_comp boolFunEquiv
          (fun ω : Fin 1 → Bool => star^[Work.Peluse.weight ω]
            (g (x + gtotal β (gcorner z z' ω))))]
    rw [show (Finset.univ : Finset Bool) = {true, false} from Fintype.univ_bool]
    rw [Finset.prod_pair (by decide : (true : Bool) ≠ false)]
    have hT : star^[Work.Peluse.weight (boolFunEquiv true)]
        (g (x + gtotal β (gcorner z z' (boolFunEquiv true)))) = star (g (x + β 0 (z 0))) := by
      simp [boolFunEquiv, Work.Peluse.weight, gtotal, gcorner]
    have hF : star^[Work.Peluse.weight (boolFunEquiv false)]
        (g (x + gtotal β (gcorner z z' (boolFunEquiv false)))) = g (x + β 0 (z' 0)) := by
      simp [boolFunEquiv, Work.Peluse.weight, gtotal, gcorner]
    rw [hT, hF, mul_comm]
  simp only [hprod]
  -- reindex the two coordinate sums
  have hA : (∑ z : GIdx 1 Y, ∑ z' : GIdx 1 Y, ∑ x ∈ W,
        g (x + β 0 (z' 0)) * star (g (x + β 0 (z 0))))
      = ∑ a : Y 0, ∑ z' : GIdx 1 Y, ∑ x ∈ W,
        g (x + β 0 (z' 0)) * star (g (x + β 0 a)) :=
    sum_gIdx_one Y (fun a : Y 0 => ∑ z' : GIdx 1 Y, ∑ x ∈ W,
        g (x + β 0 (z' 0)) * star (g (x + β 0 a)))
  have hAB : (∑ a : Y 0, ∑ z' : GIdx 1 Y, ∑ x ∈ W,
        g (x + β 0 (z' 0)) * star (g (x + β 0 a)))
      = ∑ a : Y 0, ∑ a' : Y 0, ∑ x ∈ W,
        g (x + β 0 a') * star (g (x + β 0 a)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact sum_gIdx_one Y (fun a' : Y 0 => ∑ x ∈ W, g (x + β 0 a') * star (g (x + β 0 a)))
  rw [hA, hAB, sum_comm3 W (fun a a' x => g (x + β 0 a') * star (g (x + β 0 a)))]
  -- the coordinate sums factor and produce the squared modulus
  have hx : ∀ x : ℤ, (∑ a : Y 0, ∑ a' : Y 0, g (x + β 0 a') * star (g (x + β 0 a)))
      = ((‖∑ a : Y 0, g (x + β 0 a)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have s1 : (∑ a : Y 0, ∑ a' : Y 0, g (x + β 0 a') * star (g (x + β 0 a)))
        = ∑ a : Y 0, (∑ a' : Y 0, g (x + β 0 a')) * star (g (x + β 0 a)) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_mul]
    have s2 : (∑ a : Y 0, (∑ a' : Y 0, g (x + β 0 a')) * star (g (x + β 0 a)))
        = (∑ a' : Y 0, g (x + β 0 a')) * star (∑ a' : Y 0, g (x + β 0 a')) := by
      rw [← Finset.mul_sum, ← star_sum]
    have s3 : (∑ a' : Y 0, g (x + β 0 a')) * star (∑ a' : Y 0, g (x + β 0 a'))
        = ((‖∑ a' : Y 0, g (x + β 0 a')‖ ^ 2 : ℝ) : ℂ) := by
      have h := Complex.mul_conj (∑ a' : Y 0, g (x + β 0 a'))
      rw [Complex.normSq_eq_norm_sq] at h
      simpa using h
    rw [s1, s2, s3]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Complex.ofReal_sum]

end

end Work.Peluse.SwapC
