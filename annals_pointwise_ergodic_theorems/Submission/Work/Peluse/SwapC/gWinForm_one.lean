import Mathlib
import Submission.Work.Peluse.SwapC.GDefs

namespace Work.Peluse.SwapC

open Work.Peluse

/-- The product over the two signs `Fin 1 → Bool` has exactly two factors. -/
private lemma prod_fin_one_bool_swap {M : Type*} [CommMonoid M] (f : (Fin 1 → Bool) → M) :
    (∏ ω : Fin 1 → Bool, f ω) = f (fun _ => false) * f (fun _ => true) := by
  rw [← Equiv.prod_comp (Equiv.funUnique (Fin 1) Bool).symm f]
  rw [Fintype.prod_bool]
  have h1 : (Equiv.funUnique (Fin 1) Bool).symm true = (fun _ => true) := by
    funext i; simp [Equiv.funUnique, Equiv.piUnique, uniqueElim_const]
  have h2 : (Equiv.funUnique (Fin 1) Bool).symm false = (fun _ => false) := by
    funext i; simp [Equiv.funUnique, Equiv.piUnique, uniqueElim_const]
  rw [h1, h2, mul_comm]

theorem gWinForm_one (Y : Fin 1 → Type*) [∀ i, Fintype (Y i)] (β : (i : Fin 1) → Y i → ℤ)
    (W : Finset ℤ) (φ : (Fin 1 → Bool) → ℤ → ℂ) :
    Work.Peluse.SwapC.gWinForm 1 Y β W φ
      = ∑ x ∈ W, (∑ a' : Y 0, φ (fun _ => false) (x + β 0 a')) *
          star (∑ a : Y 0, φ (fun _ => true) (x + β 0 a)) := by
  -- The inner `ω`-product collapses to the two sign terms, the `false` one being `z'`-dependent
  -- and the `true` one being `z`-dependent.
  have hprod : ∀ (z z' : GIdx 1 Y) (x : ℤ),
      (∏ ω : Fin 1 → Bool, star^[weight ω] (φ ω (x + gtotal β (gcorner z z' ω))))
        = φ (fun _ => false) (x + β 0 (z' 0)) * star (φ (fun _ => true) (x + β 0 (z 0))) := by
    intro z z' x
    rw [prod_fin_one_bool_swap]
    have h1 : (star^[weight (fun _ : Fin 1 => false)])
        (φ (fun _ => false) (x + gtotal β (gcorner z z' (fun _ => false))))
        = φ (fun _ => false) (x + β 0 (z' 0)) := by
      have hgc : gcorner z z' (fun _ => false) = z' := by
        funext i; simp [gcorner]
      have hgt : gtotal β z' = β 0 (z' 0) := by simp [gtotal]
      rw [hgc, hgt]
      simp [weight]
    have h2 : (star^[weight (fun _ : Fin 1 => true)])
        (φ (fun _ => true) (x + gtotal β (gcorner z z' (fun _ => true))))
        = star (φ (fun _ => true) (x + β 0 (z 0))) := by
      have hgc : gcorner z z' (fun _ => true) = z := by
        funext i; simp [gcorner]
      have hgt : gtotal β z = β 0 (z 0) := by simp [gtotal]
      rw [hgc, hgt]
      simp [weight]
    rw [h1, h2]
  -- Reindexing the two `GIdx 1 Y` sums by the (unique-element) equivalence `GIdx 1 Y ≃ Y 0`,
  -- after swapping the window sum out.
  have hfac : ∀ x : ℤ,
      (∑ z : GIdx 1 Y, ∑ z' : GIdx 1 Y,
        φ (fun _ => false) (x + β 0 (z' 0)) * star (φ (fun _ => true) (x + β 0 (z 0))))
      = (∑ a' : Y 0, φ (fun _ => false) (x + β 0 a')) *
          star (∑ a : Y 0, φ (fun _ => true) (x + β 0 a)) := by
    intro x
    rw [Finset.sum_comm]
    have hct : (∑ z' : GIdx 1 Y, ∑ z : GIdx 1 Y,
          φ (fun _ => false) (x + β 0 (z' 0)) * star (φ (fun _ => true) (x + β 0 (z 0))))
        = ∑ z' : GIdx 1 Y, (φ (fun _ => false) (x + β 0 (z' 0))) *
            (∑ z : GIdx 1 Y, star (φ (fun _ => true) (x + β 0 (z 0)))) := by
      refine Finset.sum_congr rfl (fun z' _ => ?_)
      rw [Finset.mul_sum]
    rw [hct, ← Finset.sum_mul]
    have e1 : (∑ z' : GIdx 1 Y, φ (fun _ => false) (x + β 0 (z' 0)))
        = ∑ a' : Y 0, φ (fun _ => false) (x + β 0 a') :=
      Equiv.sum_comp (Equiv.piUnique Y) (fun a' : Y 0 => φ (fun _ => false) (x + β 0 a'))
    have e2 : (∑ z : GIdx 1 Y, star (φ (fun _ => true) (x + β 0 (z 0))))
        = star (∑ a : Y 0, φ (fun _ => true) (x + β 0 a)) := by
      rw [star_sum]
      exact Equiv.sum_comp (Equiv.piUnique Y)
        (fun a : Y 0 => star (φ (fun _ => true) (x + β 0 a)))
    rw [e1, e2]
  unfold gWinForm
  rw [Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun z' _ =>
        Finset.sum_congr rfl (fun x _ => hprod z z' x)))]
  rw [Finset.sum_congr rfl (fun z _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => hfac x)

end Work.Peluse.SwapC
