/-
# Definitions of the main chain of `Work.Peluse.SwapC.concatStep`
-/
import Mathlib
import Submission.Work.Peluse.SwapC.concatGlue

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-- A function supported in the translate `x₀ + symIcc N` vanishes off that translate. -/
lemma vanishes_off_translate {N : ℕ} {x₀ : ℤ} {f : ℤ → ℂ}
    (hsup : ∀ x : ℤ, (N : ℤ) < |x - x₀| → f x = 0) :
    ∀ x : ℤ, x ∉ (Work.Peluse.symIcc N).map (Equiv.addRight x₀).toEmbedding → f x = 0 := by
  intro x hx
  refine hsup x ?_
  have hz : x - x₀ ∉ Work.Peluse.symIcc N := by
    intro hmem
    exact hx (Finset.mem_map.mpr ⟨x - x₀, hmem, by simp [Equiv.coe_addRight]⟩)
  have hlt : ¬ ((x - x₀).natAbs ≤ N) := fun hle => hz ((mem_symIcc_iff).mpr hle)
  have h3 : N < (x - x₀).natAbs := by omega
  rw [← Int.natCast_natAbs (x - x₀)]
  exact_mod_cast h3

/-- The raw increment of the index `i` at the pair `(a, a')` of raw coordinates. -/
def rawIncr {I : Type} {M : ℕ} (qH : I → ℤ) (i : I) (a a' : Fin M) : ℤ :=
  qH i * (((a : ℕ) : ℤ) + 1) - qH i * (((a' : ℕ) : ℤ) + 1)

/-- The level-`2s` box power of the kernel `\bar f(· + dH0) f(· + dH1)` along the concatenated
slots of the two indices. -/
def Zm {I : Type} (s M N : ℕ) (qH : I → ℤ) (q₁ q₂ : I → Fin s → ℤ) (f : ℤ → ℂ)
    (i₀ i₁ : I) (a₀ a₀' a₁ a₁' : Fin M) : ℝ :=
  ‖mCubeSum (2 * s) (Fin M × Fin M) (catDir M (q₁ i₀) (q₂ i₀) (q₁ i₁) (q₂ i₁))
      (Work.Peluse.symIcc N)
      (fun _ => fun y => star (f (y + rawIncr qH i₀ a₀ a₀')) *
        f (y + rawIncr qH i₁ a₁ a₁'))‖

end

end Work.Peluse.SwapC
