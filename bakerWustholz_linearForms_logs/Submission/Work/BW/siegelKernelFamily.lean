import Mathlib
import Submission.Work.BW.sieg2Defs
import Submission.Work.BW.sieg2_kernel_familyR

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Sharp Bombieri–Vaaler kernel-lattice bound (Siegel step engine).** -/
theorem siegelKernelFamily {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    ∃ v : Fin (Module.finrank ℚ F * (N - M)) → (Fin N → NumberField.RingOfIntegers F),
      (∀ i n, ∑ m, a n m * ((v i m : NumberField.RingOfIntegers F) : F) = 0) ∧
      LinearIndependent ℝ (fun i => Work.BW.siegCoord (v i)) ∧
      Work.BW.siegGramDet v ≤
        ((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
            Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) ^ (N - M) *
          ∏ i : Fin M, ((N : ℝ) ^ ((Module.finrank ℚ F : ℝ) / 2) *
            Height.mulHeight (a i)) := by
  obtain ⟨v, hker, hliR, hb⟩ := sieg2_kernel_familyR (F := F) hMN a hli
  refine ⟨v, hker, hliR, ?_⟩
  have hne : ∀ i : Fin M, a i ≠ 0 := fun i => hli.ne_zero i
  -- the two right-hand sides agree, by `NumberField.mulHeight_eq`
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hH : (∏ i : Fin M, Height.mulHeight (a i))
      = (∏ i : Fin M, ∏ w : NumberField.InfinitePlace F,
            (⨆ j : Fin N, w (a i j)) ^ w.mult)
        * (∏ i : Fin M, ∏ᶠ w : NumberField.FinitePlace F, (⨆ j : Fin N, w (a i j))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => NumberField.mulHeight_eq (hne i)
  have hR : (∏ i : Fin M, ((N : ℝ) ^ (d / 2) * Height.mulHeight (a i)))
      = (∏ i : Fin M, ((N : ℝ) ^ (d / 2) *
            ∏ w : NumberField.InfinitePlace F, (⨆ j : Fin N, w (a i j)) ^ w.mult))
        * (∏ i : Fin M, ∏ᶠ w : NumberField.FinitePlace F, (⨆ j : Fin N, w (a i j))) := by
    rw [Finset.prod_mul_distrib, hH, Finset.prod_mul_distrib]
    ring
  rw [hR]
  exact le_trans hb (le_of_eq (by ring))

end Work.BW
