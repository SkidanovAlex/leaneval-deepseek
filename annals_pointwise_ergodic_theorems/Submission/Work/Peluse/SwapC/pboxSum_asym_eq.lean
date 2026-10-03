import Mathlib
import Submission.Work.Peluse.SwapC.Basic

namespace Work.Peluse.SwapC

open Work.Peluse

/-- `cornerShift H H' ω = ∑ H' + cornerShift (H - H') 0 ω`: the corner `ω·H + (1-ω)·H'` is the
full lower shift `∑ H'` plus the increment contribution. -/
lemma cornerShift_eq_sum_add {t : ℕ} (H H' : Fin t → ℤ) (ω : Fin t → Bool) :
    cornerShift H H' ω = (∑ i, H' i) + cornerShift (fun i => H i - H' i) (fun _ => 0) ω := by
  rw [cornerShift, cornerShift]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ω i <;> simp [h]

/-- Translating the base variable by the sum of the lower shifts turns the symmetric cube term of
`(H, H')` into the asymmetric cube term of the increment tuple `H - H'`. -/
lemma tsum_cube_eq (d : ℕ) (H H' : Fin d → ℤ) (f : ℤ → ℂ) :
    (∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω]) (f (x + cornerShift H H' ω)))
      = ∑' y : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
            (f (y + cornerShift (fun k => H k - H' k) (fun _ => 0) ω)) := by
  set c : ℤ := ∑ i, H' i with hc
  set dv : Fin d → ℤ := fun k => H k - H' k with hdv
  have hpt : ∀ x : ℤ, (∏ ω : Fin d → Bool, (star^[weight ω]) (f (x + cornerShift H H' ω)))
      = ∏ ω : Fin d → Bool, (star^[weight ω]) (f (x + c + cornerShift dv (fun _ => 0) ω)) := by
    intro x
    refine Finset.prod_congr rfl fun ω _ => ?_
    rw [cornerShift_eq_sum_add, hc, hdv, add_assoc]
  rw [tsum_congr hpt]
  rw [show (∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
          (f (x + c + cornerShift dv (fun _ => 0) ω)))
        = ∑' y : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
          (f (y + cornerShift dv (fun _ => 0) ω))
      from Equiv.tsum_eq (Equiv.addRight c)
        (fun z => ∏ ω : Fin d → Bool, (star^[weight ω]) (f (z + cornerShift dv (fun _ => 0) ω)))]

/-- **The asymmetric (α-)form of the multiset box sum.**  Reindexing the base variable by the
sum of the shifts of one of the two tuples turns the cube term into the asymmetric cube term of the
increment tuple `H − H'`:
`∏_ω C^{|ω|} f (x + cornerShift H H' ω) = asymCube (D H − D H') f (x + ∑_k D_k (H' k))`.
Summing over `x` (a bijection of `ℤ`) gives the stated identity.  This is the first step of
`concatStep` (KKL Lemma 6.1): the base root `f y` is then the function on which the
Cauchy–Schwarz inequality in the base variable is applied. -/
theorem pboxSum_asym_eq (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.LadderP.Swap.pboxSum d q₁ q₂ M S f
      = ((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d *
        ∑ H : Fin d → Fin M × Fin M, ∑ H' : Fin d → Fin M × Fin M,
          ∑' y : ℤ,
            Work.Peluse.SwapC.asymCube
              (fun k => Work.Peluse.LadderP.Swap.pdir (q₁ k) (q₂ k) (H k) -
                Work.Peluse.LadderP.Swap.pdir (q₁ k) (q₂ k) (H' k)) f y := by
  simp only [Work.Peluse.LadderP.Swap.pboxSum, Work.Peluse.SwapC.asymCube]
  congr 1
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  exact tsum_cube_eq d (fun k => Work.Peluse.LadderP.Swap.pdir (q₁ k) (q₂ k) (h k))
    (fun k => Work.Peluse.LadderP.Swap.pdir (q₁ k) (q₂ k) (h' k)) f

end Work.Peluse.SwapC
