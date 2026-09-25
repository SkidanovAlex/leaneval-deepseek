import Mathlib
import Submission.NK.HeckeL.Zeta

namespace NK.HeckeL.Series

open Asymptotics Filter

/-- If two continuous complex-valued functions on `(1, ∞)` have the same exponential
and one of them is `O(1)` near `1⁺`, then so is the other: the difference is continuous
with values in the discrete subgroup `2πiℤ`, hence constant on the connected set `(1, ∞)`. -/
theorem isBigO_of_continuous_exp_eq (f g : ℝ → ℂ) (hf : ContinuousOn f (Set.Ioi 1))
    (hg : ContinuousOn g (Set.Ioi 1))
    (hexp : ∀ s ∈ Set.Ioi (1 : ℝ), Complex.exp (f s) = Complex.exp (g s))
    (hgO : (fun s : ℝ => g s) =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ))) :
    (fun s : ℝ => f s) =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  have hS : IsPreconnected (Set.Ioi (1 : ℝ)) := isPreconnected_Ioi
  have hFcont : ContinuousOn (fun s : ℝ => f s - g s) (Set.Ioi 1) := hf.sub hg
  have hT : IsDiscrete
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    rw [isDiscrete_iff_discreteTopology]
    exact NormedSpace.discreteTopology_zmultiples _
  have hmap : Set.MapsTo (fun s : ℝ => f s - g s) (Set.Ioi 1)
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    intro s hs
    have hexps : Complex.exp (f s - g s) = 1 := by
      rw [Complex.exp_sub, hexp s hs, div_self (Complex.exp_ne_zero (g s))]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexps
    change f s - g s ∈ AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I)
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul]
    exact hn.symm
  have hconst : ∀ x ∈ Set.Ioi (1 : ℝ), ∀ y ∈ Set.Ioi (1 : ℝ), f x - g x = f y - g y :=
    fun x hx y hy => hS.constant_of_mapsTo hT hFcont hmap hx hy
  have h2 : (2 : ℝ) ∈ Set.Ioi (1 : ℝ) := by norm_num
  have hev : (fun s : ℝ => f s) =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun s : ℝ => g s + (f 2 - g 2)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioi (1 : ℝ), self_mem_nhdsWithin, ?_⟩
    intro s hs
    exact sub_eq_iff_eq_add'.mp (hconst s hs 2 h2)
  have hb : (fun s : ℝ => g s + (f 2 - g 2)) =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun _ : ℝ => (1 : ℂ)) :=
    hgO.add (isBigO_const_one ℂ (f 2 - g 2) _)
  exact hb.congr' hev.symm Filter.EventuallyEq.rfl

end NK.HeckeL.Series
