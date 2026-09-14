import Mathlib.NumberTheory.Height.Basic

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.Height

/-- The multiplicative height of a function `f : α → K` that vanishes outside a finite set `s`
agrees with the multiplicative height of the restriction of `f` to `s`. -/
theorem mulHeight_eq_mulHeight_finset {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
    {α : Type*} {f : α → K} (s : Finset α) (hs : ∀ i, i ∉ s → f i = 0) :
    Height.mulHeight f = Height.mulHeight (fun i : s => f i) := by
  classical
  rcases eq_or_ne f 0 with hf | hf
  · subst hf
    change Height.mulHeight (0 : α → K) = Height.mulHeight (0 : s → K)
    rw [Height.mulHeight_zero, Height.mulHeight_zero]
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hf
    have hmem₀ : i₀ ∈ s := by
      by_contra h
      exact hi₀ (hs i₀ h)
    have hsne : s.Nonempty := ⟨i₀, hmem₀⟩
    haveI : Nonempty α := ⟨i₀⟩
    haveI : Nonempty ↥s := hsne.to_subtype
    have hg : (fun i : s => f i) ≠ 0 := by
      intro h
      exact hi₀ (congrFun h ⟨i₀, hmem₀⟩)
    have hsup_eq (v : AbsoluteValue K ℝ) :
        (⨆ i : α, v (f i)) = ⨆ j : s, v (f (j : α)) := by
      have hbd : BddAbove (Set.range fun i : α => v (f i)) := by
        refine ⟨s.sup' hsne (fun j => v (f j)), ?_⟩
        rintro y ⟨i, rfl⟩
        by_cases hi : i ∈ s
        · exact Finset.le_sup' (fun j => v (f j)) hi
        · change v (f i) ≤ s.sup' hsne (fun j => v (f j))
          rw [hs i hi, map_zero]
          obtain ⟨j, hj⟩ := hsne
          exact le_trans (v.nonneg _) (Finset.le_sup' (fun j => v (f j)) hj)
      refine le_antisymm (ciSup_le fun i => ?_) (ciSup_le fun j => ?_)
      · by_cases hi : i ∈ s
        · exact Finite.le_ciSup_of_le (f := fun j : s => v (f (j : α))) ⟨i, hi⟩ le_rfl
        · change v (f i) ≤ ⨆ j : s, v (f (j : α))
          rw [hs i hi, map_zero]
          exact Real.iSup_nonneg_of_nonnegHomClass v (fun j : s => f (j : α))
      · exact le_ciSup hbd (j : α)
    rw [Height.mulHeight_eq hf, Height.mulHeight_eq hg]
    congr 1
    · exact congrArg Multiset.prod (Multiset.map_congr rfl (fun v _ => hsup_eq v))
    · exact finprod_congr (fun v => hsup_eq v.val)

/-- For a finitely supported function, the height of the underlying function (on the full,
possibly infinite, index type) equals `Finsupp.mulHeight`, the height restricted to the support. -/
theorem mulHeight_finsupp_coe_eq {K : Type*} [Field K] [Height.AdmissibleAbsValues K]
    {α : Type*} (x : α →₀ K) :
    Height.mulHeight (⇑x) = Finsupp.mulHeight x := by
  classical
  rw [Finsupp.mulHeight]
  exact mulHeight_eq_mulHeight_finset x.support (fun i hi => Finsupp.notMem_support_iff.mp hi)

end Commons.NumberTheory.Height