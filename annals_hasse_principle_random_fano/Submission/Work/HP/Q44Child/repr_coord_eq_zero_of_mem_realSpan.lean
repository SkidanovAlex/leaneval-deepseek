import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs
import Submission.Work.HP.Q44Child.linIndep_triple_of_notMem

namespace Work.HP.Q44Child

open Module

/-- The coordinate functional `(toEBasis b).coord k` evaluated at `toE (b j)` is
`1` if `j = k` and `0` otherwise. -/
lemma toEBasis_coord_apply_basis (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) (j k : Fin 5) :
    (toEBasis b).coord k (toE (b j)) = if j = k then (1 : ℝ) else 0 := by
  rw [Basis.coord_apply, repr_toEBasis, Basis.repr_self, Finsupp.single_apply]
  by_cases h : j = k <;> simp [h]

/-- If a lattice vector `v` has `toE v` in the `ℝ`-span of `toE (b 0), toE (b 1)` for a
`ℤ`-basis `b` of `ℤ^5`, then the coordinates of `v` in the basis `b` at every index other than
`0, 1` vanish.

Route: `toEBasis b : Module.Basis (Fin 5) ℝ E5` (from `linIndep_triple_of_notMem.lean`) has
`toEBasis b i = toE (b i)`, and `repr_toEBasis` identifies its coordinates with `b.repr`;
the coordinate functional `(toEBasis b).coord k` vanishes on `toE (b 0), toE (b 1)` when
`k ≠ 0, 1`, hence on their `ℝ`-span. -/
theorem repr_coord_eq_zero_of_mem_realSpan (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ))
    (v : Fin 5 → ℤ) (k : Fin 5) (hk0 : k ≠ 0) (hk1 : k ≠ 1)
    (hv : Work.HP.Q44Child.toE v ∈ Submodule.span ℝ
      (Set.range fun i : Fin 2 => Work.HP.Q44Child.toE (b (Fin.castLE (by norm_num : 2 ≤ 5) i)))) :
    b.repr v k = 0 := by
  -- The coordinate functional `(toEBasis b).coord k` vanishes on the two generators.
  have hspan : Submodule.span ℝ
      (Set.range fun i : Fin 2 => toE (b (Fin.castLE (by norm_num : 2 ≤ 5) i))) ≤
      LinearMap.ker ((toEBasis b).coord k) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change (toEBasis b).coord k (toE (b (Fin.castLE (by norm_num : 2 ≤ 5) i))) = 0
    have hi : Fin.castLE (by norm_num : 2 ≤ 5) i = (0 : Fin 5) ∨
        Fin.castLE (by norm_num : 2 ≤ 5) i = (1 : Fin 5) := by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hi with h | h
    · rw [h, toEBasis_coord_apply_basis, ite_eq_right (Ne.symm hk0)]
    · rw [h, toEBasis_coord_apply_basis, ite_eq_right (Ne.symm hk1)]
  -- Evaluate it at `toE v` and read off the coordinate.
  have hzero : (toEBasis b).coord k (toE v) = 0 := by
    simpa [LinearMap.mem_ker] using hspan hv
  rw [Basis.coord_apply, repr_toEBasis] at hzero
  exact Int.cast_eq_zero.mp hzero

end Work.HP.Q44Child
