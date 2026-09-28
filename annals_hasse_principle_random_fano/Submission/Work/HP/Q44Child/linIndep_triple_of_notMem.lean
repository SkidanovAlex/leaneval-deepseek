import Mathlib
import Submission.Work.HP.Q44Child.SuperDefs

/-!
# A triple involving a vector outside a rank-`2` sublattice is `ℝ`-independent

Let `b` be a `ℤ`-basis of `ℤ^5` and let `v : ℤ^5` not lie in the `ℤ`-span of `b 0` and `b 1`.
Then the three vectors `toE (b 0)`, `toE (b 1)`, `toE v` of `E5 = ℝ^5` are `ℝ`-linearly
independent.

The point is that `toE` (the tautological inclusion `ℤ^5 ↪ ℝ^5`) sends a `ℤ`-basis of `ℤ^5`
to an `ℝ`-basis of `ℝ^5`; hence the coordinates of `toE v` in that `ℝ`-basis are exactly the
images of the integer coordinates of `v` in the `ℤ`-basis `b`.  A real linear relation then
forces the integer coordinates of `v` outside `{0, 1}` to vanish, i.e. `v` to lie in the
`ℤ`-span of `b 0, b 1`.
-/

namespace Work.HP.Q44Child

set_option autoImplicit false
set_option maxHeartbeats 800000

open Module

noncomputable section

/-- The `ℝ`-span of the standard lattice `ℤ^5 ⊆ ℝ^5` is all of `ℝ^5`. -/
lemma span_range_toE_eq_top : Submodule.span ℝ (Set.range toE) = ⊤ := by
  rw [eq_top_iff]
  have h1 : Set.range (PiLp.basisFun 2 ℝ (Fin 5)) ⊆ Set.range toE := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i (1 : ℤ), by rw [PiLp.basisFun_apply, PiLp.single, toE_single]⟩
  calc ⊤ = Submodule.span ℝ (Set.range (PiLp.basisFun 2 ℝ (Fin 5))) :=
        (Module.Basis.span_eq _).symm
    _ ≤ Submodule.span ℝ (Set.range toE) := Submodule.span_mono h1

/-- The image under `toE` of a `ℤ`-basis of `ℤ^5` spans `ℝ^5` over `ℝ`. -/
lemma toE_span_top_le (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) :
    ⊤ ≤ Submodule.span ℝ (Set.range fun i : Fin 5 => toE (b i)) := by
  have hrange : Set.range toE ⊆ Submodule.span ℝ (Set.range fun i : Fin 5 => toE (b i)) := by
    rintro _ ⟨u, rfl⟩
    have h2 : toE u = ∑ i : Fin 5, ((b.repr u i : ℤ) : ℝ) • toE (b i) := by
      conv_lhs => rw [← b.sum_repr u]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
      exact (Int.cast_smul_eq_zsmul ℝ (b.repr u i) (toE (b i))).symm
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [← span_range_toE_eq_top]
  exact Submodule.span_le.mpr hrange

/-- The `ℝ`-basis of `ℝ^5` obtained by applying `toE` to a `ℤ`-basis of `ℤ^5`. -/
noncomputable def toEBasis (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) :
    Module.Basis (Fin 5) ℝ E5 :=
  basisOfTopLeSpanOfCardEqFinrank (fun i : Fin 5 => toE (b i)) (toE_span_top_le b)
    (by rw [Module.finrank_eq_card_basis (PiLp.basisFun 2 ℝ (Fin 5))])

@[simp] lemma toEBasis_apply (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) (i : Fin 5) :
    toEBasis b i = toE (b i) :=
  congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) i

/-- In the `ℝ`-basis `toE ∘ b`, the coordinates of `toE w` are the images of the `ℤ`-coordinates
of `w` in the `ℤ`-basis `b`. -/
lemma repr_toEBasis (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) (w : Fin 5 → ℤ) (k : Fin 5) :
    (toEBasis b).repr (toE w) k = (b.repr w k : ℝ) := by
  rw [← Basis.equivFun_apply]
  have h2 : toE w = ∑ i : Fin 5, ((b.repr w i : ℤ) : ℝ) • toEBasis b i := by
    conv_lhs => rw [← b.sum_repr w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, toEBasis_apply]
    exact (Int.cast_smul_eq_zsmul ℝ (b.repr w i) (toE (b i))).symm
  rw [h2, map_sum]
  rw [Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Basis.equivFun_self]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi; simp [hi]
  · intro hk; exact absurd (Finset.mem_univ k) hk

end

theorem linIndep_triple_of_notMem {b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)} {v : Fin 5 → ℤ}
    (hv : v ∉ Submodule.span ℤ (Set.range fun i : Fin 2 => b (Fin.castLE (by norm_num : 2 ≤ 5) i))) :
    LinearIndependent ℝ ![Work.HP.Q44Child.toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2))),
      Work.HP.Q44Child.toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2))),
      Work.HP.Q44Child.toE v] := by
  -- Some coordinate of `v` outside `{0, 1}` is non-zero.
  have hk₀ : ∃ k : Fin 5, k ≠ 0 ∧ k ≠ 1 ∧ b.repr v k ≠ 0 := by
    by_contra h
    have h' : ∀ k : Fin 5, k ≠ 0 → k ≠ 1 → b.repr v k = 0 := by
      intro k h0 h1
      by_contra hne
      exact h ⟨k, h0, h1, hne⟩
    refine hv ?_
    rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases h0 : k = 0
    · subst h0
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    by_cases h1 : k = 1
    · subst h1
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
    · rw [h' k h0 h1, zero_smul]
      exact Submodule.zero_mem _
  obtain ⟨k₀, hk₀ne0, hk₀ne1, hk₀v⟩ := hk₀
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- Coordinates of the three vectors in the `ℝ`-basis `toE ∘ b`.
  have hvcoord : ∀ k : Fin 5, ((toEBasis b).coord k) (toE v) = (b.repr v k : ℝ) := by
    intro k
    rw [Basis.coord_apply, repr_toEBasis]
  have h0coord : ∀ k : Fin 5,
      ((toEBasis b).coord k) (toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2)))) =
        if (0 : Fin 5) = k then 1 else 0 := by
    intro k
    rw [show Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2) = (0 : Fin 5) from rfl,
      ← toEBasis_apply, Basis.coord_apply, Basis.repr_self_apply]
  have h1coord : ∀ k : Fin 5,
      ((toEBasis b).coord k) (toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2)))) =
        if (1 : Fin 5) = k then 1 else 0 := by
    intro k
    rw [show Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2) = (1 : Fin 5) from rfl,
      ← toEBasis_apply, Basis.coord_apply, Basis.repr_self_apply]
  -- Evaluating the linear relation in each coordinate.
  have key : ∀ k : Fin 5, g 0 * (if (0 : Fin 5) = k then (1:ℝ) else 0)
      + g 1 * (if (1 : Fin 5) = k then (1:ℝ) else 0) + g 2 * (b.repr v k : ℝ) = 0 := by
    intro k
    have h1 : ((toEBasis b).coord k)
        (∑ i : Fin 3, g i • (![toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2))),
          toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2))), toE v] : Fin 3 → E5) i) = 0 := by
      rw [hg, map_zero]
    rw [Fin.sum_univ_three] at h1
    rw [show (![toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2))),
        toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2))), toE v] : Fin 3 → E5) 0
        = toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2))) from rfl,
      show (![toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2))),
        toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2))), toE v] : Fin 3 → E5) 1
        = toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2))) from rfl,
      show (![toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (0 : Fin 2))),
        toE (b (Fin.castLE (by norm_num : 2 ≤ 5) (1 : Fin 2))), toE v] : Fin 3 → E5) 2
        = toE v from rfl] at h1
    simp only [map_add, map_smul, smul_eq_mul, h0coord k, h1coord k, hvcoord k] at h1
    exact h1
  have hg2 : g 2 = 0 := by
    have hk := key k₀
    rw [ite_eq_right (Ne.symm hk₀ne0), ite_eq_right (Ne.symm hk₀ne1)] at hk
    simp only [mul_zero, zero_add, add_zero] at hk
    have hkv' : ((b.repr v k₀ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk₀v
    exact (mul_eq_zero.mp hk).resolve_right hkv'
  have hg0 : g 0 = 0 := by
    have hk := key 0
    rw [ite_eq_left rfl, ite_eq_right (by decide : ¬ ((1 : Fin 5) = 0))] at hk
    simpa [hg2] using hk
  have hg1 : g 1 = 0 := by
    have hk := key 1
    rw [ite_eq_right (by decide : ¬ ((0 : Fin 5) = 1)), ite_eq_left rfl] at hk
    simpa [hg2] using hk
  intro i
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2

end Work.HP.Q44Child
