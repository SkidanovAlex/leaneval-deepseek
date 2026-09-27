import Mathlib
import Submission.Work.EKLContract.Defs

/-!
# Facts about `Γ₃ = SL₃(ℤ) ⊂ SL₃(ℝ)`

`Γ₃` is the image of `Matrix.SpecialLinearGroup (Fin 3) ℤ` under `Matrix.SpecialLinearGroup.map
(Int.castRingHom ℝ)`, i.e. the subgroup of integral matrices in `SL₃(ℝ)`.

We prove the four basic facts used elsewhere in the EKL development:

* `Γ₃` is countable (it is the image of the countable group `SL₃(ℤ)`);
* `Γ₃` is closed in `SL₃(ℝ)` (it is a discrete subgroup of a topological group —
  `Matrix.SpecialLinearGroup.discreteSpecialLinearGroupIntRangeSL` + the general fact that a
  discrete subgroup of a `T₂` topological group is closed);
* every entry of a matrix in `Γ₃` is an integer;
* the projection `SL₃(ℝ) → SL₃(ℝ)/Γ₃` is injective on a neighbourhood `V` of the identity:
  `a⁻¹ b ∈ Γ₃` with `a, b ∈ V` forces `a = b`.  (Equivalently: the quotient map has a local
  section at the identity coset, since `Γ₃` is discrete.)
-/

set_option linter.style.haveILetI false

namespace Work.EKLContract.Lemmas

open Filter Topology
open Work.EKLContract

/-- `SL₃(ℤ)` is countable: it is a subtype of the countable type `Matrix (Fin 3) (Fin 3) ℤ` via
the injective coercion to the underlying matrix. -/
lemma countable_specialLinearGroup_int : Countable (Matrix.SpecialLinearGroup (Fin 3) ℤ) := by
  have hM : Countable (Matrix (Fin 3) (Fin 3) ℤ) :=
    (inferInstance : Countable (Fin 3 → Fin 3 → ℤ))
  letI := hM
  exact Function.Injective.countable
    (f := fun A : Matrix.SpecialLinearGroup (Fin 3) ℤ => (A : Matrix (Fin 3) (Fin 3) ℤ))
    (fun A B hAB => Subtype.ext hAB)

/-- `Γ₃ = SL₃(ℤ)` is countable. -/
lemma countable_Γ3 : Countable Γ3 := by
  haveI hSL : Countable (Matrix.SpecialLinearGroup (Fin 3) ℤ) :=
    countable_specialLinearGroup_int
  have h : (Set.range (Matrix.SpecialLinearGroup.map (n := Fin 3) (Int.castRingHom ℝ))).Countable :=
    Set.countable_range _
  rw [← MonoidHom.coe_range] at h
  exact h

/-- `Γ₃` is a discrete subgroup of `SL₃(ℝ)`; the Mathlib instance
`discreteSpecialLinearGroupIntRangeSL` gives discreteness of the range of the coefficient
extension, which is `Γ₃` by definition. -/
instance instDiscreteTopologyΓ3 : DiscreteTopology Γ3 :=
  (inferInstance : DiscreteTopology
    (MonoidHom.range (Matrix.SpecialLinearGroup.map (n := Fin 3) (Int.castRingHom ℝ))))

/-- `Γ₃ = SL₃(ℤ)` is closed in `SL₃(ℝ)`. -/
lemma isClosed_Γ3 : IsClosed (Γ3 : Set SL3) :=
  Subgroup.isClosed_of_discrete

/-- Every entry of an element of `Γ₃` is (the image of) an integer. -/
lemma Γ3_integral_entries :
    ∀ γ : SL3, γ ∈ Γ3 → ∀ i j : Fin 3,
      ∃ k : ℤ, (γ : Matrix (Fin 3) (Fin 3) ℝ) i j = k := by
  intro γ hγ i j
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.mp hγ
  refine ⟨A i j, ?_⟩
  rw [← hA, Matrix.SpecialLinearGroup.coe_matrix_coe, Matrix.map_apply]
  norm_num

/-- The quotient map `SL₃(ℝ) → SL₃(ℝ)/Γ₃` is injective on a neighbourhood of the identity:
there is an open `V ∋ 1` such that `a⁻¹ b ∈ Γ₃` with `a, b ∈ V` forces `a = b`.

Since `Γ₃` is discrete there is a neighbourhood `U ∋ 1` with `U ∩ Γ₃ = {1}`; choosing
`symmetric` neighbourhoods `V ⊆ W ∩ W⁻¹` with `W/W ⊆ U` gives `a⁻¹ b ∈ U ∩ Γ₃ = {1}` whenever
`a, b ∈ V` and `a⁻¹ b ∈ Γ₃`, whence `a = b`. -/
lemma exists_open_injective_Γ3 :
    ∃ V : Set SL3, IsOpen V ∧ (1 : SL3) ∈ V ∧
      ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ Γ3 → a = b := by
  have hd : IsDiscrete (Γ3 : Set SL3) := isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ3)
  obtain ⟨U, hU, hUΓ⟩ := nhds_inter_eq_singleton_of_mem_discrete hd Γ3.one_mem
  obtain ⟨W, hW, hWU⟩ := exists_nhds_split_inv hU
  have hW' : W⁻¹ ∈ 𝓝 (1 : SL3) := inv_mem_nhds_one SL3 hW
  have hmem : W ∩ W⁻¹ ∈ 𝓝 (1 : SL3) := Filter.inter_mem hW hW'
  obtain ⟨V, hVsub, hVopen, hV1⟩ := mem_nhds_iff.mp hmem
  refine ⟨V, hVopen, hV1, ?_⟩
  intro a ha b hb hab
  -- `a⁻¹ ∈ W` and `b⁻¹ ∈ W` because `V` is contained in both `W` and `W⁻¹`
  have haW : a⁻¹ ∈ W := Set.mem_inv.mp (hVsub ha).2
  have hbW : b⁻¹ ∈ W := Set.mem_inv.mp (hVsub hb).2
  have habU : a⁻¹ * b ∈ U := by
    simpa using hWU a⁻¹ haW b⁻¹ hbW
  have hmem1 : a⁻¹ * b ∈ ({1} : Set SL3) := by
    rw [← hUΓ]
    exact ⟨habU, hab⟩
  exact inv_mul_eq_one.mp (by simpa using hmem1)

theorem Gamma3Facts :
    Countable Work.EKLContract.Γ3 ∧ IsClosed (Work.EKLContract.Γ3 : Set Work.EKLContract.SL3) ∧
    (∀ γ : Work.EKLContract.SL3, γ ∈ Work.EKLContract.Γ3 → ∀ i j : Fin 3,
      ∃ k : ℤ, (γ : Matrix (Fin 3) (Fin 3) ℝ) i j = k) ∧
    (∃ V : Set Work.EKLContract.SL3, IsOpen V ∧ (1 : Work.EKLContract.SL3) ∈ V ∧
      ∀ a ∈ V, ∀ b ∈ V, a⁻¹ * b ∈ Work.EKLContract.Γ3 → a = b) :=
  ⟨countable_Γ3, isClosed_Γ3, Γ3_integral_entries, exists_open_injective_Γ3⟩

end Work.EKLContract.Lemmas
