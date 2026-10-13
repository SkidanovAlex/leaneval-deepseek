import Mathlib
import Submission.Work.WilE7.MainDesignDefs

/-!
# A5: monotonicity of `NullDimLE` in the dimension index

`Work.WilE7.MainDesign.NullDimLE X μ` says that the image of `X` under *every* projection onto
`μ + 1` coordinates is Lebesgue-null.  Since a set of dimension `≤ μ` also has dimension `≤ ν`
for every `ν ≥ μ`, this measure is monotone in the index: `NullDimLE X μ → NullDimLE X ν`
whenever `μ ≤ ν`.

The point of the proof is that a reduction of the number of coordinates cannot destroy
nullity: the projection `π : ℝ^{ν+1} → ℝ^{μ+1}` dropping some coordinates is a surjective linear
map, and a surjective linear map pulls null sets back to null sets (its push-forward of
Lebesgue measure is a positive multiple — possibly `⊤` — of Lebesgue measure, by
`LinearMap.exists_map_addHaar_eq_smul_addHaar`).  Concretely, if `e : Fin (ν+1) ↪ Fin N` is a
`ν+1`-coordinate embedding and `e' := e ∘ j` for an injection `j : Fin (μ+1) ↪ Fin (ν+1)`, then
`π_e' = π ∘ π_e`, so the image of `X` under `π_e` is contained in the `π`-preimage of the
`π_e'`-image, which is null by hypothesis.
-/

open MeasureTheory

namespace Work.WilE7.DimAPI

/-- **A surjective linear map `ℝ^n → ℝ^m` pulls null sets back to null sets.**  The push-forward
of Lebesgue measure under a surjective linear map is a positive (possibly infinite) multiple of
Lebesgue measure on the target (`LinearMap.exists_map_addHaar_eq_smul_addHaar`), so it vanishes
exactly on the null sets. -/
theorem volume_preimage_null_of_surjective_linear {n m : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hL : Function.Surjective L)
    {A : Set (Fin m → ℝ)} (hA : volume A = 0) : volume (L ⁻¹' A) = 0 := by
  -- Replace `A` by a measurable null superset, so that `Measure.map_apply` applies.
  obtain ⟨A', hAA', hA'm, hA'0⟩ := exists_measurable_superset_of_null hA
  refine measure_mono_null (Set.preimage_mono hAA') ?_
  rw [← Measure.map_apply L.continuous_of_finiteDimensional.measurable hA'm]
  obtain ⟨c, _hc, hceq⟩ :=
    LinearMap.exists_map_addHaar_eq_smul_addHaar (𝕜 := ℝ) L volume volume hL
  rw [hceq, Measure.smul_apply, hA'0]
  exact smul_zero c

theorem nullDimLE_mono_dim {N μ ν : ℕ} {X : Set (Fin N → ℝ)}
    (h : Work.WilE7.MainDesign.NullDimLE X μ) (hμν : μ ≤ ν) :
    Work.WilE7.MainDesign.NullDimLE X ν := by
  intro e
  -- An injection of the `μ + 1` coordinates into the `ν + 1` coordinates.
  have hle : μ + 1 ≤ ν + 1 := Nat.succ_le_succ hμν
  let j : Fin (μ + 1) ↪ Fin (ν + 1) := ⟨Fin.castLE hle, Fin.castLE_injective hle⟩
  -- The projection `ℝ^{ν+1} → ℝ^{μ+1}` that keeps the coordinates indexed by `j`.
  let Φ : (Fin (ν + 1) → ℝ) →ₗ[ℝ] (Fin (μ + 1) → ℝ) :=
    LinearMap.funLeft ℝ ℝ (j : Fin (μ + 1) → Fin (ν + 1))
  have hsurj : Function.Surjective Φ := by
    intro z
    -- Extend `z` from the coordinates `j` to all the `ν + 1` coordinates along `invFun j`.
    refine ⟨(LinearMap.funLeft ℝ ℝ (Function.invFun (j : Fin (μ + 1) → Fin (ν + 1)))) z, ?_⟩
    funext i
    show z (Function.invFun (j : Fin (μ + 1) → Fin (ν + 1)) (j i)) = z i
    rw [Function.leftInverse_invFun j.injective i]
  -- The composed embedding, whose projection is the one required by the hypothesis.
  let e' : Fin (μ + 1) ↪ Fin N := j.trans e
  have hcomp : (fun x : Fin N → ℝ => Φ (x ∘ e)) = (fun x : Fin N → ℝ => x ∘ e') := by
    funext x i
    simp [Φ, e', LinearMap.funLeft_apply, Function.comp]
  have himg : Φ '' ((fun x : Fin N → ℝ => x ∘ e) '' X) =
      (fun x : Fin N → ℝ => x ∘ e') '' X := by
    rw [Set.image_image, hcomp]
  -- `π_{e'} = Φ ∘ π_e`, so the `π_e`-image of `X` sits in the `Φ`-preimage of a null set.
  have hnull : volume (Φ '' ((fun x : Fin N → ℝ => x ∘ e) '' X)) = 0 := by
    rw [himg]
    exact h e'
  refine measure_mono_null ?_ (volume_preimage_null_of_surjective_linear Φ hsurj hnull)
  intro y hy
  exact ⟨y, hy, rfl⟩

end Work.WilE7.DimAPI
