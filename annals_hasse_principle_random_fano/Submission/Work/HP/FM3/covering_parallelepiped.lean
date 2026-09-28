import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Transf.Basic

/-!
# The parallelepiped covering bound for a `ℤ`-submodule `K ⊆ ℝ^ι`

If `b : Fin d → K` is a real-linearly independent family in a `ℤ`-submodule `K ⊆ ℝ^ι` with
`d = rkR K`, then every point of the real span of `K` is within `(1/2)∑ ‖b j‖` of a point of `K`
(the rounding of the coordinates of `b`).  This is the elementary covering-radius bound used in
the transference induction.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.FM3

open Work.HP Work.HP.Transf

variable {ι : Type*} [Fintype ι]

theorem covering_parallelepiped (K : Submodule ℤ (ι → ℝ)) (d : ℕ)
    (hrank : rkR K = d) (b : Fin d → (ι → ℝ)) (hbK : ∀ j, b j ∈ K)
    (hbLI : LinearIndependent ℝ b) :
    ∀ x ∈ Submodule.span ℝ (K : Set (ι → ℝ)), ∃ z ∈ K,
      rNorm (x - z) ≤ (1/2) * ∑ j, rNorm (b j) := by
  intro x hx
  have hle : Submodule.span ℝ (Set.range b) ≤ Submodule.span ℝ (K : Set (ι → ℝ)) :=
    Submodule.span_mono fun y hy => by obtain ⟨j, rfl⟩ := hy; exact hbK j
  have hfin : Module.finrank ℝ ↥(Submodule.span ℝ (Set.range b)) = d := by
    rw [finrank_span_eq_card hbLI, Fintype.card_fin]
  have hfinK : Module.finrank ℝ ↥(Submodule.span ℝ (K : Set (ι → ℝ))) = d := hrank
  have hspan : Submodule.span ℝ (Set.range b) = Submodule.span ℝ (K : Set (ι → ℝ)) :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hfinK])
  have hx' : x ∈ Submodule.span ℝ (Set.range b) := by rw [hspan]; exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx'
  refine ⟨∑ j, (⌊c j + 1 / 2⌋ : ℤ) • b j, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbK j)
  · have hxsplit : x - ∑ j, (⌊c j + 1 / 2⌋ : ℤ) • b j
        = ∑ j, (c j - (⌊c j + 1 / 2⌋ : ℝ)) • b j := by
      rw [← hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Int.cast_smul_eq_zsmul ℝ (⌊c j + 1 / 2⌋) (b j), sub_smul]
    rw [hxsplit]
    calc rNorm (∑ j, (c j - (⌊c j + 1 / 2⌋ : ℝ)) • b j)
        ≤ ∑ j, rNorm ((c j - (⌊c j + 1 / 2⌋ : ℝ)) • b j) := by
          simpa using rNorm_sum_le (Finset.univ : Finset (Fin d))
            (fun j => (c j - (⌊c j + 1 / 2⌋ : ℝ)) • b j)
      _ = ∑ j, |c j - (⌊c j + 1 / 2⌋ : ℝ)| * rNorm (b j) :=
          Finset.sum_congr rfl fun j _ => rNorm_smul _ _
      _ ≤ ∑ j, (1 / 2) * rNorm (b j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (rNorm_nonneg _)
          have h1 : (⌊c j + 1 / 2⌋ : ℝ) ≤ c j + 1 / 2 := Int.floor_le _
          have h2 : c j + 1 / 2 < (⌊c j + 1 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
          rw [abs_le]
          constructor <;> linarith
      _ = (1 / 2) * ∑ j, rNorm (b j) := by rw [Finset.mul_sum]

end Work.HP.FM3
