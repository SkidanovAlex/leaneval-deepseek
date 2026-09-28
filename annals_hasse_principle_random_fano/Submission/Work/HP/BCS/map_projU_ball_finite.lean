import Mathlib
import Submission.Work.HP.BCS.lat_span_u_zsmul

namespace Work.HP.BCS

open Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **A bounded representative in each fibre of `projU u`.**

For any lattice point `x` of `Λ` there is another lattice point `z` with the same orthogonal
projection onto `u^⊥` and with norm bounded by `‖projU u x‖ + ‖u‖`: namely
`z = x - ⌊c⌋ • u` where `c = (‖u‖²)⁻¹ ⟪x,u⟫`.

This is the one geometric input for `map_projU_ball_finite`: it shows that every value of
`projU u` on `Λ` is already taken on the (finite) set of lattice points in a slightly larger
ball. -/
lemma exists_bounded_rep (Λ : Submodule ℤ (EuclideanSpace ℝ ι))
    {u : EuclideanSpace ℝ ι} (hu : u ∈ Λ) (hu0 : u ≠ 0) (x : EuclideanSpace ℝ ι) (hx : x ∈ Λ) :
    ∃ z ∈ Λ, projU u z = projU u x ∧ ‖z‖ ≤ ‖projU u x‖ + ‖u‖ := by
  set c : ℝ := (‖u‖ ^ 2)⁻¹ * inner ℝ x u with hc
  have hxdecomp : projU u x = x - c • u := by rw [projU_apply, hc]
  refine ⟨x - (⌊c⌋ : ℤ) • u, ?_, ?_, ?_⟩
  · exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hu)
  · rw [map_sub, map_zsmul, projU_self_eq_zero u hu0, zsmul_zero, sub_zero]
  · have hz_eq : x - (⌊c⌋ : ℤ) • u = projU u x + (c - (⌊c⌋ : ℝ)) • u := by
      rw [hxdecomp, sub_smul, ← Int.cast_smul_eq_zsmul ℝ (⌊c⌋) u]
      abel
    rw [hz_eq]
    have hbound : ‖(c - (⌊c⌋ : ℝ)) • u‖ ≤ ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : c - (⌊c⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one c]
      have h0 : 0 ≤ c - (⌊c⌋ : ℝ) := by linarith [Int.floor_le c]
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (norm_nonneg u) h1.le
    calc ‖projU u x + (c - (⌊c⌋ : ℝ)) • u‖
        ≤ ‖projU u x‖ + ‖(c - (⌊c⌋ : ℝ)) • u‖ := norm_add_le _ _
      _ ≤ ‖projU u x‖ + ‖u‖ := by linarith

theorem map_projU_ball_finite (ι : Type) [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ (EuclideanSpace ℝ ι))
    (hfin : ∀ T : ℝ, {x : EuclideanSpace ℝ ι | x ∈ Λ ∧ ‖x‖ ≤ T}.Finite)
    {u : EuclideanSpace ℝ ι} (hu : u ∈ Λ) (hu0 : u ≠ 0) (T : ℝ) :
    {y : EuclideanSpace ℝ ι | y ∈ Λ.map (projUZ u) ∧ ‖y‖ ≤ T}.Finite := by
  -- Only lattice points of a fixed slightly larger ball can occur as projections.
  have hBfin : {z : EuclideanSpace ℝ ι | z ∈ Λ ∧ ‖z‖ ≤ T + ‖u‖}.Finite := hfin (T + ‖u‖)
  refine (hBfin.image (fun z => projU u z)).subset ?_
  rintro y ⟨hyproj, hyT⟩
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp hyproj
  rw [← hxy] at hyT
  have hxT : ‖projU u x‖ ≤ T := by simpa only [projUZ_apply] using hyT
  obtain ⟨z, hzΛ, hzproj, hznorm⟩ := exists_bounded_rep Λ hu hu0 x hx
  refine ⟨z, ⟨hzΛ, by linarith⟩, ?_⟩
  change projU u z = y
  rw [hzproj, ← hxy, projUZ_apply]

end Work.HP.BCS
