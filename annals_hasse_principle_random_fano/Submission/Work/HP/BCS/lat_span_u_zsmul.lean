import Mathlib
import Submission.Work.HP.BCSDefs

/-!
# The multiples of a shortest vector in a lattice

Let `Λ ≤ EuclideanSpace ℝ ι` be a `ℤ`-submodule and let `u ∈ Λ` be a nonzero vector of
minimal norm in `Λ`.  Minimality forces `Λ ∩ ℝu = ℤu`:

* `lat_span_u_zsmul`: a point of `Λ` lying in the real line `ℝu` is an integer multiple of `u`;
* `projU_coset`: two points of `Λ` with the same orthogonal projection onto `u^⊥` differ by an
  integer multiple of `u`.

These are the two ingredients of the fibre count for `projU u` on `Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.HP.BCS

open Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A point of the lattice `Λ` lying on the real line `ℝu` spanned by a shortest vector `u ≠ 0`
is an integer multiple of `u`. -/
theorem lat_span_u_zsmul (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) {u : EuclideanSpace ℝ ι}
    (hu : u ∈ Λ) (hu0 : u ≠ 0) (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ Λ) (hxs : x ∈ Submodule.span ℝ {u}) :
    ∃ n : ℤ, x = n • u := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
  have hr_mem : (c - (⌊c⌋ : ℝ)) • u ∈ Λ := by
    rw [sub_smul, Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hu)
  have hcontra : c - (⌊c⌋ : ℝ) = 0 := by
    by_contra hne
    have hpos : 0 < c - (⌊c⌋ : ℝ) :=
      lt_of_le_of_ne (sub_nonneg.mpr (Int.floor_le c)) (Ne.symm hne)
    have hlt1 : c - (⌊c⌋ : ℝ) < 1 := by linarith [Int.lt_floor_add_one c]
    have hupos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
    have hnorm : ‖(c - (⌊c⌋ : ℝ)) • u‖ < ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      nlinarith
    have hle := hmin _ hr_mem (smul_ne_zero hpos.ne' hu0)
    linarith
  refine ⟨⌊c⌋, ?_⟩
  have hc : c = ((⌊c⌋ : ℤ) : ℝ) := by linarith
  conv_lhs => rw [hc]
  exact Int.cast_smul_eq_zsmul ℝ (⌊c⌋) u

/-- Two points of `Λ` with the same orthogonal projection onto `u^⊥` differ by an integer
multiple of `u`, when `u` is a shortest vector of `Λ`. -/
theorem projU_coset (Λ : Submodule ℤ (EuclideanSpace ℝ ι)) {u : EuclideanSpace ℝ ι}
    (hu : u ∈ Λ) (hu0 : u ≠ 0) (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖u‖ ≤ ‖x‖)
    {x₁ x₂ : EuclideanSpace ℝ ι} (hx₁ : x₁ ∈ Λ) (hx₂ : x₂ ∈ Λ)
    (h : projU u x₁ = projU u x₂) : ∃ n : ℤ, x₂ = x₁ + n • u := by
  have hmem : x₂ - x₁ ∈ Λ := Submodule.sub_mem _ hx₂ hx₁
  have hz : projU u (x₂ - x₁) = 0 := by
    rw [map_sub, h, sub_self]
  have hspan : x₂ - x₁ ∈ Submodule.span ℝ {u} := (projU_eq_zero_iff u hu0 _).mp hz
  obtain ⟨n, hn⟩ := lat_span_u_zsmul Λ hu hu0 hmin hmem hspan
  exact ⟨n, by rw [← hn]; abel⟩

end Work.HP.BCS
