import Mathlib
import Submission.Work.CoreTopology.Basic

/-!
# `P.carrier` is closed

For a parametrised torus `P : Work.CoreTopology.ParamTorus` the underlying surface
`P.carrier = range (fun p : ℝ × ℝ => P.psi p.1 p.2)` is a closed subset of `ℝ³`.

The point is that the parametrisation is `2π`-periodic in each variable, so the
image of the whole parameter plane agrees with the image of the compact square
`[0, 2π] × [0, 2π]`.  A continuous image of a compact set is compact, and `ℝ³` is
Hausdorff, so `P.carrier` is closed.

The reduction of an arbitrary parameter to the fundamental domain is the map
`redParam t = 2π · fract (t / 2π)`; `redParam_add` records that `t` differs from
`redParam t` by an integer multiple of `2π`, and `psi_add_int_mul` /
`psi_add_int_mul_right` record the periodicity of `P.psi` in each variable.
-/

namespace Work.CoreTopology

open Set

noncomputable section

/-- Reduce a real parameter to the fundamental interval `[0, 2π]`: the fractional
part of `t / 2π`, rescaled by `2π`. -/
def redParam (t : ℝ) : ℝ := (2 * Real.pi) * Int.fract (t / (2 * Real.pi))

/-- `redParam` lands in `[0, 2π]`. -/
lemma redParam_mem (t : ℝ) : redParam t ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  refine ⟨mul_nonneg (le_of_lt h2pi) (Int.fract_nonneg _), ?_⟩
  exact le_of_lt (calc (2 * Real.pi) * Int.fract (t / (2 * Real.pi)) < (2 * Real.pi) * 1 :=
        mul_lt_mul_of_pos_left (Int.fract_lt_one _) h2pi
    _ = 2 * Real.pi := mul_one _)

/-- `t` differs from `redParam t` by an integer multiple of `2π`. -/
lemma redParam_add (t : ℝ) :
    redParam t + ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) = t := by
  have h := Int.floor_add_fract (t / (2 * Real.pi))
  have h2 : (2 * Real.pi) *
      (((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) + Int.fract (t / (2 * Real.pi))) = t := by
    rw [h]; field_simp
  rw [mul_add] at h2
  rw [redParam]
  linarith [h2]

/-- `P.psi` is invariant under adding an integer multiple of `2π` to the first
parameter. -/
lemma psi_add_int_mul (P : ParamTorus) (x y : ℝ) (n : ℤ) :
    P.psi (x + (n : ℝ) * (2 * Real.pi)) y = P.psi x y := by
  have hper : Function.Periodic (fun x : ℝ => P.psi x y) (2 * Real.pi) :=
    fun x => P.per_left x y
  exact hper.int_mul n x

/-- `P.psi` is invariant under adding an integer multiple of `2π` to the second
parameter. -/
lemma psi_add_int_mul_right (P : ParamTorus) (x y : ℝ) (n : ℤ) :
    P.psi x (y + (n : ℝ) * (2 * Real.pi)) = P.psi x y := by
  have hper : Function.Periodic (fun y : ℝ => P.psi x y) (2 * Real.pi) :=
    fun y => P.per_right x y
  exact hper.int_mul n y

/-- Any point of the torus is the image of a pair in the fundamental square. -/
lemma psi_redParam (P : ParamTorus) (x y : ℝ) :
    P.psi (redParam x) (redParam y) = P.psi x y := by
  rw [← psi_add_int_mul P (redParam x) (redParam y) ⌊x / (2 * Real.pi)⌋, redParam_add x,
    ← psi_add_int_mul_right P x (redParam y) ⌊y / (2 * Real.pi)⌋, redParam_add y]

theorem isClosed_carrier (P : Work.CoreTopology.ParamTorus) : IsClosed P.carrier := by
  have hK : IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : Continuous (fun p : ℝ × ℝ => P.psi p.1 p.2) := P.cont
  have hcarrier : P.carrier =
      (fun p : ℝ × ℝ => P.psi p.1 p.2) ''
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    apply Set.Subset.antisymm
    · rintro X ⟨⟨x, y⟩, rfl⟩
      exact ⟨(redParam x, redParam y), ⟨⟨redParam_mem x, redParam_mem y⟩, psi_redParam P x y⟩⟩
    · rintro X ⟨⟨x, y⟩, _, rfl⟩
      exact ⟨(x, y), rfl⟩
  rw [hcarrier]
  exact (hK.image hcont).isClosed

end

end Work.CoreTopology
