import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Repel.Spec

namespace Work.Horn

open Set Filter Topology Metric
open scoped Topology

/-! ## Elementary conjugacy of the rescaled pushdown with `pushdown R`

`germ1 s R = ζ ↦ s * pushdown R (ζ/s)` is the affine conjugate of `pushdown R` by the
rescalings `ζ ↦ s * ζ` and `ζ ↦ s⁻¹ * ζ`.  These are the two iteration identities that
transport orbits (and their uniform convergence to `0`). -/

private lemma resc_germ1_mul {s : ℂ} (hs : s ≠ 0) (R : ℂ → ℂ) (z : ℂ) :
    Work.Repel.germ1 s R (s * z) = s * MandelDim.pushdown R z := by
  rw [Work.Repel.germ1_apply, mul_div_cancel_left₀ z hs]

private lemma resc_germ1_iterate {s : ℂ} (hs : s ≠ 0) (R : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    (Work.Repel.germ1 s R)^[n] (s * z) = s * (MandelDim.pushdown R)^[n] z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', resc_germ1_mul hs]

private lemma resc_pushdown_iterate {s : ℂ} (hs : s ≠ 0) (R : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    (MandelDim.pushdown R)^[n] z = s⁻¹ * (Work.Repel.germ1 s R)^[n] (s * z) := by
  rw [resc_germ1_iterate hs R n z]
  exact (inv_mul_cancel_left₀ hs ((MandelDim.pushdown R)^[n] z)).symm

private lemma isOpenMap_mul_const (s : ℂ) (hs : s ≠ 0) :
    IsOpenMap (fun ζ : ℂ => s * ζ) := by
  simpa [smul_eq_mul] using isOpenMap_smul₀ (G₀ := ℂ) (α := ℂ) hs

/-- **The parabolic basin is invariant under the rescaling `ζ ↦ s · ζ`.**

`Work.Repel.germ1 s R` is the pushed-down map `ζ ↦ s * pushdown R (ζ/s)` and
`(fun ζ => s * ζ) '' D` is its natural domain (`Work.Repel.Dgerm1`).  For `s ≠ 0` the map
`ζ ↦ s * ζ` conjugates the dynamics of `pushdown R` on `D` to that of `germ1 s R` on `s • D`,
so the uniform parabolic basin `MandelDim.ParabolicBasin` is transported.

Reusable reduction: `(Work.Repel.germ1 s R)^[n] (s * z) = s * (pushdown R)^[n] z` for every `n`
(induction, from `Work.Repel.germ1_apply` and `mul_div_cancel_left₀`); the uniform convergence
uses `‖s * x‖ = ‖s‖ * ‖x‖` and the `n = 0` case of the basin definition gives `D`. -/
theorem basin_rescale {s : ℂ} (hs : s ≠ 0) (R : ℂ → ℂ) (D : Set ℂ) (z : ℂ) :
    z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown R) D ↔
      s * z ∈ MandelDim.ParabolicBasin (Work.Repel.germ1 s R) ((fun ζ => s * ζ) '' D) := by
  have hs' : s⁻¹ ≠ 0 := inv_ne_zero hs
  have hopen : IsOpenMap (fun ζ : ℂ => s * ζ) := isOpenMap_mul_const s hs
  have hopen' : IsOpenMap (fun ζ : ℂ => s⁻¹ * ζ) := isOpenMap_mul_const s⁻¹ hs'
  constructor
  · -- forward: push a basin neighbourhood `U` of `z` forward along `ζ ↦ s * ζ`
    rintro ⟨U, hU, hmap, hconv⟩
    refine ⟨(fun ζ => s * ζ) '' U, hopen.image_mem_nhds hU, ?_, ?_⟩
    · -- all iterates of `germ1 s R` stay in `s • D`
      intro n y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨(MandelDim.pushdown R)^[n] x, hmap n hx, (resc_germ1_iterate hs R n x).symm⟩
    · -- uniform convergence to `0`
      rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
      intro ε hε
      have hε' : 0 < ε / ‖s‖ := div_pos hε (norm_pos_iff.mpr hs)
      filter_upwards [hconv (ε / ‖s‖) hε'] with n hn y hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [resc_germ1_iterate hs R n x, dist_zero_left, norm_mul]
      calc ‖s‖ * ‖(MandelDim.pushdown R)^[n] x‖ < ‖s‖ * (ε / ‖s‖) :=
            mul_lt_mul_of_pos_left (by simpa using hn x hx) (norm_pos_iff.mpr hs)
        _ = ε := by rw [← mul_div_assoc, mul_div_cancel_left₀ ε (norm_ne_zero_iff.mpr hs)]
  · -- backward: pull a basin neighbourhood `V` of `s * z` back along `ζ ↦ s⁻¹ * ζ`
    rintro ⟨V, hV, hmap, hconv⟩
    refine ⟨(fun ζ => s⁻¹ * ζ) '' V, ?_, ?_, ?_⟩
    · simpa [inv_mul_cancel_left₀ hs z] using hopen'.image_mem_nhds hV
    · intro n y hy
      obtain ⟨v, hv, rfl⟩ := hy
      obtain ⟨d, hd, hd_eq⟩ := hmap n hv
      have h1 : s * (MandelDim.pushdown R)^[n] (s⁻¹ * v) = s * d := by
        have hg := resc_germ1_iterate hs R n (s⁻¹ * v)
        rw [mul_inv_cancel_left₀ hs v] at hg
        exact hg.symm.trans hd_eq.symm
      have h2 : (MandelDim.pushdown R)^[n] (s⁻¹ * v) = d := mul_left_cancel₀ hs h1
      rw [h2]
      exact hd
    · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
      intro ε hε
      have hε' : 0 < ε * ‖s‖ := mul_pos hε (norm_pos_iff.mpr hs)
      filter_upwards [hconv (ε * ‖s‖) hε'] with n hn y hy
      obtain ⟨v, hv, rfl⟩ := hy
      rw [resc_pushdown_iterate hs R n (s⁻¹ * v), dist_zero_left, norm_mul]
      calc ‖s⁻¹‖ * ‖(Work.Repel.germ1 s R)^[n] (s * (s⁻¹ * v))‖
          = ‖s⁻¹‖ * ‖(Work.Repel.germ1 s R)^[n] v‖ := by rw [mul_inv_cancel_left₀ hs v]
        _ < ‖s⁻¹‖ * (ε * ‖s‖) :=
            mul_lt_mul_of_pos_left (by simpa using hn v hv) (norm_pos_iff.mpr hs')
        _ = ε := by
            have h : ‖s⁻¹‖ * ‖s‖ = 1 := by
              rw [norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs)]
            calc ‖s⁻¹‖ * (ε * ‖s‖) = ε * (‖s⁻¹‖ * ‖s‖) := by ring
              _ = ε := by rw [h, mul_one]

end Work.Horn
