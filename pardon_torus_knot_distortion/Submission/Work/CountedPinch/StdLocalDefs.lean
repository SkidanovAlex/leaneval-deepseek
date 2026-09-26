import Mathlib
import Submission.Work.CountedPinch.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.Basic

/-!
# The local model for `sliceArcsBody_standard_local`

This module collects the concrete objects and the elementary real-analysis facts behind the
non-degeneracy certificate `Work.CountedPinch.sliceArcsBody_standard_local`: the standard torus,
the box `PBox (1/4) (3,0,0) 1` and the cutting plane `{z = 0}`.

With `s = 2^{1/3}/12` and `α = arcsin s`:

* `Work.CountedPinch.StdLocal.c` is the centre `(3,0,0)`;
* `Work.CountedPinch.StdLocal.outerPt θ = torusMap θ 0 = (3 cos θ, 3 sin θ, 0)` is the point of the
  outer equator of the standard torus at longitude `θ`;
* the slice of the plane `{z = 0}` with the box is `outerPt '' Ioo (-α) α`: the `y`-faces of the box
  bind (`3 |sin θ| < 2^{1/3}/4`), while the `x`-faces do not (`3 (1 - cos α) < 1/4`), and the inner
  equator of the torus is outside the box.

The numeric facts (`sin_α`, `cos_α_gt`, `s_pos`, `s_lt_one`) and the two comparison lemmas
`abs_sin_lt_s` and `cos_gt_eleven` are the only analysis used.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CountedPinch.StdLocal

noncomputable section

/-- `s = 2^{1/3}/12`, i.e. the half-length `2^{1/3}/4` of the box in the `y`-direction divided by
the radius `3` of the outer equator: the constraint `|3 sin θ| < 2^{1/3}/4` is exactly
`|sin θ| < s`. -/
def s : ℝ := (2:ℝ)^(1/3:ℝ)/12

/-- `α = arcsin s`: the longitude at which the outer equator leaves the box. -/
def α : ℝ := Real.arcsin s

/-- The centre `(3,0,0)` of the box, on the outer equator of the standard torus. -/
def c : R3 := WithLp.toLp 2 (![3,0,0] : Fin 3 → ℝ)

/-- The point of the outer equator of the standard torus with longitude parameter `θ`. -/
def outerPt (θ : ℝ) : R3 := Work.Core.torusMap θ 0

/-! ## The numeric facts -/

theorem s_pos : 0 < s := by unfold s; positivity

theorem s_lt_one : s < 1 := by
  unfold s
  have h : (2:ℝ)^(1/3:ℝ) < 12 := by linarith [Submission.rpow_third_le_two]
  linarith

theorem s_sq : s ^ 2 = (2:ℝ)^(2/3:ℝ)/144 := by
  unfold s
  rw [div_pow]
  norm_num
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem s_mul_three : s * 3 = (2:ℝ)^(1/3:ℝ)/4 := by unfold s; ring

theorem sin_α : Real.sin α = s := by
  unfold α
  rw [Real.sin_arcsin]
  · linarith [s_pos]
  · unfold s; linarith [Submission.rpow_third_le_two]

theorem α_pos : 0 < α := by
  unfold α; rw [Real.arcsin_pos]; unfold s; positivity

theorem α_lt_pi_div_two : α < Real.pi / 2 := by
  unfold α; rw [Real.arcsin_lt_pi_div_two]
  exact s_lt_one

theorem α_lt_pi : α < Real.pi := by linarith [α_lt_pi_div_two, Real.pi_pos]

theorem cos_α_gt : 11/12 < Real.cos α := by
  unfold α
  rw [Real.cos_arcsin, Real.lt_sqrt]
  · norm_num
    have h2 : (2:ℝ)^(2/3:ℝ) < 23 := by linarith [Submission.rpow_two_thirds_le_two]
    rw [s_sq]; linarith
  · norm_num

/-- On `(-α, α)` the `y`-coordinate `3 sin θ` of the outer equator stays inside the box. -/
theorem abs_sin_lt_s {θ : ℝ} (hθ : θ ∈ Set.Ioo (-α) α) : |Real.sin θ| < s := by
  have hmemθ : θ ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [hθ.1, α_lt_pi_div_two], by linarith [hθ.2, α_lt_pi_div_two]⟩
  have hmemα : α ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [α_pos, Real.pi_pos], by linarith [α_lt_pi_div_two]⟩
  have hmemnegα : -α ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) :=
    ⟨by linarith [α_lt_pi_div_two], by linarith [α_pos, Real.pi_pos]⟩
  rw [abs_lt]
  refine ⟨?_, ?_⟩
  · by_cases h : 0 ≤ θ
    · have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨h, by linarith [hθ.2, α_lt_pi]⟩
      linarith [s_pos]
    · push Not at h
      have hlt : Real.sin (-α) < Real.sin θ :=
        Real.strictMonoOn_sin hmemnegα hmemθ (by linarith [hθ.1])
      rw [Real.sin_neg, sin_α] at hlt
      linarith
  · by_cases h : θ ≤ 0
    · have hs : Real.sin θ ≤ 0 := by
        have h1 : -θ ∈ Set.Icc (0:ℝ) Real.pi := ⟨by linarith, by linarith [hθ.1, α_lt_pi]⟩
        have h2 := Real.sin_nonneg_of_mem_Icc h1
        rwa [Real.sin_neg, neg_nonneg] at h2
      linarith [s_pos]
    · push Not at h
      have hlt : Real.sin θ < Real.sin α := Real.strictMonoOn_sin hmemθ hmemα hθ.2
      rw [sin_α] at hlt
      linarith

/-- On `(-α, α)` the `x`-coordinate `3 cos θ` of the outer equator stays inside the box: the
`x`-faces of the box are not reached. -/
theorem cos_gt_eleven {θ : ℝ} (hθ : θ ∈ Set.Ioo (-α) α) : 11/12 < Real.cos θ := by
  have h1 : |θ| ≤ α := by rw [abs_le]; exact ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have h : Real.cos α ≤ Real.cos |θ| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg θ)
      (by linarith [α_lt_pi_div_two, Real.pi_pos]) h1
  rw [Real.cos_abs] at h
  linarith [cos_α_gt]

/-- `arcsin` is monotone, in the form needed to invert `|sin θ| < s`. -/
theorem arcsin_mem {t x : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hx : |x| < t) :
    -(Real.arcsin t) < Real.arcsin x ∧ Real.arcsin x < Real.arcsin t := by
  have hx1 : -t < x := (abs_lt.mp hx).1
  have hx2 : x < t := (abs_lt.mp hx).2
  have hxt : x ≤ 1 := le_of_lt (lt_of_lt_of_le hx2 ht1)
  have hx0 : -1 ≤ x := by
    have ht0' := ht0
    linarith [hx1, ht0']
  constructor
  · have h := Real.arcsin_lt_arcsin (show -1 ≤ -t by linarith) hx1 hxt
    rwa [Real.arcsin_neg] at h
  · exact Real.arcsin_lt_arcsin hx0 hx2 ht1

/-- The longitudes at which the outer equator meets the box are exactly `(-α, α)`, up to inversion
by `arcsin`. -/
theorem arcsin_sin_mem {θ : ℝ} (h : |Real.sin θ| < s) :
    Real.arcsin (Real.sin θ) ∈ Set.Ioo (-α) α :=
  arcsin_mem s_pos s_lt_one.le h

/-- `cos (arcsin (sin θ)) = cos θ` when `cos θ > 0`. -/
theorem cos_arcsin_sin {θ : ℝ} (h : 0 < Real.cos θ) :
    Real.cos (Real.arcsin (Real.sin θ)) = Real.cos θ := by
  rw [Real.cos_arcsin]
  have h1 : 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  rw [h1, Real.sqrt_sq h.le]

/-! ## The coordinates of the two points -/

@[simp] theorem outerPt_apply_zero (θ : ℝ) : outerPt θ 0 = 3 * Real.cos θ := by
  rw [outerPt, Work.Core.torusMap_apply_zero, Real.cos_zero]; norm_num

@[simp] theorem outerPt_apply_one (θ : ℝ) : outerPt θ 1 = 3 * Real.sin θ := by
  rw [outerPt, Work.Core.torusMap_apply_one, Real.cos_zero]; norm_num

@[simp] theorem outerPt_apply_two (θ : ℝ) : outerPt θ 2 = 0 := by
  rw [outerPt, Work.Core.torusMap_apply_two, Real.sin_zero]

@[simp] theorem c_apply_zero : c 0 = 3 := by simp [c]

@[simp] theorem c_apply_one : c 1 = 0 := by simp [c]

@[simp] theorem c_apply_two : c 2 = 0 := by simp [c]

theorem outerPt_mem_carrier (θ : ℝ) : outerPt θ ∈ Work.CoreTopology.standard.carrier :=
  ⟨(θ, 0), rfl⟩

/-- **The points of the outer equator with `|sin θ| < s` lie in the box.** -/
theorem outerPt_mem_PBox {θ : ℝ} (hθ : θ ∈ Set.Ioo (-α) α) :
    outerPt θ ∈ Submission.PBox (1/4) c (Equiv.refl (Fin 3)) := by
  rw [Submission.mem_PBox]
  intro i
  simp only [Equiv.refl_apply]
  fin_cases i
  · show |outerPt θ 0 - c 0| < Submission.boxSide 0 * (1/4)
    rw [outerPt_apply_zero, c_apply_zero, Submission.boxSide_zero]
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · linarith [cos_gt_eleven hθ]
    · nlinarith [Real.cos_le_one θ]
  · show |outerPt θ 1 - c 1| < Submission.boxSide 1 * (1/4)
    rw [outerPt_apply_one, c_apply_one, Submission.boxSide_one, sub_zero]
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have h := abs_sin_lt_s hθ
    have h3 := s_mul_three
    nlinarith [h, h3]
  · show |outerPt θ 2 - c 2| < Submission.boxSide 2 * (1/4)
    rw [outerPt_apply_two, c_apply_two, sub_zero, abs_zero, Submission.boxSide_two]
    positivity

/-- **The outer arc, for `|sin θ| < s`, is in the slice** (the cutting plane is `{z = 0}`). -/
theorem outerPt_mem_slice {θ : ℝ} (hθ : θ ∈ Set.Ioo (-α) α) :
    outerPt θ ∈ Work.CountedPinch.slice Work.CoreTopology.standard (1/4) c
      (Equiv.refl (Fin 3)) 0 := by
  rw [Work.CountedPinch.slice, Work.BoxShrink.Core.mem_sliceRegion]
  refine ⟨outerPt_mem_carrier θ, outerPt_mem_PBox hθ, ?_⟩
  simp only [Equiv.refl_apply]
  simp


/-- Two points of `ℝ³` are equal as soon as their three coordinates are. -/
theorem eq_of_coords_eq {x y : R3} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) :
    x = y := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-! ## The slice of the plane `{z = 0}` is the outer arc -/

/-- **Every point of the slice is a point of the outer arc.**  A point `y` of the slice is
`torusMap θ φ` with `sin φ = 0`, hence `cos φ = ±1`: for `cos φ = -1` the first coordinate of `y`
is `cos θ ∈ [-1,1]`, which the `x`-face of the box excludes; for `cos φ = 1` the point is
`outerPt θ` with `|sin θ| < s` and `cos θ > 11/12`, and `arcsin (sin θ) ∈ (-α, α)` realises it as a
point of the outer arc. -/
theorem slice_subset_arc :
    Work.CountedPinch.slice Work.CoreTopology.standard (1/4) c (Equiv.refl (Fin 3)) 0 ⊆
      outerPt '' Set.Ioo (-α) α := by
  intro y hy
  rw [Work.CountedPinch.slice, Work.BoxShrink.Core.mem_sliceRegion] at hy
  obtain ⟨hyc, hyb, hyu⟩ := hy
  obtain ⟨⟨θ, φ⟩, hθφ⟩ := hyc
  change Work.Core.torusMap θ φ = y at hθφ
  have hy2 : y 2 = 0 := by
    have h := hyu
    simp only [Equiv.refl_apply] at h
    rw [c_apply_two] at h
    linarith
  have hsin : Real.sin φ = 0 := by
    have h : (Work.Core.torusMap θ φ) 2 = 0 := by rw [hθφ]; exact hy2
    rwa [Work.Core.torusMap_apply_two] at h
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hsin
  have hcos2 : Real.cos φ ^ 2 = 1 := by
    rw [← hk]
    have h := Real.sin_sq_add_cos_sq (↑k * Real.pi)
    rw [Real.sin_int_mul_pi] at h
    linarith
  have hb0 : |y 0 - 3| < 1/4 := by
    have h := hyb 0
    simp only [Equiv.refl_apply] at h
    rw [c_apply_zero, Submission.boxSide_zero] at h
    simpa using h
  have hb1 : |y 1| < (2:ℝ)^(1/3:ℝ) * (1/4) := by
    have h := hyb 1
    simp only [Equiv.refl_apply] at h
    rw [c_apply_one, Submission.boxSide_one] at h
    simpa using h
  have hy0 : y 0 = (2 + Real.cos φ) * Real.cos θ := by
    rw [← hθφ, Work.Core.torusMap_apply_zero]
  have hy1 : y 1 = (2 + Real.cos φ) * Real.sin θ := by
    rw [← hθφ, Work.Core.torusMap_apply_one]
  rcases sq_eq_one_iff.mp hcos2 with hc | hc
  · have hy0' : y 0 = 3 * Real.cos θ := by rw [hy0, hc]; ring
    have hy1' : y 1 = 3 * Real.sin θ := by rw [hy1, hc]; ring
    have hcos_pos : 0 < Real.cos θ := by
      rw [hy0'] at hb0
      linarith [(abs_lt.mp hb0).1]
    have hsin_lt : |Real.sin θ| < s := by
      rw [hy1', abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)] at hb1
      have h3 := s_mul_three
      nlinarith [hb1, h3]
    refine ⟨Real.arcsin (Real.sin θ), arcsin_sin_mem hsin_lt, ?_⟩
    exact eq_of_coords_eq
      (by rw [hy0', outerPt_apply_zero, cos_arcsin_sin hcos_pos])
      (by rw [hy1', outerPt_apply_one,
        Real.sin_arcsin (Real.neg_one_le_sin θ) (Real.sin_le_one θ)])
      (by rw [hy2, outerPt_apply_two])
  · have h0 : y 0 = Real.cos θ := by rw [hy0, hc]; ring
    rw [h0] at hb0
    exact absurd (abs_lt.mp hb0).1 (by linarith [Real.cos_le_one θ])

/-- **The slice of the plane `{z = 0}` with the box is exactly the outer arc.** -/
theorem slice_eq_arc :
    Work.CountedPinch.slice Work.CoreTopology.standard (1/4) c (Equiv.refl (Fin 3)) 0 =
      outerPt '' Set.Ioo (-α) α :=
  Set.Subset.antisymm slice_subset_arc
    (fun _ ⟨_, hθ, hy⟩ => hy ▸ outerPt_mem_slice hθ)

/-! ## The parametrisation of the arc and the closure of the slice -/

/-- The affine parameter of the arc: `[0,1] → [-α, α]`. -/
def arcArg (t : ℝ) : ℝ := 2 * α * t - α

/-- The arc of the outer equator, parametrised by `t ↦ 2 α t - α`. -/
def arcPt (t : ℝ) : R3 := outerPt (arcArg t)

theorem continuous_arcArg : Continuous arcArg := by
  unfold arcArg; fun_prop

theorem continuous_outerPt : Continuous outerPt := by
  have hfun : outerPt = fun t : ℝ => WithLp.toLp 2 (fun i : Fin 3 =>
      (if i.val = 0 then (2 + Real.cos (0:ℝ)) * Real.cos t
       else if i.val = 1 then (2 + Real.cos (0:ℝ)) * Real.sin t
       else Real.sin (0:ℝ) : ℝ)) := rfl
  rw [hfun]
  have h : Continuous fun t : ℝ => (fun i : Fin 3 =>
      (if i.val = 0 then (2 + Real.cos (0:ℝ)) * Real.cos t
       else if i.val = 1 then (2 + Real.cos (0:ℝ)) * Real.sin t
       else Real.sin (0:ℝ) : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

theorem continuous_arcPt : Continuous arcPt := by
  have h : arcPt = outerPt ∘ arcArg := rfl
  rw [h]
  exact continuous_outerPt.comp continuous_arcArg

/-- The arc, as a continuous map from the parameter interval. -/
def arcMap : C(Work.Smooth.Plane.ArcInterval, R3) :=
  ⟨fun t => arcPt (t : ℝ), continuous_arcPt.comp continuous_subtype_val⟩

@[simp] theorem arcMap_apply (t : Work.Smooth.Plane.ArcInterval) :
    arcMap t = arcPt (t : ℝ) := rfl

/-- The affine reparametrisation `[0,1] → [-α,α]` is surjective onto `[-α,α]`. -/
theorem arcArg_image : arcArg '' Set.Icc (0:ℝ) 1 = Set.Icc (-α) α := by
  have h2α : (0:ℝ) < 2 * α := by linarith [α_pos]
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    constructor <;> simp only [arcArg] <;> nlinarith [ht.1, ht.2, α_pos]
  · intro hy
    refine ⟨(y + α) / (2 * α), ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ h2α]; linarith [hy.1]
    · rw [div_le_iff₀ h2α]; linarith [hy.2]
    · have hα : α ≠ 0 := ne_of_gt α_pos
      unfold arcArg
      field_simp
      ring

/-- The image of `[0,1]` under the arc is the outer arc over `[-α,α]`. -/
theorem arcPt_image_Icc : arcPt '' Set.Icc (0:ℝ) 1 = outerPt '' Set.Icc (-α) α := by
  have h1 : arcPt '' Set.Icc (0:ℝ) 1 = outerPt '' (arcArg '' Set.Icc (0:ℝ) 1) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨arcArg t, ⟨t, ht, rfl⟩, rfl⟩
    · rintro ⟨u, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨t, ht, rfl⟩
  rw [h1, arcArg_image]

/-- The range of the arc map is the outer arc over `[-α,α]`. -/
theorem range_arcMap : Set.range (arcMap : Work.Smooth.Plane.ArcInterval → R3) =
    outerPt '' Set.Icc (-α) α := by
  have h1 : Set.range (arcMap : Work.Smooth.Plane.ArcInterval → R3) =
      arcPt '' Set.Icc (0:ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨(t : ℝ), t.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [h1, arcPt_image_Icc]

/-- **The closure of the slice is the closed outer arc.**  The outer arc over `[-α,α]` is compact
(hence closed) and contains the slice; conversely it is the image of the closure of `(-α,α)` under
the continuous `outerPt`, hence contained in the closure of the slice. -/
theorem closure_slice_eq :
    closure (Work.CountedPinch.slice Work.CoreTopology.standard (1/4) c (Equiv.refl (Fin 3)) 0)
      = outerPt '' Set.Icc (-α) α := by
  have hcomp : IsCompact (outerPt '' Set.Icc (-α) α) :=
    isCompact_Icc.image continuous_outerPt
  refine Set.Subset.antisymm ?_ ?_
  · rw [slice_eq_arc]
    exact closure_minimal (Set.image_mono Set.Ioo_subset_Icc_self) hcomp.isClosed
  · have h := image_closure_subset_closure_image continuous_outerPt (s := Set.Ioo (-α) α)
    rw [closure_Ioo (by linarith [α_pos])] at h
    rwa [← slice_eq_arc] at h

theorem arcArg_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : arcArg t ∈ Set.Icc (-α) α := by
  have h := ht
  constructor <;> simp only [arcArg] <;> nlinarith [h.1, h.2, α_pos]

/-- **The arc map is injective**: the parameters `2 α t - α` for `t ∈ [0,1]` lie in `[-α, α]`, an
interval of length `2α < 2π`, so an equality of the points forces the parameters to agree
(`Work.Core.torusMap_eq_iff`). -/
theorem arcMap_injective : Function.Injective arcMap := by
  intro a b hab
  have harg_a : arcArg (a:ℝ) ∈ Set.Icc (-α) α := arcArg_mem_Icc a.2
  have harg_b : arcArg (b:ℝ) ∈ Set.Icc (-α) α := arcArg_mem_Icc b.2
  have hab' : Work.Core.torusMap (arcArg (a:ℝ)) 0 = Work.Core.torusMap (arcArg (b:ℝ)) 0 := hab
  obtain ⟨k, hk⟩ := ((Work.Core.torusMap_eq_iff (arcArg (a:ℝ)) 0 (arcArg (b:ℝ)) 0).mp hab').1
  have hk0 : k = 0 := by
    have hπ : (0:ℝ) < 2 * Real.pi := by positivity
    have h1 : arcArg (a:ℝ) - arcArg (b:ℝ) = (k:ℝ) * (2 * Real.pi) := by linarith [hk]
    have h2 : |arcArg (a:ℝ) - arcArg (b:ℝ)| ≤ 2 * α := by
      rw [abs_sub_le_iff]
      constructor
      · linarith [harg_a.2, harg_b.1]
      · linarith [harg_b.2, harg_a.1]
    have h3 : |(k:ℝ)| * (2 * Real.pi) = |arcArg (a:ℝ) - arcArg (b:ℝ)| := by
      rw [h1, abs_mul, abs_of_pos hπ]
    have h4 : |(k:ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      rw [h3]; linarith [h2, α_lt_pi]
    have h5 : |(k:ℝ)| < 1 := by
      rw [← lt_div_iff₀ hπ] at h4
      rwa [div_self (ne_of_gt hπ)] at h4
    rw [abs_lt] at h5
    have hk1 : k < 1 := by exact_mod_cast h5.2
    have hk2 : -1 < k := by exact_mod_cast h5.1
    omega
  have harg : arcArg (a:ℝ) = arcArg (b:ℝ) := by
    rw [hk0] at hk
    simpa using hk
  refine Subtype.ext ?_
  have h2 : 2 * α * (a:ℝ) = 2 * α * (b:ℝ) := by
    have := harg
    unfold arcArg at this
    linarith [this]
  exact mul_left_cancel₀ (ne_of_gt (by linarith [α_pos] : (0:ℝ) < 2 * α)) h2

end

end Work.CountedPinch.StdLocal
