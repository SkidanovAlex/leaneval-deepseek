import Mathlib

/-!
# Helper development: the degree of a circle map as a signed crossing count

This is a self-contained copy (with fixes) of the local/one-sided-value machinery used to compute
the degree of a `C¹` circle map as a signed count of its crossings of the integer levels.

Everything here lives in the namespace `Work.Drive.SCC` so that it does not collide with the
similarly-named development in `Submission/Work/Drive/degree_crossing_count.lean`.
-/

namespace Work.Drive.SCC

open Set Filter
open scoped Topology

noncomputable section

/-! ## Local behaviour of a differentiable function near a level -/

/-- An event which holds eventually in the punctured neighbourhood filter of `0` holds on a
punctured interval `(-δ, δ)`. -/
theorem exists_pos_of_eventually_nhdsNE {P : ℝ → Prop}
    (h : ∀ᶠ t in 𝓝[≠] (0:ℝ), P t) : ∃ δ > 0, ∀ t, 0 < |t| → |t| < δ → P t := by
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hP⟩ := h
  refine ⟨δ, hδ, fun t ht hlt => hP ?_ ?_⟩
  · rwa [Real.dist_eq, sub_zero]
  · simpa using abs_pos.mp ht

/-- A function with positive derivative `c` at `0` is increasing through `0`, and its values near
`0` on both sides stay within `1` of `f 0`. -/
theorem floor_of_deriv_pos {f : ℝ → ℝ} {c : ℝ} (h : HasDerivAt f c 0) (hc : 0 < c) :
    ∃ δ > 0, (∀ x ∈ Ioo (0:ℝ) δ, f 0 < f x ∧ f x < f 0 + 1) ∧
      (∀ x ∈ Ioo (-δ) 0, f 0 - 1 < f x ∧ f x < f 0) := by
  have hslope : ∀ᶠ x in 𝓝[≠] (0:ℝ), 0 < slope f 0 x :=
    h.tendsto_slope.eventually (Ioi_mem_nhds hc)
  obtain ⟨δ₁, hδ₁, hS⟩ := exists_pos_of_eventually_nhdsNE hslope
  have hcont : f ⁻¹' Ioo (f 0 - 1) (f 0 + 1) ∈ 𝓝 (0:ℝ) :=
    h.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨δ₂, hδ₂, hC⟩ := Metric.eventually_nhds_iff.mp hcont
  have hδC : ∀ x, x ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → f x ∈ Ioo (f 0 - 1) (f 0 + 1) := by
    intro x hx
    refine hC ?_
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hx.1, min_le_right δ₁ δ₂], by linarith [hx.2, min_le_right δ₁ δ₂]⟩
  have hδ0 : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  refine ⟨min δ₁ δ₂, hδ0, ?_, ?_⟩
  · intro x hx
    have hx0 : 0 < x := hx.1
    have hlt : |x| < δ₁ := by rw [abs_of_pos hx0]; linarith [hx.2, min_le_left δ₁ δ₂]
    have hs : 0 < slope f 0 x := hS x (abs_pos.mpr (ne_of_gt hx0)) hlt
    have hs' : 0 < x⁻¹ * (f x - f 0) := by simpa [slope, sub_zero] using hs
    have hpos : 0 < f x - f 0 := by
      have := mul_pos hx0 hs'
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hx0), one_mul] at this
      exact this
    exact ⟨by linarith, (hδC x ⟨by linarith, hx.2⟩).2⟩
  · intro x hx
    have hx0 : x < 0 := hx.2
    have hlt : |x| < δ₁ := by rw [abs_of_neg hx0]; linarith [hx.1, min_le_left δ₁ δ₂]
    have hs : 0 < slope f 0 x := hS x (abs_pos.mpr (ne_of_lt hx0)) hlt
    have hs' : 0 < x⁻¹ * (f x - f 0) := by simpa [slope, sub_zero] using hs
    have hneg : f x - f 0 < 0 := by
      have := mul_neg_of_neg_of_pos hx0 hs'
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_lt hx0), one_mul] at this
      exact this
    exact ⟨(hδC x ⟨hx.1, by linarith⟩).1, by linarith⟩

/-- A function with negative derivative `c` at `0` is decreasing through `0`, and its values near
`0` on both sides stay within `1` of `f 0`. -/
theorem floor_of_deriv_neg {f : ℝ → ℝ} {c : ℝ} (h : HasDerivAt f c 0) (hc : c < 0) :
    ∃ δ > 0, (∀ x ∈ Ioo (0:ℝ) δ, f 0 - 1 < f x ∧ f x < f 0) ∧
      (∀ x ∈ Ioo (-δ) 0, f 0 < f x ∧ f x < f 0 + 1) := by
  have hslope : ∀ᶠ x in 𝓝[≠] (0:ℝ), slope f 0 x < 0 :=
    h.tendsto_slope.eventually (Iio_mem_nhds hc)
  obtain ⟨δ₁, hδ₁, hS⟩ := exists_pos_of_eventually_nhdsNE hslope
  have hcont : f ⁻¹' Ioo (f 0 - 1) (f 0 + 1) ∈ 𝓝 (0:ℝ) :=
    h.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨δ₂, hδ₂, hC⟩ := Metric.eventually_nhds_iff.mp hcont
  have hδC : ∀ x, x ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) → f x ∈ Ioo (f 0 - 1) (f 0 + 1) := by
    intro x hx
    refine hC ?_
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hx.1, min_le_right δ₁ δ₂], by linarith [hx.2, min_le_right δ₁ δ₂]⟩
  have hδ0 : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  refine ⟨min δ₁ δ₂, hδ0, ?_, ?_⟩
  · intro x hx
    have hx0 : 0 < x := hx.1
    have hlt : |x| < δ₁ := by rw [abs_of_pos hx0]; linarith [hx.2, min_le_left δ₁ δ₂]
    have hs : slope f 0 x < 0 := hS x (abs_pos.mpr (ne_of_gt hx0)) hlt
    have hs' : x⁻¹ * (f x - f 0) < 0 := by simpa [slope, sub_zero] using hs
    have hneg : f x - f 0 < 0 := by
      have := mul_neg_of_pos_of_neg hx0 hs'
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hx0), one_mul] at this
      exact this
    exact ⟨(hδC x ⟨by linarith, hx.2⟩).1, by linarith⟩
  · intro x hx
    have hx0 : x < 0 := hx.2
    have hlt : |x| < δ₁ := by rw [abs_of_neg hx0]; linarith [hx.1, min_le_left δ₁ δ₂]
    have hs : slope f 0 x < 0 := hS x (abs_pos.mpr (ne_of_lt hx0)) hlt
    have hs' : x⁻¹ * (f x - f 0) < 0 := by simpa [slope, sub_zero] using hs
    have hpos : 0 < f x - f 0 := by
      have := mul_pos_of_neg_of_neg hx0 hs'
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_lt hx0), one_mul] at this
      exact this
    exact ⟨by linarith, (hδC x ⟨hx.1, by linarith⟩).2⟩

/-! ## The crossing set of `F`, and the one-sided values of `⌊F⌋` -/

/-- The set of times at which `F` takes an integer value. -/
def CrossSet (F : ℝ → ℝ) : Set ℝ := {t | ∃ m : ℤ, F t = (m : ℝ)}

lemma mem_CrossSet {F : ℝ → ℝ} {t : ℝ} :
    t ∈ CrossSet F ↔ ∃ m : ℤ, F t = (m : ℝ) := Iff.rfl

/-- The value of `⌊F⌋` immediately to the right of `t`. -/
noncomputable def rval (F : ℝ → ℝ) (t : ℝ) : ℤ := by
  classical
  exact if t ∈ CrossSet F then (if 0 < deriv F t then ⌊F t⌋ else ⌊F t⌋ - 1) else ⌊F t⌋

/-- The value of `⌊F⌋` immediately to the left of `t`. -/
noncomputable def lval (F : ℝ → ℝ) (t : ℝ) : ℤ := by
  classical
  exact if t ∈ CrossSet F then (if 0 < deriv F t then ⌊F t⌋ - 1 else ⌊F t⌋) else ⌊F t⌋

/-- The signed jump of `⌊F⌋` at `t`. -/
noncomputable def jmp (F : ℝ → ℝ) (t : ℝ) : ℤ := by
  classical
  exact if t ∈ CrossSet F then (if 0 < deriv F t then 1 else -1) else 0

@[simp] lemma rval_of_notMem {F : ℝ → ℝ} {t : ℝ} (ht : t ∉ CrossSet F) : rval F t = ⌊F t⌋ := by
  rw [rval]; exact if_neg ht

@[simp] lemma lval_of_notMem {F : ℝ → ℝ} {t : ℝ} (ht : t ∉ CrossSet F) : lval F t = ⌊F t⌋ := by
  rw [lval]; exact if_neg ht

@[simp] lemma jmp_of_notMem {F : ℝ → ℝ} {t : ℝ} (ht : t ∉ CrossSet F) : jmp F t = 0 := by
  rw [jmp]; exact if_neg ht

lemma rval_of_mem_pos {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ CrossSet F) (hd : 0 < deriv F t) :
    rval F t = ⌊F t⌋ := by rw [rval]; rw [if_pos ht, if_pos hd]

lemma rval_of_mem_neg {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ CrossSet F) (hd : ¬ 0 < deriv F t) :
    rval F t = ⌊F t⌋ - 1 := by rw [rval]; rw [if_pos ht, if_neg hd]

lemma lval_of_mem_pos {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ CrossSet F) (hd : 0 < deriv F t) :
    lval F t = ⌊F t⌋ - 1 := by rw [lval]; rw [if_pos ht, if_pos hd]

lemma lval_of_mem_neg {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ CrossSet F) (hd : ¬ 0 < deriv F t) :
    lval F t = ⌊F t⌋ := by rw [lval]; rw [if_pos ht, if_neg hd]

lemma jmp_of_mem_pos {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ CrossSet F) (hd : 0 < deriv F t) :
    jmp F t = 1 := by rw [jmp]; rw [if_pos ht, if_pos hd]

lemma jmp_of_mem_neg {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ CrossSet F) (hd : ¬ 0 < deriv F t) :
    jmp F t = -1 := by rw [jmp]; rw [if_pos ht, if_neg hd]

/-- At a crossing the jump of `⌊F⌋` is the difference of the two one-sided values. -/
lemma jmp_eq_rval_sub_lval {F : ℝ → ℝ} {t : ℝ} (ht : t ∈ CrossSet F) :
    jmp F t = rval F t - lval F t := by
  by_cases hd : 0 < deriv F t
  · rw [jmp_of_mem_pos ht hd, rval_of_mem_pos ht hd, lval_of_mem_pos ht hd]; ring
  · rw [jmp_of_mem_neg ht hd, rval_of_mem_neg ht hd, lval_of_mem_neg ht hd]; ring

/-- Near a crossing at which `F` takes the value `m ∈ ℤ` with non-zero derivative, the floor of `F`
is `m` on one side and `m - 1` on the other, according to the sign of the derivative. -/
theorem floor_near_crossing {F : ℝ → ℝ} {t : ℝ} {m : ℤ} (htm : F t = (m : ℝ))
    (hda : HasDerivAt F (deriv F t) t) (hne : deriv F t ≠ 0) :
    ∃ δ > 0, (∀ x ∈ Ioo t (t + δ), ⌊F x⌋ = if 0 < deriv F t then m else m - 1) ∧
      (∀ x ∈ Ioo (t - δ) t, ⌊F x⌋ = if 0 < deriv F t then m - 1 else m) := by
  have hdt : HasDerivAt (fun s : ℝ => F (s + t)) (deriv F t) 0 := by
    refine HasDerivAt.comp_add_const (f := F) (f' := deriv F t) 0 t ?_
    simpa using hda
  have key : ∀ (δ : ℝ), (∀ s ∈ Ioo (0:ℝ) δ, F (0 + t) < F (s + t) ∧ F (s + t) < F (0 + t) + 1)
      → (∀ x ∈ Ioo t (t + δ), ⌊F x⌋ = m) := by
    intro δ h x hx
    have hx' : x - t ∈ Ioo (0:ℝ) δ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h0 := h (x - t) hx'
    have hxe : x - t + t = x := by ring
    rw [hxe, zero_add, htm] at h0
    exact Int.floor_eq_iff.mpr ⟨by push_cast; linarith [h0.1], by push_cast; linarith [h0.2]⟩
  have key' : ∀ (δ : ℝ), (∀ s ∈ Ioo (0:ℝ) δ, F (0 + t) - 1 < F (s + t) ∧ F (s + t) < F (0 + t))
      → (∀ x ∈ Ioo t (t + δ), ⌊F x⌋ = m - 1) := by
    intro δ h x hx
    have hx' : x - t ∈ Ioo (0:ℝ) δ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h0 := h (x - t) hx'
    have hxe : x - t + t = x := by ring
    rw [hxe, zero_add, htm] at h0
    exact Int.floor_eq_iff.mpr ⟨by push_cast; linarith [h0.1], by push_cast; linarith [h0.2]⟩
  have lkey : ∀ (δ : ℝ), (∀ s ∈ Ioo (-δ) 0, F (0 + t) < F (s + t) ∧ F (s + t) < F (0 + t) + 1)
      → (∀ x ∈ Ioo (t - δ) t, ⌊F x⌋ = m) := by
    intro δ h x hx
    have hx' : x - t ∈ Ioo (-δ) 0 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h0 := h (x - t) hx'
    have hxe : x - t + t = x := by ring
    rw [hxe, zero_add, htm] at h0
    exact Int.floor_eq_iff.mpr ⟨by push_cast; linarith [h0.1], by push_cast; linarith [h0.2]⟩
  have lkey' : ∀ (δ : ℝ), (∀ s ∈ Ioo (-δ) 0, F (0 + t) - 1 < F (s + t) ∧ F (s + t) < F (0 + t))
      → (∀ x ∈ Ioo (t - δ) t, ⌊F x⌋ = m - 1) := by
    intro δ h x hx
    have hx' : x - t ∈ Ioo (-δ) 0 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h0 := h (x - t) hx'
    have hxe : x - t + t = x := by ring
    rw [hxe, zero_add, htm] at h0
    exact Int.floor_eq_iff.mpr ⟨by push_cast; linarith [h0.1], by push_cast; linarith [h0.2]⟩
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨δ, hδ, h1, h2⟩ := floor_of_deriv_neg (f := fun s : ℝ => F (s + t)) hdt hneg
    have hif : ¬ (0 < deriv F t) := not_lt.mpr hneg.le
    refine ⟨δ, hδ, ?_, ?_⟩
    · rw [if_neg hif]; exact key' δ h1
    · rw [if_neg hif]; exact lkey δ h2
  · obtain ⟨δ, hδ, h1, h2⟩ := floor_of_deriv_pos (f := fun s : ℝ => F (s + t)) hdt hpos
    refine ⟨δ, hδ, ?_, ?_⟩
    · rw [if_pos hpos]; exact key δ h1
    · rw [if_pos hpos]; exact lkey' δ h2

/-- The one-sided value `rval F t` really is the value of `⌊F⌋` just to the right of `t`. -/
theorem eventually_floor_rval {F : ℝ → ℝ} (hF : Continuous F)
    (hreg : ∀ t ∈ CrossSet F, deriv F t ≠ 0) (hder : ∀ t, HasDerivAt F (deriv F t) t) (t : ℝ) :
    ∃ δ > 0, ∀ x ∈ Ioo t (t + δ), ⌊F x⌋ = rval F t := by
  by_cases ht : t ∈ CrossSet F
  · have htmem : t ∈ CrossSet F := ht
    obtain ⟨m, hm⟩ := ht
    have hfl : ⌊F t⌋ = m := by rw [hm]; exact Int.floor_intCast m
    obtain ⟨δ, hδ, h1, _⟩ := floor_near_crossing hm (hder t) (hreg t htmem)
    refine ⟨δ, hδ, fun x hx => ?_⟩
    rcases lt_or_gt_of_ne (hreg t htmem) with hneg | hpos
    · have hh := h1 x hx
      rw [if_neg (not_lt.mpr hneg.le)] at hh
      rw [rval, if_pos htmem, hfl, if_neg (not_lt.mpr hneg.le)]
      exact hh
    · have hh := h1 x hx
      rw [if_pos hpos] at hh
      rw [rval, if_pos htmem, hfl, if_pos hpos]
      exact hh
  · have hfloor : ⌊F t⌋ = rval F t := by rw [rval, if_neg ht]
    have haux : (⌊F t⌋ : ℝ) < F t := by
      refine lt_of_le_of_ne (Int.floor_le _) ?_
      intro h
      exact ht ⟨⌊F t⌋, h.symm⟩
    have hmem : F ⁻¹' Ioo (⌊F t⌋ : ℝ) ((⌊F t⌋ : ℝ) + 1) ∈ 𝓝 t :=
      hF.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨haux, Int.lt_floor_add_one _⟩)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hmem
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hxdist : dist x t < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (Int.floor_eq_iff.mpr ⟨le_of_lt (hδ' hxdist).1, (hδ' hxdist).2⟩).trans hfloor

/-- The one-sided value `lval F t` really is the value of `⌊F⌋` just to the left of `t`. -/
theorem eventually_floor_lval {F : ℝ → ℝ} (hF : Continuous F)
    (hreg : ∀ t ∈ CrossSet F, deriv F t ≠ 0) (hder : ∀ t, HasDerivAt F (deriv F t) t) (t : ℝ) :
    ∃ δ > 0, ∀ x ∈ Ioo (t - δ) t, ⌊F x⌋ = lval F t := by
  by_cases ht : t ∈ CrossSet F
  · have htmem : t ∈ CrossSet F := ht
    obtain ⟨m, hm⟩ := ht
    have hfl : ⌊F t⌋ = m := by rw [hm]; exact Int.floor_intCast m
    obtain ⟨δ, hδ, _, h2⟩ := floor_near_crossing hm (hder t) (hreg t htmem)
    refine ⟨δ, hδ, fun x hx => ?_⟩
    rcases lt_or_gt_of_ne (hreg t htmem) with hneg | hpos
    · have hh := h2 x hx
      rw [if_neg (not_lt.mpr hneg.le)] at hh
      rw [lval, if_pos htmem, hfl, if_neg (not_lt.mpr hneg.le)]
      exact hh
    · have hh := h2 x hx
      rw [if_pos hpos] at hh
      rw [lval, if_pos htmem, hfl, if_pos hpos]
      exact hh
  · have hfloor : ⌊F t⌋ = lval F t := by rw [lval, if_neg ht]
    have haux : (⌊F t⌋ : ℝ) < F t := by
      refine lt_of_le_of_ne (Int.floor_le _) ?_
      intro h
      exact ht ⟨⌊F t⌋, h.symm⟩
    have hmem : F ⁻¹' Ioo (⌊F t⌋ : ℝ) ((⌊F t⌋ : ℝ) + 1) ∈ 𝓝 t :=
      hF.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨haux, Int.lt_floor_add_one _⟩)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hmem
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hxdist : dist x t < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (Int.floor_eq_iff.mpr ⟨le_of_lt (hδ' hxdist).1, (hδ' hxdist).2⟩).trans hfloor


/-! ## Periodicity of the crossing data -/

lemma CrossSet_add_one {F : ℝ → ℝ} {n : ℤ} (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ))
    (t : ℝ) : t + 1 ∈ CrossSet F ↔ t ∈ CrossSet F := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m - n, ?_⟩
    have h := hper t
    push_cast
    linarith
  · rintro ⟨m, hm⟩
    refine ⟨m + n, ?_⟩
    have h := hper t
    push_cast
    linarith

lemma CrossSet_sub_one {F : ℝ → ℝ} {n : ℤ} (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ))
    (s : ℝ) : s - 1 ∈ CrossSet F ↔ s ∈ CrossSet F := by
  have h := CrossSet_add_one hper (s - 1)
  rw [sub_add_cancel] at h
  exact h.symm

lemma CrossSet_add_nat {F : ℝ → ℝ} {n : ℤ} (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ))
    (t : ℝ) : ∀ k : ℕ, t + (k : ℝ) ∈ CrossSet F ↔ t ∈ CrossSet F := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h : t + ((k + 1 : ℕ) : ℝ) = (t + (k : ℝ)) + 1 := by push_cast; ring
      rw [h, CrossSet_add_one hper]
      exact ih

lemma CrossSet_add_intCast {F : ℝ → ℝ} {n : ℤ} (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ))
    (t : ℝ) : ∀ k : ℤ, t + (k : ℝ) ∈ CrossSet F ↔ t ∈ CrossSet F := by
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h : t + (((i : ℤ) + 1 : ℤ) : ℝ) = (t + (i : ℝ)) + 1 := by push_cast; ring
      rw [h, CrossSet_add_one hper]
      exact ih
  | pred i ih =>
      have h : t + ((-(i : ℤ) - 1 : ℤ) : ℝ) = (t + ((-(i : ℤ) : ℤ) : ℝ)) - 1 := by
        push_cast; ring
      rw [h, CrossSet_sub_one hper, ih]

lemma deriv_add_one {F : ℝ → ℝ} {n : ℤ} (hder : ∀ t, HasDerivAt F (deriv F t) t)
    (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) (t : ℝ) : deriv F (t + 1) = deriv F t := by
  have h1 : (fun s : ℝ => F (s + 1) - F s) = fun _ : ℝ => (n : ℝ) := by
    funext s; rw [hper s]; ring
  have h2 : HasDerivAt (fun s : ℝ => F (s + 1) - F s) (deriv F (t + 1) - deriv F t) t := by
    have A : HasDerivAt (fun s : ℝ => F (s + 1)) (deriv F (t + 1)) t :=
      HasDerivAt.comp_add_const (f := F) (f' := deriv F (t + 1)) t 1 (hder (t + 1))
    exact A.sub (hder t)
  have h3 : deriv (fun s : ℝ => F (s + 1) - F s) t = 0 := by rw [h1]; simp
  rw [h2.deriv] at h3
  linarith

lemma deriv_sub_one {F : ℝ → ℝ} {n : ℤ} (hder : ∀ t, HasDerivAt F (deriv F t) t)
    (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) (s : ℝ) : deriv F (s - 1) = deriv F s := by
  have h := deriv_add_one hder hper (s - 1)
  rw [sub_add_cancel] at h
  exact h.symm

lemma deriv_add_intCast {F : ℝ → ℝ} {n : ℤ} (hder : ∀ t, HasDerivAt F (deriv F t) t)
    (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) (t : ℝ) :
    ∀ k : ℤ, deriv F (t + (k : ℝ)) = deriv F t := by
  intro k
  induction k using Int.induction_on with
  | zero => simp
  | succ i ih =>
      have h : t + (((i : ℤ) + 1 : ℤ) : ℝ) = (t + (i : ℝ)) + 1 := by push_cast; ring
      rw [h, deriv_add_one hder hper]
      exact ih
  | pred i ih =>
      have h : t + ((-(i : ℤ) - 1 : ℤ) : ℝ) = (t + ((-(i : ℤ) : ℤ) : ℝ)) - 1 := by
        push_cast; ring
      rw [h, deriv_sub_one hder hper, ih]

lemma lval_add_one {F : ℝ → ℝ} {n : ℤ} (hder : ∀ t, HasDerivAt F (deriv F t) t)
    (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) (t : ℝ) : lval F (t + 1) = lval F t + n := by
  have hfl : ⌊F (t + 1)⌋ = ⌊F t⌋ + n := by rw [hper t, Int.floor_add_intCast]
  have hd : (0 < deriv F (t + 1)) ↔ (0 < deriv F t) := by rw [deriv_add_one hder hper t]
  by_cases ht : t ∈ CrossSet F
  · have ht1 : t + 1 ∈ CrossSet F := (CrossSet_add_one hper t).mpr ht
    rw [lval, if_pos ht1, lval, if_pos ht, hfl]
    by_cases h : 0 < deriv F t
    · rw [if_pos (hd.mpr h), if_pos h]
      try ring
    · rw [if_neg (fun hh => h (hd.mp hh)), if_neg h]
      try ring
  · have ht1 : t + 1 ∉ CrossSet F := fun h => ht ((CrossSet_add_one hper t).mp h)
    rw [lval, if_neg ht1, lval, if_neg ht, hfl]

/-- The regularity hypothesis, extended from `[0,1)` to all of `ℝ` by periodicity. -/
lemma deriv_ne_zero_of_mem_CrossSet {F : ℝ → ℝ}
    (hreg : ∀ t ∈ Ico (0:ℝ) 1, t ∈ CrossSet F → deriv F t ≠ 0)
    (hderc : ∀ (t : ℝ) (k : ℤ), deriv F (t + (k : ℝ)) = deriv F t)
    (hTc : ∀ (t : ℝ) (k : ℤ), t + (k : ℝ) ∈ CrossSet F ↔ t ∈ CrossSet F)
    {t : ℝ} (ht : t ∈ CrossSet F) : deriv F t ≠ 0 := by
  have hmem : t - ⌊t⌋ ∈ CrossSet F := by
    refine (hTc (t - ⌊t⌋) ⌊t⌋).mp ?_
    rw [show t - ⌊t⌋ + (⌊t⌋ : ℝ) = t by push_cast; ring]
    exact ht
  have hle : (0:ℝ) ≤ t - ⌊t⌋ := by
    have := Int.floor_le t; linarith
  have hlt : t - ⌊t⌋ < 1 := by
    have := Int.lt_floor_add_one t; linarith
  have hd : deriv F t = deriv F (t - ⌊t⌋) := by
    rw [← hderc (t - ⌊t⌋) ⌊t⌋]
    congr 1
    push_cast; ring
  rw [hd]
  exact hreg (t - ⌊t⌋) ⟨hle, hlt⟩ hmem

/-! ## `⌊F⌋` is constant on an interval with no crossing -/

lemma floor_const_le {F : ℝ → ℝ} (hF : Continuous F) {A B : ℝ}
    (hc : ∀ x ∈ Ioo A B, x ∉ CrossSet F) {x y : ℝ} (hx : x ∈ Ioo A B) (hy : y ∈ Ioo A B)
    (hxy : x ≤ y) : ⌊F x⌋ = ⌊F y⌋ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hk : (((⌊F x⌋ + 1 : ℤ)) : ℝ) ∈ Icc (F x) (F y) := by
      refine ⟨?_, ?_⟩
      · have h1 := Int.lt_floor_add_one (F x)
        push_cast
        linarith
      · have h2 : ((⌊F x⌋ + 1 : ℤ) : ℝ) ≤ (⌊F y⌋ : ℝ) := by
          exact_mod_cast (show ⌊F x⌋ + 1 ≤ ⌊F y⌋ by omega)
        have h3 := Int.floor_le (F y)
        linarith
    obtain ⟨s, hs, hsF⟩ := (intermediate_value_Icc hxy hF.continuousOn) hk
    have hsI : s ∈ Ioo A B := ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
    exact hc s hsI ⟨⌊F x⌋ + 1, hsF⟩
  · have hk : (((⌊F y⌋ + 1 : ℤ)) : ℝ) ∈ Icc (F y) (F x) := by
      refine ⟨?_, ?_⟩
      · have h1 := Int.lt_floor_add_one (F y)
        push_cast
        linarith
      · have h2 : ((⌊F y⌋ + 1 : ℤ) : ℝ) ≤ (⌊F x⌋ : ℝ) := by
          exact_mod_cast (show ⌊F y⌋ + 1 ≤ ⌊F x⌋ by omega)
        have h3 := Int.floor_le (F x)
        linarith
    obtain ⟨s, hs, hsF⟩ := (intermediate_value_Icc' hxy hF.continuousOn) hk
    have hsI : s ∈ Ioo A B := ⟨lt_of_lt_of_le hx.1 hs.1, lt_of_le_of_lt hs.2 hy.2⟩
    exact hc s hsI ⟨⌊F y⌋ + 1, hsF⟩

lemma floor_const_of_not_mem {F : ℝ → ℝ} (hF : Continuous F) {A B : ℝ}
    (hc : ∀ x ∈ Ioo A B, x ∉ CrossSet F) {x y : ℝ} (hx : x ∈ Ioo A B) (hy : y ∈ Ioo A B) :
    ⌊F x⌋ = ⌊F y⌋ := by
  rcases le_total x y with h | h
  · exact floor_const_le hF hc hx hy h
  · exact (floor_const_le hF hc hy hx h).symm

/-- If `(A,B)` contains no crossing of `F`, the one-sided values of `⌊F⌋` at the two ends agree. -/
lemma rval_eq_lval_of_no_crossing {F : ℝ → ℝ} (hF : Continuous F)
    (hreg : ∀ t ∈ CrossSet F, deriv F t ≠ 0) (hder : ∀ t, HasDerivAt F (deriv F t) t)
    {A B : ℝ} (hAB : A < B) (hc : ∀ x ∈ Ioo A B, x ∉ CrossSet F) : rval F A = lval F B := by
  obtain ⟨δ₁, hδ₁, h1⟩ := eventually_floor_rval hF hreg hder A
  obtain ⟨δ₂, hδ₂, h2⟩ := eventually_floor_lval hF hreg hder B
  obtain ⟨x, hx1, hx2⟩ := exists_between (show A < min B (A + δ₁) from lt_min hAB (by linarith))
  obtain ⟨y, hy1, hy2⟩ := exists_between
    (show max A (B - δ₂) < B from max_lt_iff.mpr ⟨hAB, by linarith⟩)
  have hxA : x ∈ Ioo A B := ⟨hx1, lt_of_lt_of_le hx2 (min_le_left B (A + δ₁))⟩
  have hyA : y ∈ Ioo A B := ⟨lt_of_le_of_lt (le_max_left A (B - δ₂)) hy1, hy2⟩
  have hxδ : x ∈ Ioo A (A + δ₁) := ⟨hx1, lt_of_lt_of_le hx2 (min_le_right B (A + δ₁))⟩
  have hyδ : y ∈ Ioo (B - δ₂) B := ⟨lt_of_le_of_lt (le_max_right A (B - δ₂)) hy1, hy2⟩
  rw [← h1 x hxδ, ← h2 y hyδ]
  exact floor_const_of_not_mem hF hc hxA hyA

/-! ## Telescoping the jumps of `⌊F⌋` -/

/-- **Telescoping.**  If a finite set `T` enumerates the crossings of `F` in the half-open interval
`[A, B)`, then the sum of the signed jumps of `⌊F⌋` over `T` telescopes to
`lval F B - lval F A`. -/
theorem sum_jmp_Ico {F : ℝ → ℝ} (hF : Continuous F)
    (hreg : ∀ t ∈ CrossSet F, deriv F t ≠ 0) (hder : ∀ t, HasDerivAt F (deriv F t) t)
    (T : Finset ℝ) (A B : ℝ) (hAB : A < B)
    (hT : ∀ t, t ∈ T ↔ t ∈ CrossSet F ∧ A ≤ t ∧ t < B) :
    ∑ t ∈ T, jmp F t = lval F B - lval F A := by
  revert A B
  refine Finset.induction_on_max (motive := fun T => ∀ (A B : ℝ), A < B →
    (∀ t, t ∈ T ↔ t ∈ CrossSet F ∧ A ≤ t ∧ t < B) →
    ∑ t ∈ T, jmp F t = lval F B - lval F A) T ?_ ?_
  · intro A B hAB hT
    have hc : ∀ x ∈ Ioo A B, x ∉ CrossSet F := by
      intro x hx hxc
      have hxT : x ∈ (∅ : Finset ℝ) := (hT x).mpr ⟨hxc, le_of_lt hx.1, hx.2⟩
      simpa using hxT
    have hAc : A ∉ CrossSet F := by
      intro hA
      have hAT : A ∈ (∅ : Finset ℝ) := (hT A).mpr ⟨hA, le_refl A, hAB⟩
      simpa using hAT
    have h1 : lval F A = rval F A := by
      rw [lval_of_notMem hAc, ← rval_of_notMem hAc]
    have h2 : rval F A = lval F B := rval_eq_lval_of_no_crossing hF hreg hder hAB hc
    simp only [Finset.sum_empty]
    rw [h1, h2]
    ring
  · intro c T' hlt ih A B hAB hT
    have hcin : c ∈ insert c T' := Finset.mem_insert_self c T'
    obtain ⟨hcCross, hAc, hcB⟩ := (hT c).mp hcin
    have hT' : ∀ t, t ∈ T' ↔ t ∈ CrossSet F ∧ A ≤ t ∧ t < c := by
      intro t
      constructor
      · intro ht
        obtain ⟨h1, h2, _⟩ := (hT t).mp (Finset.mem_insert_of_mem ht)
        exact ⟨h1, h2, hlt t ht⟩
      · rintro ⟨htc, hAt, htc'⟩
        have hmem : t ∈ insert c T' := (hT t).mpr ⟨htc, hAt, lt_of_lt_of_le htc' hcB.le⟩
        rcases Finset.mem_insert.mp hmem with h | h
        · exact absurd h (ne_of_lt htc')
        · exact h
    have hcnot : c ∉ T' := fun h => absurd (hlt c h) (lt_irrefl c)
    have hnoB : ∀ x ∈ Ioo c B, x ∉ CrossSet F := by
      intro x hx hxc
      have hmem : x ∈ insert c T' :=
        (hT x).mpr ⟨hxc, by linarith [hAc, hx.1], hx.2⟩
      rcases Finset.mem_insert.mp hmem with h | h
      · exact absurd h (ne_of_gt (by linarith [hx.1]))
      · exact absurd (hlt x h) (not_lt.mpr (le_of_lt hx.1))
    have hrc : rval F c = lval F B := rval_eq_lval_of_no_crossing hF hreg hder hcB hnoB
    rw [Finset.sum_insert hcnot, jmp_eq_rval_sub_lval hcCross, hrc]
    rcases eq_or_lt_of_le hAc with hAceq | hAc_lt
    · have hT'empty : T' = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro t ht
        obtain ⟨-, h2, h3⟩ := (hT' t).mp ht
        rw [hAceq] at h2
        exact absurd h3 (not_lt_of_ge h2)
      rw [hT'empty, Finset.sum_empty, hAceq]
      ring
    · rw [ih A c hAc_lt hT']
      ring


end

end Work.Drive.SCC

namespace Work.Drive

open Set Filter
open scoped Topology
open Work.Drive.SCC

noncomputable section

/-!
# The degree of a circle map as a signed crossing count

For a `C¹` function `F : ℝ → ℝ` whose monodromy over a period is the integer `n`
(`F (t + 1) = F t + n`), whose integer-value times in `[0,1)` are finite, and which is transversal
at each of them, the degree `n` is the number of upward crossings minus the number of downward
crossings of the integer levels.

The computation is: enumerate the crossings of the integer levels in `[0,1)` by a finset `T`; the
telescoping identity `SCC.sum_jmp_Ico` computes the total signed jump of `⌊F⌋` across `[0,1)` as
`lval F 1 - lval F 0`; by `SCC.lval_add_one` this is the monodromy `n`; and the total signed jump is
by construction `#(upward crossings) − #(downward crossings)`.
-/
theorem signed_crossing_count (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (n : ℤ)
    (hper : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ))
    (hfin : {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, F t = (m : ℝ)}.Finite)
    (hreg : ∀ t ∈ Set.Ico (0 : ℝ) 1, (∃ m : ℤ, F t = (m : ℝ)) → deriv F t ≠ 0) :
    n = (Set.ncard {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ (∃ m : ℤ, F t = (m : ℝ)) ∧ 0 < deriv F t} : ℤ)
      - (Set.ncard {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ (∃ m : ℤ, F t = (m : ℝ)) ∧ deriv F t < 0} : ℤ) := by
  classical
  have hcont : Continuous F := hF.continuous
  have hdiff : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hder : ∀ t : ℝ, HasDerivAt F (deriv F t) t := fun t => (hdiff t).hasDerivAt
  -- The regularity hypothesis, extended from `[0,1)` to all of `ℝ` by periodicity.
  have hreg' : ∀ t ∈ CrossSet F, deriv F t ≠ 0 := fun t ht =>
    deriv_ne_zero_of_mem_CrossSet (fun t ht1 ht2 => hreg t ht1 ht2)
      (fun t k => deriv_add_intCast hder hper t k)
      (fun t k => CrossSet_add_intCast hper t k) ht
  -- The finite set of crossings of the integer levels in `[0,1)`, as a finset.
  have hfinS : ({t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ t ∈ CrossSet F} : Set ℝ).Finite := by
    simpa only [mem_CrossSet] using hfin
  set T : Finset ℝ := hfinS.toFinset with hTdef
  have hT : ∀ t : ℝ, t ∈ T ↔ t ∈ CrossSet F ∧ 0 ≤ t ∧ t < 1 := by
    intro t
    rw [hTdef, Set.Finite.mem_toFinset hfinS]
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2⟩
  have hTcross : ∀ t ∈ T, t ∈ CrossSet F := fun t ht => ((hT t).mp ht).1
  have hTne : ∀ t ∈ T, deriv F t ≠ 0 := fun t ht => hreg' t (hTcross t ht)
  -- The total signed jump of `⌊F⌋` across `[0,1)` is the monodromy `n`.
  have hsum : ∑ t ∈ T, jmp F t = lval F 1 - lval F 0 :=
    sum_jmp_Ico hcont hreg' hder T 0 1 zero_lt_one hT
  have hlval : lval F 1 = lval F 0 + n := by
    have h := lval_add_one hder hper 0
    simpa using h
  have hsum_n : ∑ t ∈ T, jmp F t = n := by
    rw [hsum, hlval]; ring
  -- Split the crossings into upward and downward ones.
  set U : Finset ℝ := T.filter (fun t => 0 < deriv F t) with hUdef
  set D : Finset ℝ := T.filter (fun t => deriv F t < 0) with hDdef
  have hUD : U ∪ D = T := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro t ht
      rw [Finset.mem_union] at ht
      rcases ht with h | h
      · rw [hUdef, Finset.mem_filter] at h; exact h.1
      · rw [hDdef, Finset.mem_filter] at h; exact h.1
    · intro t ht
      rw [Finset.mem_union]
      rcases lt_or_gt_of_ne (hTne t ht) with h | h
      · exact Or.inr (by rw [hDdef, Finset.mem_filter]; exact ⟨ht, h⟩)
      · exact Or.inl (by rw [hUdef, Finset.mem_filter]; exact ⟨ht, h⟩)
  have hdisj : Disjoint U D := by
    rw [Finset.disjoint_left]
    intro t htU htD
    rw [hUdef, Finset.mem_filter] at htU
    rw [hDdef, Finset.mem_filter] at htD
    linarith [htU.2, htD.2]
  have hU1 : ∑ t ∈ U, jmp F t = (U.card : ℤ) := by
    have h1 : ∀ t ∈ U, jmp F t = (1 : ℤ) := by
      intro t ht
      rw [hUdef, Finset.mem_filter] at ht
      exact jmp_of_mem_pos (hTcross t ht.1) ht.2
    rw [Finset.sum_congr rfl h1]
    simp
  have hD1 : ∑ t ∈ D, jmp F t = -(D.card : ℤ) := by
    have h1 : ∀ t ∈ D, jmp F t = (-1 : ℤ) := by
      intro t ht
      rw [hDdef, Finset.mem_filter] at ht
      exact jmp_of_mem_neg (hTcross t ht.1) (not_lt.mpr ht.2.le)
    rw [Finset.sum_congr rfl h1]
    simp
  have hsum_split : ∑ t ∈ T, jmp F t = (U.card : ℤ) - (D.card : ℤ) := by
    rw [← hUD, Finset.sum_union hdisj, hU1, hD1]
    ring
  have hn : n = (U.card : ℤ) - (D.card : ℤ) := by
    rw [← hsum_n, hsum_split]
  -- Identify the two cardinalities with the `ncard`s of the required sets.
  have hUmem : ∀ t : ℝ,
      t ∈ U ↔ t ∈ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ (∃ m : ℤ, F t = (m : ℝ)) ∧ 0 < deriv F t} := by
    intro t
    rw [hUdef, Finset.mem_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨htT, hp⟩
      obtain ⟨hc, h0, h1⟩ := (hT t).mp htT
      exact ⟨⟨h0, h1⟩, hc, hp⟩
    · rintro ⟨⟨h0, h1⟩, hc, hp⟩
      exact ⟨(hT t).mpr ⟨hc, h0, h1⟩, hp⟩
  have hDmem : ∀ t : ℝ,
      t ∈ D ↔ t ∈ {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ (∃ m : ℤ, F t = (m : ℝ)) ∧ deriv F t < 0} := by
    intro t
    rw [hDdef, Finset.mem_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨htT, hp⟩
      obtain ⟨hc, h0, h1⟩ := (hT t).mp htT
      exact ⟨⟨h0, h1⟩, hc, hp⟩
    · rintro ⟨⟨h0, h1⟩, hc, hp⟩
      exact ⟨(hT t).mpr ⟨hc, h0, h1⟩, hp⟩
  have hUncard : Set.ncard {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ (∃ m : ℤ, F t = (m : ℝ)) ∧ 0 < deriv F t}
      = U.card := by
    rw [← Set.ncard_coe_finset U]
    congr 1
    ext t
    rw [Finset.mem_coe]
    exact (hUmem t).symm
  have hDncard : Set.ncard {t : ℝ | t ∈ Set.Ico (0 : ℝ) 1 ∧ (∃ m : ℤ, F t = (m : ℝ)) ∧ deriv F t < 0}
      = D.card := by
    rw [← Set.ncard_coe_finset D]
    congr 1
    ext t
    rw [Finset.mem_coe]
    exact (hDmem t).symm
  rw [hn, hUncard, hDncard]

end

end Work.Drive
