import Submission.Work.Main0U

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry
open Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Image of the closed U-leaf: affine straight bend (main0 / Lemma T support)

For a canonical U-leaf through an interior `U`-point `x` (direction
`w = uBendDirPos`, parameters `lp = leftParam x w < 0 < rp = rightParam x w`,
endpoints `uBendA`, `uBendB` on the boundary lines) we prove:

* the kernel condition, `U`-membership and strip-interiority along the whole
  open chord `(lp, rp)` (`kernel_U_full_chord`),
* the image of the OPEN chord is affine (`affine_open_chord`):
  `f (x + s•w) = f x + s • fderiv f x w`,
* `f` is continuous along the closed chord including the boundary endpoints
  (`continuousWithinAt_f_closed_chord`), which together with the open
  formula gives the endpoint values
  (`f_uBendA_value`, `f_uBendB_value`),
* the image of the CLOSED leaf is the affine straight segment
  (`affine_on_uBendClosed`):
  `f (x + s•w) = f x + s • fderiv f x w` for all `s ∈ Icc lp rp`,
* the bend length: `‖f(uBendB) - f(uBendA)‖ = ‖uBendB - uBendA‖`
  (`bend_length_eq`), so image bends are straight segments of the same
  length as their preimage chord.

This is the geometric content of "the image of a pre-bend is a straight
bend in `Ω`" used by Prop main0 (band side), Lemma T (lengths, midpoints,
unit directions of bends) and Lemma G (length relations).
-/

noncomputable section
namespace Submission.PaperBand

/-- **Full-chord kernel data**: for a crossing kernel direction `w`
(`0 < w 0`) through an interior `U`-point `x`, the whole open chord between
the two boundary lines lies in the strip interior, has `w` in the kernel at
every point, and consists of `U`-points. -/
lemma kernel_U_full_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hdN0 : dN f x ≠ 0)
    (hker0 : dN f x w = 0) (hwne : w ≠ 0) (hwpos : 0 < w 0) :
    (∀ s ∈ Set.Ioo (leftParam x w) (rightParam x w),
      x + s • w ∈ stripInterior ∧ dN f (x + s • w) w = 0) ∧
    (∀ s ∈ Set.Ioo (leftParam x w) (rightParam x w), dN f (x + s • w) ≠ 0) := by
  rcases maximal_kernel_segment_full hf hx hdN0 hker0 hwne (ne_of_gt hwpos) with
    ⟨α, β, hα, hβ, hfull, hk, hU⟩
  constructor
  · intro s hs
    constructor
    · exact (param_stripInterior_iff hwpos s).1 hs
    · have hmem : x + s • w ∈ stripInterior := (param_stripInterior_iff hwpos s).1 hs
      have hsαβ : s ∈ Set.Ioo α β := (hfull s).2 hmem
      exact hk s hsαβ
  · intro s hs
    have hmem : x + s • w ∈ stripInterior := (param_stripInterior_iff hwpos s).1 hs
    exact hU s ((hfull s).2 hmem)

/-- Points of the closed chord (parameters between the two boundary lines)
all lie in the closed unit strip. -/
lemma chord_subset_unitStrip {x w : ℝ²} (hwpos : 0 < w 0) (hx0 : 0 < x 0)
    (_hx1 : x 0 < 1) :
    ∀ s ∈ Set.Icc (leftParam x w) (rightParam x w), x + s • w ∈ unitStrip := by
  intro s hs
  rw [Set.mem_Icc] at hs
  have hmono : 0 ≤ x 0 + s * w 0 ∧ x 0 + s * w 0 ≤ 1 := by
    have hl : leftParam x w * w 0 = -x 0 := by
      unfold leftParam
      field_simp [ne_of_gt hwpos]
    have hr : rightParam x w * w 0 = 1 - x 0 := by
      unfold rightParam
      field_simp [ne_of_gt hwpos]
    constructor
    · have h1 : leftParam x w ≤ s := hs.1
      have hle := mul_le_mul_of_nonneg_right h1 (le_of_lt hwpos)
      rw [hl] at hle
      have : -x 0 ≤ s * w 0 := hle
      linarith
    · have h2 : s ≤ rightParam x w := hs.2
      have hle := mul_le_mul_of_nonneg_right h2 (le_of_lt hwpos)
      rw [hr] at hle
      linarith
  rw [unitStrip]
  change (x + s • w) 0 ∈ Set.Icc (0 : ℝ) 1
  rw [ray_coord0]
  exact hmono

/-- **Open-chord affineness**: the image of the open chord is affine with
slope the derivative of `f` at `x`:
`f (x + s•w) = f x + s • fderiv f x w` for all interior parameters. -/
lemma affine_open_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hdN0 : dN f x ≠ 0)
    (hker0 : dN f x w = 0) (hwne : w ≠ 0) (hwpos : 0 < w 0) :
    ∀ s ∈ Set.Ioo (leftParam x w) (rightParam x w),
      f (x + s • w) = f x + s • (fderiv ℝ f x w) := by
  have hfull := (kernel_U_full_chord hf hx hdN0 hker0 hwne hwpos).1
  have hx0 : 0 < x 0 := by
    rw [stripInterior] at hx
    exact hx.1
  have hx1 : x 0 < 1 := by
    rw [stripInterior] at hx
    exact hx.2
  intro s hs
  rw [Set.mem_Ioo] at hs
  by_cases hs0 : s = 0
  · subst s
    simp
  by_cases hsgt : 0 < s
  · -- 0 < s < rp
    have hseg : ∀ t ∈ Set.Icc (0 : ℝ) s, x + t • w ∈ stripInterior := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have htIoo : t ∈ Set.Ioo (leftParam x w) (rightParam x w) := by
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le (leftParam_neg hwpos hx0) ht.1, lt_of_le_of_lt ht.2 hs.2⟩
      exact (hfull t htIoo).1
    have hk : ∀ t ∈ Set.Icc (0 : ℝ) s, dN f (x + t • w) w = 0 := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have htIoo : t ∈ Set.Ioo (leftParam x w) (rightParam x w) := by
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le (leftParam_neg hwpos hx0) ht.1, lt_of_le_of_lt ht.2 hs.2⟩
      exact (hfull t htIoo).2
    have haff := affine_on_kernel_segment hf (x := x) (v := w) (A := 0) (B := s)
      hseg hk s (by rw [Set.mem_Icc]; exact ⟨hsgt.le, le_rfl⟩)
    simpa using haff
  · -- s < 0 (s ≠ 0 and not 0 < s)
    have hsneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hsgt) hs0
    have hseg : ∀ t ∈ Set.Icc s (0 : ℝ), x + t • w ∈ stripInterior := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have htIoo : t ∈ Set.Ioo (leftParam x w) (rightParam x w) := by
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 (rightParam_pos hwpos hx1)⟩
      exact (hfull t htIoo).1
    have hk : ∀ t ∈ Set.Icc s (0 : ℝ), dN f (x + t • w) w = 0 := by
      intro t ht
      rw [Set.mem_Icc] at ht
      have htIoo : t ∈ Set.Ioo (leftParam x w) (rightParam x w) := by
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 (rightParam_pos hwpos hx1)⟩
      exact (hfull t htIoo).2
    -- slope is constant: fderiv at x+s w equals fderiv at x
    let c : ℝ³ := fderiv ℝ f x w
    -- slope is constant: fderiv at x+s w equals fderiv at x
    have hconst := tangent_const_on_kernel_segment hf (x := x) (v := w) (A := s) (B := 0)
      hseg hk 0 (by rw [Set.mem_Icc]; exact ⟨hsneg.le, le_rfl⟩)
    have hc : fderiv ℝ f (x + s • w) w = c := by
      simpa [c] using hconst.symm
    have haff := affine_on_kernel_segment hf (x := x) (v := w) (A := s) (B := 0)
      hseg hk 0 (by rw [Set.mem_Icc]; exact ⟨hsneg.le, le_rfl⟩)
    -- haff : f (x + 0•w) = f (x + s•w) + (0 - s) • fderiv ℝ f (x + s • w) w
    have haff' : f x = f (x + s • w) + (-s) • c := by
      calc
        f x = f (x + s • w) + (0 - s) • (fderiv ℝ f (x + s • w) w) := by
          simpa using haff
        _ = f (x + s • w) + (-s) • (fderiv ℝ f (x + s • w) w) := by ring_nf
        _ = f (x + s • w) + (-s) • c := by rw [hc]
    have hre : (f (x + s • w) + (-s) • c) + s • c = f (x + s • w) := by
      calc
        (f (x + s • w) + (-s) • c) + s • c
            = f (x + s • w) + ((-s) • c + s • c) := by rw [add_assoc]
        _ = f (x + s • w) + ((-s) + s) • c := by rw [← add_smul]
        _ = f (x + s • w) := by rw [show (-s) + s = 0 by ring]; simp
    calc
      f (x + s • w) = (f (x + s • w) + (-s) • c) + s • c := hre.symm
      _ = f x + s • c := by rw [← haff']

/-- The open interval `(a,b)` is a right-neighbourhood of its left endpoint. -/
lemma Ioo_mem_nhdsWithin_Ioi {a b : ℝ} (hab : a < b) : Set.Ioo a b ∈ 𝓝[>] a := by
  rw [nhdsWithin, Filter.mem_inf_principal]
  have hb : Set.Iio b ∈ 𝓝 a := isOpen_Iio.mem_nhds (by simpa [Set.mem_Iio] using hab)
  filter_upwards [hb] with x hxb
  intro hxa
  rw [Set.mem_Ioi] at hxa
  exact ⟨hxa, hxb⟩

/-- The open interval `(a,b)` is a left-neighbourhood of its right endpoint. -/
lemma Ioo_mem_nhdsWithin_Iio {a b : ℝ} (hab : a < b) : Set.Ioo a b ∈ 𝓝[<] b := by
  rw [nhdsWithin, Filter.mem_inf_principal]
  have ha : Set.Ioi a ∈ 𝓝 b := isOpen_Ioi.mem_nhds (by simpa [Set.mem_Ioi] using hab)
  filter_upwards [ha] with x hxa
  intro hxb
  rw [Set.mem_Iio] at hxb
  exact ⟨hxa, hxb⟩

/-- `f` is continuous at the left boundary endpoint of the chord from within
the chord: `f (x + t•w) → f (x + lp•w)` as `t → lp⁺`. -/
lemma tendsto_f_at_left_param {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hwne : w ≠ 0) (hwpos : 0 < w 0) :
    Tendsto (fun t : ℝ => f (x + t • w)) (𝓝[>] leftParam x w)
      (𝓝 (f (x + leftParam x w • w))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hx0 : 0 < x 0 := by
    rw [stripInterior] at hx
    exact hx.1
  have hx1 : x 0 < 1 := by
    rw [stripInterior] at hx
    exact hx.2
  have hwposnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  let lp : ℝ := leftParam x w
  let rp : ℝ := rightParam x w
  have hab : lp < rp := leftParam_lt_rightParam hwpos hx0 hx1
  have hmem1 : Set.Ioo lp rp ∈ 𝓝[>] lp := Ioo_mem_nhdsWithin_Ioi hab
  have hmem2 : Set.Ioo lp (lp + ε / ‖w‖) ∈ 𝓝[>] lp :=
    Ioo_mem_nhdsWithin_Ioi (by
      rw [lt_add_iff_pos_right]
      exact div_pos hε hwposnorm)
  have hA : x + lp • w ∈ unitStrip :=
    chord_subset_unitStrip hwpos hx0 hx1 lp (by
      rw [Set.mem_Icc]
      exact ⟨le_rfl, le_of_lt hab⟩)
  filter_upwards [hmem1, hmem2] with t ht1 ht2
  rw [dist_eq_norm]
  have htIcc : t ∈ Set.Icc lp rp := by
    rw [Set.mem_Icc]
    exact ⟨le_of_lt ht1.1, le_of_lt ht1.2⟩
  have hyU : x + t • w ∈ unitStrip := chord_subset_unitStrip hwpos hx0 hx1 t htIcc
  have hlip : ‖f (x + t • w) - f (x + lp • w)‖ ≤ ‖(x + t • w) - (x + lp • w)‖ :=
    embedding_lipschitz hf (x := x + lp • w) hA (y := x + t • w) hyU
  have hΔ : (x + t • w) - (x + lp • w) = (t - lp) • w := by
    calc
      x + t • w - (x + lp • w) = (x + t • w) + (-x + -(lp • w)) := by
        rw [sub_eq_add_neg, neg_add]
      _ = t • w - lp • w := by
        rw [← sub_eq_add_neg]
        abel
      _ = (t - lp) • w := by
        rw [← sub_smul]
  have hnorm : ‖(x + t • w) - (x + lp • w)‖ = |t - lp| * ‖w‖ := by
    rw [hΔ, norm_smul]
    rw [Real.norm_eq_abs]
  have hsubpos : 0 < t - lp := sub_pos.mpr ht1.1
  have habs : |t - lp| = t - lp := abs_of_pos hsubpos
  have hlt1 : t - lp < ε / ‖w‖ := by
    have htw : t < lp + ε / ‖w‖ := ht2.2
    linarith
  have hprod : (t - lp) * ‖w‖ < ε := by
    have hm := mul_lt_mul_of_pos_right hlt1 hwposnorm
    rw [div_mul_cancel₀ ε hwposnorm.ne'] at hm
    exact hm
  calc
    ‖f (x + t • w) - f (x + lp • w)‖ ≤ ‖(x + t • w) - (x + lp • w)‖ := hlip
    _ = |t - lp| * ‖w‖ := hnorm
    _ = (t - lp) * ‖w‖ := by rw [habs]
    _ < ε := hprod

/-- The image value at the left boundary endpoint is the affine limit:
`f (x + lp•w) = f x + lp • fderiv f x w` for a crossing kernel direction. -/
lemma affine_value_at_left {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hdN0 : dN f x ≠ 0)
    (hker0 : dN f x w = 0) (hwne : w ≠ 0) (hwpos : 0 < w 0) :
    f (x + leftParam x w • w) = f x + leftParam x w • (fderiv ℝ f x w) := by
  have hx0 : 0 < x 0 := by
    rw [stripInterior] at hx
    exact hx.1
  have hx1 : x 0 < 1 := by
    rw [stripInterior] at hx
    exact hx.2
  let lp : ℝ := leftParam x w
  let rp : ℝ := rightParam x w
  let φ : ℝ → ℝ³ := fun t => f (x + t • w)
  let g : ℝ → ℝ³ := fun t => f x + t • (fderiv ℝ f x w)
  have hab : lp < rp := leftParam_lt_rightParam hwpos hx0 hx1
  have hφg : φ =ᶠ[𝓝[>] lp] g := by
    rw [Filter.EventuallyEq]
    exact eventually_of_mem (Ioo_mem_nhdsWithin_Ioi hab) (fun t ht => by
      simpa [φ, g] using affine_open_chord hf hx hdN0 hker0 hwne hwpos t ht)
  have hgcont : ContinuousAt g lp := by
    unfold g
    fun_prop
  have hgt : Tendsto g (𝓝[>] lp) (𝓝 (g lp)) :=
    (hgcont.tendsto).mono_left (by
      unfold nhdsWithin
      exact inf_le_left)
  have hφt : Tendsto φ (𝓝[>] lp) (𝓝 (g lp)) := hgt.congr' hφg.symm
  have hφA : Tendsto φ (𝓝[>] lp) (𝓝 (f (x + lp • w))) := by
    simpa [φ] using (tendsto_f_at_left_param hf hx hwne hwpos)
  have hEq : f (x + lp • w) = g lp := tendsto_nhds_unique hφA hφt
  simpa [g] using hEq

/-- `f` is continuous at the right boundary endpoint of the chord from within
the chord: `f (x + t•w) → f (x + rp•w)` as `t → rp⁻`. -/
lemma tendsto_f_at_right_param {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hwne : w ≠ 0) (hwpos : 0 < w 0) :
    Tendsto (fun t : ℝ => f (x + t • w)) (𝓝[<] rightParam x w)
      (𝓝 (f (x + rightParam x w • w))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hx0 : 0 < x 0 := by
    rw [stripInterior] at hx
    exact hx.1
  have hx1 : x 0 < 1 := by
    rw [stripInterior] at hx
    exact hx.2
  have hwposnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  let lp : ℝ := leftParam x w
  let rp : ℝ := rightParam x w
  have hab : lp < rp := leftParam_lt_rightParam hwpos hx0 hx1
  have hmem1 : Set.Ioo lp rp ∈ 𝓝[<] rp := Ioo_mem_nhdsWithin_Iio hab
  have hmem2 : Set.Ioo (rp - ε / ‖w‖) rp ∈ 𝓝[<] rp :=
    Ioo_mem_nhdsWithin_Iio (by
      rw [sub_lt_self_iff]
      exact div_pos hε hwposnorm)
  have hB : x + rp • w ∈ unitStrip :=
    chord_subset_unitStrip hwpos hx0 hx1 rp (by
      rw [Set.mem_Icc]
      exact ⟨le_of_lt hab, le_rfl⟩)
  filter_upwards [hmem1, hmem2] with t ht1 ht2
  rw [dist_eq_norm]
  have htIcc : t ∈ Set.Icc lp rp := by
    rw [Set.mem_Icc]
    exact ⟨le_of_lt ht1.1, le_of_lt ht1.2⟩
  have hyU : x + t • w ∈ unitStrip := chord_subset_unitStrip hwpos hx0 hx1 t htIcc
  have hlip : ‖f (x + t • w) - f (x + rp • w)‖ ≤ ‖(x + t • w) - (x + rp • w)‖ :=
    embedding_lipschitz hf (x := x + rp • w) hB (y := x + t • w) hyU
  have hΔ : (x + t • w) - (x + rp • w) = (t - rp) • w := by
    calc
      x + t • w - (x + rp • w) = (x + t • w) + (-x + -(rp • w)) := by
        rw [sub_eq_add_neg, neg_add]
      _ = t • w - rp • w := by
        rw [← sub_eq_add_neg]
        abel
      _ = (t - rp) • w := by
        rw [← sub_smul]
  have hnorm : ‖(x + t • w) - (x + rp • w)‖ = |t - rp| * ‖w‖ := by
    rw [hΔ, norm_smul]
    rw [Real.norm_eq_abs]
  have hsubneg : t - rp < 0 := sub_neg.mpr ht1.2
  have habs : |t - rp| = rp - t := by
    rw [abs_of_neg hsubneg]
    ring
  have hlt1 : rp - t < ε / ‖w‖ := by
    have htw : rp - ε / ‖w‖ < t := ht2.1
    linarith
  have hprod : (rp - t) * ‖w‖ < ε := by
    have hm := mul_lt_mul_of_pos_right hlt1 hwposnorm
    rw [div_mul_cancel₀ ε hwposnorm.ne'] at hm
    exact hm
  calc
    ‖f (x + t • w) - f (x + rp • w)‖ ≤ ‖(x + t • w) - (x + rp • w)‖ := hlip
    _ = |t - rp| * ‖w‖ := hnorm
    _ = (rp - t) * ‖w‖ := by rw [habs]
    _ < ε := hprod

/-- The image value at the right boundary endpoint is the affine limit:
`f (x + rp•w) = f x + rp • fderiv f x w` for a crossing kernel direction. -/
lemma affine_value_at_right {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hdN0 : dN f x ≠ 0)
    (hker0 : dN f x w = 0) (hwne : w ≠ 0) (hwpos : 0 < w 0) :
    f (x + rightParam x w • w) = f x + rightParam x w • (fderiv ℝ f x w) := by
  have hx0 : 0 < x 0 := by
    rw [stripInterior] at hx
    exact hx.1
  have hx1 : x 0 < 1 := by
    rw [stripInterior] at hx
    exact hx.2
  let lp : ℝ := leftParam x w
  let rp : ℝ := rightParam x w
  let φ : ℝ → ℝ³ := fun t => f (x + t • w)
  let g : ℝ → ℝ³ := fun t => f x + t • (fderiv ℝ f x w)
  have hab : lp < rp := leftParam_lt_rightParam hwpos hx0 hx1
  have hφg : φ =ᶠ[𝓝[<] rp] g := by
    rw [Filter.EventuallyEq]
    exact eventually_of_mem (Ioo_mem_nhdsWithin_Iio hab) (fun t ht => by
      simpa [φ, g] using affine_open_chord hf hx hdN0 hker0 hwne hwpos t ht)
  have hgcont : ContinuousAt g rp := by
    unfold g
    fun_prop
  have hgt : Tendsto g (𝓝[<] rp) (𝓝 (g rp)) :=
    (hgcont.tendsto).mono_left (by
      unfold nhdsWithin
      exact inf_le_left)
  have hφt : Tendsto φ (𝓝[<] rp) (𝓝 (g rp)) := hgt.congr' hφg.symm
  have hφB : Tendsto φ (𝓝[<] rp) (𝓝 (f (x + rp • w))) := by
    simpa [φ] using (tendsto_f_at_right_param hf hx hwne hwpos)
  have hEq : f (x + rp • w) = g rp := tendsto_nhds_unique hφB hφt
  simpa [g] using hEq

/-- **Closed-chord affineness for the canonical U-leaf**: `f` is affine on
the whole closed chord `[uBendA, uBendB]`, including the boundary endpoints:
`f (x + s•w) = f x + s • fderiv f x w` for every `s ∈ Icc lp rp`. -/
theorem affine_on_uBendClosed {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ∀ s ∈ Set.Icc (leftParam x (uBendDirPos hf ha hx hdN))
        (rightParam x (uBendDirPos hf ha hx hdN)),
      f (x + s • (uBendDirPos hf ha hx hdN)) =
        f x + s • (fderiv ℝ f x (uBendDirPos hf ha hx hdN)) := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  intro s hs
  have hab0 : leftParam x (uBendDirPos hf ha hx hdN) <
      rightParam x (uBendDirPos hf ha hx hdN) :=
    (zero_between_params hf ha hx hdN).1.trans (zero_between_params hf ha hx hdN).2
  rw [mem_Icc_eq_Ioo_or_endpoints (a := leftParam x (uBendDirPos hf ha hx hdN))
    (b := rightParam x (uBendDirPos hf ha hx hdN)) hab0 (s := s)] at hs
  rcases hs with hsIoo | hsL | hsR
  · exact affine_open_chord hf hx hdN hker hwne hwpos s hsIoo
  · subst s
    exact affine_value_at_left hf hx hdN hker hwne hwpos
  · subst s
    exact affine_value_at_right hf hx hdN hker hwne hwpos

/-- The image of the closed U-leaf is an isometric straight segment: the
distance between the images of the two boundary endpoints equals the length
of the preimage chord. -/
theorem bend_length_eq {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    ‖f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)‖ =
    ‖uBendB hf ha hx hdN - uBendA hf ha hx hdN‖ := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  let w : ℝ² := uBendDirPos hf ha hx hdN
  let lp : ℝ := leftParam x w
  let rp : ℝ := rightParam x w
  let c : ℝ³ := fderiv ℝ f x w
  have hAval : f (uBendA hf ha hx hdN) = f x + lp • c := by
    simpa [uBendA, w, lp, c] using affine_value_at_left hf hx hdN hker hwne hwpos
  have hBval : f (uBendB hf ha hx hdN) = f x + rp • c := by
    simpa [uBendB, w, rp, c] using affine_value_at_right hf hx hdN hker hwne hwpos
  have hpre : uBendB hf ha hx hdN - uBendA hf ha hx hdN = (rp - lp) • w := by
    unfold uBendB uBendA
    calc
      x + rp • w - (x + lp • w) = rp • w - lp • w := by abel
      _ = (rp - lp) • w := by rw [← sub_smul]
  have himg : f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN) = (rp - lp) • c := by
    rw [hBval, hAval]
    calc
      f x + rp • c - (f x + lp • c) = rp • c - lp • c := by abel
      _ = (rp - lp) • c := by rw [← sub_smul]
  rw [hpre, himg, norm_smul, norm_smul]
  rw [Real.norm_eq_abs]
  have hnormc : ‖c‖ = ‖w‖ := by
    simpa [c] using fderiv_norm_eq_interior hf x hx w
  rw [hnormc]

/-- **Image of the whole open chord is straight**: for a crossing kernel
direction `w` at `x`, the image displacement between the two boundary-line
points equals the constant tangent times the parameter length:
`f (x + rp•w) − f (x + lp•w) = (rp − lp) • fderiv f x w`. -/
lemma imageVec_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hdN0 : dN f x ≠ 0)
    (hker0 : dN f x w = 0) (hwne : w ≠ 0) (hwpos : 0 < w 0) :
    f (x + rightParam x w • w) - f (x + leftParam x w • w) =
      (rightParam x w - leftParam x w) • (fderiv ℝ f x w) := by
  have hL : f (x + leftParam x w • w) = f x + leftParam x w • (fderiv ℝ f x w) :=
    affine_value_at_left hf hx hdN0 hker0 hwne hwpos
  have hR : f (x + rightParam x w • w) = f x + rightParam x w • (fderiv ℝ f x w) :=
    affine_value_at_right hf hx hdN0 hker0 hwne hwpos
  rw [hL, hR]
  calc
    (f x + rightParam x w • (fderiv ℝ f x w)) - (f x + leftParam x w • (fderiv ℝ f x w))
        = rightParam x w • (fderiv ℝ f x w) - leftParam x w • (fderiv ℝ f x w) := by abel
    _ = (rightParam x w - leftParam x w) • (fderiv ℝ f x w) := by rw [← sub_smul]

/-- **Image displacement of the canonical leaf**: between the images of the
two boundary endpoints the tangent is the constant
`fderiv f x wpos` (times the positive length factor). -/
theorem canonicalImageVec {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN) =
      (rightParam x (uBendDirPos hf ha hx hdN) - leftParam x (uBendDirPos hf ha hx hdN)) •
        (fderiv ℝ f x (uBendDirPos hf ha hx hdN)) := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  simpa [uBendA, uBendB] using imageVec_chord hf hx hdN hker hwne hwpos

/-- **Positive normalization is invariant under positive scaling**: for
`0 < a` and `v ≠ 0`, `(‖a•v‖⁻¹) • (a•v) = (‖v‖⁻¹) • v`. -/
lemma unitDir_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} {v : E} (ha : 0 < a) (hv : v ≠ 0) :
    (‖a • v‖⁻¹) • (a • v) = (‖v‖⁻¹) • v := by
  have hnorm : ‖a • v‖ = a * ‖v‖ := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt ha)]
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [hnorm]
  rw [smul_smul]
  congr 1
  field_simp [ne_of_gt ha, hvnorm]

/-- **The unit image direction of the canonical leaf**: the normalization of
`f(uBendB) − f(uBendA)` equals the normalized constant tangent
`c/‖c‖` with `c = fderiv f x wpos`. -/
theorem canonicalUnitImageDir {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (‖f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)‖⁻¹) •
        (f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)) =
      (‖fderiv ℝ f x (uBendDirPos hf ha hx hdN)‖⁻¹) •
        (fderiv ℝ f x (uBendDirPos hf ha hx hdN)) := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  let w : ℝ² := uBendDirPos hf ha hx hdN
  let c : ℝ³ := fderiv ℝ f x w
  have hx0 : 0 < x 0 := by
    rw [stripInterior] at hx
    exact hx.1
  have hx1 : x 0 < 1 := by
    rw [stripInterior] at hx
    exact hx.2
  have hsc : 0 < rightParam x w - leftParam x w :=
    sub_pos.mpr (leftParam_lt_rightParam hwpos hx0 hx1)
  have hcne : c ≠ 0 := by
    intro hz
    have hz' : fderiv ℝ f x w = 0 := by simpa [c] using hz
    have hnorm : ‖fderiv ℝ f x w‖ = ‖w‖ := fderiv_norm_eq_interior hf x hx w
    have : ‖w‖ = 0 := by
      rw [← hnorm, hz']
      simp
    have hw0 : w ≠ 0 := by simpa [w] using hwne
    exact norm_ne_zero_iff.mp (by simpa [w] using hw0) this
  change (‖f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)‖⁻¹) •
        (f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)) =
      (‖c‖⁻¹) • c
  -- image vector = (rp − lp) • c, so unit image = c/‖c‖ by positive scaling
  have himg : f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN) = (rightParam x w - leftParam x w) • c := by
    simpa [w, c] using canonicalImageVec hf ha hx hdN
  rw [himg]
  exact unitDir_pos_smul (E := ℝ³) hsc hcne

/-- **Image unit direction = tangent of the unit preimage direction**: the
normalized tangent `(‖fderiv f x w‖⁻¹) • fderiv f x w` equals
`fderiv f x ((‖w‖⁻¹) • w)` for a nonzero direction `w` (the isometry
`‖fderiv f x w‖ = ‖w‖` identifies the unit vectors). -/
lemma imageUnitDir_eq_tangent_of_unit {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x w : ℝ²} (hx : x ∈ stripInterior) (hwne : w ≠ 0) :
    (‖fderiv ℝ f x w‖⁻¹) • (fderiv ℝ f x w) = fderiv ℝ f x ((‖w‖⁻¹) • w) := by
  have hnorm : ‖fderiv ℝ f x w‖ = ‖w‖ := fderiv_norm_eq_interior hf x hx w
  calc
    (‖fderiv ℝ f x w‖⁻¹) • (fderiv ℝ f x w) = (‖w‖⁻¹) • (fderiv ℝ f x w) := by rw [hnorm]
    _ = fderiv ℝ f x ((‖w‖⁻¹) • w) := (map_smul (fderiv ℝ f x) (‖w‖⁻¹) w).symm

/-- **The unit image direction of the canonical leaf is the image (under
`fderiv f x`) of the unit preimage direction** `wpos/‖wpos‖`. -/
theorem canonicalImageUnitDir_eq_tangent {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    (‖f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)‖⁻¹) •
        (f (uBendB hf ha hx hdN) - f (uBendA hf ha hx hdN)) =
      fderiv ℝ f x ((‖uBendDirPos hf ha hx hdN‖⁻¹) • uBendDirPos hf ha hx hdN) := by
  rcases uBendDirPos_spec hf ha hx hdN with ⟨hker, hwne, hwpos⟩
  rw [canonicalUnitImageDir hf ha hx hdN]
  exact imageUnitDir_eq_tangent_of_unit hf hx hwne

end Submission.PaperBand
