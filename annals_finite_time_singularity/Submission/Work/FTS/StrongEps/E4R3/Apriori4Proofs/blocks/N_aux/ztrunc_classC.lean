import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ZTrunc
import Submission.Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# `N_aux.ZTruncClassC` — `ClassC` is invariant under the truncation `ztrunc`

`ztrunc w z θ = if 0 < z then w z θ else 0` agrees with `w` everywhere on the half-plane
`z > 0`, i.e. on the open set `Ioi 0 ×ˢ univ`.  Every field of `ClassC α w` is

* an open-quadrant value (`reg : SmoothOpen`, and the values of `w`, of its `z`-slices
  (`fsm`), of the ratio `w z θ / z` near `z = 0⁺` (`axis`), or of the nonlocal operator
  `L₁₂` (`l12`), whose defining integral runs over `s > z ≥ 0`),
* `HkMem α k` (integrals over `Iz = [0,∞)`, whose weight `w(z) = (1+z)²/z²` vanishes at
  `z = 0`), or
* a one-sided trace/limit (`BdryTraces`, `ThetaTraces`, taken at `z > 0`, as `z → 0⁺`,
  as `z → ∞`, or as `θ → 0⁺`, `θ → π/2⁻`),

and none of these sees the values of `w` at `z ≤ 0`.  The `norm` field is the exception in a
different way: it is the only field that needs the *weak* vanishing hypothesis `hz` on `w`
(for `θ ∉ (0,π/2)` and `z > 0`), since `ztrunc` does not modify the values at `z > 0`.

The `θ`-part of the traces is free: `hw.norm` already gives `w z 0 = w z (π/2) = 0` for every
`z`, and `ztrunc` agrees with `w` there.
-/

/-! ## The slots of `ztrunc` on the open half-plane -/

/-- The mixed slots of `ztrunc w` and `w` agree at every point of the open half-plane
`z > 0` (with no smoothness hypothesis: the derivative operators are local). -/
theorem ztrunc_mixed_eq {w : Fn} (b a : ℕ) {z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.mixed b a (ztrunc w) z θ = Work.Spaces.mixed b a w z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have h : Set.EqOn (Function.uncurry (ztrunc w)) (Function.uncurry w)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := fun p hp => ztrunc_of_pos hp.1
  exact Work.FTS.RegPkgGal.mixed_congr_of_isOpen hV h b a (x := (z, θ))
    ⟨by simpa using hz, trivial⟩

/-! ## The boundary traces -/

/-- Composition with `z ↦ z * (· * w z)²` preserves eventual equality (`w` the radial
weight of `Work.Spaces`). -/
private theorem eeq_mul_w_sq {l : Filter ℝ} {u v : ℝ → ℝ} (h : u =ᶠ[l] v) :
    (fun z => z * (u z * Work.Spaces.w z) ^ 2) =ᶠ[l]
      (fun z => z * (v z * Work.Spaces.w z) ^ 2) := by
  filter_upwards [h] with z hz
  rw [hz]

/-- Composition with `θ ↦ sin(2θ)^{1-γ} * (·)²` preserves eventual equality. -/
private theorem eeq_sin_gam_sq {α : ℝ} {l : Filter ℝ} {u v : ℝ → ℝ} (h : u =ᶠ[l] v) :
    (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (u θ) ^ 2) =ᶠ[l]
      (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (v θ) ^ 2) := by
  filter_upwards [h] with θ hθ
  rw [hθ]

/-- `BdryTraces` is invariant under `ztrunc`: the four boundary directions only see the
germ of the mixed slots along `z > 0`. -/
theorem ztrunc_bdryTraces {α : ℝ} {k : ℕ} {w : Fn}
    (h : Work.FTS.Nonlin.BdryTraces α k w) :
    Work.FTS.Nonlin.BdryTraces α k (ztrunc w) := by
  intro a b hab
  obtain ⟨hA, hB⟩ := h a b hab
  refine ⟨fun θ hθ => ⟨?_, ?_⟩, fun z hz0 => ⟨?_, ?_⟩⟩
  · refine (Filter.tendsto_congr' (eeq_mul_w_sq ?_)).mpr (hA θ hθ).1
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [ztrunc_mixed_eq b a hz]
  · refine (Filter.tendsto_congr' (eeq_mul_w_sq ?_)).mpr (hA θ hθ).2
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    rw [ztrunc_mixed_eq b a hz]
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr (hB z hz0).1
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq b a hz0]
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr (hB z hz0).2
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq b a hz0]

/-- `ThetaTraces` is invariant under `ztrunc` (the `θ`-traces are taken at `z > 0`). -/
theorem ztrunc_thetaTraces {α : ℝ} {k : ℕ} {w : Fn}
    (h : Work.FTS.PhiStar.ThetaTraces α k w) :
    Work.FTS.PhiStar.ThetaTraces α k (ztrunc w) := by
  intro s hs z hz
  obtain ⟨h1, h2⟩ := h s hs z hz
  refine ⟨?_, ?_⟩
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr h1
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq s 0 hz]
  · refine (Filter.tendsto_congr' (eeq_sin_gam_sq ?_)).mpr h2
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    rw [ztrunc_mixed_eq s 0 hz]

/-! ## The angular moment, the normalisation, the axis condition and `L₁₂` -/

/-- The angular moment `F_*(z) = ∫_θ w z θ sin θ cos²θ` of `ztrunc w` equals that of `w` for
every `z > 0`. -/
theorem ztrunc_Fstar {w : Fn} {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar (ztrunc w) z = Work.Elliptic.Fstar w z := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
  intro θ hθ
  simp only [ztrunc_of_pos hz]

/-- `ztrunc w` is angularly normalised as soon as `w` vanishes off the open quadrant for
`z > 0`. -/
theorem ztrunc_normTh {w : Fn}
    (hz : ∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) :
    Work.FTS.ClassC.normTh (ztrunc w) = ztrunc w := by
  funext z θ
  by_cases hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)
  · simp [Work.FTS.ClassC.normTh, hθ]
  · rw [Work.FTS.ClassC.normTh_apply_of_not_mem hθ]
    by_cases hzpos : 0 < z
    · rw [ztrunc_of_pos hzpos, hz z θ hzpos hθ]
    · exact (ztrunc_of_nonpos hzpos).symm

/-- The axis condition transfers to `ztrunc`. -/
theorem ztrunc_axis {w : Fn}
    (h : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Tendsto (fun z => w z θ / z) (𝓝[>] 0) (𝓝 0)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Tendsto (fun z => ztrunc w z θ / z) (𝓝[>] 0) (𝓝 0) := by
  intro θ hθ
  refine (Filter.tendsto_congr' ?_).mpr (h θ hθ)
  filter_upwards [self_mem_nhdsWithin] with z hz
  rw [ztrunc_of_pos hz]

/-- The zero mode of `L₁₂` is unchanged by the truncation: its defining integral runs over
`s > z ≥ 0`, where `ztrunc w = w`. -/
theorem ztrunc_L12 (w : Fn) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 (ztrunc w) z = Work.Construction.L12 w z :=
  Work.FTS.GalFields.RHS.L12f_congr_of_agreeOnQ hz
    (fun _ _ hz' _ _ => ztrunc_of_pos hz')

/-! ## The target -/

/-- **`ClassC` is invariant under the truncation `ztrunc`.**

`ztrunc w z θ = if 0 < z then w z θ else 0` agrees with `w` on the whole half-plane `z > 0`, and
every field of `ClassC α w` is either an open-quadrant value (`reg : SmoothOpen`, `norm`,
`fsm`, `axis`, `l12`), an integral over `Iz = [0,∞)` whose integrand vanishes at `z = 0`
(`mem`, `mem8`, `mem10`), or a one-sided trace/limit taken at `z ∈ Ioi 0` or as `z → 0⁺`, `z → ∞`,
`θ → 0⁺`, `θ → π/2⁻` (`tr`, `tr7`, `thTr`).  Note `hw.norm : normTh w = w` already gives
`w z 0 = w z (π/2) = 0` for every `z`, so the `θ`-part of the fields is free. -/
theorem ztrunc_classC {α : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hw : Work.FTS.ClassC.ClassC α w)
    (hz : ∀ z θ : ℝ, 0 < z → θ ∉ Set.Ioo 0 (Real.pi / 2) → w z θ = 0) :
    Work.FTS.ClassC.ClassC α
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.ztrunc w) := by
  refine { norm := ztrunc_normTh hz, reg := smoothOpen_ztrunc hw.reg,
           mem := HkMem_ztrunc hw.mem, mem8 := HkMem_ztrunc hw.mem8,
           mem10 := HkMem_ztrunc hw.mem10,
           tr := ztrunc_bdryTraces hw.tr, tr7 := ztrunc_bdryTraces hw.tr7,
           fsm := ?_, axis := ztrunc_axis hw.axis,
           l12 := by rw [ztrunc_L12 w le_rfl, hw.l12],
           thTr := ztrunc_thetaTraces hw.thTr }
  intro m
  exact (hw.fsm m).congr (fun z hz' => ztrunc_Fstar hz')

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
