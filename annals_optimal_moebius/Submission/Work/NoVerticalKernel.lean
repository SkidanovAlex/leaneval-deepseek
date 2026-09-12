import Submission.PaperBand.Band
import Submission.PaperBand.PeriodicFacts
import Submission.Work.NoFlatStopODE
import Submission.PaperBand.KernelMaximal

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# No vertical kernel directions (main0 step 1.1)

Target: at a point `x ∈ U = {dN ≠ 0}` of the paper band, the kernel line of
the shape operator is never vertical (never parallel to the unbounded strip
direction `e₁`).

## Mathematics (from session_status27)
If `dN f x e₁ = 0` with `dN f x ≠ 0` at `x ∈ stripInterior`, the maximal
kernel segment through `x` in the vertical direction would extend through the
whole forward ray (`vertical_kernel_ray_U`: it cannot stop at a flat point
(`flat_stop_impossible`), cannot leave `U` (openness + the extension
machinery), and never reaches the strip boundary (`x₀` is constant)).  Along
that whole ray `f` is affine (`BendSegments.affine_on_kernel_segment` on each
compact piece) with unit slope `c₀ = fderiv ℝ f x e₁` (an isometry), so the
image contains an unbounded straight segment — contradicting that the image
of the unit strip is bounded (`f_strip_bounded` below: every orbit meets the
compact `bandChunk a`, and `f` is constant on orbits).

This file contains the boundedness half (`f_even_shift`, `f_eq_of_bandRel`,
`f_strip_bounded`) and the maximal vertical kernel-ray lemma
(`vertical_kernel_ray_U`), all green.

## Status (main0 step 1.1): COMPLETE
* `vertical_kernel_ray_U` (PROVED, below): if `x ∈ U` and `e₁ = !₂[0,1]` is
  a kernel direction at `x`, then for every `t ≥ 0` the point
  `P(t) = x + t•e₁` stays in `stripInterior`, in `U`, with `e₁` a kernel
  direction.  Proof: cofinality of `verticalE` (sup-branches: extend past
  the sup with `kernel_segment_extend_right` + `kernel_e1_at_ray_endpoint`
  (`dN p ≠ 0` case), `flat_stop_impossible` with direction `−e₁`
  (`dN p = 0` case)), then downward closure.
* `vertical_kernel_impossible` (PROVED, below): a vertical kernel direction
  at an interior point of `U` is impossible — the forward ray would be an
  affine image of unit speed (`affine_on_kernel_segment` + `‖fderiv ℝ f x e₁‖
  = 1` via `tangent₁`), contradicting `f_strip_bounded`.  Only the forward
  ray (`t ≥ 0`) is needed, so no whole-line/direction-parametrised mirror of
  `vertical_kernel_ray_U` is required.
* `exists_crossing_kernel_direction` (PROVED, below): at every interior
  point of `U` there is a nonzero kernel direction `w` with `w 0 ≠ 0` — the
  bend direction is never vertical, so it crosses the strip (this is the
  direction input of `bends_reach_boundary_test` / `kernel_segment_two_sided`
  for Prop main0's U-bends).
-/

noncomputable section
namespace Submission.PaperBand

/-- `f` is invariant under shifting the second coordinate by an integer
multiple of `2a` (even power of the period), on the strip. -/
lemma f_even_shift {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x0 : ℝ} (hx0 : x0 ∈ Set.Icc (0 : ℝ) 1) (y : ℝ) (k : ℤ) :
    f !₂[x0, y + k • (2 * a)] = f !₂[x0, y] := by
  let φ : ℝ → ℝ³ := fun t => f !₂[x0, t]
  have hφ : Function.Periodic φ (2 * a) := by
    intro t
    dsimp [φ]
    exact f_period_twice hf (x := !₂[x0, t]) (by
      change x0 ∈ Set.Icc (0 : ℝ) 1
      exact hx0)
  have hz := hφ.zsmul k
  dsimp [φ] at hz
  -- hz : f !₂[x0, y + k • (2a)] = f !₂[x0, y]
  exact hz y

/-- `f` is constant on period orbits of points of the strip. -/
lemma f_eq_of_bandRel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {z c : ℝ²} (hz : z ∈ unitStrip) (hrel : bandRel a z c) : f z = f c := by
  rcases hrel with ⟨n, hx0eq, hd⟩ | ⟨n, hsum, hd⟩
  · -- even: c₀ = z₀, c₁ − z₁ = (2n)·a
    have hz0 : z 0 ∈ Set.Icc (0 : ℝ) 1 := by
      change z 0 ∈ Set.Icc (0 : ℝ) 1 at hz
      exact hz
    have hc' : c = !₂[z 0, z 1 + n • (2 * a)] := by
      ext i <;> fin_cases i
      · dsimp
        exact hx0eq.symm
      · dsimp
        have hzsm : (2 * n) • a = n • (2 * a) := (zsmul_two_mul a n).symm
        have hd' : c 1 - z 1 = n • (2 * a) := by simpa [hzsm] using hd
        linarith
    have hzvec : z = !₂[z 0, z 1] := by
      ext i <;> fin_cases i <;> rfl
    calc
      f z = f !₂[z 0, z 1] := congrArg f hzvec
      _ = f !₂[z 0, z 1 + n • (2 * a)] := (f_even_shift hf hz0 (z 1) n).symm
      _ = f c := by rw [hc']
  · -- odd: c₀ + z₀ = 1, c₁ − z₁ = (2n+1)·a
    let pz : ℝ² := period a z
    have hpz : pz ∈ unitStrip := by
      dsimp [pz]
      exact period_mem_unitStrip hz
    have hz0 : z 0 ∈ Set.Icc (0 : ℝ) 1 := by
      change z 0 ∈ Set.Icc (0 : ℝ) 1 at hz
      exact hz
    have hx0' : 1 - z 0 ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_Icc] at hz0 ⊢
      constructor <;> linarith
    have hc' : c = !₂[1 - z 0, (z 1 + a) + n • (2 * a)] := by
      ext i <;> fin_cases i
      · dsimp
        linarith [hsum]
      · dsimp
        have hzsm : (2 * n) • a = n • (2 * a) := (zsmul_two_mul a n).symm
        have hd' : c 1 - z 1 = (2 * n + 1) • a := hd
        have h1 : c 1 = z 1 + (2 * n + 1) • a := by linarith
        have h2 : (2 * n + 1) • a = a + n • (2 * a) := by
          have hc : (2 * n + 1) • a = (2 * n) • a + a := by
            rw [add_zsmul]
            norm_num
          rw [hc, hzsm]
          abel
        have h3 : c 1 = z 1 + a + n • (2 * a) := by
          rw [h1, h2]
          abel
        linarith
    have hfperiod : f (period a z) = f z := hf.periodic z hz
    have hfeven : f !₂[1 - z 0, (z 1 + a) + n • (2 * a)] = f !₂[1 - z 0, z 1 + a] :=
      f_even_shift hf hx0' (z 1 + a) n
    have hbase : f !₂[1 - z 0, z 1 + a] = f z := by
      have hpt : period a z = !₂[1 - z 0, z 1 + a] := by
        ext i <;> fin_cases i <;> simp [period]
      calc
        f !₂[1 - z 0, z 1 + a] = f (period a z) := by rw [hpt]
        _ = f z := hfperiod
    calc
      f z = f !₂[1 - z 0, z 1 + a] := hbase.symm
      _ = f !₂[1 - z 0, (z 1 + a) + n • (2 * a)] := (f_even_shift hf hx0' (z 1 + a) n).symm
      _ = f c := by rw [hc']

/-- **The image of the unit strip is bounded**: the paper band image is
compact, hence bounded in `ℝ³`. -/
theorem f_strip_bounded {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) (ha : 0 < a) :
    ∃ R : ℝ, ∀ z ∈ unitStrip, ‖f z‖ ≤ R := by
  -- f is constant on orbits, so f(unitStrip) = f(bandChunk a); the chunk is compact
  have hchunk : IsCompact (bandChunk a) := isCompact_bandChunk a ha
  have hcont : ContinuousOn f (bandChunk a) :=
    hf.smooth.continuousOn.mono (bandChunk_subset_unitStrip a)
  have himg : IsCompact (f '' bandChunk a) := hchunk.image_of_continuousOn hcont
  -- compact ⟹ bounded: some R bounding the norms of the image
  have hB : ∃ R : ℝ, ∀ y ∈ f '' bandChunk a, ‖y‖ ≤ R := by
    rcases himg.isBounded.subset_ball (0 : ℝ³) with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    intro y hy
    have hyb := hr hy
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hyb
    exact le_of_lt hyb
  rcases hB with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  intro z hz
  rcases exists_bandChunk_equiv ha hz with ⟨c, hc, hrel⟩
  have hfz : f z = f c := f_eq_of_bandRel hf hz hrel
  have hin : f c ∈ f '' bandChunk a := ⟨c, hc, rfl⟩
  -- ‖f z‖ = ‖f c‖ ≤ R
  have hnorm : ‖f z‖ ≤ R := by
    rw [hfz]
    exact hR (f c) hin
  exact hnorm



/-- A point reached by moving `x` in a direction whose `0`-coordinate is
zero stays in the strip interior (the `0`-coordinate is constant). -/
lemma vertical_mem_stripInterior {x : ℝ²} (hx : x ∈ stripInterior) (v : ℝ²)
    (hv : v 0 = 0) (t : ℝ) : x + t • v ∈ stripInterior := by
  change (x + t • v) 0 ∈ Set.Ioo (0 : ℝ) 1
  change x 0 ∈ Set.Ioo (0 : ℝ) 1 at hx
  simp [hv]
  exact hx



/-- **Left-continuity of the kernel condition along the vertical ray**: if
`e₁` is a kernel direction at every point of the open segment `(0,β)` of the
ray through `x`, then it is also a kernel direction at the endpoint
`x + β•e₁` (the kernel-valued map is continuous there, and the condition
holds on a left neighbourhood by hypothesis). -/
lemma kernel_e1_at_ray_endpoint {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) {β : ℝ} (hβ : 0 < β)
    (hφ : ∀ r ∈ Set.Ioo (0 : ℝ) β, dN f (x + r • !₂[0, 1]) !₂[0, 1] = 0) :
    dN f (x + β • !₂[0, 1]) !₂[0, 1] = 0 := by
  let e₁ : ℝ² := !₂[0, 1]
  have he₁0 : e₁ 0 = 0 := by simp [e₁]
  have hpI : x + β • e₁ ∈ stripInterior := vertical_mem_stripInterior hx e₁ he₁0 β
  have hφc : ContinuousAt (fun r : ℝ => dN f (x + r • e₁) e₁) β := by
    -- φ = (CLM-map) evaluated at e₁: clm_apply on hcontCLM? use differentiability again
    have hdif : DifferentiableAt ℝ (fun z : ℝ² => dN f z) (x + β • e₁) := by
      have h1 : DifferentiableOn ℝ (fun z : ℝ² => dN f z) stripInterior := by
        exact ContDiffOn.differentiableOn (contDiffOn_dN hf) (by decide)
      exact h1.differentiableAt (IsOpen.mem_nhds stripInterior_isOpen hpI)
    have haffD : DifferentiableAt ℝ (fun r : ℝ => x + r • e₁) β := by fun_prop
    have hcomp : DifferentiableAt ℝ (fun r : ℝ => dN f (x + r • e₁)) β := by
      fun_prop
    have hφd : DifferentiableAt ℝ (fun r : ℝ => (dN f (x + r • e₁)) e₁) β :=
      hcomp.clm_apply (differentiableAt_const (c := e₁) (𝕜 := ℝ))
    exact hφd.continuousAt
  by_contra hz
  have hnorm : 0 < ‖dN f (x + β • e₁) e₁‖ := norm_pos_iff.mpr hz
  -- continuity of φ at β: eventually ‖φ r − φ β‖ < ‖φβ‖/2
  have hev : ∀ᶠ r : ℝ in 𝓝 β,
      ‖dN f (x + r • e₁) e₁ - dN f (x + β • e₁) e₁‖ < ‖dN f (x + β • e₁) e₁‖ / 2 := by
    have ht := Metric.tendsto_nhds.mp hφc.tendsto (‖dN f (x + β • e₁) e₁‖ / 2) (by positivity)
    filter_upwards [ht] with r hr
    simpa [Real.dist_eq, dist_eq_norm] using hr
  rcases Metric.mem_nhds_iff.mp hev with ⟨δ, hδ, hδ'⟩
  let r₀ : ℝ := β - min (δ / 2) (β / 2)
  have hr₀I : r₀ ∈ Set.Ioo (0 : ℝ) β := by
    rw [Set.mem_Ioo]
    dsimp [r₀]
    have hm : 0 < min (δ / 2) (β / 2) := lt_min (by positivity) (by positivity)
    have hb : min (δ / 2) (β / 2) < β := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hβ)
    constructor <;> linarith
  have hφ0 : dN f (x + r₀ • e₁) e₁ = 0 := hφ r₀ hr₀I
  have hb₀ : r₀ ∈ Metric.ball β δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have hm : min (δ / 2) (β / 2) < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
    have hd : |r₀ - β| = min (δ / 2) (β / 2) := by
      dsimp [r₀]
      have hm0 : 0 ≤ min (δ / 2) (β / 2) := le_of_lt (lt_min (by positivity) (by positivity))
      have hle : r₀ - β ≤ 0 := by
        dsimp [r₀]
        linarith
      rw [abs_of_nonpos hle]
      dsimp [r₀]
      ring
    rw [hd]
    exact hm
  have hsmall := hδ' hb₀
  have hcontr : ‖dN f (x + β • e₁) e₁‖ < ‖dN f (x + β • e₁) e₁‖ / 2 := by
    simpa [hφ0] using hsmall
  linarith



/-- `dN ≠ 0` holds on a neighbourhood of `r₀` along an affine ray through an
interior point where the value is nonzero. -/
lemma eventually_dN_ne_zero_ray {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x v : ℝ²} {r₀ : ℝ} (hri : x + r₀ • v ∈ stripInterior)
    (hV : dN f (x + r₀ • v) ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝 r₀, dN f (x + r • v) ≠ 0 := by
  have hφc : ContinuousAt (fun r : ℝ => dN f (x + r • v)) r₀ := by
    have hdif : DifferentiableAt ℝ (fun z : ℝ² => dN f z) (x + r₀ • v) := by
      have h1 : DifferentiableOn ℝ (fun z : ℝ² => dN f z) stripInterior := by
        exact ContDiffOn.differentiableOn (contDiffOn_dN hf) (by decide)
      exact h1.differentiableAt (IsOpen.mem_nhds stripInterior_isOpen hri)
    have haffD : DifferentiableAt ℝ (fun r : ℝ => x + r • v) r₀ := by fun_prop
    have hcomp : DifferentiableAt ℝ (fun r : ℝ => dN f (x + r • v)) r₀ := by
      fun_prop
    exact hcomp.continuousAt
  have htend : Filter.Tendsto (fun r : ℝ => dN f (x + r • v)) (𝓝 r₀)
      (𝓝 (dN f (x + r₀ • v))) := hφc.tendsto
  have hnorm : 0 < ‖dN f (x + r₀ • v)‖ := norm_pos_iff.mpr hV
  filter_upwards [Metric.tendsto_nhds.mp htend ‖dN f (x + r₀ • v)‖ hnorm] with r hr
  intro hz0
  have hdist : ‖(dN f (x + r • v)) - dN f (x + r₀ • v)‖ < ‖dN f (x + r₀ • v)‖ := by
    simpa [Real.dist_eq, dist_eq_norm] using hr
  have : ‖dN f (x + r₀ • v)‖ < ‖dN f (x + r₀ • v)‖ := by
    rw [hz0] at hdist
    simpa using hdist
  linarith

/-- The candidate set of parameters `s ≥ 0` for the vertical kernel-`U`-ray
through `x`: on `[0,s]` every point stays in the strip interior, is in `U`
(`dN ≠ 0`), and has `e₁` in the kernel. -/
def verticalE (f : ℝ² → ℝ³) (x : ℝ²) (e₁ : ℝ²) : Set ℝ :=
  {s : ℝ | 0 ≤ s ∧ ∀ r ∈ Set.Icc 0 s,
    x + r • e₁ ∈ stripInterior ∧ dN f (x + r • e₁) ≠ 0 ∧ dN f (x + r • e₁) e₁ = 0}

/-- `0 ∈ verticalE`: the start point has the three properties. -/
lemma verticalE_zero_mem {f : ℝ² → ℝ³} {x : ℝ²} (hx : x ∈ stripInterior)
    (hU0 : dN f x ≠ 0) {e₁ : ℝ²} (hk0 : dN f x e₁ = 0) : 0 ∈ verticalE f x e₁ := by
  refine ⟨le_rfl, ?_⟩
  intro r hr
  have hr0 : r = 0 := by
    rw [Set.mem_Icc] at hr
    linarith
  subst r
  exact ⟨by simpa using hx, by simpa using hU0, by simpa using hk0⟩

/-- **`verticalE` contains a positive element**: a short kernel segment from
`kernel_segment_start`, intersected with the `dN ≠ 0` neighbourhood at `x`,
lies entirely in `verticalE`. -/
lemma verticalE_positive {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x e₁ : ℝ²} (hx : x ∈ stripInterior) (hU0 : dN f x ≠ 0)
    (hk0 : dN f x e₁ = 0) (he₁ : e₁ ≠ 0) :
    ∃ s : ℝ, 0 < s ∧ s ∈ verticalE f x e₁ := by
  have hri : x + (0 : ℝ) • e₁ ∈ stripInterior := by simpa using hx
  have hU0' : dN f (x + (0 : ℝ) • e₁) ≠ 0 := by simpa using hU0
  have hev := eventually_dN_ne_zero_ray hf hri hU0'
  rcases Metric.eventually_nhds_iff_ball.mp hev with ⟨δ0, hδ0, hδ0'⟩
  rcases kernel_segment_start hf hx hU0 hk0 he₁ with ⟨ε₀, hε₀, hseg₀⟩
  let s₁ : ℝ := min (δ0 / 2) (ε₀ / 2)
  have hs₁0 : 0 < s₁ := by
    dsimp [s₁]
    positivity
  refine ⟨s₁, hs₁0, ?_⟩
  refine ⟨le_of_lt hs₁0, ?_⟩
  intro r hr
  rw [Set.mem_Icc] at hr
  have hseg := hseg₀ r (by
    rw [Set.mem_Icc]
    have hrs : r ≤ s₁ := hr.2
    have h₁ : s₁ ≤ ε₀ / 2 := min_le_right _ _
    constructor <;> linarith)
  have hdN : dN f (x + r • e₁) ≠ 0 := by
    have hrs : r ≤ s₁ := hr.2
    have h₁ : s₁ ≤ δ0 / 2 := min_le_left _ _
    have h₂ : r ≤ δ0 / 2 := le_trans hrs h₁
    have hr0 : 0 ≤ r := hr.1
    have hrδ : |r| < δ0 := by
      rw [abs_of_nonneg hr0]
      exact lt_of_le_of_lt h₂ (half_lt_self hδ0)
    have hb : r ∈ Metric.ball (0 : ℝ) δ0 := by
      simpa [Real.dist_eq] using hrδ
    exact hδ0' r hb
  exact ⟨hseg.1, hdN, hseg.2⟩

/-- **Positivity of the supremum of `verticalE`**: whenever the set is
bounded above (so the supremum is a real number), it is strictly positive,
because `verticalE` already contains a positive element. -/
lemma sSup_verticalE_pos {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x e₁ : ℝ²} (hx : x ∈ stripInterior) (hU0 : dN f x ≠ 0)
    (hk0 : dN f x e₁ = 0) (he₁ : e₁ ≠ 0)
    (hbdd : BddAbove (verticalE f x e₁)) : 0 < sSup (verticalE f x e₁) := by
  rcases verticalE_positive hf hx hU0 hk0 he₁ with ⟨s₁, hs₁0, hs₁E⟩
  have hle : s₁ ≤ sSup (verticalE f x e₁) := le_csSup hbdd hs₁E
  linarith




/-- **Downward closure of `verticalE`**: if `s ∈ verticalE` and `0 ≤ t ≤ s`
then `t ∈ verticalE` (all three conditions are universal over the interval,
and `[0,t] ⊆ [0,s]`). -/
lemma verticalE_downclosed {f : ℝ² → ℝ³} {x e₁ : ℝ²} {s t : ℝ}
    (hs : s ∈ verticalE f x e₁) (ht0 : 0 ≤ t) (hts : t ≤ s) :
    t ∈ verticalE f x e₁ := by
  rw [verticalE] at hs ⊢
  rcases hs with ⟨hs0, hcond⟩
  refine ⟨ht0, ?_⟩
  intro r hr
  rcases Set.mem_Icc.mp hr with ⟨hr0, hrt⟩
  have hri : r ∈ Set.Icc 0 s := by
    rw [Set.mem_Icc]
    constructor <;> linarith
  exact hcond r hri




/-- **Density of `verticalE` below its supremum**: every `s` with
`0 ≤ s < sSup E` lies in `E`.  (`s` is not an upper bound of `E`, so some
`q ∈ E` sits above `s`; then downward closure `verticalE_downclosed` gives
`s ∈ E`.) -/
lemma verticalE_density {f : ℝ² → ℝ³} {x e₁ : ℝ²}
    (hEne : (verticalE f x e₁).Nonempty)
    (hbdd : BddAbove (verticalE f x e₁))
    {s : ℝ} (hs0 : 0 ≤ s) (hsβ : s < sSup (verticalE f x e₁)) :
    s ∈ verticalE f x e₁ := by
  have hsup' : ∃ q : ℝ, q ∈ verticalE f x e₁ ∧ s < q := by
    by_contra h
    have hupper : sSup (verticalE f x e₁) ≤ s := csSup_le hEne (by
      intro q hq
      by_contra hle
      exact h ⟨q, hq, lt_of_not_ge hle⟩)
    linarith
  rcases hsup' with ⟨q, hq, hsq⟩
  exact verticalE_downclosed hq hs0 (le_of_lt hsq)




/-- **The maximal vertical kernel-`U`-ray through `x`**: if `x ∈ U` and
`e₁ = !₂[0,1]` is a kernel direction at `x`, then on the whole forward
vertical ray `P(t) = x + t•e₁` (`t ≥ 0`) the points stay in the strip
interior, in `U`, with `e₁` a kernel direction. -/
theorem vertical_kernel_ray_U {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x : ℝ²} (hx : x ∈ stripInterior) (hU0 : dN f x ≠ 0) (hk0 : dN f x !₂[0,1] = 0) :
    ∀ t : ℝ, 0 ≤ t →
      x + t • !₂[0, 1] ∈ stripInterior ∧ dN f (x + t • !₂[0, 1]) ≠ 0 ∧
        dN f (x + t • !₂[0, 1]) !₂[0, 1] = 0 := by
  let e₁ : ℝ² := !₂[0, 1]
  have he₁ : e₁ ≠ 0 := by
    intro hz
    have hz1 : (e₁ 1) = 0 := by rw [hz]; rfl
    simpa [e₁] using hz1
  have he₁0 : e₁ 0 = 0 := by simp [e₁]
  have hk0' : dN f x e₁ = 0 := by simpa [e₁] using hk0
  have hE0 : (0 : ℝ) ∈ verticalE f x e₁ := verticalE_zero_mem hx hU0 hk0'
  have hEne : (verticalE f x e₁).Nonempty := ⟨0, hE0⟩
  -- cofinality: every t ≥ 0 is below some element of E
  have hcofinal : ∀ t : ℝ, 0 ≤ t → ∃ q : ℝ, q ∈ verticalE f x e₁ ∧ t ≤ q := by
    intro t ht0
    by_contra hz
    have hbdd : BddAbove (verticalE f x e₁) := by
      refine ⟨t, ?_⟩
      intro q hq
      by_contra hle
      exact hz ⟨q, hq, le_of_lt (lt_of_not_ge hle)⟩
    let β : ℝ := sSup (verticalE f x e₁)
    have hβpos : 0 < β := sSup_verticalE_pos hf hx hU0 hk0' he₁ hbdd
    let p : ℝ² := x + β • e₁
    have hpI : p ∈ stripInterior := by
      dsimp [p]
      exact vertical_mem_stripInterior hx e₁ he₁0 β
    have hdens : ∀ u ∈ Set.Ioo (0 : ℝ) β, u ∈ verticalE f x e₁ := by
      intro u hu
      exact verticalE_density hEne hbdd (le_of_lt hu.1) hu.2
    by_cases hdNp : dN f p ≠ 0
    · -- extend the kernel segment past the sup
      have hkerp : dN f p e₁ = 0 := by
        have hφ : ∀ r ∈ Set.Ioo (0 : ℝ) β, dN f (x + r • e₁) e₁ = 0 := by
          intro r hr
          have hr0 : 0 < r := (Set.mem_Ioo.mp hr).1
          have hrE := hdens r hr
          exact (hrE.2 r (by rw [Set.mem_Icc]; exact ⟨le_of_lt hr0, le_rfl⟩)).2.2
        dsimp [p]
        exact kernel_e1_at_ray_endpoint hf hx hβpos (by simpa [e₁] using hφ)
      have hsegβ : ∀ r ∈ Set.Icc 0 β,
          x + r • e₁ ∈ stripInterior ∧ dN f (x + r • e₁) e₁ = 0 := by
        intro r hr
        rw [Set.mem_Icc] at hr
        by_cases hrβ : r < β
        · by_cases hrz : r = 0
          · subst r
            exact ⟨by simpa using hx, by simpa using hk0'⟩
          · have hr0 : 0 < r := lt_of_le_of_ne hr.1 (by intro hz; exact hrz hz.symm)
            have hrE := hdens r ⟨hr0, hrβ⟩
            have hmem : r ∈ Set.Icc 0 r := by
              rw [Set.mem_Icc]
              exact ⟨le_of_lt hr0, le_rfl⟩
            exact ⟨(hrE.2 r hmem).1, (hrE.2 r hmem).2.2⟩
        · have hrβ' : r = β := by
            have h₁ : β ≤ r := le_of_not_gt hrβ
            exact le_antisymm hr.2 h₁
          subst r
          exact ⟨hpI, hkerp⟩
      have hext := kernel_segment_extend_right hf (x₀ := x) (w₀ := e₁) (ε := β)
        he₁ (le_of_lt hβpos) hsegβ (by simpa [p] using hdNp)
      rcases hext with ⟨ε', hε'β, hseg'⟩
      -- dN ≠ 0 on a neighbourhood of β along the ray
      have hmem : {r : ℝ | dN f (x + r • e₁) ≠ 0} ∈ 𝓝 β :=
        eventually_dN_ne_zero_ray hf hpI (by simpa [p] using hdNp)
      rcases Metric.eventually_nhds_iff_ball.mp hmem with ⟨δ, hδ, hδ'⟩
      let s₂ : ℝ := β + min ((ε' - β) / 2) (δ / 4)
      have hs₂β : β < s₂ := by
        dsimp [s₂]
        have hm : 0 < min ((ε' - β) / 2) (δ / 4) := lt_min (by positivity) (by positivity)
        nlinarith
      have hs₂ε' : s₂ < ε' := by
        dsimp [s₂]
        have h₁ : min ((ε' - β) / 2) (δ / 4) ≤ (ε' - β) / 2 := min_le_left _ _
        have h₂ : β + (ε' - β) / 2 < ε' := by
          have hε : ε' - β > 0 := by linarith
          nlinarith
        nlinarith
      have hs₂E : s₂ ∈ verticalE f x e₁ := by
        refine ⟨by dsimp [s₂]; positivity, ?_⟩
        intro r hr
        rw [Set.mem_Icc] at hr
        have hrs₂ : r ≤ s₂ := hr.2
        have hseg := hseg' r (by
          rw [Set.mem_Icc]
          have hrs : r ≤ s₂ := hr.2
          constructor <;> linarith)
        have hdN : dN f (x + r • e₁) ≠ 0 := by
          by_cases hrβ : r ≤ β
          · by_cases hrz : r = 0
            · subst r
              simpa using hU0
            · by_cases hreq : r = β
              · subst r
                simpa [p] using hdNp
              · have hr0 : 0 < r := lt_of_le_of_ne hr.1 (by intro hz; exact hrz hz.symm)
                have hrβ' : r < β := lt_of_le_of_ne hrβ hreq
                have hri : r ∈ Set.Icc 0 r := by
                  rw [Set.mem_Icc]
                  exact ⟨le_of_lt hr0, le_rfl⟩
                have hrE := hdens r ⟨hr0, hrβ'⟩
                exact (hrE.2 r hri).2.1
          · have hβr : β < r := lt_of_not_ge hrβ
            have hrm : r - β ≤ min ((ε' - β) / 2) (δ / 4) := by
              dsimp [s₂] at hrs₂
              nlinarith
            have h₁ : r - β ≤ δ / 4 := le_trans hrm (min_le_right _ _)
            have h₂ : 0 ≤ r - β := by linarith
            have hb : r ∈ Metric.ball β δ := by
              rw [Metric.mem_ball, Real.dist_eq]
              have hd : |r - β| < δ := by
                rw [abs_of_nonneg h₂]
                exact lt_of_le_of_lt h₁ (by linarith)
              simpa using hd
            exact hδ' r hb
        exact ⟨hseg.1, hdN, hseg.2⟩
      have hle : s₂ ≤ sSup (verticalE f x e₁) := le_csSup hbdd hs₂E
      have hleβ : s₂ ≤ β := by simpa [β] using hle
      linarith
    · exfalso
      -- flat at p: flat_stop_impossible with direction −e₁ and arc u ↦ P(β−u)
      have hflat0 : dN f p = 0 := not_ne_iff.mp hdNp
      have hW' : -e₁ ≠ 0 := by
        intro hz
        exact he₁ (neg_eq_zero.mp hz)
      have harc : ∃ η : ℝ, 0 < η ∧ ∀ u ∈ Set.Ioo (0 : ℝ) η,
          p + u • (-e₁) ∈ stripInterior ∧ dN f (p + u • (-e₁)) ≠ 0 ∧
            dN f (p + u • (-e₁)) (-e₁) = 0 := by
        refine ⟨β / 2, half_pos hβpos, ?_⟩
        intro u hu
        rcases Set.mem_Ioo.mp hu with ⟨hu0, huβ⟩
        have huβ' : u < β / 2 := huβ
        let s' : ℝ := β - u
        have hs'I : s' ∈ Set.Ioo (0 : ℝ) β := by
          rw [Set.mem_Ioo]
          dsimp [s']
          constructor <;> linarith
        have hs'E : s' ∈ verticalE f x e₁ := hdens s' hs'I
        have hseg' : x + s' • e₁ ∈ stripInterior ∧ dN f (x + s' • e₁) ≠ 0 ∧ dN f (x + s' • e₁) e₁ = 0 :=
          hs'E.2 s' (by rw [Set.mem_Icc]; constructor <;> linarith)
        have hpt : p + u • (-e₁) = x + s' • e₁ := by
          dsimp [p, s']
          rw [sub_smul, smul_neg]
          abel
        have hmem : p + u • (-e₁) ∈ stripInterior := by
          rw [hpt]
          exact hseg'.1
        have hker : dN f (p + u • (-e₁)) (-e₁) = 0 := by
          rw [hpt]
          rw [map_neg, hseg'.2.2]
          simp
        have hnz : dN f (p + u • (-e₁)) ≠ 0 := by
          rw [hpt]
          exact hseg'.2.1
        exact ⟨hmem, hnz, hker⟩
      exact flat_stop_impossible hf hpI hW' hflat0 harc
  -- conclusion: for t ≥ 0 use cofinality and downward closure
  intro t ht0
  rcases hcofinal t ht0 with ⟨q, hq, htq⟩
  have htE : t ∈ verticalE f x e₁ := verticalE_downclosed hq ht0 htq
  change x + t • !₂[0, 1] ∈ stripInterior ∧ dN f (x + t • !₂[0, 1]) ≠ 0 ∧
    dN f (x + t • !₂[0, 1]) !₂[0, 1] = 0
  rw [show !₂[0, 1] = e₁ by simp [e₁]]
  exact htE.2 t (by rw [Set.mem_Icc]; constructor <;> linarith)




/-- **No vertical kernel directions in `U`**: at an interior point of the
band where the shape operator is nonzero, the vertical direction `e₁` is not
a kernel direction.  If it were, the forward vertical ray would be a kernel
segment all the way (Lemma `vertical_kernel_ray_U`), `f` would be affine
along it with unit slope (`affine_on_kernel_segment`, `tangent₁` unit), so
the image would contain an unbounded straight segment — contradicting the
boundedness of the image of the strip (`f_strip_bounded`). -/
theorem vertical_kernel_impossible {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hU0 : dN f x ≠ 0) :
    dN f x !₂[0, 1] ≠ 0 := by
  intro hk0
  -- boundedness of the image of the strip
  rcases f_strip_bounded hf ha with ⟨R, hR⟩
  have hxU : x ∈ unitStrip := stripInterior_subset_unitStrip hx
  have hRx : ‖f x‖ ≤ R := hR x hxU
  have hR0 : 0 ≤ R := by
    have hn : 0 ≤ ‖f x‖ := norm_nonneg _
    linarith
  let t : ℝ := R + ‖f x‖ + 1
  have ht0 : 0 ≤ t := by
    dsimp [t]
    positivity
  -- the whole segment [0,t] in direction e₁ is a kernel segment in U
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) t,
      x + s • (!₂[0, 1] : ℝ²) ∈ stripInterior := by
    intro s hs
    exact (vertical_kernel_ray_U hf hx hU0 hk0 s (Set.mem_Icc.mp hs).1).1
  have hk : ∀ s ∈ Set.Icc (0 : ℝ) t,
      dN f (x + s • (!₂[0, 1] : ℝ²)) (!₂[0, 1]) = 0 := by
    intro s hs
    exact (vertical_kernel_ray_U hf hx hU0 hk0 s (Set.mem_Icc.mp hs).1).2.2
  -- affine image along the segment
  let c₀ : ℝ³ := fderiv ℝ f x (!₂[0, 1] : ℝ²)
  have hlin : f (x + t • (!₂[0, 1] : ℝ²)) = f x + t • c₀ := by
    have hmain := affine_on_kernel_segment hf (x := x) (v := (!₂[0, 1] : ℝ²))
      (A := (0 : ℝ)) (B := t) hseg hk t (by
        rw [Set.mem_Icc]
        exact ⟨ht0, le_rfl⟩)
    dsimp [c₀]
    simpa using hmain
  have hc₀ : ‖c₀‖ = 1 := by
    dsimp [c₀]
    rw [← tangent₁_eq_fderiv hx]
    exact tangent₁_norm hf x hxU
  -- P(t) ∈ unitStrip with small image norm
  have hPt : x + t • (!₂[0, 1] : ℝ²) ∈ stripInterior :=
    (vertical_kernel_ray_U hf hx hU0 hk0 t ht0).1
  have hPtU : x + t • (!₂[0, 1] : ℝ²) ∈ unitStrip := stripInterior_subset_unitStrip hPt
  have hb : ‖f (x + t • (!₂[0, 1] : ℝ²))‖ ≤ R := hR _ hPtU
  -- lower bound ‖f(P t)‖ ≥ t − ‖f x‖
  have hnorm_t : ‖t • c₀‖ = t := by
    rw [norm_smul, hc₀]
    rw [Real.norm_eq_abs, abs_of_nonneg ht0]
    simp
  have htri : ‖t • c₀‖ ≤ ‖f x + t • c₀‖ + ‖f x‖ := by
    have hnt := norm_sub_le (a := f x + t • c₀) (b := f x)
    have hnorms : (f x + t • c₀) - f x = t • c₀ := by abel
    simpa [hnorms] using hnt
  have hlb : t - ‖f x‖ ≤ ‖f (x + t • (!₂[0, 1] : ℝ²))‖ := by
    rw [hlin]
    nlinarith [hnorm_t, htri]
  have hbig : R < ‖f (x + t • (!₂[0, 1] : ℝ²))‖ := by
    have h₁ : R + 1 ≤ ‖f (x + t • (!₂[0, 1] : ℝ²))‖ := by
      have h₂ : (R + ‖f x‖ + 1) - ‖f x‖ ≤ ‖f (x + t • (!₂[0, 1] : ℝ²))‖ := by
        simpa [t] using hlb
      calc
        R + 1 = (R + ‖f x‖ + 1) - ‖f x‖ := by ring
        _ ≤ ‖f (x + t • (!₂[0, 1] : ℝ²))‖ := h₂
    linarith
  linarith

/-- **Crossing kernel directions in `U`**: at an interior point of the band
with `dN ≠ 0`, there is a nonzero kernel direction `w` whose first coordinate
is nonzero — i.e. the bend direction is never vertical, so it crosses the
strip (reaching both boundary lines). -/
theorem exists_crossing_kernel_direction {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hU0 : dN f x ≠ 0) :
    ∃ w : ℝ², dN f x w = 0 ∧ w ≠ 0 ∧ w 0 ≠ 0 := by
  rcases bendDir_is_line hf x hx hU0 with ⟨v, hvne, hspan⟩
  have hvker : dN f x v = 0 := by
    have hvB : v ∈ bendDir f x := by
      rw [hspan]
      exact Submodule.subset_span (by simp : v ∈ ({v} : Set ℝ²))
    exact mem_bendDir_iff.mp hvB
  refine ⟨v, hvker, hvne, ?_⟩
  intro hv0
  -- v is vertical, hence a scalar multiple of e₁
  have hv1 : v 1 ≠ 0 := by
    intro hz1
    apply hvne
    ext i; fin_cases i
    · simpa using hv0
    · simpa using hz1
  have hvlin : v = (v 1) • (!₂[0, 1] : ℝ²) := by
    ext i <;> fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, hv0] <;> ring
  have hback : (v 1)⁻¹ • v = (!₂[0, 1] : ℝ²) := by
    rw [hvlin, smul_smul]
    simp [inv_mul_cancel₀ hv1]
  have hke₁ : dN f x (!₂[0, 1]) = 0 := by
    have hk' : dN f x ((v 1)⁻¹ • v) = 0 := by
      rw [map_smul, hvker, smul_zero]
    rwa [hback] at hk'
  exact vertical_kernel_impossible hf ha hx hU0 hke₁

end Submission.PaperBand
