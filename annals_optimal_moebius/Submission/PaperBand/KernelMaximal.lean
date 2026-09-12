import Submission.PaperBand.KernelSegments
import Submission.PaperBand.FlatBends

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Maximal kernel segments along a ray (Lemma `mc`, continuation part)

`KernelSegments.kernel_segment_extend_right/left` extend a kernel segment
through points of `U = {dN ≠ 0}`.  Iterating that extension along a ray
`{x₀ + s • w₀ | s ≥ 0}` (with `w₀` a kernel direction whose first coordinate
is nonzero, so the ray actually crosses the strip and hits the boundary
`x0 ∈ {0,1}`), the kernel condition holds up to a *maximal* parameter `β`,
and at `β` the ray has reached the boundary of the strip, or the point is a
*flat* point that is not in the interior of a flat region
(`kernel_segment_reaches_boundary_or_flat_boundary`: `dN = 0` there but no
open neighbourhood is flat, so the segment really stops — it cannot continue
straight through the interior of a flat region, by
`FlatBends.kernel_segment_extend_into_flat`).  This is the formal content of
the "more work shows that γ continues in either direction until reaching
∂Ω" part of Lemma `mc` (paper §2.1), restricted to the set `U` (the flat
trapezoids themselves are handled in Proposition `main0`).

The proof is one-dimensional: with `E` the set of parameters `s ≥ 0` over
which the ray is a kernel segment, `E` is nonempty (by the local bend),
downward-closed and bounded above by the boundary-crossing parameter `s₀`;
at `β = sSup E < s₀` the kernel condition holds by continuity (the shape
operator is `C∞` on the interior), so `β ∈ E` (the closed segment is a
kernel segment), and if the endpoint were in `U` then
`kernel_segment_extend_right` would extend it further, while if it were in
the interior of a flat region then `kernel_segment_extend_into_flat` would —
contradicting the maximality of `β` in either case.
-/

noncomputable section
namespace Submission.PaperBand

/-- The parameter `s ≥ 0` at which the ray `{x₀ + s • w₀}` (for a direction
`w₀` with nonzero `0`-coordinate) reaches the boundary of the strip: the
coordinate `x0` becomes `1` when the ray points right and `0` when it points
left. -/
def rayStopParam (x₀ w₀ : ℝ²) : ℝ :=
  (if 0 < w₀ 0 then (1 - x₀ 0) else -x₀ 0) / w₀ 0

/-- The `0`-coordinate of an affine point on the ray. -/
lemma ray_coord0 (x w : ℝ²) (s : ℝ) : (x + s • w) 0 = x 0 + s * w 0 := by
  simp

/-- A point of the ray lies in the interior of the strip iff its `0`-coordinate
is strictly between 0 and 1. -/
lemma mem_stripInterior_ray_iff (x w : ℝ²) (s : ℝ) :
    x + s • w ∈ stripInterior ↔ 0 < x 0 + s * w 0 ∧ x 0 + s * w 0 < 1 := by
  rw [stripInterior]
  simp [ray_coord0]

/-- The parameter of the boundary crossing is positive for an interior
starting point and a direction crossing the strip. -/
lemma rayStopParam_pos {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hw0 : w₀ 0 ≠ 0) :
    0 < rayStopParam x₀ w₀ := by
  have hx0 : 0 < x₀ 0 := by
    rw [stripInterior] at hx₀
    exact hx₀.1
  have hx1 : x₀ 0 < 1 := by
    rw [stripInterior] at hx₀
    exact hx₀.2
  by_cases hpos : 0 < w₀ 0
  · dsimp [rayStopParam]
    rw [if_pos hpos]
    rw [div_pos_iff]
    exact Or.inl ⟨by linarith, hpos⟩
  · have hneg : w₀ 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (by
      intro hz
      exact hw0 hz)
    dsimp [rayStopParam]
    rw [if_neg hpos]
    rw [div_pos_iff]
    exact Or.inr ⟨by linarith, hneg⟩

/-- At the stopping parameter the ray is on the boundary of the strip:
its `0`-coordinate is `1` if the direction points right and `0` if left. -/
lemma rayStopParam_coord {x₀ w₀ : ℝ²} (hw0 : w₀ 0 ≠ 0) :
    (x₀ + rayStopParam x₀ w₀ • w₀) 0 = if 0 < w₀ 0 then 1 else 0 := by
  by_cases hpos : 0 < w₀ 0
  · have hb : rayStopParam x₀ w₀ = (1 - x₀ 0) / w₀ 0 := by
      dsimp [rayStopParam]
      rw [if_pos hpos]
    rw [ray_coord0, hb]
    field_simp [ne_of_gt hpos]
    simp [hpos]
  · have hneg : w₀ 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (by
      intro hz
      exact hw0 hz)
    have hb : rayStopParam x₀ w₀ = (-x₀ 0) / w₀ 0 := by
      dsimp [rayStopParam]
      rw [if_neg hpos]
    rw [ray_coord0, hb]
    field_simp [ne_of_lt hneg]
    simp [hpos]

/-- A ray starting inside the strip and crossing the strip (direction with
nonzero `0`-coordinate) lies in the interior of the strip on the parameter
interval `0 ≤ s < rayStopParam`. -/
lemma ray_interior_iff {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hw0 : w₀ 0 ≠ 0) :
    ∀ s : ℝ, 0 ≤ s →
      (x₀ + s • w₀ ∈ stripInterior ↔ s < rayStopParam x₀ w₀) := by
  intro s hs0
  have hx0 : 0 < x₀ 0 := by
    rw [stripInterior] at hx₀
    exact hx₀.1
  have hx1 : x₀ 0 < 1 := by
    rw [stripInterior] at hx₀
    exact hx₀.2
  by_cases hpos : 0 < w₀ 0
  · have hb : rayStopParam x₀ w₀ = (1 - x₀ 0) / w₀ 0 := by
      dsimp [rayStopParam]
      rw [if_pos hpos]
    rw [mem_stripInterior_ray_iff, hb]
    constructor
    · rintro ⟨hlo, hhi⟩
      rw [lt_div_iff₀ hpos]
      nlinarith
    · intro hs
      rw [lt_div_iff₀ hpos] at hs
      constructor
      · nlinarith
      · nlinarith
  · have hneg : w₀ 0 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (by
      intro hz
      exact hw0 hz)
    have hb : rayStopParam x₀ w₀ = (-x₀ 0) / w₀ 0 := by
      dsimp [rayStopParam]
      rw [if_neg hpos]
    rw [mem_stripInterior_ray_iff, hb]
    constructor
    · rintro ⟨hlo, hhi⟩
      rw [lt_div_iff_of_neg hneg]
      nlinarith
    · intro hs
      rw [lt_div_iff_of_neg hneg] at hs
      constructor
      · nlinarith
      · nlinarith

/-- **Local start in a prescribed kernel direction**: a nonzero kernel
direction at an interior point of `U` is locally a kernel-segment direction:
a whole initial segment `[0, ε]` of the ray `{x₀ + s • w₀ | s ≥ 0}` is a
kernel segment. -/
lemma kernel_segment_start {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hdN₀ : dN f x₀ ≠ 0)
    (hker₀ : dN f x₀ w₀ = 0) (hw₀ : w₀ ≠ 0) :
    ∃ ε > (0 : ℝ), ∀ s ∈ Set.Icc 0 ε,
      x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0 := by
  rcases bend_segment_of_dN_ne_zero hf hx₀ hdN₀ with ⟨w₁, hw₁n, ρ, hρ, h1, _h2, _h3⟩
  have hker_w₁ : dN f x₀ w₁ = 0 := by
    have hb := (h1 0 (by rw [Set.mem_Icc]; constructor <;> linarith [hρ])).2
    simpa using hb
  rcases kernel_direction_parallel hf hx₀ hdN₀ hker₀ hker_w₁ hw₀ with ⟨c, hc⟩
  have hc_ne : c ≠ 0 := by
    intro hz
    apply hw₁n
    rw [hc, hz]
    simp
  let δ : ℝ := ρ * |c|
  have hδ : 0 < δ := mul_pos hρ (abs_pos.mpr hc_ne)
  let ε : ℝ := δ / 2
  have hε : 0 < ε := by
    dsimp [ε, δ]
    positivity
  have h1' : ∀ t ∈ Set.Icc (-ρ) ρ,
      (x₀ + (0 : ℝ) • w₀) + t • w₁ ∈ stripInterior ∧
        dN f ((x₀ + (0 : ℝ) • w₀) + t • w₁) w₁ = 0 := by
    intro t ht
    have hb := h1 t ht
    simpa [zero_smul] using hb
  have hwin := local_bend_reparam hf (x₀ := x₀) (w₀ := w₀) (w₁ := w₁) (c := c)
    (ε := 0) (ρ := ρ) hρ hc hc_ne h1'
  refine ⟨ε, hε, ?_⟩
  intro s hs
  have hsIn : s ∈ Set.Icc (0 - δ) (0 + δ) := by
    rw [Set.mem_Icc]
    rcases Set.mem_Icc.mp hs with ⟨hs0, hsε⟩
    have hsδ : s ≤ δ / 2 := by simpa [ε] using hsε
    constructor <;> linarith [hδ, hsδ]
  exact hwin s hsIn


/-- The shape operator applied to a fixed vector is continuous along an
affine ray through an interior point of the strip. -/
lemma continuousAt_dN_ray {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} {r₀ : ℝ} (hy : x₀ + r₀ • w₀ ∈ stripInterior) :
    ContinuousAt (fun r : ℝ => (dN f (x₀ + r • w₀)) w₀) r₀ := by
  have hcontDN : ContinuousAt (fun z : ℝ² => dN f z) (x₀ + r₀ • w₀) :=
    ContinuousOn.continuousAt (ContDiffOn.continuousOn (contDiffOn_dN hf))
      (IsOpen.mem_nhds stripInterior_isOpen hy)
  have haff : ContinuousAt (fun r : ℝ => x₀ + r • w₀) r₀ := by fun_prop
  have hDW : ContinuousAt (fun z : ℝ² => (dN f z) w₀) (x₀ + r₀ • w₀) :=
    ContinuousAt.clm_apply (f := fun z : ℝ² => dN f z) (g := fun _ : ℝ² => w₀)
      hcontDN continuousAt_const
  exact ContinuousAt.comp (f := fun r : ℝ => x₀ + r • w₀)
    (g := fun z : ℝ² => (dN f z) w₀) (x := r₀) hDW haff

/-- **A maximal kernel segment along a ray stops at the boundary or at a
flat point.**  Let `x₀` be an interior point of `U = {dN ≠ 0}`, `w₀` a
nonzero kernel direction with nonzero first coordinate (so the ray crosses
the strip), and let `s₀` be the parameter at which the ray reaches the
boundary of the strip.  Then the kernel condition of direction `w₀` holds on
the whole open segment `(0, β)` for a *maximal* `β ∈ (0, s₀]`, and at `β`
the ray has reached the boundary (`x0 = 0` or `x0 = 1`) or the endpoint is a
flat point that is NOT flat-interior and does not have flat points of
`FlatSet` immediately ahead along the segment line:

* `dN f p = 0 ∧ ¬ IsFlatInterior f p` (p on the frontier of the flat set by
  `FlatRegions.mem_frontier_FlatSet_of_flat_not_interior`), and
* `¬ ∃ δ > 0, ∀ s ∈ Ioo 0 δ, x₀ + (β + s)•w₀ ∈ FlatSet f` — the flat region
  does not extend along the bend's own line past the stop (otherwise the
  kernel condition, being automatic on flat points, would extend the segment
  and contradict the maximality);

and moreover the stop is *genuine*: `∀ s > β`, the closed segment `[0, s]`
is not a kernel segment (`sSup`-maximality of `β`). -/
lemma kernel_segment_reaches_boundary_or_flat_boundary {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior)
    (hdN₀ : dN f x₀ ≠ 0) (hker₀ : dN f x₀ w₀ = 0) (hw₀ : w₀ ≠ 0)
    (hw0 : w₀ 0 ≠ 0) :
    let s₀ : ℝ := rayStopParam x₀ w₀
    ∃ β : ℝ, 0 < β ∧ β ≤ s₀ ∧
      (∀ s ∈ Set.Ioo (0 : ℝ) β,
        x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0) ∧
      ((x₀ + β • w₀) 0 = 0 ∨ (x₀ + β • w₀) 0 = 1 ∨
        (dN f (x₀ + β • w₀) = 0 ∧ ¬ IsFlatInterior f (x₀ + β • w₀) ∧
          ¬ (∃ δ > 0, ∀ s ∈ Set.Ioo 0 δ,
            x₀ + (β + s) • w₀ ∈ FlatSet f))) ∧
      (∀ s : ℝ, β < s → ¬ (∀ r ∈ Set.Icc 0 s,
        x₀ + r • w₀ ∈ stripInterior ∧ dN f (x₀ + r • w₀) w₀ = 0)) := by
  intro s₀
  let E : Set ℝ := {s : ℝ | 0 ≤ s ∧ ∀ r ∈ Set.Icc 0 s,
      x₀ + r • w₀ ∈ stripInterior ∧ dN f (x₀ + r • w₀) w₀ = 0}
  have hbdd : ∀ e : ℝ, e ∈ E → e ≤ s₀ := by
    intro e he
    by_contra hz
    have hs₀le : s₀ < e := lt_of_not_ge hz
    have hmem : x₀ + e • w₀ ∈ stripInterior :=
      (he.2 e (by rw [Set.mem_Icc]; exact ⟨he.1, le_rfl⟩)).1
    have hiff := (ray_interior_iff (x₀ := x₀) (w₀ := w₀) hx₀ hw0 e he.1).1 hmem
    linarith
  have hbddE : BddAbove E := ⟨s₀, hbdd⟩
  have hrestrict : ∀ e s : ℝ, e ∈ E → 0 ≤ s → s ≤ e → s ∈ E := by
    intro e s he hs0 hse
    refine ⟨hs0, ?_⟩
    intro r hr
    rcases Set.mem_Icc.mp hr with ⟨hr0, hrs⟩
    have hr' : r ∈ Set.Icc 0 e := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    exact he.2 r hr'
  rcases kernel_segment_start hf hx₀ hdN₀ hker₀ hw₀ with ⟨ε₀, hε₀, hseg₀⟩
  have hEstart : ε₀ ∈ E := by
    refine ⟨le_of_lt hε₀, ?_⟩
    intro r hr
    exact hseg₀ r hr
  have hEne : E.Nonempty := ⟨ε₀, hEstart⟩
  let β : ℝ := sSup E
  have hβpos : 0 < β := by
    dsimp [β]
    exact lt_of_lt_of_le hε₀ (le_csSup hbddE hEstart)
  have hβle : β ≤ s₀ := by
    dsimp [β]
    exact csSup_le hEne hbdd
  have hdensity : ∀ s : ℝ, 0 ≤ s → s < β → s ∈ E := by
    intro s hs0 hsβ
    have hsup' : ∃ s' : ℝ, s' ∈ E ∧ s < s' := by
      by_contra h
      have hupper : sSup E ≤ s := csSup_le hEne (by
        intro s' hs'
        by_contra hle
        exact h ⟨s', hs', lt_of_not_ge hle⟩)
      dsimp [β] at hsβ
      exact (not_lt_of_ge hupper) hsβ
    rcases hsup' with ⟨s', hs', hss'⟩
    exact hrestrict s' s hs' hs0 (le_of_lt hss')
  have hseg_open : ∀ s ∈ Set.Ioo (0 : ℝ) β,
      x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0 := by
    intro s hs
    rcases Set.mem_Ioo.mp hs with ⟨hs0, hsβ⟩
    have hsE : s ∈ E := hdensity s (le_of_lt hs0) hsβ
    exact (hsE.2 s (by rw [Set.mem_Icc]; constructor <;> linarith))
  have hmax : ∀ s : ℝ, β < s → ¬ (∀ r ∈ Set.Icc 0 s,
      x₀ + r • w₀ ∈ stripInterior ∧ dN f (x₀ + r • w₀) w₀ = 0) := by
    intro s hsβ hcond
    have hsE : s ∈ E := by
      refine ⟨le_of_lt (lt_trans hβpos hsβ), ?_⟩
      intro r hr
      exact hcond r hr
    have hsle : s ≤ sSup E := le_csSup hbddE hsE
    dsimp [β] at hsβ
    linarith
  refine ⟨β, hβpos, hβle, hseg_open, ?_, hmax⟩
  by_cases hβs₀ : β = s₀
  · -- reached the boundary
    rw [hβs₀]
    rw [rayStopParam_coord (x₀ := x₀) (w₀ := w₀) hw0]
    by_cases hpos : 0 < w₀ 0
    · simp [hpos]
    · simp [hpos]
  · -- β < s₀ : the point at β is interior; show dN vanishes there
    have hβlt : β < s₀ := lt_of_le_of_ne hβle hβs₀
    have hInt : x₀ + β • w₀ ∈ stripInterior := by
      have hiff := (ray_interior_iff (x₀ := x₀) (w₀ := w₀) hx₀ hw0 β (le_of_lt hβpos)).2
      exact hiff (by exact hβlt)
    have hkerβ : dN f (x₀ + β • w₀) w₀ = 0 := by
      by_contra hk
      have hg : ContinuousAt (fun r : ℝ => (dN f (x₀ + r • w₀)) w₀) β :=
        continuousAt_dN_ray hf hInt
      have hpre : {r : ℝ | (dN f (x₀ + r • w₀)) w₀ ≠ 0} ∈ 𝓝 β :=
        hg.preimage_mem_nhds (isOpen_ne.mem_nhds hk)
      rcases Metric.mem_nhds_iff.mp hpre with ⟨η, hη0, hη⟩
      let η' : ℝ := min η (β / 2)
      have hη'0 : 0 < η' := by
        dsimp [η']
        exact lt_min hη0 (by positivity)
      have hη'η : η' ≤ η := by dsimp [η']; exact min_le_left _ _
      have hη'β2 : η' ≤ β / 2 := by dsimp [η']; exact min_le_right _ _
      have hη'β : η' < β := by
        have : β / 2 < β := by linarith [hβpos]
        exact lt_of_le_of_lt hη'β2 this
      let r : ℝ := β - η' / 2
      have hrpos : 0 < r := by
        dsimp [r]
        have : η' / 2 ≤ β / 2 / 2 := by linarith [hη'β2]
        nlinarith [hβpos]
      have hrb : r < β := by dsimp [r]; linarith
      have hmemE : r ∈ E := hdensity r (le_of_lt hrpos) hrb
      have hker_r : dN f (x₀ + r • w₀) w₀ = 0 :=
        (hmemE.2 r (by rw [Set.mem_Icc]; constructor <;> linarith)).2
      have hrb' : r ∈ Metric.ball β η := by
        rw [Metric.mem_ball]
        rw [Real.dist_eq]
        have hmain : |r - β| ≤ η' / 2 := by
          rw [abs_le]
          constructor <;> dsimp [r] <;> linarith [hη'0]
        have hsmall : η' / 2 < η := by
          have hh : η' / 2 < η' := by linarith [hη'0]
          exact lt_of_lt_of_le hh hη'η
        exact lt_of_le_of_lt hmain hsmall
      have hne : (dN f (x₀ + r • w₀)) w₀ ≠ 0 := hη hrb'
      exact hne hker_r
    have hβE : β ∈ E := by
      refine ⟨le_of_lt hβpos, ?_⟩
      intro r hr
      rcases Set.mem_Icc.mp hr with ⟨hr0, hrβ⟩
      by_cases hrb : r < β
      · exact (hdensity r hr0 hrb).2 r (by rw [Set.mem_Icc]; constructor <;> linarith)
      · have hreq : r = β := le_antisymm hrβ (le_of_not_gt hrb)
        rw [hreq]
        exact ⟨hInt, hkerβ⟩
    by_cases hdNβ : dN f (x₀ + β • w₀) = 0
    · -- flat endpoint: not flat-interior, and the flat set does not extend
      -- along the segment line past the stop (else the kernel condition,
      -- trivial on flat points, would extend the segment — contradicting
      -- the maximality of β)
      right; right
      have hni : ¬ IsFlatInterior f (x₀ + β • w₀) := by
        intro hFI
        rcases hFI with ⟨U, hUo, hUp, hUflat⟩
        let U₁ : Set ℝ² := U ∩ stripInterior
        have hU₁o : IsOpen U₁ := hUo.inter stripInterior_isOpen
        have hU₁p : x₀ + β • w₀ ∈ U₁ := ⟨hUp, hInt⟩
        have hU₁sub : U₁ ⊆ stripInterior := Set.inter_subset_right
        have hU₁flat : ∀ x ∈ U₁, dN f x = 0 := by
          intro x hx
          exact hUflat x hx.1
        rcases kernel_segment_extend_into_flat (x₀ := x₀) (w₀ := w₀) (ε := β) hβE.2
          (U := U₁) hU₁o hU₁p hU₁flat hU₁sub with ⟨ε', hε'β, hseg'⟩
        have hε'E : ε' ∈ E := by
          refine ⟨le_of_lt (lt_trans hβpos hε'β), ?_⟩
          intro r hr
          exact hseg' r hr
        have hε'le : ε' ≤ sSup E := le_csSup hbddE hε'E
        dsimp [β] at hε'β
        linarith
      have hnoahead : ¬ (∃ δ > 0, ∀ s ∈ Set.Ioo 0 δ,
          x₀ + (β + s) • w₀ ∈ FlatSet f) := by
        rintro ⟨δ, hδ0, hflatcont⟩
        let ε' : ℝ := β + δ / 2
        have hε'β : β < ε' := by
          dsimp [ε']
          linarith [hδ0]
        have hε'E : ε' ∈ E := by
          refine ⟨le_of_lt (lt_trans hβpos hε'β), ?_⟩
          intro r hr
          rcases Set.mem_Icc.mp hr with ⟨hr0, hrε'⟩
          by_cases hrb : r < β
          · exact hβE.2 r (by rw [Set.mem_Icc]; constructor <;> linarith)
          · have hrb' : β ≤ r := le_of_not_gt hrb
            by_cases hreq : r = β
            · rw [hreq]
              constructor
              · exact hInt
              · have hk0 : dN f (x₀ + β • w₀) w₀ = 0 := by
                  rw [hdNβ]
                  simp
                exact hk0
            · have hrgt : β < r := lt_of_le_of_ne hrb' (by
                intro hz
                exact hreq hz.symm)
              let s : ℝ := r - β
              have hs0 : 0 < s := by dsimp [s]; linarith
              have hsδ : s < δ := by
                dsimp [s]
                have : r - β ≤ δ / 2 := by
                  dsimp [ε'] at hrε'
                  linarith
                exact lt_of_le_of_lt this (by linarith [hδ0])
              have hf : x₀ + (β + s) • w₀ ∈ FlatSet f := hflatcont s (by
                rw [Set.mem_Ioo]
                exact ⟨hs0, hsδ⟩)
              have hpt : x₀ + r • w₀ = x₀ + (β + s) • w₀ := by
                dsimp [s]
                congr 1
                congr 1
                ring
              constructor
              · rw [hpt]
                exact FlatSet_subset_stripInterior f hf
              · have hd : dN f (x₀ + r • w₀) = 0 := by
                  rw [hpt]
                  exact (mem_FlatSet.mp hf).2
                rw [hd]
                simp
        have hε'le : ε' ≤ sSup E := le_csSup hbddE hε'E
        dsimp [β] at hε'β
        linarith
      exact ⟨hdNβ, hni, hnoahead⟩
    · -- the endpoint is still in U: extend, contradicting maximality of β
      rcases kernel_segment_extend_right hf (x₀ := x₀) (w₀ := w₀) (ε := β) hw₀
        (le_of_lt hβpos) hβE.2 hdNβ with ⟨ε', hε'β, hseg'⟩
      have hε'E : ε' ∈ E := by
        refine ⟨le_of_lt (lt_trans hβpos hε'β), ?_⟩
        intro r hr
        exact hseg' r hr
      have hε'le : ε' ≤ sSup E := le_csSup hbddE hε'E
      dsimp [β] at hε'β
      linarith


/-- Linear algebra: a linear map kills `-w₀` iff it kills `w₀`. -/
lemma map_neg_eq_zero_iff {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    [Module ℝ E] [Module ℝ F] (L : E →ₗ[ℝ] F) (w : E) :
    L (-w) = 0 ↔ L w = 0 := by
  constructor
  · intro h
    have : L w = L (-(-w)) := by rw [neg_neg]
    rw [this, map_neg, h, neg_zero]
  · intro h
    rw [map_neg, h, neg_zero]

/-- Two minus signs cancel in a scalar product. -/
lemma smul_neg_neg {E : Type*} [AddCommGroup E] [Module ℝ E] (s : ℝ) (w : E) :
    (-s) • (-w) = s • w := by
  rw [neg_smul, smul_neg]
  simp

/-- **The maximal kernel line (pre-bend) through an interior point of `U`**:
in a direction `w₀` crossing the strip, the kernel condition of direction
`w₀` holds on a maximal open interval `(α, β) ∋ 0`; at each end the line has
reached the boundary of the strip (`x0 = 0` or `x0 = 1`) or a flat point that
is NOT in the interior of a flat region (`dN = 0 ∧ ¬ IsFlatInterior` — a
genuine stop, on the frontier of the flat set by
`FlatRegions.mem_frontier_FlatSet_of_flat_not_interior`).  No extension of
the kernel segment is possible past either end. -/
lemma kernel_segment_two_sided {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ w₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hdN₀ : dN f x₀ ≠ 0)
    (hker₀ : dN f x₀ w₀ = 0) (hw₀ : w₀ ≠ 0) (hw0 : w₀ 0 ≠ 0) :
    ∃ α β : ℝ, α < 0 ∧ 0 < β ∧
      (∀ s ∈ Set.Ioo α β,
        x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0) ∧
      ((x₀ + α • w₀) 0 = 0 ∨ (x₀ + α • w₀) 0 = 1 ∨
        (dN f (x₀ + α • w₀) = 0 ∧ ¬ IsFlatInterior f (x₀ + α • w₀))) ∧
      ((x₀ + β • w₀) 0 = 0 ∨ (x₀ + β • w₀) 0 = 1 ∨
        (dN f (x₀ + β • w₀) = 0 ∧ ¬ IsFlatInterior f (x₀ + β • w₀))) := by
  have hw₀n : -w₀ ≠ 0 := by
    intro hz
    exact hw₀ (neg_eq_zero.mp hz)
  have hw0n : (-w₀) 0 ≠ 0 := by
    intro hz
    exact hw0 (by simpa using hz)
  have hker₀n : dN f x₀ (-w₀) = 0 := by
    rw [map_neg, hker₀, neg_zero]
  rcases kernel_segment_reaches_boundary_or_flat_boundary hf hx₀ hdN₀ hker₀ hw₀ hw0 with
    ⟨β, hβpos, _hβle, hsegR, hstopR, _hmaxR⟩
  have hstopRp : (x₀ + β • w₀) 0 = 0 ∨ (x₀ + β • w₀) 0 = 1 ∨
      (dN f (x₀ + β • w₀) = 0 ∧ ¬ IsFlatInterior f (x₀ + β • w₀)) := by
    rcases hstopR with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h.1, h.2.1⟩)
  rcases kernel_segment_reaches_boundary_or_flat_boundary hf hx₀ hdN₀ hker₀n hw₀n hw0n with
    ⟨γ, hγpos, _hγle, hsegL', hstopL', _hmaxL⟩
  let α : ℝ := -γ
  have hαneg : α < 0 := by dsimp [α]; linarith
  have hsegL : ∀ s ∈ Set.Ioo α 0,
      x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0 := by
    intro s hs
    rcases Set.mem_Ioo.mp hs with ⟨hαs, hs0⟩
    let s' : ℝ := -s
    have hs' : s' ∈ Set.Ioo (0 : ℝ) γ := by
      dsimp [s']
      rw [Set.mem_Ioo]
      have hαs' : -γ < s := by simpa [α] using hαs
      constructor <;> linarith
    have hb := hsegL' s' hs'
    have hpt : x₀ + s' • (-w₀) = x₀ + s • w₀ := by
      dsimp [s']
      rw [smul_neg_neg]
    constructor
    · have hb1 := hb.1
      rw [hpt] at hb1
      exact hb1
    · have hk := hb.2
      rw [hpt] at hk
      rw [map_neg] at hk
      exact neg_eq_zero.mp hk
  have hstopL : (x₀ + α • w₀) 0 = 0 ∨ (x₀ + α • w₀) 0 = 1 ∨
      (dN f (x₀ + α • w₀) = 0 ∧ ¬ IsFlatInterior f (x₀ + α • w₀)) := by
    have hpt : x₀ + γ • (-w₀) = x₀ + α • w₀ := by
      dsimp [α]
      rw [smul_neg, neg_smul]
    rcases hstopL' with h | h | h
    · left
      rw [hpt] at h
      exact h
    · right; left
      rw [hpt] at h
      exact h
    · right; right
      rw [hpt] at h
      exact ⟨h.1, h.2.1⟩
  refine ⟨α, β, hαneg, hβpos, ?_, hstopL, hstopRp⟩
  intro s hs
  rcases Set.mem_Ioo.mp hs with ⟨hαs, hsβ⟩
  by_cases hs0 : s ≤ 0
  · by_cases hs0eq : s = 0
    · constructor
      · simpa [hs0eq] using hx₀
      · simpa [hs0eq] using hker₀
    · have hsneg : s < 0 := lt_of_le_of_ne hs0 hs0eq
      have hsI : s ∈ Set.Ioo α 0 := by
        rw [Set.mem_Ioo]
        constructor <;> linarith
      exact hsegL s hsI
  · have hs0' : 0 < s := lt_of_not_ge hs0
    have hsI : s ∈ Set.Ioo (0 : ℝ) β := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    exact hsegR s hsI

end Submission.PaperBand
end
