import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Submission.PaperBand.McFlow
import Submission.PaperBand.McStraight

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Kernel fields of the shape operator (generic flow / bend machinery)

Both the kernel vector field `Vf f` (`McStraight`) and its mirror `V2f f`
are smooth sections of the kernel of the shape operator on the strip
interior, and both *straighten*: their directional derivative along
themselves is parallel to themselves wherever they are nonzero
(`McStraight.Vf_deriv_parallel`, `McStraight.V2_deriv_parallel`).

This file bundles exactly those three properties into a structure
`IsKernelField`, proves the local *flow* consequences once, generically in
the field `v` (`field_exists_good_flow`, `field_flow_kernel_straight`,
`field_kernel_segment_around`, `field_bend_segment` — transcribed from the
`Vf`-specific development in `McFlow`), and instantiates them with `Vf f`
and `V2f f`:

* `bend_segment` — through any interior `x₀` with `Vf f x₀ ≠ 0` there is a
  straight pre-bend segment through `x₀` in direction `Vf f x₀`;
* `bend_segment_mirror` — the same for `V2f f`;
* `bend_segment_of_dN_ne_zero` — **every** interior point `x₀` with
  `dN f x₀ ≠ 0` lies in the interior of such a straight pre-bend segment
  (choose the field `Vf` when nonzero and `V2f` otherwise; both vanish only
  when the whole shape matrix — hence `dN` — vanishes, by
  `dN_eq_zero_of_entries_zero`).

That last statement is the local content of Lemma `mc` (§2.1) on the
preimage side.
-/

noncomputable section
namespace Submission.PaperBand

/-- A smooth vector field `v` on the strip interior which is a section of
the kernel of the shape operator and is *straightening*: wherever it is
nonzero its directional derivative along itself is parallel to itself.  The
kernel vector field `Vf f` and its mirror `V2f f` both satisfy these
conditions (see `kernelField_Vf`, `kernelField_V2f` below); their integral
curves are therefore straight kernel segments. -/
structure IsKernelField (f : ℝ² → ℝ³) (v : ℝ² → ℝ²) : Prop where
  contDiffAt : ∀ x : ℝ², x ∈ stripInterior → ContDiffAt ℝ 1 v x
  mem_ker : ∀ x : ℝ², x ∈ stripInterior → dN f x (v x) = 0
  straighten : ∀ x : ℝ², x ∈ stripInterior → v x ≠ 0 →
    ∃ l : ℝ, fderiv ℝ v x (v x) = l • v x

/-- **Generic kernel flow (Picard–Lindelöf)**: a local flow of the kernel
field through an interior point with nonzero field value exists and stays (on
a smaller interval) inside the interior of the strip where the field does not
vanish.  (Same content as `McFlow.exists_good_flow`, generic in the field.) -/
lemma field_exists_good_flow {f : ℝ² → ℝ³} {v : ℝ² → ℝ²} (hv : IsKernelField f v)
    {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hw₀ : v x₀ ≠ 0) :
    ∃ α : ℝ → ℝ², α 0 = x₀ ∧ ∃ ε > 0,
      (∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt α (v (α t)) t) ∧
      (∀ t ∈ Set.Ioo (-ε) ε, α t ∈ stripInterior ∧ v (α t) ≠ 0) := by
  rcases ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
    (f := v) (hv.contDiffAt x₀ hx₀) 0 with ⟨α, hα0, ε₁, hε₁, hα⟩
  have hα0mem : α 0 ∈ stripInterior := by simpa [hα0] using hx₀
  have hαcont0 : ContinuousAt α 0 := (hα 0 (by constructor <;> linarith [hε₁])).continuousAt
  have hU : {t : ℝ | α t ∈ stripInterior} ∈ 𝓝 (0 : ℝ) :=
    hαcont0.preimage_mem_nhds (IsOpen.mem_nhds stripInterior_isOpen hα0mem)
  have hV : {t : ℝ | v (α t) ≠ 0} ∈ 𝓝 (0 : ℝ) := by
    have hcontV0 : ContinuousAt (fun t : ℝ => v (α t)) 0 :=
      ((hv.contDiffAt (α 0) hα0mem).continuousAt).comp hαcont0
    have hw₀' : v (α 0) ≠ 0 := by simpa [hα0] using hw₀
    exact hcontV0.preimage_mem_nhds (isOpen_ne.mem_nhds hw₀')
  rcases Metric.mem_nhds_iff.mp hU with ⟨η₁, hη₁0, hη₁⟩
  rcases Metric.mem_nhds_iff.mp hV with ⟨η₂, hη₂0, hη₂⟩
  let η : ℝ := min η₁ η₂
  have hη0 : 0 < η := by dsimp [η]; exact lt_min hη₁0 hη₂0
  have hη₁' : η ≤ η₁ := by dsimp [η]; exact min_le_left _ _
  have hη₂' : η ≤ η₂ := by dsimp [η]; exact min_le_right _ _
  let ε : ℝ := min (ε₁ / 2) (η / 2)
  have hε0 : 0 < ε := by dsimp [ε]; exact lt_min (by positivity) (by positivity)
  have hεη : ε < η := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_right _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hη0])
  have hε₁' : ε < ε₁ := by
    dsimp [ε]
    exact lt_of_le_of_lt (min_le_left _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hε₁])
  refine ⟨α, hα0, ε, hε0, ?_, ?_⟩
  · intro t ht
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    have htε₁ : t ∈ Set.Ioo (-ε₁) ε₁ := by
      rw [Set.mem_Ioo]
      constructor <;> linarith
    exact hα t (mem_Ioo_symm_zero.mpr htε₁)
  · intro t ht
    have htη' : t ∈ Set.Ioo (-η) η := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
      constructor <;> linarith
    have htη : t ∈ Metric.ball (0 : ℝ) η := mem_ball_zero_iff_Ioo.mpr htη'
    have ht₁ : t ∈ Metric.ball (0 : ℝ) η₁ := by
      rw [Metric.mem_ball] at htη ⊢
      exact htη.trans_le hη₁'
    have ht₂ : t ∈ Metric.ball (0 : ℝ) η₂ := by
      rw [Metric.mem_ball] at htη ⊢
      exact htη.trans_le hη₂'
    exact ⟨by simpa using hη₁ ht₁, by simpa using hη₂ ht₂⟩

/-- **Generic kernel flow is straight**: along the local flow of the kernel
field the field stays parallel to its initial value (so the flow curve is a
straight segment of the flat band), and the initial direction lies in the
kernel of the shape operator at every point of the flow.  (Same content as
`McFlow.flow_kernel_straight`, generic in the field.) -/
lemma field_flow_kernel_straight {f : ℝ² → ℝ³} {v : ℝ² → ℝ²} (hv : IsKernelField f v)
    {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hw₀ : v x₀ ≠ 0) :
    ∃ α : ℝ → ℝ², α 0 = x₀ ∧ ∃ δ > 0,
      ∀ t ∈ Set.Ioo (-δ) δ,
        HasDerivAt α (v (α t)) t ∧ α t ∈ stripInterior ∧
        (∃ c : ℝ, v (α t) = c • v x₀) ∧ dN f (α t) (v x₀) = 0 := by
  let w₀ : ℝ² := v x₀
  rcases field_exists_good_flow hv hx₀ hw₀ with ⟨α, hα0, ε, hε, hα, hgood⟩
  let u : ℝ → ℝ² := fun t => v (α t)
  let u1 : ℝ → ℝ² := fun t => fderiv ℝ v (α t) (v (α t))
  have hu : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt u (u1 t) t := by
    intro t ht
    have hd : DifferentiableAt ℝ v (α t) := (hv.contDiffAt (α t) (hgood t ht).1).differentiableAt_one
    change HasDerivAt (v ∘ α) (fderiv ℝ v (α t) (v (α t))) t
    exact hd.hasFDerivAt.comp_hasDerivAt (x := t) (hα t ht)
  have hpar : ∀ t ∈ Set.Ioo (-ε) ε, ∃ l : ℝ, u1 t = l • u t := by
    intro t ht
    rcases hv.straighten (α t) (hgood t ht).1 (hgood t ht).2 with ⟨l, hl⟩
    refine ⟨l, ?_⟩
    simpa [u, u1] using hl
  have hu0 : u 0 ≠ 0 := by
    simpa [u, hα0] using hw₀
  rcases direction_const_of_parallel (u := u) (u1 := u1) (ε := ε) hε hu hpar hu0 with ⟨δ₀, hδ₀, hdir⟩
  let δ : ℝ := min δ₀ ε
  have hδ0 : 0 < δ := by dsimp [δ]; exact lt_min hδ₀ hε
  have hδle₀ : δ ≤ δ₀ := by dsimp [δ]; exact min_le_left _ _
  have hδleε : δ ≤ ε := by dsimp [δ]; exact min_le_right _ _
  refine ⟨α, hα0, δ, hδ0, ?_⟩
  intro t ht
  have htδ₀ : t ∈ Set.Ioo (-δ₀) δ₀ := by
    rw [Set.mem_Ioo]
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    constructor <;> linarith
  have htε : t ∈ Set.Ioo (-ε) ε := by
    rw [Set.mem_Ioo]
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    constructor <;> linarith
  have hd0 : HasDerivAt α (v (α t)) t := hα t htε
  rcases hdir t htδ₀ with ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    intro hz
    have : u t = 0 := by simpa [hz] using hc
    have : v (α t) = 0 := by simpa [u] using this
    exact (hgood t htε).2 this
  have hu0eq : u 0 = w₀ := by dsimp [u, w₀]; rw [hα0]
  have hparc : u t = c • w₀ := by simpa [hu0eq] using hc
  have hrel : v (α t) = c • w₀ := by simpa [u] using hparc
  have hkernel : dN f (α t) w₀ = 0 := by
    have hker0 : dN f (α t) (v (α t)) = 0 := hv.mem_ker (α t) (hgood t htε).1
    have hmain : dN f (α t) (c • w₀) = 0 := by
      rw [← hrel]
      exact hker0
    rw [map_smul] at hmain
    exact (smul_eq_zero.mp hmain).resolve_left hc0
  refine ⟨hd0, (hgood t htε).1, ⟨c, hrel⟩, hkernel⟩


/-- **Generic local kernel segment**: near an interior point `x₀` with
nonzero kernel field, the whole straight segment `{x₀ + s • w₀}` (with
`w₀ = v x₀`) stays inside the interior of the strip and is a *kernel
segment*: its direction `w₀` is in the kernel of the shape operator at every
point of the segment.  (Same content as `McFlow.kernel_segment_around`,
generic in the field.) -/
lemma field_kernel_segment_around {f : ℝ² → ℝ³} {v : ℝ² → ℝ²} (hv : IsKernelField f v)
    {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hw₀ : v x₀ ≠ 0) :
    ∃ δ > (0 : ℝ),
      (∀ s ∈ Set.Ioo (-δ) δ,
        x₀ + s • (v x₀) ∈ stripInterior ∧
        dN f (x₀ + s • (v x₀)) (v x₀) = 0) := by
  rcases field_flow_kernel_straight hv hx₀ hw₀ with ⟨α, hα0, δf, hδf, hprop⟩
  let u : ℝ → ℝ² := fun t => v (α t)
  have hu' : ∀ t ∈ Set.Ioo (-δf) δf, HasDerivAt α (u t) t := by
    intro t ht
    simpa [u] using (hprop t ht).1
  have hpar : ∀ t ∈ Set.Ioo (-δf) δf, ∃ c : ℝ, u t = c • (v x₀) := by
    intro t ht
    rcases (hprop t ht).2.2.1 with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    change v (α t) = c • (v x₀)
    exact hc
  have hline : ∀ t ∈ Set.Ioo (-δf) δf, ∃ c : ℝ, α t - x₀ = c • (v x₀) :=
    curve_on_line_of_deriv_parallel (γ := α) (u := u) (w₀ := v x₀) (x₀ := x₀)
      (ε := δf) hδf hα0 hu' hpar hw₀
  -- the coordinate function along v x₀ and its derivative
  let φ : ℝ → ℝ := fun s => coord α x₀ (v x₀) s
  have hφder : ∀ t ∈ Set.Ioo (-δf) δf,
      HasDerivAt φ (inner ℝ (u t) (v x₀) / ‖v x₀‖ ^ 2) t := by
    intro t ht
    have hd := hasDerivAt_coord (γ := α) (u := u) (x₀ := x₀) (w₀ := v x₀) (t := t) hw₀
      (hu' t ht)
    simpa [φ] using hd
  have hφeq : ∀ t ∈ Set.Ioo (-δf) δf, α t = x₀ + φ t • (v x₀) := by
    intro t ht
    dsimp [φ]
    exact coord_smul_of_parallel hw₀ (hline t ht)
  have hφ0 : φ 0 = 0 := by
    dsimp [φ, coord]
    rw [hα0]
    simp
  have hw₀nz : ‖v x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hw₀
  have hnorm2 : (0 : ℝ) < ‖v x₀‖ ^ 2 := sq_pos_of_ne_zero hw₀nz
  -- u is differentiable at 0, so G := fun t => inner (u t) (v x₀) is continuous at 0
  have hudiff0 : DifferentiableAt ℝ u 0 := by
    have hmem : α 0 ∈ stripInterior := by simpa [hα0] using hx₀
    have hdV : DifferentiableAt ℝ v (α 0) := (hv.contDiffAt (α 0) hmem).differentiableAt_one
    have hdα : DifferentiableAt ℝ α 0 := (hu' 0 (by constructor <;> linarith [hδf])).differentiableAt
    change DifferentiableAt ℝ (v ∘ α) 0
    exact hdV.comp (x := 0) hdα
  have hGcont0 : ContinuousAt (fun t : ℝ => inner ℝ (u t) (v x₀)) 0 := by
    have hinner : DifferentiableAt ℝ (fun t : ℝ => inner ℝ (u t) (v x₀)) 0 :=
      DifferentiableAt.inner ℝ hudiff0 (differentiableAt_const (v x₀))
    simpa using hinner.continuousAt
  have hG0 : 0 < inner ℝ (u 0) (v x₀) := by
    have hu0w : u 0 = v x₀ := by
      dsimp [u]
      rw [hα0]
    rw [hu0w]
    rw [real_inner_self_eq_norm_sq]
    exact hnorm2
  have hGpos : {t : ℝ | 0 < inner ℝ (u t) (v x₀)} ∈ 𝓝 (0 : ℝ) :=
    hGcont0.preimage_mem_nhds (isOpen_Ioi.mem_nhds hG0)
  rcases Metric.eventually_nhds_iff_ball.mp hGpos with ⟨ηG, hηG0, hηG⟩
  -- pick η with η < δf and G positive on the ball of radius ηG
  let η : ℝ := min (δf / 2) (ηG / 2)
  have hη0 : 0 < η := by dsimp [η]; exact lt_min (by positivity) (by positivity)
  have hηδ : η < δf := by
    dsimp [η]
    exact lt_of_le_of_lt (min_le_left _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hδf])
  have hηηG : η < ηG := by
    dsimp [η]
    exact lt_of_le_of_lt (min_le_right _ _) (by
      rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hηG0])
  -- derivative of φ is positive on (-η, η)
  have hLpos : ∀ t ∈ Set.Ioo (-η) η, 0 < inner ℝ (u t) (v x₀) / ‖v x₀‖ ^ 2 := by
    intro t ht
    rcases Set.mem_Ioo.mp ht with ⟨ht1, ht2⟩
    have htG : t ∈ Metric.ball (0 : ℝ) ηG := mem_ball_zero_iff_Ioo.mpr (by
      rw [Set.mem_Ioo]
      constructor <;> linarith)
    have hpos : 0 < inner ℝ (u t) (v x₀) := hηG t htG
    exact div_pos hpos hnorm2
  have hφcont : ContinuousOn φ (Set.Icc (-η) η) := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-δf) δf := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Icc.mp ht with ⟨ht1, ht2⟩
      constructor <;> linarith
    exact (hφder t ht').continuousAt.continuousWithinAt
  have hderivpos : ∀ t ∈ interior (Set.Icc (-η) η), 0 < deriv φ t := by
    intro t ht
    have ht' : t ∈ Set.Ioo (-η) η := by
      rw [interior_Icc] at ht
      exact ht
    have ht'' : t ∈ Set.Ioo (-δf) δf := by
      rw [Set.mem_Ioo]
      rw [Set.mem_Ioo] at ht'
      constructor <;> linarith
    have hder : deriv φ t = inner ℝ (u t) (v x₀) / ‖v x₀‖ ^ 2 :=
      (hφder t ht'').deriv
    rw [hder]
    exact hLpos t ht'
  have hmono : StrictMonoOn φ (Set.Icc (-η) η) :=
    strictMonoOn_of_deriv_pos (convex_Icc (-η) η) hφcont hderivpos
  have hφneg : φ (-η) < 0 := by
    have hlt : φ (-η) < φ 0 := hmono (a := -η) (b := 0)
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by linarith)
    rwa [hφ0] at hlt
  have hφpos : 0 < φ η := by
    have hlt : φ 0 < φ η := hmono (a := 0) (b := η)
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by rw [Set.mem_Icc]; constructor <;> linarith [hη0])
      (by linarith)
    rwa [hφ0] at hlt
  -- output interval
  let δ : ℝ := min (φ η) (-φ (-η))
  have hδ0 : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith [hφpos]) (by linarith [hφneg])
  refine ⟨δ, hδ0, ?_⟩
  intro s hs
  have hδ1 : δ ≤ φ η := by dsimp [δ]; exact min_le_left _ _
  have hδ2 : δ ≤ -φ (-η) := by dsimp [δ]; exact min_le_right _ _
  have hs1 : s < φ η := lt_of_lt_of_le hs.2 hδ1
  have hs2 : φ (-η) < s := by
    have : -δ < s := hs.1
    exact lt_of_le_of_lt (by linarith) this
  have hmono' : MonotoneOn φ (Set.Icc (-η) η) := hmono.monotoneOn
  have himage : φ '' Set.Icc (-η) η = Set.Icc (φ (-η)) (φ η) :=
    ContinuousOn.image_Icc_of_monotoneOn (le_of_lt (by linarith [hη0])) hφcont hmono'
  have hsI : s ∈ Set.Icc (φ (-η)) (φ η) := by
    rw [Set.mem_Icc]
    constructor <;> linarith
  have hsIn : s ∈ φ '' Set.Icc (-η) η := by
    rw [himage]
    exact hsI
  rcases hsIn with ⟨t, htIcc, hφt⟩
  have ht' : t ∈ Set.Ioo (-δf) δf := by
    rw [Set.mem_Ioo]
    rcases Set.mem_Icc.mp htIcc with ⟨ht1, ht2⟩
    constructor <;> linarith [hηδ]
  have hαt : α t = x₀ + s • (v x₀) := by
    have hφeqt := hφeq t ht'
    rw [hφt] at hφeqt
    exact hφeqt
  have hint : x₀ + s • (v x₀) ∈ stripInterior := by
    rw [← hαt]
    exact (hprop t ht').2.1
  have hker : dN f (x₀ + s • (v x₀)) (v x₀) = 0 := by
    rw [← hαt]
    exact (hprop t ht').2.2.2
  exact ⟨hint, hker⟩


/-- **Generic local bend through an interior point**.  When a straightening
kernel field does not vanish at an interior point `x₀`, the point lies in the
interior of a straight *pre-bend* segment `{x₀ + s • (v x₀)}` (`s ∈ Icc (-ε) ε`):
its direction is in the kernel of the shape operator at every point of the
segment, the image of `f` is the straight segment with the same endpoints (`f`
is affine on it), and the unit normal is constant along it.  This is the local
content of Lemma `mc` (paper §2.1), generic in the kernel field.  (Same content
as `McFlow.bend_segment`, generic in the field.) -/
lemma field_bend_segment {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {v : ℝ² → ℝ²} (hv : IsKernelField f v) {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior)
    (hw₀ : v x₀ ≠ 0) :
    ∃ ε > (0 : ℝ),
      (∀ s ∈ Set.Icc (-ε) ε, x₀ + s • (v x₀) ∈ stripInterior ∧ dN f (x₀ + s • (v x₀)) (v x₀) = 0) ∧
      (∀ s ∈ Set.Icc (-ε) ε, f (x₀ + s • (v x₀)) = f x₀ + s • (fderiv ℝ f x₀ (v x₀))) ∧
      (∀ s ∈ Set.Icc (-ε) ε, unitNormal f (x₀ + s • (v x₀)) = unitNormal f x₀) := by
  rcases field_kernel_segment_around hv hx₀ hw₀ with ⟨δ, hδ, hseg⟩
  let ε : ℝ := δ / 2
  have hε0 : 0 < ε := by dsimp [ε]; positivity
  have hεδ : ε < δ := by
    dsimp [ε]
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [hδ]
  have hkern : ∀ u ∈ Set.Icc (-ε) ε, dN f (x₀ + u • (v x₀)) (v x₀) = 0 := by
    intro u hu
    have huI : u ∈ Set.Ioo (-δ) δ := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
      constructor <;> linarith [hεδ]
    exact (hseg u huI).2
  have hins : ∀ u ∈ Set.Icc (-ε) ε, x₀ + u • (v x₀) ∈ stripInterior := by
    intro u hu
    have huI : u ∈ Set.Ioo (-δ) δ := by
      rw [Set.mem_Ioo]
      rcases Set.mem_Icc.mp hu with ⟨h1, h2⟩
      constructor <;> linarith [hεδ]
    exact (hseg u huI).1
  have hnorm : ∀ u ∈ Set.Icc (-ε) ε, unitNormal f (x₀ + u • (v x₀)) = unitNormal f x₀ := by
    intro u hu
    have hmain := normal_const_on_kernel_segment hf (x := x₀) (v := v x₀) (A := -ε) (B := ε)
      hins hkern u hu
    have h0 := normal_const_on_kernel_segment hf (x := x₀) (v := v x₀) (A := -ε) (B := ε)
      hins hkern 0 (by rw [Set.mem_Icc]; constructor <;> linarith [hε0])
    calc
      unitNormal f (x₀ + u • (v x₀)) = unitNormal f (x₀ + (-ε) • (v x₀)) := hmain
      _ = unitNormal f x₀ := by
        simpa using h0.symm
  have haff : ∀ u ∈ Set.Icc (-ε) ε, f (x₀ + u • (v x₀)) = f x₀ + u • (fderiv ℝ f x₀ (v x₀)) :=
    affine_from_center hf (x₀ := x₀) (v := v x₀) (A := -ε) (B := ε)
      (by linarith) (by linarith [hε0]) hins hkern
  refine ⟨ε, hε0, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨hins s hs, hkern s hs⟩
  · intro s hs
    exact haff s hs
  · intro s hs
    exact hnorm s hs


/-! ## Instances for the kernel and mirror kernel fields -/

/-- The kernel vector field `Vf f` is a straightening kernel field on the
interior of the strip. -/
lemma kernelField_Vf {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    IsKernelField f (Vf f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact contDiffAt_Vf_one hf x hx
  · intro x hx
    exact Vf_mem_ker hf x hx
  · intro x hx hw
    exact Vf_deriv_parallel hf x hx hw

/-- The mirror kernel vector field `V2f f` is a straightening kernel field on
the interior of the strip. -/
lemma kernelField_V2f {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    IsKernelField f (V2f f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact contDiffAt_V2f_one hf x hx
  · intro x hx
    exact V2f_mem_ker hf x hx
  · intro x hx hw
    exact V2_deriv_parallel hf x hx hw

/-- **Local bend, mirror branch**: through any interior point `x₀` with
`V2f f x₀ ≠ 0` there is a straight pre-bend segment in direction
`V2f f x₀` on which `f` is affine and the unit normal is constant. -/
lemma bend_segment_mirror {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hw₀ : V2f f x₀ ≠ 0) :
    ∃ ε > (0 : ℝ),
      (∀ s ∈ Set.Icc (-ε) ε, x₀ + s • (V2f f x₀) ∈ stripInterior ∧ dN f (x₀ + s • (V2f f x₀)) (V2f f x₀) = 0) ∧
      (∀ s ∈ Set.Icc (-ε) ε, f (x₀ + s • (V2f f x₀)) = f x₀ + s • (fderiv ℝ f x₀ (V2f f x₀))) ∧
      (∀ s ∈ Set.Icc (-ε) ε, unitNormal f (x₀ + s • (V2f f x₀)) = unitNormal f x₀) := by
  exact field_bend_segment hf (kernelField_V2f hf) hx₀ hw₀

/-! ## Vanishing criteria and the case split -/

/-- The kernel field `Vf f = (b, −a)` vanishes exactly when `a = b = 0`. -/
lemma Vf_eq_zero_iff {f : ℝ² → ℝ³} {x : ℝ²} :
    Vf f x = 0 ↔ dNentry f x 1 0 = 0 ∧ dNentry f x 0 0 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun z : ℝ² => z 0) h
    have h1 := congrArg (fun z : ℝ² => z 1) h
    constructor
    · simpa [Vf, e0, e1] using h0
    · have hz : -(dNentry f x 0 0) = 0 := by simpa [Vf, e0, e1] using h1
      linarith
  · rintro ⟨hb, ha⟩
    ext i <;> fin_cases i <;> simp [Vf, e0, e1, hb, ha]

/-- The mirror kernel field `V2f f = (c, −b)` vanishes exactly when
`b = c = 0`. -/
lemma V2f_eq_zero_iff {f : ℝ² → ℝ³} {x : ℝ²} :
    V2f f x = 0 ↔ dNentry f x 1 1 = 0 ∧ dNentry f x 1 0 = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun z : ℝ² => z 0) h
    have h1 := congrArg (fun z : ℝ² => z 1) h
    constructor
    · simpa [V2f, e0, e1] using h0
    · have hz : -(dNentry f x 1 0) = 0 := by simpa [V2f, e0, e1] using h1
      linarith
  · rintro ⟨hc, hb⟩
    ext i <;> fin_cases i <;> simp [V2f, e0, e1, hc, hb]

/-- If all four entries of the shape matrix vanish at an interior point, the
shape operator is zero there. -/
lemma dN_eq_zero_of_entries_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior,
      (∀ i j : Fin 2, dNentry f x i j = 0) → dN f x = 0 := by
  intro x hx hzero
  apply ContinuousLinearMap.ext
  intro v
  have hz0 : ((Matrix.of (dNentry f x))ᵀ).mulVec (![1, 0] : Fin 2 → ℝ) = 0 := by
    ext i <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.of_apply, Fin.sum_univ_two] <;> simp [hzero]
  have hk0 := shape_ker_of_mulVec hf x hx (![1, 0] : Fin 2 → ℝ) hz0
  have hde0 : dN f x !₂[1, 0] = 0 := by
    have he : WithLp.toLp 2 (![1, 0] : Fin 2 → ℝ) = (!₂[1, 0] : ℝ²) := by
      ext i <;> fin_cases i <;> simp
    rwa [he] at hk0
  have hz1 : ((Matrix.of (dNentry f x))ᵀ).mulVec (![0, 1] : Fin 2 → ℝ) = 0 := by
    ext i <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.of_apply, Fin.sum_univ_two] <;> simp [hzero]
  have hk1 := shape_ker_of_mulVec hf x hx (![0, 1] : Fin 2 → ℝ) hz1
  have hde1 : dN f x !₂[0, 1] = 0 := by
    have he : WithLp.toLp 2 (![0, 1] : Fin 2 → ℝ) = (!₂[0, 1] : ℝ²) := by
      ext i <;> fin_cases i <;> simp
    rwa [he] at hk1
  rw [vec_eq_basis v, map_add, map_smul, map_smul, hde0, hde1]
  simp

/-- Wherever the shape operator is nonzero at an interior point, at least one
of the two kernel fields `Vf f`, `V2f f` is nonzero there. -/
lemma kernel_field_ne_zero_of_dN_ne_zero {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) :
    ∀ x ∈ stripInterior, dN f x ≠ 0 → Vf f x ≠ 0 ∨ V2f f x ≠ 0 := by
  intro x hx hdN
  by_cases hVf : Vf f x ≠ 0
  · exact Or.inl hVf
  · right
    have hVf0 : Vf f x = 0 := not_not.mp hVf
    intro hV2
    apply hdN
    apply dN_eq_zero_of_entries_zero hf x hx
    intro i j
    fin_cases i <;> fin_cases j <;> simp
    · exact (Vf_eq_zero_iff.mp hVf0).2
    · have hs : dNentry f x 0 1 = dNentry f x 1 0 :=
        shapeOperator_symm hf x hx (0 : Fin 2) (1 : Fin 2)
      rw [hs]
      exact (Vf_eq_zero_iff.mp hVf0).1
    · exact (Vf_eq_zero_iff.mp hVf0).1
    · exact (V2f_eq_zero_iff.mp hV2).1

/-- **Every interior point with nonzero shape operator lies in the interior
of a straight pre-bend segment** (the local content of Lemma `mc`, paper
§2.1): there is a nonzero direction `w₀` such that the straight segment
`{x₀ + s • w₀}` (`s ∈ Icc (-ε) ε`) stays in the interior of the strip, has
`w₀` in the kernel of the shape operator throughout, maps under `f` to the
straight segment with the same endpoints (affineness), and carries constant
unit normal. -/
lemma bend_segment_of_dN_ne_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {x₀ : ℝ²} (hx₀ : x₀ ∈ stripInterior) (hdN : dN f x₀ ≠ 0) :
    ∃ w₀ : ℝ², w₀ ≠ 0 ∧ ∃ ε > (0 : ℝ),
      (∀ s ∈ Set.Icc (-ε) ε, x₀ + s • w₀ ∈ stripInterior ∧ dN f (x₀ + s • w₀) w₀ = 0) ∧
      (∀ s ∈ Set.Icc (-ε) ε, f (x₀ + s • w₀) = f x₀ + s • (fderiv ℝ f x₀ w₀)) ∧
      (∀ s ∈ Set.Icc (-ε) ε, unitNormal f (x₀ + s • w₀) = unitNormal f x₀) := by
  rcases kernel_field_ne_zero_of_dN_ne_zero hf x₀ hx₀ hdN with hvf | hv2
  · rcases field_bend_segment hf (kernelField_Vf hf) hx₀ hvf with ⟨ε, hε, h1, h2, h3⟩
    exact ⟨Vf f x₀, hvf, ε, hε, h1, h2, h3⟩
  · rcases field_bend_segment hf (kernelField_V2f hf) hx₀ hv2 with ⟨ε, hε, h1, h2, h3⟩
    exact ⟨V2f f x₀, hv2, ε, hε, h1, h2, h3⟩

end Submission.PaperBand
end
