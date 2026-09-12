import ChallengeDeps
import Submission.Metric
import Submission.ChartNormal
import Submission.ChartArc
import Submission.Rigidity
import Submission.LocalExt
import Submission.NeckRig
import Mathlib

/-!
# Local geodesic extension through a limit point (rigid statement) - final module

Theorem: `Submission.local_extension`.

## Statement

Under the challenge hypotheses, at every point `q : M` and every positive speed `c` there is
`η > 0` such that: any locally-linear curve `γ` of speed `c` on `(a,b)` (Metric.IsLocLinear)
which converges to `q` at `b⁻` extends to a locally-linear curve of speed `c` on `(a, b+η)`
agreeing with `γ` on `(a,b)`.

## Proof structure

1. `Submission.neck_rigidity` (NeckRig.lean): normal-coordinate data at `q` (radial identity,
   two-sided arc identity `hArcM` for unit `W` and small `s ≤ t`) plus the TAIL claim: any
   locally linear `γ` with limit `q` at `b⁻` is eventually `γ t = ExpM ((b-t)•V)` with
   `‖V‖ = c`.
2. Glue: with the unit vector `W := V/c`, both the neck of `γ` (for `t < b`) and the
   continuation `t ↦ ExpM((b-t)•V)` (for `t ≥ b`) lie on the single two-sided exact arc
   through `q`; the two-sided identity makes the glued curve locally linear in a window of
   radius `~ρa/c` around `b`.  Away from `b`, local linearity of `γR` at `t₀ < b` is
   inherited from `γ` (windows clipped below `b`).
-/

open scoped Manifold ENNReal ContDiff Topology
open Set Filter Metric
open Bundle

namespace Submission

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

theorem local_extension {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    (q : M) (c : NNReal) (hc : 0 < c) :
    ∃ η > 0, ∀ (a b : ℝ) (hab : a < b) (γ : ℝ → M),
      Metric.IsLocLinear a b c γ →
      Tendsto γ (𝓝[Iio b] b) (𝓝 q) →
      ∃ γR : ℝ → M, (∀ t ∈ Ioo a b, γR t = γ t) ∧
        Metric.IsLocLinear a (b + η) c γR := by
  classical
  let x₀ : E := extChartAt I q q
  rcases neck_rigidity (I := I) (M := M) q c hc with
    ⟨ρ0, hρ00, ge, hgeC, hgeSymm, hgePos, hgeAgree, hrest⟩
  rcases hrest with ⟨r, hr0, ExpM, S, invM, hExpM0, hSnhds, hS_in, hExpCont, hInj,
    hSurj, hInvS, hInvExp, hRadial, hrest2⟩
  rcases hrest2 with ⟨ρa, hρa0, hρale, hArcM, hNeck⟩
  have hBnonneg : ∀ v : E, 0 ≤ (ge x₀) v v := by
    intro v
    by_cases hv : v = 0
    · subst v; simp
    · exact le_of_lt (hgePos x₀ v hv)
  let cR : ℝ := (c : ℝ)
  have hcR0 : 0 < cR := by exact_mod_cast hc
  have hcRnonneg : 0 ≤ cR := le_of_lt hcR0
  let η : ℝ := ρa / (4 * cR)
  have hη0 : 0 < η := by
    dsimp [η]
    positivity
  have hη_scalar : cR * η < ρa := by
    dsimp [η]
    have hc : cR * (ρa / (4 * cR)) = ρa / 4 := by
      field_simp [ne_of_gt hcR0]
    rw [hc]
    linarith [hρa0]
  refine ⟨η, hη0, ?_⟩
  intro a b hab γ hγ hγq
  rcases hNeck a b hab γ hγ hγq with ⟨δ0, hδ00, V, hVnorm, hTail⟩
  -- the unit direction of the continuation
  let W : E := (1 / cR) • V
  have hWunit : Real.sqrt ((ge x₀) W W) = 1 := by
    have hsc : 0 ≤ 1 / cR := by positivity
    have hs := sqrt_quad_smul_nonneg (ge x₀) hsc V (hBnonneg V)
    dsimp [W]
    calc
      Real.sqrt ((ge x₀) ((1 / cR) • V) ((1 / cR) • V)) = (1 / cR) * Real.sqrt ((ge x₀) V V) := hs
      _ = 1 := by
        have hnorm : Real.sqrt ((ge x₀) V V) = cR := by simpa [x₀, cR] using hVnorm
        rw [hnorm]
        field_simp [ne_of_gt hcR0]
  have hscalar : ∀ (τ : ℝ), ExpM ((b - τ) • V) = ExpM ((cR * (b - τ)) • W) := by
    intro τ
    congr 1
    dsimp [W]
    rw [smul_smul]
    apply congrArg (fun s : ℝ => s • V)
    field_simp [ne_of_gt hcR0]
  -- the glued curve
  let γR : ℝ → M := fun t => if t < b then γ t else ExpM ((b - t) • V)
  have hAgree : ∀ t ∈ Ioo a b, γR t = γ t := by
    intro t ht
    dsimp [γR]
    rw [if_pos ht.2]
  -- local-linearity data window size
  let wnd : ℝ := min δ0 (ρa / (8 * cR))
  have hwnd0 : 0 < wnd := by
    dsimp [wnd]
    exact lt_min hδ00 (div_pos hρa0 (by positivity))
  have hwnd_le_δ0 : wnd ≤ δ0 := by
    dsimp [wnd]
    exact min_le_left _ _
  have hwnd_scalar : cR * wnd < ρa := by
    dsimp [wnd]
    have hmul : cR * min δ0 (ρa / (8 * cR)) ≤ cR * (ρa / (8 * cR)) :=
      mul_le_mul_of_nonneg_left (min_le_right δ0 (ρa / (8 * cR))) hcRnonneg
    have hval : cR * (ρa / (8 * cR)) = ρa / 8 := by
      field_simp [ne_of_gt hcR0]
    calc
      cR * min δ0 (ρa / (8 * cR)) ≤ ρa / 8 := le_trans hmul (le_of_eq hval)
      _ < ρa := by linarith [hρa0]
  refine ⟨γR, hAgree, ?_⟩
  intro t₀ ht₀
  by_cases ht₀b : t₀ < b
  · -- t₀ < b: clip the γ-window below b
    rcases hγ t₀ ⟨ht₀.1, ht₀b⟩ with ⟨δγ, hδγ0, hwinγ⟩
    let δ : ℝ := min δγ ((b - t₀) / 2)
    have hδ0 : 0 < δ := lt_min hδγ0 (by positivity)
    have hδ_le_δγ : δ ≤ δγ := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_le_half : δ ≤ (b - t₀) / 2 := by
      dsimp [δ]
      exact min_le_right _ _
    have hδ_lt_b : t₀ + δ < b := by
      have h1 : t₀ + (b - t₀) / 2 < b := by linarith
      linarith
    refine ⟨δ, hδ0, ?_⟩
    intro s t hs ht
    have hs_mem_γ : s ∈ Ioo (max a (t₀ - δγ)) (min b (t₀ + δγ)) := by
      constructor
      · have hL1 : max a (t₀ - δγ) ≤ max a (t₀ - δ) := by
          apply max_le_max le_rfl
          linarith
        exact lt_of_le_of_lt hL1 hs.1
      · have huR : s < min (b + η) (t₀ + δ) := hs.2
        have hu1 : s < t₀ + δ := lt_of_lt_of_le huR (min_le_right (b + η) (t₀ + δ))
        have hu2 : s < b := lt_of_lt_of_le hu1 (le_of_lt hδ_lt_b)
        exact lt_min hu2 (by linarith)
    have ht_mem_γ : t ∈ Ioo (max a (t₀ - δγ)) (min b (t₀ + δγ)) := by
      constructor
      · have hL1 : max a (t₀ - δγ) ≤ max a (t₀ - δ) := by
          apply max_le_max le_rfl
          linarith
        exact lt_of_le_of_lt hL1 ht.1
      · have huR : t < min (b + η) (t₀ + δ) := ht.2
        have hu1 : t < t₀ + δ := lt_of_lt_of_le huR (min_le_right (b + η) (t₀ + δ))
        have hu2 : t < b := lt_of_lt_of_le hu1 (le_of_lt hδ_lt_b)
        exact lt_min hu2 (by linarith)
    have hdst := hwinγ s t hs_mem_γ ht_mem_γ
    have hsB : s < b := lt_of_lt_of_le hs.2 (by
      have h1 : min (b + η) (t₀ + δ) ≤ t₀ + δ := min_le_right (b + η) (t₀ + δ)
      exact le_trans h1 (le_of_lt hδ_lt_b))
    have htB : t < b := lt_of_lt_of_le ht.2 (by
      have h1 : min (b + η) (t₀ + δ) ≤ t₀ + δ := min_le_right (b + η) (t₀ + δ)
      exact le_trans h1 (le_of_lt hδ_lt_b))
    have hsγ : γR s = γ s := by
      dsimp [γR]
      rw [if_pos hsB]
    have htγ : γR t = γ t := by
      dsimp [γR]
      rw [if_pos htB]
    rw [hsγ, htγ]
    exact hdst
  · -- t₀ ≥ b: everything in a window around t₀ is the exact two-sided arc
    have ht₀b_ge : b ≤ t₀ := le_of_not_gt ht₀b
    have ht₀η : t₀ < b + η := ht₀.2
    let δ : ℝ := min wnd (min (η / 2) ((b + η - t₀) / 2))
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact lt_min hwnd0 (lt_min (by positivity) (by positivity))
    have hδ_le_wnd : δ ≤ wnd := by
      dsimp [δ]
      exact min_le_left _ _
    have hδ_le_η2 : δ ≤ η / 2 := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hδ_le_bηm : δ ≤ (b + η - t₀) / 2 := by
      dsimp [δ]
      exact le_trans (min_le_right wnd (min (η / 2) ((b + η - t₀) / 2))) (min_le_right (η / 2) ((b + η - t₀) / 2))
    have hδ_lt_bη : t₀ + δ < b + η := by
      have h1 : t₀ + (b + η - t₀) / 2 < b + η := by linarith
      have h2 : t₀ + δ ≤ t₀ + (b + η - t₀) / 2 := by
        have h2' : δ ≤ (b + η - t₀) / 2 := hδ_le_bηm
        linarith
      exact lt_of_le_of_lt h2 h1
    refine ⟨δ, hδ0, ?_⟩
    intro s t hs ht
    -- window left end is above b - δ0 (neck region)
    have hwnd_left (u : ℝ) (hu : u ∈ Ioo (max a (t₀ - δ)) (min (b + η) (t₀ + δ))) :
        b - δ0 < u := by
      have hu1 : t₀ - δ < u := lt_of_le_of_lt (le_max_right a (t₀ - δ)) hu.1
      have h1 : δ ≤ δ0 := le_trans hδ_le_wnd hwnd_le_δ0
      have hle : b - δ0 ≤ t₀ - δ := by linarith
      exact lt_of_le_of_lt hle hu1
    -- all points of the window lie on the arc ExpM ((b-u)•V)
    have hwnd_arc (u : ℝ) (hu : u ∈ Ioo (max a (t₀ - δ)) (min (b + η) (t₀ + δ))) :
        γR u = ExpM ((b - u) • V) := by
      by_cases hub : u < b
      · have htail := hTail u ⟨hwnd_left u hu, hub⟩
        dsimp [γR]
        rw [if_pos hub]
        exact htail
      · dsimp [γR]
        rw [if_neg hub]
    -- scalar bound |cR * (b - u)| < ρa for u in the window
    have hwnd_scalar_bd (u : ℝ) (hu : u ∈ Ioo (max a (t₀ - δ)) (min (b + η) (t₀ + δ))) :
        |cR * (b - u)| < ρa := by
      have hu_bη : u < b + η := lt_of_lt_of_le hu.2 (min_le_left (b + η) (t₀ + δ))
      by_cases hub : u < b
      · -- u < b : |b-u| = b-u < δ ≤ wnd
        have hbd : b - u < δ := by
          have hu_left : t₀ - δ < u := lt_of_le_of_lt (le_max_right a (t₀ - δ)) hu.1
          have hge : b - δ ≤ t₀ - δ := by linarith
          have hgt : b - δ < u := lt_of_le_of_lt hge hu_left
          linarith
        have habs : |b - u| = b - u := abs_of_nonneg (le_of_lt (sub_pos.mpr hub))
        have hm : cR * (b - u) < ρa := by
          have h1 : cR * (b - u) < cR * δ := mul_lt_mul_of_pos_left hbd hcR0
          have h2 : cR * δ ≤ cR * wnd := mul_le_mul_of_nonneg_left hδ_le_wnd hcRnonneg
          have h3 : cR * wnd < ρa := hwnd_scalar
          linarith
        rw [abs_mul]
        rw [abs_of_nonneg hcRnonneg]
        rw [habs]
        exact hm
      · -- b ≤ u : |b-u| = u-b < η
        have hub_le : b ≤ u := le_of_not_gt hub
        have hnn : 0 ≤ u - b := sub_nonneg.mpr hub_le
        have habs : |b - u| = u - b := by
          rw [abs_of_nonpos (sub_nonpos.mpr hub_le)]
          ring
        have hm : cR * (u - b) < ρa := by
          have h1 : u - b < η := by linarith [hu_bη]
          have h2 : cR * (u - b) < cR * η := mul_lt_mul_of_pos_left h1 hcR0
          linarith [h2, hη_scalar]
        rw [abs_mul]
        rw [abs_of_nonneg hcRnonneg]
        rw [habs]
        exact hm
    -- distance equality via the two-sided arc identity
    by_cases hst : s ≤ t
    · have hsW : s ∈ Ioo (max a (t₀ - δ)) (min (b + η) (t₀ + δ)) := hs
      have htW : t ∈ Ioo (max a (t₀ - δ)) (min (b + η) (t₀ + δ)) := ht
      let α : ℝ := cR * (b - t)
      let β : ℝ := cR * (b - s)
      have hαβ : α ≤ β := by
        dsimp [α, β]
        have hst' : b - t ≤ b - s := by linarith
        exact mul_le_mul_of_nonneg_left hst' hcRnonneg
      have hαlt : |α| < ρa := by
        simpa [α] using hwnd_scalar_bd t htW
      have hβlt : |β| < ρa := by
        simpa [β] using hwnd_scalar_bd s hsW
      have hd := hArcM W hWunit hαβ hαlt hβlt
      have hdα : γR t = ExpM (α • W) := by
        have h1 := hwnd_arc t htW
        have h2 := hscalar t
        calc
          γR t = ExpM ((b - t) • V) := h1
          _ = ExpM ((cR * (b - t)) • W) := h2
          _ = ExpM (α • W) := by rfl
      have hdβ : γR s = ExpM (β • W) := by
        have h1 := hwnd_arc s hsW
        have h2 := hscalar s
        calc
          γR s = ExpM ((b - s) • V) := h1
          _ = ExpM ((cR * (b - s)) • W) := h2
          _ = ExpM (β • W) := by rfl
      have hdst : edist (γR s) (γR t) = ENNReal.ofReal (cR * (t - s)) := by
        calc
          edist (γR s) (γR t) = edist (ExpM (β • W)) (ExpM (α • W)) := by rw [hdβ, hdα]
          _ = edist (ExpM (α • W)) (ExpM (β • W)) := edist_comm _ _
          _ = ENNReal.ofReal (β - α) := hd
          _ = ENNReal.ofReal (cR * (t - s)) := by
            congr 1
            dsimp [β, α]
            ring
      have habs : |t - s| = t - s := abs_of_nonneg (sub_nonneg.mpr hst)
      calc
        edist (γR s) (γR t) = ENNReal.ofReal (cR * (t - s)) := hdst
        _ = ENNReal.ofReal (cR * |t - s|) := by rw [habs]
        _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
          rw [ENNReal.ofReal_mul hcRnonneg]
          rw [ENNReal.ofReal_coe_nnreal]
    · have hts : t ≤ s := le_of_not_ge hst
      have hsW : s ∈ Ioo (max a (t₀ - δ)) (min (b + η) (t₀ + δ)) := hs
      have htW : t ∈ Ioo (max a (t₀ - δ)) (min (b + η) (t₀ + δ)) := ht
      let α : ℝ := cR * (b - s)
      let β : ℝ := cR * (b - t)
      have hαβ : α ≤ β := by
        dsimp [α, β]
        have hts' : b - s ≤ b - t := by linarith
        exact mul_le_mul_of_nonneg_left hts' hcRnonneg
      have hαlt : |α| < ρa := by
        simpa [α] using hwnd_scalar_bd s hsW
      have hβlt : |β| < ρa := by
        simpa [β] using hwnd_scalar_bd t htW
      have hd := hArcM W hWunit hαβ hαlt hβlt
      have hdα : γR s = ExpM (α • W) := by
        have h1 := hwnd_arc s hsW
        have h2 := hscalar s
        calc
          γR s = ExpM ((b - s) • V) := h1
          _ = ExpM ((cR * (b - s)) • W) := h2
          _ = ExpM (α • W) := by rfl
      have hdβ : γR t = ExpM (β • W) := by
        have h1 := hwnd_arc t htW
        have h2 := hscalar t
        calc
          γR t = ExpM ((b - t) • V) := h1
          _ = ExpM ((cR * (b - t)) • W) := h2
          _ = ExpM (β • W) := by rfl
      have hdst : edist (γR t) (γR s) = ENNReal.ofReal (cR * (s - t)) := by
        calc
          edist (γR t) (γR s) = edist (ExpM (β • W)) (ExpM (α • W)) := by rw [hdβ, hdα]
          _ = edist (ExpM (α • W)) (ExpM (β • W)) := edist_comm _ _
          _ = ENNReal.ofReal (β - α) := hd
          _ = ENNReal.ofReal (cR * (s - t)) := by
            congr 1
            dsimp [β, α]
            ring
      have hdst' : edist (γR s) (γR t) = ENNReal.ofReal (cR * (s - t)) := by
        simpa [edist_comm] using hdst
      have habs : |t - s| = s - t := by
        rw [abs_sub_comm]
        exact abs_of_nonneg (sub_nonneg.mpr hts)
      calc
        edist (γR s) (γR t) = ENNReal.ofReal (cR * (s - t)) := hdst'
        _ = ENNReal.ofReal (cR * |t - s|) := by rw [habs]
        _ = (c : ℝ≥0∞) * ENNReal.ofReal |t - s| := by
          rw [ENNReal.ofReal_mul hcRnonneg]
          rw [ENNReal.ofReal_coe_nnreal]

end Submission
