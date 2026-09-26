import Mathlib
import Submission.Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape
import Submission.Commons.Topology.Charts.coordSet_open_preconnected_nonempty
import Submission.Commons.Topology.Homeomorph.open_interval_affine
import Submission.Commons.Topology.OneManifold.union_two_open_arcs_connected_overlap_interval
import Submission.Commons.Topology.OneManifold.nested_open_arcs_union_is_open_arc
import Submission.Commons.Topology.OneManifold.boundary_point_attracts_left_end
import Submission.Commons.Topology.OneManifold.boundary_point_attracts_right_end
import Submission.Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full
import Submission.Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full_right
import Submission.Commons.Analysis.RealIntervals.left_full_or_strip_of_left_dense
import Submission.Commons.Topology.OneManifold.chart_pullback_interval_shape
import Submission.Commons.Analysis.RealIntervals.right_full_or_strip_of_right_dense
import Submission.Commons.Topology.Homeomorph.intervalHomeo_coord_strictMono_or_anti
import Submission.Commons.Topology.Homeomorph.subtype_preimage_homeo


open Set
open scoped Topology
open Filter

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace Commons.Topology.OneManifold

namespace ReachLemma

/-- The open unit interval as a type. -/
abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

variable {X : Type*} [TopologicalSpace X] [T2Space X]

lemma val_embedding : Topology.IsEmbedding (fun t : ORI => (t : ℝ)) := by
  simpa using (Topology.IsEmbedding.subtypeVal (p := fun r : ℝ => r ∈ Set.Ioo (0 : ℝ) 1))

/-- ORI-convergence from real-value convergence. -/
lemma tendsto_ORI_of_tendsto_val {x : ℕ → ORI} {w : ℝ} (hw : w ∈ Set.Ioo (0 : ℝ) 1)
    (hx : Tendsto (fun n => (x n : ℝ)) atTop (𝓝 w)) :
    Tendsto x atTop (𝓝 (⟨w, hw⟩ : ORI)) := by
  rw [val_embedding.tendsto_nhds_iff]
  change Tendsto (fun n : ℕ => (x n : ℝ)) atTop (𝓝 w)
  exact hx

/-- A real sequence valued in a compact interval has a cluster point there. -/
lemma bounded_real_seq_cluster {u v : ℝ} {s : ℕ → ℝ} (h : ∀ n, s n ∈ Set.Icc u v) :
    ∃ w : ℝ, w ∈ Set.Icc u v ∧ MapClusterPt w atTop s := by
  let K : Set ℝ := Set.Icc u v
  have hK : IsCompact K := isCompact_Icc
  have hf : Tendsto s atTop (𝓟 K) := by
    rw [tendsto_principal]
    exact Eventually.of_forall h
  exact hK.exists_clusterPt hf

/-- **Reach contradiction**: a P-arc (coordinate map `cP`) fills a W-strip
(`cW`, coordinates strictly inside `(u,v)`) over a coordinate sequence
`tₙ` tending to the interior coordinate `β`; then the P-point at `β`
equals the W-point at some strip-boundary coordinate (`u` or `v`) or at an
interior strip coordinate `w ∈ (u,v)`. -/
lemma reach_of_filled_strip {cP cW : ORI → X} (hcP : Continuous cP) (hcW : Continuous cW)
    {t : ℕ → ORI} {β u v : ℝ}
    (hβ01 : β ∈ Set.Ioo (0 : ℝ) 1)
    (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    (ht : Tendsto (fun n => (t n : ℝ)) atTop (𝓝 β))
    (hfill : ∀ n, ∃ s : ORI, u < (s : ℝ) ∧ (s : ℝ) < v ∧ cP (t n) = cW s) :
    (cP ⟨β, hβ01⟩ = cW ⟨u, hu0, lt_trans huv hv1⟩) ∨
    (cP ⟨β, hβ01⟩ = cW ⟨v, lt_trans hu0 huv, hv1⟩) ∨
    ∃ w : ℝ, ∃ hw01 : w ∈ Set.Ioo (0 : ℝ) 1, u < w ∧ w < v ∧
      cP ⟨β, hβ01⟩ = cW ⟨w, hw01⟩ := by
  classical
  let s : ℕ → ORI := fun n => Classical.choose (hfill n)
  have hs : ∀ n, u < (s n : ℝ) ∧ (s n : ℝ) < v ∧ cP (t n) = cW (s n) :=
    fun n => Classical.choose_spec (hfill n)
  have hsval : ∀ n, (s n : ℝ) ∈ Set.Icc u v := fun n => ⟨le_of_lt (hs n).1, le_of_lt (hs n).2.1⟩
  rcases bounded_real_seq_cluster hsval with ⟨w, hwIcc, hwcl⟩
  rcases hwcl.tendsto_subseq with ⟨φ, hφmono, hφconv⟩
  have hw01 : w ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hu0 hwIcc.1, lt_of_le_of_lt hwIcc.2 hv1⟩
  have hφatTop : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hsφ : Tendsto (fun n => s (φ n)) atTop (𝓝 ⟨w, hw01⟩) :=
    tendsto_ORI_of_tendsto_val hw01 (hφconv)
  have hcWs : Tendsto (fun n => cW (s (φ n))) atTop (𝓝 (cW ⟨w, hw01⟩)) :=
    hcW.continuousAt.tendsto.comp hsφ
  have htφ : Tendsto (fun n => (t (φ n) : ℝ)) atTop (𝓝 β) := ht.comp hφatTop
  have htφORI : Tendsto (fun n => t (φ n)) atTop (𝓝 ⟨β, hβ01⟩) :=
    tendsto_ORI_of_tendsto_val hβ01 htφ
  have hcPt : Tendsto (fun n => cP (t (φ n))) atTop (𝓝 (cP ⟨β, hβ01⟩)) :=
    hcP.continuousAt.tendsto.comp htφORI
  have hseqEq : (fun n => cW (s (φ n))) = (fun n => cP (t (φ n))) := by
    funext n
    exact (hs (φ n)).2.2.symm
  have hcPtarget : Tendsto (fun n => cW (s (φ n))) atTop (𝓝 (cP ⟨β, hβ01⟩)) := by
    simpa [hseqEq] using hcPt
  have hEqPt : cP ⟨β, hβ01⟩ = cW ⟨w, hw01⟩ := tendsto_nhds_unique hcPtarget hcWs
  by_cases hwu : w = u
  · left
    simpa [hwu] using hEqPt
  · by_cases hwv : w = v
    · right; left
      simpa [hwv] using hEqPt
    · right; right
      have huw : u < w := lt_of_le_of_ne hwIcc.1 (by intro h; exact hwu h.symm)
      have hwv' : w < v := lt_of_le_of_ne hwIcc.2 hwv
      exact ⟨w, hw01, huw, hwv', hEqPt⟩

end ReachLemma

end Commons.Topology.OneManifold


open Set
open scoped Topology
open Filter

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-!
# interior_strip_forces_subset

The genuine "no-infinite-oscillation" content of the one-dimensional end
theory, in cleanest form: an open arc `P` (charted by `e`) meeting an open
arc-chart `W` (charted by `ψ`) in a filled coordinate strip bounded on
both sides by holes (coordinates `u < v`, both interior, whose points are
NOT in `P`, while every coordinate between is IN `P`) must lie entirely
inside `W`.

STATUS: COMPLETE (proved, no sorries).  `interior_strip_forces_subset`
holds: an open arc `P` (chart `e`) meeting an open arc-chart `W` (chart
`ψ`, `W` open) in a filled coordinate strip with holes at both interior
end-coordinates `u, v ∈ (0,1)` lies entirely inside `W`.

Proof architecture:
1. `StripCoordVal_shape` (Commons coordinate-set bridge + RealIntervals
   shape): the P-coordinate set of the strip is an open interval `(α,β)`.
2. `end_reach_contradiction` (powered by the VERIFIED
   `reach_lemma.reach_of_filled_strip`): a coordinate sequence `rₙ` inside
   `(α,β)` converging to an end-coordinate `c` forces `False` — the
   P-point at `c` must equal a W-point of the closed strip (Bolzano-
   Weierstrass cluster point in `[u,v]` + continuity + T2), contradicting
   the two holes or `c ∉ (α,β)`.  The right end uses
   `rₙ = β − (β−α)/(n+2)` (converging to `β`, so `β = 1`), the left end
   `rₙ = α + (β−α)/(n+2)` (converging to `α`, so `α = 0`).
3. `(α,β) = (0,1)` makes every P-point a strip point, hence a W-point.
-/
namespace StripCore

/-- The open unit interval as a type. -/
abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

variable {X : Type*} [TopologicalSpace X] [T2Space X] {P W : Set X}

/-- Chart coercions into X. -/
def ce (e : ORI ≃ₜ {x : X // x ∈ P}) : ORI → X := fun t => ((e t : {x : X // x ∈ P}) : X)
def cψ (ψ : ORI ≃ₜ {x : X // x ∈ W}) : ORI → X := fun t => ((ψ t : {x : X // x ∈ W}) : X)

theorem ce_cont (e : ORI ≃ₜ {x : X // x ∈ P}) : Continuous (ce e) := by
  change Continuous (fun t : ORI => ((e t : {x : X // x ∈ P}) : X))
  exact continuous_subtype_val.comp e.continuous

theorem cψ_cont (ψ : ORI ≃ₜ {x : X // x ∈ W}) : Continuous (cψ ψ) := by
  change Continuous (fun t : ORI => ((ψ t : {x : X // x ∈ W}) : X))
  exact continuous_subtype_val.comp ψ.continuous

theorem cψ_inj (ψ : ORI ≃ₜ {x : X // x ∈ W}) : Function.Injective (cψ ψ) := by
  intro t s h
  apply ψ.injective
  apply Subtype.ext
  exact h

/-- The P-coordinate-value set of the filled strip: `r ∈ (0,1)` belongs to it
iff the point of `P` at coordinate `r` lies in the strip. -/
def StripCoordVal (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    (u v : ℝ) : Set ℝ :=
  ((↑) : ORI → ℝ) ''
    {t : ORI | (ce e t : X) ∈
      (fun s : ORI => (cψ ψ s : X)) '' {s : ORI | u < (s : ℝ) ∧ (s : ℝ) < v}}

/-- StripCoordVal ⊆ (0,1). -/
theorem StripCoordVal_subset_unit (e : ORI ≃ₜ {x : X // x ∈ P})
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (u v : ℝ) :
    StripCoordVal e ψ u v ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro r hr
  rcases hr with ⟨t, htAst, htv⟩
  rw [← htv]
  exact t.2

/-- Openness, preconnectedness and nonemptiness of the strip coordinate set
(from the Commons coordinate-set bridge). -/
theorem StripCoordVal_shape (e : ORI ≃ₜ {x : X // x ∈ P})
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {u v : ℝ} (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    (hfill : ∀ t : ORI, u < (t : ℝ) → (t : ℝ) < v → (cψ ψ t : X) ∈ P) :
    IsOpen (StripCoordVal e ψ u v) ∧
    IsPreconnected (StripCoordVal e ψ u v) ∧
    (StripCoordVal e ψ u v).Nonempty := by
  have hne : (Set.Ioo u v ∩ Set.Ioo (0 : ℝ) 1).Nonempty := by
    have h1 : u < (u + v) / 2 := by linarith
    have h2 : (u + v) / 2 < v := by linarith
    have h3 : (0 : ℝ) < (u + v) / 2 := by linarith
    have h4 : (u + v) / 2 < 1 := by linarith
    exact ⟨(u + v) / 2, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  have hAsub : ((fun t : ORI => (cψ ψ t : X)) ''
      {t : ORI | (t : ℝ) ∈ Set.Ioo u v}) ⊆ P := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    exact hfill t ht.1 ht.2
  exact
    (Commons.Topology.Charts.coordSet_open_preconnected_nonempty (X := X)
      (P := P) (U := W) hWopen (κ := e) (ψ := ψ) (p := u) (c₀ := v) hne hAsub)


/-- If an open interval with `a < b` is contained in `(0,1)`, then `0 ≤ a`
and `b ≤ 1`. -/
theorem Ioo_subset_unit_bounds {a b : ℝ} (hab : a < b)
    (hsub : Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) 1) : 0 ≤ a ∧ b ≤ 1 := by
  constructor
  · by_contra hneg
    have hα₀ : a < 0 := lt_of_not_ge hneg
    by_cases hβ₀ : b ≤ 0
    · rcases exists_between hab with ⟨r, hr1, hr2⟩
      have hr0 : r < 0 := lt_of_lt_of_le hr2 hβ₀
      have hrI : r ∈ Set.Ioo (0 : ℝ) 1 := hsub ⟨hr1, hr2⟩
      have hrgt : 0 < r := hrI.1
      linarith
    · have h0β : 0 < b := lt_of_not_ge hβ₀
      let r : ℝ := a / 2
      have hr1 : a < r := by dsimp [r]; linarith
      have hr2 : r < b := by dsimp [r]; linarith
      have hr0 : r < 0 := by dsimp [r]; linarith
      have hrI : r ∈ Set.Ioo (0 : ℝ) 1 := hsub ⟨hr1, hr2⟩
      have hrgt : 0 < r := hrI.1
      linarith
  · by_contra hneg
    have h1b : 1 < b := lt_of_not_ge hneg
    by_cases hα0 : 0 ≤ a
    · by_cases ha1 : a < 1
      · rcases exists_between h1b with ⟨r, hr1, hr2⟩
        have hr1a : a < r := lt_trans ha1 hr1
        have hrI : r ∈ Set.Ioo (0 : ℝ) 1 := hsub ⟨hr1a, hr2⟩
        have hrlt : r < 1 := hrI.2
        linarith
      · have h1a : 1 ≤ a := le_of_not_gt ha1
        rcases exists_between hab with ⟨r, hr1, hr2⟩
        have hr1ge : 1 ≤ r := le_trans h1a (le_of_lt hr1)
        have hrI : r ∈ Set.Ioo (0 : ℝ) 1 := hsub ⟨hr1, hr2⟩
        have hrlt : r < 1 := hrI.2
        linarith
    · have ha0 : a < 0 := lt_of_not_ge hα0
      rcases exists_between h1b with ⟨r, hr1, hr2⟩
      have hra : a < r := lt_trans (lt_trans ha0 zero_lt_one) hr1
      have hrI : r ∈ Set.Ioo (0 : ℝ) 1 := hsub ⟨hra, hr2⟩
      have hrlt : r < 1 := hrI.2
      linarith

/-- A real `r ∈ (α,β) ⊆ (0,1)` gives a unit-coordinate `⟨r⟩` whose value is
`r` and which lies in the value-preimage of `(α,β)`. -/
theorem unitCoord_mem_preimage {α β : ℝ} (h : Set.Ioo α β ⊆ Set.Ioo (0 : ℝ) 1)
    {r : ℝ} (hr : r ∈ Set.Ioo α β) : (⟨r, (h hr).1, (h hr).2⟩ : ORI) ∈
      (fun t : ORI => (t : ℝ)) ⁻¹' Set.Ioo α β := by
  exact ⟨hr.1, hr.2⟩

/-- The point of ORI at real `r` (with `r ∈ (0,1)`). -/
abbrev atReal {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) : ORI := ⟨r, hr⟩

/-- Membership of the value of `⟨r⟩` in the strip's P-coordinate set. -/
theorem val_mem_stripCoord_of_Ioo (e : ORI ≃ₜ {x : X // x ∈ P})
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) {u v : ℝ}
    (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    (hfill : ∀ t : ORI, u < (t : ℝ) → (t : ℝ) < v → (cψ ψ t : X) ∈ P)
    {α β : ℝ} (hSeq : StripCoordVal e ψ u v = Set.Ioo α β)
    {r : ℝ} (hr : r ∈ Set.Ioo α β)
    (hr01 : r ∈ Set.Ioo (0 : ℝ) 1) :
    (ce e ⟨r, hr01⟩ : X) ∈ (fun s : ORI => (cψ ψ s : X)) ''
      {s : ORI | u < (s : ℝ) ∧ (s : ℝ) < v} := by
  have hrS : r ∈ StripCoordVal e ψ u v := by
    rwa [hSeq]
  rcases hrS with ⟨t₀, ht₀, htv⟩
  have ht₀eq : t₀ = ⟨r, hr01⟩ := by
    apply Subtype.ext
    exact htv
  simpa [ht₀eq] using ht₀

/-- The strip W-coordinate of the P-point at real `r` (r ∈ (α,β)); the
resulting real is in `(u,v)`. -/
noncomputable def stripCoordOf (e : ORI ≃ₜ {x : X // x ∈ P})
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) {u v : ℝ}
    (hfill : ∀ t : ORI, u < (t : ℝ) → (t : ℝ) < v → (cψ ψ t : X) ∈ P)
    (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    {α β : ℝ} (hSeq : StripCoordVal e ψ u v = Set.Ioo α β)
    (h01 : Set.Ioo α β ⊆ Set.Ioo (0 : ℝ) 1)
    (r : {x : ℝ // x ∈ Set.Ioo α β}) : {x : ℝ // x ∈ Set.Ioo u v} := by
  let h01r : r.1 ∈ Set.Ioo (0 : ℝ) 1 := h01 r.2
  have hce : (ce e ⟨r.1, h01r⟩ : X) ∈ (fun s : ORI => (cψ ψ s : X)) ''
      {s : ORI | u < (s : ℝ) ∧ (s : ℝ) < v} :=
    val_mem_stripCoord_of_Ioo e ψ hu0 huv hv1 hfill hSeq r.2 h01r
  let s : ORI := Classical.choose hce
  have hspec := Classical.choose_spec hce
  exact ⟨(s : ℝ), hspec.1⟩


/-- Point of ORI at coordinate `r` and the point of P with that coordinate is
in W with strip-coordinate in `(u,v)` — helper instances for the transition
homeomorphism. -/
theorem ce_mem_W_of_stripCoord (e : ORI ≃ₜ {x : X // x ∈ P})
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) {u v : ℝ}
    (hfill : ∀ t : ORI, u < (t : ℝ) → (t : ℝ) < v → (cψ ψ t : X) ∈ P)
    (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    {α β : ℝ} (hSeq : StripCoordVal e ψ u v = Set.Ioo α β)
    (h01 : Set.Ioo α β ⊆ Set.Ioo (0 : ℝ) 1)
    {r : ℝ} (hr : r ∈ Set.Ioo α β) :
    (ce e ⟨r, h01 hr⟩ : X) ∈ W := by
  have hce : (ce e ⟨r, h01 hr⟩ : X) ∈ (fun s : ORI => (cψ ψ s : X)) ''
      {s : ORI | u < (s : ℝ) ∧ (s : ℝ) < v} :=
    val_mem_stripCoord_of_Ioo e ψ hu0 huv hv1 hfill hSeq hr (h01 hr)
  rcases hce with ⟨s, hs, heq⟩
  have hsW : (cψ ψ s : X) ∈ W := (ψ s : {x : X // x ∈ W}).2
  simpa [heq] using hsW


/-- **End contradiction (sequence form)**: a coordinate sequence `rₙ` inside
`(α,β)` (the P-coordinate interval of the filled strip) converging to an
interior coordinate `c` (an end of the strip interval, so `c ∉ (α,β)`)
forces `False`: the P-point at coordinate `c` must equal a W-point of the
closed strip, contradicting the two holes (`huP`, `hvP`) or
`c ∉ (α,β) = StripCoordVal` (the interior case). -/
lemma end_reach_contradiction (e : ORI ≃ₜ {x : X // x ∈ P})
    (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {u v : ℝ} (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    (hfill : ∀ t : ORI, u < (t : ℝ) → (t : ℝ) < v → (cψ ψ t : X) ∈ P)
    {α β : ℝ} (hSeq : StripCoordVal e ψ u v = Set.Ioo α β)
    (h01 : Set.Ioo α β ⊆ Set.Ioo (0 : ℝ) 1)
    (huP : (cψ ψ ⟨u, hu0, lt_trans huv hv1⟩ : X) ∉ P)
    (hvP : (cψ ψ ⟨v, lt_trans hu0 huv, hv1⟩ : X) ∉ P)
    {c : ℝ} (hc01 : c ∈ Set.Ioo (0 : ℝ) 1) (hcnot : c ∉ Set.Ioo α β)
    (r : ℕ → ℝ) (hr_in : ∀ n, r n ∈ Set.Ioo α β)
    (hr_tend : Tendsto r atTop (𝓝 c))
    (hfillr : ∀ n, ∃ s : ORI, u < (s : ℝ) ∧ (s : ℝ) < v ∧
      ce e ⟨r n, h01 (hr_in n)⟩ = cψ ψ s) :
    False := by
  classical
  let tt : ℕ → ORI := fun n => ⟨r n, h01 (hr_in n)⟩
  have ht : Tendsto (fun n => (tt n : ℝ)) atTop (𝓝 c) := by
    simpa [tt] using hr_tend
  have hfillt : ∀ n, ∃ s : ORI, u < (s : ℝ) ∧ (s : ℝ) < v ∧ ce e (tt n) = cψ ψ s := by
    intro n
    rcases hfillr n with ⟨s, hs, heq⟩
    exact ⟨s, hs, heq⟩
  have hreach := ReachLemma.reach_of_filled_strip (cP := ce e) (cW := cψ ψ)
    (ce_cont e) (cψ_cont ψ) (t := tt) hc01 hu0 huv hv1 ht hfillt
  rcases hreach with h1 | h2 | h3
  · have hP : (ce e ⟨c, hc01⟩ : X) ∈ P := (e ⟨c, hc01⟩).2
    rw [h1] at hP
    exact huP hP
  · have hP : (ce e ⟨c, hc01⟩ : X) ∈ P := (e ⟨c, hc01⟩).2
    rw [h2] at hP
    exact hvP hP
  · rcases h3 with ⟨w, hw01, huw, hwv, heq⟩
    have hmem : (ce e ⟨c, hc01⟩ : X) ∈ (fun s : ORI => (cψ ψ s : X)) ''
        {s : ORI | u < (s : ℝ) ∧ (s : ℝ) < v} :=
      ⟨⟨w, hw01⟩, ⟨huw, hwv⟩, heq.symm⟩
    have hcS : c ∈ StripCoordVal e ψ u v := by
      rw [StripCoordVal]
      exact ⟨⟨c, hc01⟩, hmem, rfl⟩
    have hcIn : c ∈ Set.Ioo α β := by
      rwa [hSeq] at hcS
    exact hcnot hcIn

theorem interior_strip_forces_subset {X : Type*} [TopologicalSpace X] [T2Space X]
    {P W : Set X} (e : ORI ≃ₜ {x : X // x ∈ P})
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {u v : ℝ} (hu0 : 0 < u) (huv : u < v) (hv1 : v < 1)
    (huP : (cψ ψ ⟨u, hu0, lt_trans huv hv1⟩ : X) ∉ P)
    (hvP : (cψ ψ ⟨v, lt_trans hu0 huv, hv1⟩ : X) ∉ P)
    (hfill : ∀ t : ORI, u < (t : ℝ) → (t : ℝ) < v → (cψ ψ t : X) ∈ P) :
    P ⊆ W := by
  -- Step 1: the P-coordinate set of the strip is an open interval (α,β).
  rcases StripCoordVal_shape e ψ hWopen hu0 huv hv1 hfill with ⟨hSopen, hSpc, hSne⟩
  have hS01 : StripCoordVal e ψ u v ⊆ Set.Ioo (0 : ℝ) 1 := StripCoordVal_subset_unit e ψ u v
  rcases Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape
      hS01 hSopen hSne hSpc with ⟨α, β, hαβ, hSeq⟩
  have hbounds : 0 ≤ α ∧ β ≤ 1 := Ioo_subset_unit_bounds hαβ (by
    simpa [hSeq] using hS01)
  -- Step 2: the interval is the whole unit interval (α = 0 and β = 1).
  have h01int : Set.Ioo α β ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨lt_of_le_of_lt hbounds.1 hr.1, lt_of_lt_of_le hr.2 hbounds.2⟩
  have hfrac_pos : ∀ n : ℕ, 0 < (β - α) / (((n + 2 : ℕ) : ℝ)) := by
    intro n
    have hden : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n + 2)
    exact div_pos (sub_pos.mpr hαβ) hden
  have hfrac_lt : ∀ n : ℕ, (β - α) / (((n + 2 : ℕ) : ℝ)) < β - α := by
    intro n
    have hdenₙ : (0 : ℕ) < n + 2 := by omega
    have hden : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast hdenₙ
    have honeₙ : (1 : ℕ) < n + 2 := by omega
    have hone : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast honeₙ
    rw [div_lt_iff₀ hden]
    have hmul : (1 : ℝ) * (β - α) < (((n + 2 : ℕ) : ℝ)) * (β - α) :=
      mul_lt_mul_of_pos_right hone (sub_pos.mpr hαβ)
    nlinarith
  have hfrac_tend : Tendsto (fun n : ℕ => (β - α) / (((n + 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n : ℝ) + 2)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
    have hnv : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
      have h := tendsto_inv_atTop_zero.comp hn
      convert h using 1
      funext n
      simp [Nat.cast_add, Function.comp_def]
    have hm : Tendsto (fun n : ℕ => (β - α) * (((n + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) := by
      simpa [mul_zero] using ((tendsto_const_nhds (x := β - α)).mul hnv)
    simpa [div_eq_mul_inv] using hm
  -- right end: β = 1
  have hβeq : β = 1 := by
    by_contra hβne
    have hβlt : β < 1 := lt_of_le_of_ne hbounds.2 hβne
    have hβgt : 0 < β := lt_of_le_of_lt hbounds.1 hαβ
    have hβ01 : β ∈ Set.Ioo (0 : ℝ) 1 := ⟨hβgt, hβlt⟩
    have hcnot : β ∉ Set.Ioo α β := by
      intro hb
      exact (lt_irrefl β) hb.2
    let rv : ℕ → ℝ := fun n => β - (β - α) / (((n + 2 : ℕ) : ℝ))
    have hrv_in : ∀ n, rv n ∈ Set.Ioo α β := by
      intro n
      constructor
      · have hltf := hfrac_lt n
        dsimp [rv]
        linarith
      · have hpos := hfrac_pos n
        dsimp [rv]
        linarith
    have hrv_tend : Tendsto rv atTop (𝓝 β) := by
      dsimp [rv]
      have hc : Tendsto (fun _n : ℕ => (β : ℝ)) atTop (𝓝 (β : ℝ)) := tendsto_const_nhds
      have hsub := hc.sub hfrac_tend
      simpa using hsub
    have hfillr : ∀ n, ∃ s : ORI, u < (s : ℝ) ∧ (s : ℝ) < v ∧
        ce e ⟨rv n, h01int (hrv_in n)⟩ = cψ ψ s := by
      intro n
      rcases (val_mem_stripCoord_of_Ioo e ψ hu0 huv hv1 hfill hSeq (hrv_in n)
          (h01int (hrv_in n))) with ⟨s, hs, heq⟩
      exact ⟨s, hs.1, hs.2, heq.symm⟩
    exact end_reach_contradiction e ψ hu0 huv hv1 hfill hSeq h01int huP hvP
      hβ01 hcnot rv hrv_in hrv_tend hfillr
  -- left end: α = 0
  have hαeq : α = 0 := by
    by_contra hαne
    have hαgt : 0 < α := lt_of_le_of_ne hbounds.1 (by intro h; exact hαne h.symm)
    have hαlt : α < 1 := lt_of_lt_of_le hαβ hbounds.2
    have hα01 : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨hαgt, hαlt⟩
    have hcnot : α ∉ Set.Ioo α β := by
      intro hb
      exact (lt_irrefl α) hb.1
    let lv : ℕ → ℝ := fun n => α + (β - α) / (((n + 2 : ℕ) : ℝ))
    have hlv_in : ∀ n, lv n ∈ Set.Ioo α β := by
      intro n
      constructor
      · have hpos := hfrac_pos n
        dsimp [lv]
        linarith
      · have hltf := hfrac_lt n
        dsimp [lv]
        linarith
    have hlv_tend : Tendsto lv atTop (𝓝 α) := by
      dsimp [lv]
      have hc : Tendsto (fun _n : ℕ => (α : ℝ)) atTop (𝓝 (α : ℝ)) := tendsto_const_nhds
      have hadd := hc.add hfrac_tend
      simpa using hadd
    have hfilll : ∀ n, ∃ s : ORI, u < (s : ℝ) ∧ (s : ℝ) < v ∧
        ce e ⟨lv n, h01int (hlv_in n)⟩ = cψ ψ s := by
      intro n
      rcases (val_mem_stripCoord_of_Ioo e ψ hu0 huv hv1 hfill hSeq (hlv_in n)
          (h01int (hlv_in n))) with ⟨s, hs, heq⟩
      exact ⟨s, hs.1, hs.2, heq.symm⟩
    exact end_reach_contradiction e ψ hu0 huv hv1 hfill hSeq h01int huP hvP
      hα01 hcnot lv hlv_in hlv_tend hfilll
  have hAll : ∀ r : ℝ, r ∈ Set.Ioo (0 : ℝ) 1 → r ∈ Set.Ioo α β := by
    intro r hr
    exact ⟨by simpa [hαeq] using hr.1, by simpa [hβeq] using hr.2⟩
  -- Step 3: every P-point is a W-point.
  intro y hy
  -- y = ce ⟨r⟩ for r = its P-coordinate; r ∈ (0,1) ⊆ (α,β) = StripCoordVal
  let r : ℝ := (e.symm ⟨y, hy⟩ : ORI).1
  have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := (e.symm ⟨y, hy⟩ : ORI).2
  have hrS : r ∈ StripCoordVal e ψ u v := by
    rw [hSeq]
    exact hAll r hr01
  rcases hrS with ⟨t₀, ht₀, htv⟩
  have hteq : t₀ = ⟨r, hr01⟩ := by
    apply Subtype.ext
    exact htv
  have hce : (ce e t₀ : X) ∈ (fun s : ORI => (cψ ψ s : X)) ''
      {s : ORI | u < (s : ℝ) ∧ (s : ℝ) < v} := ht₀
  have hyW : y ∈ W := by
    -- y = ce e ⟨r, hr01⟩ = ce e t₀ ∈ strip-image ⊆ W
    have hyce : y = ce e ⟨r, hr01⟩ := by
      dsimp [ce, r]
      have h := congrArg (fun z : {x : X // x ∈ P} => (z : X)) (e.apply_symm_apply ⟨y, hy⟩)
      simpa using h
    rw [hyce]
    have hce' : (ce e ⟨r, hr01⟩ : X) ∈ (fun s : ORI => (cψ ψ s : X)) ''
        {s : ORI | u < (s : ℝ) ∧ (s : ℝ) < v} := by
      simpa [hteq] using hce
    rcases hce' with ⟨s, hs, hsc⟩
    have hsW : (cψ ψ s : X) ∈ W := (ψ s : {x : X // x ∈ W}).2
    simpa [hsc] using hsW
  exact hyW

end StripCore

end Commons.Topology.OneManifold



open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace Commons.Topology.OneManifold

/-!
# The no-maximal-proper-open-arc dichotomy (end theory, Layers 1–3)

**Goal of the module** (independent of the L46 classification): prove the
one-dimensional dichotomy

> a connected Hausdorff second-countable locally interval-charted space
> `X` is either homeomorphic to the open unit interval or compact

from the published Commons engine (two-arc gluing with connected overlap,
nested-open-arc unions are open arcs, countable unit-arc covers), by the
maximal-arc exhaustion of the fleet's Layer-3 plan:

* **Layer 1** (`arc_extension_or_compact`, the terminal-extension lemma):
  every PROPER open arc extends to a strictly larger open arc, unless the
  ambient is compact.  [the engine]
* **Layer 2**: nested open-arc unions are open arcs
  (`nested_open_arcs_union_is_open_arc`, published in the Commons).
* **Layer 3**: Zorn maximal-arc assembly of the dichotomy.

This file develops the Layer-1 end analysis bottom-up.  TODAY'S STEP (the
first bullet of the boundary analysis): **boundary points of a proper open
arc lie at the two ends** — a boundary point `z ∈ cl(P) ∖ P` of an open
arc `P` (chart `e : ORI ≃ₜ ↑P`) is a limit point of every initial segment
`e((0,a))` (the LEFT end) or of every terminal segment `e((b,1))` (the
RIGHT end):
`boundary_point_at_arc_end`.

Proof sketch (paper): write `P` as the union of the left tail over `(0,a)`,
the closed middle over `[a,b]` and the right tail over `(b,1)` for any
`0 < a < b < 1`.  The middle piece is the continuous image of the compact
interval `[a,b]`, hence compact, hence closed in the Hausdorff space `X`.
If `z` were not a limit of the left tail (for some `a`) nor of the right
tail (for some `b`), with `a < b`, then `z ∈ cl(P)` would force `z` into
the closed middle piece, i.e. `z ∈ P`, a contradiction. -/

/-- The open real unit interval as a type. -/
abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

namespace ChartVal

variable {X : Type*} [TopologicalSpace X] [T2Space X] {P W : Set X}

/-- The chart coercion ORI → X. -/
def chartVal (e : ORI ≃ₜ {x : X // x ∈ P}) : ORI → X := fun t => (e t : {x : X // x ∈ P}).1

theorem chartVal_continuous (e : ORI ≃ₜ {x : X // x ∈ P}) : Continuous (chartVal e) := by
  exact continuous_subtype_val.comp e.continuous

theorem chartVal_range (e : ORI ≃ₜ {x : X // x ∈ P}) : Set.range (chartVal e) = P := by
  ext y
  constructor
  · rintro ⟨t, rfl⟩
    exact (e t).2
  · intro hy
    refine ⟨e.symm ⟨y, hy⟩, ?_⟩
    have h := congrArg (fun z : {x : X // x ∈ P} => (z : X)) (e.apply_symm_apply ⟨y, hy⟩)
    simpa [chartVal] using h

/-- Sub-arc over the open real interval (lo,hi). -/
def sub (e : ORI ≃ₜ {x : X // x ∈ P}) (lo hi : ℝ) : Set X :=
  chartVal e '' {t : ORI | (t : ℝ) ∈ Set.Ioo lo hi}

/-- Sub-arc over the closed real interval [lo,hi]. -/
def subClosed (e : ORI ≃ₜ {x : X // x ∈ P}) (lo hi : ℝ) : Set X :=
  chartVal e '' {t : ORI | (t : ℝ) ∈ Set.Icc lo hi}

theorem mem_sub (e : ORI ≃ₜ {x : X // x ∈ P}) {x : X} {lo hi : ℝ} :
    x ∈ sub e lo hi ↔ ∃ t : ORI, (t : ℝ) ∈ Set.Ioo lo hi ∧ chartVal e t = x := by
  rfl

theorem mem_subClosed (e : ORI ≃ₜ {x : X // x ∈ P}) {x : X} {lo hi : ℝ} :
    x ∈ subClosed e lo hi ↔ ∃ t : ORI, (t : ℝ) ∈ Set.Icc lo hi ∧ chartVal e t = x := by
  rfl

theorem sub_mono (e : ORI ≃ₜ {x : X // x ∈ P}) {lo lo' hi hi' : ℝ}
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : sub e lo hi ⊆ sub e lo' hi' := by
  intro x hx
  rw [mem_sub] at hx ⊢
  rcases hx with ⟨t, ht, rfl⟩
  refine ⟨t, ⟨lt_of_le_of_lt hlo ht.1, lt_of_lt_of_le ht.2 hhi⟩, rfl⟩

theorem sub_anti_right (e : ORI ≃ₜ {x : X // x ∈ P}) {lo hi hi' : ℝ}
    (hhi : hi ≤ hi') : sub e lo hi ⊆ sub e lo hi' := sub_mono e le_rfl hhi

theorem sub_anti_left (e : ORI ≃ₜ {x : X // x ∈ P}) {lo lo' hi : ℝ}
    (hlo : lo' ≤ lo) : sub e lo hi ⊆ sub e lo' hi := sub_mono e hlo le_rfl

/-- The three-piece decomposition of the arc over (0,1) (0 < a < b < 1). -/
theorem sub_partition (e : ORI ≃ₜ {x : X // x ∈ P}) {a b : ℝ}
    (h0a : 0 < a) (hab : a < b) (hb1 : b < 1) :
    P = sub e 0 a ∪ (subClosed e a b ∪ sub e b 1) := by
  ext x
  constructor
  · intro hx
    have hrange : x ∈ Set.range (chartVal e) := by
      rw [chartVal_range e]
      exact hx
    rcases hrange with ⟨t, rfl⟩
    have ht0 : (0 : ℝ) < (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) < (1 : ℝ) := t.2.2
    by_cases hta : (t : ℝ) < a
    · left
      rw [mem_sub]
      refine ⟨t, ⟨ht0, hta⟩, rfl⟩
    · have ha_le : a ≤ (t : ℝ) := le_of_not_gt hta
      by_cases htb : (t : ℝ) ≤ b
      · right; left
        rw [mem_subClosed]
        refine ⟨t, ⟨ha_le, htb⟩, rfl⟩
      · right; right
        rw [mem_sub]
        refine ⟨t, ⟨lt_of_not_ge htb, ht1⟩, rfl⟩
  · intro hx
    rw [← chartVal_range e]
    rcases hx with hx | hx
    · rw [mem_sub] at hx
      rcases hx with ⟨t, ht, rfl⟩
      refine ⟨t, rfl⟩
    · rcases hx with hx | hx
      · rw [mem_subClosed] at hx
        rcases hx with ⟨t, ht, rfl⟩
        refine ⟨t, rfl⟩
      · rw [mem_sub] at hx
        rcases hx with ⟨t, ht, rfl⟩
        refine ⟨t, rfl⟩

/-- A closed-coordinate sub-arc is closed in X (compact image in a
Hausdorff space). -/
theorem subClosed_isClosed {X : Type*} [TopologicalSpace X] [T2Space X]
    {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {a b : ℝ}
    (h0a : 0 < a) (hb1 : b < 1) : IsClosed (subClosed e a b) := by
  let C := {r : ℝ // r ∈ Set.Icc a b}
  haveI : CompactSpace C := by
    dsimp [C]
    exact isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc a b : Set ℝ))
  have hmem : ∀ r : ℝ, r ∈ Set.Icc a b → r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨lt_of_lt_of_le h0a hr.1, lt_of_le_of_lt hr.2 hb1⟩
  let g : C → X := fun r => chartVal e ⟨(r : ℝ), hmem (r : ℝ) r.2⟩
  have hinner_cont : Continuous (fun r : C => (⟨(r : ℝ), hmem (r : ℝ) r.2⟩ : ORI)) :=
    Continuous.subtype_mk (f := fun r : C => (r : ℝ)) continuous_subtype_val
      (fun r => hmem (r : ℝ) r.2)
  have hg_cont : Continuous g := by
    dsimp [g]
    exact (chartVal_continuous e).comp hinner_cont
  have hg_compact : IsCompact (g '' Set.univ) := IsCompact.image isCompact_univ hg_cont
  have hEq : g '' Set.univ = subClosed e a b := by
    ext y
    constructor
    · rintro ⟨r, -, rfl⟩
      rw [mem_subClosed]
      refine ⟨⟨(r : ℝ), hmem (r : ℝ) r.2⟩, ?_⟩
      constructor
      · exact r.2
      · change chartVal e ⟨(r : ℝ), hmem (r : ℝ) r.2⟩ =
            chartVal e ⟨(r : ℝ), hmem (r : ℝ) r.2⟩
        rfl
    · intro hy
      rcases hy with ⟨s, hs, rfl⟩
      refine ⟨⟨(s : ℝ), hs⟩, trivial, ?_⟩
      dsimp [g]
  rw [← hEq]
  exact hg_compact.isClosed

/-- **Boundary points lie at the ends of the arc**: a boundary point
`z ∈ cl(P)∖P` of an open arc `P` (charted by `e : ORI ≃ₜ ↑P`) lies in the
closure of every initial segment (left end) or in the closure of every
terminal segment (right end). -/
theorem boundary_point_at_arc_end {X : Type*} [TopologicalSpace X] [T2Space X]
    {P : Set X} (e : ORI ≃ₜ {x : X // x ∈ P}) {z : X}
    (hz : z ∈ closure P \ P) :
    (∀ a : ℝ, 0 < a → a < 1 → z ∈ closure (sub e 0 a)) ∨
    (∀ b : ℝ, 0 < b → b < 1 → z ∈ closure (sub e b 1)) := by
  classical
  by_contra h
  push Not at h
  rcases h with ⟨⟨a₀, ha₀₀, ha₀₁, ha₀z⟩, ⟨b₀, hb₀₀, hb₀₁, hb₀z⟩⟩
  -- choose 0 < a < b < 1 with z outside both end-closures
  have habs : ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      z ∉ closure (sub e 0 a) ∧ z ∉ closure (sub e b 1) := by
    by_cases hab₀ : a₀ < b₀
    · refine ⟨a₀, b₀, ha₀₀, hab₀, hb₀₁, ha₀z, hb₀z⟩
    · have hb₀a₀ : b₀ ≤ a₀ := le_of_not_gt hab₀
      by_cases hEq : a₀ = b₀
      · refine ⟨a₀ / 2, a₀, by positivity, by linarith, ha₀₁, ?_, ?_⟩
        · intro hzsmall
          have hsub : sub e 0 (a₀ / 2) ⊆ sub e 0 a₀ := sub_anti_right e (by linarith)
          exact ha₀z (closure_mono hsub hzsmall)
        · simpa [hEq] using hb₀z
      · have hb₀a₀' : b₀ < a₀ := lt_of_le_of_ne hb₀a₀ (by intro hba; exact hEq hba.symm)
        refine ⟨b₀, a₀, hb₀₀, hb₀a₀', ha₀₁, ?_, ?_⟩
        · intro hzsmall
          have hsub : sub e 0 b₀ ⊆ sub e 0 a₀ := sub_anti_right e (le_of_lt hb₀a₀')
          exact ha₀z (closure_mono hsub hzsmall)
        · intro hzlarge
          have hsub : sub e a₀ 1 ⊆ sub e b₀ 1 := sub_anti_left e (le_of_lt hb₀a₀')
          exact hb₀z (closure_mono hsub hzlarge)
  rcases habs with ⟨a, b, ha₀, hab, hb₁, haz, hbz⟩
  -- partition and closed middle piece
  have hPpart : P = sub e 0 a ∪ (subClosed e a b ∪ sub e b 1) :=
    sub_partition e ha₀ hab hb₁
  have hzmid : z ∉ subClosed e a b := by
    intro hzm
    exact hz.2 (by rw [hPpart]; exact Or.inr (Or.inl hzm))
  have hclU : closure (sub e 0 a ∪ (subClosed e a b ∪ sub e b 1)) =
      closure (sub e 0 a) ∪ (subClosed e a b ∪ closure (sub e b 1)) := by
    rw [closure_union, closure_union]
    rw [closure_eq_iff_isClosed.mpr (subClosed_isClosed e ha₀ hb₁)]
  have hPsub : P ⊆ sub e 0 a ∪ (subClosed e a b ∪ sub e b 1) := by
    intro x hx
    rw [hPpart] at hx
    exact hx
  have hclcover : closure P ⊆
      closure (sub e 0 a) ∪ (subClosed e a b ∪ closure (sub e b 1)) := by
    intro x hx
    have hx' : x ∈ closure (sub e 0 a ∪ (subClosed e a b ∪ sub e b 1)) :=
      closure_mono hPsub hx
    rw [hclU] at hx'
    exact hx'
  have hzcl : z ∈ closure (sub e 0 a) ∪ (subClosed e a b ∪ closure (sub e b 1)) :=
    hclcover hz.1
  rcases hzcl with hzcl | hzcl
  · exact haz hzcl
  · rcases hzcl with hzcl | hzcl
    · exact hzmid hzcl
    · exact hbz hzcl

/-- The chart coercion is injective. -/
theorem chartVal_injective (e : ORI ≃ₜ {x : X // x ∈ P}) :
    Function.Injective (chartVal e) := by
  intro t u h
  change (e t : {x : X // x ∈ P}).1 = (e u : {x : X // x ∈ P}).1 at h
  have : e t = e u := by
    apply Subtype.ext
    exact h
  exact e.injective this

/-- The sub-arc of an OPEN chart-arc over an open real interval is open
in `X` (the chart coercion is an open map when the chart's set is open). -/
theorem sub_isOpen (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hW : IsOpen W) (u v : ℝ) :
    IsOpen (sub ψ u v) := by
  have hValOpen : IsOpenMap (chartVal ψ) := by
    change IsOpenMap (fun t : ORI => ((ψ t : {x : X // x ∈ W}) : X))
    exact hW.isOpenMap_subtype_val.comp ψ.isOpenMap
  have hD : IsOpen ({t : ORI | (t : ℝ) ∈ Set.Ioo u v} : Set ORI) := by
    exact IsOpen.preimage (f := fun t : ORI => (t : ℝ))
      continuous_subtype_val (isOpen_Ioo : IsOpen (Set.Ioo u v))
  simpa [sub] using hValOpen {t : ORI | (t : ℝ) ∈ Set.Ioo u v} hD

/-- The coordinate-strip subtype of `ORI` over `(u,v) ⊆ (0,1)` is
homeomorphic (by the value map) to the real interval `(u,v)`. -/
theorem valueInterval_homeo {u v : ℝ} (hu0 : 0 ≤ u) (hv1 : v ≤ 1) :
    Nonempty ({t : ORI // (t : ℝ) ∈ Set.Ioo u v} ≃ₜ {r : ℝ // r ∈ Set.Ioo u v}) := by
  let vm : ORI → ℝ := fun t => (t : ℝ)
  have hv_emb : Topology.IsEmbedding vm := by
    dsimp [vm]
    exact Topology.IsEmbedding.subtypeVal (p := fun r : ℝ => r ∈ Set.Ioo (0 : ℝ) 1)
  have hmem : ∀ r : ℝ, r ∈ Set.Ioo u v → r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨lt_of_le_of_lt hu0 hr.1, lt_of_lt_of_le hr.2 hv1⟩
  let s : Set ORI := {t : ORI | (t : ℝ) ∈ Set.Ioo u v}
  have h1 : (s : Type) ≃ₜ {r : ℝ // r ∈ vm '' s} := by
    simpa using (hv_emb.homeomorphImage s)
  have hIm : vm '' s = Set.Ioo u v := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hr
      refine ⟨⟨r, hmem r hr⟩, hr, rfl⟩
  have h2 : {r : ℝ // r ∈ vm '' s} ≃ₜ {r : ℝ // r ∈ Set.Ioo u v} :=
    Homeomorph.setCongr hIm
  exact ⟨h1.trans h2⟩

/-- The sub-arc of a chart-arc over `(u,v) ⊆ (0,1)` is itself an open arc
(homeomorphic to the open unit interval). -/
theorem sub_arc (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {u v : ℝ} (hu0 : 0 ≤ u) (huv : u < v) (hv1 : v ≤ 1) :
    Nonempty (ORI ≃ₜ (sub ψ u v)) := by
  let s : Set ORI := {t : ORI | (t : ℝ) ∈ Set.Ioo u v}
  have hemb : Topology.IsEmbedding (chartVal ψ) := by
    change Topology.IsEmbedding (fun t : ORI => ((ψ t : {x : X // x ∈ W}) : X))
    exact Topology.IsEmbedding.comp
      (Topology.IsEmbedding.subtypeVal (p := fun x : X => x ∈ W))
      (Homeomorph.isEmbedding ψ)
  have h1 : (s : Type) ≃ₜ {x : X // x ∈ chartVal ψ '' s} :=
    hemb.homeomorphImage s
  rcases valueInterval_homeo (u := u) (v := v) hu0 hv1 with ⟨h2⟩
  rcases (Commons.Topology.Homeomorph.open_interval_affine (a := u) (b := v)
      (c := 0) (d := 1) huv (by norm_num)) with ⟨h3⟩
  exact ⟨(h1.symm.trans (h2.trans h3)).symm⟩

/-- **Layer-1 step (i) — clean one-sided strip ⇒ extension.**  Let `P` be
an open arc of `X` and `W` an open arc-chart at the boundary (chart
`ψ : ORI ≃ₜ ↑W`).  Suppose `P` fills the whole coordinate strip to the
RIGHT of `c₀` (`(c₀, c₀+δᵣ)` ⊆ the `P`-coordinates of `W`) while `P`
avoids the coordinate interval `(c₀−δₗ, c₀)` to the LEFT, and the point
at coordinate `c₀` is not in `P`.  Then `P` extends to a strictly larger
open arc `Q = P ∪ ψ⁻¹((c₀−δₗ, c₀+δᵣ))`.

Proof: `V := ψ⁻¹((c₀−δₗ, c₀+δᵣ))` is an open arc (`sub_arc`); its
overlap with `P` is exactly the connected strip `ψ⁻¹((c₀, c₀+δᵣ))`; the
two-arc gluing theorem (`union_two_open_arcs_connected_overlap_interval`)
glues `P` and `V` into an open arc strictly larger than `P` (the left
half of `V` is fresh: it meets no point of `P`). -/
theorem arc_extension_of_right_strip
    (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δᵣ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ) (hδᵣ₁ : c₀ + δᵣ ≤ 1)
    (hδₗ₀ : 0 < δₗ) (hδₗ₀b : 0 ≤ c₀ - δₗ)
    (hzc : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P)
    (hPright : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∈ P)
    (hPleft : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (chartVal ψ t : X) ∉ P) :
    ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q) := by
  let u : ℝ := c₀ - δₗ
  let v : ℝ := c₀ + δᵣ
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hv1 : v ≤ 1 := by dsimp [v]; exact hδᵣ₁
  -- the overlap of P with V = ψ⁻¹((u,v)) is exactly the right strip
  have hOver : P ∩ sub ψ u v = sub ψ c₀ (c₀ + δᵣ) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxP, hxV⟩
      rw [mem_sub] at hxV
      rcases hxV with ⟨t, ht, rfl⟩
      have htu : c₀ - δₗ < (t : ℝ) := by simpa [u] using ht.1
      by_cases htc : (t : ℝ) < c₀
      · exfalso
        exact hPleft t htu htc hxP
      · have hc₀t : c₀ ≤ (t : ℝ) := le_of_not_gt htc
        by_cases ht₀ : c₀ = (t : ℝ)
        · exfalso
          have htEq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
            apply Subtype.ext
            exact ht₀.symm
          exact hzc (by simpa [htEq] using hxP)
        · have hc₀t' : c₀ < (t : ℝ) := lt_of_le_of_ne hc₀t ht₀
          rw [mem_sub]
          refine ⟨t, ⟨hc₀t', ?_⟩, rfl⟩
          have htv : (t : ℝ) < c₀ + δᵣ := by simpa [v] using ht.2
          exact htv
    · intro hx
      rw [mem_sub] at hx
      rcases hx with ⟨t, ht, rfl⟩
      constructor
      · exact hPright t ht.1 ht.2
      · rw [mem_sub]
        refine ⟨t, ⟨?_, ?_⟩, rfl⟩
        · show u < (t : ℝ)
          have h1 : u < c₀ := by dsimp [u]; linarith
          exact lt_trans h1 ht.1
        · show (t : ℝ) < v
          simpa [v] using ht.2
  -- ConnectedSpace of the overlap subtype (homeomorphic to the unit interval)
  have hconn : ConnectedSpace {x : X // x ∈ P ∩ sub ψ u v} := by
    rcases sub_arc ψ (le_of_lt hc₀₀) (by linarith) hδᵣ₁ with ⟨hO⟩
    have hOv : {x : X // x ∈ P ∩ sub ψ u v} ≃ₜ {x : X // x ∈ sub ψ c₀ (c₀ + δᵣ)} :=
      Homeomorph.setCongr hOver
    have hTot : ORI ≃ₜ {x : X // x ∈ P ∩ sub ψ u v} := hO.trans hOv.symm
    exact (hTot.connectedSpace_iff).mp ori_connected
  -- glue P with V along the connected strip
  rcases (union_two_open_arcs_connected_overlap_interval (X := X) (U := P)
      (V := (sub ψ u v)) hPopen (sub_isOpen ψ hWopen u v) eP
      (sub_arc ψ hu0 huv hv1) hconn) with ⟨eglue⟩
  -- a fresh witness in V ∖ P
  let w : ℝ := c₀ - δₗ / 2
  have hw₀ : 0 < w := by dsimp [w]; linarith
  have hw₁ : w < 1 := by dsimp [w]; linarith
  have huw : u < w := by dsimp [u, w]; linarith
  have hwc : w < c₀ := by dsimp [w]; linarith
  let tw : ORI := ⟨w, ⟨hw₀, hw₁⟩⟩
  let y : X := chartVal ψ tw
  have hyNotP : y ∉ P := by
    dsimp [y, tw]
    exact hPleft ⟨w, ⟨hw₀, hw₁⟩⟩ huw hwc
  have hyV : y ∈ sub ψ u v := by
    rw [mem_sub]
    refine ⟨tw, ?_, rfl⟩
    dsimp [u, v]
    exact ⟨huw, by linarith⟩
  refine ⟨P ∪ sub ψ u v, IsOpen.union hPopen (sub_isOpen ψ hWopen u v), ?_, ⟨eglue⟩⟩
  constructor
  · intro x hx
    exact Or.inl hx
  · intro hQsub
    have hyUnion : y ∈ P ∪ sub ψ u v := Or.inr hyV
    exact hyNotP (hQsub hyUnion)

/-- **Layer-1 step (ii) — a maximal open arc has NO right-strip boundary
point.**  If `P` is a maximal open arc (no strictly larger open arc
exists) and an open arc-chart `ψ` of `W` shows that `P` fills the whole
coordinate strip to the right of `c₀` while avoiding the strip to the
left, then `arc_extension_of_right_strip` would extend `P` — contradiction. -/
theorem maximal_no_right_strip_boundary
    (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δᵣ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ) (hδᵣ₁ : c₀ + δᵣ ≤ 1)
    (hδₗ₀ : 0 < δₗ) (hδₗ₀b : 0 ≤ c₀ - δₗ)
    (hzc : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P)
    (hPright : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∈ P)
    (hPleft : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (chartVal ψ t : X) ∉ P) : False := by
  exact hPmax (arc_extension_of_right_strip eP hPopen ψ hWopen
    hc₀₀ hc₀₁ hδᵣ₀ hδᵣ₁ hδₗ₀ hδₗ₀b hzc hPright hPleft)

/-- **Layer-1 step (ii), mirror — the LEFT-strip extension.**  If `P`
fills the whole coordinate strip to the LEFT of `c₀` while avoiding the
strip to the right, then `P` extends (glue over the left strip; the right
half of the window is fresh). -/
theorem arc_extension_of_left_strip
    (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δᵣ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ) (hδᵣ₁ : c₀ + δᵣ ≤ 1)
    (hδₗ₀ : 0 < δₗ) (hδₗ₀b : 0 ≤ c₀ - δₗ)
    (hzc : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P)
    (hPleftfull : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (chartVal ψ t : X) ∈ P)
    (hPrightempty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∉ P) :
    ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q) := by
  let u : ℝ := c₀ - δₗ
  let v : ℝ := c₀ + δᵣ
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have huv : u < v := by dsimp [u, v]; linarith
  have hv1 : v ≤ 1 := by dsimp [v]; exact hδᵣ₁
  -- the overlap of P with V = ψ⁻¹((u,v)) is exactly the LEFT strip
  have hOver : P ∩ sub ψ u v = sub ψ (c₀ - δₗ) c₀ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxP, hxV⟩
      rw [mem_sub] at hxV
      rcases hxV with ⟨t, ht, rfl⟩
      have htv : (t : ℝ) < c₀ + δᵣ := by simpa [v] using ht.2
      by_cases htc : c₀ < (t : ℝ)
      · exfalso
        exact hPrightempty t htc htv hxP
      · have ht₀c : (t : ℝ) ≤ c₀ := le_of_not_gt htc
        by_cases ht₀ : c₀ = (t : ℝ)
        · exfalso
          have htEq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
            apply Subtype.ext
            exact ht₀.symm
          exact hzc (by simpa [htEq] using hxP)
        · have ht₀c' : (t : ℝ) < c₀ := lt_of_lt_of_le (lt_of_le_of_ne ht₀c (fun hEq => ht₀ hEq.symm)) (le_rfl)
          rw [mem_sub]
          refine ⟨t, ⟨(by simpa [u] using ht.1), ht₀c'⟩, rfl⟩
    · intro hx
      rw [mem_sub] at hx
      rcases hx with ⟨t, ht, rfl⟩
      constructor
      · exact hPleftfull t ht.1 ht.2
      · rw [mem_sub]
        refine ⟨t, ⟨?_, ?_⟩, rfl⟩
        · show u < (t : ℝ)
          simpa [u] using ht.1
        · show (t : ℝ) < v
          have h1 : c₀ < v := by dsimp [v]; linarith
          exact lt_trans ht.2 h1
  -- ConnectedSpace of the overlap subtype
  have hconn : ConnectedSpace {x : X // x ∈ P ∩ sub ψ u v} := by
    rcases sub_arc ψ hδₗ₀b (by linarith) (le_of_lt hc₀₁) with ⟨hO⟩
    have hOv : {x : X // x ∈ P ∩ sub ψ u v} ≃ₜ
        {x : X // x ∈ sub ψ (c₀ - δₗ) c₀} := Homeomorph.setCongr hOver
    have hTot : ORI ≃ₜ {x : X // x ∈ P ∩ sub ψ u v} := hO.trans hOv.symm
    exact (hTot.connectedSpace_iff).mp ori_connected
  -- glue P with V along the connected strip
  rcases (union_two_open_arcs_connected_overlap_interval (X := X) (U := P)
      (V := (sub ψ u v)) hPopen (sub_isOpen ψ hWopen u v) eP
      (sub_arc ψ hu0 huv hv1) hconn) with ⟨eglue⟩
  -- a fresh witness in V ∖ P (the right half of the window)
  let w : ℝ := c₀ + δᵣ / 2
  have hw₀ : 0 < w := by dsimp [w]; linarith
  have hw₁ : w < 1 := by dsimp [w]; linarith
  have hcw : c₀ < w := by dsimp [w]; linarith
  have hwv : w < v := by dsimp [v, w]; linarith
  let tw : ORI := ⟨w, ⟨hw₀, hw₁⟩⟩
  let y : X := chartVal ψ tw
  have hyNotP : y ∉ P := by
    dsimp [y, tw]
    have hw2 : w < c₀ + δᵣ := by dsimp [w]; linarith
    exact hPrightempty ⟨w, ⟨hw₀, hw₁⟩⟩ hcw hw2
  have hyV : y ∈ sub ψ u v := by
    rw [mem_sub]
    refine ⟨tw, ?_, rfl⟩
    dsimp [u, v]
    exact ⟨(by linarith), hwv⟩
  refine ⟨P ∪ sub ψ u v, IsOpen.union hPopen (sub_isOpen ψ hWopen u v), ?_, ⟨eglue⟩⟩
  constructor
  · intro x hx
    exact Or.inl hx
  · intro hQsub
    have hyUnion : y ∈ P ∪ sub ψ u v := Or.inr hyV
    exact hyNotP (hQsub hyUnion)

/-- **Layer-1 step (ii), mirror — a maximal open arc has NO left-strip
boundary point.** -/
theorem maximal_no_left_strip_boundary
    (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δᵣ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ) (hδᵣ₁ : c₀ + δᵣ ≤ 1)
    (hδₗ₀ : 0 < δₗ) (hδₗ₀b : 0 ≤ c₀ - δₗ)
    (hzc : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P)
    (hPleftfull : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (chartVal ψ t : X) ∈ P)
    (hPrightempty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∉ P) : False := by
  exact hPmax (arc_extension_of_left_strip eP hPopen ψ hWopen
    hc₀₀ hc₀₁ hδᵣ₀ hδᵣ₁ hδₗ₀ hδₗ₀b hzc hPleftfull hPrightempty)

/-- **Layer-1 step (iii) — one-sided boundary points of a maximal arc are
impossible (right orientation).**  If a boundary chart of a maximal open
arc `P` shows a FULL coordinate strip of `P` to the right of `c₀`, then
`P` must have points of the chart arbitrarily close to `c₀` on the LEFT
as well: a left-avoided window would let `maximal_no_right_strip_boundary`
extend `P`.  Contrapositive form of `maximal_no_right_strip_boundary`. -/
theorem maximal_rightfull_left_dense
    (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δᵣ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ) (hδᵣ₁ : c₀ + δᵣ ≤ 1)
    (hzc : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P)
    (hPright : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∈ P) :
    ∀ δₗ : ℝ, 0 < δₗ → 0 ≤ c₀ - δₗ →
      ∃ t : ORI, c₀ - δₗ < (t : ℝ) ∧ (t : ℝ) < c₀ ∧ (chartVal ψ t : X) ∈ P := by
  intro δₗ hδₗ₀ hδₗb
  by_contra h
  have hPleft : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (chartVal ψ t : X) ∉ P := by
    intro t h1 h2 hmem
    exact h ⟨t, h1, h2, hmem⟩
  exact maximal_no_right_strip_boundary eP hPopen hPmax ψ hWopen
    hc₀₀ hc₀₁ hδᵣ₀ hδᵣ₁ hδₗ₀ hδₗb hzc hPright hPleft

/-- **Layer-1 step (iii) — one-sided boundary points of a maximal arc are
impossible (left orientation).**  If a boundary chart of a maximal open
arc `P` shows a FULL coordinate strip of `P` to the LEFT of `c₀`, then
`P` must have points of the chart arbitrarily close to `c₀` on the RIGHT
as well.  Contrapositive form of `maximal_no_left_strip_boundary`. -/
theorem maximal_leftfull_right_dense
    (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδₗ₀ : 0 < δₗ) (hδₗ₀b : 0 ≤ c₀ - δₗ)
    (hzc : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P)
    (hPleftfull : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (chartVal ψ t : X) ∈ P) :
    ∀ δᵣ : ℝ, 0 < δᵣ → c₀ + δᵣ ≤ 1 →
      ∃ t : ORI, c₀ < (t : ℝ) ∧ (t : ℝ) < c₀ + δᵣ ∧ (chartVal ψ t : X) ∈ P := by
  intro δᵣ hδᵣ₀ hδᵣ₁
  by_contra h
  have hPrightempty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∉ P := by
    intro t h1 h2 hmem
    exact h ⟨t, h1, h2, hmem⟩
  exact maximal_no_left_strip_boundary eP hPopen hPmax ψ hWopen
    hc₀₀ hc₀₁ hδᵣ₀ hδᵣ₁ hδₗ₀ hδₗ₀b hzc hPleftfull hPrightempty


/-- **Positive-gap exclusion for maximal arcs.**  A maximal open arc has
no boundary-chart pattern of the form "P fills the coordinate strip
`(lo, mid)` and avoids `(mid, hi)` while the point at coordinate `mid`
is not in `P`": such a pattern is exactly the left-strip extension shape
(`arc_extension_of_left_strip`), which would strictly enlarge `P`.  This
is the first exclusion step against oscillatory boundary behaviour:
oscillation through components with POSITIVE gaps is impossible for a
maximal arc. -/
theorem maximal_no_gap_strip
    (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {lo mid hi : ℝ} (hlo0 : 0 ≤ lo) (hlom : lo < mid)
    (hmih : mid < hi) (hhi1 : hi ≤ 1)
    (hmidnot : (chartVal ψ ⟨mid,
      ⟨lt_of_le_of_lt hlo0 hlom, lt_of_lt_of_le hmih hhi1⟩⟩) ∉ P)
    (hfill : ∀ t : ORI, lo < (t : ℝ) → (t : ℝ) < mid →
      (chartVal ψ t : X) ∈ P)
    (hgap : ∀ t : ORI, mid < (t : ℝ) → (t : ℝ) < hi →
      (chartVal ψ t : X) ∉ P) : False := by
  let c₀ : ℝ := mid
  let δₗ : ℝ := mid - lo
  let δᵣ : ℝ := hi - mid
  have hc₀₀ : 0 < c₀ := by dsimp [c₀]; linarith
  have hc₀₁ : c₀ < 1 := by dsimp [c₀]; linarith
  have hδᵣ₀ : 0 < δᵣ := by dsimp [δᵣ]; linarith
  have hδᵣ₁ : c₀ + δᵣ ≤ 1 := by dsimp [c₀, δᵣ]; linarith
  have hδₗ₀ : 0 < δₗ := by dsimp [δₗ]; linarith
  have hδₗ₀b : 0 ≤ c₀ - δₗ := by dsimp [c₀, δₗ]; linarith
  have hzc : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P := by
    dsimp [c₀]
    convert hmidnot using 1
  have hPleftfull : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (chartVal ψ t : X) ∈ P := by
    intro t h1 h2
    dsimp [c₀, δₗ] at h1 h2
    exact hfill t (by linarith) h2
  have hPrightempty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∉ P := by
    intro t h1 h2
    dsimp [c₀, δᵣ] at h1 h2
    exact hgap t h1 (by linarith)
  exact maximal_no_left_strip_boundary eP hPopen hPmax ψ hWopen
    hc₀₀ hc₀₁ hδᵣ₀ hδᵣ₁ hδₗ₀ hδₗ₀b hzc hPleftfull hPrightempty


/-- **Open maps pull closures back into closures**: if `f` is an open map
and `f x ∈ closure B`, then `x ∈ closure (f ⁻¹' B)`.  (Every open
neighbourhood of `x` maps to an open neighbourhood of `f x`, which meets
`B`.) -/
theorem openMap_preimage_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : IsOpenMap f) {B : Set Y} : f ⁻¹' closure B ⊆ closure (f ⁻¹' B) := by
  intro x hx
  have hx' : ∀ o : Set Y, IsOpen o → f x ∈ o → (o ∩ B).Nonempty := (mem_closure_iff).mp hx
  exact (mem_closure_iff).mpr (by
    intro U hU hxU
    have hfU : IsOpen (f '' U) := hf U hU
    have hfx : f x ∈ f '' U := ⟨x, hxU, rfl⟩
    rcases hx' (f '' U) hfU hfx with ⟨y, hyfU, hyB⟩
    rcases hyfU with ⟨a, haU, haf⟩
    refine ⟨a, haU, ?_⟩
    change f a ∈ B
    rw [haf]
    exact hyB)

/-- The chart coercion of an OPEN chart-arc is an open map into `X`. -/
theorem chartVal_isOpenMap (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W) :
    IsOpenMap (chartVal ψ) := by
  change IsOpenMap (fun t : ORI => ((ψ t : {x : X // x ∈ W}) : X))
  exact hWopen.isOpenMap_subtype_val.comp ψ.isOpenMap

/-- **Closure bridge (coordinate form).**  If the point at coordinate
`c₀` of the open chart-arc `W` lies in `closure P`, then the coordinate
`⟨c₀, _⟩` lies in the closure (inside `ORI`) of the set of coordinates of
`P`-points of the chart, `{t : ORI | chartVal ψ t ∈ P}`.  The chart
coercion is an open map (the chart's set is open), so open maps pull
closures back (`openMap_preimage_closure`). -/
theorem coord_mem_closure_of_mem_closure (ψ : ORI ≃ₜ {x : X // x ∈ W})
    (hWopen : IsOpen W) {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P) :
    ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure ({t : ORI | chartVal ψ t ∈ P} : Set ORI) := by
  have hf : IsOpenMap (chartVal ψ) := chartVal_isOpenMap ψ hWopen
  have hz' : ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ (chartVal ψ) ⁻¹' closure P := hz
  exact (openMap_preimage_closure (chartVal ψ) hf) hz'

/-- **Left density from an empty right window (the closure-bridge
consequence).**  Let the boundary point `z` at coordinate `c₀` of the
open chart-arc `W` lie in `closure P ∖ P`.  If `P` avoids the whole right
window `(c₀, c₀+δᵣ)` of the chart, then `P` has points of the chart
arbitrarily close to `c₀` on the LEFT: for every `δₗ > 0` there is a
`P`-point with coordinate in `(c₀−δₗ, c₀)`.  (Coordinates of `P`-points
accumulate at `c₀` by the bridge; none can lie in the right window or at
`c₀` itself, so they must accumulate from the left.) -/
theorem left_dense_of_mem_closure_right_empty (ψ : ORI ≃ₜ {x : X // x ∈ W})
    (hWopen : IsOpen W) {c₀ δᵣ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ)
    (hz : (chartVal ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P)
    (hrightEmpty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (chartVal ψ t : X) ∉ P) :
    ∀ δₗ : ℝ, 0 < δₗ →
      ∃ t : ORI, c₀ - δₗ < (t : ℝ) ∧ (t : ℝ) < c₀ ∧ (chartVal ψ t : X) ∈ P := by
  intro δₗ hδₗ₀
  have hS : ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure
      ({t : ORI | chartVal ψ t ∈ P} : Set ORI) :=
    coord_mem_closure_of_mem_closure ψ hWopen hc₀₀ hc₀₁ hz.1
  have hS' : ∀ o : Set ORI, IsOpen o → ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ o →
      (o ∩ {t : ORI | chartVal ψ t ∈ P}).Nonempty :=
    (mem_closure_iff).mp hS
  let A : Set ORI := {t : ORI | c₀ - δₗ < (t : ℝ) ∧ (t : ℝ) < c₀ + δᵣ}
  have hAopen : IsOpen A := by
    dsimp [A]
    exact IsOpen.preimage (f := fun t : ORI => (t : ℝ)) continuous_subtype_val
      (isOpen_Ioo : IsOpen (Set.Ioo (c₀ - δₗ) (c₀ + δᵣ)))
  have hAc₀ : ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ A := by
    dsimp [A]
    exact ⟨by linarith, by linarith⟩
  rcases hS' A hAopen hAc₀ with ⟨t, htA, htS⟩
  have hP : chartVal ψ t ∈ P := htS
  have htc : (t : ℝ) < c₀ := by
    by_contra hge
    have hc₀t : c₀ ≤ (t : ℝ) := le_of_not_gt hge
    by_cases ht₀ : c₀ = (t : ℝ)
    · exfalso
      have htEq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        apply Subtype.ext
        exact ht₀.symm
      exact hz.2 (by simpa [htEq] using hP)
    · exfalso
      have hc₀t' : c₀ < (t : ℝ) := lt_of_le_of_ne hc₀t ht₀
      exact hrightEmpty t hc₀t' htA.2 hP
  refine ⟨t, htA.1, ?_⟩
  exact ⟨htc, hP⟩

/-! ### Status of the boundary analysis (steps (i)–(iii))

Together with `boundary_point_at_arc_end`, the lemmas above establish the
first half of the one-sided/two-sided dichotomy at boundary points of
*maximal* open arcs:

* a maximal open arc has NO right-strip one-sided boundary point
  (`maximal_no_right_strip_boundary`) and NO left-strip one-sided boundary
  point (`maximal_no_left_strip_boundary`): any full coordinate strip on
  one side forces `P`-points arbitrarily close on the other side
  (`maximal_rightfull_left_dense`, `maximal_leftfull_right_dense`).

What remains for the *local* boundary structure of a maximal arc is the
exclusion of the oscillatory regime: a boundary point at which `P` meets
the chart only in infinitely many tiny components accumulating at `c₀`
from ONE side (no full strip on either side) must be impossible for a
maximal arc.  That exclusion is the "no-infinite-oscillation" content
(the project-wide T2 principle), and together with the two-sided regime it
produces the circle/compact structure used by the Zorn Layer-3 assembly. -/

end ChartVal
end Commons.Topology.OneManifold

open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

/-!
# boundary_extension — a right-empty boundary window forces an extension

**Target (master lemma `boundary_right_empty_extends`)**:  let `P` be an
open arc (chart `eP`) and `W` an open arc-chart at a boundary point
`z := ψ⟨c₀⟩ ∈ closure P ∖ P`; if the whole right window
`(c₀, c₀+δᵣ)` of the chart contains no `P`-points, then `P` extends to a
strictly larger open arc `Q`.

**Two regimes** (matching the shape of `P∩W` near `z` from the left):
1. a FULL left strip `(c₀−δₗ, c₀)` of `P`-points — the two-arc gluing
   extension (`ChartVal.arc_extension_of_left_strip`, verified);
2. NO full left strip — then left-density (`ChartVal.
   left_dense_of_mem_closure_right_empty`, verified) forces an interior
   coordinate strip `(a,b)` (`0 < a < b < c₀`, holes at both ends, filled),
   by the pure real-analysis lemma
   `Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full`
   (fleet L56, VERIFIED); `StripCore.interior_strip_forces_subset`
   (VERIFIED) then gives `P ⊆ W`, and `extends_of_contained_in_arc_chart`
   (verified) extends via `Q := W`.

**Mirror** (`boundary_left_empty_extends`, VERIFIED): the same dichotomy
with the roles of left/right exchanged — empty LEFT window `(c₀−δₗ, c₀)` of
the boundary chart ⇒ extension; Regime 1 uses the verified mirror gluing
`ChartVal.arc_extension_of_right_strip`, Regime 2 uses the mirror density
`right_dense_of_mem_closure_left_empty` (proved here by porting the left
version) and the right-side real-analysis lemma
`Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full_right`
(fleet L57, VERIFIED).

STATUS: verified engine + open global assembly.  Verified (no sorries):
the one-sided extension theorems `boundary_right_empty_extends`,
`boundary_left_empty_extends`; the two-sided local rigidity
`maximal_boundary_two_sided_structure` (`P∩W = W∖{z}`); the per-point
isolating charts `boundary_points_isolated_of_maximal`; density
`maximal_arc_dense` (`cl P = X`); and the re-homed chart layer
(`Submission.Work...arc_chart_tools`, pure Mathlib).  The two endpoint
halves `boundary_point_attracts_left_end` / `_right_end` are PROVED by the
fleet (L60, L61) and committed to the commons.  VERIFIED this session:
`exists_boundary_attracts_both_ends` (every boundary point of a maximal
arc attracts both ends).  OPEN sorries (2): `maximal_arc_ends_close`
(only the UNIQUENESS conjunct `∂P = {z₀}` remains — clean proof found,
see the module note) and the global compact branch
`no_extension_of_proper_open_arc_implies_compact` (assembly from the
uniqueness + tail-convergence + continuous image of `[0,1]`).
-/

namespace BdryExt

variable {X : Type*} [TopologicalSpace X] [T2Space X] {P W : Set X}

/-- The chart coercion (as in ChartVal). -/
abbrev cv (ψ : ORI ≃ₜ {x : X // x ∈ W}) : ORI → X := ChartVal.chartVal ψ

/-- An open arc-chart is an open arc. -/
lemma arc_of_chart (ψ : ORI ≃ₜ {x : X // x ∈ W}) : Nonempty (ORI ≃ₜ W) := ⟨ψ⟩

/-- **Regime 2 bridge**: if the open arc `P` is contained in an open
arc-chart `W` that contains a point of `W ∖ P` (a witness that `W` is
strictly bigger), then `P` extends — `Q := W`. -/
theorem extends_of_contained_in_arc_chart (eP : Nonempty (ORI ≃ₜ P))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    (hPsub : P ⊆ W) (hWnotP : ∃ x : X, x ∈ W ∧ x ∉ P) :
    ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q) := by
  refine ⟨W, hWopen, ?_, arc_of_chart ψ⟩
  constructor
  · exact hPsub
  · rintro hWsubP
    rcases hWnotP with ⟨x, hxW, hxP⟩
    exact hxP (hWsubP hxW)

/-- The coordinate set of the overlap `P∩W` inside `W`: `S = {t : ORI |
chartVal ψ t ∈ P}` as real coordinates. -/
def coordSet (ψ : ORI ≃ₜ {x : X // x ∈ W}) (P : Set X) : Set ℝ :=
  ((↑) : ORI → ℝ) '' {t : ORI | cv ψ t ∈ P}

/-- coordSet is open in ℝ (coordinates of an open overlap through an open
chart). -/
lemma coordSet_isOpen (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    (hPopen : IsOpen P) : IsOpen (coordSet ψ P) := by
  have hpre : IsOpen {t : ORI | cv ψ t ∈ P} := by
    have hcont : Continuous (cv ψ) := by
      change Continuous (fun t : ORI => ((ψ t : {x : X // x ∈ W}) : X))
      exact continuous_subtype_val.comp ψ.continuous
    exact hPopen.preimage hcont
  have hValOpen : IsOpenMap (fun t : ORI => (t : ℝ)) := by
    change IsOpenMap (Subtype.val : {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} → ℝ)
    exact (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1 : Set ℝ)).isOpenMap_subtype_val
  rw [coordSet]
  exact hValOpen {t : ORI | cv ψ t ∈ P} hpre

/-- Membership of a coordinate in coordSet ⟺ the chart point is in P. -/
lemma coordSet_mem_coord (ψ : ORI ≃ₜ {x : X // x ∈ W}) (t : ORI) :
    (t : ℝ) ∈ coordSet ψ P ↔ cv ψ t ∈ P := by
  constructor
  · intro hx
    rcases hx with ⟨t₀, ht₀, htv⟩
    have ht₀eq : t₀ = t := by
      apply Subtype.ext
      exact htv
    simpa [ht₀eq] using ht₀
  · intro hp
    exact ⟨t, hp, rfl⟩

/-- The real-coordinate hole `a ∉ coordSet` (with `a ∈ (0,1)`) means the
chart point at coordinate `a` is not in P. -/
lemma coord_hole_of_not_mem (ψ : ORI ≃ₜ {x : X // x ∈ W}) {a : ℝ}
    (ha01 : a ∈ Set.Ioo (0 : ℝ) 1) (hnot : a ∉ coordSet ψ P) :
    (cv ψ ⟨a, ha01.1, ha01.2⟩ : X) ∉ P := by
  intro hp
  exact hnot ((coordSet_mem_coord ψ ⟨a, ha01.1, ha01.2⟩).mpr hp)

/-- Left density of P-coordinates (chart form, verified) is left density of
the coordinate set (real form). -/
lemma left_dense_coordSet (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    (hPopen : IsOpen P) {c₀ δᵣ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P)
    (hrightEmpty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (cv ψ t : X) ∉ P) :
    ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ coordSet ψ P ∧ c₀ - ε < x ∧ x < c₀ := by
  intro ε hε
  have hleft := ChartVal.left_dense_of_mem_closure_right_empty ψ hWopen hc₀₀ hc₀₁ hδᵣ₀
    hz hrightEmpty ε hε
  rcases hleft with ⟨t, ht1, ht2, htP⟩
  exact ⟨(t : ℝ), (coordSet_mem_coord ψ t).mpr htP, ht1, ht2⟩

/-- A coordinate full strip implies a chart full strip (contrapositive
direction used to pass the no-full hypothesis to the real-analysis lemma). -/
lemma no_full_chart_of_no_full_coord (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₁ : c₀ < 1)
    (hcoord : ¬ ∃ b : ℝ, b < c₀ ∧ 0 ≤ b ∧ Set.Ioo b c₀ ⊆ coordSet ψ P) :
    ¬ ∃ δₗ : ℝ, 0 < δₗ ∧ 0 ≤ c₀ - δₗ ∧
      ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ → (cv ψ t : X) ∈ P := by
  intro hchart
  rcases hchart with ⟨δₗ, hδₗ₀, hδₗb, hPleftfull⟩
  apply hcoord
  refine ⟨c₀ - δₗ, ?_, hδₗb, ?_⟩
  · linarith
  · intro x hx
    have hx1 : c₀ - δₗ < x := hx.1
    have hx2 : x < c₀ := hx.2
    have hx0 : (0 : ℝ) < x := lt_of_le_of_lt hδₗb hx1
    have hx1c : x < 1 := lt_trans hx2 hc₀₁
    have htP : (cv ψ ⟨x, ⟨hx0, hx1c⟩⟩ : X) ∈ P :=
      hPleftfull ⟨x, ⟨hx0, hx1c⟩⟩ hx1 hx2
    exact (coordSet_mem_coord ψ ⟨x, ⟨hx0, hx1c⟩⟩).mpr htP

/-- **Right density from an empty LEFT window** (mirror of the verified
`ChartVal.left_dense_of_mem_closure_right_empty`):  a boundary point at
coordinate `c₀` of the open arc-chart `W`, with the whole left window
`(c₀−δₗ, c₀)` empty of `P`-points, has `P`-points arbitrarily close on the
RIGHT: for every `δᵣ > 0` a `P`-point with coordinate in `(c₀, c₀+δᵣ)`.  The
proof is the exact mirror (left/right exchanged) of the left version:
coordinates of `P`-points accumulate at `c₀` (closure bridge), none can lie
in the left window or at `c₀`, so they accumulate from the right. -/
theorem right_dense_of_mem_closure_left_empty (ψ : ORI ≃ₜ {x : X // x ∈ W})
    (hWopen : IsOpen W) {c₀ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδₗ₀ : 0 < δₗ)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P)
    (hleftEmpty : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (cv ψ t : X) ∉ P) :
    ∀ δᵣ : ℝ, 0 < δᵣ →
      ∃ t : ORI, c₀ < (t : ℝ) ∧ (t : ℝ) < c₀ + δᵣ ∧ (cv ψ t : X) ∈ P := by
  intro δᵣ hδᵣ₀
  have hS : ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure ({t : ORI | cv ψ t ∈ P} : Set ORI) :=
    ChartVal.coord_mem_closure_of_mem_closure ψ hWopen hc₀₀ hc₀₁ hz.1
  have hS' : ∀ o : Set ORI, IsOpen o → ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ o →
      (o ∩ {t : ORI | cv ψ t ∈ P}).Nonempty :=
    (mem_closure_iff).mp hS
  let A : Set ORI := {t : ORI | c₀ - δₗ < (t : ℝ) ∧ (t : ℝ) < c₀ + δᵣ}
  have hAopen : IsOpen A := by
    dsimp [A]
    exact IsOpen.preimage (f := fun t : ORI => (t : ℝ)) continuous_subtype_val
      (isOpen_Ioo : IsOpen (Set.Ioo (c₀ - δₗ) (c₀ + δᵣ)))
  have hAc₀ : ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ A := by
    dsimp [A]
    exact ⟨by linarith, by linarith⟩
  rcases hS' A hAopen hAc₀ with ⟨t, htA, htS⟩
  have hP : cv ψ t ∈ P := htS
  have htc : c₀ < (t : ℝ) := by
    by_contra hle
    have ht₀c : (t : ℝ) ≤ c₀ := le_of_not_gt hle
    by_cases ht₀ : c₀ = (t : ℝ)
    · exfalso
      have htEq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        apply Subtype.ext
        exact ht₀.symm
      exact hz.2 (by simpa [htEq] using hP)
    · exfalso
      have ht' : (t : ℝ) < c₀ := lt_of_le_of_ne ht₀c (by intro h; exact ht₀ h.symm)
      exact hleftEmpty t htA.1 ht' hP
  refine ⟨t, htc, htA.2, hP⟩

/-- Right density of P-coordinates (real-coordinate form, mirror of
`left_dense_coordSet`). -/
lemma right_dense_coordSet (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    (hPopen : IsOpen P) {c₀ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδₗ₀ : 0 < δₗ)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P)
    (hleftEmpty : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (cv ψ t : X) ∉ P) :
    ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ coordSet ψ P ∧ c₀ < x ∧ x < c₀ + ε := by
  intro ε hε
  have hright := right_dense_of_mem_closure_left_empty ψ hWopen hc₀₀ hc₀₁ hδₗ₀
    hz hleftEmpty ε hε
  rcases hright with ⟨t, ht1, ht2, htP⟩
  exact ⟨(t : ℝ), (coordSet_mem_coord ψ t).mpr htP, ht1, ht2⟩
/-- **Master lemma**: a boundary point of a proper open arc with an EMPTY
right window of the boundary chart extends the arc.

Regime 1 (full left strip) is handled by `ChartVal.arc_extension_of_left_strip`
(verified).  Regime 2 (no full strip): left density (verified
`ChartVal.left_dense_of_mem_closure_right_empty`) gives an interior
coordinate strip via the delegated real-analysis lemma
`Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full`;
`StripCore.interior_strip_forces_subset` (VERIFIED) then yields `P ⊆ W`, and
`extends_of_contained_in_arc_chart` extends via `Q := W`. -/
theorem boundary_right_empty_extends (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δᵣ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδᵣ₀ : 0 < δᵣ) (hδᵣ₁ : c₀ + δᵣ ≤ 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P)
    (hrightEmpty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (cv ψ t : X) ∉ P) :
    ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q) := by
  classical
  rcases eP with ⟨e⟩
  by_cases hfull : ∃ δₗ : ℝ, 0 < δₗ ∧ 0 ≤ c₀ - δₗ ∧
      ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ → (cv ψ t : X) ∈ P
  · rcases hfull with ⟨δₗ, hδₗ₀, hδₗb, hPleftfull⟩
    exact @ChartVal.arc_extension_of_left_strip X _ _ P W ⟨e⟩ hPopen ψ hWopen
      c₀ δᵣ δₗ hc₀₀ hc₀₁ hδᵣ₀ hδᵣ₁ hδₗ₀ hδₗb hz.2 hPleftfull hrightEmpty
  · -- Regime 2: no full left strip.  Left density + the delegated
    -- real-analysis lemma give an interior coordinate strip (a,b); the
    -- strip theorem forces P ⊆ W, and Q := W extends P.
    have hcoordNoFull : ¬ ∃ b : ℝ, b < c₀ ∧ 0 ≤ b ∧ Set.Ioo b c₀ ⊆ coordSet ψ P := by
      intro hcoordFull
      rcases hcoordFull with ⟨b, hbc, hb0, hsub⟩
      apply hfull
      refine ⟨c₀ - b, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · intro t h1 h2
        have htb : b < (t : ℝ) := by linarith
        have hxS : (t : ℝ) ∈ coordSet ψ P := hsub ⟨htb, h2⟩
        exact (coordSet_mem_coord ψ t).mp hxS
    have hleftD : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ,
        x ∈ coordSet ψ P ∧ c₀ - ε < x ∧ x < c₀ :=
      left_dense_coordSet ψ hWopen hPopen hc₀₀ hc₀₁ hδᵣ₀ hz hrightEmpty
    rcases (Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full
        (S := coordSet ψ P) (coordSet_isOpen ψ hWopen hPopen) (c := c₀) hc₀₀
        hleftD hcoordNoFull) with
      ⟨a, b, ha0, hab, hbc, hfillS, hnotA, hnotB⟩
    have hb1 : b < 1 := lt_trans hbc hc₀₁
    have ha1 : a < 1 := lt_trans hab hb1
    have ha01 : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨ha0, ha1⟩
    have hb01 : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans ha0 hab, hb1⟩
    have huaP : (cv ψ ⟨a, ha0, ha1⟩ : X) ∉ P :=
      coord_hole_of_not_mem ψ ha01 hnotA
    have hubP : (cv ψ ⟨b, lt_trans ha0 hab, hb1⟩ : X) ∉ P :=
      coord_hole_of_not_mem ψ hb01 hnotB
    have hfillP : ∀ t : ORI, a < (t : ℝ) → (t : ℝ) < b → (cv ψ t : X) ∈ P := by
      intro t hta htb
      exact (coordSet_mem_coord ψ t).mp (hfillS ⟨hta, htb⟩)
    have hPsubW : P ⊆ W :=
      @StripCore.interior_strip_forces_subset X _ _ P W e ψ hWopen
        a b ha0 hab hb1 huaP hubP hfillP
    refine extends_of_contained_in_arc_chart ⟨e⟩ ψ hWopen hPsubW ?_
    exact ⟨cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩, (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩).2, hz.2⟩


/-- **Mirror master lemma**: a boundary point of a proper open arc with an
EMPTY LEFT window of the boundary chart extends the arc.  Regime 1 (full
right strip) is handled by `ChartVal.arc_extension_of_right_strip`
(verified); Regime 2 (no full strip) uses right density (verified mirror
`right_dense_of_mem_closure_left_empty`) and the delegated right-side
real-analysis lemma
`Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full_right`
(fleet L57) to produce an interior strip, then
`StripCore.interior_strip_forces_subset` and
`extends_of_contained_in_arc_chart`. -/
theorem boundary_left_empty_extends (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ δₗ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hδₗ₀ : 0 < δₗ) (hδₗ₀b : 0 ≤ c₀ - δₗ)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P)
    (hleftEmpty : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (cv ψ t : X) ∉ P) :
    ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q) := by
  classical
  rcases eP with ⟨e⟩
  by_cases hfull : ∃ δᵣ : ℝ, 0 < δᵣ ∧ c₀ + δᵣ ≤ 1 ∧
      ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ → (cv ψ t : X) ∈ P
  · rcases hfull with ⟨δᵣ, hδᵣ₀, hδᵣ₁, hPrightfull⟩
    exact @ChartVal.arc_extension_of_right_strip X _ _ P W ⟨e⟩ hPopen ψ hWopen
      c₀ δᵣ δₗ hc₀₀ hc₀₁ hδᵣ₀ hδᵣ₁ hδₗ₀ hδₗ₀b hz.2 hPrightfull hleftEmpty
  · -- Regime 2: no full right strip; right density and the right-side
    -- real-analysis lemma give an interior strip (a,b), c₀ < a < b < 1;
    -- interior_strip_forces_subset gives P ⊆ W and
    -- extends_of_contained_in_arc_chart extends via Q := W.
    have hcoordNoFull : ¬ ∃ b : ℝ, c₀ < b ∧ b ≤ 1 ∧ Set.Ioo c₀ b ⊆ coordSet ψ P := by
      intro hcoordFull
      rcases hcoordFull with ⟨b, hcb, hb1, hsub⟩
      apply hfull
      refine ⟨b - c₀, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · intro t h1 h2
        have htb : (t : ℝ) < b := by linarith
        have hxS : (t : ℝ) ∈ coordSet ψ P := hsub ⟨h1, htb⟩
        exact (coordSet_mem_coord ψ t).mp hxS
    have hrightD : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ,
        x ∈ coordSet ψ P ∧ c₀ < x ∧ x < c₀ + ε :=
      right_dense_coordSet ψ hWopen hPopen hc₀₀ hc₀₁ hδₗ₀ hz hleftEmpty
    rcases (Commons.Analysis.RealIntervals.exists_interior_interval_of_dense_no_full_right
        (S := coordSet ψ P) (coordSet_isOpen ψ hWopen hPopen) (c := c₀) hc₀₁
        hrightD hcoordNoFull) with
      ⟨a, b, hca, hab, hb1, hfillS, hnotA, hnotB⟩
    have hua0 : 0 < a := lt_trans hc₀₀ hca
    have ha1 : a < 1 := lt_trans hab hb1
    have ha01 : a ∈ Set.Ioo (0 : ℝ) 1 := ⟨hua0, ha1⟩
    have hb01 : b ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_trans hua0 hab, hb1⟩
    have huaP : (cv ψ ⟨a, hua0, ha1⟩ : X) ∉ P :=
      coord_hole_of_not_mem ψ ha01 hnotA
    have hubP : (cv ψ ⟨b, lt_trans hua0 hab, hb1⟩ : X) ∉ P :=
      coord_hole_of_not_mem ψ hb01 hnotB
    have hfillP : ∀ t : ORI, a < (t : ℝ) → (t : ℝ) < b → (cv ψ t : X) ∈ P := by
      intro t hta htb
      exact (coordSet_mem_coord ψ t).mp (hfillS ⟨hta, htb⟩)
    have hPsubW : P ⊆ W :=
      @StripCore.interior_strip_forces_subset X _ _ P W e ψ hWopen
        a b hua0 hab hb1 huaP hubP hfillP
    refine extends_of_contained_in_arc_chart ⟨e⟩ ψ hWopen hPsubW ?_
    exact ⟨cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩, (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩).2, hz.2⟩


/-! ## The two-sided boundary case

At a boundary point `z` of a proper open arc `P`, the one-sided theorems
(`boundary_right_empty_extends`, `boundary_left_empty_extends`) already give
an extension if EITHER window of the boundary chart is empty of `P`.  Hence
for a MAXIMAL proper open arc (`hPmax`: no strictly larger open arc) every
boundary point has `P`-points on BOTH sides in every window
(`maximal_right_dense`, `maximal_left_dense`, contrapositives of the
one-sided theorems, proved below).  The two-sided structure then says that
`P` fills the whole chart except `z`:

**`maximal_boundary_two_sided_structure`**: `P ∩ W = W ∖ {z}`.

Reduction (structure): two-sided density + maximality rule out any interior
coordinate strip of `P` on either side (`StripCore.interior_strip_forces_subset`
would force `P ⊆ W`, hence the extension `Q := W`, contradicting `hPmax`);
the real-analysis lemmas
`Commons.Analysis.RealIntervals.left_full_or_strip_of_left_dense` /
`.right_full_or_strip_of_right_dense` (delegated) then return the FULL sides
`(0,c₀) ⊆ S` and `(c₀,1) ⊆ S` (S = the coordinates of `P ∩ W`); every chart
point other than `z` is therefore in `P`. -/


/-- At a maximal boundary point every right window contains a P-point. -/
lemma maximal_right_dense (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P) :
    ∀ δᵣ : ℝ, 0 < δᵣ → c₀ + δᵣ ≤ 1 →
      ∃ t : ORI, c₀ < (t : ℝ) ∧ (t : ℝ) < c₀ + δᵣ ∧ (cv ψ t : X) ∈ P := by
  rcases eP with ⟨e⟩
  intro δᵣ hδ₀ hδ₁
  by_contra h
  have hEmpty : ∀ t : ORI, c₀ < (t : ℝ) → (t : ℝ) < c₀ + δᵣ →
      (cv ψ t : X) ∉ P := by
    intro t h1 h2 hmem
    exact h ⟨t, h1, h2, hmem⟩
  have hQ := @boundary_right_empty_extends X _ _ P W ⟨e⟩ hPopen ψ hWopen
    c₀ δᵣ hc₀₀ hc₀₁ hδ₀ hδ₁ hz hEmpty
  exact hPmax hQ

/-- At a maximal boundary point every left window contains a P-point. -/
lemma maximal_left_dense (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P) :
    ∀ δₗ : ℝ, 0 < δₗ → 0 ≤ c₀ - δₗ →
      ∃ t : ORI, c₀ - δₗ < (t : ℝ) ∧ (t : ℝ) < c₀ ∧ (cv ψ t : X) ∈ P := by
  rcases eP with ⟨e⟩
  intro δₗ hδ₀ hδ₁
  by_contra h
  have hEmpty : ∀ t : ORI, c₀ - δₗ < (t : ℝ) → (t : ℝ) < c₀ →
      (cv ψ t : X) ∉ P := by
    intro t h1 h2 hmem
    exact h ⟨t, h1, h2, hmem⟩
  have hQ := @boundary_left_empty_extends X _ _ P W ⟨e⟩ hPopen ψ hWopen
    c₀ δₗ hc₀₀ hc₀₁ hδ₀ hδ₁ hz hEmpty
  exact hPmax hQ

/-- The boundary point's coordinate is not a coordinate of a P-point. -/
lemma coord_c0_not_in_coordSet (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P) :
    c₀ ∉ coordSet ψ P := by
  intro hc
  have hmem : cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ P :=
    (coordSet_mem_coord ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩).mp hc
  exact hz.2 hmem

/-- Real-coordinate form of the maximal left density. -/
lemma maximal_left_dense_coordSet (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P) :
    ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ coordSet ψ P ∧ c₀ - ε < x ∧ x < c₀ := by
  intro ε hε
  let δₗ : ℝ := min ε c₀
  have hδ₀ : 0 < δₗ := lt_min hε hc₀₀
  have hδ₁ : 0 ≤ c₀ - δₗ := by
    dsimp [δₗ]
    exact sub_nonneg.mpr (min_le_right ε c₀)
  have hw := maximal_left_dense eP hPopen hPmax ψ hWopen hc₀₀ hc₀₁ hz δₗ hδ₀ hδ₁
  rcases hw with ⟨t, ht1, ht2, htP⟩
  have hxε : c₀ - ε < (t : ℝ) := by
    have hle : c₀ - ε ≤ c₀ - δₗ := by
      dsimp [δₗ]
      exact sub_le_sub_left (min_le_left ε c₀) c₀
    exact lt_of_le_of_lt hle ht1
  exact ⟨(t : ℝ), (coordSet_mem_coord ψ t).mpr htP, hxε, ht2⟩

/-- Real-coordinate form of the maximal right density. -/
lemma maximal_right_dense_coordSet (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P) :
    ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ coordSet ψ P ∧ c₀ < x ∧ x < c₀ + ε := by
  intro ε hε
  let δᵣ : ℝ := min ε (1 - c₀)
  have hδ₀ : 0 < δᵣ := by
    dsimp [δᵣ]
    exact lt_min hε (sub_pos.mpr hc₀₁)
  have hδ₁ : c₀ + δᵣ ≤ 1 := by
    dsimp [δᵣ]
    have hminle : min ε (1 - c₀) ≤ 1 - c₀ := min_le_right ε (1 - c₀)
    linarith
  have hw := maximal_right_dense eP hPopen hPmax ψ hWopen hc₀₀ hc₀₁ hz δᵣ hδ₀ hδ₁
  rcases hw with ⟨t, ht1, ht2, htP⟩
  have hxε : (t : ℝ) < c₀ + ε := by
    have hle : δᵣ ≤ ε := by
      dsimp [δᵣ]
      exact min_le_left ε (1 - c₀)
    have hle2 : c₀ + δᵣ ≤ c₀ + ε := by linarith
    exact lt_of_lt_of_le ht2 hle2
  exact ⟨(t : ℝ), (coordSet_mem_coord ψ t).mpr htP, ht1, hxε⟩


/-- Maximality contradicts an interior coordinate strip of `P` in the chart:
the strip forces `P ⊆ W` (`StripCore.interior_strip_forces_subset`), so the
open arc-chart `W` is a strictly larger open arc — an extension. -/
lemma maximal_contradicts_strip (e : ORI ≃ₜ {x : X // x ∈ P}) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P)
    {a b : ℝ} (ha0 : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hfillS : Set.Ioo a b ⊆ coordSet ψ P)
    (hnotA : a ∉ coordSet ψ P) (hnotB : b ∉ coordSet ψ P) :
    False := by
  have huaP : (cv ψ ⟨a, ha0, lt_trans hab hb1⟩ : X) ∉ P :=
    coord_hole_of_not_mem ψ ⟨ha0, lt_trans hab hb1⟩ hnotA
  have hubP : (cv ψ ⟨b, lt_trans ha0 hab, hb1⟩ : X) ∉ P :=
    coord_hole_of_not_mem ψ ⟨lt_trans ha0 hab, hb1⟩ hnotB
  have hfillP : ∀ t : ORI, a < (t : ℝ) → (t : ℝ) < b → (cv ψ t : X) ∈ P := by
    intro t hta htb
    exact (coordSet_mem_coord ψ t).mp (hfillS ⟨hta, htb⟩)
  have hPsubW : P ⊆ W :=
    @StripCore.interior_strip_forces_subset X _ _ P W e ψ hWopen
      a b ha0 hab hb1 huaP hubP hfillP
  let z : X := cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩
  have hQ := @extends_of_contained_in_arc_chart X _ _ P W ⟨e⟩ ψ hWopen hPsubW
    ⟨z, (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}).2, hz.2⟩
  exact hPmax hQ

/-- **Two-sided structure at a maximal boundary point**: `P` fills the whole
chart `W` except the point `z` itself.  (OPEN — assembled from the two-sided
density lemmas above plus the two delegated real-analysis full-or-strip
lemmas; see the module note.) -/
theorem maximal_boundary_two_sided_structure (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    (ψ : ORI ≃ₜ {x : X // x ∈ W}) (hWopen : IsOpen W)
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P) :
    P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := by
  rcases eP with ⟨e⟩
  let S : Set ℝ := coordSet ψ P
  let z : X := cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩
  have hSopen : IsOpen S := coordSet_isOpen ψ hWopen hPopen
  have hc0not : c₀ ∉ S := coord_c0_not_in_coordSet ψ hc₀₀ hc₀₁ hz
  have hLD : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ S ∧ c₀ - ε < x ∧ x < c₀ :=
    maximal_left_dense_coordSet ⟨e⟩ hPopen hPmax ψ hWopen hc₀₀ hc₀₁ hz
  have hRD : ∀ ε : ℝ, 0 < ε → ∃ x : ℝ, x ∈ S ∧ c₀ < x ∧ x < c₀ + ε :=
    maximal_right_dense_coordSet ⟨e⟩ hPopen hPmax ψ hWopen hc₀₀ hc₀₁ hz
  have hLfull : Set.Ioo (0 : ℝ) c₀ ⊆ S := by
    rcases (Commons.Analysis.RealIntervals.left_full_or_strip_of_left_dense
        (S := S) hSopen (c := c₀) hc₀₀ hc₀₁ hc0not hLD) with hfull | hstrip
    · exact hfull
    · rcases hstrip with ⟨a, b, ha0, hab, hbc, hfillS, hnotA, hnotB⟩
      exact False.elim (maximal_contradicts_strip e hPopen hPmax ψ hWopen
        hc₀₀ hc₀₁ hz ha0 hab (lt_of_le_of_lt hbc hc₀₁) hfillS hnotA hnotB)
  have hRfull : Set.Ioo c₀ 1 ⊆ S := by
    rcases (Commons.Analysis.RealIntervals.right_full_or_strip_of_right_dense
        (S := S) hSopen (c := c₀) hc₀₀ hc₀₁ hc0not hRD) with hfull | hstrip
    · exact hfull
    · rcases hstrip with ⟨a, b, hca, hab, hb1, hfillS, hnotA, hnotB⟩
      exact False.elim (maximal_contradicts_strip e hPopen hPmax ψ hWopen
        hc₀₀ hc₀₁ hz (lt_of_lt_of_le hc₀₀ hca) hab hb1 hfillS hnotA hnotB)
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxP, hxW⟩
    refine ⟨hxW, ?_⟩
    intro hxz
    have hxzeq : x = cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by simpa [z] using hxz
    rw [hxzeq] at hxP
    exact hz.2 hxP
  · intro hx
    rcases hx with ⟨hxW, hxne⟩
    let t : ORI := ψ.symm ⟨x, hxW⟩
    let s : ℝ := (t : ℝ)
    have h01 : s ∈ Set.Ioo (0 : ℝ) 1 := t.2
    have hxeq : x = cv ψ ⟨s, ⟨h01.1, h01.2⟩⟩ := by
      have hh := congrArg (fun y : {x : X // x ∈ W} => (y : X))
        (ψ.apply_symm_apply ⟨x, hxW⟩)
      change x = (ψ (ψ.symm ⟨x, hxW⟩) : {x : X // x ∈ W}).1
      exact hh.symm
    have hsne : s ≠ c₀ := by
      intro hsc
      apply hxne
      rw [hxeq]
      apply congrArg (cv ψ)
      apply Subtype.ext
      exact hsc
    rcases lt_or_gt_of_ne hsne with hlt | hgt
    · have hxP : x ∈ P := by
        rw [hxeq]
        exact (coordSet_mem_coord ψ ⟨s, ⟨h01.1, h01.2⟩⟩).mp (hLfull ⟨h01.1, hlt⟩)
      exact ⟨hxP, hxW⟩
    · have hxP : x ∈ P := by
        rw [hxeq]
        exact (coordSet_mem_coord ψ ⟨s, ⟨h01.1, h01.2⟩⟩).mp (hRfull ⟨hgt, h01.2⟩)
      exact ⟨hxP, hxW⟩


/-! ## The global close-off (subclaim 2 of the two-sided case)

**Engine so far.**  `maximal_boundary_two_sided_structure` (VERIFIED): at
every boundary point `z ∈ closure P ∖ P` of a MAXIMAL proper open arc `P`,
every open arc-chart `W ∋ z` satisfies `P ∩ W = W ∖ {z}`.  Boundary points
are therefore mutually isolated (`∂P ∩ W = {z}`).

**Global theorem (OPEN, below) — the dichotomy's compact branch**:
a maximal PROPER open arc of a connected Hausdorff second-countable
locally interval-charted space forces the ambient to be compact:

`no_extension_of_proper_open_arc_implies_compact`.

Close-off reduction (steps):
1. **Charts at boundary points (OPEN)** — `boundary_points_isolated_of_maximal`:
   from the local-model hypothesis `hLoc` at each `z ∈ ∂P`, choose a unit
   open arc-chart `W ∋ z` (affine normalization of the local interval
   model; `z = ψ⟨c₀⟩` for `c₀ ∈ (0,1)` automatically, `ψ : ORI ≃ₜ ↑W`) and
   apply `maximal_boundary_two_sided_structure`:
   `P ∩ W = W ∖ {z}`, so `∂P ∩ W = {z}`.
2. **Density (OPEN)** — `maximal_arc_dense`: `cl P = X`.  If `y ∉ cl P`,
   a path from `P` to `y` (X connected + locally path connected) exits
   `cl P` at `z* ∈ ∂P`; step 1 gives a chart `W*` with `P∩W* = W*∖{z*}`,
   whose closure contains all of `W*`, so the path cannot leave `cl P` —
   contradiction.
3. **Ends close (mostly OPEN; uniqueness solved, see below)** — with
   `X = P ∪ ∂P` (steps 1–2), both ends of the arc `e : (0,1) ≃ₜ P`
   converge, and every boundary point attracts both ends (each chart
   punctured at `z` has its two sides filled by the two arc tails, by the
   P∩W-component analysis); hence `∂P = {z₀}` single and `X = P ∪ {z₀}` ≅ S¹.
4. **Compact (OPEN)** — with `X = P ∪ {z₀}` and tail convergence at `z₀`,
   `f : [0,1] → X` (`f 0 = f 1 = z₀`, `f t = e⟨t⟩`) is a continuous
   surjection, so `X` is compact.

**SOLUTION OF THE END CLOSE-OFF (found this session; NOT yet implemented in
Lean — implement next).**  `maximal_arc_ends_close` conjuncts 1–2 are
VERIFIED as `exists_boundary_attracts_both_ends` below.  Conjunct 3
(`∂P = {z₀}` — uniqueness of the boundary point):  for a maximal `P`,
every `z ∈ ∂P = X∖P` has an isolating chart `W_z`
(`boundary_points_isolated_of_maximal`): `P∩W_z = W_z∖{z}`, and `W_z∖{z}`
has exactly TWO connected components `side⁻(z)`, `side⁺(z)` (the chart
halves `(0,c_z)`, `(c_z,1)`).  Pull both sides back through the arc chart
`e : ORI ≃ₜ P`: `D⁻(z) := e⁻¹(side⁻(z))`, `D⁺(z) := e⁻¹(side⁺(z))` are
nonempty OPEN PRECONNECTED subsets of `(0,1)` — hence by the published
`Commons.Analysis.RealIntervals.open_preconnected_nonempty_subset_unit_Ioo_shape`
each is an open interval `Ioo a b`.  Left-end attraction (`z ∈ cl(e((0,a)))`
for every `a ∈ (0,1)`, L60), with the open nbhd `W_z`, gives
`D(z) := D⁻(z) ⊔ D⁺(z)` meets every `(0,a)`, so at least one interval
piece has infimum `0`, i.e. equals `(0,b)` with `b > 0`.  Hence for every
`z ∈ ∂P`: `∃ β_z > 0, (0,β_z) ⊆ e⁻¹(W_z)`.  Take `z₁ ≠ z₂ ∈ ∂P`; refine
their isolating charts to be DISJOINT (T2).  Then `e⁻¹(W₁)` and `e⁻¹(W₂)`
are disjoint subsets of `(0,1)`, yet each contains an initial segment
`(0,β_i)`, `β_i > 0` — contradiction.  So `∂P = {z₀}`.  Then tail
convergence of `e` at both ends to `z₀` follows inside the isolating chart
(the interval-piece analysis shows the left tail lies on ONE side of the
chart and its transferred coordinates tend to `c₀`), giving step 4 and
`no_extension_of_proper_open_arc_implies_compact`. -/

/-- **Charts at boundary points (close-off step 1, OPEN)**: every boundary
point `z` of a maximal proper open arc has a unit open arc-chart `W` with
`P ∩ W = W ∖ {z}` (so `∂P ∩ W = {z}`); boundary points are isolated.  Proof
outline: normalize the `hLoc` interval chart at `z` to a unit chart
(`ORI ≃ₜ ↑W`, `z = ψ⟨c₀⟩`, `c₀ ∈ (0,1)`) and apply
`maximal_boundary_two_sided_structure` (VERIFIED). -/
lemma boundary_points_isolated_of_maximal {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPproper : P ≠ Set.univ)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    {z : X} (hz : z ∈ closure P \ P) :
    ∃ W : Set X, IsOpen W ∧ z ∈ W ∧
      ∃ ψ : ORI ≃ₜ {x : X // x ∈ W}, P ∩ W = W \ {z} := by
  rcases eP with ⟨e⟩
  rcases hLoc z with ⟨U, hUopen, hzU, lo, hi, hf⟩
  rcases hf with ⟨f⟩
  -- U is an interval-model chart at z; normalize to a unit chart ORI ≃ₜ ↑U.
  let dom : {t : ℝ // t ∈ Set.Ioo lo hi} := f.symm ⟨z, hzU⟩
  have hlt : lo < hi := lt_trans dom.2.1 dom.2.2
  rcases (Commons.Topology.Homeomorph.open_interval_affine (a := lo) (b := hi)
      (c := 0) (d := 1) hlt (by norm_num)) with ⟨g⟩
  let ψ : ORI ≃ₜ {x : X // x ∈ U} := g.symm.trans f
  let c₀ : ℝ := (ψ.symm ⟨z, hzU⟩ : ORI).1
  have hc₀₀ : 0 < c₀ := (ψ.symm ⟨z, hzU⟩ : ORI).2.1
  have hc₀₁ : c₀ < 1 := (ψ.symm ⟨z, hzU⟩ : ORI).2.2
  have hzψ : z = cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
    have hh := congrArg (fun w : {x : X // x ∈ U} => (w : X))
      (ψ.apply_symm_apply ⟨z, hzU⟩)
    change z = (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ U}).1
    dsimp [c₀, cv]
    exact hh.symm
  have hz' : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ closure P \ P := by
    rw [← hzψ]
    exact hz
  have hstr := @maximal_boundary_two_sided_structure X _ _ P U ⟨e⟩ hPopen hPmax ψ hUopen
    c₀ hc₀₀ hc₀₁ hz'
  refine ⟨U, hUopen, hzU, ψ, ?_⟩
  rw [hstr]
  rw [hzψ]

/-- A nonempty proper CLOSED set of a connected space has nonempty frontier
(the closed set would otherwise be clopen, hence all of `X`). -/
lemma frontier_nonempty_of_proper_closed {Y : Type*} [TopologicalSpace Y] [ConnectedSpace Y]
    {S : Set Y} (hS : IsClosed S) (hne : S.Nonempty) (hprop : S ≠ Set.univ) :
    (frontier S).Nonempty := by
  by_contra h
  have hf : frontier S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hclopen : IsClopen S := isClopen_iff_frontier_eq_empty.mpr hf
  have hSuv : S = Set.univ := IsClopen.eq_univ hclopen hne
  exact hprop hSuv

/-- **Density of a maximal arc (close-off step 2, OPEN)**: a maximal proper
open arc is dense.  (Path argument: a point outside `cl P` would be
reachable from `P` by a path whose exit point from `cl P` is a boundary
point with the local structure `P∩W = W∖{z}`, through which the path cannot
leave.) -/
lemma maximal_arc_dense {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPproper : P ≠ Set.univ)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q)) :
    closure P = Set.univ := by
  classical
  by_contra hprop
  rcases eP with ⟨e⟩
  have hclPne : (closure P).Nonempty := by
    refine ⟨(e ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩ : {x : X // x ∈ P}).1, ?_⟩
    exact subset_closure (e ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩).2
  rcases frontier_nonempty_of_proper_closed (S := closure P) isClosed_closure hclPne hprop
    with ⟨z, hzb⟩
  have hzcl : z ∈ closure P := by simpa [closure_closure] using hzb.1
  have hzclc : z ∈ closure ((closure P)ᶜ) := by
    simpa [closure_compl] using hzb.2
  have hznotP : z ∉ P := by
    intro hzP
    have hV : P ∩ (closure P)ᶜ = ∅ := by
      ext y
      constructor
      · intro hy
        exact hy.2 (subset_closure hy.1)
      · intro hy
        exact False.elim hy
    have hmem := (mem_closure_iff).mp hzclc P hPopen hzP
    rw [hV] at hmem
    exact (Set.not_nonempty_empty hmem)
  have hz : z ∈ closure P \ P := ⟨hzcl, hznotP⟩
  rcases boundary_points_isolated_of_maximal hLoc ⟨e⟩ hPopen hPproper hPmax hz with
    ⟨U, hUopen, hzU, ψ, hEq⟩
  have hUcl : U ⊆ closure P := by
    intro y hyU
    by_cases hyz : y = z
    · rw [hyz]
      exact hzcl
    · have hyPU : y ∈ P ∩ U := by
        have hmem : y ∈ U \ {z} := ⟨hyU, hyz⟩
        simpa [hEq] using hmem
      exact subset_closure hyPU.1
  have hUdisj : U ∩ (closure P)ᶜ = ∅ := by
    ext y
    constructor
    · intro hy
      exact hy.2 (hUcl hy.1)
    · intro hy
      exact False.elim hy
  have hmem := (mem_closure_iff).mp hzclc U hUopen hzU
  rw [hUdisj] at hmem
  exact (Set.not_nonempty_empty hmem)


/-! ## The end-convergence lemma (close-off step 3)

`maximal_arc_dense` (VERIFIED) gives `cl P = X`, so `∂P = X ∖ P`; by
`hPproper` it is nonempty.  `boundary_points_isolated_of_maximal` gives each
`z ∈ ∂P` an isolating open arc-chart `W_z` with `P ∩ W_z = W_z ∖ {z}`.

**Claim (OPEN, `maximal_arc_ends_close` below)**: there is a single
boundary point `z₀` whose every prefix-arc and every suffix-arc of `P`
approach it — the two ends of the dense maximal arc close at one point, and
`X = P ∪ {z₀}`.

Proof plan (targeted ends argument, per boundary point `z ∈ ∂P`):
1. `P ∩ W_z = W_z ∖ {z}` splits into its two sides (coordinates `< c_z` and
   `> c_z`), each an open arc component of `P ∩ W_z`; under the arc-chart
   `e : ORI ≃ₜ ↑P` each side is a proper interval of `(0,1)`.
2. A side whose interval has an INTERIOR P-endpoint at its `z`-end would
   give `e⟨end⟩ = ψ⟨c_z⟩ = z ∈ P` (continuity + T2), impossible; so each
   side's `z`-end sits at a P-END of the arc (`0` or `1`).  The two
   disjoint side-intervals therefore occupy `(0,β_z)` (left P-end, running
   into `z`) and `(α_z,1)` (right P-end, running into `z`):
   every boundary point `z` attracts BOTH ends of the arc.
3. Uniqueness: if `z₁ ≠ z₂ ∈ ∂P`, both attract the same left end — for an
   arc whose complement is a set of isolating points this is impossible
   (a single end of an arc cannot run into two isolating boundary charts);
   hence `∂P = {z₀}`, and `X = P ∪ {z₀}` with both ends at `z₀`.

Steps 1–2 are coordinate bookkeeping on top of the isolating charts; step 3
is the genuine ends argument (delegate if needed). -/

/-- The isolating-chart identity makes the boundary point `z` a NON-P point. -/
lemma isolating_boundary_not_in_P (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩}) :
    (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∉ P := by
  intro hzP
  have hzPU : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ P ∩ W :=
    ⟨hzP, (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}).2⟩
  have hzWz : (cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩) ∈ W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := by
    rw [← hstruct]
    exact hzPU
  exact hzWz.2 rfl

/-- **A maximal proper open arc has a boundary point `z₀` that attracts
BOTH ends** (every prefix `e((0,a))` and every suffix `e((b,1))` of the arc
has `z₀` in its closure).  VERIFIED: from an isolating chart at `z₀`
(`boundary_points_isolated_of_maximal`) the fleet lemmas
`boundary_point_attracts_left_end` / `boundary_point_attracts_right_end`
(L60/L61) give the two closures; the only coordinate bookkeeping is to
identify the chart point with `z₀` (`hz₀ψ`). -/
lemma exists_boundary_attracts_both_ends {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPproper : P ≠ Set.univ)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q)) :
    ∃ z₀ : X, z₀ ∉ P ∧
      (∀ a : ℝ, 0 < a → a < 1 → z₀ ∈ closure (ChartVal.sub (Classical.choice eP) 0 a)) ∧
      (∀ b : ℝ, 0 < b → b < 1 → z₀ ∈ closure (ChartVal.sub (Classical.choice eP) b 1)) := by
  classical
  let e := Classical.choice eP
  have hdense : closure P = Set.univ := maximal_arc_dense hLoc eP hPopen hPproper hPmax
  have hbne : ∃ z₀ : X, z₀ ∉ P := by
    by_contra h
    have hPuniv : P = Set.univ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        by_contra hxP
        exact h ⟨x, hxP⟩
    exact hPproper hPuniv
  rcases hbne with ⟨z₀, hz₀⟩
  have hz₀b : z₀ ∈ closure P \ P := ⟨by rw [hdense]; trivial, hz₀⟩
  rcases boundary_points_isolated_of_maximal hLoc eP hPopen hPproper hPmax hz₀b with
    ⟨W, hWopen, hz₀W, ψ, hEq⟩
  let c₀ : ℝ := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).1
  have hc₀₀ : 0 < c₀ := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).2.1
  have hc₀₁ : c₀ < 1 := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).2.2
  have hz₀ψ : z₀ = cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
    have hh := congrArg (fun w : {x : X // x ∈ W} => (w : X))
      (ψ.apply_symm_apply ⟨z₀, hz₀W⟩)
    change z₀ = (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}).1
    dsimp [c₀, cv]
    exact hh.symm
  have hstruct : P ∩ W = W \ {(cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩)} := by
    simpa [hz₀ψ] using hEq
  have hattL := @boundary_point_attracts_left_end X _ _ P W
      e ψ c₀ hc₀₀ hc₀₁ hstruct
  have hattR := @boundary_point_attracts_right_end X _ _ P W
      e ψ c₀ hc₀₀ hc₀₁ hstruct
  refine ⟨z₀, hz₀, ?_, ?_⟩
  · intro a ha0 ha1
    have hza := hattL a ha0 ha1
    rw [hz₀ψ]
    convert hza using 1
    · rfl
    · rfl
  · intro b hb0 hb1
    have hzb := hattR b hb0 hb1
    rw [hz₀ψ]
    convert hzb using 1
    · rfl
    · rfl


/-- The coordinate set `{t : ORI | (t : ℝ) < c₀}` is connected. -/
lemma unit_left_connected {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    IsConnected ({t : ORI | (t : ℝ) < c₀} : Set ORI) := by
  have hEq : ({t : ORI | (t : ℝ) < c₀} : Set ORI) =
      {t : ORI | (t : ℝ) ∈ Set.Ioo (0 : ℝ) c₀} := by
    ext t
    constructor
    · intro ht
      exact ⟨t.2.1, ht⟩
    · intro ht
      exact ht.2
  rw [hEq]
  rcases (ChartVal.valueInterval_homeo (u := (0 : ℝ)) (v := c₀) (by norm_num)
      (le_of_lt hc₀₁)) with ⟨hφ⟩
  have hc : ConnectedSpace {r : ℝ // r ∈ Set.Ioo (0 : ℝ) c₀} :=
    (isConnected_iff_connectedSpace.mp (isConnected_Ioo (a := (0 : ℝ)) (b := c₀) hc₀₀))
  have hc' : ConnectedSpace {t : ORI // (t : ℝ) ∈ Set.Ioo (0 : ℝ) c₀} :=
    (hφ.connectedSpace_iff).mpr hc
  exact (isConnected_iff_connectedSpace.mpr hc')

/-- The coordinate set `{t : ORI | c₀ < (t : ℝ)}` is connected. -/
lemma unit_right_connected {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    IsConnected ({t : ORI | c₀ < (t : ℝ)} : Set ORI) := by
  have hEq : ({t : ORI | c₀ < (t : ℝ)} : Set ORI) =
      {t : ORI | (t : ℝ) ∈ Set.Ioo c₀ 1} := by
    ext t
    constructor
    · intro ht
      exact ⟨ht, t.2.2⟩
    · intro ht
      exact ht.1
  rw [hEq]
  rcases (ChartVal.valueInterval_homeo (u := c₀) (v := (1 : ℝ)) (le_of_lt hc₀₀)
      (by norm_num)) with ⟨hφ⟩
  have hc : ConnectedSpace {r : ℝ // r ∈ Set.Ioo c₀ 1} :=
    (isConnected_iff_connectedSpace.mp (isConnected_Ioo (a := c₀) (b := (1 : ℝ)) hc₀₁))
  have hc' : ConnectedSpace {t : ORI // (t : ℝ) ∈ Set.Ioo c₀ 1} :=
    (hφ.connectedSpace_iff).mpr hc
  exact (isConnected_iff_connectedSpace.mpr hc')

/-- The sides of an isolating chart are exactly `W` minus the boundary point. -/
lemma isolating_chart_sides (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} =
      ChartVal.sub ψ 0 c₀ ∪ ChartVal.sub ψ c₀ 1 := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxW, hxne⟩
    let t : ORI := ψ.symm ⟨x, hxW⟩
    let s : ℝ := (t : ℝ)
    have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := t.2
    have hxeq : x = cv ψ ⟨s, ⟨hs01.1, hs01.2⟩⟩ := by
      have hh := congrArg (fun y : {x : X // x ∈ W} => (y : X))
        (ψ.apply_symm_apply ⟨x, hxW⟩)
      change x = (ψ (ψ.symm ⟨x, hxW⟩) : {x : X // x ∈ W}).1
      exact hh.symm
    have hsne : s ≠ c₀ := by
      intro hsc
      apply hxne
      rw [hxeq]
      apply congrArg (cv ψ)
      apply Subtype.ext
      exact hsc
    rcases lt_or_gt_of_ne hsne with hlt | hgt
    · left
      rw [ChartVal.mem_sub]
      refine ⟨⟨s, ⟨hs01.1, hs01.2⟩⟩, ⟨hs01.1, hlt⟩, hxeq.symm⟩
    · right
      rw [ChartVal.mem_sub]
      refine ⟨⟨s, ⟨hs01.1, hs01.2⟩⟩, ⟨hgt, hs01.2⟩, hxeq.symm⟩
  · intro hx
    rcases hx with hxL | hxR
    · rw [ChartVal.mem_sub] at hxL
      rcases hxL with ⟨t, ht, hxeq⟩
      have hxW : x ∈ W := by
        rw [← hxeq]
        exact (ψ t).2
      have hxne : x ≠ cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        intro hxz
        have hlt : (t : ℝ) < c₀ := ht.2
        have ht_eq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
          apply ChartVal.chartVal_injective ψ
          rw [hxeq]
          exact hxz
        rw [ht_eq] at hlt
        exact (lt_irrefl c₀) hlt
      exact ⟨hxW, hxne⟩
    · rw [ChartVal.mem_sub] at hxR
      rcases hxR with ⟨t, ht, hxeq⟩
      have hxW : x ∈ W := by
        rw [← hxeq]
        exact (ψ t).2
      have hxne : x ≠ cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        intro hxz
        have hgt : c₀ < (t : ℝ) := ht.1
        have ht_eq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
          apply ChartVal.chartVal_injective ψ
          rw [hxeq]
          exact hxz
        rw [ht_eq] at hgt
        exact (lt_irrefl c₀) hgt
      exact ⟨hxW, hxne⟩

/-- Both sides of an isolating chart lie inside the arc `P`. -/
lemma sides_subset_P (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩}) :
    ChartVal.sub ψ 0 c₀ ⊆ P ∧ ChartVal.sub ψ c₀ 1 ⊆ P := by
  constructor
  · intro x hx
    rw [ChartVal.mem_sub] at hx
    rcases hx with ⟨t, ht, hxeq⟩
    have hxW : x ∈ W := by rw [← hxeq]; exact (ψ t).2
    have hxne : x ≠ cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
      intro hxz
      have hlt : (t : ℝ) < c₀ := ht.2
      have ht_eq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        apply ChartVal.chartVal_injective ψ
        rw [hxeq]
        exact hxz
      rw [ht_eq] at hlt
      exact (lt_irrefl c₀) hlt
    have h' : x ∈ W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := ⟨hxW, hxne⟩
    have h'' : x ∈ P ∩ W := by
      rw [hstruct]
      exact h'
    exact h''.1
  · intro x hx
    rw [ChartVal.mem_sub] at hx
    rcases hx with ⟨t, ht, hxeq⟩
    have hxW : x ∈ W := by rw [← hxeq]; exact (ψ t).2
    have hxne : x ≠ cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
      intro hxz
      have hgt : c₀ < (t : ℝ) := ht.1
      have ht_eq : t = ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
        apply ChartVal.chartVal_injective ψ
        rw [hxeq]
        exact hxz
      rw [ht_eq] at hgt
      exact (lt_irrefl c₀) hgt
    have h' : x ∈ W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := ⟨hxW, hxne⟩
    have h'' : x ∈ P ∩ W := by
      rw [hstruct]
      exact h'
    exact h''.1

/-- The chart side `sub ψ 0 c₀` is a connected open arc. -/
lemma side_left_isOpen_connected (ψ : ORI ≃ₜ {x : X // x ∈ W})
    (hWopen : IsOpen W) {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    IsOpen (ChartVal.sub ψ 0 c₀) ∧ IsConnected (ChartVal.sub ψ 0 c₀) := by
  constructor
  · exact ChartVal.sub_isOpen ψ hWopen 0 c₀
  · have hIm : ChartVal.sub ψ 0 c₀ = cv ψ '' ({t : ORI | (t : ℝ) < c₀} : Set ORI) := by
      ext x
      constructor
      · intro hx
        rw [ChartVal.mem_sub] at hx
        rcases hx with ⟨t, ht, hxeq⟩
        refine ⟨t, ht.2, hxeq⟩
      · intro hx
        rcases hx with ⟨t, ht, hxeq⟩
        rw [ChartVal.mem_sub]
        exact ⟨t, ⟨t.2.1, ht⟩, hxeq⟩
    rw [hIm]
    exact IsConnected.image (unit_left_connected hc₀₀ hc₀₁) (cv ψ)
      (ChartVal.chartVal_continuous ψ).continuousOn

/-- The chart side `sub ψ c₀ 1` is a connected open arc. -/
lemma side_right_isOpen_connected (ψ : ORI ≃ₜ {x : X // x ∈ W})
    (hWopen : IsOpen W) {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    IsOpen (ChartVal.sub ψ c₀ 1) ∧ IsConnected (ChartVal.sub ψ c₀ 1) := by
  constructor
  · exact ChartVal.sub_isOpen ψ hWopen c₀ 1
  · have hIm : ChartVal.sub ψ c₀ 1 = cv ψ '' ({t : ORI | c₀ < (t : ℝ)} : Set ORI) := by
      ext x
      constructor
      · intro hx
        rw [ChartVal.mem_sub] at hx
        rcases hx with ⟨t, ht, hxeq⟩
        refine ⟨t, ht.1, hxeq⟩
      · intro hx
        rcases hx with ⟨t, ht, hxeq⟩
        rw [ChartVal.mem_sub]
        exact ⟨t, ⟨ht, t.2.2⟩, hxeq⟩
    rw [hIm]
    exact IsConnected.image (unit_right_connected hc₀₀ hc₀₁) (cv ψ)
      (ChartVal.chartVal_continuous ψ).continuousOn


/-- **Coordinate initial segment at an isolating boundary point.** -/
lemma boundary_initial_segment (e : ORI ≃ₜ {x : X // x ∈ P}) (hPopen : IsOpen P)
    (W : Set X) (hWopen : IsOpen W) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩})
    (hattL : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a)) :
    ∃ β : ℝ, 0 < β ∧
      Set.Ioo (0 : ℝ) β ⊆ ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ W}) := by
  classical
  let z : X := cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩
  let L : Set X := ChartVal.sub ψ 0 c₀
  let R : Set X := ChartVal.sub ψ c₀ 1
  let CW : Set ℝ := (fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ W}
  let CL : Set ℝ := (fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ L}
  let CR : Set ℝ := (fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ R}
  have hzP : z ∉ P := isolating_boundary_not_in_P ψ hc₀₀ hc₀₁ hstruct
  have hLP : L ⊆ P := (sides_subset_P ψ hc₀₀ hc₀₁ hstruct).1
  have hRP : R ⊆ P := (sides_subset_P ψ hc₀₀ hc₀₁ hstruct).2
  have hLopen : IsOpen L := (side_left_isOpen_connected ψ hWopen hc₀₀ hc₀₁).1
  have hLc : IsConnected L := (side_left_isOpen_connected ψ hWopen hc₀₀ hc₀₁).2
  have hRopen : IsOpen R := (side_right_isOpen_connected ψ hWopen hc₀₀ hc₀₁).1
  have hRc : IsConnected R := (side_right_isOpen_connected ψ hWopen hc₀₀ hc₀₁).2
  have hLconn : ConnectedSpace {x : X // x ∈ L} := (isConnected_iff_connectedSpace.mp hLc)
  have hRconn : ConnectedSpace {x : X // x ∈ R} := (isConnected_iff_connectedSpace.mp hRc)
  rcases (chart_pullback_interval_shape (U := L) (hUopen := hLopen) (hUconn := hLconn)
      (hUW := hLP) (χ := e)) with ⟨aL, bL, h0aL, haLbL, hbL1, hiffL⟩
  rcases (chart_pullback_interval_shape (U := R) (hUopen := hRopen) (hUconn := hRconn)
      (hUW := hRP) (χ := e)) with ⟨aR, bR, h0aR, haRbR, hbR1, hiffR⟩
  have hCL : CL = Set.Ioo aL bL := by
    have hset : {t : ORI | cv e t ∈ L} = {t : ORI | (t : ℝ) ∈ Set.Ioo aL bL} := by
      ext t
      constructor
      · intro ht
        exact (hiffL t).mp ht
      · intro ht
        exact (hiffL t).mpr ht
    dsimp [CL]
    rw [hset]
    ext r
    constructor
    · rintro ⟨t, ht, htv⟩
      rw [← htv]
      exact ht
    · intro hr
      have h0r : (0 : ℝ) < r := lt_of_le_of_lt h0aL hr.1
      have hr1 : r < 1 := lt_of_lt_of_le hr.2 hbL1
      refine ⟨⟨r, ⟨h0r, hr1⟩⟩, hr, rfl⟩
  have hCR : CR = Set.Ioo aR bR := by
    have hset : {t : ORI | cv e t ∈ R} = {t : ORI | (t : ℝ) ∈ Set.Ioo aR bR} := by
      ext t
      constructor
      · intro ht
        exact (hiffR t).mp ht
      · intro ht
        exact (hiffR t).mpr ht
    dsimp [CR]
    rw [hset]
    ext r
    constructor
    · rintro ⟨t, ht, htv⟩
      rw [← htv]
      exact ht
    · intro hr
      have h0r : (0 : ℝ) < r := lt_of_le_of_lt h0aR hr.1
      have hr1 : r < 1 := lt_of_lt_of_le hr.2 hbR1
      refine ⟨⟨r, ⟨h0r, hr1⟩⟩, hr, rfl⟩
  have hCW : CW = CL ∪ CR := by
    dsimp [CW, CL, CR]
    have hWL : {t : ORI | cv e t ∈ W} =
        {t : ORI | cv e t ∈ L} ∪ {t : ORI | cv e t ∈ R} := by
      ext t
      constructor
      · intro ht
        have htP : cv e t ∈ P := (e t).2
        have hmem : cv e t ∈ P ∩ W := ⟨htP, ht⟩
        have hmem' : cv e t ∈ W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := by
          rw [← hstruct]
          exact hmem
        have hzsub : W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} ⊆ L ∪ R := by
          rw [isolating_chart_sides ψ hc₀₀ hc₀₁]
        have hmem'' : cv e t ∈ L ∪ R := hzsub hmem'
        rcases hmem'' with hL' | hR'
        · exact Or.inl hL'
        · exact Or.inr hR'
      · intro ht
        rcases ht with hL' | hR'
        · have hLsubW : L ⊆ W := fun x hx => by
            rw [ChartVal.mem_sub] at hx
            rcases hx with ⟨s, hs, hseq⟩
            rw [← hseq]
            exact (ψ s).2
          exact hLsubW hL'
        · have hRsubW : R ⊆ W := fun x hx => by
            rw [ChartVal.mem_sub] at hx
            rcases hx with ⟨s, hs, hseq⟩
            rw [← hseq]
            exact (ψ s).2
          exact hRsubW hR'
    rw [hWL]
    rw [Set.image_union]
  have hdens : ∀ a : ℝ, 0 < a → a < 1 → (CW ∩ Set.Ioo (0 : ℝ) a).Nonempty := by
    intro a ha0 ha1
    have hcl := hattL a ha0 ha1
    have hzW : z ∈ W := (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}).2
    have hne : (W ∩ ChartVal.sub e 0 a).Nonempty :=
      (mem_closure_iff).mp hcl W hWopen hzW
    rcases hne with ⟨x, hxW, hxA⟩
    rw [ChartVal.mem_sub] at hxA
    rcases hxA with ⟨t, ht, hxeq⟩
    have htW : cv e t ∈ W := by
      change ChartVal.chartVal e t ∈ W
      rw [hxeq]
      exact hxW
    refine ⟨(t : ℝ), ?_, ht⟩
    dsimp [CW]
    exact ⟨t, htW, rfl⟩
  by_cases hLz : aL = 0
  · refine ⟨bL, ?_, ?_⟩
    · rw [hLz] at haLbL
      exact haLbL
    · intro r hr
      change r ∈ CW
      rw [hCW]
      left
      rw [hCL, hLz]
      exact hr
  · by_cases hRz : aR = 0
    · refine ⟨bR, ?_, ?_⟩
      · rw [hRz] at haRbR
        exact haRbR
      · intro r hr
        change r ∈ CW
        rw [hCW]
        right
        rw [hCR, hRz]
        exact hr
    · have hLpos : 0 < aL := lt_of_le_of_ne h0aL (Ne.symm hLz)
      have hRpos : 0 < aR := lt_of_le_of_ne h0aR (Ne.symm hRz)
      have haL1 : aL < 1 := lt_of_lt_of_le haLbL hbL1
      have haR1 : aR < 1 := lt_of_lt_of_le haRbR hbR1
      let a : ℝ := min (aL / 2) (aR / 2)
      have ha0 : 0 < a := by
        dsimp [a]
        exact lt_min (by positivity) (by positivity)
      have ha1 : a < 1 := by
        have h1 : aL / 2 < 1 := by linarith
        have h2 : aR / 2 < 1 := by linarith
        dsimp [a]
        exact lt_of_le_of_lt (min_le_left (aL / 2) (aR / 2)) h1
      rcases hdens a ha0 ha1 with ⟨r, hrCW, hrI⟩
      rw [hCW] at hrCW
      rcases hrCW with hrL | hrR
      · rw [hCL] at hrL
        have hrLlt : aL < r := hrL.1
        have hrlta : r < a := hrI.2
        have halta : a < aL := by
          have hhalf : aL / 2 < aL := by linarith
          exact lt_of_le_of_lt (min_le_left (aL / 2) (aR / 2)) hhalf
        linarith
      · rw [hCR] at hrR
        have hrRlt : aR < r := hrR.1
        have hrlta : r < a := hrI.2
        have halta : a < aR := by
          have hhalf : aR / 2 < aR := by linarith
          exact lt_of_le_of_lt (min_le_right (aL / 2) (aR / 2)) hhalf
        linarith


/-- At an isolating boundary point with LEFT-end attraction, one of the two
chart sides has an INITIAL coordinate segment `(0,u)`. -/
lemma initial_side_coords (e : ORI ≃ₜ {x : X // x ∈ P}) (hPopen : IsOpen P)
    (W : Set X) (hWopen : IsOpen W) (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩})
    (hattL : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a)) :
    (∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧
      ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u) ∨
    (∃ u : ℝ, 0 < u ∧ u ≤ 1 ∧
      ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ c₀ 1}) = Set.Ioo 0 u) := by
  classical
  let z : X := cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩
  let L : Set X := ChartVal.sub ψ 0 c₀
  let R : Set X := ChartVal.sub ψ c₀ 1
  let CL : Set ℝ := (fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ L}
  let CR : Set ℝ := (fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ R}
  have hLP : L ⊆ P := (sides_subset_P ψ hc₀₀ hc₀₁ hstruct).1
  have hRP : R ⊆ P := (sides_subset_P ψ hc₀₀ hc₀₁ hstruct).2
  have hLopen : IsOpen L := (side_left_isOpen_connected ψ hWopen hc₀₀ hc₀₁).1
  have hLc : IsConnected L := (side_left_isOpen_connected ψ hWopen hc₀₀ hc₀₁).2
  have hRopen : IsOpen R := (side_right_isOpen_connected ψ hWopen hc₀₀ hc₀₁).1
  have hRc : IsConnected R := (side_right_isOpen_connected ψ hWopen hc₀₀ hc₀₁).2
  have hLconn : ConnectedSpace {x : X // x ∈ L} := (isConnected_iff_connectedSpace.mp hLc)
  have hRconn : ConnectedSpace {x : X // x ∈ R} := (isConnected_iff_connectedSpace.mp hRc)
  rcases (chart_pullback_interval_shape (U := L) (hUopen := hLopen) (hUconn := hLconn)
      (hUW := hLP) (χ := e)) with ⟨aL, bL, h0aL, haLbL, hbL1, hiffL⟩
  rcases (chart_pullback_interval_shape (U := R) (hUopen := hRopen) (hUconn := hRconn)
      (hUW := hRP) (χ := e)) with ⟨aR, bR, h0aR, haRbR, hbR1, hiffR⟩
  have hCL : CL = Set.Ioo aL bL := by
    have hset : {t : ORI | cv e t ∈ L} = {t : ORI | (t : ℝ) ∈ Set.Ioo aL bL} := by
      ext t
      constructor
      · intro ht
        exact (hiffL t).mp ht
      · intro ht
        exact (hiffL t).mpr ht
    dsimp [CL]
    rw [hset]
    ext r
    constructor
    · rintro ⟨t, ht, htv⟩
      rw [← htv]
      exact ht
    · intro hr
      have h0r : (0 : ℝ) < r := lt_of_le_of_lt h0aL hr.1
      have hr1 : r < 1 := lt_of_lt_of_le hr.2 hbL1
      refine ⟨⟨r, ⟨h0r, hr1⟩⟩, hr, rfl⟩
  have hCR : CR = Set.Ioo aR bR := by
    have hset : {t : ORI | cv e t ∈ R} = {t : ORI | (t : ℝ) ∈ Set.Ioo aR bR} := by
      ext t
      constructor
      · intro ht
        exact (hiffR t).mp ht
      · intro ht
        exact (hiffR t).mpr ht
    dsimp [CR]
    rw [hset]
    ext r
    constructor
    · rintro ⟨t, ht, htv⟩
      rw [← htv]
      exact ht
    · intro hr
      have h0r : (0 : ℝ) < r := lt_of_le_of_lt h0aR hr.1
      have hr1 : r < 1 := lt_of_lt_of_le hr.2 hbR1
      refine ⟨⟨r, ⟨h0r, hr1⟩⟩, hr, rfl⟩
  have hdens : ∀ a : ℝ, 0 < a → a < 1 → ((CL ∪ CR) ∩ Set.Ioo (0 : ℝ) a).Nonempty := by
    intro a ha0 ha1
    have hcl := hattL a ha0 ha1
    have hzW : z ∈ W := (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}).2
    have hne : (W ∩ ChartVal.sub e 0 a).Nonempty :=
      (mem_closure_iff).mp hcl W hWopen hzW
    rcases hne with ⟨x, hxW, hxA⟩
    rw [ChartVal.mem_sub] at hxA
    rcases hxA with ⟨t, ht, hxeq⟩
    have htP : cv e t ∈ P := (e t).2
    have hmem : cv e t ∈ P ∩ W := ⟨htP, by
      change ChartVal.chartVal e t ∈ W
      rw [hxeq]
      exact hxW⟩
    have hmem' : cv e t ∈ W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := by
      rw [← hstruct]
      exact hmem
    have hzsub : W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} ⊆ L ∪ R := by
      rw [isolating_chart_sides ψ hc₀₀ hc₀₁]
    have hmem'' : cv e t ∈ L ∪ R := hzsub hmem'
    rcases hmem'' with hL' | hR'
    · exact ⟨(t : ℝ), Or.inl (by dsimp [CL]; exact ⟨t, hL', rfl⟩), ht⟩
    · exact ⟨(t : ℝ), Or.inr (by dsimp [CR]; exact ⟨t, hR', rfl⟩), ht⟩
  by_cases hLz : aL = 0
  · left
    refine ⟨bL, ?_, ?_, ?_⟩
    · rw [hLz] at haLbL
      exact haLbL
    · exact hbL1
    · change CL = Set.Ioo (0 : ℝ) bL
      rw [hCL, hLz]
  · by_cases hRz : aR = 0
    · right
      refine ⟨bR, ?_, ?_, ?_⟩
      · rw [hRz] at haRbR
        exact haRbR
      · exact hbR1
      · change CR = Set.Ioo (0 : ℝ) bR
        rw [hCR, hRz]
    · have hLpos : 0 < aL := lt_of_le_of_ne h0aL (Ne.symm hLz)
      have hRpos : 0 < aR := lt_of_le_of_ne h0aR (Ne.symm hRz)
      have haL1 : aL < 1 := lt_of_lt_of_le haLbL hbL1
      have haR1 : aR < 1 := lt_of_lt_of_le haRbR hbR1
      let a : ℝ := min (aL / 2) (aR / 2)
      have ha0 : 0 < a := by
        dsimp [a]
        exact lt_min (by positivity) (by positivity)
      have ha1 : a < 1 := by
        have h1 : aL / 2 < 1 := by linarith
        have h2 : aR / 2 < 1 := by linarith
        dsimp [a]
        exact lt_of_le_of_lt (min_le_left (aL / 2) (aR / 2)) h1
      rcases hdens a ha0 ha1 with ⟨r, hrLR, hrI⟩
      rcases hrLR with hrL | hrR
      · rw [hCL] at hrL
        have hrLlt : aL < r := hrL.1
        have hrlta : r < a := hrI.2
        have halta : a < aL := by
          have hhalf : aL / 2 < aL := by linarith
          exact lt_of_le_of_lt (min_le_left (aL / 2) (aR / 2)) hhalf
        linarith
      · rw [hCR] at hrR
        have hrRlt : aR < r := hrR.1
        have hrlta : r < a := hrI.2
        have halta : a < aR := by
          have hhalf : aR / 2 < aR := by linarith
          exact lt_of_le_of_lt (min_le_right (aL / 2) (aR / 2)) hhalf
        linarith


/-- Interval pullback of an interior point (helper). -/
private lemma homeo_preimage {u lo hi : ℝ}
    (F : ({t : ℝ // t ∈ Set.Ioo 0 u}) ≃ₜ ({s : ℝ // s ∈ Set.Ioo lo hi}))
    {γ : ℝ} (hγ : γ ∈ Set.Ioo lo hi) :
    ∃ x₀ : {t : ℝ // t ∈ Set.Ioo 0 u}, (F x₀ : ℝ) = γ := by
  let t₀ : {t : ℝ // t ∈ Set.Ioo lo hi} := ⟨γ, hγ⟩
  refine ⟨F.symm t₀, ?_⟩
  have h := congrArg (fun q : {s : ℝ // s ∈ Set.Ioo lo hi} => (q : ℝ)) (F.apply_symm_apply t₀)
  simpa [t₀] using h

/-- GOOD increasing tail. -/
lemma real_tail_good_inc {u c d η : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hcd : c < d)
    (hη : 0 < η) (hηd : c + η < d)
    (F : ({t : ℝ // t ∈ Set.Ioo 0 u}) ≃ₜ ({s : ℝ // s ∈ Set.Ioo c d}))
    (hmono : StrictMono (fun t : {t : ℝ // t ∈ Set.Ioo 0 u} => (F t : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < u ∧
      ∀ t : {t : ℝ // t ∈ Set.Ioo 0 u}, (t : ℝ) < δ → (F t : ℝ) ∈ Set.Ioo (c - η) (c + η) := by
  have hγ : c + η ∈ Set.Ioo c d := ⟨by linarith, hηd⟩
  rcases homeo_preimage F hγ with ⟨x₀, hF⟩
  refine ⟨(x₀ : ℝ), x₀.2.1, x₀.2.2, ?_⟩
  intro t htδ
  have hlt : (F t : ℝ) < c + η := by
    have hle : t < x₀ := htδ
    have hf := hmono hle
    change (F t : ℝ) < (F x₀ : ℝ) at hf
    rw [hF] at hf
    exact hf
  have hgt : c < (F t : ℝ) := (F t).2.1
  constructor <;> linarith

/-- GOOD decreasing tail. -/
lemma real_tail_good_anti {u lo c η : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hlc : lo < c)
    (hη : 0 < η) (hηl : lo < c - η)
    (F : ({t : ℝ // t ∈ Set.Ioo 0 u}) ≃ₜ ({s : ℝ // s ∈ Set.Ioo lo c}))
    (hanti : StrictAnti (fun t : {t : ℝ // t ∈ Set.Ioo 0 u} => (F t : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < u ∧
      ∀ t : {t : ℝ // t ∈ Set.Ioo 0 u}, (t : ℝ) < δ → (F t : ℝ) ∈ Set.Ioo (c - η) (c + η) := by
  have hγ : c - η ∈ Set.Ioo lo c := ⟨hηl, by linarith⟩
  rcases homeo_preimage F hγ with ⟨x₀, hF⟩
  refine ⟨(x₀ : ℝ), x₀.2.1, x₀.2.2, ?_⟩
  intro t htδ
  have hlt : c - η < (F t : ℝ) := by
    have hle : t < x₀ := htδ
    have hf := hanti hle
    change (F x₀ : ℝ) < (F t : ℝ) at hf
    rw [hF] at hf
    exact hf
  have hltc : (F t : ℝ) < c := (F t).2.2
  constructor <;> linarith

/-- BAD increasing tail. -/
lemma real_tail_bad_inc {u lo c η : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hlc : lo < c)
    (hη : 0 < η) (hηl : lo < c - η)
    (F : ({t : ℝ // t ∈ Set.Ioo 0 u}) ≃ₜ ({s : ℝ // s ∈ Set.Ioo lo c}))
    (hmono : StrictMono (fun t : {t : ℝ // t ∈ Set.Ioo 0 u} => (F t : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < u ∧
      ∀ t : {t : ℝ // t ∈ Set.Ioo 0 u}, (t : ℝ) < δ → (F t : ℝ) < c - η := by
  have hγ : c - η ∈ Set.Ioo lo c := ⟨hηl, by linarith⟩
  rcases homeo_preimage F hγ with ⟨x₀, hF⟩
  refine ⟨(x₀ : ℝ), x₀.2.1, x₀.2.2, ?_⟩
  intro t htδ
  have hle : t < x₀ := htδ
  have hf := hmono hle
  change (F t : ℝ) < (F x₀ : ℝ) at hf
  rw [hF] at hf
  exact hf

/-- BAD decreasing tail. -/
lemma real_tail_bad_anti {u c d η : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (hcd : c < d)
    (hη : 0 < η) (hηd : c + η < d)
    (F : ({t : ℝ // t ∈ Set.Ioo 0 u}) ≃ₜ ({s : ℝ // s ∈ Set.Ioo c d}))
    (hanti : StrictAnti (fun t : {t : ℝ // t ∈ Set.Ioo 0 u} => (F t : ℝ))) :
    ∃ δ : ℝ, 0 < δ ∧ δ < u ∧
      ∀ t : {t : ℝ // t ∈ Set.Ioo 0 u}, (t : ℝ) < δ → c + η < (F t : ℝ) := by
  have hγ : c + η ∈ Set.Ioo c d := ⟨by linarith, hηd⟩
  rcases homeo_preimage F hγ with ⟨x₀, hF⟩
  refine ⟨(x₀ : ℝ), x₀.2.1, x₀.2.2, ?_⟩
  intro t htδ
  have hle : t < x₀ := htδ
  have hf := hanti hle
  change (F x₀ : ℝ) < (F t : ℝ) at hf
  rw [hF] at hf
  exact hf

/-- A small coordinate interval around `z₁ = ψ₁⟨c₁⟩` maps inside `O₁`. -/
lemma coord_interval_inside_open {W₁ O₁ : Set X} (ψ₁ : ORI ≃ₜ {x : X // x ∈ W₁})
    (hO₁ : IsOpen O₁) {c₁ : ℝ} (hc₁₀ : 0 < c₁) (hc₁₁ : c₁ < 1)
    (hzO : cv ψ₁ ⟨c₁, ⟨hc₁₀, hc₁₁⟩⟩ ∈ O₁) :
    ∃ η : ℝ, 0 < η ∧ 0 ≤ c₁ - η ∧ c₁ + η ≤ 1 ∧ η < c₁ ∧ η < 1 - c₁ ∧
      ∀ t : ORI, c₁ - η < (t : ℝ) → (t : ℝ) < c₁ + η → cv ψ₁ t ∈ O₁ := by
  classical
  let V : Set ORI := {t : ORI | cv ψ₁ t ∈ O₁}
  have hVopen : IsOpen V := by
    dsimp [V]
    exact hO₁.preimage (ChartVal.chartVal_continuous ψ₁)
  have hcV : ⟨c₁, ⟨hc₁₀, hc₁₁⟩⟩ ∈ V := by
    dsimp [V]
    exact hzO
  let Vℝ : Set ℝ := (fun t : ORI => (t : ℝ)) '' V
  have hVℝopen : IsOpen Vℝ := by
    dsimp [Vℝ]
    exact (IsOpen.isOpenMap_subtype_val (isOpen_Ioo : IsOpen (Set.Ioo (0 : ℝ) 1))) V hVopen
  have hcVℝ : c₁ ∈ Vℝ := by
    dsimp [Vℝ]
    exact ⟨⟨c₁, ⟨hc₁₀, hc₁₁⟩⟩, hcV, rfl⟩
  rcases (Metric.isOpen_iff.mp hVℝopen) c₁ hcVℝ with ⟨ε, hε, hball⟩
  let η : ℝ := min ε (min (c₁ / 2) ((1 - c₁) / 2))
  have hη₀ : 0 < η := by
    dsimp [η]
    exact lt_min hε (lt_min (by positivity) (by positivity))
  have hη₀₂ : η ≤ c₁ / 2 := by
    dsimp [η]
    exact le_trans (min_le_right ε (min (c₁ / 2) ((1 - c₁) / 2)))
      (min_le_left (c₁ / 2) ((1 - c₁) / 2))
  have hη₀₃ : η ≤ (1 - c₁) / 2 := by
    dsimp [η]
    exact le_trans (min_le_right ε (min (c₁ / 2) ((1 - c₁) / 2)))
      (min_le_right (c₁ / 2) ((1 - c₁) / 2))
  have hηε : η ≤ ε := by
    dsimp [η]
    exact min_le_left ε (min (c₁ / 2) ((1 - c₁) / 2))
  refine ⟨η, hη₀, ?_, ?_, ?_, ?_, ?_⟩
  · have hc₁₂ : c₁ / 2 ≤ c₁ := by linarith
    have hηc : η ≤ c₁ := le_trans hη₀₂ hc₁₂
    linarith
  · have h1 : (1 - c₁) / 2 ≤ 1 - c₁ := by linarith
    have hη1 : η ≤ 1 - c₁ := le_trans hη₀₃ h1
    linarith
  · have hhalf : c₁ / 2 < c₁ := by linarith
    exact lt_of_le_of_lt hη₀₂ hhalf
  · have hhalf : (1 - c₁) / 2 < 1 - c₁ := by linarith
    exact lt_of_le_of_lt hη₀₃ hhalf
  · intro t ht1 ht2
    have hηt : |(t : ℝ) - c₁| < η := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have hlt : |(t : ℝ) - c₁| < ε := lt_of_lt_of_le hηt hηε
    have hballmem : (t : ℝ) ∈ Metric.ball c₁ ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hlt
    have hmemℝ : (t : ℝ) ∈ Vℝ := hball hballmem
    rcases hmemℝ with ⟨s, hs, hsv⟩
    have hst : s = t := by
      apply Subtype.ext
      exact hsv
    have htV : t ∈ V := by
      simpa [hst] using hs
    dsimp [V] at htV
    exact htV

/-- The isolating structure restricts to sub-charts. -/
lemma subchart_structure {W₁ W₁' : Set X} {z₁ : X}
    (hstruct : P ∩ W₁ = W₁ \ {z₁}) (hWsub : W₁' ⊆ W₁) (hz₁ : z₁ ∈ W₁') :
    P ∩ W₁' = W₁' \ {z₁} := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxP, hxW'⟩
    have hxW : x ∈ W₁ := hWsub hxW'
    have hmem : x ∈ W₁ \ {z₁} := by
      rw [← hstruct]
      exact ⟨hxP, hxW⟩
    exact ⟨hxW', hmem.2⟩
  · intro hx
    rcases hx with ⟨hxW', hxne⟩
    have hxW : x ∈ W₁ := hWsub hxW'
    have hmem' : x ∈ W₁ \ {z₁} := ⟨hxW, hxne⟩
    have hmem : x ∈ P ∩ W₁ := by
      rw [hstruct]
      exact hmem'
    exact ⟨hmem.1, hxW'⟩


/-- **Two distinct NON-`P` points of a maximal proper open arc are
impossible.** -/
lemma boundary_points_singleton {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPproper : P ≠ Set.univ)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q))
    {z₁ z₂ : X} (hne : z₁ ≠ z₂) (hz₁P : z₁ ∉ P) (hz₂P : z₂ ∉ P) : False := by
  classical
  let e := Classical.choice eP
  have hdense : closure P = Set.univ := maximal_arc_dense hLoc eP hPopen hPproper hPmax
  have hz₁b : z₁ ∈ closure P \ P := ⟨by rw [hdense]; trivial, hz₁P⟩
  have hz₂b : z₂ ∈ closure P \ P := ⟨by rw [hdense]; trivial, hz₂P⟩
  rcases t2_separation hne with ⟨O₁, O₂, hO₁open, hO₂open, hz₁O₁, hz₂O₂, hdisj⟩
  have hz₂clO₁ : z₂ ∉ closure O₁ := by
    intro hcl
    have hne' := (mem_closure_iff).mp hcl O₂ hO₂open hz₂O₂
    rcases hne' with ⟨x, hxO₂, hxO₁⟩
    exact (Set.disjoint_left.mp hdisj) hxO₁ hxO₂
  rcases boundary_points_isolated_of_maximal hLoc eP hPopen hPproper hPmax hz₁b with
    ⟨W₁, hW₁open, hz₁W₁, ψ₁, hEq₁⟩
  let c₁ : ℝ := (ψ₁.symm ⟨z₁, hz₁W₁⟩ : ORI).1
  have hc₁₀ : 0 < c₁ := (ψ₁.symm ⟨z₁, hz₁W₁⟩ : ORI).2.1
  have hc₁₁ : c₁ < 1 := (ψ₁.symm ⟨z₁, hz₁W₁⟩ : ORI).2.2
  have hz₁ψ₁ : z₁ = cv ψ₁ ⟨c₁, ⟨hc₁₀, hc₁₁⟩⟩ := by
    have hh := congrArg (fun w : {x : X // x ∈ W₁} => (w : X))
      (ψ₁.apply_symm_apply ⟨z₁, hz₁W₁⟩)
    change z₁ = (ψ₁ ⟨c₁, ⟨hc₁₀, hc₁₁⟩⟩ : {x : X // x ∈ W₁}).1
    dsimp [c₁, cv]
    exact hh.symm
  have hstruct₁ : P ∩ W₁ = W₁ \ {cv ψ₁ ⟨c₁, ⟨hc₁₀, hc₁₁⟩⟩} := by
    simpa [hz₁ψ₁] using hEq₁
  have hatt₁raw := @boundary_point_attracts_left_end X _ _ P W₁ e ψ₁ c₁ hc₁₀ hc₁₁ hstruct₁
  have hz₁attract : ∀ a : ℝ, 0 < a → a < 1 → z₁ ∈ closure (ChartVal.sub e 0 a) := by
    intro a ha0 ha1
    have hza := hatt₁raw a ha0 ha1
    rw [hz₁ψ₁]
    convert hza using 1
    · rfl
    · rfl
  rcases coord_interval_inside_open ψ₁ hO₁open hc₁₀ hc₁₁ (by simpa [hz₁ψ₁] using hz₁O₁)
    with ⟨η, hη₀, hη₀₂, hη₀₃, hηc₁, hηc₁', hηmap⟩
  let W₁' : Set X := ChartVal.sub ψ₁ (c₁ - η) (c₁ + η)
  have hW₁'sub : W₁' ⊆ O₁ := by
    intro x hx
    rw [ChartVal.mem_sub] at hx
    rcases hx with ⟨t, ht, hxeq⟩
    rw [← hxeq]
    exact hηmap t ht.1 ht.2
  have hW₁'open : IsOpen W₁' := ChartVal.sub_isOpen ψ₁ hW₁open (c₁ - η) (c₁ + η)
  have hW₁'subW₁ : W₁' ⊆ W₁ := by
    intro x hx
    rw [ChartVal.mem_sub] at hx
    rcases hx with ⟨t, ht, hxeq⟩
    rw [← hxeq]
    exact (ψ₁ t).2
  have hz₁W₁' : z₁ ∈ W₁' := by
    rw [ChartVal.mem_sub]
    refine ⟨⟨c₁, ⟨hc₁₀, hc₁₁⟩⟩, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hz₁ψ₁]
  have hstruct₁z : P ∩ W₁ = W₁ \ {z₁} := by
    simpa [hz₁ψ₁] using hstruct₁
  have hstruct₁' : P ∩ W₁' = W₁' \ {z₁} :=
    subchart_structure hstruct₁z hW₁'subW₁ hz₁W₁'
  rcases (ChartVal.sub_arc ψ₁ (u := c₁ - η) (v := c₁ + η) hη₀₂ (by linarith) hη₀₃)
    with ⟨ψ₁'⟩
  let c₁' : ℝ := (ψ₁'.symm ⟨z₁, hz₁W₁'⟩ : ORI).1
  have hc₁'₀ : 0 < c₁' := (ψ₁'.symm ⟨z₁, hz₁W₁'⟩ : ORI).2.1
  have hc₁'₁ : c₁' < 1 := (ψ₁'.symm ⟨z₁, hz₁W₁'⟩ : ORI).2.2
  have hz₁ψ₁' : z₁ = cv ψ₁' ⟨c₁', ⟨hc₁'₀, hc₁'₁⟩⟩ := by
    have hh := congrArg (fun w : {x : X // x ∈ W₁'} => (w : X))
      (ψ₁'.apply_symm_apply ⟨z₁, hz₁W₁'⟩)
    change z₁ = (ψ₁' ⟨c₁', ⟨hc₁'₀, hc₁'₁⟩⟩ : {x : X // x ∈ W₁'}).1
    dsimp [c₁', cv]
    exact hh.symm
  have hstruct₁'' : P ∩ W₁' = W₁' \ {cv ψ₁' ⟨c₁', ⟨hc₁'₀, hc₁'₁⟩⟩} := by
    simpa [hz₁ψ₁'] using hstruct₁'
  have hattL₁' : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ₁' ⟨c₁', ⟨hc₁'₀, hc₁'₁⟩⟩ ∈ closure (ChartVal.sub e 0 a) := by
    intro a ha0 ha1
    rw [← hz₁ψ₁']
    exact hz₁attract a ha0 ha1
  rcases boundary_initial_segment e hPopen W₁' hW₁'open ψ₁' hc₁'₀ hc₁'₁ hstruct₁'' hattL₁'
    with ⟨β, hβ, hseg⟩
  let a₀ : ℝ := min (β / 2) (1 / 2)
  have ha₀₀ : 0 < a₀ := by
    dsimp [a₀]
    exact lt_min (by positivity) (by positivity)
  have ha₀₁ : a₀ < 1 := by
    dsimp [a₀]
    exact lt_of_le_of_lt (min_le_right (β / 2) (1 / 2)) (by norm_num)
  have ha₀β : a₀ < β := by
    dsimp [a₀]
    have hhalf : β / 2 < β := by linarith
    exact lt_of_le_of_lt (min_le_left (β / 2) (1 / 2)) hhalf
  have hsubO : ChartVal.sub e 0 a₀ ⊆ O₁ := by
    intro x hx
    rw [ChartVal.mem_sub] at hx
    rcases hx with ⟨t, ht, hxeq⟩
    have htβ : (t : ℝ) ∈ Set.Ioo (0 : ℝ) β := ⟨ht.1, lt_trans ht.2 ha₀β⟩
    have hmem : (t : ℝ) ∈ ((fun u : ORI => (u : ℝ)) '' {u : ORI | cv e u ∈ W₁'}) :=
      hseg htβ
    rcases hmem with ⟨s, hsW, hsv⟩
    have hst : s = t := by
      apply Subtype.ext
      exact hsv
    have hcontra : cv e t ∈ W₁' := by
      rw [← hst]
      exact hsW
    have hxmem : x ∈ W₁' := by
      rw [← hxeq]
      change cv e t ∈ W₁'
      exact hcontra
    exact hW₁'sub hxmem
  rcases boundary_points_isolated_of_maximal hLoc eP hPopen hPproper hPmax hz₂b with
    ⟨W₂, hW₂open, hz₂W₂, ψ₂, hEq₂⟩
  let c₂ : ℝ := (ψ₂.symm ⟨z₂, hz₂W₂⟩ : ORI).1
  have hc₂₀ : 0 < c₂ := (ψ₂.symm ⟨z₂, hz₂W₂⟩ : ORI).2.1
  have hc₂₁ : c₂ < 1 := (ψ₂.symm ⟨z₂, hz₂W₂⟩ : ORI).2.2
  have hz₂ψ₂ : z₂ = cv ψ₂ ⟨c₂, ⟨hc₂₀, hc₂₁⟩⟩ := by
    have hh := congrArg (fun w : {x : X // x ∈ W₂} => (w : X))
      (ψ₂.apply_symm_apply ⟨z₂, hz₂W₂⟩)
    change z₂ = (ψ₂ ⟨c₂, ⟨hc₂₀, hc₂₁⟩⟩ : {x : X // x ∈ W₂}).1
    dsimp [c₂, cv]
    exact hh.symm
  have hstruct₂ : P ∩ W₂ = W₂ \ {cv ψ₂ ⟨c₂, ⟨hc₂₀, hc₂₁⟩⟩} := by
    simpa [hz₂ψ₂] using hEq₂
  have hatt₂ := @boundary_point_attracts_left_end X _ _ P W₂ e ψ₂ c₂ hc₂₀ hc₂₁ hstruct₂
  have hz₂cl : z₂ ∈ closure (ChartVal.sub e 0 a₀) := by
    have hza := hatt₂ a₀ ha₀₀ ha₀₁
    rw [hz₂ψ₂]
    convert hza using 1
    · rfl
    · rfl
  have hz₂clO₁' : z₂ ∈ closure O₁ := closure_mono hsubO hz₂cl
  exact hz₂clO₁ hz₂clO₁'

theorem maximal_arc_ends_close {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPproper : P ≠ Set.univ)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q)) :
    ∃ z₀ : X, z₀ ∉ P ∧
      (∀ a : ℝ, 0 < a → a < 1 → z₀ ∈ closure (ChartVal.sub (Classical.choice eP) 0 a)) ∧
      (∀ b : ℝ, 0 < b → b < 1 → z₀ ∈ closure (ChartVal.sub (Classical.choice eP) b 1)) ∧
      (∀ y : X, y ≠ z₀ → y ∈ P) := by
  classical
  rcases exists_boundary_attracts_both_ends hLoc eP hPopen hPproper hPmax with
    ⟨z₀, hz₀P, hL, hR⟩
  refine ⟨z₀, hz₀P, hL, hR, ?_⟩
  intro y hyne
  by_contra hyP
  exact boundary_points_singleton hLoc eP hPopen hPproper hPmax hyne hyP hz₀P

end BdryExt

end Commons.Topology.OneManifold


open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

namespace TailConv

open BdryExt

variable {X : Type*} [TopologicalSpace X] [T2Space X] {P W : Set X}

abbrev ORI : Type := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}

/-- coordinates equality gives pointwise iff. -/
lemma coords_eq_iff_mem {e : ORI ≃ₜ {x : X // x ∈ P}} {side : Set X} {u : ℝ}
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ side}) = Set.Ioo 0 u) :
    ∀ t : ORI, cv e t ∈ side ↔ (t : ℝ) ∈ Set.Ioo (0 : ℝ) u := by
  intro t
  constructor
  · intro ht
    have hmem : (t : ℝ) ∈ ((fun s : ORI => (s : ℝ)) '' {s : ORI | cv e s ∈ side}) :=
      ⟨t, ht, rfl⟩
    rw [hcu] at hmem
    exact hmem
  · intro ht
    have hmem : (t : ℝ) ∈ ((fun s : ORI => (s : ℝ)) '' {s : ORI | cv e s ∈ side}) := by
      rw [hcu]
      exact ht
    rcases hmem with ⟨s, hs, hsv⟩
    have hst : s = t := by
      apply Subtype.ext
      exact hsv
    simpa [hst] using hs

/-- The left side `sub ψ 0 c₀` lies in `W`. -/
lemma side_lower_sub_W (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ} :
    ChartVal.sub ψ 0 c₀ ⊆ W := by
  intro x hx
  rw [ChartVal.mem_sub] at hx
  rcases hx with ⟨t, ht, hxeq⟩
  rw [← hxeq]
  exact (ψ t).2

/-- The right side `sub ψ c₀ 1` lies in `W`. -/
lemma side_upper_sub_W (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ} :
    ChartVal.sub ψ c₀ 1 ⊆ W := by
  intro x hx
  rw [ChartVal.mem_sub] at hx
  rcases hx with ⟨t, ht, hxeq⟩
  rw [← hxeq]
  exact (ψ t).2



/-- ψ-coordinate of a point of the left side is below c₀. -/
lemma ψcoord_lt_of_mem_lower (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) {p : X} (hW : p ∈ W)
    (hp : p ∈ ChartVal.sub ψ 0 c₀) : (ψ.symm ⟨p, hW⟩ : ORI).1 < c₀ := by
  rw [ChartVal.mem_sub] at hp
  rcases hp with ⟨t, ht, hxeq⟩
  have hts : ψ.symm ⟨cv ψ t, (ψ t).2⟩ = t := ψ.symm_apply_apply t
  have hp' : ψ.symm ⟨p, hW⟩ = ψ.symm ⟨cv ψ t, (ψ t).2⟩ := by
    apply congrArg ψ.symm
    apply Subtype.ext
    exact hxeq.symm
  rw [hp', hts]
  exact ht.2

/-- ψ-coordinate of a point of the right side is above c₀. -/
lemma c₀_lt_ψcoord_of_mem_upper (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) {p : X} (hW : p ∈ W)
    (hp : p ∈ ChartVal.sub ψ c₀ 1) : c₀ < (ψ.symm ⟨p, hW⟩ : ORI).1 := by
  rw [ChartVal.mem_sub] at hp
  rcases hp with ⟨t, ht, hxeq⟩
  have hts : ψ.symm ⟨cv ψ t, (ψ t).2⟩ = t := ψ.symm_apply_apply t
  have hp' : ψ.symm ⟨p, hW⟩ = ψ.symm ⟨cv ψ t, (ψ t).2⟩ := by
    apply congrArg ψ.symm
    apply Subtype.ext
    exact hxeq.symm
  rw [hp', hts]
  exact ht.1

/-- Points of the left side of `W` are below c₀ in ψ-coordinates; the map
`x ↦ (ψ.symm ⟨x, _⟩ : ORI).1` sends the left side onto (0,c₀). -/
lemma ψcoord_mem_lower_iff (ψ : ORI ≃ₜ {x : X // x ∈ W}) {c₀ : ℝ}
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) {p : X} (hW : p ∈ W) :
    p ∈ ChartVal.sub ψ 0 c₀ ↔ (ψ.symm ⟨p, hW⟩ : ORI).1 < c₀ := by
  constructor
  · exact ψcoord_lt_of_mem_lower ψ hc₀₀ hc₀₁ hW
  · intro hlt
    let s : ORI := ψ.symm ⟨p, hW⟩
    have hs0 : 0 < (s : ℝ) := s.2.1
    rw [ChartVal.mem_sub]
    refine ⟨s, ⟨hs0, hlt⟩, ?_⟩
    have h := congrArg (fun w : {x : X // x ∈ W} => (w : X)) (ψ.apply_symm_apply ⟨p, hW⟩)
    change (cv ψ s : X) = p
    exact h


/-- Lower-side coordinate transfer: `D → C` (explicit). -/
noncomputable def lowerFun (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u) :
    ({r : ℝ // r ∈ Set.Ioo 0 u}) → ({s : ℝ // s ∈ Set.Ioo 0 c₀}) := fun r =>
  have hr0 : (0 : ℝ) < (r : ℝ) := (Set.mem_Ioo.mp r.2).1
  have hru : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
  let t : ORI := ⟨(r : ℝ), ⟨hr0, by linarith⟩⟩
  have hp_side : cv e t ∈ ChartVal.sub ψ 0 c₀ :=
    (coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu t).mpr ⟨hr0, hru⟩
  have hpW : cv e t ∈ W := side_lower_sub_W ψ hp_side
  have hval : (ψ.symm ⟨cv e t, hpW⟩ : ORI).1 < c₀ :=
    ψcoord_lt_of_mem_lower ψ hc₀₀ hc₀₁ hpW hp_side
  ⟨(ψ.symm ⟨cv e t, hpW⟩ : ORI).1, ⟨(ψ.symm ⟨cv e t, hpW⟩ : ORI).2.1, hval⟩⟩

/-- Lower-side inverse coordinate transfer: `C → D` (explicit). -/
noncomputable def lowerInv (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u) :
    ({s : ℝ // s ∈ Set.Ioo 0 c₀}) → ({r : ℝ // r ∈ Set.Ioo 0 u}) := fun s =>
  have hs0 : (0 : ℝ) < (s : ℝ) := (Set.mem_Ioo.mp s.2).1
  have hsc : (s : ℝ) < c₀ := (Set.mem_Ioo.mp s.2).2
  let y : ORI := ⟨(s : ℝ), ⟨hs0, by linarith⟩⟩
  let p : X := cv ψ y
  have hp_side : p ∈ ChartVal.sub ψ 0 c₀ := by
    rw [ChartVal.mem_sub]
    exact ⟨y, s.2, rfl⟩
  have hpP : p ∈ P := hLP hp_side
  have hval : (e.symm ⟨p, hpP⟩ : ORI).1 ∈ Set.Ioo 0 u := by
    have hiff := coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu (e.symm ⟨p, hpP⟩)
    exact hiff.mp (by
      have hcv : cv e (e.symm ⟨p, hpP⟩) = p := by
        change ((e (e.symm ⟨p, hpP⟩) : {x : X // x ∈ P}) : X) = p
        exact congrArg (fun w : {x : X // x ∈ P} => (w : X)) (e.apply_symm_apply ⟨p, hpP⟩)
      rw [hcv]
      exact hp_side)
  ⟨(e.symm ⟨p, hpP⟩ : ORI).1, hval⟩

/-- `cv e (e.symm p) = p`. -/
theorem cv_apply_symm (e : ORI ≃ₜ {x : X // x ∈ P}) {p : X} (hp : p ∈ P) :
    cv e (e.symm ⟨p, hp⟩) = p := by
  change ((e (e.symm ⟨p, hp⟩) : {x : X // x ∈ P}) : X) = p
  exact congrArg (fun w : {x : X // x ∈ P} => (w : X)) (e.apply_symm_apply ⟨p, hp⟩)

/-- `e.symm ⟨cv e t, _⟩ = t`. -/
theorem symm_apply_cv (e : ORI ≃ₜ {x : X // x ∈ P}) (t : ORI) :
    e.symm ⟨cv e t, (e t).2⟩ = t := by
  have h1 : e (e.symm ⟨cv e t, (e t).2⟩) = e t := by
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rfl
  exact e.injective h1

/-- `e.symm ⟨cv e t, hp⟩ = t` for any `hp`. -/
theorem symm_apply_cv_any (e : ORI ≃ₜ {x : X // x ∈ P}) (t : ORI) (hp : cv e t ∈ P) :
    e.symm ⟨cv e t, hp⟩ = t := by
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  rfl

/-- value of `lowerFun`. -/
theorem lowerFun_val (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u)
    (r : {r : ℝ // r ∈ Set.Ioo 0 u}) :
    (lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu r).1 =
      (ψ.symm ⟨cv e ⟨(r : ℝ), ⟨(Set.mem_Ioo.mp r.2).1, by
        have : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
        linarith⟩⟩,
        side_lower_sub_W ψ ((coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu
          ⟨(r : ℝ), ⟨(Set.mem_Ioo.mp r.2).1, by
            have : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
            linarith⟩⟩).mpr ⟨(Set.mem_Ioo.mp r.2).1, (Set.mem_Ioo.mp r.2).2⟩)⟩ : ORI).1 := by
  rfl

/-- value of `lowerInv`. -/
theorem lowerInv_val (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u)
    (s : {s : ℝ // s ∈ Set.Ioo 0 c₀}) :
    (lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu s).1 =
      (e.symm ⟨cv ψ ⟨(s : ℝ), ⟨(Set.mem_Ioo.mp s.2).1, by
        have : (s : ℝ) < c₀ := (Set.mem_Ioo.mp s.2).2
        linarith⟩⟩,
        hLP (by
          rw [ChartVal.mem_sub]
          exact ⟨⟨(s : ℝ), ⟨(Set.mem_Ioo.mp s.2).1, by
            have : (s : ℝ) < c₀ := (Set.mem_Ioo.mp s.2).2
            linarith⟩⟩, (Set.mem_Ioo.mp s.2), rfl⟩)⟩ : ORI).1 := by
  rfl

/-- `lowerInv (lowerFun r) = r`. -/
theorem lower_left_inv (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u)
    (r : {r : ℝ // r ∈ Set.Ioo 0 u}) :
    lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu (lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu r) = r := by
  apply Subtype.ext
  have hr0 : (0 : ℝ) < (r : ℝ) := (Set.mem_Ioo.mp r.2).1
  have hru : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
  let t : ORI := ⟨(r : ℝ), ⟨hr0, by linarith⟩⟩
  have htmem : cv e t ∈ ChartVal.sub ψ 0 c₀ :=
    (coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu t).mpr ⟨hr0, hru⟩
  let s0 : ORI := ψ.symm ⟨cv e t, side_lower_sub_W ψ htmem⟩
  have hs0c : (s0 : ℝ) ∈ Set.Ioo 0 c₀ :=
    ⟨(s0 : ORI).2.1, ψcoord_lt_of_mem_lower ψ hc₀₀ hc₀₁ (side_lower_sub_W ψ htmem) htmem⟩
  have hFun : lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu r =
      (⟨(s0 : ℝ), hs0c⟩ : {s : ℝ // s ∈ Set.Ioo 0 c₀}) := by
    apply Subtype.ext
    dsimp [lowerFun, s0]
  rw [hFun]
  -- lowerInv at ⟨s0.1, hs0c⟩: value = e-coordinate of the point with ψ-coordinate s0.1
  have hsame : (⟨(s0 : ℝ), hs0c.1, by have := hs0c.2; linarith⟩ : ORI) = s0 := by
    apply Subtype.ext
    rfl
  have hcv1 : cv ψ (⟨(s0 : ℝ), hs0c.1, by have := hs0c.2; linarith⟩ : ORI) = cv e t := by
    rw [hsame]
    exact cv_apply_symm ψ (side_lower_sub_W ψ htmem)
  have hPmem : cv ψ (⟨(s0 : ℝ), hs0c.1, by have := hs0c.2; linarith⟩ : ORI) ∈ ChartVal.sub ψ 0 c₀ := by
    rw [ChartVal.mem_sub]
    exact ⟨(⟨(s0 : ℝ), hs0c.1, by have := hs0c.2; linarith⟩ : ORI), hs0c, rfl⟩
  have hvalInv : (lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu (⟨(s0 : ℝ), hs0c⟩ :
      {s : ℝ // s ∈ Set.Ioo 0 c₀})).1 = (r : ℝ) := by
    calc
      (lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu (⟨(s0 : ℝ), hs0c⟩ : {s : ℝ // s ∈ Set.Ioo 0 c₀})).1
          = (e.symm ⟨cv ψ (⟨(s0 : ℝ), hs0c.1, by have := hs0c.2; linarith⟩ : ORI), hLP hPmem⟩ : ORI).1 := by
              rfl
      _ = (e.symm ⟨cv e t, hLP htmem⟩ : ORI).1 := by
              have hpt : (⟨cv ψ (⟨(s0 : ℝ), hs0c.1, by have := hs0c.2; linarith⟩ : ORI), hLP hPmem⟩ :
                  {x : X // x ∈ P}) = ⟨cv e t, hLP htmem⟩ := by
                apply Subtype.ext
                exact hcv1
              rw [hpt]
      _ = (t : ℝ) := by
              have hE : e.symm ⟨cv e t, hLP htmem⟩ = t := symm_apply_cv_any e t (hLP htmem)
              rw [hE]
      _ = (r : ℝ) := rfl
  exact hvalInv

/-- `lowerFun (lowerInv s) = s`. -/
theorem lower_right_inv (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u)
    (s : {s : ℝ // s ∈ Set.Ioo 0 c₀}) :
    lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu (lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu s) = s := by
  apply Subtype.ext
  have hs0 : (0 : ℝ) < (s : ℝ) := (Set.mem_Ioo.mp s.2).1
  have hsc : (s : ℝ) < c₀ := (Set.mem_Ioo.mp s.2).2
  let y : ORI := ⟨(s : ℝ), ⟨hs0, by linarith⟩⟩
  have hy_side : cv ψ y ∈ ChartVal.sub ψ 0 c₀ := by
    rw [ChartVal.mem_sub]
    exact ⟨y, ⟨hs0, hsc⟩, rfl⟩
  have hyP : cv ψ y ∈ P := hLP hy_side
  let w : ℝ := (e.symm ⟨cv ψ y, hyP⟩ : ORI).1
  have hw_mem : w ∈ Set.Ioo 0 u := by
    dsimp [w]
    have hiff := coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu (e.symm ⟨cv ψ y, hyP⟩)
    exact hiff.mp (by
      have hcv : cv e (e.symm ⟨cv ψ y, hyP⟩) = cv ψ y := cv_apply_symm e hyP
      rw [hcv]
      exact hy_side)
  have hInv : lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu s =
      (⟨w, hw_mem⟩ : {r : ℝ // r ∈ Set.Ioo 0 u}) := by
    apply Subtype.ext
    dsimp [lowerInv, y, w]
  rw [hInv]
  -- value of lowerFun at ⟨w, hw_mem⟩: ψ-coordinate of cv e ⟨w,·⟩ = cv ψ y
  have hsame : (⟨w, hw_mem.1, by have := hw_mem.2; linarith⟩ : ORI) = e.symm ⟨cv ψ y, hyP⟩ := by
    apply Subtype.ext
    dsimp [w]
  have hcv_e : cv e (⟨w, hw_mem.1, by have := hw_mem.2; linarith⟩ : ORI) = cv ψ y := by
    rw [hsame]
    exact cv_apply_symm e hyP
  have hvalFun : (lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu (⟨w, hw_mem⟩ :
      {r : ℝ // r ∈ Set.Ioo 0 u})).1 = (s : ℝ) := by
    calc
      (lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu (⟨w, hw_mem⟩ : {r : ℝ // r ∈ Set.Ioo 0 u})).1
          = (ψ.symm ⟨cv e (⟨w, hw_mem.1, by have := hw_mem.2; linarith⟩ : ORI),
              side_lower_sub_W ψ ((coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu
                (⟨w, hw_mem.1, by have := hw_mem.2; linarith⟩ : ORI)).mpr hw_mem)⟩ : ORI).1 := by
              rfl
      _ = (ψ.symm ⟨cv ψ y, side_lower_sub_W ψ hy_side⟩ : ORI).1 := by
              have hpt : (⟨cv e (⟨w, hw_mem.1, by have := hw_mem.2; linarith⟩ : ORI),
                  side_lower_sub_W ψ ((coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu
                    (⟨w, hw_mem.1, by have := hw_mem.2; linarith⟩ : ORI)).mpr hw_mem)⟩ :
                  {x : X // x ∈ W}) = ⟨cv ψ y, side_lower_sub_W ψ hy_side⟩ := by
                apply Subtype.ext
                exact hcv_e
              rw [hpt]
      _ = (y : ℝ) := by
              have hE : ψ.symm ⟨cv ψ y, side_lower_sub_W ψ hy_side⟩ = y :=
                symm_apply_cv_any ψ y (side_lower_sub_W ψ hy_side)
              rw [hE]
      _ = (s : ℝ) := rfl
  exact hvalFun

/-- Map `{r // r ∈ Ioo 0 u}` (with `u ≤ 1`) into `ORI` is continuous. -/
theorem interval_into_ORI_cont {u : ℝ} (hu1 : u ≤ 1) :
    Continuous (fun r : {r : ℝ // r ∈ Set.Ioo 0 u} =>
      (⟨(r : ℝ), ⟨(Set.mem_Ioo.mp r.2).1, by
        have : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
        linarith⟩⟩ : ORI)) := by
  exact Continuous.subtype_mk continuous_subtype_val (fun r => ⟨(Set.mem_Ioo.mp r.2).1, by
    have : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
    linarith⟩)

/-- Map `{s // s ∈ Ioo 0 c₀}` (with `c₀ < 1`) into `ORI` is continuous. -/
theorem interval_into_ORI_cont_c {c₀ : ℝ} (hc₀₁ : c₀ < 1) :
    Continuous (fun s : {s : ℝ // s ∈ Set.Ioo 0 c₀} =>
      (⟨(s : ℝ), ⟨(Set.mem_Ioo.mp s.2).1, by
        have : (s : ℝ) < c₀ := (Set.mem_Ioo.mp s.2).2
        linarith⟩⟩ : ORI)) := by
  exact Continuous.subtype_mk continuous_subtype_val (fun s => ⟨(Set.mem_Ioo.mp s.2).1, by
    have : (s : ℝ) < c₀ := (Set.mem_Ioo.mp s.2).2
    linarith⟩)

/-- `lowerFun` is continuous. -/
theorem lowerFun_cont (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u) :
    Continuous (lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu) := by
  let D := {r : ℝ // r ∈ Set.Ioo 0 u}
  let f1 : D → ORI := fun r =>
    ⟨(r : ℝ), ⟨(Set.mem_Ioo.mp r.2).1, by
      have : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
      linarith⟩⟩
  have hf1c : Continuous f1 := by
    dsimp [f1, D]
    exact interval_into_ORI_cont hu1
  have hcv_cont : Continuous (cv e) := ChartVal.chartVal_continuous e
  have sp : ∀ r : D, cv e (f1 r) ∈ W := fun r =>
    side_lower_sub_W ψ
      ((coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu (f1 r)).mpr
        (Set.mem_Ioo.mp r.2))
  have hpoint : Continuous (fun r : D => (⟨cv e (f1 r), sp r⟩ : {x : X // x ∈ W})) := by
    exact Continuous.subtype_mk (hcv_cont.comp hf1c) sp
  have hval_cont : Continuous (fun r : D => (ψ.symm ⟨cv e (f1 r), sp r⟩ : ORI).1) := by
    have h1 : Continuous (fun r : D => (ψ.symm ⟨cv e (f1 r), sp r⟩ : ORI)) :=
      ψ.symm.continuous.comp hpoint
    exact continuous_subtype_val.comp h1
  change Continuous (lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu)
  exact Continuous.subtype_mk
    (by simpa [lowerFun, f1, sp] using hval_cont)
    (fun r => ⟨(ψ.symm ⟨cv e (f1 r), sp r⟩ : ORI).2.1, by
      have hr_side : cv e (f1 r) ∈ ChartVal.sub ψ 0 c₀ :=
        (coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu (f1 r)).mpr
          (Set.mem_Ioo.mp r.2)
      exact ψcoord_lt_of_mem_lower ψ hc₀₀ hc₀₁ (sp r) hr_side⟩)

/-- `lowerInv` is continuous. -/
theorem lowerInv_cont (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u) :
    Continuous (lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu) := by
  let C := {s : ℝ // s ∈ Set.Ioo 0 c₀}
  let g1 : C → ORI := fun s =>
    ⟨(s : ℝ), ⟨(Set.mem_Ioo.mp s.2).1, by
      have : (s : ℝ) < c₀ := (Set.mem_Ioo.mp s.2).2
      linarith⟩⟩
  have hg1c : Continuous g1 := by
    dsimp [g1, C]
    exact interval_into_ORI_cont_c hc₀₁
  have hcv_cont : Continuous (cv ψ) := ChartVal.chartVal_continuous ψ
  have hpP : ∀ s : C, cv ψ (g1 s) ∈ P := fun s =>
    hLP (by
      rw [ChartVal.mem_sub]
      exact ⟨g1 s, (Set.mem_Ioo.mp s.2), rfl⟩)
  have hpointP : Continuous (fun s : C => (⟨cv ψ (g1 s), hpP s⟩ : {x : X // x ∈ P})) := by
    exact Continuous.subtype_mk (hcv_cont.comp hg1c) hpP
  have hval_cont : Continuous (fun s : C => (lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu s).1) := by
    change Continuous (fun s : C => (e.symm ⟨cv ψ (g1 s), hpP s⟩ : ORI).1)
    have h1 : Continuous (fun s : C => (e.symm ⟨cv ψ (g1 s), hpP s⟩ : ORI)) :=
      e.symm.continuous.comp hpointP
    exact continuous_subtype_val.comp h1
  exact Continuous.subtype_mk hval_cont (fun s => (lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu s).2)

/-- **Lower-side transfer homeomorphism** `(0,u) ≃ₜ (0,c₀)`. -/
noncomputable def lowerHomeo (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u) :
    ({r : ℝ // r ∈ Set.Ioo 0 u}) ≃ₜ ({s : ℝ // s ∈ Set.Ioo 0 c₀}) := by
  let e0 : ({r : ℝ // r ∈ Set.Ioo 0 u}) ≃ ({s : ℝ // s ∈ Set.Ioo 0 c₀}) :=
    { toFun := lowerFun e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu
      invFun := lowerInv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu
      left_inv := lower_left_inv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu
      right_inv := lower_right_inv e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu }
  exact { toEquiv := e0
          continuous_toFun := lowerFun_cont e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu
          continuous_invFun := lowerInv_cont e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu }

/-- value identity of `lowerHomeo` at a domain element. -/
theorem lowerHomeo_val (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u)
    (r : {r : ℝ // r ∈ Set.Ioo 0 u}) :
    (lowerHomeo e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu r : ℝ) =
      (ψ.symm ⟨cv e ⟨(r : ℝ), ⟨(Set.mem_Ioo.mp r.2).1, by
        have : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
        linarith⟩⟩,
        side_lower_sub_W ψ ((coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu
          ⟨(r : ℝ), ⟨(Set.mem_Ioo.mp r.2).1, by
            have : (r : ℝ) < u := (Set.mem_Ioo.mp r.2).2
            linarith⟩⟩).mpr ⟨(Set.mem_Ioo.mp r.2).1, (Set.mem_Ioo.mp r.2).2⟩)⟩ : ORI).1 := by
  rfl


/-- The `ψ`-chart window over the real interval `(lo,hi)`. -/
def chartWindow (W : Set X) (ψ : ORI ≃ₜ {x : X // x ∈ W}) (lo hi : ℝ) : Set X :=
  cv ψ '' {s : ORI | (s : ℝ) ∈ Set.Ioo lo hi}

/-- The chart window is open (open map + open coordinate set). -/
theorem chartWindow_isOpen (W : Set X) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    (hWopen : IsOpen W) (lo hi : ℝ) : IsOpen (chartWindow W ψ lo hi) := by
  have hpre : IsOpen ({s : ORI | (s : ℝ) ∈ Set.Ioo lo hi} : Set ORI) :=
    (continuous_subtype_val.isOpen_preimage (Set.Ioo lo hi) isOpen_Ioo)
  have hom : IsOpenMap (cv ψ) := by
    change IsOpenMap (fun t : ORI => ((cv ψ t : X))) 
    simpa [cv] using (ChartVal.chartVal_isOpenMap ψ hWopen)
  dsimp [chartWindow]
  exact hom {s : ORI | (s : ℝ) ∈ Set.Ioo lo hi} hpre

/-- A point with `ψ`-coordinate in `(lo,hi)` lies in the window. -/
theorem mem_chartWindow_of_coord (W : Set X) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {p : X} (hpW : p ∈ W) {lo hi : ℝ}
    (h : (ψ.symm ⟨p, hpW⟩ : ORI).1 ∈ Set.Ioo lo hi) :
    p ∈ chartWindow W ψ lo hi := by
  dsimp [chartWindow]
  let s : ORI := ψ.symm ⟨p, hpW⟩
  refine ⟨s, h, ?_⟩
  have hh := congrArg (fun w : {x : X // x ∈ W} => (w : X)) (ψ.apply_symm_apply ⟨p, hpW⟩)
  change cv ψ s = p
  exact hh


/-- value identity of the lower transfer at a tail point `t`. -/
theorem lowerHomeo_val_tail (e : ORI ≃ₜ {x : X // x ∈ P}) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u)
    (t : ORI) (htu : (t : ℝ) < u) :
    (lowerHomeo e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu ⟨(t : ℝ), ⟨t.2.1, htu⟩⟩ : ℝ) =
      (ψ.symm ⟨cv e t, side_lower_sub_W ψ ((coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu t).mpr ⟨t.2.1, htu⟩)⟩ : ORI).1 := by
  rfl


/-- **Left-end tail enters every chart window (lower side).** -/
theorem left_tail_lower (e : ORI ≃ₜ {x : X // x ∈ P}) (hPopen : IsOpen P)
    (W : Set X) (hWopen : IsOpen W) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hLP : ChartVal.sub ψ 0 c₀ ⊆ P)
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ 0 c₀}) = Set.Ioo 0 u)
    (hattL : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a))
    {η : ℝ} (hη₀ : 0 < η) (hηc : η < c₀) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ORI, (t : ℝ) < δ → cv e t ∈ chartWindow W ψ (c₀ - η) (c₀ + η) := by
  classical
  let F : ({r : ℝ // r ∈ Set.Ioo 0 u}) ≃ₜ ({s : ℝ // s ∈ Set.Ioo 0 c₀}) :=
    lowerHomeo e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu
  rcases (Commons.Topology.Homeomorph.intervalHomeo_coord_strictMono_or_anti (a := 0) (b := u) (c := 0)
      (d := c₀) hu hc₀₀ F) with hmono | hanti
  · -- INCREASING: the tail escapes below c₀ − η, contradicting left attraction
    rcases (real_tail_bad_inc (u := u) (lo := 0) (c := c₀) (η := η) hu hu1 hc₀₀
      hη₀ (by linarith) F hmono) with ⟨δ₀, hδ₀₀, hδ₀u, hbad⟩
    let W' : Set X := chartWindow W ψ (c₀ - η / 2) (c₀ + η / 2)
    have hW'open : IsOpen W' := chartWindow_isOpen W ψ hWopen (c₀ - η / 2) (c₀ + η / 2)
    have hzW' : cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ W' := by
      dsimp [W', chartWindow]
      refine ⟨⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩, ⟨by linarith, by linarith⟩, rfl⟩
    have hδ₀₁ : δ₀ < 1 := lt_of_lt_of_le hδ₀u hu1
    have hne := (mem_closure_iff).mp (hattL δ₀ hδ₀₀ hδ₀₁) W' hW'open hzW'
    rcases hne with ⟨x, hxW', hxsub⟩
    rw [ChartVal.mem_sub] at hxsub
    rcases hxsub with ⟨t, ht, hxeq⟩
    have htδ : (t : ℝ) < δ₀ := ht.2
    have htu : (t : ℝ) < u := lt_trans htδ hδ₀u
    have hF : (F ⟨(t : ℝ), ⟨ht.1, htu⟩⟩ : ℝ) < c₀ - η := hbad ⟨(t : ℝ), ⟨ht.1, htu⟩⟩ htδ
    -- x ∈ W' gives a ψ-coordinate s ∈ window with cv ψ s = x = cv e t
    rcases hxW' with ⟨s, hswin, hxeqψ⟩
    have hcv_eq : cv ψ s = cv e t := by
      rw [hxeqψ]
      exact hxeq.symm
    have hpWt : cv e t ∈ W := by
      rw [← hcv_eq]
      exact (ψ s).2
    have hcoord : (ψ.symm ⟨cv e t, hpWt⟩ : ORI).1 = (s : ℝ) := by
      have hsymm : ψ.symm ⟨cv ψ s, (ψ s).2⟩ = s := ψ.symm_apply_apply s
      have hpair : (⟨cv e t, hpWt⟩ : {x : X // x ∈ W}) = ⟨cv ψ s, (ψ s).2⟩ := by
        apply Subtype.ext
        exact hcv_eq.symm
      rw [hpair, hsymm]
    have hFv : (F ⟨(t : ℝ), ⟨ht.1, htu⟩⟩ : ℝ) =
        (ψ.symm ⟨cv e t, side_lower_sub_W ψ ((coords_eq_iff_mem (e := e)
          (side := ChartVal.sub ψ 0 c₀) (u := u) hcu t).mpr ⟨ht.1, htu⟩)⟩ : ORI).1 :=
      lowerHomeo_val_tail e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu t htu
    have hFcoord : (F ⟨(t : ℝ), ⟨ht.1, htu⟩⟩ : ℝ) = (s : ℝ) := by
      rw [hFv]
      calc
        (ψ.symm ⟨cv e t, side_lower_sub_W ψ ((coords_eq_iff_mem (e := e)
          (side := ChartVal.sub ψ 0 c₀) (u := u) hcu t).mpr ⟨ht.1, htu⟩)⟩ : ORI).1
            = (ψ.symm ⟨cv e t, hpWt⟩ : ORI).1 := by rfl
        _ = (s : ℝ) := hcoord
    have hbig : c₀ - η / 2 < (F ⟨(t : ℝ), ⟨ht.1, htu⟩⟩ : ℝ) := by
      rw [hFcoord]
      exact hswin.1
    linarith
  · -- DECREASING: the tail enters the window
    rcases (real_tail_good_anti (u := u) (lo := 0) (c := c₀) (η := η) hu hu1 hc₀₀
      hη₀ (by linarith) F hanti) with ⟨δ, hδ₀, hδu, hgood⟩
    refine ⟨δ, hδ₀, ?_⟩
    intro t htδ
    have htu : (t : ℝ) < u := lt_trans htδ hδu
    let r : {r : ℝ // r ∈ Set.Ioo 0 u} := ⟨(t : ℝ), ⟨t.2.1, htu⟩⟩
    have hwin : (F r : ℝ) ∈ Set.Ioo (c₀ - η) (c₀ + η) := hgood r htδ
    have hpW : cv e t ∈ W :=
      side_lower_sub_W ψ ((coords_eq_iff_mem (e := e) (side := ChartVal.sub ψ 0 c₀) (u := u) hcu t).mpr ⟨t.2.1, htu⟩)
    have hcoord : (ψ.symm ⟨cv e t, hpW⟩ : ORI).1 ∈ Set.Ioo (c₀ - η) (c₀ + η) := by
      have hFv : (F r : ℝ) =
          (ψ.symm ⟨cv e t, side_lower_sub_W ψ ((coords_eq_iff_mem (e := e)
            (side := ChartVal.sub ψ 0 c₀) (u := u) hcu t).mpr ⟨t.2.1, htu⟩)⟩ : ORI).1 :=
        lowerHomeo_val_tail e ψ hc₀₀ hc₀₁ hu hu1 hLP hcu t htu
      rw [← hFv]
      exact hwin
    exact mem_chartWindow_of_coord W ψ hpW hcoord


/-- Reflection `t ↦ 1 − t` of the open unit interval. -/
noncomputable def reflORI : ORI ≃ₜ ORI where
  toFun := fun t => ⟨1 - (t : ℝ), ⟨by have : (t : ℝ) < 1 := t.2.2; linarith,
    by have : 0 < (t : ℝ) := t.2.1; linarith⟩⟩
  invFun := fun t => ⟨1 - (t : ℝ), ⟨by have : (t : ℝ) < 1 := t.2.2; linarith,
    by have : 0 < (t : ℝ) := t.2.1; linarith⟩⟩
  left_inv := by
    intro t
    apply Subtype.ext
    ring
  right_inv := by
    intro t
    apply Subtype.ext
    ring
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_const.sub continuous_subtype_val)
      (fun t => ⟨by
          change 0 < 1 - (t : ℝ)
          have h1 : (t : ℝ) < 1 := (Set.mem_Ioo.mp t.2).2
          linarith,
        by
          change 1 - (t : ℝ) < 1
          have h2 : 0 < (t : ℝ) := (Set.mem_Ioo.mp t.2).1
          linarith⟩)
  continuous_invFun := by
    exact Continuous.subtype_mk (continuous_const.sub continuous_subtype_val)
      (fun t => ⟨by
          change 0 < 1 - (t : ℝ)
          have h1 : (t : ℝ) < 1 := (Set.mem_Ioo.mp t.2).2
          linarith,
        by
          change 1 - (t : ℝ) < 1
          have h2 : 0 < (t : ℝ) := (Set.mem_Ioo.mp t.2).1
          linarith⟩)

/-- value of the reflection. -/
theorem reflORI_val (t : ORI) : (reflORI t : ℝ) = 1 - (t : ℝ) := by
  rfl

/-- reflection is an involution. -/
theorem reflORI_inv (t : ORI) : reflORI (reflORI t) = t := by
  apply Subtype.ext
  dsimp [reflORI]
  ring

/-- The reflected chart maps `ψ`-upper side onto the reflected lower side. -/
theorem side_upper_as_reflected (W : Set X) (ψ : ORI ≃ₜ {x : X // x ∈ W}) (c₀ : ℝ) :
    ChartVal.sub (reflORI.trans ψ) 0 (1 - c₀) = ChartVal.sub ψ c₀ 1 := by
  ext x
  constructor
  · intro hx
    rw [ChartVal.mem_sub] at hx
    rcases hx with ⟨t, ht, hxeq⟩
    let s : ORI := reflORI t
    have hs1 : c₀ < (s : ℝ) := by
      dsimp [s]
      rw [reflORI_val]
      linarith [ht.2]
    have hs2 : (s : ℝ) < 1 := s.2.2
    rw [ChartVal.mem_sub]
    refine ⟨s, ⟨hs1, hs2⟩, ?_⟩
    have hφ : cv (reflORI.trans ψ) t = cv ψ (reflORI t) := by
      rfl
    dsimp [s]
    exact hφ.symm.trans hxeq
  · intro hx
    rw [ChartVal.mem_sub] at hx
    rcases hx with ⟨s, hs, hxeq⟩
    have hsc : c₀ < (s : ℝ) := (Set.mem_Ioo.mp hs).1
    have hs1v : (s : ℝ) < 1 := (Set.mem_Ioo.mp hs).2
    let t : ORI := reflORI s
    have ht1 : (t : ℝ) < 1 - c₀ := by
      dsimp [t]
      rw [reflORI_val]
      linarith [hsc]
    have ht0 : 0 < (t : ℝ) := by
      dsimp [t]
      rw [reflORI_val]
      linarith [hs1v]
    rw [ChartVal.mem_sub]
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    have hφ : cv (reflORI.trans ψ) t = cv ψ s := by
      dsimp [t]
      have h1 : (reflORI.trans ψ) (reflORI s) = ψ (reflORI (reflORI s)) := by rfl
      have h2 : (reflORI.trans ψ) (reflORI s) = ψ s := by
        rw [h1, reflORI_inv]
      exact congrArg (fun w : {x : X // x ∈ W} => (w : X)) h2
    exact hφ.trans hxeq


/-- The reflected `ψ`-window over `(1-c₀-η, 1-c₀+η)` equals the
`ψ`-window over `(c₀-η, c₀+η)`. -/
theorem chartWindow_refl (W : Set X) (ψ : ORI ≃ₜ {x : X // x ∈ W}) (c₀ η : ℝ) :
    chartWindow W (reflORI.trans ψ) (1 - c₀ - η) (1 - c₀ + η) =
      chartWindow W ψ (c₀ - η) (c₀ + η) := by
  ext x
  constructor
  · intro hx
    dsimp [chartWindow] at hx
    rcases hx with ⟨t, ht, hxeq⟩
    let s : ORI := reflORI t
    have hs1 : c₀ - η < (s : ℝ) := by
      dsimp [s]
      rw [reflORI_val]
      linarith [ht.1, ht.2]
    have hs2 : (s : ℝ) < c₀ + η := by
      dsimp [s]
      rw [reflORI_val]
      linarith [ht.1, ht.2]
    dsimp [chartWindow]
    refine ⟨s, ⟨hs1, hs2⟩, ?_⟩
    dsimp [s]
    have hφ : cv (reflORI.trans ψ) t = cv ψ (reflORI t) := by rfl
    exact hφ.symm.trans hxeq
  · intro hx
    dsimp [chartWindow] at hx
    rcases hx with ⟨s, hs, hxeq⟩
    let t : ORI := reflORI s
    have ht1 : 1 - c₀ - η < (t : ℝ) := by
      dsimp [t]
      rw [reflORI_val]
      linarith [hs.1, hs.2]
    have ht2 : (t : ℝ) < 1 - c₀ + η := by
      dsimp [t]
      rw [reflORI_val]
      linarith [hs.1, hs.2]
    dsimp [chartWindow]
    refine ⟨t, ⟨ht1, ht2⟩, ?_⟩
    dsimp [t]
    have hφ : cv (reflORI.trans ψ) (reflORI s) = cv ψ s := by
      have h1 : (reflORI.trans ψ) (reflORI s) = ψ (reflORI (reflORI s)) := by rfl
      have h2 : (reflORI.trans ψ) (reflORI s) = ψ s := by
        rw [h1, reflORI_inv]
      exact congrArg (fun w : {x : X // x ∈ W} => (w : X)) h2
    exact hφ.trans hxeq

/-- Identity relating the reflected chart point at `1-c₀` with the
`ψ`-point at `c₀`. -/
theorem cv_refl_at (W : Set X) (ψ : ORI ≃ₜ {x : X // x ∈ W}) (c₀ : ℝ)
    (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) :
    cv (reflORI.trans ψ) ⟨1 - c₀, ⟨by linarith, by linarith⟩⟩ = cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
  have hφ : cv (reflORI.trans ψ) ⟨1 - c₀, ⟨by linarith, by linarith⟩⟩ =
      cv ψ (reflORI ⟨1 - c₀, ⟨by linarith, by linarith⟩⟩) := by rfl
  rw [hφ]
  congr 1
  apply Subtype.ext
  dsimp [reflORI]
  ring


/-- **Left-end tail enters every chart window (upper side).** -/
theorem left_tail_upper (e : ORI ≃ₜ {x : X // x ∈ P}) (hPopen : IsOpen P)
    (W : Set X) (hWopen : IsOpen W) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ u : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1) (hu : 0 < u) (hu1 : u ≤ 1)
    (hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩})
    (hcu : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ c₀ 1}) = Set.Ioo 0 u)
    (hattL : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a))
    {η : ℝ} (hη₀ : 0 < η) (hη : c₀ + η < 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ORI, (t : ℝ) < δ → cv e t ∈ chartWindow W ψ (c₀ - η) (c₀ + η) := by
  classical
  let ψ' : ORI ≃ₜ {x : X // x ∈ W} := reflORI.trans ψ
  let c₀' : ℝ := 1 - c₀
  have hc'₀₀ : 0 < c₀' := by dsimp [c₀']; linarith
  have hc'₀₁ : c₀' < 1 := by dsimp [c₀']; linarith
  have hLP' : ChartVal.sub ψ' 0 c₀' ⊆ P := by
    dsimp [c₀']
    rw [side_upper_as_reflected W ψ c₀]
    exact (sides_subset_P ψ hc₀₀ hc₀₁ hstruct).2
  have hcu' : ((fun t : ORI => (t : ℝ)) '' {t : ORI | cv e t ∈ ChartVal.sub ψ' 0 c₀'}) =
      Set.Ioo 0 u := by
    dsimp [c₀']
    rw [side_upper_as_reflected W ψ c₀]
    exact hcu
  have hz'eq : cv ψ' ⟨c₀', ⟨hc'₀₀, hc'₀₁⟩⟩ = cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
    dsimp [ψ', c₀']
    exact cv_refl_at W ψ c₀ hc₀₀ hc₀₁
  have hattL' : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ' ⟨c₀', ⟨hc'₀₀, hc'₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a) := by
    intro a ha0 ha1
    rw [hz'eq]
    exact hattL a ha0 ha1
  have hη' : η < c₀' := by dsimp [c₀']; linarith
  rcases (left_tail_lower e hPopen W hWopen ψ' hc'₀₀ hc'₀₁ hu hu1 hLP' hcu' hattL' hη₀ hη')
    with ⟨δ, hδ₀, htail⟩
  refine ⟨δ, hδ₀, ?_⟩
  intro t htδ
  have hm : cv e t ∈ chartWindow W ψ' (c₀' - η) (c₀' + η) := htail t htδ
  rw [← chartWindow_refl W ψ c₀ η]
  dsimp [c₀'] at hm
  exact hm


/-- A window whose coordinates map into `V` is contained in `V`. -/
theorem chartWindow_subset (W : Set X) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {V : Set X} {lo hi : ℝ}
    (hmap : ∀ s : ORI, (s : ℝ) ∈ Set.Ioo lo hi → cv ψ s ∈ V) :
    chartWindow W ψ lo hi ⊆ V := by
  intro x hx
  dsimp [chartWindow] at hx
  rcases hx with ⟨s, hs, hxeq⟩
  rw [← hxeq]
  exact hmap s hs

/-- **Left-end convergence**: for every open neighbourhood `V` of the
boundary point, the left tail of the arc eventually lies in `V`. -/
theorem left_tail_converges (e : ORI ≃ₜ {x : X // x ∈ P}) (hPopen : IsOpen P)
    (W : Set X) (hWopen : IsOpen W) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩})
    (hattL : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a))
    {V : Set X} (hVopen : IsOpen V) (hzV : cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, (t : ℝ) < δ → cv e t ∈ V := by
  classical
  rcases coord_interval_inside_open ψ hVopen hc₀₀ hc₀₁ hzV with
    ⟨η, hη₀, hη₀₂, hη₀₃, hηc, hηc', hηmap⟩
  have hwin_sub : chartWindow W ψ (c₀ - η) (c₀ + η) ⊆ V := by
    apply chartWindow_subset
    intro s hs
    exact hηmap s hs.1 hs.2
  rcases initial_side_coords e hPopen W hWopen ψ hc₀₀ hc₀₁ hstruct hattL with hlow | hup
  · rcases hlow with ⟨u, hu, hu1, hcu⟩
    have hLP : ChartVal.sub ψ 0 c₀ ⊆ P := (sides_subset_P ψ hc₀₀ hc₀₁ hstruct).1
    rcases (left_tail_lower e hPopen W hWopen ψ hc₀₀ hc₀₁ hu hu1 hLP hcu hattL hη₀ hηc)
      with ⟨δ, hδ₀, htail⟩
    refine ⟨δ, hδ₀, ?_⟩
    intro t ht
    exact hwin_sub (htail t ht)
  · rcases hup with ⟨u, hu, hu1, hcu⟩
    have hηcsum : c₀ + η < 1 := by linarith [hηc']
    rcases (left_tail_upper e hPopen W hWopen ψ hc₀₀ hc₀₁ hu hu1 hstruct hcu hattL hη₀ hηcsum)
      with ⟨δ, hδ₀, htail⟩
    refine ⟨δ, hδ₀, ?_⟩
    intro t ht
    exact hwin_sub (htail t ht)


/-- **Right-end convergence**: for every open neighbourhood `V` of the
boundary point, the right tail of the arc eventually lies in `V`.  (Mirror
of the left end through the arc reflection.) -/
theorem right_tail_converges (e : ORI ≃ₜ {x : X // x ∈ P}) (hPopen : IsOpen P)
    (W : Set X) (hWopen : IsOpen W) (ψ : ORI ≃ₜ {x : X // x ∈ W})
    {c₀ : ℝ} (hc₀₀ : 0 < c₀) (hc₀₁ : c₀ < 1)
    (hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩})
    (hattR : ∀ b : ℝ, 0 < b → b < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e b 1))
    {V : Set X} (hVopen : IsOpen V) (hzV : cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, 1 - δ < (t : ℝ) → cv e t ∈ V := by
  classical
  let e' : ORI ≃ₜ {x : X // x ∈ P} := reflORI.trans e
  have hattL' : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e' 0 a) := by
    intro a ha0 ha1
    have hne := hattR (1 - a) (by linarith) (by linarith)
    have hsubEq : ChartVal.sub e' 0 a = ChartVal.sub e (1 - a) 1 := by
      dsimp [e']
      convert side_upper_as_reflected P e (1 - a) using 1
      ring
    rw [hsubEq]
    exact hne
  rcases (left_tail_converges e' hPopen W hWopen ψ hc₀₀ hc₀₁ hstruct hattL' hVopen hzV)
    with ⟨δ, hδ₀, htail'⟩
  refine ⟨δ, hδ₀, ?_⟩
  intro t ht
  have hts : (reflORI t : ℝ) < δ := by
    rw [reflORI_val]
    linarith [ht]
  have hm := htail' (reflORI t) hts
  have hcv : cv e' (reflORI t) = cv e t := by
    dsimp [e']
    have h1 : (reflORI.trans e) (reflORI t) = e (reflORI (reflORI t)) := by rfl
    have h2 : (reflORI.trans e) (reflORI t) = e t := by
      rw [h1, reflORI_inv]
    exact congrArg (fun w : {x : X // x ∈ P} => (w : X)) h2
  rw [hcv] at hm
  exact hm

end TailConv

end Commons.Topology.OneManifold


open Set
open scoped Topology

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.Topology.OneManifold

namespace BdryExt

open TailConv

variable {X : Type*} [TopologicalSpace X] [T2Space X] {P : Set X}

/-- A closed sub-arc `subClosed e a b` (`0 < a ≤? ≤ b < 1`) is compact:
it is the continuous image of the compact interval `[a,b]`. -/
lemma subClosed_isCompact (e : ORI ≃ₜ {x : X // x ∈ P}) {a b : ℝ}
    (h0a : 0 < a) (hb1 : b < 1) : IsCompact (ChartVal.subClosed e a b) := by
  let C := {r : ℝ // r ∈ Set.Icc a b}
  haveI : CompactSpace C := by
    dsimp [C]
    exact isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact (Set.Icc a b : Set ℝ))
  have hmem : ∀ r : ℝ, r ∈ Set.Icc a b → r ∈ Set.Ioo (0 : ℝ) 1 := by
    intro r hr
    exact ⟨lt_of_lt_of_le h0a hr.1, lt_of_le_of_lt hr.2 hb1⟩
  let g : C → X := fun r => cv e ⟨(r : ℝ), hmem (r : ℝ) r.2⟩
  have hinner : Continuous (fun r : C => (⟨(r : ℝ), hmem (r : ℝ) r.2⟩ : ORI)) :=
    Continuous.subtype_mk continuous_subtype_val (fun r => hmem (r : ℝ) r.2)
  have hgcont : Continuous g := by
    dsimp [g]
    exact (ChartVal.chartVal_continuous e).comp hinner
  have himg : g '' Set.univ = ChartVal.subClosed e a b := by
    ext y
    constructor
    · rintro ⟨r, -, rfl⟩
      rw [ChartVal.mem_subClosed]
      exact ⟨⟨(r : ℝ), hmem (r : ℝ) r.2⟩, r.2, rfl⟩
    · intro hy
      rw [ChartVal.mem_subClosed] at hy
      rcases hy with ⟨s, hs, hseq⟩
      refine ⟨⟨(s : ℝ), hs⟩, trivial, ?_⟩
      dsimp [g]
      rw [← hseq]
  rw [← himg]
  exact IsCompact.image isCompact_univ hgcont

/-- **Global close-off**: a maximal proper open arc forces `X` to be
compact.  (Unique boundary point `z₀`; both arc-ends converge to `z₀`
(TailConv); an open neighbourhood `U₀` of `z₀` absorbs the two tails, the
rest `P ∖ U₀` lies in a compact closed sub-arc, so every open cover has a
finite subcover.) -/
theorem no_extension_of_proper_open_arc_implies_compact {X : Type*}
    [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [Nonempty X]
    [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (eP : Nonempty (ORI ≃ₜ P)) (hPopen : IsOpen P)
    (hPproper : P ≠ Set.univ)
    (hPmax : ¬ ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q)) :
    CompactSpace X := by
  classical
  let e := Classical.choice eP
  rcases maximal_arc_ends_close hLoc eP hPopen hPproper hPmax with ⟨z₀, hz₀P, hattL, hattR, hunique⟩
  have hdense : closure P = Set.univ := maximal_arc_dense hLoc eP hPopen hPproper hPmax
  have hz₀b : z₀ ∈ closure P \ P := ⟨by rw [hdense]; trivial, hz₀P⟩
  rcases boundary_points_isolated_of_maximal hLoc eP hPopen hPproper hPmax hz₀b with
    ⟨W, hWopen, hz₀W, ψ, hEq⟩
  let c₀ : ℝ := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).1
  have hc₀₀ : 0 < c₀ := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).2.1
  have hc₀₁ : c₀ < 1 := (ψ.symm ⟨z₀, hz₀W⟩ : ORI).2.2
  have hz₀ψ : z₀ = cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ := by
    have hh := congrArg (fun w : {x : X // x ∈ W} => (w : X))
      (ψ.apply_symm_apply ⟨z₀, hz₀W⟩)
    change z₀ = (ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ : {x : X // x ∈ W}).1
    dsimp [c₀, cv]
    exact hh.symm
  have hstruct : P ∩ W = W \ {cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩} := by
    simpa [hz₀ψ] using hEq
  have hattLψ : ∀ a : ℝ, 0 < a → a < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e 0 a) := by
    intro a ha0 ha1
    rw [← hz₀ψ]
    exact hattL a ha0 ha1
  have hattRψ : ∀ b : ℝ, 0 < b → b < 1 →
      cv ψ ⟨c₀, ⟨hc₀₀, hc₀₁⟩⟩ ∈ closure (ChartVal.sub e b 1) := by
    intro b hb0 hb1
    rw [← hz₀ψ]
    exact hattR b hb0 hb1
  have hleftConv : ∀ V : Set X, IsOpen V → z₀ ∈ V →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, (t : ℝ) < δ → cv e t ∈ V := by
    intro V hVopen hzV
    exact left_tail_converges e hPopen W hWopen ψ hc₀₀ hc₀₁ hstruct hattLψ hVopen
      (by simpa [hz₀ψ] using hzV)
  have hrightConv : ∀ V : Set X, IsOpen V → z₀ ∈ V →
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ORI, 1 - δ < (t : ℝ) → cv e t ∈ V := by
    intro V hVopen hzV
    exact right_tail_converges e hPopen W hWopen ψ hc₀₀ hc₀₁ hstruct hattRψ hVopen
      (by simpa [hz₀ψ] using hzV)
  exact isCompact_univ_iff.mp (by
    rw [isCompact_iff_finite_subcover]
    intro ι U hUopen hcover
    have hz₀cov : z₀ ∈ ⋃ i, U i := hcover trivial
    rcases (Set.mem_iUnion.mp hz₀cov) with ⟨i₀, hz₀Ui₀⟩
    rcases hleftConv (U i₀) (hUopen i₀) hz₀Ui₀ with ⟨δ₁, hδ₁₀, hleft⟩
    rcases hrightConv (U i₀) (hUopen i₀) hz₀Ui₀ with ⟨δ₂, hδ₂₀, hright⟩
    let a : ℝ := min δ₁ (1 / 2)
    let b : ℝ := 1 - min δ₂ (1 / 2)
    have ha₀ : 0 < a := by
      dsimp [a]
      exact lt_min hδ₁₀ (by norm_num)
    have hb₁ : b < 1 := by
      dsimp [b]
      have hm : 0 < min δ₂ (1 / 2) := lt_min hδ₂₀ (by norm_num)
      linarith
    have hab : a ≤ b := by
      dsimp [a, b]
      have h1 : min δ₁ (1 / 2) ≤ 1 / 2 := min_le_right δ₁ (1 / 2)
      have h2 : 1 / 2 ≤ 1 - min δ₂ (1 / 2) := by
        have hm : min δ₂ (1 / 2) ≤ 1 / 2 := min_le_right δ₂ (1 / 2)
        linarith
      linarith
    have hrest : (P \ (U i₀)) ⊆ ChartVal.subClosed e a b := by
      intro x hx
      rcases hx with ⟨hxP, hxU⟩
      have hxP' : x ∈ P := hxP
      have hxrange : x ∈ Set.range (cv e) := by
        rw [ChartVal.chartVal_range e]
        exact hxP'
      rcases hxrange with ⟨t, rfl⟩
      rw [ChartVal.mem_subClosed]
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · -- (t:ℝ) ≥ a
        by_contra hlt
        have hta : (t : ℝ) < a := lt_of_not_ge hlt
        have htδ : (t : ℝ) < δ₁ := lt_of_lt_of_le hta (by dsimp [a]; exact min_le_left δ₁ (1 / 2))
        exact hxU (hleft t htδ)
      · -- (t:ℝ) ≤ b
        by_contra hgt
        have htb : b < (t : ℝ) := lt_of_not_ge hgt
        have htδ : 1 - δ₂ < (t : ℝ) := by
          have hle : 1 - δ₂ ≤ b := by
            dsimp [b]
            have hm : min δ₂ (1 / 2) ≤ δ₂ := min_le_left δ₂ (1 / 2)
            linarith
          exact lt_of_le_of_lt hle htb
        exact hxU (hright t htδ)
    have hsubcov : ChartVal.subClosed e a b ⊆ ⋃ i, U i := by
      intro x hx
      exact hcover trivial
    rcases (isCompact_iff_finite_subcover.mp (subClosed_isCompact e ha₀ hb₁)) U hUopen hsubcov
      with ⟨t, htsub⟩
    refine ⟨insert i₀ t, ?_⟩
    intro x hx
    by_cases hxU₀ : x ∈ U i₀
    · exact Set.mem_iUnion.mpr ⟨i₀, Set.mem_iUnion.mpr ⟨(by simp : i₀ ∈ insert i₀ t), hxU₀⟩⟩
    · have hxne : x ≠ z₀ := by
        intro hxz
        apply hxU₀
        rwa [hxz]
      have hxP : x ∈ P := hunique x hxne
      have hxsub : x ∈ ChartVal.subClosed e a b := hrest ⟨hxP, hxU₀⟩
      have hxt : x ∈ ⋃ i ∈ t, U i := htsub hxsub
      simp at hxt
      rcases hxt with ⟨i, hiin, hxUi⟩
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_insert_of_mem hiin, hxUi⟩⟩)

end BdryExt

end Commons.Topology.OneManifold


namespace Commons.Topology.OneManifold

/-- **One-dimensional end theory, Layer 1**: in a connected Hausdorff
second-countable locally interval-charted space, every proper open arc
extends to a strictly larger open arc, or the whole ambient space is
compact.  (Either there is an explicit extension, or the maximality
analysis of `BdryExt` shows the space is compact.) -/
theorem arc_extension_or_compact {X : Type*} [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X] [ConnectedSpace X]
    (hLoc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ lo hi : ℝ, Nonempty ({t : ℝ // t ∈ Set.Ioo lo hi} ≃ₜ U))
    {P : Set X} (hPopen : IsOpen P)
    (eP : Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ P))
    (hPproper : P ≠ Set.univ) :
    (∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧
      Nonempty ({t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1} ≃ₜ Q)) ∨ CompactSpace X := by
  classical
  by_cases hExt : ∃ Q : Set X, IsOpen Q ∧ P ⊂ Q ∧ Nonempty (ORI ≃ₜ Q)
  · exact Or.inl hExt
  · right
    exact BdryExt.no_extension_of_proper_open_arc_implies_compact hLoc eP hPopen hPproper hExt

end Commons.Topology.OneManifold
