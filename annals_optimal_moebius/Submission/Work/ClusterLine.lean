import Submission.Work.FrontierCluster
import Submission.Work.FlatSides

open OptimalMoebius Topology ContDiff
open Filter
open scoped BigOperators Matrix Topology Metric
open InnerProductGeometry

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Cluster lines avoid flat components, and one-sidedness (NEW, GREEN)

Structural consequences of the ruling-line avoidance machinery at a
DEGENERATE frontier point, needed by the flat-frontier analysis (target
(r2) of session_status41) and the flat-component trapezoid foliation:

* **`flatComponent_avoids_cluster_line`** — let `qₙ → e` be a `U`-sequence
  (points of the strip interior with `dN ≠ 0`) whose unit ruling
  directions `unitKernelDir f (qₙ)` converge to a unit vector `w`.  Then
  every flat component `C` avoids the whole cluster line `L = e + ℝ·w`:
  no flat-interior point of `C` lies on `L`.  Proof: if `z ∈ C ∩ L`,
  `z = e + s•w`, the points `pₙ := qₙ + s • unitKernelDir f (qₙ)` lie on
  the ruling lines of the `U`-points `qₙ` (which avoid `C` entirely by
  `kernel_line_avoids_flatComponent`), yet `pₙ → e + s•w = z ∈ C` (open,
  so `pₙ ∈ C` eventually) — contradiction.  (No inner products, no
  projection formula: the constant parameter `s` does all the work.)

* **`flatComponent_one_side_of_cluster_line`** — for the same `e,w`:
  `C` lies strictly on one side of the cluster line `L` (the signed
  functional `signedLineFunc e w` is nowhere zero on the preconnected
  flat component `C`, and continuous, so it has constant strict sign).

These are the first frontier-regularity-free statements relating a flat
component to the LIMIT direction of its bordering rulings: they say the
degenerate frontier point `e` sits on the boundary line `L` of the half
plane containing `C`, with `C ∩ L = ∅`.  Combined with
`degenerateFrontier_ruling_cluster_line` (uniqueness of the cluster
direction at `e`) this fixes, at every degenerate frontier point, a single
line `L(e)` through `e` that `C` avoids and that `C` lies strictly on one
side of.  Sections 6–8 add the global rigidity of the ruling-line family:
* **`cluster_lines_cross_not_in_strip`** — the limit lines of two
  approaching `U`-families cross only OUTSIDE the strip (for constant
  sequences: the ruling lines of `U`-points never cross inside `S`);
* **`u_ruling_lines_share_point_parallel`** — two ruling lines sharing a
  strip-interior point have parallel directions (kernel line uniqueness);
* **`cluster_lines_mutually_avoid`** — for two degenerate points, if
  `e₂ ∉ L(e₁)` then `e₁ ∉ L(e₂)` (no asymmetric on-line relation).
Sections 9 adds the first frontier-containment content (the h>0 half):
* **`flatComponent_shallow_bulge_parallel`** — if `e'` is a degenerate
  point (approaching `U`-sequence, unit cluster direction `w'`) on the
  `φ<0` side of the line `L(e)` through `e ∈ closure C`, with PARALLEL
  cluster line `w = ±w'`, then `C` lies strictly on the slab side of
  `L(e')`: `signedLineFunc e w e' < signedLineFunc e w z` for all
  `z ∈ C` (proof: one-sidedness of `C` w.r.t. `L(e')` + translation of the
  signed functional to the parallel line + closure passing the strict
  inequality to `e`);
* **`no_shallow_bulge_parallel`** — consequently a flat component cannot
  have both a shallow-bulge frontier point `e'` (parallel cluster line,
  positive depth) and a point strictly deeper than `e'`: the bulge forces
  all of `C` into the slab between the parallel lines.
Sections 10 starts the depth-0 regime (frontier points at depths → 0):
* **`slab_depth_zero_forces_empty`** — pure limit step: slabs
  `{φ(e'_n) < φ}` with `φ(e'_n) → 0` and `C ⊆ {φ<0}` force `C = ∅`;
* **`no_exact_parallel_depth_zero`** — degenerate frontier points at
  depths → 0 with cluster lines EXACTLY parallel to `L(e)` force `C` empty
  (each gives the shallow-bulge slab constraint, then the limit step).
Sections 11 formalizes T1′ of the depth-0 reduction
(session_status44): **`diagonal_U_sequence_from_families`** extracts, from
a sequence of approaching `U`-families `q k → eₖ → e` and a reference
`u₀ → e` with direction limit `w₀`, a strictly monotone index extraction
`φ` and a diagonal `ψ` with `q (φ m) (ψ m) → e`,
`unitKernelDir f (q (φ m) (ψ m)) → wstar`, and `wstar = ±w₀`
(`rulingCluster_dirs_parallel` at `e`).  The depth-0 checklist now has (A)
exact-parallel and (B) diagonal extraction GREEN; only (C) the
nearly-parallel 2D sign/geometry contradiction remains, built entirely
from the green ClusterLine facts — NO Codazzi machinery is needed for the
depth-0 regime.  All lemmas here hold with no regularity hypothesis.

Sections 14–16 (session 45) complete the depth-0 nearly-parallel
contradiction in BOTH orientations and package the extraction:
* **T2 / T2′** — `depth_zero_nearly_parallel_contradiction` and its mirror
  (`_mirror`): families `w'ₖ → w` resp. `w'ₖ → -w` with `C ⊆ {φ_w < 0}`,
  `z₀ ∈ C`, `e ∈ closure C`, `φ_w(eₖ) < 0`, per-k approaching families,
  `det2 w (w'ₖ) ≠ 0` ⟹ `False` (H-A convergence + H-B/H-B′ boundary sign
  vs `same_side_product`);
* **H-B / H-B′** — `boundary_value_pos_eventually` (already green) and its
  mirror `boundary_value_neg_eventually` (via
  `crossing_side_sign` / `crossing_side_sign_mirror`, the mirror obtained
  by the direction-flip trick `w̃ := -w'`, `t̃₀ := -t₀`);
* **`off_line_direction_data`** — per-k subsequential direction limits
  `W k` (with strict-mono `γ k`), level-2 `φ`, `wstar = ±w`;
* **`off_line_sequence_contradiction`** — the regime split (C: shifted
  tail → T2/T2′; A: `Nat.nth` exact-parallel extraction →
  `no_exact_parallel_depth_zero`): any off-line family sequence with
  `φ_w(eₖ) < 0` approaching `e` is impossible.
Sections 17–18 (later in session 45) resolve the sign obstruction by
making the family REFERENCE-ORIENTATION-ROBUST (option 1 of the
session_status45 Addendum): the reference `U`-sequence keeps its OWN unit
limit `w₀` and the bookkeeping base `w` is decoupled via
`hpar₀ : w = w₀ ∨ w = -w₀`.  New green entries:
* `same_side_product_robust`, `boundary_value_pos_eventually_robust`,
  `boundary_value_neg_eventually_robust` — H-B/H-C with the crossing shown
  outside the strip via R3 applied to the reference line `L(e, w₀)`
  (aligned branch: rewrite; anti branch: R3 in `w₀`-coordinates plus the
  point equality `e + τ₀₀•w₀ = e + τ₀ₖ•w`, `w₀ = -w`, `τ₀₀ = -τ₀ₖ`);
* `vertical_cluster_dir_contradiction_robust`,
  `depth_zero_robust_contradiction` (+ `_mirror`), `sign_trans`, and
  `off_line_sequence_contradiction_robust` — the whole depth-0 regime now
  runs with the reference anti-aligned to the side-pinned base;
* **`frontier_locally_on_cluster_line`** and
  **`degenerate_frontier_contained_in_cluster_line`** — THE DEPTH-0
  CLOSE-OUT: at a degenerate frontier point `e` of `flatComponent f p`
  (`e ∈ frontier C ∩ stripInterior`) there is a unit cluster direction `w`
  and `ρ > 0` with every frontier point within `ρ` of `e` on the cluster
  line `L(e)` (`signedLineFunc e w z = 0`).  Proof: side disjunction
  (positive/negative w.r.t. `w₀`) pins `w` (or `-w₀`), then
  `frontier_locally_on_cluster_line` contradicts an off-line frontier
  sequence (radii `min ρ₀ 1/(k+1)`, per-k `U`-families) via the robust
  off-line contradiction.

Build: `lake build Submission.Work.ClusterLine` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-! ## 1. A flat component avoids every cluster line of approaching rulings -/

/-- **A flat component avoids the cluster line of a converging family of
approaching rulings**: if `qₙ → e` are `U`-points whose unit ruling
directions converge to the unit vector `w`, then no flat component `C`
meets the line `e + ℝ·w` (no `z ∈ C` lies on the line). -/
theorem flatComponent_avoids_cluster_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} {q : ℕ → ℝ²}
    (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0)
    (hqe : Tendsto q atTop (𝓝 e)) {w : ℝ²} (hwnorm : ‖w‖ = 1)
    (hd : Tendsto (fun n => unitKernelDir f (q n)) atTop (𝓝 w))
    {p z : ℝ²} (hz : z ∈ flatComponent f p) (hline : ∃ s : ℝ, z = e + s • w) : False := by
  rcases hline with ⟨s, hzs⟩
  -- the points pₙ = qₙ + s • uₙ lie on the ruling line of qₙ
  let u : ℕ → ℝ² := fun n => unitKernelDir f (q n)
  -- pₙ → e + s•w = z
  have hqsu : Tendsto (fun n : ℕ => q n + s • u n) atTop (𝓝 (e + s • w)) := by
    have hsu : Tendsto (fun n : ℕ => s • u n) atTop (𝓝 (s • w)) :=
      (tendsto_const_nhds.smul hd)
    exact hqe.add hsu
  have hpz : Tendsto (fun n : ℕ => q n + s • u n) atTop (𝓝 z) := by
    simpa [hzs] using hqsu
  -- C is open and contains z, so a whole ball around z is inside C
  have hCopen : IsOpen (flatComponent f p) := isOpen_flatComponent f p
  rcases (Metric.isOpen_iff.mp hCopen) z hz with ⟨ρ, hρ, hball⟩
  -- eventually pₙ ∈ ball z ρ ⊆ C
  rcases (eventually_atTop.mp ((Metric.tendsto_nhds.mp hpz) ρ hρ)) with ⟨N, hN⟩
  -- pick the point pₙ for a large enough n: it is in C yet on the ruling
  -- line of the U-point qₙ, contradicting kernel_line_avoids_flatComponent
  let n₀ : ℕ := N
  have hpn : q n₀ + s • u n₀ ∈ Metric.ball z ρ := hN n₀ (Nat.le_refl n₀)
  have hpnC : q n₀ + s • u n₀ ∈ flatComponent f p := hball hpn
  -- the ruling line of qₙ₀ (in the kernel direction uₙ₀) avoids C
  exact kernel_line_avoids_flatComponent hf ha (x := q n₀) (w := u n₀)
    (p := p) (z := q n₀ + s • u n₀)
    (hqS n₀) (hqU n₀)
    (unitKernelDir_mem_ker hf (hqS n₀))
    (unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha (hqS n₀) (hqU n₀)))
    hpnC
    ⟨s, rfl⟩

/-! ## 2. Generic sign-constancy on a preconnected set -/

/-- A continuous real function that never vanishes on a preconnected set
has a constant strict sign on it. -/
lemma sign_constant_of_preconnected_nowhere_zero {S : Set ℝ²} (hS : IsPreconnected S)
    {φ : ℝ² → ℝ} (hφ : ContinuousOn φ S) (hne : ∀ z ∈ S, φ z ≠ 0) :
    (∀ z ∈ S, 0 < φ z) ∨ (∀ z ∈ S, φ z < 0) := by
  by_cases hpos : ∃ x ∈ S, 0 < φ x
  · left
    intro x₂ hx₂
    by_contra hnot
    have hx₂le : φ x₂ ≤ 0 := le_of_not_gt hnot
    have hx₂neg : φ x₂ < 0 := lt_of_le_of_ne hx₂le (hne x₂ hx₂)
    rcases hpos with ⟨x₁, hx₁, hx₁pos⟩
    have hIVT : Set.Icc (φ x₂) (φ x₁) ⊆ φ '' S :=
      IsPreconnected.intermediate_value hS hx₂ hx₁ hφ
    have hzero_mem : (0 : ℝ) ∈ Set.Icc (φ x₂) (φ x₁) := by
      rw [Set.mem_Icc]
      exact ⟨le_of_lt hx₂neg, le_of_lt hx₁pos⟩
    rcases hIVT hzero_mem with ⟨x₀, hx₀, hφx₀⟩
    exact hne x₀ hx₀ (by simpa using hφx₀)
  · right
    intro x₂ hx₂
    have hx₂le : φ x₂ ≤ 0 := by
      by_contra hgt
      exact hpos ⟨x₂, hx₂, lt_of_not_ge hgt⟩
    exact lt_of_le_of_ne hx₂le (hne x₂ hx₂)

/-! ## 3. The flat component lies strictly on one side of the cluster line -/

/-- The signed line functional equals the `det2` with the point difference:
`signedLineFunc q w z = det2 (z − q) w`. -/
lemma signedLineFunc_eq_det2 (q w z : ℝ²) : signedLineFunc q w z = det2 (z - q) w := by
  unfold signedLineFunc det2
  simp

/-- **A flat component lies strictly on one side of a cluster line of
approaching rulings**: under the hypotheses of
`flatComponent_avoids_cluster_line`, the signed functional of the line
`e + ℝ·w` is nowhere zero on the flat component `C`, hence (continuous,
`C` preconnected) has a constant strict sign on `C`. -/
theorem flatComponent_one_side_of_cluster_line {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} {q : ℕ → ℝ²}
    (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0)
    (hqe : Tendsto q atTop (𝓝 e)) {w : ℝ²} (hwnorm : ‖w‖ = 1)
    (hd : Tendsto (fun n => unitKernelDir f (q n)) atTop (𝓝 w))
    {p : ℝ²} :
    (∀ z ∈ flatComponent f p, 0 < signedLineFunc e w z) ∨
      (∀ z ∈ flatComponent f p, signedLineFunc e w z < 0) := by
  let C : Set ℝ² := flatComponent f p
  -- the signed functional never vanishes on C
  have hne : ∀ z ∈ C, signedLineFunc e w z ≠ 0 := by
    intro z hz
    intro hφ
    -- signedLineFunc e w z = 0 says z − e ∥ w (w ≠ 0)
    have hwne : w ≠ 0 := by
      have hnorm_ne : ‖w‖ ≠ 0 := by linarith
      exact norm_ne_zero_iff.mp hnorm_ne
    have hpar : ∃ c : ℝ, z - e = c • w := by
      -- signedLineFunc q w z = det2 (z − q) w, and the functional vanishes
      have hφ' : det2 (z - e) w = 0 := (signedLineFunc_eq_det2 e w z).symm.trans hφ
      exact exists_smul_of_det2_eq_zero (u := z - e) (v := w) hwne hφ'
    rcases hpar with ⟨c, hc⟩
    have hzline : ∃ s : ℝ, z = e + s • w := by
      refine ⟨c, ?_⟩
      calc
        z = (z - e) + e := by abel
        _ = e + c • w := by
          rw [hc]
          abel
    exact flatComponent_avoids_cluster_line hf ha hqS hqU hqe hwnorm hd (p := p) hz hzline
  exact sign_constant_of_preconnected_nowhere_zero (S := C)
    (isPreconnected_flatComponent f p)
    (ContinuousOn.mono (continuous_signedLineFunc e w).continuousOn (fun _ h => h))
    hne

end Submission.PaperBand

namespace Submission.PaperBand

/-! ## 4. Existence of approaching ruling families at degenerate flat points -/

/-- At a degenerate flat point (`e ∈ FlatSet`, not flat-interior) there is a
`U`-sequence approaching it: `U`-points are dense near every such point
(`U_dense_near_degenerate_frontier`), and we choose one inside the ball of
radius `δₙ = min(δ₀, (n+1)⁻¹)` where `ball e δ₀ ⊆ stripInterior`. -/
theorem exists_U_sequence_to_degenerate {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    {e : ℝ²} (heS : e ∈ stripInterior) (heF : e ∈ FlatSet f)
    (hni : ¬ IsFlatInterior f e) :
    ∃ q : ℕ → ℝ², (∀ n, q n ∈ stripInterior) ∧ (∀ n, dN f (q n) ≠ 0) ∧
      Tendsto q atTop (𝓝 e) := by
  -- a small ball around e lies in the strip interior
  rcases (Metric.mem_nhds_iff.mp (stripInterior_isOpen.mem_nhds heS)) with ⟨δ₀, hδ₀, hball₀⟩
  let δ : ℕ → ℝ := fun n => min δ₀ ((n + 1 : ℝ)⁻¹)
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    have h1 : 0 < (n + 1 : ℝ)⁻¹ := inv_pos.mpr (by positivity)
    exact lt_min hδ₀ h1
  let q : ℕ → ℝ² := fun n =>
    Classical.choose (U_dense_near_degenerate_frontier (a := a) (f := f) heS heF hni (δ n) (hδpos n))
  have hqU : ∀ n, dN f (q n) ≠ 0 := by
    intro n
    exact (Classical.choose_spec (U_dense_near_degenerate_frontier (a := a) (f := f) heS heF hni (δ n) (hδpos n))).2
  have hqball : ∀ n, q n ∈ Metric.ball e (δ n) := by
    intro n
    exact (Classical.choose_spec (U_dense_near_degenerate_frontier (a := a) (f := f) heS heF hni (δ n) (hδpos n))).1
  have hqS : ∀ n, q n ∈ stripInterior := by
    intro n
    have hle : δ n ≤ δ₀ := min_le_left δ₀ ((n + 1 : ℝ)⁻¹)
    have hmono : Metric.ball e (δ n) ⊆ Metric.ball e δ₀ := by
      intro x hx
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx hle
    exact hball₀ (hmono (hqball n))
  have hqe : Tendsto q atTop (𝓝 e) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let B : ℝ := min ε δ₀
    have hBpos : 0 < B := lt_min hε hδ₀
    -- Archimedean: pick N with B⁻¹ < N
    rcases exists_nat_gt (B⁻¹) with ⟨N, hN⟩
    refine eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    have hnN' : (N : ℝ) < (n + 1 : ℝ) := by
      have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hlt : B⁻¹ < (n + 1 : ℝ) := lt_trans hN hnN'
    have hBne : B ≠ 0 := ne_of_gt hBpos
    have hBinv_mul : B⁻¹ * B = 1 := inv_mul_cancel₀ hBne
    have hposn : 0 < (n + 1 : ℝ) := by positivity
    have h1 : 1 < B * (n + 1 : ℝ) := by
      have h := mul_lt_mul_of_pos_right hlt hBpos
      rw [hBinv_mul] at h
      simpa [mul_comm] using h
    have hstep : (n + 1 : ℝ)⁻¹ < B := by
      simpa using (div_lt_iff₀ hposn).2 h1
    have hle1 : δ n ≤ (n + 1 : ℝ)⁻¹ := min_le_right δ₀ ((n + 1 : ℝ)⁻¹)
    have hle2 : B ≤ ε := min_le_left ε δ₀
    have hdn : δ n < ε := lt_of_lt_of_le (lt_of_le_of_lt hle1 hstep) hle2
    have hqdist : ‖q n - e‖ < ε := by
      have hb : q n ∈ Metric.ball e (δ n) := hqball n
      have hlt' : ‖q n - e‖ < δ n := by
        rw [Metric.mem_ball, dist_eq_norm] at hb
        exact hb
      exact lt_trans hlt' hdn
    simpa [dist_eq_norm] using hqdist
  exact ⟨q, hqS, hqU, hqe⟩

/-! ## 5. Cluster line through a degenerate flat point -/

/-- **At a degenerate flat point `e` there is a unit cluster direction `w`
of approaching rulings, with the flat component strictly on one side of the
line `e + ℝ·w`**: choose an approaching `U`-sequence (`exists_U_sequence_
to_degenerate`), extract a convergent subsequence of its unit ruling
directions (`unitDir_subseq_convergent`), and apply
`flatComponent_one_side_of_cluster_line`.  The strict sign means in
particular that `C` avoids the line entirely (`signedLineFunc e w z ≠ 0` is
recorded for every `z ∈ C`). -/
theorem degenerate_flat_point_cluster_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior) (heF : e ∈ FlatSet f)
    (hni : ¬ IsFlatInterior f e) {p : ℝ²} :
    ∃ w : ℝ², ‖w‖ = 1 ∧
      (∀ z ∈ flatComponent f p, signedLineFunc e w z ≠ 0) ∧
      ((∀ z ∈ flatComponent f p, 0 < signedLineFunc e w z) ∨
        (∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)) := by
  rcases exists_U_sequence_to_degenerate hf heS heF hni with ⟨q, hqS, hqU, hqe⟩
  -- the unit ruling directions have a convergent subsequence
  rcases unitDir_subseq_convergent (u := fun n => unitKernelDir f (q n))
    (fun n => norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hqS n) (hqU n))) with
    ⟨w, hwnorm, φ, hφmono, hd⟩
  -- along the subsequence, the base points still approach e
  have hqeφ : Tendsto (fun m => q (φ m)) atTop (𝓝 e) := hqe.comp hφmono.tendsto_atTop
  have hside := flatComponent_one_side_of_cluster_line hf ha (q := fun m => q (φ m))
    (hqS := fun m => hqS (φ m)) (hqU := fun m => hqU (φ m)) (hqe := hqeφ) (hwnorm := hwnorm)
    (hd := hd) (p := p)
  -- the functional is nowhere zero on C (each side forces it)
  have hne : ∀ z ∈ flatComponent f p, signedLineFunc e w z ≠ 0 := by
    intro z hz
    rcases hside with hpos | hneg
    · have : 0 < signedLineFunc e w z := hpos z hz
      linarith
    · have : signedLineFunc e w z < 0 := hneg z hz
      linarith
  exact ⟨w, hwnorm, hne, hside⟩


/-! ## 6. Cluster lines of two approaching families cross only outside the strip -/

/-- **Cluster lines cross only outside the strip**: let `q₁ₙ → e₁`, `q₂ₙ → e₂`
be two `U`-sequences in the strip whose unit ruling directions converge to
unit vectors `w₁, w₂` with `det2 w₁ w₂ ≠ 0` (non-parallel).  Then the
intersection point of the two LIMIT lines `e₁ + ℝ·w₁` and `e₂ + ℝ·w₂`
(Cramer: `c = e₁ + (det2 (e₂−e₁) w₂ / det2 w₁ w₂) • w₁`) does NOT lie in
the strip interior.  Proof: if `c ∈ stripInterior`, the actual ruling lines
`ℓᵢₙ` intersect at `Pₙ → c` (`det2_intersect_on_second` + convergence of
the data), so `Pₙ ∈ stripInterior` eventually; each `Pₙ` lies on both
ruling lines through the `U`-points `qᵢₙ`, so its own kernel direction is
parallel to both (`kernel_along_unit_dir_line`,
`unit_dir_parallel_along_line`), forcing `det2 u₁ₙ u₂ₙ = 0` eventually —
contradicting convergence to `det2 w₁ w₂ ≠ 0`. -/
theorem cluster_lines_cross_not_in_strip {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e₁ e₂ : ℝ²} (_he₁S : e₁ ∈ stripInterior) (_he₂S : e₂ ∈ stripInterior)
    {q₁ q₂ : ℕ → ℝ²}
    (hq₁S : ∀ n, q₁ n ∈ stripInterior) (hq₁U : ∀ n, dN f (q₁ n) ≠ 0)
    (hq₁e : Tendsto q₁ atTop (𝓝 e₁))
    (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 e₂))
    {w₁ w₂ : ℝ²} (_hw₁₁ : ‖w₁‖ = 1) (_hw₂₁ : ‖w₂‖ = 1)
    (hd₁ : Tendsto (fun n => unitKernelDir f (q₁ n)) atTop (𝓝 w₁))
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w₂))
    (hdet : det2 w₁ w₂ ≠ 0) :
    e₁ + (det2 (e₂ - e₁) w₂ / det2 w₁ w₂) • w₁ ∉ stripInterior := by
  by_contra hcS
  let N₀ : ℝ := det2 (e₂ - e₁) w₂
  let D₀ : ℝ := det2 w₁ w₂
  let t₀ : ℝ := N₀ / D₀
  let num : ℕ → ℝ := fun n => det2 (q₂ n - q₁ n) (unitKernelDir f (q₂ n))
  let den : ℕ → ℝ := fun n => det2 (unitKernelDir f (q₁ n)) (unitKernelDir f (q₂ n))
  let t : ℕ → ℝ := fun n => num n / den n
  let P : ℕ → ℝ² := fun y => q₁ y + t y • unitKernelDir f (q₁ y)
  -- the denominator converges to the nonzero limit det2 w₁ w₂
  have hden_tend : Tendsto den atTop (𝓝 D₀) := by
    simpa [den, D₀] using tendsto_det2_pair hd₁ hd₂
  have hD₀ne : D₀ ≠ 0 := by simpa [D₀] using hdet
  -- the numerator converges to N₀ = det2 (e₂−e₁) w₂
  have hnum_tend : Tendsto num atTop (𝓝 N₀) := by
    have hq₂q₁ : Tendsto (fun n => q₂ n - q₁ n) atTop (𝓝 (e₂ - e₁)) := hq₂e.sub hq₁e
    have ht := tendsto_det2_pair hq₂q₁ hd₂
    simpa [num, N₀] using ht
  -- tₙ = N₀/D₀ + (numₙ − t₀·denₙ)/denₙ → t₀
  have hden_ev_ne : ∀ᶠ n in atTop, den n ≠ 0 := by
    have hnh : {y : ℝ | y ≠ 0} ∈ 𝓝 D₀ := isOpen_ne.mem_nhds hD₀ne
    exact hden_tend hnh
  have hnum0 : Tendsto (fun n => num n - t₀ * den n) atTop (𝓝 0) := by
    have htd : Tendsto (fun n => t₀ * den n) atTop (𝓝 (t₀ * D₀)) :=
      (tendsto_const_nhds.mul hden_tend)
    have hsub := hnum_tend.sub htd
    have hz : N₀ - t₀ * D₀ = 0 := by
      have h₁ : t₀ * D₀ = N₀ := by
        dsimp [t₀]
        field_simp [hD₀ne]
      linarith
    simpa [hz] using hsub
  have hd0 : Tendsto (fun n => (num n - t₀ * den n) / den n) atTop (𝓝 0) :=
    tendsto_div_zero_of_tendsto_zero_ne hnum0 hden_tend hD₀ne
  have heq_t : (fun n : ℕ => t n) =ᶠ[atTop] fun n : ℕ => t₀ + (num n - t₀ * den n) / den n := by
    filter_upwards [hden_ev_ne] with n hdenn
    have hnum_eq : num n / den n = t₀ + (num n - t₀ * den n) / den n := by
      field_simp [hdenn]
      ring
    simpa [t] using hnum_eq
  have ht₀_t : Tendsto t atTop (𝓝 t₀) := by
    have hsum : Tendsto (fun n : ℕ => t₀ + (num n - t₀ * den n) / den n) atTop (𝓝 (t₀ + 0)) :=
      tendsto_const_nhds.add hd0
    simpa using hsum.congr' heq_t.symm
  -- Pₙ → e₁ + t₀•w₁ (which is in the strip interior by hypothesis)
  have hPc : Tendsto P atTop (𝓝 (e₁ + t₀ • w₁)) := by
    have htu : Tendsto (fun n => t n • unitKernelDir f (q₁ n)) atTop (𝓝 (t₀ • w₁)) :=
      ht₀_t.smul hd₁
    exact hq₁e.add htu
  -- Pₙ lies in the strip interior eventually
  have hPstrip : ∀ᶠ n in atTop, P n ∈ stripInterior := by
    have hcS' : e₁ + t₀ • w₁ ∈ stripInterior := by
      -- hcS has the explicit Cramer formula; identify with t₀
      dsimp [t₀, N₀, D₀]
      simpa using hcS
    rcases Metric.mem_nhds_iff.mp (stripInterior_isOpen.mem_nhds hcS') with ⟨δ, hδ, hball⟩
    have hPball : ∀ᶠ n in atTop, P n ∈ Metric.ball (e₁ + t₀ • w₁) δ := by
      have hd := (Metric.tendsto_nhds.mp hPc) δ hδ
      filter_upwards [hd] with n hn
      rw [Metric.mem_ball]
      simpa [dist_eq_norm] using hn
    filter_upwards [hPball] with n hn
    exact hball hn
  -- eventually det2 u₁ₙ u₂ₙ = 0 (both ruling lines pass through Pₙ)
  have hev_det : ∀ᶠ n in atTop, det2 (unitKernelDir f (q₁ n)) (unitKernelDir f (q₂ n)) = 0 := by
    filter_upwards [hPstrip, hden_ev_ne] with n hnP hdenn
    have hdP2 : det2 (P n - q₂ n) (unitKernelDir f (q₂ n)) = 0 := by
      have h := det2_intersect_on_second (a := q₁ n) (b := q₂ n)
        (u := unitKernelDir f (q₁ n)) (v := unitKernelDir f (q₂ n)) hdenn
      simpa [P, t, num, den] using h
    have hline₂ : ∃ s : ℝ, P n = q₂ n + s • unitKernelDir f (q₂ n) := by
      have hV2 : V2f f (q₂ n) ≠ 0 := V2f_ne_zero_at_U hf ha (hq₂S n) (hq₂U n)
      have hv₂ : unitKernelDir f (q₂ n) ≠ 0 := unitKernelDir_ne_zero hV2
      rcases exists_smul_of_det2_eq_zero (u := P n - q₂ n) (v := unitKernelDir f (q₂ n)) hv₂ hdP2 with ⟨s, hs⟩
      refine ⟨s, ?_⟩
      calc
        P n = q₂ n + (P n - q₂ n) := by abel
        _ = q₂ n + s • unitKernelDir f (q₂ n) := by rw [hs]
    have hline₁ : ∃ s : ℝ, P n = q₁ n + s • unitKernelDir f (q₁ n) := by
      exact ⟨t n, by simp [P]⟩
    have hpar₁ : ∃ c : ℝ, unitKernelDir f (P n) = c • unitKernelDir f (q₁ n) :=
      unit_dir_parallel_along_line hf ha (x := q₁ n) (hx := hq₁S n) (hU := hq₁U n)
        (z := P n) hnP hline₁
    have hpar₂ : ∃ c : ℝ, unitKernelDir f (P n) = c • unitKernelDir f (q₂ n) :=
      unit_dir_parallel_along_line hf ha (x := q₂ n) (hx := hq₂S n) (hU := hq₂U n)
        (z := P n) hnP hline₂
    rcases hpar₁ with ⟨c₁, hc₁⟩
    rcases hpar₂ with ⟨c₂, hc₂⟩
    have hdet1 : det2 (unitKernelDir f (P n)) (unitKernelDir f (q₁ n)) = 0 := by
      rw [hc₁, det2_smul_left, det2_self]
      ring
    have hdet2 : det2 (unitKernelDir f (P n)) (unitKernelDir f (q₂ n)) = 0 := by
      rw [hc₂, det2_smul_left, det2_self]
      ring
    have hPnU : dN f (P n) ≠ 0 := by
      exact (kernel_along_unit_dir_line hf ha (x := q₁ n) (hx := hq₁S n) (hU := hq₁U n)
        (z := P n) hnP hline₁).1
    have hV : V2f f (P n) ≠ 0 := V2f_ne_zero_at_U hf ha hnP hPnU
    have hPn_ne : unitKernelDir f (P n) ≠ 0 := unitKernelDir_ne_zero hV
    exact det2_eq_zero_of_det2_eq_zero_common hPn_ne hdet1 hdet2
  -- contradiction: eventually-zero sequence converging to a nonzero limit
  exact eventually_zero_not_tendsto_ne hden_tend hD₀ne (by simpa [den] using hev_det)


/-! ## 7. Ruling lines through U-points are pairwise disjoint (or equal) in S -/

/-- **Two ruling lines that share a strip-interior point coincide**: if the
ruling lines of two `U`-points `q₁,q₂` both pass through a common
`z ∈ stripInterior`, then their directions are parallel (so the lines are
the same line).  Proof: `z` lies on the ruling line of the `U`-point `q₁`,
so `z` is a `U`-point and `unitKernelDir f q₁` is a kernel direction at `z`
(`kernel_along_unit_dir_line`); likewise `unitKernelDir f q₂` is a kernel
direction at `z`; the kernel at a `U`-point is a single line
(`kernel_direction_parallel`).  In particular the ruling lines of `U`
never cross inside the strip. -/
theorem u_ruling_lines_share_point_parallel {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    {q₁ q₂ : ℝ²} (hq₁S : q₁ ∈ stripInterior) (hq₁U : dN f q₁ ≠ 0)
    (hq₂S : q₂ ∈ stripInterior) (hq₂U : dN f q₂ ≠ 0)
    {z : ℝ²} (hz : z ∈ stripInterior)
    (h₁ : ∃ s₁ : ℝ, z = q₁ + s₁ • unitKernelDir f q₁)
    (h₂ : ∃ s₂ : ℝ, z = q₂ + s₂ • unitKernelDir f q₂) :
    ∃ c : ℝ, unitKernelDir f q₂ = c • unitKernelDir f q₁ := by
  have hz₁ := kernel_along_unit_dir_line hf ha (x := q₁) (z := z) hq₁S hq₁U hz h₁
  have hzU : dN f z ≠ 0 := hz₁.1
  have hu₁z : dN f z (unitKernelDir f q₁) = 0 := hz₁.2
  have hz₂ := kernel_along_unit_dir_line hf ha (x := q₂) (z := z) hq₂S hq₂U hz h₂
  have hu₂z : dN f z (unitKernelDir f q₂) = 0 := hz₂.2
  have hu₁ne : unitKernelDir f q₁ ≠ 0 :=
    unitKernelDir_ne_zero (V2f_ne_zero_at_U hf ha hq₁S hq₁U)
  exact kernel_direction_parallel hf hz hzU (u := unitKernelDir f q₁)
    (v := unitKernelDir f q₂) hu₁z hu₂z hu₁ne

/-! ## 8. Cluster lines of two degenerate points mutually avoid each other -/

/-- **Cluster lines mutually avoid**: if `e₁,e₂` are two points of the strip
interior with approaching `U`-sequences whose unit ruling directions
converge to unit `w₁,w₂` (the cluster directions), and `e₂` does NOT lie on
the cluster line `L(e₁) = e₁ + ℝ·w₁`, then `e₁` does NOT lie on
`L(e₂) = e₂ + ℝ·w₂`.  Proof: if `e₁ ∈ L(e₂)` then — when the directions are
parallel the two lines through `e₁` coincide, forcing `e₂ ∈ L(e₁)`; when
they are non-parallel the two lines cross at `e₁ ∈ stripInterior`,
contradicting `cluster_lines_cross_not_in_strip`.  (For two degenerate
frontier points of a flat component this excludes the asymmetric "one point
on the other's supporting line but not conversely" situation.) -/
theorem cluster_lines_mutually_avoid {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e₁ e₂ : ℝ²} (he₁S : e₁ ∈ stripInterior) (he₂S : e₂ ∈ stripInterior)
    {q₁ q₂ : ℕ → ℝ²}
    (hq₁S : ∀ n, q₁ n ∈ stripInterior) (hq₁U : ∀ n, dN f (q₁ n) ≠ 0)
    (hq₁e : Tendsto q₁ atTop (𝓝 e₁))
    (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 e₂))
    {w₁ w₂ : ℝ²} (hw₁₁ : ‖w₁‖ = 1) (hw₂₁ : ‖w₂‖ = 1)
    (hd₁ : Tendsto (fun n => unitKernelDir f (q₁ n)) atTop (𝓝 w₁))
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w₂))
    (hoff : ¬ ∃ s : ℝ, e₂ = e₁ + s • w₁) :
    ¬ ∃ s : ℝ, e₁ = e₂ + s • w₂ := by
  intro hon
  by_cases hdet : det2 w₁ w₂ = 0
  · -- parallel directions: e₁ ∈ L(e₂) forces L(e₂) = L(e₁) ∋ e₂
    have hw₁ne : w₁ ≠ 0 := by
      have hnorm_ne : ‖w₁‖ ≠ 0 := by linarith
      exact norm_ne_zero_iff.mp hnorm_ne
    have hdet₂₁ : det2 w₂ w₁ = 0 := by
      rw [det2_antisymm] at hdet
      linarith
    rcases exists_smul_of_det2_eq_zero (u := w₂) (v := w₁) hw₁ne hdet₂₁ with ⟨c, hc⟩
    rcases hon with ⟨s₂, he₁⟩
    have hb : ∃ s : ℝ, e₂ = e₁ + s • w₁ := by
      refine ⟨-(s₂ * c), ?_⟩
      calc
        e₂ = e₁ - s₂ • w₂ := by
          rw [he₁]
          abel
        _ = e₁ - s₂ • (c • w₁) := by rw [hc]
        _ = e₁ + (-(s₂ * c)) • w₁ := by
          rw [smul_smul]
          rw [sub_eq_add_neg]
          congr 1
          exact (neg_smul (s₂ * c) w₁).symm
    exact hoff hb
  · -- non-parallel: L(e₁) and L(e₂) cross at e₁ (since e₁ ∈ both), but the
    -- crossing lies outside the strip interior
    rcases hon with ⟨s₂, he₁⟩
    have hnum : det2 (e₂ - e₁) w₂ = 0 := by
      have hd : e₂ - e₁ = (-s₂) • w₂ := by
        calc
          e₂ - e₁ = e₂ - (e₂ + s₂ • w₂) := by rw [he₁]
          _ = -(s₂ • w₂) := by abel
          _ = (-s₂) • w₂ := (neg_smul s₂ w₂).symm
      rw [hd, det2_smul_left, det2_self]
      ring
    have hcross : e₁ + (det2 (e₂ - e₁) w₂ / det2 w₁ w₂) • w₁ = e₁ := by
      simp [hnum]
    have hout := cluster_lines_cross_not_in_strip hf ha he₁S he₂S
      hq₁S hq₁U hq₁e hq₂S hq₂U hq₂e hw₁₁ hw₂₁ hd₁ hd₂ hdet
    rw [hcross] at hout
    exact hout he₁S


/-! ## 9. Shallow-bulge exclusion along parallel supporting lines (the h>0 case) -/

/-- **Translating the signed functional to a parallel line**: the signed
functional of the line through `e'` in direction `w` equals the one of the
parallel line through `e`, shifted by the constant value at `e'`:
`signedLineFunc e' w x = signedLineFunc e w x − signedLineFunc e w e'`. -/
lemma signedLineFunc_shift (e e' w x : ℝ²) :
    signedLineFunc e' w x = signedLineFunc e w x - signedLineFunc e w e' := by
  unfold signedLineFunc
  simp
  ring

/-- The signed functional is odd in the direction. -/
lemma signedLineFunc_neg (e w x : ℝ²) :
    signedLineFunc e (-w) x = -(signedLineFunc e w x) := by
  unfold signedLineFunc
  simp
  ring

/-- The signed functional of the line through its own base point vanishes. -/
lemma signedLineFunc_self (q w : ℝ²) : signedLineFunc q w q = 0 := by
  unfold signedLineFunc
  simp

/-- **Closure passes strict inequalities to non-strict ones**: if `e` lies
in the closure of a set on which the continuous function `ψ` is strictly
below `c`, then `ψ e ≤ c`. -/
lemma closure_lt_le {ψ : ℝ² → ℝ} (hψ : Continuous ψ) {S : Set ℝ²} {e : ℝ²} {c : ℝ}
    (he : e ∈ closure S) (hS : ∀ x ∈ S, ψ x < c) : ψ e ≤ c := by
  have hsub : S ⊆ {x : ℝ² | ψ x ≤ c} := by
    intro x hx
    exact le_of_lt (hS x hx)
  have hclosed : IsClosed {x : ℝ² | ψ x ≤ c} := isClosed_le hψ continuous_const
  have hcl : closure S ⊆ {x : ℝ² | ψ x ≤ c} := closure_minimal hsub hclosed
  exact hcl he

/-- **Shallow-bulge exclusion along parallel supporting lines**: let `C` be
a flat component, `e` a point of its closure, and `e'` a degenerate point
(`e'` has an approaching `U`-sequence with unit ruling directions
converging to `w'`) whose cluster line `L(e')` is PARALLEL to the line
`L(e) = e + ℝ·w` (i.e. `w = ±w'`), with `e'` strictly on the `φ < 0` side of `L(e)`
(`φ x := signedLineFunc e w x`, `signedLineFunc e w e' < 0`) — in the
frontier application this says `e'` is a "shallow bulge" on C's side of
`L(e)` at positive depth, since `e' ∈ ∂C` and `C ⊂ {φ < 0}` force exactly
`φ e' < 0`.  Then C lies strictly on the slab side of `L(e')`:
`signedLineFunc e w e' < signedLineFunc e w z` for every `z ∈ C`.
Proof: `C` is strictly on one side of `L(e')` (`flatComponent_one_side_of_
cluster_line`); translating the signed functional to the parallel line
through `e` (`signedLineFunc_shift`) and using `e ∈ closure C` to pass the
strict inequality to the limit (`closure_lt_le`) rules out the "beyond
`L(e')`" disjunct, leaving exactly the slab side.  In particular a
"shallow bulge" frontier point `e'` at depth `b` forces all of `C` to depth
`< b`, so any `C`-point deeper than `b` is impossible — the h>0 half of the
frontier-containment theorem (the depth-0 cusp/pinch regime is untouched
here). -/
theorem flatComponent_shallow_bulge_parallel {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a)
    {e e' : ℝ²} {q₂ : ℕ → ℝ²}
    (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 e'))
    {w w' : ℝ²} (hw'₁ : ‖w'‖ = 1)
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w'))
    (hpar : w = w' ∨ w = -w')
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hφe' : signedLineFunc e w e' < 0) :
    ∀ z ∈ flatComponent f p, signedLineFunc e w e' < signedLineFunc e w z := by
  let C : Set ℝ² := flatComponent f p
  have hR2 := flatComponent_one_side_of_cluster_line hf ha (q := q₂) hq₂S hq₂U hq₂e
    (hwnorm := hw'₁) (hd := hd₂) (p := p)
  rcases hpar with hww' | hwnegw'
  · -- case w = w' : the two signed functionals differ by the constant φ e'
    have hφ' : ∀ x : ℝ²,
        signedLineFunc e' w' x = signedLineFunc e w x - signedLineFunc e w e' := by
      intro x
      rw [← hww']
      exact signedLineFunc_shift e e' w x
    rcases hR2 with hpos | hneg
    · intro z hz
      have hp := hpos z hz
      have h := hφ' z
      rw [h] at hp
      linarith
    · exfalso
      -- C ⊂ {φ < φ e'}: closure at e gives 0 ≤ φ e', contradicting φ e' < 0
      have hCsub : ∀ x ∈ C, signedLineFunc e w x < signedLineFunc e w e' := by
        intro x hx
        have hn := hneg x hx
        have h := hφ' x
        rw [h] at hn
        linarith
      have hle : signedLineFunc e w e ≤ signedLineFunc e w e' :=
        closure_lt_le (continuous_signedLineFunc e w) heClosure hCsub
      have hφe : signedLineFunc e w e = 0 := signedLineFunc_self e w
      have hle0 : (0 : ℝ) ≤ signedLineFunc e w e' := by simpa [hφe] using hle
      exact (not_lt_of_ge hle0) hφe'
  · -- case w = −w' : w' = −w, so φ'(x) = φ(e') − φ(x)
    have hw'w : w' = -w := by
      have h := congrArg Neg.neg hwnegw'
      simpa using h.symm
    have hφ' : ∀ x : ℝ²,
        signedLineFunc e' w' x = signedLineFunc e w e' - signedLineFunc e w x := by
      intro x
      rw [hw'w]
      have hneg : signedLineFunc e' (-w) x = -(signedLineFunc e' w x) := signedLineFunc_neg e' w x
      rw [hneg]
      have hshift : signedLineFunc e' w x = signedLineFunc e w x - signedLineFunc e w e' :=
        signedLineFunc_shift e e' w x
      rw [hshift]
      ring
    rcases hR2 with hpos | hneg
    · exfalso
      -- C ⊂ {φ < φ e'} again: closure at e gives the contradiction
      have hCsub : ∀ x ∈ C, signedLineFunc e w x < signedLineFunc e w e' := by
        intro x hx
        have hp := hpos x hx
        have h := hφ' x
        rw [h] at hp
        linarith
      have hle : signedLineFunc e w e ≤ signedLineFunc e w e' :=
        closure_lt_le (continuous_signedLineFunc e w) heClosure hCsub
      have hφe : signedLineFunc e w e = 0 := signedLineFunc_self e w
      have hle0 : (0 : ℝ) ≤ signedLineFunc e w e' := by simpa [hφe] using hle
      exact (not_lt_of_ge hle0) hφe'
    · intro z hz
      have hn := hneg z hz
      have h := hφ' z
      rw [h] at hn
      linarith


/-- **Shallow bulges are impossible (parallel case)**: under the hypotheses
of `flatComponent_shallow_bulge_parallel`, a flat component `C` with
`e ∈ closure C` cannot have BOTH a shallow-bulge frontier point `e'` (off
`L(e)` on C's side, parallel cluster line) AND a point strictly deeper than
`e'` on C's side of `L(e)` — the shallow bulge would force all of `C` into
the slab between the parallel lines, contradicting the deeper point.  (This
is the h>0 half of the frontier-containment theorem: frontier points at
positive depth `b` force every `C`-point to depth `< b`.) -/
theorem no_shallow_bulge_parallel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e e' : ℝ²} {q₂ : ℕ → ℝ²}
    (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 e'))
    {w w' : ℝ²} (hw'₁ : ‖w'‖ = 1)
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w'))
    (hpar : w = w' ∨ w = -w')
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hφe' : signedLineFunc e w e' < 0)
    (hdeep : ∃ z ∈ flatComponent f p, signedLineFunc e w z < signedLineFunc e w e') : False := by
  rcases hdeep with ⟨z, hz, hd⟩
  have h := flatComponent_shallow_bulge_parallel hf ha hq₂S hq₂U hq₂e hw'₁ hd₂ hpar
    heClosure hφe' z hz
  linarith


/-! ## 10. Depth-0 regime: the exact-parallel limit step (first green piece) -/

/-- **Limit step of the depth-0 exact-parallel exclusion**: let `C` lie
strictly in `{φ < 0}` and be forced into the slabs `{φ(e'_n) < φ}` for a
sequence with `φ(e'_n) → 0` (the shallow-bulge slab conclusion, applied to
frontier points `e'_n → e ∈ L(e)` at depths `→ 0`).  Then `C` is empty: a
point `z ∈ C` has `φ z < 0`, while for large `n`, `φ(e'_n) > φ z`
(convergence to `0 > φ z`) contradicts the slab constraint. -/
lemma slab_depth_zero_forces_empty {φ : ℝ² → ℝ} {e' : ℕ → ℝ²}
    (hφe'0 : Tendsto (fun n => φ (e' n)) atTop (𝓝 (0 : ℝ)))
    {C : Set ℝ²} (hC : ∀ z ∈ C, φ z < 0)
    (hslab : ∀ n, ∀ z ∈ C, φ (e' n) < φ z) :
    C = ∅ := by
  by_contra hne
  rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨z, hz⟩
  have hφz : φ z < 0 := hC z hz
  let ε : ℝ := -φ z / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hev : ∀ᶠ n in atTop, |φ (e' n) - 0| < ε := (Metric.tendsto_nhds.mp hφe'0) ε hε
  rcases (eventually_atTop.mp hev) with ⟨N, hN⟩
  have habs : |φ (e' N) - 0| < ε := hN N (Nat.le_refl N)
  have hgt : φ z < φ (e' N) := by
    have hsub : |φ (e' N)| < ε := by simpa using habs
    have hbig : -ε < φ (e' N) := neg_lt_of_abs_lt hsub
    have hεdef : -ε = φ z / 2 := by dsimp [ε]; ring
    have h1 : φ z / 2 < φ (e' N) := by rwa [hεdef] at hbig
    have h2 : φ z < φ z / 2 := by linarith
    exact lt_trans h2 h1
  have hφ' : φ (e' N) < φ z := hslab N z hz
  linarith

/-- **Depth-0 exact-parallel frontier points are impossible**: let `C` be a
flat component, `e` a point of its closure with `C` strictly in
`{φ < 0}` (`φ x := signedLineFunc e w x`), and let `e'_n` be degenerate
points (`e'_n` has an approaching `U`-sequence with unit cluster direction
`w'_n = ±w`) with `φ(e'_n) < 0` and `φ(e'_n) → 0` (frontier points at
positive depths tending to 0, off `L(e)` on C's side, with cluster lines
EXACTLY parallel to `L(e)`).  Then `C` is forced empty: each
`flatComponent_shallow_bulge_parallel` gives the slab constraint
`φ(e'_n) < φ z` for all `z ∈ C`, and `slab_depth_zero_forces_empty`
contradicts nonemptiness.  This is the exact-parallel half of the depth-0
regime (the nearly-parallel half needs the diagonal extraction + geometry
lemmas of the next section). -/
theorem no_exact_parallel_depth_zero {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} {w : ℝ²}
    {e' : ℕ → ℝ²} {q₂ : ℕ → ℕ → ℝ²}
    (hq₂S : ∀ n m, q₂ n m ∈ stripInterior) (hq₂U : ∀ n m, dN f (q₂ n m) ≠ 0)
    (hq₂e : ∀ n, Tendsto (q₂ n) atTop (𝓝 (e' n)))
    {w' : ℕ → ℝ²} (hw' : ∀ n, ‖w' n‖ = 1)
    (hd₂ : ∀ n, Tendsto (fun m => unitKernelDir f (q₂ n m)) atTop (𝓝 (w' n)))
    (hpar : ∀ n, w = w' n ∨ w = -w' n)
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    (hφe' : ∀ n, signedLineFunc e w (e' n) < 0)
    (hφe'0 : Tendsto (fun n => signedLineFunc e w (e' n)) atTop (𝓝 0)) :
    False := by
  let φ : ℝ² → ℝ := fun x => signedLineFunc e w x
  have hslab : ∀ n, ∀ z ∈ flatComponent f p, φ (e' n) < φ z := by
    intro n z hz
    exact flatComponent_shallow_bulge_parallel hf ha (e := e) (e' := e' n) (q₂ := q₂ n)
      (hq₂S := fun m => hq₂S n m) (hq₂U := fun m => hq₂U n m) (hq₂e := hq₂e n)
      (hw'₁ := hw' n) (hd₂ := hd₂ n) (hpar := hpar n) (p := p) heClosure (hφe' n) z hz
  have hempty : (flatComponent f p) = ∅ := by
    have hφe'0' : Tendsto (fun n => φ (e' n)) atTop (𝓝 (0 : ℝ)) := by
      simpa [φ] using hφe'0
    exact slab_depth_zero_forces_empty hφe'0' (hC := fun z hz => hside z hz) (hslab := hslab)
  rcases hnonempty with ⟨z, hz⟩
  have hnot : z ∉ flatComponent f p := by
    rw [hempty]
    simp
  exact hnot hz



/-! ## 11. T1′: diagonal extraction of an approaching U-sequence (depth-0, nearly-parallel regime) -/

lemma tendsto_inv_nat_succ_zero : Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
  convert h using 1
  ext m
  simp [Nat.cast_add, add_left_comm, add_assoc]



/-- **Diagonal extraction of an approaching U-sequence from a sequence of
approaching families (T1′ of session_status44)**: let `eₖ → e` in the strip,
and for each `k` let `q k : ℕ → ℝ²` be a `U`-sequence approaching `eₖ`.
Then there are a strictly monotone index extraction `φ` and a diagonal
`ψ` such that the diagonal points `q (φ m) (ψ m)` form a `U`-sequence
approaching `e` whose unit ruling directions converge to a unit vector
`wstar` — and `wstar` is PARALLEL to the limit direction `w₀` of any given
reference approaching `U`-sequence `u₀ → e`
(`wstar = w₀ ∨ wstar = -w₀`, by `rulingCluster_dirs_parallel` at `e`).
Construction: extract per-k subsequential direction limits `W k`
(`unitDir_subseq_convergent`), extract a convergent subsequence `φ` of
`W`, then pick diagonal indices so the per-k subsequence points sit within
`1/(m+1)` of both `e_{φ m}` and `W (φ m)`. -/
theorem diagonal_U_sequence_from_families {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {eₖ : ℕ → ℝ²} (heₖe : Tendsto eₖ atTop (𝓝 e))
    {q : ℕ → ℕ → ℝ²} (hqS : ∀ k m, q k m ∈ stripInterior) (hqU : ∀ k m, dN f (q k m) ≠ 0)
    (hqke : ∀ k, Tendsto (q k) atTop (𝓝 (eₖ k)))
    {u₀ : ℕ → ℝ²} (hu₀S : ∀ n, u₀ n ∈ stripInterior) (hu₀U : ∀ n, dN f (u₀ n) ≠ 0)
    (hu₀e : Tendsto u₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀ : ‖w₀‖ = 1)
    (hd₀ : Tendsto (fun n => unitKernelDir f (u₀ n)) atTop (𝓝 w₀)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ wstar : ℝ², ‖wstar‖ = 1 ∧
      (wstar = w₀ ∨ wstar = -w₀) ∧
      ∃ ψ : ℕ → ℕ,
        Tendsto (fun m => q (φ m) (ψ m)) atTop (𝓝 e) ∧
        Tendsto (fun m => unitKernelDir f (q (φ m) (ψ m))) atTop (𝓝 wstar) := by
  -- per-k subsequential direction limits W k and the subseq point families v k
  have hW : ∀ k, ∃ w : ℝ², ‖w‖ = 1 ∧ ∃ γ : ℕ → ℕ, StrictMono γ ∧
      Tendsto (fun m => unitKernelDir f (q k (γ m))) atTop (𝓝 w) := fun k =>
    unitDir_subseq_convergent (u := fun m : ℕ => unitKernelDir f (q k m))
      (fun m => norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hqS k m) (hqU k m)))
  let W : ℕ → ℝ² := fun k => Classical.choose (hW k)
  let γ : ℕ → ℕ → ℕ := fun k => Classical.choose (Classical.choose_spec (hW k)).2
  let v : ℕ → ℕ → ℝ² := fun k m => q k (γ k m)
  have hW₁ : ∀ k, ‖W k‖ = 1 := fun k => (Classical.choose_spec (hW k)).1
  have hγmono : ∀ k, StrictMono (γ k) := fun k =>
    (Classical.choose_spec (Classical.choose_spec (hW k)).2).1
  have hdW : ∀ k, Tendsto (fun m => unitKernelDir f (v k m)) atTop (𝓝 (W k)) := fun k =>
    (Classical.choose_spec (Classical.choose_spec (hW k)).2).2
  -- v k m → eₖ k (subsequence of the approaching family)
  have hvk : ∀ k, Tendsto (v k) atTop (𝓝 (eₖ k)) := by
    intro k
    change Tendsto (fun m => q k (γ k m)) atTop (𝓝 (eₖ k))
    exact (hqke k).comp (hγmono k).tendsto_atTop
  -- level 2: a convergent subsequence of W
  rcases unitDir_subseq_convergent (u := W) hW₁ with ⟨wstar, hwstar, φ, hφmono, hφw⟩
  -- diagonal index choice: within rate 1/(m+1) of both eₖ and W along (v (φ m))
  have hdiag : ∀ m, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ‖v (φ m) n - eₖ (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) ∧
      ‖unitKernelDir f (v (φ m) n) - W (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) := by
    intro m
    have hrate : 0 < (((m + 1 : ℕ) : ℝ)⁻¹) := by positivity
    have h1 : ∀ᶠ n in atTop, dist (v (φ m) n) (eₖ (φ m)) < (((m + 1 : ℕ) : ℝ)⁻¹) :=
      (Metric.tendsto_nhds.mp (hvk (φ m))) (((m + 1 : ℕ) : ℝ)⁻¹) hrate
    have h2 : ∀ᶠ n in atTop,
        dist (unitKernelDir f (v (φ m) n)) (W (φ m)) < (((m + 1 : ℕ) : ℝ)⁻¹) :=
      (Metric.tendsto_nhds.mp (hdW (φ m))) (((m + 1 : ℕ) : ℝ)⁻¹) hrate
    rcases (eventually_atTop.mp (h1.and h2)) with ⟨n₀, hn₀⟩
    refine ⟨n₀, ?_⟩
    intro n hn
    have h := hn₀ n hn
    constructor
    · simpa [dist_eq_norm] using h.1
    · simpa [dist_eq_norm] using h.2
  let ψ : ℕ → ℕ := fun m => γ (φ m) (Classical.choose (hdiag m))
  let u : ℕ → ℝ² := fun m => q (φ m) (ψ m)
  -- the diagonal points satisfy the rate bounds
  have hu_rate : ∀ m,
      ‖u m - eₖ (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) ∧
      ‖unitKernelDir f (u m) - W (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) := by
    intro m
    have hs := Classical.choose_spec (hdiag m)
    have hle : (Classical.choose (hdiag m)) ≥ (Classical.choose (hdiag m)) := le_rfl
    have hb := hs (Classical.choose (hdiag m)) hle
    -- v (φ m) (choose) = q (φ m)(γ(φ m)(choose)) = u m
    simpa [u, v, ψ] using hb
  -- u m → e
  have huS : ∀ m, u m ∈ stripInterior := by
    intro m
    exact hqS (φ m) (ψ m)
  have huU : ∀ m, dN f (u m) ≠ 0 := by
    intro m
    exact hqU (φ m) (ψ m)
  have hue : Tendsto u atTop (𝓝 e) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    -- 1/(m+1) < ε/2 eventually and ‖eₖ(φ m) − e‖ < ε/2 eventually
    have hrate : ∀ᶠ m : ℕ in atTop, (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := by
      have hz := (Metric.tendsto_nhds.mp tendsto_inv_nat_succ_zero) (ε / 2) hε2
      exact hz.mono (by
        intro m hm
        have h' : |((m + 1 : ℕ) : ℝ)⁻¹| < ε / 2 := by simpa [Real.dist_eq] using hm
        have h'' : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ |((m + 1 : ℕ) : ℝ)⁻¹| := le_abs_self _
        exact lt_of_le_of_lt h'' h')
    have hev : ∀ᶠ m in atTop, ‖eₖ (φ m) - e‖ < ε / 2 := by
      have hd := (Metric.tendsto_nhds.mp (heₖe.comp hφmono.tendsto_atTop)) (ε / 2) hε2
      exact hd.mono (by
        intro m hm
        simpa [dist_eq_norm] using hm)
    rcases (eventually_atTop.mp hrate) with ⟨M₁, hM₁⟩
    rcases (eventually_atTop.mp hev) with ⟨M₂, hM₂⟩
    exact eventually_atTop.2 ⟨max M₁ M₂, by
      intro m hm
      have hm1 : (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := hM₁ m (le_trans (le_max_left _ _) hm)
      have hm2 : ‖eₖ (φ m) - e‖ < ε / 2 := hM₂ m (le_trans (le_max_right _ _) hm)
      have hbd := (hu_rate m).1
      have hnorm : ‖u m - e‖ < ε := by
        calc
          ‖u m - e‖ ≤ ‖u m - eₖ (φ m)‖ + ‖eₖ (φ m) - e‖ := by
            rw [← sub_add_sub_cancel (u m) (eₖ (φ m)) e]
            exact norm_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add (lt_trans hbd hm1) hm2
          _ = ε := by ring
      simpa [dist_eq_norm] using hnorm⟩
  -- directions of the diagonal points converge to wstar
  have hud : Tendsto (fun m => unitKernelDir f (u m)) atTop (𝓝 wstar) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    -- |dir − W(φ m)| < 1/(m+1) → < ε/2 eventually ; ‖W(φ m) − wstar‖ < ε/2 eventually
    have hrate : ∀ᶠ m : ℕ in atTop, (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := by
      have hz := (Metric.tendsto_nhds.mp tendsto_inv_nat_succ_zero) (ε / 2) hε2
      exact hz.mono (by
        intro m hm
        have h' : |((m + 1 : ℕ) : ℝ)⁻¹| < ε / 2 := by simpa [Real.dist_eq] using hm
        have h'' : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ |((m + 1 : ℕ) : ℝ)⁻¹| := le_abs_self _
        exact lt_of_le_of_lt h'' h')
    have hw' : ∀ᶠ m in atTop, ‖W (φ m) - wstar‖ < ε / 2 := by
      have hd := (Metric.tendsto_nhds.mp hφw) (ε / 2) hε2
      exact hd.mono (by
        intro m hm
        simpa [dist_eq_norm] using hm)
    rcases (eventually_atTop.mp hrate) with ⟨M₁, hM₁⟩
    rcases (eventually_atTop.mp hw') with ⟨M₂, hM₂⟩
    exact eventually_atTop.2 ⟨max M₁ M₂, by
      intro m hm
      have hm1 : (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := hM₁ m (le_trans (le_max_left _ _) hm)
      have hm2 : ‖W (φ m) - wstar‖ < ε / 2 := hM₂ m (le_trans (le_max_right _ _) hm)
      have hbd := (hu_rate m).2
      have hnorm : ‖unitKernelDir f (u m) - wstar‖ < ε := by
        calc
          ‖unitKernelDir f (u m) - wstar‖
              ≤ ‖unitKernelDir f (u m) - W (φ m)‖ + ‖W (φ m) - wstar‖ := by
                rw [← sub_add_sub_cancel (unitKernelDir f (u m)) (W (φ m)) wstar]
                exact norm_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add (lt_trans hbd hm1) hm2
          _ = ε := by ring
      simpa [dist_eq_norm] using hnorm⟩
  -- the parallelity of wstar with w₀: FrontierCluster at e
  have hpar : wstar = w₀ ∨ wstar = -w₀ := by
    exact rulingCluster_dirs_parallel hf ha heS (q₁ := u) (q₂ := u₀)
      huS huU hu₀S hu₀U hue hu₀e hud hd₀
  exact ⟨φ, hφmono, wstar, hwstar, hpar, ψ, hue, hud⟩


/-! ## 12. T2-core: the algebraic sign identity (crossing formula) -/

/-- **The crossing identity for the signed value of the boundary point**
(T2-core (B), algebra half): let `L(e) = e + ℝ·w` and `L' = e' + ℝ·w'`
cross at `c`, written `c = e + τ₀•w` (and `c ∈ L'`).  Then the signed
value of `e` w.r.t. `L'` is
`signedLineFunc e' w' e = -τ₀ * det2 w w'`.
So the side of `e` relative to `L'` is controlled entirely by the sign of
`τ₀ · det2 w w'` — the sign invariant that the R3 crossing-outside-S
condition fixes in the nearly-parallel regime (session_status44 Addendum 2). -/
lemma crossing_signedValue (e e' c w w' : ℝ²) (τ₀ : ℝ)
    (hc₁ : c = e + τ₀ • w) (hc₂ : ∃ t₀ : ℝ, c = e' + t₀ • w') :
    signedLineFunc e' w' e = -τ₀ * det2 w w' := by
  rcases hc₂ with ⟨t₀, hc₂⟩
  have he : e - e' = (-τ₀) • w + t₀ • w' := by
    have h₁ : e - c = (-τ₀) • w := by
      rw [hc₁]
      calc
        e - (e + τ₀ • w) = -(τ₀ • w) := by abel
        _ = (-τ₀) • w := (neg_smul τ₀ w).symm
    have h₂ : c - e' = t₀ • w' := by rw [hc₂]; abel
    calc
      e - e' = (e - c) + (c - e') := by abel
      _ = (-τ₀) • w + t₀ • w' := by rw [h₁, h₂]
  calc
    signedLineFunc e' w' e = det2 (e - e') w' := signedLineFunc_eq_det2 e' w' e
    _ = det2 ((-τ₀) • w + t₀ • w') w' := by rw [he]
    _ = det2 ((-τ₀) • w) w' + det2 (t₀ • w') w' := by rw [det2_add_left]
    _ = (-τ₀) * det2 w w' + t₀ * det2 w' w' := by rw [det2_smul_left, det2_smul_left]
    _ = -τ₀ * det2 w w' := by simp [det2_self]


/-- The strip interior is convex along segments: `e + t•(x−e) ∈ stripInterior`
for `e, x ∈ stripInterior` and `t ∈ [0,1]`. -/
lemma stripInterior_convex_segment {e x : ℝ²} (heS : e ∈ stripInterior) (hxS : x ∈ stripInterior) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, e + t • (x - e) ∈ stripInterior := by
  intro t ht
  have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
  have ht1 : t ≤ 1 := (Set.mem_Icc.mp ht).2
  rw [stripInterior, Set.mem_setOf_eq]
  have he0 : 0 < e 0 := (Set.mem_Ioo.mp (by simpa [stripInterior] using heS)).1
  have he1 : e 0 < 1 := (Set.mem_Ioo.mp (by simpa [stripInterior] using heS)).2
  have hx0 : 0 < x 0 := (Set.mem_Ioo.mp (by simpa [stripInterior] using hxS)).1
  have hx1 : x 0 < 1 := (Set.mem_Ioo.mp (by simpa [stripInterior] using hxS)).2
  have hc : (e + t • (x - e)) 0 = (1 - t) * e 0 + t * x 0 := by
    simp
    ring
  rw [hc]
  constructor
  · by_cases ht' : t < 1
    · have hm : 0 < (1 - t) * e 0 := mul_pos (by linarith) he0
      have hr : 0 ≤ t * x 0 := mul_nonneg ht0 (le_of_lt hx0)
      linarith
    · have ht_eq : t = 1 := le_antisymm ht1 (le_of_not_gt ht')
      have hm : 0 < (1 - t) * e 0 + t * x 0 := by
        rw [ht_eq]
        norm_num
        exact hx0
      exact hm
  · by_cases ht' : 0 < t
    · have hm : t * x 0 < t := by simpa using (mul_lt_mul_of_pos_left hx1 ht')
      have h01t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
      have hl : (1 - t) * e 0 ≤ 1 - t := by simpa using (mul_le_mul_of_nonneg_left (le_of_lt he1) h01t)
      linarith
    · have ht0' : t = 0 := by
        apply le_antisymm
        · exact le_of_not_gt ht'
        · exact ht0
      have hm : (1 - t) * e 0 + t * x 0 < 1 := by
        rw [ht0']
        norm_num
        exact he1
      exact hm

/-- The signed functional of a line is affine along a segment based at a
point of the strip: for `g(t) := signedLineFunc e' w' (e + t•(x−e))`,
`g(t) = ψ(e) + t·(ψ(x) − ψ(e))` with `ψ y := signedLineFunc e' w' y`
(so `g` is affine, `g 0 = ψ(e)`, `g 1 = ψ(x)`). -/
lemma signedLineFunc_affine_segment (e' w' e x : ℝ²) (t : ℝ) :
    signedLineFunc e' w' (e + t • (x - e)) =
      signedLineFunc e' w' e + t * (signedLineFunc e' w' x - signedLineFunc e' w' e) := by
  have hvec : (e + t • (x - e)) - e' = (e - e') + t • (x - e) := by abel
  have hdx : det2 (x - e) w' = signedLineFunc e' w' x - signedLineFunc e' w' e := by
    have hx : signedLineFunc e' w' x = det2 (x - e') w' := signedLineFunc_eq_det2 e' w' x
    have he0 : signedLineFunc e' w' e = det2 (e - e') w' := signedLineFunc_eq_det2 e' w' e
    have hsub : det2 (x - e') w' - det2 (e - e') w' = det2 (x - e) w' := by
      have hv : (x - e') - (e - e') = x - e := by abel
      calc
        det2 (x - e') w' - det2 (e - e') w' = det2 ((x - e') - (e - e')) w' := by
          exact (det2_sub_left (a := x - e') (b := e - e') (v := w')).symm
        _ = det2 (x - e) w' := by rw [hv]
    rw [hx, he0]
    exact hsub.symm
  calc
    signedLineFunc e' w' (e + t • (x - e)) = det2 ((e + t • (x - e)) - e') w' :=
      signedLineFunc_eq_det2 e' w' (e + t • (x - e))
    _ = det2 ((e - e') + t • (x - e)) w' := by rw [hvec]
    _ = det2 (e - e') w' + det2 (t • (x - e)) w' := by rw [det2_add_left]
    _ = det2 (e - e') w' + t * det2 (x - e) w' := by rw [det2_smul_left]
    _ = signedLineFunc e' w' e + t * (signedLineFunc e' w' x - signedLineFunc e' w' e) := by
      have h1 : det2 (e - e') w' = signedLineFunc e' w' e := (signedLineFunc_eq_det2 e' w' e).symm
      rw [h1, hdx]

/-- **A line with opposite signed values at the endpoints of a segment
crosses the segment** (IVT): if `ψ(e)ψ(x) < 0` then there is
`t ∈ [0,1]` with `ψ(e + t•(x−e)) = 0`. -/
lemma signedLineFunc_crosses_segment (e' w' e x : ℝ²)
    (hneg : signedLineFunc e' w' e * signedLineFunc e' w' x < 0) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, signedLineFunc e' w' (e + t • (x - e)) = 0 := by
  let g : ℝ → ℝ := fun t => signedLineFunc e' w' (e + t • (x - e))
  have hg0 : g 0 = signedLineFunc e' w' e := by simp [g]
  have hg1 : g 1 = signedLineFunc e' w' x := by simp [g]
  have hgcont : Continuous g := by
    have hlin : Continuous (fun t : ℝ => e + t • (x - e)) := by
      fun_prop
    exact Continuous.comp (continuous_signedLineFunc e' w') hlin
  have hgcontOn : ContinuousOn g (Set.Icc (0 : ℝ) 1) := hgcont.continuousOn
  have h1in : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have h0in : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have hprod : g 1 * g 0 < 0 := by simpa [hg0, hg1, mul_comm] using hneg
  by_cases h1n : g 1 < 0
  · have h0p : 0 < g 0 := by
      by_contra h0le0
      have h0le : g 0 ≤ 0 := le_of_not_gt h0le0
      have hg0nz : g 0 ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hprod
        linarith
      have h0lt : g 0 < 0 := lt_of_le_of_ne h0le hg0nz
      have hmul : 0 < g 1 * g 0 := mul_pos_of_neg_of_neg h1n h0lt
      linarith
    have hIVT : Set.Icc (g 1) (g 0) ⊆ g '' Set.Icc (0 : ℝ) 1 :=
      IsPreconnected.intermediate_value isPreconnected_Icc h1in h0in hgcontOn
    have h0mem : (0 : ℝ) ∈ Set.Icc (g 1) (g 0) := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    rcases hIVT h0mem with ⟨t, ht, hgt⟩
    exact ⟨t, ht, by simpa [g] using hgt⟩
  · have h1p : 0 < g 1 := by
      have hg1nz : g 1 ≠ 0 := by
        intro hz
        rw [hz, zero_mul] at hprod
        linarith
      exact lt_of_le_of_ne (le_of_not_gt h1n) hg1nz.symm
    have h0n : g 0 < 0 := by
      by_contra h0ge0
      have h0ge : 0 ≤ g 0 := le_of_not_gt h0ge0
      have hg0nz : g 0 ≠ 0 := by
        intro hz
        rw [hz, mul_zero] at hprod
        linarith
      have h0gt : 0 < g 0 := lt_of_le_of_ne h0ge hg0nz.symm
      have hmul : 0 < g 1 * g 0 := mul_pos h1p h0gt
      linarith
    have hIVT : Set.Icc (g 0) (g 1) ⊆ g '' Set.Icc (0 : ℝ) 1 :=
      IsPreconnected.intermediate_value isPreconnected_Icc h0in h1in hgcontOn
    have h0mem : (0 : ℝ) ∈ Set.Icc (g 0) (g 1) := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    rcases hIVT h0mem with ⟨t, ht, hgt⟩
    exact ⟨t, ht, by simpa [g] using hgt⟩

/-- **The boundary chord of the strip lies on one fixed side of any chord
that does not meet it** (T2-core geometry half): let `L(e) = {φ = 0}` and
`L' = {signedLineFunc e' w' = 0}` be two lines whose intersections with the
strip interior do not meet (`hno`).  Then `signedLineFunc e' w' e` and
`signedLineFunc e' w' x` have the same strict sign for every
`x ∈ L(e) ∩ S`.  (Opposite signs would make `L'` cross the segment
`[e,x] ⊆ S ∩ L(e)` — `signedLineFunc_crosses_segment` + convexity — a
crossing point of the two lines in `S`, contradicting `hno`.) -/
lemma boundary_chord_same_side {e e' w w' x : ℝ²}
    (heS : e ∈ stripInterior) (hxS : x ∈ stripInterior)
    (hφx : signedLineFunc e w x = 0)
    (hno : ¬ ∃ y : ℝ², y ∈ stripInterior ∧ signedLineFunc e' w' y = 0 ∧
      signedLineFunc e w y = 0) :
    0 < signedLineFunc e' w' e * signedLineFunc e' w' x := by
  by_contra hle
  have hneg : signedLineFunc e' w' e * signedLineFunc e' w' x < 0 := by
    have hle' : signedLineFunc e' w' e * signedLineFunc e' w' x ≤ 0 := le_of_not_gt hle
    have hne : signedLineFunc e' w' e * signedLineFunc e' w' x ≠ 0 := by
      apply mul_ne_zero
      · intro h0
        exact hno ⟨e, heS, h0, signedLineFunc_self e w⟩
      · intro h0
        exact hno ⟨x, hxS, h0, hφx⟩
    exact lt_of_le_of_ne hle' hne
  rcases signedLineFunc_crosses_segment e' w' e x hneg with ⟨t, ht, hψy⟩
  let y : ℝ² := e + t • (x - e)
  have hyS : y ∈ stripInterior := stripInterior_convex_segment heS hxS t ht
  have hφy : signedLineFunc e w y = 0 := by
    have haff := signedLineFunc_affine_segment e w e x t
    have hφe : signedLineFunc e w e = 0 := signedLineFunc_self e w
    have : signedLineFunc e w (e + t • (x - e)) =
        (1 - t) * signedLineFunc e w e + t * signedLineFunc e w x := by
      rw [signedLineFunc_affine_segment e w e x t, hφe]
      ring
    have hz : signedLineFunc e w (e + t • (x - e)) = 0 := by
      rw [this, hφe, hφx]
      ring
    simpa [y] using hz
  have hψy' : signedLineFunc e' w' y = 0 := by simpa [y] using hψy
  exact hno ⟨y, hyS, hψy', hφy⟩



/-! ## 13. T2-core (B) sign half GREEN: `crossing_side_sign` (positivity of the boundary value) -/

lemma signedLineFunc_const_along_dir (e w : ℝ²) (s : ℝ) :
    signedLineFunc e w (e + s • w) = 0 := by
  calc
    signedLineFunc e w (e + s • w) = det2 ((e + s • w) - e) w :=
      signedLineFunc_eq_det2 e w (e + s • w)
    _ = det2 (s • w) w := by rw [show (e + s • w) - e = s • w by abel]
    _ = s * det2 w w := by rw [det2_smul_left]
    _ = 0 := by simp [det2_self]

/-- φ(q + s•d) = φ(q) + s·det2(d, w) (affine in the displacement). -/
lemma signedLineFunc_add_smul (e w q d : ℝ²) (s : ℝ) :
    signedLineFunc e w (q + s • d) = signedLineFunc e w q + s * det2 d w := by
  calc
    signedLineFunc e w (q + s • d) = det2 ((q + s • d) - e) w :=
      signedLineFunc_eq_det2 e w (q + s • d)
    _ = det2 ((q - e) + s • d) w := by rw [show (q + s • d) - e = (q - e) + s • d by abel]
    _ = det2 (q - e) w + det2 (s • d) w := by rw [det2_add_left]
    _ = signedLineFunc e w q + det2 (s • d) w := by
      rw [show det2 (q - e) w = signedLineFunc e w q by
        exact (signedLineFunc_eq_det2 e w q).symm]
    _ = signedLineFunc e w q + s * det2 d w := by rw [det2_smul_left]


/-- **Sign of the crossing parameter (T2-core (B) sign half)**: let the
lines `L(e) = e + ℝ·w` and `L' = e' + ℝ·w'` cross at `c`, with
`c = e + τ₀•w = e' + t₀•w'`, and suppose
  * `e, e' ∈ stripInterior`, `c ∉ stripInterior` (the crossing is OUTSIDE
    the strip — this is R3 in the application),
  * `e'` strictly on the `φ<0` side of `L(e)`
    (`signedLineFunc e w e' < 0`),
  * `w'` has the same horizontal direction as `w` (`(w 0)·(w' 0) > 0`,
    the near-parallel regime; automatic once `w'` is close to `w` and
    `w 0 ≠ 0`),
  * `det2 w w' ≠ 0`.
Then `τ₀ · det2 w w' < 0`, so by `crossing_signedValue`
`signedLineFunc e' w' e = -τ₀·det2 w w' > 0` (boundary point on the
positive side of `L'`).

PAPER DERIVATION (complete, recorded for the proof): let D := det2 w w',
a := e 0, a' := e' 0, u := w 0, v := w' 0, g := c 0.  From
`0 = φ(c) = φ(e' + t₀w') = φ(e') − t₀·D` (φ(c)=0 since c = e+τ₀w and φ is
constant along L(e); affine step via `signedLineFunc_add_smul`) get
`t₀·D = φ(e') < 0`.  Coordinates: `g = a + τ₀u = a' + t₀v`.  `hww'` gives
u,v ≠ 0 with the same sign; `u ≠ 0` in particular.  Since `c ∉ S` and
a' ∈ (0,1): if `t₀·v < 0` then `g = a' + t₀v < a' < 1` forces `g ≤ 0`
(left exit), so `τ₀u = g − a ≤ −a < 0`, sign(τ₀) = −sign(u) = −sign(v);
and `t₀·D<0` with `t₀·v<0` gives D·v > 0 ((t₀D)(t₀v) = t₀²·Dv > 0),
sign(D) = sign(v), hence sign(τ₀) = −sign(D), τ₀·D < 0.  Symmetrically if
`t₀·v > 0`: `g > a' > 0` forces `g ≥ 1` (right exit), `τ₀u ≥ 1−a > 0`,
sign(τ₀) = sign(u) = sign(v), while `t₀D<0, t₀v>0` give D·v < 0,
sign(D) = −sign(v), so τ₀·D < 0.  (`t₀·v = 0` would give `g = a' ∈ (0,1)`,
i.e. c ∈ S, contradicting `hcS`.)  Four explicit sign cases then close.
HONEST STATE: this exact theorem is the single remaining unformalized item
of T2-core (B); its derivation is fully recorded above and every ingredient
(φ(c)=0, the affine step, crossing_signedValue, the coordinate identities,
sign arithmetic) is in this file or ClusterLine. -/

lemma crossing_side_sign {e e' c w w' : ℝ²} {t₀ τ₀ : ℝ}
    (heS : e ∈ stripInterior) (he'S : e' ∈ stripInterior)
    (hcS : c ∉ stripInterior)
    (hc₁ : c = e + τ₀ • w) (hc₂ : c = e' + t₀ • w')
    (hφ : signedLineFunc e w e' < 0)
    (hww' : (w 0) * (w' 0) > 0) (hD : det2 w w' ≠ 0) :
    τ₀ * det2 w w' < 0 := by
  let D : ℝ := det2 w w'
  let a : ℝ := e 0
  let a' : ℝ := e' 0
  let u : ℝ := w 0
  let v : ℝ := w' 0
  let g : ℝ := c 0
  have hcoord : ∀ (x : ℝ²) (s : ℝ) (d : ℝ²), (x + s • d) 0 = x 0 + s * d 0 := by
    intro x s d
    simp
  have ha0 : 0 < a := (Set.mem_Ioo.mp (by simpa [stripInterior, a] using heS)).1
  have ha1 : a < 1 := (Set.mem_Ioo.mp (by simpa [stripInterior, a] using heS)).2
  have ha'0 : 0 < a' := (Set.mem_Ioo.mp (by simpa [stripInterior, a'] using he'S)).1
  have ha'1 : a' < 1 := (Set.mem_Ioo.mp (by simpa [stripInterior, a'] using he'S)).2
  have hgS : ¬ (0 < g ∧ g < 1) := by
    intro hg
    apply hcS
    rw [stripInterior]
    exact (Set.mem_Ioo.mpr hg)
  have hu0 : u ≠ 0 := by
    intro h0
    have hw0 : w 0 = 0 := by simpa [u] using h0
    rw [hw0, zero_mul] at hww'
    linarith
  have hg₁ : g = a + τ₀ * u := by
    calc
      g = c 0 := rfl
      _ = (e + τ₀ • w) 0 := by rw [hc₁]
      _ = e 0 + τ₀ * w 0 := hcoord e τ₀ w
      _ = a + τ₀ * u := by simp [a, u]
  have hg₂ : g = a' + t₀ * v := by
    calc
      g = c 0 := rfl
      _ = (e' + t₀ • w') 0 := by rw [hc₂]
      _ = e' 0 + t₀ * w' 0 := hcoord e' t₀ w'
      _ = a' + t₀ * v := by simp [a', v]
  have hτu : τ₀ * u = g - a := by rw [hg₁]; ring
  -- t₀·D = φ(e') < 0
  have ht₀D : t₀ * D < 0 := by
    have hrel : signedLineFunc e w c = signedLineFunc e w e' - t₀ * D := by
      rw [hc₂]
      have haff := signedLineFunc_add_smul e w e' w' t₀
      have hw'w : det2 w' w = -D := by
        rw [det2_antisymm]
      rw [haff, hw'w]
      ring
    have hcφ : signedLineFunc e w c = 0 := by
      rw [hc₁]
      exact signedLineFunc_const_along_dir e w τ₀
    have hmain : signedLineFunc e w e' - t₀ * D = 0 := by
      rw [← hrel]
      exact hcφ
    have hφeq : signedLineFunc e w e' = t₀ * D := by linarith
    rwa [hφeq] at hφ
  have ht₀nz : t₀ ≠ 0 := by
    intro ht0
    have : t₀ * D = 0 := by rw [ht0, zero_mul]
    linarith
  have hv0 : v ≠ 0 := by
    intro h0
    have hw'0 : w' 0 = 0 := by simpa [v] using h0
    rw [hw'0, mul_zero] at hww'
    linarith
  -- case analysis on signs of u and D
  by_cases hu : 0 < u
  · have hv : 0 < v := by
      have hnv : ¬ v < 0 := by
        intro hvn
        have : u * v < 0 := mul_neg_of_pos_of_neg hu hvn
        linarith
      exact lt_of_le_of_ne (le_of_not_gt hnv) hv0.symm
    by_cases hDpos : 0 < D
    · -- u>0, D>0: then t₀<0 and t₀v<0, exit left, τ₀<0
      have ht₀ : t₀ < 0 := by
        have hnt₀ : ¬ 0 ≤ t₀ := by
          intro ht0
          have : 0 ≤ t₀ * D := mul_nonneg ht0 (le_of_lt hDpos)
          linarith
        exact lt_of_not_ge hnt₀
      have htv : t₀ * v < 0 := mul_neg_of_neg_of_pos ht₀ hv
      have hglt : g < a' := by rw [hg₂]; linarith
      have hg0 : g ≤ 0 := by
        by_contra hgpos0
        have hgpos : 0 < g := lt_of_not_ge hgpos0
        exact hgS ⟨hgpos, lt_trans hglt ha'1⟩
      have hτ : τ₀ < 0 := by
        have hprod : τ₀ * u < 0 := by
          rw [hτu]
          linarith
        have hnτ : ¬ 0 ≤ τ₀ := by
          intro hτ0
          have : 0 ≤ τ₀ * u := mul_nonneg hτ0 (le_of_lt hu)
          linarith
        exact lt_of_not_ge hnτ
      exact mul_neg_of_neg_of_pos hτ hDpos
    · -- u>0, D<0: t₀>0 and t₀v>0, exit right, τ₀>0
      have hDneg : D < 0 := lt_of_le_of_ne (le_of_not_gt hDpos) (by
        intro hDeq
        exact hD (by simpa [D] using hDeq))
      have ht₀ : 0 < t₀ := by
        by_contra ht₀le
        have ht₀0 : t₀ ≤ 0 := le_of_not_gt ht₀le
        have ht₀lt : t₀ < 0 := lt_of_le_of_ne ht₀0 ht₀nz
        have : 0 < t₀ * D := mul_pos_of_neg_of_neg ht₀lt hDneg
        linarith
      have htv : 0 < t₀ * v := mul_pos ht₀ hv
      have hggt : a' < g := by rw [hg₂]; linarith
      have hg1 : 1 ≤ g := by
        by_contra hg1'
        have hglt1 : g < 1 := lt_of_not_ge hg1'
        exact hgS ⟨lt_trans ha'0 hggt, hglt1⟩
      have hτ : 0 < τ₀ := by
        have hprod : 0 < τ₀ * u := by
          rw [hτu]
          linarith
        have hnτ : ¬ τ₀ ≤ 0 := by
          intro hτ0
          have : τ₀ * u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hτ0 (le_of_lt hu)
          linarith
        exact lt_of_not_ge hnτ
      exact mul_neg_of_pos_of_neg hτ hDneg
  · -- u<0: v<0 (same sign)
    have hun : u < 0 := lt_of_le_of_ne (le_of_not_gt hu) hu0
    have hv : v < 0 := by
      have hnv : ¬ 0 ≤ v := by
        intro hv0'
        have : u * v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hun) hv0'
        linarith
      exact lt_of_not_ge hnv
    by_cases hDpos : 0 < D
    · -- u<0, D>0: t₀<0, t₀v>0 (v<0), exit right, τ₀<0 (u<0: τ₀u<0 ⟹ τ₀>0? careful)
      have ht₀ : t₀ < 0 := by
        by_contra ht₀n
        have ht₀0 : 0 ≤ t₀ := le_of_not_gt ht₀n
        have ht₀gt : 0 < t₀ := lt_of_le_of_ne ht₀0 (Ne.symm ht₀nz)
        have : 0 < t₀ * D := mul_pos ht₀gt hDpos
        linarith
      have htv : 0 < t₀ * v := mul_pos_of_neg_of_neg ht₀ hv
      have hggt : a' < g := by rw [hg₂]; linarith
      have hg1 : 1 ≤ g := by
        by_contra hg1'
        have hglt1 : g < 1 := lt_of_not_ge hg1'
        exact hgS ⟨lt_trans ha'0 hggt, hglt1⟩
      have hτ : τ₀ < 0 := by
        have hprod : 0 < τ₀ * u := by
          rw [hτu]
          linarith
        have hnτ : ¬ 0 ≤ τ₀ := by
          intro hτ0
          have : τ₀ * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ0 (le_of_lt hun)
          linarith
        exact lt_of_not_ge hnτ
      exact mul_neg_of_neg_of_pos hτ hDpos
    · -- u<0, D<0: t₀>0, t₀v<0 (v<0), exit left, τ₀>0
      have hDneg : D < 0 := lt_of_le_of_ne (le_of_not_gt hDpos) (by
        intro hDeq
        exact hD (by simpa [D] using hDeq))
      have ht₀ : 0 < t₀ := by
        by_contra ht₀le
        have ht₀0 : t₀ ≤ 0 := le_of_not_gt ht₀le
        have ht₀lt : t₀ < 0 := lt_of_le_of_ne ht₀0 ht₀nz
        have : 0 < t₀ * D := mul_pos_of_neg_of_neg ht₀lt hDneg
        linarith
      have htv : t₀ * v < 0 := mul_neg_of_pos_of_neg ht₀ hv
      have hglt : g < a' := by rw [hg₂]; linarith
      have hg0 : g ≤ 0 := by
        by_contra hgpos0
        have hgpos : 0 < g := lt_of_not_ge hgpos0
        exact hgS ⟨hgpos, lt_trans hglt ha'1⟩
      have hτ : 0 < τ₀ := by
        have hprod : τ₀ * u < 0 := by
          rw [hτu]
          linarith
        have hnτ : ¬ τ₀ ≤ 0 := by
          intro hτ0
          have : 0 ≤ τ₀ * u := mul_nonneg_of_nonpos_of_nonpos hτ0 (le_of_lt hun)
          linarith
        exact lt_of_not_ge hnτ
      exact mul_neg_of_pos_of_neg hτ hDneg

/-- **Mirror crossing side sign**: the same crossing geometry as
`crossing_side_sign`, but with OPPOSITE horizontal orientation of the two
lines: `(w 0)·(w' 0) < 0` (the lines are near-parallel with opposite
`x0`-tilts).  Then the crossing exits the strip on the mirror-forced side
and `τ₀ · det2 w w' > 0`.  Derived by applying `crossing_side_sign` to the
direction `w̃ := -w'` (and parameter `t̃₀ := -t₀`): `det2 w (-w') =
-det2 w w'`, and `(w 0)·((-w') 0) = -(w 0)·(w' 0) > 0`. -/
lemma crossing_side_sign_mirror {e e' c w w' : ℝ²} {t₀ τ₀ : ℝ}
    (heS : e ∈ stripInterior) (he'S : e' ∈ stripInterior)
    (hcS : c ∉ stripInterior)
    (hc₁ : c = e + τ₀ • w) (hc₂ : c = e' + t₀ • w')
    (hφ : signedLineFunc e w e' < 0)
    (hww' : (w 0) * (w' 0) < 0) (hD : det2 w w' ≠ 0) :
    0 < τ₀ * det2 w w' := by
  -- flip the second line: w̃ := -w', t̃₀ := -t₀  keeps c = e' + t̃₀ • w̃
  have hc₂flip : c = e' + (-t₀) • (-w') := by
    calc
      c = e' + t₀ • w' := hc₂
      _ = e' + (-t₀) • (-w') := by
        rw [neg_smul, smul_neg, neg_neg]
  have hww'flip : (w 0) * ((-w') 0) > 0 := by
    have hcoord : (-w') 0 = -(w' 0) := by simp
    rw [hcoord]
    have hprod : (w 0) * (-(w' 0)) = -((w 0) * (w' 0)) := by ring
    rw [hprod]
    linarith
  have hDflip : det2 w (-w') ≠ 0 := by
    have hdet2 : det2 w (-w') = -det2 w w' := by
      simp [det2]
      ring
    intro hz
    rw [hdet2] at hz
    exact hD (by linarith)
  have hmain := crossing_side_sign heS he'S hcS hc₁ hc₂flip hφ hww'flip hDflip
  -- hmain : τ₀ * det2 w (-w') < 0 ; and det2 w (-w') = -(det2 w w')
  have hdet2 : det2 w (-w') = -det2 w w' := by
    simp [det2]
    ring
  have : τ₀ * (-(det2 w w')) < 0 := by simpa [hdet2] using hmain
  nlinarith

/-! ## 14. T2 assembly: the depth-0 contradiction -/

/-- **A vertical cluster direction at a degenerate point is impossible
alongside a non-parallel nearby family (w 0 = 0 warm-up)**: let `e` have an
approaching `U`-sequence with unit cluster direction `w` with `w 0 = 0`
(so `L(e) = e + ℝw` is the vertical line `x0 = e 0`), and let each `eₖ`
(any strip-interior point with an approaching `U`-sequence in a direction
`w'ₖ` with `det2 w w'ₖ ≠ 0`) be given.  Then R3
(`cluster_lines_cross_not_in_strip`) forces the crossing of `L(e)` and
`L(eₖ)` OUTSIDE the strip; but every point of the vertical line
`L(e) = {x0 = e 0}` lies IN the strip (as `e 0 ∈ (0,1)` and the strip is
`(0,1) × ℝ`), a contradiction.  Hence in the T2 regime the cluster
direction `w` cannot be vertical — so `(w 0) ≠ 0`, and the near-parallel
hypothesis `(w 0)·(w'ₖ 0) > 0` of `crossing_side_sign` holds for large `k`. -/
lemma vertical_cluster_dir_contradiction {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e eₖ : ℝ²} (heS : e ∈ stripInterior) (heₖS : eₖ ∈ stripInterior)
    {q₀ q₂ : ℕ → ℝ²}
    (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 eₖ))
    {w w' : ℝ²} (hw₁ : ‖w‖ = 1) (hw'₁ : ‖w'‖ = 1)
    (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w'))
    (hw0 : w 0 = 0) (hdet : det2 w w' ≠ 0) : False := by
  -- R3: the crossing of the two cluster lines is outside the strip
  have hout := cluster_lines_cross_not_in_strip hf ha heS heₖS
    hq₀S hq₀U hq₀e hq₂S hq₂U hq₂e hw₁ hw'₁ hd₀ hd₂ hdet
  -- but every point of the vertical line L(e) = {x0 = e 0} lies in the strip
  let c : ℝ² := e + (det2 (eₖ - e) w' / det2 w w') • w
  have hc0 : c 0 = e 0 := by
    dsimp [c]
    rw [hw0]
    simp
  have he0 : e 0 ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [stripInterior] using heS
  have hcS : c ∈ stripInterior := by
    rw [stripInterior, Set.mem_setOf_eq]
    -- c 0 = e 0 and the vertical coordinate is unrestricted
    have : c 0 ∈ Set.Ioo (0 : ℝ) 1 := by rwa [hc0]
    exact this
  -- R3 says exactly the opposite
  have hnot : c ∉ stripInterior := by
    dsimp [c]
    exact hout
  exact hnot hcS


/-- **Convergence of the family functionals at a fixed point (H-A)**: if
`eₖ → e` and `w'ₖ → w` (unit), then
`signedLineFunc (eₖ k) (w' k) z₀ → signedLineFunc e w z₀` for any fixed
`z₀` — the value of the family line functional at `z₀` converges to the
limit value. -/
lemma signedLineFunc_tendsto_base_dir {e : ℝ²} {w : ℝ²} {eₖ : ℕ → ℝ²} {w' : ℕ → ℝ²}
    (z₀ : ℝ²) (heₖe : Tendsto eₖ atTop (𝓝 e)) (hww : Tendsto w' atTop (𝓝 w)) :
    Tendsto (fun k => signedLineFunc (eₖ k) (w' k) z₀) atTop
      (𝓝 (signedLineFunc e w z₀)) := by
  have hpair : Tendsto (fun k => (eₖ k, w' k)) atTop (𝓝 (e, w)) := by
    simpa [nhds_prod_eq] using (Tendsto.prodMk heₖe hww)
  have hG : ContinuousAt (fun qw : ℝ² × ℝ² => signedLineFunc qw.1 qw.2 z₀) (e, w) := by
    unfold signedLineFunc
    fun_prop
  exact hG.tendsto.comp hpair


/-- **Same-side product (H-C)**: under the full per-k data with
`z₀ ∈ C = flatComponent f p`, `e ∈ closure C`, `φ(eₖ k) < 0` and
`det2 w (w' k) ≠ 0`, R2 at `eₖ k` puts `C` strictly on one side of `Lₖ`;
`e` (closure) and `z₀` (in C) both lie strictly on that side
(`e ∉ Lₖ` by mutual avoidance from `eₖ k ∉ L(e)`), so
`ψₖ(z₀)·ψₖ(e) > 0` where `ψₖ x := signedLineFunc (eₖ k) (w' k) x`. -/
lemma same_side_product {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    {eₖ : ℝ²} (heₖS : eₖ ∈ stripInterior)
    {q₂ : ℕ → ℝ²} (hq₂S : ∀ m, q₂ m ∈ stripInterior) (hq₂U : ∀ m, dN f (q₂ m) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 eₖ))
    {w' : ℝ²} (hw'₁ : ‖w'‖ = 1)
    (hd₂ : Tendsto (fun m => unitKernelDir f (q₂ m)) atTop (𝓝 w'))
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    {z₀ : ℝ²} (hz₀ : z₀ ∈ flatComponent f p)
    (hφeₖ : signedLineFunc e w eₖ < 0)
    (hdet : det2 w w' ≠ 0) :
    0 < signedLineFunc eₖ w' z₀ * signedLineFunc eₖ w' e := by
  -- eₖ ∉ L(e): from φ(eₖ) < 0
  have hoff : ¬ ∃ s : ℝ, eₖ = e + s • w := by
    intro hone
    rcases hone with ⟨s, hs⟩
    have hφx : signedLineFunc e w (e + s • w) = 0 := signedLineFunc_const_along_dir e w s
    have : signedLineFunc e w eₖ = 0 := by rwa [hs]
    linarith
  -- e ∉ L(eₖ): mutual avoidance
  have hoff' : ¬ ∃ s : ℝ, e = eₖ + s • w' :=
    cluster_lines_mutually_avoid hf ha (e₁ := e) (e₂ := eₖ) heS heₖS
      hq₀S hq₀U hq₀e hq₂S hq₂U hq₂e hw₁ hw'₁ hd₀ hd₂ hoff
  -- ψ(e) ≠ 0 (e not on Lₖ)
  have hψe0 : signedLineFunc eₖ w' e ≠ 0 := by
    intro h0
    have hw'nz : w' ≠ 0 := by
      have : ‖w'‖ ≠ 0 := by linarith
      exact norm_ne_zero_iff.mp this
    have hpar : ∃ c : ℝ, e - eₖ = c • w' :=
      exists_smul_of_det2_eq_zero (u := e - eₖ) (v := w') hw'nz
        (by simpa [signedLineFunc_eq_det2] using h0)
    rcases hpar with ⟨c, hc⟩
    exact hoff' ⟨c, by
      calc
        e = eₖ + (e - eₖ) := by abel
        _ = eₖ + c • w' := by rw [hc]⟩
  -- R2 at eₖ
  have hR2 := flatComponent_one_side_of_cluster_line hf ha (q := q₂) hq₂S hq₂U hq₂e
    (hwnorm := hw'₁) (hd := hd₂) (p := p)
  rcases hR2 with hpos | hneg
  · have hψz : 0 < signedLineFunc eₖ w' z₀ := hpos z₀ hz₀
    have hψe : 0 < signedLineFunc eₖ w' e := by
      -- e ∈ closure C, C ⊆ {ψ > 0} (positive side), so ψ(e) ≥ 0; and ≠ 0
      have hsub : (flatComponent f p) ⊆ {x : ℝ² | -(signedLineFunc eₖ w' x) < 0} := by
        intro x hx
        have hx' : 0 < signedLineFunc eₖ w' x := hpos x hx
        change -(signedLineFunc eₖ w' x) < 0
        linarith
      have hle : -(signedLineFunc eₖ w' e) ≤ 0 :=
        closure_lt_le (Continuous.neg (continuous_signedLineFunc eₖ w')) heClosure hsub
      have hge : 0 ≤ signedLineFunc eₖ w' e := by linarith
      exact lt_of_le_of_ne hge hψe0.symm
    exact mul_pos hψz hψe
  · have hψz : signedLineFunc eₖ w' z₀ < 0 := hneg z₀ hz₀
    have hle : signedLineFunc eₖ w' e ≤ 0 := by
      have hsub : (flatComponent f p) ⊆ {x : ℝ² | signedLineFunc eₖ w' x < 0} := by
        intro x hx
        exact hneg x hx
      exact closure_lt_le (continuous_signedLineFunc eₖ w') heClosure hsub
    have hψe : signedLineFunc eₖ w' e < 0 := lt_of_le_of_ne hle hψe0
    exact mul_pos_of_neg_of_neg hψz hψe



/-- **Boundary-value positivity for large k (H-B)**: under the full
sequence data with `w'ₖ → w` and `w 0 ≠ 0` (non-vertical cluster
direction), EVENTUALLY `signedLineFunc (eₖ k) (w' k) e > 0` — the boundary
point `e` lies strictly on the positive side of the family line `Lₖ`.
Proof for each large k: R3 puts the crossing `cₖ = L(e)∩Lₖ` outside the
strip; `crossing_signedValue` gives `ψₖ(e) = −τ₀ₖ·det2 w w'ₖ` and
`crossing_side_sign` gives `τ₀ₖ·det2 w w'ₖ < 0` (using the near-parallel
sign agreement `(w 0)·(w'ₖ 0) > 0`, which holds for large `k` since
`w'ₖ 0 → w 0 ≠ 0`). -/
lemma boundary_value_pos_eventually {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hww : Tendsto w' atTop (𝓝 w)) (hw0nz : w 0 ≠ 0) :
    ∀ᶠ k in atTop, 0 < signedLineFunc (eₖ k) (w' k) e := by
  -- eventually (w 0)·(w'ₖ 0) > 0
  have hcoord : Tendsto (fun k => (w' k) 0) atTop (𝓝 (w 0)) := by
    have hc : Continuous (fun v : ℝ² => v 0) := by fun_prop
    exact hc.continuousAt.tendsto.comp hww
  have hprod_ev : ∀ᶠ k in atTop, (w 0) * (w' k) 0 > 0 := by
    -- the product pₖ = (w 0)·((w'ₖ) 0) converges to (w 0)² > 0,
    -- so eventually pₖ > (w 0)²/2 > 0.
    have hmulc : Continuous (fun x : ℝ => (w 0) * x) := by fun_prop
    have hp_tend : Tendsto (fun k => (w 0) * (w' k) 0) atTop (𝓝 ((w 0) * (w 0))) :=
      hmulc.continuousAt.tendsto.comp hcoord
    have hc0 : (w 0) * (w 0) > 0 := by
      exact mul_self_pos.mpr hw0nz
    have hε : 0 < (w 0) * (w 0) / 2 := by positivity
    have hclose : ∀ᶠ k in atTop, |(w 0) * (w' k) 0 - (w 0) * (w 0)| < (w 0) * (w 0) / 2 := by
      exact (Metric.tendsto_nhds.mp hp_tend) ((w 0) * (w 0) / 2) hε
    filter_upwards [hclose] with k hk
    have hparts := abs_lt.mp hk
    -- pₖ − L > −L/2 with L = (w 0)² > 0  ⟹  pₖ > L/2 > 0
    have hgt : -( (w 0) * (w 0) / 2) < (w 0) * (w' k) 0 - (w 0) * (w 0) := hparts.1
    have hpos : 0 < (w 0) * (w' k) 0 := by
      have : (w 0) * (w 0) - (w 0) * (w 0) / 2 < (w 0) * (w' k) 0 := by linarith
      linarith
    exact hpos
  -- the positivity at a given k with (w0)·(w'k0)>0
  have hcore : ∀ k, (w 0) * (w' k) 0 > 0 →
      0 < signedLineFunc (eₖ k) (w' k) e := by
    intro k hww'k
    -- the crossing c = e + τ₀ₖ•w with τ₀ₖ := det2(eₖk−e)(w'k)/det2 w w'k
    let τ₀ₖ : ℝ := det2 (eₖ k - e) (w' k) / det2 w (w' k)
    let c : ℝ² := e + τ₀ₖ • w
    -- c ∉ S by R3
    have hout : c ∉ stripInterior := by
      have h := cluster_lines_cross_not_in_strip hf ha heS (heₖS k)
        hq₀S hq₀U hq₀e (hq₂S k) (hq₂U k) (hq₂e k) hw₁ (hw'₁ k) hd₀ (hd₂ k) (hdet k)
      simpa [c, τ₀ₖ] using h
    -- c ∈ Lₖ: det2 (c − eₖk)(w'k) = 0
    have hc2 : ∃ t₀ : ℝ, c = eₖ k + t₀ • (w' k) := by
      have hd : det2 (c - eₖ k) (w' k) = 0 := by
        have hii := det2_intersect_on_second (a := e) (b := eₖ k) (u := w) (v := w' k) (hdet k)
        simpa [c, τ₀ₖ] using hii
      have hw'nz : w' k ≠ 0 := by
        have : ‖w' k‖ ≠ 0 := by linarith [hw'₁ k]
        exact norm_ne_zero_iff.mp this
      rcases exists_smul_of_det2_eq_zero (u := c - eₖ k) (v := w' k) hw'nz hd with ⟨t₀, ht₀⟩
      refine ⟨t₀, ?_⟩
      calc
        c = eₖ k + (c - eₖ k) := by abel
        _ = eₖ k + t₀ • (w' k) := by rw [ht₀]
    -- the sign identity and its positivity
    have hsign := crossing_side_sign (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (t₀ := Classical.choose hc2) (τ₀ := τ₀ₖ) heS (heₖS k) hout
      (by rfl : c = e + τ₀ₖ • w) (Classical.choose_spec hc2) (hφeₖ k) hww'k (hdet k)
    have hid := crossing_signedValue (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (τ₀ := τ₀ₖ) (by rfl : c = e + τ₀ₖ • w) hc2
    -- signedLineFunc (eₖk)(w'k) e = −τ₀ₖ·det2 w w'k > 0
    have hψ : signedLineFunc (eₖ k) (w' k) e = -(τ₀ₖ * det2 w (w' k)) := by
      simpa [mul_comm] using hid
    have hpos : 0 < -(τ₀ₖ * det2 w (w' k)) := by linarith
    rwa [hψ]
  exact hprod_ev.mono (fun k hk => hcore k hk)


/-- **Mirror boundary-value negativity for large k (H-B′)**: the
`boundary_value_pos_eventually` twin for the OPPOSITE direction regime:
now the family directions converge to `-w` (unit, `w 0 ≠ 0`), so
eventually `(w 0)·(w'ₖ 0) < 0` (opposite horizontal orientation), and the
mirror crossing sign (`crossing_side_sign_mirror`) gives
`τ₀ₖ·det2 w (w'ₖ) > 0`, i.e. EVENTUALLY
`signedLineFunc (eₖ k) (w' k) e < 0` — the boundary point `e` lies
strictly on the NEGATIVE side of the family line `Lₖ`. -/
lemma boundary_value_neg_eventually {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hwwm : Tendsto w' atTop (𝓝 (-w))) (hw0nz : w 0 ≠ 0) :
    ∀ᶠ k in atTop, signedLineFunc (eₖ k) (w' k) e < 0 := by
  -- eventually (w 0)·(w'ₖ 0) < 0 (product → −(w 0)² < 0)
  have hcoord : Tendsto (fun k => (w' k) 0) atTop (𝓝 (-(w 0))) := by
    have hc : Continuous (fun v : ℝ² => v 0) := by fun_prop
    have h1 : Tendsto (fun k => (w' k) 0) atTop (𝓝 ((-w) 0)) := hc.continuousAt.tendsto.comp hwwm
    have hnegc : (-w) 0 = -(w 0) := by simp
    simpa [hnegc] using h1
  have hprod_ev : ∀ᶠ k in atTop, (w 0) * (w' k) 0 < 0 := by
    have hmulc : Continuous (fun x : ℝ => (w 0) * x) := by fun_prop
    have hp_tend : Tendsto (fun k => (w 0) * (w' k) 0) atTop (𝓝 ((w 0) * (-(w 0)))) :=
      hmulc.continuousAt.tendsto.comp hcoord
    have hc0 : (w 0) * (w 0) > 0 := by
      exact mul_self_pos.mpr hw0nz
    have hε : 0 < (w 0) * (w 0) / 2 := by positivity
    have hclose : ∀ᶠ k in atTop,
        |(w 0) * (w' k) 0 - (w 0) * (-(w 0))| < (w 0) * (w 0) / 2 := by
      exact (Metric.tendsto_nhds.mp hp_tend) ((w 0) * (w 0) / 2) hε
    filter_upwards [hclose] with k hk
    have hparts := abs_lt.mp hk
    -- pₖ − L < ε with L = −(w 0)², ε = (w 0)²/2  ⟹  pₖ < L + ε = −(w0)²/2 < 0
    have hlt : (w 0) * (w' k) 0 - (w 0) * (-(w 0)) < (w 0) * (w 0) / 2 := hparts.2
    have hneg : (w 0) * (w' k) 0 < 0 := by
      have hR : (w 0) * (-(w 0)) + (w 0) * (w 0) / 2 = -( (w 0) * (w 0) / 2) := by ring
      have hRneg : (w 0) * (-(w 0)) + (w 0) * (w 0) / 2 < 0 := by
        rw [hR]
        linarith
      linarith
    exact hneg
  -- the negativity at a given k with (w0)·(w'k0)<0
  have hcore : ∀ k, (w 0) * (w' k) 0 < 0 →
      signedLineFunc (eₖ k) (w' k) e < 0 := by
    intro k hww'k
    -- the crossing c = e + τ₀ₖ•w with τ₀ₖ := det2(eₖk−e)(w'k)/det2 w w'k
    let τ₀ₖ : ℝ := det2 (eₖ k - e) (w' k) / det2 w (w' k)
    let c : ℝ² := e + τ₀ₖ • w
    -- c ∉ S by R3
    have hout : c ∉ stripInterior := by
      have h := cluster_lines_cross_not_in_strip hf ha heS (heₖS k)
        hq₀S hq₀U hq₀e (hq₂S k) (hq₂U k) (hq₂e k) hw₁ (hw'₁ k) hd₀ (hd₂ k) (hdet k)
      simpa [c, τ₀ₖ] using h
    -- c ∈ Lₖ: det2 (c − eₖk)(w'k) = 0
    have hc2 : ∃ t₀ : ℝ, c = eₖ k + t₀ • (w' k) := by
      have hd : det2 (c - eₖ k) (w' k) = 0 := by
        have hii := det2_intersect_on_second (a := e) (b := eₖ k) (u := w) (v := w' k) (hdet k)
        simpa [c, τ₀ₖ] using hii
      have hw'nz : w' k ≠ 0 := by
        have : ‖w' k‖ ≠ 0 := by linarith [hw'₁ k]
        exact norm_ne_zero_iff.mp this
      rcases exists_smul_of_det2_eq_zero (u := c - eₖ k) (v := w' k) hw'nz hd with ⟨t₀, ht₀⟩
      refine ⟨t₀, ?_⟩
      calc
        c = eₖ k + (c - eₖ k) := by abel
        _ = eₖ k + t₀ • (w' k) := by rw [ht₀]
    -- the sign identity and its negativity (mirror crossing sign)
    have hsign := crossing_side_sign_mirror (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (t₀ := Classical.choose hc2) (τ₀ := τ₀ₖ) heS (heₖS k) hout
      (by rfl : c = e + τ₀ₖ • w) (Classical.choose_spec hc2) (hφeₖ k) hww'k (hdet k)
    have hid := crossing_signedValue (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (τ₀ := τ₀ₖ) (by rfl : c = e + τ₀ₖ • w) hc2
    -- signedLineFunc (eₖk)(w'k) e = −τ₀ₖ·det2 w w'k < 0
    have hψ : signedLineFunc (eₖ k) (w' k) e = -(τ₀ₖ * det2 w (w' k)) := by
      simpa [mul_comm] using hid
    have hneg : -(τ₀ₖ * det2 w (w' k)) < 0 := by linarith
    rwa [hψ]
  exact hprod_ev.mono (fun k hk => hcore k hk)

/-- **Depth-0 nearly-parallel contradiction (T2)**: assemble (A)+(B)+R2.

Under the full depth-0 sequence data — `eₖ → e` with `φ(eₖ) < 0`
(`φ x := signedLineFunc e w x`), per-k `U`-sequences `q₂ k` approaching
`eₖ k` with unit ruling directions `w' k → w`, non-parallel
(`det2 w (w' k) ≠ 0`), and `C = flatComponent f p` nonempty with
`e ∈ closure C` and `C ⊆ {φ < 0}` — we get `False`:

* vertical cluster direction `w 0 = 0` is impossible
  (`vertical_cluster_dir_contradiction` at index 0);
* otherwise, fix `z₀ ∈ C`.  (A) the family functionals converge at `z₀`
  to `φ(z₀) < 0` (`signedLineFunc_tendsto_base_dir`), so eventually
  `ψₖ(z₀) < 0`; (B) `boundary_value_pos_eventually` gives eventually
  `ψₖ(e) > 0` (near-parallel positivity via R3's crossing outside the
  strip).  But R2 at `eₖ k` (`same_side_product`) puts `z₀` and
  `e ∈ closure C` strictly on the SAME side of `Lₖ`, i.e.
  `ψₖ(z₀)·ψₖ(e) > 0` — contradiction with opposite signs. -/
theorem depth_zero_nearly_parallel_contradiction {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior) (heₖe : Tendsto eₖ atTop (𝓝 e))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hww : Tendsto w' atTop (𝓝 w)) :
    False := by
  by_cases hw0z : w 0 = 0
  · exact vertical_cluster_dir_contradiction hf ha (e := e) (eₖ := eₖ 0) heS (heₖS 0)
      hq₀S hq₀U hq₀e (hq₂S 0) (hq₂U 0) (hq₂e 0) hw₁ (hw'₁ 0) hd₀ (hd₂ 0) hw0z (hdet 0)
  · have hw0nz : w 0 ≠ 0 := hw0z
    rcases hnonempty with ⟨z₀, hz₀⟩
    have hφz₀ : signedLineFunc e w z₀ < 0 := hside z₀ hz₀
    -- (A): ψₖ(z₀) → φ(z₀) < 0, hence eventually ψₖ(z₀) < 0
    have hA : Tendsto (fun k => signedLineFunc (eₖ k) (w' k) z₀) atTop
        (𝓝 (signedLineFunc e w z₀)) :=
      signedLineFunc_tendsto_base_dir z₀ heₖe hww
    have hA_ev : ∀ᶠ k in atTop, signedLineFunc (eₖ k) (w' k) z₀ < 0 := by
      have hε : 0 < -(signedLineFunc e w z₀) / 2 := by linarith
      have hclose : ∀ᶠ k in atTop,
          |signedLineFunc (eₖ k) (w' k) z₀ - signedLineFunc e w z₀|
            < -(signedLineFunc e w z₀) / 2 := by
        exact (Metric.tendsto_nhds.mp hA) (-(signedLineFunc e w z₀) / 2) hε
      filter_upwards [hclose] with k hk
      have hlo : signedLineFunc (eₖ k) (w' k) z₀ - signedLineFunc e w z₀
          < -(signedLineFunc e w z₀) / 2 := (abs_lt.mp hk).2
      have hhalf : signedLineFunc e w z₀ / 2 < 0 := by linarith
      linarith
    -- (B): eventually ψₖ(e) > 0
    have hB_ev : ∀ᶠ k in atTop, 0 < signedLineFunc (eₖ k) (w' k) e :=
      boundary_value_pos_eventually hf ha heS hq₀S hq₀U hq₀e hw₁ hd₀ heₖS
        hq₂S hq₂U hq₂e hw'₁ hd₂ hφeₖ hdet hww hw0nz
    -- pick one k with both
    have hboth : ∀ᶠ k in atTop,
        signedLineFunc (eₖ k) (w' k) z₀ < 0 ∧ 0 < signedLineFunc (eₖ k) (w' k) e :=
      hA_ev.and hB_ev
    rcases (eventually_atTop.mp hboth) with ⟨N, hN⟩
    have hNok : signedLineFunc (eₖ N) (w' N) z₀ < 0 ∧ 0 < signedLineFunc (eₖ N) (w' N) e :=
      hN N le_rfl
    -- R2 at eₖ N: z₀ and e on the same side of L_N
    have hprod_pos : 0 < signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e :=
      same_side_product hf ha (e := e) heS hq₀S hq₀U hq₀e hw₁ hd₀
        (eₖ := eₖ N) (heₖS N) (q₂ := q₂ N) (hq₂S N) (hq₂U N) (hq₂e N)
        (w' := w' N) (hw'₁ N) (hd₂ N) (p := p) heClosure (z₀ := z₀) hz₀
        (hφeₖ N) (hdet N)
    have hprod_neg : signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e < 0 :=
      mul_neg_of_neg_of_pos hNok.1 hNok.2
    linarith



/-- **Depth-0 nearly-parallel contradiction, mirror orientation (T2′)**: the
`depth_zero_nearly_parallel_contradiction` twin for the regime in which the
family directions converge to `-w` instead of `w` (the mirror cluster
orientation).  Hypotheses identical except `hwwm : w'ₖ → -w`.  Then for a
fixed `z₀ ∈ C` with `φ(z₀) < 0` (`φ x := signedLineFunc e w x`):
(A) `ψₖ(z₀) → signedLineFunc e (-w) z₀ = -φ(z₀) > 0`, so eventually
`ψₖ(z₀) > 0`; (B′) `boundary_value_neg_eventually` gives eventually
`ψₖ(e) < 0` (mirror crossing sign via R3's crossing outside the strip).
But R2 at `eₖ k` (`same_side_product`) puts `z₀` and `e ∈ closure C` on the
SAME side of `Lₖ`, i.e. `ψₖ(z₀)·ψₖ(e) > 0` — contradiction with opposite
signs. -/
theorem depth_zero_nearly_parallel_contradiction_mirror {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior) (heₖe : Tendsto eₖ atTop (𝓝 e))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hwwm : Tendsto w' atTop (𝓝 (-w))) :
    False := by
  by_cases hw0z : w 0 = 0
  · exact vertical_cluster_dir_contradiction hf ha (e := e) (eₖ := eₖ 0) heS (heₖS 0)
      hq₀S hq₀U hq₀e (hq₂S 0) (hq₂U 0) (hq₂e 0) hw₁ (hw'₁ 0) hd₀ (hd₂ 0) hw0z (hdet 0)
  · have hw0nz : w 0 ≠ 0 := hw0z
    rcases hnonempty with ⟨z₀, hz₀⟩
    have hφz₀ : signedLineFunc e w z₀ < 0 := hside z₀ hz₀
    -- (A): ψₖ(z₀) → signedLineFunc e (-w) z₀ = -φ(z₀) > 0, so eventually ψₖ(z₀) > 0
    have hA : Tendsto (fun k => signedLineFunc (eₖ k) (w' k) z₀) atTop
        (𝓝 (signedLineFunc e (-w) z₀)) :=
      signedLineFunc_tendsto_base_dir z₀ heₖe hwwm
    have hA0 : Tendsto (fun k => signedLineFunc (eₖ k) (w' k) z₀) atTop
        (𝓝 (-(signedLineFunc e w z₀))) := by
      simpa [signedLineFunc_neg] using hA
    have hA_ev : ∀ᶠ k in atTop, 0 < signedLineFunc (eₖ k) (w' k) z₀ := by
      have hε : 0 < (-(signedLineFunc e w z₀)) / 2 := by linarith
      have hclose : ∀ᶠ k in atTop,
          |signedLineFunc (eₖ k) (w' k) z₀ - (-(signedLineFunc e w z₀))|
            < (-(signedLineFunc e w z₀)) / 2 := by
        exact (Metric.tendsto_nhds.mp hA0) (-(signedLineFunc e w z₀) / 2) hε
      filter_upwards [hclose] with k hk
      have hgt : -( (signedLineFunc e w z₀)) / 2 < signedLineFunc (eₖ k) (w' k) z₀ := by
        -- |x − L| < ε gives L − ε < x, i.e. x > L − ε with L = −φ(z₀) < 0? no L > 0
        have h1 := abs_lt.mp hk
        have : -( (-(signedLineFunc e w z₀)) / 2) <
            signedLineFunc (eₖ k) (w' k) z₀ - (-(signedLineFunc e w z₀)) := h1.1
        linarith
      have hL : -(signedLineFunc e w z₀) - (-(signedLineFunc e w z₀)) / 2 > 0 := by linarith
      linarith
    -- (B′): eventually ψₖ(e) < 0
    have hB_ev : ∀ᶠ k in atTop, signedLineFunc (eₖ k) (w' k) e < 0 := by
      exact boundary_value_neg_eventually hf ha heS hq₀S hq₀U hq₀e hw₁ hd₀ heₖS
        hq₂S hq₂U hq₂e hw'₁ hd₂ hφeₖ hdet hwwm hw0nz
    -- pick one k with both
    have hboth : ∀ᶠ k in atTop,
        0 < signedLineFunc (eₖ k) (w' k) z₀ ∧ signedLineFunc (eₖ k) (w' k) e < 0 :=
      hA_ev.and hB_ev
    rcases (eventually_atTop.mp hboth) with ⟨N, hN⟩
    have hNok : 0 < signedLineFunc (eₖ N) (w' N) z₀ ∧ signedLineFunc (eₖ N) (w' N) e < 0 :=
      hN N le_rfl
    -- R2 at eₖ N: z₀ and e on the same side of L_N
    have hprod_pos : 0 < signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e :=
      same_side_product hf ha (e := e) heS hq₀S hq₀U hq₀e hw₁ hd₀
        (eₖ := eₖ N) (heₖS N) (q₂ := q₂ N) (hq₂S N) (hq₂U N) (hq₂e N)
        (w' := w' N) (hw'₁ N) (hd₂ N) (p := p) heClosure (z₀ := z₀) hz₀
        (hφeₖ N) (hdet N)
    have hprod_neg : signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e < 0 :=
      mul_neg_of_pos_of_neg hNok.1 hNok.2
    linarith


/-- **Direction data of an off-line family (the extraction half of the
depth-0 close-out)**: let `q₀` be a `U`-sequence approaching `e` with unit
direction limit `w`, and let `q₂ k` be `U`-families approaching `eₖ` with
`eₖ → e`.  Then there are per-k subsequential direction limits `W k`
(unit) along strict-mono index maps `γ k` (so the sub-families
`v k := q₂ k ∘ γ k` still approach `eₖ k` and their directions converge to
`W k`), and a strict-mono level-2 extraction `φ` with
`W (φ m) → wstar`, where `wstar` is unit and `wstar = w ∨ wstar = -w`
(the last by `rulingCluster_dirs_parallel` at `e`, fed with the diagonal
`U`-sequence). -/
theorem off_line_direction_data {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    {eₖ : ℕ → ℝ²} (heₖe : Tendsto eₖ atTop (𝓝 e))
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k))) :
    ∃ W : ℕ → ℝ², (∀ k, ‖W k‖ = 1) ∧
      ∃ γ : ℕ → ℕ → ℕ, (∀ k, StrictMono (γ k)) ∧
      (∀ k, Tendsto (fun m => q₂ k (γ k m)) atTop (𝓝 (eₖ k))) ∧
      (∀ k, Tendsto (fun m => unitKernelDir f (q₂ k (γ k m))) atTop (𝓝 (W k))) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ wstar : ℝ², ‖wstar‖ = 1 ∧
        (wstar = w ∨ wstar = -w) ∧
        Tendsto (fun m => W (φ m)) atTop (𝓝 wstar) := by
  -- per-k subsequential direction limits
  have hW : ∀ k, ∃ w : ℝ², ‖w‖ = 1 ∧ ∃ γ : ℕ → ℕ, StrictMono γ ∧
      Tendsto (fun m => unitKernelDir f (q₂ k (γ m))) atTop (𝓝 w) := fun k =>
    unitDir_subseq_convergent (u := fun m : ℕ => unitKernelDir f (q₂ k m))
      (fun m => norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hq₂S k m) (hq₂U k m)))
  let W : ℕ → ℝ² := fun k => Classical.choose (hW k)
  let γ : ℕ → ℕ → ℕ := fun k => Classical.choose (Classical.choose_spec (hW k)).2
  have hW₁ : ∀ k, ‖W k‖ = 1 := fun k => (Classical.choose_spec (hW k)).1
  have hγ : ∀ k, StrictMono (γ k) := fun k =>
    (Classical.choose_spec (Classical.choose_spec (hW k)).2).1
  have hdW : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k (γ k m))) atTop (𝓝 (W k)) := fun k =>
    (Classical.choose_spec (Classical.choose_spec (hW k)).2).2
  have hve : ∀ k, Tendsto (fun m => q₂ k (γ k m)) atTop (𝓝 (eₖ k)) := fun k =>
    (hq₂e k).comp (hγ k).tendsto_atTop
  -- level 2: a convergent subsequence of W
  rcases unitDir_subseq_convergent (u := W) hW₁ with ⟨wstar, hwstar, φ, hφmono, hφw⟩
  -- diagonal index choice: within rate 1/(m+1) of both eₖ and W along (v (φ m))
  have hdiag : ∀ m, ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ‖q₂ (φ m) (γ (φ m) n) - eₖ (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) ∧
      ‖unitKernelDir f (q₂ (φ m) (γ (φ m) n)) - W (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) := by
    intro m
    have hrate : 0 < (((m + 1 : ℕ) : ℝ)⁻¹) := by positivity
    have h1 : ∀ᶠ n in atTop, dist (q₂ (φ m) (γ (φ m) n)) (eₖ (φ m)) < (((m + 1 : ℕ) : ℝ)⁻¹) :=
      (Metric.tendsto_nhds.mp (hve (φ m))) (((m + 1 : ℕ) : ℝ)⁻¹) hrate
    have h2 : ∀ᶠ n in atTop,
        dist (unitKernelDir f (q₂ (φ m) (γ (φ m) n))) (W (φ m)) < (((m + 1 : ℕ) : ℝ)⁻¹) :=
      (Metric.tendsto_nhds.mp (hdW (φ m))) (((m + 1 : ℕ) : ℝ)⁻¹) hrate
    rcases (eventually_atTop.mp (h1.and h2)) with ⟨n₀, hn₀⟩
    refine ⟨n₀, ?_⟩
    intro n hn
    have h := hn₀ n hn
    constructor
    · simpa [dist_eq_norm] using h.1
    · simpa [dist_eq_norm] using h.2
  let ψ : ℕ → ℕ := fun m => γ (φ m) (Classical.choose (hdiag m))
  let u : ℕ → ℝ² := fun m => q₂ (φ m) (ψ m)
  -- the diagonal points satisfy the rate bounds
  have hu_rate : ∀ m,
      ‖u m - eₖ (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) ∧
      ‖unitKernelDir f (u m) - W (φ m)‖ < (((m + 1 : ℕ) : ℝ)⁻¹) := by
    intro m
    have hs := Classical.choose_spec (hdiag m)
    have hb := hs (Classical.choose (hdiag m)) le_rfl
    simpa [u, ψ] using hb
  have huS : ∀ m, u m ∈ stripInterior := by
    intro m
    exact hq₂S (φ m) (ψ m)
  have huU : ∀ m, dN f (u m) ≠ 0 := by
    intro m
    exact hq₂U (φ m) (ψ m)
  -- u m → e
  have hue : Tendsto u atTop (𝓝 e) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hrate : ∀ᶠ m : ℕ in atTop, (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := by
      have hz := (Metric.tendsto_nhds.mp tendsto_inv_nat_succ_zero) (ε / 2) hε2
      exact hz.mono (by
        intro m hm
        have h' : |((m + 1 : ℕ) : ℝ)⁻¹| < ε / 2 := by simpa [Real.dist_eq] using hm
        have h'' : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ |((m + 1 : ℕ) : ℝ)⁻¹| := le_abs_self _
        exact lt_of_le_of_lt h'' h')
    have hev : ∀ᶠ m in atTop, ‖eₖ (φ m) - e‖ < ε / 2 := by
      have hd := (Metric.tendsto_nhds.mp (heₖe.comp hφmono.tendsto_atTop)) (ε / 2) hε2
      exact hd.mono (by
        intro m hm
        simpa [dist_eq_norm] using hm)
    rcases (eventually_atTop.mp hrate) with ⟨M₁, hM₁⟩
    rcases (eventually_atTop.mp hev) with ⟨M₂, hM₂⟩
    exact eventually_atTop.2 ⟨max M₁ M₂, by
      intro m hm
      have hm1 : (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := hM₁ m (le_trans (le_max_left _ _) hm)
      have hm2 : ‖eₖ (φ m) - e‖ < ε / 2 := hM₂ m (le_trans (le_max_right _ _) hm)
      have hbd := (hu_rate m).1
      have hnorm : ‖u m - e‖ < ε := by
        calc
          ‖u m - e‖ ≤ ‖u m - eₖ (φ m)‖ + ‖eₖ (φ m) - e‖ := by
            rw [← sub_add_sub_cancel (u m) (eₖ (φ m)) e]
            exact norm_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add (lt_trans hbd hm1) hm2
          _ = ε := by ring
      simpa [dist_eq_norm] using hnorm⟩
  -- directions of the diagonal points converge to wstar
  have hud : Tendsto (fun m => unitKernelDir f (u m)) atTop (𝓝 wstar) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hrate : ∀ᶠ m : ℕ in atTop, (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := by
      have hz := (Metric.tendsto_nhds.mp tendsto_inv_nat_succ_zero) (ε / 2) hε2
      exact hz.mono (by
        intro m hm
        have h' : |((m + 1 : ℕ) : ℝ)⁻¹| < ε / 2 := by simpa [Real.dist_eq] using hm
        have h'' : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ |((m + 1 : ℕ) : ℝ)⁻¹| := le_abs_self _
        exact lt_of_le_of_lt h'' h')
    have hw' : ∀ᶠ m in atTop, ‖W (φ m) - wstar‖ < ε / 2 := by
      have hd := (Metric.tendsto_nhds.mp hφw) (ε / 2) hε2
      exact hd.mono (by
        intro m hm
        simpa [dist_eq_norm] using hm)
    rcases (eventually_atTop.mp hrate) with ⟨M₁, hM₁⟩
    rcases (eventually_atTop.mp hw') with ⟨M₂, hM₂⟩
    exact eventually_atTop.2 ⟨max M₁ M₂, by
      intro m hm
      have hm1 : (((m + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := hM₁ m (le_trans (le_max_left _ _) hm)
      have hm2 : ‖W (φ m) - wstar‖ < ε / 2 := hM₂ m (le_trans (le_max_right _ _) hm)
      have hbd := (hu_rate m).2
      have hnorm : ‖unitKernelDir f (u m) - wstar‖ < ε := by
        calc
          ‖unitKernelDir f (u m) - wstar‖
              ≤ ‖unitKernelDir f (u m) - W (φ m)‖ + ‖W (φ m) - wstar‖ := by
                rw [← sub_add_sub_cancel (unitKernelDir f (u m)) (W (φ m)) wstar]
                exact norm_add_le _ _
          _ < ε / 2 + ε / 2 := add_lt_add (lt_trans hbd hm1) hm2
          _ = ε := by ring
      simpa [dist_eq_norm] using hnorm⟩
  -- the parallelity of wstar with w
  have hpar : wstar = w ∨ wstar = -w := by
    exact rulingCluster_dirs_parallel hf ha heS (q₁ := u) (q₂ := q₀)
      huS huU hq₀S hq₀U hue hq₀e hud hd₀
  exact ⟨W, hW₁, γ, hγ, hve, hdW, φ, hφmono, wstar, hwstar, hpar, hφw⟩


/-- **Off-line sequence contradiction (depth-0 close-out)**: let `e` lie in
`closure C` with `C = flatComponent f p` strictly in `{φ < 0}`
(`φ x := signedLineFunc e w x`), `q₀` a `U`-sequence approaching `e` with
unit direction limit `w`, and let `eₖ` be strip-interior points approaching
`e` with `φ(eₖ) < 0` (off-line frontier points on `C`'s side), each
equipped with a `U`-family `q₂ k` approaching it.  Then `False`: extract
the direction data (`off_line_direction_data`: per-k limits `W k`, level-2
`φ` with `W (φ m) → wstar = ±w`) and split:

* **regime C** (eventually `det2 w (W (φ m)) ≠ 0`): the shifted tail
  satisfies all hypotheses of `depth_zero_nearly_parallel_contradiction`
  (if `wstar = w`) or of its mirror (if `wstar = -w`);
* **regime A** (infinitely many `det2 w (W (φ m)) = 0`): extract the
  exact-parallel sub-subsequence (`Nat.nth`), where `W (φ (ρ n)) = ±w`
  (`unit_eq_or_neg_of_det2_eq_zero`), and apply
  `no_exact_parallel_depth_zero` (`φ(eₖ(φ(ρ n))) → 0` by continuity). -/
theorem off_line_sequence_contradiction {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hd₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w))
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior) (heₖe : Tendsto eₖ atTop (𝓝 e))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k))) :
    False := by
  rcases off_line_direction_data hf ha heS hq₀S hq₀U hq₀e hw₁ hd₀ heₖe
    hq₂S hq₂U hq₂e with ⟨W, hW₁, γ, hγ, hve, hdW, φ, hφmono, wstar, hwstar, hpar, hφw⟩
  by_cases hC : ∀ᶠ m in atTop, det2 w (W (φ m)) ≠ 0
  · -- regime C: shifted tail, apply T2 or its mirror
    rcases (eventually_atTop.mp hC) with ⟨N, hN⟩
    have hshift : StrictMono (fun m : ℕ => m + N) := by
      intro a b hab
      change a + N < b + N
      omega
    let e' : ℕ → ℝ² := fun m => eₖ (φ (m + N))
    let q2' : ℕ → ℕ → ℝ² := fun m n => q₂ (φ (m + N)) (γ (φ (m + N)) n)
    let w' : ℕ → ℝ² := fun m => W (φ (m + N))
    have heₖS' : ∀ m, e' m ∈ stripInterior := by
      intro m
      exact heₖS (φ (m + N))
    have heₖe' : Tendsto e' atTop (𝓝 e) := by
      have h1 : Tendsto (fun m => eₖ (φ (m + N))) atTop (𝓝 e) :=
        (heₖe.comp hφmono.tendsto_atTop).comp hshift.tendsto_atTop
      simpa [e'] using h1
    have hφeₖ' : ∀ m, signedLineFunc e w (e' m) < 0 := by
      intro m
      exact hφeₖ (φ (m + N))
    have hq₂S' : ∀ m n, q2' m n ∈ stripInterior := by
      intro m n
      exact hq₂S (φ (m + N)) (γ (φ (m + N)) n)
    have hq₂U' : ∀ m n, dN f (q2' m n) ≠ 0 := by
      intro m n
      exact hq₂U (φ (m + N)) (γ (φ (m + N)) n)
    have hq₂e' : ∀ m, Tendsto (q2' m) atTop (𝓝 (e' m)) := by
      intro m
      have h := hve (φ (m + N))
      simpa [q2', e'] using h
    have hw'₁ : ∀ m, ‖w' m‖ = 1 := by
      intro m
      exact hW₁ (φ (m + N))
    have hd₂' : ∀ m, Tendsto (fun n => unitKernelDir f (q2' m n)) atTop (𝓝 (w' m)) := by
      intro m
      have h := hdW (φ (m + N))
      simpa [q2', w'] using h
    have hdet' : ∀ m, det2 w (w' m) ≠ 0 := by
      intro m
      have hN' : det2 w (W (φ (m + N))) ≠ 0 := hN (m + N) (by omega)
      simpa [w'] using hN'
    have hww' : Tendsto w' atTop (𝓝 wstar) := by
      have h1 : Tendsto (fun m => W (φ (m + N))) atTop (𝓝 wstar) :=
        hφw.comp hshift.tendsto_atTop
      simpa [w'] using h1
    cases hpar with
    | inl hws =>
        exact depth_zero_nearly_parallel_contradiction hf ha (e := e) heS
          hq₀S hq₀U hq₀e hw₁ hd₀ (p := p) heClosure hnonempty hside
          (eₖ := e') heₖS' heₖe' hφeₖ' (q₂ := q2') hq₂S' hq₂U' hq₂e'
          (w' := w') hw'₁ hd₂' hdet' (by simpa [hws] using hww')
    | inr hws =>
        exact depth_zero_nearly_parallel_contradiction_mirror hf ha (e := e) heS
          hq₀S hq₀U hq₀e hw₁ hd₀ (p := p) heClosure hnonempty hside
          (eₖ := e') heₖS' heₖe' hφeₖ' (q₂ := q2') hq₂S' hq₂U' hq₂e'
          (w' := w') hw'₁ hd₂' hdet' (by simpa [hws] using hww')
  · -- regime A: infinitely many exact-parallel directions
    have hnotC : ¬ ∀ᶠ m in atTop, det2 w (W (φ m)) ≠ 0 := hC
    let P : ℕ → Prop := fun m => det2 w (W (φ m)) = 0
    have hinfP : Set.Infinite {m : ℕ | P m} := by
      have h1 : ∃ᶠ m in atTop, ¬ det2 w (W (φ m)) ≠ 0 := Filter.not_eventually.mp hnotC
      have hinf1 : Set.Infinite {m : ℕ | ¬ det2 w (W (φ m)) ≠ 0} :=
        (Nat.frequently_atTop_iff_infinite).1 h1
      have hset : {m : ℕ | ¬ det2 w (W (φ m)) ≠ 0} = {m : ℕ | P m} := by
        ext m
        simp [P]
      rwa [← hset]
    let ρ : ℕ → ℕ := fun n => Nat.nth P n
    have hρmono : StrictMono ρ := Nat.nth_strictMono hinfP
    have hPρ : ∀ n, P (ρ n) := fun n => Nat.nth_mem_of_infinite hinfP n
    let e' : ℕ → ℝ² := fun n => eₖ (φ (ρ n))
    let q2' : ℕ → ℕ → ℝ² := fun n m => q₂ (φ (ρ n)) (γ (φ (ρ n)) m)
    let w' : ℕ → ℝ² := fun n => W (φ (ρ n))
    have hq₂S' : ∀ n m, q2' n m ∈ stripInterior := by
      intro n m
      exact hq₂S (φ (ρ n)) (γ (φ (ρ n)) m)
    have hq₂U' : ∀ n m, dN f (q2' n m) ≠ 0 := by
      intro n m
      exact hq₂U (φ (ρ n)) (γ (φ (ρ n)) m)
    have hq₂e' : ∀ n, Tendsto (q2' n) atTop (𝓝 (e' n)) := by
      intro n
      have h := hve (φ (ρ n))
      simpa [q2', e'] using h
    have hw'₁ : ∀ n, ‖w' n‖ = 1 := by
      intro n
      exact hW₁ (φ (ρ n))
    have hd₂' : ∀ n, Tendsto (fun m => unitKernelDir f (q2' n m)) atTop (𝓝 (w' n)) := by
      intro n
      have h := hdW (φ (ρ n))
      simpa [q2', w'] using h
    have hpar' : ∀ n, w = w' n ∨ w = -w' n := by
      intro n
      have hz : det2 w (W (φ (ρ n))) = 0 := hPρ n
      exact unit_eq_or_neg_of_det2_eq_zero hw₁ (hW₁ (φ (ρ n))) (by simpa [w'] using hz)
    have hφe' : ∀ n, signedLineFunc e w (e' n) < 0 := by
      intro n
      exact hφeₖ (φ (ρ n))
    have h_e'e : Tendsto (fun n => eₖ (φ (ρ n))) atTop (𝓝 e) :=
      (heₖe.comp hφmono.tendsto_atTop).comp hρmono.tendsto_atTop
    have hφe'0 : Tendsto (fun n => signedLineFunc e w (e' n)) atTop (𝓝 0) := by
      have hφcont : Continuous (fun x : ℝ² => signedLineFunc e w x) := continuous_signedLineFunc e w
      have hφe0 : Tendsto (fun n => signedLineFunc e w (eₖ (φ (ρ n)))) atTop
          (𝓝 (signedLineFunc e w e)) :=
        hφcont.continuousAt.tendsto.comp h_e'e
      have hself : signedLineFunc e w e = 0 := signedLineFunc_self e w
      simpa [e', hself] using hφe0
    exact no_exact_parallel_depth_zero hf ha (e := e) (w := w) (e' := e') (q₂ := q2')
      hq₂S' hq₂U' hq₂e' (w' := w') hw'₁ hd₂' hpar' (p := p) heClosure hnonempty hside
      hφe' hφe'0


/-- **Same-side product, reference-robust (H-C′)**: `same_side_product`
with the reference direction decoupled from the bookkeeping base: the
reference `U`-sequence `q₀` has its OWN unit direction limit `w₀`
(`hd₀₀`), and the base `w` satisfies `w = w₀ ∨ w = -w₀` (`hpar₀`; the
limit line `e + ℝ·w = e + ℝ·w₀` is the same either way).  All other data
(`hφeₖ`, `hdet`) are relative to `w`.  Conclusion unchanged:
`0 < ψₖ(z₀)·ψₖ(e)` with `ψₖ x := signedLineFunc eₖ w' x`.  Proof: mutual
avoidance is applied to the reference line `L(e, w₀)` (its own limit
line); `eₖ ∉ L(e, w₀)` follows from `φ_w(eₖ) ≠ 0` and collinearity of
`w` with `w₀`. -/
lemma same_side_product_robust {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {eₖ : ℝ²} (heₖS : eₖ ∈ stripInterior)
    {q₂ : ℕ → ℝ²} (hq₂S : ∀ m, q₂ m ∈ stripInterior) (hq₂U : ∀ m, dN f (q₂ m) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 eₖ))
    {w' : ℝ²} (hw'₁ : ‖w'‖ = 1)
    (hd₂ : Tendsto (fun m => unitKernelDir f (q₂ m)) atTop (𝓝 w'))
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    {z₀ : ℝ²} (hz₀ : z₀ ∈ flatComponent f p)
    (hφeₖ : signedLineFunc e w eₖ ≠ 0)
    (hdet : det2 w w' ≠ 0) :
    0 < signedLineFunc eₖ w' z₀ * signedLineFunc eₖ w' e := by
  -- eₖ ∉ L(e, w₀): from φ_w(eₖ) ≠ 0 and w ∥ w₀
  have hoff₀ : ¬ ∃ s : ℝ, eₖ = e + s • w₀ := by
    intro hone
    rcases hone with ⟨s, hs⟩
    have hline₀ : signedLineFunc e w₀ eₖ = 0 := by
      calc
        signedLineFunc e w₀ eₖ = signedLineFunc e w₀ (e + s • w₀) := by rw [hs]
        _ = 0 := signedLineFunc_const_along_dir e w₀ s
    -- φ_w(eₖ) = 0 too (w ∥ w₀)
    have hφ0 : signedLineFunc e w eₖ = 0 := by
      rcases hpar₀ with hp | hp
      · rwa [← hp] at hline₀
      · -- w = -w₀: signedLineFunc e (-w₀) = -signedLineFunc e w₀
        have hn : signedLineFunc e w eₖ = -(signedLineFunc e w₀ eₖ) := by
          rw [hp]
          exact signedLineFunc_neg e w₀ eₖ
        linarith
    exact hφeₖ hφ0
  -- e ∉ L(eₖ): mutual avoidance applied to the reference line L(e, w₀)
  have hoff' : ¬ ∃ s : ℝ, e = eₖ + s • w' :=
    cluster_lines_mutually_avoid hf ha (e₁ := e) (e₂ := eₖ) heS heₖS
      hq₀S hq₀U hq₀e hq₂S hq₂U hq₂e hw₀₁ hw'₁ hd₀₀ hd₂ hoff₀
  -- ψ(e) ≠ 0 (e not on Lₖ)
  have hψe0 : signedLineFunc eₖ w' e ≠ 0 := by
    intro h0
    have hw'nz : w' ≠ 0 := by
      have : ‖w'‖ ≠ 0 := by linarith
      exact norm_ne_zero_iff.mp this
    have hpar : ∃ c : ℝ, e - eₖ = c • w' :=
      exists_smul_of_det2_eq_zero (u := e - eₖ) (v := w') hw'nz
        (by simpa [signedLineFunc_eq_det2] using h0)
    rcases hpar with ⟨c, hc⟩
    exact hoff' ⟨c, by
      calc
        e = eₖ + (e - eₖ) := by abel
        _ = eₖ + c • w' := by rw [hc]⟩
  -- R2 at eₖ
  have hR2 := flatComponent_one_side_of_cluster_line hf ha (q := q₂) hq₂S hq₂U hq₂e
    (hwnorm := hw'₁) (hd := hd₂) (p := p)
  rcases hR2 with hpos | hneg
  · have hψz : 0 < signedLineFunc eₖ w' z₀ := hpos z₀ hz₀
    have hψe : 0 < signedLineFunc eₖ w' e := by
      have hsub : (flatComponent f p) ⊆ {x : ℝ² | -(signedLineFunc eₖ w' x) < 0} := by
        intro x hx
        have hx' : 0 < signedLineFunc eₖ w' x := hpos x hx
        change -(signedLineFunc eₖ w' x) < 0
        linarith
      have hle : -(signedLineFunc eₖ w' e) ≤ 0 :=
        closure_lt_le (Continuous.neg (continuous_signedLineFunc eₖ w')) heClosure hsub
      have hge : 0 ≤ signedLineFunc eₖ w' e := by linarith
      exact lt_of_le_of_ne hge hψe0.symm
    exact mul_pos hψz hψe
  · have hψz : signedLineFunc eₖ w' z₀ < 0 := hneg z₀ hz₀
    have hle : signedLineFunc eₖ w' e ≤ 0 := by
      have hsub : (flatComponent f p) ⊆ {x : ℝ² | signedLineFunc eₖ w' x < 0} := by
        intro x hx
        exact hneg x hx
      exact closure_lt_le (continuous_signedLineFunc eₖ w') heClosure hsub
    have hψe : signedLineFunc eₖ w' e < 0 := lt_of_le_of_ne hle hψe0
    exact mul_pos_of_neg_of_neg hψz hψe


/-- **Boundary-value positivity, reference-robust (H-B-robust)**: the
`boundary_value_pos_eventually` statement with the reference direction
decoupled: `q₀` has its own unit direction limit `w₀` (`hd₀₀`) and the
bookkeeping base `w` satisfies `w = w₀ ∨ w = -w₀` (`hpar₀`); all
`φ`-data (`hφeₖ`), `hdet` and the family limit `hww` are relative to `w`.
The crossing point `c = e + τ₀ₖ·w` is shown outside the strip via R3
applied to the reference line `L(e, w₀)` (aligned branch: rewrite `w₀ ↦ w`;
anti branch: R3 in `w₀`-coordinates plus the point equality
`e + τ₀₀·w₀ = e + τ₀ₖ·w` with `w₀ = -w`, `τ₀₀ = -τ₀ₖ`). -/
lemma boundary_value_pos_eventually_robust {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hww : Tendsto w' atTop (𝓝 w)) (hw0nz : w 0 ≠ 0) :
    ∀ᶠ k in atTop, 0 < signedLineFunc (eₖ k) (w' k) e := by
  -- eventually (w 0)·(w'ₖ 0) > 0 (family → w, so product → (w 0)² > 0)
  have hcoord : Tendsto (fun k => (w' k) 0) atTop (𝓝 (w 0)) := by
    have hc : Continuous (fun v : ℝ² => v 0) := by fun_prop
    exact hc.continuousAt.tendsto.comp hww
  have hprod_ev : ∀ᶠ k in atTop, (w 0) * (w' k) 0 > 0 := by
    have hmulc : Continuous (fun x : ℝ => (w 0) * x) := by fun_prop
    have hp_tend : Tendsto (fun k => (w 0) * (w' k) 0) atTop (𝓝 ((w 0) * (w 0))) :=
      hmulc.continuousAt.tendsto.comp hcoord
    have hc0 : (w 0) * (w 0) > 0 := by
      exact mul_self_pos.mpr hw0nz
    have hε : 0 < (w 0) * (w 0) / 2 := by positivity
    have hclose : ∀ᶠ k in atTop, |(w 0) * (w' k) 0 - (w 0) * (w 0)| < (w 0) * (w 0) / 2 := by
      exact (Metric.tendsto_nhds.mp hp_tend) ((w 0) * (w 0) / 2) hε
    filter_upwards [hclose] with k hk
    have hparts := abs_lt.mp hk
    have hgt : -( (w 0) * (w 0) / 2) < (w 0) * (w' k) 0 - (w 0) * (w 0) := hparts.1
    have hpos : 0 < (w 0) * (w' k) 0 := by
      have : (w 0) * (w 0) - (w 0) * (w 0) / 2 < (w 0) * (w' k) 0 := by linarith
      linarith
    exact hpos
  -- the positivity at a given k with (w0)·(w'k0)>0
  have hcore : ∀ k, (w 0) * (w' k) 0 > 0 →
      0 < signedLineFunc (eₖ k) (w' k) e := by
    intro k hww'k
    let τ₀ₖ : ℝ := det2 (eₖ k - e) (w' k) / det2 w (w' k)
    let c : ℝ² := e + τ₀ₖ • w
    -- c ∉ S via R3, applied to the reference line L(e, w₀)
    have hout : c ∉ stripInterior := by
      rcases hpar₀ with hpar₀w | hpar₀w
      · -- aligned: w = w₀, direct R3
        have h := cluster_lines_cross_not_in_strip hf ha heS (heₖS k)
          hq₀S hq₀U hq₀e (hq₂S k) (hq₂U k) (hq₂e k) hw₀₁ (hw'₁ k) hd₀₀ (hd₂ k)
          (by simpa [hpar₀w] using hdet k)
        simpa [c, τ₀ₖ, hpar₀w] using h
      · -- anti: w = -w₀; R3 in w₀-coordinates, then convert
        let τ₀₀ : ℝ := det2 (eₖ k - e) (w' k) / det2 w₀ (w' k)
        have hd₀ₖ : det2 w₀ (w' k) ≠ 0 := by
          have hd₀' : det2 w (w' k) ≠ 0 := hdet k
          -- det2 (−w₀)(w'k) = −(det2 w₀ (w'k)) via w = −w₀
          have hd₀neg : det2 w (w' k) = -det2 w₀ (w' k) := by
            rw [hpar₀w]
            simp [det2]
            ring
          rw [hd₀neg] at hd₀'
          -- hd₀' : -(det2 w₀ (w'k)) ≠ 0; goal det2 w₀ (w'k) ≠ 0
          intro hz
          apply hd₀'
          simp [hz]
        have h₀ : e + τ₀₀ • w₀ ∉ stripInterior := by
          have h := cluster_lines_cross_not_in_strip hf ha heS (heₖS k)
            hq₀S hq₀U hq₀e (hq₂S k) (hq₂U k) (hq₂e k) hw₀₁ (hw'₁ k) hd₀₀ (hd₂ k) hd₀ₖ
          simpa [τ₀₀] using h
        have hconv : e + τ₀₀ • w₀ = c := by
          -- τ₀₀ • w₀ = τ₀ₖ • w with w = -w₀ (τ₀₀ = -τ₀ₖ)
          have hw₀w : w₀ = -w := by
            rw [hpar₀w]
            simp
          dsimp [c, τ₀ₖ, τ₀₀]
          rw [hw₀w]
          congr 1
          -- goal: (num/det2 (-w) (w'k)) • (-w) = (num/det2 w (w'k)) • w
          have hd₂w : det2 (-w) (w' k) = -det2 w (w' k) := by
            simp [det2]
            ring
          rw [hd₂w]
          -- (num / -(d2)) • (-w) = (num / d2) • w
          rw [div_neg]
          rw [neg_smul, smul_neg, neg_neg]
        simpa [hconv] using h₀
    -- c ∈ Lₖ: det2 (c − eₖk)(w'k) = 0
    have hc2 : ∃ t₀ : ℝ, c = eₖ k + t₀ • (w' k) := by
      have hd : det2 (c - eₖ k) (w' k) = 0 := by
        have hii := det2_intersect_on_second (a := e) (b := eₖ k) (u := w) (v := w' k) (hdet k)
        simpa [c, τ₀ₖ] using hii
      have hw'nz : w' k ≠ 0 := by
        have : ‖w' k‖ ≠ 0 := by linarith [hw'₁ k]
        exact norm_ne_zero_iff.mp this
      rcases exists_smul_of_det2_eq_zero (u := c - eₖ k) (v := w' k) hw'nz hd with ⟨t₀, ht₀⟩
      refine ⟨t₀, ?_⟩
      calc
        c = eₖ k + (c - eₖ k) := by abel
        _ = eₖ k + t₀ • (w' k) := by rw [ht₀]
    -- the sign identity and its positivity
    have hsign := crossing_side_sign (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (t₀ := Classical.choose hc2) (τ₀ := τ₀ₖ) heS (heₖS k) hout
      (by rfl : c = e + τ₀ₖ • w) (Classical.choose_spec hc2) (hφeₖ k) hww'k (hdet k)
    have hid := crossing_signedValue (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (τ₀ := τ₀ₖ) (by rfl : c = e + τ₀ₖ • w) hc2
    have hψ : signedLineFunc (eₖ k) (w' k) e = -(τ₀ₖ * det2 w (w' k)) := by
      simpa [mul_comm] using hid
    have hpos : 0 < -(τ₀ₖ * det2 w (w' k)) := by linarith
    rwa [hψ]
  exact hprod_ev.mono (fun k hk => hcore k hk)


/-- **Boundary-value negativity, reference-robust (H-B′-robust)**: the
mirror of `boundary_value_pos_eventually_robust`: same reference-decoupled
setup (`q₀` with own unit limit `w₀`, base `w` with `w = w₀ ∨ w = -w₀`),
but now the family directions converge to `-w` (`hwwm`), so eventually
`(w 0)·(w'ₖ 0) < 0` and the mirror crossing sign
(`crossing_side_sign_mirror`) gives EVENTUALLY
`signedLineFunc (eₖ k) (w' k) e < 0`. -/
lemma boundary_value_neg_eventually_robust {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hwwm : Tendsto w' atTop (𝓝 (-w))) (hw0nz : w 0 ≠ 0) :
    ∀ᶠ k in atTop, signedLineFunc (eₖ k) (w' k) e < 0 := by
  -- eventually (w 0)·(w'ₖ 0) < 0 (product → −(w 0)² < 0)
  have hcoord : Tendsto (fun k => (w' k) 0) atTop (𝓝 (-(w 0))) := by
    have hc : Continuous (fun v : ℝ² => v 0) := by fun_prop
    have h1 : Tendsto (fun k => (w' k) 0) atTop (𝓝 ((-w) 0)) := hc.continuousAt.tendsto.comp hwwm
    have hnegc : (-w) 0 = -(w 0) := by simp
    simpa [hnegc] using h1
  have hprod_ev : ∀ᶠ k in atTop, (w 0) * (w' k) 0 < 0 := by
    have hmulc : Continuous (fun x : ℝ => (w 0) * x) := by fun_prop
    have hp_tend : Tendsto (fun k => (w 0) * (w' k) 0) atTop (𝓝 ((w 0) * (-(w 0)))) :=
      hmulc.continuousAt.tendsto.comp hcoord
    have hc0 : (w 0) * (w 0) > 0 := by
      exact mul_self_pos.mpr hw0nz
    have hε : 0 < (w 0) * (w 0) / 2 := by positivity
    have hclose : ∀ᶠ k in atTop,
        |(w 0) * (w' k) 0 - (w 0) * (-(w 0))| < (w 0) * (w 0) / 2 := by
      exact (Metric.tendsto_nhds.mp hp_tend) ((w 0) * (w 0) / 2) hε
    filter_upwards [hclose] with k hk
    have hparts := abs_lt.mp hk
    have hlt : (w 0) * (w' k) 0 - (w 0) * (-(w 0)) < (w 0) * (w 0) / 2 := hparts.2
    have hneg : (w 0) * (w' k) 0 < 0 := by
      have hR : (w 0) * (-(w 0)) + (w 0) * (w 0) / 2 = -( (w 0) * (w 0) / 2) := by ring
      have hRneg : (w 0) * (-(w 0)) + (w 0) * (w 0) / 2 < 0 := by
        rw [hR]
        linarith
      linarith
    exact hneg
  -- the negativity at a given k with (w0)·(w'k0)<0
  have hcore : ∀ k, (w 0) * (w' k) 0 < 0 →
      signedLineFunc (eₖ k) (w' k) e < 0 := by
    intro k hww'k
    let τ₀ₖ : ℝ := det2 (eₖ k - e) (w' k) / det2 w (w' k)
    let c : ℝ² := e + τ₀ₖ • w
    -- c ∉ S via R3, applied to the reference line L(e, w₀)
    have hout : c ∉ stripInterior := by
      rcases hpar₀ with hpar₀w | hpar₀w
      · have h := cluster_lines_cross_not_in_strip hf ha heS (heₖS k)
          hq₀S hq₀U hq₀e (hq₂S k) (hq₂U k) (hq₂e k) hw₀₁ (hw'₁ k) hd₀₀ (hd₂ k)
          (by simpa [hpar₀w] using hdet k)
        simpa [c, τ₀ₖ, hpar₀w] using h
      · let τ₀₀ : ℝ := det2 (eₖ k - e) (w' k) / det2 w₀ (w' k)
        have hd₀ₖ : det2 w₀ (w' k) ≠ 0 := by
          have hd₀' : det2 w (w' k) ≠ 0 := hdet k
          have hd₀neg : det2 w (w' k) = -det2 w₀ (w' k) := by
            rw [hpar₀w]
            simp [det2]
            ring
          rw [hd₀neg] at hd₀'
          intro hz
          apply hd₀'
          simp [hz]
        have h₀ : e + τ₀₀ • w₀ ∉ stripInterior := by
          have h := cluster_lines_cross_not_in_strip hf ha heS (heₖS k)
            hq₀S hq₀U hq₀e (hq₂S k) (hq₂U k) (hq₂e k) hw₀₁ (hw'₁ k) hd₀₀ (hd₂ k) hd₀ₖ
          simpa [τ₀₀] using h
        have hconv : e + τ₀₀ • w₀ = c := by
          have hw₀w : w₀ = -w := by
            rw [hpar₀w]
            simp
          dsimp [c, τ₀ₖ, τ₀₀]
          rw [hw₀w]
          congr 1
          have hd₂w : det2 (-w) (w' k) = -det2 w (w' k) := by
            simp [det2]
            ring
          rw [hd₂w]
          rw [div_neg]
          rw [neg_smul, smul_neg, neg_neg]
        simpa [hconv] using h₀
    -- c ∈ Lₖ: det2 (c − eₖk)(w'k) = 0
    have hc2 : ∃ t₀ : ℝ, c = eₖ k + t₀ • (w' k) := by
      have hd : det2 (c - eₖ k) (w' k) = 0 := by
        have hii := det2_intersect_on_second (a := e) (b := eₖ k) (u := w) (v := w' k) (hdet k)
        simpa [c, τ₀ₖ] using hii
      have hw'nz : w' k ≠ 0 := by
        have : ‖w' k‖ ≠ 0 := by linarith [hw'₁ k]
        exact norm_ne_zero_iff.mp this
      rcases exists_smul_of_det2_eq_zero (u := c - eₖ k) (v := w' k) hw'nz hd with ⟨t₀, ht₀⟩
      refine ⟨t₀, ?_⟩
      calc
        c = eₖ k + (c - eₖ k) := by abel
        _ = eₖ k + t₀ • (w' k) := by rw [ht₀]
    -- the sign identity and its negativity (mirror crossing sign)
    have hsign := crossing_side_sign_mirror (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (t₀ := Classical.choose hc2) (τ₀ := τ₀ₖ) heS (heₖS k) hout
      (by rfl : c = e + τ₀ₖ • w) (Classical.choose_spec hc2) (hφeₖ k) hww'k (hdet k)
    have hid := crossing_signedValue (e := e) (e' := eₖ k) (c := c) (w := w) (w' := w' k)
      (τ₀ := τ₀ₖ) (by rfl : c = e + τ₀ₖ • w) hc2
    have hψ : signedLineFunc (eₖ k) (w' k) e = -(τ₀ₖ * det2 w (w' k)) := by
      simpa [mul_comm] using hid
    have hneg : -(τ₀ₖ * det2 w (w' k)) < 0 := by linarith
    rwa [hψ]
  exact hprod_ev.mono (fun k hk => hcore k hk)


/-- **Vertical cluster direction, reference-robust**: the
`vertical_cluster_dir_contradiction` statement with the reference
direction decoupled (`q₀` with own unit limit `w₀`, base `w` with
`w = w₀ ∨ w = -w₀`).  When `w 0 = 0` both `w` and `w₀` are vertical, so
the crossing of the vertical line `L(e) = {x0 = e 0}` with `Lₖ` lies in
the strip — contradicting R3. -/
theorem vertical_cluster_dir_contradiction_robust {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {eₖ : ℝ²} (heₖS : eₖ ∈ stripInterior)
    {q₂ : ℕ → ℝ²} (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₂e : Tendsto q₂ atTop (𝓝 eₖ))
    {w' : ℝ²} (hw'₁ : ‖w'‖ = 1)
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w'))
    (hw0 : w 0 = 0) (hdet : det2 w w' ≠ 0) : False := by
  rcases hpar₀ with hp | hp
  · -- aligned: w = w₀; use direction w₀ with the given data
    exact vertical_cluster_dir_contradiction hf ha (e := e) (eₖ := eₖ) heS heₖS
      hq₀S hq₀U hq₀e hq₂S hq₂U hq₂e hw₀₁ hw'₁ hd₀₀ hd₂
      (by simpa [hp] using hw0) (by simpa [hp] using hdet)
  · -- anti: w = -w₀; use direction w₀ (vertical too)
    have hw₀w : w₀ = -w := by
      rw [hp]
      simp
    have hw0₀ : w₀ 0 = 0 := by
      rw [hw₀w]
      have : (-w) 0 = -(w 0) := by simp
      rw [this, hw0]
      norm_num
    have hdet₀ : det2 w₀ w' ≠ 0 := by
      have hrel : det2 w₀ w' = -det2 w w' := by
        rw [hw₀w]
        simp [det2]
        ring
      intro hz
      apply hdet
      rw [hrel] at hz
      linarith
    exact vertical_cluster_dir_contradiction hf ha (e := e) (eₖ := eₖ) heS heₖS
      hq₀S hq₀U hq₀e hq₂S hq₂U hq₂e hw₀₁ hw'₁ hd₀₀ hd₂ hw0₀ hdet₀


/-- **Depth-0 nearly-parallel contradiction, reference-robust (T2r)**: the
`depth_zero_nearly_parallel_contradiction` statement with the reference
direction decoupled (`q₀` own limit `w₀`, base `w` with
`w = w₀ ∨ w = -w₀`).  Family directions converge to `w` (`hww`), `C` is
strictly in `{φ_w < 0}` with `z₀ ∈ C`, `e ∈ closure C`,
`φ_w(eₖ) < 0`, per-k approaching families, `det2 w (w'ₖ) ≠ 0`.  Concludes
`False` via the robust boundary positivity (H-B) and the robust same-side
product (R2) against the convergence of `ψₖ(z₀)` to `φ_w(z₀) < 0`. -/
theorem depth_zero_robust_contradiction {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior) (heₖe : Tendsto eₖ atTop (𝓝 e))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hww : Tendsto w' atTop (𝓝 w)) :
    False := by
  by_cases hw0z : w 0 = 0
  · exact vertical_cluster_dir_contradiction_robust hf ha heS hq₀S hq₀U hq₀e
      hw₀₁ hd₀₀ hw₁ hpar₀ (heₖS 0) (hq₂S 0) (hq₂U 0) (hq₂e 0) (hw'₁ 0) (hd₂ 0)
      hw0z (hdet 0)
  · have hw0nz : w 0 ≠ 0 := hw0z
    rcases hnonempty with ⟨z₀, hz₀⟩
    have hφz₀ : signedLineFunc e w z₀ < 0 := hside z₀ hz₀
    -- (A): ψₖ(z₀) → φ(z₀) < 0
    have hA : Tendsto (fun k => signedLineFunc (eₖ k) (w' k) z₀) atTop
        (𝓝 (signedLineFunc e w z₀)) :=
      signedLineFunc_tendsto_base_dir z₀ heₖe hww
    have hA_ev : ∀ᶠ k in atTop, signedLineFunc (eₖ k) (w' k) z₀ < 0 := by
      have hε : 0 < -(signedLineFunc e w z₀) / 2 := by linarith
      have hclose : ∀ᶠ k in atTop,
          |signedLineFunc (eₖ k) (w' k) z₀ - signedLineFunc e w z₀|
            < -(signedLineFunc e w z₀) / 2 := by
        exact (Metric.tendsto_nhds.mp hA) (-(signedLineFunc e w z₀) / 2) hε
      filter_upwards [hclose] with k hk
      have hlo : signedLineFunc (eₖ k) (w' k) z₀ - signedLineFunc e w z₀
          < -(signedLineFunc e w z₀) / 2 := (abs_lt.mp hk).2
      have hhalf : signedLineFunc e w z₀ / 2 < 0 := by linarith
      linarith
    -- (B): eventually ψₖ(e) > 0 (robust H-B)
    have hB_ev : ∀ᶠ k in atTop, 0 < signedLineFunc (eₖ k) (w' k) e :=
      boundary_value_pos_eventually_robust hf ha heS hq₀S hq₀U hq₀e hw₀₁ hd₀₀
        hw₁ hpar₀ heₖS hq₂S hq₂U hq₂e hw'₁ hd₂ hφeₖ hdet hww hw0nz
    have hboth : ∀ᶠ k in atTop,
        signedLineFunc (eₖ k) (w' k) z₀ < 0 ∧ 0 < signedLineFunc (eₖ k) (w' k) e :=
      hA_ev.and hB_ev
    rcases (eventually_atTop.mp hboth) with ⟨N, hN⟩
    have hNok : signedLineFunc (eₖ N) (w' N) z₀ < 0 ∧ 0 < signedLineFunc (eₖ N) (w' N) e :=
      hN N le_rfl
    -- R2 at eₖ N (robust same-side product)
    have hprod_pos : 0 < signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e :=
      same_side_product_robust hf ha (e := e) heS hq₀S hq₀U hq₀e hw₀₁ hd₀₀
        hw₁ hpar₀ (eₖ := eₖ N) (heₖS N) (q₂ := q₂ N) (hq₂S N) (hq₂U N) (hq₂e N)
        (w' := w' N) (hw'₁ N) (hd₂ N) (p := p) heClosure (z₀ := z₀) hz₀
        (ne_of_lt (hφeₖ N)) (hdet N)
    have hprod_neg : signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e < 0 :=
      mul_neg_of_neg_of_pos hNok.1 hNok.2
    linarith


/-- **Depth-0 nearly-parallel contradiction, reference-robust mirror
(T2r′)**: the mirror of `depth_zero_robust_contradiction`: hypotheses
identical except the family directions converge to `-w` (`hwwm`).  Then
`ψₖ(z₀) → signedLineFunc e (-w) z₀ = -φ_w(z₀) > 0` (eventually positive)
while robust H-B′ gives eventually `ψₖ(e) < 0`; R2 (`same_side_product
_robust`) demands `ψₖ(z₀)·ψₖ(e) > 0` — contradiction. -/
theorem depth_zero_robust_contradiction_mirror {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior) (heₖe : Tendsto eₖ atTop (𝓝 e))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k)))
    {w' : ℕ → ℝ²} (hw'₁ : ∀ k, ‖w' k‖ = 1)
    (hd₂ : ∀ k, Tendsto (fun m => unitKernelDir f (q₂ k m)) atTop (𝓝 (w' k)))
    (hdet : ∀ k, det2 w (w' k) ≠ 0)
    (hwwm : Tendsto w' atTop (𝓝 (-w))) :
    False := by
  by_cases hw0z : w 0 = 0
  · exact vertical_cluster_dir_contradiction_robust hf ha heS hq₀S hq₀U hq₀e
      hw₀₁ hd₀₀ hw₁ hpar₀ (heₖS 0) (hq₂S 0) (hq₂U 0) (hq₂e 0) (hw'₁ 0) (hd₂ 0)
      hw0z (hdet 0)
  · have hw0nz : w 0 ≠ 0 := hw0z
    rcases hnonempty with ⟨z₀, hz₀⟩
    have hφz₀ : signedLineFunc e w z₀ < 0 := hside z₀ hz₀
    -- (A): ψₖ(z₀) → signedLineFunc e (-w) z₀ = -φ(z₀) > 0
    have hA : Tendsto (fun k => signedLineFunc (eₖ k) (w' k) z₀) atTop
        (𝓝 (signedLineFunc e (-w) z₀)) :=
      signedLineFunc_tendsto_base_dir z₀ heₖe hwwm
    have hA0 : Tendsto (fun k => signedLineFunc (eₖ k) (w' k) z₀) atTop
        (𝓝 (-(signedLineFunc e w z₀))) := by
      simpa [signedLineFunc_neg] using hA
    have hA_ev : ∀ᶠ k in atTop, 0 < signedLineFunc (eₖ k) (w' k) z₀ := by
      have hε : 0 < (-(signedLineFunc e w z₀)) / 2 := by linarith
      have hclose : ∀ᶠ k in atTop,
          |signedLineFunc (eₖ k) (w' k) z₀ - (-(signedLineFunc e w z₀))|
            < (-(signedLineFunc e w z₀)) / 2 := by
        exact (Metric.tendsto_nhds.mp hA0) (-(signedLineFunc e w z₀) / 2) hε
      filter_upwards [hclose] with k hk
      have hgt : -( (signedLineFunc e w z₀)) / 2 < signedLineFunc (eₖ k) (w' k) z₀ := by
        have h1 := abs_lt.mp hk
        have : -( (-(signedLineFunc e w z₀)) / 2) <
            signedLineFunc (eₖ k) (w' k) z₀ - (-(signedLineFunc e w z₀)) := h1.1
        linarith
      have hL : -(signedLineFunc e w z₀) - (-(signedLineFunc e w z₀)) / 2 > 0 := by linarith
      linarith
    -- (B′): eventually ψₖ(e) < 0 (robust H-B′)
    have hB_ev : ∀ᶠ k in atTop, signedLineFunc (eₖ k) (w' k) e < 0 :=
      boundary_value_neg_eventually_robust hf ha heS hq₀S hq₀U hq₀e hw₀₁ hd₀₀
        hw₁ hpar₀ heₖS hq₂S hq₂U hq₂e hw'₁ hd₂ hφeₖ hdet hwwm hw0nz
    have hboth : ∀ᶠ k in atTop,
        0 < signedLineFunc (eₖ k) (w' k) z₀ ∧ signedLineFunc (eₖ k) (w' k) e < 0 :=
      hA_ev.and hB_ev
    rcases (eventually_atTop.mp hboth) with ⟨N, hN⟩
    have hNok : 0 < signedLineFunc (eₖ N) (w' N) z₀ ∧ signedLineFunc (eₖ N) (w' N) e < 0 :=
      hN N le_rfl
    -- R2 at eₖ N (robust same-side product)
    have hprod_pos : 0 < signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e :=
      same_side_product_robust hf ha (e := e) heS hq₀S hq₀U hq₀e hw₀₁ hd₀₀
        hw₁ hpar₀ (eₖ := eₖ N) (heₖS N) (q₂ := q₂ N) (hq₂S N) (hq₂U N) (hq₂e N)
        (w' := w' N) (hw'₁ N) (hd₂ N) (p := p) heClosure (z₀ := z₀) hz₀
        (ne_of_lt (hφeₖ N)) (hdet N)
    have hprod_neg : signedLineFunc (eₖ N) (w' N) z₀ * signedLineFunc (eₖ N) (w' N) e < 0 :=
      mul_neg_of_pos_of_neg hNok.1 hNok.2
    linarith


/-- **Sign-relation transitivity**: if `u = ±v` and `v = ±w` then
`u = ±w`.  Used to relate the extracted family limit `wstar = ±w₀` to the
bookkeeping base `w = ±w₀`. -/
lemma sign_trans {u v w : ℝ²} (huv : u = v ∨ u = -v) (hvw : v = w ∨ v = -w) :
    u = w ∨ u = -w := by
  rcases huv with huv | huv <;> rcases hvw with hvw | hvw
  · left
    exact huv.trans hvw
  · right
    exact huv.trans hvw
  · right
    calc
      u = -v := huv
      _ = -w := by rw [hvw]
  · left
    calc
      u = -v := huv
      _ = -(-w) := by rw [hvw]
      _ = w := by simp


/-- **Off-line sequence contradiction, reference-robust (depth-0 close-out,
robust)**: the `off_line_sequence_contradiction` statement with the
reference direction decoupled: `q₀` has its own unit limit `w₀`, and the
bookkeeping base `w` (all `φ`-data, `hside`, `hφeₖ`) satisfies
`w = w₀ ∨ w = -w₀` (`hpar₀`).  This covers BOTH orientations of the
reference relative to the side-pinned base, so the flat component may lie
on either side of the reference direction.  Regime C calls
`depth_zero_robust_contradiction` or its mirror according to whether the
extracted `wstar` equals `w` or `-w` (`sign_trans`); regime A is
reference-free and unchanged. -/
theorem off_line_sequence_contradiction_robust {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {p : ℝ²} (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    {eₖ : ℕ → ℝ²} (heₖS : ∀ k, eₖ k ∈ stripInterior) (heₖe : Tendsto eₖ atTop (𝓝 e))
    (hφeₖ : ∀ k, signedLineFunc e w (eₖ k) < 0)
    {q₂ : ℕ → ℕ → ℝ²} (hq₂S : ∀ k m, q₂ k m ∈ stripInterior)
    (hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0)
    (hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (eₖ k))) :
    False := by
  rcases off_line_direction_data hf ha heS hq₀S hq₀U hq₀e hw₀₁ hd₀₀ heₖe
    hq₂S hq₂U hq₂e with ⟨W, hW₁, γ, hγ, hve, hdW, φ, hφmono, wstar, hwstar, hpar₂, hφw⟩
  have hpar₀' : w₀ = w ∨ w₀ = -w := by
    rcases hpar₀ with hp | hp
    · left
      exact hp.symm
    · right
      have hw' : -w = w₀ := by
        rw [hp]
        simp
      exact hw'.symm
  have hws : wstar = w ∨ wstar = -w := sign_trans hpar₂ hpar₀'
  by_cases hC : ∀ᶠ m in atTop, det2 w₀ (W (φ m)) ≠ 0
  · -- regime C: shifted tail, apply robust T2 or its mirror
    rcases (eventually_atTop.mp hC) with ⟨N, hN⟩
    have hshift : StrictMono (fun m : ℕ => m + N) := by
      intro a b hab
      change a + N < b + N
      omega
    let e' : ℕ → ℝ² := fun m => eₖ (φ (m + N))
    let q2' : ℕ → ℕ → ℝ² := fun m n => q₂ (φ (m + N)) (γ (φ (m + N)) n)
    let w' : ℕ → ℝ² := fun m => W (φ (m + N))
    have heₖS' : ∀ m, e' m ∈ stripInterior := by
      intro m
      exact heₖS (φ (m + N))
    have heₖe' : Tendsto e' atTop (𝓝 e) := by
      have h1 : Tendsto (fun m => eₖ (φ (m + N))) atTop (𝓝 e) :=
        (heₖe.comp hφmono.tendsto_atTop).comp hshift.tendsto_atTop
      simpa [e'] using h1
    have hφeₖ' : ∀ m, signedLineFunc e w (e' m) < 0 := by
      intro m
      exact hφeₖ (φ (m + N))
    have hq₂S' : ∀ m n, q2' m n ∈ stripInterior := by
      intro m n
      exact hq₂S (φ (m + N)) (γ (φ (m + N)) n)
    have hq₂U' : ∀ m n, dN f (q2' m n) ≠ 0 := by
      intro m n
      exact hq₂U (φ (m + N)) (γ (φ (m + N)) n)
    have hq₂e' : ∀ m, Tendsto (q2' m) atTop (𝓝 (e' m)) := by
      intro m
      have h := hve (φ (m + N))
      simpa [q2', e'] using h
    have hw'₁ : ∀ m, ‖w' m‖ = 1 := by
      intro m
      exact hW₁ (φ (m + N))
    have hd₂' : ∀ m, Tendsto (fun n => unitKernelDir f (q2' m n)) atTop (𝓝 (w' m)) := by
      intro m
      have h := hdW (φ (m + N))
      simpa [q2', w'] using h
    have hdet' : ∀ m, det2 w (w' m) ≠ 0 := by
      intro m
      have hN' : det2 w₀ (W (φ (m + N))) ≠ 0 := hN (m + N) (by omega)
      rcases hpar₀ with hp | hp
      · simpa [w', hp] using hN'
      · have hw₀w : w₀ = -w := by rw [hp]; simp
        have hrel' : det2 w (w' m) = -det2 w₀ (w' m) := by
          dsimp [w']
          rw [hw₀w]
          simp [det2]
          ring
        rw [hrel']
        intro hz
        exact hN' (by linarith)
    have hww' : Tendsto w' atTop (𝓝 wstar) := by
      have h1 : Tendsto (fun m => W (φ (m + N))) atTop (𝓝 wstar) :=
        hφw.comp hshift.tendsto_atTop
      simpa [w'] using h1
    rcases hws with hws_p | hws_n
    · exact depth_zero_robust_contradiction hf ha (e := e) heS
        hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ (p := p) heClosure hnonempty hside
        (eₖ := e') heₖS' heₖe' hφeₖ' (q₂ := q2') hq₂S' hq₂U' hq₂e'
        (w' := w') hw'₁ hd₂' hdet' (by simpa [hws_p] using hww')
    · exact depth_zero_robust_contradiction_mirror hf ha (e := e) heS
        hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ (p := p) heClosure hnonempty hside
        (eₖ := e') heₖS' heₖe' hφeₖ' (q₂ := q2') hq₂S' hq₂U' hq₂e'
        (w' := w') hw'₁ hd₂' hdet' (by simpa [hws_n] using hww')
  · -- regime A: infinitely many exact-parallel directions
    have hnotC : ¬ ∀ᶠ m in atTop, det2 w₀ (W (φ m)) ≠ 0 := hC
    let P : ℕ → Prop := fun m => det2 w₀ (W (φ m)) = 0
    have hinfP : Set.Infinite {m : ℕ | P m} := by
      have h1 : ∃ᶠ m in atTop, ¬ det2 w₀ (W (φ m)) ≠ 0 := Filter.not_eventually.mp hnotC
      have hinf1 : Set.Infinite {m : ℕ | ¬ det2 w₀ (W (φ m)) ≠ 0} :=
        (Nat.frequently_atTop_iff_infinite).1 h1
      have hset : {m : ℕ | ¬ det2 w₀ (W (φ m)) ≠ 0} = {m : ℕ | P m} := by
        ext m
        simp [P]
      rwa [← hset]
    let ρ : ℕ → ℕ := fun n => Nat.nth P n
    have hρmono : StrictMono ρ := Nat.nth_strictMono hinfP
    have hPρ : ∀ n, P (ρ n) := fun n => Nat.nth_mem_of_infinite hinfP n
    let e' : ℕ → ℝ² := fun n => eₖ (φ (ρ n))
    let q2' : ℕ → ℕ → ℝ² := fun n m => q₂ (φ (ρ n)) (γ (φ (ρ n)) m)
    let w' : ℕ → ℝ² := fun n => W (φ (ρ n))
    have hq₂S' : ∀ n m, q2' n m ∈ stripInterior := by
      intro n m
      exact hq₂S (φ (ρ n)) (γ (φ (ρ n)) m)
    have hq₂U' : ∀ n m, dN f (q2' n m) ≠ 0 := by
      intro n m
      exact hq₂U (φ (ρ n)) (γ (φ (ρ n)) m)
    have hq₂e' : ∀ n, Tendsto (q2' n) atTop (𝓝 (e' n)) := by
      intro n
      have h := hve (φ (ρ n))
      simpa [q2', e'] using h
    have hw'₁ : ∀ n, ‖w' n‖ = 1 := by
      intro n
      exact hW₁ (φ (ρ n))
    have hd₂' : ∀ n, Tendsto (fun m => unitKernelDir f (q2' n m)) atTop (𝓝 (w' n)) := by
      intro n
      have h := hdW (φ (ρ n))
      simpa [q2', w'] using h
    have hpar' : ∀ n, w = w' n ∨ w = -w' n := by
      intro n
      have hz : det2 w₀ (W (φ (ρ n))) = 0 := hPρ n
      have hw'n : ‖w' n‖ = 1 := hW₁ (φ (ρ n))
      have hz' : det2 w₀ (w' n) = 0 := by simpa [w'] using hz
      have hpn : w₀ = w' n ∨ w₀ = -w' n :=
        unit_eq_or_neg_of_det2_eq_zero hw₀₁ hw'n hz'
      exact sign_trans hpar₀ hpn
    have hφe' : ∀ n, signedLineFunc e w (e' n) < 0 := by
      intro n
      exact hφeₖ (φ (ρ n))
    have h_e'e : Tendsto (fun n => eₖ (φ (ρ n))) atTop (𝓝 e) :=
      (heₖe.comp hφmono.tendsto_atTop).comp hρmono.tendsto_atTop
    have hφe'0 : Tendsto (fun n => signedLineFunc e w (e' n)) atTop (𝓝 0) := by
      have hφcont : Continuous (fun x : ℝ² => signedLineFunc e w x) := continuous_signedLineFunc e w
      have hφe0 : Tendsto (fun n => signedLineFunc e w (eₖ (φ (ρ n)))) atTop
          (𝓝 (signedLineFunc e w e)) :=
        hφcont.continuousAt.tendsto.comp h_e'e
      have hself : signedLineFunc e w e = 0 := signedLineFunc_self e w
      simpa [e', hself] using hφe0
    exact no_exact_parallel_depth_zero hf ha (e := e) (w := w) (e' := e') (q₂ := q2')
      hq₂S' hq₂U' hq₂e' (w' := w') hw'₁ hd₂' hpar' (p := p) heClosure hnonempty hside
      hφe' hφe'0


/-- **Frontier locally contained in the cluster line (depth-0 close-out)**:
let `e` be a frontier point of the flat component `C = flatComponent f p`
(with `q₀` an approaching `U`-sequence with unit direction limit `w₀`),
and let `w` be the side-pinned base (`w = ±w₀`, `C ⊆ {φ_w < 0}`).  Then
locally near `e` every frontier point of `C` lies on the line `L(e)`
(`φ_w z = 0`): no off-line frontier point can accumulate at `e`.  Proof by
contradiction: an off-line frontier sequence `zₖ → e` (radius
`min ρ₀ (1/(k+1))` with `B(e,ρ₀) ⊆ stripInterior`) has `φ_w(zₖ) < 0`
(frontier ⊆ closure ⊆ `{φ_w ≤ 0}`, off-line) and per-`k` approaching
`U`-families (`exists_U_sequence_to_degenerate` at the degenerate points
`zₖ`); `off_line_sequence_contradiction_robust` then gives `False`. -/
theorem frontier_locally_on_cluster_line {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p))
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ (∀ z ∈ frontier (flatComponent f p), z ∈ Metric.ball e ρ →
      signedLineFunc e w z = 0) := by
  have heClosure : e ∈ closure (flatComponent f p) := by
    rw [frontier] at heF
    exact heF.1
  have hnonempty : (flatComponent f p).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hCempty
    have hecl : e ∈ closure (∅ : Set ℝ²) := by simpa [hCempty] using heClosure
    simpa using hecl
  by_contra hno
  -- hno : ¬ (∃ρ>0, ∀z∈frontier C, z∈ball e ρ → φ_w z = 0)
  have hseq : ∀ ρ : ℝ, 0 < ρ → ∃ z : ℝ²,
      z ∈ frontier (flatComponent f p) ∧ z ∈ Metric.ball e ρ ∧ signedLineFunc e w z ≠ 0 := by
    intro ρ hρ
    by_contra hbad
    apply hno
    refine ⟨ρ, hρ, ?_⟩
    intro z hzF hzball
    by_contra hz0
    exact hbad ⟨z, hzF, hzball, hz0⟩
  -- small ball around e inside the strip
  rcases (Metric.mem_nhds_iff.mp (stripInterior_isOpen.mem_nhds heS)) with ⟨ρ₀, hρ₀, hball₀⟩
  let ρₖ : ℕ → ℝ := fun k => min ρ₀ (((k + 1 : ℕ) : ℝ)⁻¹)
  have hρₖpos : ∀ k, 0 < ρₖ k := by
    intro k
    exact lt_min hρ₀ (by positivity)
  let z : ℕ → ℝ² := fun k => Classical.choose (hseq (ρₖ k) (hρₖpos k))
  have hzF : ∀ k, z k ∈ frontier (flatComponent f p) := fun k =>
    (Classical.choose_spec (hseq (ρₖ k) (hρₖpos k))).1
  have hzball : ∀ k, z k ∈ Metric.ball e (ρₖ k) := fun k =>
    (Classical.choose_spec (hseq (ρₖ k) (hρₖpos k))).2.1
  have hφnz : ∀ k, signedLineFunc e w (z k) ≠ 0 := fun k =>
    (Classical.choose_spec (hseq (ρₖ k) (hρₖpos k))).2.2
  -- z k is in the strip interior
  have hzS : ∀ k, z k ∈ stripInterior := by
    intro k
    have hle : ρₖ k ≤ ρ₀ := min_le_left ρ₀ (((k + 1 : ℕ) : ℝ)⁻¹)
    have hmono : Metric.ball e (ρₖ k) ⊆ Metric.ball e ρ₀ := by
      intro x hx
      rw [Metric.mem_ball] at hx ⊢
      exact lt_of_lt_of_le hx hle
    exact hball₀ (hmono (hzball k))
  -- φ_w(z k) < 0: z k ∈ closure C, C ⊆ {φ_w < 0}, off-line
  have hφlt : ∀ k, signedLineFunc e w (z k) < 0 := by
    intro k
    have hzFk : z k ∈ frontier (flatComponent f p) := hzF k
    rw [frontier] at hzFk
    have hle : signedLineFunc e w (z k) ≤ 0 :=
      closure_lt_le (continuous_signedLineFunc e w) hzFk.1 hside
    exact lt_of_le_of_ne hle (hφnz k)
  -- z k → e
  have hdist : ∀ k, ‖z k - e‖ < ρₖ k := by
    intro k
    have hb : z k ∈ Metric.ball e (ρₖ k) := hzball k
    rw [Metric.mem_ball, dist_eq_norm] at hb
    exact hb
  have heₖe : Tendsto z atTop (𝓝 e) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hrate : ∀ᶠ k : ℕ in atTop, (((k + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := by
      have hz0 := (Metric.tendsto_nhds.mp tendsto_inv_nat_succ_zero) (ε / 2) hε2
      exact hz0.mono (by
        intro k hk
        have h' : |((k + 1 : ℕ) : ℝ)⁻¹| < ε / 2 := by simpa [Real.dist_eq] using hk
        have h'' : ((k + 1 : ℕ) : ℝ)⁻¹ ≤ |((k + 1 : ℕ) : ℝ)⁻¹| := le_abs_self _
        exact lt_of_le_of_lt h'' h')
    rcases (eventually_atTop.mp hrate) with ⟨M, hM⟩
    refine eventually_atTop.2 ⟨M, ?_⟩
    intro k hk
    have hk1 : (((k + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := hM k hk
    have hle : ρₖ k ≤ (((k + 1 : ℕ) : ℝ)⁻¹) := min_le_right ρ₀ (((k + 1 : ℕ) : ℝ)⁻¹)
    have hnorm : ‖z k - e‖ < ε := by
      calc
        ‖z k - e‖ < ρₖ k := hdist k
        _ ≤ (((k + 1 : ℕ) : ℝ)⁻¹) := hle
        _ < ε / 2 := hk1
        _ < ε := by linarith
    simpa [dist_eq_norm] using hnorm
  -- per-k approaching U-sequences at the degenerate frontier points z k
  have hFflat : ∀ k, z k ∈ FlatSet f := fun k =>
    flatComponent_frontier_subset_FlatSet hf (hzS k) (hzF k)
  have hni : ∀ k, ¬ IsFlatInterior f (z k) := fun k =>
    flatComponent_frontier_not_flat_interior (hzS k) (hzF k)
  have hUseq : ∀ k, ∃ r : ℕ → ℝ², (∀ n, r n ∈ stripInterior) ∧
      (∀ n, dN f (r n) ≠ 0) ∧ Tendsto r atTop (𝓝 (z k)) := fun k =>
    exists_U_sequence_to_degenerate hf (hzS k) (hFflat k) (hni k)
  let q₂ : ℕ → ℕ → ℝ² := fun k m => (Classical.choose (hUseq k)) m
  have hq₂S : ∀ k m, q₂ k m ∈ stripInterior := by
    intro k m
    exact (Classical.choose_spec (hUseq k)).1 m
  have hq₂U : ∀ k m, dN f (q₂ k m) ≠ 0 := by
    intro k m
    exact (Classical.choose_spec (hUseq k)).2.1 m
  have hq₂e : ∀ k, Tendsto (q₂ k) atTop (𝓝 (z k)) := by
    intro k
    simpa [q₂] using (Classical.choose_spec (hUseq k)).2.2
  exact off_line_sequence_contradiction_robust hf ha (e := e) heS
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ (p := p) heClosure hnonempty hside
    (eₖ := z) hzS heₖe hφlt (q₂ := q₂) hq₂S hq₂U hq₂e


/-- **Degenerate frontier locally contained in its cluster line**: at a
degenerate frontier point `e` of the flat component `C = flatComponent f p`
(any `e ∈ frontier C ∩ stripInterior`), there is a unit cluster direction
`w` and `ρ > 0` such that every frontier point of `C` within `ρ` of `e`
lies on the cluster line `e + ℝ·w` (`signedLineFunc e w z = 0`).  The
direction is pinned to `C`'s side (so `C ⊆ {φ_w < 0}`), which pins the
reference orientation too via `frontier_locally_on_cluster_line`. -/
theorem degenerate_frontier_contained_in_cluster_line {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p)) :
    ∃ w : ℝ², ∃ ρ : ℝ, ‖w‖ = 1 ∧ 0 < ρ ∧
      (∀ z ∈ frontier (flatComponent f p), z ∈ Metric.ball e ρ →
        signedLineFunc e w z = 0) := by
  -- e is a degenerate flat point
  have heFflat : e ∈ FlatSet f := flatComponent_frontier_subset_FlatSet hf heS heF
  have heni : ¬ IsFlatInterior f e := flatComponent_frontier_not_flat_interior heS heF
  -- any approaching U-sequence, then a convergent direction subsequence
  rcases exists_U_sequence_to_degenerate hf heS heFflat heni with ⟨r, hrS, hrU, hre⟩
  rcases unitDir_subseq_convergent (u := fun n => unitKernelDir f (r n))
    (fun n => norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hrS n) (hrU n))) with
    ⟨w₀, hw₀₁, φ, hφmono, hd₀₀⟩
  let q₀ : ℕ → ℝ² := fun n => r (φ n)
  have hq₀S : ∀ n, q₀ n ∈ stripInterior := fun n => hrS (φ n)
  have hq₀U : ∀ n, dN f (q₀ n) ≠ 0 := fun n => hrU (φ n)
  have hq₀e : Tendsto q₀ atTop (𝓝 e) := hre.comp hφmono.tendsto_atTop
  have hd₀₀' : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀) := by
    dsimp [q₀]
    exact hd₀₀
  -- C lies strictly on one side of the limit line L(e, w₀)
  have hside₀ := flatComponent_one_side_of_cluster_line hf ha (q := q₀) hq₀S hq₀U hq₀e
    (hwnorm := hw₀₁) (hd := hd₀₀') (p := p)
  rcases hside₀ with hpos₀ | hneg₀
  · -- C ⊆ {φ_{w₀} > 0}: use w := -w₀ (side pinned negative; reference anti)
    let w : ℝ² := -w₀
    have hw₁ : ‖w‖ = 1 := by
      simpa [w] using hw₀₁
    have hpar₀ : w = w₀ ∨ w = -w₀ := by
      right
      simp [w]
    have hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0 := by
      intro z hz
      change signedLineFunc e (-w₀) z < 0
      have hn : signedLineFunc e (-w₀) z = -(signedLineFunc e w₀ z) := signedLineFunc_neg e w₀ z
      rw [hn]
      linarith [hpos₀ z hz]
    rcases frontier_locally_on_cluster_line hf ha heS heF hq₀S hq₀U hq₀e hw₀₁ hd₀₀'
      (w := w) hw₁ hpar₀ hside with ⟨ρ, hρ, hconc⟩
    exact ⟨w, ρ, hw₁, hρ, hconc⟩
  · -- C ⊆ {φ_{w₀} < 0}: use w := w₀ directly (reference aligned)
    rcases frontier_locally_on_cluster_line hf ha heS heF hq₀S hq₀U hq₀e hw₀₁ hd₀₀'
      (w := w₀) hw₀₁ (Or.inl rfl) hneg₀ with ⟨ρ, hρ, hconc⟩
    exact ⟨w₀, ρ, hw₀₁, hρ, hconc⟩

end Submission.PaperBand
