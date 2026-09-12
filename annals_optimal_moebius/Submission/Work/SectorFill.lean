import Submission.Work.ClusterLine
import Submission.Work.FlatSides

open OptimalMoebius Topology ContDiff
open Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The flat sector of a degenerate frontier point (Target (r2), part 1)

Let `C = flatComponent f p` and let `e ∈ closure C ∩ stripInterior` be a
degenerate point (flat, not flat-interior, U-points dense near it) with a
side-pinned unit cluster direction `w` (`C ⊆ {φ_w < 0}`, `φ_w x :=
signedLineFunc e w x`) and reference `U`-sequence `q₀ → e` with unit
direction limit `w₀ = ±w`.  The depth-0 close-out
(`degenerate_frontier_contained_in_cluster_line`, ClusterLine §18) says the
frontier of `C` is locally contained in the cluster line `L(e)`.  THIS
file adds the sector side of the (r2) half-disk structure
(`C ∩ B(e,ρ) = {φ_w < 0} ∩ B(e,ρ)`):

* **`no_U_sequence_in_flat_sector`** — no `U`-sequence can approach `e`
  from the flat sector `{φ_w < 0}`: such a sequence, together with its
  CONSTANT per-index `U`-families, satisfies every hypothesis of
  `off_line_sequence_contradiction_robust` (the constant family at a
  `U`-point trivially approaches it with the same unit ruling direction),
  which concludes `False`.
* **`exists_radius_no_U_in_flat_sector`** — contrapositive: a small ball
  around `e` contains no `U`-point strictly in the sector at all;
* **`exists_radius_no_U_in_sector_ball`** — same, with `B(e,ρ)` inside the
  strip interior;
* **`exists_radius_sector_flat_interior`** — sector points are
  flat-INTERIOR (a degenerate flat point in the sector would place
  `U`-points there by `U_dense_near_degenerate_frontier`, contradicting
  the no-U radius; the neighbourhood argument uses the continuity of
  `φ_w` at `x` with the negative margin);
* **`convex_signedLineFunc_lt`** + **`flat_sector_subset_flatComponent`**
  — the sector `B(e,ρ) ∩ {φ_w < 0}` is convex, lies in
  `interior (FlatSet f)` (every point flat-interior), is preconnected and
  meets `C` (via `e ∈ closure C`), hence the whole sector lies in `C`
  (sector filling);
* **`degenerate_frontier_pinned_data`** — the reference/`w₀`/side-pinned
  `w` construction shared with the containment theorem;
* **`degenerate_frontier_half_disk`** — **Target (r2)'s statement**: at a
  degenerate frontier point `e`, `∃w ρ` (unit `w`, `0 < ρ`,
  `B(e,ρ) ⊆ stripInterior`) with `z ∈ C ⟺ signedLineFunc e w z < 0` for
  every `z ∈ B(e,ρ)` — i.e. `C ∩ B(e,ρ) = {φ_w < 0} ∩ B(e,ρ)`, the
  half-disk with the straight frontier through `e` in direction `w` and
  `C` strictly on the `φ_w < 0` side.  Combined with the green depth-0
  frontier containment and `rulingCluster_dirs_parallel` (all approaching
  ruling-direction limits are `±w`), this is the (r2) edge case in full.

Build: `lake build Submission.Work.SectorFill` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- **No `U`-sequence in the flat sector**: let `e` lie in `closure C`
with `C = flatComponent f p` strictly in `{φ_w < 0}`, `q₀` an approaching
`U`-sequence with unit direction limit `w₀ = ±w` (reference), and let
`qₙ → e` be a `U`-sequence with every point in the flat sector
(`φ_w(qₙ) < 0`).  Then `False`: the constant per-index families
`q₂ k m := q k` approach `eₖ := qₖ` with unit ruling direction
`unitKernelDir f (qₖ)`, so `off_line_sequence_contradiction_robust`
applies (regime C needs `det2 w (w'ₖ) ≠ 0` only along an extracted
subsequence; regime A handles exact-parallel terms). -/
theorem no_U_sequence_in_flat_sector {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0)
    {q : ℕ → ℝ²} (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0)
    (hqe : Tendsto q atTop (𝓝 e)) (hφq : ∀ n, signedLineFunc e w (q n) < 0) :
    False := by
  exact off_line_sequence_contradiction_robust hf ha (e := e) heS
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ (p := p) heClosure hnonempty hside
    (eₖ := q) hqS hqe hφq
    (q₂ := fun k m => q k)
    (by intro k m; exact hqS k)
    (by intro k m; exact hqU k)
    (by intro k; exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => q k) atTop (𝓝 (q k))))


/-- **A radius free of `U`-points in the flat sector**: under the data of
`no_U_sequence_in_flat_sector`, there is `ρ > 0` such that every
`U`-point within `ρ` of `e` satisfies `0 ≤ φ_w q` (no `U`-point lies
STRICTLY in the flat sector `{φ_w < 0}` near `e`).  Proof by
contrapositive: points of the sector at radii `1/(k+1)` build a
`U`-sequence in the sector approaching `e`, contradicting
`no_U_sequence_in_flat_sector`. -/
theorem exists_radius_no_U_in_flat_sector {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q : ℝ², q ∈ stripInterior → dN f q ≠ 0 → ‖q - e‖ < ρ →
      0 ≤ signedLineFunc e w q := by
  by_contra hno
  have hseq : ∀ ρ : ℝ, 0 < ρ → ∃ q : ℝ²,
      q ∈ stripInterior ∧ dN f q ≠ 0 ∧ ‖q - e‖ < ρ ∧ signedLineFunc e w q < 0 := by
    intro ρ hρ
    by_contra hbad
    apply hno
    refine ⟨ρ, hρ, ?_⟩
    intro q hqS hqU hqdist
    by_contra hge
    have hlt : signedLineFunc e w q < 0 := lt_of_not_ge hge
    exact hbad ⟨q, hqS, hqU, hqdist, hlt⟩
  let q : ℕ → ℝ² := fun n => Classical.choose (hseq (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity))
  have hqS : ∀ n, q n ∈ stripInterior := fun n =>
    (Classical.choose_spec (hseq (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity))).1
  have hqU : ∀ n, dN f (q n) ≠ 0 := fun n =>
    (Classical.choose_spec (hseq (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity))).2.1
  have hqdist : ∀ n, ‖q n - e‖ < (((n + 1 : ℕ) : ℝ)⁻¹) := fun n =>
    (Classical.choose_spec (hseq (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity))).2.2.1
  have hφq : ∀ n, signedLineFunc e w (q n) < 0 := fun n =>
    (Classical.choose_spec (hseq (((n + 1 : ℕ) : ℝ)⁻¹) (by positivity))).2.2.2
  have hqe : Tendsto q atTop (𝓝 e) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    have hrate : ∀ᶠ n : ℕ in atTop, (((n + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := by
      have hz := (Metric.tendsto_nhds.mp tendsto_inv_nat_succ_zero) (ε / 2) hε2
      exact hz.mono (by
        intro n hn
        have h' : |((n + 1 : ℕ) : ℝ)⁻¹| < ε / 2 := by simpa [Real.dist_eq] using hn
        have h'' : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ |((n + 1 : ℕ) : ℝ)⁻¹| := le_abs_self _
        exact lt_of_le_of_lt h'' h')
    rcases (eventually_atTop.mp hrate) with ⟨M, hM⟩
    refine eventually_atTop.2 ⟨M, ?_⟩
    intro n hn
    have hn1 : (((n + 1 : ℕ) : ℝ)⁻¹) < ε / 2 := hM n hn
    have hnorm : ‖q n - e‖ < ε := by
      calc
        ‖q n - e‖ < (((n + 1 : ℕ) : ℝ)⁻¹) := hqdist n
        _ < ε / 2 := hn1
        _ < ε := by linarith
    simpa [dist_eq_norm] using hnorm
  exact no_U_sequence_in_flat_sector hf ha heS heClosure hnonempty
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ hside hqS hqU hqe hφq


/-- **A radius with no `U`-points in the flat sector, inside the strip**:
combines `exists_radius_no_U_in_flat_sector` with a strip-ball radius: a
single `ρ > 0` with `B(e,ρ) ⊆ stripInterior` and every `U`-point within
`ρ` of `e` satisfies `0 ≤ φ_w q`. -/
theorem exists_radius_no_U_in_sector_ball {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball e ρ ⊆ stripInterior ∧
      ∀ q : ℝ², dN f q ≠ 0 → ‖q - e‖ < ρ → 0 ≤ signedLineFunc e w q := by
  rcases exists_radius_no_U_in_flat_sector hf ha heS heClosure hnonempty
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ hside with ⟨ρU, hρU, hnoU⟩
  rcases (Metric.mem_nhds_iff.mp (stripInterior_isOpen.mem_nhds heS)) with ⟨ρ₀, hρ₀, hball₀⟩
  refine ⟨min ρU ρ₀, lt_min hρU hρ₀, ?_, ?_⟩
  · -- B(e, min ρU ρ₀) ⊆ B(e, ρ₀) ⊆ stripInterior
    intro x hx
    have hle : dist x e < ρ₀ := lt_of_lt_of_le hx (min_le_right ρU ρ₀)
    have hxball₀ : x ∈ Metric.ball e ρ₀ := by
      rw [Metric.mem_ball]
      exact hle
    exact hball₀ hxball₀
  · intro q hqU hqdist
    have hqS : q ∈ stripInterior := by
      have hq₀le : ‖q - e‖ < ρ₀ := lt_of_lt_of_le hqdist (min_le_right ρU ρ₀)
      have hqball₀ : q ∈ Metric.ball e ρ₀ := by
        rw [Metric.mem_ball, dist_eq_norm]
        exact hq₀le
      exact hball₀ hqball₀
    have hqUρ : ‖q - e‖ < ρU := lt_of_lt_of_le hqdist (min_le_left ρU ρ₀)
    exact hnoU q hqS hqU hqUρ

/-- **Sector points are flat-interior**: with the radius of
`exists_radius_no_U_in_sector_ball`, every point of the flat sector
`{φ_w < 0}` within that radius of `e` is flat-INTERIOR (not merely flat):
it is not a `U`-point (no-U radius), and if it were a flat-degenerate
point, `U_dense_near_degenerate_frontier` would put a `U`-point of the
sector inside the radius — contradiction. -/
theorem exists_radius_sector_flat_interior {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball e ρ ⊆ stripInterior ∧
      ∀ x : ℝ², x ∈ Metric.ball e ρ → signedLineFunc e w x < 0 → IsFlatInterior f x := by
  rcases exists_radius_no_U_in_sector_ball hf ha heS heClosure hnonempty
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ hside with ⟨ρ, hρ, hballS, hnoU⟩
  refine ⟨ρ, hρ, hballS, ?_⟩
  intro x hxball hφx
  have hxS : x ∈ stripInterior := hballS hxball
  -- x is flat
  have hxflat : dN f x = 0 := by
    by_contra hx0
    have hxφ : ¬ 0 ≤ signedLineFunc e w x := by
      intro hle
      linarith
    have hxdist : ‖x - e‖ < ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hxball
      exact hxball
    exact hxφ (hnoU x hx0 hxdist)
  -- x is flat-interior
  by_contra hni
  -- U-dense near x would place a U-point of the sector inside the radius
  have hxF : x ∈ FlatSet f := by
    rw [mem_FlatSet]
    exact ⟨hxS, hxflat⟩
  -- radius margin: epsilon-ball around x stays in B(e,ρ) and in {φ_w < 0}
  have hεS : 0 < ρ - ‖x - e‖ := by
    have hxdist : ‖x - e‖ < ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hxball
      exact hxball
    linarith
  have hnegOpen : IsOpen {y : ℝ² | signedLineFunc e w y < 0} :=
    isOpen_lt (continuous_signedLineFunc e w) continuous_const
  have hnh : {y : ℝ² | signedLineFunc e w y < 0} ∈ 𝓝 x := hnegOpen.mem_nhds hφx
  rcases (Metric.mem_nhds_iff.mp hnh) with ⟨δφ, hδφ, hφδ⟩
  let δ : ℝ := min (ρ - ‖x - e‖) δφ
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hεS hδφ
  have hδle : δ ≤ ρ - ‖x - e‖ := min_le_left (ρ - ‖x - e‖) δφ
  have hδleφ : δ ≤ δφ := min_le_right (ρ - ‖x - e‖) δφ
  rcases U_dense_near_degenerate_frontier (a := a) (f := f) hxS hxF hni δ hδ
    with ⟨q, hqballx, hqU⟩
  -- q ∈ ball x δ: inside B(e,ρ) and inside {φ_w < 0}
  have hqdistx : ‖q - x‖ < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hqballx
    exact hqballx
  have hqdist : ‖q - e‖ < ρ := by
    have hnormle : ‖q - e‖ ≤ ‖q - x‖ + ‖x - e‖ := by
      rw [← sub_add_sub_cancel q x e]
      exact norm_add_le _ _
    have hlt₁ : ‖q - x‖ + ‖x - e‖ < (ρ - ‖x - e‖) + ‖x - e‖ := by
      nlinarith [hqdistx, hδle]
    linarith
  have hqφ : ¬ 0 ≤ signedLineFunc e w q := by
    intro hqφle
    have hqφneg : signedLineFunc e w q < 0 := by
      have hmem : q ∈ {y : ℝ² | signedLineFunc e w y < 0} := hφδ (by
        rw [Metric.mem_ball, dist_eq_norm]
        exact lt_of_lt_of_le hqdistx hδleφ)
      simpa using hmem
    linarith
  exact hqφ (hnoU q hqU hqdist)


/-- **The signed-line sublevel set is convex**: for unit-free affine
functional `signedLineFunc e w`, the half-plane `{x | signedLineFunc e w x
< 0}` is convex.  (The functional is affine: value at a convex combination
is the convex combination of values, both negative.) -/
lemma convex_signedLineFunc_lt (e w : ℝ²) : Convex ℝ {x | signedLineFunc e w x < 0} := by
  intro x hx y hy a b ha hb hab
  have hxy : a • (x - e) + b • (y - e) = a • x + b • y - e := by
    calc
      a • (x - e) + b • (y - e) = (a • x - a • e) + (b • y - b • e) := by
        rw [smul_sub, smul_sub]
      _ = (a • x + b • y) - (a • e + b • e) := by abel
      _ = (a • x + b • y) - ((a + b) • e) := by rw [add_smul]
      _ = (a • x + b • y) - e := by rw [hab]; simp
  have hψ : signedLineFunc e w (a • x + b • y) =
      a * signedLineFunc e w x + b * signedLineFunc e w y := by
    rw [signedLineFunc_eq_det2, signedLineFunc_eq_det2, signedLineFunc_eq_det2]
    rw [← hxy]
    rw [det2_add_left, det2_smul_left, det2_smul_left]
  have hψx : signedLineFunc e w x < 0 := by simpa using hx
  have hψy : signedLineFunc e w y < 0 := by simpa using hy
  change signedLineFunc e w (a • x + b • y) < 0
  rw [hψ]
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    rw [ha0, hb1]
    simpa using hψy
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : a * signedLineFunc e w x < 0 := mul_neg_of_pos_of_neg hapos hψx
    have h2 : b * signedLineFunc e w y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hψy)
    linarith

/-- **Flat sector fills the component (sector filling)**: with the data of
`exists_radius_sector_flat_interior` there is `ρ > 0` such that every
point of the flat sector `{φ_w < 0}` within `ρ` of `e` lies in
`C = flatComponent f p`.  Proof: every sector point is flat-interior
(sector lemma); the convex set `S = B(e,ρ) ∩ {φ_w < 0}` is preconnected,
contains a point `z₀ ∈ C` (from `e ∈ closure C`), and lies in
`interior (FlatSet f)`, so `S ⊆` the connected component of `z₀`, which
equals `C`. -/
theorem flat_sector_subset_flatComponent {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heClosure : e ∈ closure (flatComponent f p))
    (hnonempty : (flatComponent f p).Nonempty)
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    (hside : ∀ z ∈ flatComponent f p, signedLineFunc e w z < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball e ρ ⊆ stripInterior ∧
      ∀ x : ℝ², x ∈ Metric.ball e ρ → signedLineFunc e w x < 0 → x ∈ flatComponent f p := by
  rcases exists_radius_sector_flat_interior hf ha heS heClosure hnonempty
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ hside with ⟨ρ, hρ, hballS, hfi⟩
  refine ⟨ρ, hρ, hballS, ?_⟩
  intro x hxball hψx
  have hxS : x ∈ stripInterior := hballS hxball
  have hxfi : IsFlatInterior f x := hfi x hxball hψx
  have hxint : x ∈ interior (FlatSet f) :=
    (IsFlatInterior_iff_mem_interior_FlatSet (f := f) hxS).1 hxfi
  -- a point z₀ of C close to e (e ∈ closure C)
  rcases Metric.mem_closure_iff.mp heClosure ρ hρ with ⟨z₀, hz₀C, hz₀d⟩
  have hz₀ball : z₀ ∈ Metric.ball e ρ := by
    rw [Metric.mem_ball]
    simpa [dist_comm] using hz₀d
  have hz₀ψ : signedLineFunc e w z₀ < 0 := hside z₀ hz₀C
  -- the convex sector S = B(e,ρ) ∩ {φ_w < 0}
  let S : Set ℝ² := {y : ℝ² | y ∈ Metric.ball e ρ ∧ signedLineFunc e w y < 0}
  have hconv : Convex ℝ S := by
    exact (convex_ball (a := e) (r := ρ)).inter (convex_signedLineFunc_lt e w)
  have hxS : x ∈ S := ⟨hxball, hψx⟩
  have hz₀S : z₀ ∈ S := ⟨hz₀ball, hz₀ψ⟩
  have hSsub : S ⊆ interior (FlatSet f) := by
    intro y hy
    have hyS : y ∈ stripInterior := hballS hy.1
    exact (IsFlatInterior_iff_mem_interior_FlatSet (f := f) hyS).1 (hfi y hy.1 hy.2)
  have hpre : IsPreconnected S := hconv.isPreconnected
  have hcc : S ⊆ connectedComponentIn (interior (FlatSet f)) z₀ :=
    IsPreconnected.subset_connectedComponentIn (s := S) (x := z₀) hpre hz₀S hSsub
  have hxz : x ∈ connectedComponentIn (interior (FlatSet f)) z₀ := hcc hxS
  have heq : connectedComponentIn (interior (FlatSet f)) p =
      connectedComponentIn (interior (FlatSet f)) z₀ :=
    connectedComponentIn_eq (F := interior (FlatSet f)) (x := p) (y := z₀)
      (by simpa [flatComponent] using hz₀C)
  simpa [flatComponent, ← heq] using hxz


/-- **Pinned data at a degenerate frontier point**: from `e ∈ frontier C`
(`C = flatComponent f p`) in the strip interior, produce an approaching
`U`-sequence `q₀` with unit direction limit `w₀`, and the side-pinned unit
base `w` (`w = ±w₀`, `C ⊆ {φ_w < 0}`, `φ_w x := signedLineFunc e w x`).
The disjunction of sides w.r.t. `w₀` (`flatComponent_one_side_of_cluster_
line`) is absorbed here, flipping `w₀` if needed. -/
theorem degenerate_frontier_pinned_data {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p)) :
    ∃ q₀ : ℕ → ℝ², (∀ n, q₀ n ∈ stripInterior) ∧ (∀ n, dN f (q₀ n) ≠ 0) ∧
      Tendsto q₀ atTop (𝓝 e) ∧
      ∃ w₀ : ℝ², ‖w₀‖ = 1 ∧
        Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀) ∧
        ∃ w : ℝ², ‖w‖ = 1 ∧ (w = w₀ ∨ w = -w₀) ∧
          (∀ z ∈ flatComponent f p, signedLineFunc e w z < 0) := by
  have heFflat : e ∈ FlatSet f := flatComponent_frontier_subset_FlatSet hf heS heF
  have heni : ¬ IsFlatInterior f e := flatComponent_frontier_not_flat_interior heS heF
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
  have hside₀ := flatComponent_one_side_of_cluster_line hf ha (q := q₀) hq₀S hq₀U hq₀e
    (hwnorm := hw₀₁) (hd := hd₀₀') (p := p)
  rcases hside₀ with hpos₀ | hneg₀
  · -- C ⊆ {φ_{w₀} > 0}: flip to w := -w₀
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
    exact ⟨q₀, hq₀S, hq₀U, hq₀e, w₀, hw₀₁, hd₀₀', w, hw₁, hpar₀, hside⟩
  · -- C ⊆ {φ_{w₀} < 0}: use w := w₀
    exact ⟨q₀, hq₀S, hq₀U, hq₀e, w₀, hw₀₁, hd₀₀', w₀, hw₀₁, Or.inl rfl, hneg₀⟩

/-- **Degenerate frontier half-disk (Target (r2), the half-disk statement)**:
at a degenerate frontier point `e` of the flat component
`C = flatComponent f p`, there is a unit direction `w` and `ρ > 0` such
that, within `B(e,ρ)` (contained in the strip interior), the component is
exactly the flat sector: `z ∈ C ⟺ signedLineFunc e w z < 0`.  Together
with the depth-0 frontier containment (frontier ⊆ `L(e)` locally) this is
the (r2) content: the frontier of `C` near `e` is the straight segment
`L(e) = {φ_w = 0}` with `C` strictly on the `φ_w < 0` side. -/
theorem degenerate_frontier_half_disk {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heF : e ∈ frontier (flatComponent f p)) :
    ∃ w : ℝ², ∃ ρ : ℝ, ‖w‖ = 1 ∧ 0 < ρ ∧ Metric.ball e ρ ⊆ stripInterior ∧
      (∀ z : ℝ², z ∈ Metric.ball e ρ →
        (z ∈ flatComponent f p ↔ signedLineFunc e w z < 0)) := by
  rcases degenerate_frontier_pinned_data hf ha heS heF with
    ⟨q₀, hq₀S, hq₀U, hq₀e, w₀, hw₀₁, hd₀₀, w, hw₁, hpar₀, hside⟩
  have heClosure : e ∈ closure (flatComponent f p) := by
    rw [frontier] at heF
    exact heF.1
  have hnonempty : (flatComponent f p).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hCempty
    have hecl : e ∈ closure (∅ : Set ℝ²) := by simpa [hCempty] using heClosure
    simpa using hecl
  rcases flat_sector_subset_flatComponent hf ha heS heClosure hnonempty
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ hside with ⟨ρ, hρ, hballS, hfill⟩
  refine ⟨w, ρ, hw₁, hρ, hballS, ?_⟩
  intro z hzball
  constructor
  · intro hzC
    exact hside z hzC
  · intro hφz
    exact hfill z hzball hφz

end Submission.PaperBand
