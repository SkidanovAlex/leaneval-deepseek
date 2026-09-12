import Submission.Work.UHeightAccum
import Submission.Work.UMatchDirection
import Submission.PaperBand.KernelUnit
import Submission.Work.FrontierCluster
import Submission.Commons.Geometry.PlaneVector.slope_unit_coord0_lower
import Submission.Commons.Analysis.Sequences.tendsto_of_unique_subseq_limit

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Brick (C) of the degenerate-flat-height route: slope convergence

GREEN — **`uBendSlope_tendsto_of_height_tendsto` is PROVED** (zero `sorry`):
a sequence of U-heights converging to any `y₀` gives a convergent sequence
of leaf slopes, and the limit is independent of the sequence (so the two
one-sided limits from brick (B) agree at an uncovered degenerate height).

**Statement (brick C).**  Let `yₙ` be a sequence of U-heights converging to
`y₀` (`yₙ ∈ UHeight a f`, `yₙ → y₀`).  Then the slopes of the canonical
U-leaves through the centreline points `(1/2, yₙ)` converge:

    ∃ m₀ : ℝ, Tendsto (fun n => uBendSlope … (1/2, yₙ) …) atTop (𝓝 m₀)

and the limit `m₀` is independent of the sequence (so the two one-sided
limits from brick (B) agree at an uncovered degenerate height).

**Available input (all green).**
* `FrontierCluster.rulingCluster_dirs_parallel` — for TWO U-sequences
  `q₁ₙ, q₂ₙ → e ∈ stripInterior` with convergent unit ruling directions
  `unitKernelDir f (qᵢₙ) → wᵢ`: `w₁ = w₂ ∨ w₁ = −w₂` (all cluster
  directions lie in one unoriented line);
* `DegenerateLeaf.uBend_abs_disp_bound` (via `uBendSlope_eq_disp`) — the
  leaf slope is bounded: `|Δ| ≤ C := (a²−1)/(2a)` at every U-point;
* `DegenerateLeaf.uBendDispCoeff_nonneg` — `0 ≤ C` (from the same bound);
* `KernelUnit.unitKernelDir` (unit kernel direction), and
  `uBendSlope_eq_unitKernelDir_ratio` (this file): `Δ = v₁/v₀`,
  `v := unitKernelDir f x`, so a bound on `Δ` gives a uniform lower bound
  `|v₀| ≥ 1/√(1+C²)` on the direction's first coordinate
  (`slope_unit_coord0_lower`, delegated to the fleet);
* the centreline map `y ↦ (1/2, y)` is continuous
  (`LeafContinuity.continuousAt_centrePoint`).

**Proof skeleton (main theorem).**
1. `qₙ := centrePoint (y n)`: a U-sequence with `qₙ → e := centrePoint y₀`
   (`centrePoint_tendsto` below).
2. `vₙ := unitKernelDir f qₙ` (unit, `|vₙ₀| ≥ c₀ := 1/√(1+C²)` by the
   ratio equality + the slope bound), and the slope `Δₙ = vₙ₁/vₙ₀` is
   bounded by `C`.
3. Unique cluster slope: take any two convergent subsequences of `Δₙ`
   with limits `m₁,m₂`.  Extract further unit-direction sub-subsequences
   `vₙ → w₁,w₂` (`tendsto_subseq_of_bounded`, unit circle compact);
   `|wᵢ₀| ≥ c₀ > 0`.  By `rulingCluster_dirs_parallel`, `w₁ = ±w₂`, so
   the ratios `mᵢ = wᵢ₁/wᵢ₀` agree: `m₁ = m₂`.
4. Boundedness of `Δₙ` gives at least one convergent subsequence (limit
   `m₀`); step 3 shows every convergent subsequence converges to `m₀`;
   `Commons.Analysis.Sequences.tendsto_of_unique_subseq_limit` (delegated)
   finishes: `Δₙ → m₀`.
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-- **The leaf slope equals the ratio of the unit kernel direction
coordinates** at a U-point: with `v := unitKernelDir f x` (a unit vector
in the kernel line), `uBendSlope = v₁ / v₀`. -/
lemma uBendSlope_eq_unitKernelDir_ratio {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    uBendSlope hf ha hx hdN =
      (unitKernelDir f x) 1 / (unitKernelDir f x) 0 := by
  have hw₀ : (uBendDirPos hf ha hx hdN) 0 ≠ 0 := uBendDirPos_coord_ne_zero hf ha hx hdN
  have hkerw : dN f x (uBendDirPos hf ha hx hdN) = 0 := (uBendDirPos_spec hf ha hx hdN).1
  have hwne : uBendDirPos hf ha hx hdN ≠ 0 := (uBendDirPos_spec hf ha hx hdN).2.1
  have hV2 : V2f f x ≠ 0 := V2f_ne_zero_at_U hf ha hx hdN
  have hkeru : dN f x (unitKernelDir f x) = 0 := unitKernelDir_mem_ker hf hx
  have hun0 : unitKernelDir f x ≠ 0 := unitKernelDir_ne_zero hV2
  rcases kernel_direction_parallel hf hx hdN hkerw hkeru hwne with ⟨c, hc⟩
  have hcne : c ≠ 0 := by
    intro hc0
    have : unitKernelDir f x = 0 := by
      calc
        unitKernelDir f x = c • uBendDirPos hf ha hx hdN := hc
        _ = 0 := by simp [hc0]
    exact hun0 this
  calc
    uBendSlope hf ha hx hdN =
        (uBendDirPos hf ha hx hdN) 1 / (uBendDirPos hf ha hx hdN) 0 := by
      rfl
    _ = (c • uBendDirPos hf ha hx hdN) 1 / (c • uBendDirPos hf ha hx hdN) 0 := by
      simp [smul_eq_mul]
      field_simp [hcne, hw₀]
    _ = (unitKernelDir f x) 1 / (unitKernelDir f x) 0 := by
      rw [← hc]

/-- **Uniform slope bound at a U-point**: `|Δ| ≤ C := (a²−1)/(2a)` where
`Δ = uBendSlope` is the horizontal displacement of the canonical U-leaf. -/
lemma uBendSlope_abs_bound {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x : ℝ²} (hx : x ∈ stripInterior) (hdN : dN f x ≠ 0) :
    |uBendSlope hf ha hx hdN| ≤ (a ^ 2 - 1) / (2 * a) := by
  rw [uBendSlope_eq_disp hf ha hx hdN]
  exact uBend_abs_disp_bound hf ha hx hdN

/-- The centreline points of a converging height sequence converge:
`(1/2, yₙ) → (1/2, y₀)` when `yₙ → y₀`. -/
lemma centrePoint_tendsto {y : ℕ → ℝ} {y₀ : ℝ} (hyy₀ : Tendsto y atTop (𝓝 y₀)) :
    Tendsto (fun n : ℕ => centrePoint (y n)) atTop (𝓝 (centrePoint y₀)) := by
  exact (continuousAt_centrePoint y₀).tendsto.comp hyy₀


/-- **Uniform slope bound at a U-HEIGHT**: for `y ∈ UHeight a f`, the slope
of the canonical leaf through `(1/2, y)` is bounded by `C = (a²−1)/(2a)`. -/
lemma uBendSlope_abs_bound_UHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy : y ∈ UHeight a f) :
    |uBendSlope hf ha (centrePoint_mem_stripInterior y)
        ((mem_UHeight (a := a) (f := f)).mp hy)| ≤ (a ^ 2 - 1) / (2 * a) := by
  exact uBendSlope_abs_bound hf ha (centrePoint_mem_stripInterior y)
    ((mem_UHeight (a := a) (f := f)).mp hy)

/-- **The displacement coefficient is nonnegative at a U-height**: any
`y ∈ UHeight a f` gives `0 ≤ (a²−1)/(2a)`. -/
lemma uBendDispCoeff_nonneg_UHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy : y ∈ UHeight a f) :
    0 ≤ (a ^ 2 - 1) / (2 * a) := by
  exact uBendDispCoeff_nonneg hf ha (centrePoint_mem_stripInterior y)
    ((mem_UHeight (a := a) (f := f)).mp hy)

/-! ## Generic helpers (used by the brick (C) proof, all green) -/

/-- The range of a sequence of unit vectors is bounded. -/
lemma isBounded_range_unit {v : ℕ → EuclideanSpace ℝ (Fin 2)}
    (hv : ∀ n, ‖v n‖ = 1) : Bornology.IsBounded (Set.range v) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  intro z hz
  rcases hz with ⟨n, rfl⟩
  rw [hv n]

/-- The coordinate ratio of a convergent vector sequence converges to the
ratio of the coordinates of its limit (denominators nonzero). -/
lemma tendsto_coord_ratio {v : ℕ → EuclideanSpace ℝ (Fin 2)} {w : EuclideanSpace ℝ (Fin 2)}
    (hv : Tendsto v atTop (𝓝 w)) (hw0 : w 0 ≠ 0) (hv0 : ∀ n, (v n) 0 ≠ 0) :
    Tendsto (fun n : ℕ => (v n) 1 / (v n) 0) atTop (𝓝 (w 1 / w 0)) := by
  have hc1 : ContinuousAt (fun z : EuclideanSpace ℝ (Fin 2) => z 1) w := by fun_prop
  have hc0 : ContinuousAt (fun z : EuclideanSpace ℝ (Fin 2) => z 0) w := by fun_prop
  have h1 : Tendsto (fun n : ℕ => (v n) 1) atTop (𝓝 (w 1)) := (hc1.tendsto.comp hv)
  have h0 : Tendsto (fun n : ℕ => (v n) 0) atTop (𝓝 (w 0)) := (hc0.tendsto.comp hv)
  exact h1.div h0 hw0

/-- **Uniform lower bound on the unit kernel direction's first coordinate
at a U-HEIGHT**: with `C := (a²−1)/(2a) ≥ 0`, the unit kernel direction
`v := unitKernelDir f (1/2,y)` at a U-height satisfies
`1/√(1+C²) ≤ |v₀|` (the leaf is uniformly far from vertical because its
slope is bounded by `C`).  Uses the fleet-proved
`Commons.Geometry.PlaneVector.slope_unit_coord0_lower`. -/
lemma unitKernelDir_coord0_lower_UHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy : y ∈ UHeight a f) :
    1 / Real.sqrt (1 + ((a ^ 2 - 1) / (2 * a)) ^ 2) ≤
      |(unitKernelDir f (centrePoint y)) 0| := by
  let x : ℝ² := centrePoint y
  have hx : x ∈ stripInterior := by dsimp [x]; exact centrePoint_mem_stripInterior y
  have hdN : dN f x ≠ 0 := by dsimp [x]; exact (mem_UHeight (a := a) (f := f)).mp hy
  let C : ℝ := (a ^ 2 - 1) / (2 * a)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact uBendDispCoeff_nonneg hf ha hx hdN
  have hV : V2f f x ≠ 0 := V2f_ne_zero_at_U hf ha hx hdN
  have hv0 : (unitKernelDir f x) 0 ≠ 0 :=
    kernel_vector_coord0_ne_zero hf ha hx hdN (unitKernelDir_mem_ker hf hx)
      (unitKernelDir_ne_zero hV)
  have hunit : ‖unitKernelDir f x‖ = 1 := norm_unitKernelDir hV
  have hratio : |(unitKernelDir f x) 1 / (unitKernelDir f x) 0| ≤ C := by
    have hr : uBendSlope hf ha hx hdN = (unitKernelDir f x) 1 / (unitKernelDir f x) 0 :=
      uBendSlope_eq_unitKernelDir_ratio hf ha hx hdN
    have hb := uBendSlope_abs_bound hf ha hx hdN
    dsimp [C] at hb ⊢
    rwa [hr] at hb
  have hl := Commons.Geometry.PlaneVector.slope_unit_coord0_lower (C := C) hC hv0 hunit hratio
  dsimp [C, x] at hl ⊢
  exact hl

noncomputable def slopeAtHeight {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y : ℝ} (hy : y ∈ UHeight a f) : ℝ :=
  uBendSlope hf ha (centrePoint_mem_stripInterior y) ((mem_UHeight (a := a) (f := f)).mp hy)

/-- The unit kernel direction at the centreline point of height `y`. -/
noncomputable def unitDirAtHeight (f : ℝ² → ℝ³) (y : ℝ) : ℝ² :=
  unitKernelDir f (centrePoint y)

/-!
## Brick (C) — PROVED (zero sorry)

`uBendSlope_tendsto_of_height_tendsto`: a sequence of U-heights
`yₙ → y₀` gives a convergent sequence of leaf slopes
`slopeAtHeight hf ha (hyU n) → m₀`.  Proof sketch (details in the body):
the centreline points `qₙ := (1/2, yₙ)` form a U-sequence tending to
`e := (1/2,y₀)`; with `vₙ := unitKernelDir f qₙ` and `Δₙ :=
slopeAtHeight …`, `Δₙ = vₙ₁/vₙ₀` (ratio lemma) and `|Δₙ| ≤ C`
(`C := (a²−1)/(2a) ≥ 0`), so `|vₙ₀| ≥ c₀ := 1/√(1+C²)` (fleet
`Commons.Geometry.PlaneVector.slope_unit_coord0_lower`).  Two convergent
subsequences of `Δₙ` have the same limit: extract unit-direction
sub-subsequence limits `w₁,w₂` (unit circle compactness via
`tendsto_subseq_of_bounded`); `FrontierCluster.rulingCluster_dirs_parallel`
gives `w₁ = ±w₂`; the ratio is invariant under `±`, and the ratio
continuity lemma gives `Lᵢ = wᵢ₁/wᵢ₀`.  `Δₙ` is bounded, has a convergent
subsequence (limit `m₀`), every convergent subsequence converges to
`m₀`, and the fleet `Commons.Analysis.Sequences.tendsto_of_unique_subseq_limit`
concludes `Δₙ → m₀`.
-/

/-- **Brick (C)**: a sequence of U-heights converging to any `y₀` gives a
convergent sequence of leaf slopes. -/
theorem uBendSlope_tendsto_of_height_tendsto {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {y₀ : ℝ} {y : ℕ → ℝ}
    (hyU : ∀ n : ℕ, y n ∈ UHeight a f) (hyy₀ : Tendsto y atTop (𝓝 y₀)) :
    ∃ m₀ : ℝ, Tendsto (fun n : ℕ => slopeAtHeight hf ha (hyU n)) atTop (𝓝 m₀) := by
  let e : ℝ² := centrePoint y₀
  let q : ℕ → ℝ² := fun n => centrePoint (y n)
  let v : ℕ → ℝ² := fun n => unitDirAtHeight f (y n)
  let Δ : ℕ → ℝ := fun n => slopeAtHeight hf ha (hyU n)
  let C : ℝ := (a ^ 2 - 1) / (2 * a)
  have hqS : ∀ n : ℕ, q n ∈ stripInterior := by
    intro n
    dsimp [q]
    exact centrePoint_mem_stripInterior (y n)
  have hqU : ∀ n : ℕ, dN f (q n) ≠ 0 := by
    intro n
    dsimp [q]
    exact (mem_UHeight (a := a) (f := f)).mp (hyU n)
  have hqe : Tendsto q atTop (𝓝 e) := by
    dsimp [q, e]
    exact centrePoint_tendsto hyy₀
  have heS : e ∈ stripInterior := by
    dsimp [e]
    exact centrePoint_mem_stripInterior y₀
  have hvdef : ∀ n : ℕ, v n = unitKernelDir f (q n) := by
    intro n
    dsimp [v, q, unitDirAtHeight]
  have hΔdef : ∀ n : ℕ, Δ n = slopeAtHeight hf ha (hyU n) := by
    intro n
    rfl
  have hΔratio : ∀ n : ℕ, Δ n = (v n) 1 / (v n) 0 := by
    intro n
    rw [hΔdef n, hvdef n]
    dsimp [slopeAtHeight]
    exact uBendSlope_eq_unitKernelDir_ratio hf ha (hqS n) (hqU n)
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact uBendDispCoeff_nonneg_UHeight hf ha (hyU 0)
  have hΔbdd : ∀ n : ℕ, |Δ n| ≤ C := by
    intro n
    dsimp [Δ, C, slopeAtHeight]
    exact uBendSlope_abs_bound_UHeight hf ha (hyU n)
  have hvunit : ∀ n : ℕ, ‖v n‖ = 1 := by
    intro n
    rw [hvdef n]
    have hV : V2f f (q n) ≠ 0 := V2f_ne_zero_at_U hf ha (hqS n) (hqU n)
    exact norm_unitKernelDir hV
  let c₀ : ℝ := 1 / Real.sqrt (1 + C ^ 2)
  have hv₀lb : ∀ n : ℕ, c₀ ≤ |(v n) 0| := by
    intro n
    have hlb := unitKernelDir_coord0_lower_UHeight hf ha (hyU n)
    dsimp [c₀, C, v, unitDirAtHeight, q] at hlb ⊢
    exact hlb
  have hc₀pos : 0 < c₀ := by
    dsimp [c₀]
    have hsq : 0 < Real.sqrt (1 + C ^ 2) := Real.sqrt_pos.2 (by nlinarith [sq_nonneg C])
    exact div_pos (by norm_num) hsq
  have hv0nz : ∀ n : ℕ, (v n) 0 ≠ 0 := by
    intro n
    exact (abs_pos.mp (lt_of_lt_of_le hc₀pos (hv₀lb n)))
  have hΔbounded : Bornology.IsBounded (Set.range Δ) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C, ?_⟩
    intro z hz
    rcases hz with ⟨n, rfl⟩
    have h := hΔbdd n
    rwa [Real.norm_eq_abs]
  -- uniqueness core
  have hcore : ∀ (φ₁ φ₂ : ℕ → ℕ), StrictMono φ₁ → StrictMono φ₂ →
      ∀ L₁ L₂ : ℝ, Tendsto (Δ ∘ φ₁) atTop (𝓝 L₁) → Tendsto (Δ ∘ φ₂) atTop (𝓝 L₂) →
        L₁ = L₂ := by
    intro φ₁ φ₂ hφ₁ hφ₂ L₁ L₂ hL₁ hL₂
    have hvb₁ : Bornology.IsBounded (Set.range (v ∘ φ₁)) := by
      exact isBounded_range_unit (v := v ∘ φ₁) (fun n => hvunit (φ₁ n))
    rcases tendsto_subseq_of_bounded hvb₁ (x := v ∘ φ₁) (fun n => Set.mem_range_self n) with
      ⟨w₁, _hw₁cl, ψ₁, hψ₁, hvw₁⟩
    have hvb₂ : Bornology.IsBounded (Set.range (v ∘ φ₂)) := by
      exact isBounded_range_unit (v := v ∘ φ₂) (fun n => hvunit (φ₂ n))
    rcases tendsto_subseq_of_bounded hvb₂ (x := v ∘ φ₂) (fun n => Set.mem_range_self n) with
      ⟨w₂, _hw₂cl, ψ₂, hψ₂, hvw₂⟩
    -- |w₁0| ≥ c₀, unit, w₁0 ≠ 0
    have hw₁₀lb : c₀ ≤ |w₁ 0| := by
      have hc0 : ContinuousAt (fun z : ℝ² => |z 0|) w₁ := by
        fun_prop
      have ht : Tendsto (fun n : ℕ => |((v ∘ φ₁ ∘ ψ₁) n) 0|) atTop (𝓝 |w₁ 0|) :=
        (hc0.tendsto.comp hvw₁)
      have hpt : ∀ n : ℕ, c₀ ≤ |((v ∘ φ₁ ∘ ψ₁) n) 0| := by
        intro n
        exact hv₀lb (φ₁ (ψ₁ n))
      exact ge_of_tendsto ht (Filter.Eventually.of_forall hpt)
    have hw₁₁ : ‖w₁‖ = 1 := by
      have htn : Tendsto (fun n : ℕ => ‖((v ∘ φ₁ ∘ ψ₁) n)‖) atTop (𝓝 ‖w₁‖) := hvw₁.norm
      have heq : (fun n : ℕ => ‖((v ∘ φ₁ ∘ ψ₁) n)‖) =ᶠ[atTop] fun _ : ℕ => (1 : ℝ) := by
        filter_upwards with n
        exact hvunit (φ₁ (ψ₁ n))
      have htn' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 ‖w₁‖) := htn.congr' heq
      exact tendsto_nhds_unique htn' tendsto_const_nhds
    have hw₁₀nz : w₁ 0 ≠ 0 := by
      exact (abs_pos.mp (lt_of_lt_of_le hc₀pos hw₁₀lb))
    -- L₁ = ratio of w₁
    have hL₁w : L₁ = w₁ 1 / w₁ 0 := by
      have hΔ₁ : Tendsto (Δ ∘ φ₁ ∘ ψ₁) atTop (𝓝 L₁) := hL₁.comp hψ₁.tendsto_atTop
      have heq : (fun n : ℕ => Δ ((φ₁ ∘ ψ₁) n)) =ᶠ[atTop]
          fun n : ℕ => (((v ∘ φ₁ ∘ ψ₁) n) 1) / (((v ∘ φ₁ ∘ ψ₁) n) 0) := by
        filter_upwards with n
        exact hΔratio ((φ₁ ∘ ψ₁) n)
      have hΔ₁' : Tendsto (fun n : ℕ => (((v ∘ φ₁ ∘ ψ₁) n) 1) / (((v ∘ φ₁ ∘ ψ₁) n) 0))
          atTop (𝓝 L₁) := hΔ₁.congr' heq
      have hr₁ : Tendsto (fun n : ℕ => (((v ∘ φ₁ ∘ ψ₁) n) 1) / (((v ∘ φ₁ ∘ ψ₁) n) 0))
          atTop (𝓝 (w₁ 1 / w₁ 0)) :=
        tendsto_coord_ratio hvw₁ hw₁₀nz (by intro n; exact hv0nz (φ₁ (ψ₁ n)))
      exact tendsto_nhds_unique hΔ₁' hr₁
    -- mirror for w₂
    have hw₂₀lb : c₀ ≤ |w₂ 0| := by
      have hc0 : ContinuousAt (fun z : ℝ² => |z 0|) w₂ := by
        fun_prop
      have ht : Tendsto (fun n : ℕ => |((v ∘ φ₂ ∘ ψ₂) n) 0|) atTop (𝓝 |w₂ 0|) :=
        (hc0.tendsto.comp hvw₂)
      have hpt : ∀ n : ℕ, c₀ ≤ |((v ∘ φ₂ ∘ ψ₂) n) 0| := by
        intro n
        exact hv₀lb (φ₂ (ψ₂ n))
      exact ge_of_tendsto ht (Filter.Eventually.of_forall hpt)
    have hw₂₀nz : w₂ 0 ≠ 0 := by
      exact (abs_pos.mp (lt_of_lt_of_le hc₀pos hw₂₀lb))
    have hL₂w : L₂ = w₂ 1 / w₂ 0 := by
      have hΔ₂ : Tendsto (Δ ∘ φ₂ ∘ ψ₂) atTop (𝓝 L₂) := hL₂.comp hψ₂.tendsto_atTop
      have heq : (fun n : ℕ => Δ ((φ₂ ∘ ψ₂) n)) =ᶠ[atTop]
          fun n : ℕ => (((v ∘ φ₂ ∘ ψ₂) n) 1) / (((v ∘ φ₂ ∘ ψ₂) n) 0) := by
        filter_upwards with n
        exact hΔratio ((φ₂ ∘ ψ₂) n)
      have hΔ₂' : Tendsto (fun n : ℕ => (((v ∘ φ₂ ∘ ψ₂) n) 1) / (((v ∘ φ₂ ∘ ψ₂) n) 0))
          atTop (𝓝 L₂) := hΔ₂.congr' heq
      have hr₂ : Tendsto (fun n : ℕ => (((v ∘ φ₂ ∘ ψ₂) n) 1) / (((v ∘ φ₂ ∘ ψ₂) n) 0))
          atTop (𝓝 (w₂ 1 / w₂ 0)) :=
        tendsto_coord_ratio hvw₂ hw₂₀nz (by intro n; exact hv0nz (φ₂ (ψ₂ n)))
      exact tendsto_nhds_unique hΔ₂' hr₂
    -- cluster directions are parallel
    have hpar : w₁ = w₂ ∨ w₁ = -w₂ := by
      exact rulingCluster_dirs_parallel hf ha heS
        (q₁ := q ∘ φ₁ ∘ ψ₁) (q₂ := q ∘ φ₂ ∘ ψ₂)
        (hq₁S := fun n => hqS (φ₁ (ψ₁ n))) (hq₁U := fun n => hqU (φ₁ (ψ₁ n)))
        (hq₂S := fun n => hqS (φ₂ (ψ₂ n))) (hq₂U := fun n => hqU (φ₂ (ψ₂ n)))
        (hq₁e := hqe.comp (hφ₁.tendsto_atTop.comp hψ₁.tendsto_atTop))
        (hq₂e := hqe.comp (hφ₂.tendsto_atTop.comp hψ₂.tendsto_atTop))
        (hd₁ := hvw₁) (hd₂ := hvw₂)
    have hratio_eq : w₁ 1 / w₁ 0 = w₂ 1 / w₂ 0 := by
      rcases hpar with hpar | hpar
      · rw [hpar]
      · have hw : w₁ = -w₂ := hpar
        calc
          w₁ 1 / w₁ 0 = (-w₂) 1 / (-w₂) 0 := by rw [hw]
          _ = w₂ 1 / w₂ 0 := by
            simp
    calc
      L₁ = w₁ 1 / w₁ 0 := hL₁w
      _ = w₂ 1 / w₂ 0 := hratio_eq
      _ = L₂ := hL₂w.symm
  -- existence + application
  rcases tendsto_subseq_of_bounded hΔbounded (x := Δ) (fun n => Set.mem_range_self n) with
    ⟨L₀, _hL₀cl, ψ₀, hψ₀, hΔψ₀⟩
  have huniq : ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ L' : ℝ, Tendsto (Δ ∘ φ) atTop (𝓝 L') → L' = L₀ := by
    intro φ hφ L' hL'
    exact (hcore φ ψ₀ hφ hψ₀ L' L₀ hL' hΔψ₀)
  have hΔlim : Tendsto Δ atTop (𝓝 L₀) :=
    Commons.Analysis.Sequences.tendsto_of_unique_subseq_limit (u := Δ) (L := L₀) hΔbounded huniq
  refine ⟨L₀, ?_⟩
  simpa [Δ, slopeAtHeight] using hΔlim

end Submission
