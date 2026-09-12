import Submission.Work.UFoliation
import Submission.Work.FlatComponents
import Submission.Work.LeafContinuity
import Submission.PaperBand.KernelUnit
import Submission.PaperBand.KernelSegments

open OptimalMoebius Topology ContDiff
open Filter
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Cluster limits of ruling directions are parallel at every strip-interior point (GREEN)

**New result.**  Let `e` be any point of the strip interior.  Consider two
`U`-sequences `q₁ n → e`, `q₂ n → e` (points where `dN ≠ 0`) whose unit
ruling directions `unitKernelDir f (qᵢ n)` converge to unit limits `w₁`,
`w₂`.  Then `w₁ = w₂` or `w₁ = −w₂` — the two cluster directions are
parallel.

(When `e` itself is a `U`-point this is just continuity of the kernel
direction; the content is at DEGENERATE points `e` — flat but not
flat-interior frontier points of flat components, where no limit direction
is defined by continuity, yet every two approaching ruling families are
asymptotically parallel.)

**Proof (no frontier-regularity hypothesis needed).**  Suppose `w₁ ∦ w₂`.
The ruling LINES `ℓᵢₙ = qᵢₙ + ℝ·vᵢₙ` (`vᵢₙ` the unit ruling direction at
`qᵢₙ`) are each the full kernel line of a `U`-point.  Two such lines
intersect at a point `Pₙ` that tends to `e` (Cramer continuity), so `Pₙ`
lies in the strip interior eventually.  But every strip-interior point of
the ruling LINE of a `U`-point is itself a `U`-point sharing the same
kernel line (`kernel_along_unit_dir_line` +
`unit_dir_parallel_along_line`, which rest on `lineInterior_kernel_and_U`
and `kernel_direction_parallel`): `Pₙ` is a `U`-point whose unit kernel
direction is parallel to both `v₁ₙ` and `v₂ₙ`, forcing `v₁ₙ ∥ v₂ₙ` for all
large `n` — contradicting `vᵢₙ → wᵢ` with `w₁ ∦ w₂`.

Consequences for the flat-frontier analysis (`session_status41`): at every
degenerate frontier point `e` of a flat component, the set of accumulation
directions of bordering U-rulings is contained in a single line — the
uniqueness of the asymptotic ruling direction, previously listed as open
(part of Targets (A0)/(r2) needing the transversality route) — now proved
with NO regularity hypothesis on the frontier at all.

Two-dimensional helper facts (`det2` = the oriented area, "cross product"
of `ℝ²`) are developed first (bilinearity, parallelism iff vanishing, line
intersection formula, continuity of the intersection point).

**Corollary** `degenerateFrontier_ruling_cluster_line` spells out the use:
at a flat-not-flat-interior point `e` (degenerate frontier point of a flat
component), any two convergent-direction subsequences of approaching
`U`-sequences have parallel limit directions — the accumulation directions
of bordering rulings lie in one line.

Lean gotchas recorded while writing this file: coordinates of
`EuclideanSpace ℝ (Fin 2)` vectors print as `.ofLp i`; bilinearity proofs
use full `simp` then `ring` (NOT `simp only [Pi.add_apply]`); `ext i <;>
fin_cases i <;> simp` then `field_simp` works for scalar-multiple proofs;
avoid `Tendsto.div` (its function is the Pi-division application, not
defeally the pointwise lambda) — use the self-contained
`tendsto_div_zero_of_tendsto_zero_ne`; `abs_add` is not a Mathlib name
(use `norm_add_le` + `Real.norm_eq_abs`); `@[simp]` lemmas fire inside
`simpa` goals and can break `simpa ... using h` when the term's type is
not simplified (declare the intermediate type, then `rwa`).
-/

noncomputable section
namespace Submission.PaperBand

/-! ## 1. The 2-dimensional determinant `det2` and parallelism -/

/-- The oriented area (2D cross product) of two plane vectors. -/
def det2 (u v : ℝ²) : ℝ := u 0 * v 1 - u 1 * v 0

/-- `det2 0 v = 0`. -/
@[simp] lemma det2_zero_left (v : ℝ²) : det2 0 v = 0 := by
  unfold det2
  simp

/-- `det2` is zero on a repeated argument. -/
lemma det2_self (u : ℝ²) : det2 u u = 0 := by
  unfold det2
  ring

/-- `det2` is antisymmetric. -/
lemma det2_antisymm (u v : ℝ²) : det2 u v = -det2 v u := by
  unfold det2
  ring

/-- `det2` is additive in the first argument. -/
lemma det2_add_left (a b v : ℝ²) : det2 (a + b) v = det2 a v + det2 b v := by
  unfold det2
  simp
  ring

/-- `det2` is linear in the first argument. -/
lemma det2_smul_left (c : ℝ) (a v : ℝ²) : det2 (c • a) v = c * det2 a v := by
  unfold det2
  simp
  ring

/-- `det2` is linear in the second argument. -/
lemma det2_smul_right (c : ℝ) (a v : ℝ²) : det2 a (c • v) = c * det2 a v := by
  unfold det2
  simp
  ring

/-- `det2` is additive in the first argument with a subtraction. -/
lemma det2_sub_left (a b v : ℝ²) : det2 (a - b) v = det2 a v - det2 b v := by
  unfold det2
  simp
  ring

/-- If the second vector is nonzero and `det2` vanishes then the first
vector is a scalar multiple of the second. -/
lemma exists_smul_of_det2_eq_zero {u v : ℝ²} (hv : v ≠ 0) (h : det2 u v = 0) :
    ∃ c : ℝ, u = c • v := by
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      ext i <;> fin_cases i <;> simp [hv0, h1]
    have hu0 : u 0 = 0 := by
      have hd' : u 0 * v 1 = 0 := by
        unfold det2 at h
        rw [hv0] at h
        linarith
      exact mul_eq_zero.mp hd' |>.resolve_right hv1
    refine ⟨u 1 / v 1, ?_⟩
    ext i <;> fin_cases i <;> simp [hu0, hv0]
    field_simp [hv1]
  · refine ⟨u 0 / v 0, ?_⟩
    ext i <;> fin_cases i <;> simp
    · field_simp [hv0]
    · unfold det2 at h
      have hcross : u 0 * v 1 = u 1 * v 0 := by linarith
      calc
        u 1 = u 0 * v 1 / v 0 := by
          rw [hcross]
          field_simp [hv0]
        _ = (u 0 / v 0) * v 1 := by field_simp [hv0]

/-- Parallel unit vectors are equal or opposite. -/
lemma unit_eq_or_neg_of_det2_eq_zero {u v : ℝ²} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : det2 u v = 0) : u = v ∨ u = -v := by
  have hvn : v ≠ 0 := by
    intro hz
    rw [hz] at hv
    norm_num at hv
  rcases exists_smul_of_det2_eq_zero hvn h with ⟨c, hu_eq⟩
  have hnorm : ‖c • v‖ = 1 := by simpa [hu_eq] using hu
  have hcv : ‖c • v‖ = |c| * ‖v‖ := by
    rw [norm_smul]
    rw [Real.norm_eq_abs]
  have habs : |c| = 1 := by
    rw [hcv] at hnorm
    rw [hv] at hnorm
    have hc1 : |c| * 1 = 1 := hnorm
    simpa using hc1
  by_cases hcpos : 0 ≤ c
  · left
    have hc : c = 1 := by
      have hc' : |c| = c := abs_of_nonneg hcpos
      linarith
    simpa [hc] using hu_eq
  · right
    have hc : c = -1 := by
      have hneg : c < 0 := lt_of_not_ge hcpos
      have hc' : |c| = -c := abs_of_neg hneg
      linarith
    simpa [hc] using hu_eq

/-- Transitivity of parallelism through a nonzero common vector: if
`det2 a u = 0` and `det2 a v = 0` with `a ≠ 0`, then `det2 u v = 0`. -/
lemma det2_eq_zero_of_det2_eq_zero_common {a u v : ℝ²} (ha : a ≠ 0)
    (hau : det2 a u = 0) (hav : det2 a v = 0) : det2 u v = 0 := by
  have hu : ∃ c₁ : ℝ, u = c₁ • a := exists_smul_of_det2_eq_zero ha (by
    rw [det2_antisymm]
    simpa using hau)
  have hv : ∃ c₂ : ℝ, v = c₂ • a := exists_smul_of_det2_eq_zero ha (by
    rw [det2_antisymm]
    simpa using hav)
  rcases hu with ⟨c₁, hu_eq⟩
  rcases hv with ⟨c₂, hv_eq⟩
  rw [hu_eq, hv_eq]
  rw [det2_smul_left, det2_smul_right]
  rw [det2_self]
  ring

/-! ## 2. Intersection of two lines and its continuity -/

/-- The point of the line through `a` in direction `u` given by the Cramer
formula lies on the line through `b` in direction `v` when the directions
are not parallel (`det2 u v ≠ 0`). -/
lemma det2_intersect_on_second {a b u v : ℝ²} (hdet : det2 u v ≠ 0) :
    det2 ((a + (det2 (b - a) v / det2 u v) • u) - b) v = 0 := by
  let t : ℝ := det2 (b - a) v / det2 u v
  let P : ℝ² := a + t • u
  have hP : P - b = (a - b) + t • u := by
    unfold P
    abel
  calc
    det2 (P - b) v = det2 ((a - b) + t • u) v := by rw [hP]
    _ = det2 (a - b) v + det2 (t • u) v := by rw [det2_add_left]
    _ = det2 (a - b) v + t * det2 u v := by rw [det2_smul_left]
    _ = 0 := by
      have hcancel : t * det2 u v = det2 (b - a) v := by
        dsimp [t]
        exact div_mul_cancel₀ (det2 (b - a) v) hdet
      rw [hcancel]
      have hneg : det2 (b - a) v = -det2 (a - b) v := by
        rw [det2_sub_left, det2_sub_left]
        ring
      rw [hneg]
      ring

/-- The `det2` function on pairs is continuous (both coordinates are). -/
lemma continuous_det2 : Continuous (fun p : ℝ² × ℝ² => det2 p.1 p.2) := by
  unfold det2
  fun_prop

lemma tendsto_det2_pair {a b : ℕ → ℝ²} {wa wb : ℝ²} (ha : Tendsto a atTop (𝓝 wa))
    (hb : Tendsto b atTop (𝓝 wb)) :
    Tendsto (fun n => det2 (a n) (b n)) atTop (𝓝 (det2 wa wb)) := by
  have hp : Tendsto (fun n => (a n, b n)) atTop (𝓝 (wa, wb)) := by
    simpa [nhds_prod_eq] using (Tendsto.prodMk ha hb)
  change Tendsto ((fun p : ℝ² × ℝ² => det2 p.1 p.2) ∘ (fun n => (a n, b n)))
    atTop (𝓝 (det2 wa wb))
  exact continuous_det2.continuousAt.tendsto.comp hp


/-- A sequence whose norm tends to `0` tends to `0`. -/
lemma tendsto_zero_of_norm_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {x : ℕ → E} (h : Tendsto (fun n => ‖x n‖) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd := (Metric.tendsto_nhds.mp h) ε hε
  filter_upwards [hd] with n hn
  rw [dist_eq_norm]
  simpa using hn

/-- A sequence `x n` tends to `e` when `‖x n − e‖` tends to `0`. -/
lemma tendsto_nhds_of_norm_sub_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    {x : ℕ → E} {e : E} (h : Tendsto (fun n => ‖x n - e‖) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 e) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd := (Metric.tendsto_nhds.mp h) ε hε
  filter_upwards [hd] with n hn
  rw [dist_eq_norm]
  simpa using hn

/-- A pointwise ratio `f/g` tends to `0` when `f → 0` and `g → L ≠ 0`. -/
lemma tendsto_div_zero_of_tendsto_zero_ne {f g : ℕ → ℝ} {L : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (hg : Tendsto g atTop (𝓝 L)) (hL : L ≠ 0) :
    Tendsto (fun n => f n / g n) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let c : ℝ := |L| / 2
  have hc : 0 < c := by
    dsimp [c]
    exact half_pos (abs_pos.mpr hL)
  have hg_bound : ∀ᶠ n in atTop, c < |g n| := by
    have hclose : ∀ᶠ n in atTop, |g n - L| < c := by
      have hd := (Metric.tendsto_nhds.mp hg) c hc
      filter_upwards [hd] with n hn
      simpa [Real.dist_eq] using hn
    filter_upwards [hclose] with n hn
    have hn' : |g n - L| < |L| / 2 := by simpa [c] using hn
    have htri : |L| ≤ |g n| + |g n - L| := by
      have h := norm_add_le (g n) (L - g n)
      have hsum : g n + (L - g n) = L := by ring
      rw [hsum] at h
      simpa [Real.norm_eq_abs, abs_sub_comm] using h
    have hAbs : 0 ≤ |L| := abs_nonneg L
    dsimp [c]
    linarith
  have hf_abs : Tendsto (fun n => |f n|) atTop (𝓝 0) := by
    have hn := hf.norm
    simpa [Real.norm_eq_abs] using hn
  have hδε : 0 < ε * c := mul_pos hε hc
  have hf_ev : ∀ᶠ n in atTop, |f n| < ε * c := by
    have hd := (Metric.tendsto_nhds.mp hf_abs) (ε * c) hδε
    filter_upwards [hd] with n hn
    simpa [Real.dist_eq] using hn
  filter_upwards [hg_bound, hf_ev] with n hgn hfn
  calc
    |(f n / g n) - 0| = |f n / g n| := by simp
    _ = |f n| / |g n| := by rw [abs_div]
    _ ≤ |f n| / c := by
      exact div_le_div_of_nonneg_left (abs_nonneg (f n)) hc (le_of_lt hgn)
    _ < ε := by
      rw [div_lt_iff₀ hc]
      exact hfn

/-! ## 3. The kernel direction is constant along each ruling line -/

/-- **The unit ruling direction of a `U`-point is a kernel direction at
every strip-interior point of its full line** (and those points are all
`U`-points): the maximal kernel segment of the unit direction covers the
whole strip-interior part of the line. -/
lemma kernel_along_unit_dir_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x z : ℝ²} (hx : x ∈ stripInterior) (hU : dN f x ≠ 0)
    (hz : z ∈ stripInterior) (hline : ∃ s : ℝ, z = x + s • unitKernelDir f x) :
    dN f z ≠ 0 ∧ dN f z (unitKernelDir f x) = 0 := by
  have hV : V2f f x ≠ 0 := V2f_ne_zero_at_U hf ha hx hU
  have hwne : unitKernelDir f x ≠ 0 := unitKernelDir_ne_zero hV
  have hw0 : (unitKernelDir f x) 0 ≠ 0 :=
    kernel_vector_coord0_ne_zero hf ha hx hU (unitKernelDir_mem_ker hf hx) hwne
  have hzline : z ∈ lineInteriorSet x (unitKernelDir f x) := by
    constructor
    · exact hz
    · exact hline
  have hlin := lineInterior_kernel_and_U hf hx hU (unitKernelDir_mem_ker hf hx) hwne hw0
  exact ⟨hlin.1 z hzline, hlin.2 z hzline⟩

/-- **The unit kernel direction at a point of a ruling line is parallel to
the line direction**: if `z` is a strip-interior point of the full kernel
line of the `U`-point `x`, then `unitKernelDir f z` is a scalar multiple of
`unitKernelDir f x` (both are nonzero kernel directions at the `U`-point
`z`, whose kernel is a line). -/
lemma unit_dir_parallel_along_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {x z : ℝ²} (hx : x ∈ stripInterior) (hU : dN f x ≠ 0)
    (hz : z ∈ stripInterior) (hline : ∃ s : ℝ, z = x + s • unitKernelDir f x) :
    ∃ c : ℝ, unitKernelDir f z = c • unitKernelDir f x := by
  have hzU : dN f z ≠ 0 := (kernel_along_unit_dir_line hf ha hx hU hz hline).1
  have hzx : dN f z (unitKernelDir f x) = 0 := (kernel_along_unit_dir_line hf ha hx hU hz hline).2
  have hVx : V2f f x ≠ 0 := V2f_ne_zero_at_U hf ha hx hU
  have hwx : unitKernelDir f x ≠ 0 := unitKernelDir_ne_zero hVx
  exact kernel_direction_parallel hf hz hzU (x := z) (u := unitKernelDir f x)
    hzx (unitKernelDir_mem_ker hf hz) hwx

/-! ## 4. A sequence eventually zero cannot converge to a nonzero limit -/

/-- A sequence of reals that is eventually `0` cannot converge to a nonzero
limit. -/
lemma eventually_zero_not_tendsto_ne {f : ℕ → ℝ} {L : ℝ}
    (hT : Tendsto f atTop (𝓝 L)) (hL : L ≠ 0) (h0 : ∀ᶠ n in atTop, f n = 0) : False := by
  let ε : ℝ := |L| / 2
  have hε : 0 < ε := half_pos (abs_pos.mpr hL)
  have hclose : ∀ᶠ n in atTop, |f n - L| < ε := by
    have hd := (Metric.tendsto_nhds.mp hT) ε hε
    filter_upwards [hd] with n hn
    simpa [Real.dist_eq] using hn
  have hne : ∀ᶠ n in atTop, f n ≠ 0 := by
    filter_upwards [hclose] with n hn
    intro hz
    have hb : |f n - L| = |L| := by
      rw [hz]
      simp
    have hlt : |L| < |L| / 2 := by simpa [hb, ε] using hn
    have hAbs : 0 ≤ |L| := abs_nonneg L
    linarith
  rcases (eventually_atTop.mp (hne.and h0)) with ⟨N, hN⟩
  exact (hN N (Nat.le_refl N)).1 (hN N (Nat.le_refl N)).2

/-! ## 5. Main theorem: cluster ruling directions are parallel -/

/-- **Cluster limits of unit ruling directions at any strip-interior point
are parallel**: if two `U`-sequences approach `e ∈ stripInterior` and their
unit ruling directions converge to `w₁`, `w₂`, then `w₁ = w₂` or
`w₁ = −w₂`. -/
theorem rulingCluster_dirs_parallel {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior)
    {q₁ q₂ : ℕ → ℝ²} {w₁ w₂ : ℝ²}
    (hq₁S : ∀ n, q₁ n ∈ stripInterior) (hq₁U : ∀ n, dN f (q₁ n) ≠ 0)
    (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₁e : Tendsto q₁ atTop (𝓝 e)) (hq₂e : Tendsto q₂ atTop (𝓝 e))
    (hd₁ : Tendsto (fun n => unitKernelDir f (q₁ n)) atTop (𝓝 w₁))
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ n)) atTop (𝓝 w₂)) :
    w₁ = w₂ ∨ w₁ = -w₂ := by
  -- the limits are unit vectors
  have hw₁₁ : ‖w₁‖ = 1 := by
    have htn := hd₁.norm
    have hc : Tendsto (fun n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have heq : (fun n : ℕ => ‖unitKernelDir f (q₁ n)‖) =ᶠ[atTop] fun _ : ℕ => (1 : ℝ) := by
      filter_upwards with n
      exact norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hq₁S n) (hq₁U n))
    have htn' : Tendsto (fun n : ℕ => (1 : ℝ)) atTop (𝓝 ‖w₁‖) := htn.congr' heq
    exact tendsto_nhds_unique htn' hc
  have hw₂₁ : ‖w₂‖ = 1 := by
    have htn := hd₂.norm
    have hc : Tendsto (fun n : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have heq : (fun n : ℕ => ‖unitKernelDir f (q₂ n)‖) =ᶠ[atTop] fun _ : ℕ => (1 : ℝ) := by
      filter_upwards with n
      exact norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hq₂S n) (hq₂U n))
    have htn' : Tendsto (fun n : ℕ => (1 : ℝ)) atTop (𝓝 ‖w₂‖) := htn.congr' heq
    exact tendsto_nhds_unique htn' hc
  by_cases hpar : w₁ = w₂ ∨ w₁ = -w₂
  · exact hpar
  · exfalso
    have hdet_ne : det2 w₁ w₂ ≠ 0 := by
      intro hd
      exact hpar (unit_eq_or_neg_of_det2_eq_zero hw₁₁ hw₂₁ hd)
    -- the numerator, denominator and parameter sequences of the
    -- line-intersection formula
    let num : ℕ → ℝ := fun n => det2 (q₂ n - q₁ n) (unitKernelDir f (q₂ n))
    let den : ℕ → ℝ := fun n => det2 (unitKernelDir f (q₁ n)) (unitKernelDir f (q₂ n))
    let t : ℕ → ℝ := fun n => num n / den n
    -- the intersection point of the two ruling lines
    let P : ℕ → ℝ² := fun n => q₁ n + t n • unitKernelDir f (q₁ n)
    -- den converges to the (nonzero) determinant of the limits
    have hden_tend : Tendsto den atTop (𝓝 (det2 w₁ w₂)) := by
      simpa [den] using tendsto_det2_pair hd₁ hd₂
    -- eventually the denominator is nonzero, so Pₙ really is the
    -- intersection point of the two lines
    have hden_ev_ne : ∀ᶠ n in atTop, den n ≠ 0 := by
      have hnh : {y : ℝ | y ≠ 0} ∈ 𝓝 (det2 w₁ w₂) := isOpen_ne.mem_nhds hdet_ne
      exact hden_tend hnh
    -- Pₙ → e
    have hPe : Tendsto P atTop (𝓝 e) := by
      -- numerator → 0 (q₂ − q₁ → 0)
      have hq₂q₁ : Tendsto (fun n => q₂ n - q₁ n) atTop (𝓝 0) := by
        simpa using hq₂e.sub hq₁e
      have hnum_tend : Tendsto num atTop (𝓝 0) := by
        have ht : Tendsto (fun n => det2 (q₂ n - q₁ n) (unitKernelDir f (q₂ n)))
            atTop (𝓝 (det2 (0 : ℝ²) w₂)) :=
          tendsto_det2_pair (by simpa using hq₂q₁) hd₂
        rwa [det2_zero_left] at ht
      -- tₙ = numₙ / denₙ → 0 (num → 0, den → nonzero limit)
      have ht0 : Tendsto t atTop (𝓝 0) := by
        have hg := tendsto_div_zero_of_tendsto_zero_ne (f := num) (g := den) hnum_tend hden_tend hdet_ne
        simpa [t] using hg
      -- tₙ • v₁ₙ → 0 (tₙ → 0, v₁ₙ bounded with norm 1)
      have htv0 : Tendsto (fun n => t n • unitKernelDir f (q₁ n)) atTop (𝓝 0) := by
        have hnorm0 : Tendsto (fun n => ‖t n • unitKernelDir f (q₁ n)‖) atTop (𝓝 0) := by
          have htabs : Tendsto (fun n => |t n|) atTop (𝓝 0) := by
            have hn := ht0.norm
            simpa [Real.norm_eq_abs] using hn
          have heq : (fun n => ‖t n • unitKernelDir f (q₁ n)‖) =ᶠ[atTop] fun n => |t n| := by
            filter_upwards with n
            rw [norm_smul]
            have hnormv : ‖unitKernelDir f (q₁ n)‖ = 1 :=
              norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hq₁S n) (hq₁U n))
            rw [hnormv]
            rw [Real.norm_eq_abs]
            simp
          simpa using htabs.congr' heq.symm
        exact tendsto_zero_of_norm_tendsto_zero hnorm0
      -- Pₙ − e → 0
      have hPe0 : Tendsto (fun n => P n - e) atTop (𝓝 0) := by
        have hq₁e0 : Tendsto (fun n => q₁ n - e) atTop (𝓝 0) := by
          have hc : Tendsto (fun _ : ℕ => e) atTop (𝓝 e) := tendsto_const_nhds
          simpa using hq₁e.sub hc
        have hadd := hq₁e0.add htv0
        have heq : (fun n => P n - e) = fun n => (q₁ n - e) + t n • unitKernelDir f (q₁ n) := by
          funext n
          unfold P
          abel
        simpa [heq] using hadd
      exact tendsto_nhds_of_norm_sub_tendsto_zero (by
        simpa using hPe0.norm)
    -- Pₙ lies in the strip interior eventually
    have hPstrip : ∀ᶠ n in atTop, P n ∈ stripInterior := by
      rcases Metric.mem_nhds_iff.mp (stripInterior_isOpen.mem_nhds heS) with ⟨δ, hδ, hball⟩
      have hPball : ∀ᶠ n in atTop, P n ∈ Metric.ball e δ := by
        have hd := (Metric.tendsto_nhds.mp hPe) δ hδ
        filter_upwards [hd] with n hn
        rw [Metric.mem_ball]
        simpa using hn
      filter_upwards [hPball] with n hn
      exact hball hn
    -- for every large n (strip-interior Pₙ, nonzero denominator) the two
    -- directions are parallel
    have hev_det : ∀ᶠ n in atTop, det2 (unitKernelDir f (q₁ n)) (unitKernelDir f (q₂ n)) = 0 := by
      filter_upwards [hPstrip, hden_ev_ne] with n hnP hdenn
      -- Pₙ lies on the second line
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
      -- unit kernel direction at Pₙ is parallel to both directions
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
    exact eventually_zero_not_tendsto_ne hden_tend hdet_ne (by
      simpa [den] using hev_det)

/-- **Corollary (unique asymptotic ruling direction at a degenerate
frontier point)**.  Let `e ∈ stripInterior` be a flat, not-flat-interior
point (so in particular a frontier point of a flat component, with `U`-points
dense nearby).  For any two `U`-sequences approaching `e` and any
subsequences of them whose unit ruling directions converge, the two limit
directions are parallel (equal or opposite): the set of accumulation
directions of bordering rulings is contained in a single line.  This is the
"unique cluster ruling direction" content of Target (A0) of the flat-frontier
analysis — obtained with NO regularity hypothesis on the frontier. -/
theorem degenerateFrontier_ruling_cluster_line {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {e : ℝ²} (heS : e ∈ stripInterior) (_heF : e ∈ FlatSet f)
    (_hni : ¬ IsFlatInterior f e)
    {q₁ q₂ : ℕ → ℝ²}
    (hq₁S : ∀ n, q₁ n ∈ stripInterior) (hq₁U : ∀ n, dN f (q₁ n) ≠ 0)
    (hq₂S : ∀ n, q₂ n ∈ stripInterior) (hq₂U : ∀ n, dN f (q₂ n) ≠ 0)
    (hq₁e : Tendsto q₁ atTop (𝓝 e)) (hq₂e : Tendsto q₂ atTop (𝓝 e))
    {φ₁ φ₂ : ℕ → ℕ} {w₁ w₂ : ℝ²}
    (hφ₁ : StrictMono φ₁) (hφ₂ : StrictMono φ₂)
    (hd₁ : Tendsto (fun n => unitKernelDir f (q₁ (φ₁ n))) atTop (𝓝 w₁))
    (hd₂ : Tendsto (fun n => unitKernelDir f (q₂ (φ₂ n))) atTop (𝓝 w₂)) :
    w₁ = w₂ ∨ w₁ = -w₂ := by
  exact rulingCluster_dirs_parallel hf ha heS (q₁ := q₁ ∘ φ₁) (q₂ := q₂ ∘ φ₂)
    (hq₁S := fun n => hq₁S (φ₁ n)) (hq₁U := fun n => hq₁U (φ₁ n))
    (hq₂S := fun n => hq₂S (φ₂ n)) (hq₂U := fun n => hq₂U (φ₂ n))
    (hq₁e := hq₁e.comp hφ₁.tendsto_atTop) (hq₂e := hq₂e.comp hφ₂.tendsto_atTop)
    (hd₁ := hd₁) (hd₂ := hd₂)

end Submission.PaperBand
