import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2.saddleCollarFoot
import Submission.Work.Drive.N2.windowFrontierRow
import Submission.Work.Drive.N2.windowRows_of_saddleDatum
import Submission.Work.Drive.N2C.saddleCollarRowWide
import Submission.Work.Drive.N2Lead.saddlePinFunction

/-!
# Auxiliary rows of `saddleFlowRowsWide` (salvaged from the refuted first version)

The file `Work.Drive.N2Lead.saddleFlowRowsWide` (the seven flow/pin rows consumed by the core of `D2`)
was first requested **without** the numerical row `c₀ < 99/50`, and the sixth conjunct is FALSE in
that generality (the refutation is recorded in `_sfrw/refute.lean.part` of this directory).  The
*repaired* rows live here, proved on the statement's own hypotheses plus `c₀ < 99/50`:

* `frontier_invariant_eq` — at a frontier point of the model region whose value lies in the band,
  `|Im (Z x)²| = c₀` and `x` is in the model ball and the chart source;
* `eventually_collar_of_frontier` — conjunct 4 (`hcolFr`) of the repaired statement;
* `eventually_landing_of_frontier` — conjunct 7 (`hlandFr`);
* `footFrint_of_c₀_lt` — conjunct 6 (`hfootFrint`), *with* `c₀ < 99/50`.
-/

set_option maxHeartbeats 800000

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

open Set Filter in
/-- **At a frontier point of the model region whose value lies in the band, the invariant
`Im (Z ·)²` is exactly `c₀`** (and the point lies in the model ball, hence in the chart source).

This is the geometric core of the frontier rows: `≤ c₀` comes from the closure of the region and
continuity of `Z`, `≥ c₀` from the fact that the region is *open* and the point is not in it. -/
lemma frontier_invariant_eq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Zs Z : M → ℂ} {lam0 ηb c₀ : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZs : ∀ y : M, Zs y = (D.φ D.j y 0 : ℂ) + (D.φ D.j y 1 : ℂ) * Complex.I)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hηbpos : 0 < ηb) (hηb' : ηb < 1 / 10) (hc₀' : c₀ < 2)
    {x : M} (hxfr : x ∈ frontier
        (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀))
    (hxband : f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb)) :
    x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) ∧
      |((Z x) ^ 2).im| = c₀ ∧ x ∈ (D.φ D.j).source := by
  have hxU : x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) :=
    Work.Drive.N2.wrs_frontierRow (D := D) hlam0pos hlam0 rfl (fun r => rfl) hZs hZrel hZsm hlev
      hηbpos hηb' hc₀' hxfr hxband
  have hxsrc : x ∈ (D.φ D.j).source := hxU.1
  have hZc : ContinuousAt Z x :=
    (hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hxsrc)).continuousAt
  have himc : ContinuousAt (fun y : M => ((Z y) ^ 2).im) x :=
    Complex.continuous_im.continuousAt.comp (hZc.pow 2)
  have hxcl : x ∈ closure
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) :=
    frontier_subset_closure hxfr
  have himle : ((Z x) ^ 2).im ≤ c₀ :=
    Work.Drive.N2.le_of_mem_closure_of_continuousAt
      (s := Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀)
      (u := fun y : M => ((Z y) ^ 2).im) (x := x) (a := c₀) hxcl himc
      (fun y hy => le_of_lt (abs_lt.mp hy.2).2)
  have himge : -c₀ ≤ ((Z x) ^ 2).im := by
    have h := Work.Drive.N2.le_of_mem_closure_of_continuousAt
      (s := Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀)
      (u := fun y : M => -((Z y) ^ 2).im) (x := x) (a := c₀) hxcl himc.neg
      (fun y hy => by have h' := (abs_lt.mp hy.2).1; linarith)
    linarith
  have hxnotint : x ∉ interior
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) := hxfr.2
  have hUopen : IsOpen (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) := by
    have hcont : ContinuousOn (fun y : M => (D.φ D.j y : EuclideanSpace ℝ (Fin 2)))
        (D.φ D.j).source := (D.φ D.j).continuousOn_toFun
    have hpre : IsOpen ((D.φ D.j).source ∩
        (fun y : M => (D.φ D.j y : EuclideanSpace ℝ (Fin 2))) ⁻¹' Metric.ball 0 (D.ρ D.j)) :=
      hcont.isOpen_inter_preimage (D.φ D.j).open_source Metric.isOpen_ball
    have heq : (D.φ D.j).source ∩
        (fun y : M => (D.φ D.j y : EuclideanSpace ℝ (Fin 2))) ⁻¹' Metric.ball 0 (D.ρ D.j)
        = Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) := by
      ext y
      simp [Work.Drive.N2.modelBall, Metric.mem_ball, dist_eq_norm]
    rwa [heq] at hpre
  have hRopen : IsOpen
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) :=
    Work.Drive.N2.isOpen_saddleRegion hUopen (hZsm.mono (fun y hy => hy.1))
  have hxnotR : x ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀ :=
    fun hxR => hxnotint (mem_interior_iff_mem_nhds.mpr (hRopen.mem_nhds hxR))
  have hIm : |((Z x) ^ 2).im| = c₀ := by
    refine le_antisymm (abs_le.mpr ⟨himge, himle⟩) ?_
    by_contra hcon
    exact hxnotR ⟨hxU, not_le.mp hcon⟩
  exact ⟨hxU, hIm, hxsrc⟩

open Set Filter in
/-- **The collar neighbourhood row `hcolFr`** (conjunct 4 of the statement).  Near a frontier point
of the model region whose value is in the band, every band point has its `Z` in the collar: the
invariant of the frontier point is `c₀ ∈ (2 - 2δ, 2)` (`Work.Drive.N2Lead.frontier_invariant_eq`), so
it stays in the collar's imaginary range nearby, and the band gives the real-part bound. -/
theorem eventually_collar_of_frontier {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {Zs Z : M → ℂ} {lam0 ηb δ c₀ : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZs : ∀ y : M, Zs y = (D.φ D.j y 0 : ℂ) + (D.φ D.j y 1 : ℂ) * Complex.I)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hη : 0 < ηb) (hηb' : ηb < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2) :
    ∀ x : M, x ∈ frontier
        (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) →
      f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
      ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
        Z y ∈ Work.Drive.N2.saddleCollar ηb δ := by
  intro x hxfr hxband
  have hηbpos : 0 < ηb := hη
  obtain ⟨hxU, hIm, hxsrc⟩ :=
    frontier_invariant_eq D hlam0pos hlam0 hZrel hZs hZsm hlev hηbpos hηb' hc₀' hxfr hxband
  have hZc : ContinuousAt Z x :=
    (hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hxsrc)).continuousAt
  have himc : ContinuousAt (fun y : M => |((Z y) ^ 2).im|) x :=
    (Complex.continuous_im.continuousAt.comp (hZc.pow 2)).abs
  have h2dx : (2 - 2 * δ : ℝ) < |((Z x) ^ 2).im| := by rw [hIm]; exact hc₀
  have h2x : |((Z x) ^ 2).im| < 2 := by rw [hIm]; exact hc₀'
  have hlo : ∀ᶠ y in 𝓝 x, 2 - 2 * δ < |((Z y) ^ 2).im| :=
    himc.preimage_mem_nhds (isOpen_Ioi.mem_nhds h2dx)
  have hhi : ∀ᶠ y in 𝓝 x, |((Z y) ^ 2).im| < 2 :=
    himc.preimage_mem_nhds (isOpen_Iio.mem_nhds h2x)
  have hsrcy : ∀ᶠ y in 𝓝 x, y ∈ (D.φ D.j).source :=
    (D.φ D.j).open_source.mem_nhds hxsrc
  filter_upwards [hlo, hhi, hsrcy] with y hyl hyh hys hyband
  have h := hlev y hys
  have h2 : lam0 ^ 2 * ((Z y) ^ 2).re = f y - f p := by linarith
  have h3 : |f y - f p| < lam0 ^ 2 * ηb :=
    abs_lt.mpr ⟨by linarith [hyband.1], by linarith [hyband.2]⟩
  have h4 : lam0 ^ 2 * |((Z y) ^ 2).re| < lam0 ^ 2 * ηb := by
    rw [← h2, abs_mul, abs_of_nonneg (sq_nonneg lam0)] at h3
    exact h3
  exact ⟨le_of_lt (lt_of_mul_lt_mul_left h4 (sq_nonneg lam0)), le_of_lt hyl, le_of_lt hyh⟩

open Set Filter in
/-- **The landing neighbourhood row `hlandFr`** (conjunct 7 of the statement): near a frontier point
of the model region whose value is in the band, the foot of every point is on the anchor level.
Namely, near `x` the value stays in the band (continuity of `f` at `x`, from the level law) and the
`Z`-invariant stays in the collar (`Work.Drive.N2Lead.eventually_collar_of_frontier`), so the collar
row `Work.Drive.N2C.saddleCollarRowWide` applies at `y`. -/
theorem eventually_landing_of_frontier {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    {Zs Z : M → ℂ} {lam0 ηs ηb δ c₀ : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZs : ∀ y : M, Zs y = (D.φ D.j y 0 : ℂ) + (D.φ D.j y 1 : ℂ) * Complex.I)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hlevSs : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult lam0 (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((1 : ℝ) * D.φ D.j (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult lam0 (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((-1 : ℝ) * D.φ D.j (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    (hη : 0 < ηs) (hη' : ηs < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hηb : ηs < ηb) (hηb' : ηb < 1 / 10) (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2) :
    ∀ x : M, x ∈ frontier
        (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) →
      f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
      ∀ᶠ y in 𝓝 x,
        f (Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) y) = f p - lam0 ^ 2 * ηs := by
  intro x hxfr hxband
  have hηbpos : 0 < ηb := lt_trans hη hηb
  obtain ⟨hxU, hIm, hxsrc⟩ :=
    frontier_invariant_eq D hlam0pos hlam0 hZrel hZs hZsm hlev hηbpos hηb' hc₀' hxfr hxband
  -- `f` is continuous at `x` (level law + continuity of `Z`)
  have hZc : ContinuousAt Z x :=
    (hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hxsrc)).continuousAt
  have hfcont : ContinuousAt f x := by
    have h1 : ContinuousAt (fun y : M => f p + lam0 ^ 2 * ((Z y) ^ 2).re) x :=
      ContinuousAt.add continuousAt_const
        ((Complex.continuous_re.continuousAt.comp (hZc.pow 2)).const_mul (lam0 ^ 2))
    refine h1.congr ?_
    filter_upwards [(D.φ D.j).open_source.mem_nhds hxsrc] with y hy
    exact (hlev y hy).symm
  have hband' : ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) :=
    hfcont.preimage_mem_nhds (isOpen_Ioo.mem_nhds hxband)
  have hcoll := eventually_collar_of_frontier D hlam0pos hlam0 hZrel hZs hZsm hlev
    hηbpos hηb' hδ hδ' hc₀ hc₀' x hxfr hxband
  have hsrcy : ∀ᶠ y in 𝓝 x, y ∈ (D.φ D.j).source :=
    (D.φ D.j).open_source.mem_nhds hxsrc
  filter_upwards [hband', hcoll, hsrcy] with y hyband hcolly hys
  have hrow := Work.Drive.N2C.saddleCollarRowWide (η := ηs) (δ := δ) (ηb := ηb)
    D hsgn (D.φ D.j) Zs Z lam0 hlam0 rfl (fun r => rfl) hZs hZrel hlevSs hODE him
    hη hη' hδ hδ' hηb' (le_of_lt hηb) hys
    (hcolly hyband : Z y ∈ Work.Drive.N2C.saddleCollarWide ηb δ)
  exact hrow.2.1

open Set Filter in
/-- **The sixth conjunct with the missing hypothesis restored.**  With `c₀ < 99/50` added, the
frontier-footing row of `Work.Drive.N2Lead.saddleFlowRowsWide` is a theorem on the statement's own
hypotheses (the collar row is derived internally by `Work.Drive.N2C.saddleCollarRowWide`).

At a frontier point `x` of the model region with `f x` in the band one has `x ∈ modelBall`
(`Work.Drive.N2.wrs_frontierRow`), `|Im (Z x)²| = c₀` (`≤ c₀` on the closure of the region by
continuity, `≥ c₀` off the open region) and `|Re (Z x)²| ≤ ηb` (level law + band), so `Z x` lies in
the collar; the collar row gives `Z (foot x) = saddlePsi ηs δ (Z x)`, whose square is `-ηs + c₀ I`.
Hence `|Im (Z (foot x))²| = c₀ < 99/50` and `‖Z (foot x)‖² ≤ ηs + c₀ < 4`, and
`Work.Drive.N2Lead.pinTheta_eventuallyEq_one` puts a whole neighbourhood of `foot x` inside
`θ ⁻¹' {1}`. -/
theorem footFrint_of_c₀_lt {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    (hsgn : D.s₁ D.j = - D.s₂ D.j)
    {Zs Z : M → ℂ} {lam0 ηs ηb δ c₀ : ℝ}
    (hlam0pos : 0 < lam0) (hlam0 : lam0 = D.ρ D.j / 8)
    (hZrel : ∀ y : M, Zs y = (lam0 : ℂ) * Z y)
    (hZs : ∀ y : M, Zs y = (D.φ D.j y 0 : ℂ) + (D.φ D.j y 1 : ℂ) * Complex.I)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z (D.φ D.j).source)
    (hlev : ∀ y ∈ (D.φ D.j).source, f y = f p + lam0 ^ 2 * ((Z y) ^ 2).re)
    (hlevSs : ∀ y ∈ (D.φ D.j).source, f y = f p + ((Zs y) ^ 2).re)
    (hODE : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult lam0 (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((1 : ℝ) * D.φ D.j (D.Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => D.φ D.j (D.Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult lam0 (‖D.φ D.j (D.Φ (t, y))‖ ^ 2)
          * ((-1 : ℝ) * D.φ D.j (D.Φ (t, y)) 1)) t)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C D.j) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    (hη : 0 < ηs) (hη' : ηs < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hηb : ηs < ηb) (hηb' : ηb < 1 / 10) (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2)
    (hc₀m : c₀ < 99 / 50) :
    ∀ x : M, x ∈ frontier
        (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) →
      f x ∈ Set.Ioo (f p - lam0 ^ 2 * ηb) (f p + lam0 ^ 2 * ηb) →
      Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x
        ∈ interior ((Work.Drive.N2Lead.pinTheta D Z (99 / 50)) ⁻¹' {1}) := by
  intro x hxfr hxband
  have hc₀pos : 0 < c₀ := by linarith
  have hηbpos : 0 < ηb := lt_trans hη hηb
  -- ## the frontier point is in the model ball
  have hxU : x ∈ Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) :=
    Work.Drive.N2.wrs_frontierRow (D := D) hlam0pos hlam0 rfl (fun r => rfl) hZs hZrel hZsm hlev
      hηbpos hηb' hc₀' hxfr hxband
  have hxsrc : x ∈ (D.φ D.j).source := hxU.1
  -- ## continuity of `Z` and of the coordinates of `Z²` at `x`
  have hZc : ContinuousAt Z x :=
    (hZsm.contMDiffAt ((D.φ D.j).open_source.mem_nhds hxsrc)).continuousAt
  have himc : ContinuousAt (fun y : M => ((Z y) ^ 2).im) x :=
    Complex.continuous_im.continuousAt.comp (hZc.pow 2)
  have hrec : ContinuousAt (fun y : M => ((Z y) ^ 2).re) x :=
    Complex.continuous_re.continuousAt.comp (hZc.pow 2)
  -- ## `|Im (Z x)²| = c₀`
  have hxcl : x ∈ closure
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) :=
    frontier_subset_closure hxfr
  have hxnotint : x ∉ interior
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) := hxfr.2
  have himle : ((Z x) ^ 2).im ≤ c₀ :=
    Work.Drive.N2.le_of_mem_closure_of_continuousAt
      (s := Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀)
      (u := fun y : M => ((Z y) ^ 2).im) (x := x) (a := c₀) hxcl himc
      (fun y hy => le_of_lt (abs_lt.mp hy.2).2)
  have himge : -c₀ ≤ ((Z x) ^ 2).im := by
    have h := Work.Drive.N2.le_of_mem_closure_of_continuousAt
      (s := Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀)
      (u := fun y : M => -((Z y) ^ 2).im) (x := x) (a := c₀) hxcl himc.neg
      (fun y hy => by have h' := (abs_lt.mp hy.2).1; linarith)
    linarith
  have hUopen : IsOpen (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) := by
    have hcont : ContinuousOn (fun y : M => (D.φ D.j y : EuclideanSpace ℝ (Fin 2)))
        (D.φ D.j).source := (D.φ D.j).continuousOn_toFun
    have hpre : IsOpen ((D.φ D.j).source ∩
        (fun y : M => (D.φ D.j y : EuclideanSpace ℝ (Fin 2))) ⁻¹' Metric.ball 0 (D.ρ D.j)) :=
      hcont.isOpen_inter_preimage (D.φ D.j).open_source Metric.isOpen_ball
    have heq : (D.φ D.j).source ∩
        (fun y : M => (D.φ D.j y : EuclideanSpace ℝ (Fin 2))) ⁻¹' Metric.ball 0 (D.ρ D.j)
        = Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j) := by
      ext y
      simp [Work.Drive.N2.modelBall, Metric.mem_ball, dist_eq_norm]
    rwa [heq] at hpre
  have hRopen : IsOpen
      (Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀) :=
    Work.Drive.N2.isOpen_saddleRegion hUopen (hZsm.mono (fun y hy => hy.1))
  have hxnotR : x ∉ Work.Drive.N2.saddleRegion (Work.Drive.N2.modelBall (D.φ D.j) (D.ρ D.j)) Z c₀ :=
    fun hxR => hxnotint (mem_interior_iff_mem_nhds.mpr (hRopen.mem_nhds hxR))
  have hIm : |((Z x) ^ 2).im| = c₀ := by
    refine le_antisymm (abs_le.mpr ⟨himge, himle⟩) ?_
    by_contra hcon
    exact hxnotR ⟨hxU, not_le.mp hcon⟩
  -- ## `|Re (Z x)²| ≤ ηb`
  have hreabs : |((Z x) ^ 2).re| ≤ ηb := by
    have h := hlev x hxsrc
    have h2 : lam0 ^ 2 * ((Z x) ^ 2).re = f x - f p := by linarith
    have h3 : |f x - f p| < lam0 ^ 2 * ηb :=
      abs_lt.mpr ⟨by linarith [hxband.1], by linarith [hxband.2]⟩
    rw [← h2, abs_mul, abs_of_nonneg (sq_nonneg lam0)] at h3
    exact le_of_lt (lt_of_mul_lt_mul_left h3 (sq_nonneg lam0))
  -- ## the collar row at `x`
  have hxcollar : Z x ∈ Work.Drive.N2.saddleCollar ηb δ :=
    ⟨hreabs, by rw [hIm]; linarith, by rw [hIm]; linarith⟩
  have hrow := Work.Drive.N2C.saddleCollarRowWide (η := ηs) (δ := δ) (ηb := ηb)
    D hsgn (D.φ D.j) Zs Z lam0 hlam0 rfl (fun r => rfl) hZs hZrel hlevSs hODE him
    hη hη' hδ hδ' hηb' (le_of_lt hηb) hxsrc
    (hxcollar : Z x ∈ Work.Drive.N2C.saddleCollarWide ηb δ)
  obtain ⟨hfootsrc, -, hseamx⟩ := hrow
  -- ## the invariant of the foot
  have hcol := Work.Drive.N2C.saddlePsi_collarWide (η := ηs) (δ := δ) (ηb := ηb)
    hη hη' hδ hδ' hηb' (z := Z x) hreabs (by rw [hIm]; linarith) (by rw [hIm]; linarith)
  have hfootsq : ((Z (D.Φ (f p - lam0 ^ 2 * ηs - f x, x))) ^ 2)
      = (-(ηs : ℝ) : ℂ) + (((Z x) ^ 2).im : ℂ) * Complex.I := by
    rw [hseamx]
    exact hcol.1
  have hfootim : ((Z (D.Φ (f p - lam0 ^ 2 * ηs - f x, x))) ^ 2).im = ((Z x) ^ 2).im := by
    rw [hfootsq]
    simp
  -- ## the two strict bounds at the foot
  have hlt1 : |((Z (D.Φ (f p - lam0 ^ 2 * ηs - f x, x))) ^ 2).im| < 99 / 50 := by
    rw [hfootim, hIm]; exact hc₀m
  have hlt2 : ‖Z (D.Φ (f p - lam0 ^ 2 * ηs - f x, x))‖ ^ 2 < 4 := by
    have h1 : ‖(Z (D.Φ (f p - lam0 ^ 2 * ηs - f x, x))) ^ 2‖
        = ‖Z (D.Φ (f p - lam0 ^ 2 * ηs - f x, x))‖ ^ 2 := norm_pow _ 2
    rw [← h1, hfootsq]
    have h2 : ‖(-(ηs : ℝ) : ℂ) + (((Z x) ^ 2).im : ℂ) * Complex.I‖ ≤ ηs + c₀ := by
      refine (norm_add_le _ _).trans ?_
      have h4 : ‖(-(ηs : ℝ) : ℂ)‖ = ηs := by
        rw [norm_neg]; simp [abs_of_nonneg hη.le]
      have h3 : ‖(((Z x) ^ 2).im : ℂ) * Complex.I‖ = |((Z x) ^ 2).im| := by simp
      rw [h4, h3, hIm]
    linarith [h2, hη', hc₀']
  -- ## the pin
  have hfooteq : Work.Drive.N2.footMap D.Φ f (f p - lam0 ^ 2 * ηs) x
      = D.Φ (f p - lam0 ^ 2 * ηs - f x, x) := rfl
  have hev := Work.Drive.N2Lead.pinTheta_eventuallyEq_one D (Z := Z) (m := 99 / 50)
    (by norm_num) hZsm hfootsrc hlt1 hlt2
  rw [hfooteq]
  refine mem_interior_iff_mem_nhds.mpr ?_
  filter_upwards [hev] with y hy
  exact hy

end Work.Drive.N2Lead
