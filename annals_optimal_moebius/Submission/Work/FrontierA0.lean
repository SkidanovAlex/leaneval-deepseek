import Submission.Work.SectorFill

open OptimalMoebius Topology ContDiff
open Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# Target (A0) in the straight-frontier world (FrontierA0)

session_status41 Addendum 2's Target (A0) said: given (r1) `e` a
degenerate frontier point of `C = flatComponent f p`, (r2) local
half-plane regularity with a `C¹` `φ` (`C ∩ B(e,ρ) = {φ < 0} ∩ B(e,ρ)`),
and (r3) a bordering `U`-sequence, every cluster limit of the unit ruling
directions is parallel (up to sign) to the frontier tangent `T`.

SectorFill (session 46) proved the half-plane regularity in the STRONGEST
possible form: the frontier is STRAIGHT — `degenerate_frontier_half_disk`
gives the affine functional `φ_w x := signedLineFunc e w x` (unit `w`,
`φ_w(e) = 0`, gradient `(w 1, -w 0) ≠ 0`) with
`C ∩ B(e,ρ) = {φ_w < 0} ∩ B(e,ρ)`.  Consequently Target (A0)'s conclusion
(`w ∥ T` and uniqueness among sequences) is NOT a transversality statement
anymore: the tangent `T` is `w` itself, and direction uniqueness is the
`rulingCluster_dirs_parallel` content already green in ClusterLine §4
(any two approaching `U`-sequences share direction limits up to sign).
The generic `transversal_line_negative_side` commons lemma was designed
for a CURVED frontier and is not needed here.

This file records the (A0) conclusion formally and adds the strongest
sequential form:

* **`degenerate_frontier_cluster_limit`** — the exact (A0) conclusion:
  with the pinned data at a degenerate frontier point `e`, any
  approaching `U`-sequence `q` whose directions converge along a
  subsequence to `dstar` has `dstar = w ∨ dstar = -w` (the side-pinned direction;
  `sign_trans` composes the `±w₀` parallelity of `dstar` with `w = ±w₀`);
* **`bordering_rulings_asymptotically_parallel`** — the sequential
  near-parallelism: for ANY `U`-sequence `qₙ → e`,
  `det2 (unitKernelDir f (q n)) w → 0` (the ruling directions become
  parallel to the frontier line, even if they oscillate between `±w`).
  Proof by contradiction + compactness: if the determinants stayed away
  from 0 along an infinite subsequence, a convergent sub-subsequence of
  the unit directions would limit to `dstar` with `|det2 dstar w| ≠ 0`,
  contradicting `degenerate_frontier_cluster_limit` (`dstar = ±w`).

Build: `lake build Submission.Work.FrontierA0` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- **Cluster limit of bordering rulings is the side-pinned direction
(Target (A0) conclusion)**: `e` a degenerate frontier point of
`C = flatComponent f p` with pinned data (`q₀` approaching `U`-seq with
unit direction limit `w₀`, side-pinned `w = ±w₀`, `C ⊆ {φ_w < 0}`), and
`q` any approaching `U`-sequence whose directions converge along the
subsequence `φ` to `dstar`.  Then `dstar = w ∨ dstar = -w` — the bordering
rulings' direction limit is the frontier direction, up to sign, with no
further freedom (unique line). -/
theorem degenerate_frontier_cluster_limit {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heClosure : e ∈ closure (flatComponent f p))
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {q : ℕ → ℝ²} (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0)
    (hqe : Tendsto q atTop (𝓝 e))
    {φ : ℕ → ℕ} (hφmono : StrictMono φ) {dstar : ℝ²}
    (hφd : Tendsto (fun m => unitKernelDir f (q (φ m))) atTop (𝓝 dstar)) :
    dstar = w ∨ dstar = -w := by
  have hqeφ : Tendsto (fun m => q (φ m)) atTop (𝓝 e) := hqe.comp hφmono.tendsto_atTop
  have hpar₀' : w₀ = w ∨ w₀ = -w := by
    rcases hpar₀ with hp | hp
    · left
      exact hp.symm
    · right
      have hw' : -w = w₀ := by
        rw [hp]
        simp
      exact hw'.symm
  have hdpar0 : w₀ = dstar ∨ w₀ = -dstar :=
    rulingCluster_dirs_parallel hf ha heS (q₁ := q₀) (q₂ := fun m => q (φ m))
      (w₁ := w₀) (w₂ := dstar)
      hq₀S hq₀U (fun m => hqS (φ m)) (fun m => hqU (φ m)) hq₀e hqeφ hd₀₀ hφd
  have hdpar : dstar = w₀ ∨ dstar = -w₀ := by
    rcases hdpar0 with hd | hd
    · left
      exact hd.symm
    · right
      calc
        dstar = -(-dstar) := by simp
        _ = -w₀ := by rw [hd]
  exact sign_trans hdpar hpar₀'

/-- **Bordering rulings are asymptotically parallel to the frontier**:
under the pinned data at the degenerate point `e`, any `U`-sequence
`qₙ → e` has `det2 (unitKernelDir f (q n)) w → 0` — the ruling lines
through `qₙ` become parallel to the frontier line `L(e)` (they may still
oscillate between the two orientations `±w`, but never tilt away).
Proof by contradiction + compactness: if the determinants stayed away
from 0 along an infinite subsequence, a convergent sub-subsequence of the
unit directions would limit to `dstar` with `|det2 dstar w| ≠ 0`, contradicting
`degenerate_frontier_cluster_limit` (`dstar = ±w`). -/
theorem bordering_rulings_asymptotically_parallel {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e : ℝ²} (heS : e ∈ stripInterior)
    (heClosure : e ∈ closure (flatComponent f p))
    {q₀ : ℕ → ℝ²} (hq₀S : ∀ n, q₀ n ∈ stripInterior) (hq₀U : ∀ n, dN f (q₀ n) ≠ 0)
    (hq₀e : Tendsto q₀ atTop (𝓝 e))
    {w₀ : ℝ²} (hw₀₁ : ‖w₀‖ = 1)
    (hd₀₀ : Tendsto (fun n => unitKernelDir f (q₀ n)) atTop (𝓝 w₀))
    {w : ℝ²} (hw₁ : ‖w‖ = 1) (hpar₀ : w = w₀ ∨ w = -w₀)
    {q : ℕ → ℝ²} (hqS : ∀ n, q n ∈ stripInterior) (hqU : ∀ n, dN f (q n) ≠ 0)
    (hqe : Tendsto q atTop (𝓝 e)) :
    Tendsto (fun n => det2 (unitKernelDir f (q n)) w) atTop (𝓝 0) := by
  by_contra hnt
  -- metric negation of "tends to 0"
  rw [Metric.tendsto_nhds] at hnt
  push_neg at hnt
  rcases hnt with ⟨ε, hε, hbad⟩
  -- hbad : ¬ ∀ᶠ n, dist (g n) 0 < ε, g n := det2 (unitKernelDir f (q n)) w
  have hfreq : ∃ᶠ n in atTop, ε ≤ |det2 (unitKernelDir f (q n)) w| := by
    simpa [Real.dist_eq] using hbad
  -- infinite index set of the big determinants
  let P : ℕ → Prop := fun n => ε ≤ |det2 (unitKernelDir f (q n)) w|
  have hinfP : Set.Infinite {n : ℕ | P n} := by
    simpa [P] using ((Nat.frequently_atTop_iff_infinite).1 hfreq)
  let ρ : ℕ → ℕ := fun m => Nat.nth P m
  have hρmono : StrictMono ρ := Nat.nth_strictMono hinfP
  have hPρ : ∀ m, P (ρ m) := fun m => Nat.nth_mem_of_infinite hinfP m
  -- a convergent sub-subsequence of the unit directions
  have hu : ∀ m, ‖unitKernelDir f (q (ρ m))‖ = 1 := fun m =>
    norm_unitKernelDir (V2f_ne_zero_at_U hf ha (hqS (ρ m)) (hqU (ρ m)))
  rcases unitDir_subseq_convergent (u := fun m => unitKernelDir f (q (ρ m))) hu with
    ⟨dstar, hdstar, γ, hγmono, hdirγ⟩
  have hcl := degenerate_frontier_cluster_limit hf ha heS heClosure
    hq₀S hq₀U hq₀e hw₀₁ hd₀₀ hw₁ hpar₀ hqS hqU hqe
    (φ := fun m => ρ (γ m)) (hφmono := hρmono.comp hγmono) (dstar := dstar) hdirγ
  have hdetd : det2 dstar w = 0 := by
    rcases hcl with hd | hd
    · rw [hd]
      simp [det2]
      ring
    · rw [hd]
      simp [det2]
      ring
  -- the determinants along the sub-subsequence tend to det2 dstar w = 0
  have hdet_tend : Tendsto (fun m => det2 (unitKernelDir f (q (ρ (γ m)))) w) atTop
      (𝓝 (det2 dstar w)) := by
    have hpair : Tendsto (fun m => (unitKernelDir f (q (ρ (γ m))), w)) atTop (𝓝 (dstar, w)) := by
      simpa [nhds_prod_eq] using (Tendsto.prodMk hdirγ tendsto_const_nhds)
    exact (continuous_det2.continuousAt.tendsto).comp hpair
  have hdet0 : Tendsto (fun m => det2 (unitKernelDir f (q (ρ (γ m)))) w) atTop (𝓝 0) := by
    simpa [hdetd] using hdet_tend
  -- ... but every term has absolute value ≥ ε : contradiction
  have hε2 : 0 < ε / 2 := by positivity
  rcases (eventually_atTop.mp ((Metric.tendsto_nhds.mp hdet0) (ε / 2) hε2)) with ⟨M, hM⟩
  have hsmall : |det2 (unitKernelDir f (q (ρ (γ M)))) w| < ε / 2 := by
    have h := hM M le_rfl
    simpa [Real.dist_eq] using h
  have hbig : ε ≤ |det2 (unitKernelDir f (q (ρ (γ M)))) w| := hPρ (γ M)
  linarith

end Submission.PaperBand
