/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PkgJets/clusterExtract` — the cluster limit of a `LimSeq4` under the repaired packages

The task: given an operator `E` carrying the fully repaired packages `HasPkgE α Ce E` and a
`LimSeq4 α fn f` sequence (converging in all `C⁴`-slots on the open quadrant `Qd`, uniformly
`ℋ⁶`-bounded), extract a *strictly monotone* subsequence `σ` and a limit `Ψ` with

* `Ψ` solves the elliptic law for `f` (`IsBslSolPos α f Ψ`),
* `Ψ` is `C²` on every closed box `[a,b] × [0,π/2]`, `0 < a ≤ b` (`BoxReg Ψ` — the closed-box
  regularity that `ClosedUniq3`'s `FatouPkg` demands and that the integral memberships do not
  supply), and
* the *values* `E (fn (σ n))` converge pointwise on `Qd` to `Ψ`.

## The route

* `clusterLimit_of_hasPkgE` — the compactness/closure step, in the form needed here.  It is the
  argument of `Work.FTS_EllLimOK.closedCompact_of_inputs` (whose six analytic inputs
  `LimInputs` are the proved sibling modules of `FTS_EllLimOK`), fed with the *specific* local
  growth bound that `HasPkgD` supplies for this operator
  (`PkgRepair.localBound4_of_hasPkgD`), rather than with the global obligation
  `LocalBound α Ce` (which quantifies over every operator carrying the frozen packages and is not
  available here).  The Arzelà–Ascoli extraction
  `exists_subseq_tendstoLocallyUniformlyOn_fin` returns a *strictly monotone* reindexing, which
  is exactly what the statement of `clusterExtract` asks for.
* `boxReg_of_subseq_of_uniformCorner` (proved in `PkgJets/cornerBoundRepair.lean`) turns the
  uniform corner bounds of `HasPkgE.corner` together with the closed-box convergence into
  `BoxReg Ψ`.
* `boxConvOnCbox` (proved in `PkgJets/boxConvOnCbox.lean`, a separate request of this stretch)
  supplies the closed-box convergence: in the interior of the box it is the `(0,0)`-slot
  convergence, and on `θ = 0, π/2` both the sequence and the limit vanish by the Dirichlet clauses
  of `IsBslSolPos`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.PkgRepair
import Submission.Work.FTS_EllLimOK.BoxReg_of_uniform
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.FTS_EllLimOK.Assembly
import Submission.Work.FTS_EllLimOK.PkgJets.cornerBoundRepair
import Submission.Work.FTS_EllLimOK.PkgJets.boxConvOnCbox

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.PkgJets

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-- **The compactness/closure step for one operator carrying the repaired packages.**  Along every
`LimSeq4` sequence for `E`, some *strictly monotone* reindexing of the sequence has a cluster limit
`Ψ` which (on the open quadrant) solves the elliptic law for the limit profile `f`, with the
`C²`-jets converging to those of `Ψ`.

The body is the assembly of `Work.FTS_EllLimOK.closedCompact_of_inputs` with the six analytic
inputs `LimInputs` instantiated by their sibling modules, and with the local growth bound obtained
from this particular operator (`HasPkgE ⊃ HasPkgD` carries the far-field rate `PkgDecay`), instead
of from the global obligation `LocalBound α Ce`. -/
theorem clusterLimit_of_hasPkgE {α Ce : ℝ} (hα : 0 < α) {E : Fn →ₗ[ℝ] Fn}
    (hE : Work.FTS_EllLimOK.HasPkgE α Ce E) {fn : ℕ → Fn} {f : Fn}
    (hL : Work.FTS_EllLimOK.LimSeq4 α fn f) :
    ∃ (φ : ℕ → ℕ) (Ψ : ℝ → ℝ → ℝ), StrictMono φ ∧
      Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
      Work.FTS_EllLimOK.JConv (fun n => E (fn (φ n))) Ψ := by
  classical
  -- the frozen packages, and the specific local growth bound they give for this operator
  have hP : Work.FTS_EllLimOK.HasPkg α Ce E := hE.toHasPkgD.toHasPkg
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Work.FTS_EllLimOK.localBound4_of_hasPkgD hα E hE.toHasPkgD fn f hL
  have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (E (fn n)) :=
    fun n => (hP (fn n) (hL.classC n)).2.smooth
  have hsol : ∀ n : ℕ, Work.FTS.StrongGlobal.IsBslSolPos α (fn n) (E (fn n)) :=
    fun n => (hP (fn n) (hL.classC n)).2.sol
  -- the pointwise bound, in the form `wt`
  have hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C₀ * Work.FTS_EllLimOK.wt z θ := by
    intro n j i hji z θ hzθ
    have h' := hC₀ n j i (by omega) z θ hzθ
    rw [mul_div_assoc] at h'
    simpa only [Work.FTS_EllLimOK.wt] using h'
  -- the six analytic inputs, instantiated by their sibling modules
  have H : Work.FTS_EllLimOK.LimInputs :=
    ⟨Work.FTS_EllLimOK.LimExtract_bounds, Work.FTS_EllLimOK.LimTower_dz,
      Work.FTS_EllLimOK.SmoothOpen_tower, Work.FTS_EllLimOK.LimTower_identify,
      Work.FTS_EllLimOK.LimTower_c2, Work.FTS_EllLimOK.BslOp_tower⟩
  -- the Arzelà–Ascoli extraction
  obtain ⟨hbdd, heqc⟩ := H.extract hsm hbnd
  obtain ⟨φ, hφ, g, hgl⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (F := fun n p => Work.FTS_EllLimOK.fam6 (fun k => E (fn k)) n p) hbdd heqc
  -- the limit of each of the six families
  let F : ℕ → ℕ → ℝ → ℝ → ℝ := fun c d z θ => g (z, θ) (Work.FTS_EllLimOK.idx6 c d)
  have hconv : ∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0 := by
    intro c d hcd
    have h1 : TendstoLocallyUniformlyOn
        (fun n p => Work.FTS_EllLimOK.fam6 (fun k => E (fn k)) (φ n) p
          (Work.FTS_EllLimOK.idx6 c d))
        (fun p => g p (Work.FTS_EllLimOK.idx6 c d)) Filter.atTop Work.FTS.EllipticEst.Q0 := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0]
      intro K hKQ hK
      have h2 := Metric.tendstoUniformlyOn_iff.mp
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact
          Work.FTS.EllipticEst.isOpen_Q0).mp hgl K hKQ hK)
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h2 ε hε] with n hn p hp
      exact lt_of_le_of_lt (dist_le_pi_dist (g p)
        (Work.FTS_EllLimOK.fam6 (fun k => E (fn k)) (φ n) p) (Work.FTS_EllLimOK.idx6 c d))
        (hn p hp)
    have h2 : (fun n p => Work.FTS_EllLimOK.fam6 (fun k => E (fn k)) (φ n) p
          (Work.FTS_EllLimOK.idx6 c d))
        = fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2 := by
      funext n p
      simp only [Work.FTS_EllLimOK.fam6, Work.FTS_EllLimOK.idx6_spec hcd]
    have h3 : (fun p : ℝ × ℝ => g p (Work.FTS_EllLimOK.idx6 c d)) = fun p => F c d p.1 p.2 := by
      funext p
      obtain ⟨a, b⟩ := p
      rfl
    rwa [h2, h3] at h1
  -- continuity of the limits
  have hcont : ∀ (c d : ℕ), c + d ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    intro c d hcd
    refine (hconv c d hcd).continuousOn (Frequently.of_forall fun n => ?_)
    exact ((hsm (φ n)).mixed c d).continuousOn
  -- the tower relations and their consequences
  obtain ⟨hdz, hdth⟩ := H.tower hsm hconv
  have hident := H.identify hdz hdth
  have hc2 := H.c2 hcont hdz hdth
  -- the limit function
  let Ψ : ℝ → ℝ → ℝ := fun z θ => if θ ∈ Set.Ioo (0 : ℝ) (π / 2) then F 0 0 z θ else 0
  have hΨeq : Set.EqOn (Function.uncurry Ψ) (Function.uncurry (F 0 0))
      Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z, θ⟩ hzθ
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    simp only [Function.uncurry, Ψ]
    rw [if_pos (show θ ∈ Set.Ioo (0 : ℝ) (π / 2) from ⟨hθ0, hθ1⟩)]
  have hΨfun : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ := by
    intro z θ hzθ
    exact hΨeq hzθ
  have hΨc2 : ContDiffOn ℝ 2 (Function.uncurry Ψ) Work.FTS.EllipticEst.Q0 :=
    hc2.congr hΨeq
  -- the two Dirichlet conditions
  have hDir0 : ∀ z : ℝ, 0 ≤ z → Ψ z 0 = 0 := by
    intro z _
    have h : (0 : ℝ) ∉ Set.Ioo (0 : ℝ) (π / 2) := fun hh => absurd hh.1 (lt_irrefl 0)
    simp only [Ψ, if_neg h]
  have hDir1 : ∀ z : ℝ, 0 ≤ z → Ψ z (π / 2) = 0 := by
    intro z _
    have h : (π / 2) ∉ Set.Ioo (0 : ℝ) (π / 2) := fun hh => absurd hh.2 (lt_irrefl _)
    simp only [Ψ, if_neg h]
  -- the decay
  have hdecay : ∀ θ ∈ Work.Spaces.Iθ, Tendsto (fun z => Ψ z θ) Filter.atTop (𝓝 0) := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have hfun : (fun z : ℝ => Ψ z 0) = fun _ : ℝ => (0 : ℝ) := by
        funext z
        have h : (0 : ℝ) ∉ Set.Ioo (0 : ℝ) (π / 2) := fun hh => absurd hh.1 (lt_irrefl 0)
        simp only [Ψ, if_neg h]
      rw [hfun]
      exact tendsto_const_nhds
    · rcases eq_or_lt_of_le hθ.2 with h1 | h1
      · subst h1
        have hfun : (fun z : ℝ => Ψ z (π / 2)) = fun _ : ℝ => (0 : ℝ) := by
          funext z
          have h : (π / 2) ∉ Set.Ioo (0 : ℝ) (π / 2) := fun hh => absurd hh.2 (lt_irrefl _)
          simp only [Ψ, if_neg h]
        rw [hfun]
        exact tendsto_const_nhds
      · have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := ⟨h0, h1⟩
        refine Work.FTS_EllLimOK.decay_of_wt_bound hC₀pos.le h0 h1 fun z hz => ?_
        have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
          Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩
        have hΨz : Ψ z θ = F 0 0 z θ := by simp only [Ψ, if_pos hθIoo]
        rw [hΨz]
        have hlim : Tendsto (fun n => |Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ|)
            Filter.atTop (𝓝 |F 0 0 z θ|) :=
          ((hconv 0 0 (show 0 + 0 ≤ 2 by norm_num)).tendsto_at hzθ).abs
        have hle : ∀ n : ℕ,
            |Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ| ≤ C₀ * Work.FTS_EllLimOK.wt z θ :=
          fun n => hbnd (φ n) 0 0 (by norm_num) z θ hzθ
        exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hle
  -- the source converges to `f`
  have hfsrc : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => fn (φ n) z θ) Filter.atTop (𝓝 (f z θ)) := by
    intro z θ hzθ
    exact (hL.conv 0 0 (by norm_num) z θ hzθ).comp hφ.tendsto_atTop
  -- the equation and the jet convergence
  have heq : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Elliptic.bslOp α Ψ z θ = f z θ :=
    fun z θ hzθ =>
      Work.FTS_EllLimOK.bslOp_eq_of_convergence H hsm hsol hconv hdz hdth hΨfun hfsrc hzθ
  have hJ : Work.FTS_EllLimOK.JConv (fun n => E (fn (φ n))) Ψ :=
    Work.FTS_EllLimOK.jconv_of_data (α := α) hconv hident hΨeq
  exact ⟨φ, Ψ, hφ,
    ⟨fun z hz θ hθ0 hθ1 => heq z θ ⟨hz, hθ0, hθ1⟩, hDir0, hDir1, hdecay⟩, hJ⟩

/-- **The cluster extraction.**  From the repaired packages of `E` and a `LimSeq4` sequence for
`f`, one extracts a strictly monotone subsequence `σ` and a limit `Ψ` which is `IsBslSolPos` for
`f`, is `C²` on every closed box `[a,b] × [0,π/2]` (`0 < a ≤ b`), and is the pointwise limit of
the values `E (fn (σ n))` on the open quadrant. -/
theorem clusterExtract {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.HasPkgE α Ce E)
    {fn : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hL : Work.FTS_EllLimOK.LimSeq4 α fn f) :
    ∃ (σ : ℕ → ℕ) (Ψ : ℝ → ℝ → ℝ), StrictMono σ ∧
      Work.FTS_EllLimOK.BoxReg Ψ ∧
      Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun n => E (fn (σ n)) z θ) Filter.atTop (𝓝 (Ψ z θ))) := by
  obtain ⟨σ, Ψ, hσ, hsol, hJ⟩ := clusterLimit_of_hasPkgE hα hE hL
  -- the two primitive fields consumed by `BoxReg_of_uniform`
  have hstrip : ∀ g, Work.FTS.ClassC.ClassC α g → Work.Spaces.SmoothStrip (E g) :=
    fun g hg => hE.toHasPkgD.strip g hg
  have hcorner : PkgCornerU α Ce E := hE.corner
  -- the sequence solves the law, and so does its limit
  have hsolσ : ∀ n : ℕ,
      Work.FTS.StrongGlobal.IsBslSolPos α (fn (σ n)) (E (fn (σ n))) :=
    fun n => (hE.toHasPkgD.toHasPkg (fn (σ n)) (hL.classC (σ n))).2.sol
  have hbox : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
      Filter.Tendsto (fun n => E (fn (σ n)) p.1 p.2) Filter.atTop (𝓝 (Ψ p.1 p.2)) :=
    boxConvOnCbox hsolσ hsol hJ
  have hBox : Work.FTS_EllLimOK.BoxReg Ψ :=
    boxReg_of_subseq_of_uniformCorner hstrip hcorner hL σ Ψ hbox
  exact ⟨σ, Ψ, hσ, hBox, hsol, fun z θ hzθ => by
    have h := hJ 0 0 (by norm_num) z θ hzθ
    simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h⟩

end Work.FTS_EllLimOK.PkgJets
