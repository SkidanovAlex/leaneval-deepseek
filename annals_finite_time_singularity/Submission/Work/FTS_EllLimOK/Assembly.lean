import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.Closed
import Submission.Work.FTS_EllLimOK.Defs
import Submission.Work.FTS_EllLimOK.LimDefs
import Submission.Work.FTS_EllLimOK.AssemblyAux
import Submission.Work.FTS_EllLimOK.LimExtract_bounds
import Submission.Work.FTS_EllLimOK.LimTower_dz
import Submission.Work.FTS_EllLimOK.SmoothOpen_tower
import Submission.Work.FTS_EllLimOK.LimTower_identify
import Submission.Work.FTS_EllLimOK.LimTower_c2
import Submission.Work.FTS_EllLimOK.BslOp_tower
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The tower of jets of a reindexed sequence -/

/-- The tower of the mixed jets of `G (φ n)`: `jets G φ n c d = D_z^c D_θ^d (G (φ n))`. -/
def jets (G : ℕ → ℝ → ℝ → ℝ) (φ : ℕ → ℕ) (n : ℕ) : ℕ → ℕ → ℝ → ℝ → ℝ :=
  fun c d z θ => Work.Spaces.mixed c d (G (φ n)) z θ

/-! ## The equation passes to the limit -/

lemma bslOp_eq_of_convergence (H : LimInputs) {α : ℝ} {E : Fn → Fn} {fn : ℕ → Fn}
    {f : Fn} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (E (fn n)))
    (hsol : ∀ n : ℕ, Work.FTS.StrongGlobal.IsBslSolPos α (fn n) (E (fn n)))
    (hconv : ∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0)
    (hdz : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ)
    (hΨeq : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ)
    (hfsrc : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        Tendsto (fun n => fn (φ n) z θ) Filter.atTop (𝓝 (f z θ)))
    {z θ : ℝ} (hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0) :
    Work.Elliptic.bslOp α Ψ z θ = f z θ := by
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hmember : ∀ n : ℕ,
      Work.Elliptic.bslOp α (E (fn (φ n))) z θ = lhsfun α (jets (fun k => E (fn k)) φ n) z θ := by
    intro n
    obtain ⟨hsz, hst⟩ := H.smoothTower (hsm (φ n))
    exact H.bsl α (fun z' θ' _ => rfl) hsz hst hzθ
  have hsource : ∀ n : ℕ, Work.Elliptic.bslOp α (E (fn (φ n))) z θ = fn (φ n) z θ :=
    fun n => (hsol (φ n)).1 z hz θ hθ0 hθ1
  have hΨbsl : Work.Elliptic.bslOp α Ψ z θ = lhsfun α F z θ :=
    H.bsl α (fun z' θ' hz' => hΨeq z' θ' hz') hdz hdth hzθ
  have hraw : ∀ (c d : ℕ), c + d ≤ 2 →
      Tendsto (fun n => Work.Spaces.mixed c d (E (fn (φ n))) z θ) Filter.atTop
        (𝓝 (F c d z θ)) := fun c d hcd => (hconv c d hcd).tendsto_at hzθ
  have hlim : Tendsto (fun n => lhsfun α (jets (fun k => E (fn k)) φ n) z θ) Filter.atTop
      (𝓝 (lhsfun α F z θ)) := by
    have h20 := hraw 2 0 (by norm_num)
    have h10 := hraw 1 0 (by norm_num)
    have h02 := hraw 0 2 (by norm_num)
    have h01 := hraw 0 1 (by norm_num)
    have h00 := hraw 0 0 (by norm_num)
    simp only [lhsfun, jets]
    exact ((((((h20.sub h10).const_mul (-(α ^ 2))).sub
      (h10.const_mul (α * (5 + α)))).sub
      (((h02.sub (h01.const_mul (2 * Real.cos (2 * θ)))).div_const
        ((Real.sin (2 * θ)) ^ 2)))).add
      ((h01.div_const (Real.sin (2 * θ))).const_mul (Real.tan θ))).add
      (h00.const_mul (Real.tan θ ^ 2 - 5)))
  have hlim' : Tendsto (fun n => lhsfun α (jets (fun k => E (fn k)) φ n) z θ) Filter.atTop
      (𝓝 (f z θ)) := by
    refine (hfsrc z θ hzθ).congr' ?_
    filter_upwards with n
    rw [← hmember n, hsource n]
  have hkey : lhsfun α F z θ = f z θ := tendsto_nhds_unique hlim hlim'
  rw [hΨbsl, hkey]

/-! ## The jets converge to those of the limit -/

lemma jconv_of_data {α : ℝ} {E : Fn → Fn} {fn : ℕ → Fn} {φ : ℕ → ℕ}
    {F : ℕ → ℕ → ℝ → ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hconv : ∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0)
    (hident : ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F c d z θ = Work.Spaces.mixed c d (F 0 0) z θ)
    (hΨeq : Set.EqOn (Function.uncurry Ψ) (Function.uncurry (F 0 0))
      Work.FTS.EllipticEst.Q0) :
    JConv (fun n => E (fn (φ n))) Ψ := by
  intro j i hji z θ hzθ
  have h1 : Tendsto (fun n => Work.Spaces.mixed j i (E (fn (φ n))) z θ) Filter.atTop
      (𝓝 (F j i z θ)) := (hconv j i hji).tendsto_at hzθ
  have h2 : Work.Spaces.mixed j i Ψ z θ = F j i z θ := by
    have hloc := mixed_congrOn_Q0 Work.FTS.EllipticEst.isOpen_Q0 hΨeq j i hzθ
    simp only [Function.uncurry] at hloc
    rw [hloc, hident j i hji z θ hzθ]
  rw [h2]
  exact h1

/-! ## The assembly -/

theorem closedCompact_of_inputs {α Ce : ℝ} (H : LimInputs) (h : LocalBound α Ce) :
    ClosedCompact α Ce := by
  intro E hE fn f hL
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := h E hE fn f hL
  have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (E (fn n)) :=
    fun n => (hE (fn n) (hL.classC n)).2.smooth
  have hsol : ∀ n : ℕ, Work.FTS.StrongGlobal.IsBslSolPos α (fn n) (E (fn n)) :=
    fun n => (hE (fn n) (hL.classC n)).2.sol
  -- the pointwise bound of `LocalBound`, in the form `wt`
  have hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C₀ * wt z θ := by
    intro n j i hji z θ hzθ
    have h' := hC₀ n j i hji z θ hzθ
    rw [mul_div_assoc] at h'
    simpa only [wt] using h'
  -- the Arzelà–Ascoli extraction
  obtain ⟨hbdd, heqc⟩ := H.extract hsm hbnd
  obtain ⟨φ, hφ, g, hgl⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (F := fun n p => fam6 (fun k => E (fn k)) n p) hbdd heqc
  -- the limit of each of the six families
  let F : ℕ → ℕ → ℝ → ℝ → ℝ := fun c d z θ => g (z, θ) (idx6 c d)
  have hconv : ∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0 := by
    intro c d hcd
    have h1 : TendstoLocallyUniformlyOn
        (fun n p => fam6 (fun k => E (fn k)) (φ n) p (idx6 c d))
        (fun p => g p (idx6 c d)) Filter.atTop Work.FTS.EllipticEst.Q0 := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0]
      intro K hKQ hK
      have h2 := Metric.tendstoUniformlyOn_iff.mp
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact
          Work.FTS.EllipticEst.isOpen_Q0).mp hgl K hKQ hK)
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h2 ε hε] with n hn p hp
      exact lt_of_le_of_lt (dist_le_pi_dist (g p)
        (fam6 (fun k => E (fn k)) (φ n) p) (idx6 c d)) (hn p hp)
    have h2 : (fun n p => fam6 (fun k => E (fn k)) (φ n) p (idx6 c d))
        = fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2 := by
      funext n p
      simp only [fam6, idx6_spec hcd]
    have h3 : (fun p : ℝ × ℝ => g p (idx6 c d)) = fun p => F c d p.1 p.2 := by
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
        refine decay_of_wt_bound hC₀pos.le h0 h1 fun z hz => ?_
        have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
          Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩
        have hΨz : Ψ z θ = F 0 0 z θ := by simp only [Ψ, if_pos hθIoo]
        rw [hΨz]
        have hlim : Tendsto (fun n => |Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ|)
            Filter.atTop (𝓝 |F 0 0 z θ|) :=
          ((hconv 0 0 (show 0 + 0 ≤ 2 by norm_num)).tendsto_at hzθ).abs
        have hle : ∀ n : ℕ,
            |Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ| ≤ C₀ * wt z θ :=
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
    fun z θ hzθ => bslOp_eq_of_convergence H hsm hsol hconv hdz hdth hΨfun hfsrc hzθ
  have hJ : JConv (fun n => E (fn (φ n))) Ψ := jconv_of_data (α := α) hconv hident hΨeq
  exact ⟨Ψ, ⟨fun z hz θ hθ0 hθ1 => heq z θ ⟨hz, hθ0, hθ1⟩, hDir0, hDir1, hdecay⟩, hΨc2,
    ⟨φ, hφ.tendsto_atTop, hJ⟩⟩

/-- **The compactness obligation from the local growth bound**, with the six inputs instantiated
by the sibling modules of this directory. -/
theorem closedCompact_of_children {α Ce : ℝ} (h : LocalBound α Ce) : ClosedCompact α Ce :=
  closedCompact_of_inputs
    ⟨LimExtract_bounds, LimTower_dz, SmoothOpen_tower, LimTower_identify, LimTower_c2,
      BslOp_tower⟩ h

end Work.FTS_EllLimOK
