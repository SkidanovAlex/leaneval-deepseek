import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Assembly
import Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform
import Submission.Work.FTS_EllLimOK.ClosedCompact3H_of_bounds_fatou
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_EllLimOK.Decay.decay_of_hkMem0_jetBound
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.clusterExtract
import Submission.Work.FTS_EllLimOK.ProducerH.slotBd_phiTil
import Submission.Work.FTS_EllLimOK.UniqFatou
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.H2W.asliceMomentEq
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.SmoothStripDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.BoxDataH

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The assembly: the strictly monotone jet extraction over `HasPkgH`

`clusterLimitH_strict2` is the extraction step of the requested lemma `clusterLimitH_aux2`: from an
operator carrying `HasPkgH` and a `LimSeq4` sequence it produces a *strictly monotone* reindexing
`φ` and a limit `Ψ` carrying the minimal limit package `FatouPkgG` (`IsBslSolPos α f Ψ`, `C³` on
the open quadrant, the two `ℋ⁰`-memberships and `BoxReg`), which is the `C³`-jet limit of the
values `E (fn (φ n))` on the open quadrant.

It is the order-`3` compactness step of `ClosedCompact3H_of_bounds_fatou`, with two differences:

* the closed-box regularity of the limit is obtained from the *global* `C^{2,β}` Arzelà–Ascoli
  hypothesis `crux`, instead of from the closed-box data `BoxDataH` (which is not available for
  `HasPkgH` at this point of the dependency graph).  The crux is applied once, to the extracted
  family `fun m z θ => E (fn (φ m)) z θ` and the limit `Ψ`: its box-uniform data on *every* box
  comes from `RulingELF.PkgBoxH` — the members of the sequence are class-`C` and their `ℋ⁶`-norms
  are uniformly bounded — via `BoxDataH.boxUniform2_of_pkgBoxH`, and the convergence on every box
  from the convergence on the open quadrant together with the vanishing of both sides on the two
  angular boundary lines, via `BoxDataH.tendsto_values_on_cbox`;
* the reindexing `φ` produced by the Arzelà–Ascoli extraction is *strictly monotone*, and it is
  kept (rather than replaced by its cofinality), since the requested conclusion asks for a strictly
  monotone subsequence.

The remaining ingredients are the ones already proved in the area:
`FatouH.localBoundH_of_hasPkgH` and `FatouH.fatouDataH_of_hasPkgH` (the uniform pointwise bounds
of order `≤ 4` and the uniform `ℋ⁰`-data of `E (fn n)` and `E (fn n)/cos θ`),
`LimExtract.limExtract_bounds10_const` (the Arzelà–Ascoli data of the ten order-`≤ 3` jets),
`LimTower_dz3` / `LimTower_identify3` (the tower relations and the identification of the limit's
jets), `bslOp_eq_of_convergence` (the elliptic law of the limit), `Fatou.HkMem_fatou_z` (the Fatou
step giving the two `ℋ⁰`-memberships) and `Decay.decay_of_hkMem0_jetBound` (the far-field decay,
which needs the box regularity produced by the crux). -/

/-- **The strictly monotone jet extraction.**  Along a `LimSeq4` sequence for an operator carrying
`HasPkgH`, some strictly monotone reindexing `φ` has a cluster limit `Ψ` which carries the minimal
limit package `FatouPkgG α f Ψ` and is the `C³`-jet limit of the values `E (fn (φ n))` on the open
quadrant.  The box regularity of `Ψ` is supplied by the hypothesis `crux` (the `C^{2,β}`
Arzelà–Ascoli theorem applied to the box-uniform data and the boxwise convergence). -/
theorem clusterLimitH_strict2 {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.HasPkgH α Ce E)
    {fn : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hL : Work.FTS_EllLimOK.LimSeq4 α fn f)
    (crux : ∀ {H : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ},
      (∀ a b : ℝ, 0 < a → a < b → Work.FTS_EllLimOK.BoxDataH.BoxUniform2 a b H) →
      (∀ a b : ℝ, 0 < a → a < b → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        Filter.Tendsto (fun n => H n z θ) Filter.atTop (nhds (G z θ))) →
      Work.FTS_EllLimOK.BoxReg G) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψ : ℝ → ℝ → ℝ,
      Work.FTS_EllLimOK.FatouPkgG α f Ψ ∧
      Work.FTS_EllLimOK.JConv3 (fun n => E (fn (φ n))) Ψ := by
  classical
  have hPkg : Work.FTS_EllLimOK.HasPkg α Ce E := hE.toHasPkg
  obtain ⟨C₄, hC₄pos, hb⟩ :=
    (Work.FTS_EllLimOK.localBoundH_of_hasPkgH hα hα1) E hE fn f hL
  obtain ⟨C, hCpos, hseq, hseqc⟩ :=
    (Work.FTS_EllLimOK.fatouDataH_of_hasPkgH (α := α) hα) E hE fn f hL
  have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (E (fn n)) :=
    fun n => (hPkg (fn n) (hL.classC n)).2.smooth
  have hsol : ∀ n : ℕ, Work.FTS.StrongGlobal.IsBslSolPos α (fn n) (E (fn n)) :=
    fun n => (hPkg (fn n) (hL.classC n)).2.sol
  obtain ⟨B₀, hB₀⟩ := hL.bound
  -- the constant pointwise bounds of `LocalBoundH`
  have hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C₄ :=
    fun n j i hji z θ hzθ => hb n j i hji z θ hzθ
  -- the Arzelà–Ascoli extraction on the ten order-`≤ 3` jets
  obtain ⟨hbdd, heqc⟩ := Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const hsm hbnd
  obtain ⟨φ, hφ, g, hgl⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (F := fun n p => Work.FTS_EllLimOK.fam10 (fun k => E (fn k)) n p) hbdd heqc
  let F : ℕ → ℕ → ℝ → ℝ → ℝ := fun c d z θ => g (z, θ) (Work.FTS_EllLimOK.idx10 c d)
  have hconv : ∀ (c d : ℕ), c + d ≤ 3 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0 := by
    intro c d hcd
    have h1 : TendstoLocallyUniformlyOn
        (fun n p => Work.FTS_EllLimOK.fam10 (fun k => E (fn k)) (φ n) p
          (Work.FTS_EllLimOK.idx10 c d))
        (fun p => g p (Work.FTS_EllLimOK.idx10 c d)) Filter.atTop Work.FTS.EllipticEst.Q0 := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0]
      intro K hKQ hK
      have h2 := Metric.tendstoUniformlyOn_iff.mp
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact
          Work.FTS.EllipticEst.isOpen_Q0).mp hgl K hKQ hK)
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h2 ε hε] with n hn p hp
      exact lt_of_le_of_lt (dist_le_pi_dist (g p)
        (Work.FTS_EllLimOK.fam10 (fun k => E (fn k)) (φ n) p)
        (Work.FTS_EllLimOK.idx10 c d)) (hn p hp)
    have h2 : (fun n p => Work.FTS_EllLimOK.fam10 (fun k => E (fn k)) (φ n) p
          (Work.FTS_EllLimOK.idx10 c d))
        = fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2 := by
      funext n p
      simp only [Work.FTS_EllLimOK.fam10, Work.FTS_EllLimOK.idx10_spec hcd]
    have h3 : (fun p : ℝ × ℝ => g p (Work.FTS_EllLimOK.idx10 c d))
        = fun p => F c d p.1 p.2 := by
      funext p
      obtain ⟨a, b⟩ := p
      rfl
    rwa [h2, h3] at h1
  -- the limits are continuous
  have hcontF : ∀ (c d : ℕ), c + d ≤ 3 →
      ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    intro c d hcd
    refine (hconv c d hcd).continuousOn (Frequently.of_forall fun n => ?_)
    exact ((hsm (φ n)).mixed c d).continuousOn
  -- the tower relations and the identification with the jets of the limit function
  obtain ⟨hdz, hdth⟩ :=
    Work.FTS_EllLimOK.LimTower_dz3 (G := fun k => E (fn k)) hsm hconv
  obtain ⟨hFc3, hident⟩ := Work.FTS_EllLimOK.LimTower_identify3 hcontF hdz hdth
  -- the limit function
  let Ψ : ℝ → ℝ → ℝ := fun z θ =>
    if (z, θ) ∈ Work.FTS.EllipticEst.Q0 then F 0 0 z θ else 0
  have hΨfun : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ := by
    intro z θ hzθ
    simp only [Ψ]
    rw [ite_eq_left hzθ]
  have hvan : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (Real.pi / 2) → Ψ z θ = 0 := by
    intro z θ hθ
    have hz : (z, θ) ∉ Work.FTS.EllipticEst.Q0 := fun hmem =>
      hθ (Work.FTS.EllipticEst.mem_Q0.mp hmem).2
    simp only [Ψ]
    rw [ite_eq_right hz]
  have hΨeq : Set.EqOn (Function.uncurry Ψ) (Function.uncurry (F 0 0))
      Work.FTS.EllipticEst.Q0 := fun p hp => hΨfun p.1 p.2 hp
  have hc3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd :=
    hFc3.congr hΨeq
  -- the jet convergence
  have hjet : Work.FTS_EllLimOK.JConv3 (fun n => E (fn (φ n))) Ψ := by
    intro j i hji z θ hzθ
    have h1 : Tendsto (fun n => Work.Spaces.mixed j i (E (fn (φ n))) z θ) atTop
        (𝓝 (F j i z θ)) := (hconv j i (by omega)).tendsto_at hzθ
    have h2 : Work.Spaces.mixed j i Ψ z θ = F j i z θ := by
      have hloc := mixed_congrOn_Q0 (V := Work.FTS.EllipticEst.Q0)
        Work.FTS.EllipticEst.isOpen_Q0 hΨeq j i hzθ
      simp only [Function.uncurry] at hloc
      rw [hloc, ← hident j i hji z θ hzθ]
    rw [h2]
    exact h1
  have htriv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ := hΨfun
  have hcosq : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  -- the pointwise convergence of the two quantities
  have hPsiConv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => E (fn (φ n)) z θ) atTop (𝓝 (Ψ z θ)) := by
    intro z θ hzθ
    have h : Tendsto (fun n => Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ) atTop
        (𝓝 (F 0 0 z θ)) := (hconv 0 0 (by norm_num)).tendsto_at hzθ
    rw [hΨfun z θ hzθ]
    simpa using h
  have hcosConv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => E (fn (φ n)) z θ / Real.cos θ) atTop (𝓝 (Ψ z θ / Real.cos θ)) :=
    fun z θ hzθ => (hPsiConv z θ hzθ).div_const _
  -- (1) `HkMem α 0 Ψ`, by Fatou in `θ` and in `z`
  have hM1 : Work.Spaces.HkMem α 0 Ψ :=
    (hkMem0_of_tendsto_z (C := C) (un := fun n z θ => E (fn (φ n)) z θ) (u := Ψ)
      (fun n => (hseq (φ n)).1) (fun n => (hseq (φ n)).2.1) (fun n => (hseq (φ n)).2.2)
      (fun n => (hsm (φ n)).continuousOn) hPsiConv).1
  -- (2) `HkMem α 0 (Ψ/cos θ)`
  have hM5 : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) :=
    (hkMem0_of_tendsto_z (C := C)
      (un := fun n z θ => E (fn (φ n)) z θ / Real.cos θ)
      (u := fun z θ => Ψ z θ / Real.cos θ)
      (fun n => (hseqc (φ n)).1) (fun n => (hseqc (φ n)).2.1) (fun n => (hseqc (φ n)).2.2)
      (fun n => (hsm (φ n)).continuousOn.div
        ((Real.continuous_cos.comp continuous_snd).continuousOn) hcosq)
      hcosConv).1
  -- the limit inherits the constant jet bounds of the members
  have hlimbnd : ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i Ψ z θ| ≤ C₄ := by
    intro j i hji z θ hzθ
    have h1 : Work.Spaces.mixed j i Ψ z θ = F j i z θ := by
      have hloc := mixed_congrOn_Q0 (V := Work.FTS.EllipticEst.Q0)
        Work.FTS.EllipticEst.isOpen_Q0 hΨeq j i hzθ
      simp only [Function.uncurry] at hloc
      rw [hloc, ← hident j i hji z θ hzθ]
    have hlim : Tendsto (fun n => |Work.Spaces.mixed j i (E (fn (φ n))) z θ|) atTop
        (𝓝 |F j i z θ|) := ((hconv j i hji).tendsto_at hzθ).abs
    rw [h1]
    exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds
      (fun n => hb (φ n) j i (by omega) z θ hzθ)
  -- the closed-box regularity of the limit, from the *global* `C^{2,β}` Arzelà–Ascoli crux:
  -- the box-uniform data is available on every box (the members of the sequence are class-`C`
  -- and their `ℋ⁶`-norms are uniformly bounded) and so is the convergence on every box (the open
  -- quadrant by the extraction, the two angular boundary lines because both sides vanish there),
  -- so a single application of the crux yields the whole of `BoxReg`.
  have hboxΨ : Work.FTS_EllLimOK.BoxReg Ψ :=
    crux (fun a b ha hab =>
        Work.FTS_EllLimOK.BoxDataH.boxUniform2_of_pkgBoxH hE.box ha hab
          (fun m => hL.classC (φ m)) (fun m => hB₀ (φ m)))
      (fun a b ha _hab =>
        Work.FTS_EllLimOK.BoxDataH.tendsto_values_on_cbox (Ψ := Ψ)
          (un := fun m z θ => E (fn (φ m)) z θ) ha
          hPsiConv (fun z => hvan z 0 (by simp)) (fun z => hvan z (Real.pi / 2) (by simp))
          (fun m z hz => ⟨(hsol (φ m)).2.1 z hz, (hsol (φ m)).2.2.1 z hz⟩))
  -- the far-field decay of the limit
  have hdec : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Tendsto (fun z => Ψ z θ) atTop (𝓝 0) :=
    Work.FTS_EllLimOK.Decay.decay_of_hkMem0_jetBound hboxΨ hM1
      (fun z θ hzθ => hlimbnd 0 0 (by norm_num) z θ hzθ)
      (fun z θ hzθ => hlimbnd 1 0 (by norm_num) z θ hzθ)
      (fun z θ hzθ => hlimbnd 0 1 (by norm_num) z θ hzθ)
  -- the elliptic law of the limit
  have hfsrc : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => fn (φ n) z θ) atTop (𝓝 (f z θ)) :=
    fun z θ hzθ => (hL.conv 0 0 (by norm_num) z θ hzθ).comp hφ.tendsto_atTop
  have hsolf : Work.FTS.StrongGlobal.IsBslSolPos α f Ψ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz θ hθ0 hθ1
      exact Work.FTS_EllLimOK.bslOp_eq_of_convergence
        ⟨Work.FTS_EllLimOK.LimExtract_bounds, Work.FTS_EllLimOK.LimTower_dz,
          Work.FTS_EllLimOK.SmoothOpen_tower, Work.FTS_EllLimOK.LimTower_identify,
          Work.FTS_EllLimOK.LimTower_c2, Work.FTS_EllLimOK.BslOp_tower⟩
        hsm hsol (fun c d hcd => hconv c d (by omega))
        (fun c d hcd => hdz c d (by omega)) (fun c d hcd => hdth c d (by omega))
        htriv hfsrc (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
    · intro z _
      exact hvan z 0 (by simp)
    · intro z _
      exact hvan z (Real.pi / 2) (by simp)
    · intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        have hf : (fun z : ℝ => Ψ z 0) = fun _ => (0 : ℝ) :=
          funext fun z => hvan z 0 (by simp)
        rw [hf]
        exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h1 | h1
        · subst h1
          have hf : (fun z : ℝ => Ψ z (Real.pi / 2)) = fun _ => (0 : ℝ) :=
            funext fun z => hvan z (Real.pi / 2) (by simp)
          rw [hf]
          exact tendsto_const_nhds
        · exact hdec θ ⟨h0, h1⟩
  exact ⟨φ, hφ, Ψ, ⟨hsolf, hc3, hM1, hM5, hboxΨ⟩, hjet⟩

/-! ## The requested lemma -/

/-- **The requested lemma.**  Along the sub-subsequence `fn ∘ ns` of a `LimSeq4` sequence for an
operator carrying `HasPkgH`, some further *strictly monotone* reindexing `τ` has a cluster limit
`Ψ` which is `C²` on every closed box `[a,b] × [0,π/2]` (`BoxReg`), solves the elliptic law of the
limit profile `f` (`IsBslSolPos α f Ψ`), carries the two level-`0` memberships `HkMem α 0 Ψ` and
`HkMem α 0 (Ψ/cos θ)`, and is the pointwise limit of the values `E (fn (ns (τ m)))` on the open
quadrant.

The proof is `clusterLimitH_strict2` applied to the reindexed sequence `fn ∘ ns` (a `LimSeq4` again
by `limSeq4_comp`); the hypothesis `crux` provides the closed-box regularity of the limit.  The
canonical instance of `crux` is `BoxDataH.boxReg_of_boxUniform2`, which derives it from the
`C^{2,β}` Arzelà–Ascoli theorem `BoxDataH.contDiffOn_two_of_boxUniform2`. -/
theorem clusterLimitH_aux2 {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.HasPkgH α Ce E)
    {fn : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hL : Work.FTS_EllLimOK.LimSeq4 α fn f)
    {ns : ℕ → ℕ} (hns : Filter.Tendsto ns Filter.atTop Filter.atTop)
    (crux : ∀ {H : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ},
      (∀ a b : ℝ, 0 < a → a < b → Work.FTS_EllLimOK.BoxDataH.BoxUniform2 a b H) →
      (∀ a b : ℝ, 0 < a → a < b → ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (Real.pi / 2),
        Filter.Tendsto (fun n => H n z θ) Filter.atTop (nhds (G z θ))) →
      Work.FTS_EllLimOK.BoxReg G) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ Ψ : Work.FTS.Galerkin.Fn,
      Work.FTS_EllLimOK.BoxReg Ψ ∧
      Work.FTS.StrongGlobal.IsBslSolPos α f Ψ ∧
      Work.Spaces.HkMem α 0 Ψ ∧
      Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) ∧
      (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
        Filter.Tendsto (fun m => E (fn (ns (τ m))) z θ) Filter.atTop (nhds (Ψ z θ))) := by
  have hLs : Work.FTS_EllLimOK.LimSeq4 α (fun m => fn (ns m)) f :=
    Work.FTS_EllLimOK.limSeq4_comp hL hns
  obtain ⟨φ, hφ, Ψ, hΨ, hJ⟩ := clusterLimitH_strict2 hα hα1 hE hLs crux
  refine ⟨φ, hφ, Ψ, hΨ.box, hΨ.sol, hΨ.mem, hΨ.memCos, ?_⟩
  intro z θ hzθ
  have h := hJ 0 0 (by norm_num) z θ hzθ
  simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_zero, Work.Spaces.DthIter_zero] using h

end Work.FTS_EllLimOK.BoxDataH
