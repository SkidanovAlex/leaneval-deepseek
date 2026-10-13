/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ClosedCompact3H_of_bounds_fatou` — obligation 1 over `HasPkgH`

The order-`3` compactness obligation `ClosedCompact3H α Ce` follows from the three sequence-level
hypotheses of `FatouH`:

* `LocalBoundH α Ce` — the pointwise jet bounds of order `≤ 4` with a **constant** right-hand side
  (the `1/(1+z)` rate of `Defs3.LocalBound4` is false: class `C` allows `z^{-s}` tails,
  `s ∈ (1/2,3/2)`, and `bslOp` is Euler in `z`);
* `FatouDataH α Ce` — the uniform `ℋ⁰`-memberships of `E (fn n)` and `E (fn n)/cos θ` with one
  common `HkSq` bound and one common `z`-local `θ`-slice bound `C(1+1/z)`;
* `BoxDataH α Ce` — the closed-box data.

The far-field decay of the limit (needed for the `IsBslSolPos` clause of the limit package, which
the uniqueness argument and hence the target `EllLimOK3` consume) is **not** obtained from a rate:
it comes from `Decay.decay_of_hkMem0_jetBound` — the weighted `ℋ⁰`-membership of the limit plus the
constant bounds on `D_zΨ`, `D_θΨ` and `Ψ` (which the limit inherits from the members' bounds).

The extraction/tower/identification part is the argument of the frozen
`ClosedCompact3_of_bounds_fatou`; the Fatou step is the `z`-local version
`Fatou.HkMem_fatou_z`; the Arzelà–Ascoli input is
`LimExtract.limExtract_bounds10_const`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.FatouH
import Submission.Work.FTS_EllLimOK.Fatou.HkMem_fatou_z
import Submission.Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const
import Submission.Work.FTS_EllLimOK.Decay.decay_of_hkMem0_jetBound
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.ClosedCompact3_of_bounds_fatou
import Submission.Work.FTS_EllLimOK.HkSq_le_of_JConv
import Submission.Work.FTS_EllLimOK.Assembly
import Submission.Work.FTS_EllLimOK.AssemblyAux
import Submission.Work.FTS_EllLimOK.DecayAux
import Submission.Work.FTS_EllLimOK.LimDefs10
import Submission.Work.FTS_EllLimOK.LimExtract_bounds10
import Submission.Work.FTS_EllLimOK.LimTower_dz3
import Submission.Work.FTS_EllLimOK.tower_jet_identities
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.HkMem_fatou
import Submission.Work.FTS_EllLimOK.continuousOn_HkIntegrand
import Submission.Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0
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

/-! ## The `ℋ⁰`-Fatou step in the `z`-local shape -/

/-- **Fatou for `ℋ⁰`, `z`-local form**: as `hkMem0_of_tendsto`, with the angular-slice hypothesis
only bounded by `C(1+1/z)`. -/
theorem hkMem0_of_tendsto_z {α C : ℝ} {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hMem : ∀ n, Work.Spaces.HkMem α 0 (un n))
    (hSq : ∀ n, Work.Spaces.HkSq α 0 (un n) ≤ C)
    (hTheta : ∀ n, ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (un n) z θ) ≤ C * (1 + 1 / z))
    (hcont : ∀ n, ContinuousOn (Function.uncurry (un n)) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => un n z θ) atTop (𝓝 (u z θ))) :
    Work.Spaces.HkMem α 0 u ∧ Work.Spaces.HkSq α 0 u ≤ C := by
  refine HkMem_fatou_z hMem hSq hTheta ?_ ?_
  · -- the a.e.-measurability of the integrand of the limit
    refine aemeasurable_uncurry_of_tendsto_Q0
      (un := fun n z θ => Work.Spaces.HkIntegrand α 0 (un n) z θ)
      (u := fun z θ => Work.Spaces.HkIntegrand α 0 u z θ) ?_ ?_
    · intro n
      refine continuousOn_HkIntegrand (k := 0) (fun j i hji => ?_)
      have hj : j = 0 := by omega
      have hi : i = 0 := by omega
      subst hj
      subst hi
      have h' : ContinuousOn (fun p : ℝ × ℝ => un n p.1 p.2) Work.FTS.EllipticEst.Q0 := hcont n
      exact h'
    · intro z θ hzθ
      refine tendsto_HkIntegrand_of_tendsto_mixed (k := 0)
        (fn := un) (f := u) (p := (z, θ)) (fun j i hji => ?_)
      have hj : j = 0 := by omega
      have hi : i = 0 := by omega
      subst hj
      subst hi
      have h' : Tendsto (fun n => un n z θ) atTop (𝓝 (u z θ)) := hconv z θ hzθ
      exact h'
  · intro j i hji z θ hzθ
    have hj : j = 0 := by omega
    have hi : i = 0 := by omega
    subst hj
    subst hi
    simpa using hconv z θ hzθ

/-! ## The main theorem -/

theorem ClosedCompact3H_of_bounds_fatou {α Ce : ℝ}
    (hbd : Work.FTS_EllLimOK.LocalBoundH α Ce) (hfat : Work.FTS_EllLimOK.FatouDataH α Ce)
    (hbox : Work.FTS_EllLimOK.BoxDataH α Ce) : Work.FTS_EllLimOK.ClosedCompact3H α Ce := by
  intro E hE fn f hL
  classical
  have hPkg : HasPkg α Ce E := hE.toHasPkg
  obtain ⟨C₄, hC₄pos, hb⟩ := hbd E hE fn f hL
  obtain ⟨C, hCpos, hseq, hseqc⟩ := hfat E hE fn f hL
  have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (E (fn n)) :=
    fun n => (hPkg (fn n) (hL.classC n)).2.smooth
  have hsol : ∀ n : ℕ, Work.FTS.StrongGlobal.IsBslSolPos α (fn n) (E (fn n)) :=
    fun n => (hPkg (fn n) (hL.classC n)).2.sol
  -- the constant pointwise bounds of `LocalBoundH`
  have hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C₄ := by
    intro n j i hji z θ hzθ
    exact hb n j i hji z θ hzθ
  -- the Arzelà–Ascoli extraction on the ten order-`≤ 3` jets
  obtain ⟨hbdd, heqc⟩ := Work.FTS_EllLimOK.LimExtract.limExtract_bounds10_const hsm hbnd
  obtain ⟨φ, hφ, g, hgl⟩ :=
    Work.FTS.StrongEps.LocUnif.exists_subseq_tendstoLocallyUniformlyOn_fin
      (U := Work.FTS.EllipticEst.Q0) Work.FTS.EllipticEst.isOpen_Q0
      (F := fun n p => fam10 (fun k => E (fn k)) n p) hbdd heqc
  let F : ℕ → ℕ → ℝ → ℝ → ℝ := fun c d z θ => g (z, θ) (idx10 c d)
  have hconv : ∀ (c d : ℕ), c + d ≤ 3 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0 := by
    intro c d hcd
    have h1 : TendstoLocallyUniformlyOn
        (fun n p => fam10 (fun k => E (fn k)) (φ n) p (idx10 c d))
        (fun p => g p (idx10 c d)) Filter.atTop Work.FTS.EllipticEst.Q0 := by
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact Work.FTS.EllipticEst.isOpen_Q0]
      intro K hKQ hK
      have h2 := Metric.tendstoUniformlyOn_iff.mp
        ((tendstoLocallyUniformlyOn_iff_forall_isCompact
          Work.FTS.EllipticEst.isOpen_Q0).mp hgl K hKQ hK)
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [h2 ε hε] with n hn p hp
      exact lt_of_le_of_lt (dist_le_pi_dist (g p)
        (fam10 (fun k => E (fn k)) (φ n) p) (idx10 c d)) (hn p hp)
    have h2 : (fun n p => fam10 (fun k => E (fn k)) (φ n) p (idx10 c d))
        = fun n p => Work.Spaces.mixed c d (E (fn (φ n))) p.1 p.2 := by
      funext n p
      simp only [fam10, idx10_spec hcd]
    have h3 : (fun p : ℝ × ℝ => g p (idx10 c d)) = fun p => F c d p.1 p.2 := by
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
  obtain ⟨hdz, hdth⟩ := LimTower_dz3 (G := fun k => E (fn k)) hsm hconv
  obtain ⟨hFc3, hident⟩ := LimTower_identify3 hcontF hdz hdth
  -- the limit function
  let Ψ : ℝ → ℝ → ℝ := fun z θ => if (z, θ) ∈ Work.FTS.EllipticEst.Q0 then F 0 0 z θ else 0
  have hΨfun : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ := by
    intro z θ hzθ
    simp only [Ψ]
    rw [ite_eq_left hzθ]
  have hvan : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0 := by
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
  have hjet : JConv3 (fun n => E (fn (φ n))) Ψ := by
    intro j i hji z θ hzθ
    have h1 : Tendsto (fun n => Work.Spaces.mixed j i (E (fn (φ n))) z θ) atTop (𝓝 (F j i z θ)) :=
      (hconv j i (by omega)).tendsto_at hzθ
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
  -- the closed-box regularity of the limit: on the non-degenerate boxes
  have hboxEq : ∀ a' b' : ℝ, 0 < a' → a' < b' → ∃ G : Fn,
      ContDiffOn ℝ 2 (Function.uncurry G) (cbox a' b') ∧
      (∀ z ∈ Set.Icc a' b', ∀ θ ∈ Set.Icc 0 (π / 2),
        Tendsto (fun n => E (fn n) z θ) atTop (nhds (G z θ))) ∧
      (∀ z ∈ Set.Icc a' b', G z 0 = 0 ∧ G z (π / 2) = 0) ∧
      Set.EqOn (Function.uncurry Ψ) (Function.uncurry G) (cbox a' b') := by
    intro a b ha hab
    obtain ⟨G, hGc, hGlim, hG0⟩ := hbox E hE fn f hL a b ha hab
    refine ⟨G, hGc, hGlim, hG0, ?_⟩
    have hEq : Set.EqOn (Function.uncurry Ψ) (Function.uncurry G) (cbox a b) := by
      intro p hp
      obtain ⟨hza, hzb⟩ := hp.1
      obtain ⟨hθ0, hθ1⟩ := hp.2
      rcases lt_or_eq_of_le hθ0 with hθ0' | hθ0''
      · rcases lt_or_eq_of_le hθ1 with hθ1' | hθ1''
        · -- an interior point of the box: both functions are limits of the same sequence
          have hzpos : 0 < p.1 := lt_of_lt_of_le ha hza
          have hQ0 : (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 :=
            Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ0', hθ1'⟩
          have h1 : Tendsto (fun n => E (fn (φ n)) p.1 p.2) atTop (𝓝 (G p.1 p.2)) :=
            (hGlim p.1 ⟨hza, hzb⟩ p.2 ⟨le_of_lt hθ0', le_of_lt hθ1'⟩).comp hφ.tendsto_atTop
          have h2 : Tendsto (fun n => E (fn (φ n)) p.1 p.2) atTop (𝓝 (F 0 0 p.1 p.2)) :=
            (hconv 0 0 (by norm_num)).tendsto_at hQ0
          have hEqp : F 0 0 p.1 p.2 = G p.1 p.2 := tendsto_nhds_unique h2 h1
          show Ψ p.1 p.2 = G p.1 p.2
          rw [hΨfun p.1 p.2 hQ0, hEqp]
        · -- the angular endpoint `θ = π/2`: both sides vanish
          have hΨp : Ψ p.1 (π / 2) = 0 := hvan p.1 (π / 2) (by simp)
          have hGp : G p.1 (π / 2) = 0 := (hG0 p.1 ⟨hza, hzb⟩).2
          show Ψ p.1 p.2 = G p.1 p.2
          rw [hθ1'', hΨp, hGp]
      · -- the angular endpoint `θ = 0`: both sides vanish
        have hΨp : Ψ p.1 0 = 0 := hvan p.1 0 (by simp)
        have hGp : G p.1 0 = 0 := (hG0 p.1 ⟨hza, hzb⟩).1
        show Ψ p.1 p.2 = G p.1 p.2
        rw [← hθ0'', hΨp, hGp]
    exact hEq

  have hboxΨ : BoxReg Ψ := by
    intro a b ha hab
    rcases lt_or_eq_of_le hab with hlt | heq
    · obtain ⟨G, hGc, -, -, hEq⟩ := hboxEq a b ha hlt
      intro p hp
      exact (hGc.contDiffWithinAt hp).congr_of_eventuallyEq_of_mem
        (hEq.eventuallyEq_of_mem self_mem_nhdsWithin) hp
    · subst heq
      obtain ⟨G, hGc, -, -, hEq⟩ := hboxEq a (a + 1) ha (by linarith)
      have h1 : ContDiffOn ℝ 2 (Function.uncurry Ψ) (cbox a (a + 1)) := hGc.congr hEq
      intro p hp
      exact (h1 p ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩).mono
        fun q hq => ⟨⟨hq.1.1, by linarith [hq.1.2]⟩, hq.2⟩
  -- the far-field decay of the limit (no rate available: the weighted membership + the constant
  -- first-order bounds are enough)
  have hdec : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
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
      exact bslOp_eq_of_convergence
        ⟨LimExtract_bounds, LimTower_dz, SmoothOpen_tower, LimTower_identify, LimTower_c2,
          BslOp_tower⟩ hsm hsol (fun c d hcd => hconv c d (by omega))
        (fun c d hcd => hdz c d (by omega)) (fun c d hcd => hdth c d (by omega))
        htriv hfsrc (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩)
    · intro z _
      exact hvan z 0 (by simp)
    · intro z _
      exact hvan z (π / 2) (by simp)
    · intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | h0
      · subst h0
        have hf : (fun z : ℝ => Ψ z 0) = fun _ => (0 : ℝ) := funext fun z => hvan z 0 (by simp)
        rw [hf]
        exact tendsto_const_nhds
      · rcases eq_or_lt_of_le hθ.2 with h1 | h1
        · subst h1
          have hf : (fun z : ℝ => Ψ z (π / 2)) = fun _ => (0 : ℝ) :=
            funext fun z => hvan z (π / 2) (by simp)
          rw [hf]
          exact tendsto_const_nhds
        · exact hdec θ ⟨h0, h1⟩
  exact ⟨Ψ, ⟨⟨hsolf, hc3, hM1, hM5, hboxΨ⟩, ⟨φ, hφ.tendsto_atTop, hjet⟩⟩⟩

end Work.FTS_EllLimOK
