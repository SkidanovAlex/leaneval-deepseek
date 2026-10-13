/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.ClosedCompact3_of_bounds_fatou` — obligation 1 at order 3

The order-`3` compactness obligation `ClosedCompact3 α Ce` (the first half of the ruling §G5
deliverable) follows from the two sequence-level hypotheses isolated in `Defs3`:

* `LocalBound4 α Ce` — pointwise growth bounds of the jets of order `≤ 4` along every `LimSeq4`
  (this makes the order-`≤ 3` jets equicontinuous on compacta, so that Arzelà–Ascoli extracts a
  cofinal reindexing along which the order-`≤ 3` jets converge locally uniformly);
* `FatouData α Ce` — the uniform, sequence-level `ℋ⁰`/`L²` memberships, the uniform `θ`- and
  `z`-integral bounds, and the far-field decay `(1+z)^{3/2}|D_z^jD_θ^iΨ_n| ≤ C` (`j+i ≤ 2`),
  from which the *limit* inherits its Fatou package.

The proof is the order-`3` transplant of the order-`2` assembly
(`Assembly.closedCompact_of_children`): the extraction runs on the ten order-`≤ 3` jets
(`fam10`), the tower relations and the identification of the limits with the jets of the limit
function are the order-`3` versions of the sibling modules, and the Fatou package of the limit
is obtained by Fatou's lemma (once in `θ`, once in `z`) from the sequence-level data.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_EllLimOK.Defs3
import Submission.Work.FTS_EllLimOK.Closed3
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
import Submission.Work.FTS_EllLimOK.ZDecay_of_decay_bounds
import Submission.Work.FTS_EllLimOK.L2Mem_of_HkMem_zero
import Submission.Work.FTS_EllLimOK.continuousOn_HkIntegrand
import Submission.Work.FTS_EllLimOK.aemeasurable_uncurry_of_tendsto_Q0
import Submission.Work.FTS_EllLimOK.aemeasurable_slice_of_tendsto_Ioo
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

/-! ## The `ℋ⁰`-Fatou step, in the shape used below -/

/-- **Fatou for `ℋ⁰`.**  If every member of the sequence is in `ℋ⁰` with uniformly bounded
energy and uniformly bounded `θ`-integrals, if the integrands of the limit are a.e. measurable
on the quadrant, and if the members converge pointwise on the open quadrant, then the limit is
in `ℋ⁰` with the same energy bound. -/
theorem hkMem0_of_tendsto {α C : ℝ} {un : ℕ → ℝ → ℝ → ℝ} {u : ℝ → ℝ → ℝ}
    (hMem : ∀ n, Work.Spaces.HkMem α 0 (un n))
    (hSq : ∀ n, Work.Spaces.HkSq α 0 (un n) ≤ C)
    (hTheta : ∀ n, ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (un n) z θ) ≤ C)
    (hcont : ∀ n, ContinuousOn (Function.uncurry (un n)) Work.FTS.EllipticEst.Q0)
    (hconv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => un n z θ) atTop (𝓝 (u z θ))) :
    Work.Spaces.HkMem α 0 u ∧ Work.Spaces.HkSq α 0 u ≤ C := by
  refine HkMem_fatou hMem hSq hTheta ?_ ?_
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

theorem ClosedCompact3_of_bounds_fatou {α Ce : ℝ}
    (hbd : Work.FTS_EllLimOK.LocalBound4 α Ce) (hfat : Work.FTS_EllLimOK.FatouData α Ce) :
    Work.FTS_EllLimOK.ClosedCompact3 α Ce := by
  intro E hE fn f hL
  classical
  obtain ⟨C₄, hC₄pos, hb⟩ := hbd E hE fn f hL
  obtain ⟨hfat₁, hboxdata⟩ := hfat
  obtain ⟨C, hCpos, hHkB, hHkSq, hThetaB, hL2a, hL2b, hL2c, hdec⟩ := hfat₁ E hE fn f hL
  have hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (E (fn n)) :=
    fun n => (hE (fn n) (hL.classC n)).2.smooth
  have hsol : ∀ n : ℕ, Work.FTS.StrongGlobal.IsBslSolPos α (fn n) (E (fn n)) :=
    fun n => (hE (fn n) (hL.classC n)).2.sol
  -- the pointwise bounds of `LocalBound4`, in the form of the weight `wt`
  have hbnd : ∀ (n : ℕ) (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C₄ * wt z θ := by
    intro n j i hji z θ hzθ
    have h' := hb n j i hji z θ hzθ
    rw [mul_div_assoc] at h'
    simpa only [wt] using h'
  -- the Arzelà–Ascoli extraction on the ten order-`≤ 3` jets
  obtain ⟨hbdd, heqc⟩ := LimExtract_bounds10 hsm hbnd
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
  -- the `θ`-derivative identities of the limit and of the sequence members
  have hidΨ : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz Ψ z θ = F 1 0 z θ / z ∧
      Work.Spaces.pth Ψ z θ = F 0 1 z θ / Real.sin (2 * θ) ∧
      Work.Spaces.pzIter 2 Ψ z θ = (F 2 0 z θ - F 1 0 z θ) / z ^ 2 ∧
      Work.Spaces.pthIter 2 Ψ z θ
        = (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2 :=
    tower_jet_identities htriv (fun c d hcd => hdz c d (by omega))
      (fun c d hcd => hdth c d (by omega))
  have hidSeq : ∀ n : ℕ, ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Spaces.pz (E (fn (φ n))) z θ = Work.Spaces.mixed 1 0 (E (fn (φ n))) z θ / z ∧
      Work.Spaces.pth (E (fn (φ n))) z θ
        = Work.Spaces.mixed 0 1 (E (fn (φ n))) z θ / Real.sin (2 * θ) ∧
      Work.Spaces.pzIter 2 (E (fn (φ n))) z θ
        = (Work.Spaces.mixed 2 0 (E (fn (φ n))) z θ
            - Work.Spaces.mixed 1 0 (E (fn (φ n))) z θ) / z ^ 2 ∧
      Work.Spaces.pthIter 2 (E (fn (φ n))) z θ
        = (Work.Spaces.mixed 0 2 (E (fn (φ n))) z θ
            - 2 * Real.cos (2 * θ) * Work.Spaces.mixed 0 1 (E (fn (φ n))) z θ)
          / (Real.sin (2 * θ)) ^ 2 := by
    intro n
    exact tower_jet_identities (F := fun c d => Work.Spaces.mixed c d (E (fn (φ n))))
      (fun z θ _ => rfl) (SmoothOpen_tower (hsm (φ n))).1 (SmoothOpen_tower (hsm (φ n))).2
  -- the far-field decay of the limit's jets
  have hFdec : ∀ (j i : ℕ), j + i ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      (1 + z) ^ ((3 : ℝ) / 2) * |F j i z θ| ≤ C := by
    intro j i hji z θ hzθ
    have hlim : Tendsto (fun n => (1 + z) ^ ((3 : ℝ) / 2)
        * |Work.Spaces.mixed j i (E (fn (φ n))) z θ|) atTop
        (𝓝 ((1 + z) ^ ((3 : ℝ) / 2) * |F j i z θ|)) :=
      ((hconv j i (by omega)).tendsto_at hzθ).abs.const_mul _
    refine le_of_tendsto_of_tendsto' hlim tendsto_const_nhds (fun n => ?_)
    exact hdec (φ n) j i hji z θ hzθ
  -- the pointwise convergence of the five quantities
  have hPsiConv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => E (fn (φ n)) z θ) atTop (𝓝 (Ψ z θ)) := by
    intro z θ hzθ
    have h : Tendsto (fun n => Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ) atTop
        (𝓝 (F 0 0 z θ)) := (hconv 0 0 (by norm_num)).tendsto_at hzθ
    rw [hΨfun z θ hzθ]
    simpa using h
  have hpthConv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => Work.Spaces.pth (E (fn (φ n))) z θ) atTop
        (𝓝 (Work.Spaces.pth Ψ z θ)) := by
    intro z θ hzθ
    have heq : (fun n => Work.Spaces.pth (E (fn (φ n))) z θ)
        = fun n => Work.Spaces.mixed 0 1 (E (fn (φ n))) z θ / Real.sin (2 * θ) := by
      funext n; exact (hidSeq n z θ hzθ).2.1
    rw [heq, (hidΨ z θ hzθ).2.1]
    exact ((hconv 0 1 (by norm_num)).tendsto_at hzθ).div_const _
  have hpth2Conv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => Work.Spaces.pthIter 2 (E (fn (φ n))) z θ) atTop
        (𝓝 (Work.Spaces.pthIter 2 Ψ z θ)) := by
    intro z θ hzθ
    have heq : (fun n => Work.Spaces.pthIter 2 (E (fn (φ n))) z θ)
        = fun n => (Work.Spaces.mixed 0 2 (E (fn (φ n))) z θ
            - 2 * Real.cos (2 * θ) * Work.Spaces.mixed 0 1 (E (fn (φ n))) z θ)
          / (Real.sin (2 * θ)) ^ 2 := by
      funext n; exact (hidSeq n z θ hzθ).2.2.2
    rw [heq, (hidΨ z θ hzθ).2.2.2]
    exact (((hconv 0 2 (by norm_num)).tendsto_at hzθ).sub
      (((hconv 0 1 (by norm_num)).tendsto_at hzθ).const_mul (2 * Real.cos (2 * θ)))).div_const _
  have hz2Conv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => z ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) z θ) atTop
        (𝓝 (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) := by
    intro z θ hzθ
    have hzpos : 0 < z := (Work.FTS.EllipticEst.mem_Q0.mp hzθ).1
    have heq : (fun n => z ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) z θ)
        = fun n => (Work.Spaces.mixed 2 0 (E (fn (φ n))) z θ
            - Work.Spaces.mixed 1 0 (E (fn (φ n))) z θ) := by
      funext n
      rw [(hidSeq n z θ hzθ).2.2.1]
      exact mul_div_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hzpos))
    have hlim : z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ = F 2 0 z θ - F 1 0 z θ := by
      rw [(hidΨ z θ hzθ).2.2.1]
      exact mul_div_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hzpos))
    rw [heq, hlim]
    exact ((hconv 2 0 (by norm_num)).tendsto_at hzθ).sub
      ((hconv 1 0 (by norm_num)).tendsto_at hzθ)
  have hcosq : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have hcosConv : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Tendsto (fun n => E (fn (φ n)) z θ / Real.cos θ) atTop (𝓝 (Ψ z θ / Real.cos θ)) :=
    fun z θ hzθ => (hPsiConv z θ hzθ).div_const _
  -- (1) `HkMem α 0 Ψ`
  have hM1 : Work.Spaces.HkMem α 0 Ψ :=
    (hkMem0_of_tendsto (C := C) (un := fun n z θ => E (fn (φ n)) z θ) (u := Ψ)
      (fun n => (hHkB (φ n)).1) (fun n => (hHkSq (φ n)).1) (fun n => (hThetaB (φ n)).1)
      (fun n => (hsm (φ n)).continuousOn) hPsiConv).1
  -- (2) `HkMem α 0 (pth Ψ)`
  have hM2 : Work.Spaces.HkMem α 0 (Work.Spaces.pth Ψ) :=
    (hkMem0_of_tendsto (C := C) (un := fun n z θ => Work.Spaces.pth (E (fn (φ n))) z θ)
      (u := Work.Spaces.pth Ψ)
      (fun n => (hHkB (φ n)).2.1) (fun n => (hHkSq (φ n)).2.1)
      (fun n => (hThetaB (φ n)).2.1)
      (fun n => ((hsm (φ n)).pth).continuousOn) hpthConv).1
  -- (3) `HkMem α 0 (pthIter 2 Ψ)`
  have hM3 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) :=
    (hkMem0_of_tendsto (C := C)
      (un := fun n z θ => Work.Spaces.pthIter 2 (E (fn (φ n))) z θ)
      (u := Work.Spaces.pthIter 2 Ψ)
      (fun n => (hHkB (φ n)).2.2.1) (fun n => (hHkSq (φ n)).2.2.1)
      (fun n => (hThetaB (φ n)).2.2.1)
      (fun n => ((hsm (φ n)).pth.pth).continuousOn) hpth2Conv).1
  -- (4) `HkMem α 0 (z ↦ z² pzIter 2 Ψ)`
  have hM4 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    (hkMem0_of_tendsto (C := C)
      (un := fun n z θ => z ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) z θ)
      (u := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
      (fun n => (hHkB (φ n)).2.2.2.1) (fun n => (hHkSq (φ n)).2.2.2.1)
      (fun n => (hThetaB (φ n)).2.2.2.1)
      (fun n => by
        have h' : ContinuousOn
            (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) p.1 p.2)
            Work.FTS.EllipticEst.Q0 :=
          (continuousOn_fst.pow 2).mul ((hsm (φ n)).pzIter 2 |>.continuousOn)
        exact h')
      hz2Conv).1
  -- (5) `HkMem α 0 (Ψ/cos θ)`
  have hM5 : Work.Spaces.HkMem α 0 (fun z θ => Ψ z θ / Real.cos θ) :=
    (hkMem0_of_tendsto (C := C)
      (un := fun n z θ => E (fn (φ n)) z θ / Real.cos θ)
      (u := fun z θ => Ψ z θ / Real.cos θ)
      (fun n => (hHkB (φ n)).2.2.2.2) (fun n => (hHkSq (φ n)).2.2.2.2)
      (fun n => (hThetaB (φ n)).2.2.2.2)
      (fun n => (hsm (φ n)).continuousOn.div ((Real.continuous_cos.comp continuous_snd).continuousOn) hcosq)
      hcosConv).1
  -- the three `L2Mem` memberships
  have hΨ0 : ∀ θ : ℝ, Ψ 0 θ = 0 := by
    intro θ
    simp only [Ψ]
    rw [ite_eq_right (show (0, θ) ∉ Work.FTS.EllipticEst.Q0 from
      fun hmem => absurd hmem.1 (lt_irrefl (0 : ℝ)))]
  have hpth0 : ∀ θ : ℝ, Work.Spaces.pth Ψ 0 θ = 0 := by
    intro θ
    have hf : (fun θ' : ℝ => Ψ 0 θ') = fun _ => (0 : ℝ) := funext fun θ' => hΨ0 θ'
    rw [Work.Spaces.pth, hf, deriv_const]
  have hl2_3 : Work.Spaces.L2Mem (Work.Spaces.pthIter 2 Ψ) := by
    refine L2Mem_of_HkMem_zero hM3 ?_ ?_ ?_
    · intro θ
      show deriv (fun θ' : ℝ => Work.Spaces.pth Ψ 0 θ') θ = 0
      have hf : (fun θ' : ℝ => Work.Spaces.pth Ψ 0 θ') = fun _ => (0 : ℝ) :=
        funext fun θ' => hpth0 θ'
      rw [hf, deriv_const]
    · refine aemeasurable_uncurry_of_tendsto_Q0
        (un := fun n z θ => Work.Spaces.pthIter 2 (E (fn (φ n))) z θ)
        (u := fun z θ => Work.Spaces.pthIter 2 Ψ z θ)
        (fun n => ((hsm (φ n)).pth.pth).continuousOn) ?_
      intro z θ hzθ
      exact hpth2Conv z θ hzθ
    · intro z hz
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
      · subst h0
        have hf : (fun θ : ℝ => Work.Spaces.pthIter 2 Ψ 0 θ) = fun _ => (0 : ℝ) := by
          funext θ
          show deriv (fun θ' : ℝ => Work.Spaces.pth Ψ 0 θ') θ = 0
          have hf' : (fun θ' : ℝ => Work.Spaces.pth Ψ 0 θ') = fun _ => (0 : ℝ) :=
            funext fun θ' => hpth0 θ'
          rw [hf', deriv_const]
        rw [hf]
        exact aemeasurable_const
      · refine aemeasurable_slice_of_tendsto_Ioo
          (un := fun n θ => Work.Spaces.pthIter 2 (E (fn (φ n))) z θ)
          (u := fun θ => Work.Spaces.pthIter 2 Ψ z θ) (fun n => ?_) ?_
        · exact (((hsm (φ n)).pth.pth).curry_θ hzpos).continuousOn
        · intro θ hθ
          exact hpth2Conv z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)
  have hl2_4 : Work.Spaces.L2Mem (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) := by
    refine L2Mem_of_HkMem_zero hM4 ?_ ?_ ?_
    · intro θ
      show (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ = 0
      simp
    · refine aemeasurable_uncurry_of_tendsto_Q0
        (un := fun n z θ => z ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) z θ)
        (u := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (fun n => by
          have h' : ContinuousOn
              (fun p : ℝ × ℝ => p.1 ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) p.1 p.2)
              Work.FTS.EllipticEst.Q0 :=
            (continuousOn_fst.pow 2).mul ((hsm (φ n)).pzIter 2 |>.continuousOn)
          exact h') ?_
      intro z θ hzθ
      exact hz2Conv z θ hzθ
    · intro z hz
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
      · subst h0
        have hf : (fun θ : ℝ => (0 : ℝ) ^ 2 * Work.Spaces.pzIter 2 Ψ 0 θ) = fun _ => (0 : ℝ) := by
          funext θ; simp
        rw [hf]
        exact aemeasurable_const
      · refine aemeasurable_slice_of_tendsto_Ioo
          (un := fun n θ => z ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) z θ)
          (u := fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (fun n => ?_) ?_
        · have h' : ContinuousOn
              (fun θ : ℝ => z ^ 2 * Work.Spaces.pzIter 2 (E (fn (φ n))) z θ)
              (Set.Ioo (0 : ℝ) (π / 2)) :=
            continuousOn_const.mul ((((hsm (φ n)).pzIter 2).curry_θ hzpos).continuousOn)
          exact h'
        · intro θ hθ
          exact hz2Conv z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)
  have hl2_5 : Work.Spaces.L2Mem (fun z θ => Ψ z θ / Real.cos θ) := by
    refine L2Mem_of_HkMem_zero hM5 ?_ ?_ ?_
    · intro θ
      show Ψ 0 θ / Real.cos θ = 0
      rw [hΨ0 θ, zero_div]
    · refine aemeasurable_uncurry_of_tendsto_Q0
        (un := fun n z θ => E (fn (φ n)) z θ / Real.cos θ)
        (u := fun z θ => Ψ z θ / Real.cos θ)
        (fun n => (hsm (φ n)).continuousOn.div ((Real.continuous_cos.comp continuous_snd).continuousOn) hcosq) ?_
      intro z θ hzθ
      exact hcosConv z θ hzθ
    · intro z hz
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
      · subst h0
        have hf : (fun θ : ℝ => Ψ 0 θ / Real.cos θ) = fun _ => (0 : ℝ) := by
          funext θ; rw [hΨ0 θ, zero_div]
        rw [hf]
        exact aemeasurable_const
      · refine aemeasurable_slice_of_tendsto_Ioo
          (un := fun n θ => E (fn (φ n)) z θ / Real.cos θ)
          (u := fun θ => Ψ z θ / Real.cos θ) (fun n => ?_) ?_
        · refine (((hsm (φ n)).curry_θ hzpos).continuousOn.div
            (Real.continuous_cos.continuousOn) (fun θ hθ => ?_))
          exact ne_of_gt (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
        · intro θ hθ
          exact hcosConv z θ (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hzpos, hθ.1, hθ.2⟩)
  -- the boundary decay
  have hZ : Work.FTS.EllipticEst.ZDecay Ψ :=
    ZDecay_of_decay_bounds hCpos.le hΨfun hidΨ hvan hFdec
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
        · refine decay_of_wt_bound hC₄pos.le h0 h1 fun z hz => ?_
          have hzθ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
            Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, h0, h1⟩
          rw [hΨfun z θ hzθ]
          have hlim : Tendsto (fun n => |Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ|) atTop
              (𝓝 |F 0 0 z θ|) := ((hconv 0 0 (by norm_num)).tendsto_at hzθ).abs
          have hle : ∀ n : ℕ,
              |Work.Spaces.mixed 0 0 (E (fn (φ n))) z θ| ≤ C₄ * wt z θ :=
            fun n => hbnd (φ n) 0 0 (by norm_num) z θ hzθ
          exact le_of_tendsto_of_tendsto' hlim tendsto_const_nhds hle
  -- the closed-box regularity of the limit (the `θ`-boundary data of obligation 1)
  have hboxΨ : BoxReg Ψ := by
    intro a b ha hab
    obtain ⟨G, hGc, hGlim, hG0⟩ := hboxdata E hE fn f hL a b ha hab
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
    intro p hp
    exact (hGc.contDiffWithinAt hp).congr_of_eventuallyEq_of_mem
      (hEq.eventuallyEq_of_mem self_mem_nhdsWithin) hp
  exact ⟨Ψ, ⟨⟨hsolf, hc3, hM1, hM2, hM3, hM4, hM5, hl2_3, hl2_4, hl2_5, hZ, hboxΨ⟩,
    ⟨φ, hφ.tendsto_atTop, hjet⟩⟩⟩

end Work.FTS_EllLimOK
