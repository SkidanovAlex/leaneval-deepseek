import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.C.rgrad_rdist_eikonal
import Submission.Work.Diff.C.eikonal_of_inj_v2
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.Dim2.flow_shift
import Submission.Work.OddBound.sqDistChart.sqDist_contDiffAt_charts

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

/-! ### Auxiliary smoothness lemmas about a jointly smooth flow family `Φ` -/

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A flow line of a jointly smooth flow family is smooth. -/
lemma contMDiffAt_flowline {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2)) (x : M) (s : ℝ) :
    ContMDiffAt 𝓘(ℝ,ℝ) I ∞ (fun τ : ℝ => Φ 0 τ x) s := by
  have hp1 : ContMDiffAt 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
      (fun τ : ℝ => (((0 : ℝ), τ) : ℝ × ℝ)) s :=
    (contMDiffAt_const (c := (0 : ℝ))).prodMk contMDiffAt_id
  have hp2 : ContMDiffAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
      (fun τ : ℝ => ((((0 : ℝ), τ) : ℝ × ℝ), x)) s :=
    hp1.prodMk (contMDiffAt_const (c := x))
  exact (hΦsm.contMDiffAt (x := ((((0 : ℝ), s) : ℝ × ℝ), x))).comp s hp2

/-- Negation composed with a smooth real-valued function is smooth. -/
lemma contMDiffAt_neg_comp {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ f x) :
    ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun z : M => -(f z)) x := by
  have hL : ContMDiffAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (-ContinuousLinearMap.id ℝ ℝ) (f x) :=
    (ContinuousLinearMap.contMDiff (-ContinuousLinearMap.id ℝ ℝ)).contMDiffAt
  refine (hL.comp x hf).congr_of_eventuallyEq ?_
  filter_upwards with z
  simp

/-- The map `z ↦ Φ 0 (-(τ z)) z` is smooth where `τ` is. -/
lemma contMDiffAt_flow_pair {Φ : ℝ → ℝ → M → M} {τ : M → ℝ} {x : M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hτ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ τ x) :
    ContMDiffAt I I ∞ (fun z : M => Φ 0 (-(τ z)) z) x := by
  have hneg : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ (fun z : M => -(τ z)) x := contMDiffAt_neg_comp hτ
  have hpair : ContMDiffAt I ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
      (fun z : M => ((((0 : ℝ), -(τ z)) : ℝ × ℝ), z)) x :=
    ((contMDiffAt_const (c := (0 : ℝ))).prodMk hneg).prodMk contMDiffAt_id
  have h1 : ContMDiffAt I I ∞
      ((fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∘
        (fun z : M => ((((0 : ℝ), -(τ z)) : ℝ × ℝ), z))) x :=
    ContMDiffAt.comp x (hΦsm.contMDiffAt) hpair
  exact h1

theorem label_u
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p q : M} {Φp : M → TangentSpace I p} {v ρ a γ : ℝ}
    (ha : 0 < a) (hρ0 : 0 < ρ) (haρ : a < ρ) (hρv : ρ ≤ v)
    (hsm : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < v →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y)
    (hnorm : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
      Work.Diff.C.rdist (I := I) (M := M) p y = ‖Φp y‖)
    (hround : ∀ w : TangentSpace I p, ‖w‖ < ρ →
      Φp (Submission.GlobalExp.GExp (cov := cov) hmet p w) = w)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    (hval : ∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y ≤ 3 * a / 2 →
      V y = Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y)
    (hrad : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 →
      Φ 0 (-(Work.Diff.C.rdist (I := I) (M := M) p x - a)) x =
        Submission.GlobalExp.GExp (cov := cov) hmet p
          (a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x)))
    {τ : M → ℝ}
    (hτsm : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ τ
      {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x})
    (hτval : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2 →
      τ x = Work.Diff.C.rdist (I := I) (M := M) p x - a)
    (hτcoc : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ∀ s : ℝ, 0 ≤ s →
      a / 4 < Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x) →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) →
      τ (Φ 0 s x) = τ x + s)
    (hτa : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-(τ x)) x) = a) :
    ∃ u : M → TangentSpace I p,
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ u x) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ‖u x‖ = 1) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
        mfderiv I 𝓘(ℝ, TangentSpace I p) u x (V x) = 0) ∧
      (∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
        Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 →
        u x = (Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x) := by
  classical
  -- ### Step 0: `GExp p` is injective on the ball of radius `ρ`.
  have hinj : Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet p ρ := by
    intro u v hu hv huv
    have h1 : Φp (Submission.GlobalExp.GExp (cov := cov) hmet p u) = u := hround u hu
    have h2 : Φp (Submission.GlobalExp.GExp (cov := cov) hmet p v) = v := hround v hv
    rw [huv] at h1
    exact h1.symm.trans h2
  -- ### Step 1: `Φp` is a right inverse of `GExp p` on `{rdist p · < ρ}`.
  have hright : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < ρ →
      Submission.GlobalExp.GExp (cov := cov) hmet p (Φp y) = y := by
    intro y hy
    obtain ⟨w, hwG, hwd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p y
    have hw : ‖w‖ = Work.Diff.C.rdist (I := I) (M := M) p y := by
      rw [Work.Diff.C.rdist, hwd, ENNReal.toReal_ofReal (norm_nonneg w)]
    have hwρ : ‖w‖ < ρ := hw ▸ hy
    have hΦ : Φp y = w := by rw [← hwG, hround w hwρ]
    rw [hΦ]
    exact hwG
  -- ### Step 2: `Φp` is smooth on `{0 < rdist p · < ρ}`.
  have hsmooth : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < ρ →
      ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ Φp y := by
    intro y _hy0 hyρ
    obtain ⟨w, hwG, hwd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p y
    have hw : ‖w‖ = Work.Diff.C.rdist (I := I) (M := M) p y := by
      rw [Work.Diff.C.rdist, hwd, ENNReal.toReal_ofReal (norm_nonneg w)]
    have hwρ : ‖w‖ < ρ := hw ▸ hyρ
    have hinv : (mfderiv 𝓘(ℝ, E) I (Submission.XuLift.gexpMap (cov := cov) hmet p)
        (show E from w)).IsInvertible := by
      show (mfderiv 𝓘(ℝ, E) I
        (fun u : E => Submission.GlobalExp.GExp (cov := cov) hmet p u)
        (show E from w)).IsInvertible
      exact Work.OddBound.sqDistChart.isInvertible_mfderiv_GExp_of_norm_lt (I := I) (cov := cov)
        hmet htor hinj hwρ
    obtain ⟨Φloc, hΦlocsm, hΦlocy, hΦlocG⟩ :=
      Work.Diff.C.eik_v2_localInverse_GExp (I := I) (cov := cov) hmet p hwG hinv
    refine hΦlocsm.congr_of_eventuallyEq ?_
    have hcf : ContinuousAt (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y :=
      (Work.Diff.C.rdist_continuous (I := I) (M := M) p).continuousAt
    have hcΦ : ContinuousAt Φloc y := hΦlocsm.continuousAt
    have h1 : ∀ᶠ z in 𝓝 y, Work.Diff.C.rdist (I := I) (M := M) p z < ρ :=
      hcf.eventually (isOpen_Iio.mem_nhds hyρ)
    have h2 : ∀ᶠ z in 𝓝 y, ‖Φloc z‖ < ρ :=
      hcΦ.norm.eventually (isOpen_Iio.mem_nhds (by simpa [hΦlocy] using hwρ))
    filter_upwards [h1, h2, hΦlocG] with z hzρ hzΦ hzG
    have hnormΦp : ‖Φp z‖ = Work.Diff.C.rdist (I := I) (M := M) p z :=
      (hnorm z (lt_of_lt_of_le hzρ hρv)).symm
    have hz1 : Submission.GlobalExp.GExp (cov := cov) hmet p (Φp z) = z := hright z hzρ
    have hz2 : ‖Φp z‖ < ρ := by rw [hnormΦp]; exact hzρ
    have hG : Submission.GlobalExp.GExp (cov := cov) hmet p (Φp z) =
        Submission.GlobalExp.GExp (cov := cov) hmet p (Φloc z) := by rw [hz1, hzG]
    exact hinj (Φp z) (Φloc z) hz2 hzΦ hG
  -- ### Clause 1: smoothness of the label field.
  have hsm_u : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞
        (fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) x := by
    intro x hx1 hx2
    have hS : {y : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p y ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q y} ∈ 𝓝 x := by
      have h1 : {y : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p y} ∈ 𝓝 x :=
        ((Work.Diff.C.rdist_continuous (I := I) (M := M) p).isOpen_preimage _
          isOpen_Ioi).mem_nhds hx1
      have h2 : {y : M | γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q y} ∈ 𝓝 x :=
        ((Work.Diff.C.rdist_continuous (I := I) (M := M) q).isOpen_preimage _
          isOpen_Ioi).mem_nhds hx2
      exact Filter.inter_mem h1 h2
    have hτx : ContMDiffAt I 𝓘(ℝ,ℝ) ∞ τ x := hτsm.contMDiffAt hS
    have harg : ContMDiffAt I I ∞ (fun z : M => Φ 0 (-(τ z)) z) x :=
      contMDiffAt_flow_pair (I := I) (Φ := Φ) (τ := τ) hΦsm hτx
    have hfx : Work.Diff.C.rdist (I := I) (M := M) p
        ((fun z : M => Φ 0 (-(τ z)) z) x) = a := by
      simpa using hτa x hx1 hx2
    have hΦp_sm : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ Φp
        ((fun z : M => Φ 0 (-(τ z)) z) x) :=
      hsmooth _ (by rw [hfx]; exact ha) (by rw [hfx]; exact haρ)
    have hcomp : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞
        (Φp ∘ (fun z : M => Φ 0 (-(τ z)) z)) x :=
      ContMDiffAt.comp x hΦp_sm harg
    have hclm : ContMDiffAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ, TangentSpace I p) ∞
        ((a⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (TangentSpace I p))
        (Φp ((fun z : M => Φ 0 (-(τ z)) z) x)) :=
      (ContinuousLinearMap.contMDiff
        ((a⁻¹ : ℝ) • ContinuousLinearMap.id ℝ (TangentSpace I p))).contMDiffAt
    exact ContMDiffAt.comp x hclm hcomp
  -- ### Clause 2: the label field is unit.
  have hunit : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ‖a⁻¹ • Φp (Φ 0 (-(τ x)) x)‖ = 1 := by
    intro x hx1 hx2
    have hw : Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 (-(τ x)) x) = a := hτa x hx1 hx2
    have hn : ‖Φp (Φ 0 (-(τ x)) x)‖ = a := by
      have h := hnorm (Φ 0 (-(τ x)) x) (by rw [hw]; exact lt_of_lt_of_le haρ hρv)
      rw [← h, hw]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), hn]
    exact inv_mul_cancel₀ (ne_of_gt ha)
  -- ### Clause 3: the label field is constant along the flow, hence `du(V) = 0`.
  have hconst : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ, TangentSpace I p)
        (fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) x (V x) = 0 := by
    intro x hx1 hx2
    have hcontφ : ContinuousAt (fun s : ℝ => Φ 0 s x) 0 :=
      (contMDiffAt_flowline (I := I) (Φ := Φ) hΦsm x 0).continuousAt
    have hcontf : ContinuousAt
        (fun s : ℝ => Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x)) 0 :=
      (Work.Diff.C.rdist_continuous (I := I) (M := M) p).continuousAt.comp hcontφ
    have hcontg : ContinuousAt
        (fun s : ℝ => Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x)) 0 :=
      (Work.Diff.C.rdist_continuous (I := I) (M := M) q).continuousAt.comp hcontφ
    have hev1 : ∀ᶠ s in 𝓝 (0 : ℝ),
        a / 4 < Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s x) :=
      hcontf.eventually (isOpen_Ioi.mem_nhds (by simpa [hΦself 0 x] using hx1))
    have hev2 : ∀ᶠ s in 𝓝 (0 : ℝ),
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 s x) :=
      hcontg.eventually (isOpen_Ioi.mem_nhds (by simpa [hΦself 0 x] using hx2))
    have hshift : (fun s : ℝ => a⁻¹ • Φp (Φ 0 (-(τ (Φ 0 s x))) (Φ 0 s x)))
        =ᶠ[𝓝 (0 : ℝ)] (fun _ => a⁻¹ • Φp (Φ 0 (-(τ x)) x)) := by
      filter_upwards [hev1, hev2] with s hs1 hs2
      have hτs : τ (Φ 0 s x) = τ x + s := by
        rcases le_total 0 s with hs | hs
        · exact hτcoc x hx1 hx2 s hs hs1 hs2
        · have hs' : 0 ≤ -s := by linarith
          have hgrp := flow_shift (I := I) (Φ := Φ) (V := V) hVsm hΦsm hΦself hΦderiv s (-s) x
          rw [show s + -s = 0 from by ring, hΦself 0 x] at hgrp
          have hdest1 : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p
              (Φ 0 (-s) (Φ 0 s x)) := by rw [hgrp]; exact hx1
          have hdest2 : γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q
              (Φ 0 (-s) (Φ 0 s x)) := by rw [hgrp]; exact hx2
          have h := hτcoc (Φ 0 s x) hs1 hs2 (-s) hs' hdest1 hdest2
          rw [hgrp] at h
          linarith
      have hgrp := flow_shift (I := I) (Φ := Φ) (V := V) hVsm hΦsm hΦself hΦderiv s (-(τ x) - s) x
      rw [show s + (-(τ x) - s) = -(τ x) from by ring] at hgrp
      rw [hτs, show -(τ x + s) = -(τ x) - s from by ring, hgrp]
    have hzero : (fun s : ℝ => Φ 0 s x) 0 = x := hΦself 0 x
    have hdu : HasMFDerivAt I 𝓘(ℝ, TangentSpace I p)
        (fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) ((fun s : ℝ => Φ 0 s x) 0)
        (mfderiv I 𝓘(ℝ, TangentSpace I p)
          (fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) ((fun s : ℝ => Φ 0 s x) 0)) := by
      rw [hzero]
      exact ((hsm_u x hx1 hx2).mdifferentiableAt (by simp)).hasMFDerivAt
    have hdφ : HasMFDerivAt 𝓘(ℝ,ℝ) I (fun s : ℝ => Φ 0 s x) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V x)) := by
      have h := hΦderiv 0 0 x
      rw [hΦself 0 x] at h
      exact h
    have hcomp : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ, TangentSpace I p)
        ((fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) ∘ (fun s : ℝ => Φ 0 s x)) 0
        ((mfderiv I 𝓘(ℝ, TangentSpace I p)
          (fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) ((fun s : ℝ => Φ 0 s x) 0)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V x))) :=
      HasMFDerivAt.comp (f := fun s : ℝ => Φ 0 s x) (0 : ℝ) hdu hdφ
    have hcnst : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ, TangentSpace I p)
        (fun s : ℝ => a⁻¹ • Φp (Φ 0 (-(τ (Φ 0 s x))) (Φ 0 s x))) 0 0 :=
      (hasMFDerivAt_const (a⁻¹ • Φp (Φ 0 (-(τ x)) x)) (0 : ℝ)).congr_of_eventuallyEq hshift
    have hL : (mfderiv I 𝓘(ℝ, TangentSpace I p)
          (fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) ((fun s : ℝ => Φ 0 s x) 0)).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V x)) = 0 :=
      hcomp.mfderiv.symm.trans hcnst.mfderiv
    rw [hzero] at hL
    have hone : (mfderiv I 𝓘(ℝ, TangentSpace I p)
        (fun z : M => a⁻¹ • Φp (Φ 0 (-(τ z)) z)) x)
        (((1 : ℝ →L[ℝ] ℝ).smulRight (V x)) 1) =
        (0 : ℝ →L[ℝ] TangentSpace I p) 1 :=
      congrArg (fun (L : ℝ →L[ℝ] TangentSpace I p) => L 1) hL
    rw [ContinuousLinearMap.smulRight_apply] at hone
    rw [one_apply_eq_self] at hone
    rw [one_smul] at hone
    rw [zero_apply] at hone
    exact hone
  -- ### Clause 4: the value on the inner annulus.
  have hcap : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 →
      a⁻¹ • Φp (Φ 0 (-(τ x)) x) =
        (Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x := by
    intro x hx1 hx3
    have hxpos : 0 < Work.Diff.C.rdist (I := I) (M := M) p x := lt_trans (by linarith) hx1
    have hfρ : Work.Diff.C.rdist (I := I) (M := M) p x < ρ := lt_of_le_of_lt hx3 (by linarith)
    have hτx : τ x = Work.Diff.C.rdist (I := I) (M := M) p x - a :=
      hτval x hx1 (by linarith)
    have hradx : Φ 0 (-(Work.Diff.C.rdist (I := I) (M := M) p x - a)) x =
        Submission.GlobalExp.GExp (cov := cov) hmet p
          (a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x)) := hrad x hx1 hx3
    have hfx : ‖Φp x‖ = Work.Diff.C.rdist (I := I) (M := M) p x :=
      (hnorm x (lt_of_lt_of_le hfρ hρv)).symm
    have hnrm : ‖a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x)‖ < ρ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha,
        abs_of_pos (inv_pos.mpr hxpos), hfx, inv_mul_cancel₀ (ne_of_gt hxpos), mul_one]
      exact haρ
    have hroundx := hround (a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x)) hnrm
    calc a⁻¹ • Φp (Φ 0 (-(τ x)) x)
        = a⁻¹ • Φp (Φ 0 (-(Work.Diff.C.rdist (I := I) (M := M) p x - a)) x) := by rw [hτx]
      _ = a⁻¹ • Φp (Submission.GlobalExp.GExp (cov := cov) hmet p
            (a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x))) := by rw [hradx]
      _ = a⁻¹ • (a • ((Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x)) := by rw [hroundx]
      _ = (Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • Φp x := by
            rw [smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  exact ⟨fun x => a⁻¹ • Φp (Φ 0 (-(τ x)) x), hsm_u, hunit, hconst, hcap⟩

end Work.Diff.Dim2
