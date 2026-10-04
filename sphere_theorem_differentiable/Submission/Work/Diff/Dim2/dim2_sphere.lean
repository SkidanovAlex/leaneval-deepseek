import Mathlib
import Submission.Diff.ODE
import Submission.Work.Diff.Dim2.Setup
import Submission.Work.Diff.C.diffeo_of_local
import Submission.Work.Diff.C.GExp_localInverse
import Submission.Work.Diff.Dim2.cap_data2
import Submission.Work.Diff.Dim2.cap_ray
import Submission.Work.Diff.Dim2.reeb_field2
import Submission.Work.Diff.Dim2.flow_of_field
import Submission.Work.Diff.Dim2.flow_shift
import Submission.Work.Diff.Dim2.flow_radial
import Submission.Work.Diff.Dim2.flow_radial_q
import Submission.Work.Diff.Dim2.tau
import Submission.Work.Diff.Dim2.label_u
import Submission.Work.Diff.Dim2.label_u_formula
import Submission.Work.Diff.Dim2.label_u_rank
import Submission.Work.Diff.Dim2.label_v
import Submission.Work.Diff.Dim2.label_v_rank
import Submission.Work.Diff.Dim2.levelSet_orbit
import Submission.Work.Diff.Dim2.exists_isometry_EuclideanTwo
import Submission.Work.Diff.Dim2.PushField
import Submission.Work.Diff.Dim2.entry_submersion
import Submission.Work.Diff.Dim2.entry_along_flow
import Submission.Work.Diff.Dim2.flow_radial_q
import Submission.Work.Diff.Dim2.phase_data
import Submission.Work.Diff.Dim2.Azim
import Submission.Work.Diff.Dim2.Ambient
import Submission.Work.Diff.Dim2.reeb_field3
import Submission.Work.Diff.Dim2.flow_lip_f
import Submission.Work.Diff.Dim2.tau_gap
import Submission.Work.Diff.Dim2.transferSph2
import Submission.Work.Diff.Dim2.pushField_mfderiv
import Submission.Work.Diff.Dim2.azimuth
import Submission.Work.Diff.Dim2.phase
import Submission.Work.Diff.Dim2.label_u_angForm
import Submission.Work.Diff.Dim2.Caps
import Submission.Work.Diff.Dim2.sphereAmbSmooth
import Submission.Work.Diff.Dim2.sphereAmbNorm
import Submission.Work.Diff.Dim2.sphere_immersion_criterion
import Submission.Work.Diff.Dim2.ambDIso
import Submission.Work.Diff.Dim2.mfderivInjectiveOfLeftInverse
import Submission.Work.Diff.Dim2.northCapFacts
import Submission.Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_congr_of_eventuallyEq


/-!
# `d = 2`: the differentiable sphere theorem for surfaces

The single remaining obligation of this file is `dim2_exists_local_diffeo`: the construction of an
everywhere-immersion `G : M → S²`, from which `Work.Diff.C.diffeo_of_local` produces the
diffeomorphism of `dim2_sphere`.

The construction (see `STATE.md`, `Plan3.lean`, `PENDING.md` in this directory) is the smooth Reeb
construction: `G x = (sin (ξ x) • Az x, cos (ξ x))` on the middle annulus, glued to the exponential
charts at `p` and at `q`.  Steps 0a–1 of the assembly are written below; see `STATE.md` for the
status and the remaining plan.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal EuclideanSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **The main geometric construction of the `d = 2` branch.**

Data: a diameter pair `p, q` with `π/2 < D = d(p,q) < π`, the unique maximiser property of `q`, and
finiteness of all distances.  Conclusion: an everywhere-immersion `G : M → S²` (a local
diffeomorphism), from which `Work.Diff.C.diffeo_of_local` produces the diffeomorphism of the
statement. -/
theorem dim2_exists_local_diffeo
    (hdim2 : Module.finrank ℝ E = 2)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    {p q : M} {D : ℝ}
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (huniq : ∀ y : M, y ≠ q → Manifold.riemannianEDist I p y < ENNReal.ofReal D)
    (hfin : ∀ r s : M, Manifold.riemannianEDist I r s ≠ ⊤)
    (hFlow : SmoothFlow I M) :
    ∃ G : M → SphereD E, IsLocalDiffeomorph I (𝓡 (Module.finrank ℝ E)) ∞ G := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  haveI : Nonempty M := PathConnectedSpace.nonempty
  -- ### Step 0a: the scaled metric and the diameter pair.
  obtain ⟨g', hrest⟩ := dim2_diam_pair (I := I) (M := M) hdim2 cov htor hmet hpinch
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'⟩
  obtain ⟨hsmooth', hmet', hpinch', p, q, D, hpq, hDgt, hDlt, hdiam, huniq, hfin⟩ := hrest
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := hsmooth'
  -- ### Step 0b: the cap data (local inverses of the exponential maps) and the ray data.
  obtain ⟨Φp, Φq, v, δ, hv, hδ, hΦp, hΦq, hsmP, hsmQ, htri, hδsub⟩ :=
    cap_data2 (I := I) (M := M) hmet' htor hpq hdiam huniq hfin
  obtain ⟨ρp, hρp0, hρpv, hroundP, hrayP, hrayvP⟩ :=
    cap_ray (I := I) (M := M) hmet' htor (p := p) (Φp := Φp) hv
      (fun y h1 h2 => hsmP y h1 h2) (fun y hy => (hΦp y hy).2.1) (fun y hy => (hΦp y hy).2.2)
  obtain ⟨ρq, hρq0, hρqv, hroundQ, hrayQ, hrayvQ⟩ :=
    cap_ray (I := I) (M := M) hmet' htor (p := q) (Φp := Φq) hv
      (fun y h1 h2 => hsmQ y h1 h2) (fun y hy => (hΦq y hy).2.1) (fun y hy => (hΦq y hy).2.2)
  -- ### Step 0c: the small constants.
  set v' : ℝ := min v (min ρp ρq) with hv'def
  have hv'0 : 0 < v' := lt_min hv (lt_min hρp0 hρq0)
  have hv'v : v' ≤ v := min_le_left _ _
  have hv'ρp : v' ≤ ρp := le_trans (min_le_right _ _) (min_le_left _ _)
  have hv'ρq : v' ≤ ρq := le_trans (min_le_right _ _) (min_le_right _ _)
  set c : ℝ := min v' (D - Real.pi / 2) with hcdef
  have hc0 : 0 < c := lt_min hv'0 (by linarith)
  have hcv' : c ≤ v' := min_le_left _ _
  have hcD : c ≤ D - Real.pi / 2 := min_le_right _ _
  set a : ℝ := c / 1000 with hadef
  set γ : ℝ := c / 1000 with hγdef
  set e : ℝ := c / 1000 with hedef
  set S : ℝ := c / 1000 with hSdef
  have ha0 : 0 < a := by rw [hadef]; linarith
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  have he0 : 0 < e := by rw [hedef]; linarith
  have hS0 : 0 < S := by rw [hSdef]; linarith
  have h2a' : 2 * a < v' := by rw [hadef]; linarith
  have h2g' : 2 * γ < v' := by rw [hγdef]; linarith
  have h5g' : 5 * γ / 2 ≤ v' := by rw [hγdef]; linarith
  have hsep1' : 3 * a / 2 + 3 * γ < D := by rw [hadef, hγdef]; linarith
  have hsep2' : 7 * a / 4 + 5 * γ / 2 < D := by rw [hadef, hγdef]; linarith
  have hsep3' : 3 * γ < D - Real.pi / 2 := by rw [hγdef]; linarith
  have hsep4' : 5 * γ / 2 < v' := by rw [hγdef]; linarith
  have hsep5' : 3 * γ < Real.pi / 2 := by rw [hγdef]; linarith
  have haD' : a < D := by rw [hadef]; linarith
  have hsep1a : a + γ / 8 < D := by rw [hadef, hγdef]; linarith
  have hsep2a : 3 * a / 2 + γ / 4 < D := by rw [hadef, hγdef]; linarith
  have hsep3a : 3 * a / 2 + 5 * γ / 2 < D := by rw [hadef, hγdef]; linarith
  have hsmP' : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < v' →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) y :=
    fun y h1 h2 => hsmP y h1 (lt_of_lt_of_le h2 hv'v)
  have hsmQ' : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v' →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y :=
    fun y h1 h2 => hsmQ y h1 (lt_of_lt_of_le h2 hv'v)
  -- ### Step 0d: the Reeb field and its flow.
  obtain ⟨V, hVsm, hV1, hVP, hVQ, hasc, hnz⟩ :=
    reeb_field3 (I := I) (M := M) hmet' htor hpinch' (p := p) (q := q) (D := D) (v := v')
      (a := a) (γ := γ) ha0 hγ0 hv'0 h2a' h2g' hDgt hDlt hdiam hpq
      hsmP' hsmQ' hsep1' hsep2' hsep3' hsep4' hsep5'
  obtain ⟨Φ, hΦsm, hΦself, hΦderiv, hΦcoc⟩ := flow_of_field (I := I) (M := M) hFlow hVsm
  have hflow_lip : ∀ y : M, ∀ s s' : ℝ,
      |Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s y)
        - Work.Diff.C.rdist (I := I) (M := M) p (Φ 0 s' y)| ≤ |s - s'| :=
    flow_lip_f (I := I) (M := M) (p := p) hVsm hV1 hΦsm hΦself hΦderiv
  -- ### Step 0e: the crossing time of the level `{rdist p = a}`.
  obtain ⟨τ, hτsm, hτa, hτuniq, hτval, hτhalf, hτcoc, hτV⟩ :=
    tau (I := I) (M := M) hmet' htor hpinch' (p := p) (q := q) (D := D) (a := a) (γ := γ)
      (v := v') ha0 hγ0 haD' h2a' h2g' h5g' hsep1a hsep2a hsep3a hDgt hDlt hdiam htri
      hsmP' hVsm hΦsm hΦself hΦderiv hΦcoc hsmQ' hasc hnz hVP hVQ
  -- ### Step 1: the label `u` (the direction of the flow-back point on `C_p`).
  have hnormP' := fun y hy => (hΦp y hy).2.1
  have hinvP' := fun y hy => (hΦp y hy).2.2
  have hsmΦp' := fun y hy => (hΦp y hy).1
  have hroundP' := fun w hw => hroundP w (lt_of_lt_of_le hw hv'ρp)
  have hrayP' := fun (w : TangentSpace I p) (tt : ℝ) hw h0 ht =>
    hrayP w tt hw h0 (lt_of_lt_of_le ht hv'ρp)
  have hrayvP' := fun (w : TangentSpace I p) (tt : ℝ) hw h0 ht =>
    hrayvP w tt hw h0 (lt_of_lt_of_le ht hv'ρp)
  have haρ' : a < v' := by rw [hadef]; linarith
  have hrad := (flow_radial (I := I) (M := M) hmet' htor (p := p) (Φp := Φp) (v := v) (ρ := v')
      (a := a) ha0 hv'0 haρ' hv'v hsmP hnormP' hroundP' hrayP' hrayvP' hVsm hΦsm hΦself hΦderiv
      hVP).1
  obtain ⟨u, hu_sm, hu_un, hu_V, hu_cap, hu_form⟩ :=
    label_u_formula (I := I) (M := M) hmet' htor (p := p) (q := q) (Φp := Φp) (v := v) (ρ := v')
      (a := a) (γ := γ) ha0 hv'0 haρ' hv'v hsmP hnormP' hroundP' hVsm hΦsm hΦself hΦderiv
      hΦcoc hVP hrad hτsm hτval hτcoc hτa
  have hu_rank : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ, TangentSpace I p) u x ≠ 0 :=
    label_u_rank (I := I) (M := M) hmet' htor (p := p) (q := q) (a := a) (γ := γ) (v := v)
      (ρ := v') ha0 hγ0 hv'0 haρ' hv'v (by rw [hdim2]) hsmP hsmΦp' hnormP' hinvP' hroundP'
      hVsm hΦsm hΦself hΦderiv hΦcoc hτsm hτV hτa hu_sm hu_form
  -- ### Step 2: the q-direction `vE` (the direction of the entry point on `C_q`).
  have hnormQ' := fun y hy => (hΦq y hy).2.1
  have hphiQ := fun y hy => (hΦq y hy).1
  have hroundQ' := fun w hw => hroundQ w (lt_of_lt_of_le hw hv'ρq)
  have hrayQ' := fun (w : TangentSpace I q) (tt : ℝ) hw h0 ht =>
    hrayQ w tt hw h0 (lt_of_lt_of_le ht hv'ρq)
  have hrayvQ' := fun (w : TangentSpace I q) (tt : ℝ) hw h0 ht =>
    hrayvQ w tt hw h0 (lt_of_lt_of_le ht hv'ρq)
  have hsmQv : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v' →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) y :=
    fun y h1 h2 => hsmQ y h1 (lt_of_lt_of_le h2 hv'v)
  have hphiQv : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v' →
      ContMDiffAt I (modelWithCornersSelf ℝ (TangentSpace I q)) ∞ Φq y :=
    fun y h2 => (hΦq y (lt_of_lt_of_le h2 hv'v)).1
  have hnormQv : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v' →
      Work.Diff.C.rdist (I := I) (M := M) q y = ‖Φq y‖ :=
    fun y h2 => (hΦq y (lt_of_lt_of_le h2 hv'v)).2.1
  have hconst := (flow_radial_q (I := I) (M := M) hmet' htor (q := q) (Φq := Φq) (v := v)
      (ρ := v') (γ := γ) hv'0 hγ0 (by linarith : 3 * γ / 2 < v') hv'v hphiQ hsmQ hnormQ'
      hroundQ' hrayQ' hrayvQ' hVsm hΦsm hΦself hΦderiv hVQ).2
  obtain ⟨vE, t, y, hvE_sm, hvE_un, hvE_V, hvE_cap, ht_sm, hy_sm, hy_form, hy_g, hvE_form⟩ :=
    label_v (I := I) (M := M) hmet' htor hpinch' (p := p) (q := q) (D := D) (v := v') (a := a)
      (γ := γ) ha0 hγ0 hv'0 hsep4' hsmQv hphiQv hnormQv hDgt htri hdiam hVsm hΦsm hΦself
      hΦderiv hΦcoc hVQ hconst hnz hasc
  have hzv : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      0 < Work.Diff.C.rdist (I := I) (M := M) q (y x) ∧
        Work.Diff.C.rdist (I := I) (M := M) q (y x) < v' := by
    intro x h1 h2
    rw [hy_g x h1 h2]
    exact ⟨by linarith, by linarith⟩
  have hgV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ,ℝ) (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) (y x)
        (V (y x)) = (-1 : ℝ) := by
    intro x h1 h2
    obtain ⟨hz1, hz2⟩ := hzv x h1 h2
    have hg1 : γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q (y x) := by
      rw [hy_g x h1 h2]; linarith
    have hg2 : Work.Diff.C.rdist (I := I) (M := M) q (y x) ≤ 5 * γ / 2 := by
      rw [hy_g x h1 h2]; linarith
    have hV := hVQ (y x) hg1 hg2
    have heik := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) hmet' htor (q := q) (x := y x)
      (by rw [hy_g x h1 h2]; exact ne_of_gt (by linarith)) (hsmQv (y x) hz1 hz2)
    rw [← Work.Diff.C.inner_rgrad, hV, inner_neg_right, heik]
  have hNZ : IsOpen {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x} := by
    rw [Set.ofPred_and]
    exact (isOpen_lt continuous_const (Work.Diff.C.rdist_continuous (I := I) (M := M) p)).inter
      (isOpen_lt continuous_const (Work.Diff.C.rdist_continuous (I := I) (M := M) q))
  have hyd := entry_submersion (I := I) (M := M) (by rw [hdim2])
    (N := {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x})
    hNZ hVsm hΦsm hΦself hΦderiv hΦcoc
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => ht_sm x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hy_sm x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hy_form x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hy_g x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) =>
        (hsmQv (y x) (hzv x hx.1 hx.2).1 (hzv x hx.1 hx.2).2).mdifferentiableAt (by decide))
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hgV x hx.1 hx.2)
  have hyV := entry_along_flow (I := I) (M := M) (by rw [hdim2]; norm_num : 1 ≤ Module.finrank ℝ E)
    (N := {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x})
    hNZ hVsm hΦsm hΦself hΦderiv hΦcoc
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => ht_sm x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hy_sm x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hy_form x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hy_g x hx.1 hx.2)
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) =>
        (hsmQv (y x) (hzv x hx.1 hx.2).1 (hzv x hx.1 hx.2).2).mdifferentiableAt (by decide))
    (fun x (hx : a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x) => hgV x hx.1 hx.2)
  have hv_rank : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      mfderiv I 𝓘(ℝ, TangentSpace I q) vE x ≠ 0 :=
    label_v_rank (I := I) (M := M) hmet' htor (p := p) (q := q) (a := a) (γ := γ)
      (c := 3 * γ / 4) (v := v') ha0 hγ0 (by linarith) (by linarith) (by linarith) (by rw [hdim2])
      hphiQv hnormQv hroundQ' hVsm hΦself hΦderiv
      (fun x h1 h2 => hy_sm x h1 h2) (fun x h1 h2 => hy_g x h1 h2)
      (fun x h1 h2 => hyV x ⟨h1, h2⟩) (fun x h1 h2 => hyd x ⟨h1, h2⟩)
      (fun x h1 h2 => hvE_sm x h1 h2) (fun x h1 h2 => hvE_form x h1 h2)
  -- ### Step 3: the two isometric identifications of the tangent planes with `ℝ²`.
  have hfP : Module.finrank ℝ (TangentSpace I p) = 2 := by
    rw [(tangentSpaceCastModel I p).toLinearEquiv.finrank_eq, hdim2]
  have hfQ : Module.finrank ℝ (TangentSpace I q) = 2 := by
    rw [(tangentSpaceCastModel I q).toLinearEquiv.finrank_eq, hdim2]
  obtain ⟨ep⟩ := exists_isometry_EuclideanTwo (E := TangentSpace I p) hfP
  obtain ⟨eq⟩ := exists_isometry_EuclideanTwo (E := TangentSpace I q) hfQ
  set uE : M → EuclideanSpace ℝ (Fin 2) := fun x => ep (u x) with huEdef
  set vE2 : M → EuclideanSpace ℝ (Fin 2) := fun x => eq (vE x) with hvE2def
  have huE_un : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ‖uE x‖ = 1 := by
    intro x h1 h2
    have h : uE x = ep (u x) := by rw [huEdef]
    rw [h, LinearIsometryEquiv.norm_map]
    exact hu_un x h1 h2
  have hvE2_un : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ‖vE2 x‖ = 1 := by
    intro x h1 h2
    have h : vE2 x = eq (vE x) := by rw [hvE2def]
    rw [h, LinearIsometryEquiv.norm_map]
    exact hvE_un x h1 h2
  have huE_sm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ uE x := by
    intro x h1 h2
    rw [huEdef]
    exact pushField_contMDiffAt (e := ep) (f := u) (hu_sm x h1 h2)
  have hvE2_sm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ vE2 x := by
    intro x h1 h2
    rw [hvE2def]
    exact pushField_contMDiffAt (e := eq) (f := vE) (hvE_sm x h1 h2)
  -- ### Step 3c: `uE` and `vE2` are constant along the flow lines.
  have huconst : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ∀ y : M,
      a / 4 < Work.Diff.C.rdist (I := I) (M := M) p y →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q y →
      (∃ s : ℝ, y = Φ 0 s x) → uE y = uE x := by
    intro x hx1 hx2 y hy1 hy2 hs
    obtain ⟨s, rfl⟩ := hs
    have hτs : τ (Φ 0 s x) = τ x + s := by
      by_cases hs0 : 0 ≤ s
      · exact hτcoc x hx1 hx2 s hs0 hy1 hy2
      · have h1 : 0 ≤ -s := by linarith
        have hxs : Φ 0 (-s) (Φ 0 s x) = x := by
          rw [flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv s (-s) x,
            add_neg_cancel, hΦself]
        have h2 := hτcoc (Φ 0 s x) hy1 hy2 (-s) h1 (by rw [hxs]; exact hx1)
          (by rw [hxs]; exact hx2)
        rw [hxs] at h2
        linarith
    have huu : u (Φ 0 s x) = u x := by
      rw [hu_form (Φ 0 s x) hy1 hy2, hu_form x hx1 hx2]
      congr 2
      rw [flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv s (-(τ (Φ 0 s x))) x,
        hτs]
      congr 1
      ring
    show ep (u (Φ 0 s x)) = ep (u x)
    exact congrArg ep huu
  -- ### Step 4: the label fields are constant along the flow lines
  have hflow_law : ∀ (w : M) (σ : ℝ), Φ 0 σ (Φ 0 (-σ) w) = w := by
    intro w σ
    rw [flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv (-σ) σ w, neg_add_cancel,
      hΦself]
  have hflow_law' : ∀ (w : M) (σ : ℝ), Φ 0 (-σ) (Φ 0 σ w) = w := by
    intro w σ
    rw [flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv σ (-σ) w, add_neg_cancel,
      hΦself]
  have hinvQ' := fun (w : M) (hw : Work.Diff.C.rdist (I := I) (M := M) q w < v) =>
    (hΦq w hw).2.2
  have hcross_uniq := rdistQ_crossing_unique (I := I) (M := M)
    (q := q) (v := v') (γ := γ) hγ0 (by rw [hγdef]; linarith) hmet' htor hsmQv hVQ hΦsm hΦderiv
  -- ### Step 5: the two labels agree on the flow lines
  have huv : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ∀ z : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z →
      uE x = uE z → vE2 x = vE2 z := by
    intro x hx1 hx2 z hz1 hz2 huxz
    have huxz' : u x = u z := ep.injective huxz
    have hpx : Φp (Φ 0 (-(τ x)) x) = a • u x := by
      rw [hu_form x hx1 hx2, smul_smul, mul_inv_cancel₀ (ne_of_gt ha0), one_smul]
    have hpz : Φp (Φ 0 (-(τ z)) z) = a • u z := by
      rw [hu_form z hz1 hz2, smul_smul, mul_inv_cancel₀ (ne_of_gt ha0), one_smul]
    have heq : Φ 0 (-(τ x)) x = Φ 0 (-(τ z)) z := by
      have h1 : Submission.GlobalExp.GExp (cov := cov) hmet' p (Φp (Φ 0 (-(τ x)) x))
          = Φ 0 (-(τ x)) x :=
        hinvP' _ (by rw [hτa x hx1 hx2]; exact lt_of_lt_of_le haρ' hv'v)
      have h2 : Submission.GlobalExp.GExp (cov := cov) hmet' p (Φp (Φ 0 (-(τ z)) z))
          = Φ 0 (-(τ z)) z :=
        hinvP' _ (by rw [hτa z hz1 hz2]; exact lt_of_lt_of_le haρ' hv'v)
      rw [← h1, ← h2, hpx, hpz, huxz']
    have hσ : z = Φ 0 (τ z - τ x) x := by
      calc z = Φ 0 (τ z) (Φ 0 (-(τ z)) z) := (hflow_law z (τ z)).symm
        _ = Φ 0 (τ z) (Φ 0 (-(τ x)) x) := by rw [heq.symm]
        _ = Φ 0 (-(τ x) + τ z) x :=
              flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv (-(τ x)) (τ z) x
        _ = Φ 0 (τ z - τ x) x := by rw [show -(τ x) + τ z = τ z - τ x from by ring]
    have hzx : y x = y z := by
      have h1 : y z = Φ 0 (τ z - τ x + t z) x := by
        calc y z = Φ 0 (t z) z := hy_form z hz1 hz2
          _ = Φ 0 (t z) (Φ 0 (τ z - τ x) x) :=
                congrArg (fun w : M => Φ 0 (t z) w) hσ
          _ = Φ 0 (τ z - τ x + t z) x :=
                flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv (τ z - τ x) (t z) x
      have h2 : Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (τ z - τ x + t z) x)
          = 3 * γ / 4 := by
        rw [← h1]; exact hy_g z hz1 hz2
      have h3 : Work.Diff.C.rdist (I := I) (M := M) q (Φ 0 (t x) x) = 3 * γ / 4 := by
        rw [← hy_form x hx1 hx2]; exact hy_g x hx1 hx2
      have h4 : τ z - τ x + t z = t x := hcross_uniq x _ _ h2 h3
      rw [h1, h4, ← hy_form x hx1 hx2]
    have hvx : vE x = vE z := by
      rw [hvE_form x hx1 hx2, hvE_form z hz1 hz2, hzx]
    show vE2 x = vE2 z
    have hcx : vE2 x = eq (vE x) := by rw [hvE2def]
    have hcz : vE2 z = eq (vE z) := by rw [hvE2def]
    rw [hcx, hcz, hvx]
  have hvu : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      ∀ z : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p z →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q z →
      vE2 x = vE2 z → uE x = uE z := by
    intro x hx1 hx2 z hz1 hz2 hvxz
    have hvxz' : vE x = vE z := eq.injective hvxz
    have hne : (-(3 * γ / 4)⁻¹ : ℝ) ≠ 0 := by
      intro h0
      have h1 : (3 * γ / 4)⁻¹ = 0 := neg_eq_zero.mp h0
      rw [inv_eq_zero] at h1
      linarith [hγ0]
    have h4 : Φq (y x) = Φq (y z) := by
      rw [hvE_form x hx1 hx2, hvE_form z hz1 hz2] at hvxz'
      have h5 := congrArg (fun w : TangentSpace I q => (-(3 * γ / 4)⁻¹)⁻¹ • w) hvxz'
      simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using h5
    have hyxz : y x = y z := by
      have h1 : Submission.GlobalExp.GExp (cov := cov) hmet' q (Φq (y x)) = y x :=
        hinvQ' _ (by rw [hy_g x hx1 hx2]; exact lt_of_lt_of_le (by linarith) hv'v)
      have h2 : Submission.GlobalExp.GExp (cov := cov) hmet' q (Φq (y z)) = y z :=
        hinvQ' _ (by rw [hy_g z hz1 hz2]; exact lt_of_lt_of_le (by linarith) hv'v)
      rw [← h1, ← h2, h4]
    have h5 : Φ 0 (t x) x = Φ 0 (t z) z := by
      rw [← hy_form x hx1 hx2, ← hy_form z hz1 hz2, hyxz]
    have hσ : z = Φ 0 (t x - t z) x := by
      calc z = Φ 0 (-(t z)) (Φ 0 (t z) z) := (hflow_law' z (t z)).symm
        _ = Φ 0 (-(t z)) (Φ 0 (t x) x) := by rw [h5.symm]
        _ = Φ 0 (t x + (-(t z))) x :=
              flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv (t x) (-(t z)) x
        _ = Φ 0 (t x - t z) x := by rw [show t x + -(t z) = t x - t z from by ring]
    have hstep : (t x - t z) + (-(τ z)) = -(τ x) := by
      have heq2 : Φ 0 ((t x - t z) + (-(τ z))) x = Φ 0 (-(τ z)) z :=
        ((congrArg (fun w : M => Φ 0 (-(τ z)) w) hσ).trans
          (flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv (t x - t z) (-(τ z)) x)).symm
      have hfa : Work.Diff.C.rdist (I := I) (M := M) p
          (Φ 0 ((t x - t z) + (-(τ z))) x) = a := by
        rw [heq2]; exact hτa z hz1 hz2
      exact hτuniq x hx1 hx2 _ hfa
    have huz : Φ 0 (-(τ z)) z = Φ 0 (-(τ x)) x := by
      have h3 : Φ 0 (-(τ z)) z = Φ 0 (-(τ z)) (Φ 0 (t x - t z) x) :=
        congrArg (fun w : M => Φ 0 (-(τ z)) w) hσ
      rw [h3, flow_shift (I := I) (M := M) hVsm hΦsm hΦself hΦderiv (t x - t z) (-(τ z)) x,
        hstep]
    show uE x = uE z
    have hux : u x = u z := by
      rw [hu_form x hx1 hx2, hu_form z hz1 hz2, huz]
    have hcx : uE x = ep (u x) := by rw [huEdef]
    have hcz : uE z = ep (u z) := by rw [huEdef]
    rw [hcx, hcz, hux]
  -- ### Step 6: the label `uE` is onto the unit circle.
  have husurj : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ = 1 →
      ∃ x ∈ {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x}, uE x = z := by
    intro z hz
    set w : TangentSpace I p := ep.symm z with hwdef
    have hw1 : ‖w‖ = 1 := by
      rw [hwdef, LinearIsometryEquiv.norm_map]; exact hz
    set x : M := Submission.GlobalExp.GExp (cov := cov) hmet' p ((a / 2) • w) with hxdef
    have hfx : Work.Diff.C.rdist (I := I) (M := M) p x = a / 2 := by
      rw [hxdef]
      exact hrayP' w (a / 2) hw1 (by linarith [ha0]) (by linarith [haρ'])
    have hγa : γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x := by
      have h := htri x
      rw [hfx] at h
      have haγ : a / 2 + γ / 4 < Real.pi / 2 := by
        have h1 := hsep5'
        have h2 : a = γ := by rw [hadef, hγdef]
        linarith [Real.pi_pos]
      linarith [hDgt]
    have hux : u x = (a / 2)⁻¹ • Φp x := by
      rw [hu_cap x (by rw [hfx]; linarith [ha0]) (by rw [hfx]; linarith [ha0]), hfx]
    have hΦpx : Φp x = (a / 2) • w := by
      rw [hxdef]
      exact hroundP' ((a / 2) • w) (by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [ha0]), hw1, mul_one]
        linarith [haρ'])
    have hux2 : u x = w := by
      rw [hux, hΦpx, smul_smul, inv_mul_cancel₀ (by linarith [ha0]), one_smul]
    refine ⟨x, ⟨by rw [hfx]; linarith [ha0], hγa⟩, ?_⟩
    have h1 : uE x = ep (u x) := by rw [huEdef]
    rw [h1, hux2, hwdef]
    exact LinearIsometryEquiv.apply_symm_apply ep z
  -- ### Step 7: the transfer map between the two labels (a circle diffeomorphism).
  set N : Set M := {x : M | a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x ∧
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x} with hNdef
  have huE_sm' : ∀ x ∈ N, ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ uE x :=
    fun x hx => huE_sm x hx.1 hx.2
  have hvE2_sm' : ∀ x ∈ N, ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ vE2 x :=
    fun x hx => hvE2_sm x hx.1 hx.2
  have huE1' : ∀ x ∈ N, ‖uE x‖ = 1 := fun x hx => huE_un x hx.1 hx.2
  have hvE21' : ∀ x ∈ N, ‖vE2 x‖ = 1 := fun x hx => hvE2_un x hx.1 hx.2
  have huEV' : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) uE x (V x) = 0 := by
    intro x hx
    have hmd : MDifferentiableAt I 𝓘(ℝ, TangentSpace I p) u x :=
      (hu_sm x hx.1 hx.2).mdifferentiableAt (by simp)
    have h := (pushField_mfderiv (I := I) (M := M) (e := ep) (f := u) (x := x) hmd).1 (V x)
    have h2 : (Work.Diff.Dim2.pushField ep u : M → EuclideanSpace ℝ (Fin 2)) = uE := rfl
    rw [h2] at h
    exact h.trans ((congrArg ep (hu_V x hx.1 hx.2)).trans (map_zero ep))
  have hvEV' : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) vE2 x (V x) = 0 := by
    intro x hx
    have hmd : MDifferentiableAt I 𝓘(ℝ, TangentSpace I q) vE x :=
      (hvE_sm x hx.1 hx.2).mdifferentiableAt (by simp)
    have h := (pushField_mfderiv (I := I) (M := M) (e := eq) (f := vE) (x := x) hmd).1 (V x)
    have h2 : (Work.Diff.Dim2.pushField eq vE : M → EuclideanSpace ℝ (Fin 2)) = vE2 := rfl
    rw [h2] at h
    exact h.trans ((congrArg eq (hvE_V x hx.1 hx.2)).trans (map_zero eq))
  have huErank' : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) uE x ≠ 0 := by
    intro x hx
    have hmd : MDifferentiableAt I 𝓘(ℝ, TangentSpace I p) u x :=
      (hu_sm x hx.1 hx.2).mdifferentiableAt (by simp)
    have h := (pushField_mfderiv (I := I) (M := M) (e := ep) (f := u) (x := x) hmd).2
      (hu_rank x hx.1 hx.2)
    have h2 : (Work.Diff.Dim2.pushField ep u : M → EuclideanSpace ℝ (Fin 2)) = uE := rfl
    rwa [h2] at h
  have hvErank' : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) vE2 x ≠ 0 := by
    intro x hx
    have hmd : MDifferentiableAt I 𝓘(ℝ, TangentSpace I q) vE x :=
      (hvE_sm x hx.1 hx.2).mdifferentiableAt (by simp)
    have h := (pushField_mfderiv (I := I) (M := M) (e := eq) (f := vE) (x := x) hmd).2
      (hv_rank x hx.1 hx.2)
    have h2 : (Work.Diff.Dim2.pushField eq vE : M → EuclideanSpace ℝ (Fin 2)) = vE2 := rfl
    rwa [h2] at h
  obtain ⟨s, ρ, hs, hρsm, hρd, hρper, htrans⟩ :=
    transferSph2 (I := I) (M := M) (N := N) hNZ hVsm
      (fun x hx => (huE_sm' x hx).contMDiffWithinAt)
      (fun x hx => (hvE2_sm' x hx).contMDiffWithinAt)
      huE1' hvE21' huEV' hvEV' huErank' hvErank'
      (fun x hx y hy h => huv x hx.1 hx.2 y hy.1 hy.2 h)
      (fun x hx y hy h => hvu x hx.1 hx.2 y hy.1 hy.2 h)
      (fun z hz => husurj z hz)
  -- ### Step 8: the phase data and the azimuth field.
  obtain ⟨Ξ, ϑ, Θ, β, ψp, ψq, hΞ, hϑ, hΘ, hβ, hψp, hψq, hΞarc, hΞd, hΞπ, hϑarc, hϑb,
    hϑd, hΘd, hΞΘ, hΘϑ, hβ0, hβ1, hβr, hψp1, hψp0, hψpr, hψq1, hψq0, hψqr⟩ :=
    phase_data (a := a) (g := γ) (D := 0) (e := e) (S := (1 : ℝ)) ha0 hγ0 he0 one_pos
  have heγ : e = γ := by rw [hedef, hγdef]
  have hDgte : 1 + a + 3 * γ / 2 + e < D := by
    have hsum : a + 3 * γ / 2 + e = 7 * c / 2000 := by
      rw [hadef, hγdef, hedef]; ring
    have hD32 : (3 : ℝ) / 2 < D := by
      have := Real.pi_gt_three; linarith [hDgt]
    have h7 : 7 * D / 2000 < D - 1 := by
      have h1993 : (2000 : ℝ) < 1993 * D := by linarith
      linarith
    have hle : 7 * c / 2000 ≤ 7 * D / 2000 := by
      have hcD' : c ≤ D := by linarith [hcD, Real.pi_pos]
      linarith
    linarith
  have hgap := tau_gap (I := I) (M := M) (p := p) (q := q) (D := D) (a := a) (γ := γ)
    (e := e) ha0 hγ0 he0 hDgte htri (fun s x => hΦself s x) hflow_lip hτval hτhalf hτa
  have hband : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      0 < β (τ x) → β (τ x) < 1 →
      a < Work.Diff.C.rdist (I := I) (M := M) p x ∧
        3 * γ / 2 + e < Work.Diff.C.rdist (I := I) (M := M) q x := by
    intro x h1 h2 hb0 hb1
    have hτ0 : 0 < τ x := by
      by_contra hcon
      exact absurd (hβ0 (τ x) (le_of_not_gt hcon)) (ne_of_gt hb0)
    have hτ1 : τ x < 1 := by
      by_contra hcon
      exact absurd (hβ1 (τ x) (le_of_not_gt hcon)) (ne_of_lt hb1)
    exact hgap.1 x h1 h2 hτ0 hτ1
  have hLUA : ∀ x ∈ N, ∀ w : TangentSpace I x, w ≠ 0 →
      mfderiv I 𝓘(ℝ,ℝ) τ x w = 0 →
      angForm (I := I) (M := M) (Az := uE) x w ≠ 0 :=
    label_u_angForm (I := I) (M := M) hdim2 hNZ
      (fun x hx => (huE_sm' x hx).contMDiffWithinAt)
      huE1' huEV' (fun x hx => hnz x (le_of_lt hx.1) (by linarith [hx.2])) huErank'
      (fun x hx => hτV x hx.1 hx.2)
  obtain ⟨Az, hAzdef, hAz_sm, hAz1, hAz_b0, hAz_b1, hAz_V0, hAz_V1, hAz_tw⟩ :=
    azimuth (I := I) (M := M) hNZ hVsm hτsm (fun x hx => hτV x hx.1 hx.2) hβ hβ0 hβ1 hβr
      (fun x hx => (huE_sm' x hx).contMDiffWithinAt)
      (fun x hx => (hvE2_sm' x hx).contMDiffWithinAt)
      huE1' hvE21' huEV' hvEV'
      (fun x hx _ _ w hw hτw => hLUA x hx w hw hτw)
      hs hρsm hρd hρper htrans
  -- ### Step 9: the phase function.
  have hτann : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2 →
      a + τ x = Work.Diff.C.rdist (I := I) (M := M) p x := by
    intro x h1 h2 h3
    linarith [hτval x h1 h3]
  have hsepA : 3 * a / 4 + (3 * γ / 2 + e) < D := by
    rw [heγ]; linarith [hsep2']
  have hsepB : a + (3 * γ / 2 + e) < D := by
    rw [heγ]; linarith [hsep2']
  have hfsm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p x < a →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) x :=
    fun x h1 h2 h3 => hsmP' x (by linarith [ha0]) (lt_of_lt_of_le h3 (le_of_lt haρ'))
  have hgsm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2 + e →
      CMDiffAt ∞ (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x :=
    fun x h1 h2 h3 => hsmQ' x (by linarith [hγ0]) (lt_of_lt_of_le h3 (by linarith [hsep4', heγ]))
  have hfV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) p x ≤ a →
      mfderiv I 𝓘(ℝ,ℝ) (fun z : M => Work.Diff.C.rdist (I := I) (M := M) p z) x (V x) = 1 := by
    intro x h1 h2 h3
    have hV := hVP x (by linarith [ha0]) (by linarith [ha0])
    have hz1 : 0 < Work.Diff.C.rdist (I := I) (M := M) p x := by linarith [ha0]
    have hz2 : Work.Diff.C.rdist (I := I) (M := M) p x < v' := lt_of_le_of_lt h3 haρ'
    have heik := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) hmet' htor (q := p) (x := x)
      (ne_of_gt hz1) (hsmP' x hz1 hz2)
    rw [← Work.Diff.C.inner_rgrad, hV, heik]
  have hgV : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 + e →
      mfderiv I 𝓘(ℝ,ℝ) (fun z : M => Work.Diff.C.rdist (I := I) (M := M) q z) x (V x) = -1 := by
    intro x h1 h2 h3
    have hV := hVQ x (by linarith [hγ0]) (by rw [heγ] at h3; linarith [h3])
    have hz1 : 0 < Work.Diff.C.rdist (I := I) (M := M) q x := by linarith [hγ0]
    have hz2 : Work.Diff.C.rdist (I := I) (M := M) q x < v' :=
      lt_of_le_of_lt h3 (by linarith [hsep4', heγ])
    have heik := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) hmet' htor (q := q) (x := x)
      (ne_of_gt hz1) (hsmQ' x hz1 hz2)
    rw [← Work.Diff.C.inner_rgrad, hV, inner_neg_right, heik]
  have hτpos : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → 0 < a + τ x := by
    intro x h1 h2
    by_cases hf : Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 2
    · have := hτval x h1 hf
      linarith
    · push_neg at hf
      have := hτhalf x h1 h2 (le_of_lt hf)
      linarith
  obtain ⟨ξ, hξsm, hξ1, hξ2, hξV, hξtw, hξrng⟩ :=
    phase (I := I) (M := M) hmet' htor (p := p) (q := q) (D := D) (a := a) (γ := γ) (e := e)
      ha0 hγ0 he0 htri hsepA hsepB hVsm hτsm hτV hτann hτpos hβ hβ0 hβ1 hβr hband
      hΞ hϑ hΘ hψp hψq hΞarc hΞd hΞπ hϑarc hϑb hϑd hΘd hΞΘ hΘϑ
      hψp1 hψp0 hψpr hψq1 hψq0 hψqr hfsm hgsm hfV hgV
  -- ### Step 10: the sphere map
  have hdim3 : Module.finrank ℝ E + 1 = 3 := by omega
  set η : ℝ := a / 1000 with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith
  have ha4η : a / 4 < 3 * a / 4 - η := by rw [hηdef]; linarith
  have hg4η : γ / 4 < 3 * γ / 2 - η := by rw [hηdef]; linarith
  have h3a4η : 3 * a / 4 - η < 3 * a / 4 := by linarith
  have h3g2η : 3 * γ / 2 - η < 3 * γ / 2 := by linarith
  have h3a4v : 3 * a / 4 - η < v' := lt_trans h3a4η (by linarith [haρ'])
  have h3g2v : 3 * γ / 2 - η < v' := lt_trans h3g2η (by linarith [hsep4'])
  have hss : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  set Gcap0 : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)) :=
    fun x => (reindexLI hdim3).symm (northCap (ep ((2 * a)⁻¹ • Φp x))) with hGcap0def
  set Gqcap0 : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)) :=
    fun x => (reindexLI hdim3).symm (southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))))
    with hGqcap0def
  set Ggen0 : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)) :=
    fun x => (reindexLI hdim3).symm (sphereAmb (ξ x, Az x)) with hGgen0def
  have hGcap0norm : ∀ x : M,
      Work.Diff.C.rdist (I := I) (M := M) p x < 3 * a / 4 - η → ‖Gcap0 x‖ = 1 := by
    intro x hx
    have hv : Work.Diff.C.rdist (I := I) (M := M) p x < v :=
      lt_of_lt_of_le (lt_trans hx h3a4v) hv'v
    have hnorm : ‖Φp x‖ = Work.Diff.C.rdist (I := I) (M := M) p x := (hnormP' x hv).symm
    rw [hGcap0def, LinearIsometryEquiv.norm_map]
    refine norm_northCap _ ?_
    rw [LinearIsometryEquiv.norm_map]
    have h1 : ‖(2 * a)⁻¹ • Φp x‖
        = (2 * a)⁻¹ * Work.Diff.C.rdist (I := I) (M := M) p x := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos (by linarith : (0 : ℝ) < 2 * a), hnorm]
    rw [h1, ← div_eq_inv_mul, div_le_one (by linarith : (0 : ℝ) < 2 * a)]
    linarith
  have hGqcap0norm : ∀ x : M,
      Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2 - η → ‖Gqcap0 x‖ = 1 := by
    intro x hx
    have hv : Work.Diff.C.rdist (I := I) (M := M) q x < v :=
      lt_of_lt_of_le (lt_trans hx h3g2v) hv'v
    have hnorm : ‖Φq x‖ = Work.Diff.C.rdist (I := I) (M := M) q x := (hnormQ' x hv).symm
    rw [hGqcap0def, LinearIsometryEquiv.norm_map]
    refine norm_southCap _ ?_
    rw [norm_reflE hss]
    have h1 : ‖(2 * γ)⁻¹ • (-(eq (Φq x)))‖
        = (2 * γ)⁻¹ * Work.Diff.C.rdist (I := I) (M := M) q x := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos (by linarith : (0 : ℝ) < 2 * γ), norm_neg,
        LinearIsometryEquiv.norm_map, hnorm]
    rw [h1, ← div_eq_inv_mul, div_le_one (by linarith : (0 : ℝ) < 2 * γ)]
    linarith
  have hGgen0norm : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x → ‖Ggen0 x‖ = 1 := by
    intro x hx1 hx2
    rw [hGgen0def, LinearIsometryEquiv.norm_map]
    exact sphereAmbNorm (ξ x) (Az x) (hAz1 x ⟨hx1, hx2⟩)
  set G₀ : M → EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)) :=
    fun x => if Work.Diff.C.rdist (I := I) (M := M) p x < 3 * a / 4 - η then Gcap0 x
      else if Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2 - η then Gqcap0 x
      else Ggen0 x with hG₀def
  have hG₀norm : ∀ x : M, ‖G₀ x‖ = 1 := by
    intro x
    simp only [hG₀def]
    by_cases h1 : Work.Diff.C.rdist (I := I) (M := M) p x < 3 * a / 4 - η
    · rw [if_pos h1]; exact hGcap0norm x h1
    · rw [if_neg h1]
      by_cases h2 : Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2 - η
      · rw [if_pos h2]; exact hGqcap0norm x h2
      · rw [if_neg h2]
        exact hGgen0norm x (by linarith [ha4η, le_of_not_gt h1])
          (by linarith [hg4η, le_of_not_gt h2])
  set G : M → SphereD E := fun x => ⟨G₀ x, by
    rw [mem_sphere_zero_iff_norm]; exact hG₀norm x⟩ with hGdef
  -- ### Step 10b: the two agreements of the branches
  have hAgreeP : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      Work.Diff.C.rdist (I := I) (M := M) p x < 3 * a / 4 → Gcap0 x = Ggen0 x := by
    intro x hx1 hx2
    have hgx : γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x := by
      have h := htri x
      have h2 : 3 * a / 4 + 3 * γ / 2 < D := by linarith [hsep1']
      linarith
    have hfx0 : Work.Diff.C.rdist (I := I) (M := M) p x ≠ 0 := by linarith [ha0]
    have h2a : (0 : ℝ) < 2 * a := by linarith
    have hc1 : Work.Diff.C.rdist (I := I) (M := M) p x ≤ 3 * a / 4 := le_of_lt hx2
    have hrat : Work.Diff.C.rdist (I := I) (M := M) p x / (2 * a) ≤ 1 := by
      rw [div_le_one h2a]; linarith
    have hβx : β (τ x) = 0 := by
      have hτx : τ x = Work.Diff.C.rdist (I := I) (M := M) p x - a := hτval x hx1 (by linarith)
      rw [hτx]
      exact hβ0 _ (by linarith)
    have hξx : ξ x = Ξ (Work.Diff.C.rdist (I := I) (M := M) p x) := hξ1 x hx1 hgx hc1
    have hAzx : Az x = uE x := hAz_b0 x ⟨hx1, hgx⟩ hβx
    have huEx : uE x = (Work.Diff.C.rdist (I := I) (M := M) p x)⁻¹ • ep (Φp x) := by
      rw [show uE x = ep (u x) from rfl, hu_cap x hx1 hc1, map_smul]
    have hsin : Real.sin (Ξ (Work.Diff.C.rdist (I := I) (M := M) p x))
        = Work.Diff.C.rdist (I := I) (M := M) p x / (2 * a) := by
      rw [hΞarc _ (by linarith) hc1,
        Real.sin_arcsin (by rw [le_div_iff₀ h2a]; linarith) hrat]
    have hcos : Real.cos (Ξ (Work.Diff.C.rdist (I := I) (M := M) p x))
        = Real.sqrt (1 - (Work.Diff.C.rdist (I := I) (M := M) p x / (2 * a)) ^ 2) := by
      rw [hΞarc _ (by linarith) hc1, Real.cos_arcsin]
    have hnn : ‖ep ((2 * a)⁻¹ • Φp x)‖
        = Work.Diff.C.rdist (I := I) (M := M) p x / (2 * a) := by
      have h3a4v2 : 3 * a / 4 < v' := lt_trans (by linarith) haρ'
      have hv : Work.Diff.C.rdist (I := I) (M := M) p x < v :=
        lt_of_lt_of_le (lt_of_lt_of_le hx2 (le_of_lt h3a4v2)) hv'v
      rw [map_smul, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_eq_abs, abs_inv,
        abs_of_pos h2a, hnormP' x hv, inv_mul_eq_div]
    have key : northCap (ep ((2 * a)⁻¹ • Φp x))
        = sphereAmb (Ξ (Work.Diff.C.rdist (I := I) (M := M) p x), uE x) := by
      apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
      simp only [northCap, sphereAmb, ContinuousLinearEquiv.apply_symm_apply]
      have h0 : northCapComp (0 : Fin 3) (ep ((2 * a)⁻¹ • Φp x))
          = sphereAmbComp (0 : Fin 3)
              (Ξ (Work.Diff.C.rdist (I := I) (M := M) p x), uE x) := by
        rw [northCapComp_zero, sphereAmbComp_zero_, hsin, huEx]
        simp only [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        field_simp
      have h1 : northCapComp (1 : Fin 3) (ep ((2 * a)⁻¹ • Φp x))
          = sphereAmbComp (1 : Fin 3)
              (Ξ (Work.Diff.C.rdist (I := I) (M := M) p x), uE x) := by
        rw [northCapComp_one, sphereAmbComp_one_, hsin, huEx]
        simp only [map_smul, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        field_simp
      have h2 : northCapComp (2 : Fin 3) (ep ((2 * a)⁻¹ • Φp x))
          = sphereAmbComp (2 : Fin 3)
              (Ξ (Work.Diff.C.rdist (I := I) (M := M) p x), uE x) := by
        simp only [northCapComp_two, sphereAmbComp_two_, hcos, hnn]
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    simp only [hGcap0def, hGgen0def, hAzx, hξx, key]
  have hAgreeQ : ∀ x : M, a / 4 < Work.Diff.C.rdist (I := I) (M := M) p x →
      γ / 4 < Work.Diff.C.rdist (I := I) (M := M) q x →
      Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2 → Gqcap0 x = Ggen0 x := by
    intro x hx1 hx2 hx3
    have hgx0 : 0 < Work.Diff.C.rdist (I := I) (M := M) q x := by linarith [hγ0]
    have hfx0 : Work.Diff.C.rdist (I := I) (M := M) q x ≠ 0 := ne_of_gt hgx0
    have h2g : (0 : ℝ) < 2 * γ := by linarith
    have hc3 : Work.Diff.C.rdist (I := I) (M := M) q x ≤ 3 * γ / 2 := le_of_lt hx3
    have hrat : Work.Diff.C.rdist (I := I) (M := M) q x / (2 * γ) ≤ 1 := by
      rw [div_le_one h2g]; linarith
    have hβx : β (τ x) = 1 := by
      have h1 : 1 < τ x := hgap.2 x hx1 hx2 (by linarith)
      exact hβ1 _ (le_of_lt h1)
    have hξx : ξ x = Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x) :=
      hξ2 x hx1 hx2 hc3
    have hAzx : Az x = reflE s (vE2 x) := hAz_b1 x ⟨hx1, hx2⟩ (le_of_eq hβx.symm)
    have hvE2x : vE2 x = -(Work.Diff.C.rdist (I := I) (M := M) q x)⁻¹ • eq (Φq x) := by
      rw [show vE2 x = eq (vE x) from rfl,
        hvE_cap x hx1 (by linarith [hγ0]) hc3, map_smul]
    have hsin : Real.sin (Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x))
        = Work.Diff.C.rdist (I := I) (M := M) q x / (2 * γ) := by
      rw [Real.sin_pi_sub, hϑarc _ (by linarith) hc3,
        Real.sin_arcsin (by rw [le_div_iff₀ h2g]; linarith) hrat]
    have hcos : Real.cos (Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x))
        = -Real.sqrt (1 - (Work.Diff.C.rdist (I := I) (M := M) q x / (2 * γ)) ^ 2) := by
      rw [Real.cos_pi_sub, hϑarc _ (by linarith) hc3, Real.cos_arcsin]
    have hnn : ‖(2 * γ)⁻¹ • (-(eq (Φq x)))‖
        = Work.Diff.C.rdist (I := I) (M := M) q x / (2 * γ) := by
      have h3g2v2 : 3 * γ / 2 < v' := by linarith [hsep4']
      have hv : Work.Diff.C.rdist (I := I) (M := M) q x < v :=
        lt_of_lt_of_le (lt_of_lt_of_le hx3 (le_of_lt h3g2v2)) hv'v
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h2g, norm_neg,
        LinearIsometryEquiv.norm_map, hnormQ' x hv, inv_mul_eq_div]
    have key : southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))
        = sphereAmb (Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x),
            reflE s (vE2 x)) := by
      apply (EuclideanSpace.equiv (Fin 3) ℝ).injective
      simp only [southCap, sphereAmb, ContinuousLinearEquiv.apply_symm_apply]
      have h0 : southCapComp (0 : Fin 3) (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))
          = sphereAmbComp (0 : Fin 3)
              (Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x), reflE s (vE2 x)) := by
        rw [southCapComp_zero, sphereAmbComp_zero_, hsin, hvE2x, reflE_apply_zero,
          reflE_apply_zero]
        simp only [map_smul, WithLp.ofLp_smul, map_neg, WithLp.ofLp_neg, Pi.smul_apply,
          Pi.neg_apply, smul_eq_mul]
        field_simp
      have h1 : southCapComp (1 : Fin 3) (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))
          = sphereAmbComp (1 : Fin 3)
              (Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x), reflE s (vE2 x)) := by
        rw [southCapComp_one, sphereAmbComp_one_, hsin, hvE2x, reflE_apply_one,
          reflE_apply_one]
        simp only [map_smul, WithLp.ofLp_smul, map_neg, WithLp.ofLp_neg, Pi.smul_apply,
          Pi.neg_apply, smul_eq_mul]
        field_simp
      have h2 : southCapComp (2 : Fin 3) (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))
          = sphereAmbComp (2 : Fin 3)
              (Real.pi - ϑ (Work.Diff.C.rdist (I := I) (M := M) q x), reflE s (vE2 x)) := by
        simp only [southCapComp_two, sphereAmbComp_two_, hcos, norm_reflE hss, hnn]
      funext i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    simp only [hGqcap0def, hGgen0def, hAzx, hξx, key]
  -- ### Step 10c: smoothness of the three branch maps
  have hGcap0sm : ∀ x : M, Work.Diff.C.rdist (I := I) (M := M) p x < v →
      Work.Diff.C.rdist (I := I) (M := M) p x < 2 * a →
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞ Gcap0 x := by
    intro x hv h2ax
    rw [hGcap0def]
    have h2a : (0 : ℝ) < 2 * a := by linarith
    have hw : ‖ep ((2 * a)⁻¹ • Φp x)‖ < 1 := by
      have h1 : ‖(2 * a)⁻¹ • Φp x‖
          = (2 * a)⁻¹ * Work.Diff.C.rdist (I := I) (M := M) p x := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h2a, hnormP' x hv]
      rw [LinearIsometryEquiv.norm_map, h1, ← div_eq_inv_mul, div_lt_one h2a]
      exact h2ax
    have hinner : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞ (fun y => (2 * a)⁻¹ • Φp y) x :=
      (contMDiffAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (2 * a)⁻¹)).smul ((hΦp x hv).1)
    have hep : ContMDiffAt 𝓘(ℝ, TangentSpace I p) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun w : TangentSpace I p => ep w) ((2 * a)⁻¹ • Φp x) :=
      ((ep : TangentSpace I p →L[ℝ] EuclideanSpace ℝ (Fin 2)).contDiff.contMDiff.contMDiffAt)
    have hstep : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun y => ep ((2 * a)⁻¹ • Φp y)) x := hep.comp x hinner
    have hnorth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        northCap (ep ((2 * a)⁻¹ • Φp x)) :=
      (northCapFacts.1.contDiffAt
        ((isOpen_lt continuous_norm continuous_const).mem_nhds hw)).contMDiffAt
    have hL : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞
        (fun z => (reindexLI hdim3).symm z) (northCap (ep ((2 * a)⁻¹ • Φp x))) :=
      (((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))).contDiff.contMDiff.contMDiffAt)
    exact hL.comp x (ContMDiffAt.comp
      (f := fun y => ep ((2 * a)⁻¹ • Φp y)) x hnorth hstep)
  have hGqcap0sm : ∀ x : M, Work.Diff.C.rdist (I := I) (M := M) q x < v →
      Work.Diff.C.rdist (I := I) (M := M) q x < 2 * γ →
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞ Gqcap0 x := by
    intro x hv h2gx
    rw [hGqcap0def]
    have h2g : (0 : ℝ) < 2 * γ := by linarith
    have hw : ‖reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))‖ < 1 := by
      rw [norm_reflE hss]
      have h1 : ‖(2 * γ)⁻¹ • (-(eq (Φq x)))‖
          = (2 * γ)⁻¹ * Work.Diff.C.rdist (I := I) (M := M) q x := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h2g, norm_neg,
          LinearIsometryEquiv.norm_map, hnormQ' x hv]
      rw [h1, ← div_eq_inv_mul, div_lt_one h2g]
      exact h2gx
    have hCLM : ContMDiffAt 𝓘(ℝ, TangentSpace I q) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun w : TangentSpace I q => (2 * γ)⁻¹ • (-(eq w))) (Φq x) :=
      ((((2 * γ)⁻¹) • (-(eq : TangentSpace I q →L[ℝ] EuclideanSpace ℝ (Fin 2)))).contDiff.contMDiff.contMDiffAt)
    have hstep : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun y => (2 * γ)⁻¹ • (-(eq (Φq y)))) x :=
      hCLM.comp x ((hΦq x hv).1)
    have hrefl : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun z => reflE s z) ((2 * γ)⁻¹ • (-(eq (Φq x)))) :=
      ((contDiff_reflE s).contMDiff.contMDiffAt)
    have hstep2 : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
        (fun y => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x :=
      ContMDiffAt.comp (f := fun y => (2 * γ)⁻¹ • (-(eq (Φq y)))) x hrefl hstep
    have hsouth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
        southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))) :=
      (northCapFacts.2.2.1.contDiffAt
        ((isOpen_lt continuous_norm continuous_const).mem_nhds hw)).contMDiffAt
    have hL : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞
        (fun z => (reindexLI hdim3).symm z) (southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))) :=
      (((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))).contDiff.contMDiff.contMDiffAt)
    exact hL.comp x (ContMDiffAt.comp
      (f := fun y => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x hsouth hstep2)
  have hGgen0sm : ∀ x ∈ N, ContMDiffAt I
      𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞ Ggen0 x := by
    intro x hx
    rw [hGgen0def]
    have h1 : ContMDiffAt I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞
        (fun y => (ξ y, Az y)) x :=
      (hξsm.contMDiffAt (hNZ.mem_nhds hx)).prodMk_space
        (hAz_sm.contMDiffAt (hNZ.mem_nhds hx))
    have h2 : ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))
        𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ sphereAmb (ξ x, Az x) :=
      (sphereAmbSmooth.contMDiff.contMDiffAt)
    have h3 : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞
        (fun z => (reindexLI hdim3).symm z) (sphereAmb (ξ x, Az x)) :=
      (((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))).contDiff.contMDiff.contMDiffAt)
    exact h3.comp x (ContMDiffAt.comp (f := fun y => (ξ y, Az y)) x h2 h1)
  -- ### Step 10d: injectivity of the differential of the branch maps
  have hΦp_md : ∀ x : M, Work.Diff.C.rdist (I := I) (M := M) p x < v →
      MDifferentiableAt I 𝓘(ℝ, TangentSpace I p) Φp x :=
    fun x hv => ((hΦp x hv).1).mdifferentiableAt (by simp)
  have hΦq_md : ∀ x : M, Work.Diff.C.rdist (I := I) (M := M) q x < v →
      MDifferentiableAt I 𝓘(ℝ, TangentSpace I q) Φq x :=
    fun x hv => ((hΦq x hv).1).mdifferentiableAt (by simp)
  have hGExpP_md : ∀ w : TangentSpace I p,
      MDifferentiableAt 𝓘(ℝ, TangentSpace I p) I
        (fun u : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet' p u) w :=
    fun w => (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet' p w).mdifferentiableAt
      (by simp)
  have hGExpQ_md : ∀ w : TangentSpace I q,
      MDifferentiableAt 𝓘(ℝ, TangentSpace I q) I
        (fun u : TangentSpace I q => Submission.GlobalExp.GExp (cov := cov) hmet' q u) w :=
    fun w => (Submission.GExpSmooth.exists_contMDiffAt_GExp (cov := cov) hmet' q w).mdifferentiableAt
      (by simp)
  have hGcap0inj : ∀ x : M, Work.Diff.C.rdist (I := I) (M := M) p x < v →
      Work.Diff.C.rdist (I := I) (M := M) p x < 2 * a →
      Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        Gcap0 x) := by
    intro x hv h2ax
    have h2a : (0 : ℝ) < 2 * a := by linarith
    have hw : ‖ep ((2 * a)⁻¹ • Φp x)‖ < 1 := by
      have h1 : ‖(2 * a)⁻¹ • Φp x‖
          = (2 * a)⁻¹ * Work.Diff.C.rdist (I := I) (M := M) p x := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h2a, hnormP' x hv]
      rw [LinearIsometryEquiv.norm_map, h1, ← div_eq_inv_mul, div_lt_one h2a]
      exact h2ax
    have hpdiff : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y < v →
        MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (fun z : M => ep ((2 * a)⁻¹ • Φp z)) y := by
      intro y hy
      have h1a : ContMDiffAt I 𝓘(ℝ, TangentSpace I p) ∞
          (fun z : M => (2 * a)⁻¹ • Φp z) y :=
        (contMDiffAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) (c := (2 * a)⁻¹)).smul ((hΦp y hy).1)
      exact ((((ep : TangentSpace I p →L[ℝ] EuclideanSpace ℝ (Fin 2)).contDiff.contMDiff.contMDiffAt).comp
        y h1a).mdifferentiableAt (by simp))
    have hinv : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x) := by
      refine mfderivInjectiveOfLeftInverse (I := I) (M := M) (F := EuclideanSpace ℝ (Fin 2))
        (Φ := fun y : M => ep ((2 * a)⁻¹ • Φp y))
        (Ψ := fun w : EuclideanSpace ℝ (Fin 2) =>
          Submission.GlobalExp.GExp (cov := cov) hmet' p ((2 * a) • ep.symm w)) (x := x)
        (hpdiff x hv) ?_ ?_
      · have h1 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, TangentSpace I p)
            (fun z : EuclideanSpace ℝ (Fin 2) => (2 * a) • ep.symm z) (ep ((2 * a)⁻¹ • Φp x)) :=
          ((((2 * a) • (ep.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I p))).contDiff (n := ∞)).contMDiff.contMDiffAt
            |>.mdifferentiableAt (by simp)
        exact (hGExpP_md ((2 * a) • ep.symm (ep ((2 * a)⁻¹ • Φp x)))).comp
          (ep ((2 * a)⁻¹ • Φp x)) h1
      · filter_upwards [(Work.Diff.C.rdist_continuous (I := I) (M := M) p).isOpen_preimage _
          isOpen_Iio |>.mem_nhds hv] with y hy
        show Submission.GlobalExp.GExp (cov := cov) hmet' p
          ((2 * a) • ep.symm (ep ((2 * a)⁻¹ • Φp y))) = y
        rw [LinearIsometryEquiv.symm_apply_apply, smul_smul,
          mul_inv_cancel₀ (show (2 * a) ≠ 0 from ne_of_gt h2a), one_smul]
        exact (hΦp y hy).2.2
    have hkey : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        Gcap0 x := by
      rw [hGcap0def]
      exact hGcap0sm x hv h2ax |>.mdifferentiableAt (by simp)
    have hmf : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gcap0 x
        = ((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))).comp
          ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
              northCap (ep ((2 * a)⁻¹ • Φp x))).comp
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
              (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x)) := by
      rw [hGcap0def]
      have h1 := hpdiff x hv
      have h2 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          northCap (ep ((2 * a)⁻¹ • Φp x)) :=
        ((northCapFacts.1.contDiffAt
          ((isOpen_lt continuous_norm continuous_const).mem_nhds hw)).contMDiffAt).mdifferentiableAt
          (by simp)
      have h3 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          (fun z => (reindexLI hdim3).symm z) (northCap (ep ((2 * a)⁻¹ • Φp x))) :=
        ((((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))).contDiff (n := ∞)).contMDiff.contMDiffAt
          |>.mdifferentiableAt (by simp))
      have hA := mfderiv_comp (I := I) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) x h2 h1
      have hB := mfderiv_comp (I := I) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))) x h3
        (h2.comp x h1)
      rw [show (fun y : M => (reindexLI hdim3).symm (northCap (ep ((2 * a)⁻¹ • Φp y))))
          = (fun z => (reindexLI hdim3).symm z) ∘
            ((fun z : EuclideanSpace ℝ (Fin 2) => northCap z) ∘
              (fun y : M => ep ((2 * a)⁻¹ • Φp y))) from rfl]
      have hclm : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          (fun z => (reindexLI hdim3).symm z) (northCap (ep ((2 * a)⁻¹ • Φp x)))
          = ((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) := by
        rw [mfderiv_eq_fderiv]
        exact ContinuousLinearMap.fderiv (𝕜 := ℝ)
          ((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
      rw [hB, hA]
      simp only [Function.comp_apply]
      rw [hclm]
    have hm1 : Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          northCap (ep ((2 * a)⁻¹ • Φp x))) := by
      have h := northCapFacts.2.1 (ep ((2 * a)⁻¹ • Φp x)) hw
      rwa [mfderiv_eq_fderiv]
    have hM : Function.Injective
        ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            northCap (ep ((2 * a)⁻¹ • Φp x))).comp
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x)) := by
      intro u w huw
      have h1 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x) u
          = (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x) w :=
        hm1 (by simpa only [ContinuousLinearMap.comp_apply] using huw)
      exact hinv h1
    intro v v' hvv
    have h0 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gcap0 x)
        (v - v') = 0 := by
      rw [map_sub, hvv, sub_self]
    have h0' : (⇑(reindexLI hdim3).symm)
        (((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            northCap (ep ((2 * a)⁻¹ • Φp x))).comp
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x)) (v - v')) = 0 := by
      rw [hmf] at h0
      change (⇑(reindexLI hdim3).symm)
        (((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            northCap (ep ((2 * a)⁻¹ • Φp x))).comp
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x)) (v - v')) = 0 at h0
      exact h0
    have h1 : ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          northCap (ep ((2 * a)⁻¹ • Φp x))).comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (fun y : M => ep ((2 * a)⁻¹ • Φp y)) x)) (v - v') = 0 := by
      refine (reindexLI hdim3).symm.injective ?_
      rw [h0']
      exact (map_zero ((reindexLI hdim3).symm)).symm
    have h3 : v - v' = 0 := hM (by rw [h1]; exact (map_zero _).symm)
    exact sub_eq_zero.mp h3
  have hGqcap0inj : ∀ x : M, Work.Diff.C.rdist (I := I) (M := M) q x < v →
      Work.Diff.C.rdist (I := I) (M := M) q x < 2 * γ →
      Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        Gqcap0 x) := by
    intro x hv h2gx
    have h2g : (0 : ℝ) < 2 * γ := by linarith
    have hwm : ‖reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))‖ < 1 := by
      rw [norm_reflE hss]
      have h1 : ‖(2 * γ)⁻¹ • (-(eq (Φq x)))‖
          = (2 * γ)⁻¹ * Work.Diff.C.rdist (I := I) (M := M) q x := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos h2g, norm_neg,
          LinearIsometryEquiv.norm_map, hnormQ' x hv]
      rw [h1, ← div_eq_inv_mul, div_lt_one h2g]
      exact h2gx
    have hqdiff : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) q y < v →
        MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (fun z : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq z))))) y := by
      intro y hy
      have h1a : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
          (fun z : M => (2 * γ)⁻¹ • (-(eq (Φq z)))) y :=
        (((((2 * γ)⁻¹) • (-(eq : TangentSpace I q →L[ℝ] EuclideanSpace ℝ (Fin 2)))).contDiff
          (n := ∞)).contMDiff.contMDiffAt).comp y ((hΦq y hy).1)
      exact (((contDiff_reflE s).contMDiff.contMDiffAt.comp y h1a).mdifferentiableAt (by simp))
    have hinv : Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x) := by
      refine mfderivInjectiveOfLeftInverse (I := I) (M := M) (F := EuclideanSpace ℝ (Fin 2))
        (Φ := fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y)))))
        (Ψ := fun w : EuclideanSpace ℝ (Fin 2) =>
          Submission.GlobalExp.GExp (cov := cov) hmet' q
            (((2 * γ) • (-(eq.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I q))).comp
              (flip2 s) w)) (x := x)
        (hqdiff x hv) ?_ ?_
      · have hRm : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, TangentSpace I q)
            (fun w : EuclideanSpace ℝ (Fin 2) =>
              (((2 * γ) • (-(eq.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I q))).comp
                (flip2 s)) w) (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))) :=
          ((((((2 * γ) • (-(eq.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I q))).comp
            (flip2 s)).contDiff (n := ∞)).contMDiff.contMDiffAt).mdifferentiableAt (by simp))
        exact MDifferentiableAt.comp (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))
          (hGExpQ_md ((((2 * γ) • (-(eq.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I q))).comp
            (flip2 s)) (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))))) hRm
      · filter_upwards [(Work.Diff.C.rdist_continuous (I := I) (M := M) q).isOpen_preimage _
          isOpen_Iio |>.mem_nhds hv] with y hy
        show Submission.GlobalExp.GExp (cov := cov) hmet' q
          ((((2 * γ) • (-(eq.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I q))).comp
            (flip2 s)) (reflE s ((2 * γ)⁻¹ • (-(eq (Φq y)))))) = y
        have hval : ((((2 * γ) • (-(eq.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I q))).comp
            (flip2 s)) (reflE s ((2 * γ)⁻¹ • (-(eq (Φq y)))))) = Φq y := by
          simp only [ContinuousLinearMap.comp_apply, reflE_eq_flip2, flip2_involutive hss,
            ContinuousLinearMap.map_smul, ContinuousLinearMap.map_neg,
            ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, LinearIsometryEquiv.symm_apply_apply,
            smul_neg, neg_neg, smul_smul,
            mul_inv_cancel₀ (show (2 * γ) ≠ 0 from ne_of_gt h2g), one_smul]
          rw [show ((eq.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] TangentSpace I q) (eq (Φq y)))
            = Φq y from LinearIsometryEquiv.symm_apply_apply eq (Φq y)]
        rw [hval]
        exact (hΦq y hy).2.2
    have hkeyq : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        Gqcap0 x := by
      rw [hGqcap0def]
      exact (hGqcap0sm x hv h2gx).mdifferentiableAt (by simp)
    have hmfq : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gqcap0 x
        = ((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))).comp
          ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
              southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))).comp
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
              (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x)) := by
      rw [hGqcap0def]
      have h1 := hqdiff x hv
      have h2 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))) :=
        ((northCapFacts.2.2.1.contDiffAt
          ((isOpen_lt continuous_norm continuous_const).mem_nhds hwm)).contMDiffAt).mdifferentiableAt
          (by simp)
      have h3 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          (fun z => (reindexLI hdim3).symm z) (southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))) :=
        ((((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))).contDiff (n := ∞)).contMDiff.contMDiffAt
          |>.mdifferentiableAt (by simp))
      have hA := mfderiv_comp (I := I) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) x h2 h1
      have hB := mfderiv_comp (I := I) (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
        (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))) x h3
        (h2.comp x h1)
      have hclm : mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          (fun z => (reindexLI hdim3).symm z) (southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))))
          = ((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
              EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) := by
        rw [mfderiv_eq_fderiv]
        exact ContinuousLinearMap.fderiv (𝕜 := ℝ)
          ((reindexLI hdim3).symm : EuclideanSpace ℝ (Fin 3) →L[ℝ]
            EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
      rw [show (fun y : M => (reindexLI hdim3).symm
            (southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq y)))))))
          = (fun z => (reindexLI hdim3).symm z) ∘
            ((fun z : EuclideanSpace ℝ (Fin 2) => southCap z) ∘
              (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y)))))) from rfl]
      rw [hB, hA]
      simp only [Function.comp_apply]
      rw [hclm]
    have hm2 : Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))) := by
      have h := northCapFacts.2.2.2 (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x))))) hwm
      rwa [mfderiv_eq_fderiv]
    have hMq : Function.Injective
        ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))).comp
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x)) := by
      intro u w huw
      have h1 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x) u
          = (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x) w :=
        hm2 (by simpa only [ContinuousLinearMap.comp_apply] using huw)
      exact hinv h1
    intro v v' hvv
    have h0 : (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gqcap0 x)
        (v - v') = 0 := by
      rw [map_sub, hvv, sub_self]
    have h0' : (⇑(reindexLI hdim3).symm)
        (((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))).comp
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x)) (v - v')) = 0 := by
      rw [hmfq] at h0
      change (⇑(reindexLI hdim3).symm)
        (((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
            southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))).comp
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
            (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x)) (v - v')) = 0 at h0
      exact h0
    have h1 : ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          southCap (reflE s ((2 * γ)⁻¹ • (-(eq (Φq x)))))).comp
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
          (fun y : M => reflE s ((2 * γ)⁻¹ • (-(eq (Φq y))))) x)) (v - v') = 0 := by
      refine (reindexLI hdim3).symm.injective ?_
      rw [h0']
      exact (map_zero ((reindexLI hdim3).symm)).symm
    have h3 : v - v' = 0 := hMq (by rw [h1]; exact (map_zero _).symm)
    exact sub_eq_zero.mp h3
  have hGgen0inj : ∀ x ∈ N, Function.Injective
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Ggen0 x) := by
    intro x hx
    have h2md : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        (fun y : M => sphereAmb (ξ y, Az y)) x := by
      have hp : ContMDiffAt I 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞
          (fun y : M => (ξ y, Az y)) x :=
        (hξsm.contMDiffAt (hNZ.mem_nhds hx)).prodMk_space
          (hAz_sm.contMDiffAt (hNZ.mem_nhds hx))
      exact (((sphereAmbSmooth.contMDiff.contMDiffAt).comp x hp).mdifferentiableAt (by simp))
    have hsin : Real.sin (ξ x) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (hξrng x hx.1 hx.2).1 (hξrng x hx.1 hx.2).2)
    have hLUA := label_u_angForm (I := I) (M := M) hdim2 hNZ
      (fun y hy => (huE_sm' y hy).contMDiffWithinAt) huE1' huEV'
      (fun y hy => hnz y (le_of_lt hy.1) (by linarith [hy.2])) huErank'
      (fun y hy => hτV y hy.1 hy.2)
    have hkey : ∀ w : TangentSpace I x, angForm (Az := uE) x w = 0 →
        mfderiv I 𝓘(ℝ,ℝ) τ x w = 0 → w = 0 := by
      intro w h1 h2
      by_contra hw
      exact hLUA x hx w hw h2 h1
    have hL1V : angForm (Az := uE) x (V x) = 0 := by
      apply angForm_eq_zero_of_mvfderiv_eq_zero (Az := uE) (x := x) (v := V x)
      rw [show mvfderiv I uE x (V x) = NormedSpace.fromTangentSpace (uE x)
          ((mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) uE x) (V x)) from rfl,
        huEV' x hx, map_zero]
    obtain ⟨ϑ, hϑsm, hucirc, hAzcirc, hAzsm', hformula, hident⟩ :=
      azimuth_core (I := I) (M := M) hNZ hx hτsm
        (fun y hy => (huE_sm' y hy).contMDiffWithinAt) huE1' hβ hρsm hρper
    have hker : ∀ v : TangentSpace I x, mfderiv I 𝓘(ℝ,ℝ) ξ x v = 0 →
        angForm (I := I) (M := M) (Az := Az) x v = 0 → v = 0 := by
      intro v hξv hAv
      by_contra hv
      have hfinish : angForm (Az := uE) x v = 0 → False := by
        intro huEv
        set c : ℝ := mvfderiv I τ x v with hc
        have hu : v - c • V x = 0 :=
          hkey _ (by rw [map_sub, map_smul, huEv, hL1V, smul_zero, sub_zero])
            (by
              rw [map_sub, map_smul, hτV x hx.1 hx.2]
              simp only [hc, smul_eq_mul, mul_one]
              exact sub_self _)
        have hvv : v = c • V x := sub_eq_zero.mp hu
        have h3 : c = 0 := by
          have h := hξv
          rw [hvv, map_smul] at h
          exact (smul_eq_zero.mp h).resolve_right (hξV x hx.1 hx.2)
        rw [h3, zero_smul] at hvv
        exact hv hvv
      rcases eq_or_ne (β (τ x)) 0 with hb0 | hb0
      · refine hfinish ?_
        have hst : Real.smoothTransition (β (τ x)) = 0 :=
          Real.smoothTransition.zero_of_nonpos (le_of_eq hb0)
        have hder : deriv (Real.smoothTransition ∘ β) (τ x) = 0 := by
          rw [deriv_comp (τ x)
            ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable
              (by norm_num)).differentiableAt ((hβ.differentiable (by simp)).differentiableAt),
            deriv_smoothTransition_eq_zero (β (τ x)) (Or.inl (le_of_eq hb0)), zero_mul]
        have hcoef : angForm (Az := Az) x v = angForm (Az := uE) x v := by
          rw [hAzdef, hformula v, hident v, hst, hder]
          ring
        rw [← hcoef]; exact hAv
      · by_cases hb1 : 1 ≤ β (τ x)
        · refine hfinish ?_
          have hst : Real.smoothTransition (β (τ x)) = 1 :=
            Real.smoothTransition.one_of_one_le hb1
          have hder : deriv (Real.smoothTransition ∘ β) (τ x) = 0 := by
            rw [deriv_comp (τ x)
              ((Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable
                (by norm_num)).differentiableAt ((hβ.differentiable (by simp)).differentiableAt),
              deriv_smoothTransition_eq_zero (β (τ x)) (Or.inr hb1), zero_mul]
          have hcoef : angForm (Az := Az) x v = deriv ρ (ϑ x) * angForm (Az := uE) x v := by
            rw [hAzdef, hformula v, hident v, hst, hder]
            ring
          rw [hcoef] at hAv
          exact (mul_eq_zero.mp hAv).resolve_left (ne_of_gt (hρd (ϑ x)))
        · push_neg at hb1
          have hb0' : 0 < β (τ x) := lt_of_le_of_ne (hβr (τ x)).1 (Ne.symm hb0)
          have hξtw' := hξtw x hx.1 hx.2 hb0' hb1
          have hτv : mfderiv I 𝓘(ℝ,ℝ) τ x v = 0 := by
            have h := hξv
            rw [hξtw'] at h
            exact (smul_eq_zero.mp h).resolve_left (ne_of_gt (hΘd (τ x)))
          exact (hAz_tw x hx hb0' hb1 v hv hτv) hAv
    rw [hGgen0def]
    exact ambDIso (E := E) (I := I) (M := M) hdim3 h2md
      (sphere_immersion_criterion (I := I) (M := M) (ξ := ξ) (Az := Az)
        (((hξsm.contMDiffAt (hNZ.mem_nhds hx)).mdifferentiableAt (by simp)))
        (((hAz_sm.contMDiffAt (hNZ.mem_nhds hx)).mdifferentiableAt (by simp))) hsin hker)
  -- ### Step 10e: the branch analysis
  have hG₀main : ∀ x : M,
      ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞ G₀ x ∧
      Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        G₀ x) := by
    intro x
    have hPl : ∀ c : ℝ, IsOpen {y : M | Work.Diff.C.rdist (I := I) (M := M) p y < c} :=
      fun c => isOpen_lt (Work.Diff.C.rdist_continuous (I := I) (M := M) p) continuous_const
    have hPg : ∀ c : ℝ, IsOpen {y : M | c < Work.Diff.C.rdist (I := I) (M := M) p y} :=
      fun c => isOpen_lt continuous_const (Work.Diff.C.rdist_continuous (I := I) (M := M) p)
    have hQl : ∀ c : ℝ, IsOpen {y : M | Work.Diff.C.rdist (I := I) (M := M) q y < c} :=
      fun c => isOpen_lt (Work.Diff.C.rdist_continuous (I := I) (M := M) q) continuous_const
    have hQg : ∀ c : ℝ, IsOpen {y : M | c < Work.Diff.C.rdist (I := I) (M := M) q y} :=
      fun c => isOpen_lt continuous_const (Work.Diff.C.rdist_continuous (I := I) (M := M) q)
    by_cases h1 : Work.Diff.C.rdist (I := I) (M := M) p x < 3 * a / 4 - η
    · have hvp : Work.Diff.C.rdist (I := I) (M := M) p x < v :=
        lt_of_lt_of_le (lt_of_lt_of_le h1 (le_of_lt h3a4v)) hv'v
      have h2ap : Work.Diff.C.rdist (I := I) (M := M) p x < 2 * a :=
        lt_trans h1 (by linarith)
      have heq : Gcap0 =ᶠ[𝓝 x] G₀ := by
        filter_upwards [(hPl (3 * a / 4 - η)).mem_nhds h1] with y hy
        simp only [hG₀def]
        rw [if_pos hy]
      have hinj' : Function.Injective
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gcap0 x) :=
        hGcap0inj x hvp h2ap
      have hmf : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) G₀ x
          = mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gcap0 x :=
        heq.mfderiv_eq.symm
      refine ⟨(hGcap0sm x hvp h2ap).congr_of_eventuallyEq heq.symm, ?_⟩
      rw [hmf]
      exact hinj'
    · by_cases h2 : Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2 - η
      · have hxA : 3 * a / 4 - η < Work.Diff.C.rdist (I := I) (M := M) p x := by
          by_contra hcon
          push_neg at hcon
          have := htri x
          linarith [hsep1', hη0]
        have hvq : Work.Diff.C.rdist (I := I) (M := M) q x < v :=
          lt_of_lt_of_le (lt_of_lt_of_le h2 (le_of_lt h3g2v)) hv'v
        have h2gq : Work.Diff.C.rdist (I := I) (M := M) q x < 2 * γ :=
          lt_trans h2 (by linarith)
        have heq : Gqcap0 =ᶠ[𝓝 x] G₀ := by
          filter_upwards [(hPg (3 * a / 4 - η)).mem_nhds hxA, (hQl (3 * γ / 2 - η)).mem_nhds h2]
            with y hy1 hy2
          simp only [hG₀def]
          rw [if_neg (not_lt.mpr (le_of_lt hy1)), if_pos hy2]
        have hinj' : Function.Injective
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gqcap0 x) :=
          hGqcap0inj x hvq h2gq
        have hmf : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) G₀ x
            = mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Gqcap0 x :=
          heq.mfderiv_eq.symm
        refine ⟨(hGqcap0sm x hvq h2gq).congr_of_eventuallyEq heq.symm, ?_⟩
        rw [hmf]
        exact hinj'
      · have hfge : 3 * a / 4 - η ≤ Work.Diff.C.rdist (I := I) (M := M) p x := le_of_not_gt h1
        have hgge : 3 * γ / 2 - η ≤ Work.Diff.C.rdist (I := I) (M := M) q x := le_of_not_gt h2
        have hxN : x ∈ N := ⟨by linarith [ha4η, hfge], by linarith [hg4η, hgge]⟩
        have heq : Ggen0 =ᶠ[𝓝 x] G₀ := by
          rcases lt_or_eq_of_le hfge with hfxs | hfxs
          · rcases lt_or_eq_of_le hgge with hgxs | hgxs
            · filter_upwards [(hPg (3 * a / 4 - η)).mem_nhds hfxs,
                (hQg (3 * γ / 2 - η)).mem_nhds hgxs] with y hy1 hy2
              simp only [hG₀def]
              rw [if_neg (not_lt.mpr (le_of_lt hy1)), if_neg (not_lt.mpr (le_of_lt hy2))]
            · filter_upwards [hNZ.mem_nhds hxN,
                (hPg (3 * a / 4 - η)).mem_nhds hfxs,
                (hQl (3 * γ / 2)).mem_nhds (by
                  show Work.Diff.C.rdist (I := I) (M := M) q x < 3 * γ / 2
                  rw [← hgxs]; linarith [hη0])] with
                y hyN hy1 hy2
              simp only [hG₀def]
              by_cases hyb : Work.Diff.C.rdist (I := I) (M := M) q y < 3 * γ / 2 - η
              · rw [if_neg (not_lt.mpr (le_of_lt hy1)), if_pos hyb]
                exact (hAgreeQ y hyN.1 hyN.2 hy2).symm
              · rw [if_neg (not_lt.mpr (le_of_lt hy1)), if_neg hyb]
          · have hgxs : 3 * γ / 2 - η < Work.Diff.C.rdist (I := I) (M := M) q x := by
              by_contra hcon
              push_neg at hcon
              have := htri x
              linarith [hsep1', hη0]
            filter_upwards [hNZ.mem_nhds hxN,
              (hPl (3 * a / 4)).mem_nhds (by
                show Work.Diff.C.rdist (I := I) (M := M) p x < 3 * a / 4
                rw [← hfxs]; linarith [hη0]),
              (hQg (3 * γ / 2 - η)).mem_nhds hgxs] with y hyN hy1 hy2
            simp only [hG₀def]
            by_cases hyb : Work.Diff.C.rdist (I := I) (M := M) p y < 3 * a / 4 - η
            · rw [if_pos hyb]
              exact (hAgreeP y hyN.1 hy1).symm
            · rw [if_neg hyb, if_neg (not_lt.mpr (le_of_lt hy2))]
        have hinj' : Function.Injective
            (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Ggen0 x) :=
          hGgen0inj x hxN
        have hmf : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) G₀ x
            = mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) Ggen0 x :=
          heq.mfderiv_eq.symm
        refine ⟨(hGgen0sm x hxN).congr_of_eventuallyEq heq.symm, ?_⟩
        rw [hmf]
        exact hinj'
  -- ### Step 11: `G` is smooth on all of `M`, its differential is injective (hence invertible),
  -- and the workspace inverse function theorem (`isLocalDiffeomorphAt_infty_...`) converts this
  -- into `IsLocalDiffeomorph I (𝓡 (finrank ℝ E)) ∞ G`.
  have hG₀sm : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) ∞ G₀ :=
    fun x => (hG₀main x).1
  have hmems : ∀ x : M,
      G₀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1 := by
    intro x
    rw [mem_sphere_zero_iff_norm]
    exact hG₀norm x
  have hGsm : ContMDiff I (𝓡 (Module.finrank ℝ E)) ∞ G := by
    have hres := ContMDiff.codRestrict_sphere (n := Module.finrank ℝ E) hG₀sm hmems
    have hfun : G = Set.codRestrict G₀
        (sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1) hmems := by
      funext x
      rw [hGdef]
      rfl
    rw [hfun]
    exact hres
  have hchain : ∀ x : M, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) G₀ x
      = mfderiv (𝓡 (Module.finrank ℝ E))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
          (fun y : SphereD E => (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))) (G x)
        ∘SL mfderiv I (𝓡 (Module.finrank ℝ E)) G x := by
    intro x
    have hf : MDifferentiableAt I (𝓡 (Module.finrank ℝ E)) G x :=
      (hGsm x).mdifferentiableAt (by simp)
    have hg : MDifferentiableAt (𝓡 (Module.finrank ℝ E))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        (fun y : SphereD E => (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))) (G x) :=
      (contMDiff_coe_sphere
        (E := EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
        (n := Module.finrank ℝ E) (m := ∞)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (x := x) (f := G)
      (g := fun y : SphereD E => (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))) hg hf
    have hcoe : (fun y : SphereD E =>
        (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))) ∘ G = G₀ := by
      funext y
      rw [Function.comp_apply, hGdef]
    rwa [hcoe] at hcomp
  have hinj : ∀ x : M, Function.Injective (mfderiv I (𝓡 (Module.finrank ℝ E)) G x) := by
    intro x v w hvw
    have hvw' : mfderiv I (𝓡 (Module.finrank ℝ E)) G x (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have h0 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) G₀ x
        (v - w) = 0 := by
      have h1 : mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) G₀ x (v - w)
          = (mfderiv (𝓡 (Module.finrank ℝ E))
              𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))
              (fun y : SphereD E =>
                (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1)))) (G x))
            ((mfderiv I (𝓡 (Module.finrank ℝ E)) G x) (v - w)) := by
        rw [hchain x]
        rfl
      rw [h1, hvw', map_zero]
    exact sub_eq_zero.mp ((hG₀main x).2 (h0.trans (map_zero _).symm))
  have hinv : ∀ x : M, (mfderiv I (𝓡 (Module.finrank ℝ E)) G x).IsInvertible := by
    intro x
    have hrank : Module.finrank ℝ (TangentSpace I x)
        = Module.finrank ℝ (TangentSpace (𝓡 (Module.finrank ℝ E)) (G x)) := by
      rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from
            (tangentSpaceCastModel I x).toLinearEquiv.finrank_eq,
          show Module.finrank ℝ (TangentSpace (𝓡 (Module.finrank ℝ E)) (G x))
            = Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) from
            (tangentSpaceCastModel (𝓡 (Module.finrank ℝ E)) (G x)).toLinearEquiv.finrank_eq]
      exact finrank_euclideanSpace_fin.symm
    have hsurj : Function.Surjective (mfderiv I (𝓡 (Module.finrank ℝ E)) G x) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
        (V := TangentSpace I x)
        (V₂ := TangentSpace (𝓡 (Module.finrank ℝ E)) (G x)) hrank
        (f := (mfderiv I (𝓡 (Module.finrank ℝ E)) G x :
          TangentSpace I x →ₗ[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) (G x)))).mp (hinj x)
    have hbij : Function.Bijective
        ((mfderiv I (𝓡 (Module.finrank ℝ E)) G x :
          TangentSpace I x →ₗ[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) (G x))) :=
      ⟨hinj x, hsurj⟩
    let e : TangentSpace I x ≃ₗ[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) (G x) :=
      LinearEquiv.ofBijective _ hbij
    let eC : TangentSpace I x ≃L[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) (G x) :=
      e.toContinuousLinearEquiv
    have heC : (eC : TangentSpace I x →L[ℝ] TangentSpace (𝓡 (Module.finrank ℝ E)) (G x))
        = mfderiv I (𝓡 (Module.finrank ℝ E)) G x := by
      ext v
      rfl
    exact ⟨eC, heC⟩
  refine ⟨G, fun x => ?_⟩
  exact Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible
    (I := I) (I' := 𝓡 (Module.finrank ℝ E)) (f := G) (x := x) (U := Set.univ)
    Filter.univ_mem (hGsm.contMDiffOn) (BoundarylessManifold.isInteriorPoint' x) (hinv x)
/-- The construction is an everywhere-immersion, so it is a diffeomorphism onto the sphere. -/
theorem dim2_sphere_of_diam_pair
    (hdim2 : Module.finrank ℝ E = 2)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    {p q : M} {D : ℝ}
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (huniq : ∀ y : M, y ≠ q → Manifold.riemannianEDist I p y < ENNReal.ofReal D)
    (hfin : ∀ r s : M, Manifold.riemannianEDist I r s ≠ ⊤)
    (hFlow : SmoothFlow I M) :
    Nonempty (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ SphereD E) := by
  obtain ⟨G, hG⟩ :=
    dim2_exists_local_diffeo (I := I) (M := M) hdim2 cov htor hmet hpinch hpq hDgt hDlt
      hdiam huniq hfin hFlow
  exact Work.Diff.C.diffeo_of_local (I := I) (M := M) (E := E) (by omega) hG

end

theorem dim2_sphere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (hdim2 : Module.finrank ℝ E = 2)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    (hFlow : SmoothFlow I M) :
    Nonempty (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ SphereD E) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  haveI : Nonempty M := PathConnectedSpace.nonempty
  obtain ⟨g', hrest⟩ := dim2_diam_pair (I := I) (M := M) hdim2 cov htor hmet hpinch
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'⟩
  obtain ⟨hsmooth', hmet', hpinch', p, q, D, hpq, hDgt, hDlt, hdiam, huniq, hfin⟩ := hrest
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := hsmooth'
  exact dim2_sphere_of_diam_pair (I := I) (M := M) hdim2 cov htor hmet' hpinch'
    hpq hDgt hDlt hdiam huniq hfin hFlow

end Work.Diff.Dim2
