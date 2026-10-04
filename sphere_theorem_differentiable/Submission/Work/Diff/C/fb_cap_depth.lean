import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.rhess_comp
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.FarKit
import Submission.Work.Diff.C.fbcap.Defs
import Submission.Work.Diff.C.grad_smoothAt
import Submission.Work.Diff.C.rdist_continuous
import Submission.Work.Diff.C.rgrad_fcos
import Submission.HopfRinow
import Submission.HopfRinow2
import Submission.LensLoop
import Submission.RayChart
import Submission.GExpVelocity
import Submission.GExpTranslate
import Submission.GExpTwoSided
import Submission.HingeClosed
import Submission.Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve
import Submission.Work.Final.DimOne

set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission

set_option linter.unusedSectionVars false

/-! ## The pieces of the proof of `fb_cap_depth`

We prove the four ingredients isolated in `Submission.Work.Diff.C.fbcap.Defs`
(`RdistSmoothProp`, `HessNonnegProp`, `RayRdistEqProp`, `DiamFinrankOneProp`) and the arithmetic
lemma, then assemble them.

The main argument (the "midpoint" form of the far-ball bound): a point `z` in the far ball of
`q := qpt hmet p e (Fin.succ k)` has `L := rdist q z ≤ 3π/2` (triangle inequality and `hdiam`).
If `L > π`, the midpoint `x` of a minimising geodesic from `q` to `z` is at distance `L/2` from
both centres with `π/2 < L/2 ≤ 3π/4`, so `fcos q x = fcos z x = cos (L/2) > -1 + c`; hence the
distance functions are smooth at `x` with unit gradients, and for `V ⊥ γ'` the Hessian of
`F = rdist q + rdist z` at `x` is both ≥ 0 (global minimum) and ≤ `2 cot (L/2) + 2ε₁/sin (L/2)`
times `⟨V,V⟩`; this gives `cos (L/2) ≥ -ε₁`, and the arithmetic converts it into
`L ≤ π + arcsin (2ε₁)`. -/

section Pieces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]

/-- **The triangle inequality for the real-valued `rdist`.** -/
lemma fbcap_rdist_triangle (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x y z : M) :
    rdist (I := I) (M := M) x z
      ≤ rdist (I := I) (M := M) x y + rdist (I := I) (M := M) y z := by
  haveI : ConnectedSpace M := connectedSpace_iff_univ.mpr isPathConnected_univ.isConnected
  haveI : RegularSpace M := inferInstance
  have htri := Manifold.riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)
  have h1 : Manifold.riemannianEDist I x y ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor x y).ne
  have h2 : Manifold.riemannianEDist I y z ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor y z).ne
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) htri
  rw [ENNReal.toReal_add h1 h2] at h3
  simpa only [rdist] using h3

/-- `rdist` is symmetric. -/
lemma fbcap_rdist_comm (x y : M) :
    rdist (I := I) (M := M) x y = rdist (I := I) (M := M) y x := by
  rw [rdist, rdist, Manifold.riemannianEDist_comm]

/-- **Two unit vectors with inner product one are equal.** -/
lemma fbcap_eq_of_inner_eq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {a b : V} (ha : Inner.inner ℝ a a = 1) (hb : Inner.inner ℝ b b = 1)
    (hab : Inner.inner ℝ a b = 1) : a = b := by
  have h : Inner.inner ℝ (a - b) (a - b) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, ha, hb, real_inner_comm a b, hab]
    ring
  have h2 : ‖a - b‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact h
  have h3 : ‖a - b‖ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- **A non-zero vector orthogonal to a given non-zero vector**, in dimension `≥ 2`. -/
lemma fbcap_exists_orthogonal_ne_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (hdim : 2 ≤ Module.finrank ℝ V) {v : V} (hv : v ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ Inner.inner ℝ v w = 0 := by
  have h1 : Module.finrank ℝ (Submodule.span ℝ ({v} : Set V)) = 1 := by
    rw [finrank_span_singleton hv]
  have h2 : Module.finrank ℝ (Submodule.span ℝ ({v} : Set V)) +
      Module.finrank ℝ (Submodule.orthogonal (Submodule.span ℝ ({v} : Set V)))
      = Module.finrank ℝ V :=
    Submodule.finrank_add_finrank_orthogonal _
  have h3 : 1 ≤ Module.finrank ℝ (Submodule.orthogonal (Submodule.span ℝ ({v} : Set V))) := by
    omega
  have h4 : Submodule.orthogonal (Submodule.span ℝ ({v} : Set V)) ≠ ⊥ := by
    intro hbot
    rw [hbot] at h3
    simp at h3
  rw [Submodule.ne_bot_iff] at h4
  obtain ⟨w, hw, hwne⟩ := h4
  refine ⟨w, hwne, ?_⟩
  rw [Submodule.mem_orthogonal'] at hw
  rw [real_inner_comm]
  exact hw v (Submodule.mem_span_singleton_self v)

/-- **The second-derivative test, necessary condition (minimum version).**  If `f` is continuous
at `0`, has a (non-strict) local minimum at `0` and `deriv f` is differentiable at `0` with
derivative `c`, then `0 ≤ c`. -/
lemma fbcap_second_deriv_nonneg {f : ℝ → ℝ} {c : ℝ}
    (h1 : ContinuousAt f 0) (h2 : HasDerivAt (deriv f) c 0)
    (h4 : ∀ᶠ σ in 𝓝 (0 : ℝ), f 0 ≤ f σ) : 0 ≤ c := by
  by_contra hcon
  have hc : c < 0 := not_le.mp hcon
  have hmin : IsLocalMin f 0 := h4
  have hf0 : deriv f 0 = 0 := hmin.deriv_eq_zero
  have hcc : deriv (deriv f) 0 = c := h2.deriv
  have hmax : IsLocalMax f 0 :=
    isLocalMax_of_deriv_deriv_neg (by rw [hcc]; exact hc) hf0 h1
  have hmax' : ∀ᶠ σ in 𝓝 (0 : ℝ), f σ ≤ f 0 := hmax
  have hconst : f =ᶠ[𝓝 (0 : ℝ)] fun _ => f 0 := by
    filter_upwards [hmax', h4] with σ hσ₁ hσ₂
    exact le_antisymm hσ₁ hσ₂
  have hzero : deriv f =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    have h := Filter.EventuallyEq.deriv hconst
    rwa [deriv_const'] at h
  have hc0 : c = 0 := by
    rw [← hcc, Filter.EventuallyEq.deriv_eq hzero, deriv_const]
  linarith

/-- **The point `qpt hmet p e (Fin.succ k)` is at distance `π/2` from `p`.** -/
lemma fbcap_rdist_qpt_p (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hinit : InitData (I := I) (M := M) (cov := cov) hmet p e)
    {k : Fin (Module.finrank ℝ E)} :
    rdist (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) p
      = Real.pi / 2 := by
  set q : M := qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) with hq
  have hqG : q = Submission.GlobalExp.GExp (cov := cov) hmet p ((Real.pi / 2) • e k) := by
    simp [q, qpt, dirv]
  have hcos : Real.cos (rdist (I := I) (M := M) q p) = 0 := by
    have h := (hinit.2.2 k).1
    simpa [fcos] using h
  have hnorm : ‖e k‖ = 1 := by
    have h : Inner.inner ℝ (e k) (e k) = 1 := by simpa using hON k k
    have h2 : ‖e k‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact h
    nlinarith [norm_nonneg (e k)]
  have hle : rdist (I := I) (M := M) q p ≤ Real.pi / 2 := by
    have h : rdist (I := I) (M := M) p
        (Submission.GlobalExp.GExp (cov := cov) hmet p ((Real.pi / 2) • e k))
        ≤ Real.pi / 2 := by
      have hstep := Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet
        ((Real.pi / 2) • e k)
      have h2 : ‖(Real.pi / 2) • e k‖ = Real.pi / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [Real.pi_pos]), hnorm, mul_one]
      have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hstep
      rw [ENNReal.toReal_ofReal (norm_nonneg _), h2] at h3
      rw [rdist]; exact h3
    rw [fbcap_rdist_comm, hqG]
    exact h
  have h0 : 0 ≤ rdist (I := I) (M := M) q p := by rw [rdist]; exact ENNReal.toReal_nonneg
  rcases lt_or_eq_of_le hle with hlt | heq
  · exfalso
    have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos]) hlt
    rw [Real.cos_pi_div_two, hcos] at hmono
    linarith
  · exact heq

/-- **The distance identities along a minimising `GExp`-ray.** -/
lemma fbcap_ray_rdist_eq (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {q z : M} {u : TangentSpace I q} (hu : ‖u‖ = 1) {L : ℝ}
    (hL : 0 ≤ L) (hz : Submission.GlobalExp.GExp (cov := cov) hmet q (L • u) = z)
    (hmin : rdist (I := I) (M := M) q z = L) :
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      rdist (I := I) (M := M) q (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) = t ∧
      rdist (I := I) (M := M) z (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
        = L - t := by
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  intro t ht
  have ht0 : 0 ≤ t := ht.1
  have htL : t ≤ L := ht.2
  set γ : ℝ → M := fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (s • u) with hγ
  rcases eq_or_ne t 0 with ht_eq | ht_ne
  · -- the trivial endpoint
    subst ht_eq
    constructor
    · simp [rdist, Manifold.riemannianEDist_self]
    · simp only [zero_smul, sub_zero, Submission.GlobalExp.GExp_zero]
      rw [fbcap_rdist_comm]
      exact hmin
  have h1 : rdist (I := I) (M := M) q (γ t) ≤ t := by
    have h := Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet (t • u)
    rw [norm_smul, Real.norm_of_nonneg ht0, hu, mul_one] at h
    rw [rdist]
    calc (Manifold.riemannianEDist I q (γ t)).toReal
        ≤ (ENNReal.ofReal t).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = t := ENNReal.toReal_ofReal ht0
  have h2 : rdist (I := I) (M := M) z (γ t) ≤ L - t := by
    have hgt : Submission.GlobalExp.GExp (cov := cov) hmet (γ t)
        ((L - t) • Submission.Geodesic.curveVelocity (I := I) γ t) = z := by
      have htr := Submission.GExpTranslate.GExp_translate (cov := cov) hmet q (ξ := u) hu t (L - t)
      rw [show t + (L - t) = L from by ring, hz] at htr
      simpa only [hγ] using htr
    have h := Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet
      ((L - t) • Submission.Geodesic.curveVelocity (I := I) γ t)
    rw [hgt] at h
    have hnorm : ‖(L - t) • Submission.Geodesic.curveVelocity (I := I) γ t‖ = L - t := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith : 0 ≤ L - t),
        Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hu_ne ht_ne,
        hu, mul_one]
    rw [hnorm] at h
    rw [rdist, ← Manifold.riemannianEDist_comm (I := I) (x := γ t) (y := z)]
    calc (Manifold.riemannianEDist I (γ t) z).toReal
        ≤ (ENNReal.ofReal (L - t)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = L - t := ENNReal.toReal_ofReal (by linarith)
  have h3 : t ≤ rdist (I := I) (M := M) q (γ t) := by
    have htri := fbcap_rdist_triangle (I := I) (M := M) (cov := cov) hmet htor q (γ t) z
    have h2' : rdist (I := I) (M := M) (γ t) z = rdist (I := I) (M := M) z (γ t) :=
      fbcap_rdist_comm (I := I) (M := M) (γ t) z
    rw [hmin] at htri
    linarith
  have h4 : L - t ≤ rdist (I := I) (M := M) z (γ t) := by
    have htri := fbcap_rdist_triangle (I := I) (M := M) (cov := cov) hmet htor z (γ t) q
    have h1' : rdist (I := I) (M := M) (γ t) q = rdist (I := I) (M := M) q (γ t) :=
      fbcap_rdist_comm (I := I) (M := M) (γ t) q
    rw [fbcap_rdist_comm (I := I) (M := M) z q, hmin] at htri
    linarith
  exact ⟨le_antisymm h1 h3, le_antisymm h2 h4⟩

/-- **The covariant Hessian of a smooth function with a global minimum is PSD.** -/
lemma fbcap_hess_nonneg (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x)
    (hmin : ∀ y : M, F x ≤ F y) (V : TangentSpace I x) :
    0 ≤ rhess (I := I) (M := M) cov F x V V := by
  rcases eq_or_ne V 0 with rfl | hV0
  · rw [rhess]; simp
  set ξ : TangentSpace I x := Submission.GlobalExp.unitOf V hV0 with hξdef
  have hξ : ‖ξ‖ = 1 := Submission.GlobalExp.unitOf_norm V hV0
  set dl : ℝ := Submission.GlobalExp.geodDelta (cov := cov) hmet with hdldef
  have hdl : 0 < dl := Submission.GlobalExp.geodDelta_pos hmet
  set T : ℝ := 1 with hTdef
  have hT0 : 0 ≤ T := by rw [hTdef]; norm_num
  set σ : ℝ → M := Submission.GlobalExp.geodCurve (cov := cov) hmet T hT0 x ξ hξ with hσdef
  obtain ⟨hσ0, hσv0, hσsm, hσgeo, hσsp⟩ :=
    Submission.GlobalExp.geodCurve_spec (cov := cov) hmet T hT0 x ξ hξ
  have hmem : (0 : ℝ) ∈ Set.Ioo (-dl) (T + dl) := Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hopen : IsOpen (Set.Ioo (-dl) (T + dl)) := isOpen_Ioo
  have hσsm0 : CMDiffAt ∞ σ 0 := hσsm.contMDiffAt (hopen.mem_nhds hmem)
  have hσmd0 : MDifferentiableAt 𝓘(ℝ) I σ 0 := hσsm0.mdifferentiableAt (by simp)
  have hσne : Submission.Geodesic.curveVelocity (I := I) σ 0 ≠ 0 := by
    rw [hσv0]
    intro h
    rw [h, norm_zero] at hξ
    norm_num at hξ
  have hFmd0 : MDiffAt (T% (rgrad (I := I) F)) (σ 0) := by
    have h := (grad_smoothAt (I := I) (M := M) hF).mdifferentiableAt (by simp)
    simpa only [hσdef, hσ0] using h
  have hc2 : HasDerivAt
      (fun τ : ℝ => mvfderiv I F (σ τ) (Submission.Geodesic.curveVelocity (I := I) σ τ))
      (rhess (I := I) (M := M) cov F (σ 0) (Submission.Geodesic.curveVelocity (I := I) σ 0)
        (Submission.Geodesic.curveVelocity (I := I) σ 0)) 0 :=
    hasDerivAt_secondDeriv_along_geodesic (cov := cov) (γ := σ) (V := Set.Ioo (-dl) (T + dl))
      (t := 0) hmet hopen hmem hσsm (fun τ hτ => hσgeo τ hτ) hσne (f := F) hFmd0
  set φ : ℝ → ℝ := fun τ => F (σ τ) with hφdef
  have hFx : CMDiffAt ∞ F (σ 0) := by
    rw [hσdef, hσ0]
    exact hF
  have hφsm : CMDiffAt ∞ φ 0 := hFx.comp (0 : ℝ) hσsm0
  -- `F` is `C^1` on a neighbourhood of `x`, hence differentiable along the ray near `0`
  have hF1 : CMDiffAt (((1 : ℕ) : ENat) : WithTop ENat) F x :=
    hF.of_le (by simp)
  obtain ⟨U, hU, hFU⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (f := F) (x := x)
      (hn := by simp)).mp hF1
  have hσ0' : σ 0 = x := by rw [hσdef]; exact hσ0
  have hev_F_diff : ∀ᶠ τ in 𝓝 (0 : ℝ), MDifferentiableAt I 𝓘(ℝ, ℝ) F (σ τ) := by
    have hnear : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) F y := by
      filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU)] with y hy
      exact (((hFU.mono interior_subset) y hy).contMDiffAt (isOpen_interior.mem_nhds hy)).mdifferentiableAt
        (by simp)
    have hnear' : ∀ᶠ y in 𝓝 (σ 0), MDifferentiableAt I 𝓘(ℝ, ℝ) F y := by
      rw [hσ0']
      exact hnear
    exact hσsm0.continuousAt.eventually hnear'
  -- the chain rule near `0`
  have hev_chain : (fun τ : ℝ => mvfderiv I F (σ τ)
        (Submission.Geodesic.curveVelocity (I := I) σ τ)) =ᶠ[𝓝 (0 : ℝ)] deriv φ := by
    filter_upwards [isOpen_Ioo.mem_nhds hmem, hev_F_diff] with τ hτ hFmd
    have hσmd : MDifferentiableAt 𝓘(ℝ) I σ τ :=
      (hσsm.contMDiffAt (hopen.mem_nhds hτ)).mdifferentiableAt (by simp)
    have hcr := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := F) (γ := σ) (t := τ) hFmd hσmd
    simpa only [hφdef, Function.comp_def, Submission.Geodesic.curveVelocity_apply] using hcr
  have h2deriv : HasDerivAt (deriv φ) (rhess (I := I) (M := M) cov F (σ 0)
      (Submission.Geodesic.curveVelocity (I := I) σ 0)
      (Submission.Geodesic.curveVelocity (I := I) σ 0)) 0 :=
    hc2.congr_of_eventuallyEq hev_chain.symm
  have hbase_geod : 0 ≤ rhess (I := I) (M := M) cov F (σ 0)
      (Submission.Geodesic.curveVelocity (I := I) σ 0)
      (Submission.Geodesic.curveVelocity (I := I) σ 0) := by
    refine fbcap_second_deriv_nonneg hφsm.continuousAt h2deriv ?_
    filter_upwards with τ
    have h := hmin (σ τ)
    show φ 0 ≤ φ τ
    rw [hφdef]
    show F (σ 0) ≤ F (σ τ)
    rw [hσdef, hσ0]
    exact h
  have hbase : 0 ≤ rhess (I := I) (M := M) cov F x ξ ξ := by
    have h := hbase_geod
    rw [hσdef] at h
    rw [hσ0, hσv0] at h
    exact h
  -- scaling back from `ξ` to `V`
  have hVeq : ‖V‖ • ξ = V := by
    rw [hξdef, Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hV0), one_smul]
  have hbilin : ∀ (a b : ℝ) (v w : TangentSpace I x),
      rhess (I := I) (M := M) cov F x (a • v) (b • w) = a * b * rhess (I := I) (M := M) cov F x v w := by
    intro a b v w
    rw [rhess, rhess, map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  have hscaled : rhess (I := I) (M := M) cov F x V V
      = ‖V‖ ^ 2 * rhess (I := I) (M := M) cov F x ξ ξ := by
    have h : rhess (I := I) (M := M) cov F x (‖V‖ • ξ) (‖V‖ • ξ)
        = ‖V‖ ^ 2 * rhess (I := I) (M := M) cov F x ξ ξ := by
      rw [hbilin]; ring
    rwa [hVeq] at h
  rw [hscaled]
  positivity

/-- **The distance function is smooth with unit gradient where `cos ∘ rdist` is.** -/
lemma fbcap_rdist_smooth (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    {c : ℝ} (hc : 0 < c) {q x : M}
    (hx0 : 0 < rdist (I := I) (M := M) q x)
    (hxpi : rdist (I := I) (M := M) q x < Real.pi)
    (hx : -1 + c < fcos (I := I) (M := M) q x)
    (hsmC : ∀ y : M, -1 + c ≤ fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
        (fcos (I := I) (M := M) q) y)
    (hgrad : ∀ y : M, -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
        (fun y : M ↦ rdist (I := I) (M := M) q y) x ∧
      Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
        (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
        = 1 := by
  have hsmf : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fcos (I := I) (M := M) q) x := hsmC x (le_of_lt hx)
  have hcont : Continuous (fun y : M ↦ rdist (I := I) (M := M) q y) :=
    rdist_continuous (I := I) (M := M) q
  -- near `x`, `rdist q = arccos ∘ fcos q`
  have hev : (fun y : M ↦ rdist (I := I) (M := M) q y) =ᶠ[𝓝 x]
      fun y : M ↦ Real.arccos (fcos (I := I) (M := M) q y) := by
    filter_upwards [hcont.continuousAt.eventually (isOpen_Ioo.mem_nhds
      (show rdist (I := I) (M := M) q x ∈ Set.Ioo (0 : ℝ) Real.pi from ⟨hx0, hxpi⟩))]
      with y hy
    show rdist (I := I) (M := M) q y = Real.arccos (fcos (I := I) (M := M) q y)
    rw [show fcos (I := I) (M := M) q y = Real.cos (rdist (I := I) (M := M) q y) from rfl,
      Real.arccos_cos (le_of_lt hy.1) (le_of_lt hy.2)]
  have hcosx : fcos (I := I) (M := M) q x ≠ -1 := by
    intro h
    rw [h] at hx
    linarith
  have hcosx1 : fcos (I := I) (M := M) q x ≠ 1 := by
    intro h
    have h2 : Real.cos (rdist (I := I) (M := M) q x) = 1 := by
      simpa only [fcos] using h
    have h3 : rdist (I := I) (M := M) q x = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).mp h2
    linarith
  have hsmarc : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun y : M ↦ Real.arccos (fcos (I := I) (M := M) q y)) x :=
    (Real.contDiffAt_arccos hcosx hcosx1).comp_contMDiffAt hsmf
  have hsmd : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun y : M ↦ rdist (I := I) (M := M) q y) x :=
    hsmarc.congr_of_eventuallyEq hev
  refine ⟨hsmd, ?_⟩
  -- the eikonal identity for `rdist q`
  have hrg := rgrad_fcos (I := I) (M := M) (q := q) hsmd
  have hgf := hgrad x hx
  have hsin : Real.sin (rdist (I := I) (M := M) q x) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 hxpi)
  have h1 : 1 - (fcos (I := I) (M := M) q x) ^ 2
      = Real.sin (rdist (I := I) (M := M) q x) ^ 2 := by
    rw [show fcos (I := I) (M := M) q x = Real.cos (rdist (I := I) (M := M) q x) from rfl]
    linarith [Real.sin_sq_add_cos_sq (rdist (I := I) (M := M) q x)]
  have h2 : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x)
      = Real.sin (rdist (I := I) (M := M) q x) ^ 2
        * Inner.inner ℝ
          (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
          (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x) := by
    rw [hrg, real_inner_smul_left, real_inner_smul_right]
    ring
  have h3 : Real.sin (rdist (I := I) (M := M) q x) ^ 2
        * Inner.inner ℝ
          (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
          (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
      = Real.sin (rdist (I := I) (M := M) q x) ^ 2 := by
    rw [← h2, hgf, h1]
  have hs2 : Real.sin (rdist (I := I) (M := M) q x) ^ 2 ≠ 0 := pow_ne_zero 2 hsin
  have h4 : Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
        (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x) = 1 := by
    exact mul_left_cancel₀ hs2 (by rw [h3, mul_one])
  exact h4

/-- **The numerical endgame of the far-ball bound.** -/
lemma fbcap_arith {ε L : ℝ} (hε : 0 ≤ ε) (hε2 : 2 * ε ≤ 1) (hLpi : Real.pi < L)
    (hL : L ≤ 3 * Real.pi / 2) (hcos : -ε ≤ Real.cos (L / 2)) :
    L ≤ Real.pi + Real.arcsin (2 * ε) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  set θ : ℝ := L / 2 - Real.pi / 2 with hθdef
  have hθ0 : 0 < θ := by rw [hθdef]; linarith
  have hθle : θ ≤ Real.pi / 4 := by rw [hθdef]; linarith
  have hcosθ : Real.cos (L / 2) = -Real.sin θ := by
    rw [hθdef]
    rw [show L / 2 = Real.pi / 2 + (L / 2 - Real.pi / 2) from by ring, Real.cos_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hsinθ : Real.sin θ ≤ ε := by linarith [hcos, hcosθ]
  have h2θ : 2 * θ ≤ Real.pi / 2 := by linarith
  have hsin2 : Real.sin (2 * θ) ≤ 2 * ε := by
    have hsinθnn : 0 ≤ Real.sin θ :=
      le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith))
    have hcosle : Real.cos θ ≤ 1 := Real.cos_le_one θ
    rw [Real.sin_two_mul]
    calc 2 * Real.sin θ * Real.cos θ ≤ 2 * Real.sin θ * 1 :=
          mul_le_mul_of_nonneg_left hcosle (by positivity)
      _ = 2 * Real.sin θ := by ring
      _ ≤ 2 * ε := by linarith
  have hmain : 2 * θ ≤ Real.arcsin (2 * ε) := by
    have h := Real.arcsin_le_arcsin hsin2
    rwa [Real.arcsin_sin (by linarith) h2θ] at h
  calc L = Real.pi + 2 * θ := by rw [hθdef]; ring
    _ ≤ Real.pi + Real.arcsin (2 * ε) := by linarith

/-- **Additivity of the covariant Hessian in the function slot.**
`rhess cov (F + G) x V W = rhess cov F x V W + rhess cov G x V W` where both functions are smooth
at `x`: the gradients add (pointwise near `x`, by `mfderiv_add`), `cov` respects the eventual
equality and is additive on sections. -/
lemma fbcap_rhess_add {F G : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x) (hG : CMDiffAt ∞ G x)
    (V W : TangentSpace I x) :
    rhess (I := I) (M := M) cov (fun y : M => F y + G y) x V W
      = rhess (I := I) (M := M) cov F x V W + rhess (I := I) (M := M) cov G x V W := by
  have hFmd : MDiffAt (T% (rgrad (I := I) F)) x :=
    (grad_smoothAt (I := I) (M := M) hF).mdifferentiableAt (by simp)
  have hGmd : MDiffAt (T% (rgrad (I := I) G)) x :=
    (grad_smoothAt (I := I) (M := M) hG).mdifferentiableAt (by simp)
  have hFGmd : MDiffAt (T% (rgrad (I := I) (fun y : M => F y + G y))) x :=
    (grad_smoothAt (I := I) (M := M) (hF.add hG)).mdifferentiableAt (by simp)
  -- both functions are `C^1` on a neighbourhood of `x`
  have hFd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) F y := by
    have h1 : CMDiffAt (((1 : ℕ) : ENat) : WithTop ENat) F x := hF.of_le (by simp)
    obtain ⟨U, hU, hFU⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (f := F) (x := x) (hn := by simp)).mp h1
    filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU)] with y hy
    exact (((hFU.mono interior_subset) y hy).contMDiffAt (isOpen_interior.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hGd : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) G y := by
    have h1 : CMDiffAt (((1 : ℕ) : ENat) : WithTop ENat) G x := hG.of_le (by simp)
    obtain ⟨U, hU, hGU⟩ :=
      (contMDiffAt_iff_contMDiffOn_nhds (f := G) (x := x) (hn := by simp)).mp h1
    filter_upwards [isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU)] with y hy
    exact (((hGU.mono interior_subset) y hy).contMDiffAt (isOpen_interior.mem_nhds hy)).mdifferentiableAt
      (by simp)
  -- the gradients add near `x`
  have hev : (fun y : M => rgrad (I := I) (M := M) (fun z : M => F z + G z) y)
      =ᶠ[𝓝 x] (rgrad (I := I) (M := M) F + rgrad (I := I) (M := M) G) := by
    filter_upwards [hFd, hGd] with y hFy hGy
    show rgrad (I := I) (M := M) (fun z : M => F z + G z) y
        = rgrad (I := I) (M := M) F y + rgrad (I := I) (M := M) G y
    have hm := mfderiv_add (I := I) hFy hGy
    have hfun : (fun z : M => F z + G z) = (F + G) := rfl
    rw [hfun]
    simp only [rgrad]
    rw [hm, map_add]
  have hmd' : MDiffAt (T% (rgrad (I := I) (M := M) F + rgrad (I := I) (M := M) G)) x :=
    ((grad_smoothAt (I := I) (M := M) hF).add_section
      (grad_smoothAt (I := I) (M := M) hG)).mdifferentiableAt (by simp)
  rw [rhess, rhess, rhess]
  rw [show cov (rgrad (I := I) (M := M) (fun y : M => F y + G y)) x
      = cov (rgrad (I := I) (M := M) F + rgrad (I := I) (M := M) G) x from
    (cov.isCovariantDerivativeOn (s := Set.univ)).congr_of_eventuallyEq hFGmd hmd'
      Filter.univ_mem hev]
  rw [(cov.isCovariantDerivativeOn (s := Set.univ)).add hFmd hGmd]
  rw [add_apply, inner_add_left]

/-- **The diameter in dimension one.**  On a compact boundaryless one-dimensional manifold the
unit-speed `GExp`-ray from any point is periodic with a minimal period `P`, covers `M`, and the
distance function on the circle is the distance of the representatives: hence
`diam M = P/2 = max_y d(p,y)`, and the hypothesis `rdist p y ≤ π` gives `P ≤ 2π`. -/
lemma fbcap_diam_one (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) (hdim : Module.finrank ℝ E = 1) {p : M}
    (hp : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi) (x y : M) :
    rdist (I := I) (M := M) x y ≤ Real.pi := by
  haveI : ConnectedSpace M := connectedSpace_iff_univ.mpr isPathConnected_univ.isConnected
  haveI : RegularSpace M := inferInstance
  -- a unit vector at `p`
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
  set u : TangentSpace I p := Submission.GlobalExp.unitOf v₀ hv₀ with hudef
  have hu : ‖u‖ = 1 := Submission.GlobalExp.unitOf_norm v₀ hv₀
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  -- the ray is periodic, with a minimal period `P`
  obtain ⟨a, b, hab, heq⟩ :=
    Work.Final.DimOne.exists_ne_of_GExp_ray (I := I) (M := M) (cov := cov) hmet htor hdim p u hu
  obtain ⟨Q, hQpos, -, hQper⟩ :=
    Work.Final.DimOne.period_of_GExp_ray_eq (I := I) (M := M) (cov := cov) hmet hdim p u hu_ne hab heq
  obtain ⟨ρ, hρpos, hρbd⟩ :=
    Work.Final.DimOne.periods_bddBelow (I := I) (M := M) (cov := cov) hmet htor p u hu
  obtain ⟨P, hPpos, hPper, hPmin⟩ :=
    Work.Final.DimOne.exists_minimal_period (I := I) (M := M) (cov := cov) hmet p u hu_ne
      ⟨Q, hQpos, hQper⟩ ⟨ρ, hρpos, hρbd⟩
  have hcont := Work.Final.DimOne.continuous_rayLift (I := I) (M := M) (cov := cov) hmet p u hu_ne
    hPpos hPper
  have hsurj := Work.Final.DimOne.surjective_rayLift (I := I) (M := M) (cov := cov) hmet htor hdim
    p u hu_ne hPpos hPper hcont
  set γ : ℝ → M := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (τ • u) with hγdef
  have hper' : ∀ τ : ℝ, γ (τ - P) = γ τ := by
    intro τ
    have h := hPper (τ - P)
    rw [sub_add_cancel] at h
    simpa only [hγdef] using h.symm
  -- ## the lower bound at the antipode
  have hlow : P / 2 ≤ rdist (I := I) (M := M) p (γ (P / 2)) := by
    obtain ⟨v, hvG, hvd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor p (γ (P / 2))
    obtain ⟨c, hc⟩ := Work.Final.DimOne.exists_smul_eq_of_finrank_eq_one hdim hu_ne (v := v)
    have hℓc : rdist (I := I) (M := M) p (γ (P / 2)) = |c| := by
      rw [rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v), hc, norm_smul, hu, mul_one,
        Real.norm_eq_abs]
    have hcG : Submission.GlobalExp.GExp (cov := cov) hmet p (c • u)
        = Submission.GlobalExp.GExp (cov := cov) hmet p ((P / 2) • u) := by
      rw [← hc]
      simpa only [hγdef] using hvG
    have hcase : c = P / 2 ∨ P ≤ |c - P / 2| := by
      by_cases h : c = P / 2
      · exact Or.inl h
      · refine Or.inr ?_
        obtain ⟨Q', hQ'pos, hQ'le, hQ'per⟩ :=
          Work.Final.DimOne.period_of_GExp_ray_eq (I := I) (M := M) (cov := cov) hmet hdim p u hu_ne
            h hcG
        calc P ≤ Q' := hPmin Q' hQ'pos hQ'per
          _ ≤ |P / 2 - c| := hQ'le
          _ = |c - P / 2| := abs_sub_comm _ _
    rcases hcase with hcase | hcase
    · rw [hℓc, hcase, abs_of_pos (show (0 : ℝ) < P / 2 by linarith [hPpos])]
    · rw [hℓc]
      have hP2 : (0 : ℝ) < P / 2 := by linarith [hPpos]
      have h1 : |c - P / 2| ≤ |c| + P / 2 := by
        calc |c - P / 2| = |c + -(P / 2)| := by ring_nf
          _ ≤ |c| + |-(P / 2)| := abs_add_le c (-(P / 2))
          _ = |c| + P / 2 := by rw [abs_neg, abs_of_pos hP2]
      linarith
  have hP2π : P ≤ 2 * Real.pi := by
    have h := hp (γ (P / 2))
    linarith
  -- ## the diameter bound on the circle
  haveI : Fact (0 < P) := ⟨hPpos⟩
  have hdiam : rdist (I := I) (M := M) x y ≤ P / 2 := by
    obtain ⟨ξ, hξ⟩ := hsurj x
    obtain ⟨η, hη⟩ := hsurj y
    set s : ℝ := (AddCircle.equivIco (p := P) (0 : ℝ) ξ).1 with hsdef
    set t : ℝ := (AddCircle.equivIco (p := P) (0 : ℝ) η).1 with htdef
    have hs0 : 0 ≤ s := (AddCircle.equivIco (p := P) (0 : ℝ) ξ).2.1
    have hsP : s < P := by
      have h : ((AddCircle.equivIco (p := P) (0 : ℝ) ξ).1 : ℝ) < P := by
        have h0 := (AddCircle.equivIco (p := P) (0 : ℝ) ξ).2.2
        simpa only [zero_add] using h0
      rwa [hsdef]
    have ht0 : 0 ≤ t := (AddCircle.equivIco (p := P) (0 : ℝ) η).2.1
    have htP : t < P := by
      have h : ((AddCircle.equivIco (p := P) (0 : ℝ) η).1 : ℝ) < P := by
        have h0 := (AddCircle.equivIco (p := P) (0 : ℝ) η).2.2
        simpa only [zero_add] using h0
      rwa [htdef]
    have hsc : (s : AddCircle P) = ξ := by rw [hsdef]; exact AddCircle.coe_equivIco
    have htc : (t : AddCircle P) = η := by rw [htdef]; exact AddCircle.coe_equivIco
    have hxγ : x = γ s := by
      rw [← hξ, ← hsc, Work.Final.rayLift_coe (cov := cov) hmet p u P hPper s]
    have hyγ : y = γ t := by
      rw [← hη, ← htc, Work.Final.rayLift_coe (cov := cov) hmet p u P hPper t]
    rw [hxγ, hyγ]
    rcases le_total s t with hst | hts
    · have h1 : rdist (I := I) (M := M) (γ s) (γ t) ≤ t - s := by
        have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le (cov := cov) hmet p hu
          (a := s) (b := t) hs0 hst
        rw [rdist]
        calc (Manifold.riemannianEDist I (γ s) (γ t)).toReal
            ≤ (ENNReal.ofReal (t - s)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top (by simpa only [hγdef] using h)
          _ = t - s := ENNReal.toReal_ofReal (by linarith)
      have h2 : rdist (I := I) (M := M) (γ s) (γ t) ≤ P - (t - s) := by
        have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le (cov := cov) hmet p hu
          (a := t) (b := s + P) (le_trans hs0 hst) (by linarith)
        have hγs : Submission.GlobalExp.GExp (cov := cov) hmet p ((s + P) • u) = γ s := by
          simpa only [hγdef] using hPper s
        rw [hγs] at h
        rw [fbcap_rdist_comm (I := I) (M := M) (γ s) (γ t), rdist]
        calc (Manifold.riemannianEDist I (γ t) (γ s)).toReal
            ≤ (ENNReal.ofReal (s + P - t)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top h
          _ = P - (t - s) := by
              rw [ENNReal.toReal_ofReal (by linarith)]
              ring
      by_cases hc : t - s ≤ P / 2
      · linarith
      · push_neg at hc; linarith
    · have h1 : rdist (I := I) (M := M) (γ s) (γ t) ≤ s - t := by
        have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le (cov := cov) hmet p hu
          (a := t) (b := s) ht0 hts
        rw [fbcap_rdist_comm (I := I) (M := M) (γ s) (γ t), rdist]
        calc (Manifold.riemannianEDist I (γ t) (γ s)).toReal
            ≤ (ENNReal.ofReal (s - t)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top (by simpa only [hγdef] using h)
          _ = s - t := ENNReal.toReal_ofReal (by linarith)
      have h2 : rdist (I := I) (M := M) (γ s) (γ t) ≤ P - (s - t) := by
        have h := Submission.HopfRinow.riemannianEDist_GExp_ray_le (cov := cov) hmet p hu
          (a := s) (b := t + P) (le_trans ht0 hts) (by linarith)
        have hγt : Submission.GlobalExp.GExp (cov := cov) hmet p ((t + P) • u) = γ t := by
          simpa only [hγdef] using hPper t
        rw [hγt] at h
        rw [rdist]
        calc (Manifold.riemannianEDist I (γ s) (γ t)).toReal
            ≤ (ENNReal.ofReal (t + P - s)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top h
          _ = P - (s - t) := by
              rw [ENNReal.toReal_ofReal (by linarith)]
              ring
      by_cases hc : s - t ≤ P / 2
      · linarith
      · push_neg at hc; linarith
  linarith

end Pieces

open Bundle in
/-- ROUTE.  Write `q := qpt hmet p e (Fin.succ k)`; `rdist p q = π/2` (the ray from `p` in direction
`e k` of length `π/2` reaches `q`) and `rdist p y ≤ π` for all `y` (`hdiam`).  The claim is the
**cap depth**: a point at distance `≥ π - arccos (1-c)` from `q` is at distance
`≤ π + arcsin (2ε₁)` from `q`.  The constant is immaterial (anything of the shape `π + O(ε₁)`).

This is the statement of `Work.Diff.C.far_ball_excess` (module `Diff/C/far_ball_excess`), whose
attempt is stalled with ~34 compile errors; the name and statement are preserved there (a wrapper
calling this result will replace the broken body) because five other modules call it (`dip_far_ball`,
`dip_far_sharp`, `dip_cap_exit`, `dip_model_through`, `dip_model_sharp`).

Proof.  Let `γ` be a minimising geodesic from `q` to `z`, of length `L`.  The function
`F := rdist q + rdist z` satisfies `F ≥ L` everywhere by the triangle inequality and `F = L` at
every point of `γ`, so `Hess F` is positive semidefinite at the interior points of `γ` (second-order
necessary condition for a minimum of the smooth function `F` along `γ`).  On the set where both
centres are at distance `< π - δ` (`δ := arccos (1-c)`), the shape-operator input
`Work.Diff.C.rhess_rdist_bound_of_hHess` (already proved, in `Diff/C/far_sphere_size`, from `hHess`
for `fcos` via the second-order chain rule `Diff/C/rhess_comp` plus the eikonal `hgrad`) applied to
the centres `q` and `z` gives, for `V ⊥ γ'` with `‖V‖ = 1` and `t = rdist q (γ t)`,
`Hess F (V,V) ≥ (cot t + cot (L-t)) - ε₁ (1/sin t + 1/sin (L-t)) ≥ 0`, hence
`sin L ≥ -ε₁ (sin t + sin (L-t)) ≥ -2 ε₁` (multiply by `sin t sin (L-t) > 0` and use the addition
formula).  Since `L ∈ [π-δ, 3π/2]` (the triangle inequality `L ≤ rdist q p + rdist p z ≤ 3π/2`),
`sin L ≥ -2ε₁` forces `L ≤ π + arcsin (2ε₁)` unless already `L ≤ π`. -/
theorem fb_cap_depth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {α c ε₁ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hc : 0 < c) (hc1 : c ≤ 1 / 4)
    (hε₁ : 0 ≤ ε₁) (hnum1 : 3 * c ≤ 1 - Real.cos α) (hnum2 : 4 * ε₁ * Real.pi < c)
    {p : M} {e : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (hON : ∀ i j, Inner.inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (hsmC : ∀ (q y : M), -1 + c ≤ Work.Diff.C.fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) (Work.Diff.C.fcos (I := I) (M := M) q) y)
    (hHess : ∀ q : M, Work.Diff.C.HessBoundRegion (I := I) (M := M) cov c ε₁ (Work.Diff.C.fcos (I := I) (M := M) q))
    (hcont : ∀ q : M, Continuous (Work.Diff.C.fcos (I := I) (M := M) q))
    (hgrad : ∀ (q y : M), -1 + c < Work.Diff.C.fcos (I := I) (M := M) q y →
      Inner.inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        (Work.Diff.C.rgrad (I := I) (M := M) (Work.Diff.C.fcos (I := I) (M := M) q) y)
        = 1 - (Work.Diff.C.fcos (I := I) (M := M) q y) ^ 2)
    (hinit : Work.Diff.C.InitData (I := I) (M := M) (cov := cov) hmet p e)
    (hdiam : ∀ y : M, Work.Diff.C.rdist (I := I) (M := M) p y ≤ Real.pi)
    {k : Fin (Module.finrank ℝ E)} :
    ∀ z : M,
      Real.pi - Real.arccos (1 - c)
          ≤ Work.Diff.C.rdist (I := I) (M := M) (Work.Diff.C.qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z →
      Work.Diff.C.rdist (I := I) (M := M) (Work.Diff.C.qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k)) z
        ≤ Real.pi + Real.arcsin (2 * ε₁) := by
  classical
  intro z hz
  set q : M := qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ k) with hq
  -- ## dimension one
  by_cases hdim1 : Module.finrank ℝ E = 1
  · have hle := fbcap_diam_one (I := I) (M := M) (cov := cov) hmet htor hdim1 (p := p) hdiam q z
    have h0 : 0 ≤ Real.arcsin (2 * ε₁) := Real.arcsin_nonneg.mpr (by linarith)
    linarith
  -- ## dimension at least two
  have hdim2 : 2 ≤ Module.finrank ℝ E := by
    rcases Nat.lt_or_ge (Module.finrank ℝ E) 2 with h | h
    · have h1 : 0 < Module.finrank ℝ E := by
        obtain ⟨w, hw⟩ := exists_ne (0 : E)
        exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w, hw⟩
      omega
    · exact h
  have hqp : rdist (I := I) (M := M) q p = Real.pi / 2 :=
    fbcap_rdist_qpt_p (I := I) (M := M) (cov := cov) hmet htor hON hinit
  have hL3 : rdist (I := I) (M := M) q z ≤ 3 * Real.pi / 2 := by
    have htri := fbcap_rdist_triangle (I := I) (M := M) (cov := cov) hmet htor q p z
    have h2 : rdist (I := I) (M := M) p z ≤ Real.pi := hdiam z
    linarith
  by_cases hLπ : rdist (I := I) (M := M) q z ≤ Real.pi
  · have h0 : 0 ≤ Real.arcsin (2 * ε₁) := Real.arcsin_nonneg.mpr (by linarith)
    linarith
  have hLgt : Real.pi < rdist (I := I) (M := M) q z := lt_of_not_ge hLπ
  -- ## the minimising ray from `q` to `z`
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (I := I) (cov := cov) hmet htor q z
  have hvd' : rdist (I := I) (M := M) q z = ‖v‖ := by
    rw [rdist, hvd, ENNReal.toReal_ofReal (norm_nonneg v)]
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hvd'
    linarith [Real.pi_pos, hLgt, hvd']
  set L : ℝ := rdist (I := I) (M := M) q z with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith [Real.pi_pos, hLgt]
  have hLgt' : Real.pi < L := by rw [hLdef]; exact hLgt
  have hL3' : L ≤ 3 * Real.pi / 2 := by rw [hLdef]; exact hL3
  set u : TangentSpace I q := Submission.GlobalExp.unitOf v hvne with hudef
  have hu : ‖u‖ = 1 := Submission.GlobalExp.unitOf_norm v hvne
  have hu_ne : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hvu : ‖v‖ • u = v := by
    rw [hudef, Submission.GlobalExp.unitOf, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hvne), one_smul]
  have hGz : Submission.GlobalExp.GExp (cov := cov) hmet q (L • u) = z := by
    have h1 : L • u = v := by
      rw [hvd']
      exact hvu
    rw [h1]
    exact hvG
  have hray := fbcap_ray_rdist_eq (I := I) (M := M) (cov := cov) hmet htor hu (le_of_lt hLpos) hGz
    hLdef.symm
  -- ## the midpoint
  set t₀ : ℝ := L / 2 with ht₀def
  have ht₀pos : 0 < t₀ := by linarith [ht₀def, hLpos]
  have ht₀ltπ : t₀ < Real.pi := by linarith [ht₀def, hL3', Real.pi_pos]
  have ht₀L : t₀ ≤ L := by linarith [ht₀def, hLpos]
  set x : M := Submission.GlobalExp.GExp (cov := cov) hmet q (t₀ • u) with hxdef
  have hxq : rdist (I := I) (M := M) q x = t₀ := by
    rw [hxdef]
    exact (hray t₀ ⟨le_of_lt ht₀pos, ht₀L⟩).1
  have hxz : rdist (I := I) (M := M) z x = t₀ := by
    rw [hxdef]
    rw [(hray t₀ ⟨le_of_lt ht₀pos, ht₀L⟩).2, ht₀def]
    ring
  -- ## the region condition at the midpoint
  have ht₀_le : t₀ ≤ 3 * Real.pi / 4 := by linarith [ht₀def, hL3']
  have hcos_lb : -1 + c < Real.cos t₀ := by
    have hmono : Real.cos (3 * Real.pi / 4) ≤ Real.cos t₀ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (y := 3 * Real.pi / 4) (le_of_lt ht₀pos)
        (by linarith [Real.pi_pos]) ht₀_le
    have hval : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
      rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 from by ring, Real.cos_pi_sub,
        Real.cos_pi_div_four]
      ring
    rw [hval] at hmono
    have hs : Real.sqrt 2 / 2 < 3 / 4 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have hc4 : -1 + c ≤ -3 / 4 := by linarith
    linarith
  have hreg_q : -1 + c < fcos (I := I) (M := M) q x := by
    rw [fcos, hxq]
    exact hcos_lb
  have hreg_z : -1 + c < fcos (I := I) (M := M) z x := by
    rw [fcos, hxz]
    exact hcos_lb
  -- ## smoothness of the two distance functions, with unit gradients
  obtain ⟨hsm_q, heik_q⟩ := fbcap_rdist_smooth (I := I) (M := M) (cov := cov) hmet hc
    (q := q) (x := x) (by rw [hxq]; exact ht₀pos) (by rw [hxq]; exact ht₀ltπ) hreg_q
    (fun y hy => hsmC q y hy) (fun y hy => hgrad q y hy)
  obtain ⟨hsm_z, heik_z⟩ := fbcap_rdist_smooth (I := I) (M := M) (cov := cov) hmet hc
    (q := z) (x := x) (by rw [hxz]; exact ht₀pos) (by rw [hxz]; exact ht₀ltπ) hreg_z
    (fun y hy => hsmC z y hy) (fun y hy => hgrad z y hy)
  -- ## the ray as a curve, and the gradients along it
  set γ : ℝ → M := fun τ : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet q (τ • u) with hγdef
  have hxγ : x = γ t₀ := by rw [hxdef, hγdef]
  have hγmd : MDifferentiableAt 𝓘(ℝ) I γ t₀ := by
    have hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Set.Ioi 0) := by
      rw [hγdef]
      exact Submission.LensLoop.contMDiffOn_GExp_smul_Ioi (cov := cov) hmet q hu_ne
    exact (hsm.contMDiffAt (isOpen_Ioi.mem_nhds ht₀pos)).mdifferentiableAt (by simp)
  have hspeed : ‖Submission.Geodesic.curveVelocity (I := I) γ t₀‖ = 1 := by
    have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet q hu_ne
      (ne_of_gt ht₀pos)
    simpa only [hγdef, hu] using h
  have hspeed_inner : Inner.inner ℝ (Submission.Geodesic.curveVelocity (I := I) γ t₀)
      (Submission.Geodesic.curveVelocity (I := I) γ t₀) = 1 := by
    rw [real_inner_self_eq_norm_sq, hspeed]
    norm_num
  have ht₀mem : t₀ ∈ Set.Ioo (0 : ℝ) L := ⟨ht₀pos, by rw [ht₀def]; linarith [hLpos]⟩
  have hder_q : HasDerivAt (fun τ : ℝ => rdist (I := I) (M := M) q (γ τ)) 1 t₀ := by
    refine (hasDerivAt_id t₀).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht₀mem] with τ hτ
    simpa only [hγdef, id_eq] using (hray τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩).1
  have hder_z : HasDerivAt (fun τ : ℝ => rdist (I := I) (M := M) z (γ τ)) (-1) t₀ := by
    have h0 : HasDerivAt (fun τ : ℝ => L - τ) (-1) t₀ := by
      have h1 : HasDerivAt (fun τ : ℝ => L - τ) (0 - 1) t₀ :=
        (hasDerivAt_const t₀ L).sub (hasDerivAt_id t₀)
      rw [show (0 : ℝ) - 1 = -1 by norm_num] at h1
      exact h1
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds ht₀mem] with τ hτ
    simpa only [hγdef] using (hray τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩).2
  have hinq : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun y : M => rdist (I := I) (M := M) q y) x)
      (Submission.Geodesic.curveVelocity (I := I) γ t₀) = 1 := by
    rw [hxγ, inner_rgrad_mvfderiv_local]
    have hcr := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun y : M => rdist (I := I) (M := M) q y) (γ := γ) (t := t₀)
      (hsm_q.mdifferentiableAt (by simp)) hγmd
    have hd : deriv ((fun y : M => rdist (I := I) (M := M) q y) ∘ γ) t₀ = 1 := by
      simpa only [Function.comp_def] using hder_q.deriv
    rw [hd] at hcr
    simpa only [Submission.Geodesic.curveVelocity_apply] using hcr
  have hinz : Inner.inner ℝ
      (rgrad (I := I) (M := M) (fun y : M => rdist (I := I) (M := M) z y) x)
      (Submission.Geodesic.curveVelocity (I := I) γ t₀) = -1 := by
    rw [hxγ, inner_rgrad_mvfderiv_local]
    have hcr := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I)
      (g := fun y : M => rdist (I := I) (M := M) z y) (γ := γ) (t := t₀)
      (hsm_z.mdifferentiableAt (by simp)) hγmd
    have hd : deriv ((fun y : M => rdist (I := I) (M := M) z y) ∘ γ) t₀ = -1 := by
      simpa only [Function.comp_def] using hder_z.deriv
    rw [hd] at hcr
    simpa only [Submission.Geodesic.curveVelocity_apply] using hcr
  have hdir_q : rgrad (I := I) (M := M) (fun y : M => rdist (I := I) (M := M) q y) x
      = Submission.Geodesic.curveVelocity (I := I) γ t₀ :=
    fbcap_eq_of_inner_eq_one heik_q hspeed_inner hinq
  have hdir_z : rgrad (I := I) (M := M) (fun y : M => rdist (I := I) (M := M) z y) x
      = - Submission.Geodesic.curveVelocity (I := I) γ t₀ :=
    fbcap_eq_of_inner_eq_one heik_z
      (by rw [inner_neg_left, inner_neg_right, hspeed_inner]; norm_num)
      (by rw [inner_neg_right, hinz]; norm_num)
  -- ## a non-zero vector orthogonal to the direction of the ray
  have hgrad_ne : rgrad (I := I) (M := M) (fun y : M => rdist (I := I) (M := M) q y) x ≠ 0 := by
    intro h0
    rw [h0] at heik_q
    simp at heik_q
  obtain ⟨V, hVne, hVorth⟩ := fbcap_exists_orthogonal_ne_zero (V := TangentSpace I x)
    (by rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl]; exact hdim2)
    hgrad_ne
  have hVvel : Inner.inner ℝ (Submission.Geodesic.curveVelocity (I := I) γ t₀) V = 0 := by
    rw [← hdir_q]
    exact hVorth
  have hVfq : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x) V = 0 := by
    rw [rgrad_fcos (I := I) (M := M) (q := q) hsm_q, real_inner_smul_left, hVorth, mul_zero]
  have hVfz : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) z) x) V = 0 := by
    rw [rgrad_fcos (I := I) (M := M) (q := z) hsm_z, real_inner_smul_left, hdir_z, inner_neg_left,
      hVvel, neg_zero, mul_zero]
  -- ## the two Hessian bounds
  have hbq := rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov) (hHess := hHess q)
    (hx := hreg_q) (hsm := hsm_q) (hpos := by rw [hxq]; exact ht₀pos)
    (hdπ := by rw [hxq]; exact ht₀ltπ) V (hV := hVfq)
  have hbz := rhess_rdist_bound_of_hHess (I := I) (M := M) (cov := cov) (hHess := hHess z)
    (hx := hreg_z) (hsm := hsm_z) (hpos := by rw [hxz]; exact ht₀pos)
    (hdπ := by rw [hxz]; exact ht₀ltπ) V (hV := hVfz)
  have hbq' : |rhess cov (fun y : M => rdist (I := I) (M := M) q y) x V V
      - Real.cot t₀ * Inner.inner ℝ V V| ≤ (ε₁ / Real.sin t₀) * Inner.inner ℝ V V := by
    simpa [hxq] using hbq
  have hbz' : |rhess cov (fun y : M => rdist (I := I) (M := M) z y) x V V
      - Real.cot t₀ * Inner.inner ℝ V V| ≤ (ε₁ / Real.sin t₀) * Inner.inner ℝ V V := by
    simpa [hxz] using hbz
  -- ## positive semidefiniteness of the Hessian of `rdist q + rdist z` at the midpoint
  have hFsm : CMDiffAt ∞ (fun y : M => rdist (I := I) (M := M) q y + rdist (I := I) (M := M) z y) x :=
    hsm_q.add hsm_z
  have hFmin : ∀ y : M, (fun y : M => rdist (I := I) (M := M) q y + rdist (I := I) (M := M) z y) x
      ≤ (fun y : M => rdist (I := I) (M := M) q y + rdist (I := I) (M := M) z y) y := by
    intro y
    have htri := fbcap_rdist_triangle (I := I) (M := M) (cov := cov) hmet htor q y z
    have hsym : rdist (I := I) (M := M) y z = rdist (I := I) (M := M) z y :=
      fbcap_rdist_comm (I := I) (M := M) y z
    have hxL : rdist (I := I) (M := M) q x + rdist (I := I) (M := M) z x = L := by
      rw [hxq, hxz, ht₀def]
      ring
    show rdist (I := I) (M := M) q x + rdist (I := I) (M := M) z x
        ≤ rdist (I := I) (M := M) q y + rdist (I := I) (M := M) z y
    rw [hxL, ← hsym]
    linarith [htri, hLdef]
  have hpsd : 0 ≤ rhess (I := I) (M := M) cov
      (fun y : M => rdist (I := I) (M := M) q y + rdist (I := I) (M := M) z y) x V V :=
    fbcap_hess_nonneg (I := I) (M := M) (cov := cov) hmet htor hFsm hFmin V
  have hexp := fbcap_rhess_add (I := I) (M := M) (cov := cov)
    (F := fun y : M => rdist (I := I) (M := M) q y)
    (G := fun y : M => rdist (I := I) (M := M) z y) hsm_q hsm_z V V
  have hpsd' : 0 ≤ rhess (I := I) (M := M) cov (fun y : M => rdist (I := I) (M := M) q y) x V V
      + rhess (I := I) (M := M) cov (fun y : M => rdist (I := I) (M := M) z y) x V V := by
    rw [← hexp]
    exact hpsd
  -- ## the final inequality `cos t₀ ≥ -ε₁`
  have hgpos : 0 < Inner.inner ℝ V V := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hVne) 2
  have hs_pos : 0 < Real.sin t₀ := Real.sin_pos_of_pos_of_lt_pi ht₀pos ht₀ltπ
  have hmain : 0 ≤ Real.cot t₀ * Inner.inner ℝ V V
      + (ε₁ / Real.sin t₀) * Inner.inner ℝ V V := by
    have h1 := (abs_le.mp hbq').2
    have h2 := (abs_le.mp hbz').2
    linarith
  have hcot : Real.sin t₀ * Real.cot t₀ = Real.cos t₀ := by
    rw [Real.cot_eq_cos_div_sin]
    field_simp
  have hcos : -ε₁ ≤ Real.cos t₀ := by
    have h1 : 0 ≤ Real.sin t₀ * (Real.cot t₀ * Inner.inner ℝ V V
        + (ε₁ / Real.sin t₀) * Inner.inner ℝ V V) := mul_nonneg (le_of_lt hs_pos) hmain
    have h3 : Real.sin t₀ * (ε₁ / Real.sin t₀) = ε₁ := by field_simp
    rw [mul_add, ← mul_assoc, ← mul_assoc, hcot, h3] at h1
    have h2 : 0 ≤ (Real.cos t₀ + ε₁) * Inner.inner ℝ V V := by
      rw [add_mul]
      linarith
    have h4 : 0 ≤ Real.cos t₀ + ε₁ := (mul_nonneg_iff_of_pos_right hgpos).mp h2
    linarith
  -- ## the arithmetic
  have h2ε : 2 * ε₁ ≤ 1 := by
    have h4 : 4 * ε₁ * Real.pi < 1 := by linarith [hnum2, hc1]
    have hπ2 : (1 : ℝ) / 2 ≤ Real.pi := by linarith [Real.pi_gt_three]
    nlinarith [hε₁, hπ2, h4]
  have hcosL : -ε₁ ≤ Real.cos (L / 2) := by rw [← ht₀def]; exact hcos
  exact fbcap_arith hε₁ h2ε hLgt' hL3' hcosL


end Work.Diff.C
