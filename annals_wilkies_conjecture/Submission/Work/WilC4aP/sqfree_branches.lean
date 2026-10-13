/-
  Work.WilC4aP — the complex Puiseux theorem, square-free case.

  Route (complex monodromy): the root space of `P` is a covering of the punctured disk; the
  sections over the (simply connected) half plane are the single-valued branches `ζ j` of the
  roots of `Pz P (exp ·)`; the shift `w ↦ w + 2πi` permutes them by a permutation `τ` of
  `Fin m` with `τ ^ m.factorial = 1`, so the branches are invariant under `w ↦ w + m.factorial ·
  2πi`; pushing forward along `u ↦ exp (m.factorial * log u)` and applying the removable
  singularity theorem gives the holomorphic branches of the ramified polynomial.
-/
import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.SqAux
import Submission.Work.WilC4aP.SqDefs
import Submission.Work.WilC4aP.exists_local_factorization
import Submission.Work.WilC4aP.poly_root_bound
import Submission.Work.WilC4aP.prod_eq_of_distinct_roots
import Submission.Work.WilC4aP.exists_root_enum
import Submission.Work.WilC4aP.exists_ball_injective
import Submission.Work.WilC4aP.analytic_bivariate_Pz_eval
import Submission.Work.WilC4aP.eq_of_eq_at_of_lifts
import Submission.Work.WilC4aP.isLocalHomeomorphOn_rootProj
import Submission.Work.WilC4aP.exists_rootBound

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators Topology

namespace Work.WilC4aP

open Polynomial

/-! ## The main theorem -/

/-- **Complex Puiseux theorem, square-free case.** If a monic polynomial `P` with
holomorphic coefficients has only simple roots over the punctured disk of radius `ρ₀`, then
after the ramification `s = u ^ m.factorial` its roots are single-valued holomorphic
functions of `u` on some disk.

PROOF HINT: the total space `{(z,Y) // 0 < ‖z‖ < ρ₀ ∧ (Pz P z).eval Y = 0}` is a covering of
the punctured disk (`IsCoveringMap`, local triviality from `exists_local_factorization`), of
degree `m`. Lift the map `w ↦ exp w` (a covering on `{0}ᶜ`, `Complex.isCoveringMapOn_exp`)
through it (`IsCoveringMapOn.existsUnique_continuousMap_lifts`, the half plane is simply
connected); this gives `m` holomorphic `ζ j` on `{w | ‖exp w‖ < ρ₀}` (holomorphy: locally they
are the branches of `exists_local_factorization`). Shifting `w` by `2πi` permutes them: there
is `τ : Equiv.Perm (Fin m)` with `ζ j (w + 2πi) = ζ (τ j) w`, and `τ ^ m.factorial = 1`
(`perm_pow_factorial`). Then `η j u := ζ j (m.factorial * log u)` is well defined and
holomorphic on a punctured disk (glue the local branches of the logarithm, using
`ζ j (w + 2πi * m.factorial) = ζ j w`), bounded (the roots of a monic polynomial are bounded
by its coefficients, uniformly near `0`), so it extends to `u = 0` by
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`; the factorization
holds on the punctured disk (both sides are monic of degree `m` with the same `m` distinct
roots) and extends to `u = 0` by continuity. -/
theorem sqfree_branches {m : ℕ} (P : Polynomial (ℂ → ℂ)) (hmon : P.Monic)
    (hdeg : P.natDegree = m) (han : Work.WilC4aP.HolCoeffs P 0) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hsep : Work.WilC4aP.SimpleRootsOn P {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < ρ₀}) :
    ∃ (η : Fin m → ℂ → ℂ) (ρ : ℝ), 0 < ρ ∧
      (∀ j, AnalyticOnNhd ℂ (η j) (Metric.ball 0 ρ)) ∧
      Work.WilC4aP.FactoredOn P m.factorial η ρ := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `m = 0`: the polynomial is `1` and the empty product is `1`
    subst hm0
    have hP1 : P = 1 := by
      have h0 : P.coeff 0 = 1 := by
        have h := hmon.coeff_natDegree
        rw [hdeg] at h
        simpa using h
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, h0, Polynomial.C_1]
    refine ⟨fun j => j.elim0, 1, one_pos, fun j => j.elim0, ?_⟩
    intro u _
    simp [FactoredOn, hP1, Pz]
  -- radii
  obtain ⟨r₁, hr₁pos, hr₁an⟩ := exists_ball_holCoeffs P han
  set r : ℝ := min ρ₀ r₁ / 2 with hrdef
  have hminpos : 0 < min ρ₀ r₁ := lt_min hρ₀ hr₁pos
  have hrpos : 0 < r := by rw [hrdef]; positivity
  have hrρ : r < ρ₀ := by rw [hrdef]; nlinarith [min_le_left ρ₀ r₁]
  have hrr₁ : r < r₁ := by rw [hrdef]; nlinarith [min_le_right ρ₀ r₁]
  have hana : ∀ z : ℂ, ‖z‖ < r → HolCoeffs P z := fun z hz => hr₁an z (lt_trans hz hrr₁)
  have hcontR : ∀ z : ℂ, ‖z‖ ≤ r → HolCoeffs P z := fun z hz => hr₁an z (lt_of_le_of_lt hz hrr₁)
  have hcontc : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) r → HolCoeffs P z := fun z hz =>
    hcontR z (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)
  have hsepS : SimpleRootsOn P (puncDisk r) := fun z hz =>
    hsep z ⟨hz.1, lt_trans hz.2 hrρ⟩
  -- uniform root bound
  obtain ⟨R, hRpos, hRroot⟩ := exists_rootBound P hmon hcontR
  -- the root space is compact, hence the projection is a covering of the punctured disk
  haveI hCpct : CompactSpace ↥(RootSpace P r R) :=
    isCompact_iff_compactSpace.mp (isCompact_rootSpace_aux P hcontc)
  have cov : IsCoveringMapOn (rootProj P r R) (puncDisk r) :=
    IsCoveringMapOn.of_isLocalHomeomorphOn (continuous_rootProj P r R)
      (isLocalHomeomorphOn_rootProj P hmon hdeg hrpos hRpos hRroot hcontc hsepS)
  -- the half plane
  set Ω : Set ℂ := leftHalfPlane (Real.log r) with hΩ
  have hΩmem : ∀ w : ℂ, w ∈ Ω ↔ w.re < Real.log r := fun w => Iff.rfl
  have hΩopen : IsOpen Ω := isOpen_lt Complex.continuous_re continuous_const
  have hΩconv : Convex ℝ Ω := by
    have h : Ω = Complex.reCLM ⁻¹' Set.Iio (Real.log r) := by
      ext w; simp [hΩ, leftHalfPlane, Complex.reCLM_apply]
    rw [h]
    exact (convex_Iio (Real.log r)).linear_preimage Complex.reCLM.toLinearMap
  have hΩne : Ω.Nonempty := ⟨(((Real.log r - 1 : ℝ)) : ℂ), by simp [hΩ, leftHalfPlane]⟩
  haveI hCont : ContractibleSpace ↥Ω := hΩconv.contractibleSpace hΩne
  haveI hSC : SimplyConnectedSpace ↥Ω := inferInstance
  haveI hLPC : LocallyPathConnectedSpace ↥Ω := hΩopen.locallyPathConnectedSpace
  haveI hPC : PreconnectedSpace ↥Ω := inferInstance
  -- the exponential map on the half plane
  let expΩ : C(↥Ω, ℂ) := ⟨fun w => Complex.exp w.1,
    Complex.continuous_exp.comp continuous_subtype_val⟩
  have hexpΩmem : ∀ w : ↥Ω, Complex.exp w.1 ∈ puncDisk r := by
    intro w
    refine ⟨norm_pos_iff.mpr (Complex.exp_ne_zero _), ?_⟩
    rw [Complex.norm_exp]
    exact (Real.lt_log_iff_exp_lt hrpos).mp w.2
  -- base point and the enumeration of the roots of the fibre there
  obtain ⟨w₀, hw₀⟩ := hΩne
  let w₀Ω : ↥Ω := ⟨w₀, hw₀⟩
  have hz₀ : Complex.exp w₀ ∈ puncDisk r := hexpΩmem w₀Ω
  have hsepz₀ : ∀ v : ℂ, (Pz P (Complex.exp w₀)).eval v = 0 →
      (Pz P (Complex.exp w₀)).derivative.eval v ≠ 0 := hsepS _ hz₀
  obtain ⟨r₀, hr₀inj, hr₀root⟩ := exists_root_enum (monic_Pz hmon (Complex.exp w₀))
    (by rw [natDegree_Pz hmon (Complex.exp w₀), hdeg]) hsepz₀
  have hpoly₀ : Pz P (Complex.exp w₀) = ∏ k, (Polynomial.X - Polynomial.C (r₀ k)) :=
    prod_eq_of_distinct_roots (monic_Pz hmon _)
      (by rw [natDegree_Pz hmon (Complex.exp w₀), hdeg]) hr₀inj hr₀root
  have hrootmem : ∀ α : ℂ, (Pz P (Complex.exp w₀)).eval α = 0 → ∃ k : Fin m, α = r₀ k := by
    intro α hα
    have h : (∏ k, (α - r₀ k)) = 0 := by
      have h2 := hα
      rw [hpoly₀] at h2
      simpa [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] using h2
    obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp h
    exact ⟨k, sub_eq_zero.mp hk⟩
  -- the `m` starting points of the lifts
  have he₀mem : ∀ k : Fin m, (Complex.exp w₀, r₀ k) ∈ RootSpace P r R := by
    intro k
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_lt hz₀.2
    · simpa [Metric.mem_closedBall, dist_eq_norm] using
        hRroot _ (le_of_lt hz₀.2) _ (hr₀root k)
    · exact hr₀root k
  let e₀ : Fin m → ↥(RootSpace P r R) := fun k => ⟨(Complex.exp w₀, r₀ k), he₀mem k⟩
  have he₀_fst : ∀ k : Fin m, (e₀ k).1.1 = Complex.exp w₀ := fun k => rfl
  have he₀_snd : ∀ k : Fin m, (e₀ k).1.2 = r₀ k := fun k => rfl
  -- the lifts of `exp`
  have hlift : ∀ j : Fin m, ∃! F : C(↥Ω, ↥(RootSpace P r R)),
      F w₀Ω = e₀ j ∧ (rootProj P r R) ∘ F = fun w : ↥Ω => Complex.exp w.1 :=
    fun j => IsCoveringMapOn.existsUnique_continuousMap_lifts (cov := cov) (f := expΩ)
      (a₀ := w₀Ω) (e₀ := e₀ j) rfl hexpΩmem
  let Fj : Fin m → C(↥Ω, ↥(RootSpace P r R)) := fun j => (hlift j).choose
  have hFj_pt : ∀ j : Fin m, Fj j w₀Ω = e₀ j := fun j => (hlift j).choose_spec.1.1
  have hFj_lift : ∀ j : Fin m,
      (rootProj P r R) ∘ (Fj j) = fun w : ↥Ω => Complex.exp w.1 :=
    fun j => (hlift j).choose_spec.1.2
  have hFj_base : ∀ (j : Fin m) (w : ↥Ω), (Fj j w).1.1 = Complex.exp w.1 := by
    intro j w
    have h := congr_fun (hFj_lift j) w
    simpa using h
  -- the branches, as functions on the half plane
  let Zsub : Fin m → ↥Ω → ℂ := fun j x => (Fj j x).1.2
  let Z : Fin m → ℂ → ℂ := fun j z => if h : z ∈ Ω then (Fj j ⟨z, h⟩).1.2 else 0
  have hZsub_cont : ∀ j : Fin m, Continuous (Zsub j) :=
    fun j => (continuous_subtype_val.snd).comp (Fj j).continuous
  have hZΩcont : ∀ j : Fin m, ContinuousOn (Z j) Ω := by
    intro j
    rw [continuousOn_iff_continuous_domRestrict]
    refine (hZsub_cont j).congr fun x => ?_
    simp [Z, Zsub, Set.domRestrict_apply]
  have hZ_eq : ∀ (j : Fin m) (z : ℂ) (h : z ∈ Ω), Z j z = (Fj j ⟨z, h⟩).1.2 :=
    fun j z h => dif_pos h
  have hZroot : ∀ (j : Fin m) (x : ↥Ω),
      (Pz P (Complex.exp x.1)).eval (Zsub j x) = 0 := by
    intro j x
    have h1 := rootEval_zero P (Fj j x)
    rwa [hFj_base j x] at h1
  -- distinctness of the branches at every point of the half plane
  have hZinj : ∀ x : ↥Ω, Function.Injective fun j => Zsub j x := by
    intro x i j hij
    have h1 : Fj i x = Fj j x := by
      refine Subtype.ext (Prod.ext ?_ hij)
      rw [hFj_base i x, hFj_base j x]
    have h2 : Fj i = Fj j := ContinuousMap.ext fun x =>
      congr_fun (eq_of_eq_at_of_lifts cov hexpΩmem (Fj i).continuous
        (Fj j).continuous (hFj_lift i) (hFj_lift j) h1) x
    have h3 : e₀ i = e₀ j := by rw [← hFj_pt i, ← hFj_pt j, h2]
    have h4 : r₀ i = r₀ j := by
      have h := congrArg (fun q : ↥(RootSpace P r R) => q.1.2) h3
      rwa [he₀_snd i, he₀_snd j] at h
    exact hr₀inj h4
  -- the factorization on the half plane
  have hZfac : ∀ x : ↥Ω,
      Pz P (Complex.exp x.1) = ∏ j, (Polynomial.X - Polynomial.C (Zsub j x)) :=
    fun x => prod_eq_of_distinct_roots (monic_Pz hmon _)
      (by rw [natDegree_Pz hmon (Complex.exp x.1), hdeg]) (hZinj x) (fun j => hZroot j x)
  -- the branches are holomorphic
  have hZan : ∀ j : Fin m, AnalyticOnNhd ℂ (Z j) Ω := by
    intro j z hz
    -- local factorization at `exp z`
    have hzD : Complex.exp z ∈ puncDisk r := by
      refine ⟨norm_pos_iff.mpr (Complex.exp_ne_zero _), ?_⟩
      rw [Complex.norm_exp]
      exact (Real.lt_log_iff_exp_lt hrpos).mp hz
    obtain ⟨ρ₁, η, hρ₁, hηan, hηinj, hηfac⟩ :=
      exists_local_factor_distinct P hmon hdeg (z₀ := Complex.exp z)
        (hcontR _ (le_of_lt hzD.2)) (hsepS _ hzD)
    -- `Z j z` is one of the branches at `exp z`
    have hrootz : (Pz P (Complex.exp z)).eval (Z j z) = 0 := by
      rw [hZ_eq j z hz]
      exact hZroot j ⟨z, hz⟩
    obtain ⟨k, hk⟩ : ∃ k : Fin m, η k (Complex.exp z) = Z j z := by
      have h3 : Pz P (Complex.exp z)
          = ∏ i, (Polynomial.X - Polynomial.C (η i (Complex.exp z))) :=
        hηfac _ (Metric.mem_ball_self hρ₁)
      have h2 : (∏ i, (Z j z - η i (Complex.exp z))) = 0 := by
        have h4 := hrootz
        rw [h3] at h4
        simpa [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C] using h4
      obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp h2
      exact ⟨i, (sub_eq_zero.mp hi).symm⟩
    -- a small ball around `z` inside `Ω` and inside the domain of the factorization
    have hev : ∀ᶠ x in 𝓝 z, x ∈ Ω ∧ Complex.exp x ∈ Metric.ball (Complex.exp z) ρ₁ :=
      Filter.inter_mem (hΩopen.mem_nhds hz)
        (Complex.continuous_exp.continuousAt.preimage_mem_nhds
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ₁)))
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp hev
    -- on this ball `Z j` agrees with `η k ∘ exp`
    have hconst : ∀ x : ℂ, ‖x - z‖ < ε → Z j x = η k (Complex.exp x) := by
      intro x hx
      have hBpre : IsPreconnected (Metric.ball z ε) := (convex_ball z ε).isPreconnected
      haveI : PreconnectedSpace ↥(Metric.ball z ε) :=
        isPreconnected_iff_preconnectedSpace.mp hBpre
      have hZB : ContinuousOn (Z j) (Metric.ball z ε) :=
        (hZΩcont j).mono fun y hy => (hεsub (Metric.mem_ball.mp hy)).1
      have hcont1 : Continuous fun y : ↥(Metric.ball z ε) => Z j y.1 :=
        continuousOn_iff_continuous_domRestrict.mp hZB
      have hcont2 : Continuous fun y : ↥(Metric.ball z ε) => η k (Complex.exp y.1) := by
        refine continuous_iff_continuousAt.mpr fun y => ?_
        have hmem : Complex.exp y.1 ∈ Metric.ball (Complex.exp z) ρ₁ :=
          (hεsub (Metric.mem_ball.mp y.2)).2
        exact ContinuousAt.comp (g := fun w : ℂ => η k (Complex.exp w))
          (f := fun y : ↥(Metric.ball z ε) => (y : ℂ)) (x := y)
          (((hηan k) (Complex.exp y.1) hmem).comp analyticAt_cexp).continuousAt
          continuous_subtype_val.continuousAt
      have hTcl : IsClosed {y : ↥(Metric.ball z ε) | Z j y.1 = η k (Complex.exp y.1)} :=
        isClosed_eq hcont1 hcont2
      have hcover : ∀ y : ↥(Metric.ball z ε),
          ∃ i : Fin m, Z j y.1 = η i (Complex.exp y.1) := by
        intro y
        have h3 : Pz P (Complex.exp y.1)
            = ∏ i, (Polynomial.X - Polynomial.C (η i (Complex.exp y.1))) :=
          hηfac _ (hεsub (Metric.mem_ball.mp y.2)).2
        have hroot : (Pz P (Complex.exp y.1)).eval (Z j y.1) = 0 := by
          rw [hZ_eq j y.1 (hεsub (Metric.mem_ball.mp y.2)).1]
          exact hZroot j ⟨y.1, (hεsub (Metric.mem_ball.mp y.2)).1⟩
        rw [h3] at hroot
        have h4 : (∏ i, (Z j y.1 - η i (Complex.exp y.1))) = 0 := by
          simpa [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
            Polynomial.eval_C] using hroot
        obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp h4
        exact ⟨i, sub_eq_zero.mp hi⟩
      have hTopen : IsOpen {y : ↥(Metric.ball z ε) | Z j y.1 = η k (Complex.exp y.1)} := by
        have hcompl : ({y : ↥(Metric.ball z ε) | Z j y.1 = η k (Complex.exp y.1)})ᶜ
            = ⋃ i : {i : Fin m // i ≠ k},
              {y : ↥(Metric.ball z ε) | Z j y.1 = η i.1 (Complex.exp y.1)} := by
          ext y
          simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq]
          constructor
          · intro hy
            obtain ⟨i, hi⟩ := hcover y
            have hik : i ≠ k := by
              rintro rfl
              exact hy hi
            exact ⟨⟨i, hik⟩, hi⟩
          · rintro ⟨i, hyi⟩ hyk
            rw [hyk] at hyi
            exact i.2 ((hηinj _ (hεsub (Metric.mem_ball.mp y.2)).2) hyi).symm
        rw [← isClosed_compl_iff, hcompl]
        refine isClosed_iUnion_of_finite fun i => isClosed_eq hcont1 ?_
        refine continuous_iff_continuousAt.mpr fun y => ?_
        have hmem : Complex.exp y.1 ∈ Metric.ball (Complex.exp z) ρ₁ :=
          (hεsub (Metric.mem_ball.mp y.2)).2
        exact ContinuousAt.comp (g := fun w : ℂ => η i.1 (Complex.exp w))
          (f := fun y : ↥(Metric.ball z ε) => (y : ℂ)) (x := y)
          (((hηan i.1) (Complex.exp y.1) hmem).comp analyticAt_cexp).continuousAt
          continuous_subtype_val.continuousAt
      have hTne : ({y : ↥(Metric.ball z ε) | Z j y.1 = η k (Complex.exp y.1)}).Nonempty :=
        ⟨⟨z, Metric.mem_ball_self hε⟩, hk.symm⟩
      have huniv : {y : ↥(Metric.ball z ε) | Z j y.1 = η k (Complex.exp y.1)} = Set.univ :=
        IsClopen.eq_univ ⟨hTcl, hTopen⟩ hTne
      have hxT : (⟨x, by rw [Metric.mem_ball, dist_eq_norm]; exact hx⟩ :
          ↥(Metric.ball z ε)) ∈
          {y : ↥(Metric.ball z ε) | Z j y.1 = η k (Complex.exp y.1)} := by
        rw [huniv]; trivial
      exact hxT
    -- conclude analyticity
    have heq : (fun x : ℂ => η k (Complex.exp x)) =ᶠ[𝓝 z] Z j := by
      show ∀ᶠ x in 𝓝 z, η k (Complex.exp x) = Z j x
      filter_upwards [Metric.ball_mem_nhds z hε] with x hx
      exact (hconst x (by simpa [Metric.mem_ball, dist_eq_norm] using hx)).symm
    have han : AnalyticAt ℂ (fun x : ℂ => η k (Complex.exp x)) z :=
      ((hηan k) (Complex.exp z) (Metric.mem_ball_self hρ₁)).comp (analyticAt_cexp (z := z))
    exact han.congr heq
  -- the shift `w ↦ w + 2πi`
  let uu : ℂ := ((2 * Real.pi : ℝ) : ℂ) * Complex.I
  have huure : uu.re = 0 := by simp [uu, Complex.mul_re]
  have huuexp : Complex.exp uu = 1 := by
    change Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1
    rw [Complex.exp_ofReal_mul_I, Real.cos_two_pi, Real.sin_two_pi]
    norm_num
  have hshmem : ∀ w : ℂ, w ∈ Ω → w + uu ∈ Ω := by
    intro w hw
    rw [hΩmem] at hw ⊢
    simpa [Complex.add_re, huure] using hw
  let sh : ↥Ω → ↥Ω := fun w => ⟨w.1 + uu, hshmem w.1 w.2⟩
  have hsh_apply : ∀ w : ↥Ω, (sh w).1 = w.1 + uu := fun w => rfl
  have hshcont : Continuous sh :=
    Continuous.subtype_mk (f := fun w : ↥Ω => w.1 + uu)
      (continuous_subtype_val.add continuous_const) (fun w => hshmem w.1 w.2)
  have hshN : ∀ (n : ℕ) (w : ↥Ω), (sh^[n] w).1 = w.1 + (n : ℂ) * uu := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', hsh_apply, ih]
      push_cast
      ring
  -- the monodromy permutation
  have hex : ∀ j : Fin m, ∃ k : Fin m, (Fj j (sh w₀Ω)).1.2 = r₀ k := by
    intro j
    refine hrootmem _ ?_
    have hb : Complex.exp (sh w₀Ω).1 = Complex.exp w₀ := by
      rw [hsh_apply, Complex.exp_add, huuexp, mul_one]
    rw [← hb]
    exact hZroot j (sh w₀Ω)
  choose τfun hτfun using hex
  have hτrel : ∀ (j : Fin m) (w : ↥Ω), Fj j (sh w) = Fj (τfun j) w := by
    intro j w
    have hG : ((Fj j).comp ⟨sh, hshcont⟩ : C(↥Ω, ↥(RootSpace P r R))) = Fj (τfun j) := by
      refine (hlift (τfun j)).unique ⟨?_, ?_⟩ ⟨hFj_pt (τfun j), hFj_lift (τfun j)⟩
      · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Function.comp_apply]
        refine Subtype.ext (Prod.ext ?_ ?_)
        · rw [hFj_base j (sh w₀Ω), hsh_apply, Complex.exp_add, huuexp, mul_one]
        · rw [hτfun j]
      · funext x
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, Function.comp_apply]
        rw [rootProj_apply, hFj_base j (sh x), hsh_apply, Complex.exp_add, huuexp, mul_one]
    have h2 := congrArg (fun F : C(↥Ω, ↥(RootSpace P r R)) => F w) hG
    simpa using h2
  have hτinj : Function.Injective τfun := by
    intro i j hij
    have h1 : ∀ w : ↥Ω, Fj i (sh w) = Fj j (sh w) := by
      intro w; rw [hτrel i w, hτrel j w, hij]
    have h2 : Fj i (sh w₀Ω) = Fj j (sh w₀Ω) := h1 w₀Ω
    have h3 : Fj i = Fj j := ContinuousMap.ext fun x =>
      congr_fun (eq_of_eq_at_of_lifts cov hexpΩmem (Fj i).continuous
        (Fj j).continuous (hFj_lift i) (hFj_lift j) h2) x
    have h4 : e₀ i = e₀ j := by rw [← hFj_pt i, ← hFj_pt j, h3]
    have h5 : r₀ i = r₀ j := by
      have h := congrArg (fun q : ↥(RootSpace P r R) => q.1.2) h4
      rwa [he₀_snd i, he₀_snd j] at h
    exact hr₀inj h5
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective τfun
    ⟨hτinj, Finite.surjective_of_injective hτinj⟩
  have hτcoe : ⇑τ = τfun := rfl
  have hτpow : τ ^ m.factorial = 1 := by
    have h := perm_pow_factorial τ
    simpa using h
  -- iterating the shift
  have hτiter : ∀ (n : ℕ) (j : Fin m) (w : ↥Ω),
      Fj j (sh^[n] w) = Fj ((τfun^[n]) j) w := by
    intro n
    induction n with
    | zero => intro j w; simp
    | succ n ih =>
      intro j w
      rw [Function.iterate_succ_apply', hτrel, ih]
      congr 1
  -- `Z` is invariant under shifting by `m.factorial * 2πi`
  let cc : ℂ := (m.factorial : ℂ) * uu
  have hcc_re : cc.re = 0 := by simp [cc, Complex.mul_re, huure]
  have hperZ : ∀ j : Fin m, ∀ w : ℂ, w.re < Real.log r → Z j (w + cc) = Z j w := by
    intro j w hw
    have hwΩ : w ∈ Ω := (hΩmem w).mpr hw
    have hwcc : w + cc ∈ Ω := by
      rw [hΩmem]; simpa [Complex.add_re, hcc_re] using hw
    have h4 : (τfun^[m.factorial]) j = j := by
      have h5 : ⇑(τ ^ m.factorial) = (τfun^[m.factorial]) := by
        rw [Equiv.Perm.coe_pow, hτcoe]
      have h6 : ⇑(τ ^ m.factorial) = id := by rw [hτpow]; rfl
      rw [h5] at h6
      exact congr_fun h6 j
    have h3 : (Fj j (sh^[m.factorial] (⟨w, hwΩ⟩ : ↥Ω))).1.2 =
        (Fj j (⟨w, hwΩ⟩ : ↥Ω)).1.2 := by
      have h := hτiter m.factorial j (⟨w, hwΩ⟩ : ↥Ω)
      rw [h4] at h
      exact congrArg (fun q : ↥(RootSpace P r R) => q.1.2) h
    have e1 : (⟨w + cc, hwcc⟩ : ↥Ω) = sh^[m.factorial] (⟨w, hwΩ⟩ : ↥Ω) :=
      Subtype.ext (by rw [hshN])
    calc Z j (w + cc) = (Fj j ⟨w + cc, hwcc⟩).1.2 := hZ_eq j (w + cc) hwcc
      _ = (Fj j (sh^[m.factorial] (⟨w, hwΩ⟩ : ↥Ω))).1.2 := by rw [e1]
      _ = (Fj j (⟨w, hwΩ⟩ : ↥Ω)).1.2 := h3
      _ = Z j w := (hZ_eq j w hwΩ).symm
  -- the branches on the punctured disk
  let N : ℕ := m.factorial
  have hNpos : 0 < N := Nat.factorial_pos m
  have hNcoe : (N : ℂ) = (m.factorial : ℂ) := rfl
  let ρ₁ : ℝ := min 1 (r ^ (1 / (N : ℝ)))
  have hρ₁pos : 0 < ρ₁ := lt_min one_pos (Real.rpow_pos_of_pos hrpos _)
  have hρ₁r : ρ₁ ≤ r ^ (1 / (N : ℝ)) := min_le_right _ _
  have hb : ∀ {u : ℂ}, u ∈ Metric.ball (0 : ℂ) ρ₁ → ‖u‖ < ρ₁ := fun {u} h => by
    simpa [Metric.mem_ball, dist_eq_norm] using h
  have hd : ∀ {u : ℂ}, dist u 0 < ρ₁ → ‖u‖ < ρ₁ := fun {u} h => by
    simpa [dist_eq_norm] using h
  -- the key estimate `‖u‖ ^ N < r`
  have hpow_lt : ∀ u : ℂ, ‖u‖ < ρ₁ → ‖u‖ ^ N < r := by
    intro u hu
    have h1 : (r ^ (1 / (N : ℝ))) ^ N = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hrpos.le, one_div, inv_mul_cancel₀,
        Real.rpow_one]
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hNpos)
    have h2 : ‖u‖ ^ N < (r ^ (1 / (N : ℝ))) ^ N :=
      pow_lt_pow_left₀ (lt_of_lt_of_le hu hρ₁r) (norm_nonneg u)
        (Nat.pos_iff_ne_zero.mp hNpos)
    rwa [h1] at h2
  have hlogre : ∀ u : ℂ, ((N : ℂ) * Complex.log u).re = (N : ℝ) * Real.log ‖u‖ := by
    intro u
    rw [Complex.mul_re, Complex.log_re]
    simp
  have hval : ∀ u : ℂ, u ≠ 0 → ‖u‖ < ρ₁ → ((N : ℂ) * Complex.log u).re < Real.log r := by
    intro u hu0 hu
    rw [hlogre u, ← Real.log_pow ‖u‖ N]
    exact Real.log_lt_log (pow_pos (norm_pos_iff.mpr hu0) N) (hpow_lt u hu)
  -- the branches on the punctured disk are holomorphic
  have hηan : ∀ j : Fin m, AnalyticOnNhd ℂ (fun u : ℂ => Z j ((N : ℂ) * Complex.log u))
      (Metric.ball (0 : ℂ) ρ₁ \ {0}) := by
    intro j u hu
    have hper' : ∀ w : ℂ, w.re < Real.log r →
        Z j (w + (N : ℂ) * (2 * Real.pi * Complex.I)) = Z j w := by
      intro w hw
      have h2 : (N : ℂ) * (2 * Real.pi * Complex.I) = cc := by
        show (N : ℂ) * (2 * Real.pi * Complex.I)
          = (m.factorial : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I)
        rw [hNcoe]
        push_cast
        ring
      rw [h2]
      exact hperZ j w hw
    exact analyticAt_zeta_log_aux (fun w hw => hZan j w hw) hper' hu.2 (hval u hu.2 (hb hu.1))
  -- and bounded
  have hηbdd : ∀ j : Fin m, ∀ u ∈ Metric.ball (0 : ℂ) ρ₁ \ {0},
      ‖Z j ((N : ℂ) * Complex.log u)‖ ≤ R := by
    intro j u hu
    have hu0 : u ≠ 0 := hu.2
    have hmem : ((N : ℂ) * Complex.log u) ∈ Ω := (hΩmem _).mpr (hval u hu.2 (hb hu.1))
    have hroot : (Pz P (Complex.exp ((N : ℂ) * Complex.log u))).eval
        (Z j ((N : ℂ) * Complex.log u)) = 0 := by
      rw [hZ_eq j _ hmem]
      exact hZroot j ⟨_, hmem⟩
    have hexp : Complex.exp ((N : ℂ) * Complex.log u) = u ^ N := by
      rw [Complex.exp_nat_mul, Complex.exp_log hu0]
    rw [hexp] at hroot
    refine hRroot _ ?_ _ hroot
    rw [Complex.norm_pow]
    exact le_of_lt (hpow_lt u (hb hu.1))
  -- extend to the whole disk
  have hext : ∀ j : Fin m, ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball (0 : ℂ) ρ₁) ∧
      ∀ u ∈ Metric.ball (0 : ℂ) ρ₁ \ {0}, g u = Z j ((N : ℂ) * Complex.log u) :=
    fun j => exists_analyticOnNhd_ball_of_bounded_punctured_aux hρ₁pos
      (fun u hu => (hηan j u hu).differentiableAt) (hηbdd j)
  choose g hgan hgeq using hext
  refine ⟨fun j => g j, ρ₁, hρ₁pos, hgan, ?_⟩
  -- the factorization on the disk
  rw [FactoredOn]
  intro u hu
  rcases eq_or_ne u 0 with rfl | hu0
  · -- at the origin, both sides are limits of the factorization on the punctured disk
    refine Polynomial.funext fun Y => ?_
    have hleft : Tendsto (fun v : ℂ => (Pz P (v ^ N)).eval Y) (𝓝 0)
        (𝓝 ((Pz P ((0 : ℂ) ^ N)).eval Y)) := by
      have hev : ∀ v : ℂ, (Pz P (v ^ N)).eval Y
          = ∑ i ∈ P.support, P.coeff i (v ^ N) * Y ^ i := by
        intro v
        rw [Pz, Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
        simp [evAt_apply]
      simp_rw [hev]
      refine tendsto_finsetSum _ fun i _ => ?_
      have hcN : ContinuousAt (fun v : ℂ => v ^ N) (0 : ℂ) :=
        ContinuousAt.pow continuousAt_id N
      have h0N : (0 : ℂ) ^ N = 0 := zero_pow (Nat.pos_iff_ne_zero.mp hNpos)
      have hcA : ContinuousAt (P.coeff i) ((0 : ℂ) ^ N) := by
        simpa only [h0N] using (hana 0 (by simpa using hrpos) i).continuousAt
      have hc : ContinuousAt (fun v : ℂ => P.coeff i (v ^ N)) 0 :=
        ContinuousAt.comp (g := P.coeff i) (f := fun v : ℂ => v ^ N) (x := (0 : ℂ)) hcA hcN
      exact hc.mul_const (Y ^ i)
    have hright : Tendsto (fun v : ℂ => (∏ j, (Polynomial.X - Polynomial.C (g j v))).eval Y)
        (𝓝 0) (𝓝 ((∏ j, (Polynomial.X - Polynomial.C (g j 0))).eval Y)) := by
      have hev : ∀ v : ℂ, (∏ j, (Polynomial.X - Polynomial.C (g j v))).eval Y
          = ∏ j, (Y - g j v) := by
        intro v
        rw [Polynomial.eval_prod]
        exact Finset.prod_congr rfl (fun j _ => by
          simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C])
      simp_rw [hev]
      refine tendsto_finsetProd _ fun j _ => ?_
      exact ContinuousAt.sub continuousAt_const
        (((hgan j) 0 (Metric.mem_ball_self hρ₁pos)).continuousAt)
    have heq : (fun v : ℂ => (Pz P (v ^ N)).eval Y) =ᶠ[𝓝[≠] (0 : ℂ)]
        fun v : ℂ => (∏ j, (Polynomial.X - Polynomial.C (g j v))).eval Y := by
      show ∀ᶠ v in 𝓝[≠] (0 : ℂ), (Pz P (v ^ N)).eval Y
        = (∏ j, (Polynomial.X - Polynomial.C (g j v))).eval Y
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨ρ₁, hρ₁pos, fun v hv hvne => ?_⟩
      have hvne' : v ≠ 0 := hvne
      have hmem : ((N : ℂ) * Complex.log v) ∈ Ω :=
        (hΩmem _).mpr (hval v hvne' (hd hv))
      have h1 := hZfac ⟨(N : ℂ) * Complex.log v, hmem⟩
      rw [show Complex.exp ((N : ℂ) * Complex.log v) = v ^ N from by
        rw [Complex.exp_nat_mul, Complex.exp_log hvne']] at h1
      rw [h1]
      have hkey : ∀ j : Fin m,
          Zsub j ⟨(N : ℂ) * Complex.log v, hmem⟩ = g j v := by
        intro j
        simp only [Zsub]
        rw [← hZ_eq j ((N : ℂ) * Complex.log v) hmem]
        exact (hgeq j v ⟨Metric.mem_ball.mpr hv, hvne⟩).symm
      congr 1
      exact Finset.prod_congr rfl fun j _ => by rw [hkey j]
    exact tendsto_nhds_unique (hleft.mono_left nhdsWithin_le_nhds)
      ((hright.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  · -- away from the origin
    have hmem : ((N : ℂ) * Complex.log u) ∈ Ω := (hΩmem _).mpr (hval u hu0 (hb hu))
    have h1 := hZfac ⟨(N : ℂ) * Complex.log u, hmem⟩
    rw [show Complex.exp ((N : ℂ) * Complex.log u) = u ^ N from by
      rw [Complex.exp_nat_mul, Complex.exp_log hu0]] at h1
    rw [h1]
    have hkey : ∀ j : Fin m, Zsub j ⟨(N : ℂ) * Complex.log u, hmem⟩ = g j u := by
      intro j
      simp only [Zsub]
      rw [← hZ_eq j ((N : ℂ) * Complex.log u) hmem]
      exact (hgeq j u ⟨hu, hu0⟩).symm
    exact Finset.prod_congr rfl fun j _ => by rw [hkey j]

end Work.WilC4aP
