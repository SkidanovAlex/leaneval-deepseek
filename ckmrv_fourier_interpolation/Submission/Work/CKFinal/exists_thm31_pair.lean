import Mathlib
import Submission.Work.Asymptotics.exists_extension_of_propagates
import Submission.Work.Asymptotics.exists_pair_of_propagated_F2
import Submission.Work.Kernels.LogLambdaInstance
import Submission.Work.Kernels.Theorem31
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.LayerCont.Glue.TwoBall
import Submission.Work.CKFinal.exists_F2_socket
import Submission.Work.CKFinal.propagate_rSmooth_seminorm
import Submission.Work.CKFinal.strip_decay_of_line_decay
import Submission.Work.CKFinal.paperLayer_seminorm_DomainD
import Submission.Work.CKFinal.layer_line_decay
import Submission.Work.CKFinal.gaussTerm_seminorm_bound
import Submission.Work.CKFinal.T2op_gaussTerm_holo_bound
import Submission.Work.CKFinal.scale_plumbing
import Submission.Work.CKFinal.S_smul_line_mem_DomainD
import Submission.Work.CKFinal.strip_two_regime

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/CKFinal/DESIGN.md first (orchestrator design; your lemma is one node of its DAG; its §0 lists what is NOT actually proved and §5 what NOT to do). Clashes fixed by the lead (2026-09-25): Kaxis_bounded_compact's Pspace/Cseg/exists_local_bound_clean/… now carry a Kbc suffix; MiddleRange.Main's continuous_jInvariantFun is continuous_jInvariantFun_mr. Siblings run in parallel; import them when they land.

# exists_thm31_pair  (namespace Work.CKFinal)  — assembly of (1)(3)(4)(5), smoothness, evenness, decay

Fix ℓ := `Work.Kernels.logLambda` (Kernels/LogLambdaInstance.lean, sorry-free).

1. (O, F₂) := exists_F2_socket ℓ d hd. For each r, `Work.Asymptotics.exists_extension_of_propagates`
   with Propagates ((d:ℤ)/2) O (F₂ r) (−T2op (gaussTerm · r)) 0 (defect holomorphy:
   `mdifferentiable_T2op_gaussTerm`, `mdifferentiable_const`) gives Ψ r holomorphic on ℍ,
   Ψ r = F₂ r on an open U_r ⊇ closure 𝒟, T2op (Ψ r) = −T2op g_r, S2op (Ψ r) = 0. `choose`.
   (Do NOT go through `exists_pair_of_propagated_F2`: it hides Ψ.)
2. Evenness: Ψ(−r) = Ψ r on ℍ by `Glue.eqOn_of_mdifferentiableOn_of_preconnected` on univ (they agree on
   the nonempty open U_r ∩ U_{−r} since F₂ is even).
3. F τ r := gaussTerm τ r + Ψ r τ;  Ft τ r := −slash ((d:ℤ)/2) R_S (Ψ r) τ  — clauses (1),(5) exactly as
   in the proof of exists_pair_of_propagated_F2 (copy: `mdifferentiable_slash`, `slash_R_S`,
   `T2op_slash_S`, `slash_S_apply`, `Fgen_third_Ipow_key`).
4. propagate_rSmooth_seminorm with h r τ := −T2op (gaussTerm · r) τ; inputs on 𝒟 from
   paperLayer_seminorm_DomainD (Ψ r τ = pL τ r for τ ∈ 𝒟, all r ⇒ same r-function); hh_* from the
   Gaussian: |r^k ∂_r^l e^{πiτr²}| ≤ C_{kl}(1+|τ|)^l (Im τ)^{−(k+l)/2} ≤ C scale^{N} (CKMRV
   eq:moderateGaussian), ∂_r^l e^{πiτr²} = (polynomial in τ, r)·e^{πiτr²} is holomorphic in τ.
   ⇒ Ψ smooth in r everywhere, seminorms ≤ C scale^N.
5. (3) for F: add the Gaussian bound. For Ft: Ft(τ) = −Ψ(S•τ)·τ^{−d/2}; scale(S•τ) ≤ 3 scale(τ)²,
   |τ|^{−d/2} ≤ scale^{d/2}. Convert C·scale^N to α Im^{−β} + γ|τ|^δ
   (scale^N ≤ 2·3^N(Im^{−N} + |τ|^N); cf. `moderateGrowthOn_iff_scale`).
6. Strip decay: for y ≥ 2 apply strip_decay_of_line_decay (m = 1 for d = 8, m = 2 for d = 24) to
   f = F(·,r) (T2op F = 0) and f = Ft(·,r) (T2op Ft = 0) with the uniform C, N of step 5 (k=l=0) and
   the line hypothesis from layer_line_decay (e^{−πy}y^N → 0; e^{2πy}e^{−3πy}y^N → 0), using
   F = g + pL and Ft = −τ^{−d/2}pL(S•τ) on Re τ = ±1/2, Im τ ≥ Y₀ (both points in 𝒟).
   (4): Im τ ≤ 2 from (3) (|τ| ≤ 3), Im τ ≥ 2 from the decay; β := max(β₀, 1).
7. d = 24: TendsToZeroInStrip 24 1: φ(y) := C'(2+y)e^{−2πy} for y ≥ 2, α₀y^{−β}e^{4π} below 2.
8. ContDiff ∞: gaussTerm is smooth in r; Ft τ = −(τ-dependent scalar)·Ψ(·)(S•τ) is smooth in r.

--imports: Submission.Work.Asymptotics.exists_extension_of_propagates Submission.Work.Asymptotics.exists_pair_of_propagated_F2 Submission.Work.Kernels.LogLambdaInstance Submission.Work.Kernels.Theorem31 Submission.Work.FunctionalEquations.Gap Submission.Work.LayerCont.Glue.TwoBall (+ the new modules)
-/

namespace Work.CKFinal

open scoped ContDiff Manifold

set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas -/

/-- The Gaussian `e^{πiτr²}` is even in `r`. -/
lemma etp_gaussTerm_neg (τ : UpperHalfPlane) (r : ℝ) :
    Work.Kernels.gaussTerm τ (-r) = Work.Kernels.gaussTerm τ r := by
  simp only [Work.Kernels.gaussTerm, Complex.ofReal_neg]
  ring_nf

/-- The Gaussian is smooth in `r`. -/
lemma etp_contDiff_gaussTerm (τ : UpperHalfPlane) :
    ContDiff ℝ ∞ (fun r : ℝ => Work.Kernels.gaussTerm τ r) := by
  simp only [Work.Kernels.gaussTerm]
  have h1 : ContDiff ℝ ∞ (fun r : ℝ => ((r : ℂ)) ^ 2) :=
    (Complex.ofRealCLM.contDiff (n := ∞)).pow 2
  have h2 : ContDiff ℝ ∞ (fun r : ℝ => Real.pi * Complex.I * (τ : ℂ) * (r : ℂ) ^ 2) :=
    contDiff_const.mul h1
  exact Complex.contDiff_exp.comp h2

/-- The second difference of the Gaussian is smooth in `r`. -/
lemma etp_contDiff_T2op_gaussTerm (τ : UpperHalfPlane) : ContDiff ℝ ∞ (fun r : ℝ =>
    Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ) := by
  have h (σ : UpperHalfPlane) : ContDiff ℝ ∞ (fun r : ℝ => Work.Kernels.gaussTerm σ r) :=
    etp_contDiff_gaussTerm σ
  have h2 : ContDiff ℝ ∞ (fun r : ℝ =>
      Work.Kernels.gaussTerm ((2 : ℝ) +ᵥ τ) r - 2 * Work.Kernels.gaussTerm ((1 : ℝ) +ᵥ τ) r
        + Work.Kernels.gaussTerm τ r) :=
    ((h _).sub (contDiff_const.mul (h _))).add (h _)
  simpa only [Work.Kernels.T2op, UpperHalfPlane.coe_vadd] using h2

/-- `∂_r^l` of a negated function is the negative of `∂_r^l`. -/
lemma etp_iteratedDeriv_neg (l : ℕ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (r : ℝ) :
    iteratedDeriv l (fun s : ℝ => -g s) r = -iteratedDeriv l g r := by
  rw [show (fun s : ℝ => -g s) = fun s : ℝ => (-1 : ℂ) * g s by funext s; ring]
  rw [iteratedDeriv_const_mul _ (hg.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)), neg_one_mul]

/-- The `z`-power factor in the slash of the Gaussian is controlled by `scale`. -/
lemma etp_norm_zpow_le_scale (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    ‖(τ : ℂ) ^ (-((d : ℤ) / 2))‖ ≤ (Work.Kernels.scale τ) ^ ((d : ℝ) / 2) := by
  rcases hd with rfl | rfl
  · norm_num
    have hpos : 0 < ‖(τ : ℂ)‖ := lt_of_lt_of_le τ.im_pos (Work.Kernels.im_le_coe_norm τ)
    have h3 : ‖(τ : ℂ)‖⁻¹ ≤ (τ.im)⁻¹ := by
      rw [inv_le_inv₀ hpos τ.im_pos]
      exact Work.Kernels.im_le_coe_norm τ
    calc ((‖(τ : ℂ)‖ ^ (4 : ℕ))⁻¹) = ((‖(τ : ℂ)‖⁻¹)) ^ (4 : ℕ) := by rw [inv_pow]
      _ ≤ ((τ.im)⁻¹) ^ (4 : ℕ) := pow_le_pow_left₀ (by positivity) h3 4
      _ ≤ (Work.Kernels.scale τ) ^ (4 : ℕ) :=
          pow_le_pow_left₀ (by positivity) (Work.Kernels.inv_im_le_scale τ) 4
  · norm_num
    have hpos : 0 < ‖(τ : ℂ)‖ := lt_of_lt_of_le τ.im_pos (Work.Kernels.im_le_coe_norm τ)
    have h3 : ‖(τ : ℂ)‖⁻¹ ≤ (τ.im)⁻¹ := by
      rw [inv_le_inv₀ hpos τ.im_pos]
      exact Work.Kernels.im_le_coe_norm τ
    calc ((‖(τ : ℂ)‖ ^ (12 : ℕ))⁻¹) = ((‖(τ : ℂ)‖⁻¹)) ^ (12 : ℕ) := by rw [inv_pow]
      _ ≤ ((τ.im)⁻¹) ^ (12 : ℕ) := pow_le_pow_left₀ (by positivity) h3 12
      _ ≤ (Work.Kernels.scale τ) ^ (12 : ℕ) :=
          pow_le_pow_left₀ (by positivity) (Work.Kernels.inv_im_le_scale τ) 12

/-- `C y^N e^{-cy} ≤ ε` for `y` large. -/
lemma etp_exists_le_rpow_exp {C N c ε : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hε : 0 < ε) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → C * y ^ N * Real.exp (-(c * y)) ≤ ε := by
  by_cases hC0 : C = 0
  · exact ⟨0, fun y _ => by simp [hC0, hε.le]⟩
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  set k : ℕ := ⌈N⌉₊ with hk
  have hkN : N ≤ (k : ℝ) := Nat.le_ceil N
  have hck : (0 : ℝ) < c ^ k := pow_pos hc k
  have htend : Filter.Tendsto (fun y : ℝ => (c * y) ^ k * Real.exp (-(c * y)))
      Filter.atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
      (Filter.tendsto_id.const_mul_atTop hc)
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp
    (htend.eventually (eventually_le_nhds (show (0 : ℝ) < ε * c ^ k / C by positivity)))
  refine ⟨max 1 Y, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_left _ _) hy
  have hYy : Y ≤ y := le_trans (le_max_right _ _) hy
  have h1 : y ^ N ≤ y ^ k := by
    rw [← Real.rpow_natCast y k]
    exact Real.rpow_le_rpow_of_exponent_le hy1 hkN
  have h2 : C * y ^ N * Real.exp (-(c * y)) ≤ C * y ^ k * Real.exp (-(c * y)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact mul_le_mul_of_nonneg_left h1 hC
  have h3 : C * y ^ k * Real.exp (-(c * y))
      = (C / c ^ k) * ((c * y) ^ k * Real.exp (-(c * y))) := by
    rw [mul_pow]; field_simp
  calc C * y ^ N * Real.exp (-(c * y))
      ≤ C * y ^ k * Real.exp (-(c * y)) := h2
    _ = (C / c ^ k) * ((c * y) ^ k * Real.exp (-(c * y))) := h3
    _ ≤ (C / c ^ k) * (ε * c ^ k / C) := mul_le_mul_of_nonneg_left (hY y hYy) (by positivity)
    _ = ε := by field_simp

/-- `(1 + y) e^{-cy} → 0` at `+∞`. -/
lemma etp_tendsto_one_add_exp (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun y : ℝ => (1 + y) * Real.exp (-(c * y))) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun y : ℝ => Real.exp (-(c * y))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (Filter.tendsto_id.const_mul_atTop hc)
  have h2 : Filter.Tendsto (fun y : ℝ => y * Real.exp (-(c * y))) Filter.atTop (nhds 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (Filter.tendsto_id.const_mul_atTop hc)).const_mul c⁻¹
    have h' : Filter.Tendsto (fun y : ℝ => c⁻¹ * ((c * y) ^ 1 * Real.exp (-(c * y))))
        Filter.atTop (nhds 0) := by simpa using h
    refine h'.congr fun y => ?_
    simp only [pow_one]
    field_simp
  have h3 : Filter.Tendsto (fun y : ℝ => Real.exp (-(c * y)) + y * Real.exp (-(c * y)))
      Filter.atTop (nhds 0) := by simpa using h1.add h2
  refine h3.congr fun y => ?_
  ring

/-- The product of the two exponential factors occurring in the line-decay bounds. -/
lemma etp_exp_combined (d m : ℕ) (hd : d = 8 ∨ d = 24) (hm : m = if d = 8 then 1 else 2)
    (y : ℝ) : Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * y))
      * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * y) = Real.exp (-(Real.pi * y)) := by
  subst hm
  rw [← Real.exp_add]
  congr 1
  rcases hd with rfl | rfl <;> (norm_num; try ring)


/-- The hypotheses of CKMRV Thm 3.1 for `d ∈ {8, 24}` (for any `k₀`, which
`SatisfiesThm31` does not use), with smoothness and evenness of the radial profiles and, for
`d = 24`, the strip decay `F, F̃ = o(e^{-2π Im τ})`. -/
theorem exists_thm31_pair (d k₀ : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ F Ft : UpperHalfPlane → ℝ → ℂ, Work.Kernels.SatisfiesThm31 d k₀ F Ft ∧
      (∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (F τ)) ∧
      (∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (Ft τ)) ∧
      (∀ τ : UpperHalfPlane, Function.Even (F τ)) ∧
      (∀ τ : UpperHalfPlane, Function.Even (Ft τ)) ∧
      (d = 24 →
        Work.FE.TendsToZeroInStrip 24 1
          (fun τ x => if h : 0 < τ.im then F ⟨τ, h⟩ ‖x‖ else 0) ∧
        Work.FE.TendsToZeroInStrip 24 1
          (fun τ x => if h : 0 < τ.im then Ft ⟨τ, h⟩ ‖x‖ else 0)) := by


  classical
  -- ## Step 1. The `F₂`-socket (CKMRV Prop. 4.6) and the global propagation extensions `Ψ r`.
  obtain ⟨O, F₂, hOopen, hOsub, hF₂md, hF₂D, hF₂even, hF₂T, hF₂S⟩ :=
    exists_F2_socket Work.Kernels.logLambda d hd
  have hkey : ∀ r : ℝ, ∃ Ψ : UpperHalfPlane → ℂ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) Ψ ∧
      (∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧ U ⊆ O ∧
        ∀ τ ∈ U, Ψ τ = F₂ r τ) ∧
      (∀ τ : UpperHalfPlane, Work.Kernels.T2op Ψ τ =
        -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ) ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.S2op ((d : ℤ) / 2) Ψ τ = 0) := by
    intro r
    have hprop : Work.Asymptotics.Propagates ((d : ℤ) / 2) O (F₂ r)
        (fun τ : UpperHalfPlane =>
          -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ) 0 :=
      ⟨hOopen, (Work.Asymptotics.mdifferentiable_T2op_gaussTerm r).neg, mdifferentiable_const,
        hF₂md r, hF₂T r, hF₂S r⟩
    exact Work.Asymptotics.exists_extension_of_propagates hprop hOsub
  choose Ψ hΨmd hΨU hΨT hΨS using hkey
  choose U hUopen hUcl hUsub hUeq using hΨU
  -- ## Step 2. `Ψ` is even in `r` (uniqueness of the extension, `F₂` being even).
  have hΨeven : ∀ r : ℝ, Ψ (-r) = Ψ r := by
    intro r
    have hEq : Set.EqOn (Ψ (-r)) (Ψ r) Set.univ := by
      refine Work.LayerCont.Glue.eqOn_of_mdifferentiableOn_of_preconnected
        (U := Set.univ) (F := Ψ (-r)) (G := Ψ r) (V := U (-r) ∩ U r)
        isOpen_univ isPreconnected_univ (hΨmd (-r)).mdifferentiableOn
        (hΨmd r).mdifferentiableOn (Set.subset_univ _) ?_ ?_ ?_
      · exact (hUopen (-r)).inter (hUopen r)
      · obtain ⟨τ, hτ⟩ := Work.Asymptotics.DomainD_nonempty
        exact ⟨τ, hUcl (-r) (subset_closure hτ), hUcl r (subset_closure hτ)⟩
      · intro τ hτ
        exact (hUeq (-r) τ hτ.1).trans ((hF₂even r τ).trans (hUeq r τ hτ.2).symm)
    funext τ
    exact hEq (Set.mem_univ τ)
  -- ## Step 3. The `𝒟`-input for the propagation lemma, from `paperLayer_seminorm_DomainD`.
  have hB1 := paperLayer_seminorm_DomainD Work.Kernels.logLambda d hd
  have hD_smooth : ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD →
      ContDiff ℝ ∞ (fun r : ℝ => Ψ r τ) := by
    intro τ hτ
    have hfun : (fun r : ℝ => Ψ r τ) = fun r : ℝ =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp Work.Kernels.logLambda d)
          Work.Kernels.logLambda d τ r := by
      funext r
      rw [hUeq r τ (hUcl r (subset_closure hτ)), hF₂D r τ hτ]
    rw [hfun]
    exact hB1.1 τ hτ
  have hD_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.DomainD → ∀ r : ℝ,
        |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
    intro k' l
    obtain ⟨C, N, hC, hN, hle⟩ := hB1.2 k' l
    refine ⟨C, N, hC, hN, fun τ hτ r => ?_⟩
    have hfun : (fun s : ℝ => Ψ s τ) = fun s : ℝ =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp Work.Kernels.logLambda d)
          Work.Kernels.logLambda d τ s := by
      funext s
      rw [hUeq s τ (hUcl s (subset_closure hτ)), hF₂D s τ hτ]
    rw [hfun]
    exact hle τ hτ r
  -- ## Step 4. The remaining hypotheses on the Gaussian defect, from the delegated lemmas.
  obtain ⟨hT2holo, hT2bd⟩ := T2op_gaussTerm_holo_bound
  have hh_smooth : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (fun r : ℝ =>
      -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ) :=
    fun τ => (etp_contDiff_T2op_gaussTerm τ).neg
  have hh_holo : ∀ (l : ℕ) (r : ℝ), MDifferentiable (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) (fun τ : UpperHalfPlane =>
        iteratedDeriv l (fun s : ℝ =>
          -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ) r) := by
    intro l r
    rw [funext (fun τ => etp_iteratedDeriv_neg l
      (fun s : ℝ => Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ)
      (etp_contDiff_T2op_gaussTerm τ) r)]
    exact (hT2holo l r).neg
  have hh_bd : ∀ k' l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k' * ‖iteratedDeriv l (fun s : ℝ =>
        -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N := by
    intro k' l
    obtain ⟨C, N, hC, hN, hle⟩ := hT2bd k' l
    refine ⟨C, N, hC, hN, fun τ r => ?_⟩
    rw [etp_iteratedDeriv_neg l
      (fun s : ℝ => Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ s) τ)
      (etp_contDiff_T2op_gaussTerm τ) r, norm_neg]
    exact hle τ r
  -- ## Step 5. Propagation of `r`-smoothness and of the weighted seminorm bounds to all of `ℍ`.
  obtain ⟨hΨsm, hΨsc⟩ := propagate_rSmooth_seminorm ((d : ℤ) / 2) Ψ
    (fun r τ => -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) τ)
    hΨmd (fun r τ => hΨT r τ) hΨS hh_smooth hh_holo hh_bd hD_smooth hD_bd
  -- ## Step 6. The generating functions.
  set F : UpperHalfPlane → ℝ → ℂ :=
    fun τ r => Work.Kernels.gaussTerm τ r + Ψ r τ with hFdef
  set Ft : UpperHalfPlane → ℝ → ℂ :=
    fun τ r => -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) τ) with hFtdef
  have hFsmooth : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (fun r : ℝ => F τ r) := by
    intro τ
    have : F τ = fun r : ℝ => Work.Kernels.gaussTerm τ r + Ψ r τ := rfl
    rw [this]
    exact (etp_contDiff_gaussTerm τ).add (hΨsm τ)
  have hF_md : ∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun σ : UpperHalfPlane => F σ r) :=
    fun r => (Work.Asymptotics.mdifferentiable_gaussTerm r).add (hΨmd r)
  have hFt_md : ∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun σ : UpperHalfPlane => Ft σ r) := by
    intro r
    have h1 : (fun σ : UpperHalfPlane => Ft σ r)
        = -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r)) := rfl
    rw [h1]
    exact (Work.Asymptotics.mdifferentiable_slash (hΨmd r) ((d : ℤ) / 2) Work.Kernels.R_S).neg
  have hFtsmooth : ∀ τ : UpperHalfPlane, ContDiff ℝ ∞ (fun r : ℝ => Ft τ r) := by
    intro τ
    have hrew : Ft τ = fun r : ℝ =>
        -((fun r : ℝ => Ψ r (ModularGroup.S • τ)) r * (τ : ℂ) ^ (-((d : ℤ) / 2))) := by
      funext r
      have h1 : Ft τ r
          = -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) τ) := rfl
      rw [h1, Work.Kernels.slash_R_S, Work.Kernels.slash_S_apply]
    rw [hrew]
    exact ((hΨsm (ModularGroup.S • τ)).mul contDiff_const).neg
  -- ## Step 7. The scale-form growth bounds.
  have hFscale : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => F τ s) r‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
    intro k l
    obtain ⟨Cg, Ng, hCg, hNg, hgb⟩ := gaussTerm_seminorm_bound k l
    obtain ⟨Cp, Np, hCp, hNp, hpb⟩ := hΨsc k l
    refine ⟨Cg + Cp, max Ng Np, by positivity, le_max_of_le_left hNg, fun τ r => ?_⟩
    have hcd1 : ContDiffAt ℝ (l : ℕ∞ω) (fun s : ℝ => Work.Kernels.gaussTerm τ s) r :=
      (etp_contDiff_gaussTerm τ).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hcd2 : ContDiffAt ℝ (l : ℕ∞ω) (fun s : ℝ => Ψ s τ) r :=
      (hΨsm τ).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hsplit : iteratedDeriv l (fun s : ℝ => F τ s) r
        = iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r
          + iteratedDeriv l (fun s : ℝ => Ψ s τ) r := by
      have h2 : (fun s : ℝ => F τ s)
          = (fun s : ℝ => Work.Kernels.gaussTerm τ s) + fun s : ℝ => Ψ s τ := rfl
      rw [h2, iteratedDeriv_add hcd1 hcd2]
    rw [hsplit]
    have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hNg' : (Work.Kernels.scale τ) ^ Ng ≤ (Work.Kernels.scale τ) ^ max Ng Np :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    have hNp' : (Work.Kernels.scale τ) ^ Np ≤ (Work.Kernels.scale τ) ^ max Ng Np :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
    calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r
            + iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖
        ≤ |r| ^ k * (‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
            + ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Kernels.gaussTerm τ s) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Ψ s τ) r‖ := by ring
      _ ≤ Cg * (Work.Kernels.scale τ) ^ Ng + Cp * (Work.Kernels.scale τ) ^ Np :=
          add_le_add (hgb τ r) (hpb τ r)
      _ ≤ Cg * (Work.Kernels.scale τ) ^ max Ng Np + Cp * (Work.Kernels.scale τ) ^ max Ng Np :=
          add_le_add (mul_le_mul_of_nonneg_left hNg' hCg) (mul_le_mul_of_nonneg_left hNp' hCp)
      _ = (Cg + Cp) * (Work.Kernels.scale τ) ^ max Ng Np := by ring
  have hFtscale : ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Ft τ s) r‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
    intro k l
    obtain ⟨Cp, Np, hCp, hNp, hpb⟩ := hΨsc k l
    obtain ⟨CS, hCS, hCSle⟩ := Work.Kernels.scale_smul_le ModularGroup.S
    refine ⟨Cp * CS ^ Np, (d : ℝ) / 2 + 3 * Np, by positivity, by positivity, fun τ r => ?_⟩
    have hcd2 : ContDiffAt ℝ (l : ℕ∞ω) (fun s : ℝ => Ψ s (ModularGroup.S • τ)) r :=
      (hΨsm (ModularGroup.S • τ)).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have heq : (fun s : ℝ => Ft τ s) = fun s : ℝ =>
        (-((τ : ℂ) ^ (-((d : ℤ) / 2)))) * Ψ s (ModularGroup.S • τ) := by
      funext s
      have h1 : Ft τ s
          = -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ s) τ) := rfl
      rw [h1, Work.Kernels.slash_R_S, Work.Kernels.slash_S_apply]
      ring
    rw [heq, iteratedDeriv_const_mul _ hcd2, norm_mul]
    have hnormc : ‖-((τ : ℂ) ^ (-((d : ℤ) / 2)))‖ ≤ (Work.Kernels.scale τ) ^ ((d : ℝ) / 2) := by
      rw [norm_neg]
      exact etp_norm_zpow_le_scale d hd τ
    have hspos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have hstep : (Work.Kernels.scale (ModularGroup.S • τ)) ^ Np
        ≤ CS ^ Np * (Work.Kernels.scale τ) ^ (3 * Np) := by
      calc (Work.Kernels.scale (ModularGroup.S • τ)) ^ Np
          ≤ (CS * (Work.Kernels.scale τ) ^ 3) ^ Np :=
            Real.rpow_le_rpow (le_of_lt (Work.Kernels.scale_pos _)) (hCSle τ) hNp
        _ = CS ^ Np * ((Work.Kernels.scale τ) ^ 3) ^ Np := Real.mul_rpow hCS (by positivity)
        _ = CS ^ Np * (Work.Kernels.scale τ) ^ (3 * Np) := by
            rw [← Real.rpow_mul (le_of_lt hspos)]
    have hstep2 : Cp * (Work.Kernels.scale (ModularGroup.S • τ)) ^ Np
        ≤ Cp * (CS ^ Np * (Work.Kernels.scale τ) ^ (3 * Np)) :=
      mul_le_mul_of_nonneg_left hstep hCp
    calc |r| ^ k * (‖-((τ : ℂ) ^ (-((d : ℤ) / 2)))‖ * ‖iteratedDeriv l (fun s : ℝ => Ψ s (ModularGroup.S • τ)) r‖)
        = ‖-((τ : ℂ) ^ (-((d : ℤ) / 2)))‖ *
            (|r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Ψ s (ModularGroup.S • τ)) r‖) := by ring
      _ ≤ (Work.Kernels.scale τ) ^ ((d : ℝ) / 2) *
            (Cp * (Work.Kernels.scale (ModularGroup.S • τ)) ^ Np) :=
          mul_le_mul hnormc (hpb (ModularGroup.S • τ) r) (by positivity)
            (Real.rpow_nonneg (le_of_lt hspos) _)
      _ ≤ (Work.Kernels.scale τ) ^ ((d : ℝ) / 2) *
            (Cp * (CS ^ Np * (Work.Kernels.scale τ) ^ (3 * Np))) :=
          mul_le_mul_of_nonneg_left hstep2 (Real.rpow_nonneg (le_of_lt hspos) _)
      _ = (Cp * CS ^ Np) * (Work.Kernels.scale τ) ^ ((d : ℝ) / 2 + 3 * Np) := by
          rw [Real.rpow_add hspos]; ring
  -- ## Step 8. The `(3)`-form growth bounds, by converting `scale^N` into `α Im^{-β} + γ‖τ‖^δ`.
  have hF3 : ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ),
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => F τ s) r‖
          ≤ α * τ.im ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ := by
    intro k l
    obtain ⟨C, N, hC, hN, hle⟩ := hFscale k l
    obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hconv⟩ := scale_plumbing N hN
    refine ⟨C * α, β, C * γ, δ, by positivity, hβ, by positivity, hδ, fun τ r => ?_⟩
    calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => F τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N := hle τ r
      _ ≤ C * (α * τ.im ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ) :=
          mul_le_mul_of_nonneg_left (hconv τ) hC
      _ = (C * α) * τ.im ^ (-β) + (C * γ) * ‖(τ : ℂ)‖ ^ δ := by ring
  have hFt3 : ∀ k l : ℕ, ∃ α β γ δ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ),
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Ft τ s) r‖
          ≤ α * τ.im ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ := by
    intro k l
    obtain ⟨C, N, hC, hN, hle⟩ := hFtscale k l
    obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hconv⟩ := scale_plumbing N hN
    refine ⟨C * α, β, C * γ, δ, by positivity, hβ, by positivity, hδ, fun τ r => ?_⟩
    calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Ft τ s) r‖
        ≤ C * (Work.Kernels.scale τ) ^ N := hle τ r
      _ ≤ C * (α * τ.im ^ (-β) + γ * ‖(τ : ℂ)‖ ^ δ) :=
          mul_le_mul_of_nonneg_left (hconv τ) hC
      _ = (C * α) * τ.im ^ (-β) + (C * γ) * ‖(τ : ℂ)‖ ^ δ := by ring
  -- ## Step 9. The functional equations in `τ`.
  have hF_T2 : ∀ (r : ℝ) (τ : UpperHalfPlane),
      Work.Kernels.T2op (fun σ : UpperHalfPlane => F σ r) τ = 0 := by
    intro r τ
    have h1 : Work.Kernels.T2op (fun σ : UpperHalfPlane => F σ r)
        = Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r + Ψ r σ) :=
      rfl
    rw [h1, Work.Kernels.T2op_add', funext (hΨT r)]
    simp
  have hFt_T2 : ∀ (r : ℝ) (τ : UpperHalfPlane),
      Work.Kernels.T2op (fun σ : UpperHalfPlane => Ft σ r) τ = 0 := by
    intro r τ
    have h1 : Work.Kernels.T2op (fun σ : UpperHalfPlane => Ft σ r)
        = Work.Kernels.T2op (fun σ : UpperHalfPlane =>
            -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) σ)) := rfl
    rw [h1, Work.Kernels.T2op_neg', ← Work.Asymptotics.S2op_eq_T2op_slash,
      funext (hΨS r)]
    simp
  have hFE3 : ∀ (τ : UpperHalfPlane) (r : ℝ),
      F τ r + (Complex.I / (τ : ℂ)) ^ (d / 2) * Ft (ModularGroup.S • τ) r
        = Work.Kernels.gaussTerm τ r := by
    intro τ r
    have hdI : (-Complex.I) ^ (d / 2) = 1 := by
      have h4 : (-Complex.I) ^ 4 = 1 := by norm_num [Complex.ext_iff, Complex.I_mul_I]
      rcases hd with rfl | rfl
      · norm_num
      · calc (-Complex.I) ^ (24 / 2) = (-Complex.I) ^ (4 * 3) := by norm_num
          _ = ((-Complex.I) ^ 4) ^ 3 := by rw [pow_mul]
          _ = 1 := by rw [h4]; norm_num
    have hSS : ModularGroup.S • (ModularGroup.S • τ) = τ := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
      simp
    have hslash : Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r)
          (ModularGroup.S • τ) = Ψ r τ * (-((τ : ℂ))⁻¹) ^ (-((d : ℤ) / 2)) := by
      rw [Work.Kernels.slash_R_S, Work.Kernels.slash_S_apply, hSS, Work.Kernels.S_smul_coe]
    have hFr : F τ r = Work.Kernels.gaussTerm τ r + Ψ r τ := rfl
    have hFtr : Ft (ModularGroup.S • τ) r
        = -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r)
            (ModularGroup.S • τ)) := rfl
    rw [hFr, hFtr, hslash]
    have hkey2 := Work.Kernels.Section5Facts.Fgen_third_Ipow_key (τ : ℂ)
      (UpperHalfPlane.ne_zero τ) d hdI
    rw [show (Complex.I / (τ : ℂ)) ^ (d / 2)
          * (-(Ψ r τ * (-((τ : ℂ))⁻¹) ^ (-((d : ℤ) / 2))))
        = -((Complex.I / (τ : ℂ)) ^ (d / 2)
            * (-((τ : ℂ))⁻¹) ^ (-((d : ℤ) / 2))) * (Ψ r τ) by ring]
    rw [hkey2]
    ring
  -- ## Step 10. The two `scale`-form bounds with `k = l = 0`, and the line decay.
  obtain ⟨CF, NF, hCF, hNF, hF0⟩ := hFscale 0 0
  obtain ⟨Ct, Nt, hCt, hNt, hFt0⟩ := hFtscale 0 0
  have hF0' : ∀ (τ : UpperHalfPlane) (r : ℝ),
      ‖F τ r‖ ≤ max CF Ct * (Work.Kernels.scale τ) ^ max NF Nt := by
    intro τ r
    have h := hF0 τ r
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    have hs := Work.Kernels.one_le_scale τ
    have h1 : (Work.Kernels.scale τ) ^ NF ≤ (Work.Kernels.scale τ) ^ max NF Nt :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    calc ‖F τ r‖ ≤ CF * (Work.Kernels.scale τ) ^ NF := h
      _ ≤ max CF Ct * (Work.Kernels.scale τ) ^ max NF Nt :=
          mul_le_mul (le_max_left _ _) h1
            (Real.rpow_nonneg (by positivity) _) (le_trans hCF (le_max_left _ _))
  have hFt0' : ∀ (τ : UpperHalfPlane) (r : ℝ),
      ‖Ft τ r‖ ≤ max CF Ct * (Work.Kernels.scale τ) ^ max NF Nt := by
    intro τ r
    have h := hFt0 τ r
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    have hs := Work.Kernels.one_le_scale τ
    have h1 : (Work.Kernels.scale τ) ^ Nt ≤ (Work.Kernels.scale τ) ^ max NF Nt :=
      Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)
    calc ‖Ft τ r‖ ≤ Ct * (Work.Kernels.scale τ) ^ Nt := h
      _ ≤ max CF Ct * (Work.Kernels.scale τ) ^ max NF Nt :=
          mul_le_mul (le_max_right _ _) h1
            (Real.rpow_nonneg (by positivity) _) (le_trans hCF (le_max_left _ _))
  -- The dimension parameter `m` of `strip_decay_of_line_decay`.
  set m : ℕ := if d = 8 then 1 else 2 with hmdef
  have hm12 : m = 1 ∨ m = 2 := by
    rcases hd with rfl | rfl
    · left; simp [hmdef]
    · right; simp [hmdef]
  have hrate : Real.exp (2 * Real.pi * ((m : ℝ) - 1) * (1:ℝ))
      = Real.exp (2 * Real.pi * ((m : ℝ) - 1)) := by ring_nf
  -- the decay needed on each of the two vertical lines, for `F` and for `Ft`
  -- the decay needed on each of the two vertical lines, for `F` and for `Ft`
  have hlineF : ∀ r : ℝ, ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖F τ r‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) ≤ ε := by
    intro r ε hε
    obtain ⟨Cy, Ny, Y₀, hCy, hNy, hY₀, hlay⟩ :=
      layer_line_decay Work.Kernels.logLambda d hd
    obtain ⟨Y₁, hY₁⟩ := etp_exists_le_rpow_exp (C := Cy) (N := Ny) (c := Real.pi) hCy
      Real.pi_pos hε
    refine ⟨max Y₀ Y₁, fun τ hτre hYτ => ?_⟩
    have hy0 : Y₀ ≤ τ.im := le_trans (le_max_left _ _) hYτ
    have hy1 : Y₁ ≤ τ.im := le_trans (le_max_right _ _) hYτ
    obtain ⟨hτD, -⟩ := S_smul_line_mem_DomainD τ hτre (le_trans hY₀ hy0)
    have hFeq : F τ r = Work.Kernels.gaussTerm τ r
        + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp Work.Kernels.logLambda d)
            Work.Kernels.logLambda d τ r := by
      have h1 : F τ r = Work.Kernels.gaussTerm τ r + Ψ r τ := rfl
      rw [h1, hUeq r τ (hUcl r (subset_closure hτD)), hF₂D r τ hτD]
    rw [hFeq]
    have hb := (hlay τ r hτre hy0).1
    calc ‖Work.Kernels.gaussTerm τ r
            + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp Work.Kernels.logLambda d)
                Work.Kernels.logLambda d τ r‖
            * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im)
        ≤ (Cy * τ.im ^ Ny
            * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im)))
            * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = Cy * τ.im ^ Ny
            * (Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im))
              * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im)) := by ring
      _ = Cy * τ.im ^ Ny * Real.exp (-(Real.pi * τ.im)) := by
          rw [etp_exp_combined d m hd hmdef τ.im]
      _ ≤ ε := hY₁ τ.im hy1
  have hlineFt : ∀ r : ℝ, ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
      ‖Ft τ r‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) ≤ ε := by
    intro r ε hε
    obtain ⟨Cy, Ny, Y₀, hCy, hNy, hY₀, hlay⟩ :=
      layer_line_decay Work.Kernels.logLambda d hd
    obtain ⟨Y₁, hY₁⟩ := etp_exists_le_rpow_exp (C := Cy) (N := Ny) (c := Real.pi) hCy
      Real.pi_pos hε
    refine ⟨max Y₀ Y₁, fun τ hτre hYτ => ?_⟩
    have hy0 : Y₀ ≤ τ.im := le_trans (le_max_left _ _) hYτ
    have hy1 : Y₁ ≤ τ.im := le_trans (le_max_right _ _) hYτ
    obtain ⟨-, hSτD⟩ := S_smul_line_mem_DomainD τ hτre (le_trans hY₀ hy0)
    have hFteq : Ft τ r = -(Work.Asymptotics.paperLayer
        (Work.Asymptotics.Gcusp Work.Kernels.logLambda d)
        Work.Kernels.logLambda d (ModularGroup.S • τ) r * (τ : ℂ) ^ (-((d : ℤ) / 2))) := by
      have h1 : Ft τ r = -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) τ) := rfl
      rw [h1, Work.Kernels.slash_R_S, Work.Kernels.slash_S_apply,
        hUeq r (ModularGroup.S • τ) (hUcl r (subset_closure hSτD)),
        hF₂D r (ModularGroup.S • τ) hSτD]
    rw [hFteq, norm_neg]
    have hb := (hlay τ r hτre hy0).2
    calc ‖Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp Work.Kernels.logLambda d)
            Work.Kernels.logLambda d (ModularGroup.S • τ) r * (τ : ℂ) ^ (-((d : ℤ) / 2))‖
            * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im)
        ≤ (Cy * τ.im ^ Ny
            * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im)))
            * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) :=
          mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _)
      _ = Cy * τ.im ^ Ny
            * (Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im))
              * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im)) := by ring
      _ = Cy * τ.im ^ Ny * Real.exp (-(Real.pi * τ.im)) := by
          rw [etp_exp_combined d m hd hmdef τ.im]
      _ ≤ ε := hY₁ τ.im hy1
  -- ## Step 11. The strip bound (4): a large-`Im` regime from `strip_decay_of_line_decay`
  -- and a small-`Im` regime from `(3)`, merged by `strip_two_regime`.
  obtain ⟨α₀, β₀, γ₀, δ₀, hα₀, hβ₀, hγ₀, hδ₀, hF30⟩ := hF3 0 0
  obtain ⟨α₁, β₁, γ₁, δ₁, hα₁, hβ₁, hγ₁, hδ₁, hFt30⟩ := hFt3 0 0
  obtain ⟨C', hC'0, hC'⟩ := strip_decay_of_line_decay m hm12 (max CF Ct) (max NF Nt)
  -- bound `‖τ‖ ≤ 3` in the closed strip with `Im τ ≤ 2`
  have hnorm3 : ∀ τ : UpperHalfPlane, -1 ≤ τ.re → τ.re ≤ 1 → τ.im ≤ 2 → ‖(τ : ℂ)‖ ≤ 3 := by
    intro τ h1 h2 h3
    have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    have h4 : ‖(τ : ℂ)‖ ^ 2 ≤ 9 := by
      rw [hsq]; nlinarith [τ.im_pos, h1, h2, h3]
    nlinarith [norm_nonneg (τ : ℂ)]
  -- the small-`Im` bound, valid for both `F` and `Ft`
  set B : ℝ := max β₀ β₁ with hBdef
  set A : ℝ := max (α₀ * 2 ^ (max β₀ β₁ - β₀)) (α₁ * 2 ^ (max β₀ β₁ - β₁)) with hAdef
  set Cc : ℝ := max γ₀ γ₁ with hCcdef
  set D : ℝ := max δ₀ δ₁ with hDdef
  have hB0 : (0 : ℝ) ≤ B := le_trans hβ₀ (le_max_left _ _)
  have hA0 : (0 : ℝ) ≤ A := le_trans
    (mul_nonneg hα₀ (by positivity)) (le_max_left _ _)
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans hγ₀ (le_max_left _ _)
  have hD0 : (0 : ℝ) ≤ D := le_trans hδ₀ (le_max_left _ _)
  have hsmallF : ∀ (τ : UpperHalfPlane) (r : ℝ), 0 < τ.im → τ.im ≤ 2 → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖F τ r‖ ≤ A * τ.im ^ (-B) + Cc * 3 ^ D := by
    intro τ r hy hy2 h1 h2
    have h := hF30 τ r
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    have h3 := hnorm3 τ h1 h2 hy2
    have h4 : ‖(τ : ℂ)‖ ^ δ₀ ≤ 3 ^ δ₀ := Real.rpow_le_rpow (norm_nonneg _) h3 hδ₀
    have h5 : γ₀ * ‖(τ : ℂ)‖ ^ δ₀ ≤ Cc * 3 ^ D := by
      have h6 : γ₀ * ‖(τ : ℂ)‖ ^ δ₀ ≤ Cc * 3 ^ δ₀ :=
        mul_le_mul (le_max_left _ _) h4 (Real.rpow_nonneg (norm_nonneg _) _) hCc0
      have h7 : (3 : ℝ) ^ δ₀ ≤ 3 ^ D := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_left _ _)
      exact le_trans h6 (mul_le_mul_of_nonneg_left h7 hCc0)
    have h8 : α₀ * τ.im ^ (-β₀) ≤ A * τ.im ^ (-B) := by
      have h9 : τ.im ^ (-β₀) ≤ 2 ^ (B - β₀) * τ.im ^ (-B) := by
        have hy1 : (0:ℝ) < τ.im := hy
        have h10 : τ.im ^ (-β₀) = τ.im ^ (-B) * τ.im ^ (B - β₀) := by
          rw [← Real.rpow_add hy1]; ring_nf
        rw [h10, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (le_of_lt hy1) hy2 (by linarith [le_max_left β₀ β₁]))
          (Real.rpow_nonneg (le_of_lt hy1) _)
      calc α₀ * τ.im ^ (-β₀) ≤ α₀ * (2 ^ (B - β₀) * τ.im ^ (-B)) :=
            mul_le_mul_of_nonneg_left h9 hα₀
        _ ≤ A * τ.im ^ (-B) := by
            have : α₀ * 2 ^ (B - β₀) ≤ A := by
              rw [hAdef, hBdef]; exact le_max_left _ _
            calc α₀ * (2 ^ (B - β₀) * τ.im ^ (-B))
                = (α₀ * 2 ^ (B - β₀)) * τ.im ^ (-B) := by ring
              _ ≤ A * τ.im ^ (-B) := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (le_of_lt hy) _)
    exact le_trans h (add_le_add h8 h5)
  have hsmallFt : ∀ (τ : UpperHalfPlane) (r : ℝ), 0 < τ.im → τ.im ≤ 2 → -1 ≤ τ.re → τ.re ≤ 1 →
      ‖Ft τ r‖ ≤ A * τ.im ^ (-B) + Cc * 3 ^ D := by
    intro τ r hy hy2 h1 h2
    have h := hFt30 τ r
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
    have h3 := hnorm3 τ h1 h2 hy2
    have h4 : ‖(τ : ℂ)‖ ^ δ₁ ≤ 3 ^ δ₁ := Real.rpow_le_rpow (norm_nonneg _) h3 hδ₁
    have h5 : γ₁ * ‖(τ : ℂ)‖ ^ δ₁ ≤ Cc * 3 ^ D := by
      have h6 : γ₁ * ‖(τ : ℂ)‖ ^ δ₁ ≤ Cc * 3 ^ δ₁ :=
        mul_le_mul (le_max_right _ _) h4 (Real.rpow_nonneg (norm_nonneg _) _) hCc0
      have h7 : (3 : ℝ) ^ δ₁ ≤ 3 ^ D := Real.rpow_le_rpow_of_exponent_le (by norm_num) (le_max_right _ _)
      exact le_trans h6 (mul_le_mul_of_nonneg_left h7 hCc0)
    have h8 : α₁ * τ.im ^ (-β₁) ≤ A * τ.im ^ (-B) := by
      have h9 : τ.im ^ (-β₁) ≤ 2 ^ (B - β₁) * τ.im ^ (-B) := by
        have hy1 : (0:ℝ) < τ.im := hy
        have h10 : τ.im ^ (-β₁) = τ.im ^ (-B) * τ.im ^ (B - β₁) := by
          rw [← Real.rpow_add hy1]; ring_nf
        rw [h10, mul_comm]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (le_of_lt hy1) hy2 (by linarith [le_max_right β₀ β₁]))
          (Real.rpow_nonneg (le_of_lt hy1) _)
      calc α₁ * τ.im ^ (-β₁) ≤ α₁ * (2 ^ (B - β₁) * τ.im ^ (-B)) :=
            mul_le_mul_of_nonneg_left h9 hα₁
        _ ≤ A * τ.im ^ (-B) := by
            have : α₁ * 2 ^ (B - β₁) ≤ A := by
              rw [hAdef, hBdef]; exact le_max_right _ _
            calc α₁ * (2 ^ (B - β₁) * τ.im ^ (-B))
                = (α₁ * 2 ^ (B - β₁)) * τ.im ^ (-B) := by ring
              _ ≤ A * τ.im ^ (-B) := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (le_of_lt hy) _)
    exact le_trans h (add_le_add h8 h5)
  obtain ⟨α, β, hα, hβ, hlarge, hsmall⟩ :=
    strip_two_regime C' B A Cc D hC'0 hA0 hB0 hCc0 hD0
  have hstrip : ∃ α β : ℝ, 0 ≤ α ∧ 0 < β ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      -1 ≤ τ.re → τ.re ≤ 1 → max ‖F τ r‖ ‖Ft τ r‖ ≤ α * τ.im ^ (-β) := by
    refine ⟨α, β, hα, hβ, fun τ r h1 h2 => ?_⟩
    have hnorm_le : ‖(τ : ℂ)‖ ≤ 1 + τ.im := by
      have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
        ring
      have h3 : ‖(τ : ℂ)‖ ^ 2 ≤ (1 + τ.im) ^ 2 := by
        rw [hsq]; nlinarith [τ.im_pos, h1, h2]
      have h4 : 0 ≤ ‖(τ : ℂ)‖ := norm_nonneg _
      have h5 : 0 ≤ 1 + τ.im := by linarith [τ.im_pos]
      have h6 : |‖(τ : ℂ)‖| ≤ |1 + τ.im| := sq_le_sq.mp h3
      rwa [abs_of_nonneg h4, abs_of_nonneg h5] at h6
    by_cases hy : 2 ≤ τ.im
    · have hmle : Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) ≤ Real.exp (-(2 * Real.pi * τ.im)) := by
        apply Real.exp_le_exp.mpr
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
          rcases hm12 with h | h <;> rw [h] <;> norm_num
        have hprod : 2 * Real.pi * τ.im * 1 ≤ 2 * Real.pi * τ.im * (m : ℝ) :=
          mul_le_mul_of_nonneg_left hm1
            (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (le_of_lt τ.im_pos))
        linarith [hprod]
      have hstep : ∀ (g : UpperHalfPlane → ℂ),
          ‖g τ‖ ≤ C' * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) →
          ‖g τ‖ ≤ C' * (2 + τ.im) * Real.exp (-(2 * Real.pi * τ.im)) := by
        intro g hg
        have h7 : (1 + ‖(τ : ℂ)‖) ≤ 2 + τ.im := by linarith
        calc ‖g τ‖ ≤ C' * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) := hg
          _ ≤ C' * (2 + τ.im) * Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 hC'0) (Real.exp_nonneg _)
          _ ≤ C' * (2 + τ.im) * Real.exp (-(2 * Real.pi * τ.im)) :=
              mul_le_mul_of_nonneg_left hmle (by positivity)
      refine le_trans (max_le ?_ ?_) (hlarge τ.im hy)
      · exact hstep (fun σ : UpperHalfPlane => F σ r)
          (hC' (fun σ : UpperHalfPlane => F σ r) (hF_md r) (hF_T2 r)
            (fun σ => hF0' σ r) (hlineF r) τ h1 h2 hy)
      · exact hstep (fun σ : UpperHalfPlane => Ft σ r)
          (hC' (fun σ : UpperHalfPlane => Ft σ r) (hFt_md r) (hFt_T2 r)
            (fun σ => hFt0' σ r) (hlineFt r) τ h1 h2 hy)
    · push_neg at hy
      exact max_le (le_trans (hsmallF τ r τ.im_pos (le_of_lt hy) h1 h2) (hsmall τ.im τ.im_pos (le_of_lt hy)))
        (le_trans (hsmallFt τ r τ.im_pos (le_of_lt hy) h1 h2) (hsmall τ.im τ.im_pos (le_of_lt hy)))
  -- ## Step 12. Evenness in `r`.
  have hFeven : ∀ τ : UpperHalfPlane, Function.Even (F τ) := by
    intro τ r
    have h1 : F τ (-r) = Work.Kernels.gaussTerm τ (-r) + Ψ (-r) τ := rfl
    have h2 : F τ r = Work.Kernels.gaussTerm τ r + Ψ r τ := rfl
    show F τ (-r) = F τ r
    rw [h1, h2, etp_gaussTerm_neg, congr_fun (hΨeven r) τ]
  have hFteven : ∀ τ : UpperHalfPlane, Function.Even (Ft τ) := by
    intro τ r
    have h1 : Ft τ (-r) = -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ (-r)) τ) := rfl
    have h2 : Ft τ r = -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) τ) := rfl
    show Ft τ (-r) = Ft τ r
    rw [h1, h2, hΨeven r]
  -- ## Step 13. The `d = 24` strip decay.
  have hdec : d = 24 →
      Work.FE.TendsToZeroInStrip 24 1
        (fun τ x => if h : 0 < τ.im then F ⟨τ, h⟩ ‖x‖ else 0) ∧
      Work.FE.TendsToZeroInStrip 24 1
        (fun τ x => if h : 0 < τ.im then Ft ⟨τ, h⟩ ‖x‖ else 0) := by
    intro hd24
    obtain ⟨α, β, hα, hβ, hstrip'⟩ := hstrip
    have hm2 : m = 2 := by rw [hmdef]; simp [hd24]
    have htail : ∀ (f : UpperHalfPlane → ℂ),
        MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f →
        (∀ τ : UpperHalfPlane, Work.Kernels.T2op f τ = 0) →
        (∀ τ : UpperHalfPlane, ‖f τ‖ ≤ max CF Ct * (Work.Kernels.scale τ) ^ max NF Nt) →
        (∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
          (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
          ‖f τ‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) ≤ ε) →
        ∀ τ : UpperHalfPlane, -1 ≤ τ.re → τ.re ≤ 1 → 2 ≤ τ.im →
          ‖f τ‖ ≤ C' * (1 + ‖(τ : ℂ)‖) * Real.exp (-(2 * Real.pi * 2 * τ.im)) := by
      intro f h1 h2 h3 h4 τ h5 h6 h7
      simpa [hm2] using hC' f h1 h2 h3 h4 τ h5 h6 h7
    set φ : ℝ → ℝ := fun y =>
      (α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi) + 2 * C' * (1 + y))
        * Real.exp (-(2 * Real.pi * y)) with hφdef
    have hφ0 : ∀ y : ℝ, 1 ≤ y → 0 ≤ φ y := by
      intro y hy1
      rw [hφdef]
      refine mul_nonneg ?_ (Real.exp_nonneg _)
      have h1 : (0:ℝ) ≤ α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi) :=
        mul_nonneg (mul_nonneg hα (le_trans zero_le_one (le_max_left _ _))) (Real.exp_nonneg _)
      have h2 : (0:ℝ) ≤ 2 * C' * (1 + y) := by nlinarith [hC'0, hy1]
      linarith
    have hφtend : Filter.Tendsto φ Filter.atTop (nhds 0) := by
      have hK : Filter.Tendsto (fun y : ℝ =>
          (α * Real.exp (12 * Real.pi) + 4 * C') * ((1 + y) * Real.exp (-(2 * Real.pi * y))))
          Filter.atTop (nhds 0) := by
        simpa using (etp_tendsto_one_add_exp (2 * Real.pi) (by positivity)).const_mul
          (α * Real.exp (12 * Real.pi) + 4 * C')
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy1
        exact hφ0 y hy1
      · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy1
        have hmax : max 1 (y ^ (-β)) ≤ 1 := by
          refine max_le le_rfl ?_
          rw [← Real.rpow_zero y]
          exact Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)
        have h1 : α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi) ≤ α * Real.exp (12 * Real.pi) := by
          calc α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi)
              ≤ α * 1 * Real.exp (12 * Real.pi) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hα)
                  (Real.exp_nonneg _)
            _ = α * Real.exp (12 * Real.pi) := by ring
        have h3 : (1:ℝ) ≤ 1 + y := by linarith
        have h2 : 2 * C' * (1 + y) ≤ 4 * C' * (1 + y) := by nlinarith [hC'0, h3]
        have h1' : α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi)
            ≤ α * Real.exp (12 * Real.pi) * (1 + y) := by
          calc α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi)
              ≤ α * 1 * Real.exp (12 * Real.pi) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hα)
                  (Real.exp_nonneg _)
            _ = α * Real.exp (12 * Real.pi) := by ring
            _ ≤ α * Real.exp (12 * Real.pi) * (1 + y) := by
                nth_rewrite 1 [← mul_one (α * Real.exp (12 * Real.pi))]
                exact mul_le_mul_of_nonneg_left h3 (by positivity)
        rw [hφdef]
        have hyy : (0:ℝ) ≤ y := by linarith
        have hgoal2 : α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi) + 2 * C' * (1 + y)
            ≤ (α * Real.exp (12 * Real.pi) + 4 * C') * (1 + y) := by
          nlinarith [h1', h2, mul_nonneg hC'0 hyy, Real.exp_nonneg (12 * Real.pi), hα]
        calc (α * max 1 (y ^ (-β)) * Real.exp (12 * Real.pi) + 2 * C' * (1 + y))
              * Real.exp (-(2 * Real.pi * y))
            ≤ ((α * Real.exp (12 * Real.pi) + 4 * C') * (1 + y))
              * Real.exp (-(2 * Real.pi * y)) :=
              mul_le_mul_of_nonneg_right hgoal2 (Real.exp_nonneg _)
          _ = (α * Real.exp (12 * Real.pi) + 4 * C')
              * ((1 + y) * Real.exp (-(2 * Real.pi * y))) := by ring
    have hnorm_le_all : ∀ τ : ℂ, -1 ≤ τ.re → τ.re ≤ 1 → 0 < τ.im → ‖τ‖ ≤ 1 + τ.im := by
      intro τ hre1 hre2 him
      have hsq : ‖τ‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have h3 : ‖τ‖ ^ 2 ≤ (1 + τ.im) ^ 2 := by
        rw [hsq]; nlinarith [him, hre1, hre2]
      have h4 : 0 ≤ ‖τ‖ := norm_nonneg _
      have h5 : 0 ≤ 1 + τ.im := by linarith [him]
      have h6 : |‖τ‖| ≤ |1 + τ.im| := sq_le_sq.mp h3
      rwa [abs_of_nonneg h4, abs_of_nonneg h5] at h6
    have hkey : ∀ (f : UpperHalfPlane → ℝ → ℂ),
        (∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
          (fun σ : UpperHalfPlane => f σ r)) →
        (∀ (r : ℝ) (τ : UpperHalfPlane), Work.Kernels.T2op (fun σ : UpperHalfPlane => f σ r) τ = 0) →
        (∀ (r : ℝ) (τ : UpperHalfPlane),
          ‖f τ r‖ ≤ max CF Ct * (Work.Kernels.scale τ) ^ max NF Nt) →
        (∀ r : ℝ, ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ τ : UpperHalfPlane,
          (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im →
          ‖f τ r‖ * Real.exp (2 * Real.pi * ((m : ℝ) - 1) * τ.im) ≤ ε) →
        (∀ (r : ℝ) (τ : UpperHalfPlane), 0 < τ.im → τ.im ≤ 2 → -1 ≤ τ.re → τ.re ≤ 1 →
          ‖f τ r‖ ≤ α * τ.im ^ (-β)) →
        Work.FE.TendsToZeroInStrip 24 1 (fun τ x => if h : 0 < τ.im then f ⟨τ, h⟩ ‖x‖ else 0) := by
      intro f hfmd hfT hfg hfl hsmallf x
      refine ⟨φ, hφtend, fun τ hτim hre1 hre2 => ?_⟩
      rw [show (fun τ x => if h : 0 < τ.im then f ⟨τ, h⟩ ‖x‖ else 0) τ x
          = f ⟨τ, hτim⟩ ‖x‖ by simp [hτim]]
      rw [show -(2 * Real.pi * 1 * τ.im) = -(2 * Real.pi * τ.im) by ring]
      have hy0 : (0:ℝ) ≤ τ.im := le_of_lt hτim
      have hnm : ‖τ‖ ≤ 1 + τ.im := hnorm_le_all τ hre1 hre2 hτim
      by_cases hbig : 2 ≤ τ.im
      · have hb := htail (fun σ : UpperHalfPlane => f σ ‖x‖) (hfmd ‖x‖) (hfT ‖x‖)
          (fun σ => hfg ‖x‖ σ) (hfl ‖x‖) ⟨τ, hτim⟩ hre1 hre2 hbig
        have hcoe : ((⟨τ, hτim⟩ : UpperHalfPlane) : ℂ) = τ := rfl
        have him : (⟨τ, hτim⟩ : UpperHalfPlane).im = τ.im := rfl
        rw [hcoe, him] at hb
        have hexp : Real.exp (-(2 * Real.pi * 2 * τ.im))
            = Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im)) := by
          rw [← Real.exp_add]; ring_nf
        rw [hexp] at hb
        calc ‖f ⟨τ, hτim⟩ ‖x‖‖
            ≤ C' * (1 + ‖τ‖) * (Real.exp (-(2 * Real.pi * τ.im))
                * Real.exp (-(2 * Real.pi * τ.im))) := hb
          _ ≤ C' * (2 + τ.im) * (Real.exp (-(2 * Real.pi * τ.im))
                * Real.exp (-(2 * Real.pi * τ.im))) := by
              have h7 : (1 + ‖τ‖) ≤ 2 + τ.im := by linarith
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h7 hC'0)
                (by positivity)
          _ ≤ (α * max 1 (τ.im ^ (-β)) * Real.exp (12 * Real.pi) + 2 * C' * (1 + τ.im))
                * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im))) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have h8 : C' * (2 + τ.im) ≤ 2 * C' * (1 + τ.im) := by nlinarith [hC'0, hy0]
              have h9 : (0:ℝ) ≤ α * max 1 (τ.im ^ (-β)) * Real.exp (12 * Real.pi) :=
                mul_nonneg (mul_nonneg hα (le_trans zero_le_one (le_max_left _ _)))
                  (Real.exp_nonneg _)
              linarith [h8, h9]
          _ = φ τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
              rw [hφdef]; ring
      · push_neg at hbig
        have hb := hsmallf ‖x‖ (⟨τ, hτim⟩ : UpperHalfPlane) hτim (le_of_lt hbig) hre1 hre2
        have him : (⟨τ, hτim⟩ : UpperHalfPlane).im = τ.im := rfl
        rw [him] at hb
        have hE : (1:ℝ) ≤ Real.exp (12 * Real.pi)
              * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im))) := by
          have h : Real.exp (12 * Real.pi)
              * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im)))
              = Real.exp (12 * Real.pi - 4 * Real.pi * τ.im) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
          rw [h, ← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          nlinarith [Real.pi_pos, le_of_lt hbig]
        have hfac : α * τ.im ^ (-β) ≤ α * max 1 (τ.im ^ (-β)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hα
        calc ‖f ⟨τ, hτim⟩ ‖x‖‖ ≤ α * τ.im ^ (-β) := hb
          _ ≤ (α * max 1 (τ.im ^ (-β)) * Real.exp (12 * Real.pi))
                * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im))) := by
              calc α * τ.im ^ (-β) ≤ α * max 1 (τ.im ^ (-β)) := hfac
                _ = (α * max 1 (τ.im ^ (-β))) * 1 := by ring
                _ ≤ (α * max 1 (τ.im ^ (-β))) * (Real.exp (12 * Real.pi)
                      * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im)))) :=
                    mul_le_mul_of_nonneg_left hE (by positivity)
                _ = (α * max 1 (τ.im ^ (-β)) * Real.exp (12 * Real.pi))
                      * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im))) := by ring
          _ ≤ (α * max 1 (τ.im ^ (-β)) * Real.exp (12 * Real.pi) + 2 * C' * (1 + τ.im))
                * (Real.exp (-(2 * Real.pi * τ.im)) * Real.exp (-(2 * Real.pi * τ.im))) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have h9 : (0:ℝ) ≤ 2 * C' * (1 + τ.im) := by
                have h10 : (0:ℝ) ≤ 1 + τ.im := by linarith
                have h11 : (0:ℝ) ≤ 2 * C' := by linarith
                positivity
              linarith
          _ = φ τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
              rw [hφdef]; ring
    exact ⟨hkey F hF_md hF_T2 (fun r τ => hF0' τ r) hlineF
        (fun r τ h1 h2 h3 h4 => le_trans (le_max_left _ _) (hstrip' ⟨τ, h1⟩ r h3 h4)),
      hkey Ft hFt_md hFt_T2 (fun r τ => hFt0' τ r) hlineFt
        (fun r τ h1 h2 h3 h4 => le_trans (le_max_right _ _) (hstrip' ⟨τ, h1⟩ r h3 h4))⟩
  -- ## Step 14. Assembly.
  refine ⟨F, Ft, ?_, hFsmooth, hFtsmooth, hFeven, hFteven, hdec⟩
  refine ⟨?_, ?_, hF3, hFt3, hstrip, ?_, ?_, hFE3⟩
  · intro r
    exact (Work.Asymptotics.mdifferentiable_gaussTerm r).add (hΨmd r)
  · intro r
    exact (Work.Asymptotics.mdifferentiable_slash (hΨmd r) ((d : ℤ) / 2) Work.Kernels.R_S).neg
  · intro τ r
    exact hF_T2 r τ
  · intro τ r
    exact hFt_T2 r τ

end Work.CKFinal
