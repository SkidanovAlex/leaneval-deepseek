/-
# The fibres of the modular lambda function are `Γ(2)`-orbits

The modular lambda function `λ = θ₁₀⁴/θ₀₀⁴ = Work.Kernels.lambdaFun` is a Hauptmodul for the
principal congruence subgroup `Γ(2)`: the map `λ` identifies `Γ(2)\ℍ` with `ℂ ∖ {0,1}`, so
two points of `ℍ` have the same `λ`-value exactly when they are `Γ(2)`-conjugate.

The proof is the classical "reduction to the fundamental domain" argument:

* `FDom = {τ | |Re τ| ≤ 1, ‖τ‖² ≥ |Re τ|}` is the standard fundamental domain of `Γ(2)`, and
  `λ` is real on its boundary, so a fibre point with non-real `λ`-value, after being moved into
  `FDom` by an element of `Γ(2)`, lies in the interior `FDomInt`;
* near the cusp every fibre point of a small value lies in the open cusp region
  `{|Re τ| < 1, Im τ > Y}`, where `λ` is injective, so for small values the fibre meets `FDomInt`
  in at most one point;
* this "at most one point" statement is open and closed as a function of the value (using that
  `λ` is a local biholomorphism and that the fibres do not escape to the cusps), hence holds for
  every non-real value; the lower half plane follows from `λ(τ/(τ+1)) = 1/λ(τ)`, and real
  values by a limiting argument.

The individual inputs are proved in the companion modules imported below.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaTargets
import Submission.Work.Rigidity.LambdaBasic
import Submission.Work.Rigidity.LambdaFiberDefs
import Submission.Work.Rigidity.lambda_fdom_reduction
import Submission.Work.Rigidity.lambda_local_inverse
import Submission.Work.Rigidity.lambdaFun_eq_lambdaSeries
import Submission.Work.Rigidity.isBoundedAtImInfty_lambdaFun
import Submission.Work.Rigidity.lambda_local_surjective
import Submission.Work.Rigidity.lambda_surjective
import Submission.Work.Rigidity.lambdaFun_div_qParam_tendsto
import Submission.Work.Rigidity.lambda_finite_smul
import Submission.Work.Rigidity.lambda_fiber_close
import Submission.Work.Rigidity.lambda_fiber_finite
import Submission.Work.Rigidity.lambda_fiber_small
import Submission.Work.Rigidity.fiberGood_open

namespace Work.Rigidity

open UpperHalfPlane ModularGroup Matrix Filter Topology
open scoped MatrixGroups

noncomputable section

open Work.Kernels Work.Kernels.LogLambda

/-! ## The inputs of the argument -/

/-- **`λ` is a local biholomorphism**: at every point there is a radius on which `λ` is
injective. -/
theorem lambda_local_injective (τ₀ : ℍ) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ : ℍ, dist (τ : ℂ) (τ₀ : ℂ) < r →
      ∀ τ' : ℍ, dist (τ' : ℂ) (τ₀ : ℂ) < r → lambdaFun τ = lambdaFun τ' → τ = τ' := by
  obtain ⟨c, hc⟩ := exists_rho_const
  have hc0 : c ≠ 0 := rho_const_ne_zero hc
  set z₀ : ℂ := (τ₀ : ℂ) with hz₀
  have hz₀pos : 0 < z₀.im := τ₀.im_pos
  have hderiv : deriv lamC z₀ ≠ 0 := by
    rw [deriv_lamC_eq_const hc z₀ hz₀pos]
    exact mul_ne_zero hc0 (rhoC_denom_ne_zero z₀ hz₀pos)
  have hAna : AnalyticAt ℂ lamC z₀ :=
    differentiableOn_lamC.analyticAt (isOpen_U.mem_nhds hz₀pos)
  set φ : ℂ → ℂ := HasStrictDerivAt.localInverse lamC (deriv lamC z₀) z₀
    hAna.hasStrictDerivAt hderiv with hφdef
  have hleft : ∀ᶠ z in 𝓝 z₀, φ (lamC z) = z :=
    hAna.hasStrictDerivAt.eventually_left_inverse hderiv
  obtain ⟨v, hv, hball⟩ := Filter.Eventually.exists_mem hleft
  obtain ⟨r, hr, hrv⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨r, hr, ?_⟩
  intro τ hτ τ' hτ' heq
  have hmem : ∀ σ : ℍ, dist (σ : ℂ) z₀ < r → φ (lamC (σ : ℂ)) = (σ : ℂ) :=
    fun σ hσ => hball _ (hrv (by simpa [hz₀] using hσ))
  have h1 : φ (lamC (τ : ℂ)) = (τ : ℂ) := hmem τ (by simpa [hz₀] using hτ)
  have h2 : φ (lamC (τ' : ℂ)) = (τ' : ℂ) := hmem τ' (by simpa [hz₀] using hτ')
  rw [lamC_coe τ] at h1
  rw [lamC_coe τ'] at h2
  have : (τ : ℂ) = (τ' : ℂ) := by rw [← h1, ← h2, heq]
  exact UpperHalfPlane.ext this

/-- **`λ` is small deep in the cusp**: uniformly on the fundamental domain. -/
theorem lambda_small_deep_cusp (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ τ : ℍ, τ ∈ FDom → R ≤ τ.im → ‖lambdaFun τ‖ ≤ ε := by
  have hb : ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty,
      dist (lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ)) 16 < 1 :=
    lambdaFun_div_qParam_tendsto.eventually (Metric.ball_mem_nhds 16 one_pos)
  have hb' : {τ : ℍ | dist (lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ)) 16 < 1}
      ∈ UpperHalfPlane.atImInfty := hb
  rw [UpperHalfPlane.atImInfty_mem] at hb'
  obtain ⟨R₁, hR₁⟩ := hb'
  have hq : ∀ σ : ℍ, ‖Function.Periodic.qParam 2 (σ : ℂ)‖
      = Real.exp (-(Real.pi * σ.im)) := by
    intro σ
    rw [qParam_two_eq, Complex.norm_exp]
    congr 1
    rw [show (Real.pi * Complex.I * (σ : ℂ)).re = -(Real.pi * σ.im) by
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
      ring]
  obtain ⟨R, hR⟩ : ∃ R : ℝ, 17 * Real.exp (-(Real.pi * R)) ≤ ε := by
    refine ⟨Real.log (17 / ε) / Real.pi, ?_⟩
    have h17 : 0 < 17 / ε := by positivity
    have hexp : Real.exp (-(Real.log (17 / ε))) = ε / 17 := by
      rw [Real.exp_neg, Real.exp_log h17, inv_div]
    rw [show -(Real.pi * (Real.log (17 / ε) / Real.pi)) = -(Real.log (17 / ε)) by
      field_simp]
    rw [hexp, mul_comm 17 (ε / 17), div_mul_cancel₀ ε (by norm_num)]
  refine ⟨max R₁ R, fun τ hτ hτR => ?_⟩
  have hRτ : R₁ ≤ τ.im := le_trans (le_max_left _ _) hτR
  have hd := hR₁ τ hRτ
  rw [Set.mem_setOf_eq, dist_eq_norm] at hd
  have hquot : ‖lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ)‖ ≤ 17 := by
    have h1 : ‖lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ)‖
        ≤ ‖lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ) - 16‖ + ‖(16 : ℂ)‖ := by
      have := norm_add_le (lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ) - 16) 16
      simpa using this
    have h2 : ‖(16 : ℂ)‖ = 16 := by simp
    rw [h2] at h1
    linarith [le_of_lt hd]
  have hqnz : Function.Periodic.qParam 2 (τ : ℂ) ≠ 0 := by
    rw [qParam_two_eq]
    exact Complex.exp_ne_zero _
  have hval : ‖lambdaFun τ‖
      = ‖lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ)‖
        * ‖Function.Periodic.qParam 2 (τ : ℂ)‖ := by
    rw [← norm_mul, div_mul_cancel₀ _ hqnz]
  have hτR' : R ≤ τ.im := le_trans (le_max_right _ _) hτR
  calc ‖lambdaFun τ‖
      = ‖lambdaFun τ / Function.Periodic.qParam 2 (τ : ℂ)‖
        * ‖Function.Periodic.qParam 2 (τ : ℂ)‖ := hval
    _ ≤ 17 * Real.exp (-(Real.pi * τ.im)) := by
        rw [hq τ]
        exact mul_le_mul_of_nonneg_right hquot (Real.exp_nonneg _)
    _ ≤ 17 * Real.exp (-(Real.pi * R)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_pos]
    _ ≤ ε := hR

/-! ## The Hauptmodul property -/

open Work.Rigidity (FiberGood)

lemma fiberGood_zero : FiberGood 0 :=
  fun τ _ h1 _ => absurd h1 (lambdaFun_ne_zero τ)

lemma fiberGood_one : FiberGood 1 :=
  fun τ _ h1 _ => absurd h1 (lambdaFun_ne_one τ)

/-- `FiberGood` is invariant under `w ↦ 1 - w`, the action of `S` (which normalises `Γ(2)`). -/
theorem fiberGood_one_sub {w : ℂ} (h : FiberGood (1 - w)) : FiberGood w := by
  intro τ τ' h1 h2
  have hS : ∀ σ : ℍ, lambdaFun (ModularGroup.S • σ) = 1 - lambdaFun σ := by
    intro σ
    have h3 : lambdaFun σ + lambdaSFun σ = 1 := lambdaFun_add_lambdaSFun σ
    have h4 : lambdaFun (ModularGroup.S • σ) = lambdaSFun σ :=
      Work.Kernels.LogLambda.lambdaFun_S σ
    rw [h4, eq_sub_iff_add_eq, add_comm]
    exact h3
  obtain ⟨γ, hγ, hγeq⟩ := h (ModularGroup.S • τ) (ModularGroup.S • τ')
    (by rw [hS, h1]) (by rw [hS, h2])
  refine ⟨ModularGroup.S⁻¹ * γ * ModularGroup.S, ?_, ?_⟩
  · simpa using (CongruenceSubgroup.Gamma_normal 2).conj_mem γ hγ ModularGroup.S⁻¹
  · have h2' : (ModularGroup.S⁻¹ * γ * ModularGroup.S) • τ
        = ModularGroup.S⁻¹ • (γ • (ModularGroup.S • τ)) := by rw [mul_smul, mul_smul]
    rw [h2', hγeq, ← mul_smul, inv_mul_cancel, one_smul]

/-- The base case: small values have a single orbit of preimages. -/
theorem fiberGood_small : ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, ‖w‖ < δ → FiberGood w := by
  obtain ⟨δ, hδ, h⟩ := lambda_fiber_small
  exact ⟨δ, hδ, fun w hw => h w hw⟩

/-- A sequence whose values lie eventually in a finite set has a value that occurs
frequently (infinitely often). -/
private lemma exists_frequently_eq_of_finite {α : Type*} {s : Set α} (hs : s.Finite)
    {u : ℕ → α} (hu : ∀ᶠ n in atTop, u n ∈ s) : ∃ a ∈ s, ∃ᶠ n in atTop, u n = a := by
  by_contra h
  have hfin : ∀ a ∈ s, {n : ℕ | u n = a}.Finite := by
    intro a ha
    refine Set.not_infinite.mp fun hinf => h ⟨a, ha, ?_⟩
    exact Nat.frequently_atTop_iff_infinite.mpr hinf
  have hunion : (⋃ a ∈ s, {n : ℕ | u n = a}).Finite := hs.biUnion hfin
  obtain ⟨M, hM⟩ := hunion.bddAbove
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  have hmem : max M N + 1 ∈ ⋃ a ∈ s, {n : ℕ | u n = a} :=
    Set.mem_iUnion₂.mpr ⟨u (max M N + 1), hN _ (by omega), rfl⟩
  have hle : max M N + 1 ≤ M := hM hmem
  omega

/-- **Closedness of the set of good values.**

Here `w` is in the closure of the set of good values, i.e. good values accumulate at `w`.

Proof sketch.  Given `τ, τ'` with `λ τ = λ τ' = w`, take good values `wₙ → w` with `wₙ ≠ w`
(possible by the closure hypothesis, unless `FiberGood w` already holds).  Let `φ`, `φ'` be the
local inverses of `λ` at `τ`, `τ'` (`LambdaLocalInverse`); then `φ wₙ → τ` and `φ' wₙ → τ'`
with `λ (φ wₙ) = λ (φ' wₙ) = wₙ`, so `γₙ • (φ wₙ) = φ' wₙ` for some `γₙ ∈ Γ(2)`.  All `γₙ` lie
in the finite set of group elements carrying a compact neighbourhood of `τ` into a compact
neighbourhood of `τ'` (`lambda_finite_smul`), so some `γ` occurs at arbitrarily large `n`;
passing to the limit in `γ • (φ wₙ) = φ' wₙ` gives `γ • τ = τ'`. -/
theorem fiberGood_closed {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (h : w ∈ closure {w' : ℂ | FiberGood w'}) : FiberGood w := by
  classical
  by_cases hgood : FiberGood w
  · exact hgood
  intro τ τ' hτ hτ'
  -- good values accumulating at `w`
  have hv : ∀ n : ℕ, ∃ b : ℂ, FiberGood b ∧ dist w b < 1 / ((n : ℝ) + 1) := fun n =>
    Metric.mem_closure_iff.mp h _ (by positivity)
  choose v hvgood hvclose using hv
  have hv_tend : Tendsto v atTop (𝓝 w) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [dist_comm]
    exact (hvclose n).le
  -- the local inverse branches of `λ` at `τ` and at `τ'`
  obtain ⟨φ, V, hV, hφdiff, hφ0, hφev⟩ := lambda_local_inverse τ
  obtain ⟨φ', V', hV', hφ'diff, hφ'0, hφ'ev⟩ := lambda_local_inverse τ'
  have hVw : V ∈ 𝓝 w := by simpa [hτ] using hV
  have hV'w : V' ∈ 𝓝 w := by simpa [hτ'] using hV'
  have hφ0w : φ w = (τ : ℂ) := by simpa [hτ] using hφ0
  have hφ'0w : φ' w = (τ' : ℂ) := by simpa [hτ'] using hφ'0
  have hφevw : ∀ᶠ z in 𝓝 w, 0 < (φ z).im ∧
      ∀ hw : 0 < (φ z).im, lambdaFun ⟨φ z, hw⟩ = z := by simpa [hτ] using hφev
  have hφ'evw : ∀ᶠ z in 𝓝 w, 0 < (φ' z).im ∧
      ∀ hw : 0 < (φ' z).im, lambdaFun ⟨φ' z, hw⟩ = z := by simpa [hτ'] using hφ'ev
  have hφcont : ContinuousAt φ w := (hφdiff.differentiableAt hVw).continuousAt
  have hφ'cont : ContinuousAt φ' w := (hφ'diff.differentiableAt hV'w).continuousAt
  -- the two local inverse branches along the sequence
  have hvφ : ∀ᶠ n in atTop, 0 < (φ (v n)).im ∧
      ∀ hw : 0 < (φ (v n)).im, lambdaFun ⟨φ (v n), hw⟩ = v n :=
    hv_tend.eventually hφevw
  have hvφ' : ∀ᶠ n in atTop, 0 < (φ' (v n)).im ∧
      ∀ hw : 0 < (φ' (v n)).im, lambdaFun ⟨φ' (v n), hw⟩ = v n :=
    hv_tend.eventually hφ'evw
  obtain ⟨N, hN⟩ := eventually_atTop.mp hvφ
  obtain ⟨N', hN'⟩ := eventually_atTop.mp hvφ'
  set M : ℕ := max N N' with hMdef
  have hNM : N ≤ M := le_max_left _ _
  have hN'M : N' ≤ M := le_max_right _ _
  have hNkM : ∀ k : ℕ, N ≤ k + M := fun k => by omega
  have hN'kM : ∀ k : ℕ, N' ≤ k + M := fun k => by omega
  -- the two branches, reindexed so that they are defined for every `k`
  have hz_exists : ∀ k : ℕ, ∃ h : 0 < (φ (v (k + M))).im,
      lambdaFun ⟨φ (v (k + M)), h⟩ = v (k + M) := fun k =>
    ⟨(hN (k + M) (hNkM k)).1, (hN (k + M) (hNkM k)).2 (hN (k + M) (hNkM k)).1⟩
  have hz'_exists : ∀ k : ℕ, ∃ h : 0 < (φ' (v (k + M))).im,
      lambdaFun ⟨φ' (v (k + M)), h⟩ = v (k + M) := fun k =>
    ⟨(hN' (k + M) (hN'kM k)).1, (hN' (k + M) (hN'kM k)).2 (hN' (k + M) (hN'kM k)).1⟩
  let z : ℕ → ℍ := fun k => ⟨φ (v (k + M)), (hz_exists k).choose⟩
  let z' : ℕ → ℍ := fun k => ⟨φ' (v (k + M)), (hz'_exists k).choose⟩
  have hzv : ∀ k, lambdaFun (z k) = v (k + M) := fun k => (hz_exists k).choose_spec
  have hzv' : ∀ k, lambdaFun (z' k) = v (k + M) := fun k => (hz'_exists k).choose_spec
  have hz_tend : Tendsto z atTop (𝓝 τ) := by
    rw [UpperHalfPlane.isEmbedding_coe.isInducing.tendsto_nhds_iff]
    have h1 : Tendsto (fun k : ℕ => φ (v (k + M))) atTop (𝓝 (φ w)) :=
      hφcont.tendsto.comp (hv_tend.comp (tendsto_add_atTop_nat M))
    have h2 : Tendsto (fun k : ℕ => φ (v (k + M))) atTop (𝓝 (τ : ℂ)) := by
      rwa [hφ0w] at h1
    simpa [z, Function.comp_def] using h2
  have hz'_tend : Tendsto z' atTop (𝓝 τ') := by
    rw [UpperHalfPlane.isEmbedding_coe.isInducing.tendsto_nhds_iff]
    have h1 : Tendsto (fun k : ℕ => φ' (v (k + M))) atTop (𝓝 (φ' w)) :=
      hφ'cont.tendsto.comp (hv_tend.comp (tendsto_add_atTop_nat M))
    have h2 : Tendsto (fun k : ℕ => φ' (v (k + M))) atTop (𝓝 (τ' : ℂ)) := by
      rwa [hφ'0w] at h1
    simpa [z', Function.comp_def] using h2
  -- the conjugating elements
  have hγ : ∀ k, ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma 2 ∧ γ • z k = z' k :=
    fun k => hvgood (k + M) (z k) (z' k) (hzv k) (hzv' k)
  choose γseq hγseq using hγ
  -- only finitely many of them can occur
  have hK : IsCompact (Metric.closedBall τ 1) := isCompact_closedBall τ 1
  have hK' : IsCompact (Metric.closedBall τ' 1) := isCompact_closedBall τ' 1
  have hEfin : {γ : SL(2, ℤ) | γ ∈ CongruenceSubgroup.Gamma 2 ∧
      ∃ z ∈ Metric.closedBall τ 1, γ • z ∈ Metric.closedBall τ' 1}.Finite :=
    lambda_finite_smul _ _ hK hK'
  have hγE : ∀ᶠ k in atTop, γseq k ∈ {γ : SL(2, ℤ) | γ ∈ CongruenceSubgroup.Gamma 2 ∧
      ∃ z ∈ Metric.closedBall τ 1, γ • z ∈ Metric.closedBall τ' 1} := by
    filter_upwards [hz_tend.eventually (Metric.closedBall_mem_nhds τ one_pos),
      hz'_tend.eventually (Metric.closedBall_mem_nhds τ' one_pos)] with k hk hk'
    exact ⟨(hγseq k).1, z k, hk, by rw [(hγseq k).2]; exact hk'⟩
  obtain ⟨γ, hγE, hγfreq⟩ := exists_frequently_eq_of_finite hEfin hγE
  -- pass to the limit along the indices where `γseq` is constantly `γ`
  haveI : NeBot (atTop ⊓ 𝓟 {k : ℕ | γseq k = γ}) := Filter.frequently_iff_neBot.mp hγfreq
  have hcontγ : Continuous fun z : ℍ => γ • z := by
    simpa only [sl_moeb] using continuous_const_smul (γ : GL (Fin 2) ℝ)
  have hf : Tendsto (fun k => γ • z k) (atTop ⊓ 𝓟 {k : ℕ | γseq k = γ}) (𝓝 (γ • τ)) :=
    ((hcontγ.tendsto τ).comp hz_tend).mono_left inf_le_left
  have hg : Tendsto z' (atTop ⊓ 𝓟 {k : ℕ | γseq k = γ}) (𝓝 τ') :=
    hz'_tend.mono_left inf_le_left
  have hEq : (fun k => γ • z k) =ᶠ[atTop ⊓ 𝓟 {k : ℕ | γseq k = γ}] z' := by
    have hs : {k : ℕ | γseq k = γ} ∈ (atTop ⊓ 𝓟 {k : ℕ | γseq k = γ}) :=
      Filter.mem_inf_of_right (Filter.mem_principal_self _)
    filter_upwards [hs] with k hk
    rw [← hk]
    exact (hγseq k).2
  exact ⟨γ, hγE.1, tendsto_nhds_unique_of_eventuallyEq hf hg hEq⟩

/-- `{w | FiberGood w}` is clopen.  Openness uses `fiberGood_open` away from `{0,1}`,
`fiberGood_small` at `0` and `fiberGood_one_sub` at `1`; closedness uses `fiberGood_closed`
away from `{0,1}` and the vacuous cases `FiberGood 0`, `FiberGood 1` at the two exceptional
values. -/
theorem fiberGood_clopen : IsClopen {w : ℂ | FiberGood w} := by
  refine ⟨?_, ?_⟩
  · -- closedness: the closure form of the good-value condition
    rw [← closure_subset_iff_isClosed]
    intro w hw
    by_cases h0 : w = 0
    · rw [h0]
      exact fiberGood_zero
    by_cases h1 : w = 1
    · rw [h1]
      exact fiberGood_one
    · exact fiberGood_closed h0 h1 hw
  · -- openness: `fiberGood_open` away from `0, 1`, the small-value base case at `0`,
    -- and the symmetry `w ↦ 1 - w` at `1`
    rw [isOpen_iff_mem_nhds]
    intro w hw
    rcases eq_or_ne w 0 with rfl | hw0
    · obtain ⟨δ, hδpos, hgood⟩ := fiberGood_small
      refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hδpos) ?_
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
      exact hgood z hz
    rcases eq_or_ne w 1 with rfl | hw1
    · obtain ⟨δ, hδpos, hgood⟩ := fiberGood_small
      refine Filter.mem_of_superset (Metric.ball_mem_nhds (1 : ℂ) hδpos) ?_
      intro z hz
      rw [Metric.mem_ball, dist_comm, dist_eq_norm] at hz
      exact fiberGood_one_sub (hgood (1 - z) hz)
    · obtain ⟨ε, hεpos, hgood⟩ := fiberGood_open w hw0 hw1 hw
      refine Filter.mem_of_superset (Metric.ball_mem_nhds w hεpos) ?_
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact hgood z hz

/-- **Every fibre of `λ` is a single `Γ(2)`-orbit.** -/
theorem fiberGood_all (w : ℂ) : FiberGood w := by
  have huniv : {w : ℂ | FiberGood w} = Set.univ := by
    rcases isClopen_iff.mp fiberGood_clopen with h0 | h1
    · exfalso
      have h : (0 : ℂ) ∈ ({w : ℂ | FiberGood w} : Set ℂ) := fiberGood_zero
      rw [h0] at h
      exact h
    · exact h1
  exact (show w ∈ {w : ℂ | FiberGood w} from by rw [huniv]; trivial)

theorem lambda_fiber_orbit : Work.Rigidity.LambdaFiberOrbits := by
  intro τ₁ τ₂ h
  exact fiberGood_all (lambdaFun τ₁) τ₁ τ₂ rfl h.symm

end

end Work.Rigidity
