import Mathlib
import Submission.Work.RPB.B3.EvenTaylorSteps

namespace Work.RPB.B3

open scoped ContDiff Topology

open Filter

set_option autoImplicit false

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## Partial derivatives and `ContDiff` -/

/-- Composing a `C^k` map into `X →L[ℝ] E` with `fst` stays `C^k`. -/
lemma contDiff_clm_comp_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {h : X × ℝ → (X →L[ℝ] E)} (hh : ContDiff ℝ k h) :
    ContDiff ℝ k fun z => (h z).comp (ContinuousLinearMap.fst ℝ X ℝ) := by
  have h2 : ContDiff ℝ k fun z : X × ℝ =>
      ((ContinuousLinearMap.precomp E (ContinuousLinearMap.fst ℝ X ℝ) :
        ((X →L[ℝ] E) →L[ℝ] ((X × ℝ) →L[ℝ] E)))) (h z) :=
    ((ContinuousLinearMap.precomp E (ContinuousLinearMap.fst ℝ X ℝ) :
        ((X →L[ℝ] E) →L[ℝ] ((X × ℝ) →L[ℝ] E)))).contDiff.comp hh
  simpa only [ContinuousLinearMap.precomp_apply] using h2

/-- Right multiplication by `snd` of a continuous linear map stays `C^k`. -/
lemma contDiff_smulRight_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    {h : X × ℝ → E} (hh : ContDiff ℝ k h) :
    ContDiff ℝ k fun z => (ContinuousLinearMap.snd ℝ X ℝ).smulRight (h z) :=
  ((ContinuousLinearMap.smulRightL ℝ (X × ℝ) E) (ContinuousLinearMap.snd ℝ X ℝ)).contDiff.comp hh

/-! ## The chain rule for `z ↦ R (z.1, √z.2)` and continuous linear map identities -/

lemma hasFDerivAt_sqrt_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : X × ℝ → E} (hRd : Differentiable ℝ R) {x : X} {ρ : ℝ} (hρ : 0 < ρ) :
    HasFDerivAt (fun z : X × ℝ => R (z.1, Real.sqrt z.2))
      ((fderiv ℝ R (x, Real.sqrt ρ)).comp
        ((ContinuousLinearMap.fst ℝ X ℝ).prod
          ((1 / (2 * Real.sqrt ρ)) • (ContinuousLinearMap.snd ℝ X ℝ)))) (x, ρ) := by
  have hsq : HasFDerivAt (fun y : ℝ => Real.sqrt y)
      ((1 / (2 * Real.sqrt ρ)) • ContinuousLinearMap.id ℝ ℝ) ρ := by
    have h0 := (Real.hasDerivAt_sqrt (ne_of_gt hρ)).hasFDerivAt
    convert h0 using 1
    ext y
    simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
  have hu : HasFDerivAt (fun z : X × ℝ => (z.1, Real.sqrt z.2))
      ((ContinuousLinearMap.fst ℝ X ℝ).prod
        ((1 / (2 * Real.sqrt ρ)) • (ContinuousLinearMap.snd ℝ X ℝ))) (x, ρ) := by
    refine HasFDerivAt.prodMk hasFDerivAt_fst ?_
    have h2 : HasFDerivAt ((fun y : ℝ => Real.sqrt y) ∘ fun z : X × ℝ => z.2)
        ((1 / (2 * Real.sqrt ρ)) • (ContinuousLinearMap.snd ℝ X ℝ)) (x, ρ) :=
      HasFDerivAt.comp (x, ρ) hsq
        (hasFDerivAt_snd : HasFDerivAt (fun z : X × ℝ => z.2)
          (ContinuousLinearMap.snd ℝ X ℝ) (x, ρ))
    show HasFDerivAt (fun z : X × ℝ => Real.sqrt z.2)
        ((1 / (2 * Real.sqrt ρ)) • (ContinuousLinearMap.snd ℝ X ℝ)) (x, ρ)
    exact h2
  have hdz : DifferentiableAt ℝ R (x, Real.sqrt ρ) := hRd.differentiableAt
  exact (hdz.hasFDerivAt).comp (x, ρ) hu

lemma smul_smulRight' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (L : (X × ℝ) →L[ℝ] ℝ) (y : E) :
    (c • L).smulRight y = L.smulRight (c • y) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply]
  rw [smul_eq_mul, mul_smul, smul_comm]

lemma clm_comp_fst_prod_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (X × ℝ) →L[ℝ] E) :
    L.comp ((ContinuousLinearMap.fst ℝ X ℝ).prod 0)
      = (L.comp (ContinuousLinearMap.inl ℝ X ℝ)).comp (ContinuousLinearMap.fst ℝ X ℝ) := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.inl_apply, zero_apply]

lemma pow_mul_inv_sqrt {ρ : ℝ} (hρ : 0 < ρ) {M : ℕ} (hM : 1 ≤ M) :
    ρ ^ M * (1 / (2 * Real.sqrt ρ)) = ρ ^ (M - 1) * (Real.sqrt ρ / 2) := by
  have hne : Real.sqrt ρ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hρ)
  have hsq : Real.sqrt ρ * Real.sqrt ρ = ρ := by simpa [sq] using Real.sq_sqrt hρ.le
  have hpow : ρ ^ M = ρ ^ (M - 1) * ρ := by
    rw [← pow_succ]
    congr 1
    omega
  have h1 : ρ * (1 / (2 * Real.sqrt ρ)) = Real.sqrt ρ / 2 := by
    field_simp
    nlinarith [hsq]
  rw [hpow, mul_assoc, h1]

/-- **The analytic core.**  If `R : X × ℝ → E` is `C^k` and `k ≤ M`, then
`z ↦ z.2 ^ M • R (z.1, √z.2)` (where `√· = 0` on the negative half-line) is `C^k`. -/
theorem contDiff_pow_smul_sqrt (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ∀ (k M : ℕ), k ≤ M → ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [CompleteSpace E] (R : X × ℝ → E), ContDiff ℝ k R →
      ContDiff ℝ k (fun z : X × ℝ => z.2 ^ M • R (z.1, Real.sqrt z.2)) := by
  intro k
  induction k with
  | zero =>
      intro M _ E _ _ _ R hR
      exact contDiff_zero.mpr ((continuous_snd.pow M).smul
        (hR.continuous.comp (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd))))
  | succ k ih =>
      intro M hM E _ _ _ R hR
      have hMk : k ≤ M := by omega
      have hMk1 : k ≤ M - 1 := by omega
      have hM1 : 1 ≤ M := by omega
      have hRdiff : Differentiable ℝ R := hR.differentiable (by simp)
      -- auxiliary functions
      set S : X × ℝ → E := fun z => (M : ℝ) • R z + (z.2 / 2) • (fderiv ℝ R z (0, 1)) with hS
      set Gv : X × ℝ → (X →L[ℝ] E) :=
        fun z => (fderiv ℝ R z).comp (ContinuousLinearMap.inl ℝ X ℝ) with hGv
      have hSR : ContDiff ℝ k R := hR.of_le (by exact_mod_cast Nat.le_succ k)
      have hSc : ContDiff ℝ k S := by
        rw [hS]
        refine ContDiff.add (hSR.const_smul (M : ℝ)) ?_
        refine ContDiff.smul (contDiff_snd.div_const 2) ?_
        exact (hR.fderiv_right (m := k) le_rfl).clm_apply contDiff_const
      have hGvc : ContDiff ℝ k Gv := by
        rw [hGv]
        have h2 : ContDiff ℝ k fun z : X × ℝ =>
            ((ContinuousLinearMap.precomp E (ContinuousLinearMap.inl ℝ X ℝ) :
              ((X × ℝ) →L[ℝ] E) →L[ℝ] (X →L[ℝ] E))) (fderiv ℝ R z) :=
          ((ContinuousLinearMap.precomp E (ContinuousLinearMap.inl ℝ X ℝ) :
            ((X × ℝ) →L[ℝ] E) →L[ℝ] (X →L[ℝ] E))).contDiff.comp
            (hR.fderiv_right (m := k) le_rfl)
        simpa only [ContinuousLinearMap.precomp_apply] using h2
      have h2 := ih (M - 1) hMk1 S hSc
      have h1 := ih M hMk Gv hGvc
      -- candidate derivative
      set T : X × ℝ → (X × ℝ) →L[ℝ] E := fun z =>
        (ContinuousLinearMap.snd ℝ X ℝ).smulRight (z.2 ^ (M - 1) • S (z.1, Real.sqrt z.2))
        + z.2 ^ M • ((Gv (z.1, Real.sqrt z.2)).comp (ContinuousLinearMap.fst ℝ X ℝ)) with hT
      have hTc : ContDiff ℝ k T := by
        rw [hT]
        refine ContDiff.add (contDiff_smulRight_snd h2) ?_
        have h3 : ContDiff ℝ k fun z : X × ℝ =>
            (z.2 ^ M • Gv (z.1, Real.sqrt z.2)).comp (ContinuousLinearMap.fst ℝ X ℝ) :=
          contDiff_clm_comp_fst h1
        simpa only [ContinuousLinearMap.smul_comp] using h3
      rw [show (((k + 1 : ℕ)) : WithTop ℕ∞) = ((k : WithTop ℕ∞) + 1) from by norm_num]
      refine contDiff_succ_iff_hasFDerivAt.mpr ⟨T, hTc, fun z => ?_⟩
      obtain ⟨x, ρ⟩ := z
      -- derivative of the scalar factor, valid at every point
      have hp : HasFDerivAt (fun z : X × ℝ => z.2 ^ M)
          (((M : ℝ) * ρ ^ (M - 1)) • (ContinuousLinearMap.snd ℝ X ℝ)) (x, ρ) := by
        have h0 : HasFDerivAt (fun y : ℝ => y ^ M)
            (((M : ℝ) * ρ ^ (M - 1)) • ContinuousLinearMap.id ℝ ℝ) ρ := by
          have h1 := (hasDerivAt_pow M ρ).hasFDerivAt
          convert h1 using 1
          ext y
          simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]
        have h3 : HasFDerivAt ((fun y : ℝ => y ^ M) ∘ fun z : X × ℝ => z.2)
            (((M : ℝ) * ρ ^ (M - 1)) • (ContinuousLinearMap.snd ℝ X ℝ)) (x, ρ) :=
          HasFDerivAt.comp (x, ρ) h0
            (hasFDerivAt_snd : HasFDerivAt (fun z : X × ℝ => z.2)
              (ContinuousLinearMap.snd ℝ X ℝ) (x, ρ))
        show HasFDerivAt (fun z : X × ℝ => z.2 ^ M)
            (((M : ℝ) * ρ ^ (M - 1)) • (ContinuousLinearMap.snd ℝ X ℝ)) (x, ρ)
        exact h3
      rcases lt_trichotomy ρ 0 with hneg | hzero | hpos
      · -- ρ < 0 : locally `√ρ' = 0`
        have hsq0 : Real.sqrt ρ = 0 := Real.sqrt_eq_zero_of_nonpos hneg.le
        have hmem : {z : X × ℝ | z.2 < 0} ∈ 𝓝 (x, ρ) :=
          (isOpen_lt continuous_snd continuous_const).mem_nhds hneg
        have heq : (fun z : X × ℝ => z.2 ^ M • R (z.1, Real.sqrt z.2)) =ᶠ[𝓝 (x, ρ)]
            (fun z : X × ℝ => z.2 ^ M • R (z.1, 0)) := by
          filter_upwards [hmem] with z hz
          rw [Real.sqrt_eq_zero_of_nonpos hz.le]
        refine HasFDerivAt.congr_of_eventuallyEq ?_ heq
        have hR0 : HasFDerivAt (fun z : X × ℝ => R (z.1, 0))
            ((fderiv ℝ R (x, 0)).comp ((ContinuousLinearMap.fst ℝ X ℝ).prod 0)) (x, ρ) := by
          have hin : HasFDerivAt (fun z : X × ℝ => ((z.1, (0 : ℝ)) : X × ℝ))
              ((ContinuousLinearMap.fst ℝ X ℝ).prod 0) (x, ρ) :=
            HasFDerivAt.prodMk hasFDerivAt_fst (hasFDerivAt_const (x := (x, ρ)) (0 : ℝ))
          have hd : DifferentiableAt ℝ R (x, 0) := hRdiff.differentiableAt
          exact (hd.hasFDerivAt).comp (x, ρ) hin
        refine (hp.smul hR0).congr_fderiv ?_
        simp only [hT, hsq0, hS, hGv, Real.sqrt_zero, zero_div, zero_smul, add_zero,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.prod_apply, ContinuousLinearMap.inl_apply, zero_apply]
        rw [clm_comp_fst_prod_zero (fderiv ℝ R (x, 0)), smul_smulRight']
        simp only [smul_smul, mul_comm]
        abel
      · -- ρ = 0
        subst hzero
        have hT0 : ∀ v : X × ℝ, T (x, 0) v = v.2 • ((0 : ℝ) ^ (M - 1) • S (x, 0)) := by
          intro v
          simp only [hT, zero_pow (by omega : M ≠ 0), zero_smul, add_zero, Real.sqrt_zero,
            ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
            ContinuousLinearMap.coe_snd']
        have hSR0 : (0 : ℝ) ^ (M - 1) • S (x, 0) = (0 : ℝ) ^ (M - 1) • R (x, 0) := by
          rcases eq_or_lt_of_le hM1 with h1 | h1
          · subst h1
            rw [hS]
            simp
          · have hne : M - 1 ≠ 0 := by omega
            rw [zero_pow hne, zero_smul, zero_smul]
        have hkey : ∀ z' : X × ℝ,
            (z'.2 ^ M • R (z'.1, Real.sqrt z'.2)) - ((0 : ℝ) ^ M • R (x, Real.sqrt 0))
              - T (x, 0) (z' - (x, 0))
            = z'.2 • ((z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2))
                - ((0 : ℝ) ^ (M - 1) • R (x, 0))) := by
          intro z'
          have hpow : z'.2 ^ M = z'.2 * z'.2 ^ (M - 1) := by
            rw [mul_comm z'.2 (z'.2 ^ (M - 1)), ← pow_succ]
            congr 1
            omega
          have hcomp : (z' - (x, 0)).2 = z'.2 := by simp
          rw [hT0 (z' - (x, 0)), hcomp, hSR0, zero_pow (by omega : M ≠ 0), zero_smul, sub_zero,
            hpow, smul_sub, mul_smul]
        refine (hasFDerivAt_iff_isLittleO).mpr ?_
        rw [Asymptotics.isLittleO_iff]
        intro c hc
        have hcont : Continuous (fun z' : X × ℝ => z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2)) :=
          (continuous_snd.pow (M - 1)).smul
            (hRdiff.continuous.comp (continuous_fst.prodMk (Real.continuous_sqrt.comp continuous_snd)))
        have hlim : Tendsto (fun z' : X × ℝ => z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2)
            - ((0 : ℝ) ^ (M - 1) • R (x, 0))) (𝓝 (x, 0)) (𝓝 0) := by
          have h0 : Tendsto (fun z' : X × ℝ => z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2))
              (𝓝 (x, 0)) (𝓝 ((0 : ℝ) ^ (M - 1) • R (x, 0))) := by
            rw [show ((0 : ℝ) ^ (M - 1) • R (x, 0))
                = (fun z' : X × ℝ => z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2)) (x, (0 : ℝ)) by
              simp [Real.sqrt_zero]]
            exact hcont.continuousAt
          have hsub := h0.sub_const ((0 : ℝ) ^ (M - 1) • R (x, 0))
          simpa using hsub
        have hev : ∀ᶠ z' in 𝓝 ((x, (0 : ℝ)) : X × ℝ),
            ‖z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2) - ((0 : ℝ) ^ (M - 1) • R (x, 0))‖ < c := by
          have hb := hlim.eventually (Metric.ball_mem_nhds (0 : E) hc)
          filter_upwards [hb] with z' hz'
          simpa [Metric.mem_ball, dist_eq_norm] using hz'
        filter_upwards [hev] with z' hz'
        rw [hkey z']
        have hnorm : |z'.2| ≤ ‖z' - ((x, (0 : ℝ)) : X × ℝ)‖ := by
          have h1 := norm_snd_le (z' - ((x, (0 : ℝ)) : X × ℝ))
          simpa [Real.norm_eq_abs] using h1
        calc ‖z'.2 • (z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2)
              - ((0 : ℝ) ^ (M - 1) • R (x, 0)))‖
            = |z'.2| * ‖z'.2 ^ (M - 1) • R (z'.1, Real.sqrt z'.2)
                - ((0 : ℝ) ^ (M - 1) • R (x, 0))‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖z' - ((x, (0 : ℝ)) : X × ℝ)‖ * c :=
              mul_le_mul hnorm hz'.le (norm_nonneg _) (norm_nonneg _)
          _ = c * ‖z' - ((x, (0 : ℝ)) : X × ℝ)‖ := by ring
      · -- ρ > 0
        have hD : HasFDerivAt (fun z : X × ℝ => R (z.1, Real.sqrt z.2))
            ((fderiv ℝ R (x, Real.sqrt ρ)).comp
              ((ContinuousLinearMap.fst ℝ X ℝ).prod
                ((1 / (2 * Real.sqrt ρ)) • (ContinuousLinearMap.snd ℝ X ℝ)))) (x, ρ) :=
          hasFDerivAt_sqrt_comp hRdiff hpos
        refine (hp.smul hD).congr_fderiv ?_
        rw [hT, hS, hGv]
        refine ContinuousLinearMap.ext fun v => ?_
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
          add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_apply,
          ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.inl_apply, smul_eq_mul]
        rw [show (fderiv ℝ R (x, Real.sqrt ρ)) (v.1, (1 / (2 * Real.sqrt ρ)) * v.2)
            = (fderiv ℝ R (x, Real.sqrt ρ)) (v.1, 0)
              + ((1 / (2 * Real.sqrt ρ)) * v.2) • (fderiv ℝ R (x, Real.sqrt ρ) (0, 1)) by
          rw [show ((v.1, (1 / (2 * Real.sqrt ρ)) * v.2) : X × ℝ)
              = ((v.1, 0) : X × ℝ) + ((1 / (2 * Real.sqrt ρ)) * v.2) • ((0 : X), (1 : ℝ)) by
            simp]
          rw [map_add, map_smul]]
        simp only [smul_add, smul_smul]
        rw [← mul_assoc, pow_mul_inv_sqrt hpos hM1]
        module

end

/-! Even `C^∞` functions of `r` are `C^k` functions of `ρ = r²`, and the extension preserves
`2π`-periodicity in the middle variable.  Proof recipe: Hadamard/Taylor splitting
`f τ t r = Σ_{j<k} c_j(τ,t) r^{2j} + r^{2k} ψ(τ,t,r)` with `c_j` smooth and `ψ` smooth even in `r`
(iterate `f τ t r = f τ t 0 + r * ∫_0^1 ∂_r f τ t (s*r) ds`, using that the remainder is even),
then set `g τ t ρ := Σ_{j<k} c_j(τ,t) ρ^j + ρ^k * ψ(τ,t, √|ρ|)`, which is `C^k` and `2π`-periodic
in `t`.  `[CompleteSpace E]` is assumed so that the Bochner integrals in the splitting exist. -/
end Work.RPB.B3
