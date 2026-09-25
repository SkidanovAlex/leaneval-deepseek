import Mathlib
import Submission.Work.NN.Core.Lev2.PowCacc
import Submission.Work.NN.Core.Lev.moserSourceAux
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.Lev.moserSourceReduction

/-!
# Shifted Caccioppoli estimate at every power level (`srcWShiftCacc`)

With `W := srcW u Λ = fun z => max ‖u z‖ Λ` the *shifted modulus* of `u`, and assuming the
power Caccioppoli hypothesis with source, `Work.NN.Core.Lev2.HasPowCaccSource ρ A₀ Λ u`, we prove
that there is a constant `C > 0` (namely `16 n A₀`) such that for every level `k ≥ 1` and every
smooth nonnegative test function `φ` with `tsupport φ ⊆ polydisc 0 ρ`,

`∫ φ² ‖D(W^k)‖² ≤ C (k²Λ² ∫ φ² W^{2k-2} + ∫ ‖Dφ‖² W^{2k})`.

The proof is pointwise: on `{‖u‖ ≤ Λ}` the function `W^k` has a local minimum (so
`fderiv (W^k) = 0`), while on `{Λ < ‖u‖}` one has `W^k = ‖u‖^k` near the point and the chain rule
plus `‖fderiv ‖u‖‖ ≤ ‖fderiv u‖` gives `‖D(W^k)‖ ≤ k ‖u‖^{k-1} ‖Du‖`; combined with
`nnGradBoundPoint` (`‖Du‖² ≤ 8n Σ_j (‖∂_j u‖² + ‖∂̄_j u‖²)`) this reduces the claim to the level-`k`
instance of `HasPowCaccSource`.  The remaining integrals are compared using `W ≥ ‖u‖` and
`W ≥ Λ` term by term.

Auxiliary lemmas proved here: `nnNormPow_fderiv_le`, `nnNorm_fderiv_le`, `nnSrcWPow_fderiv_le`
and `hasPowCaccSource_natpow`.
-/

set_option maxHeartbeats 1000000

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology NNReal

namespace Work.NN.Core.Lev

/-- Pointwise bound of the derivative of `y ↦ ‖f y‖^k`, for `k ≥ 2`, at a point of
differentiability of `f`. -/
theorem nnNormPow_fderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : F → E} {x : F}
    (hf : DifferentiableAt ℝ f x) {k : ℕ} (hk : 2 ≤ k) :
    ‖fderiv ℝ (fun y => ‖f y‖ ^ k) x‖ ≤ (k:ℝ) * ‖f x‖ ^ (k - 1) * ‖fderiv ℝ f x‖ := by
  have hk1 : (1:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 1 < k)
  have hkeq : ((k:ℝ) - 1) = ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]; norm_num
  have hfun : (fun y : F => ‖f y‖ ^ k) = (fun y : F => ‖f y‖ ^ (k:ℝ)) := by
    funext y
    exact (Real.rpow_natCast (‖f y‖) k).symm
  rw [hfun]
  have hfd : fderiv ℝ (fun y : F => ‖f y‖ ^ (k:ℝ)) x
      = ((k:ℝ) * ‖f x‖ ^ ((k:ℝ) - 2)) • innerSL ℝ (f x) ∘SL fderiv ℝ f x := by
    have h := (hasFDerivAt_norm_rpow (f x) hk1).comp x hf.hasFDerivAt
    have h2 : (fun y : F => ‖f y‖ ^ (k:ℝ)) = (fun y : E => ‖y‖ ^ (k:ℝ)) ∘ f := rfl
    rw [h2]
    exact h.fderiv
  rw [hfd]
  set c : ℝ := (k:ℝ) * ‖f x‖ ^ ((k:ℝ) - 2) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact mul_nonneg (Nat.cast_nonneg k) (Real.rpow_nonneg (norm_nonneg _) _)
  calc ‖(c • innerSL ℝ (f x)) ∘SL (fderiv ℝ f x)‖
      ≤ ‖c • innerSL ℝ (f x)‖ * ‖fderiv ℝ f x‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = c * ‖f x‖ * ‖fderiv ℝ f x‖ := by
        rw [norm_smul, Real.norm_of_nonneg hc0, innerSL_apply_norm]
    _ = (k:ℝ) * ‖f x‖ ^ ((k:ℝ) - 1) * ‖fderiv ℝ f x‖ := by
        rw [hc]
        have h1 : ‖f x‖ ^ ((k:ℝ) - 2) * ‖f x‖ = ‖f x‖ ^ ((k:ℝ) - 1) := by
          rw [← Real.rpow_add_one' (norm_nonneg (f x)) (by linarith : ((k:ℝ) - 2) + 1 ≠ 0)]
          congr 1
          ring
        calc (k:ℝ) * ‖f x‖ ^ ((k:ℝ) - 2) * ‖f x‖ * ‖fderiv ℝ f x‖
            = (k:ℝ) * (‖f x‖ ^ ((k:ℝ) - 2) * ‖f x‖) * ‖fderiv ℝ f x‖ := by ring
          _ = (k:ℝ) * ‖f x‖ ^ ((k:ℝ) - 1) * ‖fderiv ℝ f x‖ := by rw [h1]
    _ = (k:ℝ) * ‖f x‖ ^ (k - 1) * ‖fderiv ℝ f x‖ := by
        rw [hkeq, Real.rpow_natCast]

/-- The differential of the norm of a differentiable map, composed. -/
theorem nnNorm_fderiv_le {n : ℕ} {u : Work.NN.Core.Cn n → ℂ} {z : Work.NN.Core.Cn n}
    (hu : DifferentiableAt ℝ u z) :
    ‖fderiv ℝ (fun w => ‖u w‖) z‖ ≤ ‖fderiv ℝ u z‖ := by
  have h := norm_fderiv_comp_lipschitz_le (g := fun y : ℂ => ‖y‖) (C := 1)
    (lipschitzWith_one_norm) hu
  have h2 : (fun w : Work.NN.Core.Cn n => ‖u w‖) = (fun y : ℂ => ‖y‖) ∘ u := rfl
  rw [h2]
  simpa using h

/-- The pointwise core estimate: for `z` where `u` is differentiable, the differential of the
`k`-th power of the shifted modulus `srcW u Λ = max ‖u·‖ Λ` is bounded by `k ‖u z‖^{k-1}`, times the
differential of `u`. -/
theorem nnSrcWPow_fderiv_le {n : ℕ} {u : Work.NN.Core.Cn n → ℂ} {Λ : ℝ} {k : ℕ} (hk : 1 ≤ k)
    {z : Work.NN.Core.Cn n} (hu : DifferentiableAt ℝ u z) :
    ‖fderiv ℝ (fun w => (srcW u Λ w)^k) z‖
      ≤ (k:ℝ) * ‖u z‖ ^ (k - 1) * ‖fderiv ℝ u z‖ := by
  by_cases hle : ‖u z‖ ≤ Λ
  · have hWz : srcW u Λ z = Λ := by
      show max ‖u z‖ Λ = Λ
      exact max_eq_right hle
    have h0 : 0 ≤ srcW u Λ z := by rw [hWz]; exact le_trans (norm_nonneg _) hle
    have hmin : IsLocalMin (fun w => (srcW u Λ w)^k) z := by
      refine Filter.Eventually.of_forall (fun x => ?_)
      have h1 : srcW u Λ z ≤ srcW u Λ x := by
        rw [hWz]; exact le_max_right _ _
      exact pow_le_pow_left₀ h0 h1 k
    rw [hmin.fderiv_eq_zero, norm_zero]
    positivity
  · push_neg at hle
    have hev : (fun w => (srcW u Λ w)^k) =ᶠ[𝓝 z] (fun w => ‖u w‖^k) := by
      have hcont : ContinuousAt (fun w => ‖u w‖) z := hu.continuousAt.norm
      filter_upwards [hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hle)] with w hw
      have hw' : Λ < ‖u w‖ := hw
      have hthis : srcW u Λ w = ‖u w‖ := by
        show max ‖u w‖ Λ = ‖u w‖
        exact max_eq_left (le_of_lt hw')
      rw [hthis]
    rw [hev.fderiv_eq]
    rcases eq_or_lt_of_le hk with h1 | h2
    · subst h1
      have h := nnNorm_fderiv_le hu
      simpa only [pow_one, one_mul, pow_zero, Nat.cast_one, tsub_self] using h
    · exact nnNormPow_fderiv_le hu h2

open scoped Classical in
/-- `HasPowCaccSource` with the exponents rewritten as natural powers of `‖u z‖`. -/
lemma hasPowCaccSource_natpow {n : ℕ} {ρ : Fin n → ℝ} {A₀ Λ : ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (h : Work.NN.Core.Lev2.HasPowCaccSource ρ A₀ Λ u) :
    ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
      ∫ z in Work.CR.Flat.polydisc 0 ρ,
          (k:ℝ)^2 * (φ z)^2 * ‖u z‖^(2*k-2) *
            (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
        ≤ A₀ * ((∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^(2*k))
               + (k:ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                   (φ z)^2 * ‖u z‖^(2*k-2) * Λ^2) := by
  intro k hk φ hφsm hφcs hφts hφnn
  have hpow1 : ∀ z, (‖u z‖^2)^(k-1) = ‖u z‖^(2*k-2) := by
    intro z
    rw [← pow_mul, show 2 * (k - 1) = 2 * k - 2 by omega]
  have hpow2 : ∀ z, (‖u z‖^2)^k = ‖u z‖^(2*k) := by
    intro z
    rw [← pow_mul]
  have e1 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
        (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)))
      = ∫ z in Work.CR.Flat.polydisc 0 ρ, (k : ℝ)^2 * (φ z)^2 * ‖u z‖^(2*k-2) *
        (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [hpow1 z]
  have e2 : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k)
      = ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^(2*k) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [hpow2 z]
  have e3 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2)
      = ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖^(2*k-2) * Λ^2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [hpow1 z]
  have h := h k hk φ hφsm hφcs hφts hφnn
  rw [e1, e2, e3] at h
  exact h

theorem srcWShiftCacc {n : ℕ} (hn : 0 < n) {ρ : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j)
    {A₀ : ℝ} (hA₀ : 0 < A₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ u : Work.NN.Core.Cn n → ℂ,
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
        Work.NN.Core.Lev2.HasPowCaccSource ρ A₀ Λ u →
        ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ,
              (φ z)^2 * ‖fderiv ℝ (fun w => (Work.NN.Core.Lev.srcW u Λ w)^k) z‖^2
            ≤ C * ((k:ℝ)^2 * Λ^2 * (∫ z in Work.CR.Flat.polydisc 0 ρ,
                    (φ z)^2 * (Work.NN.Core.Lev.srcW u Λ z)^(2*k-2))
                  + (∫ z in Work.CR.Flat.polydisc 0 ρ,
                    ‖fderiv ℝ φ z‖^2 * (Work.NN.Core.Lev.srcW u Λ z)^(2*k))) := by
  obtain ⟨Cg, hCg0, hCg⟩ := nnGradBoundPoint hn
  refine ⟨Cg * A₀, mul_pos hCg0 hA₀, ?_⟩
  intro Λ hΛ u hu hH k hk φ hφsm hφcs hφts hφnn
  let P : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc 0 ρ
  let W : Work.NN.Core.Cn n → ℝ := srcW u Λ
  let LH : ℝ := ∫ z in P, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
  let J : ℝ := ∫ z in P, (φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z
  let K : ℝ := ∫ z in P, ‖fderiv ℝ φ z‖^2 * ‖u z‖^(2*k)
  let S : ℝ := ∫ z in P, (φ z)^2 * ‖u z‖^(2*k-2)
  let M : ℝ := ∫ z in P, (φ z)^2 * (W z)^(2*k-2)
  let N : ℝ := ∫ z in P, ‖fderiv ℝ φ z‖^2 * (W z)^(2*k)
  have hPopen : IsOpen P := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hPmeas : MeasurableSet P := hPopen.measurableSet
  have hdiff : ∀ z ∈ P, DifferentiableAt ℝ u z := fun z hz =>
    (hu.contDiffAt (hPopen.mem_nhds hz)).differentiableAt (by norm_num)
  have hWcont : ContinuousOn W (tsupport φ) :=
    nnSrc_continuousOn_max_norm (hu.continuousOn.mono hφts) Λ
  -- ## Step 1: pointwise bound
  have hpt : ∀ z ∈ P, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
      ≤ (k:ℝ)^2 * Cg * ((φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z) := by
    intro z hz
    have hd := hdiff z hz
    have h1 : ‖fderiv ℝ (fun w => (W w)^k) z‖ ≤ (k:ℝ) * ‖u z‖^(k-1) * ‖fderiv ℝ u z‖ :=
      nnSrcWPow_fderiv_le hk hd
    have h2 : ‖fderiv ℝ u z‖^2 ≤ Cg * nnSrcEnergy u z := hCg u z
    have hexp : (k - 1) * 2 = 2 * k - 2 := by omega
    have hsq : ((k:ℝ) * ‖u z‖^(k-1) * ‖fderiv ℝ u z‖)^2
        = (k:ℝ)^2 * ‖u z‖^(2*k-2) * ‖fderiv ℝ u z‖^2 := by
      rw [mul_pow, mul_pow, ← pow_mul, hexp]
    have h3 : ‖fderiv ℝ (fun w => (W w)^k) z‖^2
        ≤ (k:ℝ)^2 * ‖u z‖^(2*k-2) * Cg * nnSrcEnergy u z := by
      calc ‖fderiv ℝ (fun w => (W w)^k) z‖^2
          ≤ ((k:ℝ) * ‖u z‖^(k-1) * ‖fderiv ℝ u z‖)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = (k:ℝ)^2 * ‖u z‖^(2*k-2) * ‖fderiv ℝ u z‖^2 := hsq
        _ ≤ (k:ℝ)^2 * ‖u z‖^(2*k-2) * (Cg * nnSrcEnergy u z) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (k:ℝ)^2 * ‖u z‖^(2*k-2) * Cg * nnSrcEnergy u z := by ring
    calc (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
        ≤ (φ z)^2 * ((k:ℝ)^2 * ‖u z‖^(2*k-2) * Cg * nnSrcEnergy u z) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = (k:ℝ)^2 * Cg * ((φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z) := by ring
  -- ## Step 2: integrability of the majorants
  have hIntJ : Integrable (fun z => (φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z) volume := by
    refine nnSrc_integrable_of_continuousOn_compact_of_support hφcs.isCompact ?_ ?_
    · exact ((hφsm.continuous.continuousOn.pow 2).mul
        (((hu.continuousOn.mono hφts).norm).pow (2*k-2))).mul
        (nnSrc_continuousOn_energy hu |>.mono hφts)
    · intro z hz
      rw [Function.mem_support] at hz
      exact subset_closure (Function.mem_support.mpr fun h0 => hz (by rw [h0]; ring))
  have hIntM : Integrable (fun z => (φ z)^2 * (W z)^(2*k-2)) volume := by
    refine nnSrc_integrable_of_continuousOn_compact_of_support hφcs.isCompact ?_ ?_
    · exact (hφsm.continuous.continuousOn.pow 2).mul (hWcont.pow (2*k-2))
    · intro z hz
      rw [Function.mem_support] at hz
      exact subset_closure (Function.mem_support.mpr fun h0 => hz (by rw [h0]; ring))
  have hIntN : Integrable (fun z => ‖fderiv ℝ φ z‖^2 * (W z)^(2*k)) volume := by
    refine nnSrc_integrable_of_continuousOn_compact_of_support hφcs.isCompact ?_ ?_
    · exact ((hφsm.continuous_fderiv (by simp)).continuousOn.norm.pow 2).mul (hWcont.pow (2*k))
    · intro z hz
      rw [Function.mem_support] at hz
      exact nnSrc_mem_tsupport_of_fderiv_ne_zero fun h0 => hz (by rw [h0]; simp)
  -- ## Step 3: the first integral comparison
  have hA : LH ≤ (k:ℝ)^2 * Cg * J := by
    have h1 : (∫ z in P, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2)
        ≤ ∫ z in P, (k:ℝ)^2 * Cg * ((φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z) := by
      refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) ?_ ?_
      · positivity
      · exact (hIntJ.const_mul ((k:ℝ)^2 * Cg)).mono_measure MeasureTheory.Measure.restrict_le_self
      · show ∀ᵐ z ∂(MeasureTheory.volume.restrict P),
            (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2
              ≤ (k:ℝ)^2 * Cg * ((φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z)
        rw [MeasureTheory.ae_restrict_iff' hPmeas]
        exact Filter.Eventually.of_forall fun z hz => hpt z hz
    have h2 : (∫ z in P, (k:ℝ)^2 * Cg * ((φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z))
        = (k:ℝ)^2 * Cg * J := by
      rw [← MeasureTheory.integral_const_mul]
    calc LH = ∫ z in P, (φ z)^2 * ‖fderiv ℝ (fun w => (W w)^k) z‖^2 := rfl
      _ ≤ ∫ z in P, (k:ℝ)^2 * Cg * ((φ z)^2 * ‖u z‖^(2*k-2) * nnSrcEnergy u z) := h1
      _ = (k:ℝ)^2 * Cg * J := h2
  -- ## Step 4: the Caccioppoli hypothesis
  have hB : (k:ℝ)^2 * J ≤ A₀ * (K + (k:ℝ)^2 * Λ^2 * S) := by
    have h := hasPowCaccSource_natpow hH k hk φ hφsm hφcs hφts hφnn
    have e1 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (k:ℝ)^2 * (φ z)^2 * ‖u z‖^(2*k-2) *
          (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2)))
        = (k:ℝ)^2 * J := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      ring
    have e2 : (∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖u z‖^(2*k)) = K := rfl
    have e3 : (∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 * ‖u z‖^(2*k-2) * Λ^2)
        = Λ^2 * S := by
      rw [show Λ^2 * S = S * Λ^2 by ring, ← MeasureTheory.integral_mul_const]
    rw [e1, e2, e3] at h
    simpa only [mul_assoc] using h
  -- ## Step 5: monotonicity
  have hC : K ≤ N := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) ?_ ?_
    · positivity
    · exact hIntN.mono_measure MeasureTheory.Measure.restrict_le_self
    · show ∀ᵐ z ∂(MeasureTheory.volume.restrict P),
          ‖fderiv ℝ φ z‖^2 * ‖u z‖^(2*k) ≤ ‖fderiv ℝ φ z‖^2 * (W z)^(2*k)
      rw [MeasureTheory.ae_restrict_iff' hPmeas]
      refine Filter.Eventually.of_forall fun z hz => ?_
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) (2*k)
  have hD : S ≤ M := by
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_) ?_ ?_
    · positivity
    · exact hIntM.mono_measure MeasureTheory.Measure.restrict_le_self
    · show ∀ᵐ z ∂(MeasureTheory.volume.restrict P),
          (φ z)^2 * ‖u z‖^(2*k-2) ≤ (φ z)^2 * (W z)^(2*k-2)
      rw [MeasureTheory.ae_restrict_iff' hPmeas]
      refine Filter.Eventually.of_forall fun z hz => ?_
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact pow_le_pow_left₀ (norm_nonneg _) (le_max_left _ _) (2*k-2)
  -- ## Step 6: assembly
  have key : LH ≤ (Cg * A₀) * ((k:ℝ)^2 * Λ^2 * M + N) := by
    calc LH ≤ (k:ℝ)^2 * Cg * J := hA
      _ = Cg * ((k:ℝ)^2 * J) := by ring
      _ ≤ Cg * (A₀ * (K + (k:ℝ)^2 * Λ^2 * S)) := mul_le_mul_of_nonneg_left hB hCg0.le
      _ = Cg * A₀ * (K + (k:ℝ)^2 * Λ^2 * S) := by ring
      _ ≤ Cg * A₀ * ((k:ℝ)^2 * Λ^2 * M + N) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCg0.le hA₀.le)
          have hD' : (k:ℝ)^2 * Λ^2 * S ≤ (k:ℝ)^2 * Λ^2 * M :=
            mul_le_mul_of_nonneg_left hD (by positivity)
          linarith
  exact key

end Work.NN.Core.Lev

