import Mathlib
import Submission.Work.BourgainPlan.Maximal.MtaDefs
import Submission.Work.BourgainPlan.Maximal.Ts_prelude

/-!
# `dyadSum` is the `L²` Fourier multiplier with symbol `mtaFullSym`

`dyadSum P K ε h = Σ_{k<K} ε k (σ_{2^k} h − σ_{2^{k+1}} h)` is a finite signed sum of polynomial
curve averages `σ_N h(x) = ∫₀¹ h (x − P (N t)) dt`, and each curve average is the `L²` Fourier
multiplier with symbol `conj (polyProfile P N)` (`curveSigma_eq_multiplier`, `Ts_prelude`).

The multiplier calculus of `Ts_prelude` (additivity, scalar multiples, independence of the proof
that the symbol is essentially bounded) then identifies `dyadSum P K ε h` almost everywhere with
the multiplier with symbol `Σ_{k<K} ε k μ_k`, where
`μ_k = conj Φ_{2^k} − conj Φ_{2^{k+1}} = muSym P k`; that symbol is `mtaFullSym P K ε`.
-/

open MeasureTheory Finset Filter
open scoped ENNReal BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-! ## Elementary helpers -/

/-- The multiplier operator does not depend on the proof that its symbol is essentially bounded. -/
lemma dyad_multiplier_proof_irrel (m : ℝ → ℂ) (h₁ h₂ : MemLp m ⊤ (volume : Measure ℝ))
    (X : Lp ℂ 2 (volume : Measure ℝ)) :
    Commons.Analysis.Fourier.BoundaryLayer.multiplier m h₁ X
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier m h₂ X := rfl

/-- A finite sum of functions, evaluated pointwise, is the sum of the values. -/
lemma dyad_sum_apply (s : Finset ℕ) (f : ℕ → ℝ → ℂ) :
    (fun x : ℝ => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
  funext x
  rw [Finset.sum_apply]

/-! ## The symbol of a summand -/

/-- The symbol `ε k · μ_k` of the `k`-th summand of `dyadSum`. -/
noncomputable def dyadSumSym (P : Polynomial ℤ) (ε : ℕ → ℂ) (k : ℕ) : ℝ → ℂ :=
  fun ξ => ε k * (starRingEnd ℂ (polyProfile P (2^k) ξ)
    - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ))

lemma memLp_dyadSumSym (P : Polynomial ℤ) (ε : ℕ → ℂ) (k : ℕ) :
    MemLp (dyadSumSym P ε k) ⊤ (volume : Measure ℝ) :=
  ((memLp_star_polyProfile P (2^k)).sub (memLp_star_polyProfile P (2^(k+1)))).const_mul (ε k)

lemma mtaFullSym_eq_sum_dyadSumSym (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) :
    mtaFullSym P K ε = fun ξ : ℝ => ∑ k ∈ Finset.range K, dyadSumSym P ε k ξ := by
  funext ξ
  simp [mtaFullSym, dyadSumSym, muSym]

/-! ## The `k`-th summand is the multiplier with symbol `ε k · μ_k` -/

lemma dyadD_multiplier_ae (P : Polynomial ℤ) (k : ℕ) (ε : ℕ → ℂ) {h : ℝ → ℂ}
    (hh2 : MemLp h 2 (volume : Measure ℝ)) :
    (fun x : ℝ => ε k * (curveSigma P (2^k) h x - curveSigma P (2^(k+1)) h x))
      =ᵐ[(volume : Measure ℝ)]
      ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
        (memLp_dyadSumSym P ε k) (hh2.toLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) := by
  classical
  obtain ⟨hm1, h1⟩ := (curveSigma_eq_multiplier P (2^k) h hh2).1
  obtain ⟨hm2, h2⟩ := (curveSigma_eq_multiplier P (2^(k+1)) h hh2).1
  have hm3 : MemLp (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)
      - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) ⊤ (volume : Measure ℝ) := hm1.sub hm2
  have hmF : MemLp (dyadSumSym P ε k) ⊤ (volume : Measure ℝ) := memLp_dyadSumSym P ε k
  -- the algebraic identity for the multipliers
  have hkey : Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k) hmF
        (hh2.toLp)
      = ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)) hm1 (hh2.toLp)
            - Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hm2 (hh2.toLp)) := by
    change Commons.Analysis.Fourier.BoundaryLayer.multiplier (fun ξ : ℝ => ε k *
        (starRingEnd ℂ (polyProfile P (2^k) ξ)
          - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ))) hmF (hh2.toLp)
      = ε k • (Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)) hm1 (hh2.toLp)
            - Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hm2 (hh2.toLp))
    rw [multiplier_const_smul (ε k)
          (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)
            - starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hm3 hmF (hh2.toLp),
      multiplier_sub_sym (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ))
        (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hm1 hm2 hm3 (hh2.toLp)]
  -- the difference of the two curve averages
  have hsub : (fun x : ℝ => curveSigma P (2^k) h x - curveSigma P (2^(k+1)) h x)
      =ᵐ[(volume : Measure ℝ)] (fun x : ℝ =>
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)) hm1 (hh2.toLp)
            - Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hm2 (hh2.toLp) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) :=
    (h1.sub h2).trans (Lp.coeFn_sub _ _).symm
  -- multiply by `ε k`
  have hcoe : ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
        hmF (hh2.toLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] (fun x : ℝ => ε k *
        (((Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^k) ξ)) hm1 (hh2.toLp)
            - Commons.Analysis.Fourier.BoundaryLayer.multiplier
              (fun ξ : ℝ => starRingEnd ℂ (polyProfile P (2^(k+1)) ξ)) hm2 (hh2.toLp) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)) := by
    rw [hkey]
    exact Lp.coeFn_smul (ε k) _
  have hconst : (fun _ : ℝ => ε k) =ᵐ[(volume : Measure ℝ)] (fun _ : ℝ => ε k) :=
    EventuallyEq.of_eq rfl
  refine (hconst.mul hsub).trans ?_
  refine hcoe.symm.trans ?_
  exact EventuallyEq.of_eq (congrArg (fun Z : Lp ℂ 2 (volume : Measure ℝ) => (Z : ℝ → ℂ))
    (dyad_multiplier_proof_irrel (dyadSumSym P ε k) (memLp_dyadSumSym P ε k) hmF (hh2.toLp)))

/-! ## The target -/

theorem dyadSum_multiplier_ae (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) {h : ℝ → ℂ}
    (hh1 : MeasureTheory.Integrable h) (hh2 : MeasureTheory.MemLp h 2 MeasureTheory.volume) :
    ∃ hm : MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mtaFullSym P K ε) ⊤ MeasureTheory.volume,
      Work.BourgainPlan.Maximal.dyadSum P K ε h =ᵐ[MeasureTheory.volume]
        (Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (Work.BourgainPlan.Maximal.mtaFullSym P K ε) hm
          (MeasureTheory.MemLp.toLp h hh2) : ℝ → ℂ) := by
  classical
  refine ⟨memLp_mtaFullSym P K ε, ?_⟩
  have hterm : ∀ k ∈ Finset.range K,
      (fun x : ℝ => ε k * (curveSigma P (2^k) h x - curveSigma P (2^(k+1)) h x))
        =ᵐ[(volume : Measure ℝ)]
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
          (memLp_dyadSumSym P ε k) (hh2.toLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    fun k _ => dyadD_multiplier_ae P k ε hh2
  have hdyad : dyadSum P K ε h
      = ∑ k ∈ Finset.range K,
          fun x : ℝ => ε k * (curveSigma P (2^k) h x - curveSigma P (2^(k+1)) h x) := by
    funext x
    simp only [dyadSum, dyadD, Finset.sum_apply]
  have hS1 : (∑ k ∈ Finset.range K,
        fun x : ℝ => ε k * (curveSigma P (2^k) h x - curveSigma P (2^(k+1)) h x))
      =ᵐ[(volume : Measure ℝ)]
      (∑ k ∈ Finset.range K, fun x : ℝ =>
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
          (memLp_dyadSumSym P ε k) (hh2.toLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x) :=
    ae_eq_finset_sum _ _ _ hterm
  have hS2 : (∑ k ∈ Finset.range K, fun x : ℝ =>
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
          (memLp_dyadSumSym P ε k) (hh2.toLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x)
      =ᵐ[(volume : Measure ℝ)]
      ((∑ k ∈ Finset.range K, Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
          (memLp_dyadSumSym P ε k) (hh2.toLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) :=
    (EventuallyEq.of_eq (dyad_sum_apply (Finset.range K) (fun k x =>
        ((Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
          (memLp_dyadSumSym P ε k) (hh2.toLp) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x))).symm.trans
      (Lp.coeFn_fun_finsetSum (Finset.range K) (fun k =>
        Commons.Analysis.Fourier.BoundaryLayer.multiplier (dyadSumSym P ε k)
          (memLp_dyadSumSym P ε k) (hh2.toLp))).symm
  have hS3 : (∑ k ∈ Finset.range K, Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (dyadSumSym P ε k) (memLp_dyadSumSym P ε k) (hh2.toLp))
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier
          (fun ξ : ℝ => ∑ k ∈ Finset.range K, dyadSumSym P ε k ξ)
          (memLpSum_top (Finset.range K) (dyadSumSym P ε) (fun k => memLp_dyadSumSym P ε k))
          (hh2.toLp) :=
    multiplier_sum (Finset.range K) (dyadSumSym P ε) (fun k => memLp_dyadSumSym P ε k) (hh2.toLp)
  have hS4 : Commons.Analysis.Fourier.BoundaryLayer.multiplier
        (fun ξ : ℝ => ∑ k ∈ Finset.range K, dyadSumSym P ε k ξ)
        (memLpSum_top (Finset.range K) (dyadSumSym P ε) (fun k => memLp_dyadSumSym P ε k))
        (hh2.toLp)
      = Commons.Analysis.Fourier.BoundaryLayer.multiplier (mtaFullSym P K ε)
          (memLp_mtaFullSym P K ε) (hh2.toLp) :=
    multiplier_congr (mtaFullSym_eq_sum_dyadSumSym P K ε).symm _ _ _
  refine (EventuallyEq.of_eq hdyad).trans (hS1.trans (hS2.trans ?_))
  refine (EventuallyEq.of_eq (congrArg (fun Z : Lp ℂ 2 (volume : Measure ℝ) => (Z : ℝ → ℂ))
    hS3)).trans ?_
  exact EventuallyEq.of_eq (congrArg (fun Z : Lp ℂ 2 (volume : Measure ℝ) => (Z : ℝ → ℂ)) hS4)

end

end Work.BourgainPlan.Maximal
