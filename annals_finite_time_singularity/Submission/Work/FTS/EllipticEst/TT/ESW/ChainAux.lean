import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.remov.SourceBound.SliceAlgebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliaries for the top-slot chain `Tk α k (∂_θθΨ) ≤ C·(chain of ∂_θ^r ∂_θθΨ)`

This file collects the bookkeeping lemmas used by `Tk_B_le_chain`:

* `SmoothOpen.pthIter`, `pthIter_add` (iterated plain angular derivatives);
* `Icc_one_split` / `not_mem_Icc_pred` (splitting `Icc 1 k = Icc 1 (k-1) ∪ {k}`);
* `setIntegral_mono_of_nonneg_ae` (the a.e. version of `setIntegral_mono_of_nonneg`);
* the abbreviations `ChainG` (the pointwise chain slots) and `ChainH` (their `θ`-integrals);
* `Tk_chain_of`, the measure-theoretic assembly: a pointwise chain bound together with the
  integrability of the chain slots gives the bound on `Step.Tk`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.TT.ESW

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Iterated plain angular derivatives -/

/-- `SmoothOpen` is preserved by the iterated plain angular derivative `∂_θ^n`. -/
theorem SmoothOpen.pthIter {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F) (n : ℕ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter n F) := by
  induction n with
  | zero => simpa using hF
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- `∂_θ^{m+n} = ∂_θ^m ∂_θ^n` for the iterated plain angular derivative. -/
theorem pthIter_add (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-! ## Splitting `Icc 1 k` at its top element -/

theorem Icc_one_split {k : ℕ} (hk : 1 ≤ k) :
    Finset.Icc 1 k = insert k (Finset.Icc 1 (k - 1)) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem not_mem_Icc_pred {k : ℕ} (hk : 1 ≤ k) : k ∉ Finset.Icc 1 (k - 1) := by
  simp only [Finset.mem_Icc]; omega

/-! ## An a.e. version of `setIntegral_mono_of_nonneg` -/

/-- `setIntegral_mono_of_nonneg` with the two pointwise hypotheses weakened to a.e. ones
(along the restricted measure); only the majorant needs to be integrable. -/
theorem setIntegral_mono_of_nonneg_ae {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : 0 ≤ᵐ[volume.restrict s] f) (h : f ≤ᵐ[volume.restrict s] g)
    (hg : IntegrableOn g s volume) :
    ∫ x in s, f x ≤ ∫ x in s, g x := by
  by_cases hf' : AEStronglyMeasurable f (volume.restrict s)
  · exact integral_mono_of_nonneg hf hg h
  · rw [integral_non_aestronglyMeasurable hf']
    exact integral_nonneg_of_ae (hf.trans h)

/-! ## The chain slots -/

/-- The pointwise chain slot `w(z)^2 · (∂_θ^r v(z,θ))^2 · sin(2θ)^{2r-γ}`. -/
abbrev ChainG (α : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) (r : ℕ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter r v z θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))

/-- The `θ`-integral of the chain slot `ChainG`. -/
abbrev ChainH (α : ℝ) (v : ℝ → ℝ → ℝ) (z : ℝ) (r : ℕ) : ℝ :=
  (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r v z θ) ^ 2 *
    Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))

/-! ## The assembly -/

/-- **The measure-theoretic assembly of the chain.**  If the top angular slot
`(D_θ^k v · Wt α)²` is dominated pointwise (on the open interval) by the chain slots
`ChainG`, and each chain slot is `θ`-integrable with `z`-integrable `θ`-integral, then
`Tk α k v ≤ C · ∑_{r ∈ Icc 1 k} ∫_z ChainH α v z r`. -/
theorem Tk_chain_of {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {v : ℝ → ℝ → ℝ} {Ca : ℝ} (hCa : 0 < Ca)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hcore : ∀ (z θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ)) →
      (Work.Spaces.DthIter k v z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r)
    (hintθ : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => ChainG α v z θ m) Work.Spaces.Iθ)
    (hintz : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      MeasureTheory.IntegrableOn (fun z => ChainH α v z m) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.remov.Step.Tk α k v
      ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α v z r := by
  have hstep : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := by
    intro z hz
    have hz0 : (0 : ℝ) ≤ z := hz
    have hmaj : MeasureTheory.IntegrableOn
        (fun θ => Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r) Work.Spaces.Iθ :=
      (integrable_finsetSum (Finset.Icc 1 k)
        (fun r hr => hintθ r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 z hz)).const_mul Ca
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := by
      rcases eq_or_lt_of_le hz0 with hzeq | hzpos
      · have hw0 : Work.Spaces.w z = 0 := by rw [← hzeq]; norm_num [Work.Spaces.w]
        refine Filter.Eventually.of_forall (fun θ => ?_)
        have hL : Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ = 0 := by
          rw [Work.Spaces.Wt, hw0, zero_mul, mul_zero]
        have hR : ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r = 0 := by
          refine Finset.sum_eq_zero (fun r hr => ?_)
          simp only [ChainG, hw0]
          ring
        rw [hL, hR, mul_zero]
        simp
      · refine Work.FTS.EllipticEst.remov.selfdth.ae_mem_Ioo_of_Iθ.mono (fun θ hθ => ?_)
        have hsm' : ∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ) :=
          fun n => (hsm n).contDiffAt ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hzpos, hθ⟩)
        simpa only [Work.Spaces.mixed_zero_left] using hcore z θ hθ hsm'
    have hmono := setIntegral_mono_of_nonneg_ae
      (f := fun θ => (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
      (g := fun θ => Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r)
      (Filter.Eventually.of_forall (fun θ => sq_nonneg _)) hae hmaj
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r := hmono
      _ = Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := by
          have hsum : (∫ θ in Work.Spaces.Iθ, ∑ r ∈ Finset.Icc 1 k, ChainG α v z θ r)
              = ∑ r ∈ Finset.Icc 1 k, ∫ θ in Work.Spaces.Iθ, ChainG α v z θ r :=
            MeasureTheory.integral_finsetSum (Finset.Icc 1 k) (fun r hr =>
              hintθ r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2 z hz)
          rw [MeasureTheory.integral_const_mul, hsum]
          congr 1
          refine Finset.sum_congr rfl (fun r hr => ?_)
          show (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
              ((Work.Spaces.pthIter r v z θ) ^ 2 *
                Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α)))
            = ChainH α v z r
          rw [MeasureTheory.integral_const_mul]
  have hzstep : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz, Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := by
    have hmaj : MeasureTheory.IntegrableOn
        (fun z => Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r) Work.Spaces.Iz :=
      (integrable_finsetSum (Finset.Icc 1 k)
        (fun r hr => hintz r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)).const_mul Ca
    refine setIntegral_mono_of_nonneg_ae
      (f := fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2)
      (g := fun z => Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r) ?_ ?_ hmaj
    · exact Filter.Eventually.of_forall (fun z => integral_nonneg (fun θ => sq_nonneg _))
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hstep z hz)
  calc Work.FTS.EllipticEst.remov.Step.Tk α k v
      = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.mixed 0 k v z θ * Work.Spaces.Wt α z θ) ^ 2 := rfl
    _ ≤ ∫ z in Work.Spaces.Iz, Ca * ∑ r ∈ Finset.Icc 1 k, ChainH α v z r := hzstep
    _ = Ca * ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α v z r := by
        have hsum : (∫ z in Work.Spaces.Iz, ∑ r ∈ Finset.Icc 1 k, ChainH α v z r)
            = ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α v z r :=
          MeasureTheory.integral_finsetSum (Finset.Icc 1 k) (fun r hr =>
            hintz r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2)
        rw [MeasureTheory.integral_const_mul, hsum]

/-! ## The target conclusion, from the two inputs -/

/-- **`Tk_B_le_chain` with its two inputs as hypotheses.**  The pointwise chain `hCa` (the
content of `TkChainCore`) together with the integrability of the chain slots `hintθ`, `hintz`
(the content of `TkChainIntegrable`) gives the stated chain bound for `Bsl Ψ = ∂_θθΨ`. -/
theorem Tk_B_le_chain_aux {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {Ψ : ℝ → ℝ → ℝ}
    (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) {Ca : ℝ} (hCa_pos : 0 < Ca)
    (hCa : ∀ (α' : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry v) (z, θ)) →
      (Work.Spaces.DthIter k v z θ * Work.Spaces.Wt α' z θ) ^ 2
        ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ChainG α' v z θ r)
    (hintθ : ∀ m : ℕ, 1 ≤ m → m ≤ k → ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => ChainG α (Bsl Ψ) z θ m) Work.Spaces.Iθ)
    (hintz : ∀ m : ℕ, 1 ≤ m → m ≤ k →
      MeasureTheory.IntegrableOn (fun z => ChainH α (Bsl Ψ) z m) Work.Spaces.Iz) :
    ∃ C : ℝ, 0 < C ∧
      Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ) ≤ C *
        ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α)) := by
  have hSO : Work.FTS.EllipticEst.SmoothOpen (Bsl Ψ) := SmoothOpen.pthIter hΨ 2
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Bsl Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n => (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hSO n
  have hcore := Tk_chain_of hk hCa_pos hsm (fun z θ hθ hs => hCa α (Bsl Ψ) z θ hθ hs) hintθ hintz
  have htop : (∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z k)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
    show (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter k (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) = _
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    rw [← pthIter_add k 2 Ψ]
  refine ⟨Ca, hCa_pos, ?_⟩
  calc Work.FTS.EllipticEst.remov.Step.Tk α k (Bsl Ψ)
      ≤ Ca * ∑ r ∈ Finset.Icc 1 k, ∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z r := hcore
    _ = Ca * ((∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z k)
          + (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, ChainH α (Bsl Ψ) z r)) := by
        rw [Icc_one_split hk, Finset.sum_insert (not_mem_Icc_pred hk)]
    _ = Ca * ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α))
          + (∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))) := by
        rw [htop]
    _ = Ca * ((∑ r ∈ Finset.Icc 1 (k - 1), ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter r (Bsl Ψ) z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (r : ℝ) - Work.Spaces.gam α))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
            ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter (k + 2) Ψ z θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)) := by
        ring

end Work.FTS.EllipticEst.TT.ESW
