import Mathlib
import Submission.Work.BourgainPlan.Maximal.DRDFDefs
import Submission.Work.BourgainPlan.Maximal.dyadic_reduction
import Submission.Work.BourgainPlan.Maximal.Ts_l2_decay
import Submission.Work.BourgainPlan.Maximal.Ts_lp_uniform
import Submission.Work.BourgainPlan.Maximal.polyProfile_increment_sum_le

/-!
# The assembly of `mst_theta_real` (step 6 of `Maximal/DRDF_ROUTE.md`): definitions

This module fixes the objects of the *assembly* of the `L^{2r}` bound for the signed lacunary sum of
polynomial curve-average differences, from

* the `L²` decay of the blocks `T_s` (`Ts_l2_decay`, equivalently the pointwise symbol bound
  `Ts_symbol_bound`),
* the uniform `L^{p₁}` bound of the blocks (`Ts_lp_uniform`),
* the Marcinkiewicz interpolation (`marcinkiewicz_two_strong_memLp_uniform`),

namely: the block symbols `ν_s`, the full symbol `Θ`, their partial sums over `|s| ≤ S`, the block
operators, and the truncation `mtaTrunc` which makes the interpolation apply to honest operators.
-/

open MeasureTheory Finset
open scoped ENNReal BigOperators FourierTransform

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

noncomputable section

/-! ## Truncation and the block symbols -/

/-- Truncation of a function to the interval `[-N, N]`. -/
def mtaTrunc (N : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f x * (Set.Icc (-(N : ℝ)) (N : ℝ)).indicator (fun _ => (1 : ℂ)) x

lemma mtaTrunc_add (N : ℕ) (f g : ℝ → ℂ) : mtaTrunc N (f + g) = mtaTrunc N f + mtaTrunc N g := by
  funext x; simp only [mtaTrunc, Pi.add_apply]; ring

lemma mtaTrunc_smul (N : ℕ) (c : ℂ) (f : ℝ → ℂ) : mtaTrunc N (c • f) = c • mtaTrunc N f := by
  funext x; simp only [mtaTrunc, Pi.smul_apply]; ring

lemma norm_mtaTrunc_apply_le (N : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    ‖mtaTrunc N f x‖ ≤ ‖f x‖ := by
  rw [mtaTrunc]
  rcases Set.indicator_eq_zero_or_self (s := Set.Icc (-(N:ℝ)) (N:ℝ)) (f := fun _ => (1:ℂ)) x with h | h
  · rw [h, mul_zero, norm_zero]; exact norm_nonneg _
  · rw [h, mul_one]

lemma mtaTrunc_eq_zero_of_notMem {N : ℕ} {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ Set.Icc (-(N : ℝ)) (N : ℝ)) : mtaTrunc N f x = 0 := by
  rw [mtaTrunc, Set.indicator_of_notMem hx, mul_zero]

lemma mtaTrunc_eq_self_of_mem {N : ℕ} {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∈ Set.Icc (-(N : ℝ)) (N : ℝ)) : mtaTrunc N f x = f x := by
  rw [mtaTrunc, Set.indicator_of_mem hx, mul_one]

/-- The symbol of the `s`-th block of the dyadic-difference sum. -/
def mtaBlkSym (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) : ℝ → ℂ :=
  fun ξ => ∑ k ∈ Finset.range K,
    ε k * (tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ *
      psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ) * muSym P k ξ

/-- The symbol of the full dyadic-difference sum. -/
def mtaFullSym (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) : ℝ → ℂ :=
  fun ξ => ∑ k ∈ Finset.range K, ε k * muSym P k ξ

/-- The partial sum of block symbols over the lacunary indices `|s| ≤ S`. -/
def mtaBlkSymSum (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (S : ℕ) : ℝ → ℂ :=
  fun ξ => ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), mtaBlkSym P K ε s ξ

/-- The `s`-th block operator (the operator of `Ts_l2_decay` / `Ts_lp_uniform`). -/
def mtaBlkOp (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ∑ k ∈ Finset.range K, dyadicProj dyadTilde ((P.natDegree : ℤ) * (k : ℤ) + s)
    (fun y => ε k * dyadicProj dyadPsi ((P.natDegree : ℤ) * (k : ℤ) + s) (dyadD P k h) y) x

/-! ## The norm of `μ_k` and the telescoping of the `ψ`-family -/

lemma norm_muSym_eq (P : Polynomial ℤ) (k : ℕ) (ξ : ℝ) :
    ‖muSym P k ξ‖ = ‖polyProfile P (2 ^ (k+1)) ξ - polyProfile P (2 ^ k) ξ‖ := by
  rw [muSym]
  have h : (starRingEnd ℂ) (polyProfile P (2^k) ξ) - (starRingEnd ℂ) (polyProfile P (2^(k+1)) ξ)
      = (starRingEnd ℂ) (polyProfile P (2^k) ξ - polyProfile P (2^(k+1)) ξ) := by
    rw [map_sub]
  rw [h, Complex.norm_conj, norm_sub_rev]

/-- Telescoping of a difference sequence indexed by `ℤ`. -/
lemma mta_sum_Icc_telescope (a : ℤ → ℝ) (S : ℕ) :
    ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), (a s - a (s + 1))
      = a (-(S : ℤ)) - a ((S : ℤ) + 1) := by
  induction S with
  | zero => simp
  | succ S ih =>
    have hset : Finset.Icc (-(↑(S+1) : ℤ)) (↑(S+1) : ℤ)
        = insert (-(↑(S+1) : ℤ)) (insert (↑(S+1) : ℤ) (Finset.Icc (-(↑S : ℤ)) (↑S : ℤ))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      constructor
      · rintro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · exact Or.inl h.symm
        · right
          rcases eq_or_lt_of_le h2 with h' | h'
          · exact Or.inl h'
          · exact Or.inr ⟨by omega, by omega⟩
      · rintro (rfl | rfl | ⟨h1, h2⟩) <;> omega
    have h1 : (-(↑(S+1) : ℤ)) ∉ insert (↑(S+1) : ℤ) (Finset.Icc (-(↑S : ℤ)) (↑S : ℤ)) := by
      rw [Finset.mem_insert, not_or]
      constructor
      · intro h; push_cast at h; omega
      · intro h; rw [Finset.mem_Icc] at h; push_cast at h; omega
    have h2 : (↑(S+1) : ℤ) ∉ Finset.Icc (-(↑S : ℤ)) (↑S : ℤ) := by
      intro h; rw [Finset.mem_Icc] at h; push_cast at h; omega
    rw [hset, Finset.sum_insert h1, Finset.sum_insert h2, ih]
    push_cast
    ring_nf

/-- The partial sum of the `ψ`-family telescopes to a difference of the bump `θ`. -/
lemma mta_sum_dyadPsi_Icc (P : Polynomial ℤ) (k : ℕ) (ξ : ℝ) (S : ℕ) :
    ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
        dyadPsi ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * ξ)
      = dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
        - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ) := by
  have hfun : (fun s : ℤ => dyadPsi ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * ξ))
      = fun s : ℤ =>
          ((fun t : ℤ => dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + t) * ξ)) s
            - (fun t : ℤ => dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + t) * ξ)) (s + 1)) := by
    funext s
    show dyadPsi ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * ξ)
      = dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * ξ)
        - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + (s + 1)) * ξ)
    rw [dyadPsi_eq]
    congr 1
    have hpow : (2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + (s + 1))
        = (2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * 2 := by
      rw [show (P.natDegree : ℤ) * (k : ℤ) + (s + 1)
            = ((P.natDegree : ℤ) * (k : ℤ) + s) + 1 by ring,
        zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]
    rw [hpow]; ring
  rw [hfun, mta_sum_Icc_telescope]

lemma mta_sum_psiFam_Icc (P : Polynomial ℤ) (k : ℕ) (ξ : ℝ) (S : ℕ) :
    ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ
      = ((dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
          - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ) : ℝ) : ℂ) := by
  rw [show (∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ)
      = ((∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
          dyadPsi ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + s) * ξ) : ℝ) : ℂ) from by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun s _ => rfl)]
  rw [mta_sum_dyadPsi_Icc]

/-! ## Basic algebra of the block symbols -/

lemma mtaBlkSym_eq_psi (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) (ξ : ℝ) :
    mtaBlkSym P K ε s ξ
      = ∑ k ∈ Finset.range K, ε k *
          (psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ * muSym P k ξ) := by
  rw [mtaBlkSym]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [tildeFam_mul_psiFam]
  ring_nf

/-- Expansion of the partial sum of block symbols. -/
lemma mtaBlkSymSum_eq (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (S : ℕ) (ξ : ℝ) :
    mtaBlkSymSum P K ε S ξ
      = ∑ k ∈ Finset.range K, ε k * muSym P k ξ *
          ((dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + -(S : ℤ)) * ξ)
            - dyadTheta ((2:ℝ) ^ ((P.natDegree : ℤ) * (k : ℤ) + ((S : ℤ) + 1)) * ξ) : ℝ) : ℂ) := by
  have hstep1 : (∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ), mtaBlkSym P K ε s ξ)
      = ∑ k ∈ Finset.range K, ∑ s ∈ Finset.Icc (-(S : ℤ)) (S : ℤ),
          (ε k * muSym P k ξ) * psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ := by
    simp only [mtaBlkSym]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun s _ => ?_))
    rw [tildeFam_mul_psiFam]
    ring_nf
  rw [mtaBlkSymSum, hstep1]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.mul_sum, mta_sum_psiFam_Icc]

/-- Sum of the norms of `μ_k`, uniformly in the frequency. -/
lemma sum_norm_muSym_le (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (hlc : 0 < P.leadingCoeff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (ξ : ℝ), ∑ k ∈ Finset.range K, ‖muSym P k ξ‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := polyProfile_increment_sum_le P hlc hdeg
  refine ⟨C, hCpos, fun K ξ => ?_⟩
  refine (Finset.sum_le_sum (fun k _ => ?_)).trans (hC ξ K)
  rw [norm_muSym_eq]

/-! ## Continuity and essential boundedness of the symbols -/

lemma continuous_dyadTilde : Continuous dyadTilde := by
  have h : dyadTilde = fun ξ : ℝ => dyadTheta (ξ / 2) := rfl
  rw [h]
  exact (dyadTheta_spec.1.continuous).comp (continuous_id.div_const 2)

lemma continuous_tildeFam (m : ℤ) : Continuous (tildeFam m) := by
  have h : tildeFam m = fun ξ : ℝ => ((dyadTilde ((2:ℝ)^m * ξ) : ℝ) : ℂ) := rfl
  rw [h]
  exact Complex.continuous_ofReal.comp
    (continuous_dyadTilde.comp (continuous_const.mul continuous_id))

lemma continuous_psiFam (m : ℤ) : Continuous (psiFam m) := by
  have h : psiFam m = fun ξ : ℝ => ((dyadPsi ((2:ℝ)^m * ξ) : ℝ) : ℂ) := rfl
  rw [h]
  exact Complex.continuous_ofReal.comp
    (continuous_dyadPsi.comp (continuous_const.mul continuous_id))

lemma continuous_mtaBlkSym (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) :
    Continuous (mtaBlkSym P K ε s) := by
  have h : mtaBlkSym P K ε s = fun ξ : ℝ => ∑ k ∈ Finset.range K,
      ε k * (tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ *
        psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ) * muSym P k ξ := rfl
  rw [h]
  exact continuous_finsetSum (s := Finset.range K) (fun k _ =>
    ((continuous_const.mul ((continuous_tildeFam _).mul (continuous_psiFam _))).mul
      (continuous_muSym P k)))

lemma continuous_mtaFullSym (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) :
    Continuous (mtaFullSym P K ε) := by
  have h : mtaFullSym P K ε = fun ξ : ℝ => ∑ k ∈ Finset.range K,
      ε k * muSym P k ξ := rfl
  rw [h]
  exact continuous_finsetSum (s := Finset.range K) (fun k _ =>
    continuous_const.mul (continuous_muSym P k))

lemma memLp_mtaBlkSym (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) (s : ℤ) :
    MemLp (mtaBlkSym P K ε s) ⊤ (volume : Measure ℝ) := by
  obtain ⟨Bt, hBt0, hBt⟩ := dyadTilde_abs_bound
  obtain ⟨Bp, _hBp0, hBp⟩ := dyadPsi_abs_bound
  refine memLp_top_of_bound' (continuous_mtaBlkSym P K ε s).aestronglyMeasurable
    (∑ k ∈ Finset.range K, (‖ε k‖ * (Bt * Bp)) * 2) (fun ξ => ?_)
  rw [mtaBlkSym]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  have h1 : ‖tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ‖ ≤ Bt := by
    rw [show tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ
        = ((dyadTilde ((2:ℝ)^((P.natDegree : ℤ) * (k : ℤ) + s) * ξ) : ℝ) : ℂ) from rfl,
      Complex.norm_real, Real.norm_eq_abs]
    exact hBt _
  have h2 : ‖psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ‖ ≤ Bp := by
    rw [show psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ
        = ((dyadPsi ((2:ℝ)^((P.natDegree : ℤ) * (k : ℤ) + s) * ξ) : ℝ) : ℂ) from rfl,
      Complex.norm_real, Real.norm_eq_abs]
    exact hBp _
  have h4 : ‖tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ *
      psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ‖ ≤ Bt * Bp := by
    rw [norm_mul]; exact mul_le_mul h1 h2 (norm_nonneg _) hBt0
  calc ‖ε k * (tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ *
        psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ) * muSym P k ξ‖
      = ‖ε k‖ * ‖tildeFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ *
          psiFam ((P.natDegree : ℤ) * (k : ℤ) + s) ξ‖ * ‖muSym P k ξ‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ ‖ε k‖ * (Bt * Bp) * 2 := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h4 (norm_nonneg _)) (norm_muSym_le_two P k ξ)
          (norm_nonneg _) ?_
        positivity
    _ = (‖ε k‖ * (Bt * Bp)) * 2 := rfl

lemma memLp_mtaFullSym (P : Polynomial ℤ) (K : ℕ) (ε : ℕ → ℂ) :
    MemLp (mtaFullSym P K ε) ⊤ (volume : Measure ℝ) := by
  refine memLp_top_of_bound' (continuous_mtaFullSym P K ε).aestronglyMeasurable
    (∑ k ∈ Finset.range K, ‖ε k‖ * 2) (fun ξ => ?_)
  rw [mtaFullSym]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_muSym_le_two P k ξ) (norm_nonneg _)

end

end Work.BourgainPlan.Maximal
