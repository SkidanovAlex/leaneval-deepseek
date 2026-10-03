import Mathlib
import Submission.Work.KMTAreas.A7.SmallModDefs
import Submission.Work.KMTAreas.A7.BilinOpKhalf
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.A7.ModelApproxCore_kernelComp
import Submission.Work.KMTAreas.A7.FpieceEqTmLq
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphiNt
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt
import Submission.Work.KMTAreas.A7.tmKernel_varphitildeNt_decay
import Submission.Work.KMTAreas.A7.varphiNt_IW_facts
import Submission.Work.KMTPlan.A6.tsum_norm_kernComp_le

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar Work.KMTContract Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-! ## §1. The rescaled cutoff as a multiplication -/

/-- `etaCut η k θ = η (θ * 2^{-k})`: the rescaling `θ / 2^k` (integer power) is the multiplication
by the real power `2^{-k}`. -/
theorem smr_etaCut_eq (η : ℝ → ℂ) (k : ℤ) (θ : ℝ) :
    etaCut η k θ = η (θ * (2 : ℝ) ^ (-(k : ℝ))) := by
  rw [etaCut, div_eq_mul_inv]
  congr 1
  rw [← Real.rpow_intCast (2 : ℝ) k, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-! ## §2. The bumps of the §6 model operator vs. the piece symbols -/

/-- The §6 bump `varphiN N k` (real rescalings) is the piece symbol `pieceSymF k N` (integer
rescalings). -/
theorem smr_varphiN_eq_pieceSymF (N k : ℕ) : varphiN N k = pieceSymF k N := by
  funext ξ
  rw [varphiN, pieceSymF]
  by_cases h : k = 0
  · rw [if_pos h, if_pos h]
    beta_reduce
    rw [smr_etaCut_eq]
    rw [show -((((-(Work.Analysis.EndVar.logN N)) : ℤ) : ℝ))
        = (Work.Analysis.EndVar.logN N : ℝ) from by push_cast; ring]
    exact congrArg kmtEta (mul_comm _ _)
  · rw [if_neg h, if_neg h]
    beta_reduce
    rw [smr_etaCut_eq, smr_etaCut_eq]
    have h1 : -((((-(Work.Analysis.EndVar.logN N) + (k : ℤ)) : ℤ) : ℝ))
        = (Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) := by push_cast; ring
    have h2 : -((((-(Work.Analysis.EndVar.logN N) + (k : ℤ) - 1 : ℤ)) : ℝ))
        = (Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1 := by push_cast; ring
    rw [h1, h2]
    have e1 : kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) * ξ)
        = kmtEta (ξ * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) :=
      congrArg kmtEta (mul_comm _ _)
    have e2 : kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) * ξ)
        = kmtEta (ξ * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) :=
      congrArg kmtEta (mul_comm _ _)
    rw [e1, e2]

/-- The second §6 bump `varphitildeN d N k` (real rescalings) is the piece symbol
`pieceSymG (d : ℤ) k N`. -/
theorem smr_varphitildeN_eq_pieceSymG (d N k : ℕ) :
    varphitildeN d N k = pieceSymG (d : ℤ) k N := by
  funext ξ
  rw [varphitildeN, pieceSymG]
  by_cases h : k = 0
  · rw [if_pos h, if_pos h]
    beta_reduce
    rw [smr_etaCut_eq]
    rw [show -(((((-((d : ℤ) * Work.Analysis.EndVar.logN N)) : ℤ)) : ℝ))
        = (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ) from by push_cast; ring]
    exact congrArg kmtEta (mul_comm _ _)
  · rw [if_neg h, if_neg h]
    beta_reduce
    rw [smr_etaCut_eq, smr_etaCut_eq]
    have h1 : -(((((d : ℤ) * (-(Work.Analysis.EndVar.logN N) + (k : ℤ))) : ℤ) : ℝ))
        = (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) := by push_cast; ring
    have h2 : -(((((d : ℤ) * (-(Work.Analysis.EndVar.logN N) + (k : ℤ) - 1)) : ℤ) : ℝ))
        = (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1) := by push_cast; ring
    rw [h1, h2]
    have e1 : kmtEta ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
        = kmtEta (ξ * (2 : ℝ) ^ ((d : ℝ) *
            ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) :=
      congrArg kmtEta (mul_comm _ _)
    have e2 : kmtEta ((2 : ℝ) ^ ((d : ℝ) *
          ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ)
        = kmtEta (ξ * (2 : ℝ) ^ ((d : ℝ) *
            ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))) :=
      congrArg kmtEta (mul_comm _ _)
    rw [e1, e2]

/-! ## §3. `Tm` as a convolution -/

/-- The §6 exact-height multiplier is the convolution with the kernel `tmKernel`. -/
theorem smr_Tm_eq_convOp (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (u : ℤ → ℂ) :
    Tm ρ l φ u = convOp (tmKernel ρ l φ) u := by
  funext n
  simp only [Tm, convOp, iwConv_apply, tmKernel, smul_eq_mul]

/-! ## §4. `ℓ¹` facts -/

/-- The kernel `khalf m P` of the halved average has finite support, hence is in `ℓ¹(ℤ²)`. -/
theorem smr_summable_khalf (m : ℕ) (P : ℤ[X]) :
    Summable (fun p : ℤ × ℤ => ‖khalf m P p.1 p.2‖) := by
  refine summable_of_ne_finset_zero
    (s := (Finset.Icc (m / 2 + 1) m).image (fun n : ℕ => ((n : ℤ), P.eval (n : ℤ)))) ?_
  rintro ⟨a, b⟩ hp
  rw [khalf]
  by_cases hc : (m / 2 : ℤ) < a ∧ a ≤ (m : ℤ) ∧ b = P.eval a
  · rw [if_pos hc]
    exfalso
    apply hp
    obtain ⟨h1, h2, h3⟩ := hc
    have ha0 : 0 ≤ a := by
      have hm0 : (0 : ℤ) ≤ (m / 2 : ℤ) :=
        Int.ediv_nonneg (Int.natCast_nonneg m) (by norm_num)
      linarith
    refine Finset.mem_image.mpr ⟨a.toNat, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · have h1' : m / 2 < a.toNat := by
          rw [← Int.ofNat_lt, Int.toNat_of_nonneg ha0]; exact h1
        omega
      · rw [← Int.ofNat_le, Int.toNat_of_nonneg ha0]; exact h2
    · rw [Prod.mk.injEq]
      exact ⟨Int.toNat_of_nonneg ha0, by rw [Int.toNat_of_nonneg ha0]; exact h3.symm⟩
  · rw [if_neg hc]
    simp

/-- The kernel of the exact-height multiplier of the bump `varphiN N k` decays like `j^{-2}`. -/
theorem smr_decay_varphiN (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖tmKernel ρ l (varphiN N k) j‖ ≤ C / (1 + |(j : ℝ)|)^2 := by
  set S : ℝ := max (∫ y, ‖varphiN N k y‖) (∫ y, ‖iteratedDeriv 2 (varphiN N k) y‖) with hS
  have hSnn : 0 ≤ S := le_max_of_le_left (integral_nonneg (fun y => norm_nonneg _))
  have h1 : (∫ y, ‖varphiN N k y‖) ≤ S := le_max_left _ _
  have h2 : (∫ y, ‖iteratedDeriv 2 (varphiN N k) y‖) ≤ S := le_max_right _ _
  have hCpos : 0 < 4 * (((diffFreqs ρ l).card : ℝ) * S) + 1 := by positivity
  refine ⟨4 * (((diffFreqs ρ l).card : ℝ) * S) + 1, hCpos, fun j => ?_⟩
  have h := iwKernel_decay_of_bump (diffFreqs ρ l) (contDiff_varphiN N k)
    (hasCompactSupport_varphiN N k) hSnn h1 h2 j
  rw [norm_kmtKernWeight, mul_one_div] at h
  simpa only [tmKernel] using h

/-- The kernel of the exact-height multiplier of the second bump `varphitildeN d N k` decays like
`j^{-2}`. -/
theorem smr_decay_varphitildeN (ρ : ℝ) (l d N k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℤ,
      ‖tmKernel ρ l (varphitildeN d N k) j‖ ≤ C / (1 + |(j : ℝ)|)^2 := by
  set S : ℝ := max (∫ y, ‖varphitildeN d N k y‖)
    (∫ y, ‖iteratedDeriv 2 (varphitildeN d N k) y‖) with hS
  have hSnn : 0 ≤ S := le_max_of_le_left (integral_nonneg (fun y => norm_nonneg _))
  have h1 : (∫ y, ‖varphitildeN d N k y‖) ≤ S := le_max_left _ _
  have h2 : (∫ y, ‖iteratedDeriv 2 (varphitildeN d N k) y‖) ≤ S := le_max_right _ _
  have hCpos : 0 < 4 * (((diffFreqs ρ l).card : ℝ) * S) + 1 := by positivity
  refine ⟨4 * (((diffFreqs ρ l).card : ℝ) * S) + 1, hCpos, fun j => ?_⟩
  have h := iwKernel_decay_of_bump (diffFreqs ρ l) (contDiff_varphitildeN d N k)
    (hasCompactSupport_varphitildeN d N k) hSnn h1 h2 j
  rw [norm_kmtKernWeight, mul_one_div] at h
  simpa only [tmKernel] using h

theorem smr_summable_tmKernel_varphiN (ρ : ℝ) (l N k : ℕ) :
    Summable (fun j : ℤ => ‖tmKernel ρ l (varphiN N k) j‖) := by
  obtain ⟨C, _hC, hdec⟩ := smr_decay_varphiN ρ l N k
  exact Work.KMTContract.kernel_l1_of_decay hdec

theorem smr_summable_tmKernel_varphitildeN (ρ : ℝ) (l d N k : ℕ) :
    Summable (fun j : ℤ => ‖tmKernel ρ l (varphitildeN d N k) j‖) := by
  obtain ⟨C, _hC, hdec⟩ := smr_decay_varphitildeN ρ l d N k
  exact Work.KMTContract.kernel_l1_of_decay hdec

/-! ## §5. The §5 pieces as `convOp`s -/

theorem smr_Fpiece_eq (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l k N : ℕ) {f : ℤ → ℂ}
    (hf : Work.KMTAreas.A5.BoundedZ f) :
    Fpiece (kmtPj ρ) 0 l ((k : ℕ) : ℤ) N f = convOp (tmKernel ρ l (varphiN N k)) f := by
  rw [FpieceEqTm_of_bounded hρ hρ1 l k N f hf.choose_spec, smr_Tm_eq_convOp,
    ← smr_varphiN_eq_pieceSymF N k]

theorem smr_Gpiece_eq (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d l k N : ℕ) {g : ℤ → ℂ}
    (hg : Work.KMTAreas.A5.BoundedZ g) :
    Gpiece (kmtPj ρ) ((d : ℕ) : ℤ) 0 l ((k : ℕ) : ℤ) N g
      = convOp (tmKernel ρ l (varphitildeN d N k)) g := by
  rw [GpieceEqTm_of_bounded hρ hρ1 (d : ℤ) l k N g hg.choose_spec, smr_Tm_eq_convOp,
    ← smr_varphitildeN_eq_pieceSymG d N k]

/-! ## §6. The concrete half of the target -/

/-- **The concrete half of `Work.KMTAreas.A7.smallModReduction`**: the §5 column `varpPiece` is
the bilinear convolution operator with the kernel `smallKconc`.

`varpPiece = AhalfR (Fpiece f) (Gpiece g)` is `bilinOp (khalf ⌊N⌋ P)` of the two pieces
(`Work.KMTAreas.A7.BilinOpKhalf`), each piece is `convOp (tmKernel ρ l (bump))` (§5 above), and
composing a bilinear convolution with two linear convolutions is `kernComp`
(`Work.A7.ModelApproxCore_kernelComp`) --- which is the definition of `smallKconc`. -/
theorem smr_varpPiece_eq_bilinOp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) (a : ℕ → ℝ≥0)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (hf : Work.KMTAreas.A5.BoundedZ f)
    (hg : Work.KMTAreas.A5.BoundedZ g) :
    varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂
      = bilinOp (smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n))) f g := by
  have hK := smr_summable_khalf (Nat.floor (a n)) P
  have hκ := smr_summable_tmKernel_varphiN ρ l₁ (Nat.floor (a n)) k₁
  have hκ' := smr_summable_tmKernel_varphitildeN ρ l₂ P.natDegree (Nat.floor (a n)) k₂
  funext x
  rw [varpPiece, BilinOpKhalf, smr_Fpiece_eq ρ hρ hρ1 l₁ k₁ (Nat.floor (a n)) hf,
    smr_Gpiece_eq ρ hρ hρ1 P.natDegree l₂ k₂ (Nat.floor (a n)) hg,
    ← Work.A7.ModelApproxCore_kernelComp (K := khalf (Nat.floor (a n)) P)
      (κ := tmKernel ρ l₁ (varphiN (Nat.floor (a n)) k₁))
      (κ' := tmKernel ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) k₂))
      (u := f) (v := g) (Cu := hf.choose) (Cv := hg.choose) hK hκ hκ'
      hf.choose_spec hg.choose_spec x]
  rfl

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar Work.KMTContract Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-! ## §1. The arithmetic kernel of the §6 model operator -/

/-- The composition kernel of the §6 model operator: the arithmetic symbol times the two
coefficient kernels `cw m_*` of the tensor factors. -/
noncomputable def smrKbaseX (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun a b => smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ a b
    * cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) a
    * cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) b

/-- `‖m_Ẑ‖ ≤ 1` (an average of `q` unimodular terms). -/
theorem smr_norm_mZ_le (P : ℤ[X]) (q : ℕ) (hq : 0 < q) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) :
    ‖mZ P q α₁ α₂‖ ≤ 1 := by
  rw [mZ, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range q,
      fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ ≤ (q : ℝ) := by
    calc ‖∑ n ∈ Finset.range q,
          fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
        ≤ ∑ n ∈ Finset.range q,
            ‖fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖ :=
          norm_sum_le _ _
      _ = ∑ _n ∈ Finset.range q, (1 : ℝ) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe, mul_one]
      _ = (q : ℝ) := by simp
  calc ((q : ℝ))⁻¹ * ‖∑ n ∈ Finset.range q,
        fourier (T := 1) (n : ℤ) α₁ * fourier (T := 1) (P.eval (n : ℤ)) α₂‖
      ≤ ((q : ℝ))⁻¹ * (q : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = 1 := by rw [inv_mul_cancel₀ (by exact_mod_cast hq.ne')]

/-- The arithmetic kernel of the exact-height §6 symbol is bounded by the product of the
cardinalities of the two frequency sets. -/
theorem smr_norm_smallArithKernel_le (ρ : ℝ) (P : ℤ[X]) (q l₁ l₂ : ℕ) (hq : 0 < q)
    (j₁ j₂ : ℤ) :
    ‖smallArithKernel ρ P q l₁ l₂ j₁ j₂‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
  rw [smallArithKernel]
  calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
        mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖
      ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        norm_sum_le _ _
    _ ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          ‖mZ P q α₁ α₂ * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂‖ :=
        Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun α₁ _ => Finset.sum_le_sum (fun α₂ _ => ?_))
        rw [norm_mul, norm_mul, fourier_apply, fourier_apply, Circle.norm_coe, Circle.norm_coe,
          mul_one, mul_one]
        exact smr_norm_mZ_le P q hq α₁ α₂
    _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- The composition kernel `smrKbaseX` of the §6 model operator is in `ℓ¹(ℤ²)`. -/
theorem smr_summable_smrKbaseX (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ k₁ k₂ : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) := by
  obtain ⟨C₁, _hC₁, hdec₁⟩ := cw_etaCut_decay (-(2 * (uScale ρ (smallL l₁ l₂ k₁ k₂) : ℤ)))
  obtain ⟨C₂, _hC₂, hdec₂⟩ :=
    cw_etaCut_decay (-((P.natDegree : ℤ) * 2 * (uScale ρ (smallL l₁ l₂ k₁ k₂) : ℤ)))
  have hdec₁' : ∀ j : ℤ, ‖cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) j‖
      ≤ C₁ / (1 + |(j : ℝ)|) ^ 2 := fun j => by simpa only [mStarF] using hdec₁ j
  have hdec₂' : ∀ j : ℤ, ‖cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) j‖
      ≤ C₂ / (1 + |(j : ℝ)|) ^ 2 := fun j => by simpa only [mStargF] using hdec₂ j
  have h₁ : Summable (fun j : ℤ => ‖cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) j‖) :=
    Work.KMTContract.kernel_l1_of_decay hdec₁'
  have h₂ : Summable (fun j : ℤ => ‖cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) j‖) :=
    Work.KMTContract.kernel_l1_of_decay hdec₂'
  have hprod : Summable (fun p : ℤ × ℤ =>
      ‖cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.1‖
        * ‖cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.2‖) :=
    Summable.mul_of_nonneg h₁ h₂ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hcard : (0 : ℝ) ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_)
    (hprod.mul_left (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)))
  have hkb := smr_norm_smallArithKernel_le ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂
    (arithQ_pos ρ _) p.1 p.2
  rw [smrKbaseX, norm_mul, norm_mul]
  calc ‖smallArithKernel ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖
        * ‖cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.1‖
        * ‖cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.2‖
      ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ))
        * ‖cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.1‖
        * ‖cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.2‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkb (norm_nonneg _))
          (norm_nonneg _)
    _ = (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ))
        * (‖cw (mStarF (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.1‖
          * ‖cw (mStargF P.natDegree (uScale ρ (smallL l₁ l₂ k₁ k₂))) p.2‖) := by ring

/-! ## §2. Uniform `ℓ¹` bounds for the two kernels -/

/-- From a `t`-uniform quadratic decay bound, the `ℓ¹` mass bound. -/
theorem smr_l1_of_weight_decay {κ : ℤ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ j : ℤ, ‖κ j‖ ≤ C * ‖kmtKernWeight j‖) :
    Summable (fun j : ℤ => ‖κ j‖) ∧ (∑' j : ℤ, ‖κ j‖) ≤ C * (∑' j : ℤ, ‖kmtKernWeight j‖) := by
  have hsum : Summable (fun j : ℤ => ‖κ j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) h (summable_kmtKernWeight.mul_left C)
  refine ⟨hsum, ?_⟩
  calc (∑' j : ℤ, ‖κ j‖) ≤ ∑' j : ℤ, C * ‖kmtKernWeight j‖ :=
        Summable.tsum_le_tsum h hsum (summable_kmtKernWeight.mul_left C)
    _ = C * (∑' j : ℤ, ‖kmtKernWeight j‖) := tsum_mul_left

theorem smr_weight_decay_varphiNt (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖tmKernel ρ l (varphiNt N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨R, S, hSnn, hB⟩ := varphiNt_bounds N k
  refine ⟨4 * ((diffFreqs ρ l).card * S) + 1, ?_, fun t ht j => ?_⟩
  · have : (0 : ℝ) ≤ ((diffFreqs ρ l).card : ℝ) * S := mul_nonneg (Nat.cast_nonneg _) hSnn
    linarith
  · obtain ⟨_, hcd, hcs, h1, h2⟩ := hB t ht
    simpa only [tmKernel] using iwKernel_decay_of_bump (diffFreqs ρ l) hcd hcs hSnn h1 h2 j

theorem smr_weight_decay_varphitildeNt (P : Polynomial ℤ) (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖tmKernel ρ l (varphitildeNt P P.natDegree N k t) j‖ ≤ C * ‖kmtKernWeight j‖ := by
  obtain ⟨C, hCpos, hdec⟩ := tmKernel_varphitildeNt_decay P ρ l N k
  refine ⟨C, hCpos.le, fun t ht j => ?_⟩
  rw [norm_kmtKernWeight, mul_one_div]
  simpa only [tmKernel] using hdec t ht j

theorem smr_uniform_varphiNt (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      Summable (fun j : ℤ => ‖tmKernel ρ l (varphiNt N k t) j‖) ∧
      (∑' j : ℤ, ‖tmKernel ρ l (varphiNt N k t) j‖) ≤ C := by
  obtain ⟨C₀, hC₀, hdec⟩ := smr_weight_decay_varphiNt ρ l N k
  refine ⟨C₀ * (∑' j : ℤ, ‖kmtKernWeight j‖),
    mul_nonneg hC₀ (tsum_nonneg (fun j => norm_nonneg _)), fun t ht => ?_⟩
  exact smr_l1_of_weight_decay hC₀ (fun j => hdec t ht j)

theorem smr_uniform_varphitildeNt (P : Polynomial ℤ) (ρ : ℝ) (l N k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      Summable (fun j : ℤ => ‖tmKernel ρ l (varphitildeNt P P.natDegree N k t) j‖) ∧
      (∑' j : ℤ, ‖tmKernel ρ l (varphitildeNt P P.natDegree N k t) j‖) ≤ C := by
  obtain ⟨C₀, hC₀, hdec⟩ := smr_weight_decay_varphitildeNt P ρ l N k
  refine ⟨C₀ * (∑' j : ℤ, ‖kmtKernWeight j‖),
    mul_nonneg hC₀ (tsum_nonneg (fun j => norm_nonneg _)), fun t ht => ?_⟩
  exact smr_l1_of_weight_decay hC₀ (fun j => hdec t ht j)

/-! ## §3. Measurability in `t` of the kernel coefficients -/

theorem smr_measurable_tmKernel_varphiNt (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => tmKernel ρ l (varphiNt N k t) j) := by
  by_cases hl : l = 0
  · subst hl
    have hgoal : (fun t : ℝ => tmKernel ρ 0 (varphiNt N k t) j)
        = fun t : ℝ => iwKernel (iwSymbolSet (iwArithFreqs ρ 0)
            (periodize (varphiNt N k t))) j := rfl
    rw [hgoal]
    exact measurable_iwKernel_varphiNt ρ 0 N k j
  · have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
      iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
    have hgoal : (fun t : ℝ => tmKernel ρ l (varphiNt N k t) j)
        = fun t : ℝ =>
            iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (varphiNt N k t))) j
              - iwKernel (iwSymbolSet (iwArithFreqs ρ (l - 1))
                  (periodize (varphiNt N k t))) j := by
      funext t
      simp only [tmKernel, diffFreqs, if_neg hl]
      exact iwKernel_iwSymbolSet_sdiff hsub (varphiNt_IW_facts ρ l N k t).1
        (varphiNt_IW_facts ρ (l - 1) N k t).1 j
    rw [hgoal]
    exact (measurable_iwKernel_varphiNt ρ l N k j).sub
      (measurable_iwKernel_varphiNt ρ (l - 1) N k j)

/-- The modulated second bump is bounded by `2` (a difference of two cutoffs bounded by `1`). -/
theorem smr_norm_varphitildeN_le_two (d N k : ℕ) (x : ℝ) : ‖varphitildeN d N k x‖ ≤ 2 := by
  rw [varphitildeN]
  split_ifs with hk
  · exact le_trans (norm_kmtEta_le _) (by norm_num)
  · calc ‖kmtEta _ - kmtEta _‖ ≤ ‖kmtEta _‖ + ‖kmtEta _‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (norm_kmtEta_le _) (norm_kmtEta_le _)
      _ = 2 := by norm_num

theorem smr_integrable_iwSymbolSet_varphitildeNt (ρ : ℝ) (P : Polynomial ℤ) (l N k : ℕ)
    (t : ℝ) :
    Integrable (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (varphitildeNt P P.natDegree N k t))) circleMeasure := by
  have hmeas : Measurable (varphitildeNt P P.natDegree N k t) := by
    have h1 : Measurable (varphitildeN P.natDegree N k) :=
      (contDiff_varphitildeN P.natDegree N k).continuous.measurable
    have h2 : Measurable (fun ξ : ℝ => ee (PevalR P ((N : ℝ) * t) * ξ)) :=
      (contDiff_ee_const_mul 2 (PevalR P ((N : ℝ) * t))).continuous.measurable
    show Measurable fun ξ : ℝ =>
      varphitildeN P.natDegree N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)
    exact h1.mul h2
  obtain ⟨R₀, hR₀⟩ :=
    exists_abs_le_of_hasCompactSupport (hasCompactSupport_varphitildeN P.natDegree N k)
  refine (memLp_iwSymbolSet (iwArithFreqs ρ l)
    (memLp_periodize hmeas (R := max R₀ 0) (C := 2) (le_max_right R₀ 0) ?_ ?_)).integrable le_top
  · intro x hx
    have hx' : R₀ < |x| := lt_of_le_of_lt (le_max_left R₀ 0) hx
    rw [varphitildeNt, hR₀ x (le_of_lt hx'), zero_mul]
  · intro x
    rw [varphitildeNt, norm_mul, norm_ee, mul_one]
    exact smr_norm_varphitildeN_le_two P.natDegree N k x

theorem smr_measurable_tmKernel_varphitildeNt (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (l N k : ℕ) (j : ℤ) :
    Measurable (fun t : ℝ => tmKernel ρ l (varphitildeNt P P.natDegree N k t) j) := by
  by_cases hl : l = 0
  · subst hl
    have hgoal : (fun t : ℝ => tmKernel ρ 0 (varphitildeNt P P.natDegree N k t) j)
        = fun t : ℝ => iwKernel (iwSymbolSet (iwArithFreqs ρ 0)
            (periodize (varphitildeNt P P.natDegree N k t))) j := rfl
    rw [hgoal]
    exact measurable_iwKernel_varphitildeNt P ρ 0 N k j
  · have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
      iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
    have hgoal : (fun t : ℝ => tmKernel ρ l (varphitildeNt P P.natDegree N k t) j)
        = fun t : ℝ =>
            iwKernel (iwSymbolSet (iwArithFreqs ρ l)
                (periodize (varphitildeNt P P.natDegree N k t))) j
              - iwKernel (iwSymbolSet (iwArithFreqs ρ (l - 1))
                  (periodize (varphitildeNt P P.natDegree N k t))) j := by
      funext t
      simp only [tmKernel, diffFreqs, if_neg hl]
      exact iwKernel_iwSymbolSet_sdiff hsub
        (smr_integrable_iwSymbolSet_varphitildeNt ρ P l N k t)
        (smr_integrable_iwSymbolSet_varphitildeNt ρ P (l - 1) N k t) j
    rw [hgoal]
    exact (measurable_iwKernel_varphitildeNt P ρ l N k j).sub
      (measurable_iwKernel_varphitildeNt P ρ (l - 1) N k j)

/-! ## §4. `bilinOp` is additive in its kernel -/

theorem smr_summable_mul_of_kernel {K : ℤ → ℤ → ℂ} {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu)
    (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (x : ℤ) :
    Summable fun p : ℤ × ℤ => K p.1 p.2 * u (x - p.1) * v (x - p.2) := by
  have hCu : 0 ≤ Cu := le_trans (norm_nonneg _) (hu 0)
  have hCv : 0 ≤ Cv := le_trans (norm_nonneg _) (hv 0)
  refine Summable.of_norm_bounded (hK.mul_right (Cu * Cv)) (fun p => ?_)
  rw [norm_mul, norm_mul]
  have h1 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ ≤ ‖K p.1 p.2‖ * Cu :=
    mul_le_mul_of_nonneg_left (hu _) (norm_nonneg _)
  have h2 : ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv :=
    mul_le_mul h1 (hv _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) hCu)
  calc ‖K p.1 p.2‖ * ‖u (x - p.1)‖ * ‖v (x - p.2)‖ ≤ ‖K p.1 p.2‖ * Cu * Cv := h2
    _ = ‖K p.1 p.2‖ * (Cu * Cv) := by ring

theorem smr_bilinOp_sub {K L : ℤ → ℤ → ℂ} {u v : ℤ → ℂ} {Cu Cv : ℝ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hL : Summable fun p : ℤ × ℤ => ‖L p.1 p.2‖)
    (hu : ∀ y : ℤ, ‖u y‖ ≤ Cu) (hv : ∀ y : ℤ, ‖v y‖ ≤ Cv) (x : ℤ) :
    bilinOp (fun a b => K a b - L a b) u v x = bilinOp K u v x - bilinOp L u v x := by
  have hsumK := smr_summable_mul_of_kernel hK hu hv x
  have hsumL := smr_summable_mul_of_kernel hL hu hv x
  have hD : Summable fun p : ℤ × ℤ => ‖K p.1 p.2 - L p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => norm_sub_le _ _) (hK.add hL)
  rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hD hu hv x,
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hK hu hv x,
    Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum hL hu hv x,
    ← Summable.tsum_sub hsumK hsumL]
  exact tsum_congr fun p => by ring

/-! ## §5. The model operator as the `t`-integral of a bilinear convolution -/

theorem smr_smallModelOp_eq (ρ : ℝ) (P : ℤ[X]) (N l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) :
    smallModelOp ρ P N l₁ l₂ k₁ k₂ f g
      = fun x : ℤ => ∫ t in (1/2 : ℝ)..1, bilinOp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
          (convOp (tmKernel ρ l₁ (varphiNt N k₁ t)) f)
          (convOp (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) g) x := by
  funext x
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [smallModelOp, smallBtwist, smrKbaseX, bilinOp, smr_Tm_eq_convOp]

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar Work.KMTContract Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-! ## §1. Measurability of the composed kernel -/

theorem smr_measurable_kernComp {K : ℤ → ℤ → ℂ} {κ κ' : ℝ → ℤ → ℂ}
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) (hκ' : ∀ j : ℤ, Measurable fun t : ℝ => κ' t j)
    (a b : ℤ) :
    Measurable fun t : ℝ => kernComp K (κ t) (κ' t) a b := by
  unfold kernComp
  refine Measurable.tsum (fun a' => ?_)
  refine Measurable.tsum (fun b' => ?_)
  exact (measurable_const.mul (hκ a')).mul (hκ' b')

/-! ## §2. A Tonelli conversion -/

/-- If the `ℝ≥0∞`-valued sum of the integrals of the norms is finite, then the real-valued
integrals of the norms are summable. -/
theorem smr_summable_integral_norm_of_tsum_lintegral_ne_topB {ι : Type*} [Countable ι]
    {μ : Measure ℝ} {φ : ι → ℝ → ℂ}
    (hint : ∀ i, Integrable (fun x : ℝ => ‖φ i x‖) μ)
    (hfin : (∑' i : ι, ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ) ≠ ⊤) :
    Summable (fun i : ι => ∫ x : ℝ, ‖φ i x‖ ∂μ) := by
  have hterm : ∀ i : ι, (∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ) ≠ ⊤ :=
    fun i => ne_top_of_le_ne_top hfin (ENNReal.le_tsum (f := fun i : ι => ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ) i)
  have hnn : ∀ i : ι, 0 ≤ ∫ x : ℝ, ‖φ i x‖ ∂μ :=
    fun i => integral_nonneg fun x => norm_nonneg _
  have hofReal : ∀ i : ι,
      ENNReal.ofReal (∫ x : ℝ, ‖φ i x‖ ∂μ) = ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ := by
    intro i
    simpa only [ofReal_norm] using
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint i)
        (Filter.Eventually.of_forall (fun x => norm_nonneg _))
  have hcoe : ∀ i : ι, (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ≥0∞)
      = ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ := by
    intro i
    rw [Real.toNNReal_of_nonneg (hnn i), ← ENNReal.ofReal_eq_coe_nnreal (hnn i), hofReal i]
  have hsum : (∑' i : ι, (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
    rw [show (∑' i : ι, (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ≥0∞))
        = ∑' i : ι, ∫⁻ x : ℝ, ‖φ i x‖ₑ ∂μ from tsum_congr hcoe]
    exact hfin
  have h1 : Summable (fun i : ι => (∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal) :=
    ENNReal.tsum_coe_ne_top_iff_summable.mp hsum
  have h2 : Summable (fun i : ι => (((∫ x : ℝ, ‖φ i x‖ ∂μ).toNNReal : ℝ≥0) : ℝ)) :=
    NNReal.summable_coe.mpr h1
  exact h2.congr (fun i => Real.coe_toNNReal _ (hnn i))

/-! ## §3. The `ℓ¹` mass of `smallKmod` -/

theorem smr_summable_smallKmod (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X])
    (l₁ l₂ k₁ k₂ N : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖smallKmod ρ P l₁ l₂ k₁ k₂ N p.1 p.2‖) := by
  obtain ⟨B₁, hB₁nn, hB₁⟩ := smr_uniform_varphiNt ρ l₁ N k₁
  obtain ⟨B₂, hB₂nn, hB₂⟩ := smr_uniform_varphitildeNt P ρ l₂ N k₂
  have hKsumm := smr_summable_smrKbaseX ρ P l₁ l₂ k₁ k₂
  have hBKnn : (0 : ℝ) ≤ ∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ :=
    tsum_nonneg (fun p => norm_nonneg _)
  have hmκ : ∀ j : ℤ, Measurable (fun t : ℝ => tmKernel ρ l₁ (varphiNt N k₁ t) j) :=
    fun j => smr_measurable_tmKernel_varphiNt ρ hρ hρ1 l₁ N k₁ j
  have hmκ' : ∀ j : ℤ,
      Measurable (fun t : ℝ => tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) j) :=
    fun j => smr_measurable_tmKernel_varphitildeNt ρ hρ hρ1 P l₂ N k₂ j
  have hmeasp : ∀ p : ℤ × ℤ, Measurable (fun t : ℝ => kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
      (tmKernel ρ l₁ (varphiNt N k₁ t))
      (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2) :=
    fun p => smr_measurable_kernComp hmκ hmκ' p.1 p.2
  -- summability of the composed kernel, uniformly in `t`
  have hsmk : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Summable (fun p : ℤ × ℤ => ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
        (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖) := by
    intro t ht
    have htI : t ∈ Set.Icc (1 / 2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    exact Work.A7.ModelApproxCore_aux.summable_kernComp hKsumm (hB₁ t htI).1 (hB₂ t htI).1
  -- the `t`-uniform mass bound of the composed kernel
  have hmass : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      (∑' p : ℤ × ℤ, ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
        (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖)
        ≤ (∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂ := by
    intro t ht
    have htI : t ∈ Set.Icc (1 / 2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    refine (Work.KMTPlan.A6.tsum_norm_kernComp_le hKsumm (hB₁ t htI).1 (hB₂ t htI).1).trans ?_
    have h0 : (0 : ℝ) ≤ ∑' j : ℤ, ‖tmKernel ρ l₁ (varphiNt N k₁ t) j‖ :=
      tsum_nonneg (fun j => norm_nonneg _)
    have h0' : (0 : ℝ) ≤ ∑' j : ℤ,
        ‖tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) j‖ :=
      tsum_nonneg (fun j => norm_nonneg _)
    exact mul_le_mul (mul_le_mul le_rfl (hB₁ t htI).2 h0 hBKnn) (hB₂ t htI).2 h0'
      (mul_nonneg hBKnn hB₁nn)
  have hconst : (0 : ℝ) ≤ (∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂ :=
    mul_nonneg (mul_nonneg hBKnn hB₁nn) hB₂nn
  have hpt : ∀ (t : ℝ), t ∈ Set.Ioc (1 / 2 : ℝ) 1 → ∀ p : ℤ × ℤ,
      ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
        (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖
        ≤ (∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂ := by
    intro t ht p
    exact le_trans (Summable.le_tsum (hsmk t ht) p (fun q _ => norm_nonneg _)) (hmass t ht)
  -- integrability of the norms
  have hint : ∀ p : ℤ × ℤ, Integrable (fun t : ℝ => ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
      (tmKernel ρ l₁ (varphiNt N k₁ t))
      (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖)
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro p
    refine Integrable.of_bound ((hmeasp p).norm).aestronglyMeasurable
      ((∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hpt t ht p
  -- the a.e. bound on the `ℝ≥0∞`-valued sum
  have hbound_ae : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      (∑' p : ℤ × ℤ, ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
        (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖ₑ)
      ≤ ENNReal.ofReal ((∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr ?_
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have h1 : (∑' p : ℤ × ℤ, ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
        (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖ₑ)
        = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
            (tmKernel ρ l₁ (varphiNt N k₁ t))
            (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun p => norm_nonneg _) (hsmk t ht)]
      exact tsum_congr (fun p => (ofReal_norm _).symm)
    rw [h1]
    exact ENNReal.ofReal_le_ofReal (hmass t ht)
  -- finiteness of the `ℝ≥0∞`-valued Tonelli sum
  have hfin : (∑' p : ℤ × ℤ, ∫⁻ t in Set.Ioc (1 / 2 : ℝ) 1, ‖kernComp
        (smrKbaseX ρ P l₁ l₂ k₁ k₂) (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖ₑ) ≠ ⊤ := by
    rw [← MeasureTheory.lintegral_tsum (fun p => ((hmeasp p).enorm).aemeasurable)]
    have h2 : (∫⁻ t : ℝ, ∑' p : ℤ × ℤ, ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
          (tmKernel ρ l₁ (varphiNt N k₁ t))
          (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖ₑ
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        ≤ ∫⁻ _t : ℝ, ENNReal.ofReal
            ((∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
      MeasureTheory.lintegral_mono_ae hbound_ae
    refine ne_top_of_le_ne_top ?_ h2
    rw [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- summability of the integrals, and comparison with `smallKmod`
  have hsumint := smr_summable_integral_norm_of_tsum_lintegral_ne_topB hint hfin
  refine Summable.of_norm_bounded hsumint (fun p => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [smallKmod]
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  exact norm_integral_le_integral_norm _

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar Work.KMTContract Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

theorem smr_integral_bilinOp_comm (Kt : ℝ → ℤ → ℤ → ℂ) (f g : ℤ → ℂ) {Cf Cg C : ℝ}
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hKt : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable (fun p : ℤ × ℤ => ‖Kt t p.1 p.2‖))
    (hKtmeas : ∀ p : ℤ × ℤ, AEMeasurable (fun t : ℝ => Kt t p.1 p.2) volume)
    (hKtmass : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, (∑' p : ℤ × ℤ, ‖Kt t p.1 p.2‖) ≤ C)
    (hC : 0 ≤ C) (x : ℤ) :
    (∫ t in (1 / 2 : ℝ)..1, bilinOp (Kt t) f g x)
      = bilinOp (fun a b : ℤ => ∫ t in (1 / 2 : ℝ)..1, Kt t a b) f g x := by
  classical
  have h12 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hae_mem : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      t ∈ Set.Ioc (1 / 2 : ℝ) 1 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun t ht => ht))
  have hbnd : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      (∑' p : ℤ × ℤ, ‖Kt t p.1 p.2‖ₑ) ≤ ENNReal.ofReal C := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun t ht => ?_))
    have h1 : (∑' p : ℤ × ℤ, ‖Kt t p.1 p.2‖ₑ)
        = ∑' p : ℤ × ℤ, ENNReal.ofReal ‖Kt t p.1 p.2‖ :=
      tsum_congr (fun p => (ofReal_norm _).symm)
    rw [h1, ← ENNReal.ofReal_tsum_of_nonneg (f := fun p : ℤ × ℤ => ‖Kt t p.1 p.2‖)
      (fun p => norm_nonneg _) (hKt t ht)]
    exact ENNReal.ofReal_le_ofReal (hKtmass t ht)
  have hGint : ∀ p : ℤ × ℤ, Integrable (fun t : ℝ => ‖Kt t p.1 p.2‖)
      (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro p
    refine Integrable.of_bound (f := fun t : ℝ => ‖Kt t p.1 p.2‖)
      ((hKtmeas p).norm.aestronglyMeasurable.restrict) C ?_
    filter_upwards [hae_mem] with t ht
    have h := (Summable.le_tsum (hKt t ht) p (fun q _ => norm_nonneg _)).trans (hKtmass t ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
  have hfin : (∑' p : ℤ × ℤ, ∫⁻ t : ℝ, ‖Kt t p.1 p.2‖ₑ
      ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) ≠ ⊤ := by
    rw [← MeasureTheory.lintegral_tsum
      (μ := volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) (f := fun p t => ‖Kt t p.1 p.2‖ₑ)
      (fun p => ((hKtmeas p).enorm).mono_measure MeasureTheory.Measure.restrict_le_self)]
    have h2 : (∫⁻ t : ℝ, ∑' p : ℤ × ℤ, ‖Kt t p.1 p.2‖ₑ
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) ≤ ENNReal.ofReal C := by
      calc ∫⁻ t : ℝ, ∑' p : ℤ × ℤ, ‖Kt t p.1 p.2‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
        ≤ ∫⁻ _t : ℝ, ENNReal.ofReal C
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
          MeasureTheory.lintegral_mono_ae hbnd
      _ = ENNReal.ofReal C * (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) Set.univ :=
          MeasureTheory.lintegral_const _
      _ = ENNReal.ofReal C * ENNReal.ofReal (1 / 2) := by
          rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            Real.volume_Ioc]
          norm_num
      _ = ENNReal.ofReal (C * (1 / 2)) := (ENNReal.ofReal_mul hC).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by nlinarith)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  have hsum_norm : Summable (fun p : ℤ × ℤ =>
      ∫ t : ℝ, ‖Kt t p.1 p.2‖ ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) :=
    smr_summable_integral_norm_of_tsum_lintegral_ne_topB (ι := ℤ × ℤ)
      (φ := fun p t => Kt t p.1 p.2) hGint hfin
  have hK' : Summable (fun p : ℤ × ℤ =>
      ‖∫ t in (1 / 2 : ℝ)..1, Kt t p.1 p.2‖) := by
    have h1 : Summable (fun p : ℤ × ℤ =>
        ‖∫ t : ℝ, Kt t p.1 p.2 ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))‖) :=
      Summable.of_nonneg_of_le (fun p => norm_nonneg _)
        (fun p => MeasureTheory.norm_integral_le_integral_norm (fun t : ℝ => Kt t p.1 p.2))
        hsum_norm
    exact h1.congr (fun p => by
      rw [intervalIntegral.integral_of_le (f := fun t : ℝ => Kt t p.1 p.2) h12])
  have hF_meas : ∀ p : ℤ × ℤ,
      AEStronglyMeasurable (fun t : ℝ => Kt t p.1 p.2 * f (x - p.1) * g (x - p.2))
        (volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    intro p
    have h : AEMeasurable (fun t : ℝ => Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)) volume :=
      ((hKtmeas p).mul aemeasurable_const).mul aemeasurable_const
    exact h.aestronglyMeasurable.restrict
  have hFmass : ∀ p : ℤ × ℤ,
      ∫⁻ t : ℝ, ‖Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
        ≤ (∫⁻ t : ℝ, ‖Kt t p.1 p.2‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * ENNReal.ofReal (Cf * Cg) := by
    intro p
    have h1 : ‖f (x - p.1)‖ₑ ≤ ENNReal.ofReal Cf := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hf _)
    have h2 : ‖g (x - p.2)‖ₑ ≤ ENNReal.ofReal Cg := by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hg _)
    calc ∫⁻ t : ℝ, ‖Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
        ≤ ∫⁻ t : ℝ, ‖Kt t p.1 p.2‖ₑ * ENNReal.ofReal (Cf * Cg)
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
          refine MeasureTheory.lintegral_mono (fun t => ?_)
          rw [enorm_mul, enorm_mul]
          calc ‖Kt t p.1 p.2‖ₑ * ‖f (x - p.1)‖ₑ * ‖g (x - p.2)‖ₑ
              ≤ ‖Kt t p.1 p.2‖ₑ * ENNReal.ofReal Cf * ENNReal.ofReal Cg :=
                mul_le_mul' (mul_le_mul' le_rfl h1) h2
            _ = ‖Kt t p.1 p.2‖ₑ * ENNReal.ofReal (Cf * Cg) := by
                rw [mul_assoc, ← ENNReal.ofReal_mul hCf]
      _ = (∫⁻ t : ℝ, ‖Kt t p.1 p.2‖ₑ ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
            * ENNReal.ofReal (Cf * Cg) :=
          MeasureTheory.lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
  have hfinF : (∑' p : ℤ × ℤ,
      ∫⁻ t : ℝ, ‖Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) ≠ ⊤ := by
    have h2 : (∑' p : ℤ × ℤ, ∫⁻ t : ℝ,
            ‖Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        ≤ (∑' p : ℤ × ℤ, ∫⁻ t : ℝ, ‖Kt t p.1 p.2‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * ENNReal.ofReal (Cf * Cg) := by
      calc (∑' p : ℤ × ℤ, ∫⁻ t : ℝ,
            ‖Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)‖ₑ
            ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        ≤ ∑' p : ℤ × ℤ, (∫⁻ t : ℝ, ‖Kt t p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * ENNReal.ofReal (Cf * Cg) :=
          ENNReal.tsum_le_tsum hFmass
      _ = (∑' p : ℤ × ℤ, ∫⁻ t : ℝ, ‖Kt t p.1 p.2‖ₑ
              ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))) * ENNReal.ofReal (Cf * Cg) :=
          ENNReal.tsum_mul_right
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hfin ENNReal.ofReal_ne_top) h2
  have hswap : (∫ t : ℝ, ∑' p : ℤ × ℤ,
        Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)
        ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
      = ∑' p : ℤ × ℤ, ∫ t : ℝ, Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) :=
    MeasureTheory.integral_tsum (ι := ℤ × ℤ)
      (μ := volume.restrict (Set.Ioc (1 / 2 : ℝ) 1))
      (f := fun q t => Kt t q.1 q.2 * f (x - q.1) * g (x - q.2)) hF_meas hfinF
  have hpull : ∀ p : ℤ × ℤ,
      (∫ t : ℝ, Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
        = (∫ t : ℝ, Kt t p.1 p.2 ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
            * f (x - p.1) * g (x - p.2) := by
    intro p
    have hcongr : (fun t : ℝ => Kt t p.1 p.2 * f (x - p.1) * g (x - p.2))
        = fun t : ℝ => Kt t p.1 p.2 * (f (x - p.1) * g (x - p.2)) := by
      funext t; ring
    rw [hcongr, MeasureTheory.integral_mul_const, mul_assoc]
  have hLHS : (∫ t in (1 / 2 : ℝ)..1, bilinOp (Kt t) f g x)
      = ∫ t : ℝ, ∑' p : ℤ × ℤ, Kt t p.1 p.2 * f (x - p.1) * g (x - p.2)
          ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)) := by
    rw [intervalIntegral.integral_of_le (f := fun t : ℝ => bilinOp (Kt t) f g x) h12]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae_mem] with t ht
    exact Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := Kt t) (u := f) (v := g)
      (Cu := Cf) (Cv := Cg) (hKt t ht) hf hg x
  have hRHS : bilinOp (fun a b : ℤ => ∫ t in (1 / 2 : ℝ)..1, Kt t a b) f g x
      = ∑' p : ℤ × ℤ,
          (∫ t : ℝ, Kt t p.1 p.2 ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
            * f (x - p.1) * g (x - p.2) := by
    rw [Work.A7.ModelApproxCore_aux.bilinOp_eq_tsum (K := fun a b : ℤ =>
          ∫ t in (1 / 2 : ℝ)..1, Kt t a b) (u := f) (v := g) (Cu := Cf) (Cv := Cg) hK' hf hg x]
    refine tsum_congr (fun p => ?_)
    show (∫ t in (1 / 2 : ℝ)..1, Kt t p.1 p.2) * f (x - p.1) * g (x - p.2)
        = (∫ t : ℝ, Kt t p.1 p.2 ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)))
            * f (x - p.1) * g (x - p.2)
    rw [intervalIntegral.integral_of_le (f := fun t : ℝ => Kt t p.1 p.2) h12]
  exact hLHS.trans (hswap.trans ((tsum_congr hpull).trans hRHS.symm))

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.EndVar Work.KMTContract Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-- Measurability in `t` of the composed kernel, in `AEMeasurable` form. -/
theorem smr_aemeasurable_kernComp {K : ℤ → ℤ → ℂ} {κ κ' : ℝ → ℤ → ℂ}
    (hκ : ∀ j : ℤ, Measurable fun t : ℝ => κ t j) (hκ' : ∀ j : ℤ, Measurable fun t : ℝ => κ' t j)
    (a b : ℤ) :
    AEMeasurable (fun t : ℝ => kernComp K (κ t) (κ' t) a b) volume := by
  have h : Measurable (fun t : ℝ => kernComp K (κ t) (κ' t) a b) := by
    unfold kernComp
    refine Measurable.tsum (fun a' => ?_)
    refine Measurable.tsum (fun b' => ?_)
    exact (measurable_const.mul (hκ a')).mul (hκ' b')
  exact h.aemeasurable

theorem smr_smallModelOp_eq_bilinOp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X])
    (N l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ) (hf : Work.KMTAreas.A5.BoundedZ f)
    (hg : Work.KMTAreas.A5.BoundedZ g) (x : ℤ) :
    smallModelOp ρ P N l₁ l₂ k₁ k₂ f g x
      = bilinOp (smallKmod ρ P l₁ l₂ k₁ k₂ N) f g x := by
  classical
  have h12 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  obtain ⟨B₁, hB₁nn, hB₁⟩ := smr_uniform_varphiNt ρ l₁ N k₁
  obtain ⟨B₂, hB₂nn, hB₂⟩ := smr_uniform_varphitildeNt P ρ l₂ N k₂
  obtain ⟨Cf, hCf'⟩ := hf
  obtain ⟨Cg, hCg'⟩ := hg
  have hCf : 0 ≤ Cf := le_trans (norm_nonneg _) (hCf' 0)
  have hCg : 0 ≤ Cg := le_trans (norm_nonneg _) (hCg' 0)
  have hKsumm : Summable (fun p : ℤ × ℤ => ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) :=
    smr_summable_smrKbaseX ρ P l₁ l₂ k₁ k₂
  have hBKnn : (0 : ℝ) ≤ ∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ :=
    tsum_nonneg (fun p => norm_nonneg _)
  have hmκ : ∀ j : ℤ, Measurable (fun t : ℝ => tmKernel ρ l₁ (varphiNt N k₁ t) j) :=
    fun j => smr_measurable_tmKernel_varphiNt ρ hρ hρ1 l₁ N k₁ j
  have hmκ' : ∀ j : ℤ,
      Measurable (fun t : ℝ => tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) j) :=
    fun j => smr_measurable_tmKernel_varphitildeNt ρ hρ hρ1 P l₂ N k₂ j
  -- the hypotheses of the abstract Fubini step for the composed kernel
  have hKt : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, Summable (fun p : ℤ × ℤ =>
      ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂) (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖) := by
    intro t ht
    have htI : t ∈ Set.Icc (1 / 2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    exact Work.A7.ModelApproxCore_aux.summable_kernComp hKsumm (hB₁ t htI).1 (hB₂ t htI).1
  have hKtmeas : ∀ p : ℤ × ℤ, AEMeasurable (fun t : ℝ =>
      kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂) (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2) volume :=
    fun p => smr_aemeasurable_kernComp hmκ hmκ' p.1 p.2
  have hKtmass : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1, (∑' p : ℤ × ℤ,
      ‖kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂) (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) p.1 p.2‖)
      ≤ (∑' p : ℤ × ℤ, ‖smrKbaseX ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) * B₁ * B₂ := by
    intro t ht
    have htI : t ∈ Set.Icc (1 / 2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    refine (Work.KMTPlan.A6.tsum_norm_kernComp_le hKsumm (hB₁ t htI).1 (hB₂ t htI).1).trans ?_
    have h0 : (0 : ℝ) ≤ ∑' j : ℤ, ‖tmKernel ρ l₁ (varphiNt N k₁ t) j‖ := by
      exact tsum_nonneg (fun _ => norm_nonneg _)
    have h0' : (0 : ℝ) ≤ ∑' j : ℤ,
        ‖tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t) j‖ := by
      exact tsum_nonneg (fun _ => norm_nonneg _)
    exact mul_le_mul (mul_le_mul le_rfl (hB₁ t htI).2 h0 hBKnn) (hB₂ t htI).2 h0'
      (mul_nonneg hBKnn hB₁nn)
  -- the pointwise composition identity for the integrand
  have hpt : ∀ t ∈ Set.Ioc (1 / 2 : ℝ) 1,
      bilinOp (smrKbaseX ρ P l₁ l₂ k₁ k₂) (convOp (tmKernel ρ l₁ (varphiNt N k₁ t)) f)
          (convOp (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) g) x
        = bilinOp (fun a b : ℤ => kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
            (tmKernel ρ l₁ (varphiNt N k₁ t))
            (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) a b) f g x := by
    intro t ht
    have htI : t ∈ Set.Icc (1 / 2 : ℝ) 1 := Set.Ioc_subset_Icc_self ht
    exact (Work.A7.ModelApproxCore_kernelComp (K := smrKbaseX ρ P l₁ l₂ k₁ k₂)
      (κ := tmKernel ρ l₁ (varphiNt N k₁ t))
      (κ' := tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t))
      (u := f) (v := g) (Cu := Cf) (Cv := Cg) hKsumm
      (hB₁ t htI).1 (hB₂ t htI).1 hCf' hCg' x).symm
  have hae_mem : ∀ᵐ t ∂(volume.restrict (Set.Ioc (1 / 2 : ℝ) 1)),
      t ∈ Set.Ioc (1 / 2 : ℝ) 1 :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall (fun t ht => ht))
  rw [smr_smallModelOp_eq ρ P N l₁ l₂ k₁ k₂ f g]
  beta_reduce
  rw [intervalIntegral.integral_of_le (f := fun t : ℝ =>
        bilinOp (smrKbaseX ρ P l₁ l₂ k₁ k₂) (convOp (tmKernel ρ l₁ (varphiNt N k₁ t)) f)
          (convOp (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) g) x) h12]
  rw [MeasureTheory.integral_congr_ae
      (f := fun t : ℝ => bilinOp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
          (convOp (tmKernel ρ l₁ (varphiNt N k₁ t)) f)
          (convOp (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) g) x)
      (g := fun t : ℝ => bilinOp (fun a b : ℤ =>
          kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂) (tmKernel ρ l₁ (varphiNt N k₁ t))
            (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) a b) f g x)
      (by filter_upwards [hae_mem] with t ht; exact hpt t ht)]
  rw [← intervalIntegral.integral_of_le (f := fun t : ℝ => bilinOp (fun a b : ℤ =>
      kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂) (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) a b) f g x) h12]
  rw [smr_integral_bilinOp_comm (Kt := fun t : ℝ => kernComp (smrKbaseX ρ P l₁ l₂ k₁ k₂)
        (tmKernel ρ l₁ (varphiNt N k₁ t))
        (tmKernel ρ l₂ (varphitildeNt P P.natDegree N k₂ t))) f g hCf' hCg' hCf hCg
      hKt hKtmeas hKtmass (mul_nonneg (mul_nonneg hBKnn hB₁nn) hB₂nn) x]
  rfl

end

end Work.KMTAreas.A7

namespace Work.KMTAreas.A7

/-- The concrete kernel `smallKconc` is the composition of the finitely supported kernel `khalf`
with the two absolutely summable exact-height kernels, hence is in `ℓ¹(ℤ²)`. -/
theorem smr_summable_smallKconc (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖smallKconc ρ P l₁ l₂ k₁ k₂ N p.1 p.2‖) :=
  Work.A7.ModelApproxCore_aux.summable_kernComp (smr_summable_khalf N P)
    (smr_summable_tmKernel_varphiN ρ l₁ N k₁)
    (smr_summable_tmKernel_varphitildeN ρ l₂ P.natDegree N k₂)

theorem smallModReduction (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : Work.KMTAreas.A7.smallCond ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (fun x : ℤ => Work.KMTAreas.A7.smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        - Work.KMTAreas.A7.smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      = Work.KMTAreas.A7.bilinOp
          (fun x y : ℤ => Work.KMTAreas.A7.smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y
            - Work.KMTAreas.A7.smallKmod ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)) x y) f g := by
  funext x
  have h1 : smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = bilinOp (smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n))) f g x := by
    rw [show smallMainPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        = Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x from by
      simp only [smallMainPart, if_pos h]]
    exact congrFun (smr_varpPiece_eq_bilinOp ρ hρ hρ1 P a f g l₁ l₂ k₁ k₂ n hf hg) x
  have h2 : smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = bilinOp (smallKmod ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n))) f g x := by
    rw [show smallModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
        = smallModelOp ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ f g x from by
      simp only [smallModelTuple, if_pos h, smallModelOp]]
    exact smr_smallModelOp_eq_bilinOp ρ hρ hρ1 P (Nat.floor (a n)) l₁ l₂ k₁ k₂ f g hf hg x
  rw [h1, h2]
  exact (smr_bilinOp_sub (K := smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)))
    (L := smallKmod ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)))
    (smr_summable_smallKconc ρ P l₁ l₂ k₁ k₂ (Nat.floor (a n)))
    (smr_summable_smallKmod ρ hρ hρ1 P l₁ l₂ k₁ k₂ (Nat.floor (a n)))
    hf.choose_spec hg.choose_spec x).symm

end Work.KMTAreas.A7
