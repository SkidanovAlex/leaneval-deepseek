import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.BourgainPlan.Maximal.mst_lvl_approx_pointwise
import Submission.Work.BourgainPlan.Maximal.mst_err1_opmul_coeff
import Submission.Work.BourgainPlan.Maximal.mst_minor_per_n
import Submission.Work.BourgainPlan.Maximal.mst_lvl_err_aux
import Submission.Work.BourgainPlan.Maximal.mstFreeze_arc_coeff_bound
import Submission.Work.BourgainPlan.Maximal.lvlErrCls_coeff_arc
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs
import Submission.Work.BourgainPlan.Maximal.mstTht_deriv_bounds
import Submission.Work.BourgainPlan.Maximal.mstHat_decay_of_contDiff
import Submission.Work.BourgainPlan.Maximal.mstHat_dilate_eq
import Submission.Work.BourgainPlan.Maximal.mstHat_bound
import Submission.Work.BourgainPlan.Maximal.mst_freeze_small
import Submission.Work.BourgainPlan.Maximal.lattice_shift_inv_sq_bound
import Submission.Work.BourgainPlan.Maximal.mstU_card_le_exp
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.polyKernelZDefs

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The exponent comparison: `(s+1)^{1/10} ≤ √(s+1)/4` for `s + 1 ≥ 32`. -/
lemma rpow_ten_add_one_le_sqrt_div (s : ℕ) (hs : 32 ≤ s + 1) :
    ((s : ℝ) + 1) ^ (1 / 10 : ℝ) ≤ Real.sqrt ((s : ℝ) + 1) / 4 := by
  have hx : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have h32 : (32 : ℝ) ≤ (s : ℝ) + 1 := by exact_mod_cast hs
  have hsplit : ((s : ℝ) + 1) ^ (1 / 10 : ℝ)
      = ((s : ℝ) + 1) ^ (1 / 2 : ℝ) * ((s : ℝ) + 1) ^ (-(2 / 5) : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [hsplit, Real.sqrt_eq_rpow]
  have h1 : ((s : ℝ) + 1) ^ (-(2 / 5) : ℝ) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) = (32 : ℝ) ^ (2 / 5 : ℝ) := by
      rw [show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, ← Real.rpow_natCast (2 : ℝ) 5,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc ((s : ℝ) + 1) ^ (-(2 / 5) : ℝ) ≤ (32 : ℝ) ^ (-(2 / 5) : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) h32 (by norm_num)
      _ = 1 / 4 := by
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 32), h4]
          norm_num
  calc ((s : ℝ) + 1) ^ (1 / 2 : ℝ) * ((s : ℝ) + 1) ^ (-(2 / 5) : ℝ)
      ≤ ((s : ℝ) + 1) ^ (1 / 2 : ℝ) * (1 / 4) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx.le _)
    _ = ((s : ℝ) + 1) ^ (1 / 2 : ℝ) / 4 := by ring


/-- Interchanging a finite sum over a `Finset` of circles with a summable `ℤ`-series: the `ℓ¹`-norms
of a finite family of coefficient kernels add up, and their total mass is the sum of the masses. -/
lemma lvlErr_summable_finset_tsum_swap {T : Finset Circ} {f : Circ → ℤ → ℝ}
    (hf : ∀ β ∈ T, Summable (fun m : ℤ => f β m)) :
    Summable (fun m : ℤ => ∑ β ∈ T, f β m) ∧
      (∑' m : ℤ, ∑ β ∈ T, f β m) = ∑ β ∈ T, ∑' m : ℤ, f β m := by
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨by simpa using (summable_zero : Summable (fun _ : ℤ => (0 : ℝ))), ?_⟩
      simp
  | insert a u ha ih =>
      have ha' : Summable (fun m : ℤ => f a m) := hf a (Finset.mem_insert_self a u)
      have hu' : ∀ β ∈ u, Summable (fun m : ℤ => f β m) :=
        fun β hβ => hf β (Finset.mem_insert_of_mem hβ)
      obtain ⟨hsum_u, hsplit_u⟩ := ih hu'
      have hfun : (fun m : ℤ => ∑ β ∈ insert a u, f β m)
          = fun m : ℤ => f a m + ∑ β ∈ u, f β m := by
        funext m; rw [Finset.sum_insert ha]
      refine ⟨by rw [hfun]; exact ha'.add hsum_u, ?_⟩
      rw [hfun, ha'.tsum_add hsum_u, Finset.sum_insert ha, hsplit_u]

/-- **The `ℓ¹` coefficient bound of the level-`s` freezing error, from the per-arc estimate.**
Given the number-theoretic input that the single-arc coefficient kernel
`m ↦ arcCoeff P l d χ η J s k β m` has `ℓ¹`-norm at most `C₁ exp(-√(s+1)/2)` for every arc
`β ∈ 𝒰(s+1)` (`hper`), and the coefficient identity of the level-error class (`hcoeff`), the
absolute coefficient kernel of the whole error `ν^s_{2^k} - m_J • Π^s_{2^k}` is summable with
`ℓ¹`-norm at most `C exp(-√(s+1)/4)`: the subexponential cardinality `♯𝒰(s+1) = e^{O((s+1)^{1/10})}`
of the annulus is absorbed by the exponential gain. -/
lemma lvlErrCls_tsum_le_of_arc (P : Polynomial ℤ) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (η : ℝ → ℂ)
    (hcoeff : ∀ (s k J : ℕ)
      (hML : MemLp (mstNuS P l P.natDegree χ η k s) ⊤ haarT)
      (hηml : MemLp (mstEta P.natDegree χ η s) ⊤ haarT) (m : ℤ),
      (∫ ξ : Circ, (((mstNuSCls P l P.natDegree χ η k s hML
          - khatZMult P J • mstPiCls P l P.natDegree χ η s hηml (2 ^ k) :
          Lp ℂ ⊤ haarT)) : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT)
        = ∑ β ∈ mstLevel l (s + 1) \ mstLevel l s,
            arcCoeff P l P.natDegree χ η J s k β m)
    (hper : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ s₁ : ℕ, ∀ s : ℕ, s₁ ≤ s → ∀ k : ℕ, ∀ β ∈ mstU l (s + 1),
      Summable (fun m : ℤ => ‖arcCoeff P l P.natDegree χ η
          (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) s k β m‖) ∧
      (∑' m : ℤ, ‖arcCoeff P l P.natDegree χ η
          (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) s k β m‖)
        ≤ C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ,
      ∀ (hML : MemLp (mstNuS P l P.natDegree χ η k s) ⊤ haarT)
        (hηml : MemLp (mstEta P.natDegree χ η s) ⊤ haarT),
      Summable (fun m : ℤ => ‖∫ ξ : Circ,
          (((mstNuSCls P l P.natDegree χ η k s hML
            - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • mstPiCls P l P.natDegree χ η s hηml (2 ^ k) : Lp ℂ ⊤ haarT)) : Circ → ℂ) ξ
            * star (fourier m ξ) ∂haarT‖) ∧
      (∑' m : ℤ, ‖∫ ξ : Circ,
          (((mstNuSCls P l P.natDegree χ η k s hML
            - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • mstPiCls P l P.natDegree χ η s hηml (2 ^ k) : Lp ℂ ⊤ haarT)) : Circ → ℂ) ξ
            * star (fourier m ξ) ∂haarT‖)
        ≤ C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)) := by
  obtain ⟨C₁, hC₁, s₁, hper⟩ := hper
  obtain ⟨Cc, hCc, hcard⟩ := mstU_card_le_exp l hl
  refine ⟨C₁ * Cc, mul_pos hC₁ hCc, max (max s₁ 1) 32, fun s hs k hML hηml => ?_⟩
  have hs1 : s₁ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs32 : 32 ≤ s := le_trans (le_max_right (max s₁ 1) 32) hs
  set J : ℕ := ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ with hJ
  set Es : Finset Circ := mstLevel l (s + 1) \ mstLevel l s with hEs
  set Φ : Lp ℂ ⊤ haarT := mstNuSCls P l P.natDegree χ η k s hML
    - khatZMult P J • mstPiCls P l P.natDegree χ η s hηml (2 ^ k) with hΦ
  have hcoeff' : ∀ m : ℤ, (∫ ξ : Circ, (Φ : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT)
      = ∑ β ∈ Es, arcCoeff P l P.natDegree χ η J s k β m := by
    intro m
    rw [hΦ, hEs, hJ]
    exact hcoeff s k J hML hηml m
  have hperβ : ∀ β ∈ Es, Summable (fun m : ℤ => ‖arcCoeff P l P.natDegree χ η J s k β m‖) ∧
      (∑' m : ℤ, ‖arcCoeff P l P.natDegree χ η J s k β m‖)
        ≤ C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
    intro β hβmem
    have hbU : β ∈ mstU l (s + 1) := by
      rw [← mstLevel_succ l s]
      exact (Finset.mem_sdiff.mp (hEs ▸ hβmem)).1
    exact hper s hs1 k β hbU
  haveI : Nonempty Circ := ⟨0⟩
  have hpair' := lvlErr_summable_finset_tsum_swap (T := Es)
    (f := fun β m => ‖arcCoeff P l P.natDegree χ η J s k β m‖)
    (fun β hβ => (hperβ β hβ).1)
  have hsum_all : Summable (fun m : ℤ => ∑ β ∈ Es, ‖arcCoeff P l P.natDegree χ η J s k β m‖) :=
    hpair'.1
  have hKle : ∀ m : ℤ, ‖∫ ξ : Circ, (Φ : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT‖
      ≤ ∑ β ∈ Es, ‖arcCoeff P l P.natDegree χ η J s k β m‖ := by
    intro m
    rw [hcoeff' m]
    exact norm_sum_le _ _
  have hsumK : Summable (fun m : ℤ =>
      ‖∫ ξ : Circ, (Φ : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hKle hsum_all
  refine ⟨?_, ?_⟩
  · rw [hΦ]
    exact hsumK
  · rw [hΦ]
    have hcard' : ((Es.card : ℕ) : ℝ) ≤ Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
      have hsub : Es ⊆ mstU l (s + 1) := by
        intro β hβmem
        rw [← mstLevel_succ l s]
        exact (Finset.mem_sdiff.mp (hEs ▸ hβmem)).1
      calc (((Es.card : ℕ)) : ℝ) ≤ ((mstU l (s + 1)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ Cc * Real.exp (((((s + 1 : ℕ)) : ℝ) ^ l) ^ (mstRho l)) := hcard (s + 1)
        _ = Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)) := by
            have hpoweq : ((((s + 1) ^ l : ℕ) : ℝ)) ^ (mstRho l)
                = ((s : ℝ) + 1) ^ (1 / 10 : ℝ) := by
              have h2 := mstRho_pow_eq l hl (s + 1) (by omega : 1 ≤ s + 1)
              simpa only [Nat.cast_add, Nat.cast_one] using h2
            rw [← Nat.cast_pow (α := ℝ), hpoweq]
    calc (∑' m : ℤ, ‖∫ ξ : Circ, (Φ : Circ → ℂ) ξ * star (fourier m ξ) ∂haarT‖)
        ≤ ∑' m : ℤ, ∑ β ∈ Es, ‖arcCoeff P l P.natDegree χ η J s k β m‖ :=
          Summable.tsum_le_tsum hKle hsumK hsum_all
      _ = ∑ β ∈ Es, ∑' m : ℤ, ‖arcCoeff P l P.natDegree χ η J s k β m‖ :=
          hpair'.2
      _ ≤ ∑ β ∈ Es, C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) :=
          Finset.sum_le_sum (fun β hβ => (hperβ β hβ).2)
      _ = (Es.card : ℝ) * (C₁ * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (C₁ * (Es.card : ℝ)) * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by ring
      _ ≤ (C₁ * (Cc * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))))
            * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard' hC₁.le) (by positivity)
      _ = (C₁ * Cc) * (Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ))
            * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) := by ring
      _ = (C₁ * Cc) * Real.exp (((s : ℝ) + 1) ^ (1 / 10 : ℝ)
            - Real.sqrt ((s : ℝ) + 1) / 2) := by
          rw [← Real.exp_add]; ring
      _ ≤ (C₁ * Cc) * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC₁.le hCc.le)
          have h32 : 32 ≤ s + 1 := by omega
          linarith [rpow_ten_add_one_le_sqrt_div s h32]


/-- **The level error `ν^s_{2^k} - m_J • Π^s_{2^k}` is an `ℓᵖ`-contraction up to
`exp(-√(s+1)/4)`** (MST Theorem 7, step (i), arXiv:1512.07518 §4.4 eqs. (99)–(101)). -/
theorem mst_lvl_err (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    {p : ℝ} (hp : 1 < p)
    (hML : ∀ n s : ℕ, MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η n s) ⊤
      (AddCircle.haarAddCircle (T := 1)))
    (hηml : ∀ s : ℕ, MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ, ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => Work.BourgainPlan.Maximal.opMulFinsuppLM
          (Work.BourgainPlan.Maximal.mstNuSCls P l P.natDegree χ η k s (hML k s)
            - Work.BourgainPlan.Maximal.khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • Work.BourgainPlan.Maximal.mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) g m)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 4)))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  obtain ⟨C₁, hC₁, s₁, hper⟩ :=
    mstFreeze_arc_coeff_bound P hd hc l hl hχ0 hχ1 η M hM hηc hηbd hη0 hder1 hder2
  obtain ⟨C₀, hC₀, s₀, hbound⟩ :=
    lvlErrCls_tsum_le_of_arc P l hl (χ := χ) η
      (fun s k J hML hηml m =>
        lvlErrCls_coeff_arc P l P.natDegree χ η J k s M hηbd hML hηml m)
      ⟨C₁, hC₁, s₁, hper⟩
  refine ⟨C₀, hC₀, s₀, fun s hs k g => ?_⟩
  obtain ⟨hsum, hle⟩ := hbound s hs k (hML k s) (hηml s)
  have hker : ∀ m : ℤ, (∫ ξ : Circ,
        ((((mstNuSCls P l P.natDegree χ η k s (hML k s)
            - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k) : Lp ℂ ⊤ haarT)) :
            Circ → ℂ) ξ * star (fourier m ξ)) ∂haarT)
      = (fun m : ℤ => ∫ ξ : Circ,
        ((((mstNuSCls P l P.natDegree χ η k s (hML k s)
            - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
              • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k) : Lp ℂ ⊤ haarT)) :
            Circ → ℂ) ξ * star (fourier m ξ)) ∂haarT) m :=
    fun m => rfl
  have hmain := mst_err1_opmul_coeff (p := p) (le_of_lt hp)
    (Φ := mstNuSCls P l P.natDegree χ η k s (hML k s)
      - khatZMult P (⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊)
        • mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ k)) hsum hker hle (⇑g)
    (memℓp_finsupp g)
  rw [opMulFinsuppLM_apply]
  exact hmain

end

end Work.BourgainPlan.Maximal
