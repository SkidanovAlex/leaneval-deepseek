/-
# The crude `ℓ^p` bound for the exact-height IW multiplier of the randomised small-scale symbol

This module proves `Work.KMTAreas.A7rand.Tm_randSymb_crude_bound`: for `1 < p`, `ρ > 0` and
parameters `C₀, B`, there is a constant `C(Λ)` — depending on the lacunarity parameter `Λ` and
on `ρ, C₀, B, p`, but *uniform* in the lacunary sequence `a`, in the scales `l₁,l₂,k₁,k₂` with
`smallL l₁ l₂ k₁ k₂ ≤ B`, in the sign families `ε`, in the truncation `K`, in `t ∈ [1/2,1]`
and in the input `f` — such that

  `‖ T^{l₁}_{randSymb (smallSymbF …) ε K} f ‖_{ℓ^p(ℤ)} ≤ C(Λ) ‖f‖_{ℓ^p(ℤ)}`.

## The proof

The symbol `σ = randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K` is, by
`Work.KMTAreas.A7.randSymb_eq_activeSum`, a *finite* linear combination
`σ = ∑_{m ∈ A_i} d m · φ_{⌊a m⌋,t}` of the modulated Ionescu--Wainger bumps, where the index set
`A_i` consists of *active* indices `randAct ρ C₀ a l₁ l₂ k₁ k₂ m`; those satisfy, by lacunarity,
`Λ ^ m ≤ a m` together with `Nat.floor (a m) ≤ splitCut ρ (smallL l₁ l₂ k₁ k₂) ≤ M`, so `m` is
bounded by an explicit `Nlim(Λ)` and the scale `⌊a m⌋` by `2 ^ (M + 1)` — with a *single* `M`
chosen from `B` only.  Consequently

* `σ` is `C²` with compact support (`randSymb_contDiff_hasCompactSupport`), and
* its two `L¹` norms `∫‖σ‖`, `∫‖σ''‖` are bounded by `2 · (sup of the bump bounds) · #A_i`
  (`integral_norm_sum_bumps_le`).

The operator `Tm ρ l₁ σ` is the convolution with the Fourier coefficients of
`iwSymbolSet (diffFreqs ρ l₁) (periodize σ)`; `iwKernel_decay_of_bump` gives their quadratic decay
with the explicit constant `4 · (#(diffFreqs ρ l₁) · S) + 1`, and `#(diffFreqs ρ l₁) ≤ #(ℚ/ℤ)_{≤B}`
is bounded by a quantity depending on `ρ, B` only.  Young's inequality for convolution on `ℤ`
(`Work.KMTAreas.A4.offYoung_conv_count_le`) then finishes, giving the crude (gain-free) `ℓ^p` bound
with the constant `C(Λ)`.

This is the "crude" companion of `Work.KMTAreas.A7.randSymb_Tle_crude`: the difference is that the
multiplier here is the *exact-height* one (`diffFreqs ρ l₁` instead of `iwArithFreqs ρ l₁`), that
no Ionescu--Wainger input (`AreaA1`) is used, and that the scale parameter `M` is *derived* from the
hypothesis `smallL l₁ l₂ k₁ k₂ ≤ B` rather than assumed.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbCrudeAux
import Submission.Work.KMTAreas.A7.tsum_norm_iwKernel_le
import Submission.Work.KMTAreas.A7.randSymb_eq_activeSum
import Submission.Work.KMTAreas.A7.integral_norm_sum_bumps_le
import Submission.Work.KMTAreas.A4.offYoung

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7rand

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

theorem Tm_randSymb_crude_bound (p : ℝ) (hp : 1 < p) (ρ : ℝ) (hρ : 0 < ρ) (C₀ B : ℕ) :
    ∃ C : NNReal → NNReal, ∀ (Λ : NNReal) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ)
      (ε : ℕ → ℂ) (f : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ ≤ B →
      t ∈ Set.Icc (1/2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.Tm ρ l₁
          (Work.KMTAreas.A7.randSymb (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f x)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  -- The uniform bound on the scale parameters.  It depends on `ρ` and `B` only, and it dominates
  -- both `B` and the small-scale cut `splitCut ρ L` for every `L ≤ B`.
  let M : ℕ := max B ((Finset.range (B + 1)).sup (fun L => splitCut ρ L))
  -- The uniform bound on the bumps `φ_{N,t}` for `N < 2 ^ (M+1)`, `k ≤ M`, `t ∈ [1/2,1]`.
  let Sall : ℝ := ∑ N ∈ Finset.range (2 ^ (M + 1)), ∑ k ∈ Finset.range (M + 1), bumpS N k
  -- The uniform bound on the cardinality of the exact-height frequency sets.
  let Acard : ℕ := (Finset.range (B + 1)).sup (fun l => (iwArithFreqs ρ l).card)
  -- The comparison weight.
  let Kw : ℝ := ∑' j : ℤ, ‖kmtKernWeight j‖
  -- The bound on the number of active scales, as a function of `Λ`.
  let NlimF : NNReal → ℕ :=
    fun Λ => Nat.floor (((M : ℝ) + 1) * Real.log 2 / Real.log (Λ : ℝ)) + 1
  let SvalF : NNReal → ℝ := fun Λ => 2 * Sall * ((NlimF Λ + 1 : ℕ) : ℝ)
  let Cval : NNReal → ℝ := fun Λ => (4 * ((Acard : ℝ) * SvalF Λ) + 1) * Kw
  have hSall_nonneg : 0 ≤ Sall :=
    Finset.sum_nonneg (fun N _ => Finset.sum_nonneg (fun k _ => bumpS_nonneg N k))
  have hKw_nonneg : 0 ≤ Kw := tsum_nonneg (fun j => norm_nonneg _)
  have hSval_nonneg : ∀ Λ : NNReal, 0 ≤ SvalF Λ := by
    intro Λ
    have hN : (0 : ℝ) ≤ ((NlimF Λ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg (mul_nonneg (by norm_num) hSall_nonneg) hN
  have hCval_nonneg : ∀ Λ : NNReal, 0 ≤ Cval Λ := by
    intro Λ
    have h1 : (0 : ℝ) ≤ 4 * ((Acard : ℝ) * SvalF Λ) + 1 := by
      have hA : (0 : ℝ) ≤ (Acard : ℝ) := Nat.cast_nonneg _
      have hAS : 0 ≤ (Acard : ℝ) * SvalF Λ := mul_nonneg hA (hSval_nonneg Λ)
      linarith
    exact mul_nonneg h1 hKw_nonneg
  let Cfun : NNReal → NNReal := fun Λ => ⟨Cval Λ, hCval_nonneg Λ⟩
  refine ⟨Cfun, ?_⟩
  intro Λ a l₁ l₂ k₁ k₂ K t ε f hΛ ha ha1 hsmallL ht hε
  -- ## The scale parameters are bounded by `M`
  have hBM : B ≤ M := le_max_left _ _
  have hLkB : smallL l₁ l₂ k₁ k₂ ≤ B := hsmallL
  have hl₁B : l₁ ≤ B := le_trans (le_trans (le_max_left l₁ l₂) (le_max_left _ _)) hLkB
  have hk₁B : k₁ ≤ B := le_trans (le_trans (le_max_left k₁ k₂) (le_max_right _ _)) hLkB
  have hk₁M : k₁ ≤ M := le_trans hk₁B hBM
  have hcutM : splitCut ρ (smallL l₁ l₂ k₁ k₂) ≤ M :=
    le_trans (Finset.le_sup (s := Finset.range (B + 1)) (f := fun L => splitCut ρ L)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hLkB))) (le_max_right _ _)
  have hAcard_le : ∀ l : ℕ, l ≤ B → (iwArithFreqs ρ l).card ≤ Acard := by
    intro l hl
    exact Finset.le_sup (s := Finset.range (B + 1)) (f := fun l => (iwArithFreqs ρ l).card)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  -- The exact-height frequency set is a subset of the height-`≤ l₁` one.
  have hdiff_sub : diffFreqs ρ l₁ ⊆ iwArithFreqs ρ l₁ := by
    by_cases h0 : l₁ = 0
    · rw [diffFreqs, if_pos h0, h0]
    · rw [diffFreqs, if_neg h0]
      exact Finset.sdiff_subset
  have hcard_diff : (diffFreqs ρ l₁).card ≤ Acard :=
    le_trans (Finset.card_le_card hdiff_sub) (hAcard_le l₁ hl₁B)
  -- ## The randomised symbol
  let σ : ℝ → ℂ := randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K
  change eLpNorm (fun x : ℤ => Tm ρ l₁ σ f x) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ (Cfun Λ : ENNReal) * eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count
  -- The active indices are bounded, and so are their scales.
  have hindex : ∀ m : ℕ, randAct ρ C₀ a l₁ l₂ k₁ k₂ m →
      m ≤ NlimF Λ ∧ Nat.floor (a m) < 2 ^ (M + 1) := by
    intro m hm
    obtain ⟨-, hsc⟩ := hm
    obtain ⟨-, hcut, -⟩ := hsc
    have hfloorM : Nat.floor (a m) ≤ M := le_trans hcut hcutM
    have hpowself : M < 2 ^ (M + 1) :=
      lt_of_lt_of_le (Nat.lt_succ_self M) (le_of_lt (Nat.lt_two_pow_self (n := M + 1)))
    have hfloorlt : Nat.floor (a m) < 2 ^ (M + 1) := lt_of_le_of_lt hfloorM hpowself
    refine ⟨?_, hfloorlt⟩
    have hpow : (Λ : ℝ) ^ m ≤ (a m : ℝ) := by
      have h := Work.Analysis.EndVar.pow_le_of_lacunary hΛ ha ha1 m
      exact_mod_cast h
    have ham_lt : (a m : ℝ) < (2 : ℝ) ^ (M + 1) := by
      have h1 : (a m : ℝ) < ((Nat.floor (a m) : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((Nat.floor (a m) : ℕ) : ℝ) + 1 ≤ (M : ℝ) + 1 := by
        have : Nat.floor (a m) + 1 ≤ M + 1 := Nat.succ_le_succ hfloorM
        exact_mod_cast this
      have h3 : (M : ℝ) + 1 ≤ (2 : ℝ) ^ (M + 1) := by
        have h4 : M + 1 ≤ 2 ^ (M + 1) := le_of_lt (Nat.lt_two_pow_self (n := M + 1))
        exact_mod_cast h4
      linarith
    have hlt : (Λ : ℝ) ^ m < (2 : ℝ) ^ (M + 1) := lt_of_le_of_lt hpow ham_lt
    have hloglt := Real.log_lt_log (by positivity : (0 : ℝ) < (Λ : ℝ) ^ m) hlt
    rw [Real.log_pow, Real.log_pow] at hloglt
    have hlogΛpos : 0 < Real.log (Λ : ℝ) := Real.log_pos (by exact_mod_cast hΛ)
    have hcast : (((M + 1 : ℕ)) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hloglt
    have hr : (m : ℝ) ≤ ((M : ℝ) + 1) * Real.log 2 / Real.log (Λ : ℝ) := by
      rw [le_div_iff₀ hlogΛpos]
      exact hloglt.le
    rw [show NlimF Λ
      = Nat.floor (((M : ℝ) + 1) * Real.log 2 / Real.log (Λ : ℝ)) + 1 from rfl]
    exact le_trans (Nat.le_floor hr) (Nat.le_succ _)
  let Nlim : ℕ := NlimF Λ
  let Ai : Finset ℕ := (Finset.range (Nlim + 1)).filter (randAct ρ C₀ a l₁ l₂ k₁ k₂)
  -- The symbol as a finite combination of bumps over the active indices.
  have hσid : σ = fun ξ => ∑ m ∈ Ai, randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
      * varphiNt (Nat.floor (a m)) k₁ t ξ :=
    randSymb_eq_activeSum ρ C₀ a l₁ l₂ k₁ k₂ t ε K Nlim (fun m hm => (hindex m hm).1)
  have hcardAi : Ai.card ≤ Nlim + 1 := by
    calc Ai.card ≤ (Finset.range (Nlim + 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = Nlim + 1 := Finset.card_range _
  -- Pointwise and `L¹` bounds for the bumps appearing in the sum.
  have hbump : ∀ m ∈ Ai, ContDiff ℝ 2 (fun ξ => varphiNt (Nat.floor (a m)) k₁ t ξ) ∧
      HasCompactSupport (fun ξ => varphiNt (Nat.floor (a m)) k₁ t ξ) ∧
      (∫ y, ‖varphiNt (Nat.floor (a m)) k₁ t y‖) ≤ Sall ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt (Nat.floor (a m)) k₁ t ξ) y‖) ≤ Sall := by
    intro m hm
    have hmact : randAct ρ C₀ a l₁ l₂ k₁ k₂ m := (Finset.mem_filter.mp hm).2
    have hN : Nat.floor (a m) ∈ Finset.range (2 ^ (M + 1)) :=
      Finset.mem_range.mpr (hindex m hmact).2
    have hk : k₁ ∈ Finset.range (M + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk₁M)
    have h1 : bumpS (Nat.floor (a m)) k₁
        ≤ ∑ k ∈ Finset.range (M + 1), bumpS (Nat.floor (a m)) k :=
      Finset.single_le_sum (fun k _ => bumpS_nonneg _ k) hk
    have h2 : (∑ k ∈ Finset.range (M + 1), bumpS (Nat.floor (a m)) k) ≤ Sall :=
      Finset.single_le_sum (fun N _ => Finset.sum_nonneg (fun k _ => bumpS_nonneg N k)) hN
    have hSle : bumpS (Nat.floor (a m)) k₁ ≤ Sall := h1.trans h2
    have hb := bumpS_spec (Nat.floor (a m)) k₁ t ht
    exact ⟨contDiff_varphiNt _ _ t, hasCompactSupport_varphiNt _ _ t,
      hb.1.trans hSle, hb.2.trans hSle⟩
  have hcoeff : ∀ m : ℕ, ‖randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 2 := by
    intro m
    unfold randCoeff
    by_cases hact : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos hact]
      have h1 : ‖(if m ≤ K then (1 : ℂ) else 0)‖ ≤ 1 := by
        by_cases hK : m ≤ K <;> simp [hK]
      have h2 : ‖(if m < K then (1 : ℂ) else 0)‖ ≤ 1 := by
        by_cases hK : m < K <;> simp [hK]
      calc ‖ε (m - 1) * (if m ≤ K then 1 else 0) - ε m * (if m < K then 1 else 0)‖
          ≤ ‖ε (m - 1) * (if m ≤ K then 1 else 0)‖
            + ‖ε m * (if m < K then 1 else 0)‖ := norm_sub_le _ _
        _ = ‖ε (m - 1)‖ * ‖(if m ≤ K then (1 : ℂ) else 0)‖
            + ‖ε m‖ * ‖(if m < K then (1 : ℂ) else 0)‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 + 1 * 1 := by
            refine add_le_add (mul_le_mul (hε _) h1 (norm_nonneg _) zero_le_one)
              (mul_le_mul (hε _) h2 (norm_nonneg _) zero_le_one)
        _ = 2 := by norm_num
    · rw [if_neg hact, norm_zero]; norm_num
  have hint := integral_norm_sum_bumps_le Ai (randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K)
    (fun m ξ => varphiNt (Nat.floor (a m)) k₁ t ξ) Sall hSall_nonneg hcoeff hbump
  have hcard_le : 2 * Sall * (Ai.card : ℝ) ≤ SvalF Λ := by
    have hc : (Ai.card : ℝ) ≤ ((NlimF Λ + 1 : ℕ) : ℝ) := by
      have : Ai.card ≤ NlimF Λ + 1 := by simpa only [Nlim] using hcardAi
      exact_mod_cast this
    have h2 : (0 : ℝ) ≤ 2 * Sall := mul_nonneg (by norm_num) hSall_nonneg
    exact mul_le_mul_of_nonneg_left hc h2
  have hI1 : (∫ y, ‖σ y‖) ≤ SvalF Λ := by
    have hEq : (∫ y, ‖σ y‖) = ∫ y, ‖∑ m ∈ Ai, randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
        * varphiNt (Nat.floor (a m)) k₁ t y‖ := by rw [hσid]
    rw [hEq]
    exact hint.1.trans hcard_le
  have hI2 : (∫ y, ‖iteratedDeriv 2 σ y‖) ≤ SvalF Λ := by
    have hEq : (∫ y, ‖iteratedDeriv 2 σ y‖) = ∫ y, ‖iteratedDeriv 2 (fun y =>
        ∑ m ∈ Ai, randCoeff ρ C₀ a l₁ l₂ k₁ k₂ ε K m
          * varphiNt (Nat.floor (a m)) k₁ t y) y‖ := by rw [hσid]
    rw [hEq]
    exact hint.2.trans hcard_le
  have hch := randSymb_contDiff_hasCompactSupport ρ C₀ a l₁ l₂ k₁ k₂ t ε K
  have hcd : ContDiff ℝ 2 σ := hch.1
  have hcs : HasCompactSupport σ := hch.2
  -- ## The `ℓ¹` mass of the kernel of the symbol
  have hdec : ∀ j : ℤ, ‖iwKernel (iwSymbolSet (diffFreqs ρ l₁) (periodize σ)) j‖
      ≤ (4 * (((diffFreqs ρ l₁).card : ℝ) * SvalF Λ) + 1) * ‖kmtKernWeight j‖ :=
    iwKernel_decay_of_bump (diffFreqs ρ l₁) hcd hcs (hSval_nonneg Λ) hI1 hI2
  have hκsumm : Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet (diffFreqs ρ l₁) (periodize σ)) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec (summable_kmtKernWeight.mul_left _)
  have hkd := tsum_norm_iwKernel_le (diffFreqs ρ l₁) σ (hSval_nonneg Λ) hcd hcs hI1 hI2
  have hKle : (4 * (((diffFreqs ρ l₁).card : ℝ) * SvalF Λ) + 1) * Kw ≤ Cval Λ := by
    have hcardR : ((diffFreqs ρ l₁).card : ℝ) ≤ (Acard : ℝ) := by exact_mod_cast hcard_diff
    have h1 : ((diffFreqs ρ l₁).card : ℝ) * SvalF Λ ≤ (Acard : ℝ) * SvalF Λ :=
      mul_le_mul_of_nonneg_right hcardR (hSval_nonneg Λ)
    have h3 : 4 * (((diffFreqs ρ l₁).card : ℝ) * SvalF Λ) + 1
        ≤ 4 * ((Acard : ℝ) * SvalF Λ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h3 hKw_nonneg
  have hkey : (fun x : ℤ => Tm ρ l₁ σ f x)
      = fun n : ℤ => ∑' j : ℤ,
          iwKernel (iwSymbolSet (diffFreqs ρ l₁) (periodize σ)) j * f (n - j) := by
    funext n
    simp only [Tm, iwConv_apply, smul_eq_mul]
  -- ## Young's inequality
  calc eLpNorm (fun x : ℤ => Tm ρ l₁ σ f x) (ENNReal.ofReal p) MeasureTheory.Measure.count
      = eLpNorm (fun n : ℤ => ∑' j : ℤ,
          iwKernel (iwSymbolSet (diffFreqs ρ l₁) (periodize σ)) j * f (n - j))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := by rw [hkey]
    _ ≤ (∑' t : ℤ, ENNReal.ofReal
            ‖iwKernel (iwSymbolSet (diffFreqs ρ l₁) (periodize σ)) t‖)
          * eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count :=
        Work.KMTAreas.A4.offYoung_conv_count_le (le_of_lt hp) _ _
    _ = ENNReal.ofReal (∑' t : ℤ,
          ‖iwKernel (iwSymbolSet (diffFreqs ρ l₁) (periodize σ)) t‖)
          * eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hκsumm]
    _ ≤ ENNReal.ofReal (Cval Λ) * eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        exact hkd.trans hKle
    _ = (Cfun Λ : ENNReal) * eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        have hcoe : ((Cfun Λ : NNReal) : ℝ) = Cval Λ := rfl
        have h2 : ENNReal.ofReal (Cval Λ) = (Cfun Λ : ENNReal) := by
          rw [← hcoe, ENNReal.ofReal_coe_nnreal]
        rw [h2]

end

end Work.KMTAreas.A7rand
