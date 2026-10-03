import Mathlib
import Submission.Work.KMTAreas.A7.SmallModDefs
import Submission.Work.KMTAreas.A7.randSymbG_telescope
import Submission.Work.KMTAreas.A7rand.Tm_randSymb_crude_bound
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

noncomputable section

/-! ## Elementary helpers

These mirror the corresponding facts of `Work.KMTAreas.A7.randSymbCrudeAux` (the `f`-side), with
the `g`-side bump family `varphitildeNt` in place of `varphiNt`. -/

/-- A `Λ`-lacunary sequence with `Λ > 1` and values `≥ 1` is increasing.  Needed for the
telescoping identity `randSymbG_telescope`, whose coefficient bound uses that the active indices
form an interval. -/
private lemma lacunary_mono {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h1 : Λ * a n < a (n + 1) := by
    have h2 : Λ < a (n + 1) / a n := ha n
    rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by nlinarith [ha1 n, hΛ]
  exact le_trans h3 h1.le

/-- The uniform-in-`t` `L¹` bounds for the `g`-side modulated bump family at a single scale. -/
private lemma exists_bumpSg (P : Polynomial ℤ) (N k₂ : ℕ) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ContDiff ℝ 2 (fun ξ => varphitildeNt P P.natDegree N k₂ t ξ) ∧
      HasCompactSupport (fun ξ => varphitildeNt P P.natDegree N k₂ t ξ) ∧
      (∫ y, ‖varphitildeNt P P.natDegree N k₂ t y‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNt P P.natDegree N k₂ t ξ) y‖) ≤ S := by
  obtain ⟨S, hS, hspec⟩ := Work.KMTPlan.A6.varphitildeNt_bounds P P.natDegree N k₂
  exact ⟨S, hS, fun t ht => ⟨(hspec t ht).1, (hspec t ht).2.1, (hspec t ht).2.2.1,
    (hspec t ht).2.2.2⟩⟩

/-- The canonical uniform bump bound for the `g`-side bump at scale `N` and exponent `k₂`. -/
private noncomputable def bumpSg (P : Polynomial ℤ) (N k₂ : ℕ) : ℝ :=
  Classical.choose (exists_bumpSg P N k₂)

private lemma bumpSg_nonneg (P : Polynomial ℤ) (N k₂ : ℕ) : 0 ≤ bumpSg P N k₂ :=
  (Classical.choose_spec (exists_bumpSg P N k₂)).1

private lemma bumpSg_full (P : Polynomial ℤ) (N k₂ : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    ContDiff ℝ 2 (fun ξ => varphitildeNt P P.natDegree N k₂ t ξ) ∧
    HasCompactSupport (fun ξ => varphitildeNt P P.natDegree N k₂ t ξ) ∧
    (∫ y, ‖varphitildeNt P P.natDegree N k₂ t y‖) ≤ bumpSg P N k₂ ∧
    (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNt P P.natDegree N k₂ t ξ) y‖) ≤ bumpSg P N k₂ :=
  (Classical.choose_spec (exists_bumpSg P N k₂)).2 t ht

/-- The randomised `g`-side symbol `randSymb (smallSymbG …) ε K` is `C²` with compact support
(the `g`-side counterpart of `randSymb_contDiff_hasCompactSupport`). -/
private lemma randSymbG_contDiff_hasCompactSupport (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ε : ℕ → ℂ) (K : ℕ) :
    ContDiff ℝ 2 (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) ∧
      HasCompactSupport (randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) := by
  have hcd : ∀ m : ℕ, ContDiff ℝ 2 (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m) := by
    intro m
    rw [smallSymbG_apply]
    by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos h]
      exact Work.KMTPlan.A6.contDiff_varphitildeNt_aux P P.natDegree (Nat.floor (a m)) k₂ t
    · rw [if_neg h]
      exact contDiff_const
  have hcs : ∀ m : ℕ, HasCompactSupport (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m) := by
    intro m
    rw [smallSymbG_apply]
    by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos h]
      exact Work.KMTPlan.A6.hasCompactSupport_varphitildeNt_aux P P.natDegree (Nat.floor (a m)) k₂ t
    · rw [if_neg h]
      exact HasCompactSupport.zero
  have hsymb : randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K
      = fun ξ : ℝ => ∑ n ∈ Finset.range K, ε n *
          (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t (n + 1) ξ
            - smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n ξ) := rfl
  constructor
  · rw [hsymb]
    exact ContDiff.sum (fun n _ => (contDiff_const (c := ε n)).mul ((hcd (n + 1)).sub (hcd n)))
  · rw [hsymb]
    refine hasCompactSupport_finsetSum _ _ (fun n _ => ?_)
    exact ((hcs (n + 1)).sub (hcs n)).comp_left (g := fun z : ℂ => ε n * z) (by simp)

/- Mirror of `Work.KMTAreas.A7rand.Tm_randSymb_crude_bound` with the `g`-side bump family
`smallSymbG`/`varphitildeNt` in place of the `f`-side `smallSymbF`/`varphiNt`.  Useful public
inputs: `Work.KMTPlan.A6.varphitildeNt_bounds` (`∃ S ≥ 0, ∀ t ∈ Icc, C² ∧ compact support ∧
∫‖φ̃_{N,t}‖ ≤ S ∧ ∫‖φ̃''_{N,t}‖ ≤ S`), `Work.KMTAreas.A7.randSymbG_telescope`,
`Work.KMTAreas.A7.randAct_index_bound`, `Work.KMTAreas.A7.iwKernel_decay_of_bump`,
`Work.KMTAreas.A7.tsum_norm_iwKernel_le`, `Work.KMTAreas.A4.offYoung_conv_count_le`,
`Work.KMTAreas.A7.integral_norm_sum_bumps_le`, `Work.KMTAreas.A7.SmallModDefs` (`tmKernel`).
Do NOT import `Submission.Work.KMTAreas.A7.SmallKernMassBasics`: that module is currently broken
(duplicate declaration of `tmKernel_varphitildeNt_decay`). -/
theorem Tm_randSymbG_crude_bound (P : Polynomial ℤ) (p : ℝ) (hp : 1 < p) (ρ : ℝ) (hρ : 0 < ρ)
    (C₀ B : ℕ) :
    ∃ C : NNReal → NNReal,
      ∀ (Λ : NNReal) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        Work.KMTAreas.A7.smallL l₁ l₂ k₁ k₂ ≤ B →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (∀ n, ‖ε n‖ ≤ 1) →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.Tm ρ l₂
            (Work.KMTAreas.A7.randSymb
              (Work.KMTAreas.A7.smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g x)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  -- The uniform bound on the scale parameters, depending on `ρ` and `B` only.
  let M : ℕ := max B ((Finset.range (B + 1)).sup (fun L => splitCut ρ L))
  -- The uniform bound on the `g`-side bumps for `N < 2 ^ (M+1)`, `k₂ ≤ M`, `t ∈ [1/2,1]`.
  let Sall : ℝ := ∑ N ∈ Finset.range (2 ^ (M + 1)), ∑ k ∈ Finset.range (M + 1), bumpSg P N k
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
    Finset.sum_nonneg (fun N _ => Finset.sum_nonneg (fun k _ => bumpSg_nonneg P N k))
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
  intro Λ a l₁ l₂ k₁ k₂ K t ε g hΛ ha ha1 hsmallL ht hε
  -- ## The scale parameters are bounded by `M`
  have hBM : B ≤ M := le_max_left _ _
  have hLkB : smallL l₁ l₂ k₁ k₂ ≤ B := hsmallL
  have hl₂B : l₂ ≤ B := le_trans (le_trans (le_max_right l₁ l₂) (le_max_left _ _)) hLkB
  have hk₂B : k₂ ≤ B := le_trans (le_trans (le_max_right k₁ k₂) (le_max_right _ _)) hLkB
  have hk₂M : k₂ ≤ M := le_trans hk₂B hBM
  have hcutM : splitCut ρ (smallL l₁ l₂ k₁ k₂) ≤ M :=
    le_trans (Finset.le_sup (s := Finset.range (B + 1)) (f := fun L => splitCut ρ L)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hLkB))) (le_max_right _ _)
  have hAcard_le : ∀ l : ℕ, l ≤ B → (iwArithFreqs ρ l).card ≤ Acard := by
    intro l hl
    exact Finset.le_sup (s := Finset.range (B + 1)) (f := fun l => (iwArithFreqs ρ l).card)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  -- The exact-height frequency set is a subset of the height-`≤ l₂` one.
  have hdiff_sub : diffFreqs ρ l₂ ⊆ iwArithFreqs ρ l₂ := by
    by_cases h0 : l₂ = 0
    · rw [diffFreqs, if_pos h0, h0]
    · rw [diffFreqs, if_neg h0]
      exact Finset.sdiff_subset
  have hcard_diff : (diffFreqs ρ l₂).card ≤ Acard :=
    le_trans (Finset.card_le_card hdiff_sub) (hAcard_le l₂ hl₂B)
  -- ## The randomised symbol
  let σ : ℝ → ℂ := randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K
  change eLpNorm (fun x : ℤ => Tm ρ l₂ σ g x) (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ (Cfun Λ : ENNReal) * eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count
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
  -- The active index set: the `m ≤ K` with `randAct`.  Its cardinality is bounded by `NlimF Λ + 1`
  -- because every active index is `≤ NlimF Λ`, independently of `K`.
  let Ai : Finset ℕ := (Finset.range (K + 1)).filter (randAct ρ C₀ a l₁ l₂ k₁ k₂)
  have hmono : Monotone a := lacunary_mono hΛ ha ha1
  -- The telescoped identity for the symbol, as a sum over the (finite) active index set.
  have hσid : σ = fun ξ => ∑ m ∈ Ai, randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m
      * varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ := by
    have htel := (randSymbG_telescope ρ P C₀ a l₁ l₂ k₁ k₂ t ε hε hmono K).1
    rw [show σ = randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K from rfl, htel]
    funext ξ
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    unfold randSymbGCoef
    by_cases hm : randAct ρ C₀ a l₁ l₂ k₁ k₂ m <;> simp [hm]
  have hcardAi : Ai.card ≤ NlimF Λ + 1 := by
    have hsub : Ai ⊆ Finset.range (NlimF Λ + 1) := by
      intro m hm
      obtain ⟨-, hmact⟩ := Finset.mem_filter.mp hm
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hindex m hmact).1)
    calc Ai.card ≤ (Finset.range (NlimF Λ + 1)).card := Finset.card_le_card hsub
      _ = NlimF Λ + 1 := Finset.card_range _
  -- Pointwise and `L¹`-bounds for the bumps appearing in the sum.
  have hbump : ∀ m ∈ Ai, ContDiff ℝ 2
        (fun ξ => varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ) ∧
      HasCompactSupport (fun ξ => varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ) ∧
      (∫ y, ‖varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t y‖) ≤ Sall ∧
      (∫ y, ‖iteratedDeriv 2
        (fun ξ => varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ) y‖) ≤ Sall := by
    intro m hm
    have hmact : randAct ρ C₀ a l₁ l₂ k₁ k₂ m := (Finset.mem_filter.mp hm).2
    have hN : Nat.floor (a m) ∈ Finset.range (2 ^ (M + 1)) :=
      Finset.mem_range.mpr (hindex m hmact).2
    have hk : k₂ ∈ Finset.range (M + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk₂M)
    have h1 : bumpSg P (Nat.floor (a m)) k₂
        ≤ ∑ k ∈ Finset.range (M + 1), bumpSg P (Nat.floor (a m)) k :=
      Finset.single_le_sum (fun k _ => bumpSg_nonneg P _ k) hk
    have h2 : (∑ k ∈ Finset.range (M + 1), bumpSg P (Nat.floor (a m)) k) ≤ Sall :=
      Finset.single_le_sum (fun N _ => Finset.sum_nonneg (fun k _ => bumpSg_nonneg P N k)) hN
    have hSle : bumpSg P (Nat.floor (a m)) k₂ ≤ Sall := h1.trans h2
    have hb := bumpSg_full P (Nat.floor (a m)) k₂ t ht
    exact ⟨hb.1, hb.2.1, hb.2.2.1.trans hSle, hb.2.2.2.trans hSle⟩
  have hcoeff : ∀ m : ℕ, ‖randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m‖ ≤ 2 := by
    intro m
    have h1 : ‖(if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0 : ℂ)‖ ≤ 1 := by
      by_cases h : 1 ≤ m ∧ m ≤ K
      · rw [if_pos h]; exact hε (m - 1)
      · rw [if_neg h]; simp
    have h2 : ‖(if m < K then ε m else 0 : ℂ)‖ ≤ 1 := by
      by_cases h : m < K
      · rw [if_pos h]; exact hε m
      · rw [if_neg h]; simp
    have htele : ‖teleCoef ε K m‖ ≤ 2 := by
      rw [teleCoef]
      calc ‖(if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0 : ℂ)
            - (if m < K then ε m else 0 : ℂ)‖
          ≤ ‖(if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0 : ℂ)‖
            + ‖(if m < K then ε m else 0 : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add h1 h2
        _ = 2 := by norm_num
    unfold randSymbGCoef
    by_cases hm : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
    · rw [if_pos hm]; exact htele
    · rw [if_neg hm, norm_zero]; norm_num
  have hint := integral_norm_sum_bumps_le Ai (randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K)
    (fun m ξ => varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ) Sall hSall_nonneg hcoeff hbump
  have hcard_le : 2 * Sall * (Ai.card : ℝ) ≤ SvalF Λ := by
    have hc : (Ai.card : ℝ) ≤ ((NlimF Λ + 1 : ℕ) : ℝ) := by exact_mod_cast hcardAi
    have h2 : (0 : ℝ) ≤ 2 * Sall := mul_nonneg (by norm_num) hSall_nonneg
    have hSval : SvalF Λ = 2 * Sall * ((NlimF Λ + 1 : ℕ) : ℝ) := rfl
    rw [hSval]
    exact mul_le_mul_of_nonneg_left hc h2
  have hI1 : (∫ y, ‖σ y‖) ≤ SvalF Λ := by
    have hEq : (∫ y, ‖σ y‖) = ∫ y, ‖∑ m ∈ Ai, randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m
        * varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t y‖ := by rw [hσid]
    rw [hEq]
    exact hint.1.trans hcard_le
  have hI2 : (∫ y, ‖iteratedDeriv 2 σ y‖) ≤ SvalF Λ := by
    have hEq : (∫ y, ‖iteratedDeriv 2 σ y‖) = ∫ y, ‖iteratedDeriv 2 (fun y =>
        ∑ m ∈ Ai, randSymbGCoef ρ C₀ a l₁ l₂ k₁ k₂ ε K m
          * varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t y) y‖ := by rw [hσid]
    rw [hEq]
    exact hint.2.trans hcard_le
  have hch := randSymbG_contDiff_hasCompactSupport ρ P C₀ a l₁ l₂ k₁ k₂ t ε K
  have hcd : ContDiff ℝ 2 σ := hch.1
  have hcs : HasCompactSupport σ := hch.2
  -- ## The `ℓ¹` mass of the kernel of the symbol
  have hdec : ∀ j : ℤ, ‖iwKernel (iwSymbolSet (diffFreqs ρ l₂) (periodize σ)) j‖
      ≤ (4 * (((diffFreqs ρ l₂).card : ℝ) * SvalF Λ) + 1) * ‖kmtKernWeight j‖ :=
    iwKernel_decay_of_bump (diffFreqs ρ l₂) hcd hcs (hSval_nonneg Λ) hI1 hI2
  have hκsumm : Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet (diffFreqs ρ l₂) (periodize σ)) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec (summable_kmtKernWeight.mul_left _)
  have hkd := tsum_norm_iwKernel_le (diffFreqs ρ l₂) σ (hSval_nonneg Λ) hcd hcs hI1 hI2
  have hKle : (4 * (((diffFreqs ρ l₂).card : ℝ) * SvalF Λ) + 1) * Kw ≤ Cval Λ := by
    have hcardR : ((diffFreqs ρ l₂).card : ℝ) ≤ (Acard : ℝ) := by exact_mod_cast hcard_diff
    have h1 : ((diffFreqs ρ l₂).card : ℝ) * SvalF Λ ≤ (Acard : ℝ) * SvalF Λ :=
      mul_le_mul_of_nonneg_right hcardR (hSval_nonneg Λ)
    have h3 : 4 * (((diffFreqs ρ l₂).card : ℝ) * SvalF Λ) + 1
        ≤ 4 * ((Acard : ℝ) * SvalF Λ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h3 hKw_nonneg
  have hkey : (fun x : ℤ => Tm ρ l₂ σ g x)
      = fun n : ℤ => ∑' j : ℤ,
          iwKernel (iwSymbolSet (diffFreqs ρ l₂) (periodize σ)) j * g (n - j) := by
    funext n
    simp only [Tm, iwConv_apply, smul_eq_mul]
  -- ## Young's inequality
  calc eLpNorm (fun x : ℤ => Tm ρ l₂ σ g x) (ENNReal.ofReal p) MeasureTheory.Measure.count
      = eLpNorm (fun n : ℤ => ∑' j : ℤ,
          iwKernel (iwSymbolSet (diffFreqs ρ l₂) (periodize σ)) j * g (n - j))
          (ENNReal.ofReal p) MeasureTheory.Measure.count := by rw [hkey]
    _ ≤ (∑' t : ℤ, ENNReal.ofReal
            ‖iwKernel (iwSymbolSet (diffFreqs ρ l₂) (periodize σ)) t‖)
          * eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count :=
        Work.KMTAreas.A4.offYoung_conv_count_le (le_of_lt hp) _ _
    _ = ENNReal.ofReal (∑' t : ℤ,
          ‖iwKernel (iwSymbolSet (diffFreqs ρ l₂) (periodize σ)) t‖)
          * eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _) hκsumm]
    _ ≤ ENNReal.ofReal (Cval Λ) * eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
        exact hkd.trans hKle
    _ = (Cfun Λ : ENNReal) * eLpNorm g (ENNReal.ofReal p) MeasureTheory.Measure.count := by
        have hcoe : ((Cfun Λ : NNReal) : ℝ) = Cval Λ := rfl
        have h2 : ENNReal.ofReal (Cval Λ) = (Cfun Λ : ENNReal) := by
          rw [← hcoe, ENNReal.ofReal_coe_nnreal]
        rw [h2]

end

end Work.KMTAreas.A7
