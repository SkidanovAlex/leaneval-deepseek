import Mathlib.MeasureTheory.Function.L2Space
import Submission.Commons.Analysis.InnerProductSpace.norm_sum_sq_of_orthogonal
import Submission.Commons.Analysis.InnerProductSpace.block_recombination

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Commons.Analysis.Fourier

/-! ### Auxiliary facts about `L²` integrals and extended norms -/

/-- For a function `f : α → E`, the `lintegral` of the square of the extended norm is the square
of the `L²` seminorm. -/
private theorem lintegral_enorm_rpow_two_eq_eLpNorm_rpow_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] (f : α → E)
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ = (eLpNorm f 2 μ) ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf]
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The `lintegral` of the square of the extended norm of `f` is the square of the `L²` norm of
the associated element of `Lp`. -/
private theorem lintegral_enorm_rpow_two_eq_ofReal_norm_toLp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] {f : α → E} (hf : MemLp f 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (‖hf.toLp f‖ ^ 2) := by
  rw [lintegral_enorm_rpow_two_eq_eLpNorm_rpow_two _ hf.aestronglyMeasurable, ← Lp.enorm_toLp hf, ← ofReal_norm]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [← ENNReal.ofReal_pow (norm_nonneg _) 2]

/-- The `lintegral` of the square of the extended norm of an `Lp` element is
`ofReal` of the square of its norm. -/
private theorem lintegral_enorm_rpow_two_coeFn {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {E : Type*} [NormedAddCommGroup E] (x : Lp E 2 μ) :
    ∫⁻ a, ‖(x : α → E) a‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [lintegral_enorm_rpow_two_eq_eLpNorm_rpow_two _ (Lp.aestronglyMeasurable x), ← Lp.enorm_def, ← ofReal_norm]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [← ENNReal.ofReal_pow (norm_nonneg x) 2]

/-- A finite sum of almost-everywhere equal functions is almost-everywhere equal to the sum of
the limits. -/
private theorem ae_eq_sum_finset {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {E : Type*}
    [AddCommMonoid E] (s : Finset ι) {f g : ι → α → E} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun a => ∑ i ∈ s, f i a) =ᵐ[μ] (fun a => ∑ i ∈ s, g i a) := by
  filter_upwards [(eventually_all_finset s).2 h] with a ha
  exact Finset.sum_congr rfl (fun i hi => ha i hi)

/-- The upper logarithm in base `2` is at most the lower logarithm plus one: the number of
halving steps needed to bring `M` down to `1` is at most `log₂ M + 1`. -/
private theorem nat_clog_two_le_log2_add_one (M : ℕ) : Nat.clog 2 M ≤ Nat.log2 M + 1 := by
  refine Nat.clog_le_of_le_pow ?_
  rw [Nat.log2_eq_log_two]
  exact le_of_lt (Nat.lt_pow_succ_log_self Nat.one_lt_two M)

/-! ### The recombination lemma -/

/-- **Block dual recombination.** Let `R j` be a decreasing (nested) sequence of measurable sets,
`V j` an `L²`-orthogonal family of functions supported on the blocks
`{j ∈ J : b j = r}`, `r < M`.  If on each block the sum `∑_{j} 1_{R_j} V_j` is bounded by
`B (∑_j ‖V_j‖²)^{1/2}`, then the total sum is bounded by
`(B + log₂ M + 1) (∑_j ‖V_j‖²)^{1/2}`.

The gain over the trivial bound is the collapse identity `⟪1_{R_i}V_i, 1_{R_j}V_j⟫ = ⟪V_i, 1_{R_j}V_j⟫`
for `i < j` (valid since `R_j ⊆ R_i`), which makes the interaction between the blocks pay only
a factor `log₂ M` through a divide-and-conquer recursion (Bourgain's "dual Doob" argument). -/
theorem block_dual_recombination {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (R : ℕ → Set α) (V : ℕ → α → ℂ) (J : Finset ℕ) (b : ℕ → ℕ) (M : ℕ) (B : ℝ)
    (hRmeas : ∀ j, MeasurableSet (R j))
    (hnest : ∀ i j, i ≤ j → R j ⊆ R i)
    (hbmono : ∀ i ∈ J, ∀ j ∈ J, i ≤ j → b i ≤ b j)
    (hbM : ∀ j ∈ J, b j < M)
    (hV : ∀ j ∈ J, MeasureTheory.MemLp (V j) 2 μ)
    (hVzero : ∀ j, j ∉ J → V j = 0)
    (horth : ∀ i j, i ≠ j → ∫ a, V i a * star (V j a) ∂μ = 0)
    (hB : 0 ≤ B)
    (hblock : ∀ r : ℕ, r < M →
      ∫⁻ a, ‖∑ j ∈ J.filter (fun j => b j = r), Set.indicator (R j) (V j) a‖ₑ ^ (2:ℝ) ∂μ
        ≤ ENNReal.ofReal (B ^ 2) *
            ∑ j ∈ J.filter (fun j => b j = r), ∫⁻ a, ‖V j a‖ₑ ^ (2:ℝ) ∂μ) :
    ∫⁻ a, ‖∑ j ∈ J, Set.indicator (R j) (V j) a‖ₑ ^ (2:ℝ) ∂μ
      ≤ ENNReal.ofReal ((B + (Nat.log2 M : ℝ) + 1) ^ 2)
        * ∑ j ∈ J, ∫⁻ a, ‖V j a‖ₑ ^ (2:ℝ) ∂μ := by
  classical
  -- `V j` is `L²` for every `j` by the support condition.
  have hVall : ∀ j, MemLp (V j) 2 μ := fun j => by
    by_cases hj : j ∈ J
    · exact hV j hj
    · rw [hVzero j hj]; exact MemLp.zero
  -- The `Lp` elements associated to `V j` and to `1_{R_j} V_j`.
  let F : ℕ → Lp ℂ 2 μ := fun j => (hVall j).toLp (V j)
  let I : ℕ → Lp ℂ 2 μ :=
    fun j => ((hVall j).indicator (hRmeas j)).toLp (Set.indicator (R j) (V j))
  -- The block of indices `j ∈ J` with `b j = r`.
  let bl : ℕ → Finset ℕ := fun r => J.filter (fun j => b j = r)
  -- The block sums, first as functions, then as elements of `Lp`.
  let Φfn : ℕ → α → ℂ := fun r a => ∑ j ∈ bl r, Set.indicator (R j) (V j) a
  let ffn : ℕ → α → ℂ := fun r a => ∑ j ∈ bl r, V j a
  let φ : ℕ → Lp ℂ 2 μ := fun r => ∑ j ∈ bl r, I j
  let f : ℕ → Lp ℂ 2 μ := fun r => ∑ j ∈ bl r, F j
  -- Almost-everywhere descriptions of the representatives.
  have hIae : ∀ j, (I j : α → ℂ) =ᵐ[μ] Set.indicator (R j) (V j) := fun j => by
    dsimp only [I]; exact ((hVall j).indicator (hRmeas j)).coeFn_toLp
  have hFae : ∀ j, (F j : α → ℂ) =ᵐ[μ] V j := fun j => by
    dsimp only [F]; exact (hVall j).coeFn_toLp
  have hΦae : ∀ r, (φ r : α → ℂ) =ᵐ[μ] Φfn r := fun r => by
    have h1 : (φ r : α → ℂ) =ᵐ[μ] (fun a => ∑ j ∈ bl r, (I j : α → ℂ) a) := by
      dsimp only [φ]; exact Lp.coeFn_fun_finsetSum (bl r) I
    have h2 : (fun a => ∑ j ∈ bl r, (I j : α → ℂ) a) =ᵐ[μ] Φfn r := by
      dsimp only [Φfn]; exact ae_eq_sum_finset (bl r) (fun j _ => hIae j)
    exact h1.trans h2
  -- Orthogonality of the `F j`.
  have hFV : ∀ i j, i ≠ j → inner ℂ (F i) (F j) = 0 := by
    intro i j hij
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (horth j i hij.symm)
    filter_upwards [hFae i, hFae j] with a hi hj
    simp only [hi, hj, RCLike.inner_apply, starRingEnd_apply]
  -- Orthogonality within each block: `‖f r‖² = ∑_{j ∈ bl r} ‖F j‖²`.
  have hsum : ∀ r, ∑ j ∈ bl r, ‖F j‖ ^ 2 = ‖f r‖ ^ 2 := fun r => by
    dsimp only [f]
    exact (Commons.Analysis.InnerProductSpace.norm_sum_sq_of_orthogonal (bl r) F (fun i _ j _ hij => hFV i j hij)).symm
  -- Orthogonality of the block sums: `⟪f r, f s⟫ = 0` for `r ≠ s`.
  have horthf : ∀ r s, r ≠ s → inner ℂ (f r) (f s) = 0 := by
    intro r s hrs
    have hL : inner ℂ (f r) (f s) = ∑ i ∈ bl r, ∑ j ∈ bl s, inner ℂ (F i) (F j) := by
      dsimp only [f]
      rw [sum_inner]
      exact Finset.sum_congr rfl (fun i _ => by rw [inner_sum])
    rw [hL]
    refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun j hj => ?_))
    have hij : i ≠ j := by
      intro h
      exact hrs (by rw [← (Finset.mem_filter.mp hi).2, ← (Finset.mem_filter.mp hj).2, h])
    exact hFV i j hij
  -- The collapse identity: for `r < s`, `⟪φ r, φ s⟫ = ⟪f r, φ s⟫`.
  have hcollapse : ∀ r s, r < s → inner ℂ (φ r) (φ s) = inner ℂ (f r) (φ s) := by
    intro r s hrs
    have hpair : ∀ i ∈ bl r, ∀ j ∈ bl s, inner ℂ (I i) (I j) = inner ℂ (F i) (I j) := by
      intro i hi j hj
      have hiJ : i ∈ J := (Finset.mem_filter.mp hi).1
      have hjJ : j ∈ J := (Finset.mem_filter.mp hj).1
      have hib : b i = r := (Finset.mem_filter.mp hi).2
      have hjb : b j = s := (Finset.mem_filter.mp hj).2
      have hij : i < j := by
        rcases lt_or_ge i j with h | h
        · exact h
        · exfalso
          have hle := hbmono j hjJ i hiJ h
          omega
      have hsub : R j ⊆ R i := hnest i j (le_of_lt hij)
      rw [L2.inner_def, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hIae i, hIae j, hFae i] with a hIih hIjh hFih
      rw [hIih, hIjh, hFih]
      by_cases hmem : a ∈ R i
      · rw [Set.indicator_of_mem hmem]
      · have hmem' : a ∉ R j := fun h => hmem (hsub h)
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem', inner_zero_left,
          inner_zero_right]
    have hL : inner ℂ (φ r) (φ s) = ∑ i ∈ bl r, ∑ j ∈ bl s, inner ℂ (I i) (I j) := by
      dsimp only [φ]
      rw [sum_inner]
      exact Finset.sum_congr rfl (fun i _ => by rw [inner_sum])
    have hR : inner ℂ (f r) (φ s) = ∑ i ∈ bl r, ∑ j ∈ bl s, inner ℂ (F i) (I j) := by
      dsimp only [f, φ]
      rw [sum_inner]
      exact Finset.sum_congr rfl (fun i _ => by rw [inner_sum])
    rw [hL, hR]
    exact Finset.sum_congr rfl (fun i hi =>
      Finset.sum_congr rfl (fun j hj => hpair i hi j hj))
  -- The block bound `‖φ r‖ ≤ B ‖f r‖`, deduced from `hblock`.
  have hbd : ∀ r, r < M → ‖φ r‖ ≤ B * ‖f r‖ := by
    intro r hr
    have hb := hblock r hr
    have hLHS : ∫⁻ a, ‖Φfn r a‖ₑ ^ (2:ℝ) ∂μ = ENNReal.ofReal (‖φ r‖ ^ 2) := by
      rw [lintegral_enorm_rpow_two_eq_eLpNorm_rpow_two _
          ((Lp.aestronglyMeasurable _).congr (hΦae r)), eLpNorm_congr_ae (hΦae r).symm,
        ← Lp.enorm_def, ← ofReal_norm]
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      exact (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    have hRHS : (∑ j ∈ J.filter (fun j => b j = r), ∫⁻ a, ‖V j a‖ₑ ^ (2:ℝ) ∂μ)
        = ENNReal.ofReal (∑ j ∈ bl r, ‖F j‖ ^ 2) := by
      simp only [bl]
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [F]
      exact lintegral_enorm_rpow_two_eq_ofReal_norm_toLp (hVall j)
    have hb' : ENNReal.ofReal (‖φ r‖ ^ 2)
        ≤ ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (∑ j ∈ bl r, ‖F j‖ ^ 2) := by
      rw [← hLHS, ← hRHS]
      exact hb
    have hfin : ‖φ r‖ ^ 2 ≤ B ^ 2 * (∑ j ∈ bl r, ‖F j‖ ^ 2) := by
      refine (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg B)
        (Finset.sum_nonneg (fun j _ => sq_nonneg _)))).mp ?_
      rw [ENNReal.ofReal_mul (sq_nonneg B)]
      exact hb'
    rw [hsum] at hfin
    have hs : ‖φ r‖ ^ 2 ≤ (B * ‖f r‖) ^ 2 := by
      rw [mul_pow]; exact hfin
    have h3 := sq_le_sq.mp hs
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg hB (norm_nonneg _))] at h3
  -- Apply the abstract recombination lemma on the block interval `[0, M)`.
  have hmain : ‖∑ r ∈ Finset.range M, φ r‖
      ≤ (B + (1 / 2) * (Nat.clog 2 M : ℝ)) * Real.sqrt (∑ r ∈ Finset.range M, ‖f r‖ ^ 2) := by
    have h := Commons.Analysis.InnerProductSpace.block_recombination B hB 0 M (Nat.zero_le M) φ f
      (fun r hr => hbd r (Finset.mem_Ico.mp hr).2)
      (fun r _ s _ hrs => hcollapse r s hrs)
      (fun r _ s _ hrs => horthf r s hrs)
    simpa only [Nat.sub_zero, Finset.range_eq_Ico] using h
  set ΦLp : Lp ℂ 2 μ := ∑ r ∈ Finset.range M, φ r with hΦLp
  set S : ℝ := ∑ j ∈ J, ‖F j‖ ^ 2 with hS
  have hSnn : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hSval : S = ∑ r ∈ Finset.range M, ‖f r‖ ^ 2 := by
    rw [hS, ← Finset.sum_fiberwise_of_maps_to
      (fun j hj => Finset.mem_range.mpr (hbM j hj)) (fun j => ‖F j‖ ^ 2)]
    exact Finset.sum_congr rfl (fun r _ => hsum r)
  have hmain' : ‖ΦLp‖ ≤ (B + (1 / 2) * (Nat.clog 2 M : ℝ)) * Real.sqrt S := by
    rw [hΦLp, hSval]
    exact hmain
  -- Square the bound.
  have hbound : ‖ΦLp‖ ^ 2 ≤ (B + (1 / 2) * (Nat.clog 2 M : ℝ)) ^ 2 * S := by
    calc ‖ΦLp‖ ^ 2
        ≤ ((B + (1 / 2) * (Nat.clog 2 M : ℝ)) * Real.sqrt S) ^ 2 := by
          simpa [sq] using mul_self_le_mul_self (norm_nonneg ΦLp) hmain'
      _ = (B + (1 / 2) * (Nat.clog 2 M : ℝ)) ^ 2 * S := by rw [mul_pow, Real.sq_sqrt hSnn]
  -- Replace the constant by `B + log₂ M + 1`.
  have hconst : B + (1 / 2) * (Nat.clog 2 M : ℝ) ≤ B + (Nat.log2 M : ℝ) + 1 := by
    have h2 : (Nat.clog 2 M : ℝ) ≤ (Nat.log2 M : ℝ) + 1 := by
      have hh : Nat.clog 2 M ≤ Nat.log2 M + 1 := nat_clog_two_le_log2_add_one M
      have hh' : ((Nat.clog 2 M : ℕ) : ℝ) ≤ ((Nat.log2 M + 1 : ℕ) : ℝ) := by
        exact_mod_cast hh
      push_cast at hh'
      exact hh'
    linarith
  have hCnn : 0 ≤ B + (1 / 2) * (Nat.clog 2 M : ℝ) := by positivity
  have hfinal : ‖ΦLp‖ ^ 2 ≤ (B + (Nat.log2 M : ℝ) + 1) ^ 2 * S := by
    have hsq : (B + (1 / 2) * (Nat.clog 2 M : ℝ)) ^ 2 ≤ (B + (Nat.log2 M : ℝ) + 1) ^ 2 :=
      (by simpa [sq] using mul_self_le_mul_self hCnn hconst)
    nlinarith [hbound, hSnn, hsq]
  -- Identify the total left-hand side.
  have hfib : (fun a => ∑ r ∈ Finset.range M, Φfn r a)
      = (fun a => ∑ j ∈ J, Set.indicator (R j) (V j) a) := by
    funext a
    dsimp only [Φfn]
    exact Finset.sum_fiberwise_of_maps_to
      (fun j hj => Finset.mem_range.mpr (hbM j hj)) (fun j => Set.indicator (R j) (V j) a)
  have hΦtot_ae : (fun a => ∑ j ∈ J, Set.indicator (R j) (V j) a) =ᵐ[μ] (ΦLp : α → ℂ) := by
    rw [hΦLp]
    have h1 : (fun a => ∑ j ∈ J, Set.indicator (R j) (V j) a)
        =ᵐ[μ] (fun a => ∑ r ∈ Finset.range M, Φfn r a) := Filter.EventuallyEq.of_eq hfib.symm
    have h2 : (fun a => ∑ r ∈ Finset.range M, Φfn r a)
        =ᵐ[μ] (fun a => ∑ r ∈ Finset.range M, (φ r : α → ℂ) a) :=
      (ae_eq_sum_finset (Finset.range M) (fun r _ => hΦae r)).symm
    exact h1.trans (h2.trans (Lp.coeFn_fun_finsetSum (Finset.range M) φ).symm)
  have hQtot : ∫⁻ a, ‖∑ j ∈ J, Set.indicator (R j) (V j) a‖ₑ ^ (2:ℝ) ∂μ
      = ENNReal.ofReal (‖ΦLp‖ ^ 2) := by
    rw [lintegral_enorm_rpow_two_eq_eLpNorm_rpow_two _
        ((Lp.aestronglyMeasurable _).congr hΦtot_ae.symm), eLpNorm_congr_ae hΦtot_ae,
      ← Lp.enorm_def, ← ofReal_norm]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    exact (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
  -- Identify the total right-hand side.
  have hQsum : (∑ j ∈ J, ∫⁻ a, ‖V j a‖ₑ ^ (2:ℝ) ∂μ) = ENNReal.ofReal S := by
    rw [hS, ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [F]
    exact lintegral_enorm_rpow_two_eq_ofReal_norm_toLp (hVall j)
  rw [hQtot, hQsum, ← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) hSnn)]
  exact hfinal

end Commons.Analysis.Fourier