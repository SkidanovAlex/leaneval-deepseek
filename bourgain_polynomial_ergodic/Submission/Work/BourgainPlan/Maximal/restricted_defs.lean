import Mathlib
import Submission.Work.BourgainPlan.Maximal.foundations
import Submission.Work.BourgainPlan.Maximal.kernel_l2

namespace Work.BourgainPlan.Maximal

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology
open Submission.BourgainPlan (discAvg NonnegOnNat)

set_option autoImplicit false

/-! ## The window (restricted) maximal operator and its elementary reductions

The target `Work.BourgainPlan.Maximal.restricted_maximal` is Bourgain's *restricted maximal
inequality* (Lemma 7.32 / (7.33)): the maximal function of the polynomial density averages, taken
over the *window* `N₀ < N ≤ N₀^{1+ε}` only, satisfies an `ℓᵖ` bound with the loss `(C log log N₀)^p`.

What is proved here (all `sorry`-free except the target itself):

* `restrictedMax`, `restrictedAbsMax` — the window maximal function and its absolute-value
  (positive) version, with the elementary `ℓ^∞`, subadditivity and monotonicity properties;
* `restricted_maximal_of_maximal` — the target follows from the *full* maximal statement
  `Submission.BourgainPlan.MaximalStatement`;
* `restricted_maximal_deg_le_one` — the target for `P.natDegree ≤ 1`, every `1 < p`;
* `restricted_maximal_ge_two` — the target for `2 ≤ p`, **every** `P`.

The remaining content is `1 < p < 2` with `P.natDegree ≥ 2`, i.e. Bourgain §7.3. -/

/-- The maximal function of the polynomial density averages restricted to the window
`(N₀, ⌊N₀^{1+ε}⌋]`. -/
noncomputable def restrictedMax (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) (g : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  ⨆ N ∈ Finset.Icc (N₀ + 1) (Nat.floor ((N₀ : ℝ) ^ (1 + ε))), ‖discAvg P N g n‖ₑ

/-- The **absolute-value** window maximal function: the sum of the density kernel against `|g|`,
restricted to the window.  This is the *positive* version of the window maximal operator, in the
form in which Bourgain's §7.3 ("a problem about positive functions") states its estimates. -/
noncomputable def restrictedAbsMax (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    ℝ≥0∞ :=
  ⨆ N ∈ Finset.Icc (N₀ + 1) (Nat.floor ((N₀ : ℝ) ^ (1 + ε))), absMaxSum P g n N

/-- The window maximal function is dominated by the full maximal function. -/
lemma restrictedMax_le_iSup (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    restrictedMax P N₀ ε g n ≤ ⨆ N : ℕ, ‖discAvg P N g n‖ₑ := by
  unfold restrictedMax
  exact iSup₂_le fun N _ => le_iSup (fun N : ℕ => ‖discAvg P N g n‖ₑ) N

/-- The window maximal function is dominated by the absolute-value window maximal function. -/
lemma restrictedMax_le_restrictedAbsMax (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) (g : ℕ → ℝ)
    (n : ℕ) : restrictedMax P N₀ ε g n ≤ restrictedAbsMax P N₀ ε g n := by
  unfold restrictedMax restrictedAbsMax
  refine iSup₂_le fun N hN => le_trans ?_ (le_iSup₂_of_le N hN le_rfl)
  calc ‖discAvg P N g n‖ₑ
      = ‖∑ j ∈ Finset.range (Submission.polySupport P N),
          Submission.polyKernel P N j * g (n + j)‖ₑ := rfl
    _ ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ‖Submission.polyKernel P N j * g (n + j)‖ₑ := enorm_sum_le _ _
    _ = ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ := by
        exact Finset.sum_congr rfl fun j _ =>
          (enorm_mul_ofReal _ (polyKernel_nonneg P N j) (g (n + j))).symm

/-- The absolute-value window maximal function is dominated by the full one. -/
lemma restrictedAbsMax_le_absMax (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    restrictedAbsMax P N₀ ε g n ≤ absMax P g n := by
  unfold restrictedAbsMax absMax
  exact iSup₂_le fun N _ => le_iSup (fun N : ℕ => absMaxSum P g n N) N

/-- Subadditivity of the absolute-value window maximal function. -/
lemma restrictedAbsMax_add_le (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) (f h : ℕ → ℝ) :
    restrictedAbsMax P N₀ ε (f + h) ≤ restrictedAbsMax P N₀ ε f + restrictedAbsMax P N₀ ε h := by
  intro n
  unfold restrictedAbsMax
  refine iSup₂_le fun N hN => ?_
  refine le_trans ?_ (add_le_add (le_iSup₂_of_le N hN le_rfl) (le_iSup₂_of_le N hN le_rfl))
  calc ∑ j ∈ Finset.range (Submission.polySupport P N),
        ENNReal.ofReal (Submission.polyKernel P N j) * ‖(f + h) (n + j)‖ₑ
      = ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * ‖f (n + j) + h (n + j)‖ₑ := by
        exact Finset.sum_congr rfl fun j _ => by rw [Pi.add_apply]
    _ ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * (‖f (n + j)‖ₑ + ‖h (n + j)‖ₑ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_right (enorm_add_le (f (n + j)) (h (n + j))) _
    _ = (∑ j ∈ Finset.range (Submission.polySupport P N),
            ENNReal.ofReal (Submission.polyKernel P N j) * ‖f (n + j)‖ₑ)
          + ∑ j ∈ Finset.range (Submission.polySupport P N),
            ENNReal.ofReal (Submission.polyKernel P N j) * ‖h (n + j)‖ₑ := by
        simp_rw [mul_add, Finset.sum_add_distrib]

/-- Monotonicity of the absolute-value window maximal function. -/
lemma restrictedAbsMax_mono (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) {f h : ℕ → ℝ}
    (hf : ∀ n, ‖f n‖ₑ ≤ ‖h n‖ₑ) : restrictedAbsMax P N₀ ε f ≤ restrictedAbsMax P N₀ ε h := by
  intro n
  unfold restrictedAbsMax
  refine iSup₂_le fun N hN => ?_
  refine le_trans ?_ (le_iSup₂_of_le N hN le_rfl)
  refine Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_right (hf (n + j)) _

/-- The absolute-value window maximal function is pointwise bounded by `‖g‖_∞`. -/
lemma restrictedAbsMax_le_iSup_enorm (P : Polynomial ℤ) (N₀ : ℕ) (ε : ℝ) (g : ℕ → ℝ)
    (n : ℕ) : restrictedAbsMax P N₀ ε g n ≤ ⨆ k : ℕ, ‖g k‖ₑ :=
  le_trans (restrictedAbsMax_le_absMax P N₀ ε g n) (absMax_le_iSup_enorm P g n)

/-- `log log 4 = log(log 4) > 0` (used to absorb the `N₀ = 4` endpoint into the constant). -/
lemma log_log_four_pos : 0 < Real.log (Real.log (4 : ℝ)) := by
  have h : (1 : ℝ) < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_three]
  exact Real.log_pos h

/-- `N ↦ log log N` is nondecreasing for `N ≥ 4`. -/
lemma log_log_mono {N : ℕ} (h : 4 ≤ N) :
    Real.log (Real.log (4 : ℝ)) ≤ Real.log (Real.log (N : ℝ)) := by
  have h4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hN : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
  exact Real.log_le_log h4 (Real.log_le_log (by norm_num) hN)

/-- **A full `ℓᵖ` maximal bound with constant `C₀` gives the window maximal bound with the
`log log` constant.**  This is the elementary bookkeeping that turns any `ℓᵖ` maximal inequality
into the restricted inequality of Lemma 7.32 (the constant is `C₀ / log log 4 + 1`). -/
lemma window_lintegral_le_of_full {P : Polynomial ℤ} {p : ℝ} (hp : 0 < p) {ε : ℝ} {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀)
    (hb : ∀ g : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C₀ ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count) :
    ∀ (N₀ : ℕ), 4 ≤ N₀ → ∀ g : ℕ → ℝ,
      (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n, (restrictedMax P N₀ ε g n) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (((C₀ / Real.log (Real.log (4 : ℝ)) + 1)
              * Real.log (Real.log (N₀ : ℝ))) ^ p)
            * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := by
  intro N₀ hN₀ g hg
  have hpos : 0 < Real.log (Real.log (4 : ℝ)) := log_log_four_pos
  have hc₀ : Real.log (Real.log (4 : ℝ)) ≤ Real.log (Real.log (N₀ : ℝ)) := log_log_mono hN₀
  have hC0' : 0 ≤ C₀ / Real.log (Real.log (4 : ℝ)) + 1 := by positivity
  have hbound : C₀ ≤ (C₀ / Real.log (Real.log (4 : ℝ)) + 1)
      * Real.log (Real.log (N₀ : ℝ)) := by
    have h1 : C₀ / Real.log (Real.log (4 : ℝ)) ≤
        C₀ / Real.log (Real.log (4 : ℝ)) + 1 := by linarith
    have h2 : C₀ / Real.log (Real.log (4 : ℝ)) * Real.log (Real.log (4 : ℝ))
        ≤ (C₀ / Real.log (Real.log (4 : ℝ)) + 1) * Real.log (Real.log (N₀ : ℝ)) :=
      mul_le_mul h1 hc₀ hpos.le hC0'
    rw [div_mul_cancel₀] at h2
    · exact h2
    · exact ne_of_gt hpos
  calc ∫⁻ n, (restrictedMax P N₀ ε g n) ^ p ∂Measure.count
      ≤ ∫⁻ n, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count :=
        lintegral_mono fun n => ENNReal.rpow_le_rpow (restrictedMax_le_iSup P N₀ ε g n) hp.le
    _ ≤ ENNReal.ofReal (C₀ ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := hb g hg
    _ ≤ ENNReal.ofReal (((C₀ / Real.log (Real.log (4 : ℝ)) + 1)
            * Real.log (Real.log (N₀ : ℝ))) ^ p) * ∫⁻ n, ‖g n‖ₑ ^ p ∂Measure.count := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hC₀ hbound hp.le)

/-- **The restricted maximal inequality follows from the full maximal inequality.**  If
`Submission.BourgainPlan.MaximalStatement` holds then the window maximal function of every
nonnegative-on-`ℕ` polynomial satisfies the `log log N₀` bound of Lemma 7.32.

(Note that this is the *trivial* direction: the window sup is dominated by the full sup, and the
`log log N₀ ≥ log log 4 > 0` factor is absorbed into the constant.) -/
theorem restricted_maximal_of_maximal (h : Submission.BourgainPlan.MaximalStatement) :
    ∀ (P : Polynomial ℤ), NonnegOnNat P → ∀ {p : ℝ}, 1 < p → ∀ {ε : ℝ}, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ (N₀ : ℕ), 4 ≤ N₀ → ∀ g : ℕ → ℝ,
        (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
        ∫⁻ n : ℕ, (restrictedMax P N₀ ε g n) ^ p ∂Measure.count
          ≤ ENNReal.ofReal ((C * Real.log (Real.log (N₀ : ℝ))) ^ p)
              * ∫⁻ n : ℕ, ‖g n‖ₑ ^ p ∂Measure.count := by
  intro P hP p hp ε hε
  obtain ⟨C₀, hC₀, hb⟩ := h P hP p hp
  have hpos : 0 < Real.log (Real.log (4 : ℝ)) := log_log_four_pos
  exact ⟨C₀ / Real.log (Real.log (4 : ℝ)) + 1,
    add_pos_of_nonneg_of_pos (div_nonneg hC₀ hpos.le) zero_lt_one,
    window_lintegral_le_of_full (lt_trans zero_lt_one hp) hC₀ hb⟩

/-- **The restricted maximal inequality for polynomials of degree `≤ 1`**, for every `1 < p` and
every `ε > 0` — unconditional, via the full maximal inequality of `deg_le_one`. -/
theorem restricted_maximal_deg_le_one (P : Polynomial ℤ) (hP : NonnegOnNat P)
    (hdeg : P.natDegree ≤ 1) {p : ℝ} (hp : 1 < p) {ε : ℝ} (_hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N₀ : ℕ), 4 ≤ N₀ → ∀ g : ℕ → ℝ,
      (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n : ℕ, (restrictedMax P N₀ ε g n) ^ p ∂Measure.count
        ≤ ENNReal.ofReal ((C * Real.log (Real.log (N₀ : ℝ))) ^ p)
            * ∫⁻ n : ℕ, ‖g n‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C₀, hC₀, hb⟩ := deg_le_one P hP hdeg p hp
  have hpos : 0 < Real.log (Real.log (4 : ℝ)) := log_log_four_pos
  exact ⟨C₀ / Real.log (Real.log (4 : ℝ)) + 1,
    add_pos_of_nonneg_of_pos (div_nonneg hC₀ hpos.le) zero_lt_one,
    window_lintegral_le_of_full (lt_trans zero_lt_one hp) hC₀ hb⟩

/-- **The restricted maximal inequality for `2 ≤ p`, for every `P`.**  Unconditional: the `ℓ²` half
of the maximal inequality is proved (`Work.BourgainPlan.Maximal.kernel_l2`), and `p > 2` follows
from `p = 2` by Marcinkiewicz interpolation (`Work.BourgainPlan.Maximal.lp_gt_two_of_l2`). -/
theorem restricted_maximal_ge_two (P : Polynomial ℤ) (hP : NonnegOnNat P)
    {p : ℝ} (hp : 2 ≤ p) {ε : ℝ} (_hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N₀ : ℕ), 4 ≤ N₀ → ∀ g : ℕ → ℝ,
      (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n : ℕ, (restrictedMax P N₀ ε g n) ^ p ∂Measure.count
        ≤ ENNReal.ofReal ((C * Real.log (Real.log (N₀ : ℝ))) ^ p)
            * ∫⁻ n : ℕ, ‖g n‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C₂, hC₂pos, h₂⟩ := kernel_l2 P hP
  rcases lt_or_eq_of_le hp with hlt | heq
  · obtain ⟨C, hCpos, hb⟩ := lp_gt_two_of_l2 P hC₂pos h₂ hlt
    have hpos : 0 < Real.log (Real.log (4 : ℝ)) := log_log_four_pos
    exact ⟨C / Real.log (Real.log (4 : ℝ)) + 1,
      add_pos_of_nonneg_of_pos (div_nonneg hCpos.le hpos.le) zero_lt_one,
      window_lintegral_le_of_full (by linarith) hCpos.le hb⟩
  · subst heq
    have hpos : 0 < Real.log (Real.log (4 : ℝ)) := log_log_four_pos
    refine ⟨C₂ / Real.log (Real.log (4 : ℝ)) + 1,
      add_pos_of_nonneg_of_pos (div_nonneg hC₂pos.le hpos.le) zero_lt_one, ?_⟩
    intro N₀ hN₀ g hg
    exact window_lintegral_le_of_full (by norm_num) hC₂pos.le
      (fun g hg => by simpa using h₂ g hg) N₀ hN₀ g hg

/-- **The remaining gap of Lemma 7.32, isolated.**  `WindowWeakType P ε` is Bourgain's (7.35) for
the *window* maximal operator: for every `q > 1` the restricted weak-`(q,q)` estimate holds with
the constant `C_q log log N₀`.  Bourgain derives it from the dual sum estimate (7.36), which in turn
follows from the multilinear bootstrap (7.39)–(7.43) with input the `L¹` product estimate (7.42). -/
def WindowWeakType (P : Polynomial ℤ) (ε : ℝ) : Prop :=
  ∀ q : ℝ, 1 < q → ∃ C : ℝ, 0 < C ∧ ∀ (N₀ : ℕ), 4 ≤ N₀ → ∀ g : ℕ → ℝ,
    (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) → ∀ lam : ℝ, 0 < lam →
      ENNReal.ofReal lam ^ q * Measure.count {n : ℕ | ENNReal.ofReal lam < restrictedAbsMax P N₀ ε g n}
        ≤ ENNReal.ofReal ((C * Real.log (Real.log (N₀ : ℝ))) ^ q)
            * ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count


/-- **`WindowWeakType` is no harder than the full maximal inequality.**  The full `ℓ^q` maximal
bound (for every `q > 1`) implies Bourgain's (7.35) for the window operator: the window sup is
dominated by the full one applied to `|g|`, Chebyshev gives the weak-`(q,q)` estimate, and the
`log log N₀ ≥ log log 4 > 0` factor is absorbed into the constant.

Together with `restricted_maximal_of_maximal` and the §7.4 assembly this shows that the remaining
gap of the target is *equivalent* to `Submission.BourgainPlan.MaximalStatement` up to the `§7.4`
bookkeeping: the extra content of Lemma 7.32 over the full theorem is the *independence of `N₀`*
of the constant. -/
theorem windowWeakType_of_maximal (h : Submission.BourgainPlan.MaximalStatement)
    (P : Polynomial ℤ) (hP : NonnegOnNat P) (ε : ℝ) : WindowWeakType P ε := by
  intro q hq
  obtain ⟨C₀, hC₀, hb⟩ := h P hP q hq
  have hpos : 0 < Real.log (Real.log (4 : ℝ)) := log_log_four_pos
  refine ⟨C₀ / Real.log (Real.log (4 : ℝ)) + 1,
    add_pos_of_nonneg_of_pos (div_nonneg hC₀ hpos.le) zero_lt_one, ?_⟩
  intro N₀ hN₀ g hg lam hlam
  -- the window sup is dominated by the full maximal function of `|g|`
  have hdom : ∀ n, restrictedAbsMax P N₀ ε g n ≤ (⨆ N : ℕ, ‖discAvg P N (fun k => |g k|) n‖ₑ) := by
    intro n
    rw [← absMax_eq]
    exact restrictedAbsMax_le_absMax P N₀ ε g n
  have hsupp : ∃ s : Finset ℕ, ∀ n, n ∉ s → (fun k => |g k|) n = 0 :=
    ⟨hg.choose, fun n hn => by simp [hg.choose_spec n hn]⟩
  -- Chebyshev for the `q`-th power
  have hcheb : ENNReal.ofReal lam ^ q * Measure.count {n : ℕ |
        ENNReal.ofReal lam < restrictedAbsMax P N₀ ε g n}
      ≤ ∫⁻ n : ℕ, (restrictedAbsMax P N₀ ε g n) ^ q ∂Measure.count := by
    have hsub : Measure.count {n : ℕ | ENNReal.ofReal lam < restrictedAbsMax P N₀ ε g n}
        ≤ Measure.count {n : ℕ | ENNReal.ofReal lam ^ q
            ≤ (restrictedAbsMax P N₀ ε g n) ^ q} :=
      MeasureTheory.measure_mono fun n hn => ENNReal.rpow_le_rpow hn.le (by linarith : (0:ℝ) ≤ q)
    have hmeas : Measurable (fun n : ℕ => (restrictedAbsMax P N₀ ε g n) ^ q) :=
      measurable_of_countable _
    have h := MeasureTheory.mul_meas_ge_le_lintegral (μ := Measure.count) hmeas
      (ENNReal.ofReal lam ^ q)
    refine le_trans (mul_le_mul_of_nonneg_left hsub bot_le) ?_
    simpa using h
  -- the full `ℓ^q` bound, applied to `|g|`
  have hfull : ∫⁻ n : ℕ, (⨆ N : ℕ, ‖discAvg P N (fun k => |g k|) n‖ₑ) ^ q ∂Measure.count
      ≤ ENNReal.ofReal (C₀ ^ q) * ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count := by
    have := hb (fun k => |g k|) hsupp
    simpa only [Real.enorm_eq_ofReal_abs, abs_abs] using this
  have hmono : ∫⁻ n : ℕ, (restrictedAbsMax P N₀ ε g n) ^ q ∂Measure.count
      ≤ ∫⁻ n : ℕ, (⨆ N : ℕ, ‖discAvg P N (fun k => |g k|) n‖ₑ) ^ q ∂Measure.count :=
    lintegral_mono fun n => ENNReal.rpow_le_rpow (hdom n) (by linarith : (0:ℝ) ≤ q)
  -- bookkeeping: `C₀ ≤ (C₀ / log log 4 + 1) * log log N₀`
  have hc₀ : Real.log (Real.log (4 : ℝ)) ≤ Real.log (Real.log (N₀ : ℝ)) := log_log_mono hN₀
  have hbound : C₀ ≤ (C₀ / Real.log (Real.log (4 : ℝ)) + 1) * Real.log (Real.log (N₀ : ℝ)) := by
    have h1 : C₀ / Real.log (Real.log (4 : ℝ)) ≤
        C₀ / Real.log (Real.log (4 : ℝ)) + 1 := by linarith
    have hC0' : 0 ≤ C₀ / Real.log (Real.log (4 : ℝ)) + 1 := by positivity
    have h2 : C₀ / Real.log (Real.log (4 : ℝ)) * Real.log (Real.log (4 : ℝ))
        ≤ (C₀ / Real.log (Real.log (4 : ℝ)) + 1) * Real.log (Real.log (N₀ : ℝ)) :=
      mul_le_mul h1 hc₀ hpos.le hC0'
    rw [div_mul_cancel₀] at h2
    · exact h2
    · exact ne_of_gt hpos
  calc ENNReal.ofReal lam ^ q * Measure.count {n : ℕ |
          ENNReal.ofReal lam < restrictedAbsMax P N₀ ε g n}
      ≤ ∫⁻ n : ℕ, (restrictedAbsMax P N₀ ε g n) ^ q ∂Measure.count := hcheb
    _ ≤ ∫⁻ n : ℕ, (⨆ N : ℕ, ‖discAvg P N (fun k => |g k|) n‖ₑ) ^ q ∂Measure.count := hmono
    _ ≤ ENNReal.ofReal (C₀ ^ q) * ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count := hfull
    _ ≤ ENNReal.ofReal (((C₀ / Real.log (Real.log (4 : ℝ)) + 1)
            * Real.log (Real.log (N₀ : ℝ))) ^ q) * ∫⁻ n : ℕ, ‖g n‖ₑ ^ q ∂Measure.count := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hC₀ hbound (by linarith : (0:ℝ) ≤ q))

/-- **The `ℓ²` bound for the window maximal operator**, for every `P` nonnegative on `ℕ` and every
window: immediate from the proved `ℓ²` maximal inequality (`Work.BourgainPlan.Maximal.kernel_l2`),
since the window sup is dominated by the full sup of `|g|`.  This is the `(2,2)` endpoint used by
the (delegated) Marcinkiewicz interpolation `lintegral_rpow_le_of_weak_one_l2`. -/
theorem restrictedAbsMax_lintegral_sq_le (P : Polynomial ℤ) (hP : NonnegOnNat P) (N₀ : ℕ) (ε : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ℕ → ℝ,
      (∃ s : Finset ℕ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ n : ℕ, (restrictedAbsMax P N₀ ε g n) ^ (2 : ℝ) ∂Measure.count
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ n : ℕ, ‖g n‖ₑ ^ (2 : ℝ) ∂Measure.count := by
  obtain ⟨C, hCpos, hb⟩ := kernel_l2 P hP
  refine ⟨C, hCpos, fun g hg => ?_⟩
  have hsupp : ∃ s : Finset ℕ, ∀ n, n ∉ s → (fun k => |g k|) n = 0 :=
    ⟨hg.choose, fun n hn => by simp [hg.choose_spec n hn]⟩
  have hmono : ∫⁻ n : ℕ, (restrictedAbsMax P N₀ ε g n) ^ (2 : ℝ) ∂Measure.count
      ≤ ∫⁻ n : ℕ, (⨆ N : ℕ, ‖discAvg P N (fun k => |g k|) n‖ₑ) ^ (2 : ℝ)
          ∂Measure.count := by
    refine lintegral_mono fun n => ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← absMax_eq]
    exact restrictedAbsMax_le_absMax P N₀ ε g n
  refine le_trans hmono ?_
  have := hb (fun k => |g k|) hsupp
  simpa only [Real.enorm_eq_ofReal_abs, abs_abs] using this

/-- **The single-scale absolute average is an `ℓ¹` contraction**: integrating
`absMaxSum P g · N` against the counting measure costs nothing. -/
lemma absMaxSum_lintegral_le (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) :
    ∫⁻ n : ℕ, absMaxSum P g n N ∂Measure.count ≤ ∫⁻ n : ℕ, ‖g n‖ₑ ∂Measure.count := by
  have hterm : ∀ j : ℕ,
      ∫⁻ n : ℕ, ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ
          ∂Measure.count
        ≤ ENNReal.ofReal (Submission.polyKernel P N j) * ∫⁻ n : ℕ, ‖g n‖ₑ ∂Measure.count := by
    intro j
    rw [MeasureTheory.lintegral_const_mul]
    · refine mul_le_mul_of_nonneg_left ?_ bot_le
      rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
      exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => n + j)
        (fun a _ hab => Nat.add_right_cancel hab) (fun m => ‖g m‖ₑ)
    · exact measurable_of_countable _
  calc ∫⁻ n : ℕ, absMaxSum P g n N ∂Measure.count
      = ∑ j ∈ Finset.range (Submission.polySupport P N),
          ∫⁻ n : ℕ, ENNReal.ofReal (Submission.polyKernel P N j) * ‖g (n + j)‖ₑ
            ∂Measure.count := by
        unfold absMaxSum
        rw [MeasureTheory.lintegral_finsetSum]
        intro j _
        exact measurable_of_countable _
    _ ≤ ∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j) * ∫⁻ n : ℕ, ‖g n‖ₑ ∂Measure.count :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j ∈ Finset.range (Submission.polySupport P N),
          ENNReal.ofReal (Submission.polyKernel P N j)) * ∫⁻ n : ℕ, ‖g n‖ₑ ∂Measure.count := by
        rw [Finset.sum_mul]
    _ ≤ 1 * ∫⁻ n : ℕ, ‖g n‖ₑ ∂Measure.count := by
        refine mul_le_mul_of_nonneg_right ?_ bot_le
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => polyKernel_nonneg P N j)]
        simpa using ENNReal.ofReal_le_ofReal (sum_polyKernel_le_one P N)
    _ = ∫⁻ n : ℕ, ‖g n‖ₑ ∂Measure.count := one_mul _

end Work.BourgainPlan.Maximal
