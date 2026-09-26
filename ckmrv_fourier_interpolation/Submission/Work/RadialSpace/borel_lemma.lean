import Mathlib
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.iteratedDeriv_ofReal

/-!
# Borel's lemma for smooth functions on `ℝ`

Given any sequence `b : ℕ → ℂ` there is a smooth function `W : ℝ → ℂ` whose `m`-th
derivative at `0` equals `b m`.  This is the classical *Borel lemma*: every power
series is the Taylor series of a smooth function.

The construction is the standard one.  Let `φ` be a smooth bump function which
equals `1` on `[-1,1]` and vanishes outside `(-2,2)`, let `a n` be a sequence
growing so fast that the `n`-th summand `b n / n! * x ^ n * φ (a n * x)` is tiny
in every `C^k` norm, and set

`W x = ∑' n, b n / n! * x ^ n * φ (a n * x)`.

Near `0` the `n`-th summand equals `b n / n! * x ^ n`, which has vanishing Taylor
coefficients of every order except `n`, where the coefficient is `b n`.
-/

open Filter Topology Set
open scoped ContDiff

namespace Work.RadialSpace

/-! ### A bump function -/

/-- The standard bump function on `ℝ`: smooth, equal to `1` on `[-1,1]` and
supported in the open ball of radius `2`. -/
noncomputable abbrev borelBump : ℝ → ℝ := (default : ContDiffBump (0 : ℝ))

lemma borelBump_rIn : (default : ContDiffBump (0 : ℝ)).rIn = 1 := rfl

lemma borelBump_rOut : (default : ContDiffBump (0 : ℝ)).rOut = 2 := rfl

lemma borelBump_contDiff : ContDiff ℝ ∞ borelBump :=
  ContDiffBump.contDiff (default : ContDiffBump (0 : ℝ)) (n := ⊤)

attribute [local fun_prop] borelBump_contDiff

lemma borelBump_hasCompactSupport : HasCompactSupport borelBump :=
  ContDiffBump.hasCompactSupport (default : ContDiffBump (0 : ℝ))

lemma borelBump_one {x : ℝ} (hx : |x| ≤ 1) : borelBump x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, borelBump_rIn]
  exact hx

lemma borelBump_zero {x : ℝ} (hx : 2 ≤ |x|) : borelBump x = 0 := by
  apply ContDiffBump.zero_of_le_dist
  rw [dist_zero_right, Real.norm_eq_abs, borelBump_rOut]
  exact hx

/-- Near a point `x` with `2 < |a * x|`, the composed bump `z ↦ φ (a * z)` vanishes. -/
lemma borelBump_eventually_eq_zero {a x : ℝ} (hax : 2 < |a * x|) :
    (fun z : ℝ => borelBump (a * z)) =ᶠ[𝓝 x] 0 := by
  have hcont : Continuous fun z : ℝ => a * z := continuous_const.mul continuous_id
  have hopen : IsOpen {z : ℝ | 2 < |a * z|} := isOpen_lt continuous_const hcont.abs
  filter_upwards [hopen.mem_nhds hax] with z hz
  exact borelBump_zero (le_of_lt hz)

private lemma coe_nat_le_smooth (k : ℕ) : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
  WithTop.coe_le_coe.mpr le_top

/-! ### Uniform bounds for the derivatives of the bump function -/

/-- A nonnegative, monotone bound for the `i`-th derivative of the bump function,
uniform in the point and in `i ≤ k`. -/
noncomputable def borelBound (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1),
    sSup (Set.range fun x : ℝ => ‖iteratedFDeriv ℝ i borelBump x‖)

private lemma bddAbove_borelBump (i : ℕ) :
    BddAbove (Set.range fun x : ℝ => ‖iteratedFDeriv ℝ i borelBump x‖) := by
  have hcs : HasCompactSupport (iteratedFDeriv ℝ i borelBump) :=
    borelBump_hasCompactSupport.iteratedFDeriv i
  have hcont : Continuous (iteratedFDeriv ℝ i borelBump) :=
    borelBump_contDiff.continuous_iteratedFDeriv (coe_nat_le_smooth i)
  have h1 : BddAbove ((fun x : ℝ => ‖iteratedFDeriv ℝ i borelBump x‖) ''
      tsupport (iteratedFDeriv ℝ i borelBump)) := (hcs.image hcont.norm).bddAbove
  have h2 : BddAbove ({(0 : ℝ)} : Set ℝ) := (finite_singleton (0 : ℝ)).bddAbove
  refine BddAbove.mono ?_ (bddAbove_union.mpr ⟨h1, h2⟩)
  rintro y ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport (iteratedFDeriv ℝ i borelBump)
  · exact Or.inl ⟨x, hx, rfl⟩
  · refine Or.inr ?_
    have hzero : iteratedFDeriv ℝ i borelBump x = 0 := by
      by_contra h
      exact hx (subset_closure (Function.mem_support.mpr h))
    simp [hzero]

private lemma borelBound_term_nonneg (i : ℕ) :
    0 ≤ sSup (Set.range fun x : ℝ => ‖iteratedFDeriv ℝ i borelBump x‖) :=
  (norm_nonneg _).trans
    (le_csSup (bddAbove_borelBump i) ⟨0, rfl⟩)

lemma borelBound_mono : Monotone borelBound := by
  intro k l hkl
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ _
    exact borelBound_term_nonneg i

lemma borelBound_nonneg (k : ℕ) : 0 ≤ borelBound k :=
  Finset.sum_nonneg fun i _ => borelBound_term_nonneg i

lemma le_borelBound {i k : ℕ} (hik : i ≤ k) (x : ℝ) :
    ‖iteratedFDeriv ℝ i borelBump x‖ ≤ borelBound k := by
  refine (le_csSup (bddAbove_borelBump i) (Set.mem_range_self x)).trans ?_
  exact Finset.single_le_sum (fun j _ => borelBound_term_nonneg j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hik))

/-! ### The scaling sequence and the summands -/

/-- The (very fast growing) scaling sequence attached to `b`. -/
noncomputable def borelA (b : ℕ → ℂ) (n : ℕ) : ℝ :=
  max 1 (‖b n‖ * (n.factorial : ℝ) * borelBound n * 2 ^ (4 * n))

lemma one_le_borelA (b : ℕ → ℂ) (n : ℕ) : 1 ≤ borelA b n := le_max_left _ _

lemma borelA_pos (b : ℕ → ℂ) (n : ℕ) : 0 < borelA b n :=
  lt_of_lt_of_le one_pos (one_le_borelA b n)

lemma borelA_ne_zero (b : ℕ → ℂ) (n : ℕ) : borelA b n ≠ 0 := (borelA_pos b n).ne'

/-- The `n`-th real summand. -/
noncomputable def borelHTerm (b : ℕ → ℂ) (n : ℕ) : ℝ → ℝ :=
  fun x => x ^ n * borelBump (borelA b n * x)

/-- The `n`-th complex summand. -/
noncomputable def borelTerm (b : ℕ → ℂ) (n : ℕ) : ℝ → ℂ :=
  (b n / (n.factorial : ℂ)) • fun x => ((borelHTerm b n x : ℝ) : ℂ)

/-- The Borel sum. -/
noncomputable def borelW (b : ℕ → ℂ) : ℝ → ℂ := fun x => ∑' n, borelTerm b n x

lemma contDiff_borelHTerm (b : ℕ → ℂ) (n : ℕ) : ContDiff ℝ ∞ (borelHTerm b n) := by
  unfold borelHTerm
  fun_prop

lemma contDiff_borelTerm (b : ℕ → ℂ) (n : ℕ) : ContDiff ℝ ∞ (borelTerm b n) := by
  have h : ContDiff ℝ ∞ (fun x : ℝ => ((borelHTerm b n x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_borelHTerm b n)
  unfold borelTerm
  exact h.const_smul (b n / (n.factorial : ℂ))

lemma contDiffAt_borelTerm (b : ℕ → ℂ) (n k : ℕ) (x : ℝ) :
    ContDiffAt ℝ k (fun x : ℝ => ((borelHTerm b n x : ℝ) : ℂ)) x := by
  have h : ContDiff ℝ ∞ (fun y : ℝ => ((borelHTerm b n y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_borelHTerm b n)
  exact (h.of_le (coe_nat_le_smooth k)).contDiffAt

/-! ### The majorant and its summability -/

/-- A summable majorant for `‖iteratedFDeriv k (borelTerm b n)‖`, uniform in the point. -/
noncomputable def borelV (b : ℕ → ℂ) (k n : ℕ) : ℝ :=
  ‖b n‖ * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k) * (borelA b n) ^ ((k : ℤ) - (n : ℤ))
    + 2 ^ k * (1 / 8 : ℝ) ^ n

/-- For `n > k` the fast growth of `a n` beats the `n`-th summand. -/
private lemma borelV_first_le (b : ℕ → ℂ) {k n : ℕ} (hnk : k < n) :
    ‖b n‖ * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k) * (borelA b n) ^ ((k : ℤ) - (n : ℤ))
      ≤ 2 ^ k * (1 / 8 : ℝ) ^ n := by
  set a := borelA b n with ha
  have ha1 : 1 ≤ a := one_le_borelA b n
  have hapos : 0 < a := borelA_pos b n
  have hz : a ^ ((k : ℤ) - (n : ℤ)) = (a ^ (n - k))⁻¹ := by
    have hk : ((k : ℤ) - (n : ℤ)) = -(((n - k : ℕ)) : ℤ) := by
      have := Nat.cast_sub (R := ℤ) (le_of_lt hnk)
      omega
    rw [hk, zpow_neg, zpow_natCast]
  rw [hz, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hapos _)]
  have hage : ‖b n‖ * (n.factorial : ℝ) * borelBound n * 2 ^ (4 * n) ≤ a ^ (n - k) := by
    have h1 : ‖b n‖ * (n.factorial : ℝ) * borelBound n * 2 ^ (4 * n) ≤ a := le_max_right _ _
    exact h1.trans (le_self_pow₀ ha1 (by omega : n - k ≠ 0))
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hage (by positivity))
  have hle : (k.factorial : ℝ) * borelBound k ≤ (n.factorial : ℝ) * borelBound n := by
    have hk1 : (k.factorial : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (le_of_lt hnk)
    have hk2 : borelBound k ≤ borelBound n := borelBound_mono (le_of_lt hnk)
    nlinarith [Nat.cast_nonneg k (α := ℝ), Nat.cast_nonneg n (α := ℝ),
      borelBound_nonneg k, borelBound_nonneg n]
  have h8 : (1 / 8 : ℝ) ^ n * 2 ^ (4 * n) = 2 ^ n := by
    rw [pow_mul, ← mul_pow]; norm_num
  calc ‖b n‖ * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k)
      = 2 ^ k * (‖b n‖ * ((k.factorial : ℝ) * borelBound k)) * 2 ^ n := by
        rw [pow_add]; ring
    _ ≤ 2 ^ k * (‖b n‖ * ((n.factorial : ℝ) * borelBound n)) * 2 ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hle (norm_nonneg _)) (by positivity)
    _ = 2 ^ k * (1 / 8 : ℝ) ^ n
          * (‖b n‖ * (n.factorial : ℝ) * borelBound n * 2 ^ (4 * n)) := by
        calc 2 ^ k * (‖b n‖ * ((n.factorial : ℝ) * borelBound n)) * 2 ^ n
            = 2 ^ k * 2 ^ n * (‖b n‖ * ((n.factorial : ℝ) * borelBound n)) := by ring
          _ = 2 ^ k * ((1 / 8 : ℝ) ^ n * 2 ^ (4 * n))
                * (‖b n‖ * ((n.factorial : ℝ) * borelBound n)) := by rw [h8]
          _ = 2 ^ k * (1 / 8 : ℝ) ^ n
                * (‖b n‖ * (n.factorial : ℝ) * borelBound n * 2 ^ (4 * n)) := by ring

lemma summable_borelV (b : ℕ → ℂ) (k : ℕ) : Summable (borelV b k) := by
  have hgeom : Summable (fun n : ℕ => 2 ^ k * (1 / 8 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hfin : Summable (fun n : ℕ => if n ≤ k then
      ‖b n‖ * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k)
        * (borelA b n) ^ ((k : ℤ) - (n : ℤ)) + 2 ^ k * (1 / 8 : ℝ) ^ n else 0) := by
    refine summable_of_ne_finset_zero (s := Finset.range (k + 1)) ?_
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [if_neg (by omega : ¬ n ≤ k)]
  have hgeom2 : Summable (fun n : ℕ => 2 * (2 ^ k * (1 / 8 : ℝ) ^ n)) := hgeom.mul_left 2
  refine Summable.of_nonneg_of_le ?_ ?_ (hfin.add hgeom2)
  · intro n
    exact add_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
        (borelBound_nonneg k)) (by positivity)) (zpow_pos (borelA_pos b n) _).le)
      (by positivity)
  · intro n
    rcases le_or_gt n k with hnk | hnk
    · rw [borelV, if_pos hnk]
      exact le_add_of_nonneg_right (by positivity)
    · rw [borelV, if_neg (by omega : ¬ n ≤ k)]
      have h := borelV_first_le b hnk
      linarith

/-! ### Elementary estimates -/

private lemma eighth_pow_mul (n : ℕ) : (1 / 8 : ℝ) ^ n * 2 ^ (4 * n) = 2 ^ n := by
  rw [pow_mul, ← mul_pow]
  norm_num

/-- The `i`-th derivative of `x ^ n` on the region `|x| ≤ 2 / a`. -/
private lemma norm_iteratedFDeriv_pow_le {n i : ℕ} {x a : ℝ} (ha : 0 < a)
    (hx : |x| ≤ 2 / a) :
    ‖iteratedFDeriv ℝ i (fun y : ℝ => y ^ n) x‖
      ≤ (n.factorial : ℝ) * 2 ^ (n - i) * a ^ ((i : ℤ) - (n : ℤ)) := by
  have hnn : 0 ≤ (n.factorial : ℝ) * 2 ^ (n - i) * a ^ ((i : ℤ) - (n : ℤ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (zpow_pos ha _).le
  rcases le_or_gt i n with hi | hi
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow]
    have hcast : ‖((n.descFactorial i : ℝ) * x ^ (n - i))‖
        = (n.descFactorial i : ℝ) * |x| ^ (n - i) := by
      rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs, abs_pow]
    rw [hcast]
    have hdf : (n.descFactorial i : ℝ) ≤ (n.factorial : ℝ) := by
      have h : n.descFactorial i ≤ n.factorial := by
        rw [Nat.descFactorial_eq_div hi]
        exact Nat.div_le_self _ _
      exact_mod_cast h
    have hxw : |x| ^ (n - i) ≤ (2 / a) ^ (n - i) :=
      pow_le_pow_left₀ (abs_nonneg x) hx _
    have hdiv : (2 / a) ^ (n - i) = 2 ^ (n - i) * a ^ ((i : ℤ) - (n : ℤ)) := by
      rw [div_pow, div_eq_mul_inv]
      have hk : ((i : ℤ) - (n : ℤ)) = -(((n - i : ℕ)) : ℤ) := by
        have := Nat.cast_sub (R := ℤ) hi
        omega
      rw [hk, zpow_neg, zpow_natCast]
    calc (n.descFactorial i : ℝ) * |x| ^ (n - i)
        ≤ (n.factorial : ℝ) * |x| ^ (n - i) := by gcongr
      _ ≤ (n.factorial : ℝ) * (2 / a) ^ (n - i) := by gcongr
      _ = (n.factorial : ℝ) * 2 ^ (n - i) * a ^ ((i : ℤ) - (n : ℤ)) := by
            rw [hdiv]; ring
  · have h0 : n.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow, h0]
    simp only [Nat.cast_zero, zero_mul, norm_zero]
    exact hnn

/-- The `j`-th derivative of `z ↦ φ (a * z)`. -/
private lemma norm_iteratedFDeriv_borelBump_mul_le (b : ℕ → ℂ) (n j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ => borelBump (borelA b n * y)) x‖
      ≤ (j.factorial : ℝ) * borelBound j * (borelA b n) ^ j := by
  have ha1 : (1 : ℝ) ≤ borelA b n := one_le_borelA b n
  have hrew : (fun y : ℝ => borelBump (borelA b n * y))
      = fun z : ℝ => borelBump (borelA b n • z) := by
    funext z; rw [smul_eq_mul]
  rw [hrew, iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (borelA b n)
    (borelBump_contDiff.of_le (coe_nat_le_smooth j))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_trans zero_le_one ha1) j)]
  calc (borelA b n) ^ j * ‖iteratedFDeriv ℝ j borelBump (borelA b n • x)‖
      ≤ (borelA b n) ^ j * borelBound j := by
        gcongr
        exact le_borelBound le_rfl _
    _ ≤ (j.factorial : ℝ) * borelBound j * (borelA b n) ^ j := by
        have h1 : (1 : ℝ) ≤ (j.factorial : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j)
        rw [mul_comm ((borelA b n) ^ j) (borelBound j), mul_assoc]
        exact le_mul_of_one_le_left
          (mul_nonneg (borelBound_nonneg j) (pow_nonneg (le_trans zero_le_one ha1) j)) h1

/-- The binomial-type sum appearing in the product rule. -/
private lemma sum_choose_pow_le (n k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (↑(k.choose i) * 2 ^ (n - i) * (k - i).factorial : ℝ)
      ≤ (k.factorial : ℝ) * 2 ^ (n + k) := by
  have hb : ∀ i ∈ Finset.range (k + 1),
      (↑(k.choose i) * 2 ^ (n - i) * (k - i).factorial : ℝ) ≤ (k.factorial : ℝ) * 2 ^ n := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hif : 1 ≤ i.factorial := Nat.succ_le_of_lt (Nat.factorial_pos i)
    have hchoose : (↑(k.choose i) * (k - i).factorial : ℝ) ≤ (k.factorial : ℝ) := by
      have hnat : k.choose i * (k - i).factorial ≤ k.factorial := by
        calc k.choose i * (k - i).factorial
            = 1 * (k.choose i * (k - i).factorial) := (one_mul _).symm
          _ ≤ (i.factorial) * (k.choose i * (k - i).factorial) :=
                Nat.mul_le_mul_right _ hif
          _ = k.choose i * i.factorial * (k - i).factorial := by ring
          _ = k.factorial := Nat.choose_mul_factorial_mul_factorial hik
      exact_mod_cast hnat
    have hpow : 2 ^ (n - i) ≤ (2 : ℝ) ^ n :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le n i)
    calc (↑(k.choose i) * 2 ^ (n - i) * (k - i).factorial : ℝ)
        = (↑(k.choose i) * (k - i).factorial) * 2 ^ (n - i) := by ring
      _ ≤ (k.factorial : ℝ) * 2 ^ n :=
            mul_le_mul hchoose hpow (by positivity) (Nat.cast_nonneg _)
  calc ∑ i ∈ Finset.range (k + 1), (↑(k.choose i) * 2 ^ (n - i) * (k - i).factorial : ℝ)
      ≤ ∑ _i ∈ Finset.range (k + 1), ((k.factorial : ℝ) * 2 ^ n) := Finset.sum_le_sum hb
    _ = (k + 1 : ℝ) * ((k.factorial : ℝ) * 2 ^ n) := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (k.factorial : ℝ) * 2 ^ k * 2 ^ n := by
          have h1 : (k + 1 : ℝ) ≤ 2 ^ k := by
            exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k)))
          have h2 : (0 : ℝ) ≤ (k.factorial : ℝ) * 2 ^ n :=
            mul_nonneg (Nat.cast_nonneg _) (by positivity)
          calc (k + 1 : ℝ) * ((k.factorial : ℝ) * 2 ^ n)
              ≤ 2 ^ k * ((k.factorial : ℝ) * 2 ^ n) :=
                mul_le_mul_of_nonneg_right h1 h2
            _ = (k.factorial : ℝ) * 2 ^ k * 2 ^ n := by ring
    _ = (k.factorial : ℝ) * 2 ^ (n + k) := by
          rw [mul_assoc, ← pow_add, Nat.add_comm]

private lemma zpow_sub_mul_pow {a : ℝ} (ha : a ≠ 0) {n i k : ℕ} (hik : i ≤ k) :
    a ^ ((i : ℤ) - (n : ℤ)) * a ^ (k - i) = a ^ ((k : ℤ) - (n : ℤ)) := by
  rw [← zpow_natCast a (k - i), ← zpow_add₀ ha]
  congr 1
  have := Nat.cast_sub (R := ℤ) hik
  omega

/-- The main estimate: the `k`-th derivative of the `n`-th summand of the real part. -/
private lemma norm_iteratedFDeriv_borelHTerm_le (b : ℕ → ℂ) (n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (borelHTerm b n) x‖
      ≤ (n.factorial : ℝ) * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k)
          * (borelA b n) ^ ((k : ℤ) - (n : ℤ)) := by
  have ha : 0 < borelA b n := borelA_pos b n
  have hane : borelA b n ≠ 0 := ha.ne'
  have hconst : 0 ≤ (n.factorial : ℝ) * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k)
      * (borelA b n) ^ ((k : ℤ) - (n : ℤ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (borelBound_nonneg k)) (by positivity)) (zpow_pos ha _).le
  rcases le_or_gt |x| (2 / borelA b n) with hx | hx
  · have hmul := norm_iteratedFDeriv_mul_le
        (f := fun y : ℝ => y ^ n) (g := fun y : ℝ => borelBump (borelA b n * y))
        ((contDiff_id : ContDiff ℝ ∞ (fun y : ℝ => y)).pow n)
        (borelBump_contDiff.comp ((contDiff_const (c := borelA b n)).mul
          (contDiff_id : ContDiff ℝ ∞ (fun y : ℝ => y))))
        x (coe_nat_le_smooth k)
    refine hmul.trans ?_
    have hsum : ∑ i ∈ Finset.range (k + 1),
          ↑(k.choose i) * ‖iteratedFDeriv ℝ i (fun y : ℝ => y ^ n) x‖
            * ‖iteratedFDeriv ℝ (k - i) (fun y : ℝ => borelBump (borelA b n * y)) x‖
        ≤ ∑ i ∈ Finset.range (k + 1),
            (n.factorial : ℝ) * borelBound k * (borelA b n) ^ ((k : ℤ) - (n : ℤ))
              * (↑(k.choose i) * 2 ^ (n - i) * (k - i).factorial) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hP := norm_iteratedFDeriv_pow_le (n := n) (i := i) (x := x) ha hx
      have hPsi := norm_iteratedFDeriv_borelBump_mul_le (b := b) (n := n) (j := k - i) (x := x)
      have hPhi : borelBound (k - i) ≤ borelBound k := borelBound_mono (Nat.sub_le k i)
      have hPsi' : ‖iteratedFDeriv ℝ (k - i) (fun y : ℝ => borelBump (borelA b n * y)) x‖
          ≤ ((k - i).factorial : ℝ) * borelBound k * (borelA b n) ^ (k - i) := by
        refine hPsi.trans ?_
        gcongr
      have hz := zpow_sub_mul_pow (a := borelA b n) hane (n := n) (i := i) (k := k) hik
      calc ↑(k.choose i) * ‖iteratedFDeriv ℝ i (fun y : ℝ => y ^ n) x‖
              * ‖iteratedFDeriv ℝ (k - i) (fun y : ℝ => borelBump (borelA b n * y)) x‖
          ≤ ↑(k.choose i) * ((n.factorial : ℝ) * 2 ^ (n - i)
                * (borelA b n) ^ ((i : ℤ) - (n : ℤ)))
              * (((k - i).factorial : ℝ) * borelBound k * (borelA b n) ^ (k - i)) := by
            gcongr
        _ = (n.factorial : ℝ) * borelBound k * (borelA b n) ^ ((k : ℤ) - (n : ℤ))
              * (↑(k.choose i) * 2 ^ (n - i) * (k - i).factorial) := by
            rw [← hz]; ring
    refine hsum.trans ?_
    calc ∑ i ∈ Finset.range (k + 1),
            (n.factorial : ℝ) * borelBound k * (borelA b n) ^ ((k : ℤ) - (n : ℤ))
              * (↑(k.choose i) * (2 : ℝ) ^ (n - i) * (k - i).factorial)
        = (n.factorial : ℝ) * borelBound k * (borelA b n) ^ ((k : ℤ) - (n : ℤ))
            * ∑ i ∈ Finset.range (k + 1),
                (↑(k.choose i) * (2 : ℝ) ^ (n - i) * (k - i).factorial) := by
          rw [Finset.mul_sum]
      _ ≤ (n.factorial : ℝ) * borelBound k * (borelA b n) ^ ((k : ℤ) - (n : ℤ))
            * ((k.factorial : ℝ) * 2 ^ (n + k)) := by
          refine mul_le_mul_of_nonneg_left (sum_choose_pow_le n k) ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (borelBound_nonneg k)) (zpow_pos ha _).le
      _ = (n.factorial : ℝ) * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k)
            * (borelA b n) ^ ((k : ℤ) - (n : ℤ)) := by ring
  · have hlt : 2 < |borelA b n * x| := by
      rw [abs_mul, abs_of_nonneg (le_trans zero_le_one (one_le_borelA b n))]
      have : 2 / borelA b n * borelA b n = 2 := by field_simp
      calc (2 : ℝ) = 2 / borelA b n * borelA b n := this.symm
        _ < |x| * borelA b n := mul_lt_mul_of_pos_right hx ha
        _ = borelA b n * |x| := by ring
    have heq : borelHTerm b n =ᶠ[𝓝 x] 0 := by
      filter_upwards [borelBump_eventually_eq_zero hlt] with z hz
      simp [borelHTerm, hz]
    have hzero : iteratedFDeriv ℝ k (borelHTerm b n) x
        = iteratedFDeriv ℝ k (fun _ : ℝ => (0 : ℝ)) x :=
      (heq.iteratedFDeriv ℝ k).eq_of_nhds
    rw [hzero]
    have hz0 : ‖iteratedFDeriv ℝ k (fun _ : ℝ => (0 : ℝ)) x‖ = 0 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rw [norm_iteratedFDeriv_zero]
        simp
      · rw [iteratedFDeriv_const_of_ne (by omega : k ≠ 0) (0 : ℝ)]
        simp
    rw [hz0]
    exact hconst

/-- The `k`-th derivative of the `n`-th complex summand. -/
private lemma norm_iteratedFDeriv_borelTerm_le (b : ℕ → ℂ) (n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (borelTerm b n) x‖
      ≤ ‖b n‖ * (k.factorial : ℝ) * borelBound k * 2 ^ (n + k)
          * (borelA b n) ^ ((k : ℤ) - (n : ℤ)) := by
  rw [borelTerm, iteratedFDeriv_const_smul_apply (contDiffAt_borelTerm b n k x), norm_smul]
  have hnorm : ‖iteratedFDeriv ℝ k (fun x : ℝ => ((borelHTerm b n x : ℝ) : ℂ)) x‖
      = ‖iteratedFDeriv ℝ k (borelHTerm b n) x‖ := by
    have hcomp : (fun x : ℝ => ((borelHTerm b n x : ℝ) : ℂ))
        = ⇑Complex.ofRealLI ∘ borelHTerm b n := rfl
    rw [hcomp, LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI
      (contDiff_borelHTerm b n).contDiffAt (coe_nat_le_smooth k)]
  rw [hnorm]
  have hc : ‖b n / (n.factorial : ℂ)‖ = ‖b n‖ / (n.factorial : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
  rw [hc]
  refine (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_borelHTerm_le b n k x)
    (by positivity)).trans (le_of_eq ?_)
  have hne : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

private lemma norm_iteratedFDeriv_borelTerm_le_v (b : ℕ → ℂ) (k n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (borelTerm b n) x‖ ≤ borelV b k n :=
  (norm_iteratedFDeriv_borelTerm_le b n k x).trans (le_add_of_nonneg_right (by positivity))

/-! ### The derivatives of the summands at `0` -/

lemma iteratedDeriv_borelTerm (b : ℕ → ℂ) (n m : ℕ) :
    iteratedDeriv m (borelTerm b n) 0 = if m = n then b n else 0 := by
  have hsmul : iteratedDeriv m (borelTerm b n) 0
      = (b n / (n.factorial : ℂ))
          • iteratedDeriv m (fun x : ℝ => ((borelHTerm b n x : ℝ) : ℂ)) 0 := by
    rw [borelTerm]
    exact iteratedDeriv_const_smul (contDiffAt_borelTerm b n m 0) _
  rw [hsmul, iteratedDeriv_ofReal]
  have hh : ((iteratedDeriv m (borelHTerm b n) 0 : ℝ) : ℂ)
      = if m = n then (n.factorial : ℂ) else 0 := by
    have heq : borelHTerm b n =ᶠ[𝓝 0] (fun y : ℝ => y ^ n) := by
      have ha1 : 1 ≤ borelA b n := one_le_borelA b n
      have hpos : 0 < (borelA b n)⁻¹ := inv_pos.mpr (borelA_pos b n)
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with y hy
      have hy' : |y| ≤ 1 / borelA b n := by
        rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
        rw [one_div]
        exact le_of_lt hy
      have hle1 : |borelA b n * y| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (le_trans zero_le_one ha1)]
        calc borelA b n * |y| ≤ borelA b n * (1 / borelA b n) :=
              mul_le_mul_of_nonneg_left hy' (le_trans zero_le_one ha1)
          _ = 1 := by field_simp
      rw [borelHTerm, borelBump_one hle1, mul_one]
    rw [heq.iteratedDeriv_eq m, iteratedDeriv_fun_pow_zero]
    by_cases h : m = n <;> simp [h]
  rw [hh]
  by_cases hmn : m = n
  · have hnz : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp only [if_pos hmn]
    rw [smul_eq_mul, div_mul_cancel₀ _ hnz]
  · simp only [if_neg hmn, smul_zero]

/-! ### The final theorem -/

theorem borel_lemma (b : ℕ → ℂ) :
    ∃ W : ℝ → ℂ, ContDiff ℝ Work.RadialSpace.Smooth W ∧ ∀ m : ℕ, iteratedDeriv m W 0 = b m := by
  refine ⟨borelW b, ?_, fun m => ?_⟩
  · have h := contDiff_tsum (𝕜 := ℝ) (N := (⊤ : ℕ∞)) (f := fun n => borelTerm b n)
      (v := borelV b) (fun n => contDiff_borelTerm b n)
      (fun k _ => summable_borelV b k)
      (fun k n x _ => norm_iteratedFDeriv_borelTerm_le_v b k n x)
    unfold borelW
    exact h
  · have hsumm : Summable (fun n => iteratedFDeriv ℝ m (borelTerm b n) 0) :=
      Summable.of_norm_bounded (summable_borelV b m)
        (fun n => norm_iteratedFDeriv_borelTerm_le_v b m n 0)
    have hW : iteratedFDeriv ℝ m (borelW b) 0
        = ∑' n, iteratedFDeriv ℝ m (borelTerm b n) 0 :=
      iteratedFDeriv_tsum_apply (N := ⊤) (f := fun n => borelTerm b n) (v := borelV b)
        (fun n => contDiff_borelTerm b n) (fun k _ => summable_borelV b k)
        (fun k n x _ => norm_iteratedFDeriv_borelTerm_le_v b k n x) le_top 0
    have key : (∑' n, iteratedFDeriv ℝ m (borelTerm b n) 0) (fun _ : Fin m => (1 : ℝ))
        = ∑' n, (iteratedFDeriv ℝ m (borelTerm b n) 0) (fun _ : Fin m => (1 : ℝ)) :=
      ContinuousLinearMap.map_tsum (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ) ℂ
        (fun _ : Fin m => (1 : ℝ))) hsumm
    have hderiv : iteratedDeriv m (borelW b) 0
        = ∑' n, iteratedDeriv m (borelTerm b n) 0 := by
      have h1 : iteratedDeriv m (borelW b) 0
          = (∑' n, iteratedFDeriv ℝ m (borelTerm b n) 0) (fun _ : Fin m => (1 : ℝ)) := by
        rw [iteratedDeriv_eq_iteratedFDeriv, hW]
      rw [h1, key]
      rfl
    rw [hderiv, tsum_eq_single m]
    · rw [iteratedDeriv_borelTerm, if_pos rfl]
    · intro n hn
      rw [iteratedDeriv_borelTerm, if_neg (fun h : m = n => hn h.symm)]

end Work.RadialSpace
