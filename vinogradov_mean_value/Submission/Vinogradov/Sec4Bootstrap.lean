/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.AsymModels
import Submission.Vinogradov.AsymLin
import Submission.Vinogradov.AsymLower
import Submission.Vinogradov.L2BaseCase
import Submission.Commons.Analysis.Asymptotics.exponent_bootstrap_nonpos

/-!
# The §4 exponent bootstrap of GLYZ

This module assembles the strong induction on the degree `k` which proves `etaLin k ≤ 0` for every
`k ≥ 1`, and hence (through `Section4Exp.exists_decLinScale_of_etaLin_nonpos`) the enlarged
`ℓ²`-decoupling theorem `glyz_decoupling`.

The auxiliary function of `Commons.Analysis.Asymptotics.exponent_bootstrap_nonpos` is

  `bsA k hk 0 b = etaLin k * (1 - b)`,   `bsA k hk k b = etaLin k`,
  `bsA k hk l b = Aexp k hk l b`  (`1 ≤ l ≤ k - 1`).

With this definition `hA0` is `rfl`, `hbdd` at `l = 0` and `l = k` is trivial, `hrec` at `l = 1`
is `AsymRecIneq.asymExpSet_recursion_one_ineq` (whose second term is exactly `etaLin k (1-b)`) and
at `l ≥ 2` is `AsymRecIneq.asymExpSet_recursion_ineq`, fed with the degree-`L` models built from
the induction hypothesis by `AsymModels.exists_models_of_etaLin_le_zero`.

`hbdd` uses the two unconditional steps:
* Step 3 (`AsymLin.Aexp_le_linCoef_mul_etaLin`): `A_l(b) ≤ linCoef k l b · η`;
* Step 4 (`AsymLower.etaLin_le_bilinCoef_Aexp`): `η ≤ b · bilinCoef k l + A_l(b)`,
together with `AsymLower.one_sub_linCoef : 1 − linCoef k l b = b · bilinCoef k l`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Submission.Vinogradov

/-! ## 1. The auxiliary function of the bootstrap -/

/-- The auxiliary function `A` of the §4 exponent bootstrap.  It is the definition (not a theorem)
that makes `hA0` and the `l = 0`, `l = k` cases of `hbdd` trivial. -/
noncomputable def bsA (k : ℕ) (hk : 1 ≤ k) : ℕ → ℝ → ℝ :=
  fun l b => if l = 0 then etaLin k * (1 - b) else if l = k then etaLin k else Aexp k hk l b

lemma bsA_zero {k : ℕ} (hk : 1 ≤ k) (b : ℝ) : bsA k hk 0 b = etaLin k * (1 - b) := by
  simp [bsA]

lemma bsA_self {k : ℕ} (hk : 1 ≤ k) (b : ℝ) : bsA k hk k b = etaLin k := by
  have hk0 : k ≠ 0 := by omega
  simp [bsA, hk0]

lemma bsA_of {k l : ℕ} (hk : 1 ≤ k) (hl1 : 1 ≤ l) (hlk : l ≤ k - 1) (b : ℝ) :
    bsA k hk l b = Aexp k hk l b := by
  have h1 : l ≠ 0 := by omega
  have h2 : l ≠ k := by omega
  simp [bsA, h1, h2]

/-! ## 2. The models with a single constant -/

/-- **The degree-`L` models of the recursion, in the `εm`-dependent form consumed by
`AsymRec.asymExpSet_recursion`.**  For every `εm > 0` there is a constant `a₀ ≥ 1` with
`DecLinScale L M (laneEnl k L hk hl hlk) (ofReal (a₀ M^εm))` for every `M ≥ 1`. -/
theorem exists_models_eps {k L : ℕ} (hk : 1 ≤ k) (hL1 : 1 ≤ L) (hLk : L ≤ k)
    (hη : etaLin L ≤ 0) :
    ∀ (εm : ℝ), 0 < εm → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
      DecLinScale L M (laneEnl k L hk hL1 hLk) (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm)) :=
  fun εm hεm => exists_models_of_etaLin_le_zero hk hL1 hLk hη hεm

/-! ## 3. `hbdd`: the boundedness of `(η − A_l(b))/b` -/

lemma eventually_small {k l : ℕ} (hk : 1 ≤ k) (hl1 : 1 ≤ l) (hlk : l ≤ k) :
    ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ),
      0 < b ∧ b ≤ 1 ∧ b ≤ b₀ k ∧ asymRatio k l * b ≤ 1 := by
  have hρ0 : 0 ≤ asymRatio k l := (asymRatio_pos hk hl1 hlk).le
  rcases eq_or_lt_of_le hρ0 with h | h
  · have hev : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), 0 < b ∧ b ≤ 1 ∧ b ≤ b₀ k := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iic_mem_nhds (show (0:ℝ) < min 1 (b₀ k) by
        exact lt_min one_pos (b₀_pos k))] with b hb hb0
      exact ⟨hb0, le_trans hb (min_le_left _ _), le_trans hb (min_le_right _ _)⟩
    refine hev.mono fun b hb => ?_
    exact ⟨hb.1, hb.2.1, hb.2.2, by rw [← h]; norm_num⟩
  · have hρpos : 0 < asymRatio k l := h
    have hev : ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ),
        0 < b ∧ b ≤ 1 ∧ b ≤ b₀ k ∧ b ≤ 1 / asymRatio k l := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [Iic_mem_nhds (show (0:ℝ) < min (min 1 (b₀ k)) (1 / asymRatio k l) by
        exact lt_min (lt_min one_pos (b₀_pos k)) (by positivity))] with b hb hb0
      exact ⟨hb0, le_trans hb (le_trans (min_le_left _ _) (min_le_left _ _)),
        le_trans hb (le_trans (min_le_left _ _) (min_le_right _ _)),
        le_trans hb (min_le_right _ _)⟩
    refine hev.mono fun b hb => ?_
    exact ⟨hb.1, hb.2.1, hb.2.2.1, by
      rw [mul_comm]
      exact (le_div_iff₀ hρpos).mp hb.2.2.2⟩

/-- **`hbdd` of the bootstrap**: `(η − A_l(b))/b` is bounded near `0⁺`. -/
theorem exists_bdd_bsA {k : ℕ} (hk : 2 ≤ k) (hk1 : 1 ≤ k) (l : ℕ) (hl : l ≤ k) :
    ∃ M : ℝ, ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ), |(etaLin k - bsA k hk1 l b) / b| ≤ M := by
  rcases eq_or_lt_of_le (Nat.zero_le l) with h | hl1
  · -- `l = 0`
    subst h
    exact ⟨|etaLin k|, by
      filter_upwards [self_mem_nhdsWithin] with b hb
      have hb0 : (0:ℝ) < b := hb
      rw [bsA_zero]
      have : (etaLin k - etaLin k * (1 - b)) / b = etaLin k := by
        field_simp
        ring
      rw [this]⟩
  · rcases eq_or_lt_of_le hl with hk_eq | hlt
    · -- `l = k`
      subst hk_eq
      exact ⟨0, by
        filter_upwards [self_mem_nhdsWithin] with b hb
        rw [bsA_self, sub_self, zero_div, abs_zero]⟩
    · -- `1 ≤ l ≤ k − 1`
      have hlk : l ≤ k - 1 := by omega
      refine ⟨max |bilinCoef k l * etaLin k| |bilinCoef k l|, ?_⟩
      filter_upwards [eventually_small hk1 hl1 (by omega)] with b hb
      obtain ⟨hb0, hb1, hb2, hρb⟩ := hb
      rw [bsA_of hk1 hl1 hlk]
      have h3 := Aexp_le_linCoef_mul_etaLin hk1 hl1 hlk hb0 hb2
      have h4 := etaLin_le_bilinCoef_Aexp hk1 hl1 hlk hb0 hb1 hρb
      have h5 := one_sub_linCoef (k := k) (l := l) hk1 b
      have hA : (etaLin k - Aexp k hk1 l b) ≤ b * bilinCoef k l := by linarith [h4]
      have hB : b * bilinCoef k l * etaLin k ≤ (etaLin k - Aexp k hk1 l b) :=
        calc b * bilinCoef k l * etaLin k
            = (1 - linCoef k l b) * etaLin k := by rw [h5]
          _ = etaLin k - linCoef k l b * etaLin k := by ring
          _ ≤ etaLin k - Aexp k hk1 l b := by linarith [h3]
      have hdiv1 : (etaLin k - Aexp k hk1 l b) / b ≤ bilinCoef k l := by
        rw [div_le_iff₀ hb0]
        linarith [hA]
      have hdiv2 : bilinCoef k l * etaLin k ≤ (etaLin k - Aexp k hk1 l b) / b := by
        rw [le_div_iff₀ hb0]
        have h7 : b * (bilinCoef k l * etaLin k) = b * bilinCoef k l * etaLin k := by ring
        linarith [hB, h7]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h9 : -(max |bilinCoef k l * etaLin k| |bilinCoef k l|)
            ≤ -|bilinCoef k l * etaLin k| :=
          neg_le_neg (le_max_left _ _)
        have h10 := neg_abs_le (bilinCoef k l * etaLin k)
        linarith [h9, h10, hdiv2]
      · have h11 : bilinCoef k l ≤ |bilinCoef k l| := le_abs_self _
        have h12 : |bilinCoef k l| ≤ max |bilinCoef k l * etaLin k| |bilinCoef k l| :=
          le_max_right _ _
        linarith [hdiv1, h11, h12]

/-! ## 4. `hrec`: the recursion for the auxiliary function `bsA` -/

set_option maxHeartbeats 16000000 in
/-- **`hrec` of the bootstrap**: the recursion inequality for the auxiliary function `bsA`. -/
theorem eventually_rec_bsA {k : ℕ} (hk2 : 2 ≤ k) (hk1 : 1 ≤ k)
    (hih : ∀ L, 1 ≤ L → L < k → etaLin L ≤ 0)
    (l : ℕ) (hl1 : 1 ≤ l) (hlk : l ≤ k - 1) :
    ∀ᶠ b : ℝ in 𝓝[>] (0 : ℝ),
      bsA k hk1 l b
        ≤ (1 / ((k : ℝ) - (l : ℝ) + 1)) * bsA k hk1 (k - l)
            ((((k : ℝ) - (l : ℝ) + 1) / (l : ℝ)) * b)
        + (((k : ℝ) - (l : ℝ)) / ((k : ℝ) - (l : ℝ) + 1)) * bsA k hk1 (l - 1) b := by
  have hlk' : l ≤ k := by omega
  have hkl1 : 1 ≤ k - l := by omega
  have hklk : k - l ≤ k := by omega
  rcases eq_or_lt_of_le hl1 with h1 | hl2
  · -- `l = 1`
    subst h1
    have hk2' : 1 ≤ k - 1 := by omega
    have hmod : ∀ (εm : ℝ), 0 < εm → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
        DecLinScale (k - 1) M (laneEnl k (k - 1) hk1 (by omega) (by omega))
          (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm)) :=
      fun εm hεm => exists_models_eps hk1 (by omega) (by omega)
        (hih (k - 1) (by omega) (by omega)) εm hεm
    have h := asymExpSet_recursion_one_ineq hk1 hk2' hmod
    rw [asymRatio_one] at h
    refine h.mono fun b hb => ?_
    rw [bsA_of hk1 le_rfl (by omega),
      bsA_of hk1 (show 1 ≤ k - 1 by omega) (by omega),
      show (1 : ℕ) - 1 = 0 from rfl, bsA_zero (k := k) hk1 b]
    convert hb using 2 <;> push_cast <;> ring
  · -- `l ≥ 2`
    have hmod₁ : ∀ (εm : ℝ), 0 < εm → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
        DecLinScale (k - l) M (laneEnl k (k - l) hk1 (by omega) (by omega))
          (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm)) :=
      fun εm hεm => exists_models_eps hk1 hkl1 hklk (hih (k - l) hkl1 (by omega)) εm hεm
    have hmod₂ : ∀ (εm : ℝ), 0 < εm → ∃ a₀ : ℝ, 1 ≤ a₀ ∧ ∀ M : ℕ, 1 ≤ M →
        DecLinScale (l - 1) M (laneEnl k (l - 1) hk1 (by omega) (by omega))
          (ENNReal.ofReal (a₀ * (M : ℝ) ^ εm)) :=
      fun εm hεm => exists_models_eps hk1 (by omega) (by omega)
        (hih (l - 1) (by omega) (by omega)) εm hεm
    have h := asymExpSet_recursion_ineq hk1 hl2 hlk hmod₁ hmod₂
    rw [asymRatio_of_pos hl1] at h
    refine h.mono fun b hb => ?_
    rw [bsA_of hk1 hl1 hlk, bsA_of hk1 hkl1 (by omega),
      bsA_of hk1 (show 1 ≤ l - 1 by omega) (by omega)]
    exact hb

/-! ## 5. The §4 exponent bootstrap -/

/-- **GLYZ §4, the exponent bootstrap**: the decoupling exponent of the moment curve of degree `k`
is nonpositive. -/
theorem etaLin_nonpos (k : ℕ) (hk : 1 ≤ k) : etaLin k ≤ 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases eq_or_lt_of_le hk with h1 | hk2
    · rw [← h1]; exact etaLin_one_le_zero
    · have hk2' : 2 ≤ k := hk2
      have hk1 : 1 ≤ k := by omega
      have hih : ∀ L, 1 ≤ L → L < k → etaLin L ≤ 0 := fun L hL1 hLk => ih L hLk hL1
      refine Commons.Analysis.Asymptotics.exponent_bootstrap_nonpos hk2' (etaLin k)
        (bsA k hk1) ?_ ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with b _
        exact bsA_zero hk1 b
      · intro l hl
        exact exists_bdd_bsA hk2' hk1 l hl
      · intro l hl1 hlk
        exact eventually_rec_bsA hk2' hk1 hih l hl1 hlk

end Submission.Vinogradov
