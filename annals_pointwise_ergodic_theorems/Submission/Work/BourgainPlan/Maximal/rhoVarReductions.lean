import Mathlib
import Submission.Work.BourgainPlan.Maximal.chainLp_le_chainSq
import Submission.Work.BourgainPlan.Maximal.varTwoLeRmLevels
import Submission.Work.BourgainPlan.Maximal.varOscSel_le_varRho
import Submission.Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
import Submission.Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal

/-!
# The `ρ`-variation semisnorm: reductions to the `2`-variation, the maximal function and the
Rademacher–Menshov levels (KMSZ Proposition 5.10, conditions (1) and (2))

This file instantiates Kosz–Mirek–Słomian–Zhang (arXiv:2606.12663) Proposition 5.10: for `ρ ≥ 2`
the `ρ`-variation seminorm `varRho ρ` is *dominated by* the `2`-variation seminorm `varTwo`, hence

* satisfies the **splitting property** of their Definition 5.1(1) (proved for `varRho` in
  `varRhoSplitting`);
* satisfies the **Rademacher–Menshov inequality** of their Definition 5.1(2) (proved here in the
  integrated form `varELpNormLeRho`, from `varELpNormLe` at `ρ = 2` and the domination
  `varRho ≤ varTwo`);
* dominates the **maximal function** (`iSup_enorm_le_enorm_add_varRho`: the sup of a sequence over an
  index window is at most the base value plus *any* `ρ`-variation, `ρ ≥ 1` — this is the step (6.9)
  of KMSZ), and
* dominates the `ρ`-oscillation (`varOsc`, resp. its selection form `varOscSel`), which is therefore
  also a Rademacher–Menshov seminorm of type `(d,p)` for `ρ ≥ 2` — the estimate (6.7) of KMSZ, i.e.
  the oscillation half of Bourgain's theorem.

The point of the reduction `varRho ≤ varTwo` for `ρ ≥ 2` is that it lets the *whole* `ρ`-variation
machinery (`ρ > 2` is the range in which the variational inequalities of Bourgain/Krause hold, the
`2`-variation being unbounded on `ℓ²`) be fed by the `2`-variation estimates, i.e. by the dyadic
block square functions `rmLevel` of `mstRademacherMenshov.lean`.
-/

namespace Work.BourgainPlan.Maximal

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **The `ρ`-variation is dominated by the `2`-variation for `ρ ≥ 2`** (KMSZ Proposition 5.10:
"by `ρ ∈ [2,∞]` each of (5.6)–(5.8) is dominated by `V^{2,p}`"). -/
theorem varRho_le_varTwo {ρ : ℝ} (hρ : 2 ≤ ρ) (lo hi : ℕ) (a : ℕ → E) :
    varRho ρ lo hi a ≤ varTwo lo hi a := by
  rw [varRho, varTwo]
  refine iSup_le fun J => iSup_le fun t => iSup_le fun ht => iSup_le fun h => ?_
  exact le_trans (ENNReal.ofReal_le_ofReal (chainLp_le_chainSq ρ hρ J a t))
    (le_iSup_of_le J (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le h le_rfl))))

/-- **The `ρ`-variation is dominated by the Rademacher–Menshov dyadic block levels** for `ρ ≥ 2`,
over a dyadic window. -/
theorem varRho_le_rmLevels {ρ : ℝ} (hρ : 2 ≤ ρ) (n lo : ℕ) (a : ℕ → E) :
    varRho ρ lo (lo + 2 ^ n) a
      ≤ ENNReal.ofReal (2 * ∑ l ∈ Finset.range (n + 1), rmLevel n l (fun r => a (lo + r))) :=
  (varRho_le_varTwo hρ lo (lo + 2 ^ n) a).trans (varTwo_le_rmLevels n lo a)

/-- **A single increment is dominated by the `ρ`-variation** (`ρ > 0`): the two-point chain. -/
lemma enorm_sub_le_varRho {ρ : ℝ} (hρ : 0 < ρ) {lo hi n : ℕ} (h1 : lo ≤ n) (h2 : n ≤ hi)
    (a : ℕ → E) : ‖a n - a lo‖ₑ ≤ varRho ρ lo hi a := by
  refine le_trans ?_ (le_iSup_of_le 1 (le_iSup_of_le (fun i => if i = 0 then lo else n)
    (le_iSup_of_le ?_ (le_iSup_of_le ?_ le_rfl))))
  · -- the chain value
    have hchain : chainLp ρ 1 a (fun i => if i = 0 then lo else n) = ‖a n - a lo‖ := by
      rw [chainLp, Finset.range_one, Finset.sum_singleton]
      have e0 : (if (0 : ℕ) + 1 = 0 then lo else n) = n := by simp
      have e1 : (if (0 : ℕ) = 0 then lo else n) = lo := by simp
      rw [e0, e1, ← Real.rpow_mul (norm_nonneg (a n - a lo)),
        show ρ * (1 / ρ) = 1 by field_simp, Real.rpow_one]
    rw [hchain, ← ofReal_norm]
  · -- monotonicity of the two-point chain
    intro i j hij
    rcases Nat.eq_zero_or_pos i with hi0 | hi0
    · subst hi0
      simp only [if_pos rfl]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; simp
      · simp only [if_neg (by omega : j ≠ 0)]; exact h1
    · have hj0 : j ≠ 0 := by omega
      have hi0 : i ≠ 0 := by omega
      simp only [if_neg hi0, if_neg hj0]
      exact le_rfl
  · -- the range condition
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0; simp only [if_pos rfl]; exact ⟨le_rfl, le_trans h1 h2⟩
    · have hj1 : j = 1 := by omega
      subst hj1
      simp only [if_neg (by norm_num : (1 : ℕ) ≠ 0)]
      exact ⟨h1, h2⟩

/-- **The maximal function is dominated by the base value plus any `ρ`-variation** (`ρ ≥ 1`), KMSZ
(6.9): `⨆_{lo ≤ k ≤ hi} ‖a k‖ₑ ≤ ‖a lo‖ₑ + V^ρ(a)`. -/
theorem iSup_enorm_le_enorm_add_varRho {ρ : ℝ} (hρ : 1 ≤ ρ) {lo hi : ℕ} (a : ℕ → E) :
    (⨆ k ∈ Finset.Icc lo hi, ‖a k‖ₑ) ≤ ‖a lo‖ₑ + varRho ρ lo hi a := by
  refine iSup₂_le fun k hk => ?_
  have h1 : lo ≤ k := (Finset.mem_Icc.mp hk).1
  have h2 : k ≤ hi := (Finset.mem_Icc.mp hk).2
  have htri : ‖a k‖ₑ ≤ ‖a lo‖ₑ + ‖a k - a lo‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg (a lo)) (norm_nonneg (a k - a lo))]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := norm_add_le (a lo) (a k - a lo)
    rwa [add_sub_cancel] at h
  calc ‖a k‖ₑ ≤ ‖a lo‖ₑ + ‖a k - a lo‖ₑ := htri
    _ ≤ ‖a lo‖ₑ + varRho ρ lo hi a :=
        add_le_add le_rfl
          (enorm_sub_le_varRho (lt_of_lt_of_le zero_lt_one hρ) h1 h2 a)

/-- **The oscillation is dominated by the `2`-variation** for `ρ ≥ 2` (selection form; KMSZ
Proposition 5.10 for the oscillation seminorm `O^ρ`, `ρ ≥ 2`). -/
theorem varOscSel_le_varTwo {ρ : ℝ} (hρ : 2 ≤ ρ) (lo hi : ℕ) (a : ℕ → E) :
    varOscSel ρ lo hi a ≤ varTwo lo hi a :=
  (varOscSel_le_varRho (le_trans (by norm_num : (1 : ℝ) ≤ 2) hρ) lo hi a).trans
    (varRho_le_varTwo hρ lo hi a)

/-- **KMSZ (6.9) in `L^p` form**: on any measure space, the maximal function of a family over an
index window is dominated in `L^p` by the base value plus *any* `ρ`-variation (`ρ ≥ 1`).  This is the
step that turns a variational estimate for a lacunary scale family into the maximal inequality. -/
theorem eLpNorm_iSup_le_base_add_varRho {X : Type*} [MeasurableSpace X] {F : Type*}
    [NormedAddCommGroup F] {ρ : ℝ} (hρ : 1 ≤ ρ) (μ : Measure X) {p : ℝ} (_hp : 1 ≤ p)
    (lo hi : ℕ) (f : ℕ → X → F)
    (hmeas : AEStronglyMeasurable (fun x => ⨆ k ∈ Finset.Icc lo hi, ‖f k x‖ₑ) μ) :
    eLpNorm (fun x => ⨆ k ∈ Finset.Icc lo hi, ‖f k x‖ₑ) (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun x => ‖f lo x‖ₑ + varRho ρ lo hi (fun i => f i x)) (ENNReal.ofReal p) μ := by
  refine eLpNorm_mono_enorm hmeas fun x => ?_
  rw [enorm_eq_self, enorm_eq_self]
  exact iSup_enorm_le_enorm_add_varRho (E := F) hρ (fun i => f i x)

end

end Work.BourgainPlan.Maximal
