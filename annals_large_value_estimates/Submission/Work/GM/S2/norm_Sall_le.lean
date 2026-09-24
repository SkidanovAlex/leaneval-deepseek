import Mathlib
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.hhat_neg_symm

/-!
# `‖Sall N t‖ ≤ ‖Spos N t‖ + ‖Spos N (-t)‖`

The full `m`-sum `Sall N t = Σ'_{m ≠ 0} ĥ_t(mN)` splits into its positive and negative
halves.  The reflection symmetry `ĥ_t(-ξ) = conj (ĥ_{-t}(ξ))` (`hsymm`) identifies the
negative half `Σ'_{k ≥ 0} ĥ_t(-(k+1)N)` with `conj (Spos N (-t))`, and the triangle
inequality gives the claim.

The splitting is done with the Mathlib lemmas `tsum_subtype` (to pass from the subtype
`{m // m ≠ 0}` to `ℤ`) and `tsum_of_add_one_of_neg_add_one` (to split a `ℤ`-sum into its
nonnegative and negative parts); both need the summand to be summable, which is supplied
by the decay hypothesis `hdec` (compared against the convergent series `Σ |m|^{-2}`).
-/

open Complex MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Work.GM.S2

/-- The full `m`-sum written as a sum over `ℤ`: the `m = 0` term is set to `0`
(so that `Σ'_{m ≠ 0} ĥ_t(mN) = Σ_{m ∈ ℤ} gfull N t m`). -/
noncomputable def gfull (N : ℕ) (t : ℝ) : ℤ → ℂ :=
  fun m => if m = 0 then 0 else Submission.GM.hhat t ((m : ℝ) * (N : ℝ))

/-- `gfull N t` is summable: `hdec` bounds `‖ĥ_t(mN)‖ ≤ C (1+|t|)^2 / |mN|^2`, and
`Σ_{m ∈ ℤ} |m|^{-2}` converges. -/
private lemma summable_gfull (hdec : Work.GM.S2.DecHyp) (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    Summable (gfull N t) := by
  obtain ⟨C, hCpos, hC⟩ := hdec 2
  have hbase : Summable (fun m : ℤ => C * (1 + |t|) ^ 2 * (((|(m : ℝ)| : ℝ)) ^ 2)⁻¹) := by
    refine summable_int_iff_summable_nat_and_neg.mpr ⟨?_, ?_⟩
    · have h := ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : 1 < 2)).mul_left
        (C * (1 + |t|) ^ 2)
      refine h.congr (fun n => ?_)
      simp only [Int.cast_natCast, Nat.abs_cast, div_eq_mul_inv, one_mul]
    · have h := ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : 1 < 2)).mul_left
        (C * (1 + |t|) ^ 2)
      refine h.congr (fun n => ?_)
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast, div_eq_mul_inv, one_mul]
  refine Summable.of_norm_bounded hbase (fun m => ?_)
  by_cases hm : m = 0
  · subst hm
    simp [gfull]
  · rw [gfull, if_neg hm]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hξ : (m : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero hmR (by positivity)
    have hb := hC t ((m : ℝ) * (N : ℝ)) hξ
    have hm2 : 0 < ((|(m : ℝ)| : ℝ)) ^ 2 := by positivity
    have hξ2 : 0 < ((|(m : ℝ) * (N : ℝ)| : ℝ)) ^ 2 := by positivity
    have habsξ : |((m : ℝ) * (N : ℝ))| = |(m : ℝ)| * (N : ℝ) := by
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) by positivity)]
    have hle1 : (|(m : ℝ)| : ℝ) ≤ |((m : ℝ) * (N : ℝ))| := by
      rw [habsξ]
      calc (|(m : ℝ)| : ℝ) = |(m : ℝ)| * 1 := by ring
        _ ≤ |(m : ℝ)| * (N : ℝ) := by
            gcongr
            exact_mod_cast hN
    have hle : ((|(m : ℝ)| : ℝ)) ^ 2 ≤ ((|(m : ℝ) * (N : ℝ)| : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hle1 2
    calc ‖Submission.GM.hhat t ((m : ℝ) * (N : ℝ))‖
        ≤ C * (1 + |t|) ^ 2 / |(m : ℝ) * (N : ℝ)| ^ 2 := hb
      _ = C * (1 + |t|) ^ 2 * ((|(m : ℝ) * (N : ℝ)| : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ C * (1 + |t|) ^ 2 * ((|(m : ℝ)| : ℝ) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left ((inv_le_inv₀ hξ2 hm2).mpr hle) (by positivity)

/-- `Sall` is the `ℤ`-sum of `gfull`. -/
private lemma Sall_eq_tsum_gfull (N : ℕ) (t : ℝ) :
    Work.GM.S2.Sall N t = ∑' m : ℤ, gfull N t m := by
  unfold Work.GM.S2.Sall
  refine (tsum_subtype (s := {m : ℤ | m ≠ 0})
    (f := fun m : ℤ => Submission.GM.hhat t ((m : ℝ) * (N : ℝ)))).trans ?_
  refine tsum_congr (fun m => ?_)
  by_cases h : m = 0 <;> simp [gfull, h]

/-- The positive half, written with `gfull`. -/
private lemma Spos_eq_tsum_gfull (N : ℕ) (t : ℝ) :
    Work.GM.S2.Spos N t = ∑' k : ℕ, gfull N t ((k : ℤ) + 1) := by
  unfold Work.GM.S2.Spos
  refine tsum_congr (fun k => ?_)
  have h1 : ((k : ℤ) + 1) ≠ 0 := by omega
  rw [gfull, if_neg h1]
  congr 1

/-- The negative half is the conjugate of `Spos N (-t)`, by the reflection symmetry. -/
private lemma conj_Spos_eq_tsum_gfull
    (hsymm : ∀ t ξ : ℝ, Submission.GM.hhat t (-ξ) = (starRingEnd ℂ) (Submission.GM.hhat (-t) ξ))
    (N : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (Work.GM.S2.Spos N (-t))
      = ∑' k : ℕ, gfull N t (-((k : ℤ) + 1)) := by
  unfold Work.GM.S2.Spos
  rw [Complex.conj_tsum]
  refine tsum_congr (fun k => ?_)
  have key : gfull N t (-((k : ℤ) + 1))
      = Submission.GM.hhat t (-((((k + 1 : ℕ)) : ℝ) * (N : ℝ))) := by
    rw [gfull, if_neg (by omega : -((k : ℤ) + 1) ≠ 0)]
    congr 1
    push_cast
    ring
  rw [key]
  exact (hsymm t ((((k + 1 : ℕ)) : ℝ) * (N : ℝ))).symm

theorem norm_Sall_le
    (hsymm : ∀ t ξ : ℝ, Submission.GM.hhat t (-ξ) = (starRingEnd ℂ) (Submission.GM.hhat (-t) ξ))
    (hdec : Work.GM.S2.DecHyp) (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    ‖Work.GM.S2.Sall N t‖ ≤ ‖Work.GM.S2.Spos N t‖ + ‖Work.GM.S2.Spos N (-t)‖ := by
  have hgs : Summable (gfull N t) := summable_gfull hdec N hN t
  have hsumm1 : Summable (fun n : ℕ => gfull N t ((n : ℤ) + 1)) :=
    hgs.comp_injective (fun a b h => by omega)
  have hsumm2 : Summable (fun n : ℕ => gfull N t (-((n : ℤ) + 1))) :=
    hgs.comp_injective (fun a b h => by omega)
  have hsplit := tsum_of_add_one_of_neg_add_one (f := gfull N t) hsumm1 hsumm2
  have hmain : Work.GM.S2.Sall N t
      = Work.GM.S2.Spos N t + (starRingEnd ℂ) (Work.GM.S2.Spos N (-t)) := by
    rw [Sall_eq_tsum_gfull, hsplit, ← Spos_eq_tsum_gfull, ← conj_Spos_eq_tsum_gfull hsymm]
    simp [gfull]
  calc ‖Work.GM.S2.Sall N t‖
      = ‖Work.GM.S2.Spos N t + (starRingEnd ℂ) (Work.GM.S2.Spos N (-t))‖ := by rw [hmain]
    _ ≤ ‖Work.GM.S2.Spos N t‖ + ‖(starRingEnd ℂ) (Work.GM.S2.Spos N (-t))‖ := norm_add_le _ _
    _ = ‖Work.GM.S2.Spos N t‖ + ‖Work.GM.S2.Spos N (-t)‖ := by rw [Complex.norm_conj]

end Work.GM.S2
