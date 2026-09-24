import Mathlib
import Submission.Work.GM.S2.pair_sum_defs
import Submission.Work.GM.S2.hhat_sum_tail

/-!
# GM §6: the "small" case of the inner sum over `m ≠ 0`

When `N` is large compared with `(1+|t|) T^η` — precisely
`(1+|t|) M^η ≤ N` with `M = N^{6/5}` — the decay of `ĥ_t` in the frequency
variable (GM Lemma 4.3(2), formalised as `DecHyp`) makes the whole series

`Sall N t = Σ_{m ≠ 0} ĥ_t(mN)`

small: it is `≪ M^{-η j}`, i.e. `≪ N^{-(6/5)ηj}`, for every fixed order `j ≥ 2`
with a constant depending only on `j`, `η` and the decay constant of `ĥ`.

The proof is the elementary one: `|ĥ_t(mN)| ≤ C_j (1+|t|)^j / (|m|^j N^j)`, the
constant factor `(1+|t|)^j N^{-j}` is `≤ M^{-ηj}` because `1+|t| ≤ N M^{-η}`, and
the `p`-series `Σ_{m≠0} |m|^{-j}` converges (uniformly in everything) for `j ≥ 2`.
-/

open Complex Finset MeasureTheory
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.S2

/-- The `p`-series `Σ_{m ≠ 0} |m|^{-j}` over the nonzero integers is summable. -/
lemma summable_subtype_int_abs_pow_inv {j : ℕ} (hj : 2 ≤ j) :
    Summable (fun m : {m : ℤ // m ≠ 0} => ((|(((m : ℤ) : ℝ))| : ℝ) ^ j)⁻¹) :=
  (summable_int_abs_pow_inv hj).subtype _

/-- GM §6, "N large": if `(1+|t|) M^η ≤ N` then `Σ_{m ≠ 0} ĥ_t(mN) ≪ M^{-η j}`. -/
theorem norm_Sall_small
    (hdec : Work.GM.S2.DecHyp) (j : ℕ) (hj : 2 ≤ j) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (t : ℝ),
      (1 + |t|) * (Submission.LargeValues.M N) ^ η ≤ (N : ℝ) →
      ‖Work.GM.S2.Sall N t‖ ≤ C * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))) := by
  obtain ⟨Cj, hCjpos, hCj⟩ := hdec j
  have hsumm_p : Summable (fun m : {m : ℤ // m ≠ 0} => ((|(((m : ℤ) : ℝ))| : ℝ) ^ j)⁻¹) :=
    summable_subtype_int_abs_pow_inv hj
  set S : ℝ := ∑' (m : {m : ℤ // m ≠ 0}), ((|(((m : ℤ) : ℝ))| : ℝ) ^ j)⁻¹ with hS
  have hS_ge_one : 1 ≤ S := by
    have hle := hsumm_p.le_tsum (i := ⟨(1 : ℤ), by norm_num⟩)
      (fun b _ => inv_nonneg.mpr (pow_nonneg (abs_nonneg _) j))
    rw [← hS] at hle
    simpa using hle
  have hS_nonneg : 0 ≤ S := le_trans zero_le_one hS_ge_one
  refine ⟨Cj * S, mul_pos hCjpos (lt_of_lt_of_le zero_lt_one hS_ge_one), ?_⟩
  intro N hN t ht
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hM1 : 1 ≤ Submission.LargeValues.M N := by
    rw [Submission.LargeValues.M]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hMpos : 0 < Submission.LargeValues.M N := lt_of_lt_of_le zero_lt_one hM1
  have hMηpos : 0 < (Submission.LargeValues.M N) ^ η := Real.rpow_pos_of_pos hMpos η
  -- the constant factor `(1+|t|)^j N^{-j}` is at most `M^{-ηj}`
  have hcoef : (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹
      ≤ (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))) := by
    have h1 : (1 + |t|) / (N : ℝ) ≤ (Submission.LargeValues.M N) ^ (-η) := by
      rw [Real.rpow_neg (le_of_lt hMpos), div_le_iff₀ hNpos]
      have h2 : (1 + |t|) ≤ (N : ℝ) / (Submission.LargeValues.M N) ^ η :=
        (le_div_iff₀ hMηpos).mpr ht
      rw [div_eq_mul_inv] at h2
      linarith
    have hpow : ((1 + |t|) / (N : ℝ)) ^ j ≤ ((Submission.LargeValues.M N) ^ (-η)) ^ j :=
      pow_le_pow_left₀ (by positivity) h1 j
    have h2 : ((Submission.LargeValues.M N) ^ (-η)) ^ j
        = (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hMpos)]
      congr 1
      ring
    calc (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹ = ((1 + |t|) / (N : ℝ)) ^ j := by
          rw [div_pow, div_eq_mul_inv]
      _ ≤ ((Submission.LargeValues.M N) ^ (-η)) ^ j := hpow
      _ = (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))) := h2
  -- termwise decay
  have hpt : ∀ m : {m : ℤ // m ≠ 0},
      ‖Submission.GM.hhat t (((m : ℤ) : ℝ) * (N : ℝ))‖
        ≤ (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * ((|(((m : ℤ) : ℝ))| : ℝ) ^ j)⁻¹ := by
    intro m
    have hm0 : ((m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast m.2
    have hξ : ((m : ℤ) : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero hm0 (by positivity)
    have hb := hCj t _ hξ
    rw [abs_mul, abs_of_nonneg (le_of_lt hNpos), mul_pow] at hb
    calc ‖Submission.GM.hhat t (((m : ℤ) : ℝ) * (N : ℝ))‖
        ≤ Cj * (1 + |t|) ^ j / (((|(((m : ℤ) : ℝ))| : ℝ) ^ j) * (N : ℝ) ^ j) := hb
      _ = (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * ((|(((m : ℤ) : ℝ))| : ℝ) ^ j)⁻¹ := by
          rw [div_eq_mul_inv, mul_inv]; ring
  have hsumm_dom : Summable (fun m : {m : ℤ // m ≠ 0} =>
      (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * ((|(((m : ℤ) : ℝ))| : ℝ) ^ j)⁻¹) :=
    hsumm_p.mul_left _
  have hsumm : Summable (fun m : {m : ℤ // m ≠ 0} =>
      Submission.GM.hhat t (((m : ℤ) : ℝ) * (N : ℝ))) :=
    Summable.of_norm_bounded hsumm_dom hpt
  have hsumm_norm : Summable (fun m : {m : ℤ // m ≠ 0} =>
      ‖Submission.GM.hhat t (((m : ℤ) : ℝ) * (N : ℝ))‖) := hsumm.norm
  calc ‖Work.GM.S2.Sall N t‖
      = ‖∑' m : {m : ℤ // m ≠ 0}, Submission.GM.hhat t (((m : ℤ) : ℝ) * (N : ℝ))‖ := rfl
    _ ≤ ∑' m : {m : ℤ // m ≠ 0}, ‖Submission.GM.hhat t (((m : ℤ) : ℝ) * (N : ℝ))‖ :=
        norm_tsum_le_tsum_norm hsumm_norm
    _ ≤ ∑' m : {m : ℤ // m ≠ 0},
          (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * ((|(((m : ℤ) : ℝ))| : ℝ) ^ j)⁻¹ :=
        Summable.tsum_le_tsum hpt hsumm_norm hsumm_dom
    _ = (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * S := by rw [hS, tsum_mul_left]
    _ ≤ (Cj * S) * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))) := by
        have h1 : (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * S
            ≤ (Cj * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) * S := by
          apply mul_le_mul_of_nonneg_right _ hS_nonneg
          calc Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹
              = Cj * ((1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) := by ring
            _ ≤ Cj * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))) :=
                mul_le_mul_of_nonneg_left hcoef (le_of_lt hCjpos)
        calc (Cj * (1 + |t|) ^ j * ((N : ℝ) ^ j)⁻¹) * S
            ≤ (Cj * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ)))) * S := h1
          _ = (Cj * S) * (Submission.LargeValues.M N) ^ (-(η * (j : ℝ))) := by ring

end Work.GM.S2
