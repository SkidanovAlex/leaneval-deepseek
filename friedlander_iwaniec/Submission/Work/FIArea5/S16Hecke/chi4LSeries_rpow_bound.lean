import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A uniform bound for the Dirichlet `L`-series of `χ₄` on `1 < σ ≤ 2`

We prove

`∃ C > 0, ∀ σ, 1 < σ → σ ≤ 2 → |∑' n, χ₄(n) · n^{-σ}| ≤ C`

with the explicit constant `C = 1`.

The proof is elementary and uses only the two structural features of `χ₄`:

* `χ₄` vanishes on the even integers and alternates on the odd ones:
  `χ₄(2m+1) = (-1)^m`;
* consequently `∑_n χ₄(n) n^{-σ} = ∑_m (-1)^m (2m+1)^{-σ}` (reindexing along the injection
  `m ↦ 2m+1`, legitimate for the `tsum` of a supported function);

and then the alternating-series bound `|∑ (-1)^m a_m| ≤ a_0` for an antitone `a ≥ 0` decaying
to `0` (here `a_m = (2m+1)^{-σ}`, so `a_0 = 1`).
-/

namespace Work.FIArea5.S16Hecke

open Finset

/-- The real value of `χ₄` at `n : ℕ`: `1` for `n ≡ 1 (4)`, `-1` for `n ≡ 3 (4)` and `0`
otherwise. -/
private lemma chi4_val (n : ℕ) :
    ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ)
      = (if n % 2 = 0 then (0 : ℝ) else if n % 4 = 1 then 1 else -1) := by
  rw [ZMod.χ₄_nat_eq_if_mod_four]
  push_cast
  rfl

/-- On the odd integers `χ₄(2m+1) = (-1)^m`, so the summand of the `L`-series at `n = 2m+1`
is `(-1)^m (2m+1)^{-σ}`. -/
private lemma chi4_summand_eq (σ : ℝ) (m : ℕ) :
    ((ZMod.χ₄ (((2 * m + 1 : ℕ)) : ZMod 4) : ℤ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ) ^ (-σ)
      = (-1 : ℝ) ^ m * ((2 * m + 1 : ℕ) : ℝ) ^ (-σ) := by
  have hodd : (2 * m + 1) % 2 = 1 := by omega
  have hchi : ZMod.χ₄ (((2 * m + 1 : ℕ)) : ZMod 4) = (-1) ^ m := by
    rw [ZMod.χ₄_eq_neg_one_pow (n := 2 * m + 1) hodd]
    congr 1
    omega
  rw [hchi]
  push_cast
  ring

/-- `n ↦ (2n+1)^{-σ}` is antitone for `σ > 0`. -/
private lemma antitone_g (σ : ℝ) (hσ : 0 < σ) :
    Antitone (fun m : ℕ => ((2 * m + 1 : ℕ) : ℝ) ^ (-σ)) := by
  intro a b hab
  have ha : (0 : ℝ) < ((2 * a + 1 : ℕ) : ℝ) := by positivity
  have hle : ((2 * a + 1 : ℕ) : ℝ) ≤ ((2 * b + 1 : ℕ) : ℝ) := by
    have : 2 * a + 1 ≤ 2 * b + 1 := by omega
    exact_mod_cast this
  have := Real.rpow_le_rpow_of_nonpos ha hle (by linarith : -σ ≤ 0)
  simpa using this

/-- `∑_m (2m+1)^{-σ}` converges for `σ > 1`. -/
private lemma summable_g (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun m : ℕ => ((2 * m + 1 : ℕ) : ℝ) ^ (-σ)) := by
  have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-σ)) := by
    rw [Real.summable_nat_rpow]
    linarith
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
    have hh := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-σ)) 1).mpr hbase
    simpa using hh
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hshift
  · positivity
  · have h2 : ((m + 1 : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by
      have : m + 1 ≤ 2 * m + 1 := by omega
      exact_mod_cast this
    have := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < ((m + 1 : ℕ) : ℝ) by positivity) h2
      (by linarith : -σ ≤ 0)
    simpa using this

/-- The summand `n ↦ χ₄(n) n^{-σ}` is supported on the odd integers. -/
private lemma chi4_support (σ : ℝ) (hσ : 1 < σ) :
    Function.support
        (fun n : ℕ => ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ))
      ⊆ Set.range (fun m : ℕ => 2 * m + 1) := by
  intro n hn
  change ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ) ≠ 0 at hn
  have hσne : (-σ) ≠ 0 := by linarith
  have hnne : n ≠ 0 := by
    intro h0
    apply hn
    rw [h0]
    simp only [Nat.cast_zero]
    rw [Real.zero_rpow hσne, mul_zero]
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hnne
  have hchi : ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) ≠ 0 := by
    intro hc
    exact hn (by rw [hc, zero_mul])
  refine ⟨n / 2, ?_⟩
  show 2 * (n / 2) + 1 = n
  have h2 : n % 2 ≠ 0 := by
    intro h
    apply hchi
    rw [chi4_val, if_pos h]
  have hmod : n % 2 = 1 := by omega
  have hdiv := Nat.div_add_mod n 2
  omega

theorem chi4LSeries_rpow_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      |∑' n : ℕ, ((ZMod.χ₄ ((n : ℕ) : ZMod 4) : ℤ) : ℝ) * (n : ℝ) ^ (-σ)| ≤ C := by
  refine ⟨1, one_pos, ?_⟩
  intro σ hσ _
  -- the alternating series `∑ (-1)^m (2m+1)^{-σ}` is bounded by its first term `1`
  have hg_anti : Antitone (fun m : ℕ => ((2 * m + 1 : ℕ) : ℝ) ^ (-σ)) :=
    antitone_g σ (by linarith)
  have hg_sum : Summable (fun m : ℕ => ((2 * m + 1 : ℕ) : ℝ) ^ (-σ)) := summable_g σ hσ
  have halt := alternating_series_error_bound
    (fun m : ℕ => ((2 * m + 1 : ℕ) : ℝ) ^ (-σ)) hg_anti hg_sum 0
  have halt' : |∑' i : ℕ, (-1 : ℝ) ^ i * ((2 * i + 1 : ℕ) : ℝ) ^ (-σ)| ≤ 1 := by
    simpa using halt
  -- reindex the `L`-series along the injection `m ↦ 2m+1`
  have hsupp := chi4_support σ hσ
  have hinj : Function.Injective (fun m : ℕ => 2 * m + 1) := by
    intro a b h
    have h' : 2 * a + 1 = 2 * b + 1 := h
    omega
  have hreindex := Function.Injective.tsum_eq (g := fun m : ℕ => 2 * m + 1) hinj hsupp
  rw [← hreindex]
  have hcongr :
      (∑' c : ℕ,
          ((ZMod.χ₄ (((2 * c + 1 : ℕ)) : ZMod 4) : ℤ) : ℝ) * ((2 * c + 1 : ℕ) : ℝ) ^ (-σ))
        = ∑' i : ℕ, (-1 : ℝ) ^ i * ((2 * i + 1 : ℕ) : ℝ) ^ (-σ) :=
    tsum_congr (fun m => chi4_summand_eq σ m)
  rw [hcongr]
  exact halt'

end Work.FIArea5.S16Hecke
