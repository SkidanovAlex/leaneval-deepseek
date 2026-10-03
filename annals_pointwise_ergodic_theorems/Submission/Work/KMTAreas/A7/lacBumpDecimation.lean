import Mathlib
import Submission.Work.KMTAreas.A7.lacBumpDefs

namespace Work.KMTAreas.A7

open scoped NNReal

/-!
# Decimating a lacunary scale sequence

`Work.KMTAreas.A7.lacunaryBump_mult_bound_k1pos` needs the family of bump scales
`σ_n = lacσ ⌊a n⌋ k₁` to be `2`-lacunary on the index set `U` (`LacunaryFam 2 U σ`,
the hypothesis of Appendix B's `cz-shift`).  For an arbitrary `Λ`-lacunary `a` with `Λ > 1`
this fails for *consecutive* indices `n`, `n+1`: the integer part `⌊a n⌋` changes by a factor
which may be arbitrarily close to `1`, and `lacσ` is insensitive to changes of `⌊a n⌋` by a
factor `< 2`.

The point of this lemma is that it *does* hold after *decimation*: for a modulus `M` large
enough that `Λ ^ M ≥ 5`, the subsequence `n, n + M, n + 2M, …` has
`⌊a (n + M)⌋ ≥ 4 ⌊a n⌋`, hence (since `Log (4m) ≥ Log m + 1`, `Log = log₂ max(·,2)`)
`lacσ ⌊a (n+M)⌋ k₁ ≥ 2 · lacσ ⌊a n⌋ k₁`, and chaining the gap `M` gives the `2`-lacunarity of
`σ` on every residue class mod `M`.

The analytic content is in the two helper lemmas below:

* `logN_four_mul` : `Log (4m) ≥ Log m + 1` for `m ≥ 1`;
* `two_mul_lacσ_le` : `2 * lacσ m k ≤ lacσ n k` for integer exponents with `Log m + 1 ≤ Log n`.
-/

/-- `Log (4 * m) ≥ Log m + 1` for every `m ≥ 1`. -/
private lemma logN_four_mul (m : ℕ) (hm : 1 ≤ m) :
    Work.Analysis.EndVar.logN m + 1 ≤ Work.Analysis.EndVar.logN (4 * m) := by
  have key : Nat.log 2 (max m 2) + 1 ≤ Nat.log 2 (max (4 * m) 2) := by
    rcases eq_or_lt_of_le hm with h | h
    · subst h; norm_num [Work.Analysis.EndVar.logN]
    · have hm2 : 2 ≤ m := h
      rw [max_eq_left hm2, max_eq_left (by omega : 2 ≤ 4 * m)]
      refine (Nat.le_log_iff_pow_le (b := 2) (x := Nat.log 2 m + 1) (y := 4 * m)
        (by norm_num) (by omega)).mpr ?_
      calc 2 ^ (Nat.log 2 m + 1) = 2 * 2 ^ Nat.log 2 m := by ring
        _ ≤ 2 * m := Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (by omega))
        _ ≤ 4 * m := by omega
  simp only [Work.Analysis.EndVar.logN]
  exact_mod_cast key

/-- `lacσ` is monotone enough in its frequency argument: `2 * lacσ m k ≤ lacσ n k` as soon as
`Log m + 1 ≤ Log n`. -/
private lemma two_mul_lacσ_le {m n k : ℕ}
    (h : Work.Analysis.EndVar.logN m + 1 ≤ Work.Analysis.EndVar.logN n) :
    2 * lacσ m k ≤ lacσ n k := by
  have hle : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN m : ℤ) + 1 - (k : ℤ))
      ≤ (2 : ℝ) ^ ((Work.Analysis.EndVar.logN n : ℤ) - (k : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
  have h1 : (2 : ℝ) * (2 : ℝ) ^ ((Work.Analysis.EndVar.logN m : ℤ) - (k : ℤ))
      = (2 : ℝ) ^ ((Work.Analysis.EndVar.logN m : ℤ) + 1 - (k : ℤ)) := by
    rw [mul_comm]
    rw [show (Work.Analysis.EndVar.logN m : ℤ) + 1 - (k : ℤ)
        = ((Work.Analysis.EndVar.logN m : ℤ) - (k : ℤ)) + 1 by ring]
    rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  simp only [lacσ]
  rw [h1]
  exact hle

/-- **Decimation of a lacunary scale sequence.**  For every `Λ > 1` there is a modulus `M > 0`
such that, for every `Λ`-lacunary `a` with `a n ≥ 1`, every `k₁`, every finite `U` and every
residue `r`, the scales `lacσ ⌊a n⌋ k₁` are `2`-lacunary on `{n ∈ U : n % M = r}`. -/
theorem lacBumpDecimation (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ M : ℕ, 0 < M ∧ ∀ (k₁ : ℕ) (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → ∀ (U : Finset ℕ) (r : ℕ),
      Work.Analysis.CzShift.LacunaryFam 2 (U.filter (fun n => n % M = r))
        (fun n => Work.KMTAreas.A7.lacσ (Nat.floor (a n)) k₁) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  -- Choose the modulus so that `Λ ^ M ≥ 5`.
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt (5 : ℝ) hΛR
  set M : ℕ := max n₀ 1 with hM
  have hMpos : 0 < M := by omega
  have hM5 : (5 : ℝ) ≤ (Λ : ℝ) ^ M := by
    have h1 : (Λ : ℝ) ^ n₀ ≤ (Λ : ℝ) ^ max n₀ 1 :=
      pow_le_pow_right₀ hΛR.le (le_max_left _ _)
    rw [hM]
    linarith
  refine ⟨M, hMpos, ?_⟩
  intro k₁ a ha ha1 U r
  -- `⌊a n⌋ ≥ 1`.
  have hb1 : ∀ n, 1 ≤ Nat.floor (a n) := by
    intro n
    exact Nat.le_floor (by simpa using ha1 n)
  -- One step of the lacunarity of `a`, in `ℝ`: `Λ * a m < a (m+1)`.
  have hstep : ∀ m : ℕ, (Λ : ℝ) * (a m : ℝ) < (a (m + 1) : ℝ) := by
    intro m
    have h := ha m
    have h'' : ((Λ : NNReal) : ℝ) < ((a (m + 1) / a m : NNReal) : ℝ) := by exact_mod_cast h
    rw [NNReal.coe_div] at h''
    have hpos : 0 < (a m : ℝ) := by
      have h0 : (0 : NNReal) < a m := lt_of_lt_of_le zero_lt_one (ha1 m)
      exact_mod_cast h0
    have h2 := mul_lt_mul_of_pos_right h'' hpos
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at h2
    simpa [mul_comm] using h2
  -- Geometric growth: `Λ ^ k * a m ≤ a (m + k)`.
  have hgeo : ∀ k m, (Λ : ℝ) ^ k * (a m : ℝ) ≤ (a (m + k) : ℝ) := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      have h1 : (Λ : ℝ) ^ k * (a m : ℝ) ≤ (a (m + k) : ℝ) := ih m
      have h2 := hstep (m + k)
      have h3 : (Λ : ℝ) ^ (k + 1) * (a m : ℝ)
          = (Λ : ℝ) * ((Λ : ℝ) ^ k * (a m : ℝ)) := by ring
      rw [h3]
      calc (Λ : ℝ) * ((Λ : ℝ) ^ k * (a m : ℝ)) ≤ (Λ : ℝ) * (a (m + k) : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (a (m + k + 1) : ℝ) := le_of_lt h2
        _ = (a (m + (k + 1)) : ℝ) := by rw [Nat.add_assoc]
  have h5mul : ∀ n, (5 : ℝ) * (a n : ℝ) ≤ (a (n + M) : ℝ) := by
    intro n
    have h1 := hgeo M n
    have h2 : (0 : ℝ) ≤ (a n : ℝ) := by positivity
    calc (5 : ℝ) * (a n : ℝ) ≤ (Λ : ℝ) ^ M * (a n : ℝ) :=
          mul_le_mul_of_nonneg_right hM5 h2
      _ ≤ (a (n + M) : ℝ) := h1
  -- The decimated sequence grows by a factor `4` in the integer part.
  have hfour : ∀ n, 4 * Nat.floor (a n) ≤ Nat.floor (a (n + M)) := by
    intro n
    have hfn : ((Nat.floor (a n) : ℕ) : ℝ) ≤ (a n : ℝ) :=
      Nat.floor_le (show (0 : ℝ) ≤ (a n : ℝ) from by positivity)
    have h1n : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
    have key : ((4 * Nat.floor (a n) : ℕ) : ℝ) ≤ (a (n + M) : ℝ) := by
      have hgrowth := h5mul n
      push_cast
      nlinarith
    exact Nat.le_floor (by exact_mod_cast key)
  -- Hence the logarithmic scale grows by at least `1` every `M` indices.
  have hlog : ∀ n, Work.Analysis.EndVar.logN (Nat.floor (a n)) + 1
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a (n + M))) := by
    intro n
    exact le_trans (logN_four_mul (Nat.floor (a n)) (hb1 n))
      (Work.Analysis.EndVar.logN_mono (hfour n))
  -- Chaining: `Log ⌊a (i + t M)⌋ ≥ Log ⌊a i⌋ + t`.
  have hchain : ∀ (t : ℕ) (i : ℕ), Work.Analysis.EndVar.logN (Nat.floor (a i)) + (t : ℤ)
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a (i + t * M))) := by
    intro t
    induction t with
    | zero =>
      intro i
      simp
    | succ t ih =>
      intro i
      have h1 : Work.Analysis.EndVar.logN (Nat.floor (a i)) + (t : ℤ)
          ≤ Work.Analysis.EndVar.logN (Nat.floor (a (i + t * M))) := ih i
      have h2 : Work.Analysis.EndVar.logN (Nat.floor (a (i + t * M))) + 1
          ≤ Work.Analysis.EndVar.logN (Nat.floor (a (i + t * M + M))) := hlog (i + t * M)
      have h3 : i + (t + 1) * M = i + t * M + M := by ring
      rw [h3]
      rw [Nat.cast_add, Nat.cast_one]
      linarith
  -- Residue classes that differ by a nonzero multiple of `M` gain `1` in `Log`.
  have hdvd : ∀ {i j : ℕ}, i ≤ j → i % M = j % M → M ∣ j - i := by
    intro i j hij hmod
    have hmodeq : i ≡ j [MOD M] := by
      rw [Nat.ModEq]
      exact hmod
    exact (Nat.modEq_iff_dvd' hij).mp hmodeq
  have hpair : ∀ {i j : ℕ}, i ≤ j → i % M = j % M → i ≠ j →
      Work.Analysis.EndVar.logN (Nat.floor (a i)) + 1
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a j)) := by
    intro i j hij hmod hne
    have hdvdij : M ∣ j - i := hdvd hij hmod
    have hpos : 0 < j - i := by omega
    have hMle : M ≤ j - i := Nat.le_of_dvd hpos hdvdij
    have ht1 : 1 ≤ (j - i) / M := by
      rw [Nat.one_le_div_iff hMpos]
      exact hMle
    have hc := hchain ((j - i) / M) i
    have hjm : i + (j - i) / M * M = j := by
      rw [Nat.div_mul_cancel hdvdij, Nat.add_sub_of_le hij]
    rw [hjm] at hc
    have ht : ((1 : ℕ) : ℤ) ≤ ((j - i) / M : ℕ) := by exact_mod_cast ht1
    omega
  refine ⟨?_, ?_⟩
  · intro i _
    show 0 < lacσ (Nat.floor (a i)) k₁
    rw [lacσ]
    positivity
  · intro i hi j hj hij
    have eqres : i % M = j % M := by
      rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h := hpair hlt.le eqres hij
      have h2 := two_mul_lacσ_le (k := k₁) h
      have hmin : min (lacσ (Nat.floor (a i)) k₁) (lacσ (Nat.floor (a j)) k₁)
          ≤ lacσ (Nat.floor (a i)) k₁ := min_le_left _ _
      have hmax : lacσ (Nat.floor (a j)) k₁
          ≤ max (lacσ (Nat.floor (a i)) k₁) (lacσ (Nat.floor (a j)) k₁) := le_max_right _ _
      linarith
    · have h := hpair hgt.le eqres.symm hij.symm
      have h2 := two_mul_lacσ_le (k := k₁) h
      have hmin : min (lacσ (Nat.floor (a i)) k₁) (lacσ (Nat.floor (a j)) k₁)
          ≤ lacσ (Nat.floor (a j)) k₁ := min_le_right _ _
      have hmax : lacσ (Nat.floor (a i)) k₁
          ≤ max (lacσ (Nat.floor (a i)) k₁) (lacσ (Nat.floor (a j)) k₁) := le_max_left _ _
      linarith

end Work.KMTAreas.A7
