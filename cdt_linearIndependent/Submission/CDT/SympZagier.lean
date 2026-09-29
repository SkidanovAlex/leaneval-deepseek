import Submission.CDT.SympDescent
import Submission.CDT.ZagierH

/-!
# `Sym⁺H_A ∈ ℤ[[y]]` (paper eq. defG)

The paper's §"The symmetrization of H(x)" (defG) asserts that with the
symmetrization coordinate `y = x²/(x−1)` the symmetrized series

```lean
G_A(y) = Sym⁺H_A(x) = H_A(x) + H_A(x/(x−1)) ∈ ℤ[[y]]
```

of the Hauptmodul series `H_A(x) = Σₙ aₙ xⁿ` (`aₙ = Σₖ C(n,k)²C(2k,k)`,
Zagier's sequence `C`, module `Submission.CDT.ZagierH`) has integer
coefficients as a series in `y`.  Here we instantiate the general
`ℤ`-refinement of the descent (`SympDescent`: `IntSeries`,
`sympSym_int`) with `H_A`, and — in the last section — **verify the
paper's defG display** by computing the first coefficients of `G_A`
through the descent recursion applied to `F = H_A + H_A∘φ`:

```lean
G_A(y) = 2 − 27·y + 1014·y² − 49536·y³ + …
```

(`sympSym_HA_coeff_zero/one/two/three`); the next eight coefficients
`g₄ = 2699568`, `g₅ = −156368412`, `g₆ = 9417572124`,
`g₇ = −582777991998`, `g₈ = 36790168266504`, `g₉ = −2358331843506732`,
`g₁₀ = 153015687754620984`, `g₁₁ = −10026092063682326736` are verified in
the same way (`sympSym_HA_coeff_four/five/six/seven/eight/nine/ten/eleven`).
The engine is the coefficient
law `coeff_sympPhi_pow` for the powers of `φ = −X·(1−X)⁻¹` together with
the even-coefficient values of `F` (`coeff_HAF_even_two/four/six`) and the
descent recursion `sympDescCoeff_HAF_zero/one/two/three` — a fully worked
end-to-end run of the descent machinery on the actual `H_A` series.

All declarations are fully proved (no axioms, no `sorry`).
-/

noncomputable section

namespace Submission.CDT

open PowerSeries

/-- the coefficients of `H_A` are integers -/
lemma HA_IntSeries : IntSeries HA := by
  intro n
  rw [coeff_HA]
  refine ⟨HA_coeffZ n, ?_⟩
  exact (HA_coeff_eq_cast n).symm

/-- paper defG: `G_A(y) = Sym⁺H_A` has integer coefficients as a series in `y` -/
lemma sympSym_HA_IntSeries : IntSeries (sympSym HA) :=
  sympSym_int HA HA_IntSeries


/-! ## The paper's defG display: `G_A(y) = 2 − 27y + 1014y² − 49536y³ + …`

The descent machinery of `SympDescent` is instantiated with `H_A` and the
first four coefficients of `G_A(y) = Sym⁺H_A(y) = H_A(x) + H_A(x/(x−1))` are
computed and verified against the paper's display (defG):
`G_A(y) = 2 − 27y + 1014y² − 49536y³ + …`.

The engine is the triangular descent recursion
(`sympDescCoeff_eq_sign`) applied to the `φ`-invariant series
`F = H_A + H_A∘φ` (`HAF` below): `gₙ = coeffₙ G_A = sympDescCoeff F n`.
Its ingredients (all proved here):

* the coefficient laws for `φ = −X·(1−X)⁻¹` and its powers:
  `coeff_sympPhi_of_pos` (all positive coefficients of `φ` are `−1`),
  `coeff_one_sub_X_inv` (all coefficients of `(1−X)⁻¹` are `1`),
  `one_sub_X_inv_eq_mk_one`, `coeff_mk_one_pow` / `coeff_one_sub_X_inv_pow`
  (binomial coefficients of `(1−X)⁻ᵐ`), `sympPhi_eq_neg_X_mul_one_sub_inv`,
  and `coeff_sympPhi_pow` (`coeffⱼ(φᵐ) = (−1)ᵐ·C(j−1, m−1)` for
  `1 ≤ m ≤ j`);
* the even coefficients of `F` (`coeff_HAF_even_two/four/six` = 27, 1041,
  52605), computed through `coeff_subst_range` + `coeff_sympPhi_pow` from
  the integer values `a₀ = 1, …, a₆ = 35169` (`HA_coeff_three/four/five/six`);
* the `y`-power coefficients needed by the recursion (`coeff_sympY_of_two_le`:
  `coeffⱼ y = −1` for `j ≥ 2`; `coeff_sympY_sq_six`: `coeff₆ y² = 3`;
  the diagonal values come from `coeff_sympY_pow_diag`);
* the descent values `sympDescCoeff_HAF_zero/one/two/three/four/five` and
  hence the coefficient theorems
  `sympSym_HA_coeff_zero/one/two/three/four/five`:
  `coeffₙ G_A = 2, −27, 1014, −49536, 2699568, −156368412, 9417572124,
  −582777991998, 36790168266504, −2358331843506732, 153015687754620984,
  −10026092063682326736` for `n = 0..11` — the paper's defG display
  (`2 − 27y + 1014y² − 49536y³ + …`), now verified in Lean.  The extension
  lemmas for `n = 4..12` (`HA_coeff_seven..twenty_four`, the even-degree
  `y`-power law `coeff_sympY_pow_even`, the substitution coefficients at
  even degrees 8..24) mirror the `n ≤ 3` machinery; the degree-24 block
  (`coeff_sympY_*_twentyfour`, `sympDescCoeff_HAF_twelve`) adds
  `g₁₂ = 662302233027566488692`, needed by the explicitode equation
  `GA_odeLHS_coeff_eleven` (`SympExplicitode`).
-/

/-- all positive coefficients of `φ = X/(X−1)` are `−1` -/
lemma coeff_sympPhi_of_pos {j : ℕ} (hj : 1 ≤ j) : PowerSeries.coeff j sympPhi = -1 := by
  have hjj : j = (j - 1) + 1 := by omega
  rw [hjj]
  unfold sympPhi
  rw [PowerSeries.coeff_succ_X_mul (j - 1) (((X : PowerSeries ℚ) - 1)⁻¹)]
  exact coeff_inv_X_sub_one (j - 1)

/-- all coefficients of `(1−X)⁻¹` are `1` -/
lemma coeff_one_sub_X_inv (j : ℕ) : PowerSeries.coeff j (((1 : PowerSeries ℚ) - X)⁻¹) = 1 := by
  have hcc : PowerSeries.constantCoeff ((1 : PowerSeries ℚ) - X) ≠ 0 := by
    simp
  have hmul : ((1 : PowerSeries ℚ) - X) * (((1 : PowerSeries ℚ) - X)⁻¹) = 1 := by
    exact PowerSeries.mul_inv_cancel ((1 : PowerSeries ℚ) - X) hcc
  have hf : ∀ j : ℕ, PowerSeries.coeff j (((1 : PowerSeries ℚ) - X)⁻¹) = 1 := by
    intro j
    induction j with
    | zero =>
        have hc := congrArg (PowerSeries.coeff 0) hmul
        have hcone : PowerSeries.coeff 0 (1 : PowerSeries ℚ) = 1 := by simp
        rw [hcone] at hc
        have hc0 : PowerSeries.coeff 0 (((1 : PowerSeries ℚ) - X) * (((1 : PowerSeries ℚ) - X)⁻¹)) =
            PowerSeries.coeff 0 (((1 : PowerSeries ℚ) - X)⁻¹) := by
          rw [coeff_mul]
          simp [Finset.HasAntidiagonal.mem_antidiagonal]
        rw [hc0] at hc
        exact hc
    | succ j ih =>
        have hc := congrArg (PowerSeries.coeff (j + 1)) hmul
        have hcone' : PowerSeries.coeff (j + 1) (1 : PowerSeries ℚ) = 0 := by simp
        rw [hcone'] at hc
        have hsplit : PowerSeries.coeff (j + 1) (((1 : PowerSeries ℚ) - X) * (((1 : PowerSeries ℚ) - X)⁻¹)) =
            PowerSeries.coeff (j + 1) (((1 : PowerSeries ℚ) - X)⁻¹) -
              PowerSeries.coeff j (((1 : PowerSeries ℚ) - X)⁻¹) := by
          calc
            PowerSeries.coeff (j + 1) (((1 : PowerSeries ℚ) - X) * (((1 : PowerSeries ℚ) - X)⁻¹))
                = PowerSeries.coeff (j + 1) ((((1 : PowerSeries ℚ) - X)⁻¹) - X * (((1 : PowerSeries ℚ) - X)⁻¹)) := by
                  rw [sub_mul]
                  rw [one_mul]
            _ = PowerSeries.coeff (j + 1) (((1 : PowerSeries ℚ) - X)⁻¹) -
                  PowerSeries.coeff (j + 1) (X * (((1 : PowerSeries ℚ) - X)⁻¹)) := by
                  rw [map_sub]
            _ = PowerSeries.coeff (j + 1) (((1 : PowerSeries ℚ) - X)⁻¹) -
                  PowerSeries.coeff j (((1 : PowerSeries ℚ) - X)⁻¹) := by
                  rw [PowerSeries.coeff_succ_X_mul j (((1 : PowerSeries ℚ) - X)⁻¹)]
        have hmain : PowerSeries.coeff (j + 1) (((1 : PowerSeries ℚ) - X)⁻¹) -
              PowerSeries.coeff j (((1 : PowerSeries ℚ) - X)⁻¹) = 0 := by
          rw [hsplit] at hc
          exact hc
        have : PowerSeries.coeff (j + 1) (((1 : PowerSeries ℚ) - X)⁻¹) = 1 := by
          linarith
        exact this
  exact hf j

/-- `(1−X)⁻¹ = mk 1` (the all-ones series) -/
lemma one_sub_X_inv_eq_mk_one :
    (((1 : PowerSeries ℚ) - X)⁻¹) = PowerSeries.mk (1 : ℕ → ℚ) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_one_sub_X_inv n]
  simp

/-- coefficient of `(mk 1)^m` is the binomial `C(m−1+t, m−1)` (`m ≥ 1`) -/
lemma coeff_mk_one_pow (t m : ℕ) (hm : 1 ≤ m) :
    PowerSeries.coeff t ((PowerSeries.mk (1 : ℕ → ℚ)) ^ m) =
      (Nat.choose (m - 1 + t) (m - 1) : ℚ) := by
  have hm' : m = (m - 1) + 1 := by omega
  rw [hm']
  have hpow := (PowerSeries.mk_one_pow_eq_mk_choose_add ℚ (m - 1))
  rw [hpow]
  simp

/-- coefficient of `((1−X)⁻¹)^m` is `C(m−1+t, m−1)` (`m ≥ 1`) -/
lemma coeff_one_sub_X_inv_pow (t m : ℕ) (hm : 1 ≤ m) :
    PowerSeries.coeff t ((((1 : PowerSeries ℚ) - X)⁻¹) ^ m) =
      (Nat.choose (m - 1 + t) (m - 1) : ℚ) := by
  rw [one_sub_X_inv_eq_mk_one]
  exact coeff_mk_one_pow t m hm

/-- `φ = −X·(1−X)⁻¹` (series identity) -/
lemma sympPhi_eq_neg_X_mul_one_sub_inv :
    sympPhi = -((X : PowerSeries ℚ) * (((1 : PowerSeries ℚ) - X)⁻¹)) := by
  apply PowerSeries.ext
  intro j
  by_cases hj : j = 0
  · subst j
    simp [sympPhi]
  · have hj1 : 1 ≤ j := by omega
    have hjj : j = (j - 1) + 1 := by omega
    calc
      PowerSeries.coeff j sympPhi = -1 := coeff_sympPhi_of_pos hj1
      _ = PowerSeries.coeff j (-((X : PowerSeries ℚ) * (((1 : PowerSeries ℚ) - X)⁻¹))) := by
            rw [hjj]
            rw [map_neg]
            rw [PowerSeries.coeff_succ_X_mul (j - 1) (((1 : PowerSeries ℚ) - X)⁻¹)]
            rw [coeff_one_sub_X_inv (j - 1)]

/-- coefficient of `φ^m` (`1 ≤ m ≤ j`): `(−1)^m·C(j−1, m−1)` -/
lemma coeff_sympPhi_pow (j m : ℕ) (hm : 1 ≤ m) (hmj : m ≤ j) :
    PowerSeries.coeff j (sympPhi ^ m) =
      (-1 : ℚ) ^ m * (Nat.choose (j - 1) (m - 1) : ℚ) := by
  let W : PowerSeries ℚ := ((1 : PowerSeries ℚ) - X)⁻¹
  have hsymp : sympPhi ^ m = (-(X * W)) ^ m := by
    rw [sympPhi_eq_neg_X_mul_one_sub_inv]
  calc
    PowerSeries.coeff j (sympPhi ^ m)
        = PowerSeries.coeff j ((-(X * W)) ^ m) := by rw [hsymp]
    _ = PowerSeries.coeff j ((((-1 : ℚ) • (X * W)) ^ m)) := by
          congr 2
          simp
    _ = PowerSeries.coeff j (((-1 : ℚ) ^ m) • ((X * W) ^ m)) := by
          rw [smul_pow]
    _ = PowerSeries.coeff j (((-1 : ℚ) ^ m) • (X ^ m * W ^ m)) := by
          congr 2
          rw [mul_pow]
    _ = (-1 : ℚ) ^ m * PowerSeries.coeff j (X ^ m * W ^ m) := by
          simp
    _ = (-1 : ℚ) ^ m * PowerSeries.coeff (j - m) (W ^ m) := by
          rw [PowerSeries.coeff_X_pow_mul' (W ^ m) m j]
          rw [if_pos hmj]
    _ = (-1 : ℚ) ^ m * (Nat.choose (m - 1 + (j - m)) (m - 1) : ℚ) := by
          rw [coeff_one_sub_X_inv_pow (j - m) m hm]
    _ = (-1 : ℚ) ^ m * (Nat.choose (j - 1) (m - 1) : ℚ) := by
          congr 2
          congr 1
          omega

/-- `a₃ = 93` -/
lemma HA_coeff_three : HA_coeff 3 = 93 := by native_decide
/-- `a₄ = 639` -/
lemma HA_coeff_four : HA_coeff 4 = 639 := by native_decide
/-- `a₅ = 4653` -/
lemma HA_coeff_five : HA_coeff 5 = 4653 := by native_decide
/-- `a₆ = 35169` -/
lemma HA_coeff_six : HA_coeff 6 = 35169 := by native_decide

/-- `[x²](H_A∘φ) = 12` -/
lemma coeff_HA_subst_sympPhi_two : PowerSeries.coeff 2 (HA.subst sympPhi) = 12 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 2]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num

lemma coeff_HA_subst_sympPhi_zero : PowerSeries.coeff 0 (HA.subst sympPhi) = 1 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 0]
  norm_num [Finset.sum_range_succ]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply HA]
  rw [coeff_HA, HA_coeff_zero]

/-- `[x¹](H_A∘φ) = −3` -/
lemma coeff_HA_subst_sympPhi_one : PowerSeries.coeff 1 (HA.subst sympPhi) = -3 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 1]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_one, coeff_sympPhi_of_pos]

/-- `[x³](H_A∘φ) = −66` -/
lemma coeff_HA_subst_sympPhi_three : PowerSeries.coeff 3 (HA.subst sympPhi) = -66 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 3]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_one, HA_coeff_two, HA_coeff_three,
    coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num

/-- `[x⁴](H_A∘φ) = 402` -/
lemma coeff_HA_subst_sympPhi_four : PowerSeries.coeff 4 (HA.subst sympPhi) = 402 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 4]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four, coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num

/-- `[x⁶](H_A∘φ) = 17436` -/
lemma coeff_HA_subst_sympPhi_six : PowerSeries.coeff 6 (HA.subst sympPhi) = 17436 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 6]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 5 2 = 10 by native_decide, show Nat.choose 5 3 = 10 by native_decide]

/-- the `φ`-invariant combination `F = H_A + H_A∘φ` (the descent input of `G_A`) -/
def HAF : PowerSeries ℚ := HA + HA.subst sympPhi

/-- `[x⁰]F = 2` -/
lemma coeff0_HAF : PowerSeries.coeff 0 HAF = 2 := by
  rw [HAF]
  rw [map_add]
  rw [coeff_HA]
  rw [coeff_subst_range HA coeff_sympPhi_zero 0]
  rw [HA_coeff_zero]
  simp [coeff_HA, HA_coeff_zero, Finset.sum_range_succ, PowerSeries.coeff_one]
  norm_num

/-- `[x²]F = 27` -/
lemma coeff_HAF_even_two : PowerSeries.coeff 2 HAF = 27 := by
  change PowerSeries.coeff 2 (HA + HA.subst sympPhi) = 27
  rw [map_add, coeff_HA, HA_coeff_two, coeff_HA_subst_sympPhi_two]
  norm_num

/-- `[x⁴]F = 1041` -/
lemma coeff_HAF_even_four : PowerSeries.coeff 4 HAF = 1041 := by
  change PowerSeries.coeff 4 (HA + HA.subst sympPhi) = 1041
  rw [map_add, coeff_HA, HA_coeff_four, coeff_HA_subst_sympPhi_four]
  norm_num

/-- `[x⁶]F = 52605` -/
lemma coeff_HAF_even_six : PowerSeries.coeff 6 HAF = 52605 := by
  change PowerSeries.coeff 6 (HA + HA.subst sympPhi) = 52605
  rw [map_add, coeff_HA, HA_coeff_six, coeff_HA_subst_sympPhi_six]
  norm_num

/-- `y = X·φ` has all coefficients `−1` from degree `2` on -/
lemma coeff_sympY_of_two_le {j : ℕ} (hj : 2 ≤ j) : PowerSeries.coeff j sympY = -1 := by
  have hjj : j = (j - 1) + 1 := by omega
  rw [hjj]
  unfold sympY
  rw [PowerSeries.coeff_succ_X_mul (j - 1) sympPhi]
  exact coeff_sympPhi_of_pos (by omega)

/-- `[x⁶]y² = 3` -/
lemma coeff_sympY_sq_six : PowerSeries.coeff 6 (sympY ^ 2) = 3 := by
  have hy : sympY ^ 2 = (X : PowerSeries ℚ) ^ 2 * sympPhi ^ 2 := by
    unfold sympY
    rw [mul_pow]
  rw [hy]
  rw [PowerSeries.coeff_X_pow_mul' (sympPhi ^ 2) 2 6]
  rw [if_pos (by norm_num : 2 ≤ 6)]
  rw [coeff_sympPhi_pow 4 2 (by norm_num) (by norm_num)]
  norm_num

/-- descent value `g₀ = 2` -/
lemma sympDescCoeff_HAF_zero : sympDescCoeff HAF 0 = 2 := by
  rw [sympDescCoeff_eq_sign HAF 0]
  norm_num [Finset.sum_range_succ]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff0_HAF

/-- descent value `g₁ = −27` -/
lemma sympDescCoeff_HAF_one : sympDescCoeff HAF 1 = -27 := by
  rw [sympDescCoeff_eq_sign HAF 1]
  norm_num [Finset.sum_range_succ]
  rw [coeff_HAF_even_two]

/-- descent value `g₂ = 1014` -/
lemma sympDescCoeff_HAF_two : sympDescCoeff HAF 2 = 1014 := by
  rw [sympDescCoeff_eq_sign HAF 2]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one]
  rw [coeff_sympY_of_two_le (by norm_num : 2 ≤ 4)]
  rw [coeff_HAF_even_four]
  norm_num

/-- descent value `g₃ = −49536` -/
lemma sympDescCoeff_HAF_three : sympDescCoeff HAF 3 = -49536 := by
  rw [sympDescCoeff_eq_sign HAF 3]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two]
  rw [coeff_sympY_of_two_le (by norm_num : 2 ≤ 6)]
  rw [coeff_sympY_sq_six]
  rw [coeff_HAF_even_six]
  norm_num

/-- paper defG: `[y⁰]G_A = 2` -/
theorem sympSym_HA_coeff_zero : PowerSeries.coeff 0 (sympSym HA) = 2 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 0 = 2
  exact sympDescCoeff_HAF_zero

/-- paper defG: `[y¹]G_A = −27` -/
theorem sympSym_HA_coeff_one : PowerSeries.coeff 1 (sympSym HA) = -27 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 1 = -27
  exact sympDescCoeff_HAF_one

/-- paper defG: `[y²]G_A = 1014` -/
theorem sympSym_HA_coeff_two : PowerSeries.coeff 2 (sympSym HA) = 1014 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 2 = 1014
  exact sympDescCoeff_HAF_two

/-- paper defG: `[y³]G_A = −49536` -/
theorem sympSym_HA_coeff_three : PowerSeries.coeff 3 (sympSym HA) = -49536 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 3 = -49536
  exact sympDescCoeff_HAF_three

lemma HA_coeff_seven : HA_coeff 7 = 272835 := by native_decide
/-- `a₈ = 2157759` -/
lemma HA_coeff_eight : HA_coeff 8 = 2157759 := by native_decide
/-- `a₉ = 17319837` -/
lemma HA_coeff_nine : HA_coeff 9 = 17319837 := by native_decide
/-- `a₁₀ = 140668065` -/
lemma HA_coeff_ten : HA_coeff 10 = 140668065 := by native_decide

/-- coefficient of `y^m` at the even degree `2n` (`1 ≤ m ≤ n`):
`[x^{2n}]y^m = (−1)^m·C(2n−m−1, m−1)` -/
lemma coeff_sympY_pow_even {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    PowerSeries.coeff (2 * n) (sympY ^ m) =
      (-1 : ℚ) ^ m * (Nat.choose (2 * n - m - 1) (m - 1) : ℚ) := by
  have hy : sympY ^ m = (X : PowerSeries ℚ) ^ m * sympPhi ^ m := by
    unfold sympY
    rw [mul_pow]
  rw [hy]
  have hshift := PowerSeries.coeff_X_pow_mul' (sympPhi ^ m) m (2 * n)
  rw [hshift]
  rw [if_pos]
  · rw [coeff_sympPhi_pow (2 * n - m) m hm (by omega)]
  · omega

/-- `[x⁸](H_A∘φ) = 844122` -/
lemma coeff_HA_subst_sympPhi_eight : PowerSeries.coeff 8 (HA.subst sympPhi) = 844122 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 8]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight,
    coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 7 1 = 7 by native_decide, show Nat.choose 7 2 = 21 by native_decide,
    show Nat.choose 7 3 = 35 by native_decide, show Nat.choose 7 4 = 35 by native_decide,
    show Nat.choose 7 5 = 21 by native_decide, show Nat.choose 7 6 = 7 by native_decide]

/-- `[x¹⁰](H_A∘φ) = 43446192` -/
lemma coeff_HA_subst_sympPhi_ten : PowerSeries.coeff 10 (HA.subst sympPhi) = 43446192 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 10]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 9 1 = 9 by native_decide, show Nat.choose 9 2 = 36 by native_decide,
    show Nat.choose 9 3 = 84 by native_decide, show Nat.choose 9 4 = 126 by native_decide,
    show Nat.choose 9 5 = 126 by native_decide, show Nat.choose 9 6 = 84 by native_decide,
    show Nat.choose 9 7 = 36 by native_decide, show Nat.choose 9 8 = 9 by native_decide]

/-- `[x⁸]F = 3001881` -/
lemma coeff_HAF_even_eight : PowerSeries.coeff 8 HAF = 3001881 := by
  change PowerSeries.coeff 8 (HA + HA.subst sympPhi) = 3001881
  rw [map_add, coeff_HA, HA_coeff_eight, coeff_HA_subst_sympPhi_eight]
  norm_num

/-- `[x¹⁰]F = 184114257` -/
lemma coeff_HAF_even_ten : PowerSeries.coeff 10 HAF = 184114257 := by
  change PowerSeries.coeff 10 (HA + HA.subst sympPhi) = 184114257
  rw [map_add, coeff_HA, HA_coeff_ten, coeff_HA_subst_sympPhi_ten]
  norm_num

/-- `[x⁸]y = −1` -/
lemma coeff_sympY_eight : PowerSeries.coeff 8 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 8)

/-- `[x⁸]y² = 5` -/
lemma coeff_sympY_sq_eight : PowerSeries.coeff 8 (sympY ^ 2) = 5 := by
  have h := coeff_sympY_pow_even (n := 4) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h


/-- `[x⁸]y³ = −6` -/
lemma coeff_sympY_cube_eight : PowerSeries.coeff 8 (sympY ^ 3) = -6 := by
  have h := coeff_sympY_pow_even (n := 4) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h


/-- `[x¹⁰]y = −1` -/
lemma coeff_sympY_ten : PowerSeries.coeff 10 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 10)

/-- `[x¹⁰]y² = 7` -/
lemma coeff_sympY_sq_ten : PowerSeries.coeff 10 (sympY ^ 2) = 7 := by
  have h := coeff_sympY_pow_even (n := 5) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h


/-- `[x¹⁰]y³ = −15` -/
lemma coeff_sympY_cube_ten : PowerSeries.coeff 10 (sympY ^ 3) = -15 := by
  have h := coeff_sympY_pow_even (n := 5) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h


/-- `[x¹⁰]y⁴ = 10` -/
lemma coeff_sympY_fourth_ten : PowerSeries.coeff 10 (sympY ^ 4) = 10 := by
  have h := coeff_sympY_pow_even (n := 5) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h


/-- descent value `g₄ = 2699568` -/
lemma sympDescCoeff_HAF_four : sympDescCoeff HAF 4 = 2699568 := by
  rw [sympDescCoeff_eq_sign HAF 4]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three]
  rw [coeff_HAF_even_eight]
  norm_num [coeff_sympY_eight, coeff_sympY_sq_eight, coeff_sympY_cube_eight]

/-- descent value `g₅ = −156368412` -/
lemma sympDescCoeff_HAF_five : sympDescCoeff HAF 5 = -156368412 := by
  rw [sympDescCoeff_eq_sign HAF 5]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three, sympDescCoeff_HAF_four]
  rw [coeff_HAF_even_ten]
  norm_num [coeff_sympY_ten, coeff_sympY_sq_ten, coeff_sympY_cube_ten, coeff_sympY_fourth_ten]

/-- paper defG extended: `[y⁴]G_A = 2699568` -/
theorem sympSym_HA_coeff_four : PowerSeries.coeff 4 (sympSym HA) = 2699568 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 4 = 2699568
  exact sympDescCoeff_HAF_four

/-- paper defG extended: `[y⁵]G_A = −156368412` -/
theorem sympSym_HA_coeff_five : PowerSeries.coeff 5 (sympSym HA) = -156368412 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 5 = -156368412
  exact sympDescCoeff_HAF_five
lemma HA_coeff_eleven : HA_coeff 11 = 1153462995 := by native_decide
/-- `a₁₂ = 9533639025` -/
lemma HA_coeff_twelve : HA_coeff 12 = 9533639025 := by native_decide

/-- `[x¹²](H_A∘φ) = 2325340320` -/
lemma coeff_HA_subst_sympPhi_twelve : PowerSeries.coeff 12 (HA.subst sympPhi) = 2325340320 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 12]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    HA_coeff_eleven, HA_coeff_twelve, coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 11 1 = 11 by native_decide, show Nat.choose 11 2 = 55 by native_decide,
    show Nat.choose 11 3 = 165 by native_decide, show Nat.choose 11 4 = 330 by native_decide,
    show Nat.choose 11 5 = 462 by native_decide, show Nat.choose 11 6 = 462 by native_decide,
    show Nat.choose 11 7 = 330 by native_decide, show Nat.choose 11 8 = 165 by native_decide,
    show Nat.choose 11 9 = 55 by native_decide, show Nat.choose 11 10 = 11 by native_decide]

/-- `[x¹²]F = 11858979345` -/
lemma coeff_HAF_even_twelve : PowerSeries.coeff 12 HAF = 11858979345 := by
  change PowerSeries.coeff 12 (HA + HA.subst sympPhi) = 11858979345
  rw [map_add, coeff_HA, HA_coeff_twelve, coeff_HA_subst_sympPhi_twelve]
  norm_num

/-- `[x¹²]y = −1` -/
lemma coeff_sympY_twelve : PowerSeries.coeff 12 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 12)
/-- `[x¹²]y² = 9` -/
lemma coeff_sympY_sq_twelve : PowerSeries.coeff 12 (sympY ^ 2) = 9 := by
  have h := coeff_sympY_pow_even (n := 6) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹²]y³ = −28` -/
lemma coeff_sympY_cube_twelve : PowerSeries.coeff 12 (sympY ^ 3) = -28 := by
  have h := coeff_sympY_pow_even (n := 6) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹²]y⁴ = 35` -/
lemma coeff_sympY_fourth_twelve : PowerSeries.coeff 12 (sympY ^ 4) = 35 := by
  have h := coeff_sympY_pow_even (n := 6) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹²]y⁵ = −15` -/
lemma coeff_sympY_fifth_twelve : PowerSeries.coeff 12 (sympY ^ 5) = -15 := by
  have h := coeff_sympY_pow_even (n := 6) (m := 5) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- descent value `g₆ = 9417572124` -/
lemma sympDescCoeff_HAF_six : sympDescCoeff HAF 6 = 9417572124 := by
  rw [sympDescCoeff_eq_sign HAF 6]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three,
    sympDescCoeff_HAF_four, sympDescCoeff_HAF_five]
  rw [coeff_HAF_even_twelve]
  norm_num [coeff_sympY_twelve, coeff_sympY_sq_twelve, coeff_sympY_cube_twelve,
    coeff_sympY_fourth_twelve, coeff_sympY_fifth_twelve]

/-- paper defG extended: `[y⁶]G_A = 9417572124` -/
theorem sympSym_HA_coeff_six : PowerSeries.coeff 6 (sympSym HA) = 9417572124 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 6 = 9417572124
  exact sympDescCoeff_HAF_six
lemma HA_coeff_thirteen : HA_coeff 13 = 79326566595 := by native_decide
/-- `a₁₄ = 663835030335` -/
lemma HA_coeff_fourteen : HA_coeff 14 = 663835030335 := by native_decide

/-- `[x¹⁴](H_A∘φ) = 127886769120` -/
lemma coeff_HA_subst_sympPhi_fourteen : PowerSeries.coeff 14 (HA.subst sympPhi) = 127886769120 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 14]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    HA_coeff_eleven, HA_coeff_twelve, HA_coeff_thirteen, HA_coeff_fourteen,
    coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 13 1 = 13 by native_decide, show Nat.choose 13 2 = 78 by native_decide,
    show Nat.choose 13 3 = 286 by native_decide, show Nat.choose 13 4 = 715 by native_decide,
    show Nat.choose 13 5 = 1287 by native_decide, show Nat.choose 13 6 = 1716 by native_decide,
    show Nat.choose 13 7 = 1716 by native_decide, show Nat.choose 13 8 = 1287 by native_decide,
    show Nat.choose 13 9 = 715 by native_decide, show Nat.choose 13 10 = 286 by native_decide,
    show Nat.choose 13 11 = 78 by native_decide, show Nat.choose 13 12 = 13 by native_decide]

/-- `[x¹⁴]F = 791721799455` -/
lemma coeff_HAF_even_fourteen : PowerSeries.coeff 14 HAF = 791721799455 := by
  change PowerSeries.coeff 14 (HA + HA.subst sympPhi) = 791721799455
  rw [map_add, coeff_HA, HA_coeff_fourteen, coeff_HA_subst_sympPhi_fourteen]
  norm_num

/-- `[x¹⁴]y = −1` -/
lemma coeff_sympY_fourteenth : PowerSeries.coeff 14 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 14)
/-- `[x¹⁴]y² = 11` -/
lemma coeff_sympY_sq_fourteenth : PowerSeries.coeff 14 (sympY ^ 2) = 11 := by
  have h := coeff_sympY_pow_even (n := 7) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁴]y³ = −45` -/
lemma coeff_sympY_cube_fourteenth : PowerSeries.coeff 14 (sympY ^ 3) = -45 := by
  have h := coeff_sympY_pow_even (n := 7) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁴]y⁴ = 84` -/
lemma coeff_sympY_fourth_fourteenth : PowerSeries.coeff 14 (sympY ^ 4) = 84 := by
  have h := coeff_sympY_pow_even (n := 7) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁴]y⁵ = −70` -/
lemma coeff_sympY_fifth_fourteenth : PowerSeries.coeff 14 (sympY ^ 5) = -70 := by
  have h := coeff_sympY_pow_even (n := 7) (m := 5) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁴]y⁶ = 21` -/
lemma coeff_sympY_sixth_fourteenth : PowerSeries.coeff 14 (sympY ^ 6) = 21 := by
  have h := coeff_sympY_pow_even (n := 7) (m := 6) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- descent value `g₇ = −582777991998` -/
lemma sympDescCoeff_HAF_seven : sympDescCoeff HAF 7 = -582777991998 := by
  rw [sympDescCoeff_eq_sign HAF 7]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three,
    sympDescCoeff_HAF_four, sympDescCoeff_HAF_five, sympDescCoeff_HAF_six]
  rw [coeff_HAF_even_fourteen]
  norm_num [coeff_sympY_fourteenth, coeff_sympY_sq_fourteenth, coeff_sympY_cube_fourteenth,
    coeff_sympY_fourth_fourteenth, coeff_sympY_fifth_fourteenth, coeff_sympY_sixth_fourteenth]

/-- paper defG extended: `[y⁷]G_A = −582777991998` -/
theorem sympSym_HA_coeff_seven : PowerSeries.coeff 7 (sympSym HA) = -582777991998 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 7 = -582777991998
  exact sympDescCoeff_HAF_seven
lemma HA_coeff_fifteen : HA_coeff 15 = 5582724468093 := by native_decide
/-- `a₁₆ = 47152425626559` -/
lemma HA_coeff_sixteen : HA_coeff 16 = 47152425626559 := by native_decide

/-- `[x¹⁶](H_A∘φ) = 7175426581338` -/
lemma coeff_HA_subst_sympPhi_sixteen : PowerSeries.coeff 16 (HA.subst sympPhi) = 7175426581338 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 16]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    HA_coeff_eleven, HA_coeff_twelve, HA_coeff_thirteen, HA_coeff_fourteen,
    HA_coeff_fifteen, HA_coeff_sixteen, coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 15 1 = 15 by native_decide, show Nat.choose 15 2 = 105 by native_decide,
    show Nat.choose 15 3 = 455 by native_decide, show Nat.choose 15 4 = 1365 by native_decide,
    show Nat.choose 15 5 = 3003 by native_decide, show Nat.choose 15 6 = 5005 by native_decide,
    show Nat.choose 15 7 = 6435 by native_decide, show Nat.choose 15 8 = 6435 by native_decide,
    show Nat.choose 15 9 = 5005 by native_decide, show Nat.choose 15 10 = 3003 by native_decide,
    show Nat.choose 15 11 = 1365 by native_decide, show Nat.choose 15 12 = 455 by native_decide,
    show Nat.choose 15 13 = 105 by native_decide, show Nat.choose 15 14 = 15 by native_decide]

/-- `[x¹⁶]F = 54327852207897` -/
lemma coeff_HAF_even_sixteen : PowerSeries.coeff 16 HAF = 54327852207897 := by
  change PowerSeries.coeff 16 (HA + HA.subst sympPhi) = 54327852207897
  rw [map_add, coeff_HA, HA_coeff_sixteen, coeff_HA_subst_sympPhi_sixteen]
  norm_num

/-- `[x¹⁶]y = −1` -/
lemma coeff_sympY_sixteenth : PowerSeries.coeff 16 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 16)
/-- `[x¹⁶]y² = 13` -/
lemma coeff_sympY_sq_sixteenth : PowerSeries.coeff 16 (sympY ^ 2) = 13 := by
  have h := coeff_sympY_pow_even (n := 8) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁶]y³ = −66` -/
lemma coeff_sympY_cube_sixteenth : PowerSeries.coeff 16 (sympY ^ 3) = -66 := by
  have h := coeff_sympY_pow_even (n := 8) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁶]y⁴ = 165` -/
lemma coeff_sympY_fourth_sixteenth : PowerSeries.coeff 16 (sympY ^ 4) = 165 := by
  have h := coeff_sympY_pow_even (n := 8) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁶]y⁵ = −210` -/
lemma coeff_sympY_fifth_sixteenth : PowerSeries.coeff 16 (sympY ^ 5) = -210 := by
  have h := coeff_sympY_pow_even (n := 8) (m := 5) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁶]y⁶ = 126` -/
lemma coeff_sympY_sixth_sixteenth : PowerSeries.coeff 16 (sympY ^ 6) = 126 := by
  have h := coeff_sympY_pow_even (n := 8) (m := 6) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁶]y⁷ = −28` -/
lemma coeff_sympY_seventh_sixteenth : PowerSeries.coeff 16 (sympY ^ 7) = -28 := by
  have h := coeff_sympY_pow_even (n := 8) (m := 7) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- descent value `g₈ = 36790168266504` -/
lemma sympDescCoeff_HAF_eight : sympDescCoeff HAF 8 = 36790168266504 := by
  rw [sympDescCoeff_eq_sign HAF 8]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three,
    sympDescCoeff_HAF_four, sympDescCoeff_HAF_five, sympDescCoeff_HAF_six, sympDescCoeff_HAF_seven]
  rw [coeff_HAF_even_sixteen]
  norm_num [coeff_sympY_sixteenth, coeff_sympY_sq_sixteenth, coeff_sympY_cube_sixteenth,
    coeff_sympY_fourth_sixteenth, coeff_sympY_fifth_sixteenth, coeff_sympY_sixth_sixteenth,
    coeff_sympY_seventh_sixteenth]

/-- paper defG extended: `[y⁸]G_A = 36790168266504` -/
theorem sympSym_HA_coeff_eight : PowerSeries.coeff 8 (sympSym HA) = 36790168266504 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 8 = 36790168266504
  exact sympDescCoeff_HAF_eight
lemma HA_coeff_seventeen : HA_coeff 17 = 399769750195965 := by native_decide
/-- `a₁₈ = 3400775573443089` -/
lemma HA_coeff_eighteen : HA_coeff 18 = 3400775573443089 := by native_decide

/-- `[x¹⁸](H_A∘φ) = 408814803262056` -/
lemma coeff_HA_subst_sympPhi_eighteen : PowerSeries.coeff 18 (HA.subst sympPhi) = 408814803262056 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 18]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    HA_coeff_eleven, HA_coeff_twelve, HA_coeff_thirteen, HA_coeff_fourteen,
    HA_coeff_fifteen, HA_coeff_sixteen, HA_coeff_seventeen, HA_coeff_eighteen,
    coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 17 1 = 17 by native_decide, show Nat.choose 17 2 = 136 by native_decide,
    show Nat.choose 17 3 = 680 by native_decide, show Nat.choose 17 4 = 2380 by native_decide,
    show Nat.choose 17 5 = 6188 by native_decide, show Nat.choose 17 6 = 12376 by native_decide,
    show Nat.choose 17 7 = 19448 by native_decide, show Nat.choose 17 8 = 24310 by native_decide,
    show Nat.choose 17 9 = 24310 by native_decide, show Nat.choose 17 10 = 19448 by native_decide,
    show Nat.choose 17 11 = 12376 by native_decide, show Nat.choose 17 12 = 6188 by native_decide,
    show Nat.choose 17 13 = 2380 by native_decide, show Nat.choose 17 14 = 680 by native_decide,
    show Nat.choose 17 15 = 136 by native_decide, show Nat.choose 17 16 = 17 by native_decide]

/-- `[x¹⁸]F = 3809590376705145` -/
lemma coeff_HAF_even_eighteen : PowerSeries.coeff 18 HAF = 3809590376705145 := by
  change PowerSeries.coeff 18 (HA + HA.subst sympPhi) = 3809590376705145
  rw [map_add, coeff_HA, HA_coeff_eighteen, coeff_HA_subst_sympPhi_eighteen]
  norm_num

/-- `[x¹⁸]y = −1` -/
lemma coeff_sympY_eighteenth : PowerSeries.coeff 18 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 18)
/-- `[x¹⁸]y² = 15` -/
lemma coeff_sympY_sq_eighteenth : PowerSeries.coeff 18 (sympY ^ 2) = 15 := by
  have h := coeff_sympY_pow_even (n := 9) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁸]y³ = −91` -/
lemma coeff_sympY_cube_eighteenth : PowerSeries.coeff 18 (sympY ^ 3) = -91 := by
  have h := coeff_sympY_pow_even (n := 9) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁸]y⁴ = 286` -/
lemma coeff_sympY_fourth_eighteenth : PowerSeries.coeff 18 (sympY ^ 4) = 286 := by
  have h := coeff_sympY_pow_even (n := 9) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁸]y⁵ = −495` -/
lemma coeff_sympY_fifth_eighteenth : PowerSeries.coeff 18 (sympY ^ 5) = -495 := by
  have h := coeff_sympY_pow_even (n := 9) (m := 5) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁸]y⁶ = 462` -/
lemma coeff_sympY_sixth_eighteenth : PowerSeries.coeff 18 (sympY ^ 6) = 462 := by
  have h := coeff_sympY_pow_even (n := 9) (m := 6) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁸]y⁷ = −210` -/
lemma coeff_sympY_seventh_eighteenth : PowerSeries.coeff 18 (sympY ^ 7) = -210 := by
  have h := coeff_sympY_pow_even (n := 9) (m := 7) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x¹⁸]y⁸ = 36` -/
lemma coeff_sympY_eighth_eighteenth : PowerSeries.coeff 18 (sympY ^ 8) = 36 := by
  have h := coeff_sympY_pow_even (n := 9) (m := 8) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- descent value `g₉ = −2358331843506732` -/
lemma sympDescCoeff_HAF_nine : sympDescCoeff HAF 9 = -2358331843506732 := by
  rw [sympDescCoeff_eq_sign HAF 9]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three,
    sympDescCoeff_HAF_four, sympDescCoeff_HAF_five, sympDescCoeff_HAF_six,
    sympDescCoeff_HAF_seven, sympDescCoeff_HAF_eight]
  rw [coeff_HAF_even_eighteen]
  norm_num [coeff_sympY_eighteenth, coeff_sympY_sq_eighteenth, coeff_sympY_cube_eighteenth,
    coeff_sympY_fourth_eighteenth, coeff_sympY_fifth_eighteenth, coeff_sympY_sixth_eighteenth,
    coeff_sympY_seventh_eighteenth, coeff_sympY_eighth_eighteenth]

/-- paper defG extended: `[y⁹]G_A = −2358331843506732` -/
theorem sympSym_HA_coeff_nine : PowerSeries.coeff 9 (sympSym HA) = -2358331843506732 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 9 = -2358331843506732
  exact sympDescCoeff_HAF_nine
lemma HA_coeff_nineteen : HA_coeff 19 = 29016970072920387 := by native_decide
/-- `a₂₀ = 248256043372999089` -/
lemma HA_coeff_twenty : HA_coeff 20 = 248256043372999089 := by native_decide

/-- `[x²⁰](H_A∘φ) = 23576097906346332` -/
lemma coeff_HA_subst_sympPhi_twenty : PowerSeries.coeff 20 (HA.subst sympPhi) = 23576097906346332 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 20]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    HA_coeff_eleven, HA_coeff_twelve, HA_coeff_thirteen, HA_coeff_fourteen,
    HA_coeff_fifteen, HA_coeff_sixteen, HA_coeff_seventeen, HA_coeff_eighteen,
    HA_coeff_nineteen, HA_coeff_twenty, coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 19 1 = 19 by native_decide, show Nat.choose 19 2 = 171 by native_decide,
    show Nat.choose 19 3 = 969 by native_decide, show Nat.choose 19 4 = 3876 by native_decide,
    show Nat.choose 19 5 = 11628 by native_decide, show Nat.choose 19 6 = 27132 by native_decide,
    show Nat.choose 19 7 = 50388 by native_decide, show Nat.choose 19 8 = 75582 by native_decide,
    show Nat.choose 19 9 = 92378 by native_decide, show Nat.choose 19 10 = 92378 by native_decide,
    show Nat.choose 19 11 = 75582 by native_decide, show Nat.choose 19 12 = 50388 by native_decide,
    show Nat.choose 19 13 = 27132 by native_decide, show Nat.choose 19 14 = 11628 by native_decide,
    show Nat.choose 19 15 = 3876 by native_decide, show Nat.choose 19 16 = 969 by native_decide,
    show Nat.choose 19 17 = 171 by native_decide, show Nat.choose 19 18 = 19 by native_decide]

/-- `[x²⁰]F = 271832141279345421` -/
lemma coeff_HAF_even_twenty : PowerSeries.coeff 20 HAF = 271832141279345421 := by
  change PowerSeries.coeff 20 (HA + HA.subst sympPhi) = 271832141279345421
  rw [map_add, coeff_HA, HA_coeff_twenty, coeff_HA_subst_sympPhi_twenty]
  norm_num

/-- `[x²⁰]y = −1` -/
lemma coeff_sympY_twentieth : PowerSeries.coeff 20 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 20)
/-- `[x²⁰]y² = 17` -/
lemma coeff_sympY_sq_twentieth : PowerSeries.coeff 20 (sympY ^ 2) = 17 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁰]y³ = −120` -/
lemma coeff_sympY_cube_twentieth : PowerSeries.coeff 20 (sympY ^ 3) = -120 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁰]y⁴ = 455` -/
lemma coeff_sympY_fourth_twentieth : PowerSeries.coeff 20 (sympY ^ 4) = 455 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁰]y⁵ = −1001` -/
lemma coeff_sympY_fifth_twentieth : PowerSeries.coeff 20 (sympY ^ 5) = -1001 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 5) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁰]y⁶ = 1287` -/
lemma coeff_sympY_sixth_twentieth : PowerSeries.coeff 20 (sympY ^ 6) = 1287 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 6) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁰]y⁷ = −924` -/
lemma coeff_sympY_seventh_twentieth : PowerSeries.coeff 20 (sympY ^ 7) = -924 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 7) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁰]y⁸ = 330` -/
lemma coeff_sympY_eighth_twentieth : PowerSeries.coeff 20 (sympY ^ 8) = 330 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 8) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁰]y⁹ = −45` -/
lemma coeff_sympY_ninth_twentieth : PowerSeries.coeff 20 (sympY ^ 9) = -45 := by
  have h := coeff_sympY_pow_even (n := 10) (m := 9) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- descent value `g₁₀ = 153015687754620984` -/
lemma sympDescCoeff_HAF_ten : sympDescCoeff HAF 10 = 153015687754620984 := by
  rw [sympDescCoeff_eq_sign HAF 10]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three,
    sympDescCoeff_HAF_four, sympDescCoeff_HAF_five, sympDescCoeff_HAF_six,
    sympDescCoeff_HAF_seven, sympDescCoeff_HAF_eight, sympDescCoeff_HAF_nine]
  rw [coeff_HAF_even_twenty]
  norm_num [coeff_sympY_twentieth, coeff_sympY_sq_twentieth, coeff_sympY_cube_twentieth,
    coeff_sympY_fourth_twentieth, coeff_sympY_fifth_twentieth, coeff_sympY_sixth_twentieth,
    coeff_sympY_seventh_twentieth, coeff_sympY_eighth_twentieth, coeff_sympY_ninth_twentieth]

/-- paper defG extended: `[y¹⁰]G_A = 153015687754620984` -/
theorem sympSym_HA_coeff_ten : PowerSeries.coeff 10 (sympSym HA) = 153015687754620984 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 10 = 153015687754620984
  exact sympDescCoeff_HAF_ten
lemma HA_coeff_twenty_one : HA_coeff 21 = 2129158861755559587 := by native_decide
/-- `a₂₂ = 18301184259810988815` -/
lemma HA_coeff_twenty_two : HA_coeff 22 = 18301184259810988815 := by native_decide

/-- `[x²²](H_A∘φ) = 1373055471369517992` -/
lemma coeff_HA_subst_sympPhi_twenty_two : PowerSeries.coeff 22 (HA.subst sympPhi) = 1373055471369517992 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 22]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_zero, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    HA_coeff_eleven, HA_coeff_twelve, HA_coeff_thirteen, HA_coeff_fourteen,
    HA_coeff_fifteen, HA_coeff_sixteen, HA_coeff_seventeen, HA_coeff_eighteen,
    HA_coeff_nineteen, HA_coeff_twenty, HA_coeff_twenty_one, HA_coeff_twenty_two,
    coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 21 1 = 21 by native_decide, show Nat.choose 21 2 = 210 by native_decide,
    show Nat.choose 21 3 = 1330 by native_decide, show Nat.choose 21 4 = 5985 by native_decide,
    show Nat.choose 21 5 = 20349 by native_decide, show Nat.choose 21 6 = 54264 by native_decide,
    show Nat.choose 21 7 = 116280 by native_decide, show Nat.choose 21 8 = 203490 by native_decide,
    show Nat.choose 21 9 = 293930 by native_decide, show Nat.choose 21 10 = 352716 by native_decide,
    show Nat.choose 21 11 = 352716 by native_decide, show Nat.choose 21 12 = 293930 by native_decide,
    show Nat.choose 21 13 = 203490 by native_decide, show Nat.choose 21 14 = 116280 by native_decide,
    show Nat.choose 21 15 = 54264 by native_decide, show Nat.choose 21 16 = 20349 by native_decide,
    show Nat.choose 21 17 = 5985 by native_decide, show Nat.choose 21 18 = 1330 by native_decide,
    show Nat.choose 21 19 = 210 by native_decide, show Nat.choose 21 20 = 21 by native_decide]

/-- `[x²²]F = 19674239731180506807` -/
lemma coeff_HAF_even_twenty_two : PowerSeries.coeff 22 HAF = 19674239731180506807 := by
  change PowerSeries.coeff 22 (HA + HA.subst sympPhi) = 19674239731180506807
  rw [map_add, coeff_HA, HA_coeff_twenty_two, coeff_HA_subst_sympPhi_twenty_two]
  norm_num

/-- `[x²²]y = −1` -/
lemma coeff_sympY_twentytwo : PowerSeries.coeff 22 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 22)
/-- `[x²²]y² = 19` -/
lemma coeff_sympY_sq_twentytwo : PowerSeries.coeff 22 (sympY ^ 2) = 19 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y³ = −153` -/
lemma coeff_sympY_cube_twentytwo : PowerSeries.coeff 22 (sympY ^ 3) = -153 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y⁴ = 680` -/
lemma coeff_sympY_fourth_twentytwo : PowerSeries.coeff 22 (sympY ^ 4) = 680 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y⁵ = −1820` -/
lemma coeff_sympY_fifth_twentytwo : PowerSeries.coeff 22 (sympY ^ 5) = -1820 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 5) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y⁶ = 3003` -/
lemma coeff_sympY_sixth_twentytwo : PowerSeries.coeff 22 (sympY ^ 6) = 3003 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 6) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y⁷ = −3003` -/
lemma coeff_sympY_seventh_twentytwo : PowerSeries.coeff 22 (sympY ^ 7) = -3003 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 7) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y⁸ = 1716` -/
lemma coeff_sympY_eighth_twentytwo : PowerSeries.coeff 22 (sympY ^ 8) = 1716 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 8) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y⁹ = −495` -/
lemma coeff_sympY_ninth_twentytwo : PowerSeries.coeff 22 (sympY ^ 9) = -495 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 9) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²²]y¹⁰ = 55` -/
lemma coeff_sympY_tenth_twentytwo : PowerSeries.coeff 22 (sympY ^ 10) = 55 := by
  have h := coeff_sympY_pow_even (n := 11) (m := 10) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- descent value `g₁₁ = −10026092063682326736` -/
lemma sympDescCoeff_HAF_eleven : sympDescCoeff HAF 11 = -10026092063682326736 := by
  rw [sympDescCoeff_eq_sign HAF 11]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three,
    sympDescCoeff_HAF_four, sympDescCoeff_HAF_five, sympDescCoeff_HAF_six,
    sympDescCoeff_HAF_seven, sympDescCoeff_HAF_eight, sympDescCoeff_HAF_nine,
    sympDescCoeff_HAF_ten]
  rw [coeff_HAF_even_twenty_two]
  norm_num [coeff_sympY_twentytwo, coeff_sympY_sq_twentytwo, coeff_sympY_cube_twentytwo,
    coeff_sympY_fourth_twentytwo, coeff_sympY_fifth_twentytwo, coeff_sympY_sixth_twentytwo,
    coeff_sympY_seventh_twentytwo, coeff_sympY_eighth_twentytwo, coeff_sympY_ninth_twentytwo,
    coeff_sympY_tenth_twentytwo]

/-- paper defG extended: `[y¹¹]G_A = −10026092063682326736` -/
theorem sympSym_HA_coeff_eleven : PowerSeries.coeff 11 (sympSym HA) = -10026092063682326736 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 11 = -10026092063682326736
  exact sympDescCoeff_HAF_eleven

/-! ## The defG display continued: `g₁₂` (degree-24 block)

The same descent machinery instantiated at degree `24` gives the twelfth
coefficient `g₁₂ = 662302233027566488692` of `G_A(y) = Sym⁺H_A` —
the value needed by the explicitode coefficient equation of degree `11`
(`Submission.CDT.SympExplicitode.GA_odeLHS_coeff_eleven`). -/

/-- `a₂₃ = 157626238006835196237` -/
lemma HA_coeff_twenty_three : HA_coeff 23 = 157626238006835196237 := by native_decide
/-- `a₂₄ = 1360135024740956026161` -/
lemma HA_coeff_twenty_four : HA_coeff 24 = 1360135024740956026161 := by native_decide

/-- `[x²⁴](H_A∘φ) = 80619042136252578672` -/
lemma coeff_HA_subst_sympPhi_twenty_four : PowerSeries.coeff 24 (HA.subst sympPhi) = 80619042136252578672 := by
  rw [coeff_subst_range HA coeff_sympPhi_zero 24]
  norm_num [Finset.sum_range_succ]
  simp [coeff_HA, HA_coeff_one, HA_coeff_two, HA_coeff_three, HA_coeff_four,
    HA_coeff_five, HA_coeff_six, HA_coeff_seven, HA_coeff_eight, HA_coeff_nine, HA_coeff_ten,
    HA_coeff_eleven, HA_coeff_twelve, HA_coeff_thirteen, HA_coeff_fourteen,
    HA_coeff_fifteen, HA_coeff_sixteen, HA_coeff_seventeen, HA_coeff_eighteen,
    HA_coeff_nineteen, HA_coeff_twenty, HA_coeff_twenty_one, HA_coeff_twenty_two,
    HA_coeff_twenty_three, HA_coeff_twenty_four,
    coeff_sympPhi_pow, coeff_sympPhi_of_pos]
  norm_num [show Nat.choose 23 1 = 23 by native_decide, show Nat.choose 23 2 = 253 by native_decide,
    show Nat.choose 23 3 = 1771 by native_decide, show Nat.choose 23 4 = 8855 by native_decide,
    show Nat.choose 23 5 = 33649 by native_decide, show Nat.choose 23 6 = 100947 by native_decide,
    show Nat.choose 23 7 = 245157 by native_decide, show Nat.choose 23 8 = 490314 by native_decide,
    show Nat.choose 23 9 = 817190 by native_decide, show Nat.choose 23 10 = 1144066 by native_decide,
    show Nat.choose 23 11 = 1352078 by native_decide, show Nat.choose 23 12 = 1352078 by native_decide,
    show Nat.choose 23 13 = 1144066 by native_decide, show Nat.choose 23 14 = 817190 by native_decide,
    show Nat.choose 23 15 = 490314 by native_decide, show Nat.choose 23 16 = 245157 by native_decide,
    show Nat.choose 23 17 = 100947 by native_decide, show Nat.choose 23 18 = 33649 by native_decide,
    show Nat.choose 23 19 = 8855 by native_decide, show Nat.choose 23 20 = 1771 by native_decide,
    show Nat.choose 23 21 = 253 by native_decide, show Nat.choose 23 22 = 23 by native_decide]

/-- `[x²⁴]F = 1440754066877208604833` -/
lemma coeff_HAF_even_twenty_four : PowerSeries.coeff 24 HAF = 1440754066877208604833 := by
  change PowerSeries.coeff 24 (HA + HA.subst sympPhi) = 1440754066877208604833
  rw [map_add, coeff_HA, HA_coeff_twenty_four, coeff_HA_subst_sympPhi_twenty_four]
  norm_num

/-- `[x²⁴]y = −1` -/
lemma coeff_sympY_twentyfour : PowerSeries.coeff 24 sympY = -1 := by
  exact coeff_sympY_of_two_le (by norm_num : 2 ≤ 24)
/-- `[x²⁴]y² = 21` -/
lemma coeff_sympY_sq_twentyfour : PowerSeries.coeff 24 (sympY ^ 2) = 21 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y³ = −190` -/
lemma coeff_sympY_cube_twentyfour : PowerSeries.coeff 24 (sympY ^ 3) = -190 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y⁴ = 969` -/
lemma coeff_sympY_fourth_twentyfour : PowerSeries.coeff 24 (sympY ^ 4) = 969 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y⁵ = −3060` -/
lemma coeff_sympY_fifth_twentyfour : PowerSeries.coeff 24 (sympY ^ 5) = -3060 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 5) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y⁶ = 6188` -/
lemma coeff_sympY_sixth_twentyfour : PowerSeries.coeff 24 (sympY ^ 6) = 6188 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 6) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y⁷ = −8008` -/
lemma coeff_sympY_seventh_twentyfour : PowerSeries.coeff 24 (sympY ^ 7) = -8008 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 7) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y⁸ = 6435` -/
lemma coeff_sympY_eighth_twentyfour : PowerSeries.coeff 24 (sympY ^ 8) = 6435 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 8) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y⁹ = −3003` -/
lemma coeff_sympY_ninth_twentyfour : PowerSeries.coeff 24 (sympY ^ 9) = -3003 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 9) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y¹⁰ = 715` -/
lemma coeff_sympY_tenth_twentyfour : PowerSeries.coeff 24 (sympY ^ 10) = 715 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 10) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y¹¹ = −66` -/
lemma coeff_sympY_eleventh_twentyfour : PowerSeries.coeff 24 (sympY ^ 11) = -66 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 11) (by norm_num) (by norm_num)
  norm_num at h
  exact h
/-- `[x²⁴]y¹² = 1` -/
lemma coeff_sympY_twelfth_twentyfour : PowerSeries.coeff 24 (sympY ^ 12) = 1 := by
  have h := coeff_sympY_pow_even (n := 12) (m := 12) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- descent value `g₁₂ = 662302233027566488692` -/
lemma sympDescCoeff_HAF_twelve : sympDescCoeff HAF 12 = 662302233027566488692 := by
  rw [sympDescCoeff_eq_sign HAF 12]
  norm_num [Finset.sum_range_succ]
  rw [sympDescCoeff_HAF_one, sympDescCoeff_HAF_two, sympDescCoeff_HAF_three,
    sympDescCoeff_HAF_four, sympDescCoeff_HAF_five, sympDescCoeff_HAF_six,
    sympDescCoeff_HAF_seven, sympDescCoeff_HAF_eight, sympDescCoeff_HAF_nine,
    sympDescCoeff_HAF_ten, sympDescCoeff_HAF_eleven]
  rw [coeff_HAF_even_twenty_four]
  norm_num [coeff_sympY_twentyfour, coeff_sympY_sq_twentyfour, coeff_sympY_cube_twentyfour,
    coeff_sympY_fourth_twentyfour, coeff_sympY_fifth_twentyfour, coeff_sympY_sixth_twentyfour,
    coeff_sympY_seventh_twentyfour, coeff_sympY_eighth_twentyfour, coeff_sympY_ninth_twentyfour,
    coeff_sympY_tenth_twentyfour, coeff_sympY_eleventh_twentyfour, coeff_sympY_twelfth_twentyfour]

/-- paper defG extended: `[y¹²]G_A = 662302233027566488692` -/
theorem sympSym_HA_coeff_twelve : PowerSeries.coeff 12 (sympSym HA) = 662302233027566488692 := by
  rw [sympSym_eq_sympDesc, sympDesc_coeff]
  change sympDescCoeff HAF 12 = 662302233027566488692
  exact sympDescCoeff_HAF_twelve

end Submission.CDT
