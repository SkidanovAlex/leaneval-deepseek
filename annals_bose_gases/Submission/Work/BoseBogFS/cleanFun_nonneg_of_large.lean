import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.CleanFunAux
import Submission.Work.BoseBogFS.CleanRowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.cleanFun_nonneg_of_large` — the sign row of the clean part

FS `eq:LHYIntegral1` splits the zero-point summand into a *clean* part

`cleanFun v h ρ μ k = 𝒵(τ(k)+c(k), c(k)) − c(k)²/(2‖k‖²)`

(`𝒵(𝒜,ℬ) = 𝒜 − √(𝒜²−ℬ²)`) and the mass part `c²/(4‖k‖²)`.  This module proves that the clean
part is **nonnegative for large `‖k‖`**, uniformly on the admissible region and over the closed
condition `|ρ−μ| ≤ μK_ℓ⁻²/(2¹⁴π)` — the row that lets a finite mode set containing the
low-momentum ball be replaced by the full dual lattice in the lattice form of the clean deficit.

## The mechanism

Write `x = ‖k‖`, `A = τ(k) + c(k)`, `c = c(k) = ρŴ₁(k)`.  The clean part is
`A − √(A²−c²) − c²/(2x²)`, and

  `A − √(A²−c²) = c²/(A + √(A²−c²)) ≥ c²/(2A)`

whenever `0 < A` and `|c| ≤ A` (then `√(A²−c²) ≤ A`).  Hence the clean part is `≥ c²/(2A) −
c²/(2x²) ≥ 0` as soon as `A ≤ x²` (`le_sub_sqrt_div`, proved in `CleanFunAux`).  So it suffices
to produce, for large `x`,

* `0 < A`, i.e. `τ ≥ 2|c|`, and
* `A ≤ x²`, i.e. `x² − τ ≥ |c|`.

Both follow from the two FS-profile bounds of `τ̃ = Work.BoseBoxFock.tauProf`:
`(r−2)₊² ≤ τ̃ r ≤ (r−1)₊²`.  With the two kinematic thresholds `c₁ = cleanLo1`, `c₂ = cleanLo2`:

* **lower bound** (`tauAt_lower`): `(max 0 (x − 2·cleanLoMax))² ≤ τ(k)`, so beyond
  `2·cleanLoMax + √(2·cleanCB)` we get `τ ≥ 2·cleanCB`;
* **linear deficit** (`tauAt_deficit`): `2x·cleanLoMin − cleanLoMax² ≤ x² − τ(k)`, so beyond
  `(cleanCB + cleanLoMax²)/(2·cleanLoMin)` we get `x² − τ ≥ cleanCB`;
* **pairing bound** (`cleanAbsCAtLe`): FS `eq:WSestimate` `|Ŵ₁| ≤ 16π·a` (`W1hat_abs_le`)
  together with `|ρ| ≤ cleanRhoB` from the closed condition gives `|c| ≤ cleanCB`.

The threshold is therefore `cleanKstar v μ = max (2·cleanLoMax + √(2·cleanCB))
((cleanCB + cleanLoMax²)/(2·cleanLoMin))`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The two profile bounds of the chosen kinetic profile -/

/-- The upper profile bound of `Work.BoseBoxFock.exists_tauProf`: `τ̃ r ≤ (max 0 (r−1))²`. -/
lemma tauProfUpperBog (r : ℝ) : Work.BoseBoxFock.tauProf r ≤ (max 0 (r - 1)) ^ 2 :=
  Work.BoseBoxFock.tauProf_spec.2.2.2.1 r

/-- The lower profile bound of `Work.BoseBoxFock.exists_tauProf`: `(max 0 (r−2))² ≤ τ̃ r`. -/
lemma tauProfLowerBog (r : ℝ) : (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
  Work.BoseBoxFock.tauProf_spec.2.2.1 r

/-! ## 2. The elementary one-variable layer -/

/-- `max 0 (c * y) = c * max 0 y` for `c > 0`. -/
private lemma maxZeroMulPos {c y : ℝ} (hc : 0 < c) : max 0 (c * y) = c * max 0 y := by
  rcases le_or_gt 0 y with h | h
  · rw [max_eq_right (mul_nonneg hc.le h), max_eq_right h]
  · rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc.le h.le), max_eq_left h.le, mul_zero]

/-- Rescaling the truncated square: `c²·(max 0 (x/c − d))² = (max 0 (x − d·c))²` for `c > 0`. -/
private lemma sqMaxMulSub {c x d : ℝ} (hc : 0 < c) :
    c ^ 2 * (max 0 (x / c - d)) ^ 2 = (max 0 (x - d * c)) ^ 2 := by
  have h : x - d * c = c * (x / c - d) := by field_simp
  rw [h, maxZeroMulPos hc, mul_pow]

/-- The upper profile bound transported through `r = x/c`:
`c²·τ̃(x/c) ≤ (max 0 (x−c))²`. -/
private lemma termUpper {c x : ℝ} (hc : 0 < c) :
    c ^ 2 * Work.BoseBoxFock.tauProf (x / c) ≤ (max 0 (x - c)) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left (tauProfUpperBog (x / c)) (sq_nonneg c)
  have h2 := sqMaxMulSub (c := c) (x := x) (d := 1) hc
  simpa using le_trans h (le_of_eq h2)

/-- The lower profile bound transported through `r = x/c`:
`(max 0 (x−2c))² ≤ c²·τ̃(x/c)`. -/
private lemma termLower {c x : ℝ} (hc : 0 < c) :
    (max 0 (x - 2 * c)) ^ 2 ≤ c ^ 2 * Work.BoseBoxFock.tauProf (x / c) := by
  have h := mul_le_mul_of_nonneg_left (tauProfLowerBog (x / c)) (sq_nonneg c)
  have h2 := sqMaxMulSub (c := c) (x := x) (d := 2) hc
  simpa using le_trans (le_of_eq h2.symm) h

/-- `(max 0 (x − t))² ≤ (max 0 (x − s))²` for `s ≤ t`. -/
private lemma sqMaxZeroAnti {x s t : ℝ} (hst : s ≤ t) :
    (max 0 (x - t)) ^ 2 ≤ (max 0 (x - s)) ^ 2 := by
  have h : max 0 (x - t) ≤ max 0 (x - s) := max_le_max le_rfl (by linarith)
  exact pow_le_pow_left₀ (le_max_left _ _) h 2

/-- `(max 0 y)² ≤ y²`. -/
private lemma sqMaxZeroLe (y : ℝ) : (max 0 y) ^ 2 ≤ y ^ 2 := by
  rcases le_or_gt 0 y with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_lt h)]
    nlinarith [sq_nonneg y]

/-- `2xc − c² ≤ x² − (max 0 (x−c))²`. -/
private lemma sqSubMaxZeroGe (x c : ℝ) : 2 * x * c - c ^ 2 ≤ x ^ 2 - (max 0 (x - c)) ^ 2 := by
  have h := sqMaxZeroLe (x - c)
  nlinarith [h]

/-! ## 3. The bounds of the profile combination

The combination `A = (1−ε_T)c₁²τ̃(x/c₁) + ε_T c₂²τ̃(x/c₂)` is an affine (in the weights) mixture
of the two rescaled terms `t_i = c_i²τ̃(x/c_i)`, each of which lies between
`(max 0 (x−2c_i))²` and `(max 0 (x−c_i))²`. -/

/-- **The linear deficit of the profile combination.**  For `0 ≤ ε_T ≤ 1`, `c₁, c₂ > 0` and
`x ≥ 0`,

`2x·min(c₁,c₂) − max(c₁,c₂)² ≤ x² − ((1−ε_T)c₁²τ̃(x/c₁) + ε_T c₂²τ̃(x/c₂))`.

Indeed `x² − t_i ≥ 2x·c_i − c_i²` (`sqSubMaxZeroGe`), and the weighted average of the two
right-hand sides is at least `2x·min − max²`. -/
lemma comboDeficit {eT c1 c2 x : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1)
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hx : 0 ≤ x) :
    2 * x * min c1 c2 - (max c1 c2) ^ 2
      ≤ x ^ 2 - ((1 - eT) * c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1)
          + eT * c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2)) := by
  have hw1 : 0 ≤ 1 - eT := by linarith
  have t1 := termUpper (c := c1) (x := x) hc1
  have t2 := termUpper (c := c2) (x := x) hc2
  have e1 := sqSubMaxZeroGe x c1
  have e2 := sqSubMaxZeroGe x c2
  have hcomb1 : min c1 c2 ≤ (1 - eT) * c1 + eT * c2 := by
    nlinarith [min_le_left c1 c2, min_le_right c1 c2, heT0, hw1]
  have hcomb2 : (1 - eT) * c1 ^ 2 + eT * c2 ^ 2 ≤ (max c1 c2) ^ 2 := by
    have hM1 : c1 ≤ max c1 c2 := le_max_left _ _
    have hM2 : c2 ≤ max c1 c2 := le_max_right _ _
    have hMpos : 0 ≤ max c1 c2 := le_trans hc1.le hM1
    have hs1 : c1 ^ 2 ≤ (max c1 c2) ^ 2 := by nlinarith [hM1, hMpos, hc1]
    have hs2 : c2 ^ 2 ≤ (max c1 c2) ^ 2 := by nlinarith [hM2, hMpos, hc2]
    have h := add_le_add (mul_le_mul_of_nonneg_left hs1 hw1) (mul_le_mul_of_nonneg_left hs2 heT0)
    linarith
  have step1 : (1 - eT) * (c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1))
      + eT * (c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2))
      ≤ (1 - eT) * (max 0 (x - c1)) ^ 2 + eT * (max 0 (x - c2)) ^ 2 :=
    add_le_add (mul_le_mul_of_nonneg_left t1 hw1) (mul_le_mul_of_nonneg_left t2 heT0)
  have h4 : 2 * x * min c1 c2 - (max c1 c2) ^ 2
      ≤ (1 - eT) * (2 * x * c1 - c1 ^ 2) + eT * (2 * x * c2 - c2 ^ 2) := by
    have hxw : 2 * x * min c1 c2 ≤ 2 * x * ((1 - eT) * c1 + eT * c2) :=
      mul_le_mul_of_nonneg_left hcomb1 (by linarith)
    have h5 : (1 - eT) * (2 * x * c1 - c1 ^ 2) + eT * (2 * x * c2 - c2 ^ 2)
        = 2 * x * ((1 - eT) * c1 + eT * c2) - ((1 - eT) * c1 ^ 2 + eT * c2 ^ 2) := by ring
    rw [h5]
    linarith
  have split : x ^ 2 - ((1 - eT) * (max 0 (x - c1)) ^ 2 + eT * (max 0 (x - c2)) ^ 2)
      = (1 - eT) * (x ^ 2 - (max 0 (x - c1)) ^ 2)
        + eT * (x ^ 2 - (max 0 (x - c2)) ^ 2) := by ring
  have step3 : (1 - eT) * (2 * x * c1 - c1 ^ 2) + eT * (2 * x * c2 - c2 ^ 2)
      ≤ (1 - eT) * (x ^ 2 - (max 0 (x - c1)) ^ 2)
        + eT * (x ^ 2 - (max 0 (x - c2)) ^ 2) :=
    add_le_add (mul_le_mul_of_nonneg_left e1 hw1) (mul_le_mul_of_nonneg_left e2 heT0)
  have hnL : (1 - eT) * c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1)
      + eT * c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2)
      = (1 - eT) * (c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1))
        + eT * (c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2)) := by ring
  rw [hnL]
  have hfin : 2 * x * min c1 c2 - (max c1 c2) ^ 2
      ≤ x ^ 2 - ((1 - eT) * (max 0 (x - c1)) ^ 2 + eT * (max 0 (x - c2)) ^ 2) := by
    rw [split]
    linarith
  linarith [hfin, step1]

/-- **The quadratic lower bound of the profile combination.**  For `0 ≤ ε_T ≤ 1` and `c₁,c₂ > 0`,

`(max 0 (x − 2·max(c₁,c₂)))² ≤ (1−ε_T)c₁²τ̃(x/c₁) + ε_T c₂²τ̃(x/c₂)`:

each `t_i` dominates `(max 0 (x−2c_i))² ≥ (max 0 (x−2·max(c₁,c₂)))²`, and a convex combination
dominates its minimum. -/
lemma comboLower {eT c1 c2 x : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    (max 0 (x - 2 * max c1 c2)) ^ 2
      ≤ (1 - eT) * c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1)
        + eT * c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2) := by
  have hw1 : 0 ≤ 1 - eT := by linarith
  have s1 : (max 0 (x - 2 * max c1 c2)) ^ 2
      ≤ c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1) :=
    le_trans (sqMaxZeroAnti (by linarith [le_max_left c1 c2] : 2 * c1 ≤ 2 * max c1 c2))
      (termLower (c := c1) (x := x) hc1)
  have s2 : (max 0 (x - 2 * max c1 c2)) ^ 2
      ≤ c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2) :=
    le_trans (sqMaxZeroAnti (by linarith [le_max_right c1 c2] : 2 * c2 ≤ 2 * max c1 c2))
      (termLower (c := c2) (x := x) hc2)
  have hnL : (1 - eT) * c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1)
      + eT * c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2)
      = (1 - eT) * (c1 ^ 2 * Work.BoseBoxFock.tauProf (x / c1))
        + eT * (c2 ^ 2 * Work.BoseBoxFock.tauProf (x / c2)) := by ring
  rw [hnL]
  have hsum : (max 0 (x - 2 * max c1 c2)) ^ 2
      = (1 - eT) * (max 0 (x - 2 * max c1 c2)) ^ 2
        + eT * (max 0 (x - 2 * max c1 c2)) ^ 2 := by ring
  rw [hsum]
  exact add_le_add (mul_le_mul_of_nonneg_left s1 hw1) (mul_le_mul_of_nonneg_left s2 heT0)

/-! ## 4. The two bounds at the honest kinetic symbol -/

/-- The honest kinetic symbol as the profile combination at `c₁ = cleanLo1`, `c₂ = cleanLo2`. -/
private lemma tauAt_eq_combo (v : E3 → ℝ) (μ : ℝ) (k : E3) :
    tauAt v μ k = (1 - (paramsAt μ (a v)).eT) * (cleanLo1 v μ) ^ 2
        * Work.BoseBoxFock.tauProf (‖k‖ / cleanLo1 v μ)
      + (paramsAt μ (a v)).eT * (cleanLo2 v μ) ^ 2
        * Work.BoseBoxFock.tauProf (‖k‖ / cleanLo2 v μ) := by
  rw [tauAt, Work.BoseBoxFock.tauSm, cleanLo1, cleanLo2]

/-- The two kinematic thresholds are positive. -/
private lemma cleanLo_pos {v : E3 → ℝ} {μ : ℝ}
    (hs : 0 < (paramsAt μ (a v)).s) (hd : 0 < (paramsAt μ (a v)).d)
    (hℓ : 0 < ell v μ) : 0 < cleanLo1 v μ ∧ 0 < cleanLo2 v μ :=
  ⟨by rw [cleanLo1]; positivity, by rw [cleanLo2]; positivity⟩

/-- **The linear deficit of `τ`:** `2x·cleanLoMin − cleanLoMax² ≤ x² − τ(k)`. -/
lemma tauAt_deficit {v : E3 → ℝ} {μ : ℝ} {k : E3}
    (hs : 0 < (paramsAt μ (a v)).s) (hd : 0 < (paramsAt μ (a v)).d)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1)
    (hℓ : 0 < ell v μ) :
    2 * ‖k‖ * cleanLoMin v μ - (cleanLoMax v μ) ^ 2 ≤ ‖k‖ ^ 2 - tauAt v μ k := by
  obtain ⟨hc1, hc2⟩ := cleanLo_pos hs hd hℓ
  have h := comboDeficit (eT := (paramsAt μ (a v)).eT) (c1 := cleanLo1 v μ)
    (c2 := cleanLo2 v μ) (x := ‖k‖) heT0 heT1 hc1 hc2 (norm_nonneg k)
  have hM : cleanLoMax v μ = max (cleanLo1 v μ) (cleanLo2 v μ) := rfl
  have hm : cleanLoMin v μ = min (cleanLo1 v μ) (cleanLo2 v μ) := rfl
  rw [tauAt_eq_combo, hM, hm]
  exact h

/-- **The quadratic lower bound of `τ`:** `(max 0 (‖k‖ − 2·cleanLoMax))² ≤ τ(k)`. -/
lemma tauAt_lower {v : E3 → ℝ} {μ : ℝ} {k : E3}
    (hs : 0 < (paramsAt μ (a v)).s) (hd : 0 < (paramsAt μ (a v)).d)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1)
    (hℓ : 0 < ell v μ) :
    (max 0 (‖k‖ - 2 * cleanLoMax v μ)) ^ 2 ≤ tauAt v μ k := by
  obtain ⟨hc1, hc2⟩ := cleanLo_pos hs hd hℓ
  have h := comboLower (eT := (paramsAt μ (a v)).eT) (c1 := cleanLo1 v μ)
    (c2 := cleanLo2 v μ) (x := ‖k‖) heT0 heT1 hc1 hc2
  have hM : cleanLoMax v μ = max (cleanLo1 v μ) (cleanLo2 v μ) := rfl
  rw [tauAt_eq_combo, hM]
  exact h

/-! ## 5. The uniform bound of the pairing coefficient -/

/-- **FS `eq:WSestimate` at the closed condition.**  Under `Adm` and `CloseCondFS v μ ρ`,

`|cAt v h ρ μ k| ≤ cleanCB v μ = (μ + μK_ℓ⁻²/(2¹⁴π))·16π·a v`:

`|ρ| ≤ μ + μK_ℓ⁻²/(2¹⁴π)` is the arithmetic of `|ρ−μ| ≤ μK_ℓ⁻²/(2¹⁴π)`, and
`|Ŵ₁(k)| ≤ 16π·a v` is `Work.BoseB7AK.W1rows.W1hat_abs_le`, whose regime `R ≤ ℓ·chiR0` is
supplied by `exists_adm_ell_ge` at a small diluteness threshold. -/
theorem cleanAbsCAtLe {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ → ∀ k : E3,
        |cAt v h ρ μ k| ≤ cleanCB v μ := by
  have hχpos : 0 < Submission.BoseGases.chiR0 := Submission.BoseGases.chiR0_pos
  obtain ⟨ε, hε, hε'⟩ := exists_adm_ell_ge (v := v) hav
    (M := R / Submission.BoseGases.chiR0) (div_pos hR hχpos)
  refine ⟨ε, hε, fun μ hμ ρ hρ k => ?_⟩
  have hμpos : 0 < μ := hμ.1
  obtain ⟨-, hd, hs, heT0, heT1, hb, hKl⟩ := Work.BoseBox.paramsAt_facts hμpos hμ.2.2
  have hℓpos : 0 < ell v μ := lt_of_lt_of_le (div_pos hR hχpos) (hε' μ hμ)
  have hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0 := by
    have h0 := hε' μ hμ
    rw [div_le_iff₀ hχpos] at h0
    linarith
  have hW := Work.BoseB7AK.W1rows.W1hat_abs_le (ℓ := ell v μ) hR hℓpos hv hvrad hv_supp h hRℓ k
  have hW' : |Work.BoseFixR.chat (W1At v h μ) k| ≤ 16 * Real.pi * a v := by
    have hWAt : W1At v h μ = Work.BoseFixR.W1fun v h (ell v μ) := rfl
    rw [hWAt]
    exact hW
  have hcl : |ρ - μ| ≤ μ * (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * Real.pi) :=
    hρ
  have hρb : |ρ| ≤ cleanRhoB v μ := by
    rw [cleanRhoB]
    have h1 : |ρ| ≤ |ρ - μ| + |μ| := by
      have := abs_add_le (ρ - μ) μ
      simpa using this
    have h2 : |μ| = μ := abs_of_pos hμpos
    linarith [h1, hcl, h2]
  have hnn : 0 ≤ cleanRhoB v μ := le_trans (abs_nonneg ρ) hρb
  calc |cAt v h ρ μ k|
      = |ρ| * |Work.BoseFixR.chat (W1At v h μ) k| := by rw [cAt, abs_mul]
    _ ≤ cleanRhoB v μ * (16 * Real.pi * a v) :=
        mul_le_mul hρb hW' (abs_nonneg _) hnn
    _ = cleanCB v μ := by rw [cleanCB]

/-! ## 6. The sign row -/

theorem cleanFun_nonneg_of_large {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      ∃ kstar : ℝ, 0 ≤ kstar ∧ ∀ k : EuclideanSpace ℝ (Fin 3), kstar ≤ ‖k‖ →
        0 ≤ Work.BoseBogFS.cleanFun v h ρ μ k := by
  obtain ⟨ε₀, hε₀pos, hcB⟩ := cleanAbsCAtLe (v := v) (h := h) (R := R) hR hv hvrad hv_supp hav
  refine ⟨ε₀, hε₀pos, fun μ hAdm ρ hclose => ?_⟩
  obtain ⟨hμpos, hμa3le, hP⟩ := hAdm
  have hAdm' : Work.BoseBoxFix.Adm v ε₀ μ := ⟨hμpos, hμa3le, hP⟩
  obtain ⟨ha, hd, hs, heT0, heT1, hb, hKl⟩ := Work.BoseBox.paramsAt_facts hμpos hP
  have hℓpos : 0 < ell v μ := by
    rw [Work.BoseFixR.ell_eq]
    exact Work.BoseBox.sideAt_pos hμpos ha
  obtain ⟨hc1, hc2⟩ := cleanLo_pos (v := v) (μ := μ) hs hd hℓpos
  have hVpos : 0 < cleanLoMax v μ := by
    rw [cleanLoMax]
    exact lt_of_lt_of_le hc1 (le_max_left _ _)
  have hκpos : 0 < cleanLoMin v μ := by
    rw [cleanLoMin]
    exact lt_min hc1 hc2
  have hCBpos : 0 < cleanCB v μ := by
    have h1 : 0 < cleanRhoB v μ := by
      rw [cleanRhoB]
      have h2 : 0 < (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hKl _
      positivity
    rw [cleanCB]
    exact mul_pos h1 (by positivity)
  refine ⟨cleanKstar v μ, le_max_left _ _, fun k hk => ?_⟩
  -- the two threshold consequences of `cleanKstar v μ ≤ ‖k‖`
  have hk1 : 2 * cleanLoMax v μ + Real.sqrt (2 * cleanCB v μ) ≤ ‖k‖ := by
    refine le_trans ?_ hk
    rw [cleanKstar]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hk2 : (cleanCB v μ + (cleanLoMax v μ) ^ 2) / (2 * cleanLoMin v μ) ≤ ‖k‖ := by
    refine le_trans ?_ hk
    rw [cleanKstar]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h2V : 2 * cleanLoMax v μ ≤ ‖k‖ := by
    have := Real.sqrt_nonneg (2 * cleanCB v μ)
    linarith
  have hxpos : 0 < ‖k‖ := lt_of_lt_of_le (by linarith) h2V
  -- `τ ≥ 2·cleanCB`
  have hτlow := tauAt_lower (v := v) (μ := μ) (k := k) hs hd heT0 heT1 hℓpos
  have hxV : Real.sqrt (2 * cleanCB v μ) ≤ ‖k‖ - 2 * cleanLoMax v μ := by linarith
  have hmaxeq : max 0 (‖k‖ - 2 * cleanLoMax v μ) = ‖k‖ - 2 * cleanLoMax v μ :=
    max_eq_right (le_trans (Real.sqrt_nonneg _) hxV)
  have hτ2CB : 2 * cleanCB v μ ≤ tauAt v μ k := by
    have hsq : 2 * cleanCB v μ ≤ (‖k‖ - 2 * cleanLoMax v μ) ^ 2 := by
      have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hxV 2
      rwa [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * cleanCB v μ)] at h
    rw [hmaxeq] at hτlow
    linarith
  -- `‖k‖² − τ ≥ cleanCB`
  have hτdef := tauAt_deficit (v := v) (μ := μ) (k := k) hs hd heT0 heT1 hℓpos
  have h2xκ : cleanCB v μ + (cleanLoMax v μ) ^ 2 ≤ 2 * ‖k‖ * cleanLoMin v μ := by
    have h0 : 0 ≤ 2 * cleanLoMin v μ := by linarith
    have h := mul_le_mul_of_nonneg_left hk2 h0
    have hc : 2 * cleanLoMin v μ * ((cleanCB v μ + (cleanLoMax v μ) ^ 2)
        / (2 * cleanLoMin v μ)) = cleanCB v μ + (cleanLoMax v μ) ^ 2 := by
      field_simp
    linarith [h, hc]
  have hx2τ : cleanCB v μ ≤ ‖k‖ ^ 2 - tauAt v μ k := by linarith
  -- the three hypotheses of the core, and the core
  have hcabs : |cAt v h ρ μ k| ≤ cleanCB v μ := hcB μ hAdm' ρ hclose k
  have hApos : 0 < tauAt v μ k + cAt v h ρ μ k := by
    have h1 : -(cleanCB v μ) ≤ cAt v h ρ μ k := (abs_le.mp hcabs).1
    linarith
  have hAc : |cAt v h ρ μ k| ≤ tauAt v μ k + cAt v h ρ μ k := by
    have h1 := (abs_le.mp hcabs).1
    have h2 := (abs_le.mp hcabs).2
    rw [abs_le]
    constructor <;> linarith
  have hAx : tauAt v μ k + cAt v h ρ μ k ≤ ‖k‖ ^ 2 := by
    have h2 := (abs_le.mp hcabs).2
    linarith
  have hcore := le_sub_sqrt_div (A := tauAt v μ k + cAt v h ρ μ k) (c := cAt v h ρ μ k)
    (x := ‖k‖) hApos hAc hAx
  have hclean : cleanFun v h ρ μ k
      = (tauAt v μ k + cAt v h ρ μ k)
        - Real.sqrt ((tauAt v μ k + cAt v h ρ μ k) ^ 2 - (cAt v h ρ μ k) ^ 2)
        - (cAt v h ρ μ k) ^ 2 / (2 * ‖k‖ ^ 2) := by
    rw [cleanFun, Work.BoseB6.bogZeroPoint]
  rw [hclean]
  exact hcore

end Work.BoseBogFS
