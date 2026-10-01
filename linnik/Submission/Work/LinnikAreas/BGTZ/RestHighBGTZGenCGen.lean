import Mathlib
import Submission.Work.LinnikAreas.BGTZ.RestHighBGTZGenC
import Submission.Work.LinnikAreas.BGTZ.algPowCS
import Submission.Work.LinnikAreas.RestHighFree

namespace Work.LinnikAreas.BGTZ

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section
open Work.LinnikContract
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-!
# `Work.LinnikAreas.BGTZ.RestHighBGTZGenCGen` — the `λ₁`-saving high-zero bound from the BGTZ
repulsion with an arbitrary additive constant `C₀` and an arbitrary log-free family count
coefficient `c₃ = 261/100`

`Submission/Work/LinnikAreas/BGTZ/RestHighBGTZGenC.lean` proves `Siegel.RestHighBGTZSpec (-3/2)`
from the *specific* log-free family count `LogFreeFamHeight (5/2) (3/2)` (the coefficient obtained
from Jutila + Huxley).  The present file generalises that argument to the coefficient
`c₃ = 261/100 = 2.61 < 49/10`, which is the one available from Jutila + Montgomery *alone* (no
Huxley; see `Submission/Work/LinnikAreas/logFreeFamOfMontgomery.lean`).

Only two things change.  Write `s := 49/10 - c₃ = 229/100` for the *net* kernel decay rate of a
zero above the repulsion floor (`e^{c₃ λ}·e^{-(49/10) λ} = e^{-s λ}`).

* the per-layer repulsion mass bound (`windowMassFloorGenAux`) produces the factor
  `e^{-s·Lf j}` in place of `e^{-(12/5)·Lf j}` (`Lf j` the repulsion floor of the `j`-th dyadic
  layer), and the conversion of that factor into a power of `λ₁ = e^{-α}` (`algPowCS`) and the
  layer gap (`layerGap2S`) must be re-run with the exponent `s` in place of `12/5`;
* the layer gap is weaker for the larger `c₃` (a saving of `2^{-j/2}·λ₁^{s/U_j}` rather than
  `2^{-j/2}·λ₁^{12/(5U_j)}`), so the height threshold is raised from `log q ≥ 20` to
  `log q ≥ 200`; the gain `2^{-j/4}` per layer and the full factor `λ₁` survive, because the
  exponent deficit `α(1 - s/U_j) ≤ (log 2/4)·j` still holds for `log q ≥ 200`.

The rest of the argument (the dyadic split at `J = ⌈2 log q/log 2⌉`, the `λ₁`-free tail
`windowMassFreeGenAux`, the split of `S` at `λ₁` into the repulsion range and the zero-free range
`height_sep_of_ZFR`) is unchanged.
-/

/-- The geometric tail with ratio `2^{-1/4}`. -/
private lemma geom_le_quarter (A : Finset ℕ) :
    (∑ j ∈ A, ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j) ≤ (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹ := by
  have h0 : 0 ≤ (2 : ℝ) ^ (-(1 / 4) : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h1 : (2 : ℝ) ^ (-(1 / 4) : ℝ) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    refine inv_lt_one_of_one_lt₀ ?_
    rw [← Real.rpow_zero 2]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hs := summable_geometric_of_lt_one h0 h1
  calc (∑ j ∈ A, ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j)
      ≤ ∑' j : ℕ, ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j :=
        Summable.sum_le_tsum A (fun i _ => by positivity) hs
    _ = (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹ := tsum_geometric_of_lt_one h0 h1

/-- **Per-height-window Abel summation with a repulsion floor**, for an arbitrary coefficient `c`
of the `λ`-count (`c < 49/10`).  This is `Work.LinnikAreas.windowMassFloor` with the fixed
exponent `5/2` of the counting hypothesis replaced by the parameter `c`; the resulting kernel
saving exponent is `49/10 - c` rather than `12/5`. -/
private theorem windowMassFloorGenAux {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₂ H Λ c : ℝ} (hc0 : 0 < c) (hc : c < 49 / 10) (hC₂ : 0 < C₂) (hH : 0 < H) (hΛ : 0 < Λ)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp (c * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ))
    (hfloor : ∀ z ∈ S, Λ ≤ lamOf q z.2) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp c * Real.exp ((c - 49 / 10) * Λ)
          / (1 - Real.exp (c - 49 / 10)) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hlamL : ∀ z ∈ S, lamOf q z.2 ≤ Real.log (q : ℝ) := by
    intro z hz
    have h1 : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
    rw [lamOf]
    calc (1 - z.2.re) * Real.log (q : ℝ) ≤ 1 * Real.log (q : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) hlog.le
      _ = Real.log (q : ℝ) := by ring
  have hcount : ∀ t : ℝ, Λ ≤ t → t ≤ Real.log (q : ℝ) →
      (∑ z ∈ S.filter (fun z => lamOf q z.2 ≤ t), (zeroMult z.1 z.2 : ℝ))
        ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (c * t) := by
    intro t htΛ htL
    have htpos : 0 < t := lt_of_lt_of_le hΛ htΛ
    calc (∑ z ∈ S.filter (fun z => lamOf q z.2 ≤ t), (zeroMult z.1 z.2 : ℝ))
        ≤ Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ)) :=
          pairCountHeight_dom hq χ₁ β₁ _
            (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
            (fun z hz => (Finset.mem_filter.mp hz).2)
            (fun z hz => him z (Finset.mem_filter.mp hz).1)
            (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
      _ ≤ C₂ * Real.exp (c * t) * H ^ (3 / 2 : ℝ) := hcnt t htpos htL
      _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp (c * t) := by ring
  exact sum_mul_exp_neg_le_of_count (S := S)
    (m := fun z : DirichletCharacter ℂ q × ℂ => (zeroMult z.1 z.2 : ℝ))
    (lam := fun z : DirichletCharacter ℂ q × ℂ => lamOf q z.2)
    (a₀ := 49 / 10) (Λ := Λ) (L := Real.log (q : ℝ)) (D := C₂)
    (lam₁ := H ^ (3 / 2 : ℝ)) (c := c)
    (by norm_num) hc0.le hc hC₂ hΛ (Real.rpow_pos_of_pos hH _)
    (fun z _ => Nat.cast_nonneg _) hfloor hlamL hcount

/-- **The `λ₁`-free per-window mass bound** (with the minimum of the window's `λ`'s as floor), for
an arbitrary coefficient `c` of the `λ`-count.  This is `Work.LinnikAreas.windowMassFree` with
`5/2` replaced by `c` and `12/5` by `49/10 - c`. -/
private theorem windowMassFreeGenAux {q : ℕ} [NeZero q] (hq : 1 < q)
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ)
    {C₂ H c : ℝ} (hc0 : 0 < c) (hc : c < 49 / 10) (hC₂ : 0 < C₂) (hH : 0 < H)
    (hcnt : ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp (c * t) * H ^ (3 / 2 : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁))
    (him : ∀ z ∈ S, |z.2.im| * Real.log (q : ℝ) ≤ H * Real.log (q : ℝ)) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
      ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp c / (1 - Real.exp (c - 49 / 10)) := by
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
  rcases S.eq_empty_or_nonempty with hS | hne
  · subst hS
    simp only [Finset.sum_empty]
    exact div_nonneg (by positivity) (by
      have : Real.exp (c - 49 / 10) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith)
  · have hSpos : ∀ z ∈ S, 0 < lamOf q z.2 := fun z hz => by
      have h1 : z.2.re < 1 := boxMaxZeroAux.zeroMult_re_lt_one z.1 (hzm z hz)
      rw [lamOf]; exact mul_pos (by linarith) hlog
    set Λ : ℝ := S.inf' hne (fun z => lamOf q z.2) with hΛdef
    have hΛpos : 0 < Λ := by
      obtain ⟨z, hz, heq⟩ := Finset.exists_mem_eq_inf' hne (fun z => lamOf q z.2)
      rw [hΛdef, heq]; exact hSpos z hz
    have hΛle : ∀ z ∈ S, Λ ≤ lamOf q z.2 := by
      intro z hz
      rw [hΛdef]
      exact Finset.inf'_le (s := S) (fun z => lamOf q z.2) hz
    have hcount : ∀ t : ℝ, Λ ≤ t → t ≤ Real.log (q : ℝ) →
        (∑ z ∈ S.filter (fun z => lamOf q z.2 ≤ t), (zeroMult z.1 z.2 : ℝ))
          ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp (c * t) := by
      intro t hΛt htL
      have htpos : 0 < t := lt_of_lt_of_le hΛpos hΛt
      calc (∑ z ∈ S.filter (fun z => lamOf q z.2 ≤ t), (zeroMult z.1 z.2 : ℝ))
          ≤ Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ)) :=
            pairCountHeight_dom hq χ₁ β₁ _
              (fun z hz => hzm z (Finset.mem_filter.mp hz).1)
              (fun z hz => (Finset.mem_filter.mp hz).2)
              (fun z hz => him z (Finset.mem_filter.mp hz).1)
              (fun z hz => hexc z (Finset.mem_filter.mp hz).1)
        _ ≤ C₂ * Real.exp (c * t) * H ^ (3 / 2 : ℝ) := hcnt t htpos htL
        _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp (c * t) := by ring
    have hlamL : ∀ z ∈ S, lamOf q z.2 ≤ Real.log (q : ℝ) := by
      intro z hz
      have h1 : 0 < z.2.re := zeroMult_re_pos z.1 (hzm z hz)
      rw [lamOf]
      nlinarith [hlog]
    have hmain := sum_mul_exp_neg_le_of_count (S := S)
      (m := fun z : DirichletCharacter ℂ q × ℂ => (zeroMult z.1 z.2 : ℝ))
      (lam := fun z : DirichletCharacter ℂ q × ℂ => lamOf q z.2)
      (a₀ := 49 / 10) (Λ := Λ) (L := Real.log (q : ℝ)) (D := C₂)
      (lam₁ := H ^ (3 / 2 : ℝ)) (c := c)
      (by norm_num) hc0.le hc hC₂ hΛpos
      (Real.rpow_pos_of_pos hH _) (fun z _ => Nat.cast_nonneg _) hΛle hlamL hcount
    refine hmain.trans ?_
    have hden : 0 < 1 - Real.exp (c - 49 / 10) := by
      have : Real.exp (c - 49 / 10) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
    have hexp_le : Real.exp ((c - 49 / 10) * Λ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hΛpos]
    have hnum : 0 ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp c := by positivity
    calc C₂ * H ^ (3 / 2 : ℝ) * Real.exp c * Real.exp ((c - 49 / 10) * Λ)
            / (1 - Real.exp (c - 49 / 10))
        ≤ C₂ * H ^ (3 / 2 : ℝ) * Real.exp c * 1 / (1 - Real.exp (c - 49 / 10)) := by
          refine div_le_div_of_nonneg_right ?_ hden.le
          exact mul_le_mul_of_nonneg_left hexp_le hnum
      _ = C₂ * H ^ (3 / 2 : ℝ) * Real.exp c / (1 - Real.exp (c - 49 / 10)) := by ring

/-- **The `λ₁`-free mass bound for the high zeros, from an arbitrary log-free family count.**
This is `Work.LinnikAreas.highFinsetBoundFree` with the coefficient `5/2` replaced by the
parameter `c₃ < 49/10`; the conclusion `K·(log q)^{-2}` is unchanged. -/
private theorem highFinsetBoundFreeGenAux {c₃ : ℝ} (hc₃ : c₃ < 49 / 10)
    (hfam : Work.ZeroDensity.LogFreeFamHeight c₃ (3 / 2)) :
    ∃ K : ℝ, 0 < K ∧ ∃ q₀ : ℕ, ∀ {q : ℕ} [NeZero q], q₀ ≤ q → 1 < q →
      ∀ (χ₁ : DirichletCharacter ℂ q) (β₁ : ℂ) (S : Finset (DirichletCharacter ℂ q × ℂ)),
        (∀ z ∈ S, zeroMult z.1 z.2 ≠ 0) →
        (∀ z ∈ S, 1 < |z.2.im|) →
        (∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = β₁)) →
        (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ K * (Real.log q) ^ (-2 : ℝ) := by
  obtain ⟨C₂, hC₂, q₀₀, hfam₀⟩ := hfam
  have hDpos : 0 < Real.exp (max c₃ 0) * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹ := by
    have h1 : Real.exp (max c₃ 0 - 49 / 10) < 1 := by
      rw [Real.exp_lt_one_iff]
      have h2 : max c₃ 0 < 49 / 10 := max_lt hc₃ (by norm_num)
      linarith
    positivity
  have hBpos : 0 < (2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹ := by
    have h1 : (2 : ℝ) ^ ((3 / 2 : ℝ) - 2) < 1 := by
      have h2 : 1 < (2 : ℝ) ^ (2 - (3 / 2 : ℝ)) := Real.one_lt_rpow (by norm_num) (by norm_num)
      rw [show (3 / 2 : ℝ) - 2 = -(2 - 3 / 2) by norm_num, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_lt_one_of_one_lt₀ h2
    positivity
  refine ⟨4 * C₂ * (Real.exp (max c₃ 0) * (1 - Real.exp (max c₃ 0 - 49 / 10))⁻¹)
      * ((2 : ℝ) ^ (3 / 2 : ℝ) * (1 - (2 : ℝ) ^ ((3 / 2 : ℝ) - 2))⁻¹),
    mul_pos (mul_pos (mul_pos (by norm_num) hC₂) hDpos) hBpos, max q₀₀ 2, ?_⟩
  intro q _ hq₀ hq₁ χ₁ β₁ S hzm hhigh hexc
  have hq₀' : q₀₀ ≤ q := le_trans (le_max_left _ _) hq₀
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq₁)
  have hlam1pos : 0 < (Real.log (q : ℝ)) ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hlog _
  have hcnt : ∀ t T : ℝ, 0 < t → t ≤ Real.log q → Real.log q ≤ T →
      Siegel.pairCountHeight χ₁ β₁ t T
        ≤ C₂ * (Real.log q) ^ (-(3 / 2 : ℝ)) * Real.exp (c₃ * t) * T ^ (3 / 2 : ℝ) :=
    fun t T ht htL hT => pairCountHeight_le_famCount_scaled (q := q) hq₁ χ₁ β₁
      (fun σ T h1 h2 h3 => hfam₀ q hq₀' σ T h1 h2 h3) ht htL hT
  have hbound := high_finset_bound_hi hq₁ χ₁ β₁ hC₂ hlam1pos hc₃
    (by norm_num : (3 : ℝ) / 2 < 2) hcnt S hzm hhigh hexc
  have hprod : (Real.log q) ^ (-(3 / 2 : ℝ)) * (Real.log q) ^ ((3 / 2 : ℝ) - 2)
      = (Real.log q) ^ (-2 : ℝ) := by
    rw [← Real.rpow_add hlog]
    norm_num
  refine hbound.trans (le_of_eq ?_)
  rw [← hprod]
  ring

/-- **The layer-gap estimate for the net decay exponent `s = 229/100`.**  With
`U_j = 11/5 + (11/10)·log(5 + 2^{j+1})/𝓛`, `α > 0`, `α ≤ 𝓛/2` and `𝓛 ≥ 200`,
`2^{-j/2}·(e^{-α})^{s/U_j} ≤ e^{-α}·2^{-j/4}`: the repulsion saving of the `j`-th height layer,
measured with the *smaller* net exponent `s = 49/10 - 261/100`, still contributes the full factor
`e^{-α}` and the geometric gain `2^{-j/4}`.  This is `Work.LinnikAreas.BGTZ.layer_gap2` with
`12/5` replaced by `229/100` (and the height threshold raised from `20` to `200`). -/
private theorem layerGap2S {𝓛 α : ℝ} (h𝓛 : 200 ≤ 𝓛) (hα0 : 0 < α) (hα : α ≤ 𝓛 / 2) (j : ℕ) :
    ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j
        * (Real.exp (-α)) ^ ((229 / 100) / (11 / 5 + (11 / 10)
            * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / 𝓛)))
      ≤ Real.exp (-α) * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set X : ℝ := Real.log (5 + (2 : ℝ) ^ (j + 1)) with hXdef
  set U : ℝ := 11 / 5 + (11 / 10) * (X / 𝓛) with hUdef
  have h𝓛pos : 0 < 𝓛 := by linarith
  have hXpos : 0 < X := by
    rw [hXdef]
    refine Real.log_pos ?_
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hξnn : 0 ≤ X / 𝓛 := div_nonneg hXpos.le h𝓛pos.le
  have hUpos : 0 < U := by rw [hUdef]; nlinarith [hξnn]
  have hXexp : X ≤ Real.log 9 + ((j : ℝ) + 1) * Real.log 2 := by
    rw [hXdef]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
    have h4 : (5 : ℝ) + (2 : ℝ) ^ (j + 1) ≤ 9 * (2 : ℝ) ^ (j + 1) := by linarith
    calc Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log (9 * (2 : ℝ) ^ (j + 1)) :=
          Real.log_le_log (by positivity) h4
      _ = Real.log 9 + ((j : ℝ) + 1) * Real.log 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
          push_cast; ring
  have hkey : α * (1 - (229 / 100) / U) ≤ ((j : ℝ) / 4) * Real.log 2 := by
    by_cases hcase : U ≤ 229 / 100
    · have h1 : 1 ≤ (229 / 100) / U := (one_le_div hUpos).mpr hcase
      have h2 : 1 - (229 / 100) / U ≤ 0 := by linarith
      have h3 : α * (1 - (229 / 100) / U) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hα0.le h2
      have h4 : 0 ≤ ((j : ℝ) / 4) * Real.log 2 := by positivity
      linarith
    · push_neg at hcase
      have hspos : (0 : ℝ) < 229 / 100 := by norm_num
      have h1 : 1 - (229 / 100) / U = (U - 229 / 100) / U := by
        rw [sub_div, div_self (ne_of_gt hUpos)]
      have h2 : (U - 229 / 100) / U ≤ (U - 229 / 100) / (229 / 100) := by
        rw [div_le_div_iff₀ hUpos hspos]
        nlinarith [sq_nonneg (U - 229 / 100)]
      have h3 : 1 - (229 / 100) / U ≤ (U - 229 / 100) / (229 / 100) := h1.le.trans h2
      have h4 : 0 ≤ 1 - (229 / 100) / U := by
        have h5 : (229 / 100) / U ≤ 1 := (div_le_one hUpos).mpr hcase.le
        linarith
      have h5 : 0 ≤ 𝓛 / 2 := by linarith
      have h6 : α * (1 - (229 / 100) / U) ≤ (𝓛 / 2) * ((U - 229 / 100) / (229 / 100)) :=
        mul_le_mul hα h3 h4 h5
      refine h6.trans ?_
      have hident : (𝓛 / 2) * ((U - 229 / 100) / (229 / 100))
          = (-(18 : ℝ) * 𝓛 + 220 * X) / 916 := by
        rw [hUdef]
        field_simp
        ring
      rw [hident]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 916)]
      have h916 : (((j : ℝ) / 4) * Real.log 2) * 916 = 229 * (j : ℝ) * Real.log 2 := by
        ring
      rw [h916]
      have hL9 : Real.log 9 ≤ 8 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
        linarith
      have hL2u : Real.log 2 ≤ 0.7 := by
        have h := Real.log_two_lt_d9
        linarith
      have hL2l : (0.69 : ℝ) ≤ Real.log 2 := by
        have h := Real.log_two_gt_d9
        linarith
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith [h𝓛, hXexp, hL9, hL2u, hL2l, hj]
  have hLHS : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j * (Real.exp (-α)) ^ ((229 / 100) / U)
      = Real.exp (-((j : ℝ) / 2 * Real.log 2 + α * ((229 / 100) / U))) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (Real.exp_pos (-α)), Real.log_exp]
    conv_lhs => rw [← Real.exp_add]
    congr 1
    push_cast
    ring_nf
  have hRHS : Real.exp (-α) * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j
      = Real.exp (-α) * Real.exp (-((j : ℝ) / 4 * Real.log 2)) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 4) : ℝ)) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring_nf
  have hfac : Real.exp (-α) * Real.exp (-((j : ℝ) / 2 * Real.log 2 + α * ((229 / 100) / U)) + α)
      = Real.exp (-((j : ℝ) / 2 * Real.log 2 + α * ((229 / 100) / U))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hLHS, hRHS, ← hfac]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rw [Real.exp_le_exp]
  linarith [hkey]
theorem highMassRep261 {q : ℕ} [NeZero q] (hq : 1 < q) (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ)
    {C₂ C₀ : ℝ} (hC₂ : 0 < C₂) (hC₀ : 0 < C₀) (q₀f : ℕ) (hqf : q₀f ≤ q)
    (hfam : ∀ (σ T : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ T →
      Work.ZeroDensity.famCount q σ T
        ≤ C₂ * Real.exp (((261 : ℝ) / 100) * ((1 - σ) * Real.log (q : ℝ))) * T ^ (3 / 2 : ℝ))
    (hrepq : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → lamOf q (β₁ : ℂ) ≤ lamOf q ρ →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (C₀ * ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ lamOf q ρ)
    (hlam1pos : 0 < lamOf q (β₁ : ℂ)) (hsmall : lamOf q (β₁ : ℂ) < 1 / (6 * C₀))
    (hlam1lt : lamOf q (β₁ : ℂ) < 1)
    (hαhalf : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (q : ℝ) / 2)
    (h𝓛big : 200 ≤ Real.log (q : ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hzm : ∀ z ∈ S, zeroMult z.1 z.2 ≠ 0) (hhigh : ∀ z ∈ S, 1 < |z.2.im|)
    (hexc : ∀ z ∈ S, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)))
    (hsep : ∀ z ∈ S, lamOf q z.2 < lamOf q (β₁ : ℂ) → 4 * (q : ℝ) ^ 2 ≤ |z.2.im|) :
    (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      ≤ 4 * (2 : ℝ) ^ (3 / 2 : ℝ) * C₂ * Real.exp (261 / 100) / (1 - Real.exp (-(229 / 100)))
        * (Real.exp ((229 / 100) * C₀) * (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹
            + (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹)
        * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
  classical
  have hlog : 0 < Real.log (q : ℝ) := lt_of_lt_of_le (by norm_num) h𝓛big
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_of_lt hq)
  set Ks : ℝ := 4 * (2 : ℝ) ^ (3 / 2 : ℝ) * C₂ * Real.exp (261 / 100) / (1 - Real.exp (-(229 / 100)))
    with hKsdef
  have hKspos : 0 < Ks := by
    rw [hKsdef]
    have h : Real.exp (-(229 / 100)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    positivity
  set lam1 : ℝ := lamOf q (β₁ : ℂ) with hlam1def
  have hlam1pos' : 0 < lam1 := hlam1pos
  have hlam1lt1 : lam1 < 1 := by rw [hlam1def]; exact hlam1lt
  set α : ℝ := Real.log (1 / lam1) with hαdef
  have hαpos : 0 < α := by
    rw [hαdef]
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hlam1pos']
    simpa using hlam1lt1
  have hexp_neg : Real.exp (-α) = lam1 := by
    rw [hαdef, Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]
  have hαle : α ≤ Real.log (q : ℝ) / 2 := by rw [hαdef, hlam1def]; exact hαhalf
  set J : ℕ := Nat.ceil (2 * Real.log (q : ℝ) / Real.log 2) with hJdef
  have hJlt : (J : ℝ) < 2 * Real.log (q : ℝ) / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hJge : 2 * Real.log (q : ℝ) / Real.log 2 ≤ (J : ℝ) := Nat.le_ceil _
  have h2J : (2 : ℝ) ^ (J + 1) ≤ 4 * (q : ℝ) ^ 2 := by
    have h7 : (J : ℝ) + 1 < 2 * Real.log (q : ℝ) / Real.log 2 + 2 := by linarith [hJlt]
    have h8 : (2 : ℝ) ^ (J + 1) ≤ (2 : ℝ) ^ (2 * Real.log (q : ℝ) / Real.log 2 + 2) := by
      rw [← Real.rpow_natCast (2 : ℝ) (J + 1)]
      push_cast
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h7.le
    calc (2 : ℝ) ^ (J + 1) ≤ (2 : ℝ) ^ (2 * Real.log (q : ℝ) / Real.log 2 + 2) := h8
      _ = (2 : ℝ) ^ (2 * Real.log (q : ℝ) / Real.log 2) * (2 : ℝ) ^ (2 : ℝ) := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ = (q : ℝ) ^ 2 * 4 := by
          congr 1
          · rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
            have h10 : Real.log 2 * (2 * Real.log (q : ℝ) / Real.log 2)
                = 2 * Real.log (q : ℝ) := by field_simp
            have h9 : Real.log ((q : ℝ) ^ 2) = 2 * Real.log (q : ℝ) := by
              rw [Real.log_pow]; ring
            rw [h10, ← h9]
            exact Real.exp_log (by positivity)
          · rw [Real.rpow_two]; norm_num
      _ = 4 * (q : ℝ) ^ 2 := by ring
  set U : ℕ → ℝ := fun j =>
    (11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ))
    with hUdef
  set Lf : ℕ → ℝ := fun j => (α - Real.log (C₀ * U j)) / U j with hLdef
  have hξnn : ∀ j, 0 ≤ Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ) := by
    intro j
    refine div_nonneg ?_ hlog.le
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by positivity
    linarith
  have hUpos : ∀ j, 0 < U j := by
    intro j; rw [hUdef]; have := hξnn j; nlinarith
  have hUge : ∀ j, (4 / 3 + 1 / 100 : ℝ) ≤ U j := by
    intro j; rw [hUdef]; have := hξnn j; nlinarith
  have hU6 : ∀ j, j ≤ J → U j ≤ 6 := by
    intro j hj
    have h2j : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (J + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hp : 5 + (2 : ℝ) ^ (j + 1) ≤ 20 * (q : ℝ) ^ 2 := by
      have h2 : 5 + 4 * (q : ℝ) ^ 2 ≤ 20 * (q : ℝ) ^ 2 := by nlinarith [hq1]
      linarith
    have hlogp : Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log 20 + 2 * Real.log (q : ℝ) := by
      calc Real.log (5 + (2 : ℝ) ^ (j + 1)) ≤ Real.log (20 * (q : ℝ) ^ 2) :=
            Real.log_le_log (by positivity) hp
        _ = Real.log 20 + 2 * Real.log (q : ℝ) := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            ring
    have hξ6 : Real.log (5 + (2 : ℝ) ^ (j + 1)) / Real.log (q : ℝ) ≤ 2.95 := by
      rw [div_le_iff₀ hlog]
      have h1 : Real.log 20 ≤ 19 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 20); linarith
      nlinarith [hlogp, h1, h𝓛big]
    rw [hUdef]
    nlinarith [hξ6]
  have hCU_J : ∀ j, j ≤ J → C₀ * U j < Real.exp α := by
    intro j hj
    have h1 : C₀ * U j ≤ 6 * C₀ := by nlinarith [hU6 j hj, hC₀]
    have h3 : Real.exp α = 1 / lam1 := by rw [hαdef, Real.exp_log (by positivity)]
    have h2 : 6 * C₀ < Real.exp α := by
      rw [h3, lt_div_iff₀ hlam1pos']
      have hs : lam1 < 1 / (6 * C₀) := by rw [hlam1def]; exact hsmall
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 6 * C₀)] at hs
      linarith [hs]
    linarith
  have hLpos : ∀ j, j ≤ J → 0 < Lf j := by
    intro j hj
    rw [hLdef]
    refine div_pos ?_ (hUpos j)
    rw [sub_pos]
    have h5 : Real.log (C₀ * U j) < Real.log (Real.exp α) :=
      Real.log_lt_log (mul_pos hC₀ (hUpos j)) (hCU_J j hj)
    rwa [Real.log_exp] at h5
  have hfloorpos_J : ∀ j, j ≤ J → C₀ * U j ≤ 1 / lam1 := by
    intro j hj
    have h3 : Real.exp α = 1 / lam1 := by rw [hαdef, Real.exp_log (by positivity)]
    rw [← h3]; linarith [hCU_J j hj]
  have hcnt : ∀ (H : ℝ), 1 ≤ H → ∀ t : ℝ, 0 < t → t ≤ Real.log (q : ℝ) →
      Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ C₂ * Real.exp ((261 / 100) * t) * H ^ (3 / 2 : ℝ) := by
    intro H hH t ht htL
    have hσ1 : 0 ≤ 1 - t / Real.log (q : ℝ) := by
      have h1 : t / Real.log (q : ℝ) ≤ 1 := (div_le_one hlog).mpr htL
      linarith
    have hσ2 : 1 - t / Real.log (q : ℝ) ≤ 1 := by
      have h1 : 0 ≤ t / Real.log (q : ℝ) := div_nonneg ht.le hlog.le
      linarith
    calc Siegel.pairCountHeight χ₁ β₁ t (H * Real.log (q : ℝ))
        ≤ Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ))
            ((H * Real.log (q : ℝ)) / Real.log (q : ℝ)) :=
          pairCountHeight_le_famCount hq χ₁ β₁
      _ = Work.ZeroDensity.famCount q (1 - t / Real.log (q : ℝ)) H := by
          rw [mul_div_cancel_right₀ _ (ne_of_gt hlog)]
      _ ≤ C₂ * Real.exp ((261 / 100) * ((1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ)))
            * H ^ (3 / 2 : ℝ) := hfam _ _ hσ1 hσ2 hH
      _ = C₂ * Real.exp ((261 / 100) * t) * H ^ (3 / 2 : ℝ) := by
          rw [show (1 - (1 - t / Real.log (q : ℝ))) * Real.log (q : ℝ) = t by
            field_simp; ring]
  have him_lt_of : ∀ (j : ℕ) (z : DirichletCharacter ℂ q × ℂ), jjC z = j →
      |z.2.im| < (2 : ℝ) ^ (j + 1) := by
    intro j z hjj
    have h1 : Nat.floor |z.2.im| < 2 ^ (Nat.log 2 (Nat.floor |z.2.im|) + 1) :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
    rw [show Nat.log 2 (Nat.floor |z.2.im|) = j from hjj] at h1
    have h2 : (Nat.floor |z.2.im| : ℝ) + 1 ≤ (2 : ℝ) ^ (j + 1) := by exact_mod_cast h1
    have h3 : |z.2.im| < (Nat.floor |z.2.im| : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  set Gs : ℕ → ℝ := fun j => ∑ z ∈ S.filter (fun z => jjC z = j),
      (zeroMult z.1 z.2 : ℝ) * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ with hGs
  have hfib_le : ∀ (j : ℕ), j ∈ S.image jjC → j ≤ J →
      Gs j ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
          * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (261 / 100)
              * Real.exp (-(229 / 100) * Lf j) / (1 - Real.exp (-(229 / 100)))) := by
    intro j hjT hjJ
    show (∑ z ∈ S.filter (fun z => jjC z = j), (zeroMult z.1 z.2 : ℝ)
          * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖) ≤ _
    set F := S.filter (fun z => jjC z = j) with hFdef
    have hzmF : ∀ z ∈ F, zeroMult z.1 z.2 ≠ 0 := fun z hz => hzm z (Finset.mem_filter.mp hz).1
    have hhighF : ∀ z ∈ F, 1 < |z.2.im| := fun z hz => hhigh z (Finset.mem_filter.mp hz).1
    have hexcF : ∀ z ∈ F, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)) :=
      fun z hz => hexc z (Finset.mem_filter.mp hz).1
    have him_le : ∀ z ∈ F, |z.2.im| ≤ (2 : ℝ) ^ (j + 1) :=
      fun z hz => (him_lt_of j z (Finset.mem_filter.mp hz).2).le
    have himF : ∀ z ∈ F, |z.2.im| * Real.log (q : ℝ)
        ≤ ((2 : ℝ) ^ (j + 1)) * Real.log (q : ℝ) :=
      fun z hz => mul_le_mul_of_nonneg_right (him_le z hz) hlog.le
    have hfloorF : ∀ z ∈ F, Lf j ≤ lamOf q z.2 := by
      intro z hz
      have hge : lamOf q (β₁ : ℂ) ≤ lamOf q z.2 := by
        by_contra hcon
        push Not at hcon
        have hs := hsep z (Finset.mem_filter.mp hz).1 hcon
        have h2j : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ (J + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hzlt : |z.2.im| < (2 : ℝ) ^ (J + 1) :=
          lt_of_lt_of_le (him_lt_of j z (Finset.mem_filter.mp hz).2) h2j
        linarith [h2J]
      have hrep_apply := repulsionFloorHiC (u := 11 / 5) (v := 11 / 10)
        (H := (2 : ℝ) ^ (j + 1)) χ₁ β₁ (C₀ := C₀) hC₀ (by norm_num) (by norm_num)
        (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
        (by have := hξnn j; nlinarith)
        (hrep := hrepq)
        (hfloor0 := by have h := hfloorpos_J j hjJ; rw [hUdef] at h; exact h)
        hq (hzmF z hz) (him_le z hz) (hexcF z hz) (hge)
      rw [hLdef, hUdef]
      exact hrep_apply
    have hmass := windowMassFloorGenAux hq χ₁ β₁ (by norm_num) (by norm_num) hC₂ (by positivity)
      (hLpos j hjJ)
      (hcnt ((2 : ℝ) ^ (j + 1)) (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
      F hzmF hexcF himF hfloorF
    rw [show (261 : ℝ) / 100 - 49 / 10 = -(229 / 100) by norm_num] at hmass
    have hstep1 : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
          * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
        ≤ ∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2)
            * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) :=
      Finset.sum_le_sum (fun z hz => kernel_leC hq z (hzmF z hz) (hhighF z hz))
    have hstep2 : (∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2)
            * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)))
        = 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
            * (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [(Finset.mem_filter.mp hz).2]
    calc (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
          * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
        ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
            * (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) :=
          le_trans hstep1 hstep2.le
      _ ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
            * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (261 / 100)
                * Real.exp (-(229 / 100) * Lf j) / (1 - Real.exp (-(229 / 100)))) := by
          refine mul_le_mul_of_nonneg_left hmass ?_
          positivity
  have hrpow : ((Real.log (q : ℝ)) ^ 2)⁻¹ = (Real.log (q : ℝ)) ^ (-2 : ℝ) := by
    rw [show (Real.log (q : ℝ)) ^ 2 = (Real.log (q : ℝ)) ^ ((2 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    rw [← Real.rpow_neg hlog.le]
    norm_num
  have hAlg : ∀ (j : ℕ) (Y : ℝ),
      4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
          * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (261 / 100) * Y
              / (1 - Real.exp (-(229 / 100))))
        = Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ) * (((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j * Y) := by
    intro j Y
    have e1 : 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
        = 4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * ((4 : ℝ) ^ j)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv_rev, hrpow]
      ring
    have e2 : (4 * (Real.log (q : ℝ)) ^ (-2 : ℝ) * ((4 : ℝ) ^ j)⁻¹)
          * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (261 / 100) * Y
              / (1 - Real.exp (-(229 / 100))))
        = (4 * C₂ * Real.exp (261 / 100) / (1 - Real.exp (-(229 / 100)))
            * (Real.log (q : ℝ)) ^ (-2 : ℝ))
          * ((((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * ((4 : ℝ) ^ j)⁻¹) * Y) := by
      ring
    rw [e1, e2, hKsdef, dyadic_key_freeC j]
    ring
  have hgs_pt : ∀ (j : ℕ), j ∈ S.image jjC → j ≤ J →
      Gs j ≤ Ks * Real.exp ((229 / 100) * C₀) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
              * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j := by
    intro j hjT hjJ
    have h1 := hfib_le j hjT hjJ
    rw [hAlg j (Real.exp (-(229 / 100) * Lf j))] at h1
    have hYexp : Real.exp (-(229 / 100) * Lf j)
        ≤ Real.exp ((229 / 100) * C₀) * (Real.exp (-α)) ^ ((229 / 100) / (U j)) := by
      have h := algPowCS (s := 229 / 100) (C₀ := C₀) (u := U j) (A := α)
        (by norm_num) hC₀ (hUpos j)
      rw [hLdef]; exact h
    have hY : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j * (Real.exp (-α)) ^ ((229 / 100) / (U j))
        ≤ Real.exp (-α) * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j := by
      simpa [hUdef] using layerGap2S (𝓛 := Real.log (q : ℝ)) h𝓛big hαpos hαle j
    have hstep : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j * Real.exp (-(229 / 100) * Lf j)
        ≤ Real.exp ((229 / 100) * C₀) * (Real.exp (-α)
            * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j) := by
      calc ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j * Real.exp (-(229 / 100) * Lf j)
          ≤ ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j
              * (Real.exp ((229 / 100) * C₀) * (Real.exp (-α)) ^ ((229 / 100) / (U j))) :=
            mul_le_mul_of_nonneg_left hYexp (by positivity)
        _ = Real.exp ((229 / 100) * C₀)
              * (((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j * (Real.exp (-α)) ^ ((229 / 100) / (U j))) := by
            ring
        _ ≤ Real.exp ((229 / 100) * C₀)
              * (Real.exp (-α) * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j) :=
            mul_le_mul_of_nonneg_left hY (by positivity)
    have h1' : Gs j ≤ Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ)
        * (Real.exp ((229 / 100) * C₀) * (Real.exp (-α)
            * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j)) := by
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left hstep ?_
      positivity
    refine h1'.trans (le_of_eq ?_)
    rw [hexp_neg]
    ring
  have hrm : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hrm0 : 0 ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hG_tail : ∀ (M : ℕ) (Y : Finset ℕ), (∀ j ∈ Y, M < j) →
      (∑ j ∈ Y, ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j)
        ≤ ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (M + 1) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ)) := by
    intro M Y hY
    have hsub : Y ⊆ Finset.Ico (M + 1) (Y.sup id + 1) := by
      intro j hj
      refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
      · have := hY j hj; omega
      · exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
    exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity))
      (geom_sum_Ico_le_of_lt_one hrm0 hrm)
  have hJtail : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ J ≤ lam1 := by
    have h1 : α ≤ ((J : ℝ) / 2) * Real.log 2 := by
      have h2 : 2 * Real.log (q : ℝ) / Real.log 2 * Real.log 2 = 2 * Real.log (q : ℝ) := by
        field_simp
      nlinarith [hJge, hlog2pos, hαle, hlog]
    have h4 : (2 : ℝ) ^ ((-(1 / 2) : ℝ) * (J : ℝ)) ≤ Real.exp (-α) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
      nlinarith [hlog2pos, h1]
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) J,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← hexp_neg]
    exact h4
  have hA : (∑ j ∈ (S.image jjC).filter (fun j => j ≤ J), Gs j)
      ≤ Ks * Real.exp ((229 / 100) * C₀)
          * (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹
          * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by
    have hper : ∀ j ∈ (S.image jjC).filter (fun j => j ≤ J),
        Gs j ≤ Ks * Real.exp ((229 / 100) * C₀) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
                * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j :=
      fun j hj => hgs_pt j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
    calc (∑ j ∈ (S.image jjC).filter (fun j => j ≤ J), Gs j)
        ≤ ∑ j ∈ (S.image jjC).filter (fun j => j ≤ J),
            Ks * Real.exp ((229 / 100) * C₀) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
              * ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j :=
          Finset.sum_le_sum hper
      _ = Ks * Real.exp ((229 / 100) * C₀) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
            * (∑ j ∈ (S.image jjC).filter (fun j => j ≤ J), ((2 : ℝ) ^ (-(1 / 4) : ℝ)) ^ j) := by
          rw [Finset.mul_sum]
      _ ≤ Ks * Real.exp ((229 / 100) * C₀) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1
            * (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹ := by
          refine mul_le_mul_of_nonneg_left (geom_le_quarter _) ?_
          have h1 : 0 < (Real.log (q : ℝ)) ^ (-2 : ℝ) := Real.rpow_pos_of_pos hlog _
          positivity
      _ = Ks * Real.exp ((229 / 100) * C₀)
            * (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹
            * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by ring
  have hB : (∑ j ∈ (S.image jjC).filter (fun j => ¬ j ≤ J), Gs j)
      ≤ Ks * (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by
    have hper : ∀ j ∈ (S.image jjC).filter (fun j => ¬ j ≤ J),
        Gs j ≤ Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j := by
      intro j hj
      have hjT : j ∈ S.image jjC := (Finset.mem_filter.mp hj).1
      set F := S.filter (fun z => jjC z = j) with hFdef
      have hzmF : ∀ z ∈ F, zeroMult z.1 z.2 ≠ 0 := fun z hz => hzm z (Finset.mem_filter.mp hz).1
      have hhighF : ∀ z ∈ F, 1 < |z.2.im| := fun z hz => hhigh z (Finset.mem_filter.mp hz).1
      have hexcF : ∀ z ∈ F, ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ)) :=
        fun z hz => hexc z (Finset.mem_filter.mp hz).1
      have him_le : ∀ z ∈ F, |z.2.im| ≤ (2 : ℝ) ^ (j + 1) :=
        fun z hz => (him_lt_of j z (Finset.mem_filter.mp hz).2).le
      have himF : ∀ z ∈ F, |z.2.im| * Real.log (q : ℝ)
          ≤ ((2 : ℝ) ^ (j + 1)) * Real.log (q : ℝ) :=
        fun z hz => mul_le_mul_of_nonneg_right (him_le z hz) hlog.le
      have hmass := windowMassFreeGenAux hq χ₁ β₁ (by norm_num) (by norm_num) hC₂ (by positivity)
        (hcnt ((2 : ℝ) ^ (j + 1)) (by exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
        F hzmF hexcF himF
      have hmass' : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2))
          ≤ C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (261 / 100) * 1
              / (1 - Real.exp (-(229 / 100))) := by
        rw [show (261 : ℝ) / 100 - 49 / 10 = -(229 / 100) by norm_num] at hmass
        simpa using hmass
      have hstep1 : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ ∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2)
              * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) :=
        Finset.sum_le_sum (fun z hz => kernel_leC hq z (hzmF z hz) (hhighF z hz))
      have hstep2 : (∑ z ∈ F, 4 / ((4 : ℝ) ^ (jjC z) * (Real.log (q : ℝ)) ^ 2)
              * ((zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)))
          = 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ) * Real.exp (-(49 / 10) * lamOf q z.2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun z hz => ?_)
        rw [(Finset.mem_filter.mp hz).2]
      have hfinal : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j := by
        have hmid : (∑ z ∈ F, (zeroMult z.1 z.2 : ℝ)
              * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
            ≤ 4 / ((4 : ℝ) ^ j * (Real.log (q : ℝ)) ^ 2)
              * (C₂ * ((2 : ℝ) ^ (j + 1)) ^ (3 / 2 : ℝ) * Real.exp (261 / 100) * 1
                  / (1 - Real.exp (-(229 / 100)))) := by
          refine (le_trans hstep1 hstep2.le).trans ?_
          exact mul_le_mul_of_nonneg_left hmass' (by positivity)
        exact hmid.trans (le_of_eq (by rw [hAlg j 1]; ring))
      show Gs j ≤ _
      rw [hGs]
      exact hfinal
    calc (∑ j ∈ (S.image jjC).filter (fun j => ¬ j ≤ J), Gs j)
        ≤ ∑ j ∈ (S.image jjC).filter (fun j => ¬ j ≤ J),
            Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ) * ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j :=
          Finset.sum_le_sum hper
      _ = Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ)
            * (∑ j ∈ (S.image jjC).filter (fun j => ¬ j ≤ J), ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ j) := by
          rw [Finset.mul_sum]
      _ ≤ Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ)
            * (((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (J + 1) / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · refine hG_tail J _ ?_
            intro j hj
            have := (Finset.mem_filter.mp hj).2
            omega
          · positivity
      _ ≤ Ks * (Real.log (q : ℝ)) ^ (-2 : ℝ)
            * (lam1 / (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))) := by
          refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right ?_ ?_) ?_
          · rw [pow_succ]
            calc ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ J * (2 : ℝ) ^ (-(1 / 2) : ℝ)
                ≤ lam1 * 1 := mul_le_mul hJtail hrm.le (by positivity) hlam1pos'.le
              _ = lam1 := by ring
          · have h : (2 : ℝ) ^ (-(1 / 2) : ℝ) < 1 := hrm
            linarith
          · have h1 : 0 < (Real.log (q : ℝ)) ^ (-2 : ℝ) := Real.rpow_pos_of_pos hlog _
            positivity
      _ = Ks * (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lam1 := by
          ring
  have hGeq : (∑ z ∈ S, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
      = ∑ j ∈ S.image jjC, Gs j := by
    rw [hGs]
    exact (Finset.sum_fiberwise_of_maps_to (fun z hz => Finset.mem_image_of_mem jjC hz)
      (fun z => (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)).symm
  rw [hGeq]
  have hsplit : (∑ j ∈ S.image jjC, Gs j)
      = (∑ j ∈ (S.image jjC).filter (fun j => j ≤ J), Gs j)
        + (∑ j ∈ (S.image jjC).filter (fun j => ¬ j ≤ J), Gs j) := by
    rw [Finset.sum_filter_add_sum_filter_not (S.image jjC) (fun j => j ≤ J) Gs]
  rw [hsplit]
  refine le_trans (add_le_add hA hB) (le_of_eq ?_)
  rw [hKsdef]
  ring

theorem RestHighBGTZGenCGen (cZ C₀ : ℝ) (hcZ : 0 < cZ) (hC₀ : 0 < C₀)
    (hrep : Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) C₀)
    (hfam : Work.ZeroDensity.LogFreeFamHeight ((261 : ℝ) / 100) (3 / 2))
    (hzfr : Work.LinnikAreas.BGTZ.ZFRInput cZ) :
    Work.LinnikAreas.Siegel.RestHighBGTZSpec (-3 / 2) := by
  obtain ⟨Kf, hKfpos, q₀f, hKf⟩ :=
    highFinsetBoundFreeGenAux (by norm_num : (261 : ℝ) / 100 < 49 / 10) hfam
  obtain ⟨C₂, hC₂, q₀fam, hfam'⟩ := hfam
  obtain ⟨Cₛ, hCₛpos, hCₛ⟩ := lamOfEps200
  obtain ⟨Csi, hCsipos, hCsi⟩ := Siegel.lamOf_lower_bound
  obtain ⟨q₀rep, hrepall⟩ := hrep
  obtain ⟨q₀zfr, hzfrall⟩ := hzfr
  set σ : ℝ := min (1 / 10) (min (cZ / 4) (1 / (6 * C₀))) with hσdef
  have hσpos : 0 < σ := by
    rw [hσdef]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hσ10 : σ ≤ 1 / 10 := by rw [hσdef]; exact min_le_left _ _
  have hσcZ : σ ≤ cZ / 4 := by
    rw [hσdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hσC₀ : σ ≤ 1 / (6 * C₀) := by
    rw [hσdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  set K₂ : ℝ := 4 * (2 : ℝ) ^ (3 / 2 : ℝ) * C₂ * Real.exp (261 / 100) / (1 - Real.exp (-(229 / 100)))
      * (Real.exp ((229 / 100) * C₀) * (1 - (2 : ℝ) ^ (-(1 / 4) : ℝ))⁻¹
          + (1 - (2 : ℝ) ^ (-(1 / 2) : ℝ))⁻¹) with hK₂def
  set R : ℝ := 200 + 1 / Csi + 1 / Real.sqrt Cₛ with hRdef
  refine ⟨max (Kf / σ) K₂, lt_max_of_lt_left (div_pos hKfpos hσpos),
    max q₀f (max (max q₀rep q₀fam) (max q₀zfr (Nat.ceil (Real.exp R)))), ?_⟩
  intro q hq hNq χ₁ β₁ hχ hsq hβ hz hlam10
  have hq₀f : q₀f ≤ q := le_trans (le_max_left _ _) hq
  have hqrest : (max (max q₀rep q₀fam) (max q₀zfr (Nat.ceil (Real.exp R)))) ≤ q :=
    le_trans (le_max_right _ _) hq
  have hq₀rep : q₀rep ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hqrest
  have hq₀fam : q₀fam ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hqrest
  have hqz : (max q₀zfr (Nat.ceil (Real.exp R))) ≤ q := le_trans (le_max_right _ _) hqrest
  have hq₀zfr : q₀zfr ≤ q := le_trans (le_max_left _ _) hqz
  have hqR : Nat.ceil (Real.exp R) ≤ q := le_trans (le_max_right _ _) hqz
  have hq2 : 1 < q := by
    have h1 : 2 ≤ Nat.ceil (Real.exp R) := by
      have h2 : (2 : ℝ) ≤ Real.exp R := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        refine Real.exp_le_exp.mpr ?_
        have h5 : Real.log 2 ≤ 20 := by
          have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          linarith
        rw [hRdef]
        have h3 : 0 < 1 / Real.sqrt Cₛ := by positivity
        have h4 : 0 ≤ 1 / Csi := by positivity
        linarith
      have h3 : (2 : ℝ) ≤ (Nat.ceil (Real.exp R) : ℝ) := le_trans h2 (Nat.le_ceil _)
      exact_mod_cast h3
    have h4 : Nat.ceil (Real.exp R) ≤ q := hqR
    omega
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq2)
  have h𝓛R : R ≤ Real.log (q : ℝ) := by
    have h1 : Real.exp R ≤ (q : ℝ) := by
      have h2 : Real.exp R ≤ (Nat.ceil (Real.exp R) : ℝ) := Nat.le_ceil _
      exact le_trans h2 (by exact_mod_cast hqR)
    have h3 : Real.log (Real.exp R) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_exp] at h3
  have h𝓛big : 200 ≤ Real.log (q : ℝ) := by
    have h1 : 200 ≤ R := by
      rw [hRdef]
      have h2 : 0 < 1 / Real.sqrt Cₛ := by positivity
      have h3 : 0 ≤ 1 / Csi := by positivity
      linarith
    linarith
  have hq16 : 16 ≤ q := by
    have h1 : (16 : ℝ) < (q : ℝ) := by
      have h2 : (16 : ℝ) < Real.exp (200 : ℝ) := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 16)]
        refine Real.exp_lt_exp.mpr ?_
        have h6 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16)
        linarith
      have h3 : Real.exp (200 : ℝ) ≤ (q : ℝ) := by
        have h4 : Real.exp (200 : ℝ) ≤ Real.exp (Real.log (q : ℝ)) := Real.exp_le_exp.mpr h𝓛big
        rwa [Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))] at h4
      linarith
    exact_mod_cast h1.le
  have hCsilog : (1 : ℝ) ≤ Csi * Real.log (q : ℝ) := by
    have h1 : 1 / Csi ≤ Real.log (q : ℝ) := by
      have h2 : 1 / Csi ≤ R := by
        rw [hRdef]
        have h3 : 0 < 1 / Real.sqrt Cₛ := by positivity
        linarith
      linarith
    rw [div_le_iff₀ hCsipos] at h1
    linarith [h1]
  have hCsL2 : (1 : ℝ) ≤ Cₛ * Real.log (q : ℝ) ^ 2 := by
    have h1 : 1 / Real.sqrt Cₛ ≤ Real.log (q : ℝ) := by
      have h2 : 1 / Real.sqrt Cₛ ≤ R := by
        rw [hRdef]
        have h3 : 0 ≤ 1 / Csi := by positivity
        linarith
      linarith
    have h3 : Real.sqrt Cₛ * (1 / Real.sqrt Cₛ) = 1 := by
      field_simp [ne_of_gt (Real.sqrt_pos.mpr hCₛpos)]
    have h4 : (1 : ℝ) ≤ Real.sqrt Cₛ * Real.log (q : ℝ) := by
      nlinarith [h1, hCₛpos, h3, Real.sqrt_pos.mpr hCₛpos]
    nlinarith [h4, Real.sq_sqrt hCₛpos.le, sq_nonneg (Real.log (q : ℝ))]
  have hlampos : 0 < lamOf q (β₁ : ℂ) := Siegel.lamOf_pos hχ hβ hz
  have hCsi_app : Csi * Real.log (q : ℝ) / Real.sqrt (q : ℝ) ≤ lamOf q (β₁ : ℂ) :=
    hCsi q (by omega) χ₁ β₁ hχ hsq hβ hz
  have hCₛ_app : Cₛ * Real.log (q : ℝ) / (q : ℝ) ^ (1 / 200 : ℝ) ≤ lamOf q (β₁ : ℂ) :=
    hCₛ q (by omega) χ₁ β₁ hχ hsq hβ hz
  have hαhalf : Real.log (1 / lamOf q (β₁ : ℂ)) ≤ Real.log (q : ℝ) / 2 := by
    have h3 : 1 / lamOf q (β₁ : ℂ) ≤ Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ)) := by
      rw [div_le_div_iff₀ hlampos (mul_pos hCsipos hlog)]
      have h4 : Csi * Real.log (q : ℝ) ≤ lamOf q (β₁ : ℂ) * Real.sqrt (q : ℝ) := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)))] at hCsi_app
        linarith [hCsi_app]
      linarith [h4]
    calc Real.log (1 / lamOf q (β₁ : ℂ))
        ≤ Real.log (Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ))) :=
          Real.log_le_log (by positivity) h3
      _ = Real.log (q : ℝ) / 2 - Real.log (Csi * Real.log (q : ℝ)) := by
          have h1 : Real.log (Real.sqrt (q : ℝ) / (Csi * Real.log (q : ℝ)))
              = Real.log (Real.sqrt (q : ℝ)) - Real.log (Csi * Real.log (q : ℝ)) :=
            Real.log_div (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q))))
              (ne_of_gt (mul_pos hCsipos hlog))
          have h2 : Real.log (Real.sqrt (q : ℝ)) = Real.log (q : ℝ) / 2 :=
            Real.log_sqrt (by positivity)
          rw [h1, h2]
      _ ≤ Real.log (q : ℝ) / 2 := by
          have h5 : 0 ≤ Real.log (Csi * Real.log (q : ℝ)) := Real.log_nonneg hCsilog
          linarith
  have hhy : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) < lamOf q (β₁ : ℂ) := by
    have h1 : 1 / ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))
        < Cₛ * Real.log (q : ℝ) / (q : ℝ) ^ (1 / 200 : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ))
        (by positivity : (0 : ℝ) < (q : ℝ) ^ (1 / 200 : ℝ))]
      have h2 : (q : ℝ) ^ (1 / 200 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hq2) (by norm_num)
      have h3 : (q : ℝ) ^ (1 / 100 : ℝ)
          ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Cₛ * Real.log (q : ℝ) ^ 2) :=
        le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _) hCsL2
      calc (1 : ℝ) * (q : ℝ) ^ (1 / 200 : ℝ) < (q : ℝ) ^ (1 / 100 : ℝ) := by simpa using h2
        _ ≤ (q : ℝ) ^ (1 / 100 : ℝ) * (Cₛ * Real.log (q : ℝ) ^ 2) := h3
        _ = (Cₛ * Real.log (q : ℝ)) * ((q : ℝ) ^ (1 / 100 : ℝ) * Real.log (q : ℝ)) := by ring
    linarith [hCₛ_app]
  have hrepq : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) → lamOf q (β₁ : ℂ) ≤ lamOf q ρ →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (C₀ * ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((11 / 5 : ℝ) + (11 / 10 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ lamOf q ρ :=
    fun χ ρ hzm' hne hle => hrepall q hq₀rep χ₁ β₁ hχ hsq hβ hz hhy hlam10 χ ρ hzm' hne hle
  let p : DirichletCharacter ℂ q × ℂ → Prop := fun z =>
    zeroMult z.1 z.2 ≠ 0 ∧ 1 < |z.2.im| ∧ ¬(z.1 = χ₁ ∧ z.2 = (β₁ : ℂ))
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if p z then (zeroMult z.1 z.2 : ℝ)
      * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ else 0
  have hFnn : 0 ≤ F := fun z => by
    simp only [F]
    split_ifs with hp
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    · exact le_refl 0
  have hbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ),
      ∑ z ∈ u, F z ≤ max (Kf / σ) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
    intro u
    have hsum_eq : ∑ z ∈ u, F z = ∑ z ∈ u.filter p, F z := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro z hz hnotin
      have hp : ¬ p z := fun hpp => hnotin (Finset.mem_filter.mpr ⟨hz, hpp⟩)
      simp only [F]; rw [if_neg hp]
    have hSF : ∑ z ∈ u.filter p, F z = ∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
        * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖ := by
      refine Finset.sum_congr rfl (fun z hz => ?_)
      have hp : p z := (Finset.mem_filter.mp hz).2
      simp only [F]; rw [if_pos hp]
    rw [hsum_eq, hSF]
    by_cases hbig : σ ≤ lamOf q (β₁ : ℂ)
    · have h1 : (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) :=
        hKf hq₀f hq2 χ₁ β₁ (u.filter p)
          (fun z hz => (Finset.mem_filter.mp hz).2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
          (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
      have hσinv : (1 : ℝ) ≤ (1 / σ) * lamOf q (β₁ : ℂ) := by
        rw [div_mul_eq_mul_div, one_mul]
        exact (le_div_iff₀ hσpos).mpr (by linarith [hbig])
      have h1' : 0 ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) :=
        mul_nonneg hKfpos.le (Real.rpow_nonneg hlog.le _)
      calc (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) := h1
        _ ≤ Kf * (Real.log (q : ℝ)) ^ (-2 : ℝ) * ((1 / σ) * lamOf q (β₁ : ℂ)) :=
            le_mul_of_one_le_right h1' hσinv
        _ = (Kf / σ) * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by ring
        _ ≤ max (Kf / σ) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlampos.le
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hlog.le _)
    · have hsmallσ : lamOf q (β₁ : ℂ) < σ := not_le.mp hbig
      have hsep : ∀ z ∈ u.filter p, lamOf q z.2 < lamOf q (β₁ : ℂ) → 4 * (q : ℝ) ^ 2 ≤ |z.2.im| := by
        intro z hzmem hlt
        exact height_sep_of_ZFR (q := q) (cZ := cZ) hq16 (hzfrall q hq₀zfr) hχ hsq hβ hz
          (lt_of_lt_of_le hsmallσ hσ10) (lt_of_lt_of_le hsmallσ hσcZ)
          (Finset.mem_filter.mp hzmem).2.1 hlt
      have h3 := highMassRep261 hq2 χ₁ β₁ hC₂ hC₀ q₀fam hq₀fam (hfam' q hq₀fam) hrepq hlampos
        (lt_of_lt_of_le hsmallσ hσC₀) (lt_of_le_of_lt hlam10 (by norm_num)) hαhalf h𝓛big
        (u.filter p)
        (fun z hz => (Finset.mem_filter.mp hz).2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.1)
        (fun z hz => (Finset.mem_filter.mp hz).2.2.2)
        hsep
      rw [← hK₂def] at h3
      calc (∑ z ∈ u.filter p, (zeroMult z.1 z.2 : ℝ)
            * ‖Hk (11 / 2) (3 / 10) ((1 - z.2) * (Real.log q : ℂ))‖)
          ≤ K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := h3
        _ ≤ max (Kf / σ) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := by
            refine mul_le_mul_of_nonneg_right ?_ hlampos.le
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hlog.le _)
  have hsumm : Summable F := summable_of_sum_le hFnn hbound
  have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z
      ≤ max (Kf / σ) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) :=
    Real.tsum_le_of_sum_le hFnn hbound
  rw [Summable.tsum_prod hsumm] at htsum
  rw [tsum_fintype] at htsum
  have hEq : Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
      = ∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ) := rfl
  rw [hEq]
  have hpow : (Real.log (q : ℝ)) ^ (-2 : ℝ)
      = (Real.log (q : ℝ)) ^ (-(1 / 2) : ℝ) * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hlog]
    norm_num
  have hhalf : (Real.log (q : ℝ)) ^ (-(1 / 2) : ℝ) ≤ 1 := by
    rw [Real.rpow_neg hlog.le, inv_le_one₀ (Real.rpow_pos_of_pos hlog _)]
    have h1 : (1 : ℝ) ≤ Real.log (q : ℝ) := by linarith
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
      _ ≤ (Real.log (q : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  calc (∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ))
      ≤ max (Kf / σ) K₂ * (Real.log (q : ℝ)) ^ (-2 : ℝ) * lamOf q (β₁ : ℂ) := htsum
    _ = max (Kf / σ) K₂
          * ((Real.log (q : ℝ)) ^ (-(1 / 2) : ℝ) * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ))
          * lamOf q (β₁ : ℂ) := by rw [hpow]
    _ ≤ max (Kf / σ) K₂ * (1 * (Real.log (q : ℝ)) ^ (-(3 / 2) : ℝ)) * lamOf q (β₁ : ℂ) := by
        refine mul_le_mul_of_nonneg_right ?_ hlampos.le
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (lt_max_of_lt_left (by positivity)))
        exact mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hlog.le _)
    _ = max (Kf / σ) K₂ * lamOf q (β₁ : ℂ) * (Real.log (q : ℝ)) ^ (-3 / 2 : ℝ) := by
        rw [show (-(3 / 2) : ℝ) = -3 / 2 by norm_num]
        ring


end
end Work.LinnikAreas.BGTZ