import Mathlib
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.FatouCoord.Repelling.defect_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Decay of the bounded correction `Z` of the repelling coordinate

For a parabolic germ `f z = z + z ^ 2 h z` (`h 0 = 1`, `ParabolicBounds f h a r A A'`) the
repelling coordinate is built from the corrected ansatz `V w = w + (1 - a) Λ w + Z w` in the
chart `w = -1/z`, where `Z` is a *bounded* solution of the difference equation
`Z (w + 1) - Z w = defect f a w (Z w)` on a left half-plane `{Re w < -R}`; equivalently `Z` is a
fixed point of the operator `Omega f a`.

This file proves that such a `Z` (the statement only uses that `‖Z w‖ ≤ 1/2` and that `Z` is
*any* fixed point of `Omega` on `LeftHalfPlane R`) actually decays: the fixed-point equation
expresses `Z w` as the series `∑_n defect f a (w - n - 1) (Z (w - n - 1))` of defects, each of
which is `O((1 + log ‖w - n - 1‖)/‖w - n - 1‖²)`, and since `‖w - n - 1‖ ≥ 1 - w.re + n` this
gives

* a quantitative bound `‖Z w‖ ≤ K / √(1 - Re w)` on the half-plane, and
* uniform convergence `‖Z w‖ → 0` as `Re w → -∞`.
-/

namespace Work.FatouCoordFix.Repelling

open Work.FatouCoord Work.FatouCoord.Petal
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {R : ℝ} {Z : ℂ → ℂ}

/-! ## Elementary estimates -/

/-- The telescoping step for the majorant of the defect series: for `X ≥ 1`,
`1/((X+1)√(X+1)) ≤ 2(1/√X - 1/√(X+1))`.

Indeed, after clearing denominators this is
`(2X+3) √X ≤ 2(X+1) √(X+1)`, which follows by squaring:
`(2X+3)² X = 4X³ + 12X² + 9X ≤ 4X³ + 12X² + 12X + 4 = 4(X+1)³`. -/
private theorem inv_mul_sqrt_shift_le {X : ℝ} (hX : 1 ≤ X) :
    1 / ((X + 1) * Real.sqrt (X + 1)) ≤ 2 * (1 / Real.sqrt X - 1 / Real.sqrt (X + 1)) := by
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX
  have hY0 : 0 < X + 1 := by linarith
  have hsa : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hsb : 0 < Real.sqrt (X + 1) := Real.sqrt_pos.mpr hY0
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (X + 1) * Real.sqrt (X + 1))]
  have hkey : 2 * (1 / Real.sqrt X - 1 / Real.sqrt (X + 1)) * ((X + 1) * Real.sqrt (X + 1))
      = 2 * (X + 1) * Real.sqrt (X + 1) / Real.sqrt X - 2 * (X + 1) := by
    field_simp
  rw [hkey, le_sub_iff_add_le, le_div_iff₀ hsa]
  have hL : 0 ≤ (1 + 2 * (X + 1)) * Real.sqrt X := by positivity
  have hR : 0 ≤ 2 * (X + 1) * Real.sqrt (X + 1) := by positivity
  rw [mul_self_le_mul_self_iff hL hR]
  have e1 : ((1 + 2 * (X + 1)) * Real.sqrt X) * ((1 + 2 * (X + 1)) * Real.sqrt X)
      = (1 + 2 * (X + 1)) ^ 2 * X := by
    rw [← sq, mul_pow, Real.sq_sqrt hX0.le]
  have e2 : (2 * (X + 1) * Real.sqrt (X + 1)) * (2 * (X + 1) * Real.sqrt (X + 1))
      = (2 * (X + 1)) ^ 2 * (X + 1) := by
    rw [← sq, mul_pow, Real.sq_sqrt hY0.le]
  rw [e1, e2]
  nlinarith

/-- The summation estimate for the majorant of the defect series:
`∑_n 1/((N+n) √(N+n)) ≤ 3/√N` for `N ≥ 1`, together with its summability.
The terms are dominated by a telescoping difference of `1/√·`; the case `N = 1` fixes the
constant `3` (`1/(N√N) ≤ 1/√N` and `2/√N` for the telescoped tail). -/
private theorem inv_mul_sqrt_tsum_aux {N : ℝ} (hN : 1 ≤ N) :
    Summable (fun n : ℕ => (1 : ℝ) / ((N + (n : ℝ)) * Real.sqrt (N + (n : ℝ)))) ∧
      ∑' n : ℕ, (1 : ℝ) / ((N + (n : ℝ)) * Real.sqrt (N + (n : ℝ))) ≤ 3 / Real.sqrt N := by
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have hfnn : ∀ n : ℕ, 0 ≤ (1 : ℝ) / ((N + (n : ℝ)) * Real.sqrt (N + (n : ℝ))) := by
    intro n; positivity
  have hstep : ∀ i : ℕ,
      (1 : ℝ) / ((N + ((i + 1 : ℕ) : ℝ)) * Real.sqrt (N + ((i + 1 : ℕ) : ℝ)))
        ≤ 2 * ((1 / Real.sqrt (N + (i : ℝ))) - (1 / Real.sqrt (N + ((i + 1 : ℕ) : ℝ)))) := by
    intro i
    have hi : (1 : ℝ) ≤ N + (i : ℝ) := by
      have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      linarith
    have h := inv_mul_sqrt_shift_le (X := N + (i : ℝ)) hi
    push_cast
    simpa only [add_assoc] using h
  have hpartial : ∀ k : ℕ,
      ∑ i ∈ Finset.range k, (1 : ℝ) / ((N + (i : ℝ)) * Real.sqrt (N + (i : ℝ)))
        ≤ 3 / Real.sqrt N := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [Finset.range_zero, Finset.sum_empty]
      positivity
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rw [Finset.sum_range_succ', add_comm]
      have hsum1 : ∑ i ∈ Finset.range j,
            (1 : ℝ) / ((N + ((i + 1 : ℕ) : ℝ)) * Real.sqrt (N + ((i + 1 : ℕ) : ℝ)))
          ≤ ∑ i ∈ Finset.range j,
            2 * ((1 / Real.sqrt (N + (i : ℝ))) - (1 / Real.sqrt (N + ((i + 1 : ℕ) : ℝ)))) :=
        Finset.sum_le_sum (fun i _ => hstep i)
      have hsum2 : ∑ i ∈ Finset.range j,
            2 * ((1 / Real.sqrt (N + (i : ℝ))) - (1 / Real.sqrt (N + ((i + 1 : ℕ) : ℝ))))
          = 2 * (1 / Real.sqrt N - 1 / Real.sqrt (N + (j : ℝ))) := by
        rw [← Finset.mul_sum]
        congr 1
        have h := Finset.sum_range_sub' (fun i : ℕ => 1 / Real.sqrt (N + (i : ℝ))) j
        simpa using h
      have htail : 2 * (1 / Real.sqrt N - 1 / Real.sqrt (N + (j : ℝ))) ≤ 2 * (1 / Real.sqrt N) := by
        have h1 : 0 ≤ 1 / Real.sqrt (N + (j : ℝ)) := by positivity
        linarith
      have hsumtail : (∑ i ∈ Finset.range j,
                (1 : ℝ) / ((N + ((i + 1 : ℕ) : ℝ)) * Real.sqrt (N + ((i + 1 : ℕ) : ℝ))))
            ≤ 2 * (1 / Real.sqrt N) :=
        le_trans hsum1 (le_trans (le_of_eq hsum2) htail)
      have hf0 : (1 : ℝ) / ((N + ((0 : ℕ) : ℝ)) * Real.sqrt (N + ((0 : ℕ) : ℝ)))
          = 1 / (N * Real.sqrt N) := by norm_num
      have h1sqrt : 1 / (N * Real.sqrt N) ≤ 1 / Real.sqrt N := by
        refine one_div_le_one_div_of_le hsqN ?_
        exact le_mul_of_one_le_left hsqN.le hN
      have hbound : 1 / (N * Real.sqrt N)
            + ∑ i ∈ Finset.range j,
                (1 : ℝ) / ((N + ((i + 1 : ℕ) : ℝ)) * Real.sqrt (N + ((i + 1 : ℕ) : ℝ)))
          ≤ 3 / Real.sqrt N := by
        have h2 := h1sqrt
        have h1n : 3 / Real.sqrt N = 1 / Real.sqrt N + 2 * (1 / Real.sqrt N) := by ring
        linarith
      rw [hf0]
      exact hbound
  exact ⟨summable_of_sum_range_le hfnn hpartial, Real.tsum_le_of_sum_range_le hfnn hpartial⟩

/-- `-Re z ≤ ‖z‖`. -/
private theorem neg_re_le_norm (z : ℂ) : -z.re ≤ ‖z‖ :=
  le_trans (neg_le_abs z.re) (Complex.abs_re_le_norm z)

/-- `1 + log t ≤ 3 √t` for `t ≥ 1`. -/
private theorem one_add_log_le_three_sqrt {t : ℝ} (ht : 1 ≤ t) :
    1 + Real.log t ≤ 3 * Real.sqrt t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hlog : Real.log t = 2 * Real.log (Real.sqrt t) := by
    rw [← hsq, Real.log_pow]
    norm_num
  have h2 : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 := Real.log_le_sub_one_of_pos hs0
  have h3 : 1 ≤ Real.sqrt t := by
    have := Real.sqrt_le_sqrt ht
    rwa [Real.sqrt_one] at this
  rw [hlog]
  linarith

/-- Pointwise domination of one defect term: for `1 ≤ s ≤ t`,
`K (1 + log t)/t² ≤ 3K/(s√s)`. -/
private theorem defect_term_sqrt_le {K t s : ℝ} (hK : 0 ≤ K) (ht : 1 ≤ t) (hs : 0 < s)
    (hst : s ≤ t) : K * (1 + Real.log t) / t ^ 2 ≤ 3 * K / (s * Real.sqrt s) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  have hlog := one_add_log_le_three_sqrt ht
  have h1 : K * (1 + Real.log t) / t ^ 2 ≤ K * (3 * Real.sqrt t) / t ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hlog hK
  have h2 : K * (3 * Real.sqrt t) / t ^ 2 = 3 * K * (Real.sqrt t / t ^ 2) := by ring
  have h3 : Real.sqrt t / t ^ 2 = 1 / (t * Real.sqrt t) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [show Real.sqrt t * (t * Real.sqrt t) = t * (Real.sqrt t * Real.sqrt t) by ring,
      Real.mul_self_sqrt ht0.le]
    ring
  have h4 : 1 / (t * Real.sqrt t) ≤ 1 / (s * Real.sqrt s) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul hst (Real.sqrt_le_sqrt hst) (Real.sqrt_nonneg s) ((le_of_lt hs).trans hst)
  have h5 : 3 * K * (1 / (s * Real.sqrt s)) = 3 * K / (s * Real.sqrt s) := by ring
  calc K * (1 + Real.log t) / t ^ 2
      ≤ K * (3 * Real.sqrt t) / t ^ 2 := h1
    _ = 3 * K * (Real.sqrt t / t ^ 2) := h2
    _ = 3 * K * (1 / (t * Real.sqrt t)) := by rw [h3]
    _ ≤ 3 * K * (1 / (s * Real.sqrt s)) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 3 * K / (s * Real.sqrt s) := h5

/-! ## The deep decay estimate -/

/-- **The deep decay estimate.**  On a sufficiently far left half-plane a bounded fixed point of
`Omega` satisfies `‖Z w‖ ≤ K / √(1 - Re w)`.  The proof expands `Z w = Omega f a Z w` into the
defect series and dominates it, term by term, by `3K₀/((N + n)√(N + n))` with `N = 1 - Re w`,
whose sum is `O(1/√N)` uniformly. -/
private theorem Z_deep_estimate (hb : ParabolicBounds f h a r A A') (Z : ℂ → ℂ)
    (hZbd : ∀ w : ℂ, w ∈ LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2)
    (hZfix : ∀ w : ℂ, w ∈ LeftHalfPlane R → Z w = Omega f a Z w)
    (htsum : ∀ N : ℝ, 1 ≤ N →
      Summable (fun n : ℕ => (1 : ℝ) / ((N + (n : ℝ)) * Real.sqrt (N + (n : ℝ)))) ∧
        ∑' n : ℕ, (1 : ℝ) / ((N + (n : ℝ)) * Real.sqrt (N + (n : ℝ))) ≤ 3 / Real.sqrt N) :
    ∃ R' K : ℝ, R ≤ R' ∧ 0 ≤ K ∧
      ∀ w : ℂ, w.re < -R' → ‖Z w‖ ≤ K / Real.sqrt (1 + (-w.re)) := by
  obtain ⟨R₀, K₀, _hR₀pos, _hrR₀, hK₀, hdef⟩ := Work.FatouCoord.Repelling.defect_bound hb
  refine ⟨max R (max R₀ 1), 9 * K₀, le_max_left R (max R₀ 1), by positivity, ?_⟩
  intro w hw
  have hRle : R ≤ max R (max R₀ 1) := le_max_left R (max R₀ 1)
  have hR₀le : R₀ ≤ max R (max R₀ 1) :=
    le_trans (le_max_left R₀ 1) (le_max_right R (max R₀ 1))
  have hwmemR : w ∈ LeftHalfPlane R := by
    rw [mem_LeftHalfPlane]
    linarith
  set N₀ : ℝ := 1 + (-w.re) with hN₀def
  have hN₀1 : 1 ≤ N₀ := by
    have h1 : (1 : ℝ) ≤ max R (max R₀ 1) :=
      le_trans (le_max_right R₀ 1) (le_max_right R (max R₀ 1))
    rw [hN₀def]
    linarith
  have hgsumm : Summable (fun n : ℕ => 3 * K₀ / ((N₀ + (n : ℝ)) * Real.sqrt (N₀ + (n : ℝ)))) :=
    ((htsum N₀ hN₀1).1.mul_left (3 * K₀)).congr (fun n => by rw [mul_one_div])
  have hterm : ∀ n : ℕ,
      ‖Petal.defect f a (w - (((n : ℕ) : ℂ) + 1)) (Z (w - (((n : ℕ) : ℂ) + 1)))‖
        ≤ 3 * K₀ / ((N₀ + (n : ℝ)) * Real.sqrt (N₀ + (n : ℝ))) := by
    intro n
    set x : ℂ := w - (((n : ℕ) : ℂ) + 1) with hxdef
    have hxre : x.re = w.re - ((n : ℝ) + 1) := by
      rw [hxdef]
      simp
    have hxR : x ∈ LeftHalfPlane R := by
      rw [mem_LeftHalfPlane, hxre]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hxR₀ : x ∈ LeftHalfPlane R₀ := by
      rw [mem_LeftHalfPlane, hxre]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hZx : ‖Z x‖ ≤ 1 := le_trans (hZbd x hxR) (by norm_num)
    have hbound := hdef x (Z x) hxR₀ hZx
    have hxnorm : N₀ + (n : ℝ) ≤ ‖x‖ := by
      have h := neg_re_le_norm x
      rw [hxre] at h
      have hkey : -(w.re - ((n : ℝ) + 1)) = N₀ + (n : ℝ) := by
        rw [hN₀def]
        ring
      linarith
    have hs0 : 0 < N₀ + (n : ℝ) := by linarith
    have ht1 : 1 ≤ ‖x‖ := le_trans (by linarith : (1 : ℝ) ≤ N₀ + (n : ℝ)) hxnorm
    exact le_trans hbound (defect_term_sqrt_le hK₀ ht1 hs0 hxnorm)
  have hfixw : Z w = ∑' n : ℕ,
      Petal.defect f a (w - (((n : ℕ) : ℂ) + 1)) (Z (w - (((n : ℕ) : ℂ) + 1))) := by
    rw [hZfix w hwmemR, Petal.Omega_apply]
  have hnormsumm : Summable (fun n : ℕ =>
      ‖Petal.defect f a (w - (((n : ℕ) : ℂ) + 1)) (Z (w - (((n : ℕ) : ℂ) + 1)))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hgsumm
  calc ‖Z w‖
      = ‖∑' n : ℕ,
          Petal.defect f a (w - (((n : ℕ) : ℂ) + 1)) (Z (w - (((n : ℕ) : ℂ) + 1)))‖ := by
        rw [hfixw]
    _ ≤ ∑' n : ℕ,
          ‖Petal.defect f a (w - (((n : ℕ) : ℂ) + 1)) (Z (w - (((n : ℕ) : ℂ) + 1)))‖ :=
        norm_tsum_le_tsum_norm hnormsumm
    _ ≤ ∑' n : ℕ, 3 * K₀ / ((N₀ + (n : ℝ)) * Real.sqrt (N₀ + (n : ℝ))) :=
        Summable.tsum_le_tsum hterm hnormsumm hgsumm
    _ = 3 * K₀ * (∑' n : ℕ, (1 : ℝ) / ((N₀ + (n : ℝ)) * Real.sqrt (N₀ + (n : ℝ)))) := by
        rw [← tsum_mul_left]
        exact tsum_congr (fun n => by rw [mul_one_div])
    _ ≤ 3 * K₀ * (3 / Real.sqrt N₀) :=
        mul_le_mul_of_nonneg_left (htsum N₀ hN₀1).2 (by positivity)
    _ = 9 * K₀ / Real.sqrt (1 + (-w.re)) := by
        rw [hN₀def]
        ring

/-! ## The decay of `Z` -/

theorem Z_Omega_decay {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') {R : ℝ} (hR : 0 ≤ R) (Z : ℂ → ℂ) (hZbd : ∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2) (hZfix : ∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → Z w = Work.FatouCoord.Petal.Omega f a Z w) : (∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, w ∈ Work.FatouCoord.Petal.LeftHalfPlane R → ‖Z w‖ ≤ K / Real.sqrt (1 + (-w.re))) ∧ (∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, R ≤ R' ∧ ∀ w : ℂ, w.re < -R' → ‖Z w‖ < ε) := by
  obtain ⟨R₀, K₀, hRR₀, hK₀nn, hdeep⟩ :=
    Z_deep_estimate hb Z hZbd hZfix (fun N hN => inv_mul_sqrt_tsum_aux hN)
  refine ⟨⟨max K₀ (Real.sqrt (1 + R₀) / 2) + 1, by positivity, ?_⟩, ?_⟩
  · intro w hw
    rw [mem_LeftHalfPlane] at hw
    set K' : ℝ := max K₀ (Real.sqrt (1 + R₀) / 2) + 1 with hK'def
    have hK'ge : K₀ ≤ K' := by
      rw [hK'def]
      linarith [le_max_left K₀ (Real.sqrt (1 + R₀) / 2)]
    have hK'ge₂ : Real.sqrt (1 + R₀) / 2 ≤ K' := by
      rw [hK'def]
      linarith [le_max_right K₀ (Real.sqrt (1 + R₀) / 2)]
    rcases lt_or_ge w.re (-R₀) with hlt | hge
    · exact le_trans (hdeep w hlt)
        (div_le_div_of_nonneg_right hK'ge (Real.sqrt_nonneg _))
    · have hbd := hZbd w (by rw [mem_LeftHalfPlane]; exact hw)
      have hsqpos : 0 < Real.sqrt (1 + R₀) := Real.sqrt_pos.mpr (by linarith)
      have hsqle : Real.sqrt (1 + (-w.re)) ≤ Real.sqrt (1 + R₀) := Real.sqrt_le_sqrt (by linarith)
      have hpos : 0 < Real.sqrt (1 + (-w.re)) := Real.sqrt_pos.mpr (by linarith [hR])
      have hhalf : (1 : ℝ) / 2 ≤ K' / Real.sqrt (1 + (-w.re)) := by
        have h2 : (Real.sqrt (1 + R₀) / 2) / Real.sqrt (1 + R₀) ≤ K' / Real.sqrt (1 + R₀) :=
          div_le_div_of_nonneg_right hK'ge₂ hsqpos.le
        have h3 : K' / Real.sqrt (1 + R₀) ≤ K' / Real.sqrt (1 + (-w.re)) :=
          div_le_div_of_nonneg_left (by positivity) hpos hsqle
        have h4 : (Real.sqrt (1 + R₀) / 2) / Real.sqrt (1 + R₀) = 1 / 2 := by
          field_simp
        linarith
      linarith
  · intro ε hε
    by_cases hK0 : K₀ = 0
    · refine ⟨R₀, hRR₀, fun w hw => ?_⟩
      have hd := hdeep w hw
      rw [hK0, zero_div] at hd
      linarith
    · have hKpos : 0 < K₀ := lt_of_le_of_ne hK₀nn (Ne.symm hK0)
      obtain ⟨n, hn⟩ := exists_nat_gt (max (max R R₀) ((K₀ / ε) ^ 2))
      refine ⟨(n : ℝ), ?_, ?_⟩
      · have h1 : R ≤ max R R₀ := le_max_left R R₀
        have h2 : max R R₀ ≤ max (max R R₀) ((K₀ / ε) ^ 2) := le_max_left _ _
        linarith
      · intro w hw
        have hR₀n : R₀ < (n : ℝ) := by
          have h2 : max R R₀ ≤ max (max R R₀) ((K₀ / ε) ^ 2) := le_max_left _ _
          have h4 : R₀ ≤ max R R₀ := le_max_right R R₀
          linarith
        have hgn : (K₀ / ε) ^ 2 < (n : ℝ) := by
          have h3 : (K₀ / ε) ^ 2 ≤ max (max R R₀) ((K₀ / ε) ^ 2) := le_max_right _ _
          linarith
        have hd := hdeep w (by linarith)
        have hwre : (K₀ / ε) ^ 2 < 1 + (-w.re) := by linarith
        have hpos : 0 < Real.sqrt (1 + (-w.re)) := Real.sqrt_pos.mpr (by linarith)
        have hsq : K₀ / ε < Real.sqrt (1 + (-w.re)) := by
          rw [show K₀ / ε = Real.sqrt ((K₀ / ε) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
          exact Real.sqrt_lt_sqrt (by positivity) hwre
        calc ‖Z w‖ ≤ K₀ / Real.sqrt (1 + (-w.re)) := hd
          _ < ε := by
              rw [div_lt_iff₀ hpos]
              have h := mul_lt_mul_of_pos_left hsq hε
              rwa [show ε * (K₀ / ε) = K₀ by field_simp] at h

end

end Work.FatouCoordFix.Repelling
