import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_norm_iterate_atTop
import Submission.Work.Bottcher.Green.green_eq_zero_iff_bounded
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Contraction2.isPreconnected_preimage_sq
import Submission.Work.Bottcher.Contraction2.isPreconnected_iInter_of_antitone_isCompact

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The filled tricorn is connected for mandelbar parameters

For `c` in the mandelbar (`c ∈ M*`, i.e. the critical orbit `T_c^n(0)` is bounded) the
*filled Julia set* of the tricorn map `T_c(z) = z̄² + c`, i.e. the zero locus of the
Green function `{z | G_c z = 0}`, is connected.

The proof is the elementary "nested compact continua" argument, avoiding any use of the
Böttcher coordinate.  Fix a radius

`R = max (2 * (1 + ‖c‖)) (M + 1)`

where `M` bounds the critical orbit.  Then `R` is an escape radius for `T_c` and contains
the whole critical orbit `T_c^n(0)` and hence also the orbit `T_c^n(c)` of the critical
value.  With

`A n = {z | ‖T_c^n z‖ ≤ R}`

the family `A n` is a decreasing sequence of compact preconnected sets whose intersection
is exactly the filled Julia set:

* `A 0` is a closed ball, hence preconnected;
* `A (n+1) = T_c^{-1}(A n)`, and the preimage of a preconnected set *containing the
  critical value* `c = T_c(0)` under `T_c` is again preconnected;
* `⋂ n, A n = {z | the T_c-orbit of z is bounded} = {z | G_c z = 0}`.

The intersection of a decreasing sequence of compact preconnected sets is preconnected,
and it contains `0`, so the filled Julia set is connected.
-/

open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Preimage of a preconnected set under `z ↦ z² + c`.** -/
theorem isPreconnected_preimage_sq_add {c : ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (hc : c ∈ S) : IsPreconnected {z : ℂ | z ^ 2 + c ∈ S} := by
  have hS' : IsPreconnected {w : ℂ | w + c ∈ S} := by
    have himg : {w : ℂ | w + c ∈ S} = (fun u : ℂ => u - c) '' S := by
      ext w
      constructor
      · intro hw; exact ⟨w + c, hw, by ring⟩
      · rintro ⟨u, hu, rfl⟩; simpa using hu
    rw [himg]
    exact hS.image _ (continuous_id.sub continuous_const).continuousOn
  have h0' : (0 : ℂ) ∈ {w : ℂ | w + c ∈ S} := by simpa using hc
  have h := isPreconnected_preimage_sq hS' h0'
  have heq : {z : ℂ | z ^ 2 + c ∈ S} = {z : ℂ | z ^ 2 ∈ {w : ℂ | w + c ∈ S}} := rfl
  rw [heq]; exact h

/-- **Preimage of a preconnected set under the antiholomorphic tricorn map.**  If `S` is
preconnected and contains the critical value `c = T_c(0)`, then `{z | T_c z ∈ S}` is
preconnected.  This is `isPreconnected_preimage_sq_add` conjugated by `z ↦ z̄`. -/
theorem isPreconnected_preimage_Tantibar {c : ℂ} {S : Set ℂ} (hS : IsPreconnected S)
    (hc : c ∈ S) : IsPreconnected {z : ℂ | Tantibar c z ∈ S} := by
  have h := isPreconnected_preimage_sq_add (c := c) hS hc
  have himg : {z : ℂ | Tantibar c z ∈ S} = (starRingEnd ℂ) '' {z : ℂ | z ^ 2 + c ∈ S} := by
    ext w
    constructor
    · intro hw
      exact ⟨starRingEnd ℂ w, hw, by simp⟩
    · rintro ⟨u, hu, rfl⟩
      show (starRingEnd ℂ (starRingEnd ℂ u)) ^ 2 + c ∈ S
      rw [show starRingEnd ℂ (starRingEnd ℂ u) = u by simp]
      exact hu
  rw [himg]
  exact h.image _ continuous_star.continuousOn

/-- `T_c^n(c) = T_c^{n+1}(0)`. -/
theorem iterate_Tantibar_c (c : ℂ) (n : ℕ) :
    (Tantibar c)^[n] c = (Tantibar c)^[n + 1] 0 := by
  conv_rhs => rw [Function.iterate_succ_apply]
  simp [Tantibar]

/-- **Escape step for the tricorn.**  For `R` at least the escape radius `2 (1 + ‖c‖)`, a
point of norm exceeding `R` is mapped to a point of norm exceeding `R`. -/
theorem lt_norm_Tantibar_of_lt {c : ℂ} {R : ℝ} {z : ℂ} (hR : 2 * (1 + ‖c‖) ≤ R)
    (hz : R < ‖z‖) : R < ‖Tantibar c z‖ := by
  have hz2 : (2 : ℝ) ≤ ‖z‖ := by
    have : (2 : ℝ) ≤ 2 * (1 + ‖c‖) := by linarith [norm_nonneg c]
    linarith
  have hcn : ‖c‖ < ‖z‖ / 2 := by
    have h : 2 * (1 + ‖c‖) ≤ ‖z‖ := le_trans hR hz.le
    linarith
  have hge : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c z‖ := by
    have h := Work.Escape.norm_Td_ge 2 c z
    rwa [Work.Escape.Td_two_eq] at h
  have h1 : ‖z‖ * (‖z‖ - 1 / 2) < ‖Tantibar c z‖ := by
    have heq : ‖z‖ ^ 2 - ‖z‖ / 2 = ‖z‖ * (‖z‖ - 1 / 2) := by ring
    linarith
  have h2 : R ≤ ‖z‖ * (‖z‖ - 1 / 2) := by
    have hz1 : (1 : ℝ) ≤ ‖z‖ - 1 / 2 := by linarith
    calc R ≤ ‖z‖ * 1 := by simpa using hz.le
      _ ≤ ‖z‖ * (‖z‖ - 1 / 2) := mul_le_mul_of_nonneg_left hz1 (norm_nonneg z)
  linarith

/-- If `R ≥ 2 * (1 + ‖c‖)` then exceeding the radius `R` is preserved by every iterate. -/
theorem lt_norm_iterate_Tantibar_of_lt {c : ℂ} {R : ℝ} (hR : 2 * (1 + ‖c‖) ≤ R) :
    ∀ (n : ℕ) (z : ℂ), R < ‖z‖ → R < ‖(Tantibar c)^[n] z‖ := by
  intro n
  induction n with
  | zero => intro z hz; simpa using hz
  | succ k ih =>
      intro z hz
      rw [Function.iterate_succ_apply']
      exact lt_norm_Tantibar_of_lt hR (ih z hz)

theorem isConnected_filledJulia_of_mem_mandelbar (c : ℂ)
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) :
    IsConnected {z : ℂ | Work.Bottcher.green c z = 0} := by
  classical
  obtain ⟨M, hM⟩ := hc
  have hnormc : ‖c‖ ≤ M := by
    have h1 : ‖c‖ = ‖(Tantibar c)^[1] 0‖ := by simp [Tantibar]
    rw [h1]; exact hM 1
  set R : ℝ := max (2 * (1 + ‖c‖)) (M + 1) with hRdef
  have hRge : 2 * (1 + ‖c‖) ≤ R := le_max_left _ _
  have hRM : M + 1 ≤ R := le_max_right _ _
  have hMlt : M < R := by linarith
  have hesc : ∀ z : ℂ, R < ‖z‖ → R < ‖Tantibar c z‖ := fun z hz =>
    lt_norm_Tantibar_of_lt hRge hz
  have hstep : ∀ (n : ℕ) (z : ℂ), R < ‖z‖ → R < ‖(Tantibar c)^[n] z‖ :=
    lt_norm_iterate_Tantibar_of_lt hRge
  set A : ℕ → Set ℂ := fun n => {z : ℂ | ‖(Tantibar c)^[n] z‖ ≤ R} with hAdef
  have hA0 : ∀ n, (0 : ℂ) ∈ A n := by
    intro n
    change ‖(Tantibar c)^[n] 0‖ ≤ R
    exact le_of_lt (lt_of_le_of_lt (hM n) hMlt)
  have hAc : ∀ n, c ∈ A n := by
    intro n
    change ‖(Tantibar c)^[n] c‖ ≤ R
    rw [iterate_Tantibar_c]
    exact le_of_lt (lt_of_le_of_lt (hM (n + 1)) hMlt)
  have hAbdd : ∀ n, A n ⊆ Metric.closedBall 0 R := by
    intro n z hz
    change ‖(Tantibar c)^[n] z‖ ≤ R at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra h
    rw [not_le] at h
    exact absurd hz (not_le.mpr (hstep n z h))
  have hAcpt : ∀ n, IsCompact (A n) := by
    intro n
    have hcont : Continuous fun z : ℂ => (Tantibar c)^[n] z :=
      (continuous_star.pow 2).add continuous_const |>.iterate n
    exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
      (isClosed_le (continuous_norm.comp hcont) continuous_const) (hAbdd n)
  have hAsucc : ∀ n, A (n + 1) = {z : ℂ | Tantibar c z ∈ A n} := by
    intro n
    ext z
    change ‖(Tantibar c)^[n + 1] z‖ ≤ R ↔ ‖(Tantibar c)^[n] (Tantibar c z)‖ ≤ R
    rw [Function.iterate_succ_apply]
  have hApre : ∀ n, IsPreconnected (A n) := by
    intro n
    induction n with
    | zero =>
        have h0 : A 0 = Metric.closedBall 0 R := by
          ext z
          simp [hAdef, Metric.mem_closedBall, dist_zero_right]
        rw [h0]
        exact (convex_closedBall (0 : ℂ) R).isPreconnected
    | succ k ih =>
        rw [hAsucc k]
        exact isPreconnected_preimage_Tantibar ih (hAc k)
  have hAanti : ∀ n, A (n + 1) ⊆ A n := by
    intro n z hz
    change ‖(Tantibar c)^[n + 1] z‖ ≤ R at hz
    change ‖(Tantibar c)^[n] z‖ ≤ R
    by_contra h
    rw [not_le] at h
    rw [show (Tantibar c)^[n + 1] z = Tantibar c ((Tantibar c)^[n] z) from
      Function.iterate_succ_apply' _ _ _] at hz
    exact absurd hz (not_le.mpr (hesc _ h))
  have hInter : IsPreconnected (⋂ n, A n) :=
    isPreconnected_iInter_of_antitone_isCompact hAcpt hApre hAanti
  have hKeq : {z : ℂ | Work.Bottcher.green c z = 0} = ⋂ n, A n := by
    ext z
    change Work.Bottcher.green c z = 0 ↔ z ∈ ⋂ n, A n
    rw [Set.mem_iInter, Work.Bottcher.Green.green_eq_zero_iff_bounded]
    constructor
    · rintro ⟨M', hM'⟩ n
      change ‖(Tantibar c)^[n] z‖ ≤ R
      by_contra h
      rw [not_le] at h
      have hw : (Tantibar c)^[n] z ∈ Work.Escape.escapeRegion ‖c‖ := by
        rw [Work.Escape.mem_escapeRegion]
        have hmax : max 2 ‖c‖ ≤ 2 * (1 + ‖c‖) := by
          rw [max_le_iff]
          exact ⟨by linarith [norm_nonneg c], by linarith [norm_nonneg c]⟩
        exact lt_of_le_of_lt hmax (lt_of_le_of_lt hRge h)
      have hten : Tendsto (fun k : ℕ => ‖(Tantibar c)^[k] ((Tantibar c)^[n] z)‖)
          atTop atTop :=
        Work.Escape.tendsto_norm_iterate_atTop (Tantibar c) 2 ‖c‖
          (Work.Escape.monicGrowth_Tantibar c) le_rfl hw
      rw [Filter.tendsto_atTop_atTop] at hten
      obtain ⟨i, hi⟩ := hten (M' + 1)
      have h1 : M' + 1 ≤ ‖(Tantibar c)^[i] ((Tantibar c)^[n] z)‖ := hi i le_rfl
      have h2 : ‖(Tantibar c)^[i] ((Tantibar c)^[n] z)‖ ≤ M' := by
        rw [← Function.iterate_add_apply]
        exact hM' (i + n)
      linarith
    · intro h
      refine ⟨R, fun n => ?_⟩
      have hn := h n
      change ‖(Tantibar c)^[n] z‖ ≤ R at hn
      exact hn
  refine ⟨⟨0, ?_⟩, ?_⟩
  · change Work.Bottcher.green c 0 = 0
    rw [Work.Bottcher.Green.green_eq_zero_iff_bounded]
    exact ⟨M, hM⟩
  · rw [hKeq]
    exact hInter

end Work.Bottcher.Contraction2
