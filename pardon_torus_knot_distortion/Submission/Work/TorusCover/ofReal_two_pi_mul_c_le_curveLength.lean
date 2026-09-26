import Mathlib
import Submission.Work.TorusCover.Basic

/-!
# The length of an essential curve on a parametrised torus

`Work.TorusCover.TorusParam` carries a uniform *pointwise* lower bound for the derivative of
`psiMap psi`, and `Work.TorusCover.exists_dist_lower_bound` upgrades it to a two-point bound:
for every `ε > 0` there is `δ > 0` with

  `(P.c - ε) * ‖x - y‖ ≤ ‖psiMap P.psi x - psiMap P.psi y‖`  whenever `‖x - y‖ ≤ δ`.

The present file deduces the corresponding *global* lower bound for the extrinsic length
(total variation) of a curve on the torus: if `γ` admits a periodic lift `Λ` whose winding
vector `v` is nonzero, then `γ` must travel at least `2π * P.c` during one period, because it
must cross the fundamental domain once in the direction of `v`:

  `ENNReal.ofReal (2 * π * P.c) ≤ curveLength γ 0 (2π)`.

The proof is the classical chain of inequalities, carried out in the extended nonnegative
reals:

* the endpoint displacement `Λ (2π) - Λ 0 = periodShift v` of the lift has norm `≥ 2π`
  (`IsPeriodicLift.two_pi_le_norm_displacement`);
* the variation of the lift over `[0, 2π]` dominates that displacement
  (`eVariationOn.edist_le`, via telescoping sums);
* the curve `γ = psiMap psi ∘ Λ` is compared with the lift on a partition of `[0, 2π]` fine
  enough that consecutive lift values are within `δ`; continuity of `Λ` on the compact
  interval supplies such a partition (uniform continuity);
* the resulting bound `2π * (P.c - ε) ≤ curveLength γ 0 (2π)` for every `ε > 0` is passed to
  the limit `ε → 0` using the left continuity of `ENNReal.ofReal`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.TorusCover

noncomputable section

/-! ### A limiting form of `ENNReal.ofReal` -/

/-- If `ENNReal.ofReal y ≤ L` for every `0 ≤ y < x`, then `ENNReal.ofReal x ≤ L`.
This is the "left continuity" of `ENNReal.ofReal`: `ofReal x` is the supremum of the
values `ofReal y` over `y < x`. -/
lemma ofReal_le_of_forall_lt (L : ℝ≥0∞) {x : ℝ}
    (h : ∀ y : ℝ, 0 ≤ y → y < x → ENNReal.ofReal y ≤ L) : ENNReal.ofReal x ≤ L := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [ENNReal.ofReal_eq_zero.mpr hx.le]; exact zero_le
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rw [← hx0, ENNReal.ofReal_zero]; exact zero_le
  rcases eq_or_ne L ⊤ with hL | hL
  · rw [hL]; exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal hL]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_gt (x / ε)
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le (div_pos hxpos hε) hn.le
  have hn1 : (1:ℝ) ≤ n := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.cast_pos.mp hnpos))
  have hxn : x / n < ε := by
    rw [div_lt_iff₀ hnpos, mul_comm]
    exact (div_lt_iff₀ hε).mp hn
  have hdiv : x / n ≤ x := by
    rw [div_le_iff₀ hnpos]
    exact le_mul_of_one_le_right hxpos.le hn1
  have hy0 : 0 ≤ x - x / n := by linarith
  have hylt : x - x / n < x := by
    have : 0 < x / n := div_pos hxpos hnpos
    linarith
  have hyl := h (x - x / n) hy0 hylt
  rw [ENNReal.ofReal_le_iff_le_toReal hL] at hyl
  calc x = (x - x / n) + x / n := by ring
    _ ≤ L.toReal + ε := by linarith [hyl, le_of_lt hxn]

/-! ### Uniform partitions of `[0, 2π]` -/

/-- The interval `[0, 2π]` can be subdivided into `N` equal pieces of length `< δ`:
there is an increasing sequence `t : ℕ → ℝ` with `t 0 = 0`, `t N = 2π`, all of whose terms
lie in `[0, 2π]` and whose consecutive terms are closer than `δ`. -/
lemma exists_uniform_partition {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, 0 < N ∧ ∃ t : ℕ → ℝ, t 0 = 0 ∧ t N = 2 * Real.pi ∧ Monotone t ∧
      (∀ i, t i ∈ Set.Icc (0:ℝ) (2 * Real.pi)) ∧ ∀ i < N, dist (t (i+1)) (t i) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * Real.pi / δ)
  have hNpos : (0:ℝ) < N := lt_of_lt_of_le (div_pos Real.two_pi_pos hδ) hN.le
  have hNpos' : (0:ℕ) < N := Nat.cast_pos.mp hNpos
  have hNne : ((N:ℕ):ℝ) ≠ 0 := ne_of_gt hNpos
  have hNlt : 2 * Real.pi / (N:ℝ) < δ := by
    rw [div_lt_iff₀ hNpos]
    have h := (div_lt_iff₀ hδ).mp hN
    linarith [h]
  have hstep_nonneg : 0 ≤ 2 * Real.pi / (N:ℝ) := div_nonneg Real.two_pi_pos.le hNpos.le
  set t : ℕ → ℝ := fun i => min ((i:ℝ) * (2 * Real.pi / (N:ℝ))) (2 * Real.pi) with ht_def
  have ht_coe : ∀ i ≤ N, t i = (i:ℝ) * (2 * Real.pi / (N:ℝ)) := by
    intro i hi
    simp only [ht_def]
    refine min_eq_left ?_
    calc (i:ℝ) * (2*Real.pi/(N:ℝ)) ≤ (N:ℝ) * (2*Real.pi/(N:ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hstep_nonneg
      _ = 2*Real.pi := mul_div_cancel₀ _ hNne
  refine ⟨N, hNpos', t, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht_coe 0 (Nat.zero_le N)]; simp
  · rw [ht_coe N le_rfl, mul_div_cancel₀ _ hNne]
  · apply monotone_nat_of_le_succ
    intro i
    simp only [ht_def]
    exact min_le_min (mul_le_mul_of_nonneg_right (by push_cast; linarith) hstep_nonneg) le_rfl
  · intro i
    simp only [ht_def, Set.mem_Icc]
    exact ⟨le_min (mul_nonneg (Nat.cast_nonneg i) hstep_nonneg) Real.two_pi_pos.le,
      min_le_right _ _⟩
  · intro i hi
    have hiN : i + 1 ≤ N := Nat.succ_le_of_lt hi
    rw [ht_coe (i+1) hiN, ht_coe i hi.le, Real.dist_eq,
      show (↑(i+1) : ℝ) * (2*Real.pi/(N:ℝ)) - (i:ℝ) * (2*Real.pi/(N:ℝ)) = 2*Real.pi/(N:ℝ) by
        push_cast; ring,
      abs_of_pos (div_pos Real.two_pi_pos hNpos)]
    exact hNlt

/-! ### Variation of a curve versus variation of its lift -/

/-- **The core length estimate.**  Let `Λ : ℝ → ℝ × ℝ` be a continuous curve in the parameter
plane, `γ` the curve it traces on the torus (`γ t = psiMap P.psi (Λ t)`), and suppose that on
the endpoints of one period the lift has moved by at least `2π` (as happens for a periodic lift
with nonzero winding vector).  If `psiMap` expands distances between points at distance `≤ δ`
by at least a factor `c' ≥ 0`, then the total variation of `γ` over `[0, 2π]` is at least
`c' * 2π`.

The comparison is made on a uniform partition of `[0, 2π]` fine enough that the lift does not
move more than `δ` between consecutive partition points; such a partition exists by uniform
continuity of `Λ` on the compact interval. -/
lemma ofReal_mul_le_eVariationOn_of_two_point_bound (P : TorusParam) {γ : ℝ → R3}
    {Λ : ℝ → ℝ × ℝ} (hΛc : Continuous Λ) (hmap : ∀ t, γ t = psiMap P.psi (Λ t))
    (hends : 2 * Real.pi ≤ ‖Λ (2 * Real.pi) - Λ 0‖) {c' : ℝ} (hc' : 0 ≤ c')
    {δ : ℝ} (hδ : 0 < δ)
    (hbd : ∀ x y : ℝ × ℝ, ‖x - y‖ ≤ δ →
      c' * ‖x - y‖ ≤ ‖psiMap P.psi x - psiMap P.psi y‖) :
    ENNReal.ofReal (c' * (2 * Real.pi)) ≤ eVariationOn γ (Set.Icc 0 (2 * Real.pi)) := by
  have huc : UniformContinuousOn Λ (Set.Icc (0:ℝ) (2*Real.pi)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hΛc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ', hδ'pos, hδ'⟩ := huc δ hδ
  obtain ⟨N, hNpos, t, ht0, htN, htmono, htmem, htstep⟩ := exists_uniform_partition hδ'pos
  -- the term-by-term comparison on the partition
  have hterm : ∀ i < N, ENNReal.ofReal (c' * ‖Λ (t (i+1)) - Λ (t i)‖) ≤
      edist (γ (t (i+1))) (γ (t i)) := by
    intro i hi
    have hdist : ‖Λ (t (i+1)) - Λ (t i)‖ ≤ δ := by
      have h1 := hδ' (t (i+1)) (htmem (i+1)) (t i) (htmem i) (htstep i hi)
      rw [dist_eq_norm] at h1
      exact h1.le
    have hb := hbd (Λ (t (i+1))) (Λ (t i)) hdist
    have h2 : ENNReal.ofReal (c' * ‖Λ (t (i+1)) - Λ (t i)‖) ≤
        ENNReal.ofReal ‖psiMap P.psi (Λ (t (i+1))) - psiMap P.psi (Λ (t i))‖ :=
      ENNReal.ofReal_le_ofReal hb
    simpa [edist_dist, dist_eq_norm, hmap] using h2
  have hsum : (∑ i ∈ Finset.range N, edist (γ (t (i+1))) (γ (t i))) ≤
      eVariationOn γ (Set.Icc 0 (2*Real.pi)) :=
    eVariationOn.sum_le (f := γ) (s := Set.Icc 0 (2*Real.pi)) htmono htmem
  -- the displacement of the lift is dominated by its variation along the partition
  have htel : ‖Λ (2*Real.pi) - Λ 0‖ ≤ ∑ i ∈ Finset.range N, ‖Λ (t (i+1)) - Λ (t i)‖ := by
    have htel_sum : ∑ i ∈ Finset.range N, (Λ (t (i+1)) - Λ (t i)) = Λ (t N) - Λ (t 0) :=
      Finset.sum_range_sub (fun i => Λ (t i)) N
    calc ‖Λ (2*Real.pi) - Λ 0‖
        = ‖∑ i ∈ Finset.range N, (Λ (t (i+1)) - Λ (t i))‖ := by
          rw [htel_sum, htN, ht0]
      _ ≤ ∑ i ∈ Finset.range N, ‖Λ (t (i+1)) - Λ (t i)‖ := norm_sum_le _ _
  have h4 : ENNReal.ofReal (c' * ∑ i ∈ Finset.range N, ‖Λ (t (i+1)) - Λ (t i)‖)
      = ∑ i ∈ Finset.range N, ENNReal.ofReal (c' * ‖Λ (t (i+1)) - Λ (t i)‖) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg hc' (norm_nonneg _))]
  calc ENNReal.ofReal (c' * (2 * Real.pi))
      ≤ ENNReal.ofReal (c' * ‖Λ (2*Real.pi) - Λ 0‖) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hends hc')
    _ ≤ ENNReal.ofReal (c' * ∑ i ∈ Finset.range N, ‖Λ (t (i+1)) - Λ (t i)‖) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left htel hc')
    _ = ∑ i ∈ Finset.range N, ENNReal.ofReal (c' * ‖Λ (t (i+1)) - Λ (t i)‖) := h4
    _ ≤ ∑ i ∈ Finset.range N, edist (γ (t (i+1))) (γ (t i)) :=
        Finset.sum_le_sum (fun i hi => hterm i (Finset.mem_range.mp hi))
    _ ≤ eVariationOn γ (Set.Icc 0 (2*Real.pi)) := hsum

/-! ### The length bound -/

theorem ofReal_two_pi_mul_c_le_curveLength (P : Work.TorusCover.TorusParam)
    {γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ}
    (hΛ : Work.TorusCover.IsPeriodicLift P.psi γ v Λ) (hv : v ≠ 0)
    (hest : ∀ ε > 0, ∃ δ > 0, ∀ x y : ℝ × ℝ, ‖x - y‖ ≤ δ →
      (P.c - ε) * ‖x - y‖ ≤ ‖Work.TorusCover.psiMap P.psi x - Work.TorusCover.psiMap P.psi y‖) :
    ENNReal.ofReal (2 * Real.pi * P.c) ≤ Work.TorusCover.curveLength γ 0 (2 * Real.pi) := by
  rw [curveLength_def]
  refine ofReal_le_of_forall_lt (eVariationOn γ (Set.Icc 0 (2 * Real.pi))) fun d hd0 hdlt => ?_
  set c' : ℝ := d / (2 * Real.pi) with hc'def
  have h2pi : (0:ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hc'0 : 0 ≤ c' := by rw [hc'def]; exact div_nonneg hd0 h2pi.le
  have hc'lt : c' < P.c := by rw [hc'def, div_lt_iff₀ h2pi]; linarith
  obtain ⟨δ, hδpos, hδ⟩ := hest (P.c - c') (by linarith)
  have hδ' : ∀ x y : ℝ × ℝ, ‖x - y‖ ≤ δ →
      c' * ‖x - y‖ ≤ ‖psiMap P.psi x - psiMap P.psi y‖ := by
    intro x y hxy
    have h := hδ x y hxy
    have hcc : P.c - (P.c - c') = c' := by ring
    rwa [hcc] at h
  have hcore := ofReal_mul_le_eVariationOn_of_two_point_bound P hΛ.continuous
      (fun t => (hΛ.map_eq t).symm) (hΛ.two_pi_le_norm_displacement hv) hc'0 hδpos hδ'
  have hcd : c' * (2 * Real.pi) = d := by
    rw [hc'def]
    exact div_mul_cancel₀ d (ne_of_gt h2pi)
  rw [← hcd]
  exact hcore

end

end Work.TorusCover
