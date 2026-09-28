import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.volume_rNorm_ball
import Submission.Work.HP.rNorm_smul
import Submission.Work.HP.box_card
import Submission.Work.HP.LsetAux.GridDefs
import Submission.Work.HP.LsetAux.exists_grid_net
import Submission.Work.HP.LsetAux.grid_arith
import Submission.Work.HP.LsetAux.grid_slab
import Submission.Work.HP.LsetAux.grid_subset

/-!
# `Lset d n` has measure zero

`Lset d n` is the set of coefficient vectors `a` in the unit ball of degree-`d` forms (`d ≥ 2`,
`n ≥ 3`) for which some unit vector `x` is a *singular* real zero: `f_a(x) = 0` and
`∇f_a(x) = 0`.

The proof covers the unit sphere by the rescaled grid `{z/N}` (`LsetAux.exists_grid_net`): for
`a ∈ Lset d n` with singular zero `x` and a grid point `w = gw n N z` within `2√(n+1)/N ≤ δ`
of `x`, the Taylor hypothesis `htay` and the Lipschitz hypothesis `hgrad` give
`|f_a(w)| ≤ 4 C₂ (n+1)/N² =: ε` and `|∇f_a(w)| ≤ 2 C₁ √(n+1)/N =: δ`
(`LsetAux.grid_subset`).  The slab estimate `hslab` bounds the volume of the coefficient region
`{a : |f_a(w)| ≤ ε, |∇f_a(w)| ≤ δ}` by `K ε δ^n` (`LsetAux.grid_slab`), and there are only
`(2N+1)^{n+1}` grid points, so
`volume (Lset d n) ≤ (2N+1)^{n+1} K ε δ^n ≪ 1/N → 0` (`LsetAux.grid_arith`, `box_card`).
-/

set_option autoImplicit false
noncomputable section
open Classical Finset MvPolynomial MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Work.HP

theorem Lset_zero (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n)
    (hslab : ∃ K, 0 < K ∧ ∀ (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (A ε δ : ℝ),
      1 / (n + 1 : ℝ) ≤ |x i| → rNorm x ≤ 2 → 0 ≤ A → 0 ≤ ε → 0 ≤ δ →
      volume {a : Mon d n → ℝ | rNorm a ≤ A ∧ |formEvalR d n a x| ≤ ε ∧
          (∀ j : Fin (n + 1), |gradVec d n a x j| ≤ δ)}
        ≤ ENNReal.ofReal (K * ε * δ ^ n * A ^ (NN d n - n - 1)))
    (hgrad : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        rNorm (gradVec d n a y - gradVec d n a x) ≤ C * rNorm a * rNorm (y - x))
    (htay : ∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ C * rNorm a * (rNorm (y - x)) ^ 2)
    (hball : ∀ (r : ℝ) (x : Mon d n → ℝ), 0 ≤ r →
        volume {w : Mon d n → ℝ | rNorm (w - x) ≤ r}
          = ENNReal.ofReal (r ^ NN d n) * volume {w : Mon d n → ℝ | rNorm w ≤ 1}) :
    volume (Lset d n) = 0 := by
  obtain ⟨K, hKpos, hslab'⟩ := hslab
  obtain ⟨C1, hC1pos, hgrad'⟩ := hgrad
  obtain ⟨C2, hC2pos, htay'⟩ := htay
  have hC1nn : 0 ≤ C1 := le_of_lt hC1pos
  have hC2nn : 0 ≤ C2 := le_of_lt hC2pos
  set M : ℝ := 3 ^ (n + 1) * K * 4 * C2 * ((n : ℝ) + 1) *
      (2 * C1 * Real.sqrt ((n : ℝ) + 1)) ^ n with hM
  have key : ∀ N : ℕ, 2 * (n + 1) ≤ N →
      volume (Lset d n) ≤ ENNReal.ofReal (M / (N : ℝ)) := by
    intro N hN
    have hN1 : 1 ≤ N := by omega
    have hNne : N ≠ 0 := by omega
    set s : Finset (Fin (n + 1) → ℤ) := (LsetAux.gbox n N).filter (fun z => z ≠ 0) with hs
    set c : ℝ := K * LsetAux.gEps n N C2 * (LsetAux.gDel n N C1) ^ n with hc
    have hε : 0 ≤ LsetAux.gEps n N C2 := by
      rw [LsetAux.gEps]; apply div_nonneg <;> positivity
    have hδ : 0 ≤ LsetAux.gDel n N C1 := by
      rw [LsetAux.gDel]; apply div_nonneg <;> positivity
    have hcnn : 0 ≤ c := by rw [hc]; positivity
    have hcover := LsetAux.grid_subset d n N hN hC1nn hC2nn hgrad' htay'
    have h1 : volume (Lset d n) ≤ ∑ z ∈ s, volume (LsetAux.gS d n N C1 C2 z) := by
      calc volume (Lset d n) ≤ volume (⋃ z ∈ s, LsetAux.gS d n N C1 C2 z) :=
            measure_mono (by rw [hs]; exact hcover)
        _ ≤ ∑ z ∈ s, volume (LsetAux.gS d n N C1 C2 z) :=
            measure_biUnion_finset_le s _
    have h2 : (∑ z ∈ s, volume (LsetAux.gS d n N C1 C2 z)) ≤
        ∑ z ∈ s, ENNReal.ofReal c := by
      refine Finset.sum_le_sum (fun z hz => ?_)
      have hz' : z ∈ (LsetAux.gbox n N).filter (fun z => z ≠ 0) := by
        rw [← hs]; exact hz
      have hz0 : z ≠ 0 := (Finset.mem_filter.mp hz').2
      have h := LsetAux.grid_slab d n N hKpos hC1nn hC2nn hslab' hNne hz0
      rwa [hc]
    have h3 : (∑ z ∈ s, ENNReal.ofReal c) = ENNReal.ofReal ((s.card : ℝ) * c) := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast (s.card)]
      rw [← ENNReal.ofReal_mul (p := (s.card : ℝ)) (by positivity : (0:ℝ) ≤ (s.card : ℝ))]
    have hcard : (s.card : ℝ) ≤ (2 * (N : ℝ) + 1) ^ (n + 1) := by
      have h1 : s.card ≤ (LsetAux.gbox n N).card := by
        rw [hs]; exact Finset.card_filter_le _ _
      have h2 : ((LsetAux.gbox n N).card : ℝ) = (2 * (N : ℝ) + 1) ^ (n + 1) := by
        have h := (box_card (ι := Fin (n + 1)) N).1
        simpa [LsetAux.gbox] using h
      calc (s.card : ℝ) ≤ ((LsetAux.gbox n N).card : ℝ) := by exact_mod_cast h1
        _ = (2 * (N : ℝ) + 1) ^ (n + 1) := h2
    have h4 : (s.card : ℝ) * c ≤ M / (N : ℝ) := by
      rw [hM]
      calc (s.card : ℝ) * c ≤ (2 * (N : ℝ) + 1) ^ (n + 1) * c :=
            mul_le_mul_of_nonneg_right hcard hcnn
        _ = (2 * (N : ℝ) + 1) ^ (n + 1) * K * LsetAux.gEps n N C2 *
              (LsetAux.gDel n N C1) ^ n := by rw [hc]; ring
        _ ≤ (3 ^ (n + 1) * K * 4 * C2 * ((n : ℝ) + 1) *
              (2 * C1 * Real.sqrt ((n : ℝ) + 1)) ^ n) / (N : ℝ) :=
            LsetAux.grid_arith n N hKpos hC1pos hC2pos hN1
    calc volume (Lset d n) ≤ ∑ z ∈ s, volume (LsetAux.gS d n N C1 C2 z) := h1
      _ ≤ ∑ z ∈ s, ENNReal.ofReal c := h2
      _ = ENNReal.ofReal ((s.card : ℝ) * c) := h3
      _ ≤ ENNReal.ofReal (M / (N : ℝ)) := ENNReal.ofReal_le_ofReal h4
  suffices volume (Lset d n) ≤ 0 by exact le_antisymm this zero_le
  have htend : Tendsto (fun N : ℕ => ENNReal.ofReal (M / (N : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => M / (N : ℝ)) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop tendsto_natCast_atTop_atTop M
    simpa using ENNReal.tendsto_ofReal h0
  exact ge_of_tendsto htend
    (Filter.eventually_atTop.mpr ⟨2 * (n + 1), fun N hN => key N hN⟩)

end Work.HP
