import Mathlib
import Submission.Work.A3.majorArc_split

/-!
# The "deep arc" contribution to the energy (Area A3)

This is the piece of the circle-method analysis of `Work.A3.PolyEnergyBound` that handles the
**deep shoulder** of the major arcs: the points `θ = a/q + β` with `q ≤ N^γ`, `(a,q) = 1` and

  `|β| N^d ≥ 100⁻¹ (N/q)^{d/(d+1)}`,   `|β| ≤ 1/(q N^{d/2})`,   `d = deg Q`

(`Work.A3.deepArcSet Q N γ`).  On this range the elementary block/Riemann-sum comparison of
`Work.A3.coherentArc_bound` and `Work.A3.transitionArc_bound` no longer applies, and the whole
content of the region is the hypothesis `hdeep`: a *pointwise* power saving

  `‖expSum Q N (a/q + β)‖ ≤ C₀ N^{1-θ₀}`

which the paper's §5 obtains by the Ionescu–Wainger large-sieve/mean-value argument over the deep
shoulder.

The contribution of the region to the `2s`-th moment is then purely a matter of *how much of
`[0,1]` it occupies*: the region is contained in the union of the arcs of radius `1/(q N^{d/2})`
about the reduced fractions with `q ≤ N^γ`, of which there are `O(N^γ)` in `[0,1]`, each of
length `O(1/(q N^{d/2}))`, so

  `vol (deepArcSet Q N γ ∩ [0,1]) ≤ 16 N^{γ - d/2}`

(`Work.A3.volume_deepArcSet_le`).  Multiplying the pointwise bound to the power `2s` by this
volume and using the exponent bookkeeping

  `2γ + d/2 ≤ 2sθ₀`  (`hcond`)  `⟹`  `(1-θ₀)·2s + γ - d/2 ≤ 2s - d`

gives the claimed `C^{2s} N^{2s-d}`.

Note that no hypothesis relating `d` and `s` is needed: when `d > 2s` the right-hand side
`N^{2s-d}` is read with the *truncated* subtraction `max (2s-d) 0`, and the estimate above is
still valid (`2s - γ - d < 0`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.A3

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- **The pointwise deep-arc saving.**  Unpacking the witness `(q,a)` of `θ ∈ deepArcSet Q N γ`
and applying the hypothesis `hdeep` with `β = θ - a/q` gives the power saving at `θ`. -/
private lemma norm_expSum_le_of_mem_deepArcSet (Q : Polynomial ℤ) {γ θ₀ C₀ : ℝ} {N : ℕ}
    (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ∈ deepArcSet Q N γ)
    (hdeep : ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) ^ γ →
      ((N : ℝ) / (q : ℝ)) ^ ((Polynomial.natDegree Q : ℝ) / (Polynomial.natDegree Q + 1)) / 100
        ≤ |β| * (N : ℝ) ^ Polynomial.natDegree Q →
      |β| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) / 2)) →
      ‖expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C₀ * (N : ℝ) ^ (1 - θ₀)) :
    ‖expSum Q N θ‖ ≤ C₀ * (N : ℝ) ^ (1 - θ₀) := by
  obtain ⟨q, a, hq1, hcop, hqγ, herr, hdeepc⟩ := hθ
  have hq1Z : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1
  have h := hdeep N a (q : ℤ) (θ - (a : ℝ) / (q : ℝ)) hN hq1Z hcop hqγ
    (by push_cast; exact hdeepc) (by push_cast; exact herr)
  have harg : (a : ℝ) / ((q : ℤ) : ℝ) + (θ - (a : ℝ) / (q : ℝ)) = θ := by push_cast; ring
  rwa [harg] at h

/-- The volume of the deep arcs inside `[0,1]`: contained in the arcs of radius `1/(q N^{d/2})`
about the reduced fractions with `q ≤ N^γ`. -/
private lemma volume_deepArcSet_le_aux (Q : Polynomial ℤ) {γ : ℝ} (hγ : 0 ≤ γ) {N : ℕ}
    (hN : 1 ≤ N) :
    MeasureTheory.volume (deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal (16 * (N : ℝ) ^ (γ - (Q.natDegree : ℝ) / 2)) := by
  classical
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  set Nd : ℝ := (N : ℝ) ^ ((Q.natDegree : ℝ) / 2) with hNddef
  have hNdpos : 0 < Nd := by rw [hNddef]; exact Real.rpow_pos_of_pos hNpos _
  have hNd1 : (1 : ℝ) ≤ Nd := by rw [hNddef]; exact Real.one_le_rpow hN1 (by positivity)
  set M : ℕ := Nat.floor ((N : ℝ) ^ γ) with hMdef
  have hNγ1 : (1 : ℝ) ≤ (N : ℝ) ^ γ := Real.one_le_rpow hN1 hγ
  -- ### the covering of the deep arcs
  have hcover : deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1 ⊆
      ⋃ q ∈ Finset.range (M + 1), ⋃ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
        Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Nd))
          ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Nd)) := by
    rintro θ ⟨hθ, hθ0, hθ1⟩
    obtain ⟨q, a, hq1, hcop, hqγ, herr, -⟩ := hθ
    have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
    have hqM : q ≤ M := by rw [hMdef]; exact Nat.le_floor hqγ
    -- the approved error is at most `1/q`
    have herr2 : |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) := by
      refine le_trans herr (one_div_le_one_div_of_le hq0 ?_)
      nlinarith [hq0, hNd1]
    have hsplit : -(1 / (q : ℝ)) ≤ θ - (a : ℝ) / (q : ℝ) ∧
        θ - (a : ℝ) / (q : ℝ) ≤ 1 / (q : ℝ) := by
      have h := abs_le.mp herr2
      exact ⟨by linarith [h.1], h.2⟩
    -- the numerator range `-1 ≤ a ≤ q+1`
    have halow : (-1 : ℤ) ≤ a := by
      have h : (-(1 : ℝ)) ≤ (a : ℝ) := by
        have h2 : θ - 1 / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) := by linarith [hsplit.2]
        have h3 : (θ - 1 / (q : ℝ)) * (q : ℝ) ≤ (a : ℝ) := (le_div_iff₀ hq0).mp h2
        have hid : (θ - 1 / (q : ℝ)) * (q : ℝ) = θ * (q : ℝ) - 1 := by field_simp
        rw [hid] at h3
        nlinarith [hθ0, hq0]
      have h' : (((-1 : ℤ)) : ℝ) ≤ ((a : ℤ) : ℝ) := by push_cast; exact h
      exact (Int.cast_le (R := ℝ)).mp h'
    have hahigh : a ≤ (q : ℤ) + 1 := by
      have h : (a : ℝ) ≤ (q : ℝ) + 1 := by
        have h2 : (a : ℝ) / (q : ℝ) ≤ θ + 1 / (q : ℝ) := by linarith [hsplit.1]
        have h3 : (a : ℝ) ≤ (θ + 1 / (q : ℝ)) * (q : ℝ) := (div_le_iff₀ hq0).mp h2
        have hid : (θ + 1 / (q : ℝ)) * (q : ℝ) = θ * (q : ℝ) + 1 := by field_simp
        rw [hid] at h3
        nlinarith [hθ1, hq0]
      have h' : ((a : ℤ) : ℝ) ≤ (((q : ℤ) + 1 : ℤ) : ℝ) := by push_cast; exact h
      exact (Int.cast_le (R := ℝ)).mp h'
    refine Set.mem_iUnion₂.mpr ⟨q, Finset.mem_range.mpr (by omega), ?_⟩
    refine Set.mem_iUnion₂.mpr ⟨a, Finset.mem_Icc.mpr ⟨halow, hahigh⟩, ?_⟩
    have h := abs_le.mp herr
    exact Set.mem_Icc.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  -- ### the measure of the union of arcs
  have hperq : ∀ q : ℕ,
      (∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1), 2 * (1 / ((q : ℝ) * Nd))) ≤ 8 * Nd⁻¹ := by
    intro q
    have hcard : (Finset.Icc (-1 : ℤ) ((q : ℤ) + 1)).card = q + 3 := by
      rw [Int.card_Icc]
      have h1 : ((q : ℤ) + 1 + 1 - (-1)) = ((q + 3 : ℕ) : ℤ) := by push_cast; ring
      rw [h1, Int.toNat_natCast]
    have hsum : (∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1), 2 * (1 / ((q : ℝ) * Nd)))
        = ((q : ℝ) + 3) * (2 * (1 / ((q : ℝ) * Nd))) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      push_cast
      ring
    rw [hsum]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      simp only [Nat.cast_zero, zero_mul, div_zero, mul_zero]
      positivity
    · have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hkey : ((q : ℝ) + 3) * (2 * (1 / ((q : ℝ) * Nd))) = 2 * ((q : ℝ) + 3) / ((q : ℝ) * Nd) := by
        field_simp
      rw [hkey, div_le_iff₀ (by positivity)]
      have hkey2 : (8 * Nd⁻¹) * ((q : ℝ) * Nd) = 8 * (q : ℝ) := by
        field_simp
      rw [hkey2]
      have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      linarith
  have hbd : MeasureTheory.volume (deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1)
      ≤ ENNReal.ofReal ((M + 1 : ℝ) * (8 * Nd⁻¹)) := by
    calc MeasureTheory.volume (deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1)
        ≤ MeasureTheory.volume (⋃ q ∈ Finset.range (M + 1),
            ⋃ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
              Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Nd))
                ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Nd))) := measure_mono hcover
      _ ≤ ∑ q ∈ Finset.range (M + 1), MeasureTheory.volume (⋃ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
              Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Nd))
                ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Nd))) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ q ∈ Finset.range (M + 1), ENNReal.ofReal (8 * Nd⁻¹) := by
          refine Finset.sum_le_sum (fun q _ => ?_)
          refine le_trans (measure_biUnion_finset_le _ _) ?_
          have hterm : ∀ a : ℤ, MeasureTheory.volume (Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Nd))
                ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Nd)))
              = ENNReal.ofReal (2 * (1 / ((q : ℝ) * Nd))) := by
            intro a
            rw [Real.volume_Icc]
            congr 1
            ring
          calc ∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1),
                MeasureTheory.volume (Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * Nd))
                  ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * Nd)))
              = ∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1), ENNReal.ofReal (2 * (1 / ((q : ℝ) * Nd))) :=
                Finset.sum_congr rfl (fun a _ => hterm a)
            _ = ENNReal.ofReal (∑ a ∈ Finset.Icc (-1 : ℤ) ((q : ℤ) + 1), 2 * (1 / ((q : ℝ) * Nd))) :=
                (ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity)).symm
            _ ≤ ENNReal.ofReal (8 * Nd⁻¹) := ENNReal.ofReal_le_ofReal (hperq q)
      _ = ENNReal.ofReal ((M + 1 : ℝ) * (8 * Nd⁻¹)) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => by positivity)]
          congr 1
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  refine le_trans hbd (ENNReal.ofReal_le_ofReal ?_)
  have hMle : (M : ℝ) ≤ (N : ℝ) ^ γ := by
    rw [hMdef]
    exact Nat.floor_le (by positivity)
  have hfin : ((M : ℝ) + 1) ≤ 2 * (N : ℝ) ^ γ := by linarith
  have hbound : ((M + 1 : ℝ) * (8 * Nd⁻¹)) ≤ 16 * (N : ℝ) ^ (γ - (Q.natDegree : ℝ) / 2) := by
    have h1 : ((M : ℝ) + 1) * (8 * Nd⁻¹) ≤ (2 * (N : ℝ) ^ γ) * (8 * Nd⁻¹) :=
      mul_le_mul_of_nonneg_right hfin (by positivity)
    have h2 : (2 * (N : ℝ) ^ γ) * (8 * Nd⁻¹) = 16 * (N : ℝ) ^ (γ - (Q.natDegree : ℝ) / 2) := by
      rw [hNddef, Real.rpow_sub hNpos γ ((Q.natDegree : ℝ) / 2), div_eq_mul_inv]
      ring
    linarith [h1, h2.le, h2.ge]
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

/-- **The exponent bookkeeping of the deep arcs**: `2γ + d/2 ≤ 2sθ₀` makes the pointwise saving
`N^{1-θ₀}` (to the power `2s`) pay for the volume `N^{γ-d/2}` of the region and still gain
`N^{-d}`.  No relation between `d` and `s` is needed, thanks to the truncated subtraction. -/
private lemma deepArc_exponent_bookkeeping {γ θ₀ : ℝ} (hγ : 0 ≤ γ) {d s : ℕ}
    (hcond : 2 * γ + (d : ℝ) / 2 ≤ 2 * (s : ℝ) * θ₀) :
    (1 - θ₀) * ((2 * s : ℕ) : ℝ) + (γ - (d : ℝ) / 2) ≤ ((2 * s - d : ℕ) : ℝ) := by
  rcases lt_or_ge (2 * s) d with hlt | hle
  · rw [Nat.sub_eq_zero_of_le (le_of_lt hlt)]
    have hdR : ((2 * s : ℕ) : ℝ) < ((d : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at hdR ⊢
    nlinarith
  · rw [Nat.cast_sub hle]
    push_cast
    linarith

theorem deepArc_energy_contribution (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {γ θ₀ : ℝ} (hγ : 0 ≤ γ) (hθ₀ : 0 < θ₀) {C₀ : ℝ} (hC₀ : 0 < C₀) {s : ℕ} (hs : 1 ≤ s)
    (hcond : 2 * γ + (Polynomial.natDegree Q : ℝ) / 2 ≤ 2 * (s : ℝ) * θ₀)
    (hdeep : ∀ (N : ℕ) (a q : ℤ) (β : ℝ), 1 ≤ N → 1 ≤ q → IsCoprime a (q : ℤ) →
      (q : ℝ) ≤ (N : ℝ) ^ γ →
      ((N : ℝ) / (q : ℝ)) ^ ((Polynomial.natDegree Q : ℝ) / (Polynomial.natDegree Q + 1)) / 100
        ≤ |β| * (N : ℝ) ^ Polynomial.natDegree Q →
      |β| ≤ 1 / ((q : ℝ) * (N : ℝ) ^ ((Polynomial.natDegree Q : ℝ) / 2)) →
      ‖Work.A3.expSum Q N ((a : ℝ) / (q : ℝ) + β)‖ ≤ C₀ * (N : ℝ) ^ (1 - θ₀)) :
    ∃ C > 0, ∀ N : ℕ, 1 ≤ N →
      ∫ θ in Work.A3.deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1, ‖Work.A3.expSum Q N θ‖ ^ (2 * s)
        ≤ C ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
  classical
  refine ⟨max 1 (16 * C₀), lt_max_of_lt_left zero_lt_one, ?_⟩
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hN1
  set A : Set ℝ := deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1 with hA
  set K : ℝ := (C₀ * (N : ℝ) ^ (1 - θ₀)) ^ (2 * s) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  -- the pointwise saving, to the power `2s`
  have hpt : ∀ θ ∈ A, ‖expSum Q N θ‖ ^ (2 * s) ≤ K := by
    intro θ hθ
    rw [hK]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_expSum_le_of_mem_deepArcSet Q hN (hA ▸ hθ).1 hdeep) _
  -- the volume of `A` is finite (it sits inside `[0,1]`)
  have hfin : volume A < ⊤ := by
    rw [hA]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) (by rw [Real.volume_Icc]; simp)
  -- integrate the pointwise bound
  have h1 : ∫ θ in A, ‖expSum Q N θ‖ ^ (2 * s) ≤ K * volume.real A := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume) (s := A)
      (f := fun θ => ‖expSum Q N θ‖ ^ (2 * s)) (C := K) hfin (fun θ hθ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt θ hθ)
    calc ∫ θ in A, ‖expSum Q N θ‖ ^ (2 * s)
        ≤ ‖∫ θ in A, ‖expSum Q N θ‖ ^ (2 * s)‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ K * volume.real A := h
  -- the volume bound
  have h2 : volume.real A ≤ 16 * (N : ℝ) ^ (γ - (Polynomial.natDegree Q : ℝ) / 2) := by
    have hvol := volume_deepArcSet_le_aux Q hγ hN
    have htr : (volume (deepArcSet Q N γ ∩ Set.Icc (0 : ℝ) 1)).toReal
        ≤ 16 * (N : ℝ) ^ (γ - (Polynomial.natDegree Q : ℝ) / 2) := by
      refine le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol) (le_of_eq ?_)
      exact ENNReal.toReal_ofReal (by positivity)
    rw [MeasureTheory.Measure.real, hA]
    exact htr
  -- the exponent comparison
  have hexp : (1 - θ₀) * ((2 * s : ℕ) : ℝ) + (γ - (Polynomial.natDegree Q : ℝ) / 2)
      ≤ ((2 * s - Polynomial.natDegree Q : ℕ) : ℝ) :=
    deepArc_exponent_bookkeeping hγ hcond
  -- the constant comparison
  have hconst : 16 * C₀ ^ (2 * s) ≤ (max 1 (16 * C₀)) ^ (2 * s) := by
    have h1 : (16 * C₀) ^ (2 * s) ≤ (max 1 (16 * C₀)) ^ (2 * s) :=
      pow_le_pow_left₀ (by positivity) (le_max_right _ _) _
    have h2 : 16 * C₀ ^ (2 * s) ≤ (16 * C₀) ^ (2 * s) := by
      rw [mul_pow]
      have h16 : (16 : ℝ) ≤ 16 ^ (2 * s) := by
        calc (16 : ℝ) = 16 ^ 1 := (pow_one 16).symm
          _ ≤ 16 ^ (2 * s) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact mul_le_mul_of_nonneg_right h16 (by positivity)
    exact le_trans h2 h1
  calc ∫ θ in A, ‖expSum Q N θ‖ ^ (2 * s)
      ≤ K * volume.real A := h1
    _ ≤ K * (16 * (N : ℝ) ^ (γ - (Polynomial.natDegree Q : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h2 hKpos.le
    _ = (16 * C₀ ^ (2 * s)) *
          (N : ℝ) ^ ((1 - θ₀) * ((2 * s : ℕ) : ℝ)
            + (γ - (Polynomial.natDegree Q : ℝ) / 2)) := by
        rw [hK, mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 - θ₀)) (2 * s),
          ← Real.rpow_mul hNpos.le (1 - θ₀) ((2 * s : ℕ) : ℝ)]
        rw [Real.rpow_add hNpos]
        ring
    _ ≤ (16 * C₀ ^ (2 * s)) * (N : ℝ) ^ (((2 * s - Polynomial.natDegree Q : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hexp) (by positivity)
    _ = (16 * C₀ ^ (2 * s)) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) := by
        rw [Real.rpow_natCast]
    _ ≤ (max 1 (16 * C₀)) ^ (2 * s) * (N : ℝ) ^ (2 * s - Polynomial.natDegree Q) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)

end

end Work.A3
