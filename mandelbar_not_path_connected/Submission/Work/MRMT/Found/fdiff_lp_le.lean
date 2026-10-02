import Mathlib
import Submission.Work.MRMT.Found.norm_iteratedDeriv_affine_le
import Submission.Work.MRMT.Found.eLpNorm_le_of_support_measure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-! ## A one-dimensional finite-difference mean-value estimate

The `n`-th forward difference `∑_{j=0}^n (-1)^{n-j} C(n,j) h(a+j)` of a smooth function
`h : ℝ → ℂ` is bounded by any bound `B` for `‖h^{(n)}‖` on the interval `[a, a+n]`.  This is
the classical Hermite–Genocchi (discrete mean value) estimate, proved here by induction using
the Pascal-type recursion for binomial coefficients and the mean value inequality for the
auxiliary function `s ↦ ∑_j (-1)^{n-j} C(n,j) h(s+j)`. -/

/-- The Pascal recursion for the forward difference operator:
`Δ^{n+1} h (a) = Δ^n h (a+1) - Δ^n h (a)`. -/
private lemma fd_recur (n : ℕ) (h : ℝ → ℂ) (a : ℝ) :
    (∑ j ∈ Finset.range (n + 2), (-1 : ℂ) ^ (n + 1 - j) * ((n + 1).choose j : ℂ) * h (a + (j : ℝ)))
  = (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ (n - j) * (n.choose j : ℂ) * h (a + 1 + (j : ℝ)))
    - (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ (n - j) * (n.choose j : ℂ) * h (a + (j : ℝ))) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      (-1 : ℂ) ^ (n + 1 - (k + 1)) * ((n + 1).choose (k + 1) : ℂ) * h (a + ((k + 1 : ℕ) : ℝ))
      = (-1 : ℂ) ^ (n - k) * ((n.choose k : ℂ) + (n.choose (k + 1) : ℂ)) * h (a + 1 + (k : ℝ)) := by
    intro k hk
    have hexp : n + 1 - (k + 1) = n - k := by omega
    have hch : ((n + 1).choose (k + 1) : ℂ) = (n.choose k : ℂ) + (n.choose (k + 1) : ℂ) := by
      rw [Nat.choose_succ_succ]; push_cast; ring
    have harg : a + ((k + 1 : ℕ) : ℝ) = a + 1 + (k : ℝ) := by push_cast; ring
    rw [hexp, hch, harg]
  have hstepA : (∑ j ∈ Finset.range (n + 2),
        (-1 : ℂ) ^ (n + 1 - j) * ((n + 1).choose j : ℂ) * h (a + (j : ℝ)))
      = (∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ (n - k) * ((n.choose k : ℂ) + (n.choose (k + 1) : ℂ)) * h (a + 1 + (k : ℝ)))
        - (-1 : ℂ) ^ n * h a := by
    rw [Finset.sum_range_succ']
    have hf0 : (-1 : ℂ) ^ (n + 1 - 0) * ((n + 1).choose 0 : ℂ) * h (a + ((0 : ℕ) : ℝ))
        = -((-1 : ℂ) ^ n * h a) := by
      rw [Nat.sub_zero, pow_succ]
      simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, add_zero, mul_one]
      ring
    rw [Finset.sum_congr rfl hterm, hf0]
    ring
  have hstepB : (∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ (n - k) * ((n.choose k : ℂ) + (n.choose (k + 1) : ℂ)) * h (a + 1 + (k : ℝ)))
      = (∑ k ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ (n - k) * (n.choose k : ℂ) * h (a + 1 + (k : ℝ)))
        + (∑ k ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ (n - k) * (n.choose (k + 1) : ℂ) * h (a + 1 + (k : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    ring
  have hstepC : (∑ k ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ (n - k) * (n.choose (k + 1) : ℂ) * h (a + 1 + (k : ℝ)))
      = -(∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ (n - j) * (n.choose j : ℂ) * h (a + (j : ℝ)))
        + (-1 : ℂ) ^ n * h a := by
    rw [Finset.sum_range_succ]
    have hz : (-1 : ℂ) ^ (n - n) * (n.choose (n + 1) : ℂ) * h (a + 1 + (n : ℝ)) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega)]; ring
    rw [hz, add_zero]
    have hT : ∀ k ∈ Finset.range n,
        (-1 : ℂ) ^ (n - k) * (n.choose (k + 1) : ℂ) * h (a + 1 + (k : ℝ))
        = - ((-1 : ℂ) ^ (n - (k + 1)) * (n.choose (k + 1) : ℂ) * h (a + ((k + 1 : ℕ) : ℝ))) := by
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hexp : n - k = (n - (k + 1)) + 1 := by omega
      have harg : a + ((k + 1 : ℕ) : ℝ) = a + 1 + (k : ℝ) := by push_cast; ring
      rw [harg, hexp, pow_succ]
      ring
    rw [Finset.sum_congr rfl hT, Finset.sum_neg_distrib]
    have hsplit : (∑ k ∈ Finset.range n,
        (-1 : ℂ) ^ (n - (k + 1)) * (n.choose (k + 1) : ℂ) * h (a + ((k + 1 : ℕ) : ℝ)))
        = (∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ (n - j) * (n.choose j : ℂ) * h (a + (j : ℝ)))
          - (-1 : ℂ) ^ n * h a := by
      have hs := Finset.sum_range_succ'
        (fun j : ℕ => (-1 : ℂ) ^ (n - j) * (n.choose j : ℂ) * h (a + (j : ℝ))) n
      have hg0 : (-1 : ℂ) ^ (n - 0) * (n.choose 0 : ℂ) * h (a + ((0 : ℕ) : ℝ)) = (-1 : ℂ) ^ n * h a := by
        simp
      rw [eq_sub_iff_add_eq, ← hg0, ← hs]
    rw [hsplit]
    ring
  rw [hstepA, hstepB, hstepC]
  ring

/-- The discrete mean value estimate: the `n`-th forward difference of `h` at `a` is bounded
by any upper bound `B` for `‖h^{(n)}‖` on `[a, a+n]`. -/
private theorem fdiff_one_dim_aux (n : ℕ) : ∀ (h : ℝ → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h →
    ∀ (a B : ℝ), (∀ s ∈ Set.Icc a (a + n), ‖iteratedDeriv n h s‖ ≤ B) →
      ‖∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ (n - j) * (n.choose j : ℂ) * h (a + (j : ℝ))‖ ≤ B := by
  induction n with
  | zero =>
      intro h hh a B hB
      have h0 : (∑ j ∈ Finset.range (0 + 1),
          (-1 : ℂ) ^ (0 - j) * (Nat.choose 0 j : ℂ) * h (a + (j : ℝ))) = h a := by
        simp
      rw [h0]
      simpa using hB a (by simp)
  | succ n ih =>
      intro h hh a B hB
      rw [fd_recur n h a]
      set F : ℝ → ℂ := fun s => ∑ j ∈ Finset.range (n + 1),
        (-1 : ℂ) ^ (n - j) * (Nat.choose n j : ℂ) * h (s + (j : ℝ)) with hF
      have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
      have hFderiv : ∀ s : ℝ, HasDerivAt F
          (∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ (n - j) * (Nat.choose n j : ℂ) * deriv h (s + (j : ℝ))) s := by
        intro s
        rw [hF]
        exact HasDerivAt.fun_sum (fun j hj => by
          have h1 : HasDerivAt (fun u : ℝ => h (u + (j : ℝ))) (deriv h (s + (j : ℝ))) s :=
            (((hh.differentiable hn) (s + (j : ℝ))).hasDerivAt).comp_add_const s (j : ℝ)
          simpa using h1.const_mul ((-1 : ℂ) ^ (n - j) * (Nat.choose n j : ℂ)))
      have hmvt : ‖F (a + 1) - F a‖ ≤ B := by
        have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := F) (a := a) (b := a + 1)
          (f' := fun s => ∑ j ∈ Finset.range (n + 1),
            (-1 : ℂ) ^ (n - j) * (Nat.choose n j : ℂ) * deriv h (s + (j : ℝ)))
          (C := B) (fun x hx => (hFderiv x).hasDerivWithinAt) (fun x hx => by
            have hx1 : a ≤ x := hx.1
            have hx2 : x < a + 1 := hx.2
            refine ih (deriv h) ((contDiff_infty_iff_deriv.mp hh).2) x B (fun s hs => ?_)
            have hs1 : s ∈ Set.Icc a (a + ((n + 1 : ℕ) : ℝ)) := by
              refine ⟨le_trans hx1 hs.1, ?_⟩
              have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
              rw [this]; linarith [hs.2]
            rw [← iteratedDeriv_succ']
            exact hB s hs1)
        have h1 := h (a + 1) ⟨by linarith, by linarith⟩
        simpa using h1
      simpa only [hF] using hmvt

/-- One-dimensional finite-difference estimate in the exact form used below. -/
private theorem fdiff_one_dim_le {n : ℕ} {h : ℝ → ℂ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {a B : ℝ} (hB : ∀ s ∈ Set.Icc a (a + n), ‖iteratedDeriv n h s‖ ≤ B) :
    ‖∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ (n - j) * (n.choose j : ℂ) * h (a + j)‖ ≤ B :=
  fdiff_one_dim_aux n h hh a B hB

/-! ## The `L²` bound for the `N`-th finite difference -/

theorem fdiff_lp_le {g : ℂ → ℂ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hs : HasCompactSupport g)
    (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ,
      MeasureTheory.eLpNorm (fun z => ∑ j ∈ Finset.range (N+1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t))
        2 (MeasureTheory.volume : MeasureTheory.Measure ℂ) ≤ ENNReal.ofReal (C * ‖t‖ ^ N) := by
  obtain ⟨K, hK0, hK⟩ := hs.exists_bound_iteratedFDeriv hg N
  have hfinite : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport g) ≠ ⊤ :=
    (IsCompact.measure_lt_top hs).ne
  refine ⟨K * Real.sqrt (((N + 1 : ℕ) : ℝ) *
      ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport g)).toReal), ?_, ?_⟩
  · exact mul_nonneg hK0 (Real.sqrt_nonneg _)
  · intro t
    have hcont : Continuous (fun z : ℂ =>
        ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t)) := by
      refine continuous_finsetSum _ (fun j hj => ?_)
      exact continuous_const.mul (hg.continuous.comp (continuous_id.sub continuous_const))
    have hbound : ∀ z : ℂ,
        ‖∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t)‖
          ≤ K * ‖t‖ ^ N := by
      intro z
      have hCd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => g (z - u • t)) :=
        hg.comp (contDiff_const.sub (ContinuousLinearMap.contDiff (ContinuousLinearMap.toSpanSingleton ℝ t)))
      have hB : ∀ s ∈ Set.Icc (0 : ℝ) (0 + (N : ℝ)),
          ‖iteratedDeriv N (fun u : ℝ => g (z - u • t)) s‖ ≤ K * ‖t‖ ^ N := by
        intro s hs
        exact norm_iteratedDeriv_affine_le hg N (fun w => hK N le_rfl w) z t s
      have hmain := fdiff_one_dim_le (n := N) (h := fun u : ℝ => g (z - u • t)) hCd
        (a := (0 : ℝ)) (B := K * ‖t‖ ^ N) hB
      rw [show (∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t))
            = (∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ)
                * (fun u : ℝ => g (z - u • t)) (0 + j)) from by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            simp [Complex.real_smul]]
      exact hmain
    set S : Set ℂ := ⋃ j ∈ Finset.range (N + 1), {z : ℂ | z - (j : ℂ) * t ∈ tsupport g} with hSdef
    have hSclosed : IsClosed S := by
      rw [hSdef]
      exact (Finset.finite_toSet _).isClosed_biUnion
        (fun j hj => (isClosed_tsupport g).preimage (continuous_id.sub continuous_const))
    have hzero' : ∀ z : ℂ, z ∉ S →
        (∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t)) = 0 := by
      intro z hz
      refine Finset.sum_eq_zero (fun j hj => ?_)
      have hnot : z - (j : ℂ) * t ∉ tsupport g := fun hmem => hz (by
        rw [hSdef]; exact Set.mem_biUnion hj hmem)
      rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
    have hmeas : (MeasureTheory.volume : MeasureTheory.Measure ℂ) S
        ≤ ENNReal.ofReal (((N + 1 : ℕ) : ℝ) *
            ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport g)).toReal) := by
      rw [hSdef]
      calc (MeasureTheory.volume : MeasureTheory.Measure ℂ)
              (⋃ j ∈ Finset.range (N + 1), {z : ℂ | z - (j : ℂ) * t ∈ tsupport g})
          ≤ ∑ j ∈ Finset.range (N + 1),
              (MeasureTheory.volume : MeasureTheory.Measure ℂ) {z : ℂ | z - (j : ℂ) * t ∈ tsupport g} :=
            measure_biUnion_finset_le _ _
        _ = ∑ j ∈ Finset.range (N + 1), (MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport g) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            have h1 : {z : ℂ | z - (j : ℂ) * t ∈ tsupport g}
                = (fun h : ℂ => h + (-((j : ℂ) * t))) ⁻¹' tsupport g := by
              ext z; simp [Set.mem_preimage, sub_eq_add_neg]
            rw [h1, measure_preimage_add_right]
        _ = ((N + 1 : ℕ) : ENNReal) * (MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport g) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = ENNReal.ofReal (((N + 1 : ℕ) : ℝ) *
              ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport g)).toReal) := by
            rw [show ((N + 1 : ℕ) : ENNReal) = ENNReal.ofReal (((N + 1 : ℕ) : ℝ)) by
              rw [ENNReal.ofReal_natCast]]
            conv_lhs => rw [← ENNReal.ofReal_toReal hfinite]
            rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity)]
    have hfinal := eLpNorm_le_of_support_measure
      (f := fun z : ℂ => ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ (N - j) * (N.choose j : ℂ) * g (z - (j : ℂ) * t))
      (S := S) (M := K * ‖t‖ ^ N)
      (V := ((N + 1 : ℕ) : ℝ) * ((MeasureTheory.volume : MeasureTheory.Measure ℂ) (tsupport g)).toReal)
      (mul_nonneg hK0 (pow_nonneg (norm_nonneg t) N))
      (mul_nonneg (by positivity) ENNReal.toReal_nonneg)
      hcont.aestronglyMeasurable hSclosed.measurableSet.nullMeasurableSet hzero' hbound hmeas
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hfinal

end Work.MRMT.Found
