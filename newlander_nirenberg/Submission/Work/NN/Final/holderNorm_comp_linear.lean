/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Control of the `C^{k,α}` norm under composition with a continuous linear map on the right

This file proves `Work.NN.Final.holderNorm_comp_linear`, the right-composition analogue of
`Work.CR.Flat.Holder.comp_linear_le`.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.comp_linear_le

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Final

open Work.CR.Flat

/-! ### Elementary real inequalities -/

/-- The quotient estimate underlying the Hölder part: if `N ≤ M * P ^ i` and `d ≤ P * r` with
`P, r, d > 0`, then `N / r ^ α ≤ P ^ (i + α) * (M / d ^ α)`. -/
lemma holder_quot_le {α : ℝ} (hα : 0 < α) (i : ℕ) {N M P r d : ℝ}
    (hNM : N ≤ M * P ^ i) (hM : 0 ≤ M) (hP : 0 < P) (hr : 0 < r) (hd : 0 < d)
    (hle : d ≤ P * r) :
    N / r ^ α ≤ P ^ ((i : ℝ) + α) * (M / d ^ α) := by
  have hrpow : 0 < r ^ α := Real.rpow_pos_of_pos hr _
  have hdpow : 0 < d ^ α := Real.rpow_pos_of_pos hd _
  have hdP : d ^ α ≤ P ^ α * r ^ α := by
    rw [← Real.mul_rpow hP.le hr.le]
    exact Real.rpow_le_rpow (by positivity) hle hα.le
  have hkey : M * P ^ i * d ^ α ≤ P ^ ((i : ℝ) + α) * M * r ^ α := by
    rw [Real.rpow_add hP, Real.rpow_natCast]
    calc M * P ^ i * d ^ α ≤ M * P ^ i * (P ^ α * r ^ α) :=
          mul_le_mul_of_nonneg_left hdP (by positivity)
      _ = P ^ i * P ^ α * M * r ^ α := by ring
  calc N / r ^ α ≤ M * P ^ i / r ^ α := div_le_div_of_nonneg_right hNM hrpow.le
    _ ≤ P ^ ((i : ℝ) + α) * M / d ^ α := (div_le_div_iff₀ hrpow hdpow).mpr hkey
    _ = P ^ ((i : ℝ) + α) * (M / d ^ α) := (mul_div_assoc' _ _ _).symm

/-- The `i`-th (natural) power is bounded by `max 1 (P ^ (k + α))` when `i ≤ k` and `α ≥ 0`. -/
lemma rpow_nat_pow_le_max {P : ℝ} (hP : 0 ≤ P) {i k : ℕ} {α : ℝ} (hα : 0 ≤ α) (hik : i ≤ k) :
    P ^ i ≤ max 1 (P ^ ((k : ℝ) + α)) := by
  by_cases h1 : P ≤ 1
  · exact le_trans (pow_le_one₀ hP h1) (le_max_left _ _)
  · have h1' : 1 ≤ P := le_of_lt (not_le.mp h1)
    rw [← Real.rpow_natCast]
    refine le_trans (Real.rpow_le_rpow_of_exponent_le h1' ?_) (le_max_right _ _)
    have hik' : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
    linarith

/-- The `(i + α)`-th (real) power is bounded by `max 1 (P ^ (k + α))` when `i ≤ k`
and `α ≥ 0`. -/
lemma rpow_add_le_max {P : ℝ} (hP : 0 ≤ P) {i k : ℕ} {α : ℝ} (hα : 0 ≤ α) (hik : i ≤ k) :
    P ^ ((i : ℝ) + α) ≤ max 1 (P ^ ((k : ℝ) + α)) := by
  by_cases h1 : 1 ≤ P
  · refine le_trans (Real.rpow_le_rpow_of_exponent_le h1 ?_) (le_max_right _ _)
    have hik' : (i : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hik
    linarith
  · refine le_trans (Real.rpow_le_one hP (le_of_lt (not_le.mp h1)) ?_) (le_max_left _ _)
    have hik' : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith

/-! ### Derivatives of a composition with a continuous linear map on the right -/

/-- `compContinuousLinearMap` is additive in the multilinear map.  (Mathlib bundles linearity
in the family of linear maps, but not, as a `ContinuousLinearMap`, in the multilinear map.) -/
lemma compContinuousLinearMap_sub {ι : Type*} [Fintype ι]
    {E : ι → Type*} {E₁ : ι → Type*} {G : Type*}
    [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, SeminormedAddCommGroup (E₁ i)] [∀ i, NormedSpace ℝ (E₁ i)]
    (g₁ g₂ : ContinuousMultilinearMap ℝ E₁ G) (f : ∀ i, E i →L[ℝ] E₁ i) :
    (g₁ - g₂).compContinuousLinearMap f
      = g₁.compContinuousLinearMap f - g₂.compContinuousLinearMap f := by
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- The norm of the `i`-th iterated derivative of `u ∘ Φ` at `x` is bounded by `‖Φ‖ ^ i` times
the norm of the `i`-th iterated derivative of `u` at `Φ x`. -/
lemma norm_iteratedFDerivWithin_comp_right_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E →L[ℝ] F) (i : ℕ) (m : WithTop ℕ∞) {u : F → ℂ} {s : Set F}
    (hu : ContDiffOn ℝ m u s) (hs : UniqueDiffOn ℝ s) (hs' : UniqueDiffOn ℝ (Φ ⁻¹' s))
    (hin : (i : WithTop ℕ∞) ≤ m) {x : E} (hx : x ∈ Φ ⁻¹' s) :
    ‖iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) x‖
      ≤ ‖iteratedFDerivWithin ℝ i u s (Φ x)‖ * ‖Φ‖ ^ i := by
  have h := Φ.iteratedFDerivWithin_comp_right hu hs hs' hx hin
  rw [show (u ∘ ⇑Φ) = (fun z => u (Φ z)) from rfl] at h
  rw [h]
  calc ‖(iteratedFDerivWithin ℝ i u s (Φ x)).compContinuousLinearMap (fun _ => Φ)‖
      ≤ ‖iteratedFDerivWithin ℝ i u s (Φ x)‖ * ∏ _ : Fin i, ‖Φ‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = ‖iteratedFDerivWithin ℝ i u s (Φ x)‖ * ‖Φ‖ ^ i := by simp

/-- The norm of a difference of `i`-th iterated derivatives of `u ∘ Φ` is bounded by `‖Φ‖ ^ i`
times the norm of the corresponding difference for `u`. -/
lemma norm_iteratedFDerivWithin_comp_right_sub_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E →L[ℝ] F) (i : ℕ) (m : WithTop ℕ∞) {u : F → ℂ} {s : Set F}
    (hu : ContDiffOn ℝ m u s) (hs : UniqueDiffOn ℝ s) (hs' : UniqueDiffOn ℝ (Φ ⁻¹' s))
    (hin : (i : WithTop ℕ∞) ≤ m) {x y : E} (hx : x ∈ Φ ⁻¹' s) (hy : y ∈ Φ ⁻¹' s) :
    ‖iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) x
        - iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) y‖
      ≤ ‖iteratedFDerivWithin ℝ i u s (Φ x) - iteratedFDerivWithin ℝ i u s (Φ y)‖
          * ‖Φ‖ ^ i := by
  have hx' := Φ.iteratedFDerivWithin_comp_right hu hs hs' hx hin
  have hy' := Φ.iteratedFDerivWithin_comp_right hu hs hs' hy hin
  rw [show (u ∘ ⇑Φ) = (fun z => u (Φ z)) from rfl] at hx' hy'
  rw [hx', hy', ← compContinuousLinearMap_sub]
  calc ‖(iteratedFDerivWithin ℝ i u s (Φ x)
        - iteratedFDerivWithin ℝ i u s (Φ y)).compContinuousLinearMap (fun _ => Φ)‖
      ≤ ‖iteratedFDerivWithin ℝ i u s (Φ x)
        - iteratedFDerivWithin ℝ i u s (Φ y)‖ * ∏ _ : Fin i, ‖Φ‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ = _ := by simp

/-! ### The two halves of the `C^{k,α}` norm -/

/-- The `C^i` piece of the `C^{k,α}` norm: the sup-norm of the `i`-th derivative of `u ∘ Φ` on
`Φ ⁻¹' s` is at most `‖Φ‖ ^ i` times that of `u` on `s`. -/
lemma iterDerivNorm_comp_right_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E →L[ℝ] F) (i : ℕ) (m : WithTop ℕ∞) {u : F → ℂ} {s : Set F}
    (hu : ContDiffOn ℝ m u s) (hs : UniqueDiffOn ℝ s) (hs' : UniqueDiffOn ℝ (Φ ⁻¹' s))
    (hin : (i : WithTop ℕ∞) ≤ m) :
    iterDerivNorm i (fun z => u (Φ z)) (Φ ⁻¹' s)
      ≤ ENNReal.ofReal (‖Φ‖ ^ i) * iterDerivNorm i u s := by
  refine iSup₂_le fun x hx => ?_
  calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) x‖
      ≤ ENNReal.ofReal (‖iteratedFDerivWithin ℝ i u s (Φ x)‖ * ‖Φ‖ ^ i) :=
        ENNReal.ofReal_le_ofReal (norm_iteratedFDerivWithin_comp_right_le Φ i m hu hs hs' hin hx)
    _ = ENNReal.ofReal (‖Φ‖ ^ i) * ENNReal.ofReal ‖iteratedFDerivWithin ℝ i u s (Φ x)‖ := by
        rw [mul_comm ‖iteratedFDerivWithin ℝ i u s (Φ x)‖,
          ENNReal.ofReal_mul (pow_nonneg (norm_nonneg Φ) i)]
    _ ≤ ENNReal.ofReal (‖Φ‖ ^ i) * iterDerivNorm i u s :=
        mul_le_mul_right (le_iterDerivNorm i u s hx) _

/-- The `C^{i,α}` piece of the `C^{k,α}` norm: the Hölder seminorm of order `α` of the `i`-th
derivative of `u ∘ Φ` on `Φ ⁻¹' s` is at most `‖Φ‖ ^ (i + α)` times that of `u` on `s`. -/
lemma holderSeminorm_comp_right_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E →L[ℝ] F) (i : ℕ) (m : WithTop ℕ∞) {α : ℝ} (hα : 0 < α) {u : F → ℂ} {s : Set F}
    (hu : ContDiffOn ℝ m u s) (hs : UniqueDiffOn ℝ s) (hs' : UniqueDiffOn ℝ (Φ ⁻¹' s))
    (hin : (i : WithTop ℕ∞) ≤ m) :
    holderSeminorm i α (fun z => u (Φ z)) (Φ ⁻¹' s)
      ≤ ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α)) * holderSeminorm i α u s := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  by_cases hxy' : Φ x = Φ y
  · have hDx := Φ.iteratedFDerivWithin_comp_right hu hs hs' hx hin
    have hDy := Φ.iteratedFDerivWithin_comp_right hu hs hs' hy hin
    rw [show (u ∘ ⇑Φ) = (fun z => u (Φ z)) from rfl] at hDx hDy
    have hz : iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) x
        - iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) y = 0 := by
      rw [hDx, hDy, hxy', sub_self]
    rw [hz, norm_zero, zero_div, ENNReal.ofReal_zero]
    exact bot_le
  · have hle : ‖Φ x - Φ y‖ ≤ ‖Φ‖ * ‖x - y‖ := by
      simpa using Φ.le_opNorm (x - y)
    have hr : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hd : 0 < ‖Φ x - Φ y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy')
    have hP : 0 < ‖Φ‖ := by
      by_contra h
      have h0 : ‖Φ‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg Φ)
      rw [h0, zero_mul] at hle
      linarith
    have hNM := norm_iteratedFDerivWithin_comp_right_sub_le Φ i m hu hs hs' hin hx hy
    calc ENNReal.ofReal (‖iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) x
            - iteratedFDerivWithin ℝ i (fun z => u (Φ z)) (Φ ⁻¹' s) y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α)
            * (‖iteratedFDerivWithin ℝ i u s (Φ x) - iteratedFDerivWithin ℝ i u s (Φ y)‖
              / ‖Φ x - Φ y‖ ^ α)) :=
          ENNReal.ofReal_le_ofReal
            (holder_quot_le hα i hNM (norm_nonneg _) hP hr hd hle)
      _ = ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α))
            * ENNReal.ofReal (‖iteratedFDerivWithin ℝ i u s (Φ x)
              - iteratedFDerivWithin ℝ i u s (Φ y)‖ / ‖Φ x - Φ y‖ ^ α) :=
          ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg Φ) _)
      _ ≤ ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α)) * holderSeminorm i α u s :=
          mul_le_mul_right (le_holderSeminorm i α u s hx hy hxy') _

/-! ### The main statement -/

/-- **Control of the `C^{k,α}` norm under composition with a continuous linear map on the
right.**  Dually to `Work.CR.Flat.Holder.comp_linear_le` (which handles `L ∘ φ` for a continuous
linear `L`), here the *argument* is transformed by a continuous linear `Φ`:

  `‖u ∘ Φ‖_{C^{k,α}(Φ ⁻¹' t)} ≤ C · ‖u‖_{C^{k,α}(t)}`.

The constant `C` depends on `k`, `α`, `n` and `‖Φ‖` (a valid choice is
`(k+1) * max 1 ‖Φ‖ ^ (k+α)`), not on `u`.  Proof: Mathlib's
`ContinuousLinearMap.iteratedFDerivWithin_comp_right` gives
`iteratedFDerivWithin ℝ i (u ∘ Φ) (Φ ⁻¹' t) x
   = (iteratedFDerivWithin ℝ i u t (Φ x)).compContinuousLinearMap (fun _ => Φ)`,
so both the iterated-derivative norms and their differences acquire at most a factor
`‖Φ‖ ^ i` (via `ContinuousMultilinearMap.norm_compContinuousLinearMap_le` and the linearity of
`compContinuousLinearMap` in its argument — the same computation as in `comp_linear_le`), while
the Hölder denominator gains `‖Φ‖ ^ α` from `‖Φ x - Φ y‖ ≤ ‖Φ‖ ‖x - y‖`.  This is the piece of
scaling bookkeeping needed to transfer estimates between nested polydiscs of different
multi-radii via the diagonal map `z ↦ (i ↦ σ i * z i)`. -/
theorem holderNorm_comp_linear {n : ℕ} (k : ℕ) {α : ℝ} (hα : 0 < α)
    (Φ : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) {t : Set (Fin n → ℂ)} (ht : IsOpen t) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin n → ℂ) → ℂ, ContDiffOn ℝ k u t →
      Work.CR.Flat.holderNorm k α (fun z => u (Φ z)) (Φ ⁻¹' t)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α u t := by
  refine ⟨max 1 (‖Φ‖ ^ ((k : ℝ) + α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  have hsd : UniqueDiffOn ℝ t := ht.uniqueDiffOn
  have hpd : UniqueDiffOn ℝ (Φ ⁻¹' t) := (ht.preimage Φ.continuous).uniqueDiffOn
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hik' : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hik
  have hfac1 : ENNReal.ofReal (‖Φ‖ ^ i) ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) :=
    ENNReal.ofReal_le_ofReal (rpow_nat_pow_le_max (norm_nonneg Φ) hα.le hik)
  have hfac2 : ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α))
      ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) :=
    ENNReal.ofReal_le_ofReal (rpow_add_le_max (norm_nonneg Φ) hα.le hik)
  rw [mul_add]
  refine add_le_add ?_ ?_
  · exact le_trans (iterDerivNorm_comp_right_le Φ i (k : WithTop ℕ∞) hu hsd hpd hik')
      (mul_le_mul_left hfac1 _)
  · exact le_trans (holderSeminorm_comp_right_le Φ i (k : WithTop ℕ∞) hα hu hsd hpd hik')
      (mul_le_mul_left hfac2 _)

end Work.NN.Final
