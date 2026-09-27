import Mathlib

/-!
# Extension of a smooth family of linear equivalences fixing a family of vectors

This file proves `Work.Drive.Whitney.stabilizerExtension`.

Let `E := EuclideanSpace ℝ (Fin m)`, let `k ≤ m` and let `b_0, …, b_{k-1}` be the first `k`
standard basis vectors of `E`.  Given a smooth family `A : ℝ → E ≃L[ℝ] E` which fixes each `b_i`
for `t ∈ [0,1]`, we produce a smooth family `Ã : ℝ → E ≃L[ℝ] E` with `Ã t = A t` for `t ∈ [0,1]`
and `Ã t b_i = b_i` for *all* `t : ℝ` and all `i < k`.

The construction has three ingredients.

* `contDiff_extend_Icc`: a smooth extension of a smooth map `f : ℝ → F` from the interval `[0,1]`
  to all of `ℝ`, *quantitatively* controlled: outside `[0,1]` the values stay within the prescribed
  distance of the two anchor values `f 0` and `f 1`.  This is the smooth Tietze device; it is the
  statement that makes "the image of `[0,1]` is compact, so a neighbourhood of it still lies in the
  open set `GL(E)`" effective.

* `stabCorr` (with `stabCorrLin`, `stabCorrCst`): the affine projection of `E →L[ℝ] E` onto the
  affine subspace of endomorphisms fixing all the `w i`.  Its linear part `stabCorrLin` is a
  continuous linear map, and `stabCorr w Z = Z` as soon as `Z` fixes all `w i`.

* the assembly: extend `A` to a smooth family `g` of *units* of `E →L[ℝ] E` (the target of the
  Tietze step is the open set `{Z | IsUnit Z}`, using `Units.isOpen`), then correct it by
  `stabCorr`.  Because the correction is affine with linear part `stabCorrLin`, and because `g`
  never leaves the prescribed balls around `A 0` and `A 1` (which are contained in the units), the
  corrected family consists of units as well.
-/

namespace Work.Drive.Whitney

open scoped Topology

noncomputable section

/-! ## 1. A smooth extension from `[0,1]` with quantitative control -/

/-- **Smooth extension of a smooth map from `[0,1]` to `ℝ`, quantitatively controlled.**

Let `F` be a normed space over `ℝ`, `f : ℝ → F` a `C^∞` map, `ε : ℝ` and `δ > 0`.  Assume that `f`
does not move by more than `ε` near `0` (on `[-δ,0]`) and near `1` (on `[1,1+δ]`).  Then there is a
`C^∞` map `g : ℝ → F` with `g = f` on `[0,1]`, with `dist (g t) (f 0) < ε` for all `t ≤ 0` and with
`dist (g t) (f 1) < ε` for all `t ≥ 1`.

The construction is the explicit blend
`g t = f t + σ(-t/δ) • (f 0 - f t) + σ((t-1)/δ) • (f 1 - f t)`
with `σ = Real.smoothTransition` (`σ = 0` on `(-∞,0]` and `σ = 1` on `[1,∞)`): on `[0,1]` the two
correction terms vanish and `g = f`; off `[0,1]` each correction term is a convex combination of
`f t` with an anchor, so the values stay close to that anchor. -/
theorem contDiff_extend_Icc {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) {ε δ : ℝ} (hδ : 0 < δ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (h0 : ∀ t ∈ Set.Icc (-δ) 0, dist (f t) (f 0) < ε)
    (h1 : ∀ t ∈ Set.Icc 1 (1 + δ), dist (f t) (f 1) < ε) :
    ∃ g : ℝ → F, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, g t = f t) ∧
      (∀ t, t ≤ 0 → dist (g t) (f 0) < ε) ∧
      (∀ t, 1 ≤ t → dist (g t) (f 1) < ε) := by
  have hε : 0 < ε := by
    have h := h0 0 (Set.mem_Icc.mpr ⟨by linarith, le_refl 0⟩)
    simpa using h
  have hσc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.smoothTransition ((-t) / δ)) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp ((contDiff_id.neg).div_const δ)
  have hτc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.smoothTransition ((t - 1) / δ)) :=
    (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_id.sub contDiff_const).div_const δ)
  have hGc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
        + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t)) :=
    (hf.add (hσc.smul (contDiff_const.sub hf))).add (hτc.smul (contDiff_const.sub hf))
  refine ⟨fun t : ℝ => f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
      + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t), hGc, ?_, ?_, ?_⟩
  · intro t ht
    have hσ0 : Real.smoothTransition ((-t) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) hδ.le)
    have hτ0 : Real.smoothTransition ((t - 1) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith [ht.2]) hδ.le)
    simp [hσ0, hτ0]
  · intro t ht
    have hτ0 : Real.smoothTransition ((t - 1) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    have hsub : f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
        + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t) - f 0
        = (1 - Real.smoothTransition ((-t) / δ)) • (f t - f 0) := by
      rw [hτ0, zero_smul, add_zero]
      module
    have hb : ‖1 - Real.smoothTransition ((-t) / δ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [Real.smoothTransition.le_one ((-t) / δ)],
        by linarith [Real.smoothTransition.nonneg ((-t) / δ)]⟩
    by_cases hcase : -δ ≤ t
    · have hd := h0 t (Set.mem_Icc.mpr ⟨hcase, ht⟩)
      calc dist (f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
              + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t)) (f 0)
          = ‖f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
              + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t) - f 0‖ := dist_eq_norm _ _
        _ = ‖1 - Real.smoothTransition ((-t) / δ)‖ * ‖f t - f 0‖ := by
              rw [hsub, norm_smul]
        _ ≤ 1 * ‖f t - f 0‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = ‖f t - f 0‖ := one_mul _
        _ = dist (f t) (f 0) := (dist_eq_norm _ _).symm
        _ < ε := hd
    · have hlt : t < -δ := lt_of_not_ge hcase
      have h3 : Real.smoothTransition ((-t) / δ) = 1 := by
        refine Real.smoothTransition.one_of_one_le ?_
        rw [le_div_iff₀ hδ]
        linarith
      calc dist (f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
              + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t)) (f 0)
          = ‖1 - Real.smoothTransition ((-t) / δ)‖ * ‖f t - f 0‖ := by
              rw [dist_eq_norm, hsub, norm_smul]
        _ = 0 := by rw [h3]; simp
        _ < ε := hε
  · intro t ht
    have hσ0 : Real.smoothTransition ((-t) / δ) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
    have hsub : f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
        + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t) - f 1
        = (1 - Real.smoothTransition ((t - 1) / δ)) • (f t - f 1) := by
      rw [hσ0, zero_smul, add_zero]
      module
    have hb : ‖1 - Real.smoothTransition ((t - 1) / δ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [Real.smoothTransition.le_one ((t - 1) / δ)],
        by linarith [Real.smoothTransition.nonneg ((t - 1) / δ)]⟩
    by_cases hcase : t ≤ 1 + δ
    · have hd := h1 t (Set.mem_Icc.mpr ⟨ht, hcase⟩)
      calc dist (f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
              + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t)) (f 1)
          = ‖f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
              + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t) - f 1‖ := dist_eq_norm _ _
        _ = ‖1 - Real.smoothTransition ((t - 1) / δ)‖ * ‖f t - f 1‖ := by
              rw [hsub, norm_smul]
        _ ≤ 1 * ‖f t - f 1‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
        _ = ‖f t - f 1‖ := one_mul _
        _ = dist (f t) (f 1) := (dist_eq_norm _ _).symm
        _ < ε := hd
    · have hgt : 1 + δ < t := lt_of_not_ge hcase
      have h3 : Real.smoothTransition ((t - 1) / δ) = 1 := by
        refine Real.smoothTransition.one_of_one_le ?_
        rw [le_div_iff₀ hδ]
        linarith
      calc dist (f t + Real.smoothTransition ((-t) / δ) • (f 0 - f t)
              + Real.smoothTransition ((t - 1) / δ) • (f 1 - f t)) (f 1)
          = ‖1 - Real.smoothTransition ((t - 1) / δ)‖ * ‖f t - f 1‖ := by
              rw [dist_eq_norm, hsub, norm_smul]
        _ = 0 := by rw [h3]; simp
        _ < ε := hε

/-! ## 2. The affine projection onto the endomorphisms fixing a family of vectors -/

section Corr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The linear part of the affine projection onto the endomorphisms fixing the `w i`.**

`stabCorrLin w Z = Z - ∑ i, (fun x => ⟪w i, x⟫) • (Z (w i))`; it is continuous linear in `Z`. -/
def stabCorrLin (w : ι → E) : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.id ℝ (E →L[ℝ] E) -
    ∑ i : ι, (ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ (w i))) ∘L
      ((ContinuousLinearMap.apply ℝ E) (w i))

/-- **The constant part of the affine projection onto the endomorphisms fixing the `w i`.**

`stabCorrCst w = ∑ i, (fun x => ⟪w i, x⟫) • (w i)`. -/
def stabCorrCst (w : ι → E) : E →L[ℝ] E :=
  ∑ i : ι, (ContinuousLinearMap.smulRightL ℝ E E (innerSL ℝ (w i))) (w i)

/-- **The affine projection onto the endomorphisms fixing the `w i`:**
`Z ↦ Z + ∑ i, ⟪w i, ·⟫ • (w i - Z (w i))`. -/
def stabCorr (w : ι → E) (Z : E →L[ℝ] E) : E →L[ℝ] E := stabCorrLin w Z + stabCorrCst w

lemma stabCorrLin_apply (w : ι → E) (Z : E →L[ℝ] E) :
    stabCorrLin w Z = Z - ∑ i : ι, (innerSL ℝ (w i)).smulRight (Z (w i)) := by
  simp only [stabCorrLin, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.apply_apply]
  simp

lemma stabCorrCst_apply (w : ι → E) (x : E) :
    stabCorrCst w x = ∑ i : ι, inner ℝ (w i) x • w i := by
  simp only [stabCorrCst, sum_apply, ContinuousLinearMap.smulRightL_apply_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]

lemma stabCorr_apply_apply (w : ι → E) (Z : E →L[ℝ] E) (x : E) :
    stabCorr w Z x = Z x - ∑ i : ι, inner ℝ (w i) x • Z (w i)
      + ∑ i : ι, inner ℝ (w i) x • w i := by
  simp only [stabCorr, stabCorrLin_apply, stabCorrCst, sum_apply, add_apply, sub_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]

/-- `stabCorr w` fixes every endomorphism which already fixes all the `w i`. -/
lemma stabCorr_fix (w : ι → E) {Z : E →L[ℝ] E} (hZ : ∀ i, Z (w i) = w i) :
    stabCorr w Z = Z := by
  rw [stabCorr, stabCorrLin_apply, stabCorrCst]
  simp only [ContinuousLinearMap.smulRightL_apply_apply]
  rw [show (∑ i : ι, (innerSL ℝ (w i)).smulRight (Z (w i)))
      = ∑ i : ι, (innerSL ℝ (w i)).smulRight (w i) from
    Finset.sum_congr rfl fun i _ => by rw [hZ i]]
  rw [sub_add_cancel]

/-- **The image of `stabCorr w` consists of endomorphisms fixing all the `w i`** (assuming the
`w i` are orthonormal). -/
lemma stabCorr_apply_mem (w : ι → E)
    (horth : ∀ i j : ι, inner ℝ (w i) (w j) = if i = j then (1 : ℝ) else 0)
    (Z : E →L[ℝ] E) (j : ι) : stabCorr w Z (w j) = w j := by
  rw [stabCorr_apply_apply]
  have h1 : (∑ i : ι, inner ℝ (w i) (w j) • Z (w i)) = Z (w j) := by
    rw [Finset.sum_eq_single j]
    · rw [horth j j, if_pos rfl, one_smul]
    · intro i _ hij
      rw [horth i j, if_neg hij, zero_smul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h2 : (∑ i : ι, inner ℝ (w i) (w j) • w i) = w j := by
    rw [Finset.sum_eq_single j]
    · rw [horth j j, if_pos rfl, one_smul]
    · intro i _ hij
      rw [horth i j, if_neg hij, zero_smul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [h1, h2, sub_self, zero_add]

/-- The difference of two values of `stabCorr` depends only on the difference of the arguments. -/
lemma stabCorr_sub (w : ι → E) (Z Z' : E →L[ℝ] E) :
    stabCorr w Z - stabCorr w Z' = stabCorrLin w (Z - Z') := by
  simp only [stabCorr]
  rw [map_sub]
  abel

/-- The Lipschitz estimate for `stabCorr`. -/
lemma norm_stabCorr_sub (w : ι → E) (Z Z' : E →L[ℝ] E) :
    ‖stabCorr w Z - stabCorr w Z'‖ ≤ ‖stabCorrLin w‖ * ‖Z - Z'‖ := by
  rw [stabCorr_sub]
  exact ContinuousLinearMap.le_opNorm _ _

/-- The coercion to continuous linear maps of `ContinuousLinearEquiv.unitsEquiv` is the unit itself. -/
lemma unitsEquiv_coe (u : (E →L[ℝ] E)ˣ) :
    ((ContinuousLinearEquiv.unitsEquiv ℝ E u) : E →L[ℝ] E) = ↑u :=
  ContinuousLinearMap.ext fun x => ContinuousLinearEquiv.unitsEquiv_apply ℝ E u x

end Corr

/-! ## 3. The extension theorem -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Extension of a smooth family of linear equivalences fixing an orthonormal family.**

Let `w : ι → E` be an orthonormal family in a complete real inner product space `E`, let
`A : ℝ → E ≃L[ℝ] E` be a smooth family of linear equivalences which fixes every `w i` on the
interval `[0,1]`.  Then `A|[0,1]` extends to a smooth family `Ã : ℝ → E ≃L[ℝ] E` which fixes every
`w i` on all of `ℝ`.

The proof: extend the smooth family `A` — viewed as a family of *units* of the ring `E →L[ℝ] E` —
from `[0,1]` to `ℝ` by the controlled smooth extension `contDiff_extend_Icc`, applied to the open
set `{Z | IsUnit Z}` (`Units.isOpen`); the extension is arranged to stay in prescribed balls around
`A 0` and `A 1`, which consist of units.  Then post-compose with the affine projection `stabCorr w`,
whose linear part is continuous linear: this does not destroy unit-ness (it is Lipschitz on the
balls) and it forces the fixing condition. -/
theorem exists_stabilizerExtension (w : ι → E)
    (horth : ∀ i j : ι, inner ℝ (w i) (w j) = if i = j then (1 : ℝ) else 0)
    (A : ℝ → E ≃L[ℝ] E)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (A t : E →L[ℝ] E)))
    (hAf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : ι, A t (w i) = w i) :
    ∃ Ã : ℝ → E ≃L[ℝ] E,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => (Ã t : E →L[ℝ] E)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Ã t = A t) ∧
      (∀ (t : ℝ) (i : ι), Ã t (w i) = w i) := by
  let f : ℝ → E →L[ℝ] E := fun t => (A t : E →L[ℝ] E)
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := hA
  have hunitA : ∀ t : ℝ, IsUnit (f t) :=
    fun t => (ContinuousLinearEquiv.toUnit (A t)).isUnit
  obtain ⟨η₀, hη₀pos, hη₀⟩ :=
    Metric.isOpen_iff.mp (Units.isOpen (R := E →L[ℝ] E)) (f 0) (hunitA 0)
  obtain ⟨η₁, hη₁pos, hη₁⟩ :=
    Metric.isOpen_iff.mp (Units.isOpen (R := E →L[ℝ] E)) (f 1) (hunitA 1)
  set η : ℝ := min η₀ η₁ with hηdef
  have hηpos : 0 < η := by rw [hηdef]; exact lt_min hη₀pos hη₁pos
  have hη0 : ∀ x : E →L[ℝ] E, dist x (f 0) < η → IsUnit x := by
    intro x hx
    exact hη₀ (Metric.mem_ball.mpr (lt_of_lt_of_le hx (by rw [hηdef]; exact min_le_left _ _)))
  have hη1 : ∀ x : E →L[ℝ] E, dist x (f 1) < η → IsUnit x := by
    intro x hx
    exact hη₁ (Metric.mem_ball.mpr (lt_of_lt_of_le hx (by rw [hηdef]; exact min_le_right _ _)))
  set C : ℝ := ‖stabCorrLin w‖ + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set ε : ℝ := η / C with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hηpos hCpos
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ > 0, ∀ t : ℝ, dist t 0 < δ → dist (f t) (f 0) < ε :=
    Metric.continuousAt_iff.mp (hf.continuous.continuousAt (x := (0 : ℝ))) ε hεpos
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ : ∃ δ > 0, ∀ t : ℝ, dist t 1 < δ → dist (f t) (f 1) < ε :=
    Metric.continuousAt_iff.mp (hf.continuous.continuousAt (x := (1 : ℝ))) ε hεpos
  set δ : ℝ := min δ₀ δ₁ / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδ0 : ∀ t ∈ Set.Icc (-δ) 0, dist (f t) (f 0) < ε := by
    intro t ht
    apply hδ₀
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonpos ht.2]
    have h2 : -t ≤ min δ₀ δ₁ / 2 := by rw [← hδdef]; linarith [ht.1]
    have h3 : min δ₀ δ₁ / 2 ≤ δ₀ / 2 := by linarith [min_le_left δ₀ δ₁]
    have h4 : δ₀ / 2 < δ₀ := by linarith
    linarith
  have hδ1 : ∀ t ∈ Set.Icc 1 (1 + δ), dist (f t) (f 1) < ε := by
    intro t ht
    apply hδ₁
    rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
    have h2 : t - 1 ≤ min δ₀ δ₁ / 2 := by rw [← hδdef]; linarith [ht.2]
    have h3 : min δ₀ δ₁ / 2 ≤ δ₁ / 2 := by linarith [min_le_right δ₀ δ₁]
    have h4 : δ₁ / 2 < δ₁ := by linarith
    linarith
  obtain ⟨g, hg, hgeq, hg0, hg1⟩ :=
    contDiff_extend_Icc (F := E →L[ℝ] E) (ε := ε) (δ := δ) f hδpos hf hδ0 hδ1
  have hfix0 : stabCorr w (f 0) = f 0 :=
    stabCorr_fix w (fun i => hAf 0 ⟨le_refl 0, zero_le_one⟩ i)
  have hfix1 : stabCorr w (f 1) = f 1 :=
    stabCorr_fix w (fun i => hAf 1 ⟨zero_le_one, le_refl 1⟩ i)
  have hηbound : ‖stabCorrLin w‖ * ε < η := by
    rw [hεdef, ← mul_div_assoc, div_lt_iff₀ hCpos]
    nlinarith [hηpos, norm_nonneg (stabCorrLin w), hCdef]
  have hunit : ∀ t : ℝ, IsUnit (stabCorr w (g t)) := by
    intro t
    rcases le_or_gt t 0 with ht0 | ht0
    · apply hη0
      rw [dist_eq_norm]
      calc ‖stabCorr w (g t) - f 0‖
          ≤ ‖stabCorrLin w‖ * ‖g t - f 0‖ := by
            rw [show stabCorr w (g t) - f 0 = stabCorrLin w (g t - f 0) from by
              conv_lhs => rw [← hfix0]
              exact stabCorr_sub w (g t) (f 0)]
            exact ContinuousLinearMap.le_opNorm _ _
        _ = ‖stabCorrLin w‖ * dist (g t) (f 0) := by rw [dist_eq_norm]
        _ ≤ ‖stabCorrLin w‖ * ε :=
            mul_le_mul_of_nonneg_left (le_of_lt (hg0 t ht0))
              (by positivity : (0:ℝ) ≤ ‖stabCorrLin w‖)
        _ < η := hηbound
    · rcases le_or_gt 1 t with ht1 | ht1
      · apply hη1
        rw [dist_eq_norm]
        calc ‖stabCorr w (g t) - f 1‖
            ≤ ‖stabCorrLin w‖ * ‖g t - f 1‖ := by
              rw [show stabCorr w (g t) - f 1 = stabCorrLin w (g t - f 1) from by
                conv_lhs => rw [← hfix1]
                exact stabCorr_sub w (g t) (f 1)]
              exact ContinuousLinearMap.le_opNorm _ _
          _ = ‖stabCorrLin w‖ * dist (g t) (f 1) := by rw [dist_eq_norm]
          _ ≤ ‖stabCorrLin w‖ * ε :=
              mul_le_mul_of_nonneg_left (le_of_lt (hg1 t ht1))
                (by positivity : (0:ℝ) ≤ ‖stabCorrLin w‖)
          _ < η := hηbound
      · have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht0, le_of_lt ht1⟩
        rw [hgeq t ht, stabCorr_fix w (fun i => hAf t ht i)]
        exact hunitA t
  have hÃc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => stabCorr w (g t)) := by
    rw [show (fun t : ℝ => stabCorr w (g t))
        = fun t : ℝ => stabCorrLin w (g t) + stabCorrCst w from funext fun t => rfl]
    exact ((stabCorrLin w).contDiff.comp hg).add contDiff_const
  have hcoe : ∀ t : ℝ,
      ((ContinuousLinearEquiv.unitsEquiv ℝ E ((hunit t).unit)) : E →L[ℝ] E) = stabCorr w (g t) := by
    intro t
    rw [unitsEquiv_coe, IsUnit.unit_spec]
  refine ⟨fun t : ℝ => ContinuousLinearEquiv.unitsEquiv ℝ E ((hunit t).unit), ?_, ?_, ?_⟩
  · rw [show (fun t : ℝ => ((ContinuousLinearEquiv.unitsEquiv ℝ E ((hunit t).unit)) :
        E →L[ℝ] E)) = fun t : ℝ => stabCorr w (g t) from funext hcoe]
    exact hÃc
  · intro t ht
    apply ContinuousLinearEquiv.coe_injective
    rw [unitsEquiv_coe, IsUnit.unit_spec, hgeq t ht]
    exact stabCorr_fix w (fun i => hAf t ht i)
  · intro t i
    change ((ContinuousLinearEquiv.unitsEquiv ℝ E ((hunit t).unit)) : E →L[ℝ] E) (w i) = w i
    rw [unitsEquiv_coe, IsUnit.unit_spec]
    exact stabCorr_apply_mem w horth (g t) i

end Main

/-- **Extension of a smooth `G`-valued family from `[0,1]` to `ℝ`.**

Let `E := EuclideanSpace ℝ (Fin m)`, `k ≤ m`, and let `G` be the set of linear equivalences of `E`
which fix each of the first `k` standard basis vectors `e_0, …, e_{k-1}`.

Then every smooth `G`-valued family on `[0,1]` extends to a smooth `G`-valued family on `ℝ`.

This is a "smooth Tietze for a compact interval into an open subset of a finite-dimensional normed
space": `G` is open in the affine space `{Z | Z e_i = e_i, i < k}` and the image of `[0,1]` is
compact, so a neighbourhood of that image still lies in `G`. -/
theorem stabilizerExtension {m k : ℕ} (hkm : k ≤ m)
    (A : ℝ → (EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (A t : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))))
    (hAf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin k,
      A t ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
        (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) :
    ∃ Ã : ℝ → (EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun t : ℝ => (Ã t : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Ã t = A t) ∧
      (∀ (t : ℝ) (i : Fin k),
        Ã t ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
          (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) := by
  refine exists_stabilizerExtension
    (fun i : Fin k => (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) ?_ A hA hAf
  intro i j
  have h := orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal
    (Fin.castLE hkm i) (Fin.castLE hkm j)
  simpa only [Fin.castLE_inj] using h

end

end Work.Drive.Whitney
