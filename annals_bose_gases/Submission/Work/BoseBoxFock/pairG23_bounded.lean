import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KsubStateAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairG23_bounded` — the block II.2 fibre is bounded

The fibre `pairG23 p Θ A B w₀ w₁` of the FS `Q₂` row (`pairRowGDefs`) is a *triple* integral

    ∫ x' ∫ y ∫ u  star (Θ z) * star (A y) * star (B u) * Θ (update (update z p.1 y) p.2 u) ,
    z = insertCoord2 p w₀ w₁ x' ,

over the *unbounded* configuration spaces `({k // k ≠ p.1 ∧ k ≠ p.2} → E3)`, `E3`, `E3`.  It is
nevertheless bounded uniformly in the two kernel variables `w₀`, `w₁`, and this module proves it.

The mechanism is purely support-theoretic, exactly as in `pairG_supports`:

* the factor `Θ (insertCoord2 p w₀ w₁ x')` forces every *free* coordinate `x' k` into the
  one-particle box `boxL ℓ`;
* the factor `Θ (update (update z p.1 y) p.2 u)` forces `y` and `u` into `boxL ℓ`.

So the integrand is supported in the *finite-measure* set
`B' ×ˢ (boxL ℓ × boxL ℓ) ⊆ ({k // …} → E3) × E3 × E3` and is bounded by
`(sup ‖Θ‖)² sup ‖A‖ sup ‖B‖` there.  The proof extracts this bound one integral at a time, using
`MeasureTheory.norm_setIntegral_le_of_norm_le_const` (which needs no measurability of the
integrand), and rewrites each iterated integral over the whole space as a set integral over the box
through `integral_indicator`.

No hypothesis on `Θ`, `A`, `B` beyond a uniform bound and `support Θ ⊆ boxPow n ℓ` is used; in
particular measurability is *not* needed.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `insertCoord2` inserts the values `w₀`, `w₁` at the slots `p.1`, `p.2`: for an index `k`
which is neither `p.1` nor `p.2` the inserted configuration agrees with the free fibre. -/
private lemma insertCoord2_apply_of_ne {n : ℕ} (p : Fin n × Fin n) (w₀ w₁ : E3)
    (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)
    (k : Fin n) (hk1 : k ≠ p.1) (hk2 : k ≠ p.2) :
    insertCoord2 p w₀ w₁ x' k = x' ⟨k, hk1, hk2⟩ := by
  rw [insertCoord2_eq]
  simp only [dif_neg hk1, dif_neg hk2]

theorem pairG23_bounded {n : ℕ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2) {ℓ : ℝ}
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C) :
    ∃ C : ℝ, ∀ w y, ‖Work.BoseBoxFock.pairG23 p Θ A B w y‖ ≤ C := by
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨CA, hCA⟩ := hAb
  obtain ⟨CB, hCB⟩ := hBb
  -- the uniform bound on the integrand
  set K : ℝ := max CΘ 0 * max CA 0 * max CB 0 * max CΘ 0 with hK
  -- the one-particle box, of finite measure
  have hBc : IsCompact (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ
  have hBmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) := hBc.isClosed.measurableSet
  have hBfin : (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) < ⊤ := hBc.measure_lt_top
  set v : ℝ := (volume : Measure E3).real (Work.BoseK15.corpusBox.boxL ℓ) with hv
  -- the product box for the free coordinates
  set B' : Set ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) :=
    Set.univ.pi (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => Work.BoseK15.corpusBox.boxL ℓ)
    with hB'
  have hB'meas : MeasurableSet B' := by
    rw [hB']; exact MeasurableSet.univ_pi (fun _ => hBmeas)
  have hB'fin : (volume : Measure ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) B' < ⊤ := by
    rw [hB']
    change (MeasureTheory.Measure.pi
      (fun _ : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} => (volume : Measure E3)))
      (Set.univ.pi (fun _ => Work.BoseK15.corpusBox.boxL ℓ)) < ⊤
    rw [MeasureTheory.Measure.pi_pi]
    exact ENNReal.prod_lt_top (fun i _ => hBfin)
  set v' : ℝ := (volume : Measure ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)).real B' with hv'
  refine ⟨K * v * v * v', fun W0 W1 => ?_⟩
  -- the pointwise bound on the integrand
  have key : ∀ (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) (Y U : E3),
      ‖star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
        * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)‖ ≤ K := by
    intro x' Y U
    have h1 : ‖Θ (insertCoord2 p W0 W1 x')‖ ≤ max CΘ 0 :=
      (hCΘ _).trans (le_max_left _ _)
    have h2 : ‖A Y‖ ≤ max CA 0 := (hCA Y).trans (le_max_left _ _)
    have h3 : ‖B U‖ ≤ max CB 0 := (hCB U).trans (le_max_left _ _)
    have h4 : ‖Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)‖
        ≤ max CΘ 0 := (hCΘ _).trans (le_max_left _ _)
    calc ‖star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
            * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)‖
        = ‖Θ (insertCoord2 p W0 W1 x')‖ * ‖A Y‖ * ‖B U‖
            * ‖Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)‖ := by
          simp only [norm_mul, norm_star]
      _ ≤ max CΘ 0 * max CA 0 * max CB 0 * max CΘ 0 := by gcongr
      _ = K := hK.symm
  -- the integral over `u`: supported in the box, bounded by `K`
  have stepU : ∀ (x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) (Y : E3),
      ‖∫ U : E3, star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
        * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)‖
        ≤ K * v := by
    intro x' Y
    have hvan : ∀ U : E3, U ∉ Work.BoseK15.corpusBox.boxL ℓ →
        star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U) = 0 := by
      intro U hU
      have hz : Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)
          = 0 :=
        theta_eq_zero_of_coord_notMem hΘs (j := p.2) (by
          rw [Function.update_apply, if_pos rfl]; exact hU)
      rw [hz, mul_zero]
    have hfun : (fun U : E3 => star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U))
        = (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun U : E3 =>
            star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)) := by
      funext U
      by_cases hU : U ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hU]
      · rw [Set.indicator_of_notMem hU, hvan U hU]
    rw [hfun, MeasureTheory.integral_indicator hBmeas, hv]
    exact MeasureTheory.norm_setIntegral_le_of_norm_le_const hBfin (fun U _ => key x' Y U)
  -- the integral over `y`: supported in the box, bounded by `K * v`
  have stepY : ∀ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3,
      ‖∫ Y : E3, ∫ U : E3, star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
        * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)‖
        ≤ K * v * v := by
    intro x'
    have hvan : ∀ Y : E3, Y ∉ Work.BoseK15.corpusBox.boxL ℓ →
        (∫ U : E3, star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)) = 0 := by
      intro Y hY
      have hzero : ∀ U : E3, star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U) = 0 := by
        intro U
        have hz : Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)
            = 0 :=
          theta_eq_zero_of_coord_notMem hΘs (j := p.1) (by
            rw [Function.update_apply, if_neg hp, Function.update_self]; exact hY)
        rw [hz, mul_zero]
      simp only [hzero, MeasureTheory.integral_zero]
    have hfun : (fun Y : E3 => ∫ U : E3, star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U))
        = (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun Y : E3 => ∫ U : E3,
            star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)) := by
      funext Y
      by_cases hY : Y ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hY]
      · rw [Set.indicator_of_notMem hY, hvan Y hY]
    rw [hfun, MeasureTheory.integral_indicator hBmeas]
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hBfin (C := K * v)
      (fun Y _ => stepU x' Y)
    simpa only [hv, mul_assoc] using h
  -- the integral over the free coordinates: supported in the product box
  have stepX : ‖∫ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3,
      ∫ Y : E3, ∫ U : E3, star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
        * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)‖
        ≤ K * v * v * v' := by
    have hvan : ∀ x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3, x' ∉ B' →
        (∫ Y : E3, ∫ U : E3, star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)) = 0 := by
      intro x' hx
      have hz : Θ (insertCoord2 p W0 W1 x') = 0 := by
        by_contra hne
        have hmem := Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr hne))
        exact hx (by
          rw [hB', Set.mem_univ_pi]
          intro k
          have h := hmem k.1
          rw [insertCoord2_apply_of_ne p W0 W1 x' k.1 k.2.1 k.2.2] at h
          exact h)
      have hzero : ∀ (Y U : E3),
          star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U) = 0 := by
        intro Y U; simp only [hz, star_zero, zero_mul]
      simp only [hzero, MeasureTheory.integral_zero]
    have hfun : (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 => ∫ Y : E3, ∫ U : E3,
          star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U))
        = B'.indicator (fun x' : {k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3 => ∫ Y : E3, ∫ U : E3,
          star (Θ (insertCoord2 p W0 W1 x')) * star (A Y) * star (B U)
          * Θ (Function.update (Function.update (insertCoord2 p W0 W1 x') p.1 Y) p.2 U)) := by
      funext x'
      by_cases hx : x' ∈ B'
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, hvan x' hx]
    rw [hfun, MeasureTheory.integral_indicator hB'meas]
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const hB'fin (C := K * v * v)
      (fun x' _ => stepY x')
    simpa only [hv'] using h
  rw [pairG23]
  exact stepX

end Work.BoseBoxFock
