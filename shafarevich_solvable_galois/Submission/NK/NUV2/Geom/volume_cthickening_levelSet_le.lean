import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Volume bound for the `ε`-thickening of a logarithmic level set

Let `ι` be a finite nonempty type, `L : (ι → ℝ) →ₗ[ℝ] ℝ` a nonzero linear form, `K ≥ 1`,
`C > 0` and let `A` be a set of points `y` with positive coordinates such that

* all coordinates of `y` are within a factor `K` of one another (`y i ≤ K * y k`),
* all coordinates are `≤ C`,
* `L (fun i ↦ log (y i)) = c`.

Then the Lebesgue volume of the `ε`-thickening of `A` is `O(ε)`: there is `c₀ > 0` with
`volume (cthickening ε A) ≤ c₀ * ε` for all `0 < ε ≤ 1`.

The proof picks a coordinate `j` with `l j ≠ 0` (where `l i = L (Pi.single i 1)`), so that
the level equation can be solved for the `j`-th coordinate. Every point of the `ε`-thickening
is either close to a point of `A` whose coordinates are all small (giving a box of volume
`O(εⁿ)`), or lies in a "slab" of width `O(ε)` over the level set, and the volume of such a
slab is controlled by slicing in the `j`-th coordinate (`split_slab`).

## Main results

* `NK.NUV2.Geom.abs_log_sub_log_le_min`, `NK.NUV2.Geom.abs_exp_sub_one_le`: elementary
  one-variable estimates.
* `NK.NUV2.Geom.prod_slab_volume_le'`, `NK.NUV2.Geom.split_slab`: measure-theoretic slab
  bounds (the second is the coordinate-sliced version on `ι → ℝ`).
* `NK.NUV2.Geom.good_estimate`: the pointwise estimate on the level set.
* `NK.NUV2.Geom.volume_cthickening_levelSet_le`: the main theorem.
-/

namespace NK.NUV2.Geom

open MeasureTheory

/-- `|log x - log y| ≤ |x - y| / min x y` for positive `x` and `y`. -/
theorem abs_log_sub_log_le_min {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |Real.log x - Real.log y| ≤ |x - y| / min x y := by
  rcases le_total x y with h | h
  · have hmin : min x y = x := min_eq_left h
    have hxy : |x - y| = y - x := by rw [abs_of_nonpos (by linarith)]; ring
    have hlog : |Real.log x - Real.log y| = Real.log y - Real.log x := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hx h)), neg_sub]
    rw [hmin, hxy, hlog, ← Real.log_div (ne_of_gt hy) (ne_of_gt hx)]
    calc Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy hx)
      _ = (y - x) / x := by rw [sub_div, div_self (ne_of_gt hx)]
  · have hmin : min x y = y := min_eq_right h
    have hxy : |x - y| = x - y := by rw [abs_of_nonneg (by linarith)]
    have hlog : |Real.log x - Real.log y| = Real.log x - Real.log y :=
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hy h))
    rw [hmin, hxy, hlog, ← Real.log_div (ne_of_gt hx) (ne_of_gt hy)]
    calc Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = (x - y) / y := by rw [sub_div, div_self (ne_of_gt hy)]

/-- `|exp t - 1| ≤ |t| * exp |t|`. -/
theorem abs_exp_sub_one_le (t : ℝ) : |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  have hmain : ∀ s : ℝ, 0 ≤ s → Real.exp s - 1 ≤ s * Real.exp s := by
    intro s hs
    have h2 : 1 - Real.exp (-s) ≤ s := by
      have := Real.add_one_le_exp (-s); linarith
    have h3 : Real.exp s * (1 - Real.exp (-s)) = Real.exp s - 1 := by
      rw [mul_sub, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h4 : 0 < Real.exp s := Real.exp_pos s
    nlinarith [h2, h3, h4]
  rcases lt_or_ge t 0 with ht | ht
  · have hmul : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have htpos : 0 < Real.exp t := Real.exp_pos t
    have hexplt : Real.exp t < 1 := by
      rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr ht
    have h1 : 1 - Real.exp t ≤ -t := by
      have h := hmain (-t) (by linarith)
      nlinarith [h, hmul, htpos]
    have hle : (1:ℝ) ≤ Real.exp (-t) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
    calc |Real.exp t - 1| = 1 - Real.exp t := by rw [abs_of_neg (by linarith), neg_sub]
      _ ≤ -t := h1
      _ ≤ -t * Real.exp (-t) := by nlinarith [hle]
      _ = |t| * Real.exp |t| := by rw [abs_of_neg ht]
  · have habs : |Real.exp t - 1| = Real.exp t - 1 :=
      abs_of_nonneg (by linarith [Real.add_one_le_exp t])
    calc |Real.exp t - 1| = Real.exp t - 1 := habs
      _ ≤ t * Real.exp t := hmain t ht
      _ = |t| * Real.exp |t| := by rw [abs_of_nonneg ht]

/-- Fubini-type slab bound: the volume of the part of the "graph slab"
`{p | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r}` is at most `2 * (Λ * r) * volume S`. -/
theorem prod_slab_volume_le' {δ : Type*} [Fintype δ]
    (S : Set (δ → ℝ)) (hS : MeasurableSet S) (H : (δ → ℝ) → ℝ) (hH : Measurable H)
    (Λ r : ℝ) (_hr : 0 ≤ Λ * r) :
    MeasureTheory.volume {p : (δ → ℝ) × ℝ | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r}
      ≤ ENNReal.ofReal (2 * (Λ * r)) * MeasureTheory.volume S := by
  have hm : Measurable (fun p : (δ → ℝ) × ℝ => p.2 - H p.1) :=
    measurable_snd.sub (hH.comp measurable_fst)
  have hmeas : MeasurableSet {p : (δ → ℝ) × ℝ | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r} := by
    have hmM : Measurable (fun p : (δ → ℝ) × ℝ => (p.1, p.2 - H p.1)) :=
      Measurable.prod measurable_fst hm
    convert ((hS.prod measurableSet_Icc).preimage hmM) using 1
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, abs_le.mp h.2⟩, fun h => ⟨h.1, abs_le.mpr h.2⟩⟩
  let F : (δ → ℝ) → ENNReal := S.indicator (1 : (δ → ℝ) → ENNReal)
  have hFmeas : Measurable F := measurable_const.indicator hS
  have hFval : ∀ x, x ∈ S → F x = 1 := fun x hx => by simp [F, Set.indicator_of_mem hx]
  have hFval' : ∀ x, x ∉ S → F x = 0 := fun x hx => by simp [F, Set.indicator_of_notMem hx]
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  calc ∫⁻ x, volume (Prod.mk x ⁻¹' {p : (δ → ℝ) × ℝ | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r}) ∂volume
      ≤ ∫⁻ x, ENNReal.ofReal (2 * (Λ * r)) * F x ∂volume := by
        apply lintegral_mono
        intro x
        simp only []
        by_cases hx : x ∈ S
        · have hsub : Prod.mk x ⁻¹' {p : (δ → ℝ) × ℝ | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r}
              ⊆ Set.Icc (H x - Λ * r) (H x + Λ * r) := by
            intro t ht
            simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc] at ht ⊢
            have h2 := ht.2
            rw [abs_le] at h2
            exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
          calc volume (Prod.mk x ⁻¹' {p : (δ → ℝ) × ℝ | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r})
              ≤ volume (Set.Icc (H x - Λ * r) (H x + Λ * r)) := measure_mono hsub
            _ = ENNReal.ofReal (2 * (Λ * r)) := by
                rw [Real.volume_Icc]; congr 1; ring
            _ = ENNReal.ofReal (2 * (Λ * r)) * F x := by rw [hFval x hx, mul_one]
        · have h0 : Prod.mk x ⁻¹' {p : (δ → ℝ) × ℝ | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r} = ∅ := by
            ext t; simp [hx]
          rw [h0, measure_empty, hFval' x hx, mul_zero]
    _ = ENNReal.ofReal (2 * (Λ * r)) * ∫⁻ x, F x ∂volume := lintegral_const_mul _ hFmeas
    _ = ENNReal.ofReal (2 * (Λ * r)) * volume S := by
        congr 1
        simpa [F] using lintegral_indicator_one (μ := (volume : Measure (δ → ℝ))) hS

/-- Coordinate-sliced slab bound on `ι → ℝ`: the volume of
`{y | (fun i : {i // i ≠ j} => y i) ∈ S ∧ |y j - H (fun i => y i)| ≤ Λ * r}` is at most
`2 * (Λ * r) * volume S`. -/
theorem split_slab {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι)
    (S : Set ({i : ι // i ≠ j} → ℝ)) (hS : MeasurableSet S)
    (H : ({i : ι // i ≠ j} → ℝ) → ℝ) (hH : Measurable H)
    (Λ r : ℝ) (hr : 0 ≤ Λ * r) :
    MeasureTheory.volume {y : ι → ℝ |
        (fun i : {i : ι // i ≠ j} => y i.1) ∈ S ∧
        |y j - H (fun i : {i : ι // i ≠ j} => y i.1)| ≤ Λ * r}
      ≤ ENNReal.ofReal (2 * (Λ * r)) * MeasureTheory.volume S := by
  let eu : ({i : ι // ¬(i ≠ j)} → ℝ) ≃ᵐ ℝ :=
  { toFun := fun f => f ⟨j, by simp⟩
    invFun := fun t => fun _ => t
    left_inv := by
      intro f
      funext i
      have h1 : (i : ι) = j := by
        by_contra h
        exact i.2 h
      exact congrArg f (Subtype.ext h1.symm)
    right_inv := by intro t; rfl
    measurable_toFun := measurable_pi_apply _
    measurable_invFun := measurable_pi_iff.mpr (fun _ => measurable_id) }
  have hEu : MeasurePreserving eu volume volume := by
    refine ⟨eu.measurable, ?_⟩
    change Measure.map (Function.eval (⟨j, by simp⟩ : {i : ι // ¬(i ≠ j)})) volume = volume
    rw [volume_pi, Measure.pi_map_eval]
    simp
  let e1 : (ι → ℝ) ≃ᵐ ({i : ι // i ≠ j} → ℝ) × ({i : ι // ¬(i ≠ j)} → ℝ) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i => i ≠ j)
  let e2 : ({i : ι // i ≠ j} → ℝ) × ({i : ι // ¬(i ≠ j)} → ℝ) ≃ᵐ
      ({i : ι // i ≠ j} → ℝ) × ℝ :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) eu
  let E : (ι → ℝ) ≃ᵐ ({i : ι // i ≠ j} → ℝ) × ℝ := e1.trans e2
  have hEapp : ∀ y : ι → ℝ, E y = (fun i : {i : ι // i ≠ j} => y i.1, y j) := by
    intro y
    simp only [E, MeasurableEquiv.trans_apply]
    rw [show e1 y = (fun i : {i : ι // i ≠ j} => y i.1,
        fun i : {i : ι // ¬(i ≠ j)} => y i.1) from rfl]
    change (fun i : {i : ι // i ≠ j} => y i.1,
        eu (fun i : {i : ι // ¬(i ≠ j)} => y i.1))
      = (fun i : {i : ι // i ≠ j} => y i.1, y j)
    rfl
  have hmp : MeasurePreserving E volume volume := by
    have h1 := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i => i ≠ j)
    have h2 : MeasurePreserving
        (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ({i : ι // i ≠ j} → ℝ)) eu)
        volume volume := MeasurePreserving.prod (MeasurePreserving.id _) hEu
    exact h1.trans h2
  set T : Set (({i : ι // i ≠ j} → ℝ) × ℝ) :=
    {p | p.1 ∈ S ∧ |p.2 - H p.1| ≤ Λ * r} with hT
  have hmeasT : MeasurableSet T := by
    rw [hT]
    have hm : Measurable (fun p : ({i : ι // i ≠ j} → ℝ) × ℝ => p.2 - H p.1) :=
      measurable_snd.sub (hH.comp measurable_fst)
    have hmM : Measurable (fun p : ({i : ι // i ≠ j} → ℝ) × ℝ => (p.1, p.2 - H p.1)) :=
      Measurable.prod measurable_fst hm
    convert ((hS.prod measurableSet_Icc).preimage hmM) using 1
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, abs_le.mp h.2⟩, fun h => ⟨h.1, abs_le.mpr h.2⟩⟩
  have hpre : E ⁻¹' T = {y : ι → ℝ |
      (fun i : {i : ι // i ≠ j} => y i.1) ∈ S ∧
      |y j - H (fun i : {i : ι // i ≠ j} => y i.1)| ≤ Λ * r} := by
    ext y
    simp only [Set.mem_preimage, hT, Set.mem_ofPred_eq]
    rw [hEapp y]
  have hmain : (Measure.map E volume) T = volume (E ⁻¹' T) := Measure.map_apply E.measurable hmeasT
  have hgoal : volume {y : ι → ℝ |
      (fun i : {i : ι // i ≠ j} => y i.1) ∈ S ∧
      |y j - H (fun i : {i : ι // i ≠ j} => y i.1)| ≤ Λ * r} = volume T := by
    rw [← hpre, ← hmain, hmp.map_eq]
  rw [hgoal]
  exact prod_slab_volume_le' S hS H hH Λ r hr

/-- Pointwise estimate on the level set: for `y` close to a point `a` of the level set whose
coordinates are all `≥ 2 * r`, the `j`-th coordinate of `y` is within `Λ * r` of the value of
the level function on the other coordinates. -/
theorem good_estimate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l : ι → ℝ) (j : ι) (hj : l j ≠ 0) (c K r : ℝ) (hr : 0 < r) (hK : 1 ≤ K)
    (a y : ι → ℝ) (halog : ∑ i, l i * Real.log (a i) = c)
    (hcomp : ∀ i k, a i ≤ K * a k)
    (h2 : ∀ i, 2 * r ≤ a i) (hy : ∀ i, |y i - a i| ≤ r) :
    |y j - Real.exp ((c - ∑ i ∈ Finset.univ.erase j, l i * Real.log (y i)) / l j)|
      ≤ (1 + 2 * K * ((∑ i ∈ Finset.univ.erase j, |l i|) / |l j|)
            * Real.exp (K * ((∑ i ∈ Finset.univ.erase j, |l i|) / |l j|))) * r := by
  set L1 : ℝ := (∑ i ∈ Finset.univ.erase j, |l i|) / |l j| with hL1def
  set X : ℝ := (c - ∑ i ∈ Finset.univ.erase j, l i * Real.log (y i)) / l j with hX
  have haj : 0 < a j := by linarith [h2 j]
  have hljpos : 0 < |l j| := abs_pos.mpr hj
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hL1 : 0 ≤ L1 := by
    rw [hL1def]
    exact div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) hljpos.le
  have hsplit : ∑ i, l i * Real.log (a i)
      = l j * Real.log (a j) + ∑ i ∈ Finset.univ.erase j, l i * Real.log (a i) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    ring
  have hajlog : Real.log (a j)
      = (c - ∑ i ∈ Finset.univ.erase j, l i * Real.log (a i)) / l j := by
    rw [← halog, hsplit, add_sub_cancel_right, mul_div_cancel_left₀ _ hj]
  have hδeq : X - Real.log (a j)
      = -(∑ i ∈ Finset.univ.erase j, l i * (Real.log (y i) - Real.log (a i))) / l j := by
    rw [hX, hajlog]
    have h1 : (c - ∑ i ∈ Finset.univ.erase j, l i * Real.log (y i)) / l j
        - (c - ∑ i ∈ Finset.univ.erase j, l i * Real.log (a i)) / l j
        = ((∑ i ∈ Finset.univ.erase j, l i * Real.log (a i))
            - (∑ i ∈ Finset.univ.erase j, l i * Real.log (y i))) / l j := by
      rw [div_sub_div_same]; ring
    rw [h1]
    have h2' : (∑ i ∈ Finset.univ.erase j, l i * (Real.log (y i) - Real.log (a i)))
        = (∑ i ∈ Finset.univ.erase j, l i * Real.log (y i))
          - (∑ i ∈ Finset.univ.erase j, l i * Real.log (a i)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2']; ring
  have hterm : ∀ i ∈ Finset.univ.erase j,
      |Real.log (a i) - Real.log (y i)| ≤ 2 * r / a i := by
    intro i _
    have hai : 0 < a i := by linarith [h2 i]
    have hyi : 0 < y i := by
      have := (abs_le.mp (hy i)).1; linarith [h2 i]
    have hmin : a i / 2 ≤ min (a i) (y i) := by
      rw [le_min_iff]
      exact ⟨by linarith, by have := (abs_le.mp (hy i)).1; linarith [h2 i]⟩
    calc |Real.log (a i) - Real.log (y i)| ≤ |a i - y i| / min (a i) (y i) :=
          abs_log_sub_log_le_min hai hyi
      _ ≤ r / (a i / 2) := div_le_div₀ hr.le (by rw [abs_sub_comm]; exact hy i) (by linarith) hmin
      _ = 2 * r / a i := by rw [div_div_eq_mul_div]; ring
  have hsum : ∑ i ∈ Finset.univ.erase j, |l i| * |Real.log (a i) - Real.log (y i)|
      ≤ 2 * r * K * (∑ i ∈ Finset.univ.erase j, |l i|) / a j := by
    have hstep : ∀ i ∈ Finset.univ.erase j,
        |l i| * |Real.log (a i) - Real.log (y i)| ≤ |l i| * (2 * r * K / a j) := by
      intro i hi
      have hai : 0 < a i := by linarith [h2 i]
      have hinv : 1 / a i ≤ K / a j := by
        rw [le_div_iff₀ (by positivity)]
        rw [div_mul_eq_mul_div, div_le_iff₀ hai]
        linarith [hcomp j i]
      have hb : 2 * r / a i ≤ 2 * r * K / a j := by
        have h2r : (0:ℝ) ≤ 2 * r := by linarith
        calc 2 * r / a i = 2 * r * (1 / a i) := by ring
          _ ≤ 2 * r * (K / a j) := mul_le_mul_of_nonneg_left hinv h2r
          _ = 2 * r * K / a j := by ring
      exact (mul_le_mul_of_nonneg_left (hterm i hi) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
    calc ∑ i ∈ Finset.univ.erase j, |l i| * |Real.log (a i) - Real.log (y i)|
        ≤ ∑ i ∈ Finset.univ.erase j, |l i| * (2 * r * K / a j) := Finset.sum_le_sum hstep
      _ = 2 * r * K / a j * (∑ i ∈ Finset.univ.erase j, |l i|) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 2 * r * K * (∑ i ∈ Finset.univ.erase j, |l i|) / a j := by ring
  have hδle : |X - Real.log (a j)| ≤ 2 * r * K * L1 / a j := by
    rw [hδeq, abs_div, abs_neg]
    have hnum : |∑ i ∈ Finset.univ.erase j, l i * (Real.log (y i) - Real.log (a i))|
        ≤ ∑ i ∈ Finset.univ.erase j, |l i| * |Real.log (a i) - Real.log (y i)| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_sub_comm]
    have h1 : (∑ i ∈ Finset.univ.erase j, |l i| * |Real.log (a i) - Real.log (y i)|) / |l j|
        ≤ (2 * r * K * (∑ i ∈ Finset.univ.erase j, |l i|) / a j) / |l j| :=
      div_le_div_of_nonneg_right hsum hljpos.le
    have h2' : (2 * r * K * (∑ i ∈ Finset.univ.erase j, |l i|) / a j) / |l j|
        = 2 * r * K * L1 / a j := by
      rw [hL1def]; field_simp
    exact (div_le_div_of_nonneg_right hnum hljpos.le).trans (h1.trans (le_of_eq h2'))
  have hDexp : Real.exp |X - Real.log (a j)| ≤ Real.exp (K * L1) := by
    apply Real.exp_le_exp.mpr
    have h : 2 * r * K * L1 / a j ≤ K * L1 := by
      rw [div_le_iff₀ haj]
      have hKLI : (0:ℝ) ≤ K * L1 := by positivity
      calc 2 * r * K * L1 = 2 * r * (K * L1) := by ring
        _ ≤ a j * (K * L1) := mul_le_mul_of_nonneg_right (h2 j) hKLI
        _ = K * L1 * a j := by ring
    exact hδle.trans h
  have hexp_eq : Real.exp X = a j * Real.exp (X - Real.log (a j)) := by
    rw [Real.exp_sub, Real.exp_log haj]
    field_simp
  have hsec : |a j - Real.exp X| ≤ a j * ((2 * r * K * L1 / a j) * Real.exp (K * L1)) := by
    have hfac : |a j - Real.exp X| = a j * |1 - Real.exp (X - Real.log (a j))| := by
      rw [hexp_eq]
      rw [show a j - a j * Real.exp (X - Real.log (a j))
          = a j * (1 - Real.exp (X - Real.log (a j))) from by ring, abs_mul, abs_of_pos haj]
    rw [hfac, show |1 - Real.exp (X - Real.log (a j))|
        = |Real.exp (X - Real.log (a j)) - 1| from by rw [abs_sub_comm]]
    refine mul_le_mul_of_nonneg_left ?_ haj.le
    exact (abs_exp_sub_one_le _).trans
      (mul_le_mul hδle hDexp (by positivity) (by positivity))
  have htri : |y j - Real.exp X| ≤ |y j - a j| + |a j - Real.exp X| := by
    rw [show y j - Real.exp X = (y j - a j) + (a j - Real.exp X) from by ring]
    exact abs_add_le _ _
  refine (htri.trans (add_le_add (hy j) hsec)).trans (le_of_eq ?_)
  show r + a j * ((2 * r * K * L1 / a j) * Real.exp (K * L1))
    = (1 + 2 * K * L1 * Real.exp (K * L1)) * r
  field_simp

/-- **Main theorem.** The `ε`-thickening of a bounded logarithmic level set has volume `O(ε)`. -/
theorem volume_cthickening_levelSet_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : (ι → ℝ) →ₗ[ℝ] ℝ) (hL : L ≠ 0) (c K C : ℝ) (hK : 1 ≤ K) (hC : 0 < C)
    (A : Set (ι → ℝ))
    (hA : ∀ y ∈ A, (∀ i, 0 < y i) ∧ (∀ i k, y i ≤ K * y k) ∧ (∀ i, y i ≤ C) ∧
      L (fun i ↦ Real.log (y i)) = c) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      MeasureTheory.volume (Metric.cthickening ε A) ≤ ENNReal.ofReal (c₀ * ε) := by
  classical
  let l : ι → ℝ := fun i => L (Pi.single i 1)
  have hl : ∀ i, l i = L (Pi.single i 1) := fun i => rfl
  have hcoord : ∀ z : ι → ℝ, L z = ∑ i, l i * z i := by
    intro z
    conv_lhs => rw [show z = ∑ i, z i • (Pi.single i (1:ℝ) : ι → ℝ) from by
      ext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp
      · intro b _ hb; simp [Pi.single_eq_of_ne (Ne.symm hb)]
      · intro h; exact absurd (Finset.mem_univ k) h]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hl i]; ring
  have hex : ∃ j, l j ≠ 0 := by
    by_contra h
    push Not at h
    refine hL (LinearMap.ext fun z => ?_)
    rw [hcoord z]
    simp [h]
  obtain ⟨j, hj⟩ := hex
  have hlj : 0 < |l j| := abs_pos.mpr hj
  have hI : 0 ≤ ∑ i ∈ Finset.univ.erase j, |l i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hL1 : 0 ≤ (∑ i ∈ Finset.univ.erase j, |l i|) / |l j| := div_nonneg hI hlj.le
  set Λ : ℝ := 1 + 2 * K * ((∑ i ∈ Finset.univ.erase j, |l i|) / |l j|)
      * Real.exp (K * ((∑ i ∈ Finset.univ.erase j, |l i|) / |l j|)) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ]
    have h2 : 0 ≤ 2 * K * ((∑ i ∈ Finset.univ.erase j, |l i|) / |l j|)
        * Real.exp (K * ((∑ i ∈ Finset.univ.erase j, |l i|) / |l j|)) :=
      mul_nonneg (mul_nonneg (by linarith) hL1) (Real.exp_pos _).le
    linarith
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos hΛ1
  refine ⟨((4*K+4)^(Fintype.card ι) + 4*Λ*(C+4)^(Fintype.card ι)) + 1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ (4*K+4)^(Fintype.card ι) := by positivity
    have h2 : (0:ℝ) ≤ 4*Λ*(C+4)^(Fintype.card ι) := by positivity
    linarith
  · intro ε hε0 hε1
    by_cases hAe : A = ∅
    · rw [hAe, Metric.cthickening_empty]
      simp
    · set r : ℝ := 2 * ε with hr
      have hrpos : 0 < r := by rw [hr]; linarith
      have hr2 : r ≤ 2 := by rw [hr]; linarith
      set S : Set ({i : ι // i ≠ j} → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-2) (C + 2))
        with hS
      have hSmeas : MeasurableSet S := by
        rw [hS]
        exact MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
      have hSvol : volume S ≤ ENNReal.ofReal ((C+4)^(Fintype.card ι)) := by
        rw [hS, volume_pi, Measure.pi_pi]
        simp only [Real.volume_Icc]
        rw [Finset.prod_const]
        have h1 : (C + 2) - (-2) = C + 4 := by ring
        rw [h1, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ C + 4)]
        exact ENNReal.ofReal_le_ofReal
          (pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ C + 4) (Fintype.card_subtype_le _))
      set H : ({i : ι // i ≠ j} → ℝ) → ℝ :=
        fun x => Real.exp ((c - ∑ i : {i : ι // i ≠ j}, l i.1 * Real.log (x i)) / l j) with hH
      have hHmeas : Measurable H := by rw [hH]; fun_prop
      set B : Set (ι → ℝ) := Set.pi Set.univ (fun _ : ι => Set.Ioo (-r) ((2*K+1)*r)) with hB
      set G : Set (ι → ℝ) := {y | (fun i : {i : ι // i ≠ j} => y i.1) ∈ S ∧
          |y j - H (fun i : {i : ι // i ≠ j} => y i.1)| ≤ Λ * r} with hG
      have hdec : Metric.cthickening ε A ⊆ B ∪ G := by
        intro y hy
        have hmem : Metric.infEDist y A ≤ ENNReal.ofReal ε := Metric.mem_cthickening_iff.mp hy
        have hlt : Metric.infEDist y A < ENNReal.ofReal r := by
          refine lt_of_le_of_lt hmem ?_
          rw [ENNReal.ofReal_lt_ofReal_iff hrpos, hr]
          linarith
        obtain ⟨a, haA, hda⟩ := Metric.infEDist_lt_iff.mp hlt
        have hdist : dist y a < r := by
          rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hrpos] at hda
          exact hda
        have hya : ∀ i, |y i - a i| ≤ r := fun i => by
          have h1 := dist_le_pi_dist y a i
          rw [Real.dist_eq] at h1
          exact le_of_lt (lt_of_le_of_lt h1 hdist)
        have hapos : ∀ i, 0 < a i := fun i => (hA a haA).1 i
        have hacomp : ∀ i k, a i ≤ K * a k := (hA a haA).2.1
        have haC : ∀ i, a i ≤ C := (hA a haA).2.2.1
        have halvl : L (fun i => Real.log (a i)) = c := (hA a haA).2.2.2
        by_cases hgood : ∀ i, 2 * r ≤ a i
        · right
          constructor
          · rw [hS, Set.mem_pi]
            intro i _
            simp only [Set.mem_Icc]
            have h1 := (abs_le.mp (hya i.1)).1
            have h2 := (abs_le.mp (hya i.1)).2
            have h3 := hapos i.1
            have h4 := haC i.1
            exact ⟨by linarith, by linarith⟩
          · have hsum_eq : (∑ i : {i : ι // i ≠ j}, l i.1 * Real.log (y i.1))
                = ∑ i ∈ Finset.univ.erase j, l i * Real.log (y i) := by
              have hp : (fun x : ι => x ≠ j)
                  = (fun x : ι => x ∈ Finset.univ.erase j) := by
                funext x
                exact propext (by simp [Finset.mem_erase])
              refine (Fintype.sum_equiv (Equiv.subtypeEquivProp hp)
                (fun i : {i : ι // i ≠ j} => l i.1 * Real.log (y i.1))
                (fun i : {i : ι // i ∈ Finset.univ.erase j} => l i.1 * Real.log (y i.1))
                (fun i => rfl)).trans ?_
              exact (Finset.sum_subtype (s := Finset.univ.erase j)
                (h := fun x => Iff.rfl)
                (f := fun i => l i * Real.log (y i))).symm
            have halog : ∑ i, l i * Real.log (a i) = c := by
              rw [← hcoord (fun i => Real.log (a i))]
              exact halvl
            have hge := good_estimate l j hj c K r hrpos hK a y halog hacomp hgood hya
            simp only [hH]
            rw [hsum_eq, hΛ]
            exact hge
        · left
          rw [hB, Set.mem_pi]
          intro i _
          simp only [Set.mem_Ioo]
          push Not at hgood
          obtain ⟨i0, hi0⟩ := hgood
          have h1 := hacomp i i0
          have h2 := (abs_le.mp (hya i)).1
          have h3 := (abs_le.mp (hya i)).2
          have h4 := hapos i
          have h5 : K * a i0 < K * (2 * r) :=
            mul_lt_mul_of_pos_left hi0 (by linarith : (0:ℝ) < K)
          constructor
          · linarith
          · nlinarith
      have hBvol : volume B ≤ ENNReal.ofReal (((2*K+2)*r)^(Fintype.card ι)) := by
        rw [hB, volume_pi, Measure.pi_pi]
        simp only [Real.volume_Ioo]
        rw [Finset.prod_const]
        have h1 : (2*K+1)*r - (-r) = (2*K+2)*r := by ring
        rw [h1, ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (2*K+2)*r), Finset.card_univ]
      have hGvol : volume G ≤
          ENNReal.ofReal (2 * (Λ * r)) * ENNReal.ofReal ((C+4)^(Fintype.card ι)) := by
        have hmain := split_slab j S hSmeas H hHmeas Λ r (by positivity)
        rw [hG]
        exact hmain.trans (by gcongr)
      calc volume (Metric.cthickening ε A) ≤ volume (B ∪ G) := measure_mono hdec
        _ ≤ volume B + volume G := measure_union_le _ _
        _ ≤ ENNReal.ofReal (((2*K+2)*r)^(Fintype.card ι))
              + ENNReal.ofReal (2 * (Λ * r)) * ENNReal.ofReal ((C+4)^(Fintype.card ι)) :=
            add_le_add hBvol hGvol
        _ ≤ ENNReal.ofReal
              ((((4*K+4)^(Fintype.card ι) + 4*Λ*(C+4)^(Fintype.card ι)) + 1) * ε) := by
            have hreal : ((2*K+2)*r)^(Fintype.card ι) + 2 * (Λ * r) * (C+4)^(Fintype.card ι)
                ≤ (((4*K+4)^(Fintype.card ι) + 4*Λ*(C+4)^(Fintype.card ι)) + 1) * ε := by
              have hpow : ((2*K+2)*r)^(Fintype.card ι)
                  = (4*K+4)^(Fintype.card ι) * ε^(Fintype.card ι) := by
                rw [hr, show (2*K+2)*(2*ε) = (4*K+4)*ε by ring, mul_pow]
              have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
              have h2 : ε^(Fintype.card ι) ≤ ε := by
                calc ε^(Fintype.card ι) ≤ ε^1 := pow_le_pow_of_le_one hε0.le hε1 hn
                  _ = ε := pow_one ε
              have h3 : (0:ℝ) ≤ (4*K+4)^(Fintype.card ι) := pow_nonneg (by linarith) _
              have h5 := mul_le_mul_of_nonneg_left h2 h3
              have h6 : (0:ℝ) ≤ 4*Λ*(C+4)^(Fintype.card ι) := by positivity
              rw [hpow]
              nlinarith [h5, hε0.le, h6, mul_nonneg h6 hε0.le]
            calc ENNReal.ofReal (((2*K+2)*r)^(Fintype.card ι))
                  + ENNReal.ofReal (2 * (Λ * r)) * ENNReal.ofReal ((C+4)^(Fintype.card ι))
                = ENNReal.ofReal (((2*K+2)*r)^(Fintype.card ι))
                  + ENNReal.ofReal (2 * (Λ * r) * (C+4)^(Fintype.card ι)) := by
                    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (Λ * r))]
                _ = ENNReal.ofReal (((2*K+2)*r)^(Fintype.card ι)
                      + 2 * (Λ * r) * (C+4)^(Fintype.card ι)) := by
                    rw [ENNReal.ofReal_add (by positivity : (0:ℝ) ≤ ((2*K+2)*r)^(Fintype.card ι))
                      (by positivity : (0:ℝ) ≤ 2 * (Λ * r) * (C+4)^(Fintype.card ι))]
                _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end NK.NUV2.Geom
