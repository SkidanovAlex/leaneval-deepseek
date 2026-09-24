import Mathlib

/-!
# `Work.GM.Affine.periodization_le_window_sum`

Comparing the integral of a periodisation with the sum of window integrals:

`∫_0^T Σ_ℓ g (ℓ + u) du ≤ Σ_ℓ ∫_{[ℓ-a, ℓ+a]} g`

for `0 < T ≤ 1/2`, `T ≤ a` and `g ≥ 0` continuous integrable.  The proof swaps the
integral and the (nonnegative) sum by `integral_tsum`, compares each translated interval
`(ℓ, ℓ+T]` with the window `[ℓ-a, ℓ+a]` (which contains it because `T ≤ a`), and finally
proves that the window sums are summable (each point lies in boundedly many windows).
-/

namespace Work.GM.Affine

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The window of half width `a` centred at the integer `ℓ`. -/
private def win (a : ℝ) (ℓ : ℤ) : Set ℝ := Set.Icc ((ℓ : ℝ) - a) ((ℓ : ℝ) + a)

private lemma mem_win {a x : ℝ} {ℓ : ℤ} : x ∈ win a ℓ ↔ (ℓ : ℝ) - a ≤ x ∧ x ≤ (ℓ : ℝ) + a :=
  Set.mem_Icc

private lemma disjoint_Ioc_intCast (m n : ℤ) (h : m ≠ n) :
    Disjoint (Set.Ioc (m : ℝ) ((m : ℝ) + 1)) (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) := by
  rw [Set.disjoint_left]
  intro x hmx hnx
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by
      have : m + 1 ≤ n := by omega
      exact_mod_cast this
    have hx1 : x ≤ (m : ℝ) + 1 := hmx.2
    have hx2 : (n : ℝ) < x := hnx.1
    linarith
  · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      have : n + 1 ≤ m := by omega
      exact_mod_cast this
    have hx1 : x ≤ (n : ℝ) + 1 := hnx.2
    have hx2 : (m : ℝ) < x := hmx.1
    linarith

/-- The Lebesgue integral over `ℝ` as the sum of the integrals over the unit intervals `(n, n+1]`. -/
private lemma lintegral_intCast_Ioc_tsum (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x = ∑' n : ℤ, ∫⁻ x in Set.Ioc (n : ℝ) ((n : ℝ) + 1), g x := by
  have hd : Pairwise (Function.onFun Disjoint (fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))) :=
    fun m n hmn => disjoint_Ioc_intCast m n hmn
  have h := lintegral_iUnion (μ := volume) (s := fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))
      (fun n => measurableSet_Ioc) hd g
  rw [iUnion_Ioc_intCast ℝ, Measure.restrict_univ] at h
  exact h

/-- Translation invariance of the `ℝ≥0∞`-valued set integral. -/
private lemma setLIntegral_comp_add_left_Ioc (f : ℝ → ℝ≥0∞) (a c : ℝ) :
    ∫⁻ u in Set.Ioc (0 : ℝ) c, f (a + u) = ∫⁻ x in Set.Ioc a (a + c), f x := by
  have h := MeasurePreserving.setLIntegral_comp_emb (measurePreserving_add_left volume a)
      (Homeomorph.addLeft a).measurableEmbedding f (Set.Ioc (0 : ℝ) c)
  rw [Set.image_const_add_Ioc] at h
  simpa using h

/-- Translation invariance of the real-valued set integral. -/
private lemma setIntegral_comp_add_left_Ioc (F : ℝ → ℝ) (a c : ℝ) :
    ∫ u in Set.Ioc (0 : ℝ) c, F (a + u) = ∫ x in Set.Ioc a (a + c), F x := by
  have h := (MeasurePreserving.setIntegral_image_emb (measurePreserving_add_left volume a)
      (Homeomorph.addLeft a).measurableEmbedding F (Set.Ioc (0 : ℝ) c)).symm
  rw [Set.image_const_add_Ioc] at h
  simpa using h

theorem periodization_le_window_sum {a T : ℝ} (ha : 0 < a) (hT : 0 < T) (hT1 : T ≤ 1 / 2)
    (hTa : T ≤ a) {g : ℝ → ℝ} (hg : Continuous g) (hgnn : ∀ x, 0 ≤ g x) (hgint : Integrable g) :
    ∫ u in (0 : ℝ)..T, (∑' ℓ : ℤ, g ((ℓ : ℝ) + u)) ≤
      ∑' ℓ : ℤ, ∫ x in Set.Icc ((ℓ : ℝ) - a) ((ℓ : ℝ) + a), g x := by
  classical
  have hTle : (0 : ℝ) ≤ T := le_of_lt hT
  have hT1' : T ≤ 1 := by linarith
  -- ## Step 1: swap the integral and the sum
  have hfin : (∑' ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g ((ℓ : ℝ) + u)‖ₑ) ≠ ⊤ := by
    have hstep : ∀ ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g ((ℓ : ℝ) + u)‖ₑ
        ≤ ∫⁻ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), ENNReal.ofReal (g x) := by
      intro ℓ
      have h1 : ∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g ((ℓ : ℝ) + u)‖ₑ
          = ∫⁻ u in Set.Ioc (0 : ℝ) T, ENNReal.ofReal (g ((ℓ : ℝ) + u)) :=
        lintegral_congr (fun u => Real.enorm_of_nonneg (hgnn _))
      rw [h1, setLIntegral_comp_add_left_Ioc (fun x => ENNReal.ofReal (g x)) (ℓ : ℝ) T]
      apply lintegral_mono_set
      intro x hx
      exact ⟨hx.1, le_trans hx.2 (by linarith)⟩
    have hchain : (∑' ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g ((ℓ : ℝ) + u)‖ₑ)
        ≤ ENNReal.ofReal (∫ x, g x) := by
      calc ∑' ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) T, ‖g ((ℓ : ℝ) + u)‖ₑ
          ≤ ∑' ℓ : ℤ, ∫⁻ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), ENNReal.ofReal (g x) :=
            ENNReal.tsum_le_tsum hstep
        _ = ∫⁻ x, ENNReal.ofReal (g x) := (lintegral_intCast_Ioc_tsum _).symm
        _ = ENNReal.ofReal (∫ x, g x) :=
            (ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall hgnn)).symm
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hchain
  have hswap : ∫ u in Set.Ioc (0 : ℝ) T, (∑' ℓ : ℤ, g ((ℓ : ℝ) + u))
      = ∑' ℓ : ℤ, ∫ u in Set.Ioc (0 : ℝ) T, g ((ℓ : ℝ) + u) := by
    apply integral_tsum
    · intro ℓ
      exact ((hg.comp (continuous_const.add continuous_id)).measurable).aestronglyMeasurable
    · exact hfin
  -- ## Step 2: the translated intervals lie inside the windows
  have hterm : ∀ ℓ : ℤ, ∫ u in (0 : ℝ)..T, g ((ℓ : ℝ) + u)
      ≤ ∫ x in Set.Icc ((ℓ : ℝ) - a) ((ℓ : ℝ) + a), g x := by
    intro ℓ
    have h1 : ∫ u in (0 : ℝ)..T, g ((ℓ : ℝ) + u)
        = ∫ u in Set.Ioc (0 : ℝ) T, g ((ℓ : ℝ) + u) := intervalIntegral.integral_of_le hTle
    rw [h1, setIntegral_comp_add_left_Ioc g (ℓ : ℝ) T]
    apply setIntegral_mono_set
    · exact hgint.integrableOn
    · exact Filter.Eventually.of_forall (fun x => hgnn x)
    · exact Filter.Eventually.of_forall (fun x hx => ⟨by linarith [hx.1, ha], by linarith [hx.2, hTa]⟩)
  -- ## Step 3: the window sums are summable
  have hbnonneg : ∀ ℓ : ℤ, 0 ≤ ∫ x in Set.Icc ((ℓ : ℝ) - a) ((ℓ : ℝ) + a), g x :=
    fun ℓ => integral_nonneg (fun x => hgnn x)
  have hbsumm : Summable (fun ℓ : ℤ => ∫ x in Set.Icc ((ℓ : ℝ) - a) ((ℓ : ℝ) + a), g x) := by
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 2 * a ≤ (n : ℝ) := exists_nat_ge (2 * a)
    have hbnd : (∑' ℓ : ℤ, ENNReal.ofReal (∫ x in win a ℓ, g x))
        ≤ (↑(n + 1) : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (g x) := by
      have hΦmeas : Measurable (fun x : ℝ => ENNReal.ofReal (g x)) :=
        ENNReal.measurable_ofReal.comp hg.measurable
      have hstep1 : ∀ ℓ : ℤ, ENNReal.ofReal (∫ x in win a ℓ, g x)
          = ∫⁻ x in win a ℓ, ENNReal.ofReal (g x) := by
        intro ℓ
        exact ofReal_integral_eq_lintegral_ofReal (hgint.integrableOn)
          (Filter.Eventually.of_forall hgnn)
      have hcount : ∀ x : ℝ,
          (∑' ℓ : ℤ, (win a ℓ).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ (↑(n + 1) : ℝ≥0∞) := by
        intro x
        set m : ℤ := ⌈x - a⌉ with hm
        have hm1 : ∀ ℓ : ℤ, x ∈ win a ℓ → m ≤ ℓ := by
          intro ℓ hℓ
          have h1 : x ≤ (ℓ : ℝ) + a := (mem_win.mp hℓ).2
          rw [hm, Int.ceil_le]
          linarith
        have hm2 : ∀ ℓ : ℤ, x ∈ win a ℓ → ℓ ≤ m + (n : ℤ) := by
          intro ℓ hℓ
          have h1 : (ℓ : ℝ) - a ≤ x := (mem_win.mp hℓ).1
          have hx : x ≤ (m : ℝ) + a := by
            have h2 := Int.le_ceil (x - a)
            rw [← hm] at h2
            linarith
          have h2 : (ℓ : ℝ) ≤ ((m + (n : ℤ) : ℤ) : ℝ) := by
            push_cast
            linarith
          exact_mod_cast h2
        calc ∑' ℓ : ℤ, (win a ℓ).indicator (fun _ => (1 : ℝ≥0∞)) x
            ≤ ∑' ℓ : ℤ, (if ℓ ∈ Finset.Icc m (m + (n : ℤ)) then (1 : ℝ≥0∞) else 0) := by
              apply ENNReal.tsum_le_tsum
              intro ℓ
              rw [Set.indicator_apply]
              by_cases hx : x ∈ win a ℓ
              · have h1 := hm1 ℓ hx
                have h2 := hm2 ℓ hx
                simp [hx, Finset.mem_Icc.mpr ⟨h1, h2⟩]
              · simp [hx]
          _ = (↑(Finset.Icc m (m + (n : ℤ))).card : ℝ≥0∞) := by
              rw [tsum_eq_sum (s := Finset.Icc m (m + (n : ℤ))) (fun b hb => by simp [hb])]
              have key : ∀ b ∈ Finset.Icc m (m + (n : ℤ)),
                  (if b ∈ Finset.Icc m (m + (n : ℤ)) then (1 : ℝ≥0∞) else 0) = 1 :=
                fun b hb => by simp [hb]
              rw [Finset.sum_congr rfl key]
              simp
          _ = (↑(n + 1) : ℝ≥0∞) := by
              rw [Int.card_Icc]
              have h3 : (m + (n : ℤ) + 1 - m).toNat = n + 1 := by
                have h4 : m + (n : ℤ) + 1 - m = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
                rw [h4, Int.toNat_natCast]
              rw [h3]
      calc ∑' ℓ : ℤ, ENNReal.ofReal (∫ x in win a ℓ, g x)
          = ∑' ℓ : ℤ, ∫⁻ x in win a ℓ, ENNReal.ofReal (g x) := tsum_congr hstep1
        _ = ∑' ℓ : ℤ, ∫⁻ x, (win a ℓ).indicator (fun _ => ENNReal.ofReal (g x)) x := by
              apply tsum_congr
              intro ℓ
              exact (lintegral_indicator (f := fun x => ENNReal.ofReal (g x))
                measurableSet_Icc).symm
        _ = ∫⁻ x, ∑' ℓ : ℤ, (win a ℓ).indicator (fun _ => ENNReal.ofReal (g x)) x :=
              (lintegral_tsum (fun ℓ => (hΦmeas.indicator measurableSet_Icc).aemeasurable)).symm
        _ = ∫⁻ x, ENNReal.ofReal (g x)
              * (∑' ℓ : ℤ, (win a ℓ).indicator (fun _ => (1 : ℝ≥0∞)) x) := by
              apply lintegral_congr
              intro x
              rw [← ENNReal.tsum_mul_left]
              apply tsum_congr
              intro ℓ
              rw [Set.indicator_apply, Set.indicator_apply]
              by_cases hx : x ∈ win a ℓ <;> simp [hx]
        _ ≤ ∫⁻ x, ENNReal.ofReal (g x) * (↑(n + 1) : ℝ≥0∞) :=
              lintegral_mono (fun x => mul_le_mul_of_nonneg_left (hcount x) zero_le)
        _ = (∫⁻ x, ENNReal.ofReal (g x)) * (↑(n + 1) : ℝ≥0∞) :=
              lintegral_mul_const _ hΦmeas
        _ = (↑(n + 1) : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (g x) := mul_comm _ _
    have hΦtop : ∫⁻ x, ENNReal.ofReal (g x) ≠ ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall hgnn)]
      exact ENNReal.ofReal_ne_top
    have hbnd' : (∑' ℓ : ℤ, ENNReal.ofReal (∫ x in win a ℓ, g x)) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hΦtop) hbnd
    have hcoe : Summable (fun ℓ : ℤ => Real.toNNReal (∫ x in win a ℓ, g x)) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp (by simpa [ENNReal.ofReal] using hbnd')
    have hcoe2 : Summable (fun ℓ : ℤ => ((Real.toNNReal (∫ x in win a ℓ, g x) : ℝ≥0) : ℝ)) :=
      NNReal.summable_coe.mpr hcoe
    refine hcoe2.congr (fun ℓ => ?_)
    rw [Real.coe_toNNReal']
    exact max_eq_left (show 0 ≤ ∫ x in win a ℓ, g x from hbnonneg ℓ)
  -- ## Assembly
  have hasumm : Summable (fun ℓ : ℤ => ∫ u in (0 : ℝ)..T, g ((ℓ : ℝ) + u)) := by
    refine Summable.of_nonneg_of_le (fun ℓ => ?_) hterm hbsumm
    rw [intervalIntegral.integral_of_le hTle]
    exact integral_nonneg (f := fun x : ℝ => g ((ℓ : ℝ) + x)) (fun x => hgnn ((ℓ : ℝ) + x))
  calc ∫ u in (0 : ℝ)..T, (∑' ℓ : ℤ, g ((ℓ : ℝ) + u))
      = ∫ u in Set.Ioc (0 : ℝ) T, (∑' ℓ : ℤ, g ((ℓ : ℝ) + u)) :=
        intervalIntegral.integral_of_le hTle
    _ = ∑' ℓ : ℤ, ∫ u in Set.Ioc (0 : ℝ) T, g ((ℓ : ℝ) + u) := hswap
    _ = ∑' ℓ : ℤ, ∫ u in (0 : ℝ)..T, g ((ℓ : ℝ) + u) :=
        tsum_congr (fun ℓ => (intervalIntegral.integral_of_le hTle).symm)
    _ ≤ ∑' ℓ : ℤ, ∫ x in Set.Icc ((ℓ : ℝ) - a) ((ℓ : ℝ) + a), g x :=
        Summable.tsum_le_tsum hterm hasumm hbsumm

end Work.GM.Affine
