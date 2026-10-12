import ChallengeDeps
import Submission.Work.BoseFixB1.KernelFacts
import Submission.Work.BoseFixB1.boxQ1_pair_integrableL
import Submission.Work.BoseFixB1.boxQ1_slotPair_inner_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Pointwise structure of `q1P` at an inserted configuration -/

/-- `q1P` at a configuration whose slot `i` has been set to `t`: the box indicator times the
slot-independent one-slot mean `Q0C.oneRest`. -/
lemma q1P_kcInsN {ℓ d : ℝ} (u : E3) {n : ℕ} (i : Fin (n + 1))
    (Ψ : X (n + 1) → ℝ) (t : E3) (r : X n) :
    q1P ℓ d u i Ψ (kcInsN n i (t, r))
      = (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) t
        * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) i Ψ r := by
  have hh := Work.BoseFixB1S.Q0C.boxPInd_kcInsN (q1Vol ℓ d u) (q1Box ℓ d u) i Ψ t r
  simpa only [q1P, Work.BoseFixB1S.Q0C.oneRest_def] using hh

/-- **Inner slot-`s` integral, general fibre form.**  For an arbitrary `g` whose box-indicator
integral equals `c`, the `y`-integral of the product of the two `P_s`-factors against `g` factorises
into the two slot means and `c`. -/
lemma q1_slotPair_inner_general {ℓ d : ℝ} (u : E3) {n : ℕ} (s : Fin (n + 1)) (t' : Fin n)
    (Ψ₁ Ψ₂ : X (n + 1) → ℝ) {g : E3 → ℝ} {c : ℝ}
    (hg : (∫ y in acube ℓ, (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y * g y) = c)
    (r : X n) :
    (∫ y in acube ℓ,
        q1P ℓ d u s Ψ₁ (kcInsN n s (y, r)) * q1P ℓ d u s Ψ₂ (kcInsN n s (y, r)) * g y)
      = Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₁ r
        * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₂ r * c := by
  have hpt : ∀ y : E3,
      q1P ℓ d u s Ψ₁ (kcInsN n s (y, r)) * q1P ℓ d u s Ψ₂ (kcInsN n s (y, r)) * g y
        = (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y
          * (Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₁ r
              * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₂ r * g y) := by
    intro y
    rw [q1P_kcInsN, q1P_kcInsN]
    by_cases hy : y ∈ q1Box ℓ d u
    · simp only [Set.indicator_of_mem hy]; ring
    · simp only [Set.indicator_of_notMem hy]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [show (∫ y in acube ℓ, (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y
        * (Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₁ r
            * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₂ r * g y))
      = (Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₁ r
          * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s Ψ₂ r)
        * (∫ y in acube ℓ, (q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) y * g y) from by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring]
  rw [hg]

/-! ## The core peel -/

/-- **Core peel with the two integrabilities assumed.**  Peeling the slot `s` of the centred box
and collapsing the localised `g₂`-kernel into its second-slot fibre. -/
theorem boxQ1_pair_peel_of_integrable {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    (hvrad : _root_.BoseGases.IsRadial v) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (hvol : 0 < q1Vol ℓ d u)
    {N : ℕ} {Φ : X N → ℝ} {s t : Fin N} (hst : s ≠ t)
    (hInt1 : MeasureTheory.IntegrableOn
      (fun x : X N =>
        (q1P ℓ d u s (q1Q ℓ d u t Φ) x) * (q1P ℓ d u s (q1P ℓ d u t Φ) x)
          * (q1W2 h M ℓ d u (x s) (x t)))
      (abox N ℓ))
    (hInt2 : MeasureTheory.IntegrableOn
      (fun x : X N =>
        (q1P ℓ d u s (q1Q ℓ d u t Φ) x) * (q1P ℓ d u s (q1P ℓ d u t Φ) x)
          * (q1Fib2 h M ℓ d u (x t)))
      (abox N ℓ)) :
    (∫ x in abox N ℓ,
        (q1P ℓ d u s (q1Q ℓ d u t Φ) x) * (q1P ℓ d u s (q1P ℓ d u t Φ) x)
          * (q1W2 h M ℓ d u (x s) (x t)))
      = (1 / q1Vol ℓ d u)
        * (∫ x in abox N ℓ,
        (q1P ℓ d u s (q1Q ℓ d u t Φ) x) * (q1P ℓ d u s (q1P ℓ d u t Φ) x)
          * (q1Fib2 h M ℓ d u (x t))) := by
  classical
  cases N with
  | zero => exact (Nat.not_lt_zero s.val s.isLt).elim
  | succ n =>
    obtain ⟨t', ht'⟩ := Fin.exists_succAbove_eq (x := t) (y := s) hst.symm
    subst ht'
    set F : X (n + 1) → ℝ := fun x =>
      (q1P ℓ d u s (q1Q ℓ d u (s.succAbove t') Φ) x)
        * (q1P ℓ d u s (q1P ℓ d u (s.succAbove t') Φ) x)
        * (q1W2 h M ℓ d u (x s) (x (s.succAbove t'))) with hFdef
    set G : X (n + 1) → ℝ := fun x =>
      (q1P ℓ d u s (q1Q ℓ d u (s.succAbove t') Φ) x)
        * (q1P ℓ d u s (q1P ℓ d u (s.succAbove t') Φ) x)
        * (q1Fib2 h M ℓ d u (x (s.succAbove t'))) with hGdef
    have hInt1' : MeasureTheory.IntegrableOn F (abox (n + 1) ℓ) := by
      rw [hFdef]; exact hInt1
    have hInt2' : MeasureTheory.IntegrableOn G (abox (n + 1) ℓ) := by
      rw [hGdef]; exact hInt2
    have hL := abox_integral_peel (n := n) (ℓ := ℓ) (i := s) (F := F) hInt1'
    have hR := abox_integral_peel (n := n) (ℓ := ℓ) (i := s) (F := G) hInt2'
    have hinnerF : ∀ r : X n, (∫ y : E3 in acube ℓ, F (kcInsN n s (y, r)))
        = Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
            (q1Q ℓ d u (s.succAbove t') Φ) r
          * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
            (q1P ℓ d u (s.succAbove t') Φ) r
          * q1Fib2 h M ℓ d u (r t') := by
      intro r
      simp only [hFdef, kc_insN_apply_same, kc_insN_apply_succ]
      exact q1_slotPair_inner_general u s t' _ _
        (hg := q1W2_fibre_first_indicator h hM hvrad hℓ hd u (r t')) r
    have hinnerG : ∀ r : X n, (∫ y : E3 in acube ℓ, G (kcInsN n s (y, r)))
        = (Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
              (q1Q ℓ d u (s.succAbove t') Φ) r
            * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
              (q1P ℓ d u (s.succAbove t') Φ) r
            * q1Fib2 h M ℓ d u (r t')) * q1Vol ℓ d u := by
      intro r
      simp only [hGdef, kc_insN_apply_succ]
      exact boxQ1_slotPair_inner_const hℓ u s t' _ _ r (q1Fib2 h M ℓ d u (r t'))
    rw [hL, hR]
    have h1 : (∫ r : X n, (∫ y : E3 in acube ℓ, F (kcInsN n s (y, r)))
          ∂((volume : Measure (X n)).restrict (abox n ℓ)))
        = ∫ r : X n, (Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
              (q1Q ℓ d u (s.succAbove t') Φ) r
            * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
              (q1P ℓ d u (s.succAbove t') Φ) r
            * q1Fib2 h M ℓ d u (r t'))
          ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
      apply integral_congr_ae
      filter_upwards with r
      exact hinnerF r
    have h2 : (1 / q1Vol ℓ d u)
          * (∫ r : X n, (∫ y : E3 in acube ℓ, G (kcInsN n s (y, r)))
              ∂((volume : Measure (X n)).restrict (abox n ℓ)))
        = ∫ r : X n, (Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
              (q1Q ℓ d u (s.succAbove t') Φ) r
            * Work.BoseFixB1S.Q0C.oneRest (q1Vol ℓ d u) (q1Box ℓ d u) s
              (q1P ℓ d u (s.succAbove t') Φ) r
            * q1Fib2 h M ℓ d u (r t'))
          ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with r
      rw [hinnerG r]
      have hV : (q1Vol ℓ d u : ℝ) ≠ 0 := ne_of_gt hvol
      field_simp
    rw [h1, h2]

/-- Integrability of the two `P_s`-factors against the fibre `fib₂` over the box (fallback
version carrying `0 < q1Vol`, which the caller has). -/
private lemma q1_pair_integrableR_aux {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : _root_.tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : E3) (hvol : 0 < q1Vol ℓ d u)
    {N : ℕ} {Φ : X N → ℝ} (hΦc : Continuous Φ) {s t : Fin N} (hst : s ≠ t) :
    MeasureTheory.IntegrableOn
      (fun x : X N =>
        (q1P ℓ d u s (q1Q ℓ d u t Φ) x) * (q1P ℓ d u s (q1P ℓ d u t Φ) x)
          * (q1Fib2 h M ℓ d u (x t)))
      (abox N ℓ) := by
  classical
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := Work.BoseFixB1S.exists_abox_bound (N := N) hℓ hΦc
  have hA : MeasurableSet (q1Box ℓ d u) := q1Box_measurableSet ℓ d u
  have hAc : q1Box ℓ d u ⊆ acube ℓ := q1Box_subset_acube ℓ d u
  have hvolA : q1Vol ℓ d u = ((volume : Measure E3) (q1Box ℓ d u)).toReal := by
    simpa only [Measure.real_def] using q1Vol_eq_real ℓ d u
  have hPt : ∀ x ∈ abox N ℓ, |q1P ℓ d u t Φ x| ≤ CΦ := fun x hx => by
    simpa only [q1P, q1Vol, q1Box] using
      Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := q1Vol ℓ d u)
        hℓ hvol hA hvolA hAc t (Ψ := Φ) hCΦ x hx
  have hQb : ∀ x ∈ abox N ℓ, |q1Q ℓ d u t Φ x| ≤ 2 * CΦ := by
    intro x hx
    have h1 : |(q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) (x t) * Φ x| ≤ CΦ := by
      have hind : |(q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) (x t)| ≤ 1 := by
        by_cases hxt : x t ∈ q1Box ℓ d u
        · rw [Set.indicator_of_mem hxt]; norm_num
        · rw [Set.indicator_of_notMem hxt]; norm_num
      calc |(q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) (x t) * Φ x|
          = |(q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) (x t)| * |Φ x| := abs_mul _ _
        _ ≤ 1 * CΦ := mul_le_mul hind (hCΦ x hx) (abs_nonneg _) (by norm_num)
        _ = CΦ := one_mul CΦ
    have h2 : |q1P ℓ d u t Φ x| ≤ CΦ := hPt x hx
    calc |q1Q ℓ d u t Φ x|
        = |(q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) (x t) * Φ x - q1P ℓ d u t Φ x| := rfl
      _ ≤ |(q1Box ℓ d u).indicator (fun _ => (1 : ℝ)) (x t) * Φ x| + |q1P ℓ d u t Φ x| :=
          abs_sub _ _
      _ ≤ CΦ + CΦ := add_le_add h1 h2
      _ = 2 * CΦ := by ring
  have hPs1 : ∀ x ∈ abox N ℓ, |q1P ℓ d u s (q1Q ℓ d u t Φ) x| ≤ 2 * CΦ := fun x hx => by
    simpa only [q1P, q1Vol, q1Box] using
      Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := q1Vol ℓ d u)
        hℓ hvol hA hvolA hAc s (Ψ := q1Q ℓ d u t Φ) hQb x hx
  have hPs2 : ∀ x ∈ abox N ℓ, |q1P ℓ d u s (q1P ℓ d u t Φ) x| ≤ CΦ := fun x hx => by
    simpa only [q1P, q1Vol, q1Box] using
      Work.BoseFixB1S.abs_boxPInd_le (N := N) (ℓ := ℓ) (volA := q1Vol ℓ d u)
        hℓ hvol hA hvolA hAc s (Ψ := q1P ℓ d u t Φ) hPt x hx
  have hfib : ∀ z : E3, |q1Fib2 h M ℓ d u z| ≤ wFibC M (16 * Real.pi * _root_.BoseGases.a v) := by
    intro z
    simpa only [q1Fib2, Submission.BoseGases.w1Fibre] using
      wSmall2_fibre_abs_le_gen hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z
  have hg2aem : AEMeasurable (Submission.BoseGases.g2 v h) (volume : Measure E3) :=
    (Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h).aemeasurable
  have hfaes : AEStronglyMeasurable (fun z : E3 => q1Fib2 h M ℓ d u z)
      (volume.restrict (acube ℓ)) := by
    simpa only [q1Fib2, Submission.BoseGases.w1Fibre] using
      Work.BoseFixB1.aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u
        hg2aem.aestronglyMeasurable.aemeasurable
  have hFm : Measurable (q1Q ℓ d u t Φ) := by
    have hh := Work.SlotWord.measurable_boxQInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA t
      (Ψ := Φ) hΦc.measurable
    simpa only [q1Q, q1Vol, q1Box] using hh
  have hPtm : Measurable (q1P ℓ d u t Φ) := by
    have hh := Work.BoseFixB1S.measurable_boxPInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA t
      (Ψ := Φ) hΦc.measurable
    simpa only [q1P, q1Vol, q1Box] using hh
  have hP1m : Measurable (q1P ℓ d u s (q1Q ℓ d u t Φ)) := by
    have hh := Work.BoseFixB1S.measurable_boxPInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA s
      (Ψ := q1Q ℓ d u t Φ) hFm
    simpa only [q1P, q1Vol, q1Box] using hh
  have hP2m : Measurable (q1P ℓ d u s (q1P ℓ d u t Φ)) := by
    have hh := Work.BoseFixB1S.measurable_boxPInd (N := N) (q1Vol ℓ d u) (q1Box ℓ d u) hA s
      (Ψ := q1P ℓ d u t Φ) hPtm
    simpa only [q1P, q1Vol, q1Box] using hh
  refine MeasureTheory.IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le)
    (((hP1m.mul hP2m).aestronglyMeasurable).mul
      (Submission.BoseGases.aem_comp_coord' (N := N) (ℓ := ℓ) t hfaes))
    (2 * CΦ * CΦ * wFibC M (16 * Real.pi * _root_.BoseGases.a v)) ?_
  rw [MeasureTheory.ae_restrict_iff' (abox_measurable N ℓ)]
  refine ae_of_all _ (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hPs1 x hx) (hPs2 x hx) (abs_nonneg _) (by positivity))
    (hfib (x t)) (abs_nonneg _) (by positivity)

/-- Per-pair peel: both `P_s`-factors are `1_A(x s)` times a slot-`s`-independent
factor, so the slot-`s` integral collapses the kernel `w₂(x s, x t)` into its second-slot
fibre `fib₂(x t) = ∫_{acube ℓ} w₂(x t, y) dy` (using support in the sliding box and the
evenness of the numerator `g₂`).  Available inputs (in `Work.BoseFixB1`): the pointwise
structure `Work.UBBInputs8.boxPInd_kcInsN`, the peel
`Submission.Work.SmallBoxPairIdent.abox_integral_peel_gen`, the fibre identities
`Work.BoseFixB1.q1W2_fibre_first_indicator` / `q1_indicator_acube`, plus
`Work.BoseFixB1.q1W2_eq_zero_of_notMem`, `Work.BoseFixB1.q1W2_symm`,
`Work.SmallBoxSliding.dlBox_subset_acube`,
`Work.SmallBoxSliding.measurableSet_dlBox`,
`Work.SmallBoxSliding.boxMass_eq_measureReal`. -/
theorem boxQ1_pair_peel {v : Work.BoseFixB1.E3 → ℝ} {R0 : ℝ}
    (hv_supp : _root_.tsupport v ⊆ Metric.ball (0 : Work.BoseFixB1.E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : Work.BoseFixB1.E3) (hvol : 0 < Work.BoseFixB1.q1Vol ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1.q1P ℓ d u s (Work.BoseFixB1.q1Q ℓ d u t Φ) x)
          * (Work.BoseFixB1.q1P ℓ d u s (Work.BoseFixB1.q1P ℓ d u t Φ) x)
          * (Work.BoseFixB1.q1W2 h M ℓ d u (x s) (x t)))
      = (1 / Work.BoseFixB1.q1Vol ℓ d u)
        * (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.BoseFixB1.q1P ℓ d u s (Work.BoseFixB1.q1Q ℓ d u t Φ) x)
          * (Work.BoseFixB1.q1P ℓ d u s (Work.BoseFixB1.q1P ℓ d u t Φ) x)
          * (Work.BoseFixB1.q1Fib2 h M ℓ d u (x t))) := by
  exact boxQ1_pair_peel_of_integrable h hM hvrad hℓ hd u hvol hst
    (boxQ1_pair_integrableL hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u hΦc hst)
    (q1_pair_integrableR_aux hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u hvol hΦc hst)

end Work.BoseFixB1
