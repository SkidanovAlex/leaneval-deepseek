import ChallengeDeps
import Submission.Work.BoseFixB1.boxQ1_pair_peel
import Submission.Work.BoseFixB1.integrableOn_pairG0_fibre
import Submission.Work.BoseFixB1.integrableOn_pairG0_kernel
import Submission.Work.BoseFixB1.wSmall1Pair_fibre_indicator
import Submission.Work.BoseFixB1S.integrableOn_boxFragments
import Submission.Work.BoseFixB1S.peelPInd_pairMixed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The generic per-pair peel at the sliding box

The two `P_s`-factors `P_s(Q_tΦ)` and `P_s(P_tΦ)` of the FS box projection
`P_{B,i}Ψ = |B|⁻¹(∫_B Ψ(·|i↦z)dz)·1_B(x_i)` both carry the *same* slot-`s` indicator
`1_B(x_s)`, so peeling slot `s` of the centred box `abox (n+1) ℓ` collapses the two-slot weight
`W (x_s) (x_t)` into the box-indicator fibre `∫_B 1_B(y)W(y,x_t)dy = fib (x_t)`, at the price of a
factor `|B|⁻¹`.

This is the `g₀`-kernel (`wSmall1Pair`) companion of `Work.BoseFixB1P.boxQ1_pair_peel`
(which is the `g₂`-kernel statement): the argument is independent of the numerator, so it is
carried out here for an arbitrary weight `W` together with its fibre `fib`. -/
theorem boxPInd_pair_peel_fibre_gen {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : E3) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {W : E3 → E3 → ℝ} {fib : E3 → ℝ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (s : Fin (n + 1)) (t' : Fin n)
    (hInt1 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * W (x s) (x (s.succAbove t')))
      (Submission.BoseGases.abox (n + 1) ℓ) MeasureTheory.volume)
    (hInt2 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X (n + 1) =>
        Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * fib (x (s.succAbove t')))
      (Submission.BoseGases.abox (n + 1) ℓ) MeasureTheory.volume)
    (hfib : ∀ z : E3, (∫ y in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y * W y z) = fib z) :
    (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * W (x s) (x (s.succAbove t')))
      = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
        (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
        Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
          * fib (x (s.succAbove t'))) := by
  classical
  set F : Submission.BoseGases.X (n + 1) → ℝ := fun x =>
      Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) s
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
        * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
        * W (x s) (x (s.succAbove t')) with hFdef
  set G : Submission.BoseGases.X (n + 1) → ℝ := fun x =>
      Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) s
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
        * Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) x
        * fib (x (s.succAbove t')) with hGdef
  have hInt1' : MeasureTheory.IntegrableOn F (Submission.BoseGases.abox (n + 1) ℓ) := by
    rw [hFdef]; exact hInt1
  have hInt2' : MeasureTheory.IntegrableOn G (Submission.BoseGases.abox (n + 1) ℓ) := by
    rw [hGdef]; exact hInt2
  have hL := Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) (i := s) (F := F) hInt1'
  have hR := Submission.BoseGases.abox_integral_peel (n := n) (ℓ := ℓ) (i := s) (F := G) hInt2'
  have hinnerF : ∀ r : Submission.BoseGases.X n,
      (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN n s (y, r)))
        = Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
          * Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
          * fib (r t') := by
    intro r
    simp only [hFdef, Submission.BoseGases.kc_insN_apply_same,
      Submission.BoseGases.kc_insN_apply_succ]
    simpa only [q1P, q1Q, q1Vol, q1Box] using
      (q1_slotPair_inner_general (ℓ := ℓ) (d := d) u s t'
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ)
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ)
        (g := fun y => W y (r t')) (c := fib (r t'))
        (by simpa only [q1Box] using hfib (r t')) r)
  have hinnerG : ∀ r : Submission.BoseGases.X n,
      (∫ y in Submission.BoseGases.acube ℓ, G (Submission.BoseGases.kcInsN n s (y, r)))
        = Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
          * Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
          * fib (r t') * Work.SmallBoxSliding.boxMass ℓ d u := by
    intro r
    simp only [hGdef, Submission.BoseGases.kc_insN_apply_succ]
    simpa only [q1P, q1Q, q1Vol, q1Box] using
      (boxQ1_slotPair_inner_const (ℓ := ℓ) (d := d) hℓ u s t'
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ)
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ)
        r (fib (r t')))
  rw [hL, hR]
  have h1 : (∫ r : Submission.BoseGases.X n,
        (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN n s (y, r)))
        ∂((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)))
      = ∫ r : Submission.BoseGases.X n,
          (Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
            * Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) s
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
            * fib (r t'))
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) := by
    apply integral_congr_ae
    filter_upwards with r
    exact hinnerF r
  have h2 : (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
        * (∫ r : Submission.BoseGases.X n,
            (∫ y in Submission.BoseGases.acube ℓ, G (Submission.BoseGases.kcInsN n s (y, r)))
            ∂((volume : Measure (Submission.BoseGases.X n)).restrict
              (Submission.BoseGases.abox n ℓ)))
      = ∫ r : Submission.BoseGases.X n,
          (Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
            * Work.BoseFixB1S.Q0C.oneRest (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) s
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) (s.succAbove t') Φ) r
            * fib (r t'))
          ∂((volume : Measure (Submission.BoseGases.X n)).restrict
            (Submission.BoseGases.abox n ℓ)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    rw [hinnerG r]
    have hV : (Work.SmallBoxSliding.boxMass ℓ d u : ℝ) ≠ 0 := ne_of_gt hvol
    rw [mul_comm ((Work.SmallBoxSliding.boxMass ℓ d u)⁻¹), mul_assoc,
      mul_inv_cancel₀ hV, mul_one]
  rw [h1, h2]

theorem boxQ1_pair_peel_w1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {s t : Fin N} (hst : s ≠ t) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) s
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
          * (Submission.BoseGases.wSmall1Pair h M ℓ d u (x s) (x t)))
      = (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
        (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) s
              (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
            * (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                (Submission.BoseGases.dlBox ℓ d u) s
                (Work.UBBInputs8.boxPInd (Work.SmallBoxSliding.boxMass ℓ d u)
                  (Submission.BoseGases.dlBox ℓ d u) t Φ) x)
            * (Submission.BoseGases.w1Fibre ℓ
                (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x t))) := by
  classical
  cases N with
  | zero => exact (Nat.not_lt_zero s.val s.isLt).elim
  | succ n =>
    obtain ⟨t', ht'⟩ := Fin.exists_succAbove_eq (x := t) (y := s) hst.symm
    subst ht'
    refine boxPInd_pair_peel_fibre_gen (n := n) (ℓ := ℓ) (d := d) hℓ u hvol
      (W := Submission.BoseGases.wSmall1Pair h M ℓ d u)
      (fib := Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u))
      (Φ := Φ) (s := s) (t' := t') ?_ ?_ ?_
    · exact integrableOn_pairG0_kernel hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u hvol hΦc
        (Fin.succAbove_ne s t').symm
    · exact integrableOn_pairG0_fibre hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u hvol hΦc
        (Fin.succAbove_ne s t').symm
    · intro z
      exact wSmall1Pair_fibre_indicator hvrad h hM hℓ hd u z

end Work.BoseFixB1

end
