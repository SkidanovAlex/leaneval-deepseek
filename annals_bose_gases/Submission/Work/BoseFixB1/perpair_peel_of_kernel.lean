import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Q1Peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

/-- **Per-pair q1 peel + replacement for an arbitrary symmetric-fibre kernel `K`** (`depends_on` supplies `Submission.Work.Q1Peel`).

For an arbitrary kernel `K : ℝ³ → ℝ³ → ℝ` whose cube fibre equals `w1Fibre ℓ K` (premise `hsym`, the abstract form of "`K` is symmetric"), with `w1Fibre ℓ K` a.e.-strongly measurable and bounded on `acube ℓ` (premises `hfibaem`, `hfibbd`), and with the three slot integrabilities available (premises `hInt1`–`hInt3`), the per-pair peel identity holds for all `i ≠ j`:

`∫ (P_jQ_iΦ)·(P_jP_iΦ)·K(x_j,x_i) = (ℓ³)⁻¹·∫ (P_jQ_iΦ)·(P_iΦ)·(w1Fibre ℓ K)(x_i)`

The proof is `q1_lhs_closed` + `q1_pair_replace` of `Submission/Work/Q1Peel.lean` with the global kernel `wPairC ℓ (g2 v h)` replaced by `K`: peel the slot `j` (`Submission.BoseGases.abox_integral_peel`), use `P_j`-constancy in slot `j` (`Submission.BoseGases.aP_kcInsN`), the fibre identity `hsym`, and replace `P_jP_iΦ` by `P_iΦ` through the orthogonality `∫(P_jQ_iΦ)(P_iQ_jΦ)·fibre = 0` (`Submission.BoseGases.q1_ortho`). -/
theorem perpair_peel_of_kernel {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {C : ℝ}
    (hsym : ∀ z : EuclideanSpace ℝ (Fin 3), (∫ y in Submission.BoseGases.acube ℓ, K y z)
        = Submission.BoseGases.w1Fibre ℓ K z)
    (hfibaem : MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.w1Fibre ℓ K)
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    (hfibbd : ∀ z ∈ Submission.BoseGases.acube ℓ, |Submission.BoseGases.w1Fibre ℓ K z| ≤ C)
    (hInt1 : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn
        (fun x => (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) * K (x j) (x i))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hInt2 : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn
        (fun x => (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x)
          * Submission.BoseGases.w1Fibre ℓ K (x i))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hInt3 : ∀ i j : Fin N, i ≠ j → MeasureTheory.IntegrableOn
        (fun x => (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ i Φ x)
          * Submission.BoseGases.w1Fibre ℓ K (x i))
        (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    ∀ i j : Fin N, i ≠ j →
      (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) * K (x j) (x i))
      = (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox N ℓ,
        (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
          * (Submission.BoseGases.aP ℓ i Φ x)
          * Submission.BoseGases.w1Fibre ℓ K (x i))
    := by
  classical
  intro i j hij
  cases N with
  | zero => exact Fin.elim0 i
  | succ n =>
    let F : Submission.BoseGases.X (n + 1) → ℝ := fun x =>
      (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
        * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x) * K (x j) (x i)
    let H : Submission.BoseGases.X (n + 1) → ℝ := fun x =>
      (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
        * (Submission.BoseGases.aP ℓ i Φ x) * Submission.BoseGases.w1Fibre ℓ K (x i)
    have hFint : IntegrableOn F (Submission.BoseGases.abox (n + 1) ℓ) volume := by
      simpa only [F] using hInt1 i j hij
    have hHint : IntegrableOn H (Submission.BoseGases.abox (n + 1) ℓ) volume := by
      simpa only [H] using hInt3 i j hij
    -- the per-`r` fibre identity: peel the `j`-slot on both sides
    have hinner : ∀ r : Submission.BoseGases.X n,
        (∫ y in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN n j (y, r)))
        = (ℓ ^ 3)⁻¹ *
            (∫ y in Submission.BoseGases.acube ℓ, H (Submission.BoseGases.kcInsN n j (y, r))) := by
      intro r
      let ci : EuclideanSpace ℝ (Fin 3) := (Submission.BoseGases.kcInsN n j (0, r)) i
      let CA : ℝ := (1 / ℓ ^ 3) * (∫ y in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aQ ℓ i Φ) (Submission.BoseGases.kcInsN n j (y, r)))
      let CB : ℝ := (1 / ℓ ^ 3) * (∫ y in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aP ℓ i Φ) (Submission.BoseGases.kcInsN n j (y, r)))
      have hAcst : ∀ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ)
            (Submission.BoseGases.kcInsN n j (y, r)) = CA := by
        intro y
        dsimp only [CA]
        exact Submission.BoseGases.aP_kcInsN (i := j) y r
      have hBcst : ∀ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ)
            (Submission.BoseGases.kcInsN n j (y, r)) = CB := by
        intro y
        dsimp only [CB]
        exact Submission.BoseGases.aP_kcInsN (i := j) y r
      have hci : ∀ y : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.kcInsN n j (y, r)) i = ci := by
        intro y
        exact Submission.BoseGases.kc_insN_other_indep n j y 0 r i hij
      have hyj : ∀ y : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.kcInsN n j (y, r)) j = y := fun y =>
        Submission.BoseGases.kc_insN_apply_same n j y r
      have hFy : (∫ y in Submission.BoseGases.acube ℓ,
            F (Submission.BoseGases.kcInsN n j (y, r)))
          = CA * CB * Submission.BoseGases.w1Fibre ℓ K ci := by
        calc
          (∫ y in Submission.BoseGases.acube ℓ,
              F (Submission.BoseGases.kcInsN n j (y, r)))
              = ∫ y in Submission.BoseGases.acube ℓ, CA * CB * K y ci := by
                  apply integral_congr_ae
                  refine ae_of_all _ (fun y => ?_)
                  dsimp only [F]
                  rw [hAcst y, hBcst y, hyj y, hci y]
          _ = CA * CB * (∫ y in Submission.BoseGases.acube ℓ, K y ci) := by
                  rw [integral_const_mul]
          _ = CA * CB * Submission.BoseGases.w1Fibre ℓ K ci := by rw [hsym ci]
      have hCB : (∫ y in Submission.BoseGases.acube ℓ,
            (Submission.BoseGases.aP ℓ i Φ) (Submission.BoseGases.kcInsN n j (y, r)))
          = ℓ ^ 3 * CB := by
        dsimp only [CB]
        field_simp
      have hHy : (∫ y in Submission.BoseGases.acube ℓ,
            H (Submission.BoseGases.kcInsN n j (y, r)))
          = (ℓ ^ 3) * (CA * CB * Submission.BoseGases.w1Fibre ℓ K ci) := by
        calc
          (∫ y in Submission.BoseGases.acube ℓ,
              H (Submission.BoseGases.kcInsN n j (y, r)))
              = ∫ y in Submission.BoseGases.acube ℓ,
                  (CA * Submission.BoseGases.w1Fibre ℓ K ci)
                    * ((Submission.BoseGases.aP ℓ i Φ)
                        (Submission.BoseGases.kcInsN n j (y, r))) := by
                  apply integral_congr_ae
                  refine ae_of_all _ (fun y => ?_)
                  dsimp only [H]
                  rw [hAcst y, hci y]
                  ring
          _ = (CA * Submission.BoseGases.w1Fibre ℓ K ci)
                * (∫ y in Submission.BoseGases.acube ℓ,
                    (Submission.BoseGases.aP ℓ i Φ)
                      (Submission.BoseGases.kcInsN n j (y, r))) := by
                  rw [integral_const_mul]
          _ = (CA * Submission.BoseGases.w1Fibre ℓ K ci) * (ℓ ^ 3 * CB) := by rw [hCB]
          _ = (ℓ ^ 3) * (CA * CB * Submission.BoseGases.w1Fibre ℓ K ci) := by ring
      rw [hFy, hHy]
      field_simp
    have hpeelF := Submission.BoseGases.abox_integral_peel (n := n) (i := j) F hFint
    have hpeelH := Submission.BoseGases.abox_integral_peel (n := n) (i := j) H hHint
    calc
      (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
            * (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Φ) x)
            * K (x j) (x i))
          = ∫ x in Submission.BoseGases.abox (n + 1) ℓ, F x := by simp only [F]
      _ = ∫ r : Submission.BoseGases.X n,
            (∫ y in Submission.BoseGases.acube ℓ,
              F (Submission.BoseGases.kcInsN n j (y, r)))
              ∂((volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ)) := hpeelF
      _ = ∫ r : Submission.BoseGases.X n,
            (ℓ ^ 3)⁻¹ *
              (∫ y in Submission.BoseGases.acube ℓ,
                H (Submission.BoseGases.kcInsN n j (y, r)))
              ∂((volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ)) := by
            apply integral_congr_ae
            refine ae_of_all _ (fun r => ?_)
            exact hinner r
      _ = (ℓ ^ 3)⁻¹ * ∫ r : Submission.BoseGases.X n,
            (∫ y in Submission.BoseGases.acube ℓ,
              H (Submission.BoseGases.kcInsN n j (y, r)))
              ∂((volume : Measure (Submission.BoseGases.X n)).restrict
                  (Submission.BoseGases.abox n ℓ)) := by
            rw [integral_const_mul]
      _ = (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) ℓ, H x := by rw [hpeelH]
      _ = (ℓ ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (n + 1) ℓ,
          (Submission.BoseGases.aP ℓ j (Submission.BoseGases.aQ ℓ i Φ) x)
            * (Submission.BoseGases.aP ℓ i Φ x)
            * Submission.BoseGases.w1Fibre ℓ K (x i)) := by simp only [H]

end Work.BoseFixB1
