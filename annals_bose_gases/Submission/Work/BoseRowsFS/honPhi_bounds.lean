import ChallengeDeps
import Submission.Work.BoseRowsFS.chat_g0_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.honPhi_bounds` — the honest window kernel `φ = Ŵ₁ĝ₀/2` is decaying and Lipschitz

FS §11/§12 (the rows `lem:EstimateIntegral` / `q2exLower`) use the product

    φ(p) := ½·Ŵ₁(p)·ĝ(p),        Ŵ₁ = chat (W1fun v h ℓ),   ĝ = chat (g₀ v h),

and need two things about it:

* **decay** `|φ(p)| ≤ (C a)²/2 /(1+‖p‖)⁴`, i.e. the product of the two decay rows
  `|Ŵ₁(p)|(1+‖p‖)² ≤ Cw a`, `|ĝ(p)|(1+‖p‖)² ≤ Cw a`, where `a = a v`;
* **Lipschitz** `|φ(p) − φ(q)| ≤ 8πR Cw a² ‖p−q‖(1/(1+‖p‖)² + 1/(1+‖q‖)²)`,
  the product rule applied to the two *Lipschitz* rows
  `|Ŵ₁(p) − Ŵ₁(q)| ≤ 16πR a ‖p−q‖` (`Work.BoseGateFS.chat_W1fun_lipschitz`) and
  `|ĝ(p) − ĝ(q)| ≤ 8πR a ‖p−q‖` (`Work.BoseRowsFS.chat_g0_lipschitz`, dominated here
  by the `Ŵ₁` constant `16πR a`: both kernels are supported in `ball 0 R` with `L¹`
  mass `≤ 16π a`).

The *weighted* form is what makes the constants come out exactly: the product-rule
splitting `½(|Ŵ₁(p)|·|ĝ(p)−ĝ(q)| + |Ŵ₁(p)−Ŵ₁(q)|·|ĝ(q)|)` puts one decay row against
each Lipschitz row, so with both Lipschitz constants `16πR a` each point of the
replacement set has the *same* decay weight, and the arithmetic closes as an identity

    ½( (Ca/(1+‖p‖)²)(16πRa‖p−q‖) + (16πRa‖p−q‖)(Ca/(1+‖q‖)²) )
      = 8πR (Ca) a ‖p−q‖ (1/(1+‖p‖)² + 1/(1+‖q‖)²).
-/

namespace Work.BoseRowsFS

noncomputable section

open MeasureTheory

theorem honPhi_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ Cw : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < _root_.BoseGases.a v) (hCw : 0 ≤ Cw)
    (hdecayW : ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2
        ≤ Cw * _root_.BoseGases.a v)
    (hdecayg : ∀ p : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 2
        ≤ Cw * _root_.BoseGases.a v) :
    (∀ p : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
            * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / 2|
          ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 / (1 + ‖p‖) ^ 4)
    ∧ (∀ p q : EuclideanSpace ℝ (Fin 3),
        |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / 2
            - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q / 2|
          ≤ 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2 * ‖p - q‖
              * (1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖q‖) ^ 2)) := by
  -- the `ĝ` Lipschitz row, with constant `8πR a`
  have hglip : ∀ p q : EuclideanSpace ℝ (Fin 3),
      |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
        - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|
      ≤ 8 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ := fun p q =>
    chat_g0_lipschitz hR hv_nonneg hvrad hv_supp p q
  have ha : (0 : ℝ) ≤ _root_.BoseGases.a v := hav.le
  have hCwa : 0 ≤ Cw * _root_.BoseGases.a v := mul_nonneg hCw ha
  constructor
  · -- decay: multiply the two decay rows
    intro p
    have h4 : (0 : ℝ) < (1 + ‖p‖) ^ 4 := by positivity
    have hkey : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p|
        * |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 4
        ≤ Cw ^ 2 * _root_.BoseGases.a v ^ 2 := by
      have h4eq : (1 + ‖p‖ : ℝ) ^ 4 = (1 + ‖p‖) ^ 2 * (1 + ‖p‖) ^ 2 := by ring
      calc |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p|
            * |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 4
          = (|Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| * (1 + ‖p‖) ^ 2)
            * (|Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p| * (1 + ‖p‖) ^ 2) := by
              rw [h4eq]; ring
        _ ≤ (Cw * _root_.BoseGases.a v) * (Cw * _root_.BoseGases.a v) :=
              mul_le_mul (hdecayW p) (hdecayg p) (by positivity) hCwa
        _ = Cw ^ 2 * _root_.BoseGases.a v ^ 2 := by ring
    rw [abs_div, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    refine (div_le_div_iff₀ (show (0 : ℝ) < 2 by norm_num) h4).mpr ?_
    rw [show Cw ^ 2 * _root_.BoseGases.a v ^ 2 / 2 * 2 = Cw ^ 2 * _root_.BoseGases.a v ^ 2
        from by ring]
    exact hkey
  · -- Lipschitz: the product rule
    intro p q
    have hDp : (0 : ℝ) < (1 + ‖p‖) ^ 2 := by positivity
    have hDq : (0 : ℝ) < (1 + ‖q‖) ^ 2 := by positivity
    have hDpnn : 0 ≤ Cw * _root_.BoseGases.a v / (1 + ‖p‖) ^ 2 := div_nonneg hCwa hDp.le
    have hLnn : 0 ≤ 16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hR.le)
        ha) (norm_nonneg _)
    have hWp : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p|
        ≤ Cw * _root_.BoseGases.a v / (1 + ‖p‖) ^ 2 := (le_div_iff₀ hDp).mpr (hdecayW p)
    have hgq : |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|
        ≤ Cw * _root_.BoseGases.a v / (1 + ‖q‖) ^ 2 := (le_div_iff₀ hDq).mpr (hdecayg q)
    have hlipW : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
        - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q|
        ≤ 16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ :=
      Work.BoseGateFS.chat_W1fun_lipschitz hR hℓ hv_nonneg hvrad hv_supp hRℓ p q
    have hlipg : |Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
        - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|
        ≤ 16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ := by
      refine le_trans (hglip p q) ?_
      have h8 : 0 ≤ 8 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hR.le)
          ha) (norm_nonneg _)
      nlinarith [h8]
    -- the algebraic splitting `xy/2 − x'y'/2 = (x(y−y') + (x−x')y')/2`
    have hdecomp : Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p / 2
        - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q / 2
        = (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
             * (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
                - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q)
           + (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
                - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q)
             * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q) / 2 := by ring
    rw [hdecomp, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    have hb1 : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
          * (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
              - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q)|
        ≤ (Cw * _root_.BoseGases.a v / (1 + ‖p‖) ^ 2)
          * (16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖) := by
      rw [abs_mul]
      exact mul_le_mul hWp hlipg (abs_nonneg _) hDpnn
    have hb2 : |(Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
            - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q)
          * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|
        ≤ (16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖)
          * (Cw * _root_.BoseGases.a v / (1 + ‖q‖) ^ 2) := by
      rw [abs_mul]
      exact mul_le_mul hlipW hgq (abs_nonneg _) hLnn
    have harith : ((Cw * _root_.BoseGases.a v / (1 + ‖p‖) ^ 2)
          * (16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖)
        + (16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖)
          * (Cw * _root_.BoseGases.a v / (1 + ‖q‖) ^ 2)) / 2
        = 8 * Real.pi * R * Cw * _root_.BoseGases.a v ^ 2 * ‖p - q‖
            * (1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖q‖) ^ 2) := by ring
    calc |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
             * (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
                - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q)
           + (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
                - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q)
             * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q| / 2
        ≤ (|Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
              * (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
                  - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q)|
            + |(Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
                  - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q)
                * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q|) / 2 := by
          have h := abs_add_le (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
              * (Work.BoseFixR.chat (Submission.BoseGases.g0 v h) p
                  - Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q))
            ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
                - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q)
              * Work.BoseFixR.chat (Submission.BoseGases.g0 v h) q)
          linarith
      _ ≤ ((Cw * _root_.BoseGases.a v / (1 + ‖p‖) ^ 2)
              * (16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖)
            + (16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖)
              * (Cw * _root_.BoseGases.a v / (1 + ‖q‖) ^ 2)) / 2 := by linarith
      _ = _ := harith

end

end Work.BoseRowsFS
