import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1B.chiB_abs_le_boxMargin
import Submission.Work.BoseFixB1S.chiSmall_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lipschitz bound for the two-factor sliding box cutoff `chiSmallB`

The sliding small-box cutoff of `Submission.Work.ChiSmall` is the product

    `chiSmallB M ℓ d u x = chiScale ℓ x · chiSmall M ((ℓ*d)⁻¹ • x - u)`

of the corpus bump at the `ℓ` scale and the explicit cosine-`M`-th-power bump at the `ℓd` scale.
The lemma proved here is that, for `ℓ, d > 0` and `M ≥ 1` (and every `u`), this function is
Lipschitz in `x` — an *existential* constant is enough for the use in the sector arguments.

Route (a product-rule argument, no differentiability of `chiSmall` needed):

* `Work.BoseFixB1B.exists_lipschitz_chi` — the corpus bump `chi` is Lipschitz (it is `C^∞` with
  compact support); scaling to `chiScale ℓ` divides the constant by `ℓ`;
* `Work.BoseFixB1S.chiSmall_lipschitz` — the cosine bump `chiSmall M` is Lipschitz; translating
  by `u` and rescaling the argument by `(ℓd)⁻¹` divides the constant by `ℓd`;
* the two global sup bounds `|chiScale ℓ x| ≤ chiSupAbs`
  (`Submission.BoseGases.chiScale_abs_le_sup`) and `|chiSmall M z| ≤ chiSmallDecay M`
  (`Submission.BoseGases.chiSmall_decay_coord_le_decay`) then give, via
  `|A x B x − A y B y| ≤ |A x − A y|·|B x| + |A y|·|B x − B y|`, the constant
  `L = (C·ℓ⁻¹)·chiSmallDecay M + chiSupAbs·(L₁·(ℓd)⁻¹)`.
-/

namespace Work.BoseFixB1.SectorAux

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The scaled corpus bump `x ↦ chiScale ℓ x = chi (ℓ⁻¹ • x)` inherits the Lipschitz constant of
`chi`, divided by `ℓ`. -/
lemma chiScale_lipschitz {C ℓ : ℝ} (hC : ∀ a b : ℝ³, |chi a - chi b| ≤ C * ‖a - b‖)
    (hℓ : 0 < ℓ) (x y : ℝ³) :
    |chiScale ℓ x - chiScale ℓ y| ≤ C * ℓ⁻¹ * ‖x - y‖ := by
  have h := hC (ℓ⁻¹ • x) (ℓ⁻¹ • y)
  have hd : ‖(ℓ⁻¹ : ℝ) • x - ℓ⁻¹ • y‖ = ℓ⁻¹ * ‖x - y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hℓ.le)]
  rw [hd] at h
  have hx : chiScale ℓ x = chi (ℓ⁻¹ • x) := rfl
  have hy : chiScale ℓ y = chi (ℓ⁻¹ • y) := rfl
  rw [hx, hy]
  calc |chi (ℓ⁻¹ • x) - chi (ℓ⁻¹ • y)| ≤ C * (ℓ⁻¹ * ‖x - y‖) := h
    _ = C * ℓ⁻¹ * ‖x - y‖ := by ring

/-- The small-box factor `x ↦ chiSmall M ((ℓ*d)⁻¹ • x - u)` is Lipschitz with constant
`L * (ℓ*d)⁻¹`, obtained from a Lipschitz bound `L` for `chiSmall M` by translating with `u` and
rescaling the argument by `(ℓ*d)⁻¹`. -/
lemma chiSmall_smul_sub_lipschitz {M : ℕ} {L ℓ d : ℝ}
    (hL : ∀ y t : ℝ³, |chiSmall M y - chiSmall M (y - t)| ≤ L * ‖t‖)
    (hc : 0 < ℓ * d) (u x y : ℝ³) :
    |chiSmall M ((ℓ * d)⁻¹ • x - u) - chiSmall M ((ℓ * d)⁻¹ • y - u)|
      ≤ L * (ℓ * d)⁻¹ * ‖x - y‖ := by
  have h := hL ((ℓ * d)⁻¹ • x - u) ((ℓ * d)⁻¹ • (x - y))
  have hsub : (ℓ * d)⁻¹ • x - u - (ℓ * d)⁻¹ • (x - y) = (ℓ * d)⁻¹ • y - u := by
    rw [smul_sub]
    abel
  rw [hsub] at h
  have hd : ‖(ℓ * d)⁻¹ • (x - y)‖ = (ℓ * d)⁻¹ * ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hc.le)]
  rw [hd] at h
  calc |chiSmall M ((ℓ * d)⁻¹ • x - u) - chiSmall M ((ℓ * d)⁻¹ • y - u)|
      ≤ L * ((ℓ * d)⁻¹ * ‖x - y‖) := h
    _ = L * (ℓ * d)⁻¹ * ‖x - y‖ := by ring

theorem chiSmallB_lipschitz {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.chiSmallB M ℓ d u x - Submission.BoseGases.chiSmallB M ℓ d u y|
        ≤ L * ‖x - y‖ := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1B.exists_lipschitz_chi
  obtain ⟨L₁, hL₁0, hL₁⟩ := Work.BoseFixB1S.chiSmall_lipschitz (M := M) hM
  have hℓd : 0 < ℓ * d := mul_pos hℓ hd
  have hℓinv : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
  have hℓdinv : 0 ≤ (ℓ * d)⁻¹ := inv_nonneg.mpr hℓd.le
  refine ⟨C * ℓ⁻¹ * chiSmallDecay M + chiSupAbs * (L₁ * (ℓ * d)⁻¹), ?_, ?_⟩
  · exact add_nonneg (mul_nonneg (mul_nonneg hC0 hℓinv) (chiSmallDecay_nonneg M))
      (mul_nonneg chiSupAbs_nonneg (mul_nonneg hL₁0 hℓdinv))
  · intro x y
    have hA := chiScale_lipschitz hC hℓ x y
    have hB := chiSmall_smul_sub_lipschitz (M := M) hL₁ hℓd u x y
    have hBx : |chiSmall M ((ℓ * d)⁻¹ • x - u)| ≤ chiSmallDecay M :=
      chiSmall_decay_coord_le_decay hM _
    have hAy : |chiScale ℓ y| ≤ chiSupAbs := chiScale_abs_le_sup ℓ y
    have hkey : Submission.BoseGases.chiSmallB M ℓ d u x
          - Submission.BoseGases.chiSmallB M ℓ d u y
        = (chiScale ℓ x - chiScale ℓ y) * chiSmall M ((ℓ * d)⁻¹ • x - u)
          + chiScale ℓ y * (chiSmall M ((ℓ * d)⁻¹ • x - u)
              - chiSmall M ((ℓ * d)⁻¹ • y - u)) := by
      simp only [chiSmallB]
      ring
    rw [hkey]
    have h1 : |(chiScale ℓ x - chiScale ℓ y) * chiSmall M ((ℓ * d)⁻¹ • x - u)|
        ≤ (C * ℓ⁻¹ * ‖x - y‖) * chiSmallDecay M := by
      rw [abs_mul]
      exact mul_le_mul hA hBx (abs_nonneg _)
        (mul_nonneg (mul_nonneg hC0 hℓinv) (norm_nonneg _))
    have h2 : |chiScale ℓ y * (chiSmall M ((ℓ * d)⁻¹ • x - u)
          - chiSmall M ((ℓ * d)⁻¹ • y - u))|
        ≤ chiSupAbs * (L₁ * (ℓ * d)⁻¹ * ‖x - y‖) := by
      rw [abs_mul]
      exact mul_le_mul hAy hB (abs_nonneg _) chiSupAbs_nonneg
    calc |(chiScale ℓ x - chiScale ℓ y) * chiSmall M ((ℓ * d)⁻¹ • x - u)
          + chiScale ℓ y * (chiSmall M ((ℓ * d)⁻¹ • x - u)
              - chiSmall M ((ℓ * d)⁻¹ • y - u))|
        ≤ |(chiScale ℓ x - chiScale ℓ y) * chiSmall M ((ℓ * d)⁻¹ • x - u)|
          + |chiScale ℓ y * (chiSmall M ((ℓ * d)⁻¹ • x - u)
              - chiSmall M ((ℓ * d)⁻¹ • y - u))| := abs_add_le _ _
      _ ≤ (C * ℓ⁻¹ * ‖x - y‖) * chiSmallDecay M
          + chiSupAbs * (L₁ * (ℓ * d)⁻¹ * ‖x - y‖) := by linarith
      _ = (C * ℓ⁻¹ * chiSmallDecay M + chiSupAbs * (L₁ * (ℓ * d)⁻¹)) * ‖x - y‖ := by ring

end Work.BoseFixB1.SectorAux
