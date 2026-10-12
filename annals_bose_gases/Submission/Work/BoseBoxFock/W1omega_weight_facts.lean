import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.W1fun_integrable_of_regime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.W1omega_weight_facts`

The `L¹`-weight facts about the χ-renormalised kernel `W₁ω = wScaled ℓ (g₀ω)`
(`g₀ = v(1−ω)`, `ω = Classical.choose h`), needed by the `L¹`-tail chapter, together
with the two **Coulomb-energy** integrabilities: for the single weight `W₁ω` (which is
the Coulomb statement of the sibling `L1Tails.W1fun_coulomb_le`) and — the new content
here — for the **sum** `W₁ + W₁ω`, the weight that actually multiplies the two-body
potential in FS's §4 decomposition.

* integrability, a.e. nonnegativity, the support bound `R ≤ ‖x‖ ⇒ W₁ω x = 0` and the
  a.e. domination by `(1 + 2C(R/ℓ)²)g₀` are the sibling `L1Tails.w1omegaFun_facts`;
* evenness is the radiality of `v` and of the scattering solution `ω`
  (`g0_even`, `radial_neg`), since `wScaled ℓ (g₀ω)` is the quotient of an even
  numerator by the even renormalisation `convScale ℓ` (`convScale_symm`);
* `CoulInt(W₁) , CoulInt(W₁ω) ∈ L¹` come from `L1Tails.W1fun_coulomb_le`, whose engine
  `L1Tails.coulInt_integrable_of_le` (a.e. slice bound `∫⁻_y g₀(y)‖x−y‖⁻¹ ≤ 8π` of the
  scattering weight `g₀`) we re-run with `A = W₁ + W₁ω ≤ 2(1+δ)g₀`, `δ = 2C(R/ℓ)² ≤ 1`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The `L¹` facts about `W₁ω` are those of `L1Tails.w1omegaFun_facts`; the new
content is the evenness of `W₁ω` (radiality of `g₀ω` and of `convScale`) and the
integrability of the Coulomb energy of the **sum** `W₁ + W₁ω`, which is dominated by
`2(1 + 2C(R/ℓ)²)g₀` a.e. and so falls under the slice-bound engine
`L1Tails.coulInt_integrable_of_le`. -/
theorem W1omega_weight_facts {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ r₁ C : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hC : 0 ≤ C) (hr₁ : 0 < r₁)
    (hT : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ r₁ → |Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi x - 1| ≤ C * ‖x‖ ^ 2)
    (hℓ : 0 < ℓ) (hreg : R / ℓ ≤ r₁) (hcond : C * (R / ℓ) ^ 2 ≤ 1 / 2) :
    MeasureTheory.Integrable (Work.BoseFixR.W1omegaFun v h ℓ) ∧
      (∀ᵐ x : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseFixR.W1omegaFun v h ℓ x) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → Work.BoseFixR.W1omegaFun v h ℓ x = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.W1omegaFun v h ℓ (-x) = Work.BoseFixR.W1omegaFun v h ℓ x) ∧
      MeasureTheory.Integrable (Work.BoseBoxFock.coulInt (Work.BoseFixR.W1omegaFun v h ℓ)) ∧
      MeasureTheory.Integrable (Work.BoseBoxFock.coulInt
        (fun x : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x)) := by
  -- the dominating scattering weight `g₀ = v(1 − ω)` and the relative excess `δ`
  set g : E3 → ℝ := Submission.BoseGases.g0 v h with hgdef
  set δ : ℝ := 2 * C * (R / ℓ) ^ 2 with hδdef
  have hδ0 : 0 ≤ δ := by
    rw [hδdef]; exact mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _)
  have h1δ0 : 0 ≤ 1 + δ := by linarith
  -- facts about `g₀`
  have hgI : MeasureTheory.Integrable g := by
    rw [hgdef]; exact Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0 : ∀ᵐ x : E3, 0 ≤ g x := by
    rw [hgdef]; exact Submission.BoseGases.g0_nonneg_ae hR hv hvrad hv_supp h
  have hslice : ∀ᵐ x : E3,
      (∫⁻ y, ENNReal.ofReal (g y * ‖x - y‖⁻¹)) ≤ ENNReal.ofReal (8 * Real.pi) := by
    have hh := Work.BoseFixR.FarLat.g0_coulPot_lintegral_ae_le (v := v) h hv hvrad hR hv_supp
    simpa [hgdef] using hh
  -- the `L¹`/support/domination facts about `W₁ω` and about `W₁`
  obtain ⟨hW2I, hW20, hW2le0, hW2supp⟩ :=
    Work.BoseBoxFock.L1Tails.w1omegaFun_facts (v := v) (R := R) (ℓ := ℓ) (r₁ := r₁) (C := C)
      hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  obtain ⟨hW1I, hW10, _⟩ :=
    Work.BoseBoxFock.W1fun_integrable_of_regime (v := v) (h := h) (R := R) (ℓ := ℓ) (r₁ := r₁)
      (C := C) hR hv hvrad hv_supp hC hr₁ hT hℓ hreg hcond
  have hsand := Submission.BoseGases.wScaled_g0_ae_bounds (v := v) (R := R) (ℓ := ℓ)
    (r₁ := r₁) (C := C) hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  have hW1le : ∀ᵐ x : E3, Work.BoseFixR.W1fun v h ℓ x ≤ (1 + δ) * g x := by
    filter_upwards [hsand] with x hx
    rw [hδdef]
    have h2 : Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) x
        ≤ (1 + 2 * C * (R / ℓ) ^ 2) * Submission.BoseGases.g0 v h x := by nlinarith [hx.2]
    simpa [hgdef, Work.BoseFixR.W1fun] using h2
  have hW2le : ∀ᵐ x : E3, Work.BoseFixR.W1omegaFun v h ℓ x ≤ (1 + δ) * g x := by
    filter_upwards [hW2le0] with x hx
    rw [hδdef]
    simpa [hgdef] using hx
  -- `W₁ω` is even: the numerator `g₀ω` is radial and so is `convScale ℓ`
  have hsym : ∀ x : E3,
      Work.BoseFixR.W1omegaFun v h ℓ (-x) = Work.BoseFixR.W1omegaFun v h ℓ x := by
    intro x
    have hnum : Work.BoseB7AK.W1rows.W1omegaNum v h (-x)
        = Work.BoseB7AK.W1rows.W1omegaNum v h x := by
      simp only [Work.BoseB7AK.W1rows.W1omegaNum]
      rw [Submission.BoseGases.g0_even hvrad h x,
        Submission.BoseGases.radial_neg (Classical.choose_spec h).1 x]
    rw [Work.BoseB7AK.W1rows.W1omegaFun_eq]
    simp only [Submission.BoseGases.wScaled]
    rw [hnum, Submission.BoseGases.convScale_symm ℓ x]
  -- the two Coulomb integrabilities of the sibling
  obtain ⟨_, _, hcoul2, _⟩ :=
    Work.BoseBoxFock.L1Tails.W1fun_coulomb_le (v := v) (R := R) (ℓ := ℓ) (r₁ := r₁) (C := C)
      hR hv hvrad hv_supp h hC hr₁ hT hℓ hreg hcond
  -- the sum `W₁ + W₁ω ≤ 2(1 + δ)g₀`
  have hsumI : MeasureTheory.Integrable
      (fun x : E3 => Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x) :=
    hW1I.add hW2I
  have hsum0 : ∀ᵐ x : E3,
      0 ≤ Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x := by
    filter_upwards [hW10, hW20] with x h1 h2
    linarith
  have hsumle : ∀ᵐ x : E3,
      Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x
        ≤ (2 * (1 + δ)) * g x := by
    filter_upwards [hW1le, hW2le] with x h1 h2
    have h : (1 + δ) * g x + (1 + δ) * g x = (2 * (1 + δ)) * g x := by ring
    linarith [h]
  have hsumCoul := Work.BoseBoxFock.L1Tails.coulInt_integrable_of_le
    (g := g)
    (A := fun x : E3 => Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x)
    (c := 2 * (1 + δ)) (κ := 8 * Real.pi) (by linarith) (by positivity)
    hgI hg0 hsumI hsum0 hsumle hslice
  exact ⟨hW2I, hW20, hW2supp, hsym, hcoul2, hsumCoul.1⟩

end Work.BoseBoxFock
