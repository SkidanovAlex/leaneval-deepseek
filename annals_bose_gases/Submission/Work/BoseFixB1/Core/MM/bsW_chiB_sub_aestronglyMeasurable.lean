import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.Decomp.ShiftDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A.e. strong measurability of the sliding kinetic word `u ↦ bsW F (χ_{B(u)}·(g − ρ u))`

The sliding one-body kinetic word is, in Box-Centre form,

    `bsW F h = ∫_p F(‖p‖)·‖bsPsi h p‖²`,   `bsPsi h p = kinFT (h · : ℂ) p`,

with `kinFT v p = ∫_y e^{−i⟪p,y⟫} v(y) dy`.  Here we prove that

    `u ↦ bsW (fsKinCoeff c) (fun z => chiB ℓ d u z * (g z - ρ u))`

is a.e. strongly measurable on `ℝ³` for `g` continuous and `ρ` merely measurable — no
positivity of `ℓ`, `d`, no integrability, no compact support and no decay are needed.

The point is that `kinFT` is a parametric Bochner integral over *all* of `ℝ³` with no
integrability hypothesis on the integrand, so the classical “measurable parameter ⇒
measurable integral” device is unavailable; the right tool is
`MeasureTheory.StronglyMeasurable.integral_prod_right'` (equivalently its `AE`-version),
which turns strong measurability of a jointly strongly measurable integrand on a product
into strong measurability of its partial integral, with the total (zero-on-non-integrable)
Bochner integral convention.

The argument is a two-fold application of that lemma, packaged below as the general tool
`aestronglyMeasurable_bsW_of_joint`:

* the joint integrand `(u,p,y) ↦ e^{−i⟪p,y⟫}·(H (u,y) : ℂ)` is strongly measurable on
  `(ℝ³ × ℝ³) × ℝ³` as soon as `H` is jointly strongly measurable (the phase factor is
  continuous);
* integrating out the position `y` gives strong measurability of `(u,p) ↦ bsPsi (H u) p`;
* multiplying by the continuous `p ↦ F‖p‖` and by `‖·‖²` preserves it, and integrating out
  the momentum `p` gives strong measurability of `u ↦ bsW F (H u)`.

For the concrete window of the statement we use that
`(u,z) ↦ chiB ℓ d u z = chiScale ℓ z · chiScale (ℓd)(z − (ℓd)•u)` is jointly **continuous**
(so its joint measurability is free) while `(u,z) ↦ g z − ρ u` is jointly **measurable**
(`g` continuous, `ρ` measurable); on a second countable space
`Measurable.stronglyMeasurable` upgrades the joint measurability of the product to the
strong measurability the tool needs.
-/

namespace Work.BoseFixB1.Core.MM

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

set_option autoImplicit false

/-- **General tool.**  If the symbol `F` is continuous and `H : ℝ³ × ℝ³ → ℝ` is jointly
strongly measurable, then the sliding kinetic word `u ↦ bsW F (fun z => H (u,z))` is a.e.
strongly measurable for Lebesgue measure.

The proof is the two-fold application of `MeasureTheory.StronglyMeasurable.integral_prod_right'`
described in the module docstring. -/
theorem aestronglyMeasurable_bsW_of_joint {F : ℝ → ℝ} (hF : Continuous F)
    {H : ℝ³ × ℝ³ → ℝ} (hH : StronglyMeasurable H) :
    AEStronglyMeasurable
      (fun u : ℝ³ => Work.BSKinetic.Decomp.bsW F (fun z : ℝ³ => H (u, z)))
      (volume : Measure ℝ³) := by
  -- **Step 1.** The phase factor is continuous, hence strongly measurable.
  have hexp : StronglyMeasurable (fun s : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ)))) :=
    (by fun_prop : Continuous (fun s : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ s.1.2 s.2 : ℂ))))).stronglyMeasurable
  -- **Step 2.** The integrand of `kinFT`, jointly in `(u,p,y)`.
  have hstat : StronglyMeasurable (fun s : (ℝ³ × ℝ³) × ℝ³ =>
      Complex.ofReal (H (s.1.1, s.2))) :=
    (Complex.continuous_ofReal.comp_stronglyMeasurable
      (hH.comp_measurable (by fun_prop : Measurable fun s : (ℝ³ × ℝ³) × ℝ³ => (s.1.1, s.2))))
  -- **Step 3.** Integrate out the position `y`: this is `(u,p) ↦ bsPsi (H u) p`.
  have hK : StronglyMeasurable (fun q : ℝ³ × ℝ³ =>
      ∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
        Complex.ofReal (H (q.1, y))) :=
    (hexp.mul hstat).integral_prod_right' (ν := (volume : Measure ℝ³))
  -- **Step 4.** Multiply by the symbol `F‖p‖` and take the squared norm.
  have hGp : StronglyMeasurable (fun q : ℝ³ × ℝ³ =>
      F ‖q.2‖ * ‖(∫ y : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q.2 y : ℂ))) *
        Complex.ofReal (H (q.1, y)))‖ ^ 2) := by
    have hFm : StronglyMeasurable (fun q : ℝ³ × ℝ³ => F ‖q.2‖) :=
      (hF.comp (continuous_norm.comp continuous_snd)).stronglyMeasurable
    exact hFm.mul (hK.norm.pow 2)
  -- **Step 5.** Integrate out the momentum `p`.
  have hFin : StronglyMeasurable (fun u : ℝ³ =>
      ∫ p : ℝ³, F ‖p‖ * ‖(∫ y : ℝ³,
        Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * Complex.ofReal (H (u, y)))‖ ^ 2) :=
    hGp.integral_prod_right' (ν := (volume : Measure ℝ³))
  -- **Step 6.** Identify with `bsW` and weaken to a.e. strong measurability.
  refine hFin.aestronglyMeasurable.congr ?_
  filter_upwards with u
  simp only [Work.BSKinetic.Decomp.bsW, Work.BSKinetic.Decomp.bsPsi, Submission.BoseGases.kinFT]

/-- **A.e. strong measurability of the sliding cutoff kinetic word.**

For continuous `g` and merely measurable `ρ`, the function
`u ↦ bsW (fsKinCoeff c) (fun z => chiB ℓ d u z * (g z − ρ u))` is a.e. strongly measurable
on `ℝ³` (`chiB ℓ d u z = chiScale ℓ z · chiScale (ℓd)(z − (ℓd)u)`).

This is `aestronglyMeasurable_bsW_of_joint` applied to the jointly strongly measurable
integrand `H (u,z) = chiB ℓ d u z · (g z − ρ u)`: the window is jointly *continuous*, the
remaining factor is jointly *measurable*, and their product is jointly measurable, hence
(second countability) jointly strongly measurable.  No positivity of `ℓ`,`d`, no
integrability and no decay are needed. -/
theorem bsW_chiB_sub_aestronglyMeasurable {ℓ d c : ℝ}
    {g ρ : EuclideanSpace ℝ (Fin 3) → ℝ} (hg : Continuous g) (hρ : Measurable ρ) :
    MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BSKinetic.Decomp.bsW (Submission.BoseGases.fsKinCoeff c)
        (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.chiB ℓ d u z * (g z - ρ u))) MeasureTheory.volume := by
  -- Continuity of the spectral symbol `r ↦ [r−c]₊²`.
  have hFcont : Continuous (Submission.BoseGases.fsKinCoeff c) := by
    have h : Submission.BoseGases.fsKinCoeff c = fun r : ℝ => (max (r - c) 0) ^ 2 := rfl
    rw [h]
    exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
  refine aestronglyMeasurable_bsW_of_joint (F := Submission.BoseGases.fsKinCoeff c)
    (H := fun q : ℝ³ × ℝ³ =>
      Submission.BoseGases.chiB ℓ d q.1 q.2 * (g q.2 - ρ q.1)) hFcont ?_
  -- The window `(u,z) ↦ chiB ℓ d u z` is jointly continuous.
  have hchi1 : Continuous (fun q : ℝ³ × ℝ³ => Submission.BoseGases.chiScale ℓ q.2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
  have hchi2 : Continuous (fun q : ℝ³ × ℝ³ =>
      Submission.BoseGases.chiScale (ℓ * d) (q.2 - (ℓ * d) • q.1)) :=
    (Submission.BoseGases.chiScale_continuous (ℓ * d)).comp (by fun_prop)
  have hchiBm : Measurable (fun q : ℝ³ × ℝ³ => Submission.BoseGases.chiB ℓ d q.1 q.2) := by
    show Measurable (fun q : ℝ³ × ℝ³ => Submission.BoseGases.chiScale ℓ q.2 *
      Submission.BoseGases.chiScale (ℓ * d) (q.2 - (ℓ * d) • q.1))
    exact (hchi1.mul hchi2).measurable
  -- The factor `(u,z) ↦ g z − ρ u` is jointly measurable.
  have hgr : Measurable (fun q : ℝ³ × ℝ³ => g q.2 - ρ q.1) :=
    (hg.measurable.comp measurable_snd).sub (hρ.comp measurable_fst)
  exact (hchiBm.mul hgr).stronglyMeasurable

end Work.BoseFixB1.Core.MM
