import ChallengeDeps
import Submission.Work.BoseFixB1.Core.symA_fsKinCoeff_mix_scaled
import Submission.Work.BoseFixB1.profHat_tail_pow
import Submission.Work.BoseFixB1S.symACriteriaB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

noncomputable section

open MeasureTheory
open scoped Real Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## The analytic core: the scaled comparison at FS's parameters

`Work.BoseFixB1.symA_fsKinCoeff_mix_scaled` is the two-cut comparison at scale `a = ℓ d` with
`C = 1/s`; the four scalar side conditions are supplied by `Work.BoseFixB1S.symACriteriaB1`
(`s > 0`, `d ≤ 1/2`, `eT ≤ 1/2`, `M₁ ≤ 1/s`, `8M₂ ≤ (1−d)²/s²`), and the tail hypothesis is
reflexive at `β := symA 1 (fsKinCoeff (1/(2s))) 0`.  The only work here is the elementary
bookkeeping identifying the three cut-offs:

* `C/a = (1/s)/(ℓd) = (dsℓ)⁻¹ = sbCut μ a` (the sliding cut-off),
* `dC/(2a) = (1/s)/(2ℓ) = (2sℓ)⁻¹` (the `(1−eT)`-branch),
* `C/(2a) = (1/s)/(2ℓd) = (2dsℓ)⁻¹` (the `eT`-branch),
* `C/2 = 1/(2s)`,
* `β/a² = (ℓd)⁻²β`. -/
lemma symA_mix_at_params {μ a : ℝ}
    (hcrit : 0 < (Work.BoseBox.paramsAt μ a).s ∧ (Work.BoseBox.paramsAt μ a).d ≤ 1 / 2 ∧
      (Work.BoseBox.paramsAt μ a).eT ≤ 1 / 2 ∧
      Work.BoseFixB1.KH.symAMom1 ≤ ((Work.BoseBox.paramsAt μ a).s)⁻¹ ∧
      8 * Work.BoseFixB1.KH.symAMom2 ≤ (1 - (Work.BoseBox.paramsAt μ a).d) ^ 2 *
        (((Work.BoseBox.paramsAt μ a).s)⁻¹) ^ 2)
    (hell : 0 < Work.BoseBox.sideAt μ a) (hdpos : 0 < (Work.BoseBox.paramsAt μ a).d)
    (heT0 : 0 ≤ (Work.BoseBox.paramsAt μ a).eT) (q : E3) :
    Work.OneBodyKin.symA (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)
        (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ a)) q
      ≤ (1 - (Work.BoseBox.paramsAt μ a).eT) * Submission.BoseGases.fsKinCoeff
          ((2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹) ‖q‖
        + (Work.BoseBox.paramsAt μ a).eT * Submission.BoseGases.fsKinCoeff
            ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
              * Work.BoseBox.sideAt μ a))⁻¹) ‖q‖
        + ((Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d) ^ 2)⁻¹
          * Work.OneBodyKin.symA 1
              (Submission.BoseGases.fsKinCoeff ((2 * (Work.BoseBox.paramsAt μ a).s)⁻¹)) 0 := by
  obtain ⟨hspos, hdle, heTle, hM1, hM2⟩ := hcrit
  have hdne : (Work.BoseBox.paramsAt μ a).d ≠ 0 := ne_of_gt hdpos
  have hellne : Work.BoseBox.sideAt μ a ≠ 0 := ne_of_gt hell
  have hC : 0 < ((Work.BoseBox.paramsAt μ a).s)⁻¹ := inv_pos.mpr hspos
  have ha' : 0 < Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d := mul_pos hell hdpos
  have hd0 : 0 ≤ (Work.BoseBox.paramsAt μ a).d := le_of_lt hdpos
  -- the two moment inputs, in the shape required by the scaled comparison
  have hm1 : ((2 * Real.pi) ^ 3)⁻¹ * ∫ t : E3, (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖
      ≤ ((Work.BoseBox.paramsAt μ a).s)⁻¹ := by
    simpa [Work.BoseFixB1.KH.symAMom1] using hM1
  have hm2 : 8 * (((2 * Real.pi) ^ 3)⁻¹ * ∫ t : E3, (Work.OneBodyKin.profHat t) ^ 2 * ‖t‖ ^ 2)
      ≤ (1 - (Work.BoseBox.paramsAt μ a).d) ^ 2 * (((Work.BoseBox.paramsAt μ a).s)⁻¹) ^ 2 := by
    simpa [Work.BoseFixB1.KH.symAMom2] using hM2
  have h := Work.BoseFixB1.symA_fsKinCoeff_mix_scaled
     (a := Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)
     (C := ((Work.BoseBox.paramsAt μ a).s)⁻¹) (d := (Work.BoseBox.paramsAt μ a).d)
     (ε := (Work.BoseBox.paramsAt μ a).eT)
     (β := Work.OneBodyKin.symA 1
       (Submission.BoseGases.fsKinCoeff (((Work.BoseBox.paramsAt μ a).s)⁻¹ / 2)) 0)
     ha' hC hd0 hdle heT0 heTle hm1 hm2 (le_refl _) q
  -- the five elementary identifications of the cut-offs
  have hsb : ((Work.BoseBox.paramsAt μ a).s)⁻¹ / (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d)
      = Work.BoseFixB1.sbCut μ a := by
    rw [Work.BoseFixB1.sbCut]; field_simp
  have hc1 : (Work.BoseBox.paramsAt μ a).d * ((Work.BoseBox.paramsAt μ a).s)⁻¹
        / (2 * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d))
      = (2 * ((Work.BoseBox.paramsAt μ a).s * Work.BoseBox.sideAt μ a))⁻¹ := by
    field_simp
  have hc2 : ((Work.BoseBox.paramsAt μ a).s)⁻¹
        / (2 * (Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d))
      = (2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s
          * Work.BoseBox.sideAt μ a))⁻¹ := by
    field_simp
  have ht : ((Work.BoseBox.paramsAt μ a).s)⁻¹ / 2 = (2 * (Work.BoseBox.paramsAt μ a).s)⁻¹ := by
    field_simp
  rw [hsb, hc1, hc2, ht, div_eq_inv_mul] at h
  exact h

/-- **The unprojected two-cut symbol comparison at FS's parameters** — step (3) of the ledger
`Submission/Work/BoseFixB1S/FINDING_kineticCruxFinB1_routeB.md`, and the only analytic input of the
crux's route B.

In the window's own units (`ρ = (dℓ)q`, `C = c_sb·dℓ = 1/s`) `symA (dℓ) (fsKinCoeff c_sb)` is the
smearing `(2π)⁻³∫_t [‖ρ+t‖ − C]₊² profHat(t)² dt` of the sliding cutoff; the claim is that it is
dominated pointwise by the *anchored* two-cut mixture of the crux's right-hand side
(`(1−eT)`-branch at `c₁ = (2sℓ)⁻¹`, `eT`-branch at `c₂ = (2dsℓ)⁻¹`), up to the free constant
`tail := symA 1 (fsKinCoeff (1/(2s))) 0` (the profile tail beyond `1/(2s)`, payable by
`Work.BoseFixB1S.cruxTailB1`) times `(dℓ)⁻²`.

It is the FS-parameter instance of the PROVED `Work.BoseFixB1.symA_fsKinCoeff_mix` /
`Core.symA_fsKinCoeff_mix_scaled`, whose three side conditions — `M₁ ≤ C`, `8M₂ ≤ (1−d)²C²`
(`M₁, M₂` the profile moments of `BoseFixB1/Smear/Defs.lean`) and `symA 1 (fsKinCoeff (C/2)) 0 ≤ β`
— are monomial conditions in `s` at `C = 1/s`, `d = s⁶`, `eT = s^{23/4}`, so `ε₀` is an explicit
(constant-dependent) threshold (`Work.BoseFixB1.exists_ε₀_criteria`,
`Work.BoseFixB1.paramsAt_facts`, `fsXp_le_fsXp`; `0 < C`, `0 ≤ d ≤ 1/2`, `0 ≤ eT ≤ 1/2` for small
`s`).  The same statement exists as the (unproved) sibling node
`Work.BoseFixB1.KH.symA_fsParams`; it is repeated here because it is the sole analytic input of the
crux's route B and must be sorry-free in the crux's own import cone. -/
theorem symAFsParamsB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ q : EuclideanSpace ℝ (Fin 3),
      Work.OneBodyKin.symA (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))) q
        ≤ (1 - (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
            * Submission.BoseGases.fsKinCoeff
                ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            * Submission.BoseGases.fsKinCoeff
                ((2 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                  * Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))⁻¹) ‖q‖
          + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
            * Work.OneBodyKin.symA 1
                (Submission.BoseGases.fsKinCoeff
                  ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0 := by
  refine ⟨Work.BoseFixB1.KH.symAEps0, Work.BoseFixB1.KH.symAEps0_pos, ?_⟩
  intro μ hAdm q
  exact symA_mix_at_params (symACriteriaB1 hAdm.1 (Work.BoseFixB1.adm_a_pos hAdm) hAdm.2.1)
    (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm)
    (Work.BoseFixB1.adm_eT_bounds hAdm).1 q

end

end Work.BoseFixB1S
