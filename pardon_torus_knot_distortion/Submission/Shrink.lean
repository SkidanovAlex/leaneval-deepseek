import Mathlib
import ChallengeDeps
import Submission.Box
import Submission.Smooth
import Submission.Iterate
import Submission.Assemble
import Submission.RatioBound
import Submission.Extract
import Submission.Work.CoreTopology.Winding
import Submission.Work.CoreTopology.Transport
import Submission.Work.CoreTopology.IntersectionNumberDiffeomorphic
import Submission.Work.Sweep.Defs
import Submission.Work.Geometry.periodic_bounded
import Submission.Work.CoreSetup.essential_diam_lower_bound
import Submission.Work.InnermostDisk.isEssential_iff_hasWinding

/-!
# The shrinking step of Pardon's argument

This file assembles Pardon's proof of the torus-knot distortion bound from the single
geometric input `Submission.BoxShrinkStatement`: a box whose intersection with the embedded
torus contains an essential curve can be replaced, under the distortion hypothesis, by a
strictly smaller box (`shrinkFactor * r` with `shrinkFactor < 1`) with the same property.

Given that input, the argument is:

* the surface `F = ψ(F_standard)` of the challenge lies in a large box, and the whole torus
  contains an essential curve (a meridian), so some scale `R₀` admits a box meeting `F` in an
  essential curve;
* the shrink step propagates this property downward: `ρ ↦ shrinkFactor * ρ`;
* the extrinsic systole (`Work.CoreSetup.essential_diam_lower_bound`) bounds such scales below
  by `ρ_min > 0`;
* `Submission.shrink_contradiction` then gives the contradiction.

Consequently `Submission.CoreStatement` holds, and with it the challenge
(`Submission.theorem_of_core`).
-/

namespace Submission

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

noncomputable section

/-- The surface of the parametrised torus `P` meets the box `PBox r c σ` in an essential closed
curve (a closed curve whose winding vector is nonzero). -/
def HasEssBox (P : Work.CoreTopology.ParamTorus) (r : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
    ∀ t : ℝ, γ t ∈ PBox r c σ

theorem HasEssBox.mono {r r' : ℝ} (h : r ≤ r') {P : Work.CoreTopology.ParamTorus} {c : R3}
    {σ : Equiv.Perm (Fin 3)} (hP : HasEssBox P r c σ) : HasEssBox P r' c σ := by
  obtain ⟨γ, hγ, hmem⟩ := hP
  exact ⟨γ, hγ, fun t => PBox_mono h (hmem t)⟩

/-- A positive scale `ρ` such that some box of size `ρ` meets the surface in an essential
curve. -/
def HasEssScale (P : Work.CoreTopology.ParamTorus) (ρ : ℝ) : Prop :=
  ∃ c : R3, ∃ σ : Equiv.Perm (Fin 3), HasEssBox P ρ c σ

theorem HasEssScale.mono {ρ ρ' : ℝ} (h : ρ ≤ ρ') {P : Work.CoreTopology.ParamTorus}
    (hP : HasEssScale P ρ) : HasEssScale P ρ' := by
  obtain ⟨c, σ, hb⟩ := hP
  exact ⟨c, σ, hb.mono h⟩

/-- **The extrinsic systole.**  A box whose intersection with the surface `ψ(F_standard)`
contains an essential curve has size bounded below by a positive constant. -/
theorem systole_of_psiHomeo (Φ : AmbientIsotopy) :
    ∃ ρmin : ℝ, 0 < ρmin ∧ ∀ ρ : ℝ, 0 < ρ →
      HasEssScale (Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ)) ρ → ρmin ≤ ρ := by
  obtain ⟨ρmin, hρpos, hρ⟩ := Work.CoreSetup.essential_diam_lower_bound Φ
  refine ⟨ρmin / 5, by linarith, ?_⟩
  intro ρ hρpos' hρ
  obtain ⟨c, σ, γ, hess, hmem⟩ := hρ
  have hfun : (Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ)).psi =
      (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) := by
    funext x y
    rw [Work.CoreTopology.ParamTorus.mapHomeomorph_psi, psiHomeo_apply]
  have hess' : Work.TorusCover.IsEssential
      (Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ)).psi γ.γ :=
    (Work.InnermostDisk.isEssential_iff_hasWinding _ γ).mp hess
  obtain ⟨v, hv, hw⟩ := hess'
  have hw' : Work.TorusCover.HasWinding
      (fun x y => Φ.Hinv 1 (Work.Core.torusMap x y)) γ.γ v := by
    rw [← hfun]; exact hw
  have h2 : ρmin ≤ Metric.diam (Set.range γ.γ) := hρ γ.γ v hv hw'
  have h3 : Metric.diam (Set.range γ.γ) ≤ 5 * ρ :=
    diam_range_le_of_subset_PBox (γ := γ.γ) (le_of_lt hρpos') (fun t => hmem t)
  linarith

/-- **The starting box.**  A box large enough to contain the whole surface
`ψ(F_standard)` meets it in an essential curve (the image of a meridian circle). -/
theorem exists_start_of_psiHomeo (Φ : AmbientIsotopy) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ HasEssScale (Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ)) R₀ := by
  set P := Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ) with hP
  have hbdd : Bornology.IsBounded (Set.range fun p : ℝ × ℝ => P.psi p.1 p.2) :=
    Work.Geometry.periodic_bounded P.psi P.cont P.per_left P.per_right
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : R3)).mp hbdd
  set γ := Work.CoreTopology.ClosedCurve.mapHomeomorph (psiHomeo Φ)
    (Work.CoreTopology.meridianCurve Work.CoreTopology.standard 0) with hγ
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), 0, Equiv.refl (Fin 3), γ, ?_, ?_⟩
  · exact Work.CoreTopology.ClosedCurve.isEssential_mapHomeomorph _ _
      (Work.CoreTopology.meridianCurve_essential _ 0)
  · intro t
    rw [mem_PBox]
    intro i
    have hmem : γ t ∈ P.carrier := γ.mem t
    have hb : ‖γ t‖ < max R 1 := by
      have h := hR (by simpa [Work.CoreTopology.ParamTorus.carrier] using hmem)
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
      exact lt_of_lt_of_le h (le_max_left _ _)
    have hc : |γ t i - (0 : R3) i| ≤ ‖γ t‖ := by
      have h1 : |γ t i - (0 : R3) i| = |γ t i| := by simp
      rw [h1, ← Real.norm_eq_abs]
      exact PiLp.norm_apply_le (p := 2) (β := fun _ : Fin 3 => ℝ) (γ t) i
    have h4 : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    exact lt_of_lt_of_le (lt_of_le_of_lt hc hb)
      (le_mul_of_one_le_left (le_of_lt h4) (one_le_boxSide i))

/-- **The single geometric input of Pardon's proof.**  For coprime `p, q > 0`, a
**diffeomorphism** `ψ` of `ℝ³` (this is the situation of the challenge, where `ψ = Φ.Hinv 1`
for an ambient isotopy `Φ`, so that the surface `ψ(F_standard)` is a smoothly embedded torus)
and a knot `K` whose image is the image of the standard `(p,q)`-curve under `ψ`, satisfying the
distortion bound `d` with `countConst * d < min p q`, every box of positive size meeting
`ψ(F_standard)` in an essential curve can be replaced by a box of size
`shrinkFactor * r < r` with the same property.

The restriction to a *diffeomorphism* (rather than an arbitrary homeomorphism of `ℝ³`) is what
the challenge provides and is what makes the surface `ψ(F_standard)` a smooth surface, so that
the transversality, implicit-function and Morse-theoretic tools apply to it. -/
def BoxShrinkStatement (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    countConst * d < (Nat.min p q : ℝ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      HasEssBox (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph) r c σ →
      ∃ c' σ', HasEssBox (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
        (shrinkFactor * r) c' σ'

/-- **Reduction of the core statement to the box shrink step.** -/
theorem CoreStatement_of_boxShrink
    (hbox : ∀ (p q : ℕ), BoxShrinkStatement p q) :
    CoreStatement := by
  intro p q hp hq hc K hclass hratio
  obtain ⟨Φ, σrep, hσ⟩ := hclass
  have hKcurve : ∀ t : ℝ, K.curve t = psiHomeo Φ (Work.CoreTopology.standardCurve p q (σrep.f t)) := by
    intro t
    rw [curve_eq_inv_comp Φ σrep K hσ t]
    have h1 : standardTorusCurve p q (σrep.f t) = Work.CoreTopology.standardCurve p q (σrep.f t) :=
      (Work.CoreTopology.standardCurve_apply p q (σrep.f t)).symm
    rw [h1]
    rfl
  have himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph (psiHomeo Φ) (Work.CoreTopology.standardCurve p q)).γ := by
    have h1 : Set.range K.curve =
        Set.range (fun t => psiHomeo Φ (Work.CoreTopology.standardCurve p q (σrep.f t))) := by
      rw [funext hKcurve]
    have h2 : (Work.CoreTopology.ClosedCurve.mapHomeomorph (psiHomeo Φ) (Work.CoreTopology.standardCurve p q)).γ
        = fun s => psiHomeo Φ (Work.CoreTopology.standardCurve p q s) := rfl
    rw [h1, h2]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨σrep.f t, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨σrep.finv s, by simp [σrep.right_inv]⟩
  set d : ℝ := (1 / 160) * (Nat.min p q : ℝ) with hd_def
  have hd_nonneg : 0 ≤ d := by rw [hd_def]; positivity
  have hstrict := bound_of_ratio_lt K (d := d) hratio
  have hbound : Work.Sweep.IsDistortionBound K d := by
    intro s hs t ht
    by_cases hst : s = t
    · subst hst
      have h0 : intrinsicDistance K s s = 0 := by
        unfold intrinsicDistance parameterArcLength
        rw [intervalIntegral.integral_same, abs_zero, sub_zero]
        exact min_eq_left (by unfold totalArcLength parameterArcLength; positivity)
      rw [h0]
      exact mul_nonneg hd_nonneg dist_nonneg
    · exact le_of_lt (hstrict s hs t ht hst)
  have hm_pos : 0 < (Nat.min p q : ℝ) := by
    have h : 0 < Nat.min p q := lt_min hp hq
    exact_mod_cast h
  have hsmall : countConst * d < (Nat.min p q : ℝ) := by
    rw [hd_def, countConst]
    nlinarith [hm_pos]
  have hshrink : ∀ ρ : ℝ, 0 < ρ →
      HasEssScale (Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ)) ρ →
      HasEssScale (Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ))
        (shrinkFactor * ρ) := by
    intro ρ hρ hbox₀
    obtain ⟨c, σ, hb⟩ := hbox₀
    exact hbox p q hp hq hc (psiDiffeo Φ) K d hd_nonneg hbound himg hsmall ρ hρ c σ hb
  obtain ⟨ρmin, hρmin_pos, hlow⟩ := systole_of_psiHomeo Φ
  obtain ⟨R₀, hR₀_pos, hstart⟩ := exists_start_of_psiHomeo Φ
  refine shrink_contradiction
    (P := fun ρ => HasEssScale (Work.CoreTopology.ParamTorus.mapHomeomorph (psiHomeo Φ)) ρ)
    R₀ shrinkFactor ρmin hR₀_pos shrinkFactor_pos shrinkFactor_lt_one hρmin_pos hstart ?_ ?_
  · exact hshrink
  · intro ρ hρ hP
    exact hlow ρ hρ hP

end

end Submission
