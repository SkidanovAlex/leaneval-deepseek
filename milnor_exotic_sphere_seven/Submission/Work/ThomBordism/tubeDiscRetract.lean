import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing
import Submission.Work.ThomBordism.tubeTrans_modelSpan
import Submission.Work.ThomBordism.radialRescale_homologyMap_id

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The radial capping preserves the punctured pair of the normal bundle

`Work.ThomBordism.tubeRelChains_iso_puncturedNormalPair` compares the punctured tube pair
`(C.U ∖ {pt}, tubeInvPunct)` with the punctured normal pair `(ν ∖ {x₀}, ν ∖ 0)` through the
fibrewise radial retraction `Work.ThomBordism.cap E ε` of the normal total space onto the closed
`ε`-disc bundle (the capping of `Submission/Work/ThomBordism/ambientLocalDefs2.lean`), which is the
identity on the tube inverse `C.inv` of the disc bundle.

This file supplies the two facts about the capping that the comparison needs and that are not
already in `ambientLocalDefs2`:

* `cap_ne_basePt`: the capping fixes exactly the base point `x₀ = basePt E x` of the punctured pair;
* `radialCoeff_capCoeff_pos`: the interpolation coefficient of the radial homotopy
  `radialRescaleHomotopyFun E (capCoeff ε)` is positive at *every* point (no hypothesis on the norm),
  whence `radialRescaleHomotopyFun_ne_basePt`: the radial homotopy preserves the complement of the
  base point at every time.
-/

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The projection of a capped point is that of the original point. -/
theorem cap_proj (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ)
    (p : Work.Tubular.NormalTotal E) : (cap E ε p).proj = p.proj :=
  radialRescale_proj E (capCoeff ε) p

/-- The normal vector of a capped point is the clamped vector of the original point. -/
theorem cap_vec (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (ε : ℝ)
    (p : Work.Tubular.NormalTotal E) :
    (cap E ε p).vec = capCoeff ε (Work.Tubular.normalNorm E p) • p.vec :=
  congrArg Prod.snd (radialRescale_coe E (capCoeff ε) p)

/-- **The capping preserves the complement of the base point `x₀`**, because it preserves the
projection and clamps the normal vector by a strictly positive coefficient. -/
theorem cap_ne_basePt {ε : ℝ} (hε : 0 < ε)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    {p : Work.Tubular.NormalTotal E} (hp : p ≠ Work.Tubular.PuncturedDiscPair.basePt E x) :
    cap E ε p ≠ Work.Tubular.PuncturedDiscPair.basePt E x := by
  intro h
  refine hp (Work.Tubular.NormalTotal.ext (Prod.ext ?_ ?_))
  · have h1 := cap_proj E ε p
    rw [h] at h1
    exact h1.symm
  · have h1 := cap_vec E ε p
    rw [h] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left
      (ne_of_gt (capCoeff_pos hε _ (Work.Tubular.normalNorm_nonneg E p)))

/-- The capping fixes exactly the base point `x₀`: its only fixed point of that form is `x₀`. -/
theorem cap_eq_basePt_iff {ε : ℝ} (hε : 0 < ε)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (p : Work.Tubular.NormalTotal E) :
    cap E ε p = Work.Tubular.PuncturedDiscPair.basePt E x ↔
      p = Work.Tubular.PuncturedDiscPair.basePt E x := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hp
    exact cap_ne_basePt hε E x hp h
  · rw [h]
    exact cap_eq_self_of_le E hε.le (by
      rw [Work.Tubular.PuncturedDiscPair.normalNorm_basePt]; exact hε.le)

/-- The interpolation coefficient of the radial homotopy is positive at every point for the
clamping coefficient, without any hypothesis on the norm of the point. -/
theorem radialCoeff_capCoeff_pos {ε : ℝ} (hε : 0 < ε)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (t : unitInterval)
    (p : Work.Tubular.NormalTotal E) : 0 < radialCoeff E (capCoeff ε) (t, p) := by
  have hφ : 0 < capCoeff ε (Work.Tubular.normalNorm E p) :=
    capCoeff_pos hε _ (Work.Tubular.normalNorm_nonneg E p)
  have ht1 : (t : ℝ) ≤ 1 := unitInterval.le_one t
  rw [radialCoeff]
  rcases lt_or_eq_of_le ht1 with ht | ht
  · have h1 : 0 < 1 - (t : ℝ) := by linarith
    nlinarith [mul_pos h1 hφ, unitInterval.nonneg t]
  · rw [ht]; norm_num

/-- **The radial homotopy preserves the complement of the base point** at every time. -/
theorem radialRescaleHomotopyFun_ne_basePt {ε : ℝ} (hε : 0 < ε)
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt)
    (t : unitInterval) {p : Work.Tubular.NormalTotal E}
    (hp : p ≠ Work.Tubular.PuncturedDiscPair.basePt E x) :
    radialRescaleHomotopyFun E (capCoeff ε) (t, p) ≠
      Work.Tubular.PuncturedDiscPair.basePt E x := by
  intro h
  refine hp (Work.Tubular.NormalTotal.ext (Prod.ext ?_ ?_))
  · have h1 : (radialRescaleHomotopyFun E (capCoeff ε) (t, p)).proj = p.proj := by
      rw [radialRescaleHomotopyFun_apply]; rfl
    rw [h] at h1
    exact h1.symm
  · have h1 : (radialRescaleHomotopyFun E (capCoeff ε) (t, p)).vec
        = radialCoeff E (capCoeff ε) (t, p) • p.vec := by
      rw [radialRescaleHomotopyFun_apply]; rfl
    rw [h] at h1
    exact (smul_eq_zero.mp h1.symm).resolve_left
      (ne_of_gt (radialCoeff_capCoeff_pos hε E t p))

end

end Work.ThomBordism
