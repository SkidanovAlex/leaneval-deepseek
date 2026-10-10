/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.ChartMaps
import Submission.Work.MotK.AwayAlgEquivOfComp
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.ChartIso` — the chart isomorphism of the T-twisted link

The two composites of `PhiT` and `PsiT` (`Work.MotK.TGen.ChartMaps`) are computed on the three
generators with the two link identities `KleinTwLinkComp1`/`KleinTwLinkComp2`, and the
assembly lemma `Work.MotK.AwayAlgEquivOfComp` then produces

  `chartIsoT : Nonempty (R[1/Fdiv] ≃ₐ[K] R[1/Gdiv])`.

The computation is the one of the paper's `ψ^* = χ^{-1,*}`:  on the generators

* `Ψ (Φ x_j) = Ψ (ǧ_{j+1}/ǧ₄) = f^*_{j+1}(ǧ)/f^*_4(ǧ) = x_j`  using
  `KleinTwLinkComp2` (`ǧ (f̂) = -GambT · chart`), and
* `Φ (Ψ y_j) = Φ (f̂_{j+1}/f̂₄) = ǧ_{j+1}(f̂)/ǧ₄(f̂) = y_j`  using
  `KleinTwLinkComp1` (`f̂ (ǧ) = b(p,Rǧ)² s'(ǧ) · ǧ`),

the common factors cancelling because they are units of the corresponding localisation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-- **The composite `Ψ ∘ Φ` is the identity on the generators.** -/
theorem PsiTPhiTX (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (j : Fin 3) :
    PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh)
        (PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K)))
      = algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
  rw [PhiT_algebraMap, Phi0_X, psiG_apply, map_mul, PsiT_algebraMap]
  -- `Ψ(1/ǧ₄) · Ψ₀(ǧ₄) = 1`
  have hA : PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (invG4 a b h)
      * Psi0 a b h (bwVec a b h 4) = 1 := by
    have h2 : PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (invG4 a b h)
        * (Psi0 a b h (FambT a b h) * Psi0 a b h (bwVec a b h 4))
        = Psi0 a b h (FambT a b h) := by
      have h3 : PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (invG4 a b h)
          * PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (algebraMap _ _ (Gdiv a b h))
          = PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (algebraMap _ _ (FambT a b h)) := by
        rw [← map_mul, invG4_spec]
      rw [PsiT_algebraMap, PsiT_algebraMap] at h3
      have h4 : Psi0 a b h (Gdiv a b h)
          = Psi0 a b h (FambT a b h) * Psi0 a b h (bwVec a b h 4) := by
        rw [show Gdiv a b h = FambT a b h * bwVec a b h 4 from rfl, map_mul]
      rw [h4] at h3
      exact h3
    refine (isUnit_Psi0_fambT a b h ha hh).mul_right_cancel ?_
    rw [one_mul, mul_assoc,
      mul_comm (Psi0 a b h (bwVec a b h 4)) (Psi0 a b h (FambT a b h))]
    exact h2
  -- `x_j · Ψ₀(ǧ₄) = Ψ₀(ǧ_{j+1})`
  have hC : algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) * Psi0 a b h (bwVec a b h 4)
      = Psi0 a b h (bwVec a b h (ch3 j)) := by
    rw [Psi0BwVec a b h ha hb hh 4, Psi0BwVec a b h ha hb hh (ch3 j), chart3_four,
      chart3_ch3]
    simp only [map_mul, map_neg, mul_one]
    first | refl_ring1 | ring
  have hfinal : PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (invG4 a b h)
      * Psi0 a b h (bwVec a b h (ch3 j))
      = (PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (invG4 a b h)
          * Psi0 a b h (bwVec a b h 4))
          * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Fdiv a b h))
              (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
    rw [← hC]
    first | refl_ring1 | ring
  rw [hfinal, hA, one_mul]

/-- **The composite `Φ ∘ Ψ` is the identity on the generators.** -/
theorem PhiTPsiTX (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) (j : Fin 3) :
    PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh)
        (PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh) (algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K)))
      = algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
  rw [PsiT_algebraMap, Psi0_X, phiF_apply, map_mul, PhiT_algebraMap]
  have hA : PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (invF4 a b h)
      * Phi0 a b h (fwVec a b h 4) = 1 := by
    have h2 : PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (invF4 a b h)
        * (Phi0 a b h (GambT a b h) * Phi0 a b h (fwVec a b h 4))
        = Phi0 a b h (GambT a b h) := by
      have h3 : PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (invF4 a b h)
          * PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (algebraMap _ _ (Fdiv a b h))
          = PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (algebraMap _ _ (GambT a b h)) := by
        rw [← map_mul, invF4_spec]
      rw [PhiT_algebraMap, PhiT_algebraMap] at h3
      have h4 : Phi0 a b h (Fdiv a b h)
          = Phi0 a b h (GambT a b h) * Phi0 a b h (fwVec a b h 4) := by
        rw [show Fdiv a b h = GambT a b h * fwVec a b h 4 from rfl, map_mul]
      rw [h4] at h3
      exact h3
    refine (isUnit_Phi0_gambT a b h ha hb hh).mul_right_cancel ?_
    rw [one_mul, mul_assoc,
      mul_comm (Phi0 a b h (fwVec a b h 4)) (Phi0 a b h (GambT a b h))]
    exact h2
  have hC : algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) * Phi0 a b h (fwVec a b h 4)
      = Phi0 a b h (fwVec a b h (ch3 j)) := by
    rw [Phi0FwVec a b h ha hb hh 4, Phi0FwVec a b h ha hb hh (ch3 j), chart3_four,
      chart3_ch3]
    simp only [map_mul, map_neg, mul_one]
    first | refl_ring1 | ring
  have hfinal : PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (invF4 a b h)
      * Phi0 a b h (fwVec a b h (ch3 j))
      = (PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh) (invF4 a b h)
          * Phi0 a b h (fwVec a b h 4))
          * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (Gdiv a b h))
              (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
    rw [← hC]
    first | refl_ring1 | ring
  rw [hfinal, hA, one_mul]

/-- **The chart isomorphism of the T-twisted Crauder--Katz link.** -/
theorem chartIsoT (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Nonempty (Localization.Away (Fdiv a b h) ≃ₐ[K] Localization.Away (Gdiv a b h)) :=
  Work.MotK.AwayAlgEquivOfComp (Fdiv a b h) (Gdiv a b h)
    (PhiT a b h (isUnit_Phi0_Fdiv a b h ha hb hh))
    (PsiT a b h (isUnit_Psi0_Gdiv a b h ha hb hh))
    (fun j => PsiTPhiTX a b h ha hb hh j)
    (fun j => PhiTPsiTX a b h ha hb hh j)

end Work.MotK.TGen
