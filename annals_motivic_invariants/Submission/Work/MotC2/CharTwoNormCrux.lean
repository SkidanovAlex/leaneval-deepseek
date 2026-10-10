import Mathlib
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.CharTwoCrux
import Submission.Work.MotC2.EllipticCharTwoNonsingular
import Submission.Work.MotC2.RatFuncIntegral
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

set_option linter.style.haveILetI false

theorem CharTwoNormCrux (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (h2 : (2 : L) = 0) (p q : Work.MotC2.Func E)
    (hp : p ∈ Set.range (Work.MotC2.xPsi E)) (hq : q ∈ Set.range (Work.MotC2.xPsi E))
    (hqe : q * Work.MotC2.eK E ∈ Work.MotC2.Ax E)
    (hN : p ^ 2 + p * (q * Work.MotC2.eK E) + q ^ 2 * Work.MotC2.cK E ∈ Work.MotC2.Ax E) :
    p ∈ Work.MotC2.Ax E ∧ q ∈ Work.MotC2.Ax E := by
  -- Write `p = xPsi w`, `q = xPsi v`: both lie in `L(x) ⊆ L(E)`.
  obtain ⟨w, rfl⟩ := hp
  obtain ⟨v, rfl⟩ := hq
  -- The two polynomials `e = a₁X + a₃` and `c = X³ + a₂X² + a₄X + a₆`.
  set ep : Polynomial L := Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃ with hep
  set cp : Polynomial L := Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2
      + Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆ with hcp
  have hxPsi_ep : xPsi E (algebraMap (Polynomial L) (RatFunc L) ep) = eK E := by
    rw [xPsi_apply_algebraMap]; simp [xPhi, hep, eK]
  have hxPsi_cp : xPsi E (algebraMap (Polynomial L) (RatFunc L) cp) = cK E := by
    rw [xPsi_apply_algebraMap]; simp [xPhi, hcp, cK]
  -- Translate the two hypotheses to `RatFunc L`.
  have hqe' : ∃ B : Polynomial L, v * algebraMap (Polynomial L) (RatFunc L) ep
      = algebraMap (Polynomial L) (RatFunc L) B := by
    have hm : xPsi E (v * algebraMap (Polynomial L) (RatFunc L) ep) ∈ (xPhi E).range := by
      rw [xPhi_range E, map_mul, hxPsi_ep]
      exact hqe
    obtain ⟨B, hB⟩ := hm
    exact ⟨B, xPsi_injective E (by rw [xPsi_apply_algebraMap]; exact hB.symm)⟩
  have hN' : ∃ N : Polynomial L, w ^ 2 + w * (v * algebraMap (Polynomial L) (RatFunc L) ep)
      + v ^ 2 * algebraMap (Polynomial L) (RatFunc L) cp
      = algebraMap (Polynomial L) (RatFunc L) N := by
    have h1 : xPsi E (w ^ 2 + w * (v * algebraMap (Polynomial L) (RatFunc L) ep)
        + v ^ 2 * algebraMap (Polynomial L) (RatFunc L) cp)
        = xPsi E w ^ 2 + xPsi E w * (xPsi E v * eK E) + xPsi E v ^ 2 * cK E := by
      simp only [map_add, map_mul, map_pow, hxPsi_ep, hxPsi_cp]
    have hm : xPsi E (w ^ 2 + w * (v * algebraMap (Polynomial L) (RatFunc L) ep)
        + v ^ 2 * algebraMap (Polynomial L) (RatFunc L) cp) ∈ (xPhi E).range := by
      rw [xPhi_range E, h1]
      exact hN
    obtain ⟨N, hN⟩ := hm
    exact ⟨N, xPsi_injective E (by rw [xPsi_apply_algebraMap]; exact hN.symm)⟩
  -- The main step: `w` and `v` are base changes of polynomials.
  have key : (∃ P : Polynomial L, algebraMap (Polynomial L) (RatFunc L) P = w) ∧
      (∃ Q : Polynomial L, algebraMap (Polynomial L) (RatFunc L) Q = v) := by
    by_cases ha₁ : E.a₁ = 0
    · -- Degenerate case `a₁ = 0`: `eK` is the nonzero scalar `a₃`, so `q ∈ L[x]` directly;
      -- then `p` is a root of a monic quadratic with coefficients in `L[x]`.
      haveI hch : CharP L 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      have hΔ : E.Δ = E.a₃ ^ 4 := by
        rw [WeierstrassCurve.Δ_of_char_two, ha₁]; simp
      have ha₃ : E.a₃ ≠ 0 := by
        intro h
        exact (hΔ ▸ E.isUnit_Δ).ne_zero (by simp [h])
      have hscalar : algebraMap (Polynomial L) (RatFunc L) ep = algebraMap L (RatFunc L) E.a₃ := by
        have hepeq : ep = Polynomial.C E.a₃ := by rw [hep, ha₁]; simp
        rw [hepeq, Polynomial.C_eq_algebraMap]
        exact (IsScalarTower.algebraMap_apply L (Polynomial L) (RatFunc L) E.a₃).symm
      have hnes : algebraMap L (RatFunc L) E.a₃ ≠ 0 := by
        have hpne : algebraMap (Polynomial L) (RatFunc L) ep ≠ 0 := by
          intro h
          have heq : algebraMap (Polynomial L) (RatFunc L) (Polynomial.C E.a₃)
              = algebraMap (Polynomial L) (RatFunc L) ep := by
            rw [hscalar, Polynomial.C_eq_algebraMap,
              ← IsScalarTower.algebraMap_apply L (Polynomial L) (RatFunc L) E.a₃]
          have h' : algebraMap (Polynomial L) (RatFunc L) (Polynomial.C E.a₃) = 0 := by
            rw [heq]; exact h
          have h'' : Polynomial.C E.a₃ = 0 :=
            RatFunc.algebraMap_injective L (by rw [h', map_zero])
          exact ha₃ (Polynomial.C_eq_zero.mp h'')
        rwa [hscalar] at hpne
      have hv : ∃ Q : Polynomial L, algebraMap (Polynomial L) (RatFunc L) Q = v := by
        obtain ⟨B, hB⟩ := hqe'
        refine ⟨Polynomial.C E.a₃⁻¹ * B, ?_⟩
        have hmul : algebraMap (Polynomial L) (RatFunc L) (Polynomial.C E.a₃⁻¹ * B)
            = (algebraMap L (RatFunc L) E.a₃)⁻¹
              * algebraMap (Polynomial L) (RatFunc L) B := by
          rw [map_mul, Polynomial.C_eq_algebraMap]
          rw [← IsScalarTower.algebraMap_apply L (Polynomial L) (RatFunc L) E.a₃⁻¹]
          rw [map_inv₀]
        rw [hmul]
        have hB' : v * algebraMap L (RatFunc L) E.a₃
            = algebraMap (Polynomial L) (RatFunc L) B := by
          rw [← hscalar]; exact hB
        rw [← hB']
        rw [mul_comm v (algebraMap L (RatFunc L) E.a₃), ← mul_assoc,
          inv_mul_cancel₀ hnes, one_mul]
      refine ⟨?_, hv⟩
      obtain ⟨Q, hQ⟩ := hv
      obtain ⟨N, hNeq⟩ := hN'
      rw [← hQ] at hNeq
      refine RatFuncIntegral w (Q * ep) (Q ^ 2 * cp - N) ?_
      simp only [map_mul, map_pow, map_sub] at hNeq ⊢
      linear_combination (norm := first | refl_ring1 | ring1) hNeq
    · -- Nondegenerate case `a₁ ≠ 0`: the char-two valuation crux.
      have hns : ¬ ∃ s : L, ep ^ 2 ∣ cp - Polynomial.C s * Polynomial.C s
          - Polynomial.C s * ep := by
        simpa [hep, hcp] using EllipticCharTwoNonsingular L E h2 ha₁
      obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := CharTwoCrux L h2 E.a₁ E.a₂ E.a₃ E.a₄ E.a₆ ha₁ hns w v
        (by simpa [hep] using hqe') (by simpa [hep, hcp] using hN')
      exact ⟨⟨P, hP.symm⟩, ⟨Q, hQ.symm⟩⟩
  -- Translate back: `xPsi (algebraMap P) = xPhi P ∈ Ax`.
  obtain ⟨hw, hv⟩ := key
  constructor
  · obtain ⟨P, hP⟩ := hw
    rw [← hP, xPsi_apply_algebraMap, ← xPhi_range E]
    exact ⟨P, rfl⟩
  · obtain ⟨Q, hQ⟩ := hv
    rw [← hQ, xPsi_apply_algebraMap, ← xPhi_range E]
    exact ⟨Q, rfl⟩

end Work.MotC2
