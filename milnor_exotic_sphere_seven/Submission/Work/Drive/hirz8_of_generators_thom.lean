import Mathlib
import Submission.Work.Drive.Interfaces

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `Hirz8` from two Hirzebruch generators and the rational Thom theorem

This file proves the pure-algebra bridge of the drive: if two closed oriented smooth 8-manifolds
`G₁`, `G₂` satisfy Hirzebruch's identity `45σ = 7p₂ - p₁²` and their Pontryagin-number vectors
`(p₁², p₂)` are linearly independent, and if the rational Thom theorem holds (a weighted family of
closed oriented 8-manifolds whose weighted `p₁²`- and `p₂`-numbers vanish has vanishing weighted
signature), then Hirzebruch's identity holds for every closed oriented smooth 8-manifold.

The argument is Cramer's rule. Fix `M` and let
`A = p₁²(M)`, `B = p₂(M)`, `S = σ(M)`, `Aᵢ = p₁²(Gᵢ)`, `Bᵢ = p₂(Gᵢ)`, `D = A₁B₂ - B₁A₂ ≠ 0`.
Apply `ThomRational` to the family `(M, G₁, G₂)` with the weights
`(D, -(AB₂ - BA₂), -(A₁B - B₁A))`; both the weighted `p₁²`-sum and the weighted `p₂`-sum are
identically zero, so
`D S - (AB₂ - BA₂) σ₁ - (A₁B - B₁A) σ₂ = 0`.
Multiplying by `45` and substituting `45σᵢ = 7Bᵢ - Aᵢ` turns this into
`D (45S - (7B - A)) = 0`, whence `45S = 7B - A` since `D ≠ 0`.
-/

namespace Work.Drive

/-- Cramer's rule arithmetic, isolated: the weighted signature relation for `(M, G₁, G₂)` with the
weights `(D, -(AB₂ - BA₂), -(A₁B - B₁A))`, together with the two generators' Hirzebruch identities,
forces `D (45S - (7B - A)) = 0`. -/
private lemma cramer_key (A B A₁ B₁ A₂ B₂ S s₁ s₂ : ℤ)
    (h1 : 45 * s₁ = 7 * B₁ - A₁) (h2 : 45 * s₂ = 7 * B₂ - A₂)
    (h0 : (A₁ * B₂ - B₁ * A₂) * S + (-(A * B₂ - B * A₂)) * s₁
      + (-(A₁ * B - B₁ * A)) * s₂ = 0) :
    (A₁ * B₂ - B₁ * A₂) * (45 * S - (7 * B - A)) = 0 := by
  linear_combination (45 : ℤ) * h0 - (-(A * B₂ - B * A₂)) * h1 - (-(A₁ * B - B₁ * A)) * h2

/-- **`Hirz8` from two generators and the rational Thom theorem.** -/
theorem hirz8_of_generators_thom (hG : Work.Drive.Generators8) (hT : Work.Drive.ThomRational) :
    Work.Drive.Hirz8 := by
  obtain ⟨G₁, G₂, hG₁, hG₂, hindep⟩ := hG
  intro M
  have h1 : 45 * G₁.sigma = 7 * G₁.p2Num - G₁.p1Sq := hG₁
  have h2 : 45 * G₂.sigma = 7 * G₂.p2Num - G₂.p1Sq := hG₂
  -- the Cramer weights for the family `(M, G₁, G₂)`
  have hp1 : ∑ i : Fin 3,
      (![G₁.p1Sq * G₂.p2Num - G₁.p2Num * G₂.p1Sq,
        -(M.p1Sq * G₂.p2Num - M.p2Num * G₂.p1Sq),
        -(G₁.p1Sq * M.p2Num - G₁.p2Num * M.p1Sq)] : Fin 3 → ℤ) i
        * (![M, G₁, G₂] i).p1Sq = 0 := by
    simp [Fin.sum_univ_three]
    ring
  have hp2 : ∑ i : Fin 3,
      (![G₁.p1Sq * G₂.p2Num - G₁.p2Num * G₂.p1Sq,
        -(M.p1Sq * G₂.p2Num - M.p2Num * G₂.p1Sq),
        -(G₁.p1Sq * M.p2Num - G₁.p2Num * M.p1Sq)] : Fin 3 → ℤ) i
        * (![M, G₁, G₂] i).p2Num = 0 := by
    simp [Fin.sum_univ_three]
    ring
  have hσ := hT 3 ![M, G₁, G₂]
    (![G₁.p1Sq * G₂.p2Num - G₁.p2Num * G₂.p1Sq,
       -(M.p1Sq * G₂.p2Num - M.p2Num * G₂.p1Sq),
       -(G₁.p1Sq * M.p2Num - G₁.p2Num * M.p1Sq)] : Fin 3 → ℤ) hp1 hp2
  have hσ' : (G₁.p1Sq * G₂.p2Num - G₁.p2Num * G₂.p1Sq) * M.sigma
      + (-(M.p1Sq * G₂.p2Num - M.p2Num * G₂.p1Sq)) * G₁.sigma
      + (-(G₁.p1Sq * M.p2Num - G₁.p2Num * M.p1Sq)) * G₂.sigma = 0 := by
    simpa [Fin.sum_univ_three] using hσ
  have hkey := cramer_key M.p1Sq M.p2Num G₁.p1Sq G₁.p2Num G₂.p1Sq G₂.p2Num M.sigma G₁.sigma
    G₂.sigma h1 h2 hσ'
  have hD : (G₁.p1Sq * G₂.p2Num - G₁.p2Num * G₂.p1Sq) ≠ 0 := sub_ne_zero.mpr hindep
  have hfin : 45 * M.sigma - (7 * M.p2Num - M.p1Sq) = 0 := by
    rcases mul_eq_zero.mp hkey with h | h
    · exact absurd h hD
    · exact h
  exact sub_eq_zero.mp hfin

end Work.Drive
