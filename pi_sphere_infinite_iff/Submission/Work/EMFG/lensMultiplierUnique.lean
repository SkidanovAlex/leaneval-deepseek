import Mathlib
import Submission.Work.RatHurewicz.LensSpace.Basic
import Submission.Work.EMFG.lensIsometry

namespace Work.EMFG

/-- The multiplier relating two `μₙ`-orbits that both shadow the same family of points `x i`
to within `ε`, when the action is separated by more than `4ε`. -/
theorem lensMultiplierUnique {n N : ℕ} [NeZero n] {β : Type} (b : β)
    {ε : ℝ} (hsep : ∀ (z : Work.RatHurewicz.lensTotal N)
      (g : Multiplicative (ZMod n)), g ≠ 1 → 4 * ε < dist (g • z) z)
    (x : β → Work.RatHurewicz.lensTotal N) (e z : Work.RatHurewicz.lensTotal N)
    (lam mu : β → Multiplicative (ZMod n))
    (hlam : ∀ i, (lam i) • e ∈ Metric.ball (x i) ε)
    (hmu : ∀ i, (mu i) • z ∈ Metric.ball (x i) ε) :
    ∃ k : Multiplicative (ZMod n), ∀ i, mu i = lam i * k := by
  classical
  -- Step 1: for every `i`, the point `e` is within `2ε` of `((lam i)⁻¹ * mu i) • z`.
  have key : ∀ i, dist e (((lam i)⁻¹ * mu i) • z) < 2 * ε := by
    intro i
    have h1 : dist ((lam i)⁻¹ • x i) e < ε := by
      have hh := Metric.mem_ball.mp (hlam i)
      have hiso := lensIsometry n N ((lam i)⁻¹) ((lam i) • e) (x i)
      rw [inv_smul_smul] at hiso
      rw [← hiso] at hh
      rwa [dist_comm] at hh
    have h2 : dist ((lam i)⁻¹ • x i) (((lam i)⁻¹ * mu i) • z) < ε := by
      have hh := Metric.mem_ball.mp (hmu i)
      rw [dist_comm] at hh
      have hiso := lensIsometry n N ((lam i)⁻¹) (x i) ((mu i) • z)
      rw [← mul_smul] at hiso
      rw [← hiso] at hh
      exact hh
    have h3 := dist_triangle e ((lam i)⁻¹ • x i) (((lam i)⁻¹ * mu i) • z)
    rw [dist_comm] at h1
    linarith
  -- Step 2: the multipliers `(lam i)⁻¹ * mu i` do not depend on `i`.
  have heq : ∀ i j, (lam i)⁻¹ * mu i = (lam j)⁻¹ * mu j := by
    intro i j
    by_contra hne
    have hlt : dist (((lam i)⁻¹ * mu i) • z) (((lam j)⁻¹ * mu j) • z) < 4 * ε := by
      have h3 := dist_triangle (((lam i)⁻¹ * mu i) • z) e (((lam j)⁻¹ * mu j) • z)
      have hii := key i
      have hjj := key j
      rw [dist_comm] at hii
      linarith
    have hgt : 4 * ε < dist (((lam i)⁻¹ * mu i) • z) (((lam j)⁻¹ * mu j) • z) := by
      have hne' : ((lam i)⁻¹ * mu i)⁻¹ * ((lam j)⁻¹ * mu j) ≠ 1 := by
        intro h
        apply hne
        have hh : (lam j)⁻¹ * mu j = (lam i)⁻¹ * mu i := by
          calc (lam j)⁻¹ * mu j
              = ((lam i)⁻¹ * mu i) * (((lam i)⁻¹ * mu i)⁻¹ * ((lam j)⁻¹ * mu j)) := by
                group
            _ = ((lam i)⁻¹ * mu i) * 1 := by rw [h]
            _ = (lam i)⁻¹ * mu i := by rw [mul_one]
        exact hh.symm
      have hsp := hsep z (((lam i)⁻¹ * mu i)⁻¹ * ((lam j)⁻¹ * mu j)) hne'
      have hiso := lensIsometry n N (((lam i)⁻¹ * mu i)⁻¹)
        (((lam i)⁻¹ * mu i) • z) (((lam j)⁻¹ * mu j) • z)
      rw [inv_smul_smul, ← mul_smul] at hiso
      rw [dist_comm] at hsp
      rwa [hiso] at hsp
    linarith
  -- Step 3: assemble with `k = (lam b)⁻¹ * mu b`.
  refine ⟨(lam b)⁻¹ * mu b, fun i => ?_⟩
  have hbi : (lam i)⁻¹ * mu i = (lam b)⁻¹ * mu b := heq i b
  calc mu i = lam i * ((lam i)⁻¹ * mu i) := by group
    _ = lam i * ((lam b)⁻¹ * mu b) := by rw [hbi]

end Work.EMFG
