import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB6.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB6

theorem zeroPoint_fs {ρz a ℓ : ℝ} (hρz : 0 < ρz) (ha : 0 < a) (hℓ : 0 < ℓ) {n : ℕ} (hn : 1 ≤ n)
    (hrel : (n : ℝ) + 1 = ℓ * Real.sqrt (ρz * a))
    (hconst : (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * Work.BoseB6.lhyValue (8 * Real.pi) = 4 * Real.pi * Work.BoseB6.lhySharp)
    (hmesh : |(Work.BoseB6.meshD n) ^ 3 * Work.BoseB6.latticeSum (8 * Real.pi) n + Work.BoseB6.lhyValue (8 * Real.pi)| ≤ Work.BoseB6.latticeMeshErr (8 * Real.pi) n) :
    -(1 / 2) * (ρz * a) * Work.BoseB6.latticeSum (8 * Real.pi) n
      ≥ 4 * Real.pi * Work.BoseB6.lhySharp * (ρz * a) ^ (5 / 2 : ℝ) * ℓ ^ 3
        - (1 / 2) * (((2 * Real.pi) ^ 3)⁻¹) * (ρz * a) ^ (5 / 2 : ℝ) * ℓ ^ 3 * Work.BoseB6.latticeMeshErr (8 * Real.pi) n := by
  -- Elementary reduction.  Write `P = ρ_z a`, `D = meshD n = 2π/(n+1) = 2π/(ℓ√P)`,
  -- `S = latticeSum (8π) n`, `M = latticeMeshErr (8π) n`, `V = lhyValue (8π)`.
  -- The hypothesis `hmesh` gives `D³S ≤ M − V`; multiplying by the positive number
  -- `(1/2)P/D³` and negating yields `−((1/2)P S) ≥ ((1/2)P/D³)(V−M)`.  It remains to
  -- identify `(1/2)P/D³` with the coefficient `(1/2)(2π)⁻³ P^{5/2}ℓ³` of the goal;
  -- that identity is `D³ℓ³P^{5/2} = (2π)³P`, which follows from `(n+1)³ = ℓ³P^{3/2}`
  -- and `D³(n+1)³ = (2π)³`, together with `P^{3/2}·P = P^{5/2}`.
  have hP : 0 < ρz * a := mul_pos hρz ha
  have hD : 0 < Work.BoseB6.meshD n := by unfold Work.BoseB6.meshD; positivity
  have hD3 : (Work.BoseB6.meshD n)^3 ≠ 0 := by positivity
  have hsq3 : Real.sqrt (ρz*a) ^ 3 = (ρz*a) ^ (3/2:ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hP.le]; norm_num
  have hu : (n:ℝ) + 1 ≠ 0 := by positivity
  have hDu : Work.BoseB6.meshD n * ((n:ℝ)+1) = 2*Real.pi := by
    unfold Work.BoseB6.meshD
    rw [div_mul_cancel₀]; exact hu
  have hu3 : ((n:ℝ)+1)^3 = ℓ^3 * (ρz*a)^(3/2:ℝ) := by rw [hrel, mul_pow, hsq3]
  have hk3 : (Work.BoseB6.meshD n)^3 * (ℓ^3 * (ρz*a)^(3/2:ℝ)) = (2*Real.pi)^3 := by
    rw [← hu3, ← mul_pow, hDu]
  have hpadd : (ρz*a)^(3/2:ℝ) * (ρz*a) = (ρz*a)^(5/2:ℝ) := by
    have h := Real.rpow_add hP (3/2:ℝ) 1
    simp only [Real.rpow_one] at h
    rw [show (3:ℝ)/2 + 1 = 5/2 by norm_num] at h
    exact h.symm
  have hkey : (Work.BoseB6.meshD n)^3 * (ℓ^3 * (ρz*a)^(5/2:ℝ)) = (2*Real.pi)^3 * (ρz*a) := by
    calc (Work.BoseB6.meshD n)^3 * (ℓ^3 * (ρz*a)^(5/2:ℝ))
        = (Work.BoseB6.meshD n)^3 * (ℓ^3 * ((ρz*a)^(3/2:ℝ) * (ρz*a))) := by rw [hpadd]
      _ = (Work.BoseB6.meshD n)^3 * (ℓ^3 * (ρz*a)^(3/2:ℝ)) * (ρz*a) := by ring
      _ = (2*Real.pi)^3 * (ρz*a) := by rw [hk3]
  have hKval : ((2*Real.pi)^3 : ℝ) = 8*Real.pi^3 := by ring
  have hstep : (1/2) * (((2*Real.pi)^3)⁻¹) * ((Work.BoseB6.meshD n)^3 * (ℓ^3 * (ρz*a)^(5/2:ℝ)))
      = (1/2)*(ρz*a) := by
    rw [hkey, hKval]
    field_simp
  have hcoef : (1/2) * (((2 * Real.pi) ^ 3)⁻¹) * (ρz*a)^(5/2:ℝ) * ℓ^3
      = (1/2)*(ρz*a)/(Work.BoseB6.meshD n)^3 := by
    rw [eq_div_iff hD3]
    rw [show (1/2) * (((2*Real.pi)^3)⁻¹) * (ρz*a)^(5/2:ℝ) * ℓ^3 * (Work.BoseB6.meshD n)^3
          = (1/2) * (((2*Real.pi)^3)⁻¹) * ((Work.BoseB6.meshD n)^3 * (ℓ^3 * (ρz*a)^(5/2:ℝ))) by ring]
    exact hstep
  have hup2 : (Work.BoseB6.meshD n)^3 * Work.BoseB6.latticeSum (8*Real.pi) n
      ≤ Work.BoseB6.latticeMeshErr (8*Real.pi) n - Work.BoseB6.lhyValue (8*Real.pi) := by
    have h2 := (abs_le.mp hmesh).2
    linarith
  have hc : 0 < (1/2)*(ρz*a)/(Work.BoseB6.meshD n)^3 := by positivity
  have hneg : ((1/2)*(ρz*a)/(Work.BoseB6.meshD n)^3) * (Work.BoseB6.lhyValue (8*Real.pi) - Work.BoseB6.latticeMeshErr (8*Real.pi) n)
      ≤ -(1/2)*(ρz*a)*Work.BoseB6.latticeSum (8*Real.pi) n := by
    have hmul := mul_le_mul_of_nonneg_left hup2 hc.le
    have h1 : ((1/2)*(ρz*a)/(Work.BoseB6.meshD n)^3) * ((Work.BoseB6.meshD n)^3 * Work.BoseB6.latticeSum (8*Real.pi) n)
        = (1/2)*(ρz*a)*Work.BoseB6.latticeSum (8*Real.pi) n := by
      field_simp
    have h2 : ((1/2)*(ρz*a)/(Work.BoseB6.meshD n)^3) * (Work.BoseB6.latticeMeshErr (8*Real.pi) n - Work.BoseB6.lhyValue (8*Real.pi))
        = -(((1/2)*(ρz*a)/(Work.BoseB6.meshD n)^3) * (Work.BoseB6.lhyValue (8*Real.pi) - Work.BoseB6.latticeMeshErr (8*Real.pi) n)) := by ring
    linarith
  rw [ge_iff_le, ← hconst]
  have heq : (1/2) * (((2*Real.pi)^3)⁻¹) * Work.BoseB6.lhyValue (8*Real.pi) * (ρz*a)^(5/2:ℝ) * ℓ^3
      - (1/2) * (((2*Real.pi)^3)⁻¹) * (ρz*a)^(5/2:ℝ) * ℓ^3 * Work.BoseB6.latticeMeshErr (8*Real.pi) n
      = ((1/2)*(ρz*a)/(Work.BoseB6.meshD n)^3) * (Work.BoseB6.lhyValue (8*Real.pi) - Work.BoseB6.latticeMeshErr (8*Real.pi) n) := by
    rw [← hcoef]; ring
  rw [heq]
  exact hneg

end Work.BoseB6
