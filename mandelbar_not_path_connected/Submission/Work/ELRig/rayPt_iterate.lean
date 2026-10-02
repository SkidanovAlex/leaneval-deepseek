/-
# `rayPt_iterate`: the dynamical ray points under the degree-`1024` map `F`

The external ray of angle `θ` of the antipolynomial `T_c(z) = z̄² + c` is mapped by `T_c` onto
the ray of angle `T θ = -2θ mod 1`, the level `t` being squared (in the Böttcher coordinate the
dynamics is `w ↦ conj w ^ 2`, so `t·e^{2πiθ} ↦ t²·e^{2πi(-2θ)}`).  Iterating this `10` times,
i.e. applying the holomorphic degree-`1024` map `F c = (Tsq c)^[5] = (T_c)^{10}` of the nests,
sends the ray point of angle `θ` and level `t` to the ray point of angle `T^[10] θ` and level
`t ^ 1024`.

The proof has three ingredients:

* `F c z = orbit c z 10`, i.e. `F c = (Tantibar c)^[10]` (`Work.Landing.Tsq` is the second
  iterate of `Tantibar c`);
* the Böttcher functional equation iterated `10` times (`IsDynBottcher.functional_iterate` with
  `n = 5`), giving `φ (F c z) = φ z ^ 1024`, together with `dynPhi = φ` off the filled Julia
  set and the fact that `F` preserves the escaping set;
* the pure angle computation `T^[10] θ ≡ (-2)^10 θ = 1024 θ (mod 1)`, which shows that the two
  points of the exterior circle `(rayPoint θ t) ^ 1024` and `rayPoint (T^[10] θ) (t ^ 1024)`
  coincide (`rayPoint` is `1`-periodic in the angle).

The equality of the two dynamic points is then `Set.InjOn` of `dynPhi c φ` on the complement of
`K c`.
-/
import Mathlib
import Submission.Work.ELRig.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

noncomputable section

namespace Work.ELRig

open scoped Topology ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The angle map `T` modulo `1` -/

/-- The angle-doubling map `T θ = -2θ mod 1` of the antiholomorphic quadratic family is
congruent to `(-2)^n θ` modulo `ℤ`: for every `n` there is an integer `m` with
`T^[n] θ = (-2)^n θ + m`.  (The integer records the `⌊·⌋` produced by `Int.fract` at each
step.) -/
theorem T_iterate_eq_add_int (θ : ℝ) (n : ℕ) :
    ∃ m : ℤ, Work.EL.T^[n] θ = ((-2 : ℝ) ^ n) * θ + m := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨-2 * m - Int.floor (-2 * (Work.EL.T^[n] θ)), ?_⟩
    rw [Function.iterate_succ_apply', Work.EL.T]
    have hfl : Int.fract (-2 * (Work.EL.T^[n] θ)) =
        -2 * (Work.EL.T^[n] θ) - (Int.floor (-2 * (Work.EL.T^[n] θ)) : ℝ) := by
      have h := Int.fract_add_floor (-2 * (Work.EL.T^[n] θ))
      linarith
    rw [hfl, hm]
    push_cast
    ring

/-! ## The circle points `rayPoint` -/

/-- The points `rayPoint θ t = t·e^{2πiθ}` of the exterior of the unit disc: taking the `n`-th
power multiplies the angle by `n` and raises the level to the `n`-th power. -/
theorem rayPoint_pow (θ t : ℝ) (n : ℕ) :
    (Work.Top.NakaneData.rayPoint θ t) ^ n
      = Work.Top.NakaneData.rayPoint (n * θ) (t ^ n) := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint]
  rw [mul_pow, Complex.ofReal_pow, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring_nf

/-- The circle point `rayPoint θ t` depends on the angle only modulo `ℤ`: the rays are
`1`-periodic in the angle, hence invariant under `θ ↦ θ + k` for `k : ℤ`. -/
theorem rayPoint_add_int (a u : ℝ) (k : ℤ) :
    Work.Top.NakaneData.rayPoint (a + k) u = Work.Top.NakaneData.rayPoint a u := by
  have h1 : Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  have harg : (2 * (Real.pi : ℂ) * ((a + k : ℝ) : ℂ) * Complex.I)
      = 2 * (Real.pi : ℂ) * (a : ℂ) * Complex.I
        + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, harg, Complex.exp_add, h1,
    mul_one]

/-! ## The iteration of the ray points -/

theorem rayPt_iterate {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hB : Work.ParamRays.IsDynBottcher c φ) {θ t : ℝ} (ht : 1 < t) :
    Work.EL.F c (Work.EL.rayPt hN θ t) = Work.EL.rayPt hN ((Work.EL.T^[10]) θ) (t ^ (1024 : ℕ)) := by
  -- `Tsq c` is the second iterate of `Tantibar c`, so `F c = (Tantibar c)^[10]`
  have hTsq : Work.Landing.Tsq c = (Tantibar c)^[2] := by
    funext w
    simp [Work.Landing.Tsq, Tantibar, Function.iterate_succ]
  have hFz : Work.EL.F c (Work.EL.rayPt hN θ t)
      = Work.ParamRays.orbit c (Work.EL.rayPt hN θ t) 10 := by
    simp only [Work.EL.F, Work.ParamRays.orbit]
    rw [hTsq, ← Function.iterate_mul]
  -- the angle congruence `T^[10] θ ≡ 1024 θ (mod 1)`
  obtain ⟨m, hm⟩ := T_iterate_eq_add_int θ 10
  have hm1024 : Work.EL.T^[10] θ = (1024 : ℝ) * θ + m := by
    have h : ((-2 : ℝ) ^ 10) = 1024 := by norm_num
    rw [h] at hm
    exact hm
  have hkey : ((1024 : ℕ) * θ : ℝ) = Work.EL.T^[10] θ + ((-m : ℤ) : ℝ) := by
    rw [hm1024]
    push_cast
    ring
  -- the two exterior-circle points agree
  have hray : (Work.Top.NakaneData.rayPoint θ t) ^ (1024 : ℕ) =
      Work.Top.NakaneData.rayPoint (Work.EL.T^[10] θ) (t ^ (1024 : ℕ)) := by
    rw [rayPoint_pow θ t 1024, hkey]
    exact rayPoint_add_int (Work.EL.T^[10] θ) (t ^ (1024 : ℕ)) (-m)
  -- `rayPt θ t` escapes, and so does its image under `F`
  have hzK : Work.EL.rayPt hN θ t ∉ Work.EL.K c := hN.rayPt_notMem ht
  have hzesc : Work.ParamRays.Escaping c (Work.EL.rayPt hN θ t) :=
    (Work.ParamRays.escaping_iff_not_bounded c _).mpr hzK
  have hFesc : Work.ParamRays.Escaping c (Work.EL.F c (Work.EL.rayPt hN θ t)) := by
    rw [hFz]
    exact hzesc.iterate 10
  have hFK : Work.EL.F c (Work.EL.rayPt hN θ t) ∉ Work.EL.K c :=
    (Work.ParamRays.escaping_iff_not_bounded c _).mp hFesc
  -- the Böttcher equation iterated `10` times
  have hphi : φ (Work.EL.F c (Work.EL.rayPt hN θ t))
      = φ (Work.EL.rayPt hN θ t) ^ (1024 : ℕ) := by
    rw [hFz]
    have h5 := hB.functional_iterate hzesc 5
    simpa using h5
  -- both points have the same `dynPhi`-value
  have hPhiF : Work.EL.dynPhi c φ (Work.EL.F c (Work.EL.rayPt hN θ t)) =
      Work.Top.NakaneData.rayPoint (Work.EL.T^[10] θ) (t ^ (1024 : ℕ)) := by
    rw [Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hFK, hphi,
      ← Work.EL.dynPhi_of_notMem (c := c) (φ := φ) hzK, hN.Phi_rayPt ht]
    exact hray
  have ht1024 : (1 : ℝ) < t ^ (1024 : ℕ) := one_lt_pow₀ ht (by norm_num)
  exact hN.injOn_Phi hFK (hN.rayPt_notMem ht1024) (by rw [hPhiF, hN.Phi_rayPt ht1024])

end Work.ELRig
