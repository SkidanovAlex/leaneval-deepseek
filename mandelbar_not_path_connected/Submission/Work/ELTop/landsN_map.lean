import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ParamRays.Interface

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open scoped ComplexConjugate

namespace Work.ELTop

/-! ## The angle doubling map on the Böttcher values

The exterior point `rayPoint θ t = t exp (2πiθ)` is equivariant for the angle doubling
`T θ = -2θ mod 1` and the squaring followed by conjugation, which is exactly the dynamical
equation `φ (T_c z) = conj (φ z)^2` of the Böttcher coordinate in the Böttcher plane. -/

/-- `T θ = -2θ mod 1`, so the Böttcher values at angles `T θ` and `-2θ` agree. -/
theorem rayPoint_T (θ t : ℝ) :
    Work.Top.NakaneData.rayPoint (Work.EL.T θ) t = Work.Top.NakaneData.rayPoint (-2 * θ) t := by
  have hT : Work.EL.T θ = -2 * θ + (-⌊-2 * θ⌋ : ℤ) := by
    unfold Work.EL.T
    rw [Int.fract]
    push_cast
    ring
  rw [hT]
  exact rayPoint_add_int (-2 * θ) t (-⌊-2 * θ⌋)

/-- The angle doubling corresponds to conjugating and squaring the Böttcher value. -/
theorem rayPoint_neg_two (θ s : ℝ) :
    Work.Top.NakaneData.rayPoint (-2 * θ) (s ^ 2)
      = conj (Work.Top.NakaneData.rayPoint θ s) ^ 2 := by
  simp only [Work.Top.NakaneData.rayPoint]
  rw [map_mul]
  rw [show conj (↑s : ℂ) = ↑s by simp]
  rw [show conj (Complex.exp (2 * ↑Real.pi * ↑θ * Complex.I))
      = Complex.exp (-(2 * ↑Real.pi * ↑θ * Complex.I)) by
        rw [← Complex.exp_conj]; congr 1
        simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]; ring]
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 2
  · push_cast; ring
  · push_cast; ring

/-- The Böttcher value at angle `T θ` and squared level is the conjugate square of the value
at angle `θ` and level `s`. -/
theorem rayPoint_T_sq (θ s : ℝ) :
    Work.Top.NakaneData.rayPoint (Work.EL.T θ) (s ^ 2)
      = conj (Work.Top.NakaneData.rayPoint θ s) ^ 2 := by
  rw [rayPoint_T]
  exact rayPoint_neg_two θ s

/-! ## The ray points are equivariant under `T_c` -/

/-- **The ray point of angle `T θ` at level `s²` is the image under `T_c` of the ray point of
angle `θ` at level `s`.**  This is the dynamical equivariance of the Böttcher coordinate
`φ (T_c z) = conj (φ z)^2`, read on the level sets of `‖φ‖`. -/
theorem rayPt_T {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {θ s : ℝ} (hs : 1 < s) :
    Work.EL.rayPt hN (Work.EL.T θ) (s ^ 2) = Tantibar c (Work.EL.rayPt hN θ s) := by
  have hsq : (1 : ℝ) < s ^ 2 := by nlinarith
  have hzK : Work.EL.rayPt hN θ s ∉ Work.EL.K c := Work.EL.rayPt_notMem_K hN hs
  have hzb : ¬ Work.ParamRays.BoundedOrbit c (Work.EL.rayPt hN θ s) := hzK
  have hesc : Work.ParamRays.Escaping c (Work.EL.rayPt hN θ s) :=
    (Work.ParamRays.escaping_iff_not_bounded c _).mpr hzb
  have hesc1 : Work.ParamRays.Escaping c (Tantibar c (Work.EL.rayPt hN θ s)) := by
    have h := Work.ParamRays.Escaping.iterate hesc 1
    simpa [Work.ParamRays.orbit] using h
  have hTzK : Tantibar c (Work.EL.rayPt hN θ s) ∉ Work.EL.K c :=
    (Work.ParamRays.escaping_iff_not_bounded c _).mp hesc1
  have hPhiz : φ (Work.EL.rayPt hN θ s) = Work.Top.NakaneData.rayPoint θ s := by
    rw [← Work.EL.dynPhi_of_notMem (φ := φ) hzK]
    exact Work.Top.NakaneData.Phi_rayPt hN hs
  have hval : Work.EL.dynPhi c φ (Tantibar c (Work.EL.rayPt hN θ s))
      = Work.Top.NakaneData.rayPoint (Work.EL.T θ) (s ^ 2) := by
    rw [Work.EL.dynPhi_of_notMem hTzK, hφ.2.1 _ hesc, hPhiz]
    exact (rayPoint_T_sq θ s).symm
  exact Work.Top.NakaneData.injOn_Phi hN (Work.Top.NakaneData.rayPt_notMem hN hsq) hTzK
    (by rw [Work.Top.NakaneData.Phi_rayPt hN hsq, hval])

/-! ## Landing is equivariant under `T_c` -/

theorem one_lt_sqrt {t : ℝ} (ht : 1 < t) : 1 < Real.sqrt t := by
  have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) ht
  rwa [Real.sqrt_one] at h

/-- **Landing is natural under `T_c`**: if the ray of angle `θ` lands at `y`, then the ray of
angle `T θ` lands at `T_c y`. -/
theorem landsN_map {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) {θ : ℝ} {y : ℂ} (h : Work.EL.LandsN hN θ y) :
    Work.EL.LandsN hN (Work.EL.T θ) (LeanEval.ComplexAnalysis.Tantibar c y) := by
  -- the square root map pushes `1⁺` to `1⁺`
  have hsqrt : Filter.Tendsto (fun t : ℝ => Real.sqrt t) (nhdsWithin 1 (Set.Ioi 1))
      (nhdsWithin 1 (Set.Ioi 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using (Real.continuous_sqrt.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact one_lt_sqrt ht
  -- the ray points of angle `θ` at level `√t` converge to `y`
  have hcomp : Filter.Tendsto (fun t : ℝ => Work.EL.rayPt hN θ (Real.sqrt t))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds y) := h.comp hsqrt
  have hcont : Continuous (fun w : ℂ => Tantibar c w) := by
    unfold LeanEval.ComplexAnalysis.Tantibar
    fun_prop
  have hcomp2 : Filter.Tendsto
      (fun t : ℝ => Tantibar c (Work.EL.rayPt hN θ (Real.sqrt t)))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (Tantibar c y)) :=
    (hcont.tendsto y).comp hcomp
  have heq : (fun t : ℝ => Work.EL.rayPt hN (Work.EL.T θ) t)
      =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        (fun t : ℝ => Tantibar c (Work.EL.rayPt hN θ (Real.sqrt t))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht1 : (1 : ℝ) < t := ht
    have hsq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt (le_of_lt (by linarith))
    have hgoal := rayPt_T hN hφ (θ := θ) (s := Real.sqrt t) (one_lt_sqrt ht1)
    rwa [hsq] at hgoal
  exact Filter.Tendsto.congr' heq.symm hcomp2

end Work.ELTop
