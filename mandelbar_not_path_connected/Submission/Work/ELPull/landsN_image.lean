/-
# The image of a landing ray under `Tantibar c`

If the external ray of angle `θ` (in the dynamical Böttcher/Nakane vocabulary `LandsN`) lands
at the point `y` of the filled Julia set, then the external ray of the image angle
`T θ = -2 θ mod 1` lands at the image point `Tantibar c y`.

The argument is the dynamical Böttcher functional equation together with the arithmetic of the
Böttcher plane:

* `exp_two_pi_fract` : `exp (2πi · fract a · i) = exp (2πi a · i)`, i.e. the exponential is
  `1`-periodic in the angle;
* `rayPoint_neg_conj` : `conj (rayPoint θ t) = rayPoint (-θ) t`;
* `rayPoint_sq` : `rayPoint θ t ^ 2 = rayPoint (2 θ) (t ^ 2)`;
* `rayPoint_mod_one` : `rayPoint a t = rayPoint (fract a) t`;
* `rayPoint_T_conj_sq` : `conj (rayPoint θ t) ^ 2 = rayPoint (T θ) (t ^ 2)`, the image of a
  ray point under `w ↦ conj w ^ 2`;
* `dynPhi_Tantibar` : the Böttcher functional equation `dynPhi c (Tantibar c z) = conj (dynPhi c z)^2`
  off the filled Julia set, inherited from the Böttcher coordinate `dynPhiOf c`;
* `rayPt_Tantibar` : the image of the ray point of angle `θ` at level `t` is the ray point of
  angle `T θ` at level `t ^ 2`; and finally the limit statement `landsN_image`.
-/
import Mathlib
import Submission.Work.ELPull.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Function Filter
open scoped Topology ComplexConjugate

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Arithmetic of the Böttcher plane -/

/-- The exponential `exp (2πi θ i)` only depends on the angle `θ` modulo `1`. -/
theorem exp_two_pi_fract (a : ℝ) :
    Complex.exp (2 * (Real.pi : ℂ) * ((Int.fract a : ℝ) : ℂ) * Complex.I)
      = Complex.exp (2 * (Real.pi : ℂ) * ((a : ℝ) : ℂ) * Complex.I) := by
  have h : ((Int.fract a : ℝ) : ℂ) + (((⌊a⌋ : ℤ) : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by
    rw [← Complex.ofReal_add, Int.fract_add_floor]
  rw [show ((a : ℝ) : ℂ) = ((Int.fract a : ℝ) : ℂ) + (((⌊a⌋ : ℤ) : ℝ) : ℂ) from h.symm]
  rw [show (2 : ℂ) * ↑Real.pi * (((Int.fract a : ℝ) : ℂ) + (((⌊a⌋ : ℤ) : ℝ) : ℂ)) * Complex.I
      = 2 * ↑Real.pi * ((Int.fract a : ℝ) : ℂ) * Complex.I
        + (((⌊a⌋ : ℤ) : ℝ) : ℂ) * (2 * ↑Real.pi * Complex.I) from by ring]
  rw [Complex.exp_add, Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_two_pi_mul_I,
    one_zpow, mul_one]

/-- Complex conjugation sends the ray point of angle `θ` to the ray point of angle `-θ`. -/
theorem rayPoint_neg_conj (θ t : ℝ) :
    (starRingEnd ℂ) (Work.Top.NakaneData.rayPoint θ t)
      = Work.Top.NakaneData.rayPoint (-θ) t := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, map_mul,
    Complex.conj_ofReal, (Complex.exp_conj (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I)).symm]
  congr 2
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

/-- The square of the ray point of angle `a` at level `u` is the ray point of the doubled
angle `2 a` at level `u ^ 2`. -/
theorem rayPoint_sq (a u : ℝ) :
    Work.Top.NakaneData.rayPoint a u ^ 2
      = Work.Top.NakaneData.rayPoint (2 * a) (u ^ 2) := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, mul_pow,
    (Complex.exp_nat_mul (2 * (Real.pi : ℂ) * (a : ℂ) * Complex.I) 2).symm]
  push_cast
  congr 2
  ring

/-- The ray point of angle `a` only depends on `a` modulo `1`. -/
theorem rayPoint_mod_one (a u : ℝ) :
    Work.Top.NakaneData.rayPoint a u = Work.Top.NakaneData.rayPoint (Int.fract a) u := by
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, exp_two_pi_fract a]

/-- The image of a ray point under `w ↦ conj w ^ 2` is the ray point of the doubled angle
`T θ = -2θ mod 1` at squared modulus. -/
theorem rayPoint_T_conj_sq (θ t : ℝ) :
    (starRingEnd ℂ) (Work.Top.NakaneData.rayPoint θ t) ^ 2
      = Work.Top.NakaneData.rayPoint (T θ) (t ^ 2) := by
  rw [rayPoint_neg_conj θ t, rayPoint_sq]
  rw [show (2 : ℝ) * (-θ) = -2 * θ by ring, rayPoint_mod_one]
  rfl

/-! ## The dynamical Böttcher functional equation -/

/-- **The Böttcher functional equation for `dynPhi c`.**  Off the filled Julia set, `dynPhi c`
satisfies `dynPhi c (Tantibar c z) = conj (dynPhi c z) ^ 2`, as inherited from the input
Böttcher coordinate `dynPhiOf c`. -/
theorem dynPhi_Tantibar {c : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    {z : ℂ} (hz : z ∉ Work.ParamRays.filledJulia c) :
    Work.ParamRays.dynPhi c (Tantibar c z)
      = (starRingEnd ℂ) (Work.ParamRays.dynPhi c z) ^ 2 := by
  have hesc : Work.ParamRays.Escaping c z :=
    (Work.ParamRays.escaping_iff_not_bounded c z).mpr
      (by simpa [Work.ParamRays.filledJulia] using hz)
  have hstep : Work.ParamRays.dynPhiOf c (Tantibar c z)
      = (starRingEnd ℂ) (Work.ParamRays.dynPhiOf c z) ^ 2 := hφ.2.1 z hesc
  have hz' : Work.ParamRays.dynPhi c z = Work.ParamRays.dynPhiOf c z :=
    Work.ParamRays.dynPhi_of_not_mem hz
  have hT : Work.ParamRays.Escaping c (Tantibar c z) := by
    have h := hesc.iterate 1
    simpa [Work.ParamRays.orbit] using h
  have hTmem : Tantibar c z ∉ Work.ParamRays.filledJulia c := by
    simp only [Work.ParamRays.filledJulia, Set.mem_ofPred_eq]
    exact (Work.ParamRays.escaping_iff_not_bounded c (Tantibar c z)).mp hT
  rw [Work.ParamRays.dynPhi_of_not_mem hTmem, hstep, hz']

/-! ## The image of a ray point -/

/-- **The image of a ray point.**  For `t > 1`, the image of the point of the ray of angle `θ`
at level `t` under `Tantibar c` is the point of the ray of angle `T θ` at level `t ^ 2`. -/
theorem rayPt_Tantibar {c : ℂ} (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    {θ t : ℝ} (ht : 1 < t) :
    hN.rayPt (T θ) (t ^ 2) = Tantibar c (hN.rayPt θ t) := by
  have hzt : 1 < t ^ 2 := by nlinarith
  have hzF : hN.rayPt θ t ∉ Work.ParamRays.filledJulia c := hN.rayPt_notMem ht
  have hTF : Tantibar c (hN.rayPt θ t) ∉ Work.ParamRays.filledJulia c := by
    have hesc : Work.ParamRays.Escaping c (hN.rayPt θ t) :=
      (Work.ParamRays.escaping_iff_not_bounded c _).mpr
        (by simpa [Work.ParamRays.filledJulia] using hzF)
    have hT := hesc.iterate 1
    simp only [Work.ParamRays.filledJulia, Set.mem_ofPred_eq]
    refine (Work.ParamRays.escaping_iff_not_bounded c (Tantibar c (hN.rayPt θ t))).mp ?_
    simpa [Work.ParamRays.orbit] using hT
  have hz2F : hN.rayPt (T θ) (t ^ 2) ∉ Work.ParamRays.filledJulia c :=
    hN.rayPt_notMem hzt
  have hEq : Work.ParamRays.dynPhi c (Tantibar c (hN.rayPt θ t))
      = Work.ParamRays.dynPhi c (hN.rayPt (T θ) (t ^ 2)) := by
    rw [dynPhi_Tantibar hφ hzF, hN.Phi_rayPt ht, rayPoint_T_conj_sq]
    exact (hN.Phi_rayPt hzt).symm
  exact (hN.injOn_Phi hTF hz2F hEq).symm

/-! ## The limit statement -/

/-- **The image of a landing ray.**  If the ray of angle `θ` lands at `y`, then the ray of angle
`T θ` lands at `Tantibar c y`. -/
theorem landsN_image {c : ℂ} (hN : DynB c)
    (hφ : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c))
    {θ : ℝ} {y : ℂ} (h : LandsN hN θ y) :
    LandsN hN (T θ) (LeanEval.ComplexAnalysis.Tantibar c y) := by
  have hmem : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1), 1 < t := self_mem_nhdsWithin
  have hcont : Continuous (Tantibar c) := by
    change Continuous (fun z : ℂ => (starRingEnd ℂ z) ^ 2 + c)
    exact (Complex.continuous_conj.pow 2).add_const c
  have h1 : Tendsto (fun t : ℝ => Tantibar c (hN.rayPt θ t))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) :=
    (hcont.tendsto y).comp h
  have hfg : (fun t : ℝ => Tantibar c (hN.rayPt θ t))
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun t : ℝ => hN.rayPt (T θ) (t ^ 2)) := by
    filter_upwards [hmem] with t ht
    exact (rayPt_Tantibar hN hφ ht).symm
  have h2 : Tendsto (fun t : ℝ => hN.rayPt (T θ) (t ^ 2))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) := h1.congr' hfg
  have hsqrt : Tendsto (fun s : ℝ => Real.sqrt s) (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa [Real.sqrt_one] using
        (Real.continuous_sqrt.continuousAt (x := (1:ℝ))).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)).mpr (by simpa using hs)
  have h3 : Tendsto (fun s : ℝ => hN.rayPt (T θ) ((Real.sqrt s) ^ 2))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) := h2.comp hsqrt
  have h4 : Tendsto (fun s : ℝ => hN.rayPt (T θ) s)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (Tantibar c y)) := by
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Real.sq_sqrt (lt_trans zero_lt_one hs).le]
  exact h4

end Work.ELPull
