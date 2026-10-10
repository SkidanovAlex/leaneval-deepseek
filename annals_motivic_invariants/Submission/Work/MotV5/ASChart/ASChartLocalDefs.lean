import Mathlib
import Submission.Work.MotV5.ASChart.ASCore
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASChart.ASChartLocalDefs` — a local copy of the corrected AS chart data

`Work.MotAS.CensusAS2` (the corrected AS chart of the Crauder–Katz link) depends, through
`Work.MotAS.ASLink`, on the *proofs* of the link identities; the present module repeats the
*definitions* of the chart data verbatim (using the local copies `bilinAS`, `stereoAS` of
`Work.MotAS.kleinBilinAS`, `Work.MotAS.kleinStereoAS` of
`Submission/Work/MotV5/ASChart/ASCore.lean`, which are definitionally equal to them), so that the
value lemmas of the chart isomorphism can be developed and verified independently.  The final
theorem `Work.MotV5.ASChart.chartIsoAS2` transfers along the definitional equalities.

The chart is the corrected one of `Submission/Work/MotAS/GUIDE_CENSUSAS2.md`:

* stereographic point `pAS0 = e₀ = (1,0,0,0,0)`,
* source chart `{v₀ = 0} ∩ {v₄ = 1}`, chart vector `chart3 = (0,X₀,X₁,X₂,1)`,
* target chart `{ẑ₄ = 0} ∩ {ẑ₀ = 1}`, chart vector `tchart = (1,X₀,X₁,X₂,0)`,
* `fwVecAS2 = P^AS ∘ y^AS(pAS0, ·)` at `chart3`, `bwVecAS2 = π_{pAS0} ∘ R^AS` at `tchart`,
* `FdivAS2 = linAS2 · sAS2 · fwVecAS2 0`, `GdivAS2 = cubAS2 · sdualAS2 · bwVecAS2 4`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotV5.ASChart

open MvPolynomial

/-- The stereographic point `e₀ = (1,0,0,0,0)`, as a vector of constants. -/
noncomputable def pAS0L (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 3) K := ![1, 0, 0, 0, 0]

/-- The target chart vector `(1,X₀,X₁,X₂,0)`. -/
noncomputable def tchartL (K : Type*) [CommRing K] : Fin 5 → MvPolynomial (Fin 3) K :=
  ![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0]

variable {K : Type*} [Field K]

/-! ## §1 The chart data -/

/-- The forward chart map: `P^AS ∘ y^AS(pAS0, ·)` at the source chart vector `chart3`. -/
noncomputable def fwVecAS2L (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (Work.MotK.chart3 K))

/-- The inverse chart map: `π_{pAS0} ∘ R^AS` at the target chart vector `tchart`. -/
noncomputable def bwVecAS2L (a b g : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  Work.MotK.kleinTwPi (pAS0L K)
    (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchartL K))

/-- The source polar factor `b^AS(pAS0, chart3)`. -/
noncomputable def linAS2L (a b : K) : MvPolynomial (Fin 3) K :=
  bilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (Work.MotK.chart3 K)

/-- The source ruling quintic `s^AS(y^AS(pAS0, chart3))`. -/
noncomputable def sAS2L (a b g : K) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinSecAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (Work.MotK.chart3 K))

/-- The target polar factor `b^AS(pAS0, R^AS(tchart))`. -/
noncomputable def cubAS2L (a b g : K) : MvPolynomial (Fin 3) K :=
  bilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K)
    (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (tchartL K))

/-- The target ruling quintic `s'^AS(tchart)`. -/
noncomputable def sdualAS2L (a b g : K) : MvPolynomial (Fin 3) K :=
  Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
    (tchartL K)

/-- The source equation `b^AS(pAS0, chart3) · s^AS(y^AS(pAS0, chart3))`. -/
noncomputable def GambAS2L (a b g : K) : MvPolynomial (Fin 3) K := linAS2L a b * sAS2L a b g

/-- The target equation `b^AS(pAS0, R^AS(tchart)) · s'^AS(tchart)`. -/
noncomputable def FambAS2L (a b g : K) : MvPolynomial (Fin 3) K := cubAS2L a b g * sdualAS2L a b g

/-- **The source divisor of the chart.** -/
noncomputable def FdivAS2L (a b g : K) : MvPolynomial (Fin 3) K :=
  linAS2L a b * sAS2L a b g * fwVecAS2L a b g 0

/-- **The target divisor of the chart.** -/
noncomputable def GdivAS2L (a b g : K) : MvPolynomial (Fin 3) K :=
  cubAS2L a b g * sdualAS2L a b g * bwVecAS2L a b g 4

/-! ## §2 Basic facts -/

theorem bwVecAS2L_zero (a b g : K) : bwVecAS2L a b g 0 = 0 := by
  simp only [bwVecAS2L, Work.MotK.kleinTwPi, pAS0L, Matrix.cons_val_zero]
  refl_ring1

/-- The AS quadric vanishes at the chart point `pAS0 = e₀`. -/
theorem kleinQAS_pAS0L (a b : K) :
    Work.MotAS.kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) = 0 := by
  simp only [Work.MotAS.kleinQAS, pAS0L, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four]
  refl_ring1

/-- **The quadric on the stereographic image:** `q(y(v)) = q(v)² · q(p)`. -/
theorem kleinQAS_stereoAS_free {R : Type*} [CommRing R] (a b : R) (p v : Fin 5 → R) :
    Work.MotAS.kleinQAS a b (stereoAS a b p v)
      = Work.MotAS.kleinQAS a b v ^ 2 * Work.MotAS.kleinQAS a b p := by
  simp only [stereoAS, bilinAS, Work.MotAS.kleinQAS, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  refl_ring1

/-- The fourth coordinate of the forward chart map vanishes: the target chart is `{ẑ₄ = 0}`. -/
theorem fwVecAS2L_four (a b g : K) : fwVecAS2L a b g 4 = 0 := by
  have h4 : fwVecAS2L a b g 4
      = -Work.MotAS.kleinQAS (MvPolynomial.C a) (MvPolynomial.C b)
          (stereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K) (Work.MotK.chart3 K)) := by
    simp only [fwVecAS2L]
    exact kleinPAS_four_eq_neg_free _ _ _ _
  rw [h4, kleinQAS_stereoAS_free, kleinQAS_pAS0L, mul_zero, neg_zero]

/-- `linAS2L` is the constant `-2 (a² - ab - b²)`. -/
theorem linAS2L_eq_const (a b : K) :
    linAS2L a b = -(2 : MvPolynomial (Fin 3) K)
      * (MvPolynomial.C a ^ 2 - MvPolynomial.C a * MvPolynomial.C b
          - MvPolynomial.C b ^ 2) := by
  have hchart : (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) = ![0, X 0, X 1, X 2, 1] :=
    rfl
  have hp : pAS0L K = (![1, 0, 0, 0, 0] : Fin 5 → MvPolynomial (Fin 3) K) := rfl
  simp only [linAS2L, bilinAS, hp, hchart, Work.MotAS.kleinQAS, Pi.add_apply, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, zero_add, add_zero]
  refl_ring1

/-- `cubAS2L = linAS2L · bwVecAS2L · 4`. -/
theorem cubAS2L_eq (a b g : K) : cubAS2L a b g = linAS2L a b * bwVecAS2L a b g 4 := by
  have h1 : cubAS2L a b g
      = -(2 : MvPolynomial (Fin 3) K)
          * (MvPolynomial.C a ^ 2 - MvPolynomial.C a * MvPolynomial.C b
              - MvPolynomial.C b ^ 2)
          * Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
              (tchartL K) 4 := by
    simp only [cubAS2L]
    rw [show bilinAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0L K)
          (Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (tchartL K))
        = -(2 : MvPolynomial (Fin 3) K)
            * (MvPolynomial.C a ^ 2 - MvPolynomial.C a * MvPolynomial.C b
                - MvPolynomial.C b ^ 2)
            * Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                (tchartL K) 4 from by
      simp only [bilinAS, pAS0L, Work.MotAS.kleinQAS, Pi.add_apply, Matrix.head_cons,
        Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_four]
      ring]
  have h2 : bwVecAS2L a b g 4
      = Work.MotAS.kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (tchartL K) 4 := by
    simp only [bwVecAS2L, Work.MotK.kleinTwPi]
    rw [show (pAS0L K : Fin 5 → MvPolynomial (Fin 3) K) 4 = 0 from rfl, mul_zero, sub_zero]
  rw [h1, linAS2L_eq_const, h2]

/-! ## §3 The two chart rings -/

/-- `1 / fwVecAS2L · 0` in `R[1/FdivAS2L]`, written as `GambAS2L / (GambAS2L · fwVecAS2L 0)`. -/
noncomputable def invFL (a b g : K) : Localization.Away (FdivAS2L a b g) :=
  IsLocalization.mk' (Localization.Away (FdivAS2L a b g)) (GambAS2L a b g)
    ⟨FdivAS2L a b g,
      (Submonoid.mem_powers_iff (FdivAS2L a b g) (FdivAS2L a b g)).mpr ⟨1, pow_one _⟩⟩

/-- `1 / bwVecAS2L · 4` in `R[1/GdivAS2L]`, written as `FambAS2L / (FambAS2L · bwVecAS2L 4)`. -/
noncomputable def invGL (a b g : K) : Localization.Away (GdivAS2L a b g) :=
  IsLocalization.mk' (Localization.Away (GdivAS2L a b g)) (FambAS2L a b g)
    ⟨GdivAS2L a b g,
      (Submonoid.mem_powers_iff (GdivAS2L a b g) (GdivAS2L a b g)).mpr ⟨1, pow_one _⟩⟩

theorem invFL_spec (a b g : K) :
    invFL a b g * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
        (FdivAS2L a b g)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
          (GambAS2L a b g) :=
  IsLocalization.mk'_spec _ _ _

theorem invGL_spec (a b g : K) :
    invGL a b g * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
        (GdivAS2L a b g)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
          (FambAS2L a b g) :=
  IsLocalization.mk'_spec _ _ _

theorem invFL_mul (a b g : K) :
    invFL a b g * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
        (fwVecAS2L a b g 0) = 1 := by
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
      (GambAS2L a b g)) :=
    IsLocalization.Away.isUnit_of_dvd (FdivAS2L a b g) (dvd_mul_right _ _)
  have hF : algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
        (FdivAS2L a b g)
      = algebraMap _ _ (GambAS2L a b g) * algebraMap _ _ (fwVecAS2L a b g 0) := by
    change algebraMap _ _ (GambAS2L a b g * fwVecAS2L a b g 0) = _
    rw [map_mul]
  have hs := invFL_spec a b g
  rw [hF] at hs
  refine hunit.mul_left_cancel ?_
  rw [mul_one, ← mul_assoc, mul_comm (algebraMap _ _ (GambAS2L a b g)) (invFL a b g)]
  simpa only [← mul_assoc] using hs

theorem invGL_mul (a b g : K) :
    invGL a b g * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
        (bwVecAS2L a b g 4) = 1 := by
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
      (FambAS2L a b g)) :=
    IsLocalization.Away.isUnit_of_dvd (GdivAS2L a b g) (dvd_mul_right _ _)
  have hG : algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
        (GdivAS2L a b g)
      = algebraMap _ _ (FambAS2L a b g) * algebraMap _ _ (bwVecAS2L a b g 4) := by
    change algebraMap _ _ (FambAS2L a b g * bwVecAS2L a b g 4) = _
    rw [map_mul]
  have hs := invGL_spec a b g
  rw [hG] at hs
  refine hunit.mul_left_cancel ?_
  rw [mul_one, ← mul_assoc, mul_comm (algebraMap _ _ (FambAS2L a b g)) (invGL a b g)]
  simpa only [← mul_assoc] using hs

/-- The chart coordinates of the forward chart map. -/
noncomputable def phiFL (a b g : K) : Fin 3 → Localization.Away (FdivAS2L a b g) :=
  ![invFL a b g * algebraMap _ _ (fwVecAS2L a b g 1),
    invFL a b g * algebraMap _ _ (fwVecAS2L a b g 2),
    invFL a b g * algebraMap _ _ (fwVecAS2L a b g 3)]

/-- The chart coordinates of the inverse chart map. -/
noncomputable def psiGL (a b g : K) : Fin 3 → Localization.Away (GdivAS2L a b g) :=
  ![invGL a b g * algebraMap _ _ (bwVecAS2L a b g 1),
    invGL a b g * algebraMap _ _ (bwVecAS2L a b g 2),
    invGL a b g * algebraMap _ _ (bwVecAS2L a b g 3)]

/-- The pullback of the inverse chart map on the chart ring. -/
noncomputable def PhiL (a b g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (GdivAS2L a b g) :=
  MvPolynomial.aeval (psiGL a b g)

/-- The pullback of the forward chart map on the chart ring. -/
noncomputable def PsiL (a b g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (FdivAS2L a b g) :=
  MvPolynomial.aeval (phiFL a b g)

theorem PhiL_X (a b g : K) (j : Fin 3) : PhiL a b g (MvPolynomial.X j) = psiGL a b g j := by
  simp only [PhiL, MvPolynomial.aeval_X]

theorem PsiL_X (a b g : K) (j : Fin 3) : PsiL a b g (MvPolynomial.X j) = phiFL a b g j := by
  simp only [PsiL, MvPolynomial.aeval_X]

/-- The index shift `Fin 3 → Fin 5`, `j ↦ j + 1`. -/
def ch3 (j : Fin 3) : Fin 5 := ⟨j.val + 1, by omega⟩

theorem chart3_ch3 (j : Fin 3) :
    (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) (ch3 j)
      = (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
  fin_cases j <;> rfl

theorem tchartL_ch3 (j : Fin 3) :
    (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) (ch3 j)
      = (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
  fin_cases j <;> rfl

theorem psiGL_ch3 (a b g : K) (j : Fin 3) :
    psiGL a b g j = invGL a b g * algebraMap (MvPolynomial (Fin 3) K)
      (Localization.Away (GdivAS2L a b g)) (bwVecAS2L a b g (ch3 j)) := by
  fin_cases j <;> rfl

theorem phiFL_ch3 (a b g : K) (j : Fin 3) :
    phiFL a b g j = invFL a b g * algebraMap (MvPolynomial (Fin 3) K)
      (Localization.Away (FdivAS2L a b g)) (fwVecAS2L a b g (ch3 j)) := by
  fin_cases j <;> rfl

theorem PhiL_C (a b g : K) (c : K) :
    PhiL a b g (MvPolynomial.C c) = algebraMap K (Localization.Away (GdivAS2L a b g)) c := by
  simp only [PhiL, MvPolynomial.aeval_C]

theorem PsiL_C (a b g : K) (c : K) :
    PsiL a b g (MvPolynomial.C c) = algebraMap K (Localization.Away (FdivAS2L a b g)) c := by
  simp only [PsiL, MvPolynomial.aeval_C]

/-- The source chart vector `chart3` evaluated on the inverse chart map is
`invGL • (algebraMap ∘ bwVecAS2L)`. -/
theorem PhiL_chart3 (a b g : K) :
    (fun i => PhiL a b g (Work.MotK.chart3 K i))
      = fun i => invGL a b g * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (GdivAS2L a b g)) (bwVecAS2L a b g i) := by
  have h0 : PhiL a b g (Work.MotK.chart3 K 0) = 0 := by
    rw [show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 0 = 0 from rfl, map_zero]
  have h1 : PhiL a b g (Work.MotK.chart3 K 1)
      = invGL a b g * algebraMap _ _ (bwVecAS2L a b g 1) := by
    rw [show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 1
      = MvPolynomial.X 0 from rfl, PhiL_X]
    rfl
  have h2 : PhiL a b g (Work.MotK.chart3 K 2)
      = invGL a b g * algebraMap _ _ (bwVecAS2L a b g 2) := by
    rw [show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 2
      = MvPolynomial.X 1 from rfl, PhiL_X]
    rfl
  have h3 : PhiL a b g (Work.MotK.chart3 K 3)
      = invGL a b g * algebraMap _ _ (bwVecAS2L a b g 3) := by
    rw [show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 3
      = MvPolynomial.X 2 from rfl, PhiL_X]
    rfl
  have h4 : PhiL a b g (Work.MotK.chart3 K 4)
      = invGL a b g * algebraMap _ _ (bwVecAS2L a b g 4) := by
    rw [show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 4 = 1 from rfl, map_one,
      invGL_mul]
  funext i
  fin_cases i
  · show PhiL a b g (Work.MotK.chart3 K 0)
        = invGL a b g * algebraMap _ _ (bwVecAS2L a b g 0)
    rw [h0, bwVecAS2L_zero a b g, map_zero, mul_zero]
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- The target chart vector `tchart` evaluated on the forward chart map is
`invFL • (algebraMap ∘ fwVecAS2L)`. -/
theorem PsiL_tchart (a b g : K) :
    (fun i => PsiL a b g (tchartL K i))
      = fun i => invFL a b g * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (FdivAS2L a b g)) (fwVecAS2L a b g i) := by
  have h0 : PsiL a b g (tchartL K 0) = 1 := by
    rw [show (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) 0 = 1 from rfl, map_one]
  have h1 : PsiL a b g (tchartL K 1)
      = invFL a b g * algebraMap _ _ (fwVecAS2L a b g 1) := by
    rw [show (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) 1
      = MvPolynomial.X 0 from rfl, PsiL_X]
    rfl
  have h2 : PsiL a b g (tchartL K 2)
      = invFL a b g * algebraMap _ _ (fwVecAS2L a b g 2) := by
    rw [show (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) 2
      = MvPolynomial.X 1 from rfl, PsiL_X]
    rfl
  have h3 : PsiL a b g (tchartL K 3)
      = invFL a b g * algebraMap _ _ (fwVecAS2L a b g 3) := by
    rw [show (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) 3
      = MvPolynomial.X 2 from rfl, PsiL_X]
    rfl
  have h4 : PsiL a b g (tchartL K 4) = 0 := by
    rw [show (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) 4 = 0 from rfl, map_zero]
  funext i
  fin_cases i
  · show PsiL a b g (tchartL K 0) = invFL a b g * algebraMap _ _ (fwVecAS2L a b g 0)
    rw [h0, invFL_mul a b g]
  · exact h1
  · exact h2
  · exact h3
  · show PsiL a b g (tchartL K 4) = invFL a b g * algebraMap _ _ (fwVecAS2L a b g 4)
    rw [h4, fwVecAS2L_four a b g, map_zero, mul_zero]

end Work.MotV5.ASChart
