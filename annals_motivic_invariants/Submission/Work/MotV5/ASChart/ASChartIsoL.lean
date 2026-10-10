import Mathlib
import Submission.Work.MotK.AwayAlgEquivOfComp
import Submission.Work.MotV5.ASChart.ASChartLocalDefs
import Submission.Work.MotV5.ASChart.PsiL_bwVecAS2L
import Submission.Work.MotV5.ASChart.PhiL_fwVecAS2L
import Submission.Work.MotV5.ASChart.PsiL_sdualAS2L
import Submission.Work.MotV5.ASChart.PhiL_sAS2L_sq
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASChart.ASChartIsoL` — the chart isomorphism of the corrected AS chart (local form)

Assembly of the four value lemmas of `Submission/Work/MotV5/ASChart/` into the isomorphism

  `A[1/FdivAS2L] ≃ₐ[K] A[1/GdivAS2L]`   (`A = K[X₀,X₁,X₂]`)

of the two affine charts of the AS Crauder–Katz link, as in the T-twisted model
(`Submission/Work/MotK/TGen/ChartIso.lean`): the two composites `Ψ ∘ Φ`, `Φ ∘ Ψ` are the identity
on the generators `X_j`, and `Work.MotK.AwayAlgEquivOfComp` upgrades this to the algebra
equivalence.  The descent maps are `PhiLA` (from `PhiL = χ^*`) and `PsiLA` (from `PsiL = f^*`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.MotV5.ASChart

variable {K : Type*} [Field K]

/-! ## §0 A monoid lemma -/

/-- If `x * x` is a unit in a commutative monoid, so is `x`. -/
theorem isUnit_of_mul_self_isUnit {M : Type*} [CommMonoid M] {x : M} (h : IsUnit (x * x)) :
    IsUnit x := by
  obtain ⟨u, hu⟩ := h
  refine ⟨⟨x, ↑u⁻¹ * x, ?_, ?_⟩, rfl⟩
  · calc x * (↑u⁻¹ * x) = ↑u⁻¹ * (x * x) := by ac_rfl
      _ = ↑u⁻¹ * ↑u := by rw [hu]
      _ = 1 := u.inv_mul
  · calc (↑u⁻¹ * x) * x = ↑u⁻¹ * (x * x) := by ac_rfl
      _ = ↑u⁻¹ * ↑u := by rw [hu]
      _ = 1 := u.inv_mul

/-! ## §1 Units of the chart divisors -/

theorem isUnit_alg_linAS2L (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
      (linAS2L a b)) :=
  IsLocalization.Away.isUnit_of_dvd (FdivAS2L a b g)
    ⟨sAS2L a b g * fwVecAS2L a b g 0, by simp only [FdivAS2L]; ring⟩

theorem isUnit_alg_sAS2L (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
      (sAS2L a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (FdivAS2L a b g)
    ⟨linAS2L a b * fwVecAS2L a b g 0, by simp only [FdivAS2L]; ring⟩

theorem isUnit_alg_fwVecAS2L_zero (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
      (fwVecAS2L a b g 0)) :=
  IsLocalization.Away.isUnit_of_dvd (FdivAS2L a b g)
    ⟨linAS2L a b * sAS2L a b g, by simp only [FdivAS2L]; ring⟩

theorem isUnit_alg_GambAS2L (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2L a b g))
      (GambAS2L a b g)) := by
  rw [show GambAS2L a b g = linAS2L a b * sAS2L a b g from rfl, map_mul]
  exact (isUnit_alg_linAS2L a b g).mul (isUnit_alg_sAS2L a b g)

theorem isUnit_alg_cubAS2L (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
      (cubAS2L a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (GdivAS2L a b g)
    ⟨sdualAS2L a b g * bwVecAS2L a b g 4, by simp only [GdivAS2L]; ring⟩

theorem isUnit_alg_sdualAS2L (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
      (sdualAS2L a b g)) :=
  IsLocalization.Away.isUnit_of_dvd (GdivAS2L a b g)
    ⟨cubAS2L a b g * bwVecAS2L a b g 4, by simp only [GdivAS2L]; ring⟩

theorem isUnit_alg_bwVecAS2L_four (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
      (bwVecAS2L a b g 4)) :=
  IsLocalization.Away.isUnit_of_dvd (GdivAS2L a b g)
    ⟨cubAS2L a b g * sdualAS2L a b g, by simp only [GdivAS2L]; ring⟩

theorem isUnit_alg_FambAS2L (a b g : K) :
    IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
      (FambAS2L a b g)) := by
  rw [show FambAS2L a b g = cubAS2L a b g * sdualAS2L a b g from rfl, map_mul]
  exact (isUnit_alg_cubAS2L a b g).mul (isUnit_alg_sdualAS2L a b g)

theorem isUnit_invFL (a b g : K) : IsUnit (invFL a b g) :=
  isUnit_of_dvd_unit ⟨algebraMap _ _ (FdivAS2L a b g), (invFL_spec a b g).symm⟩
    (IsLocalization.Away.isUnit_of_dvd (FdivAS2L a b g) (dvd_mul_right _ _))

theorem isUnit_invGL (a b g : K) : IsUnit (invGL a b g) :=
  isUnit_of_dvd_unit ⟨algebraMap _ _ (GdivAS2L a b g), (invGL_spec a b g).symm⟩
    (IsLocalization.Away.isUnit_of_dvd (GdivAS2L a b g) (dvd_mul_right _ _))

/-! ## §2 `linAS2L` is a constant, hence a unit of both localisations -/

/-- `linAS2L a b` divides `GdivAS2L a b g`. -/
theorem linAS2L_dvd_GdivAS2L (a b g : K) : linAS2L a b ∣ GdivAS2L a b g :=
  ⟨bwVecAS2L a b g 4 * sdualAS2L a b g * bwVecAS2L a b g 4, by
    rw [GdivAS2L, cubAS2L_eq]; ring⟩

/-- The image of a unit under `PhiL` is a unit. -/
theorem isUnit_PhiL_of_isUnit (a b g : K) {x : MvPolynomial (Fin 3) K} (h : IsUnit x) :
    IsUnit (PhiL a b g x) :=
  h.map (PhiL a b g).toRingHom.toMonoidHom

/-- The image of a unit under `PsiL` is a unit. -/
theorem isUnit_PsiL_of_isUnit (a b g : K) {x : MvPolynomial (Fin 3) K} (h : IsUnit x) :
    IsUnit (PsiL a b g x) :=
  h.map (PsiL a b g).toRingHom.toMonoidHom

/-- `PhiL (fwVecAS2L · 0)` is a unit. -/
theorem isUnit_PhiL_fwVec0 (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0) :
    IsUnit (PhiL a b g (fwVecAS2L a b g 0)) := by
  rw [PhiL_fwVecAS2L a b g h5 0,
    show (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) 0 = 1 from rfl, mul_one]
  rw [map_mul, map_pow]
  exact (isUnit_invGL a b g).pow 4 |>.mul
    ((isUnit_alg_cubAS2L a b g).pow 2 |>.mul (isUnit_alg_sdualAS2L a b g))

/-- `PhiL (sAS2L)` is a unit (its square is). -/
theorem isUnit_PhiL_sAS2L (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0) :
    IsUnit (PhiL a b g (sAS2L a b g)) := by
  have hfw : (fun i => PhiL a b g (fwVecAS2L a b g i))
      = fun i => invGL a b g ^ 4 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (GdivAS2L a b g))
          (cubAS2L a b g ^ 2 * sdualAS2L a b g * tchartL K i) :=
    funext fun i => PhiL_fwVecAS2L a b g h5 i
  have h2 := PhiL_sAS2L_sq a b g h5 hfw
  have h3 : PhiL a b g (sAS2L a b g) * PhiL a b g (sAS2L a b g)
      = (invGL a b g ^ 4 * algebraMap (MvPolynomial (Fin 3) K)
          (Localization.Away (GdivAS2L a b g))
          (cubAS2L a b g ^ 2 * sdualAS2L a b g)) ^ 5
        * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2L a b g))
            (sdualAS2L a b g) := by
    rw [← pow_two, h2]
  have hunit : IsUnit (PhiL a b g (sAS2L a b g) * PhiL a b g (sAS2L a b g)) := by
    rw [h3, map_mul, map_pow]
    exact (((isUnit_invGL a b g).pow 4).mul
      ((isUnit_alg_cubAS2L a b g).pow 2 |>.mul (isUnit_alg_sdualAS2L a b g))).pow 5 |>.mul
        (isUnit_alg_sdualAS2L a b g)
  exact isUnit_of_mul_self_isUnit hunit

/-- `PhiL (GambAS2L)` is a unit. -/
theorem isUnit_PhiL_GambAS2L (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) :
    IsUnit (PhiL a b g (GambAS2L a b g)) := by
  rw [show GambAS2L a b g = linAS2L a b * sAS2L a b g from rfl, map_mul]
  exact (isUnit_PhiL_of_isUnit a b g hlin).mul (isUnit_PhiL_sAS2L a b g h5)

/-- `PhiL (FdivAS2L)` is a unit, so `PhiL` descends to the localisation at `FdivAS2L`. -/
theorem isUnit_PhiL_FdivAS2L (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) :
    IsUnit (PhiL a b g (FdivAS2L a b g)) := by
  rw [show FdivAS2L a b g = GambAS2L a b g * fwVecAS2L a b g 0 from rfl, map_mul]
  exact (isUnit_PhiL_GambAS2L a b g h5 hlin).mul (isUnit_PhiL_fwVec0 a b g h5)

/-- `PsiL (bwVecAS2L · 4)` is a unit. -/
theorem isUnit_PsiL_bwVec4 (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0) :
    IsUnit (PsiL a b g (bwVecAS2L a b g 4)) := by
  rw [PsiL_bwVecAS2L a b g h5 4,
    show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 4 = 1 from rfl, mul_one, map_neg]
  exact ((isUnit_invFL a b g).pow 3).mul ((isUnit_alg_GambAS2L a b g).neg)

/-- `PsiL (sdualAS2L)` is a unit. -/
theorem isUnit_PsiL_sdualAS2L (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0) :
    IsUnit (PsiL a b g (sdualAS2L a b g)) := by
  rw [PsiL_sdualAS2L a b g h5, map_pow]
  exact ((isUnit_invFL a b g).pow 5).mul ((isUnit_alg_sAS2L a b g).pow 2)

/-- `PsiL (cubAS2L)` is a unit. -/
theorem isUnit_PsiL_cubAS2L (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) :
    IsUnit (PsiL a b g (cubAS2L a b g)) := by
  rw [cubAS2L_eq a b g, map_mul]
  exact (isUnit_PsiL_of_isUnit a b g hlin).mul (isUnit_PsiL_bwVec4 a b g h5)

/-- `PsiL (FambAS2L)` is a unit. -/
theorem isUnit_PsiL_FambAS2L (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) :
    IsUnit (PsiL a b g (FambAS2L a b g)) := by
  rw [show FambAS2L a b g = cubAS2L a b g * sdualAS2L a b g from rfl, map_mul]
  exact (isUnit_PsiL_cubAS2L a b g h5 hlin).mul (isUnit_PsiL_sdualAS2L a b g h5)

/-- `PsiL (GdivAS2L)` is a unit, so `PsiL` descends to the localisation at `GdivAS2L`. -/
theorem isUnit_PsiL_GdivAS2L (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) :
    IsUnit (PsiL a b g (GdivAS2L a b g)) := by
  rw [show GdivAS2L a b g = FambAS2L a b g * bwVecAS2L a b g 4 from rfl, map_mul]
  exact (isUnit_PsiL_FambAS2L a b g h5 hlin).mul (isUnit_PsiL_bwVec4 a b g h5)

/-! ## §4 The two maps of the localisations -/

/-- The pullback `χ^*` of the inverse chart map, as a `K`-algebra homomorphism of the
localisations. -/
noncomputable def PhiLA (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) :
    Localization.Away (FdivAS2L a b g) →ₐ[K] Localization.Away (GdivAS2L a b g) :=
  IsLocalization.Away.liftAlgHom (FdivAS2L a b g) (isUnit_PhiL_FdivAS2L a b g h5 hlin)

/-- The pullback `f^*` of the forward chart map, as a `K`-algebra homomorphism of the
localisations. -/
noncomputable def PsiLA (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) :
    Localization.Away (GdivAS2L a b g) →ₐ[K] Localization.Away (FdivAS2L a b g) :=
  IsLocalization.Away.liftAlgHom (GdivAS2L a b g) (isUnit_PsiL_GdivAS2L a b g h5 hlin)

theorem PhiLA_algebraMap (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) (x : MvPolynomial (Fin 3) K) :
    PhiLA a b g h5 hlin (algebraMap _ _ x) = PhiL a b g x :=
  IsLocalization.Away.lift_eq (FdivAS2L a b g) (isUnit_PhiL_FdivAS2L a b g h5 hlin) x

theorem PsiLA_algebraMap (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) (x : MvPolynomial (Fin 3) K) :
    PsiLA a b g h5 hlin (algebraMap _ _ x) = PsiL a b g x :=
  IsLocalization.Away.lift_eq (GdivAS2L a b g) (isUnit_PsiL_GdivAS2L a b g h5 hlin) x

/-! ## §5 The two composites on the generators -/

/-- **The composite `Ψ ∘ Φ` is the identity on the generators.** -/
theorem PsiLA_PhiLA_X (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) (j : Fin 3) :
    PsiLA a b g h5 hlin (PhiLA a b g h5 hlin (algebraMap _ _
        (MvPolynomial.X j : MvPolynomial (Fin 3) K)))
      = algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
  rw [PhiLA_algebraMap a b g h5 hlin, PhiL_X]
  have hpsi : psiGL a b g j = invGL a b g * algebraMap (MvPolynomial (Fin 3) K)
      (Localization.Away (GdivAS2L a b g)) (bwVecAS2L a b g (ch3 j)) := psiGL_ch3 a b g j
  rw [hpsi, map_mul, PsiLA_algebraMap a b g h5 hlin]
  have hA : PsiLA a b g h5 hlin (invGL a b g) * PsiL a b g (bwVecAS2L a b g 4) = 1 := by
    have h3 : PsiLA a b g h5 hlin (invGL a b g)
        * PsiLA a b g h5 hlin (algebraMap _ _ (GdivAS2L a b g))
        = PsiLA a b g h5 hlin (algebraMap _ _ (FambAS2L a b g)) := by
      rw [← map_mul, invGL_spec]
    have hsplit : PsiL a b g (GdivAS2L a b g)
        = PsiL a b g (FambAS2L a b g) * PsiL a b g (bwVecAS2L a b g 4) := by
      rw [show GdivAS2L a b g = FambAS2L a b g * bwVecAS2L a b g 4 from rfl, map_mul]
    rw [PsiLA_algebraMap a b g h5 hlin, PsiLA_algebraMap a b g h5 hlin, hsplit] at h3
    refine (isUnit_PsiL_FambAS2L a b g h5 hlin).mul_right_cancel ?_
    rw [one_mul, mul_assoc,
      mul_comm (PsiL a b g (bwVecAS2L a b g 4)) (PsiL a b g (FambAS2L a b g))]
    exact h3
  have hC : algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K)
        * PsiL a b g (bwVecAS2L a b g 4)
      = PsiL a b g (bwVecAS2L a b g (ch3 j)) := by
    rw [PsiL_bwVecAS2L a b g h5 4, PsiL_bwVecAS2L a b g h5 (ch3 j),
      show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K) 4 = 1 from rfl, mul_one,
      chart3_ch3 j]
    simp only [map_neg, map_mul]
    first | refl_ring1 | ring
  have hfinal : PsiLA a b g h5 hlin (invGL a b g) * PsiL a b g (bwVecAS2L a b g (ch3 j))
      = (PsiLA a b g h5 hlin (invGL a b g) * PsiL a b g (bwVecAS2L a b g 4))
          * algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
    rw [← hC]
    first | refl_ring1 | ring
  rw [hfinal, hA, one_mul]

/-- **The composite `Φ ∘ Ψ` is the identity on the generators.** -/
theorem PhiLA_PsiLA_X (a b g : K) (h5 : (5 : MvPolynomial (Fin 3) K) = 0)
    (hlin : IsUnit (linAS2L a b)) (j : Fin 3) :
    PhiLA a b g h5 hlin (PsiLA a b g h5 hlin (algebraMap _ _
        (MvPolynomial.X j : MvPolynomial (Fin 3) K)))
      = algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
  rw [PsiLA_algebraMap a b g h5 hlin, PsiL_X]
  have hphi : phiFL a b g j = invFL a b g * algebraMap (MvPolynomial (Fin 3) K)
      (Localization.Away (FdivAS2L a b g)) (fwVecAS2L a b g (ch3 j)) := phiFL_ch3 a b g j
  rw [hphi, map_mul, PhiLA_algebraMap a b g h5 hlin]
  have hA : PhiLA a b g h5 hlin (invFL a b g) * PhiL a b g (fwVecAS2L a b g 0) = 1 := by
    have h3 : PhiLA a b g h5 hlin (invFL a b g)
        * PhiLA a b g h5 hlin (algebraMap _ _ (FdivAS2L a b g))
        = PhiLA a b g h5 hlin (algebraMap _ _ (GambAS2L a b g)) := by
      rw [← map_mul, invFL_spec]
    have hsplit : PhiL a b g (FdivAS2L a b g)
        = PhiL a b g (GambAS2L a b g) * PhiL a b g (fwVecAS2L a b g 0) := by
      rw [show FdivAS2L a b g = GambAS2L a b g * fwVecAS2L a b g 0 from rfl, map_mul]
    rw [PhiLA_algebraMap a b g h5 hlin, PhiLA_algebraMap a b g h5 hlin, hsplit] at h3
    refine (isUnit_PhiL_GambAS2L a b g h5 hlin).mul_right_cancel ?_
    rw [one_mul, mul_assoc,
      mul_comm (PhiL a b g (fwVecAS2L a b g 0)) (PhiL a b g (GambAS2L a b g))]
    exact h3
  have hC : algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K)
        * PhiL a b g (fwVecAS2L a b g 0)
      = PhiL a b g (fwVecAS2L a b g (ch3 j)) := by
    rw [PhiL_fwVecAS2L a b g h5 0, PhiL_fwVecAS2L a b g h5 (ch3 j),
      show (tchartL K : Fin 5 → MvPolynomial (Fin 3) K) 0 = 1 from rfl, mul_one,
      tchartL_ch3 j]
    simp only [map_mul]
    first | refl_ring1 | ring
  have hfinal : PhiLA a b g h5 hlin (invFL a b g) * PhiL a b g (fwVecAS2L a b g (ch3 j))
      = (PhiLA a b g h5 hlin (invFL a b g) * PhiL a b g (fwVecAS2L a b g 0))
          * algebraMap _ _ (MvPolynomial.X j : MvPolynomial (Fin 3) K) := by
    rw [← hC]
    first | refl_ring1 | ring
  rw [hfinal, hA, one_mul]

end Work.MotV5.ASChart
