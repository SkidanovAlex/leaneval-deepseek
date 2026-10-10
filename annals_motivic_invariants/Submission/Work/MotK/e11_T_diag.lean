import Submission.Work.MotK.E11TDiagAux
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.e11_T_diag` — the `T_diag` field for the `E₁₁` Klein model

The main theorem, assembled from the polynomial identities in `E11TDiagAux`.
-/

set_option maxHeartbeats 4000000

namespace Work.MotK

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

/-! ## §1 Abstract function-field computations (variables, no unfolding) -/

/-- The cleared `x`-formula: if `u = NX5/(5·D5²)` and `NX5, D5, Y5` are the scaled
intermediates of the translation, then `u·(5·D5²) = NX5`. -/
lemma e11_raw_x_clear (F : Type) [Field F] (X Y A B NX5 D5 Y5 : F)
    (hD : X - A ≠ 0)
    (hD5 : D5 = 5 * (X - A)) (hY5 : Y5 = 5 * (Y - B))
    (hNX5 : NX5 = 5 * Y5 ^(2:ℕ) - 50 * Y5 * D5 + (55 - 5 * X - 5 * A) * D5 ^(2:ℕ)) :
    (((Y - B) / (X - A)) ^(2:ℕ) - 10 * ((Y - B) / (X - A)) + 11 - X - A) * (5 * D5 ^(2:ℕ)) = NX5 := by
  rw [hNX5, hY5, hD5]
  field_simp [hD]
  refl_ring1

/-- The cleared `y`-formula. -/
lemma e11_raw_y_clear (F : Type) [Field F] (X Y A B u NX5 NY5 D5 Y5 : F)
    (h5 : (5 : F) ≠ 0) (hD5ne : D5 ≠ 0) (hD : X - A ≠ 0)
    (hD5 : D5 = 5 * (X - A)) (hY5 : Y5 = 5 * (Y - B))
    (hu : u = NX5 / (5 * D5 ^(2:ℕ)))
    (hNY5 : NY5 = -(Y5) * (NX5 - 5 * X * D5 ^(2:ℕ)) - 5 * Y * D5 ^(3:ℕ) + 10 * NX5 * D5 + 55 * D5 ^(3:ℕ)) :
    (-(((Y - B) / (X - A)) * (u - X) + Y) + 10 * u + 11) * (5 * D5 ^(3:ℕ)) = NY5 := by
  rw [hNY5, hY5, hu, hD5]
  field_simp [hD, h5]
  refl_ring1

/-- The cleared `κ₀`-formula. -/
lemma e11_sigma_clear_0 (F : Type) [Field F] (u NX5 D5 : F)
    (h5 : (5 : F) ≠ 0) (hD5ne : D5 ≠ 0) (hu : u = NX5 / (5 * D5 ^(2:ℕ))) :
    (121 + 55 * u + 5 * u ^(2:ℕ)) * (5 * D5 ^(4:ℕ)) = 605 * D5 ^(4:ℕ) + 55 * NX5 * D5 ^(2:ℕ) + NX5 ^(2:ℕ) := by
  rw [hu]
  field_simp [h5, hD5ne]
  refl_ring1

/-- The cleared `κ₁`-formula. -/
lemma e11_sigma_clear_1 (F : Type) [Field F] (u v NX5 NY5 D5 : F)
    (h5 : (5 : F) ≠ 0) (hD5ne : D5 ≠ 0)
    (hu : u = NX5 / (5 * D5 ^(2:ℕ))) (hv : v = NY5 / (5 * D5 ^(3:ℕ))) :
    (-55 * u + 11 * v - 6 * u ^(2:ℕ) + u * v) * (25 * D5 ^(6:ℕ))
      = (25*(0))*D5^(6:ℕ) + (5*(-55))*NX5*D5^(4:ℕ) + (5*(11))*NY5*D5^(3:ℕ)
        + (-6)*NX5^(2:ℕ)*D5^(2:ℕ) + (1)*NX5*NY5*D5 := by
  rw [hu, hv]
  field_simp [h5, hD5ne]
  refl_ring1

/-- The cleared `κ₂`-formula. -/
lemma e11_sigma_clear_2 (F : Type) [Field F] (u v NX5 NY5 D5 : F)
    (h5 : (5 : F) ≠ 0) (hD5ne : D5 ≠ 0)
    (hu : u = NX5 / (5 * D5 ^(2:ℕ))) (hv : v = NY5 / (5 * D5 ^(3:ℕ))) :
    (-121 - 33 * u - 7 * u ^(2:ℕ) + u * v) * (25 * D5 ^(6:ℕ))
      = (25*(-121))*D5^(6:ℕ) + (5*(-33))*NX5*D5^(4:ℕ) + (5*(0))*NY5*D5^(3:ℕ)
        + (-7)*NX5^(2:ℕ)*D5^(2:ℕ) + (1)*NX5*NY5*D5 := by
  rw [hu, hv]
  field_simp [h5, hD5ne]
  refl_ring1

/-- The cleared `κ₃`-formula. -/
lemma e11_sigma_clear_3 (F : Type) [Field F] (u v NX5 NY5 D5 : F)
    (h5 : (5 : F) ≠ 0) (hD5ne : D5 ≠ 0)
    (hu : u = NX5 / (5 * D5 ^(2:ℕ))) (hv : v = NY5 / (5 * D5 ^(3:ℕ))) :
    (-121 - 22 * u + 3 * u ^(2:ℕ) - u * v) * (25 * D5 ^(6:ℕ))
      = (25*(-121))*D5^(6:ℕ) + (5*(-22))*NX5*D5^(4:ℕ) + (5*(0))*NY5*D5^(3:ℕ)
        + (3)*NX5^(2:ℕ)*D5^(2:ℕ) + (-1)*NX5*NY5*D5 := by
  rw [hu, hv]
  field_simp [h5, hD5ne]
  refl_ring1

/-- The cleared `κ₄`-formula. -/
lemma e11_sigma_clear_4 (F : Type) [Field F] (u v NX5 NY5 D5 : F)
    (h5 : (5 : F) ≠ 0) (hD5ne : D5 ≠ 0)
    (hu : u = NX5 / (5 * D5 ^(2:ℕ))) (hv : v = NY5 / (5 * D5 ^(3:ℕ))) :
    (121 + 66 * u - 11 * v + 4 * u ^(2:ℕ) - u * v) * (25 * D5 ^(6:ℕ))
      = (25*(121))*D5^(6:ℕ) + (5*(66))*NX5*D5^(4:ℕ) + (5*(-11))*NY5*D5^(3:ℕ)
        + (4)*NX5^(2:ℕ)*D5^(2:ℕ) + (-1)*NX5*NY5*D5 := by
  rw [hu, hv]
  field_simp [h5, hD5ne]
  refl_ring1

theorem e11_T_diag (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] (ζ : L)
    (hζ : IsPrimitiveRoot ζ 5) (h5 : (5 : L) ≠ 0) (h11 : (11 : L) ≠ 0) :
    ∃ σ : WeierstrassCurve.Affine.FunctionField ((Work.MotK.kleinDataCandidate 𝕜).E.baseChange L) ≃ₐ[L]
        WeierstrassCurve.Affine.FunctionField ((Work.MotK.kleinDataCandidate 𝕜).E.baseChange L),
      ∀ i : Fin 5,
        σ (Work.MotV.kleinCoord (Work.MotK.kleinDataCandidate 𝕜) L i /
            Work.MotV.kleinCoord (Work.MotK.kleinDataCandidate 𝕜) L 0) =
          algebraMap L (WeierstrassCurve.Affine.FunctionField
              ((Work.MotK.kleinDataCandidate 𝕜).E.baseChange L)) ζ ^ (i : ℕ) *
            (Work.MotV.kleinCoord (Work.MotK.kleinDataCandidate 𝕜) L i /
              Work.MotV.kleinCoord (Work.MotK.kleinDataCandidate 𝕜) L 0) := by
  classical
  have hPhiL : ζ ^(4:ℕ) + ζ ^(3:ℕ) + ζ ^(2:ℕ) + ζ + 1 = 0 := e11_zeta_Phi L ζ hζ
  have h11k : (11 : 𝕜) ≠ 0 := by
    intro h
    apply h11
    rw [← map_ofNat (algebraMap 𝕜 L) 11, h, map_zero]
  haveI hE11 : (E11 𝕜).IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    have hΔ : (E11 𝕜).Δ = -(161051 : 𝕜) := by
      simp only [E11, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      norm_num
    rw [hΔ]
    exact neg_ne_zero.mpr (by
      have h : (161051 : 𝕜) = (11 : 𝕜) ^(5:ℕ) := by norm_num
      rw [h]; exact pow_ne_zero 5 h11k)
  haveI hKe : ((kleinDataCandidate 𝕜).E.baseChange L).IsElliptic := by
    change ((E11 𝕜).map (algebraMap 𝕜 L)).IsElliptic
    infer_instance
  set a : L := e11a L ζ with ha_def
  set b : L := e11b L ζ with hb_def
  have hQ : b ^(2:ℕ) - (10 * a + 11) * b - a ^(3:ℕ) + 11 * a ^(2:ℕ) = 0 := by
    rw [ha_def, hb_def]; exact e11_pt_eq L ζ hζ h5
  have hEq : WeierstrassCurve.Affine.Equation ((kleinDataCandidate 𝕜).E.baseChange L) a b := by
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [e11_ke_baseChange_a₁ 𝕜 L, e11_ke_baseChange_a₂ 𝕜 L, e11_ke_baseChange_a₃ 𝕜 L,
      e11_ke_baseChange_a₄ 𝕜 L, e11_ke_baseChange_a₆ 𝕜 L]
    have h10 : algebraMap 𝕜 L (-10 : 𝕜) = (-10 : L) := by rw [map_neg, map_ofNat]
    have h11' : algebraMap 𝕜 L (-11 : 𝕜) = (-11 : L) := by rw [map_neg, map_ofNat]
    rw [h10, h11']
    simp only [map_zero, mul_zero, add_zero]
    linear_combination (norm := refl_ring1) hQ
  have hns : WeierstrassCurve.Affine.Nonsingular ((kleinDataCandidate 𝕜).E.baseChange L) a b :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular).mp hEq
  refine ⟨Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
      (WeierstrassCurve.Affine.Point.some a b hns), ?_⟩
  intro i
  set x : e11_keFF 𝕜 L := e11_keX 𝕜 L with hx
  set y : e11_keFF 𝕜 L := e11_keY 𝕜 L with hy
  set z : e11_keFF 𝕜 L := algebraMap L (e11_keFF 𝕜 L) ζ with hz
  have h5F : (5 : e11_keFF 𝕜 L) ≠ 0 := by
    rw [show (5 : e11_keFF 𝕜 L) = algebraMap L (e11_keFF 𝕜 L) 5 from (map_ofNat _ 5).symm]
    intro h
    exact h5 ((algebraMap L (e11_keFF 𝕜 L)).injective (by rw [h, map_zero]))
  have h25 : (25 : e11_keFF 𝕜 L) ≠ 0 := by
    have h : (25 : e11_keFF 𝕜 L) = 5 * 5 := by norm_num
    rw [h]; exact mul_ne_zero h5F h5F
  have hW : y ^(2:ℕ) - 10 * x * y - 11 * y - x ^(3:ℕ) + 11 * x ^(2:ℕ) = 0 := by
    rw [hx, hy]; exact e11_ke_relation 𝕜 L
  have hPhi : z ^(4:ℕ) + z ^(3:ℕ) + z ^(2:ℕ) + z + 1 = 0 := by
    rw [hz]
    have h' := congrArg (algebraMap L (e11_keFF 𝕜 L)) hPhiL
    simpa using h'
  have hk0 : Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0
      = (121 : e11_keFF 𝕜 L) + 55 * x + 5 * x ^(2:ℕ) := by
    rw [hx]; exact e11_ke_kC_0 𝕜 L
  have hκ0ne : Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0 ≠ 0 :=
    e11_coord0_ne_candidate 𝕜 h11k L
  have hA5 : pA5 (e11_keFF 𝕜 L) z = 5 * algebraMap L (e11_keFF 𝕜 L) a := by
    rw [hz, pA5, ha_def]
    simp only [e11a, map_div₀, map_mul, map_add, map_sub, map_pow, map_ofNat]
    field_simp
  have hB5 : pB5 (e11_keFF 𝕜 L) z = 5 * algebraMap L (e11_keFF 𝕜 L) b := by
    rw [hz, pB5, hb_def]
    simp only [e11b, map_div₀, map_mul, map_add, map_sub, map_pow, map_ofNat]
    field_simp
  have hxM : x = Work.MotC2.genX ((kleinDataCandidate 𝕜).E.baseChange L) := by
    rw [hx]; exact e11_MotV_genX_eq_MotC2_genX _
  have hyM : y = Work.MotC2.genY ((kleinDataCandidate 𝕜).E.baseChange L) := by
    rw [hy]; exact e11_MotV_genY_eq_MotC2_genY _
  have hDne : x - algebraMap L (e11_keFF 𝕜 L) a ≠ 0 := by
    rw [hxM]; exact sub_ne_zero.mpr (Work.MotC2.genX_ne_algebraMap _ a)
  have hD5eq : pD5 (e11_keFF 𝕜 L) x z = 5 * (x - algebraMap L (e11_keFF 𝕜 L) a) := by
    rw [pD5, hA5]; ring
  have hY5eq : pY5 (e11_keFF 𝕜 L) y z = 5 * (y - algebraMap L (e11_keFF 𝕜 L) b) := by
    rw [pY5, hB5]; ring
  have hD5ne : pD5 (e11_keFF 𝕜 L) x z ≠ 0 := by rw [hD5eq]; exact mul_ne_zero h5F hDne
  have hNX5eq : pNX5 (e11_keFF 𝕜 L) x y z
      = 5 * (pY5 (e11_keFF 𝕜 L) y z) ^(2:ℕ) - 50 * (pY5 (e11_keFF 𝕜 L) y z)
          * (pD5 (e11_keFF 𝕜 L) x z) + (55 - 5 * x - 5 * algebraMap L (e11_keFF 𝕜 L) a)
          * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ) := by
    rw [pNX5, hA5]
  have hbase_a₁ : (Work.MotC2.baseE ((kleinDataCandidate 𝕜).E.baseChange L)).a₁
      = (-10 : e11_keFF 𝕜 L) := by
    rw [Work.MotC2.baseE, WeierstrassCurve.map_a₁, e11_ke_baseChange_a₁]
    rw [← IsScalarTower.algebraMap_apply 𝕜 L (e11_keFF 𝕜 L)]
    simp only [map_neg, map_ofNat]
  have hbase_a₂ : (Work.MotC2.baseE ((kleinDataCandidate 𝕜).E.baseChange L)).a₂
      = (-11 : e11_keFF 𝕜 L) := by
    rw [Work.MotC2.baseE, WeierstrassCurve.map_a₂, e11_ke_baseChange_a₂]
    rw [← IsScalarTower.algebraMap_apply 𝕜 L (e11_keFF 𝕜 L)]
    simp only [map_neg, map_ofNat]
  have hbase_a₃ : (Work.MotC2.baseE ((kleinDataCandidate 𝕜).E.baseChange L)).a₃
      = (-11 : e11_keFF 𝕜 L) := by
    rw [Work.MotC2.baseE, WeierstrassCurve.map_a₃, e11_ke_baseChange_a₃]
    rw [← IsScalarTower.algebraMap_apply 𝕜 L (e11_keFF 𝕜 L)]
    simp only [map_neg, map_ofNat]
  have hraw_x : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)) x
      = ((y - algebraMap L (e11_keFF 𝕜 L) b) / (x - algebraMap L (e11_keFF 𝕜 L) a)) ^(2:ℕ)
        - 10 * ((y - algebraMap L (e11_keFF 𝕜 L) b) / (x - algebraMap L (e11_keFF 𝕜 L) a))
        + 11 - x - algebraMap L (e11_keFF 𝕜 L) a := by
    rw [hxM, hyM, Work.MotC2.transAlgEquiv_genX _ hns, WeierstrassCurve.Affine.addX,
      hbase_a₁, hbase_a₂, WeierstrassCurve.Affine.slope,
      if_neg (Work.MotC2.genX_ne_algebraMap ((kleinDataCandidate 𝕜).E.baseChange L) a)]
    refl_ring1
  have hraw_y : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)) y
      = -(((y - algebraMap L (e11_keFF 𝕜 L) b) / (x - algebraMap L (e11_keFF 𝕜 L) a))
            * ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
                (WeierstrassCurve.Affine.Point.some a b hns)) x - x) + y)
        + 10 * ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
                (WeierstrassCurve.Affine.Point.some a b hns)) x) + 11 := by
    rw [hxM, hyM, Work.MotC2.transAlgEquiv_genY _ hns, Work.MotC2.transAlgEquiv_genX _ hns,
      WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX,
      hbase_a₁, hbase_a₂, hbase_a₃, WeierstrassCurve.Affine.slope,
      if_neg (Work.MotC2.genX_ne_algebraMap ((kleinDataCandidate 𝕜).E.baseChange L) a)]
    refl_ring1
  have hσx_clear : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)) x
        * (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ)) = pNX5 (e11_keFF 𝕜 L) x y z := by
    rw [hraw_x]
    exact e11_raw_x_clear (e11_keFF 𝕜 L) x y (algebraMap L (e11_keFF 𝕜 L) a)
      (algebraMap L (e11_keFF 𝕜 L) b) (pNX5 (e11_keFF 𝕜 L) x y z) (pD5 (e11_keFF 𝕜 L) x z)
      (pY5 (e11_keFF 𝕜 L) y z) hDne hD5eq hY5eq hNX5eq
  have hσx : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)) x
      = pNX5 (e11_keFF 𝕜 L) x y z / (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ)) := by
    rw [eq_div_iff (mul_ne_zero h5F (pow_ne_zero 2 hD5ne))]
    exact hσx_clear
  have hσy_clear : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)) y
        * (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(3:ℕ)) = pNY5 (e11_keFF 𝕜 L) x y z := by
    rw [hraw_y, hσx]
    exact e11_raw_y_clear (e11_keFF 𝕜 L) x y (algebraMap L (e11_keFF 𝕜 L) a)
      (algebraMap L (e11_keFF 𝕜 L) b)
      (pNX5 (e11_keFF 𝕜 L) x y z / (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ)))
      (pNX5 (e11_keFF 𝕜 L) x y z) (pNY5 (e11_keFF 𝕜 L) x y z) (pD5 (e11_keFF 𝕜 L) x z)
      (pY5 (e11_keFF 𝕜 L) y z) h5F hD5ne hDne hD5eq hY5eq rfl (by rw [pNY5])
  have hσy : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)) y
      = pNY5 (e11_keFF 𝕜 L) x y z / (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(3:ℕ)) := by
    rw [eq_div_iff (mul_ne_zero h5F (pow_ne_zero 3 hD5ne))]
    exact hσy_clear
  have hσ0_clear : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns))
        (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0)
        * (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(4:ℕ)) = pB05 (e11_keFF 𝕜 L) x y z := by
    rw [hk0]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    exact e11_sigma_clear_0 (e11_keFF 𝕜 L)
      ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)) x)
      (pNX5 (e11_keFF 𝕜 L) x y z) (pD5 (e11_keFF 𝕜 L) x z) h5F hD5ne hσx
  have compose : ∀ (i : Fin 5) (A5i : e11_keFF 𝕜 L),
      (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i)
          * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ)) = A5i →
      A5i * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0
          - 5 * z ^ (i : ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i
              * pB05 (e11_keFF 𝕜 L) x y z * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ) = 0 →
      (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i /
            Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0)
        = z ^ (i : ℕ) * (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i /
            Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0) := by
    intro i A5i hσi hpoly
    have hden : (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ)) ≠ 0 :=
      mul_ne_zero h25 (pow_ne_zero 6 hD5ne)
    have hkey : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i)
          * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0
        = z ^ (i : ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i
          * (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
              (WeierstrassCurve.Affine.Point.some a b hns))
              (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0) := by
      apply mul_right_cancel₀ hden
      have hb : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
            (WeierstrassCurve.Affine.Point.some a b hns))
            (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0)
            * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))
          = pB05 (e11_keFF 𝕜 L) x y z * (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ)) := by
        rw [show (25 : e11_keFF 𝕜 L) * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ)
              = (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(4:ℕ)) * (5 * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ))
            from by ring]
        rw [← mul_assoc, hσ0_clear]
      rw [show ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
              (WeierstrassCurve.Affine.Point.some a b hns))
              (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i)
              * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0)
              * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))
            = ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
              (WeierstrassCurve.Affine.Point.some a b hns))
              (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i)
              * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ)))
              * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0 from by ring,
          hσi]
      rw [show (z ^ (i : ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i
              * (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
                (WeierstrassCurve.Affine.Point.some a b hns))
                (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0))
              * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))
            = z ^ (i : ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i
              * ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
                (WeierstrassCurve.Affine.Point.some a b hns))
                (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0)
                * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))) from by ring,
          hb]
      linear_combination (norm := refl_ring1) hpoly
    rw [map_div₀]
    have hσκ0ne : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0) ≠ 0 := by
      intro h
      exact hκ0ne ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
        (WeierstrassCurve.Affine.Point.some a b hns)).injective (by rw [h, map_zero]))
    rw [show z ^ (i : ℕ) * (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i /
            Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0)
          = z ^ (i : ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i /
            Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0 from by ring]
    rw [div_eq_div_iff hσκ0ne hκ0ne]
    exact hkey
  have hi5 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    fin_cases i <;> simp
  rcases hi5 with h | h | h | h | h
  · rw [h]
    rw [div_self hκ0ne, map_one]
    simp
  · rw [h]
    have hk1 : Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 1
        = -55 * x + 11 * y - 6 * x ^(2:ℕ) + x * y := by
      rw [hx, hy]; exact e11_ke_kC_1 𝕜 L
    have hσ1 : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 1)
          * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))
        = (25*(0))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(-55))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(11))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (-6)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z) := by
      rw [hk1]
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
      exact e11_sigma_clear_1 (e11_keFF 𝕜 L)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) x)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) y)
        (pNX5 (e11_keFF 𝕜 L) x y z) (pNY5 (e11_keFF 𝕜 L) x y z) (pD5 (e11_keFF 𝕜 L) x z)
        h5F hD5ne hσx hσy
    have hpoly1 : ((25*(0))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(-55))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(11))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (-6)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z))
          * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0
        - 5 * z ^(1:ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 1
            * (pB05 (e11_keFF 𝕜 L) x y z) * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ) = 0 := by
      have h := e11_poly_ident_1 (e11_keFF 𝕜 L) x y z hW hPhi
      rw [← hk0, ← hk1] at h
      exact h
    exact compose 1 _ hσ1 hpoly1
  · rw [h]
    have hk2 : Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 2
        = -121 - 33 * x - 7 * x ^(2:ℕ) + x * y := by
      rw [hx, hy]; exact e11_ke_kC_2 𝕜 L
    have hσ2 : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 2)
          * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))
        = (25*(-121))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(-33))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(0))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (-7)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z) := by
      rw [hk2]
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
      exact e11_sigma_clear_2 (e11_keFF 𝕜 L)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) x)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) y)
        (pNX5 (e11_keFF 𝕜 L) x y z) (pNY5 (e11_keFF 𝕜 L) x y z) (pD5 (e11_keFF 𝕜 L) x z)
        h5F hD5ne hσx hσy
    have hpoly2 : ((25*(-121))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(-33))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(0))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (-7)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z))
          * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0
        - 5 * z ^(2:ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 2
            * (pB05 (e11_keFF 𝕜 L) x y z) * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ) = 0 := by
      have h := e11_poly_ident_2 (e11_keFF 𝕜 L) x y z hW hPhi
      rw [← hk0, ← hk2] at h
      exact h
    exact compose 2 _ hσ2 hpoly2
  · rw [h]
    have hk3 : Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 3
        = -121 - 22 * x + 3 * x ^(2:ℕ) - x * y := by
      rw [hx, hy]; exact e11_ke_kC_3 𝕜 L
    have hσ3 : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 3)
          * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))
        = (25*(-121))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(-22))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(0))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (3)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (-1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z) := by
      rw [hk3]
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
      exact e11_sigma_clear_3 (e11_keFF 𝕜 L)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) x)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) y)
        (pNX5 (e11_keFF 𝕜 L) x y z) (pNY5 (e11_keFF 𝕜 L) x y z) (pD5 (e11_keFF 𝕜 L) x z)
        h5F hD5ne hσx hσy
    have hpoly3 : ((25*(-121))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(-22))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(0))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (3)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (-1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z))
          * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0
        - 5 * z ^(3:ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 3
            * (pB05 (e11_keFF 𝕜 L) x y z) * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ) = 0 := by
      have h := e11_poly_ident_3 (e11_keFF 𝕜 L) x y z hW hPhi
      rw [← hk0, ← hk3] at h
      exact h
    exact compose 3 _ hσ3 hpoly3
  · rw [h]
    have hk4 : Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 4
        = 121 + 66 * x - 11 * y + 4 * x ^(2:ℕ) - x * y := by
      rw [hx, hy]; exact e11_ke_kC_4 𝕜 L
    have hσ4 : (Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns))
          (Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 4)
          * (25 * (pD5 (e11_keFF 𝕜 L) x z) ^(6:ℕ))
        = (25*(121))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(66))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(-11))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (4)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (-1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z) := by
      rw [hk4]
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]
      exact e11_sigma_clear_4 (e11_keFF 𝕜 L)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) x)
        ((Work.MotC2.transAlgEquiv ((kleinDataCandidate 𝕜).E.baseChange L)
          (WeierstrassCurve.Affine.Point.some a b hns)) y)
        (pNX5 (e11_keFF 𝕜 L) x y z) (pNY5 (e11_keFF 𝕜 L) x y z) (pD5 (e11_keFF 𝕜 L) x z)
        h5F hD5ne hσx hσy
    have hpoly4 : ((25*(121))*(pD5 (e11_keFF 𝕜 L) x z)^(6:ℕ) + (5*(66))*(pNX5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(4:ℕ)
          + (5*(-11))*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z)^(3:ℕ)
          + (4)*(pNX5 (e11_keFF 𝕜 L) x y z)^(2:ℕ)*(pD5 (e11_keFF 𝕜 L) x z)^(2:ℕ)
          + (-1)*(pNX5 (e11_keFF 𝕜 L) x y z)*(pNY5 (e11_keFF 𝕜 L) x y z)*(pD5 (e11_keFF 𝕜 L) x z))
          * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0
        - 5 * z ^(4:ℕ) * Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 4
            * (pB05 (e11_keFF 𝕜 L) x y z) * (pD5 (e11_keFF 𝕜 L) x z) ^(2:ℕ) = 0 := by
      have h := e11_poly_ident_4 (e11_keFF 𝕜 L) x y z hW hPhi
      rw [← hk0, ← hk4] at h
      exact h
    exact compose 4 _ hσ4 hpoly4

end

end Work.MotK
