import Mathlib
import Submission.Work.KT.Fund.Kappa

/-!
# `Work.KT.FP.disc_unit_homotopic_const`

For a compact Hausdorff space `X`, every unit matrix `G` over `C(X × D, ℂ)` (with `D` the closed
unit disc of `ℂ`) restricts on the boundary `X × S¹` to a matrix which is homotopic, through unit
matrices over `C((X × S¹) × [0,1], ℂ)`, to the pull-back of a unit matrix `M` over `C(X, ℂ)`.

The homotopy is the radial contraction `((x,z),t) ↦ (x, t·z)`: at `t = 1` it is the inclusion of
the boundary `X × S¹ ↪ X × D`, and at `t = 0` it is the constant section `x ↦ (x,0)`.  The matrix
`M` is the evaluation of `G` on the zero section (a unit, since evaluation at `0` is a unital ring
homomorphism).  Nothing here is deep — it is the triviality of `K¹` of a contractible space, at the
level of the clutching unit of `Work.KT.Fund.kappa`.
-/

namespace Work.KT.FP

set_option linter.unusedSectionVars false

noncomputable section

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-! ## The radial contraction of the disc onto its centre -/

/-- `t·z` lies in the closed unit disc, for `t ∈ [0,1]` and `z` of norm `1`. -/
lemma mem_ball_smul_sph (r : unitInterval) (v : Sph ℂ) :
    (r : ℝ) • (v : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Fund.norm_coe_sph v, mul_one,
    Real.norm_eq_abs, abs_of_nonneg r.2.1]
  exact r.2.2

/-- The contraction `((x,z),t) ↦ (x, t·z)` of `X × S¹ × [0,1]` into `X × D`. -/
def discUnitCm : C((X × Sph ℂ) × unitInterval, X × Ball ℂ) where
  toFun p := (p.1.1, ⟨((p.2 : unitInterval) : ℝ) • ((p.1.2 : Sph ℂ) : ℂ),
    mem_ball_smul_sph p.2 p.1.2⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_fst
    · apply Continuous.subtype_mk
      show Continuous (fun p : (X × Sph ℂ) × unitInterval =>
        ((p.2 : unitInterval) : ℝ) • ((p.1.2 : Sph ℂ) : ℂ))
      fun_prop

@[simp] lemma discUnitCm_apply_fst (p : (X × Sph ℂ) × unitInterval) :
    ((discUnitCm X p).1 : X) = p.1.1 := rfl

@[simp] lemma discUnitCm_apply_snd (p : (X × Sph ℂ) × unitInterval) :
    ((discUnitCm X p).2 : ℂ) = ((p.2 : unitInterval) : ℝ) • ((p.1.2 : Sph ℂ) : ℂ) := rfl

/-- The zero section `x ↦ (x, 0)` of the disc. -/
def discUnitZero : C(X, X × Ball ℂ) where
  toFun x := (x, ⟨0, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩)
  continuous_toFun := by fun_prop

@[simp] lemma discUnitZero_apply_fst (x : X) : ((discUnitZero X x).1 : X) = x := rfl

@[simp] lemma discUnitZero_apply_snd (x : X) : ((discUnitZero X x).2 : ℂ) = 0 := rfl

/-- Pull-back of functions on the disc along the contraction `discUnitCm`. -/
def discUnitRH : C(X × Ball ℂ, ℂ) →+* C((X × Sph ℂ) × unitInterval, ℂ) :=
  (pullAlg (discUnitCm X)).toRingHom

@[simp] lemma discUnitRH_apply (g : C(X × Ball ℂ, ℂ)) (p : (X × Sph ℂ) × unitInterval) :
    discUnitRH X g p = g (discUnitCm X p) := rfl

/-- Evaluation of functions on the disc on the zero section. -/
def discUnitEv0 : C(X × Ball ℂ, ℂ) →+* C(X, ℂ) :=
  (pullAlg (discUnitZero X)).toRingHom

@[simp] lemma discUnitEv0_apply (g : C(X × Ball ℂ, ℂ)) (x : X) :
    discUnitEv0 X g x = g (discUnitZero X x) := rfl

/-! ## The homotopy -/

theorem disc_unit_homotopic_const (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (G : (Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ))ˣ) :
    ∃ (M : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
      (H : (Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ))ˣ),
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 0)
          = (M : Matrix (Fin n) (Fin n) C(X, ℂ)) i j x) ∧
      (∀ (i j : Fin n) (x : X) (z : Sph ℂ),
        (H : Matrix (Fin n) (Fin n) C((X × Sph ℂ) × unitInterval, ℂ)) i j ((x, z), 1)
          = ((G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map
              (fun f => Fund.bdryRestrict X f)) i j (x, z)) := by
  refine ⟨⟨(G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(discUnitEv0 X),
      ((↑(G⁻¹) : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(discUnitEv0 X)), ?_, ?_⟩,
    ⟨(G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(discUnitRH X),
      ((↑(G⁻¹) : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(discUnitRH X)), ?_, ?_⟩,
    ?_, ?_⟩
  · -- `M` is a unit: evaluation on the zero section is a unital ring homomorphism.
    rw [← Matrix.map_mul (f := discUnitEv0 X), Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← Matrix.map_mul (f := discUnitEv0 X), Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · -- `H` is a unit: `discUnitRH` is a unital ring homomorphism.
    rw [← Matrix.map_mul (f := discUnitRH X), Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · rw [← Matrix.map_mul (f := discUnitRH X), Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  · -- At `t = 0` the contraction is the zero section.
    intro i j x z
    change ((G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(discUnitRH X)) i j
        ((x, z), (0 : unitInterval))
      = ((G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(discUnitEv0 X)) i j x
    rw [Matrix.map_apply, Matrix.map_apply, discUnitRH_apply, discUnitEv0_apply]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by simp))
  · -- At `t = 1` the contraction is the inclusion of the boundary.
    intro i j x z
    change ((G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(discUnitRH X)) i j
        ((x, z), (1 : unitInterval))
      = ((G : Matrix (Fin n) (Fin n) C(X × Ball ℂ, ℂ)).map ⇑(Fund.bdryRestrict X)) i j (x, z)
    rw [Matrix.map_apply, Matrix.map_apply, discUnitRH_apply, Fund.bdryRestrict_apply]
    congr 1
    exact Prod.ext rfl (Subtype.ext (by simp [Fund.sphIncl]))

end

end Work.KT.FP
