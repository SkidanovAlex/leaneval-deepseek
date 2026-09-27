import Mathlib
import Submission.Work.Drive.Whitney.frameExtensionBoundary
import Submission.Work.Drive.Whitney.glFreedom

namespace Work.Drive.Whitney

open scoped ContDiff

/-- If `0 < n`, `u w : EuclideanSpace ℝ (Fin n)` are nonzero and `M₀ M₁` are invertible continuous
linear maps with `M₀ u = M₁ u = w` and `0 < det M₀ * det M₁`, then `M₀` and `M₁` are joined by a
smooth path of invertible continuous linear maps all sending `u` to `w`.

The proof conjugates by a unit `Z` sending `u` to the first basis vector `e₀`, so that the problem
becomes one inside the stabiliser of `e₀`; the latter is connected by the proved brick
`Work.Drive.Whitney.FB.stabilizerPath` (smooth paths in `GL(E)` fixing the first `k` basis vectors
and satisfying the determinant sign condition). -/
theorem pathThroughGLofFixedLine {n : ℕ} (hn : 0 < n)
    (u w : EuclideanSpace ℝ (Fin n)) (hu : u ≠ 0) (hw : w ≠ 0)
    {M₀ M₁ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (h₀ : IsUnit M₀) (h₁ : IsUnit M₁) (hM₀ : M₀ u = w) (hM₁ : M₁ u = w)
    (hcomp : 0 < (LinearMap.det (M₀ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) *
                (LinearMap.det (M₁ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))) :
    ∃ Φ : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ (∀ t, IsUnit (Φ t)) ∧
      (∀ t, Φ t u = w) ∧ Φ 0 = M₀ ∧ Φ 1 = M₁ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  have hkm : 1 ≤ m + 1 := by omega
  have he₀ne : (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0 ≠ 0 := by
    rw [EuclideanSpace.basisFun_apply]
    intro h
    have hc := congrArg (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x.ofLp (0 : Fin (m + 1))) h
    simpa using hc
  -- (1) a unit `Z` sending `u` to `e₀`
  obtain ⟨Z, hZunit, hZu⟩ :=
    exists_isUnit_apply_eq u ((EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0) hu he₀ne
  -- (2) `Z`, `M₀`, `M₁` as continuous linear equivalences
  set Zc : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) := ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin (m + 1))) hZunit.unit with hZcdef
  have hZc : (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = Z := by
    rw [hZcdef]
    refine ContinuousLinearMap.ext fun x => ?_
    show ((ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin (m + 1)))) hZunit.unit) x = Z x
    rw [ContinuousLinearEquiv.unitsEquiv_apply, hZunit.unit_spec]
  set M₀c : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) := ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin (m + 1))) h₀.unit with hM₀cdef
  set M₁c : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) := ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin (m + 1))) h₁.unit with hM₁cdef
  have hM₀c : (M₀c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = M₀ := by
    rw [hM₀cdef]
    refine ContinuousLinearMap.ext fun x => ?_
    show ((ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin (m + 1)))) h₀.unit) x = M₀ x
    rw [ContinuousLinearEquiv.unitsEquiv_apply, h₀.unit_spec]
  have hM₁c : (M₁c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = M₁ := by
    rw [hM₁cdef]
    refine ContinuousLinearMap.ext fun x => ?_
    show ((ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin (m + 1)))) h₁.unit) x = M₁ x
    rw [ContinuousLinearEquiv.unitsEquiv_apply, h₁.unit_spec]
  have hZcu : (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) u = (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0 := by
    rw [hZc]; exact hZu
  -- (3) `C := M₀⁻¹ M₁`, sending `u` to `u`
  set C : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) := M₁c.trans M₀c.symm with hCdef
  have hC_u : C u = u := by
    show M₀c.symm (M₁c u) = u
    have h1 : M₁c u = w := by
      have hh : (M₁c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) u = M₁ u := by rw [hM₁c]
      simpa using hh.trans hM₁
    rw [h1, ← hM₀]
    exact ContinuousLinearEquiv.symm_apply_apply M₀c u
  -- determinant bookkeeping, all at the level of continuous linear maps
  let detc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) → ℝ := fun f => LinearMap.det (f : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
  have hdet_mul : ∀ f g : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))), detc (f * g) = detc f * detc g := by
    intro f g
    show LinearMap.det ((f * g : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = LinearMap.det (f : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * LinearMap.det (g : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
    rw [show ((f * g : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = (f : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ∘ₗ (g : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) from rfl, LinearMap.det_comp]
  have hdet_one : detc (1 : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = 1 := by
    show LinearMap.det ((1 : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = 1
    rw [show ((1 : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = (1 : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) from rfl,
      show (1 : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = LinearMap.id from rfl, LinearMap.det_id]
  have hsymm : detc (M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * detc (M₀c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = 1 := by
    rw [← hdet_mul (M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) (M₀c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))]
    have h1 : ((M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (M₀c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) = 1 := by
      refine ContinuousLinearMap.ext fun x => ?_
      exact ContinuousLinearEquiv.symm_apply_apply M₀c x
    rw [h1, hdet_one]
  have hM₀cdet : detc (M₀c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by rw [hM₀c]
  have hM₁cdet : detc (M₁c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = detc (M₁ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by rw [hM₁c]
  have hCclm : (C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = (M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (M₁c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
    rw [hCdef]
    refine ContinuousLinearMap.ext fun x => ?_
    show M₀c.symm (M₁c x) = ((M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (M₁c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) x
    rw [show ((M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (M₁c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) x
      = (M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ((M₁c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) x) from rfl]
    rfl
  have hdetC : detc (C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = detc (M₁ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
    rw [hCclm, hdet_mul, hM₁cdet]
    calc detc (M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * detc (M₁ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
        = detc (M₁ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (detc (M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * detc (M₀c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) := by
          rw [← hM₀cdet]; ring
      _ = detc (M₁ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by rw [hsymm, mul_one]
  have hcomp' : 0 < detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * detc (M₁ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := hcomp
  have hCpos : 0 < detc (C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
    have hd₀ : detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hcomp'
      exact lt_irrefl 0 hcomp'
    have hkey : detc (C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
        * detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
        * detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
        = detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * detc (M₁ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
      rw [hdetC]; ring
    have hsq : 0 < detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
        * detc (M₀ : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) :=
      mul_self_pos.mpr hd₀
    nlinarith [hkey, hcomp', hsq]
  -- (4) `C' := Zc⁻¹ C Zc`, fixing `e₀`
  set C' : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) := Zc.symm.trans (C.trans Zc) with hC'def
  have hC'apply : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), C' x = Zc (C (Zc.symm x)) := by
    intro x
    rw [hC'def, ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply]
  have hcast : Fin.castLE hkm (0 : Fin 1) = (0 : Fin (m + 1)) := by
    ext; simp
  have hZsymm : Zc.symm ((EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0) = u := by
    rw [ContinuousLinearEquiv.symm_apply_eq]
    show (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0 = (Zc : (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1)))) u
    rw [hZc]; exact hZu.symm
  have hdetC' : detc (C' : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = detc (C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
    show LinearMap.det ((C' : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = LinearMap.det ((C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
    have hlin : ((C' : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = ((Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ∘ₗ
        (((C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ∘ₗ ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) := by
      rw [show ((C' : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = ((C' : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) from rfl, hC'def]
      refine LinearMap.ext fun x => ?_
      show (Zc.symm.trans (C.trans Zc)) x
        = ((Zc : (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))))) (((C : (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))))) (((Zc.symm : (EuclideanSpace ℝ (Fin (m+1)) →L[ℝ] EuclideanSpace ℝ (Fin (m+1))))) x))
      rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply]
      rfl
    rw [hlin]
    have h := LinearMap.det_conj ((C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) (Zc : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    exact h
  -- (5) the path inside the stabiliser of `e₀`, from `1` to `C'`
  obtain ⟨h, hh0, hh1, hfix, hsm⟩ :=
    FB.stabilizerPath (m := m + 1) (k := 1) hkm
      (1 : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) C'
      (by intro i
          rw [show (1 : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
              = ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (m + 1))) from rfl]
          exact ContinuousLinearEquiv.refl_apply ℝ (EuclideanSpace ℝ (Fin (m + 1))) _)
      (fun i => by
          have hA : (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) (Fin.castLE hkm i)
              = (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0 := by
            congr 1
            exact Fin.ext (by simp)
          rw [hA, hC'apply, hZsymm, hC_u]
          show (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) u
            = (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0
          rw [hZc]; exact hZu)
      (by
        change 0 < detc (1 : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * detc (C' : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
        rw [hdet_one, hdetC', one_mul]
        exact hCpos)
  -- (6) the final family `r ↦ M₀ · Zc⁻¹ · h r · Zc`
  refine ⟨fun r => M₀ * ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))), ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ =>
      (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) := hsm
    have hfam1 : (fun r : ℝ => (((h r).trans Zc.symm) :
          (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))
        = fun r : ℝ => (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
            * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
      funext r
      refine ContinuousLinearMap.ext fun x => ?_
      change ((h r).trans Zc.symm) x =
        ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) x
      rw [ContinuousLinearEquiv.trans_apply]
      rfl
    have hA' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ =>
        (((h r).trans Zc.symm) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) :=
      ContDiff.clm_comp (𝕜 := ℝ)
        (g := fun _ : ℝ => (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))
        (f := fun r : ℝ => (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))
        contDiff_const hs
    have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ =>
        (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) := by
      rw [← hfam1]; exact hA'
    have hfam2 : (fun r : ℝ => ((Zc.trans ((h r).trans Zc.symm)) :
          (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))
        = fun r : ℝ =>
            (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
            * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
            * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
      funext r
      refine ContinuousLinearMap.ext fun x => ?_
      change (Zc.trans ((h r).trans Zc.symm)) x =
        ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) x
      rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply]
      rfl
    have hB' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ =>
        ((Zc.trans ((h r).trans Zc.symm)) :
          (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) :=
      ContDiff.clm_comp (𝕜 := ℝ)
        (g := fun r : ℝ => (((h r).trans Zc.symm) :
          (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))
        (f := fun _ : ℝ => (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) hA' contDiff_const
    have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ =>
        (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) := by
      rw [← hfam2]; exact hB'
    exact ContDiff.clm_comp (𝕜 := ℝ) (g := fun _ : ℝ => M₀)
      (f := fun r : ℝ =>
        (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (h r : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))
          * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))))) contDiff_const hB
  · -- invertibility
    intro r
    have hZunit' : IsUnit (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) :=
      (ContinuousLinearMap.isUnit_iff_bijective (f := (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))).mpr Zc.bijective
    have hZsymm_unit : IsUnit ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) :=
      (ContinuousLinearMap.isUnit_iff_bijective (f := ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))).mpr Zc.symm.bijective
    have hhr : IsUnit ((h r : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) :=
      (ContinuousLinearMap.isUnit_iff_bijective (f := ((h r : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))).mpr (h r).bijective
    exact h₀.mul (hZsymm_unit.mul (hhr.mul hZunit'))
  · -- `u ↦ w`
    intro r
    show (M₀ * ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * ((h r : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))) u = w
    change M₀ ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) (((h r : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ((Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) u))) = w
    rw [hZcu]
    have hfixr : ((h r : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ((EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0)
        = (EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0 := by
      have hh := hfix r (0 : Fin 1)
      rw [hcast] at hh
      exact hh
    rw [hfixr]
    have hZsymm_u : (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) ((EuclideanSpace.basisFun (Fin (m + 1)) ℝ) 0) = u := by
      rw [← hZcu]
      exact ContinuousLinearEquiv.symm_apply_apply Zc u
    rw [hZsymm_u]
    exact hM₀
  · -- `Φ 0 = M₀`
    show (M₀ * ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * ((h 0 : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))) = M₀
    have hh0' : ((h 0 : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = 1 := by
      rw [hh0]
      rw [show (1 : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (m + 1))) from rfl,
        ContinuousLinearEquiv.coe_refl]
      rfl
    rw [hh0', mul_one]
    have hZcinv : (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = 1 := by
      refine ContinuousLinearMap.ext fun x => ?_
      exact ContinuousLinearEquiv.symm_apply_apply Zc x
    rw [hZcinv, mul_one]
  · -- `Φ 1 = M₁`
    show (M₀ * ((Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * ((h 1 : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))))) = M₁
    have hh1' : ((h 1 : (EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = (C' : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by rw [hh1]
    rw [hh1']
    have hCeq : (Zc.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (C' : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (Zc : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = (C : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) := by
      refine ContinuousLinearMap.ext fun x => ?_
      show Zc.symm (C' (Zc x)) = C x
      rw [hC'apply, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [hCeq, hCclm]
    have hM₀c_inv : (M₀c : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) * (M₀c.symm : (EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))) = 1 := by
      refine ContinuousLinearMap.ext fun x => ?_
      exact ContinuousLinearEquiv.apply_symm_apply M₀c x
    rw [← hM₀c, ← hM₁c, ← mul_assoc, hM₀c_inv, one_mul]

end Work.Drive.Whitney
