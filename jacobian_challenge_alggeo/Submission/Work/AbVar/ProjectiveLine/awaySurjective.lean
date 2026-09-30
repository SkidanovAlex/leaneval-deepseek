import Mathlib
import Submission.Work.AbVar.ProjectiveLine.chart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.AbVar.ProjectiveLine

open MvPolynomial HomogeneousLocalization

/-- The chart ring `Away (StdG R) (X i)` of the projective line is generated, as an
`↥(StdG R 0)`-algebra, by `X_j / X_i` (for `j ≠ i`).  This is the surjectivity of the
substitution `T ↦ X_j/X_i`. -/
theorem awaySurjective {R : Type*} [CommRing R] {i j : Fin 2} (hij : j ≠ i) :
    Function.Surjective (Work.AbVar.ProjectiveLine.polyToAway (R := R) i j) := by
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (StdG R) (X_mem_stdG (R := R) i) x
  refine ⟨subst (R := R) i a, ?_⟩
  let L := Localization (Submonoid.powers (MvPolynomial.X i : Poly2 R))
  let ψ : Poly2 R →+* L := algebraMap _ _
  let w : L := algebraMap (Poly2 R) L (MvPolynomial.X i)
  let E : L := Localization.mk (MvPolynomial.X j) (powOne (R := R) i)
  let θ : Poly2 R →+* L :=
    MvPolynomial.eval₂Hom (algebraMap R L) (fun k : Fin 2 => if k = i then (1 : L) else E)
  let s : Submonoid.powers (MvPolynomial.X i : Poly2 R) := ⟨MvPolynomial.X i ^ n, ⟨n, rfl⟩⟩
  -- The value of a constant of `𝒜 0` inside `Away` is the corresponding element of `Poly2 R`.
  have val_zeroHom : ∀ b : ↥(StdG R 0),
      (algebraMap (Away (StdG R) (MvPolynomial.X i)) L)
          ((algebraMap (StdG R 0) (Away (StdG R) (MvPolynomial.X i))) b)
        = algebraMap (Poly2 R) L (b : Poly2 R) := by
    intro b
    rw [← IsScalarTower.algebraMap_apply (↥(StdG R 0)) (Away (StdG R) (MvPolynomial.X i)) L b]
    rw [IsScalarTower.algebraMap_apply (↥(StdG R 0)) (Poly2 R) L b]
    rw [show algebraMap (↥(StdG R 0)) (Poly2 R) b = (b : Poly2 R) from rfl]
  -- `ψ` is the substitution of the variables by their images in the localisation.
  have psi_eq : ψ = MvPolynomial.eval₂Hom (algebraMap R L)
      (fun k : Fin 2 => ψ (MvPolynomial.X k)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      rw [MvPolynomial.eval₂Hom_C]
      rw [← MvPolynomial.algebraMap_eq]
      exact IsScalarTower.algebraMap_apply R (Poly2 R) L r
    · intro k
      rw [MvPolynomial.eval₂Hom_X']
  have θ_monomial (d : Fin 2 →₀ ℕ) (r : R) :
      θ (MvPolynomial.monomial d r)
        = algebraMap R L r * ∏ k : Fin 2, (if k = i then (1 : L) else E) ^ (d k) := by
    rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun k => by simp)]
  have psi_monomial (d : Fin 2 →₀ ℕ) (r : R) :
      ψ (MvPolynomial.monomial d r)
        = algebraMap R L r * ∏ k : Fin 2, (ψ (MvPolynomial.X k)) ^ (d k) := by
    conv_lhs => rw [psi_eq]
    rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun k => by simp)]
  -- Multiplicatively, `θ` and `ψ` differ by the factor `w = X_i`.
  have hθX : ∀ k : Fin 2, (if k = i then (1 : L) else E) * w = ψ (MvPolynomial.X k) := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [ite_eq_left rfl, one_mul]
    · have hkj : k = j := by
        apply Fin.ext
        have h1 : k.val ≠ i.val := fun h => hk (Fin.ext h)
        have h2 : j.val ≠ i.val := fun h => hij (Fin.ext h)
        have hk2 := k.isLt; have hj2 := j.isLt; have hi2 := i.isLt
        omega
      rw [hkj]
      rw [ite_eq_right hij]
      change Localization.mk (MvPolynomial.X j) (powOne (R := R) i) * w = ψ (MvPolynomial.X j)
      rw [show w = algebraMap (Poly2 R) L
            ((powOne (R := R) i : Submonoid.powers (MvPolynomial.X i)) : Poly2 R) by
          rw [powOne_val, map_pow, pow_one]]
      rw [Localization.mk_eq_mk', IsLocalization.mk'_spec]
  -- The core computation: for a homogeneous polynomial of degree `n`,
  -- `θ a * w ^ n = ψ a`.
  have key : ∀ (n : ℕ) (a : Poly2 R), MvPolynomial.IsHomogeneous a n → θ a * w ^ n = ψ a := by
    intro n a ha
    induction ha using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p q hp hq ihp ihq => rw [map_add, map_add, add_mul, ihp, ihq]
    | monomial d r hr =>
        rw [θ_monomial, psi_monomial]
        have hsum : ∑ k : Fin 2, d k = n := by
          rw [Finsupp.weight_eq_sum] at hr
          simpa using hr
        have hψ : ∏ k : Fin 2, (ψ (MvPolynomial.X k)) ^ (d k)
            = (∏ k : Fin 2, (if k = i then (1 : L) else E) ^ (d k)) * w ^ n := by
          calc ∏ k : Fin 2, (ψ (MvPolynomial.X k)) ^ (d k)
              = ∏ k : Fin 2, ((if k = i then (1 : L) else E) * w) ^ (d k) := by
                apply Finset.prod_congr rfl
                intro k _
                rw [hθX k]
            _ = ∏ k : Fin 2, ((if k = i then (1 : L) else E) ^ (d k) * w ^ (d k)) := by
                apply Finset.prod_congr rfl
                intro k _
                rw [mul_pow]
            _ = (∏ k : Fin 2, (if k = i then (1 : L) else E) ^ (d k))
                  * (∏ k : Fin 2, w ^ (d k)) := by
                rw [Finset.prod_mul_distrib]
            _ = (∏ k : Fin 2, (if k = i then (1 : L) else E) ^ (d k)) * w ^ n := by
                rw [Finset.prod_pow_eq_pow_sum, hsum]
        rw [hψ, mul_assoc]
  -- Identifying `θ` with the composite `val ∘ polyToAway ∘ subst`.
  have hcomp : θ = (algebraMap (Away (StdG R) (MvPolynomial.X i)) L).comp
      ((polyToAway (R := R) i j).toRingHom.comp (subst (R := R) i)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      show θ (MvPolynomial.C r) = _
      rw [MvPolynomial.eval₂Hom_C]
      show algebraMap R L r = (algebraMap (Away (StdG R) (MvPolynomial.X i)) L)
        (polyToAway (R := R) i j (subst (R := R) i (MvPolynomial.C r)))
      rw [subst_C, polyToAway_C]
      show algebraMap R L r = (algebraMap (Away (StdG R) (MvPolynomial.X i)) L)
        ((algebraMap (↥(StdG R 0)) (Away (StdG R) (MvPolynomial.X i))) (constToZero (R := R) r))
      rw [val_zeroHom (constToZero (R := R) r)]
      rw [constToZero_apply, ← MvPolynomial.algebraMap_eq]
      rw [← IsScalarTower.algebraMap_apply R (Poly2 R) L r]
    · intro k
      show θ (MvPolynomial.X k) = _
      rw [MvPolynomial.eval₂Hom_X']
      show (if k = i then (1 : L) else E) = (algebraMap (Away (StdG R) (MvPolynomial.X i)) L)
        (polyToAway (R := R) i j (subst (R := R) i (MvPolynomial.X k)))
      by_cases hk : k = i
      · subst hk
        rw [subst_self, map_one, map_one, ite_eq_left rfl]
      · have hkj : k = j := by
          apply Fin.ext
          have h1 : k.val ≠ i.val := fun h => hk (Fin.ext h)
          have h2 : j.val ≠ i.val := fun h => hij (Fin.ext h)
          have hk2 := k.isLt; have hj2 := j.isLt; have hi2 := i.isLt
          omega
        rw [hkj, ite_eq_right hij, subst_other hij, polyToAway_X]
        change Localization.mk (MvPolynomial.X j) (powOne (R := R) i) = (awayU (R := R) i j).val
        rw [awayU_val]
  have ha' : a ∈ StdG R n := by simpa using ha
  have hkey := key n a ((MvPolynomial.mem_homogeneousSubmodule n a).mp ha')
  -- The image of `a / X_i ^ n` in the localisation, computed two ways.
  have hmk : Localization.mk a s * w ^ n = ψ a := by
    have hw : w ^ n = algebraMap (Poly2 R) L (s : Poly2 R) := by
      show (algebraMap (Poly2 R) L (MvPolynomial.X i)) ^ n
        = algebraMap (Poly2 R) L (s : Poly2 R)
      rw [map_pow]
    rw [hw, Localization.mk_eq_mk', IsLocalization.mk'_spec]
  have huw : IsUnit w := by
    have h := IsLocalization.map_units L (powOne (R := R) i)
    rw [powOne_val] at h
    simpa [w] using h
  have hθa : θ a = Localization.mk a s :=
    IsUnit.mul_right_cancel (huw.pow n) (hkey.trans hmk.symm)
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk]
  have hval1 : (polyToAway (R := R) i j (subst (R := R) i a)).val = θ a := by
    rw [hcomp]
    rfl
  rw [hval1]
  exact hθa

end Work.AbVar.ProjectiveLine
