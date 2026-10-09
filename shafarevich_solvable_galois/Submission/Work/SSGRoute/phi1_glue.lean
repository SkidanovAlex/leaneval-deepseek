import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_wcolim
import Submission.Work.SSGRoute.phi1_lambda_compat
import Submission.Work.SSGRoute.phiAt_level_infl
import Submission.Work.SSGRoute.addHom_extend_of_exponent
import Submission.Work.SSGRoute.phi1_level_trivial_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance: read `PHI1_REALIZATION_STATUS.md` (this lane) and `DESIGN_FIX.md` §1.

# The gluing layer of the E5s realisation: `λ`, `Λ`

This file closes the *unconditional* part of the realisation step
`Work.SSGRoute.exists_realization_of_delta_lam` (node E5s).  For the short exact sequence
`S : 0 → 𝔽_p --i--> M --π--> M₂ → 0` over `G = Gal(K/k)` and a class `y ∈ Ext¹_G(M₂, C_K)` whose
level functionals kill the kernel of the connecting map `δ_L` (the hypothesis `hy`), we build:

* `lambdaColim : Wcolim →+ A` — the glued functional, with `A = colim_L H²(Gal(L/k), C_L)`;
* `lambdaColim_eq_zero_of_iota_eq_zero` — it kills the kernel of `iota : Wcolim →+ V`;
* `lambdaBar : iota.range →+ A` — the descent to the image `W = ⋃_L W_L ⊆ V`;
* `lambdaBar_ext` — the extension `Λ : V →+ A` of `λ` with `p`-torsion values
  (`Work.SSGRoute.addHom_extend_of_exponent`), and its value rule
  `Λ (δ_L j) = ofA_L (φ¹(y)(j))` on the `δ`-images.

The `p`-torsion of the values is the "E5s p-torsion" addendum of `DESIGN_FIX.md`: `δ_L (p • j) = 0`
because `δ_L j` has coefficients `𝔽_p`, whence `φ¹(y)(p • j) = 0` by `hy`, and the pairing is
additive in `j`.

Everything here is unconditional (`Ext` algebra, direct limits, linear algebra).  The remaining
inputs of the realisation are class-field-theoretic (`INJ`, `CYC`, E4Ω). -/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

variable {k K Ω : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] [IsGalois k K]

section Glue

variable (p : ℕ) [Fact p.Prime] (M M₂ : Rep.{0} Coeff (K ≃ₐ[k] K))
  (i : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ M) (π : M ⟶ M₂) (hh : i ≫ π = 0)
  (hS : (ShortComplex.mk i π hh).ShortExact)
  (y : Abelian.Ext M₂ (classesK k K) 1)
  (hy : ∀ (L : Lvl k K Ω) (h : extH (Rep.res (galRes k K L.1) M₂) 1),
      deltaHom (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS h = 0 →
        phiAt (k := k) (K := K) (L := L.1) y h = 0)

/-! ## The glued functional `λ : Wcolim →+ A` -/

/-- **The glued functional on the `δ`-images.**  Its component at the level `L` is
`λ_L : W_L → H²(Gal(L/k), C_L)`, pushed into the class-group colimit `A`. -/
noncomputable def lambdaColim :
    Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
  Wcolim.lift (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
    (g := fun L => (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L).comp
      (lambdaOnRange (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS y (hy L)))
    (hg := by
      intro L L' h w
      obtain ⟨j, hj⟩ := AddMonoidHom.mem_range.mp w.2
      have hw : w = (deltaHom (k := k) (K := K) (L := L.1)
          (ShortComplex.mk i π hh) hS).rangeRestrict j := by
        apply Subtype.ext
        exact hj.symm
      have hw2 : wStep p M M₂ i π hh hS L L' h
            ((deltaHom (k := k) (K := K) (L := L.1)
              (ShortComplex.mk i π hh) hS).rangeRestrict j)
          = (deltaHom (k := k) (K := K) (L := L'.1)
              (ShortComplex.mk i π hh) hS).rangeRestrict
            (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j) := by
        apply Subtype.ext
        show AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L')
            (wStep p M M₂ i π hh hS L L' h
              ((deltaHom (k := k) (K := K) (L := L.1)
                (ShortComplex.mk i π hh) hS).rangeRestrict j))
          = AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L')
              ((deltaHom (k := k) (K := K) (L := L'.1)
                (ShortComplex.mk i π hh) hS).rangeRestrict
                (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j))
        rw [wStep_apply (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L L' h
          ((deltaHom (k := k) (K := K) (L := L.1)
            (ShortComplex.mk i π hh) hS).rangeRestrict j)]
        show inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h)
            (deltaHom (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS j)
          = deltaHom (k := k) (K := K) (L := L'.1) (ShortComplex.mk i π hh) hS
              (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j)
        exact (deltaHom_inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h)
          (ShortComplex.mk i π hh) hS j).symm
      rw [hw, hw2]
      have keyL' : lambdaOnRange (k := k) (K := K) (L := L'.1) (ShortComplex.mk i π hh) hS y (hy L')
            ((deltaHom (k := k) (K := K) (L := L'.1)
              (ShortComplex.mk i π hh) hS).rangeRestrict
              (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j))
          = phiAt (k := k) (K := K) (L := L'.1) y
              (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j) :=
        lambdaOnRange_apply (k := k) (K := K) (L := L'.1) (ShortComplex.mk i π hh) hS y (hy L') _
      have keyL : lambdaOnRange (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS y (hy L)
            ((deltaHom (k := k) (K := K) (L := L.1)
              (ShortComplex.mk i π hh) hS).rangeRestrict j)
          = phiAt (k := k) (K := K) (L := L.1) y j :=
        lambdaOnRange_apply (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS y (hy L) j
      have h1 : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
            (phiAt (k := k) (K := K) (L := L.1) y j)
          = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L'
              (inflCIn (k := k) (show L.1 ≤ L'.1 from h)
                (phiAt (k := k) (K := K) (L := L.1) y j)) :=
        (ClassLevelLimit.of_levelMap (k := k) (K := K) (Ω := Ω) (show L.1 ≤ L'.1 from h)
          (phiAt (k := k) (K := K) (L := L.1) y j)).symm
      have hstep : ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L'
            (phiAt (k := k) (K := K) (L := L'.1) y
              (inflHIn (k := k) (K := K) (show L.1 ≤ L'.1 from h) j))
          = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
              (phiAt (k := k) (K := K) (L := L.1) y j) :=
        (congrArg (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L')
          (phiAt_level_infl (k := k) (K := K) (Ω := Ω) L.1 L'.1
            (show L.1 ≤ L'.1 from h) M₂ y j).symm).trans h1.symm
      exact (congrArg (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L') keyL').trans
        (hstep.trans (congrArg (ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L) keyL).symm))

@[simp] theorem lambdaColim_of (L : Lvl k K Ω) (w : Wsys p M M₂ i π hh hS L) :
    lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy
        (Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L w)
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (lambdaOnRange (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS y (hy L) w) :=
  rfl

/-- **`lambdaColim` kills the kernel of `iota`** — this is where the well-definedness of `λ` on
`W = ⋃_L W_L ⊆ V` is proved, and it needs *no* class-field-theoretic input: if `w ∈ W_L` dies in
`V`, it dies at a higher level `L'`; there `inflHIn` is `inflTrivIn` (the trivial module!), so the
vanishing is that of `levelMap`, hence `wStep w = 0` and `w = 0` in `Wcolim`. -/
theorem lambdaColim_eq_zero_of_iota_eq_zero (z : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS)
    (hz : iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS z = 0) :
    lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z = 0 := by
  refine Wcolim.induction (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
    (C := fun z => iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS z = 0 →
      lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z = 0) ?_ z hz
  intro L w hw
  rw [iota_of] at hw
  obtain ⟨L', hLL', hmap⟩ := (LevelCohLimit.of_eq_zero_iff (k := k) (K := K) (Ω := Ω) p L
    (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)).mp hw
  have hmap' : inflTrivIn (k := k) (show L.1 ≤ L'.1 from hLL') (ZMod p)
      (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w) = 0 := by
    rw [← levelMap_apply (k := k) p L L' hLL'
      (AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L) w)]
    exact hmap
  have hw0 : wStep p M M₂ i π hh hS L L' hLL' w = 0 := by
    apply Subtype.ext
    show AddSubgroup.subtype (wc_Wsub p M M₂ i π hh hS L')
      (wStep p M M₂ i π hh hS L L' hLL' w) = 0
    rw [wStep_apply (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L L' hLL' w]
    rw [inflHIn_eq_inflTrivIn (k := k) (K := K) p (show L.1 ≤ L'.1 from hLL')]
    exact hmap'
  rw [← Wcolim.of_wStep (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS hLL' w, hw0,
    Wcolim.of_zero]
  exact map_zero _

/-! ## The descent to `W = iota.range ⊆ V` and the extension `Λ` -/

/-- **The descended functional `λ̄` on `W = iota.range ⊆ V`.** -/
noncomputable def lambdaBar :
    (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS).range →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω) :=
  rangeLift (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS)
    (lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy)
    (by
      intro z hz
      rw [AddMonoidHom.mem_ker] at hz ⊢
      exact lambdaColim_eq_zero_of_iota_eq_zero (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
        y hy z hz)

/-- The computation rule of `λ̄` on the canonical images. -/
theorem lambdaBar_apply (z : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS) :
    lambdaBar (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy
        ((iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS).rangeRestrict z)
      = lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z :=
  rangeLift_apply _ _ _ z

/-- **The values of `λ_L` are `p`-torsion** (the "E5s p-torsion" addendum): `δ_L j` has coefficients
`𝔽_p`, so `p • δ_L j = 0`, whence `φ¹(y)(p • j) = 0` by `hy` and additivity gives
`p • λ_L (δ_L j) = 0`. -/
theorem smul_lambdaOnRange_eq_zero (L : Lvl k K Ω) (w : Wsys p M M₂ i π hh hS L) :
    p • lambdaOnRange (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS y (hy L) w = 0 := by
  obtain ⟨j, hj⟩ := AddMonoidHom.mem_range.mp w.2
  have hw : w = (deltaHom (k := k) (K := K) (L := L.1)
      (ShortComplex.mk i π hh) hS).rangeRestrict j := by
    apply Subtype.ext
    exact hj.symm
  rw [hw, lambdaOnRange_apply (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS y
    (hy L) j]
  have hpj : p • phiAt (k := k) (K := K) (L := L.1) y j
      = phiAt (k := k) (K := K) (L := L.1) y (p • j) :=
    ((phiAtHomRight (k := k) (K := K) (L := L.1) y).map_nsmul p j).symm
  rw [hpj]
  refine hy L (p • j) ?_
  rw [map_nsmul]
  exact extH_trivial_zmodp_smul_eq_zero p
    (deltaHom (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS j)

/-- The values of `lambdaColim` are `p`-torsion. -/
theorem smul_lambdaColim_eq_zero (z : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS) :
    p • lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z = 0 := by
  refine Wcolim.induction (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
    (C := fun z => p • lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z = 0) ?_ z
  intro L w
  rw [lambdaColim_of]
  rw [← map_nsmul,
    smul_lambdaOnRange_eq_zero (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy L w,
    map_zero]

/-- The values of `λ̄` are `p`-torsion. -/
theorem smul_lambdaBar_eq_zero (w : (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS).range) :
    p • lambdaBar (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy w = 0 := by
  obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.mp w.2
  have hw : w = (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS).rangeRestrict z := by
    apply Subtype.ext
    exact hz.symm
  rw [hw, lambdaBar_apply (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z]
  exact smul_lambdaColim_eq_zero (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z

/-- **The level system `V` has exponent `p`.** -/
theorem smul_levelCohLimit_eq_zero (v : LevelCohLimit (k := k) (K := K) (Ω := Ω) p) :
    p • v = 0 := by
  refine LevelCohLimit.induction (k := k) (K := K) (Ω := Ω) p
    (C := fun v => p • v = 0) ?_ v
  intro L x
  rw [← map_nsmul, extH_trivial_zmodp_smul_eq_zero p x, map_zero]

/-- **The extension `Λ : V →+ A` of `λ` with `p`-torsion values** — the last unconditional piece of
the gluing.  It is produced from `λ̄ : W →+ A` by `Work.SSGRoute.addHom_extend_of_exponent` (`V` has
exponent `p`, the values of `λ̄` are `p`-torsion). -/
theorem lambdaBar_ext :
    ∃ Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
        ClassLevelLimit (k := k) (K := K) (Ω := Ω),
      (∀ z : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS,
        Λ (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS z)
          = lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z)
      ∧ ∀ v, p • Λ v = 0 := by
  obtain ⟨Φ, hΦ, hpΦ⟩ := addHom_extend_of_exponent p
    (smul_levelCohLimit_eq_zero (k := k) (K := K) (Ω := Ω) p)
    (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS).range
    (lambdaBar (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy)
    (smul_lambdaBar_eq_zero (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy)
  refine ⟨Φ, fun z => ?_, hpΦ⟩
  rw [← lambdaBar_apply (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z]
  exact hΦ ((iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS).rangeRestrict z)

/-- **The value of `Λ` on the `δ`-images**: `Λ(δ_L j) = ofA_L (φ¹(y)(j))`. -/
theorem Lambda_apply_delta
    (Λ : LevelCohLimit (k := k) (K := K) (Ω := Ω) p →+
      ClassLevelLimit (k := k) (K := K) (Ω := Ω))
    (hΛ : ∀ z : Wcolim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS,
      Λ (iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS z)
        = lambdaColim (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS y hy z)
    (L : Lvl k K Ω) (j : extH (Rep.res (galRes k K L.1) M₂) 1) :
    Λ (LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L
        (deltaHom (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS j))
      = ClassLevelLimit.of (k := k) (K := K) (Ω := Ω) L
          (phiAt (k := k) (K := K) (L := L.1) y j) := by
  have h1 : iota (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS
      (Wcolim.of (k := k) (K := K) (Ω := Ω) p M M₂ i π hh hS L
        ((deltaHom (k := k) (K := K) (L := L.1)
          (ShortComplex.mk i π hh) hS).rangeRestrict j))
      = LevelCohLimit.of (k := k) (K := K) (Ω := Ω) p L
          (deltaHom (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS j) := by
    rw [iota_of]
    rfl
  rw [← h1, hΛ, lambdaColim_of,
    lambdaOnRange_apply (k := k) (K := K) (L := L.1) (ShortComplex.mk i π hh) hS y (hy L) j]

end Glue

end Work.SSGRoute
