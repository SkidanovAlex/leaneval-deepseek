import Mathlib
import Submission.NK.NUV2.Transfer.verDefs
import Submission.NK.NUV2.Transfer.normLevelSetup
import Submission.NK.NUV2.Transfer.transferEll_natural
import Submission.NK.Reconstruct.generalBaseChange_galToGamma
import Submission.NK.Reconstruct.exists_gammaEquivOfPhi
import Submission.NK.Reconstruct.continuous_tauStar
import Submission.NK.Reconstruct.inertia_ellPart_pow_eq_one

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NK.NUV2.Transfer

open NK.Reconstruct
open scoped commutatorElement

noncomputable section

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

namespace NormLevelB

/-! ## Part A: elementary helpers -/

section Helpers

variable {A : Type*} [CommGroup A] [Finite A]

/-- The ℓ-primary projection distributes over finite products. -/
theorem ellComp_prod (ℓ : ℕ) {ι : Type*} (s : Finset ι) (f : ι → A) :
    ellComp ℓ (s.prod f) = s.prod (fun i => ellComp ℓ (f i)) :=
  map_prod (ellCompHom (A := A) ℓ) f s

end Helpers

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
  (M : NumFieldIn ℚ Ω) (L : FrobLevel ℚ Ω)
  [NumberField ↥M.L] [NumberField ↥L.L] [FiniteDimensional ℚ ↥M.L] [FiniteDimensional ℚ ↥L.L]
  [Normal ℚ ↥L.L] [IsSepClosure ↥M.L Ω] [IsSepClosure ↥L.L Ω] (hML : M.L ≤ L.L)
  [Algebra ↥M.L ↥L.L] [IsScalarTower ↥M.L ↥L.L Ω]

/-! ## Part B: the chosen extensions of the elements of `Gal(L.L/M.L)` -/

/-- A chosen extension of `g` to a ring automorphism of `Ω`. -/
noncomputable def thetaOf (g : Gal(↥L.L/↥M.L)) : Ω ≃+* Ω :=
  Classical.choose
    (exists_ringEquiv_extends_of_isSepClosure Ω L.L (AlgEquiv.restrictScalars ℚ g))

theorem thetaOf_mem (g : Gal(↥L.L/↥M.L)) :
    ∀ x : Ω, x ∈ L.L ↔ thetaOf M L g x ∈ L.L :=
  (Classical.choose_spec
    (exists_ringEquiv_extends_of_isSepClosure Ω L.L (AlgEquiv.restrictScalars ℚ g))).1

theorem thetaOf_apply (g : Gal(↥L.L/↥M.L)) (x : ↥L.L) :
    thetaOf M L g (x : Ω) = ((AlgEquiv.restrictScalars ℚ g x : ↥L.L) : Ω) :=
  (Classical.choose_spec
    (exists_ringEquiv_extends_of_isSepClosure Ω L.L (AlgEquiv.restrictScalars ℚ g))).2 x

/-- The chosen extension, viewed as an `↥M.L`-algebra automorphism of `Ω`. -/
noncomputable def thetaM (g : Gal(↥L.L/↥M.L)) : Gal(Ω/↥M.L) where
  toRingEquiv := thetaOf M L g
  commutes' c := by
    show thetaOf M L g (algebraMap ↥M.L Ω c) = algebraMap ↥M.L Ω c
    rw [IsScalarTower.algebraMap_apply ↥M.L ↥L.L Ω c]
    show (thetaOf M L g) ((algebraMap ↥M.L ↥L.L c : ↥L.L) : Ω)
      = ((algebraMap ↥M.L ↥L.L c : ↥L.L) : Ω)
    rw [thetaOf_apply M L g (algebraMap ↥M.L ↥L.L c)]
    exact congrArg Subtype.val
      ((AlgEquiv.restrictScalars_apply ℚ g (algebraMap ↥M.L ↥L.L c)).trans (g.commutes c))

@[simp] theorem thetaM_apply (g : Gal(↥L.L/↥M.L)) (x : Ω) :
    (thetaM M L g) x = thetaOf M L g x := rfl

/-- The restriction of the chosen extension to the auxiliary level `AUX R`. -/
noncomputable def thetaA (R : FrobLevel ↥L.L Ω) (g : Gal(↥L.L/↥M.L)) :
    Gal(↥(auxA M L hML R).L/↥M.L) :=
  AlgEquiv.restrictNormalHom (F := ↥M.L) (K₁ := Ω) (auxA M L hML R).L (thetaM M L g)

theorem thetaA_apply_coe (R : FrobLevel ↥L.L Ω) (g : Gal(↥L.L/↥M.L))
    (x : ↥(auxA M L hML R).L) :
    ((thetaA M L hML R g x : ↥(auxA M L hML R).L) : Ω) = thetaOf M L g (x : Ω) :=
  AlgEquiv.restrictNormalHom_apply (F := ↥M.L) (K₁ := Ω) (auxA M L hML R).L
    (thetaM M L g) x

/-- The restriction of `σ : Gal(Ω/L.L)` to the auxiliary level `AUX R`. -/
noncomputable def sigmaA (R : FrobLevel ↥L.L Ω) (σ : Gal(Ω/↥L.L)) :
    Gal(↥(auxA M L hML R).L/↥M.L) :=
  AlgEquiv.restrictNormalHom (F := ↥M.L) (K₁ := Ω) (auxA M L hML R).L (galRestrict hML σ)

theorem sigmaA_apply_coe (R : FrobLevel ↥L.L Ω) (σ : Gal(Ω/↥L.L))
    (x : ↥(auxA M L hML R).L) :
    ((sigmaA M L hML R σ x : ↥(auxA M L hML R).L) : Ω) = σ (x : Ω) :=
  AlgEquiv.restrictNormalHom_apply (F := ↥M.L) (K₁ := Ω) (auxA M L hML R).L
    (galRestrict hML σ) x

/-! ## Part C: the unwinding of `resQ` -/

/-- The restriction `resQ` computed on elements: it is the restriction of the automorphism to
`L.L`. -/
theorem resQ_apply (R : FrobLevel ↥L.L Ω) (σ : Gal(↥(auxA M L hML R).L/↥M.L)) (x : ↥L.L) :
    (((resQ M L hML R σ) x : ↥L.L) : Ω)
      = ((σ ⟨(x : Ω), le_auxA M L hML R (LL_le_B (L := L) (B := R) x)⟩
            : ↥(auxA M L hML R).L) : Ω) := by
  rfl


/-- **The restriction of the chosen extension to `AUX R` restricts to `g` on `L.L`.** -/
theorem resQ_thetaA (R : FrobLevel ↥L.L Ω) (g : Gal(↥L.L/↥M.L)) :
    resQ M L hML R (thetaA M L hML R g) = g := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  rw [resQ_apply M L hML R (thetaA M L hML R g) x, thetaA_apply_coe, thetaOf_apply M L g]
  exact congrArg Subtype.val (AlgEquiv.restrictScalars_apply ℚ g x)

/-- **The restriction `resQ : Gal(AUX/M.L) →* Gal(L.L/M.L)` is surjective.** -/
theorem resQ_surjective (R : FrobLevel ↥L.L Ω) : Function.Surjective (resQ M L hML R) :=
  fun g => ⟨thetaA M L hML R g, resQ_thetaA M L hML R g⟩

/-- The reindexing `Gal(AUX/M.L) ⧸ H_A ≃* Gal(L.L/M.L)`. -/
noncomputable def resQEquiv (R : FrobLevel ↥L.L Ω) :
    (Gal(↥(auxA M L hML R).L/↥M.L) ⧸ HA M L hML R) ≃* Gal(↥L.L/↥M.L) :=
  QuotientGroup.quotientKerEquivOfSurjective (resQ M L hML R) (resQ_surjective M L hML R)

@[simp] theorem resQEquiv_mk (R : FrobLevel ↥L.L Ω)
    (g : Gal(↥(auxA M L hML R).L/↥M.L)) :
    resQEquiv M L hML R (QuotientGroup.mk g) = resQ M L hML R g := rfl

/-- The restriction of `σ` to the auxiliary level lies in `H_A`. -/
theorem sigmaA_mem_HA (R : FrobLevel ↥L.L Ω) (σ : Gal(Ω/↥L.L)) :
    sigmaA M L hML R σ ∈ HA M L hML R := by
  rw [mem_HA_iff]
  intro x
  apply Subtype.ext
  rw [sigmaA_apply_coe]
  exact σ.commutes ⟨(x : Ω), x.2⟩

/-- `sigmaA` together with its proof of membership in `H_A`. -/
noncomputable abbrev sigmaHat (R : FrobLevel ↥L.L Ω) (σ : Gal(Ω/↥L.L)) : ↥(HA M L hML R) :=
  ⟨sigmaA M L hML R σ, sigmaA_mem_HA M L hML R σ⟩

/-- The conjugate of `σ` by the chosen extension `thetaOf g`. -/
noncomputable abbrev alpha (g : Gal(↥L.L/↥M.L)) (σ : Gal(Ω/↥L.L)) : Gal(Ω/↥L.L) :=
  ringConjAlgEquiv L.L (thetaOf M L g) (thetaOf_mem M L g) σ

/-! ## Part D: `restrB ∘ convH` and the term comparison -/

/-- The composite `restrB ∘ convH` computed on elements: it is the restriction to `R` of the
automorphism of the auxiliary level. -/
theorem restrB_convH_apply_coe (R : FrobLevel ↥L.L Ω)
    (z : ↥(HA M L hML R)) (y : ↥R.L) :
    (((restrB M L hML R (convH M L hML R z)) y : ↥R.L) : Ω)
      = ((z.1 ⟨(y : Ω), le_auxA M L hML R y.2⟩ : ↥(auxA M L hML R).L) : Ω) := by
  rw [restrB_apply_coe, convH_applyAL]
  rfl

/-- The inverse of `thetaA` acts on elements by the inverse of `thetaOf`. -/
theorem thetaA_inv_apply_coe (R : FrobLevel ↥L.L Ω) (g : Gal(↥L.L/↥M.L))
    (x : ↥(auxA M L hML R).L) :
    ((((thetaA M L hML R g)⁻¹) x : ↥(auxA M L hML R).L) : Ω)
      = (thetaOf M L g)⁻¹ (x : Ω) := by
  have h1 : (thetaA M L hML R g)⁻¹
      = AlgEquiv.restrictNormalHom (F := ↥M.L) (K₁ := Ω) (auxA M L hML R).L
          (thetaM M L g)⁻¹ := by
    rw [show thetaA M L hML R g
        = AlgEquiv.restrictNormalHom (F := ↥M.L) (K₁ := Ω) (auxA M L hML R).L
            (thetaM M L g) from rfl, map_inv]
  rw [h1, AlgEquiv.restrictNormalHom_apply]
  rfl

/-- **The key term computation**: conjugating by the chosen lift `thetaA R g` and restricting to
`R` gives the conjugate action of `thetaOf g` on the restriction of `σ` to `R`. -/
theorem restrB_convH_conj_eq (R : FrobLevel ↥L.L Ω) (g : Gal(↥L.L/↥M.L)) (σ : Gal(Ω/↥L.L)) :
    restrB M L hML R (convH M L hML R
      ((MulAut.conjNormal (H := HA M L hML R) (thetaA M L hML R g))
        (sigmaHat M L hML R σ)))
      = AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) R.L
          (alpha M L g σ) := by
  set w : ↥(HA M L hML R) :=
    (MulAut.conjNormal (H := HA M L hML R) (thetaA M L hML R g))
      (sigmaHat M L hML R σ) with hwdef
  have hw : (w.1 : Gal(↥(auxA M L hML R).L/↥M.L))
      = thetaA M L hML R g * (sigmaA M L hML R σ) * (thetaA M L hML R g)⁻¹ := by
    rw [hwdef, MulAut.conjNormal_apply]
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  rw [restrB_convH_apply_coe M L hML R w y]
  conv_lhs => rw [hw]
  simp only [AlgEquiv.mul_apply]
  rw [thetaA_apply_coe, sigmaA_apply_coe, thetaA_inv_apply_coe]
  rw [AlgEquiv.restrictNormalHom_apply, ringConjAlgEquiv_apply]
  rfl


/-! ## Part E: the projection formulas -/

/-- The general base change of `galToGamma σ` at the auxiliary level is the class of `sigmaA`. -/
theorem proj_baseChange (R : FrobLevel ↥L.L Ω) (σ : Gal(Ω/↥L.L)) :
    Gamma.proj (AUX M L hML R)
      (generalBaseChange M (NumFieldIn.ofFrobLevel L) hML 2
        (galToGamma (K := ↥L.L) (K' := Ω) 2 σ))
      = ellComp 2 (Abelianization.of (sigmaA M L hML R σ)) := by
  rw [generalBaseChange_galToGamma M (NumFieldIn.ofFrobLevel L) hML 2 σ]
  rw [galToGamma_proj]
  rfl

/-- The projection at `R` of `ρ g` applied to `galToGamma σ` is the class of the conjugate of `σ`
by the chosen extension `thetaOf g`. -/
theorem proj_rho (ρ : Gal(↥L.L/ℚ) →* (Gamma ↥L.L Ω 2 ≃* Gamma ↥L.L Ω 2))
    (hρ : ∀ (τ : Gal(↥L.L/ℚ)) (θ : Ω ≃+* Ω) (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L)
      (hθτ : ∀ x : ↥L.L, θ (x : Ω) = ((τ x : ↥L.L) : Ω)),
      ρ τ = tauStar L.L 2 θ hθ)
    (R : FrobLevel ↥L.L Ω) (g : Gal(↥L.L/↥M.L)) (σ : Gal(Ω/↥L.L)) :
    Gamma.proj R (ρ (AlgEquiv.restrictScalars ℚ g) (galToGamma (K := ↥L.L) (K' := Ω) 2 σ))
      = ellComp 2 (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) R.L
          (alpha M L g σ))) := by
  rw [hρ (AlgEquiv.restrictScalars ℚ g) (thetaOf M L g) (thetaOf_mem M L g)
    (thetaOf_apply M L g)]
  rw [tauStar_galToGamma L.L 2 (thetaOf M L g) (thetaOf_mem M L g) σ]
  rw [show ringConjHom L.L (thetaOf M L g) (thetaOf_mem M L g) σ
      = alpha M L g σ from rfl]
  rw [galToGamma_proj]
  rfl

/-- **The right-hand side at the level `R`**, expanded as a product over the cosets of `H_A`. -/
theorem eps_baseChange_proj (R : FrobLevel ↥L.L Ω) (σ : Gal(Ω/↥L.L)) :
    eps M L hML R (Gamma.proj (AUX M L hML R)
      (generalBaseChange M (NumFieldIn.ofFrobLevel L) hML 2
        (galToGamma (K := ↥L.L) (K' := Ω) 2 σ)))
      = ∏ q : Gal(↥(auxA M L hML R).L/↥M.L) ⧸ HA M L hML R,
          ellComp 2 (Abelianization.of (restrB M L hML R (convH M L hML R
            ((MulAut.conjNormal (H := HA M L hML R) (Quotient.out q))
              (sigmaHat M L hML R σ))))) := by
  rw [show eps M L hML R = transferEll M L hML R from rfl]
  rw [proj_baseChange M L hML R σ, transferEll_apply]
  rw [ellComp_map 2 (W M L hML R) (Abelianization.of (sigmaA M L hML R σ))]
  rw [show Abelianization.of (sigmaA M L hML R σ)
      = Abelianization.map (HA M L hML R).subtype
          (Abelianization.of (sigmaHat M L hML R σ)) from
    (map_subtype_of_mk (HA M L hML R) _ _).symm]
  rw [show W M L hML R
        (Abelianization.map (HA M L hML R).subtype
          (Abelianization.of (sigmaHat M L hML R σ)))
      = Abelianization.map (restrB M L hML R)
          (Abelianization.map (convH M L hML R)
            (transferAb M L hML R
              (Abelianization.map (HA M L hML R).subtype
                (Abelianization.of (sigmaHat M L hML R σ)))))
      from rfl]
  rw [transferAb_norm M L hML R]
  rw [map_prod, map_prod, ellComp_prod]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  rw [Abelianization.map_of, Abelianization.map_of, Abelianization.map_of]
  rfl


/-- `resQ` on a chosen representative is `resQEquiv`. -/
theorem resQ_out (R : FrobLevel ↥L.L Ω)
    (q : Gal(↥(auxA M L hML R).L/↥M.L) ⧸ HA M L hML R) :
    resQ M L hML R (Quotient.out q) = resQEquiv M L hML R q := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [resQEquiv_mk]

/-- **The per-coset term comparison.**  For `u` an element of `Gal(AUX/M.L)` restricting to `g` on
`L.L`, the `u`-conjugate term of the transfer product equals the `g`-th term of the norm. -/
theorem term_eq (R : FrobLevel ↥L.L Ω) (g : Gal(↥L.L/↥M.L)) (σ : Gal(Ω/↥L.L))
    (u : Gal(↥(auxA M L hML R).L/↥M.L)) (hu : resQ M L hML R u = g) :
    ellComp 2 (Abelianization.of (restrB M L hML R (convH M L hML R
        ((MulAut.conjNormal (H := HA M L hML R) u)
          (sigmaHat M L hML R σ)))))
      = ellComp 2 (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) R.L
          (alpha M L g σ))) := by
  have hu' : u⁻¹ * thetaA M L hML R g ∈ HA M L hML R := by
    show resQ M L hML R (u⁻¹ * thetaA M L hML R g) = 1
    rw [map_mul, map_inv, hu, resQ_thetaA M L hML R g, inv_mul_cancel]
  have hstep : Abelianization.of ((MulAut.conjNormal (H := HA M L hML R) u)
        (sigmaHat M L hML R σ))
      = Abelianization.of ((MulAut.conjNormal (H := HA M L hML R) (thetaA M L hML R g))
        (sigmaHat M L hML R σ)) :=
    calc Abelianization.of ((MulAut.conjNormal (H := HA M L hML R) u)
          (sigmaHat M L hML R σ))
        = Abelianization.map ((MulAut.conjNormal (H := HA M L hML R) u :
              MulAut ↥(HA M L hML R)) : ↥(HA M L hML R) →* ↥(HA M L hML R))
            (Abelianization.of (sigmaHat M L hML R σ)) :=
          (Abelianization.map_of
            ((MulAut.conjNormal (H := HA M L hML R) u : MulAut ↥(HA M L hML R)) :
              ↥(HA M L hML R) →* ↥(HA M L hML R)) (sigmaHat M L hML R σ)).symm
      _ = Abelianization.map ((MulAut.conjNormal (H := HA M L hML R) (thetaA M L hML R g) :
              MulAut ↥(HA M L hML R)) : ↥(HA M L hML R) →* ↥(HA M L hML R))
            (Abelianization.of (sigmaHat M L hML R σ)) :=
          (DFunLike.congr_fun (abelianization_map_conjNormal_eq_of_mem (H := HA M L hML R) hu')
            (Abelianization.of (sigmaHat M L hML R σ))).symm
      _ = Abelianization.of ((MulAut.conjNormal (H := HA M L hML R) (thetaA M L hML R g))
          (sigmaHat M L hML R σ)) :=
          Abelianization.map_of
            ((MulAut.conjNormal (H := HA M L hML R) (thetaA M L hML R g) :
              MulAut ↥(HA M L hML R)) : ↥(HA M L hML R) →* ↥(HA M L hML R))
            (sigmaHat M L hML R σ)
  have hcongr : ∀ z : ↥(HA M L hML R),
      Abelianization.of (restrB M L hML R (convH M L hML R z))
        = Abelianization.map (restrB M L hML R)
            (Abelianization.map (convH M L hML R) (Abelianization.of z)) := by
    intro z
    rw [← Abelianization.map_of (restrB M L hML R) (convH M L hML R z),
      ← Abelianization.map_of (convH M L hML R) z]
  rw [hcongr, hstep, ← hcongr, restrB_convH_conj_eq M L hML R g σ]


/-! ## Part F: the norm–transfer identity at a finite level -/

/-- **The level form of the norm identity** (the mathematical content of the Verlagerung identity
`ver ∘ π = N`). -/
theorem norm_level_factor_b (ρ : Gal(↥L.L/ℚ) →* (Gamma ↥L.L Ω 2 ≃* Gamma ↥L.L Ω 2))
    (hρ : ∀ (τ : Gal(↥L.L/ℚ)) (θ : Ω ≃+* Ω) (hθ : ∀ x : Ω, x ∈ L.L ↔ θ x ∈ L.L)
      (hθτ : ∀ x : ↥L.L, θ (x : Ω) = ((τ x : ↥L.L) : Ω)),
      ρ τ = tauStar L.L 2 θ hθ)
    (R : FrobLevel ↥L.L Ω) (x : Gamma ↥L.L Ω 2) :
    Gamma.proj R (normEndo M L ρ x)
      = eps M L hML R (Gamma.proj (AUX M L hML R)
          (generalBaseChange M (NumFieldIn.ofFrobLevel L) hML 2 x)) := by
  obtain ⟨σ, rfl⟩ := galToGamma_surjective (K := ↥L.L) (K' := Ω) 2 x
  rw [normEndo_apply, map_prod, eps_baseChange_proj M L hML R σ]
  have hLHS : (∏ g : Gal(↥L.L/↥M.L), Gamma.proj R
        (ρ (AlgEquiv.restrictScalars ℚ g) (galToGamma (K := ↥L.L) (K' := Ω) 2 σ)))
      = ∏ g : Gal(↥L.L/↥M.L),
        ellComp 2 (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) R.L
          (alpha M L g σ))) :=
    Finset.prod_congr rfl (fun g _ => proj_rho M L ρ hρ R g σ)
  rw [hLHS]
  let e : Gal(↥L.L/↥M.L) ≃ (Gal(↥(auxA M L hML R).L/↥M.L) ⧸ HA M L hML R) :=
    (resQEquiv M L hML R).toEquiv.symm
  have hG : (∏ g : Gal(↥L.L/↥M.L),
        ellComp 2 (Abelianization.of (AlgEquiv.restrictNormalHom (F := ↥L.L) (K₁ := Ω) R.L
          (alpha M L g σ))))
      = ∏ g : Gal(↥L.L/↥M.L),
        ellComp 2 (Abelianization.of (restrB M L hML R (convH M L hML R
          ((MulAut.conjNormal (H := HA M L hML R) (Quotient.out (e g)))
            (sigmaHat M L hML R σ))))) := by
    refine Finset.prod_congr rfl (fun g _ => ?_)
    refine (term_eq M L hML R g σ (Quotient.out (e g)) ?_).symm
    rw [resQ_out M L hML R (e g)]
    exact Equiv.apply_symm_apply (resQEquiv M L hML R).toEquiv g
  rw [hG]
  exact Equiv.prod_comp e (fun q => ellComp 2 (Abelianization.of (restrB M L hML R
    (convH M L hML R ((MulAut.conjNormal (H := HA M L hML R) (Quotient.out q))
      (sigmaHat M L hML R σ))))))

end NormLevelB

end

end NK.NUV2.Transfer
