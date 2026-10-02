import Mathlib
import Submission.Work.Kunneth.HomValue
import Submission.Work.Kunneth.Splitting
import Submission.Work.Kunneth.exists_splitting

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A *transparent* splitting of a chain complex of projectives

`Work.Kunneth.exists_splitting` produces maps `π : D ⟶ homSum D`, `ι : homSum D ⟶ D` with
`ι ≫ π = 𝟙` and `π ≫ ι ≃ 𝟙` for a chain complex `D` of `ℤ`-modules whose terms and homology
modules are projective.  For the Künneth theorem one needs a *little more*: the projection `π`
must send the homology class of a cycle to the class of that cycle, i.e.

`(π.f q) ((D.iCycles q) v) = (D.homologyπ q) v`

for every cycle `v` of `D` in degree `q`.

The projection of `Work.Kunneth.Splitting` is `π_q = e⁻¹ ∘ mkQ ∘ rZ`, where `e : H_q ≅ Z_q ⧸ B_q`
is an isomorphism produced by `Classical.choice`.  As the isomorphism chosen by `Classical.choice`
is opaque, the transparency identity cannot be deduced from the generic statement; instead we
choose the *explicit* isomorphism `Work.Kunneth.homQuotIso` and use the concrete description
`Z_q → H_q` given by `homologyπ ∘ cycIso⁻¹`.  Every construction of `Splitting.lean` that does not
involve the isomorphism (`rZ`, `secT`, `secσ`, `qLin`, `hLin`, `homFn`) is reused verbatim; only
the four lemmas that mention `π` and `ι` are redone.

## Main result

* `Work.Kunneth.exists_splitting_transparent` — the splitting, with a transparent `π`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

universe u

/-! ## The transparent projection and inclusion -/

/-- **The transparent projection to homology**, degree by degree: a chain `x` is first projected
onto its cycles (`rZ`), the cycle so obtained is viewed as an element of `D.cycles n` (`cycIso`),
and then its homology class is taken (`homologyπ`). -/
noncomputable def piLinT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥(D.X n) →ₗ[ℤ] ↥(D.homology n) :=
  ((D.homologyπ n).hom).comp (((cycIso D n).inv.hom).comp (rZ D hD hH n))

/-- **The inclusion of homology**, degree by degree: a homology class is represented in
`Zₙ ⧸ Bₙ` (`homQuotIso`), the representative cycle is chosen by `secσ`, and it is viewed as an
element of `D.X n`. -/
noncomputable def iotaLinT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥(D.homology n) →ₗ[ℤ] ↥(D.X n) :=
  ((Work.Cohomology.uctZ D n).subtype).comp
    ((secσ D hD hH n).comp ((homQuotIso D n).hom.hom))

theorem piLinT_apply (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (x : ↥(D.X n)) :
    piLinT D hD hH n x
      = (D.homologyπ n).hom ((cycIso D n).inv.hom (rZ D hD hH n x)) := rfl

/-! ## Elementary properties of the cycle projection -/

/-- On a cycle, `rZ` is the identity (through the identification `cycIso` of `Zₙ` with the cycles
of `D`). -/
theorem rZ_iCycles (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (v : ↥(D.cycles n)) :
    rZ D hD hH n ((D.iCycles n).hom v) = (cycIso D n).hom v := by
  have hmem : (D.iCycles n).hom v ∈ Work.Cohomology.uctZ D n := by
    show (D.d n (n-1)).hom ((D.iCycles n).hom v) = 0
    have h := congrArg (fun (m : D.cycles n ⟶ D.X (n-1)) => ModuleCat.Hom.hom m v)
      (HomologicalComplex.iCycles_d D n (n-1))
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero, LinearMap.comp_apply,
      LinearMap.zero_apply] using h
  apply Subtype.ext
  rw [rZ_apply_of_mem D hD hH n _ hmem]
  exact (cycIso_hom_val D n v).symm

/-- **The computation rule for the canonical description of homology**: the class of the cycle
`cycIso⁻¹ z` is `homQuotIso⁻¹` of the class of `z` in `Zₙ ⧸ Bₙ`. -/
theorem homologyπ_cycIso_inv (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (z : ↥(cycKer D n)) :
    (D.homologyπ n).hom ((cycIso D n).inv.hom z)
      = (homQuotIso D n).inv.hom ((homBnd D n).mkQ z) := by
  have h := homQuotIso_apply D n ((cycIso D n).inv.hom z)
  rw [homIso_hom_apply (cycIso D n) z] at h
  rw [← h, homIso_inv_apply]

/-! ## The projection and the inclusion -/

/-- The projection `π` kills boundaries, so it is a chain map. -/
theorem piLinT_d_eq_zero (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (y : ↥(D.X (n+1))) :
    piLinT D hD hH n ((D.d (n+1) n).hom y) = 0 := by
  have hcyc : (D.d (n+1) n).hom y ∈ Work.Cohomology.uctZ D n := by
    show (D.d n (n-1)).hom ((D.d (n+1) n).hom y) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d D (n+1) n (n-1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h y
  show (D.homologyπ n).hom
    ((cycIso D n).inv.hom (rZ D hD hH n ((D.d (n+1) n).hom y))) = 0
  rw [show rZ D hD hH n ((D.d (n+1) n).hom y) = ⟨(D.d (n+1) n).hom y, hcyc⟩ from
      rZ_subtype D hD hH n ⟨(D.d (n+1) n).hom y, hcyc⟩]
  rw [homologyπ_cycIso_inv D n ⟨(D.d (n+1) n).hom y, hcyc⟩]
  rw [show (homBnd D n).mkQ ⟨(D.d (n+1) n).hom y, hcyc⟩ = 0 from
    mkQ_uctH_eq_zero_of_mem_uctB D hD hH n _ ⟨y, rfl⟩]
  exact map_zero _

/-- **Transparency**: the projection sends the class of a cycle to the class of that cycle. -/
theorem piLinT_iCycles (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (v : ↥(D.cycles n)) :
    piLinT D hD hH n ((D.iCycles n).hom v) = (D.homologyπ n).hom v := by
  show (D.homologyπ n).hom ((cycIso D n).inv.hom (rZ D hD hH n ((D.iCycles n).hom v)))
    = (D.homologyπ n).hom v
  rw [rZ_iCycles D hD hH n v, homIso_inv_apply]

/-- The inclusion lands in the cycles. -/
theorem d_iotaLinT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (y : ↥(D.homology n)) :
    (D.d n (n-1)).hom (iotaLinT D hD hH n y) = 0 := by
  show (D.d n (n-1)).hom
    ((secσ D hD hH n ((homQuotIso D n).hom.hom y) : ↥(Work.Cohomology.uctZ D n))
      : ↥(D.X n)) = 0
  exact (secσ D hD hH n ((homQuotIso D n).hom.hom y)).2

/-- The composite `π ∘ ι` is the identity on homology. -/
theorem piLinT_iotaLinT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (y : ↥(D.homology n)) :
    piLinT D hD hH n (iotaLinT D hD hH n y) = y := by
  show (D.homologyπ n).hom ((cycIso D n).inv.hom (rZ D hD hH n
    ((secσ D hD hH n ((homQuotIso D n).hom.hom y) : ↥(Work.Cohomology.uctZ D n))
      : ↥(D.X n)))) = y
  rw [rZ_subtype D hD hH n (secσ D hD hH n ((homQuotIso D n).hom.hom y))]
  rw [homologyπ_cycIso_inv D n (secσ D hD hH n ((homQuotIso D n).hom.hom y))]
  rw [show (homBnd D n).mkQ (secσ D hD hH n ((homQuotIso D n).hom.hom y))
      = (homQuotIso D n).hom.hom y from secσ_spec D hD hH n _]
  exact homIso_inv_apply (homQuotIso D n) y

/-- The rule computing `π` of a class in terms of the chosen section `σ` of `Zₙ → Hₙ`. -/
theorem homQuotIso_piLinT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (x : ↥(D.X n)) :
    (homQuotIso D n).hom.hom (piLinT D hD hH n x)
      = (homBnd D n).mkQ (rZ D hD hH n x) := by
  show (homQuotIso D n).hom.hom
      ((D.homologyπ n).hom ((cycIso D n).inv.hom (rZ D hD hH n x))) = _
  have h := homQuotIso_apply D n ((cycIso D n).inv.hom (rZ D hD hH n x))
  rw [homIso_hom_apply (cycIso D n) (rZ D hD hH n x)] at h
  exact h

/-- The composite `ι ∘ π` on elements. -/
theorem iota_pi_applyT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (x : ↥(D.X n)) :
    iotaLinT D hD hH n (piLinT D hD hH n x)
      = ((secσ D hD hH n ((Work.Cohomology.uctH D n).mkQ (rZ D hD hH n x))
          : ↥(Work.Cohomology.uctZ D n)) : ↥(D.X n)) := by
  show ((secσ D hD hH n ((homQuotIso D n).hom.hom (piLinT D hD hH n x))
      : ↥(Work.Cohomology.uctZ D n)) : ↥(D.X n)) = _
  rw [homQuotIso_piLinT D hD hH n x]
  rfl

/-! ## The chain maps -/

/-- The transparent projection `D ⟶ homSum D`. -/
noncomputable def piHomT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) : D ⟶ Work.Kunneth.homSum D where
  f n := ModuleCat.ofHom (piLinT D hD hH n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    have hd0 : (Work.Kunneth.homSum D).d (j+1) j = 0 :=
      Work.Kunneth.sumShift_d (fun q => D.homology q) j
    rw [hd0, comp_zero]
    symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact piLinT_d_eq_zero D hD hH j x

/-- The transparent inclusion `homSum D ⟶ D`. -/
noncomputable def iotaHomT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) : Work.Kunneth.homSum D ⟶ D where
  f n := ModuleCat.ofHom (iotaLinT D hD hH n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    have hd0 : (Work.Kunneth.homSum D).d (j+1) j = 0 :=
      Work.Kunneth.sumShift_d (fun q => D.homology q) j
    rw [hd0, zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact d_iotaLinT D hD hH (j+1) x

theorem piHomT_f (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    (piHomT D hD hH).f n = ModuleCat.ofHom (piLinT D hD hH n) := rfl

theorem iotaHomT_f (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    (iotaHomT D hD hH).f n = ModuleCat.ofHom (iotaLinT D hD hH n) := rfl

theorem iota_comp_piT_apply (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (y : ↥((Work.Kunneth.homSum D).X n)) :
    ((iotaHomT D hD hH ≫ piHomT D hD hH).f n).hom y = y := by
  rw [comp_f, iotaHomT_f, piHomT_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ModuleCat.hom_ofHom]
  exact piLinT_iotaLinT D hD hH n y

theorem iota_comp_piT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    iotaHomT D hD hH ≫ piHomT D hD hH = 𝟙 (Work.Kunneth.homSum D) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [id_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [ModuleCat.hom_id]
  exact iota_comp_piT_apply D hD hH n y

/-! ## The chain homotopy -/

/-- The homotopy identity in degree `0`. -/
theorem hLin_identity_zeroT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (x : ↥(D.X 0)) :
    (D.d 1 0).hom (hLin D hD hH 0 x) = x - iotaLinT D hD hH 0 (piLinT D hD hH 0 x) := by
  rw [hLin_apply D hD hH 0 x, iota_pi_applyT D hD hH 0 x,
    qLin_apply D hD hH 0 (rZ D hD hH 0 x)]
  have hz : ((rZ D hD hH 0 x : ↥(Work.Cohomology.uctZ D 0)) : ↥(D.X 0)) = x :=
    rZ_apply_of_mem D hD hH 0 x (by rw [Work.Cohomology.uctZ_zero]; trivial)
  rw [hz]

/-- The homotopy identity in positive degrees. -/
theorem hLin_identity_succT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (m : ℕ) (x : ↥(D.X (m+1))) :
    (D.d (m+2) (m+1)).hom (hLin D hD hH (m+1) x)
        + hLin D hD hH m ((D.d (m+1) m).hom x)
      = x - iotaLinT D hD hH (m+1) (piLinT D hD hH (m+1) x) := by
  rw [hLin_apply D hD hH (m+1) x, hLin_apply_of_boundary D hD hH m x,
    iota_pi_applyT D hD hH (m+1) x, qLin_apply D hD hH (m+1) (rZ D hD hH (m+1) x)]
  have hz : ((rZ D hD hH (m+1) x : ↥(Work.Cohomology.uctZ D (m+1))) : ↥(D.X (m+1)))
      = x - secT D hD hH m (dB D m x) := by
    show x - secT D hD hH m (dB D m x) = _
    rfl
  rw [hz]
  abel

theorem comm_identityT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (k : ℕ) (x : ↥(D.X k)) :
    (dNext k (homFn D hD hH)).hom x + (prevD k (homFn D hD hH)).hom x
      = iotaLinT D hD hH k (piLinT D hD hH k x) - x := by
  rcases k with _ | m
  · rw [dNext_nat D D 0 (homFn D hD hH),
      prevD_eq (homFn D hD hH) (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [show (0:ℕ) - 1 = 0 from rfl,
      show homFn D hD hH 0 0 = 0 from dif_neg (by omega),
      show homFn D hD hH 0 1 = ModuleCat.ofHom (-(hLin D hD hH 0)) from
        homFn_apply_self D hD hH 0]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, ModuleCat.hom_ofHom, LinearMap.neg_apply,
      map_neg, hLin_identity_zeroT D hD hH x]
    abel
  · rw [dNext_nat D D (m+1) (homFn D hD hH),
      prevD_eq (homFn D hD hH) (show (ComplexShape.down ℕ).Rel (m+2) (m+1) from rfl)]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [show m + 1 - 1 = m from Nat.succ_sub_one m,
      show homFn D hD hH m (m+1) = ModuleCat.ofHom (-(hLin D hD hH m)) from
        homFn_apply_self D hD hH m,
      show homFn D hD hH (m+1) (m+2) = ModuleCat.ofHom (-(hLin D hD hH (m+1))) from
        homFn_apply_self D hD hH (m+1)]
    simp only [ModuleCat.hom_ofHom, LinearMap.neg_apply, map_neg]
    have hx : iotaLinT D hD hH (m+1) (piLinT D hD hH (m+1) x) - x
        = -((D.d (m+2) (m+1)).hom (hLin D hD hH (m+1) x)
            + (hLin D hD hH m) ((D.d (m+1) m) x)) := by
      rw [hLin_identity_succT D hD hH m x]
      abel
    rw [hx]
    abel

theorem comm_morphismT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (k : ℕ) :
    dNext k (homFn D hD hH) + prevD k (homFn D hD hH)
      = (piHomT D hD hH ≫ iotaHomT D hD hH).f k - 𝟙 (D.X k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_add, ModuleCat.hom_sub, comp_f, piHomT_f, iotaHomT_f, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  exact comm_identityT D hD hH k x

/-- The chain homotopy `π ≫ ι ≃ 𝟙`. -/
noncomputable def homotopyDataT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    Homotopy (piHomT D hD hH ≫ iotaHomT D hD hH) (𝟙 D) where
  hom := homFn D hD hH
  zero i j hij := by
    dsimp only [homFn]
    exact dif_neg hij
  comm i := by
    rw [id_f, comm_morphismT D hD hH i]
    abel

/-! ## The splitting -/

/-- **A chain complex of projective `ℤ`-modules with projective homology splits, with a projection
that is transparent on cycles.**  There are maps `π : D ⟶ homSum D` and `ι : homSum D ⟶ D` with
`ι ≫ π = 𝟙`, `π ≫ ι ≃ 𝟙`, and `π` sends the class of every cycle to the class of that cycle. -/
theorem exists_splitting_transparent (D : ChainComplex (ModuleCat ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    ∃ (π : D ⟶ Work.Kunneth.homSum D) (ι : Work.Kunneth.homSum D ⟶ D),
      CategoryTheory.CategoryStruct.comp ι π = CategoryTheory.CategoryStruct.id (Work.Kunneth.homSum D) ∧
      Nonempty (Homotopy (CategoryTheory.CategoryStruct.comp π ι)
        (CategoryTheory.CategoryStruct.id D)) ∧
      (∀ (q : ℕ) (v : ↥(D.cycles q)),
        (π.f q).hom ((D.iCycles q).hom v) = (D.homologyπ q).hom v) :=
  ⟨piHomT D hD hH, iotaHomT D hD hH, iota_comp_piT D hD hH, ⟨homotopyDataT D hD hH⟩,
    fun q v => piLinT_iCycles D hD hH q v⟩

end

end Work.Kunneth
