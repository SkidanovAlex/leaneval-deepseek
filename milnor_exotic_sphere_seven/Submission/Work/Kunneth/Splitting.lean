import Mathlib
import Submission.Work.Kunneth.Algebra
import Submission.Work.Cohomology.uctDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Splitting a chain complex of projectives with projective homology

Let `D` be a chain complex of `ℤ`-modules (indexed by `ℕ`) whose terms are all projective and
whose homology modules are all projective (over `ℤ` these are the free ones).  Then `D` is
homotopy equivalent to its `homSum` — the complex with `D`'s homology in each degree and zero
differentials.

The proof is the classical one: each short exact sequence
`0 → Zₙ → Dₙ → Bₙ₋₁ → 0` and `0 → Bₙ → Zₙ → Hₙ → 0` splits (the target is projective), so all
cycles and boundaries of `D` are projective, and choosing sections `τₙ : Bₙ → Dₙ₊₁`,
`σₙ : Hₙ → Zₙ` gives the projection `π`, the inclusion `ι` and an explicit chain homotopy
`π ≫ ι ≃ 𝟙` given by `hₙ = τₙ ∘ qₙ ∘ rZₙ`, where `qₙ` is the projection of the cycles onto the
boundaries along `im σₙ` and `rZₙ` is the retraction of `Dₙ` onto its cycles with kernel
`im τₙ₋₁`.

Main results:

* `Work.Kunneth.projective_cycles_boundaries` — every module of cycles and of boundaries of `D`
  is projective;
* `Work.Kunneth.piHom`, `Work.Kunneth.iotaHom` — the projection to the homology complex and the
  inclusion of the homology complex;
* `Work.Kunneth.iota_comp_pi`, `Work.Kunneth.homotopyData` — `ι ≫ π = 𝟙` and `π ≫ ι ≃ 𝟙`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Kunneth

noncomputable section

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

universe u

/-! ## The homology quotients of a complex with projective homology -/

/-- If `Hₖ` is projective then `Zₖ ⧸ Bₖ` is projective. -/
theorem projective_quot_cycles (E : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (k : ℕ)
    (h : Module.Projective ℤ (↥(E.homology k))) :
    Module.Projective ℤ (↥(Work.Cohomology.uctZ E k) ⧸ Work.Cohomology.uctH E k) := by
  obtain ⟨e⟩ := Work.Cohomology.homology_iso_H E k
  haveI := h
  exact Module.Projective.of_equiv' (Work.Cohomology.uctIsoToLinearEquiv e)

/-- The boundaries inside the cycles are the same as the boundaries. -/
noncomputable def uctHBEquiv (E : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ) :
    ↥(Work.Cohomology.uctH E n) ≃ₗ[ℤ] ↥(Work.Cohomology.uctB E n) where
  toFun x := ⟨(x : ↥(E.X n)), (Work.Cohomology.mem_uctH E n x).mp x.2⟩
  invFun b := ⟨⟨(b : ↥(E.X n)), Work.Cohomology.uctB_le_uctZ E n b.2⟩,
      (Work.Cohomology.mem_uctH E n _).mpr b.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv b := Subtype.ext rfl
  map_add' x y := by ext; simp [Submodule.coe_add]
  map_smul' c x := by ext; simp [Submodule.coe_smul, RingHom.id_apply]

/-- **Every cycle module and every boundary module is projective.** -/
theorem projective_cycles_boundaries (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    ∀ n, Module.Projective ℤ ↥(Work.Cohomology.uctZ D n) ∧
      Module.Projective ℤ ↥(Work.Cohomology.uctB D n) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  have hZ : Module.Projective ℤ ↥(Work.Cohomology.uctZ D n) := by
    rcases n with _ | m
    · rw [Work.Cohomology.uctZ_zero]
      haveI := hD 0
      exact Module.Projective.of_equiv' (Submodule.topEquiv (R := ℤ)).symm
    · have hBm : Module.Projective ℤ ↥(Work.Cohomology.uctB D m) := (ih m (by omega)).2
      obtain ⟨ρ, hρ⟩ := Work.Cohomology.exists_retraction_ker (D.d (m+1) m).hom hBm
      haveI := hD (m+1)
      exact Module.Projective.of_split (LinearMap.ker (D.d (m+1) m).hom).subtype ρ hρ
  have hB : Module.Projective ℤ ↥(Work.Cohomology.uctB D n) := by
    have hQ : Module.Projective ℤ (↥(Work.Cohomology.uctZ D n) ⧸ Work.Cohomology.uctH D n) :=
      projective_quot_cycles D n (hH n)
    obtain ⟨r, hr⟩ := Work.Cohomology.exists_retraction_onto_of_projective_quotient
      (Work.Cohomology.uctH D n) hQ
    have hHn : Module.Projective ℤ ↥(Work.Cohomology.uctH D n) :=
      Module.Projective.of_split (Work.Cohomology.uctH D n).subtype r hr
    exact Module.Projective.of_equiv' (uctHBEquiv D n)
  exact ⟨hZ, hB⟩

/-! ## Choosing the sections -/

/-- A section of `dₙ₊₁ : Dₙ₊₁ → Bₙ` over the boundaries. -/
theorem exists_section_boundary (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ∃ s : ↥(Work.Cohomology.uctB D n) →ₗ[ℤ] ↥(D.X (n+1)),
      ∀ b, (D.d (n+1) n).hom (s b) = (b : ↥(D.X n)) := by
  haveI := (projective_cycles_boundaries D hD hH n).2
  let k : ↥(D.X (n+1)) →ₗ[ℤ] ↥(Work.Cohomology.uctB D n) :=
    ((D.d (n+1) n).hom).codRestrict (Work.Cohomology.uctB D n) (fun x => ⟨x, rfl⟩)
  have hk : Function.Surjective k := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property k LinearMap.id hk
  refine ⟨s, fun b => ?_⟩
  have h1 : k (s b) = b := by
    have h2 := LinearMap.congr_fun hs b
    simpa using h2
  have h3 := congrArg Subtype.val h1
  simpa [k, LinearMap.codRestrict_apply] using h3

/-- The chosen section `τₙ : Bₙ → Dₙ₊₁` of `dₙ₊₁`. -/
noncomputable def secT (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥(Work.Cohomology.uctB D n) →ₗ[ℤ] ↥(D.X (n+1)) :=
  Classical.choose (exists_section_boundary D hD hH n)

theorem secT_spec (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (b : ↥(Work.Cohomology.uctB D n)) :
    (D.d (n+1) n).hom (secT D hD hH n b) = (b : ↥(D.X n)) :=
  Classical.choose_spec (exists_section_boundary D hD hH n) b

/-- A section of the quotient map `Zₙ → Hₙ`. -/
theorem exists_section_mkQ (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ∃ s : (↥(Work.Cohomology.uctZ D n) ⧸ Work.Cohomology.uctH D n) →ₗ[ℤ]
        ↥(Work.Cohomology.uctZ D n),
      ∀ y, (Work.Cohomology.uctH D n).mkQ (s y) = y := by
  haveI := projective_quot_cycles D n (hH n)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (Work.Cohomology.uctH D n).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  refine ⟨s, fun y => ?_⟩
  have h2 := LinearMap.congr_fun hs y
  simpa using h2

/-- The chosen section `σₙ : Hₙ → Zₙ`. -/
noncomputable def secσ (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    (↥(Work.Cohomology.uctZ D n) ⧸ Work.Cohomology.uctH D n) →ₗ[ℤ]
      ↥(Work.Cohomology.uctZ D n) :=
  Classical.choose (exists_section_mkQ D hD hH n)

theorem secσ_spec (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (y : ↥(Work.Cohomology.uctZ D n) ⧸ Work.Cohomology.uctH D n) :
    (Work.Cohomology.uctH D n).mkQ (secσ D hD hH n y) = y :=
  Classical.choose_spec (exists_section_mkQ D hD hH n) y

/-! ## `dx` as a boundary, and the retraction onto the cycles -/

/-- `dx`, viewed as an element of the boundaries `Bₙ = im (dₙ₊₁)`. -/
noncomputable def dB (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ) :
    ↥(D.X (n+1)) →ₗ[ℤ] ↥(Work.Cohomology.uctB D n) :=
  ((D.d (n+1) n).hom).codRestrict (Work.Cohomology.uctB D n) (fun x => ⟨x, rfl⟩)

theorem dB_coe (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ) (x : ↥(D.X (n+1))) :
    ((dB D n x : ↥(Work.Cohomology.uctB D n)) : ↥(D.X n)) = (D.d (n+1) n).hom x := by
  simp only [dB, LinearMap.codRestrict_apply]

theorem dB_mk (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ) (x : ↥(D.X (n+1))) :
    dB D n x = (⟨(D.d (n+1) n).hom x, ⟨x, rfl⟩⟩ : ↥(Work.Cohomology.uctB D n)) := by
  refine Subtype.ext ?_
  simp only [dB, LinearMap.codRestrict_apply]

theorem dB_eq_zero_of_mem (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (x : ↥(D.X (n+1))) (hx : (D.d (n+1) n).hom x = 0) : dB D n x = 0 := by
  refine Subtype.ext ?_
  rw [dB_coe, Submodule.coe_zero]
  exact hx

/-- The retraction of `Dₙ` onto its cycles whose kernel is `im τₙ₋₁`. -/
noncomputable def rZ (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    ∀ n, ↥(D.X n) →ₗ[ℤ] ↥(Work.Cohomology.uctZ D n)
  | 0 => LinearMap.codRestrict (Work.Cohomology.uctZ D 0)
      (LinearMap.id : ↥(D.X 0) →ₗ[ℤ] ↥(D.X 0))
      (fun x => by
        show (D.d 0 (0-1)).hom x = 0
        rw [HomologicalComplex.shape D 0 0 (by simp [ComplexShape.down]), ModuleCat.hom_zero,
          LinearMap.zero_apply])
  | n+1 => LinearMap.codRestrict (Work.Cohomology.uctZ D (n+1))
      ((LinearMap.id : ↥(D.X (n+1)) →ₗ[ℤ] ↥(D.X (n+1)))
        - (secT D hD hH n).comp (dB D n))
      (fun x => by
        show (D.d (n+1) n).hom (x - secT D hD hH n (dB D n x)) = 0
        rw [map_sub, secT_spec D hD hH n (dB D n x), dB_coe, sub_self])

theorem rZ_apply_of_mem (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (x : ↥(D.X n))
    (hx : x ∈ Work.Cohomology.uctZ D n) :
    ((rZ D hD hH n x : ↥(Work.Cohomology.uctZ D n)) : ↥(D.X n)) = x := by
  rcases n with _ | m
  · show ((LinearMap.codRestrict (Work.Cohomology.uctZ D 0)
      (LinearMap.id : ↥(D.X 0) →ₗ[ℤ] ↥(D.X 0)) _) x : ↥(D.X 0)) = x
    simp only [LinearMap.codRestrict_apply, LinearMap.id_apply, Subtype.coe_mk]
  · show x - secT D hD hH m (dB D m x) = x
    have hx' : (D.d (m+1) m).hom x = 0 := hx
    rw [dB_eq_zero_of_mem D m x hx', map_zero, sub_zero]

theorem rZ_subtype (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (z : ↥(Work.Cohomology.uctZ D n)) :
    rZ D hD hH n (z : ↥(D.X n)) = z :=
  Subtype.ext (rZ_apply_of_mem D hD hH n (z : ↥(D.X n)) z.2)

/-! ## The projection of the cycles onto the boundaries -/

/-- The projection of the cycles onto the boundaries along the chosen complement `im σₙ`. -/
noncomputable def qLin (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥(Work.Cohomology.uctZ D n) →ₗ[ℤ] ↥(Work.Cohomology.uctB D n) :=
  LinearMap.codRestrict (Work.Cohomology.uctB D n)
    (((Work.Cohomology.uctZ D n).subtype).comp
      ((LinearMap.id : ↥(Work.Cohomology.uctZ D n) →ₗ[ℤ] ↥(Work.Cohomology.uctZ D n))
        - (secσ D hD hH n).comp (Work.Cohomology.uctH D n).mkQ))
    (fun z => (Work.Cohomology.mem_uctH D n _).mp (by
      have h : (Work.Cohomology.uctH D n).mkQ
          (((LinearMap.id : ↥(Work.Cohomology.uctZ D n) →ₗ[ℤ] ↥(Work.Cohomology.uctZ D n))
            - (secσ D hD hH n).comp (Work.Cohomology.uctH D n).mkQ) z) = 0 := by
        rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
          secσ_spec D hD hH n ((Work.Cohomology.uctH D n).mkQ z), sub_self]
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h))

/-- A cycle whose underlying element is a boundary represents zero in `Hₙ = Zₙ ⧸ Bₙ`. -/
theorem mkQ_uctH_eq_zero_of_mem_uctB (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (x : ↥(Work.Cohomology.uctZ D n)) (hx : (x : ↥(D.X n)) ∈ Work.Cohomology.uctB D n) :
    (Work.Cohomology.uctH D n).mkQ x = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (Work.Cohomology.mem_uctH D n x).mpr hx

theorem qLin_apply (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (z : ↥(Work.Cohomology.uctZ D n)) :
    ((qLin D hD hH n z : ↥(Work.Cohomology.uctB D n)) : ↥(D.X n))
      = (z : ↥(D.X n))
        - ((secσ D hD hH n ((Work.Cohomology.uctH D n).mkQ z) : ↥(Work.Cohomology.uctZ D n))
            : ↥(D.X n)) := by
  show ((((LinearMap.id : ↥(Work.Cohomology.uctZ D n) →ₗ[ℤ] ↥(Work.Cohomology.uctZ D n))
      - (secσ D hD hH n).comp (Work.Cohomology.uctH D n).mkQ) z
        : ↥(Work.Cohomology.uctZ D n)) : ↥(D.X n)) = _
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
  simp only [Submodule.coe_sub]

theorem qLin_apply_boundary (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (b : ↥(Work.Cohomology.uctB D n)) :
    qLin D hD hH n ⟨(b : ↥(D.X n)), Work.Cohomology.uctB_le_uctZ D n b.2⟩ = b := by
  refine Subtype.ext ?_
  rw [qLin_apply]
  have hz : (Work.Cohomology.uctH D n).mkQ
      ⟨(b : ↥(D.X n)), Work.Cohomology.uctB_le_uctZ D n b.2⟩ = 0 :=
    mkQ_uctH_eq_zero_of_mem_uctB D hD hH n _ b.2
  rw [hz, map_zero, Submodule.coe_zero, sub_zero]

/-! ## The homotopy components -/

/-- The `n`-th component of the chain homotopy: `hₙ = τₙ ∘ qₙ ∘ rZₙ`. -/
noncomputable def hLin (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥(D.X n) →ₗ[ℤ] ↥(D.X (n+1)) :=
  (secT D hD hH n).comp ((qLin D hD hH n).comp (rZ D hD hH n))

theorem hLin_apply (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (x : ↥(D.X n)) :
    (D.d (n+1) n).hom (hLin D hD hH n x)
      = ((qLin D hD hH n (rZ D hD hH n x) : ↥(Work.Cohomology.uctB D n))
          : ↥(D.X n)) := by
  show (D.d (n+1) n).hom
    (secT D hD hH n ((qLin D hD hH n).comp (rZ D hD hH n) x)) = _
  rw [LinearMap.comp_apply, secT_spec D hD hH n (qLin D hD hH n (rZ D hD hH n x))]

theorem hLin_apply_of_boundary (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (y : ↥(D.X (n+1))) :
    hLin D hD hH n ((D.d (n+1) n).hom y) = secT D hD hH n (dB D n y) := by
  have hcyc : (D.d (n+1) n).hom y ∈ Work.Cohomology.uctZ D n := by
    show (D.d n (n-1)).hom ((D.d (n+1) n).hom y) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d D (n+1) n (n-1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h y
  show secT D hD hH n
    ((qLin D hD hH n).comp (rZ D hD hH n) ((D.d (n+1) n).hom y)) = _
  rw [LinearMap.comp_apply,
    show rZ D hD hH n ((D.d (n+1) n).hom y) = ⟨(D.d (n+1) n).hom y, hcyc⟩ from
      rZ_subtype D hD hH n ⟨(D.d (n+1) n).hom y, hcyc⟩,
    show qLin D hD hH n ⟨(D.d (n+1) n).hom y, hcyc⟩ = dB D n y from by
      rw [dB_mk D n y]
      exact qLin_apply_boundary D hD hH n ⟨(D.d (n+1) n).hom y, ⟨y, rfl⟩⟩]

/-! ## The projection to homology and the inclusion of homology -/

/-- The comparison isomorphism `Hₙ ≅ Zₙ ⧸ Bₙ`. -/
noncomputable def hIso (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ) :
    D.homology n ≅ ModuleCat.of ℤ (↥(Work.Cohomology.uctZ D n) ⧸ Work.Cohomology.uctH D n) :=
  Classical.choice (Work.Cohomology.homology_iso_H D n)

theorem hIso_hom_inv (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ)
    (y : (↥(Work.Cohomology.uctZ D n) ⧸ Work.Cohomology.uctH D n)) :
    (hIso D n).hom.hom ((hIso D n).inv.hom y) = y := by
  have h1 : ((hIso D n).hom.hom).comp ((hIso D n).inv.hom) = LinearMap.id := by
    rw [← ModuleCat.hom_comp (hIso D n).inv (hIso D n).hom, Iso.inv_hom_id, ModuleCat.hom_id]
  exact LinearMap.congr_fun h1 y

theorem hIso_inv_hom (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ) (n : ℕ) (y : ↥(D.homology n)) :
    (hIso D n).inv.hom ((hIso D n).hom.hom y) = y := by
  have h1 : ((hIso D n).inv.hom).comp ((hIso D n).hom.hom) = LinearMap.id := by
    rw [← ModuleCat.hom_comp (hIso D n).hom (hIso D n).inv, Iso.hom_inv_id, ModuleCat.hom_id]
  exact LinearMap.congr_fun h1 y

/-- The projection `Dₙ → Hₙ`. -/
noncomputable def piLin (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥(D.X n) →ₗ[ℤ] ↥(D.homology n) :=
  ((hIso D n).inv.hom).comp ((Work.Cohomology.uctH D n).mkQ.comp (rZ D hD hH n))

/-- The inclusion `Hₙ → Dₙ`. -/
noncomputable def iotaLin (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    ↥(D.homology n) →ₗ[ℤ] ↥(D.X n) :=
  ((Work.Cohomology.uctZ D n).subtype).comp ((secσ D hD hH n).comp ((hIso D n).hom.hom))

/-- The projection kills boundaries, so it is a chain map. -/
theorem piLin_d_eq_zero (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (y : ↥(D.X (n+1))) :
    piLin D hD hH n ((D.d (n+1) n).hom y) = 0 := by
  have hcyc : (D.d (n+1) n).hom y ∈ Work.Cohomology.uctZ D n := by
    show (D.d n (n-1)).hom ((D.d (n+1) n).hom y) = 0
    have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_d D (n+1) n (n-1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h y
  show (hIso D n).inv.hom
    ((Work.Cohomology.uctH D n).mkQ (rZ D hD hH n ((D.d (n+1) n).hom y))) = 0
  rw [show rZ D hD hH n ((D.d (n+1) n).hom y)
        = ⟨(D.d (n+1) n).hom y, hcyc⟩ from
      rZ_subtype D hD hH n ⟨(D.d (n+1) n).hom y, hcyc⟩]
  rw [mkQ_uctH_eq_zero_of_mem_uctB D hD hH n _ ⟨y, rfl⟩, map_zero]

/-- The composite `ι ∘ π` on elements. -/
theorem iota_pi_apply (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (x : ↥(D.X n)) :
    iotaLin D hD hH n (piLin D hD hH n x)
      = ((secσ D hD hH n ((Work.Cohomology.uctH D n).mkQ (rZ D hD hH n x))
          : ↥(Work.Cohomology.uctZ D n)) : ↥(D.X n)) := by
  show ((secσ D hD hH n ((hIso D n).hom.hom ((hIso D n).inv.hom
    ((Work.Cohomology.uctH D n).mkQ (rZ D hD hH n x)))) : ↥(Work.Cohomology.uctZ D n))
      : ↥(D.X n)) = _
  rw [hIso_hom_inv]

/-- The composite `π ∘ ι` is the identity on homology. -/
theorem piLin_iotaLin (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (y : ↥(D.homology n)) :
    piLin D hD hH n (iotaLin D hD hH n y) = y := by
  show (hIso D n).inv.hom ((Work.Cohomology.uctH D n).mkQ (rZ D hD hH n
    ((secσ D hD hH n ((hIso D n).hom.hom y) : ↥(Work.Cohomology.uctZ D n))
      : ↥(D.X n)))) = y
  rw [rZ_subtype D hD hH n (secσ D hD hH n ((hIso D n).hom.hom y)),
    secσ_spec D hD hH n ((hIso D n).hom.hom y), hIso_inv_hom]

/-- The inclusion lands in cycles. -/
theorem d_iotaLin (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) (y : ↥(D.homology n)) :
    (D.d n (n-1)).hom (iotaLin D hD hH n y) = 0 := by
  show (D.d n (n-1)).hom
    ((secσ D hD hH n ((hIso D n).hom.hom y) : ↥(Work.Cohomology.uctZ D n))
      : ↥(D.X n)) = 0
  exact (secσ D hD hH n ((hIso D n).hom.hom y)).2

/-! ## The chain maps -/

/-- The projection `D ⟶ homSum D`. -/
noncomputable def piHom (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) : D ⟶ Work.Kunneth.homSum D where
  f n := ModuleCat.ofHom (piLin D hD hH n)
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
    exact piLin_d_eq_zero D hD hH j x

theorem piHom_f (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    (piHom D hD hH).f n = ModuleCat.ofHom (piLin D hD hH n) := rfl

/-- The inclusion `homSum D ⟶ D`. -/
noncomputable def iotaHom (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) : Work.Kunneth.homSum D ⟶ D where
  f n := ModuleCat.ofHom (iotaLin D hD hH n)
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    have hd0 : (Work.Kunneth.homSum D).d (j+1) j = 0 :=
      Work.Kunneth.sumShift_d (fun q => D.homology q) j
    rw [hd0, zero_comp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact d_iotaLin D hD hH (j+1) x

theorem iotaHom_f (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ) :
    (iotaHom D hD hH).f n = ModuleCat.ofHom (iotaLin D hD hH n) := rfl

theorem iota_comp_pi_apply (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (n : ℕ)
    (y : ↥((Work.Kunneth.homSum D).X n)) :
    ((iotaHom D hD hH ≫ piHom D hD hH).f n).hom y = y := by
  rw [comp_f, iotaHom_f, piHom_f, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ModuleCat.hom_ofHom]
  exact piLin_iotaLin D hD hH n y

theorem iota_comp_pi (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    iotaHom D hD hH ≫ piHom D hD hH = 𝟙 (Work.Kunneth.homSum D) := by
  apply HomologicalComplex.Hom.ext
  funext n
  rw [id_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rw [ModuleCat.hom_id]
  exact iota_comp_pi_apply D hD hH n y

/-! ## The chain homotopy -/

/-- The degreewise components of the homotopy, extended by zero off the shift. -/
noncomputable def homFn (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (i j : ℕ) : D.X i ⟶ D.X j :=
  if h : i + 1 = j then
    ModuleCat.ofHom (-(hLin D hD hH i)) ≫ eqToHom (congrArg D.X h)
  else 0

theorem homFn_apply_self (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (k : ℕ) :
    homFn D hD hH k (k+1) = ModuleCat.ofHom (-(hLin D hD hH k)) := by
  rw [homFn, dif_pos (rfl : k + 1 = k + 1), CategoryTheory.eqToHom_refl, Category.comp_id]

/-- The homotopy identity in degree `0`. -/
theorem hLin_identity_zero (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (x : ↥(D.X 0)) :
    (D.d 1 0).hom (hLin D hD hH 0 x) = x - iotaLin D hD hH 0 (piLin D hD hH 0 x) := by
  rw [hLin_apply D hD hH 0 x, iota_pi_apply D hD hH 0 x,
    qLin_apply D hD hH 0 (rZ D hD hH 0 x)]
  have hz : ((rZ D hD hH 0 x : ↥(Work.Cohomology.uctZ D 0)) : ↥(D.X 0)) = x :=
    rZ_apply_of_mem D hD hH 0 x (by rw [Work.Cohomology.uctZ_zero]; trivial)
  rw [hz]

/-- The homotopy identity in positive degrees. -/
theorem hLin_identity_succ (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (m : ℕ) (x : ↥(D.X (m+1))) :
    (D.d (m+2) (m+1)).hom (hLin D hD hH (m+1) x)
        + hLin D hD hH m ((D.d (m+1) m).hom x)
      = x - iotaLin D hD hH (m+1) (piLin D hD hH (m+1) x) := by
  rw [hLin_apply D hD hH (m+1) x, hLin_apply_of_boundary D hD hH m x,
    iota_pi_apply D hD hH (m+1) x, qLin_apply D hD hH (m+1) (rZ D hD hH (m+1) x)]
  have hz : ((rZ D hD hH (m+1) x : ↥(Work.Cohomology.uctZ D (m+1))) : ↥(D.X (m+1)))
      = x - secT D hD hH m (dB D m x) := by
    show x - secT D hD hH m (dB D m x) = _
    rfl
  rw [hz]
  abel

theorem comm_identity (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (k : ℕ) (x : ↥(D.X k)) :
    (dNext k (homFn D hD hH)).hom x + (prevD k (homFn D hD hH)).hom x
      = iotaLin D hD hH k (piLin D hD hH k x) - x := by
  rcases k with _ | m
  · rw [dNext_nat D D 0 (homFn D hD hH),
      prevD_eq (homFn D hD hH) (show (ComplexShape.down ℕ).Rel 1 0 from rfl)]
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    rw [show (0:ℕ) - 1 = 0 from rfl,
      show homFn D hD hH 0 0 = 0 from dif_neg (by omega),
      show homFn D hD hH 0 1 = ModuleCat.ofHom (-(hLin D hD hH 0)) from
        homFn_apply_self D hD hH 0]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, ModuleCat.hom_ofHom, LinearMap.neg_apply,
      map_neg, hLin_identity_zero D hD hH x]
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
    have hx : iotaLin D hD hH (m+1) (piLin D hD hH (m+1) x) - x
        = -((D.d (m+2) (m+1)).hom (hLin D hD hH (m+1) x)
            + (hLin D hD hH m) ((D.d (m+1) m) x)) := by
      rw [hLin_identity_succ D hD hH m x]
      abel
    rw [hx]
    abel

theorem comm_morphism (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) (k : ℕ) :
    dNext k (homFn D hD hH) + prevD k (homFn D hD hH)
      = (piHom D hD hH ≫ iotaHom D hD hH).f k - 𝟙 (D.X k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rw [ModuleCat.hom_add, ModuleCat.hom_sub, comp_f, piHom_f, iotaHom_f, ModuleCat.hom_comp,
    ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_id, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.id_apply]
  exact comm_identity D hD hH k x

/-- The chain homotopy `π ≫ ι ≃ 𝟙`. -/
noncomputable def homotopyData (D : ChainComplex (ModuleCat.{u,0} ℤ) ℕ)
    (hD : ∀ q, Module.Projective ℤ ↥(D.X q))
    (hH : ∀ q, Module.Projective ℤ ↥(D.homology q)) :
    Homotopy (piHom D hD hH ≫ iotaHom D hD hH) (𝟙 D) where
  hom := homFn D hD hH
  zero i j hij := by
    dsimp only [homFn]
    exact dif_neg hij
  comm i := by
    rw [id_f, comm_morphism D hD hH i]
    abel

end

end Work.Kunneth
