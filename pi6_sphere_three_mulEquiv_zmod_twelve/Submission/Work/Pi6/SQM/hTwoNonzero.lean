import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.Cohomology.kronH_bijective_field
import Submission.Work.Stems.HurewiczFirstDegree

/-! Guidance from the project lead (the requester):

SQM piece (small). NOTES_LEAD_SQM §5 last paragraph. X a K(ℤ/2,2) range model through N ≥ 3: X is simply connected,
Work.Stems.hurewicz_first_degree 2 gives H₂(X;ℤ) ≅ π₂ ≅ ℤ/2; a cycle c representing the generator stays nonzero mod 2
(if c ≡ ∂e mod 2 then c = ∂ẽ + 2c', so [c] = 2[c'] = 0); field duality (kronH_bijective_field) gives a nonzero class in
H²(X;𝔽₂). If area BOCK (Pi6/BOCK/bocksteinLES) is proved first you may use its exactness instead.

## How it is proved here (and why)

Write `K = chZ X` for the integral singular chain complex of `X` and `S = bockSES 2 X` for the short
complex `0 → K ⊗ ℤ --·2--> K ⊗ ℤ --red--> K ⊗ ℤ/2 → 0` of `Work.Pi6.EMZ.BocksteinCore` (get it from
the coefficient short exact sequence `0 → ℤ --·2--> ℤ --red--> ℤ/2 → 0`, tensored with the
degreewise free complex `K`).  The first map of `S` is *literally* `2 • 𝟙`, so it induces `2 • 𝟙` on
homology (`homologyMap_smul_id`, additivity of the homology functor), which is `0` because `H₂(X;ℤ)`
is `2`-torsion; exactness at the middle term of the homology sequence
(`ShortComplex.ShortExact.homology_exact₂`) then makes the reduction map
`red : H₂(X;ℤ) → H₂(X;𝔽₂) = H₂(K ⊗ ℤ/2)` injective.  Since `H₂(X;ℤ) ≅ ℤ/2` is nontrivial
(Hurewicz: `Work.Stems.hurewicz_first_degree` in degree `2`), the group `H₂(X;𝔽₂)` is nontrivial, and
Kronecker duality over the field `𝔽₂` (`kronH_bijective_field`) turns that into nontriviality of
`H²(X;𝔽₂)`.

The one subtlety is the identification `expTensHom K (mulP 2) = 2 • 𝟙 (expTens K zZ)` on the chain
level (`bockSES_f_two`); over `ℤ` the `ℤ`-module diamond (`M.isModule` versus
`AddCommGroup.toIntModule`) makes some `simp`-rewrites fail with instance mismatches, so the
computation is done on pure tensors and finished with `two_zsmul`/`TensorProduct.tmul_add`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory

namespace Work.Pi6.SQM

noncomputable section

/-! ## 1. The coefficient short exact sequence `0 → ℤ --·2--> ℤ --red--> ℤ/2 → 0` -/

/-- Multiplication by `2` on `ℤ` is injective. -/
theorem mono_mulP_two : Mono (Work.Pi6.EMZ.mulP 2) := by
  refine (ModuleCat.mono_iff_injective _).mpr ?_
  have hmulapp : ∀ z : ↥(Work.Pi6.EMZ.zZ), (Work.Pi6.EMZ.mulP 2) z = (2 : ℤ) • z :=
    fun z => Work.Pi6.EMZ.mulP_hom_apply 2 z
  intro x y h
  have h' : (2 : ℤ) • x = (2 : ℤ) • y := by
    rw [← hmulapp x, ← hmulapp y]
    exact h
  have h2 : (2 : ℤ) * x = (2 : ℤ) * y := by simpa [zsmul_eq_mul] using h'
  exact mul_left_cancel₀ (by norm_num) h2

/-- The reduction `ℤ → ℤ/2` is surjective. -/
theorem epi_redP_two : Epi (Work.Pi6.EMZ.redP 2) := by
  refine (ModuleCat.epi_iff_surjective _).mpr ?_
  have hredapp : ∀ z : ↥(Work.Pi6.EMZ.zZ), (Work.Pi6.EMZ.redP 2) z = ((z : ℤ) : ZMod 2) :=
    fun z => Work.Pi6.EMZ.redP_hom_apply 2 z
  intro y
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := 2) y
  exact ⟨k, by rw [hredapp]; exact hk⟩

/-- The coefficient sequence `ℤ --·2--> ℤ --red--> ℤ/2` is exact in the middle. -/
theorem exact_mulP_two : Function.Exact (Work.Pi6.EMZ.mulP 2).hom (Work.Pi6.EMZ.redP 2).hom := by
  intro y
  have hred : (Work.Pi6.EMZ.redP 2).hom y = ((y : ℤ) : ZMod 2) :=
    Work.Pi6.EMZ.redP_hom_apply 2 y
  have hmul : ∀ x : ↥(Work.Pi6.EMZ.zZ), (Work.Pi6.EMZ.mulP 2).hom x = (2 : ℤ) • x :=
    fun x => Work.Pi6.EMZ.mulP_hom_apply 2 x
  rw [hred]
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y 2).mp hy
    refine Set.mem_range.mpr ⟨x, ?_⟩
    rw [hmul]
    have hx' : (2 : ℤ) • x = y := by
      rw [zsmul_eq_mul]
      exact hx.symm
    exact hx'
  · rintro ⟨x, hx⟩
    have hxy : y = (2 : ℤ) • x := by
      rw [← hx]
      exact Work.Pi6.EMZ.mulP_hom_apply 2 x
    rw [hxy, zsmul_eq_mul]
    push_cast
    exact mul_eq_zero_of_left (CharP.cast_eq_zero (ZMod 2) 2) _

/-- **The mod-`2` coefficient short exact sequence** `0 → ℤ --·2--> ℤ --red--> ℤ/2 → 0`. -/
theorem coeffSES_two_shortExact : (Work.Pi6.EMZ.coeffSES 2).ShortExact :=
  ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (Work.Pi6.EMZ.coeffSES 2)).mpr
      exact_mulP_two)
    mono_mulP_two epi_redP_two

/-! ## 2. The first map of the chain-level Bockstein sequence is `2 • 𝟙` -/

/-- **Whiskering by the unit on the left is linear in the scalar**: over `ℤ`,
`A ◁ (c • 𝟙 M) = c • 𝟙 (A ⊗ M)`.  (`MonoidalLinear` is not available for `ModuleCat ℤ` in this
toolchain, and the elementwise proof has to avoid the `ℤ`-module diamond, hence the `two_zsmul`
route.) -/
theorem whiskerLeft_two (A M : ModuleCat ℤ) :
    A ◁ ((2 : ℤ) • 𝟙 M) = (2 : ℤ) • 𝟙 (A ⊗ M) := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' (fun x y => ?_)
  rw [ModuleCat.hom_whiskerLeft, LinearMap.lTensor_tmul, Work.Pi6.EMZ.smul_id_hom_apply,
    Work.Pi6.EMZ.smul_id_hom_apply, two_zsmul, two_zsmul, TensorProduct.tmul_add]

/-- The `n`-th component of a scalar multiple of the identity chain map. -/
theorem smul_id_f (C : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) (c : ℤ) :
    (c • 𝟙 C).f n = c • 𝟙 (C.X n) := by simp

/-- **Scalar multiples of the identity induce scalars on homology.** -/
theorem homologyMap_smul_id (C : ChainComplex (ModuleCat ℤ) ℕ) (i : ℕ) (c : ℤ) :
    HomologicalComplex.homologyMap (c • 𝟙 C) i = c • 𝟙 (C.homology i) := by
  have h1 : HomologicalComplex.homologyMap (c • 𝟙 C) i
      = c • HomologicalComplex.homologyMap (𝟙 C) i := by
    rw [← HomologicalComplex.homologyFunctor_map (ModuleCat ℤ) (ComplexShape.down ℕ) i (c • 𝟙 C),
      ← HomologicalComplex.homologyFunctor_map (ModuleCat ℤ) (ComplexShape.down ℕ) i (𝟙 C),
      Functor.map_zsmul]
    exact rfl
  rw [h1]
  simp only [HomologicalComplex.homologyMap_id C i]

/-- **The first map of the chain-level mod-`2` Bockstein sequence is multiplication by `2`.** -/
theorem bockSES_f_two (X : Type) [TopologicalSpace X] :
    (Work.Pi6.EMZ.bockSES 2 X).f
      = (2 : ℤ) • 𝟙 (Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ) := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [Work.SSS.expTensHom_f, smul_id_f]
  simp only [Work.SSS.expTens_X]
  exact whiskerLeft_two _ _

/-! ## 3. Duality over a field: nontrivial homology implies nontrivial cohomology -/

/-- **Over a field, nontrivial homology implies nontrivial cohomology.**  Kronecker duality
(`Work.Cohomology.kronH_bijective_field`) identifies `Hⁿ(X;F)` with the `F`-dual of `Hₙ(X;F)`, and
the dual of a nontrivial vector space is nontrivial. -/
theorem nontrivialCohOfNontrivialHomology (F : Type) [Field F] (X : Type) [TopologicalSpace X]
    (n : ℕ) (h : Nontrivial (Work.Pi6.HR F X n)) : Nontrivial (Work.Pi6.Coh F X n) := by
  obtain ⟨c, d, hcd⟩ := h.exists_pair_ne
  have hne : ∃ v : ↥(Work.Pi6.HR F X n), v ≠ 0 := by
    by_cases hd : d = 0
    · exact ⟨c, fun hc0 => hcd (by rw [hc0, hd])⟩
    · exact ⟨d, hd⟩
  obtain ⟨v, hv⟩ := hne
  have hφ : ∃ φ : ↥(Work.Pi6.HR F X n) →ₗ[F] F, φ v ≠ 0 := by
    by_contra hcon
    refine hv ((Module.forall_dual_apply_eq_zero_iff F v).mp fun φ => ?_)
    exact not_not.mp (not_exists.mp hcon φ)
  obtain ⟨φ, hφne⟩ := hφ
  haveI : Nontrivial (↥(Work.Pi6.HR F X n) →ₗ[F] F) :=
    ⟨φ, 0, fun h0 => hφne (by simpa using LinearMap.congr_fun h0 v)⟩
  have e : ↥(Work.Pi6.Coh F X n) ≃ₗ[F] (↥(Work.Pi6.HR F X n) →ₗ[F] F) :=
    LinearEquiv.ofBijective (Work.Cohomology.kronH F (TopCat.toSSet.obj (TopCat.of X)) n)
      (Work.Cohomology.kronH_bijective_field F (TopCat.toSSet.obj (TopCat.of X)) n)
  exact e.toEquiv.nontrivial

/-! ## 4. The target: `H²` of a `K(ℤ/2,2)` range model is nontrivial -/

set_option backward.isDefEq.respectTransparency false in  -- v435decl
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in  -- v435decl
set_option backward.isDefEq.respectTransparency.types false in  -- v435decl
theorem hTwoNonzero (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ) (hN : 3 ≤ N)
    (hX : Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀) :
    Nontrivial (Work.Pi6.Coh (ZMod 2) X 2) := by
  -- ## Step 0: connectivity and the Hurewicz map in degree `2`
  have hconn : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) X x₀) :=
    fun i hi => hX.2 i (by omega) (Or.inl hi)
  obtain ⟨eπ⟩ := hX.1
  have hb := Work.Stems.hurewicz_first_degree (Y := X) 2 (by norm_num) x₀ hconn
  -- ## Step 1: `H₂(X;ℤ)` is nontrivial
  have hntZ : Nontrivial (Work.Pi6.HR ℤ X 2) := by
    haveI : Nontrivial (HomotopyGroup (Fin 2) X x₀) :=
      (eπ : HomotopyGroup (Fin 2) X x₀ ≃ Multiplicative (ZMod 2)).nontrivial
    exact hb.1.nontrivial
  -- ## Step 2: `H₂(X;ℤ)` is `2`-torsion (`π₂ ≅ ℤ/2` and additivity of the Hurewicz map)
  have htorsZ : ∀ y : Work.Pi6.HR ℤ X 2, (2 : ℤ) • y = 0 := by
    intro y
    obtain ⟨a, ha⟩ := hb.2 y
    have hsq : a * a = 1 := by
      refine eπ.injective ?_
      rw [map_mul, map_one]
      refine Multiplicative.ext ?_
      rw [toAdd_mul, toAdd_one, ← two_nsmul, nsmul_eq_mul]
      exact mul_eq_zero_of_left (CharP.cast_eq_zero (ZMod 2) 2) _
    have hkey : (2 : ℤ) • Work.Stems.hurewiczMapN 2 (by norm_num) x₀ a
        = Work.Stems.hurewiczMapN 2 (by norm_num) x₀ (a * a) := by
      rw [two_zsmul, ← Work.Stems.hurewiczMapN_mul 1 x₀ a a]
    rw [← ha, hkey, hsq]
    exact Work.Stems.hurewiczMap_one 1
  -- ## Step 3: the mod-`2` coefficient short exact sequence of chain complexes
  have hSES : (Work.Pi6.EMZ.bockSES 2 X).ShortExact :=
    Work.Pi6.EMZ.bockSES_shortExact 2 (by norm_num) X coeffSES_two_shortExact
  -- ## Step 4: the reduction map `H₂(X;ℤ) → H₂(X;𝔽₂)` is injective
  -- its kernel is the image of the first map of the Bockstein sequence, which is `2 • 𝟙 = 0`
  have hMsmul : (2 : ℤ) • 𝟙 ((Work.SSS.expTens (Work.Pi6.EMZ.chZ X) Work.Pi6.EMZ.zZ).homology 2)
      = 0 := by
    let eZ := (Work.Pi6.EMZ.expTensUnitHomologyIso X 2).toLinearEquiv.toAddEquiv
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    simp only [Work.Pi6.EMZ.smul_id_hom_apply, ModuleCat.hom_zero, LinearMap.zero_apply]
    apply eZ.injective
    rw [two_zsmul, map_add, map_zero, ← two_zsmul]
    exact htorsZ (eZ y)
  have hfzero : HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f 2 = 0 := by
    rw [bockSES_f_two X, homologyMap_smul_id]
    exact hMsmul
  have hex : Function.Exact ⇑(HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).f 2)
      ⇑(HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g 2) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hSES.homology_exact₂ 2)
  have hg_inj : Function.Injective
      ⇑(HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g 2) := by
    intro x y hxy
    have hz : (HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g 2) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨w, hw⟩ := Set.mem_range.mp ((hex (x - y)).mp hz)
    have hw0 : x - y = 0 := by
      rw [← hw, hfzero]
      simp
    exact sub_eq_zero.mp hw0
  -- ## Step 5: `H₂(X;𝔽₂)` is nontrivial, hence so is `H²(X;𝔽₂)`
  let red : ↥(Work.Pi6.HR ℤ X 2) → ↥(Work.Pi6.HR (ZMod 2) X 2) := fun a =>
    (Work.Pi6.EMZ.expTensCoeffAddEquiv 2 (by norm_num) X 2)
      ((HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g 2)
        ((Work.Pi6.EMZ.expTensUnitHomologyIso X 2).toLinearEquiv.toAddEquiv.symm a))
  have hred : Function.Injective red := by
    intro a b hab
    have h1 : (HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g 2)
          ((Work.Pi6.EMZ.expTensUnitHomologyIso X 2).toLinearEquiv.toAddEquiv.symm a)
        = (HomologicalComplex.homologyMap (Work.Pi6.EMZ.bockSES 2 X).g 2)
          ((Work.Pi6.EMZ.expTensUnitHomologyIso X 2).toLinearEquiv.toAddEquiv.symm b) :=
      (Work.Pi6.EMZ.expTensCoeffAddEquiv 2 (by norm_num) X 2).injective hab
    exact (Work.Pi6.EMZ.expTensUnitHomologyIso X 2).toLinearEquiv.toAddEquiv.symm.injective
      (hg_inj h1)
  haveI := hntZ
  exact nontrivialCohOfNontrivialHomology (ZMod 2) X 2 hred.nontrivial

end

end Work.Pi6.SQM
