import Mathlib
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.mv_shortExact

/-!
# Exactness at the middle of the cochain Mayer–Vietoris sequence

The chain-level Mayer–Vietoris sequence

`0 ⟶ C_*(U ∩ V) --mvLeft--> C_*(U) ⊞ C_*(V) --mvRight--> C^{U,V}_*(X) ⟶ 0`

is short exact (`mv_shortExact`), hence so is its degreewise dual

`0 ⟶ C^*(C^{U,V}) --mvCochainF--> C^*(U) ⊞ C^*(V) --mvCochainG--> C^*(U ∩ V) ⟶ 0`,

because the dual of a short exact sequence of modules is exact in the middle
(`LinearMap.ker (dualMap f) ≤ LinearMap.range (dualMap g)`).

## Main results

* `exists_dualMap_eq_of_mem_ker` — the dual of a short exact sequence is exact in the middle,
  elementwise form: a functional killing the image of `f` factors through `g`;
* `mvCochainG_ker_le_range` — `ker (mvCochainG).f n ≤ range (mvCochainF).f n`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-! ## The dual of a short exact sequence of modules is exact in the middle -/

/-- **The dual of a short exact sequence is exact at the middle**, elementwise form: if
`0 ⟶ M --f--> N --g--> P ⟶ 0` is exact and `ψ : N → R` vanishes on the image of `f`, then `ψ`
factors as `χ ∘ g` for a unique such `χ`. -/
theorem exists_dualMap_eq_of_mem_ker {R : Type*} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hg : Function.Surjective g)
    (hfg : LinearMap.ker g = LinearMap.range f)
    (ψ : Module.Dual R N) (hψ : ∀ m, ψ (f m) = 0) :
    ∃ χ : Module.Dual R P, ∀ n, χ (g n) = ψ n := by
  have hker : LinearMap.ker g ≤ LinearMap.ker ψ := by
    intro n hn
    rw [hfg] at hn
    obtain ⟨m, rfl⟩ := hn
    exact hψ m
  refine ⟨((LinearMap.ker g).liftQ ψ hker).comp
    (LinearMap.quotKerEquivOfSurjective g hg).symm.toLinearMap, ?_⟩
  intro n
  rw [LinearMap.comp_apply]
  have h2 : (↑((LinearMap.quotKerEquivOfSurjective g hg).symm.toLinearMap) :
      P → N ⧸ LinearMap.ker g) (g n) = Submodule.Quotient.mk n :=
    LinearMap.quotKerEquivOfSurjective_symm_apply g hg n
  rw [h2, Submodule.liftQ_apply]

/-- **The dual of a short exact sequence of modules is exact at the middle.** -/
theorem dualMap_ker_le_range {R : Type*} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hg : Function.Surjective g)
    (hfg : LinearMap.ker g = LinearMap.range f) :
    LinearMap.ker (LinearMap.dualMap f) ≤ LinearMap.range (LinearMap.dualMap g) := by
  intro ψ hψ
  rw [LinearMap.mem_ker] at hψ
  have hψ0 : ∀ m : M, ψ (f m) = 0 := fun m => LinearMap.congr_fun hψ m
  obtain ⟨χ, hχ⟩ := exists_dualMap_eq_of_mem_ker f g hg hfg ψ hψ0
  refine LinearMap.mem_range.mpr ⟨χ, ?_⟩
  ext n
  exact hχ n

/-! ## The degreewise components of the Mayer–Vietoris cochain maps -/

section Components

variable (U V : Set X) (n : ℕ)

/-- `mvCochainG` on the first summand is the transpose of `chainInclU`. -/
lemma mvCochainG_apply_inl (a : (cochainU U V).X n) :
    ((mvCochainG U V).f n).hom (((biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V).f n).hom a)
      = a.comp (((chainInclU U V).f n).hom) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, mvCochainG_inl, dualComplexMap_f]
  simp only [dualComplexMapComp, ModuleCat.hom_ofHom]
  rfl

/-- `mvCochainG` on the second summand is the transpose of `chainInclV`. -/
lemma mvCochainG_apply_inr (b : (cochainV U V).X n) :
    ((mvCochainG U V).f n).hom (((biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V).f n).hom b)
      = b.comp (((chainInclV U V).f n).hom) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, mvCochainG_inr, dualComplexMap_f]
  simp only [dualComplexMapComp, ModuleCat.hom_ofHom]
  rfl

/-- The `fst`-component of `mvCochainF` is the transpose of `smallOfU`. -/
lemma mvCochainF_fst_apply (χ : (dualComplex ℤ (smallChains U V)).X n) :
    ((biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V).f n).hom
      (((mvCochainF U V).f n).hom χ)
      = χ.comp (((smallOfU U V).f n).hom) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, mvCochainF_fst, dualComplexMap_f]
  simp only [dualComplexMapComp, ModuleCat.hom_ofHom]
  rfl

/-- The `snd`-component of `mvCochainF` is minus the transpose of `smallOfV`. -/
lemma mvCochainF_snd_apply (χ : (dualComplex ℤ (smallChains U V)).X n) :
    ((biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V).f n).hom
      (((mvCochainF U V).f n).hom χ)
      = -(χ.comp (((smallOfV U V).f n).hom)) := by
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, mvCochainF_snd]
  rw [show (-(dualComplexMap ℤ (singularChains ℤ (TopCat.of V)) (smallChains U V)
      (smallOfV U V))).f n
    = -(dualComplexMap ℤ (singularChains ℤ (TopCat.of V)) (smallChains U V) (smallOfV U V)).f n
    from rfl]
  rw [ModuleCat.hom_neg]
  simp only [dualComplexMap_f, dualComplexMapComp, ModuleCat.hom_ofHom]
  rfl

end Components

/-! ## The degreewise components of the Mayer–Vietoris chain maps -/

section ChainComponents

variable (U V : Set X) (n : ℕ)

/-- The first component of `mvLeft` at degree `n` is `chainInclU`. -/
lemma mvLeft_fst_hom :
    (((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n)).hom.comp (((mvLeft U V).f n).hom)
      = ((chainInclU U V).f n).hom := by
  have h := HomologicalComplex.biprod_lift_fst_f (chainInclU U V) (chainInclV U V) n
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp] at h2
  rw [show (mvLeft U V) = biprod.lift (chainInclU U V) (chainInclV U V) from rfl]
  exact h2

/-- The second component of `mvLeft` at degree `n` is `chainInclV`. -/
lemma mvLeft_snd_hom :
    (((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n)).hom.comp (((mvLeft U V).f n).hom)
      = ((chainInclV U V).f n).hom := by
  have h := HomologicalComplex.biprod_lift_snd_f (chainInclU U V) (chainInclV U V) n
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp] at h2
  rw [show (mvLeft U V) = biprod.lift (chainInclU U V) (chainInclV U V) from rfl]
  exact h2

/-- The first projection of `C_*(U) ⊞ C_*(V)` composed with the first inclusion is the identity. -/
lemma chainBiprod_fst_inl :
    (((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n)).hom.comp
      (((biprod.inl : singularChains ℤ (TopCat.of U) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n).hom) = LinearMap.id := by
  have h := HomologicalComplex.biprod_inl_fst_f (singularChains ℤ (TopCat.of U))
    (singularChains ℤ (TopCat.of V)) n
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  exact h2

/-- The second projection of `C_*(U) ⊞ C_*(V)` composed with the first inclusion is zero. -/
lemma chainBiprod_snd_inl :
    (((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n)).hom.comp
      (((biprod.inl : singularChains ℤ (TopCat.of U) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n).hom) = 0 := by
  have h := HomologicalComplex.biprod_inl_snd_f (singularChains ℤ (TopCat.of U))
    (singularChains ℤ (TopCat.of V)) n
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  exact h2

/-- The first projection of `C_*(U) ⊞ C_*(V)` composed with the second inclusion is zero. -/
lemma chainBiprod_fst_inr :
    (((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n)).hom.comp
      (((biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n).hom) = 0 := by
  have h := HomologicalComplex.biprod_inr_fst_f (singularChains ℤ (TopCat.of U))
    (singularChains ℤ (TopCat.of V)) n
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  exact h2

/-- The second projection of `C_*(U) ⊞ C_*(V)` composed with the second inclusion is the identity. -/
lemma chainBiprod_snd_inr :
    (((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n)).hom.comp
      (((biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
        singularChains ℤ (TopCat.of V)).f n).hom) = LinearMap.id := by
  have h := HomologicalComplex.biprod_inr_snd_f (singularChains ℤ (TopCat.of U))
    (singularChains ℤ (TopCat.of V)) n
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_id] at h2
  exact h2

/-- `mvRight` on the first summand is `smallOfU`. -/
lemma mvRight_inl_hom (x : (singularChains ℤ (TopCat.of U)).X n) :
    ((mvRight U V).f n).hom
      (((biprod.inl : singularChains ℤ (TopCat.of U) ⟶ singularChains ℤ (TopCat.of U) ⊞
          singularChains ℤ (TopCat.of V)).f n).hom x)
      = ((smallOfU U V).f n).hom x := by
  have h := HomologicalComplex.biprod_inl_desc_f (smallOfU U V) (-(smallOfV U V)) n
  rw [show (mvRight U V) = biprod.desc (smallOfU U V) (-(smallOfV U V)) from rfl]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  rw [h]

/-- `mvRight` on the second summand is `-smallOfV`. -/
lemma mvRight_inr_hom (y : (singularChains ℤ (TopCat.of V)).X n) :
    ((mvRight U V).f n).hom
      (((biprod.inr : singularChains ℤ (TopCat.of V) ⟶ singularChains ℤ (TopCat.of U) ⊞
          singularChains ℤ (TopCat.of V)).f n).hom y)
      = -(((smallOfV U V).f n).hom y) := by
  have h := HomologicalComplex.biprod_inr_desc_f (smallOfU U V) (-(smallOfV U V)) n
  rw [show (mvRight U V) = biprod.desc (smallOfU U V) (-(smallOfV U V)) from rfl]
  rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp]
  rw [h]
  rw [show (-(smallOfV U V)).f n = -((smallOfV U V).f n) from rfl]
  rw [ModuleCat.hom_neg]
  rfl

end ChainComponents

/-! ## Exactness at the middle of the cochain Mayer–Vietoris sequence -/

/-- **Exactness at the middle of the cochain Mayer–Vietoris sequence**, degree `n`: every
`n`-cochain of the pair `(U, V)` that is killed by `mvCochainG` comes from the small cochains
through `mvCochainF`. -/
theorem mvCochainG_ker_le_range {X : TopCat} (U V : Set X) (n : ℕ) : LinearMap.ker (ModuleCat.Hom.hom ((Work.Cohomology.mvCochainG U V).f n)) ≤ LinearMap.range (ModuleCat.Hom.hom ((Work.Cohomology.mvCochainF U V).f n)) := by
  intro y hy
  rw [LinearMap.mem_ker] at hy
  rw [LinearMap.mem_range]
  -- ## Step 1: the chain-level Mayer–Vietoris sequence is exact in degree `n`
  set S := (ShortComplex.mk (mvLeft U V) (mvRight U V) (mvComp U V)).map
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n) with hS
  have hSx : S.ShortExact := mv_degreewise U V n
  have hsurj : Function.Surjective (((mvRight U V).f n).hom) := by
    intro p
    obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective S.g).1 hSx.epi_g p
    exact ⟨x, hx⟩
  have hex' : ∀ x, ((mvRight U V).f n).hom x = 0 → ∃ c, ((mvLeft U V).f n).hom c = x := by
    intro x hx
    obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff S).1 hSx.exact x (by exact hx)
    exact ⟨c, hc⟩
  have hex : LinearMap.ker (((mvRight U V).f n).hom)
      = LinearMap.range (((mvLeft U V).f n).hom) := by
    refine le_antisymm (fun x hx => hex' x hx) ?_
    rintro x ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    have hcomp : ((mvLeft U V).f n) ≫ ((mvRight U V).f n) = 0 := by
      rw [← HomologicalComplex.comp_f, mvComp, HomologicalComplex.zero_f]
    have h2 := congrArg ModuleCat.Hom.hom hcomp
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    exact LinearMap.congr_fun h2 c
  -- ## Step 2: the two components of `y`
  set a : ((singularChains ℤ (TopCat.of U)).X n) →ₗ[ℤ] ℤ :=
    ConcreteCategory.hom ((biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V).f n) y with ha
  set b : ((singularChains ℤ (TopCat.of V)).X n) →ₗ[ℤ] ℤ :=
    ConcreteCategory.hom ((biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V).f n) y with hb
  have hydec : ConcreteCategory.hom ((biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V).f n) a
      + ConcreteCategory.hom ((biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V).f n) b
      = y := by
    rw [ha, hb]
    exact biprodX_total y
  -- ## Step 3: they satisfy the compatibility relation
  have hcond : a.comp (((chainInclU U V).f n).hom) + b.comp (((chainInclV U V).f n).hom) = 0 := by
    have h0 : ModuleCat.Hom.hom ((mvCochainG U V).f n)
        (ConcreteCategory.hom ((biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V).f n) a
          + ConcreteCategory.hom ((biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V).f n) b)
        = 0 := by
      rw [hydec]
      exact hy
    rw [map_add, mvCochainG_apply_inl, mvCochainG_apply_inr] at h0
    exact h0
  -- ## Step 4: the chain-level functional `ψ`
  set ψ : ((singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).X n) →ₗ[ℤ] ℤ :=
    a.comp (((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n).hom)
      + b.comp (((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n).hom) with hψ
  have hψ0 : ∀ m, ψ (((mvLeft U V).f n).hom m) = 0 := by
    intro m
    have h1 : (((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n).hom) (((mvLeft U V).f n).hom m)
        = ((chainInclU U V).f n).hom m := LinearMap.congr_fun (mvLeft_fst_hom U V n) m
    have h2 : (((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n).hom) (((mvLeft U V).f n).hom m)
        = ((chainInclV U V).f n).hom m := LinearMap.congr_fun (mvLeft_snd_hom U V n) m
    have h3 : a (((chainInclU U V).f n).hom m) + b (((chainInclV U V).f n).hom m) = 0 :=
      LinearMap.congr_fun hcond m
    rw [hψ]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, h1, h2]
    exact h3
  -- ## Step 5: the dual of the chain-level short exact sequence
  obtain ⟨χ, hχ⟩ := exists_dualMap_eq_of_mem_ker (((mvLeft U V).f n).hom)
    (((mvRight U V).f n).hom) hsurj hex ψ hψ0
  refine ⟨χ, ?_⟩
  -- ## Step 6: `mvCochainF χ = y`
  apply biprodX_ext
  · show ((biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V).f n).hom
      (((mvCochainF U V).f n).hom χ) = a
    rw [mvCochainF_fst_apply]
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply]
    have hA : χ (((smallOfU U V).f n).hom x)
        = χ (((mvRight U V).f n).hom (((biprod.inl : singularChains ℤ (TopCat.of U) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n).hom x)) :=
      congrArg χ (mvRight_inl_hom U V n x).symm
    rw [hA, hχ _]
    rw [hψ]
    have hP : (((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n).hom) (((biprod.inl : singularChains ℤ (TopCat.of U) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n).hom x) = x :=
      LinearMap.congr_fun (chainBiprod_fst_inl U V n) x
    have hQ : (((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n).hom) (((biprod.inl : singularChains ℤ (TopCat.of U) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n).hom x) = 0 :=
      LinearMap.congr_fun (chainBiprod_snd_inl U V n) x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hP, hQ]
    simp
  · show ((biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V).f n).hom
      (((mvCochainF U V).f n).hom χ) = b
    rw [mvCochainF_snd_apply]
    apply LinearMap.ext
    intro x
    rw [LinearMap.neg_apply, LinearMap.comp_apply]
    have hB : χ (((smallOfV U V).f n).hom x)
        = -ψ (((biprod.inr : singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n).hom x) := by
      rw [show ((smallOfV U V).f n).hom x
          = -(((mvRight U V).f n).hom (((biprod.inr : singularChains ℤ (TopCat.of V) ⟶
              singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n).hom x))
          from by rw [mvRight_inr_hom U V n x]; simp]
      rw [map_neg, hχ _]
    rw [hB, hψ]
    have hP : (((biprod.fst : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of U)).f n).hom) (((biprod.inr : singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n).hom x) = 0 :=
      LinearMap.congr_fun (chainBiprod_fst_inr U V n) x
    have hQ : (((biprod.snd : singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V) ⟶
        singularChains ℤ (TopCat.of V)).f n).hom) (((biprod.inr : singularChains ℤ (TopCat.of V) ⟶
            singularChains ℤ (TopCat.of U) ⊞ singularChains ℤ (TopCat.of V)).f n).hom x) = x :=
      LinearMap.congr_fun (chainBiprod_snd_inr U V n) x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, hP, hQ]
    simp

end

end Work.Cohomology
