import Mathlib
import Submission.Work.ANALYTIC.CechPt.CoordDefs

/-!
# `doubleDualUnit (∐_J 𝟙)` is an isomorphism

For a finite index type `J`, the canonical double-dual unit
`doubleDualUnit X : X ⟶ ((X ⟹ 𝟙) ⟹ 𝟙)` of the free object `X = ∐_J 𝟙 = ℤ[J]` is an
isomorphism: the finite free module `ℤ[J]` is reflexive.

## The argument

Write `X = ∐_J 𝟙`.  We use the biproduct structure on `X = ∐_J 𝟙 = ∏_J 𝟙` to obtain

* the isomorphism `kapU J : ⨁_J 𝟙 ≅ ∐_J 𝟙`,
* the projections `piU J j : X ⟶ 𝟙` and the inclusions `inclU J j : 𝟙 ⟶ X`,
* the "identity matrix" isomorphism `EU J : X ⟶ ∏_J 𝟙` (`kapU⁻¹ ≫ isoProduct`).

Three maps are compared:

* `PgU J : sd X ⟶ ∏_j 𝟙`, the coordinate map `λ ↦ (λ(ι_j))_j`;
* `PsiU J : X ⟶ sd X`, the coproduct of the elements `curry (ρ_X ≫ π_j)` (the transpose of the
  evaluation pairing);
* `WU J : dd X ⟶ ∏_j 𝟙`, the coordinate map `Pi.lift (coordMap X (π_j))` of the double dual.

The key input is the identity (`PgU_inv_comp_PsiU`)

  `(PgU J ≫ (EU J)⁻¹) ≫ PsiU J = 𝟙 (sd X)`,

which exhibits `PgU J ≫ (EU J)⁻¹` as a section of `PsiU J` and `(EU J)⁻¹ ≫ PsiU J` as a retraction
of `PgU J`.  Hence `PsiU J` is a split epi and `PgU J` is a split mono.  Therefore

* `Mono (PgU J)`;
* `Mono ((pre (PsiU J)).app 𝟙)`, because a morphism with a section induces a monomorphism on
  internal homs (cancelling the section uses `pre_map` and `pre_id`);

and from `WU J = (pre (PsiU J)).app 𝟙 ≫ PgU J` (`WU_eq`) we deduce `Mono (WU J)`.

On the other hand `doubleDualUnit X ≫ WU J = EU J` (`doubleDualUnit_comp_WU`), because
`doubleDualUnit X ≫ coordMap X λ = λ` for every `λ : X ⟶ 𝟙` (`doubleDualUnit_coord`).  Since
`EU J` is an isomorphism, `WU J` is a split epi as well; being also a mono it is an isomorphism,
and `doubleDualUnit X = EU J ≫ (WU J)⁻¹` is an isomorphism.
-/

namespace Work.ANALYTIC.CechPt

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

/-- Naturality of `Pi.lift` in the source: `Pi.lift (fun j ↦ a ≫ g j) = a ≫ Pi.lift g`. -/
lemma Pi_lift_comp_naturality {C : Type*} [Category* C] {J : Type*} {f : J → C} [HasProduct f]
    {X Y : C} (a : X ⟶ Y) (g : ∀ j, Y ⟶ f j) :
    Pi.lift (fun j => a ≫ g j) = a ≫ Pi.lift g := by
  apply Pi.hom_ext
  intro j
  rw [Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π]

/-- If `s ≫ f = 𝟙 Y` (i.e. `s` is a section of `f`) then precomposition with `f` is a
monomorphism of internal homs. -/
lemma mono_pre_app_of_section {X Y Z : LightCondAb} (f : X ⟶ Y) (s : Y ⟶ X)
    (h : s ≫ f = 𝟙 Y) : Mono ((MonoidalClosed.pre f).app Z) := by
  have hsec : (MonoidalClosed.pre f).app Z ≫ (MonoidalClosed.pre s).app Z =
      𝟙 ((ihom Y).obj Z) := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, h, MonoidalClosed.pre_id,
      NatTrans.id_app]
  haveI : IsSplitMono ((MonoidalClosed.pre f).app Z) :=
    ⟨⟨SplitMono.mk ((MonoidalClosed.pre s).app Z) hsec⟩⟩
  exact IsSplitMono.mono _

/-- The free object `∐_J 𝟙 = ℤ[J]`. -/
abbrev sigU (J : Type) : LightCondAb := ∐ (fun _ : J => 𝟙_ LightCondAb)

/-- The product `∏_J 𝟙`. -/
abbrev prodU (J : Type) : LightCondAb := ∏ᶜ (fun _ : J => 𝟙_ LightCondAb)

/-- The biproduct `⨁_J 𝟙`. -/
abbrev bipU (J : Type) [Fintype J] : LightCondAb := ⨁ (fun _ : J => 𝟙_ LightCondAb)

/-- The biproduct `⨁_J 𝟙` is the coproduct `∐_J 𝟙`. -/
noncomputable def kapU (J : Type) [Fintype J] : bipU J ≅ sigU J :=
  biproduct.isoCoproduct (fun _ : J => 𝟙_ LightCondAb)

/-- The `j`-th projection `∐_J 𝟙 ⟶ 𝟙`, through the biproduct structure. -/
noncomputable def piU (J : Type) [Fintype J] (j : J) : sigU J ⟶ (𝟙_ LightCondAb) :=
  (kapU J).inv ≫ biproduct.π (fun _ : J => 𝟙_ LightCondAb) j

/-- The `j`-th inclusion `𝟙 ⟶ ∐_J 𝟙`. -/
noncomputable def inclU (J : Type) (j : J) : (𝟙_ LightCondAb) ⟶ sigU J :=
  Sigma.ι (fun _ : J => 𝟙_ LightCondAb) j

/-- The "identity matrix" isomorphism `∐_J 𝟙 ⟶ ∏_J 𝟙`. -/
noncomputable def EU (J : Type) [Fintype J] : sigU J ≅ prodU J :=
  (kapU J).symm ≪≫ (biproduct.isoProduct (fun _ : J => 𝟙_ LightCondAb))

/-- The coordinate map `sd X ⟶ ∏_j 𝟙`, `λ ↦ (λ(ι_j))_j`. -/
noncomputable def PgU (J : Type) [Fintype J] : sd (sigU J) ⟶ prodU J :=
  Pi.lift (fun j : J => (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
    (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom)

/-- The transpose `X ⟶ sd X` of the evaluation pairing, defined on the coproduct by the elements
`curry (ρ_X ≫ π_j)`. -/
noncomputable def PsiU (J : Type) [Fintype J] : sigU J ⟶ sd (sigU J) :=
  Sigma.desc (fun j : J => MonoidalClosed.curry ((ρ_ (sigU J)).hom ≫ piU J j))

/-- The coordinate map of the double dual, `Pi.lift (coordMap X (π_j))`. -/
noncomputable def WU (J : Type) [Fintype J] : dd (sigU J) ⟶ prodU J :=
  Pi.lift (fun j : J => coordMap (sigU J) (piU J j))

/-! ## Finite sums of `pre`'s -/

/-- Finite sums of `pre`'s are the `pre` of the finite sum. -/
lemma pre_finset_sum {J' : Type} [Fintype J'] {A B : LightCondAb} (g : J' → (A ⟶ B)) :
    MonoidalClosed.pre (∑ j, g j) = ∑ j, MonoidalClosed.pre (g j) := by
  classical
  induction (Finset.univ : Finset J') using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact pre_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, pre_add, ih]

/-! ## The evaluation pairing and the matrix identity `PsiU ≫ PgU = EU` -/

/-- **The evaluation pairing.**  The element `curry (ρ_X ≫ λ) : 𝟙 ⟶ sd X` of the internal hom
corresponding to the functional `λ : X ⟶ 𝟙`, evaluated at the element `y : 𝟙 ⟶ X`, is the scalar
`y ≫ λ`.

(Proved by a colleague in `Submission/Work/ANALYTIC/CechPt/PsiU_comp_PgU.lean`; repeated here so
that the present module, which that one imports, stays self-contained.) -/
lemma curry_rho_comp_pre_eval (X : LightCondAb) (lam : X ⟶ 𝟙_ LightCondAb)
    (y : 𝟙_ LightCondAb ⟶ X) :
    MonoidalClosed.curry ((ρ_ X).hom ≫ lam) ≫
      ((MonoidalClosed.pre y).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom) = y ≫ lam := by
  set f := MonoidalClosed.curry ((ρ_ X).hom ≫ lam) ≫
      (MonoidalClosed.pre y).app (𝟙_ LightCondAb) with hf
  have hkey : MonoidalClosed.uncurry f = (y ▷ (𝟙_ LightCondAb)) ≫ (ρ_ X).hom ≫ lam := by
    rw [hf, MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry]
  have h1 : MonoidalClosed.curry ((ρ_ X).hom ≫ lam) ≫
      ((MonoidalClosed.pre y).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom) =
      f ≫ (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom := by
    rw [hf, Category.assoc]
  rw [h1, ← MonoidalClosed.curry_uncurry f, curry_unitIsoSelf, hkey,
      MonoidalCategory.rightUnitor_naturality_assoc, ← unitors_equal, Iso.inv_hom_id_assoc]

/-- The `j`-th coprojection composed with the biproduct identification is the `j`-th biproduct
inclusion. -/
lemma Sigma_iota_comp_kapU_inv (J : Type) [Fintype J] (j : J) :
    (Sigma.ι (fun _ : J => 𝟙_ LightCondAb) j) ≫ (kapU J).inv =
      biproduct.ι (fun _ : J => 𝟙_ LightCondAb) j := by
  rw [kapU, biproduct.isoCoproduct_inv, Sigma.ι_comp_desc]

/-- The fundamental matrix entry `ι_j ≫ π_k`. -/
lemma Sigma_iota_comp_piU (J : Type) [Fintype J] (j k : J) :
    (Sigma.ι (fun _ : J => 𝟙_ LightCondAb) j) ≫ piU J k =
      biproduct.ι (fun _ : J => 𝟙_ LightCondAb) j ≫
        biproduct.π (fun _ : J => 𝟙_ LightCondAb) k := by
  rw [piU, ← Category.assoc, Sigma_iota_comp_kapU_inv]

/-- Diagonal matrix entries: `ι_j ≫ π_j = 𝟙`. -/
lemma inclU_comp_piU_self (J : Type) [Fintype J] (j : J) :
    inclU J j ≫ piU J j = 𝟙 (𝟙_ LightCondAb) := by
  rw [inclU, Sigma_iota_comp_piU,
    biproduct.ι_π_self (f := fun _ : J => 𝟙_ LightCondAb)]

/-- Off-diagonal matrix entries: `ι_j ≫ π_k = 0` for `j ≠ k`. -/
lemma inclU_comp_piU_ne (J : Type) [Fintype J] {j k : J} (h : j ≠ k) :
    inclU J j ≫ piU J k = 0 := by
  rw [inclU, Sigma_iota_comp_piU,
    biproduct.ι_π_ne (f := fun _ : J => 𝟙_ LightCondAb) h]

/-- **The matrix identity `PsiU J ≫ PgU J = EU J`.** -/
theorem PsiU_comp_PgU (J : Type) [Fintype J] :
    PsiU J ≫ PgU J = (EU J).hom := by
  classical
  have hpi : Pi.lift (fun j : J => piU J j) = (EU J).hom := by
    show Pi.lift (fun j : J => (kapU J).inv ≫
      biproduct.π (fun _ : J => 𝟙_ LightCondAb) j) = (EU J).hom
    rw [Pi_lift_comp_naturality, ← biproduct.isoProduct_hom, EU, Iso.trans_hom, Iso.symm_hom]
  have hcoord : ∀ j : J, PsiU J ≫ ((MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom) = piU J j := by
    intro j
    apply Sigma.hom_ext
    intro k
    rw [← Category.assoc, PsiU, Sigma.ι_comp_desc, curry_rho_comp_pre_eval]
    rcases eq_or_ne j k with h | h
    · subst h
      rw [inclU_comp_piU_self, Sigma_iota_comp_piU,
        biproduct.ι_π_self (f := fun _ : J => 𝟙_ LightCondAb)]
    · rw [inclU_comp_piU_ne J h, Sigma_iota_comp_piU,
        biproduct.ι_π_ne (f := fun _ : J => 𝟙_ LightCondAb) (Ne.symm h)]
  calc PsiU J ≫ PgU J
      = Pi.lift (fun j : J => PsiU J ≫ ((MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
          (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom)) := by
        rw [PgU, ← Pi_lift_comp_naturality]
    _ = Pi.lift (fun j : J => piU J j) := by rw [funext hcoord]
    _ = (EU J).hom := hpi

/-! ## The matrix decomposition of the identity of `∐_J 𝟙` -/

/-- The identity of a finite biproduct is the sum of its "matrix units" `∑ j, π j ≫ ι j`. -/
lemma biproduct_sum_pi_iota {C : Type*} [Category* C] [Preadditive C] {J' : Type*} [Fintype J']
    (F : J' → C) [HasBiproduct F] :
    (∑ j : J', biproduct.π F j ≫ biproduct.ι F j) = 𝟙 (⨁ F) := by
  classical
  apply biproduct.hom_ext
  intro i
  rw [Preadditive.sum_comp, Category.id_comp]
  rw [Finset.sum_eq_single i]
  · rw [Category.assoc, biproduct.ι_π_self, Category.comp_id]
  · intro j _ hj
    rw [Category.assoc, biproduct.ι_π_ne F hj, comp_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The `j`-th biproduct inclusion followed by the identification `⨁_J 𝟙 ≅ ∐_J 𝟙` is the `j`-th
coprojection. -/
lemma Sigma_iota_eq_inclusion_comp_kapU_hom (J : Type) [Fintype J] (j : J) :
    (Sigma.ι (fun _ : J => 𝟙_ LightCondAb) j) =
      biproduct.ι (fun _ : J => 𝟙_ LightCondAb) j ≫ (kapU J).hom := by
  rw [kapU, biproduct.isoCoproduct_hom, biproduct.ι_desc]

/-- `∑ j, π_j ≫ ι_j = 𝟙 (∐_J 𝟙)`: the matrix decomposition of the identity of `sigU J`. -/
theorem sum_piU_comp_inclU (J : Type) [Fintype J] :
    (∑ j : J, piU J j ≫ inclU J j) = 𝟙 (sigU J) := by
  classical
  have hterm : ∀ j : J, piU J j ≫ inclU J j =
      ((kapU J).inv ≫ (biproduct.π (fun _ : J => 𝟙_ LightCondAb) j ≫
        biproduct.ι (fun _ : J => 𝟙_ LightCondAb) j)) ≫ (kapU J).hom := by
    intro j
    rw [piU, inclU, Sigma_iota_eq_inclusion_comp_kapU_hom J j]
    simp only [Category.assoc]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Preadditive.sum_comp,
    ← Preadditive.comp_sum, biproduct_sum_pi_iota, Category.comp_id, Iso.inv_hom_id]

/-! ## The coordinate map is a monomorphism -/

/-- **`PgU J` is a monomorphism**: two functionals on `∐_J 𝟙` taking the same values on all the
basis elements `ι_j` are equal. -/
theorem mono_PgU (J : Type) [Fintype J] : Mono (PgU J) := by
  classical
  refine ⟨fun {Z} a b hab => ?_⟩
  -- the coordinates of `a` and `b` at `ι_j` agree
  have h2 : ∀ j : J, a ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) =
      b ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) := by
    intro j
    have h := congrArg (fun t => t ≫ Pi.π (fun _ : J => 𝟙_ LightCondAb) j) hab
    simp only [Category.assoc, PgU, Pi.lift_comp_π] at h
    rw [← Category.assoc, ← Category.assoc] at h
    calc a ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb)
        = ((a ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb)) ≫
            (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom) ≫
            (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).inv := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = ((b ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb)) ≫
            (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom) ≫
            (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).inv := by rw [h]
      _ = b ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) := by
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- the expansion of the identity of `sd X` along the matrix decomposition
  have hsum : 𝟙 (sd (sigU J)) = ∑ j : J,
      ((MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.pre (piU J j)).app (𝟙_ LightCondAb)) := by
    calc 𝟙 (sd (sigU J))
        = (MonoidalClosed.pre (𝟙 (sigU J))).app (𝟙_ LightCondAb) := by
          rw [MonoidalClosed.pre_id, NatTrans.id_app]
      _ = (MonoidalClosed.pre (∑ j : J, piU J j ≫ inclU J j)).app (𝟙_ LightCondAb) := by
          rw [sum_piU_comp_inclU]
      _ = (∑ j : J, MonoidalClosed.pre (piU J j ≫ inclU J j)).app (𝟙_ LightCondAb) := by
          rw [pre_finset_sum]
      _ = (∑ j : J, (MonoidalClosed.pre (inclU J j) ≫
              MonoidalClosed.pre (piU J j))).app (𝟙_ LightCondAb) := by
          rw [show (fun j : J => MonoidalClosed.pre (piU J j ≫ inclU J j)) =
              (fun j : J => MonoidalClosed.pre (inclU J j) ≫
                MonoidalClosed.pre (piU J j)) from
            funext (fun j => MonoidalClosed.pre_map (piU J j) (inclU J j))]
      _ = ∑ j : J, ((MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
              (MonoidalClosed.pre (piU J j)).app (𝟙_ LightCondAb)) := by
          rw [NatTrans.app_sum]
          exact Finset.sum_congr rfl (fun j _ => NatTrans.comp_app _ _ _)
  have hexp : ∀ c : Z ⟶ sd (sigU J), c = ∑ j : J,
      (c ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.pre (piU J j)).app (𝟙_ LightCondAb)) := by
    intro c
    calc c = c ≫ 𝟙 (sd (sigU J)) := (Category.comp_id c).symm
      _ = c ≫ (∑ j : J, ((MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
            (MonoidalClosed.pre (piU J j)).app (𝟙_ LightCondAb))) := by rw [hsum]
      _ = ∑ j : J, (c ≫ (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
            (MonoidalClosed.pre (piU J j)).app (𝟙_ LightCondAb)) := by
          rw [Preadditive.comp_sum]
  rw [hexp a, hexp b]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [← Category.assoc]
  rw [h2 j]

/-- **Key computation.** `PgU J ≫ (EU J)⁻¹` is a section of `PsiU J`; equivalently
`(EU J)⁻¹ ≫ PsiU J` is a retraction of `PgU J`. -/
theorem PgU_inv_comp_PsiU (J : Type) [Fintype J] :
    (PgU J ≫ (EU J).inv) ≫ PsiU J = 𝟙 (sd (sigU J)) := by
  haveI : Mono (PgU J) := mono_PgU J
  have hg : ((EU J).inv ≫ PsiU J) ≫ PgU J = 𝟙 (prodU J) := by
    rw [Category.assoc, PsiU_comp_PgU, Iso.inv_hom_id]
  have h : (PgU J ≫ ((EU J).inv ≫ PsiU J)) ≫ PgU J = 𝟙 (sd (sigU J)) ≫ PgU J := by
    rw [Category.assoc, hg, Category.comp_id, Category.id_comp]
  rw [show (PgU J ≫ (EU J).inv) ≫ PsiU J = PgU J ≫ ((EU J).inv ≫ PsiU J) from
    Category.assoc _ _ _]
  exact (cancel_mono (PgU J)).mp h

/-- `doubleDualUnit X ≫ coordMap X λ = λ`, summed over the coordinates `λ = π_j`. -/
theorem doubleDualUnit_comp_WU (J : Type) [Fintype J] :
    doubleDualUnit (sigU J) ≫ WU J = (EU J).hom := by
  have h1 : doubleDualUnit (sigU J) ≫ WU J =
      Pi.lift (fun j : J => doubleDualUnit (sigU J) ≫ coordMap (sigU J) (piU J j)) := by
    rw [WU, ← Pi_lift_comp_naturality]
  rw [h1]
  have h2 : (fun j : J => doubleDualUnit (sigU J) ≫ coordMap (sigU J) (piU J j)) =
      (fun j : J => piU J j) :=
    funext (fun j => doubleDualUnit_coord (sigU J) (piU J j))
  rw [h2]
  have h3 : Pi.lift (fun j : J => piU J j) = (EU J).hom := by
    show Pi.lift (fun j : J => (kapU J).inv ≫
      biproduct.π (fun _ : J => 𝟙_ LightCondAb) j) = (EU J).hom
    rw [Pi_lift_comp_naturality, ← biproduct.isoProduct_hom, EU, Iso.trans_hom, Iso.symm_hom]
  rw [h3]

/-- `WU J = (pre (PsiU J)).app 𝟙 ≫ PgU J`. -/
theorem WU_eq (J : Type) [Fintype J] :
    WU J = (MonoidalClosed.pre (PsiU J)).app (𝟙_ LightCondAb) ≫ PgU J := by
  have hcoord : ∀ j : J, coordMap (sigU J) (piU J j) =
      (MonoidalClosed.pre (PsiU J)).app (𝟙_ LightCondAb) ≫
        ((MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
          (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom) := by
    intro j
    have hψ : MonoidalClosed.curry ((ρ_ (sigU J)).hom ≫ piU J j) = inclU J j ≫ PsiU J := by
      rw [PsiU, inclU, Sigma.ι_comp_desc]
    show (MonoidalClosed.pre
        (MonoidalClosed.curry ((ρ_ (sigU J)).hom ≫ piU J j))).app (𝟙_ LightCondAb) ≫
        (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom = _
    rw [hψ, ← Category.assoc, ← NatTrans.comp_app, ← MonoidalClosed.pre_map]
  rw [show WU J = Pi.lift (fun j : J => coordMap (sigU J) (piU J j)) from rfl,
    show (fun j : J => coordMap (sigU J) (piU J j)) =
      (fun j : J => (MonoidalClosed.pre (PsiU J)).app (𝟙_ LightCondAb) ≫
        ((MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
          (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom)) from funext hcoord,
    show PgU J = Pi.lift (fun j : J => (MonoidalClosed.pre (inclU J j)).app (𝟙_ LightCondAb) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ LightCondAb)).hom) from rfl]
  rw [Pi_lift_comp_naturality]

/-- **`doubleDualUnit (∐_J 𝟙)` is an isomorphism** for a finite index type `J`. -/
theorem doubleDualUnit_sigma_unit (J : Type) [Fintype J] :
    IsIso (Work.ANALYTIC.CechPt.doubleDualUnit
      (∐ (fun _ : J => 𝟙_ LightCondAb))) := by
  have hsec : (PgU J ≫ (EU J).inv) ≫ PsiU J = 𝟙 (sd (sigU J)) := PgU_inv_comp_PsiU J
  -- `PgU J` is a split mono (with retraction `(EU J)⁻¹ ≫ PsiU J`)
  haveI hsplitM : IsSplitMono (PgU J) :=
    ⟨⟨SplitMono.mk ((EU J).inv ≫ PsiU J) hsec⟩⟩
  have hPg_mono : Mono (PgU J) := IsSplitMono.mono _
  -- `PsiU J` is a split epi (with section `PgU J ≫ (EU J)⁻¹`)
  haveI hsplitE : IsSplitEpi (PsiU J) :=
    ⟨⟨SplitEpi.mk (PgU J ≫ (EU J).inv) hsec⟩⟩
  -- hence precomposition with `PsiU J` is a mono
  haveI hpreMono : Mono ((MonoidalClosed.pre (PsiU J)).app (𝟙_ LightCondAb)) :=
    mono_pre_app_of_section (PsiU J) (PgU J ≫ (EU J).inv) hsec
  haveI hPgMono : Mono (PgU J) := hPg_mono
  -- hence `WU J` is a mono
  haveI hW_mono : Mono (WU J) := by
    rw [WU_eq J]
    exact mono_comp ((MonoidalClosed.pre (PsiU J)).app (𝟙_ LightCondAb)) (PgU J)
  -- `WU J` is an isomorphism
  let E' : prodU J ⟶ dd (sigU J) := (EU J).inv ≫ doubleDualUnit (sigU J)
  have h2 : E' ≫ WU J = 𝟙 (prodU J) := by
    dsimp only [E']
    rw [Category.assoc, doubleDualUnit_comp_WU J, Iso.inv_hom_id]
  have h1 : WU J ≫ E' = 𝟙 (dd (sigU J)) := by
    refine (cancel_mono (WU J)).mp ?_
    show (WU J ≫ E') ≫ WU J = 𝟙 (dd (sigU J)) ≫ WU J
    rw [Category.assoc, h2, Category.comp_id, Category.id_comp]
  haveI hW_iso : IsIso (WU J) := ⟨E', h1, h2⟩
  -- conclude
  have hf : doubleDualUnit (sigU J) = (EU J).hom ≫ inv (WU J) := by
    rw [← Category.comp_id (doubleDualUnit (sigU J)), ← IsIso.hom_inv_id (WU J),
      ← Category.assoc, doubleDualUnit_comp_WU J]
  show IsIso (doubleDualUnit (sigU J))
  rw [hf]
  infer_instance

end

end Work.ANALYTIC.CechPt
