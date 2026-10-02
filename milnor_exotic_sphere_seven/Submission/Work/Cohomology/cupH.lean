import Mathlib
import Submission.Work.Cohomology.AlexanderWhitney
import Submission.Work.Cohomology.cupBilinear
import Submission.Work.Cohomology.cupLeibniz

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cup product on singular cohomology of a simplicial set

`Submission/Work/Cohomology/AlexanderWhitney.lean` defines the Alexander–Whitney cup product
`cup R X α β` of two singular *cochains* of a simplicial set `X`.  This file proves that it
descends to a bilinear pairing on singular *cohomology*
`Hⁿ(X;R) →ₗ[R] Hᵐ(X;R) →ₗ[R] Hⁿ⁺ᵐ(X;R)`,
which on the classes of two cocycles `α`, `β` (with `α ⌣ β` again a cocycle) is the class of
`α ⌣ β`:

`cupH (R) (X) : ∃ cup, ∀ n m α β hα hβ hαβ, cup n m [α] [β] = [α ⌣ β]`.

The proof is the standard descent argument.  Both ingredients are imported from the rest of the
cohomology chapter:

* the Leibniz rule `cupLeibniz` (`δ (α ⌣ β) = δα ⌣ β + (-1)ⁿ α ⌣ δβ`), which shows that the
  product of two cocycles is a cocycle and (using that `δβ = 0`) that the product of a coboundary
  with a cocycle is a coboundary — this is what makes the pairing well defined on cohomology;
* bilinearity of `cup` on the cochain level (`cupBilinear`), from which linearity of the pairing
  on cohomology follows.

The descent itself is carried out with the universal property of `K.homology n` as the cokernel of
the boundary map `K.toCycles (prev n) n : K.X (prev n) ⟶ K.cycles n` (`descH` below): to define a
map out of `Hⁿ` it suffices to give a map on `n`-cocycles which kills boundaries.

## Main definitions

* `descH` — the descent map `Hⁿ ⟶ A` induced by a map on `n`-cycles killing boundaries, with its
  computation rule `homologyπ_descH`;
* `cupZ`/`cupZW` — the cup product of two cocycles, as a cycle, together with its linearity;
* `cupHMap` — the induced map on cohomology, in two descent steps.

## Main results

* `cupH` — the existence of the cup product pairing on cohomology.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-! ## Elementary API for the singular cochain complex

We collect the small amount of "concrete" information about `SSetCochainComplex R X` that the
descent argument needs: its differential is `cochainDiff`, `iCycles` is injective, and the
`cochainDiff` of a cycle is zero. -/

/-- The differential of the singular cochain complex is `cochainDiff`. -/
lemma SSetCochainComplex_d_apply (n : ℕ) (γ : (SSetCochainComplex R X).X n) :
    ((SSetCochainComplex R X).d n (n + 1)).hom γ = cochainDiff R X γ := by
  rw [SSetCochainComplex_d]
  exact cochainDiffLM_apply R X n γ

/-- The inclusion of the cycles is injective. -/
lemma iCycles_injective (n : ℕ) :
    Function.Injective ((SSetCochainComplex R X).iCycles n).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The value of `liftCycles` on an element, formulated for the underlying elements of a
morphism out of a module object. -/
lemma liftCycles_i_apply {n : ℕ} {A : ModuleCat R}
    (k : A ⟶ (SSetCochainComplex R X).X n) (j : ℕ)
    (hj : (ComplexShape.up ℕ).next n = j)
    (hk : k ≫ (SSetCochainComplex R X).d n j = 0) (a : A) :
    (SSetCochainComplex R X).iCycles n
      (((SSetCochainComplex R X).liftCycles k j hj hk).hom a) = k.hom a := by
  have hli := HomologicalComplex.liftCycles_i (SSetCochainComplex R X) k j hj hk
  have h' := congrArg (fun (g : A ⟶ (SSetCochainComplex R X).X n) => g.hom a) hli
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'

/-- The linear functional `c ↦ c • x` evaluated at `1` is `x`. -/
lemma ofHom_toSpanSingleton_one (M : Type) [AddCommGroup M] [Module R M] (α : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R M α)).hom (1 : R) = α := by
  rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]

/-- The cycle built from a cocycle with the help of `liftCycles` maps to the cocycle. -/
lemma iCycles_toSpanSingleton_liftCycles {n : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) (j : ℕ)
    (hj : (ComplexShape.up ℕ).next n = j)
    (hk : (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) α)) ≫
      (SSetCochainComplex R X).d n j = 0) :
    (SSetCochainComplex R X).iCycles n
      (((SSetCochainComplex R X).liftCycles (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) α)) j hj hk).hom 1) = α := by
  rw [liftCycles_i_apply R X (ModuleCat.ofHom (LinearMap.toSpanSingleton R
      ((X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) α)) j hj hk (1 : R)]
  exact ofHom_toSpanSingleton_one R _ α

/-- The cycle associated with a cocycle has the cocycle as its image under `iCycles`. -/
lemma iCycles_cocycleOf {n : ℕ} (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (h : cochainDiff R X α = 0) :
    (SSetCochainComplex R X).iCycles n (cocycleOf R X α h) = α := by
  rw [cocycleOf]
  exact iCycles_toSpanSingleton_liftCycles R X α (n + 1) _ _

/-- `cocycleOf` is additive. -/
lemma cocycleOf_add {n : ℕ} (α α' : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (h : cochainDiff R X (α + α') = 0) (hα : cochainDiff R X α = 0)
    (hα' : cochainDiff R X α' = 0) :
    cocycleOf R X (α + α') h = cocycleOf R X α hα + cocycleOf R X α' hα' := by
  apply iCycles_injective R X n
  rw [map_add, iCycles_cocycleOf, iCycles_cocycleOf, iCycles_cocycleOf]

/-- `cocycleOf` is homogeneous. -/
lemma cocycleOf_smul {n : ℕ} (a : R) (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (h : cochainDiff R X (a • α) = 0) (hα : cochainDiff R X α = 0) :
    cocycleOf R X (a • α) h = a • cocycleOf R X α hα := by
  apply iCycles_injective R X n
  rw [map_smul, iCycles_cocycleOf, iCycles_cocycleOf]

/-- The `cochainDiff` of a cycle is zero. -/
lemma cochainDiff_iCycles (n : ℕ) (z : (SSetCochainComplex R X).cycles n) :
    cochainDiff R X ((SSetCochainComplex R X).iCycles n z) = 0 := by
  have h := HomologicalComplex.iCycles_d (SSetCochainComplex R X) n (n + 1)
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  have h3 : ((SSetCochainComplex R X).d n (n + 1)).hom
      ((SSetCochainComplex R X).iCycles n z) = 0 := by
    have hh := congrFun (congrArg DFunLike.coe h2) z
    simpa using hh
  rw [SSetCochainComplex_d_apply] at h3
  exact h3

/-! ## Maps out of cohomology

`K.homology n` is the cokernel of `K.toCycles (prev n) n : K.X (prev n) ⟶ K.cycles n`; this gives
the universal property used below. -/

/-- **Descent.** To define a morphism `Hⁿ(X;R) ⟶ A` out of the `n`-th cohomology it suffices to
give a morphism on `n`-cycles which kills the image of the boundary map
`K.toCycles (prev n) n : K.X (prev n) ⟶ K.cycles n`. -/
noncomputable def descH (n : ℕ) {A : ModuleCat R}
    (k : (SSetCochainComplex R X).cycles n ⟶ A)
    (hk : (SSetCochainComplex R X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ k = 0) :
    (SSetCochainComplex R X).homology n ⟶ A :=
  Cofork.IsColimit.desc ((SSetCochainComplex R X).homologyIsCokernel
    ((ComplexShape.up ℕ).prev n) n rfl) k (by simpa using hk)

/-- The computation rule for `descH`. -/
lemma homologyπ_descH (n : ℕ) {A : ModuleCat R}
    (k : (SSetCochainComplex R X).cycles n ⟶ A)
    (hk : (SSetCochainComplex R X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ k = 0) :
    (SSetCochainComplex R X).homologyπ n ≫ descH R X n k hk = k :=
  Cofork.IsColimit.π_desc (t := CokernelCofork.ofπ k (by simpa using hk))
    ((SSetCochainComplex R X).homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl)

/-- The image of `toCycles` under `iCycles` is the boundary. -/
lemma iCycles_toCycles (i j : ℕ) (y : (SSetCochainComplex R X).X i) :
    (SSetCochainComplex R X).iCycles j ((SSetCochainComplex R X).toCycles i j y)
      = ((SSetCochainComplex R X).d i j).hom y := by
  have h := HomologicalComplex.toCycles_i (SSetCochainComplex R X) i j
  have h' := congrArg (fun (g : (SSetCochainComplex R X).X i ⟶ (SSetCochainComplex R X).X j)
    => g.hom y) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'

/-- Boundaries have zero class in cohomology. -/
lemma homologyπ_toCycles (i j : ℕ) (y : (SSetCochainComplex R X).X i) :
    (SSetCochainComplex R X).homologyπ j ((SSetCochainComplex R X).toCycles i j y) = 0 := by
  have h := HomologicalComplex.toCycles_comp_homologyπ (SSetCochainComplex R X) i j
  have h' := congrArg (fun (g : (SSetCochainComplex R X).X i ⟶
    (SSetCochainComplex R X).homology j) => g.hom y) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h'

/-- A cycle whose image under `iCycles` is a boundary of degree `n` (i.e. is
`K.d i n y` for some `y : K.X i`) has zero cohomology class. -/
lemma homologyπ_eq_zero_of_d (n i : ℕ) (z : (SSetCochainComplex R X).cycles n)
    (y : (SSetCochainComplex R X).X i)
    (h : (SSetCochainComplex R X).iCycles n z = ((SSetCochainComplex R X).d i n).hom y) :
    (SSetCochainComplex R X).homologyπ n z = 0 := by
  have hz : (SSetCochainComplex R X).toCycles i n y = z := by
    apply iCycles_injective R X n
    rw [iCycles_toCycles]
    exact h.symm
  rw [← hz]
  exact homologyπ_toCycles R X i n y


/-! ## The two inputs: bilinearity and the Leibniz rule

Both are proved elsewhere in the cohomology chapter (`cupBilinear` and `cupLeibniz`).  To keep the
descent argument independent of the exact form in which they are stated we take them as explicit
hypotheses here; `cupH` below instantiates them. -/

/-- Bilinearity of the Alexander–Whitney cup product in each variable. -/
def CupBilin : Prop := ∀ n m : ℕ,
    (∀ (α α' : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
       (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R),
      cup R X (α + α') β = cup R X α β + cup R X α' β) ∧
    (∀ (a : R) (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
       (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R),
      cup R X (a • α) β = a • cup R X α β) ∧
    (∀ (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
       (β β' : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R),
      cup R X α (β + β') = cup R X α β + cup R X α β') ∧
    (∀ (a : R) (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
       (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R),
      cup R X α (a • β) = a • cup R X α β)

/-- The Leibniz rule for the Alexander–Whitney cup product. -/
def Leibniz : Prop := ∀ {n m : ℕ}
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R),
    cochainDiff R X (cup R X α β) =
      (Nat.add_right_comm n 1 m ▸ cup R X (cochainDiff R X α) β) +
      ((-1 : R) ^ n) • (cup R X α (cochainDiff R X β))

/-! ### Bilinearity -/

lemma cup_add_left (hbil : CupBilin R X) (n m : ℕ)
    (α α' : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    cup R X (α + α') β = cup R X α β + cup R X α' β :=
  (hbil n m).1 α α' β

lemma cup_smul_left (hbil : CupBilin R X) (n m : ℕ) (a : R)
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    cup R X (a • α) β = a • cup R X α β :=
  (hbil n m).2.1 a α β

lemma cup_add_right (hbil : CupBilin R X) (n m : ℕ)
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β β' : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    cup R X α (β + β') = cup R X α β + cup R X α β' :=
  (hbil n m).2.2.1 α β β'

lemma cup_smul_right (hbil : CupBilin R X) (n m : ℕ) (a : R)
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    cup R X α (a • β) = a • cup R X α β :=
  (hbil n m).2.2.2 a α β

/-- The cup product is `0` as soon as its first argument is `0`. -/
lemma cup_zero_left (hbil : CupBilin R X) (n m : ℕ)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    cup R X (0 : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) β = 0 := by
  have h := cup_smul_left R X hbil n m (0 : R)
    (0 : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) β
  simpa using h

/-- The cup product is `0` as soon as its second argument is `0`. -/
lemma cup_zero_right (hbil : CupBilin R X) (n m : ℕ)
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R) :
    cup R X α (0 : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) = 0 := by
  have h := cup_smul_right R X hbil n m (0 : R) α
    (0 : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R)
  simpa using h

lemma neg_one_pow_mul_self (n : ℕ) : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← mul_pow, neg_mul_neg, one_mul, one_pow]

/-! ### Casts along index identifications

The Leibniz rule is stated with the index identification `(n+1)+m = n+m+1`; these lemmas move
between the two descriptions of the degree. -/

lemma eqRec_zero {a b : ℕ} (h : a = b) :
    (h ▸ (0 : (SSetCochainComplex R X).X a)) = (0 : (SSetCochainComplex R X).X b) := by
  cases h; rfl

lemma eqRec_symm_eqRec_self {a b : ℕ} (h : a = b) (x : (SSetCochainComplex R X).X a) :
    h.symm ▸ (h ▸ x) = x := by
  cases h; rfl

lemma XIsoOfEq_hom_apply {a b : ℕ} (h : a = b) (y : (SSetCochainComplex R X).X a) :
    (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) h).hom y = h ▸ y := by
  cases h; rfl

lemma XIsoOfEq_inv_apply {a b : ℕ} (h : a = b) (y : (SSetCochainComplex R X).X b) :
    (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) h).inv y = h.symm ▸ y := by
  cases h; rfl

/-! ### Consequences of the Leibniz rule -/

/-- The product of two cocycles is a cocycle. -/
lemma cochainDiff_cup_cocycles (_hleib : Leibniz R X) (hbil : CupBilin R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    cochainDiff R X (cup R X ((SSetCochainComplex R X).iCycles n z)
      ((SSetCochainComplex R X).iCycles m w)) = 0 := by
  have h := _hleib ((SSetCochainComplex R X).iCycles n z) ((SSetCochainComplex R X).iCycles m w)
  rw [cochainDiff_iCycles, cochainDiff_iCycles] at h
  rw [cup_zero_left R X hbil, cup_zero_right R X hbil, smul_zero, add_zero,
    eqRec_zero R X] at h
  exact h

/-- Leibniz rule in the second variable: for a cocycle `α` of degree `n` and an arbitrary cochain
`x` of degree `m`, `δ(α ⌣ x) = (-1)ⁿ α ⌣ δx`. -/
lemma leibniz_right (hleib : Leibniz R X) (hbil : CupBilin R X) (n m : ℕ)
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (hα : cochainDiff R X α = 0)
    (x : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) :
    ((SSetCochainComplex R X).d (n + m) (n + (m + 1))).hom (cup R X α x) =
      ((-1 : R) ^ n) • cup R X α (cochainDiff R X x) := by
  have h := hleib α x
  rw [hα, cup_zero_left R X hbil, eqRec_zero R X, zero_add] at h
  exact (SSetCochainComplex_d_apply R X (n + m) (cup R X α x)).trans h

/-- Leibniz rule in the first variable: for an arbitrary cochain `x` of degree `n` and a cocycle
`β` of degree `m`, `δ(x ⌣ β) = δx ⌣ β`. -/
lemma leibniz_left (hleib : Leibniz R X) (hbil : CupBilin R X) (n m : ℕ)
    (x : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R) (hβ : cochainDiff R X β = 0) :
    ((SSetCochainComplex R X).d (n + m) ((n + 1) + m)).hom (cup R X x β) =
      cup R X (cochainDiff R X x) β := by
  have hh : (n + 1) + m = n + m + 1 := Nat.add_right_comm n 1 m
  set γ : (SSetCochainComplex R X).X ((n + 1) + m) := cup R X (cochainDiff R X x) β with hγ
  have h : ((SSetCochainComplex R X).d (n + m) (n + m + 1)).hom (cup R X x β) = hh ▸ γ := by
    have h0 := hleib x β
    rw [hβ, cup_zero_right R X hbil, smul_zero, add_zero] at h0
    exact (SSetCochainComplex_d_apply R X (n + m) (cup R X x β)).trans h0
  have hd := HomologicalComplex.d_comp_XIsoOfEq_inv (SSetCochainComplex R X) hh (n + m)
  have hd2 : ((SSetCochainComplex R X).d (n + m) ((n + 1) + m)).hom (cup R X x β) =
      (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).inv
        (((SSetCochainComplex R X).d (n + m) (n + m + 1)).hom (cup R X x β)) := by
    have hd' := congrArg (fun (g : (SSetCochainComplex R X).X (n + m) ⟶
      (SSetCochainComplex R X).X ((n + 1) + m)) => g.hom (cup R X x β)) hd
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd'
    exact hd'.symm
  have key : (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).inv (hh ▸ γ) = γ := by
    rw [XIsoOfEq_inv_apply R X hh, eqRec_symm_eqRec_self]
  calc ((SSetCochainComplex R X).d (n + m) ((n + 1) + m)).hom (cup R X x β)
      = (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).inv
          (((SSetCochainComplex R X).d (n + m) (n + m + 1)).hom (cup R X x β)) := hd2
    _ = (HomologicalComplex.XIsoOfEq (SSetCochainComplex R X) hh).inv (hh ▸ γ) := by rw [h]
    _ = γ := key

/-! ## Mirror lemmas

Rewriting with the pointwise form of these facts is more robust than relying on the coercion of
morphisms of `ModuleCat` to functions, so we record them explicitly. -/

lemma iCycles_add (n : ℕ) (z z' : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).iCycles n (z + z') =
      (SSetCochainComplex R X).iCycles n z + (SSetCochainComplex R X).iCycles n z' :=
  map_add ((SSetCochainComplex R X).iCycles n).hom z z'

lemma iCycles_smul (n : ℕ) (a : R) (z : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).iCycles n (a • z) =
      a • (SSetCochainComplex R X).iCycles n z :=
  map_smul ((SSetCochainComplex R X).iCycles n).hom a z

lemma homologyπ_add (n : ℕ) (w w' : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).homologyπ n (w + w') =
      (SSetCochainComplex R X).homologyπ n w + (SSetCochainComplex R X).homologyπ n w' :=
  map_add ((SSetCochainComplex R X).homologyπ n).hom w w'

lemma homologyπ_smul (n : ℕ) (a : R) (w : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).homologyπ n (a • w) =
      a • (SSetCochainComplex R X).homologyπ n w :=
  map_smul ((SSetCochainComplex R X).homologyπ n).hom a w

/-! ## The cup product of two cocycles -/

/-- The Alexander–Whitney product of two cocycles, as a cycle.  This is well defined because the
product of two cocycles is again a cocycle (`cochainDiff_cup_cocycles`). -/
noncomputable def cupZ (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    (SSetCochainComplex R X).cycles (n + m) :=
  cocycleOf R X (cup R X ((SSetCochainComplex R X).iCycles n z)
    ((SSetCochainComplex R X).iCycles m w))
    (cochainDiff_cup_cocycles R X hleib hbil n m z w)

/-- The underlying cochain of `cupZ` is the cup product of the underlying cochains. -/
lemma iCycles_cupZ (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    (SSetCochainComplex R X).iCycles (n + m) (cupZ R X hbil hleib n m z w) =
      cup R X ((SSetCochainComplex R X).iCycles n z)
        ((SSetCochainComplex R X).iCycles m w) :=
  iCycles_cocycleOf R X _ _

/-- Additivity of `cupZ` in its first variable. -/
lemma cupZ_add_left (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z z' : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    cupZ R X hbil hleib n m (z + z') w =
      cupZ R X hbil hleib n m z w + cupZ R X hbil hleib n m z' w := by
  apply iCycles_injective R X (n + m)
  rw [iCycles_add, iCycles_cupZ, iCycles_add, iCycles_cupZ, iCycles_cupZ]
  exact cup_add_left R X hbil n m _ _ _

/-- Homogeneity of `cupZ` in its first variable. -/
lemma cupZ_smul_left (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ) (a : R)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    cupZ R X hbil hleib n m (a • z) w =
      a • cupZ R X hbil hleib n m z w := by
  apply iCycles_injective R X (n + m)
  rw [iCycles_smul, iCycles_cupZ, iCycles_smul, iCycles_cupZ]
  exact cup_smul_left R X hbil n m a _ _

/-- Additivity of `cupZ` in its second variable. -/
lemma cupZ_add_right (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w w' : (SSetCochainComplex R X).cycles m) :
    cupZ R X hbil hleib n m z (w + w') =
      cupZ R X hbil hleib n m z w + cupZ R X hbil hleib n m z w' := by
  apply iCycles_injective R X (n + m)
  rw [iCycles_add, iCycles_cupZ, iCycles_add, iCycles_cupZ, iCycles_cupZ]
  exact cup_add_right R X hbil n m _ _ _

/-- Homogeneity of `cupZ` in its second variable. -/
lemma cupZ_smul_right (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ) (a : R)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    cupZ R X hbil hleib n m z (a • w) =
      a • cupZ R X hbil hleib n m z w := by
  apply iCycles_injective R X (n + m)
  rw [iCycles_smul, iCycles_cupZ, iCycles_smul, iCycles_cupZ]
  exact cup_smul_right R X hbil n m a _ _

/-- The cup product with a fixed cocycle, as a linear map on the cycles of the other variable. -/
noncomputable def cupZW (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).cycles m →ₗ[R] (SSetCochainComplex R X).cycles (n + m) where
  toFun w := cupZ R X hbil hleib n m z w
  map_add' w w' := cupZ_add_right R X hbil hleib n m z w w'
  map_smul' a w := cupZ_smul_right R X hbil hleib n m a z w

lemma cupZW_apply (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    cupZW R X hbil hleib n m z w = cupZ R X hbil hleib n m z w := rfl

/-! ## The two descent steps -/

/-- Computation rule for `descH` on the class of a cycle. -/
lemma descH_apply {n : ℕ} {A : ModuleCat R} (k : (SSetCochainComplex R X).cycles n ⟶ A)
    (hk : (SSetCochainComplex R X).toCycles ((ComplexShape.up ℕ).prev n) n ≫ k = 0)
    (w : (SSetCochainComplex R X).cycles n) :
    (descH R X n k hk).hom ((SSetCochainComplex R X).homologyπ n w) = k.hom w := by
  have h := homologyπ_descH R X n k hk
  have h2 := congrArg (fun (g : (SSetCochainComplex R X).cycles n ⟶ A) => g.hom w) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-- The map on cycles `w ↦ [α ⌣ w]`, where `α = iCycles z` is a fixed cocycle. -/
noncomputable def chiZ (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).cycles m ⟶ (SSetCochainComplex R X).homology (n + m) :=
  ModuleCat.ofHom (((SSetCochainComplex R X).homologyπ (n + m)).hom.comp
    (cupZW R X hbil hleib n m z))

lemma chiZ_apply (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    chiZ R X hbil hleib n m z w =
      (SSetCochainComplex R X).homologyπ (n + m) (cupZ R X hbil hleib n m z w) :=
  rfl

/-- A boundary in the second variable is killed by `chiZ`: the product of a cocycle with a
coboundary is a coboundary, by the Leibniz rule. -/
lemma toCycles_chiZ (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).toCycles ((ComplexShape.up ℕ).prev m) m ≫
      chiZ R X hbil hleib n m z = 0 := by
  generalize hpm : (ComplexShape.up ℕ).prev m = pm
  rcases m with _ | m'
  · have hpm' : pm = 0 := by rw [← hpm]; simp
    rw [hpm']
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpm' : pm = m' := by rw [← hpm]; simp
    rw [hpm']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hchain : (SSetCochainComplex R X).iCycles (m' + 1)
        ((SSetCochainComplex R X).toCycles m' (m' + 1) x) = cochainDiff R X x := by
      rw [iCycles_toCycles]
      exact SSetCochainComplex_d_apply R X m' x
    have hZ : chiZ R X hbil hleib n (m' + 1) z
        ((SSetCochainComplex R X).toCycles m' (m' + 1) x) = 0 := by
      rw [chiZ_apply]
      refine homologyπ_eq_zero_of_d R X (n + (m' + 1)) (n + m')
        (cupZ R X hbil hleib n (m' + 1) z ((SSetCochainComplex R X).toCycles m' (m' + 1) x))
        (((-1 : R) ^ n) • cup R X ((SSetCochainComplex R X).iCycles n z) x) ?_
      rw [iCycles_cupZ, hchain, map_smul]
      rw [leibniz_right R X hleib hbil n m' ((SSetCochainComplex R X).iCycles n z)
        (cochainDiff_iCycles R X n z) x, smul_smul, neg_one_pow_mul_self, one_smul]
    simpa using hZ

/-- The underlying linear map of the second descent: `[w] ↦ [α ⌣ w]`. -/
noncomputable def PhiFun (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) :
    (SSetCochainComplex R X).homology m →ₗ[R] (SSetCochainComplex R X).homology (n + m) :=
  (descH R X m (chiZ R X hbil hleib n m z) (toCycles_chiZ R X hbil hleib n m z)).hom

lemma PhiFun_apply (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    PhiFun R X hbil hleib n m z ((SSetCochainComplex R X).homologyπ m w) =
      chiZ R X hbil hleib n m z w :=
  descH_apply R X _ _ w

lemma PhiFun_add (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z z' : (SSetCochainComplex R X).cycles n) :
    PhiFun R X hbil hleib n m (z + z') =
      PhiFun R X hbil hleib n m z + PhiFun R X hbil hleib n m z' := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((SSetCochainComplex R X).homologyπ m)).mp inferInstance y
  rw [LinearMap.add_apply, PhiFun_apply, PhiFun_apply, PhiFun_apply, chiZ_apply, chiZ_apply,
    chiZ_apply, cupZ_add_left, homologyπ_add]

lemma PhiFun_smul (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ) (a : R)
    (z : (SSetCochainComplex R X).cycles n) :
    PhiFun R X hbil hleib n m (a • z) = a • PhiFun R X hbil hleib n m z := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((SSetCochainComplex R X).homologyπ m)).mp inferInstance y
  rw [LinearMap.smul_apply, PhiFun_apply, PhiFun_apply, chiZ_apply, chiZ_apply, cupZ_smul_left,
    homologyπ_smul]

/-- Descent in the second variable: for a fixed cocycle `z`, the linear map
`Hᵐ(X;R) ⟶ Hⁿ⁺ᵐ(X;R)`, `[w] ↦ [α ⌣ w]`, where `α = iCycles z`. -/
noncomputable def Phi (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ) :
    (SSetCochainComplex R X).cycles n →ₗ[R]
      ((SSetCochainComplex R X).homology m →ₗ[R] (SSetCochainComplex R X).homology (n + m)) where
  toFun := PhiFun R X hbil hleib n m
  map_add' := PhiFun_add R X hbil hleib n m
  map_smul' := PhiFun_smul R X hbil hleib n m

lemma Phi_apply (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) (w : (SSetCochainComplex R X).cycles m) :
    Phi R X hbil hleib n m z ((SSetCochainComplex R X).homologyπ m w) =
      chiZ R X hbil hleib n m z w :=
  PhiFun_apply R X hbil hleib n m z w

/-- A boundary in the first variable is killed by `Phi`: the product of a coboundary with a
cocycle is a coboundary, by the Leibniz rule. -/
lemma toCycles_Phi (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ) :
    (SSetCochainComplex R X).toCycles ((ComplexShape.up ℕ).prev n) n ≫
      ModuleCat.ofHom (Phi R X hbil hleib n m) = 0 := by
  generalize hpn : (ComplexShape.up ℕ).prev n = pn
  rcases n with _ | n'
  · have hpn' : pn = 0 := by rw [← hpn]; simp
    rw [hpn']
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpn' : pn = n' := by rw [← hpn]; simp
    rw [hpn']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : Phi R X hbil hleib (n' + 1) m
        ((SSetCochainComplex R X).toCycles n' (n' + 1) x) = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨w, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((SSetCochainComplex R X).homologyπ m)).mp inferInstance y
      rw [Phi_apply, chiZ_apply]
      have hchain : (SSetCochainComplex R X).iCycles (n' + 1)
          ((SSetCochainComplex R X).toCycles n' (n' + 1) x) = cochainDiff R X x := by
        rw [iCycles_toCycles]
        exact SSetCochainComplex_d_apply R X n' x
      refine homologyπ_eq_zero_of_d R X ((n' + 1) + m) (n' + m)
        (cupZ R X hbil hleib (n' + 1) m ((SSetCochainComplex R X).toCycles n' (n' + 1) x) w)
        (cup R X x ((SSetCochainComplex R X).iCycles m w)) ?_
      rw [iCycles_cupZ, hchain]
      exact (leibniz_left R X hleib hbil n' m x ((SSetCochainComplex R X).iCycles m w)
        (cochainDiff_iCycles R X m w)).symm
    simpa using hx

/-- The cup product pairing on cohomology: `Hⁿ(X;R) ⟶ Hᵐ(X;R) ⟶ Hⁿ⁺ᵐ(X;R)`. -/
noncomputable def cupHMap (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ) :
    (SSetCochainComplex R X).homology n ⟶
      ModuleCat.of R ((SSetCochainComplex R X).homology m →ₗ[R]
        (SSetCochainComplex R X).homology (n + m)) :=
  descH R X n (ModuleCat.ofHom (Phi R X hbil hleib n m)) (toCycles_Phi R X hbil hleib n m)

lemma cupHMap_apply (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (z : (SSetCochainComplex R X).cycles n) :
    (cupHMap R X hbil hleib n m).hom ((SSetCochainComplex R X).homologyπ n z) =
      Phi R X hbil hleib n m z :=
  descH_apply R X _ _ z

lemma cupZ_cocycleOf (hbil : CupBilin R X) (hleib : Leibniz R X) (n m : ℕ)
    (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0)
    (h : cochainDiff R X (cup R X α β) = 0) :
    cupZ R X hbil hleib n m (cocycleOf R X α hα) (cocycleOf R X β hβ) =
      cocycleOf R X (cup R X α β) h := by
  apply iCycles_injective R X (n + m)
  rw [iCycles_cupZ, iCycles_cocycleOf, iCycles_cocycleOf, iCycles_cocycleOf]

/-- `cocycleOf` does not depend on the proof that the cochain is a cocycle. -/
lemma cocycleOf_proof_irrel {n : ℕ} (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
    (h h' : cochainDiff R X α = 0) :
    cocycleOf R X α h = cocycleOf R X α h' :=
  congrArg (fun h : cochainDiff R X α = 0 => cocycleOf R X α h) (Subsingleton.elim h h')

/-- The cup product pairing on cohomology, from the two inputs. -/
lemma exists_cup_of (hbil : CupBilin R X) (hleib : Leibniz R X) :
    ∃ cup : ∀ n m : ℕ,
        (SSetCochainComplex R X).homology n →ₗ[R]
        (SSetCochainComplex R X).homology m →ₗ[R]
        (SSetCochainComplex R X).homology (n + m),
      ∀ (n m : ℕ) (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
        (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R)
        (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0)
        (hαβ : cochainDiff R X (Work.Cohomology.cup R X α β) = 0),
        cup n m (cohomologyClassOf R X α hα) (cohomologyClassOf R X β hβ) =
          cohomologyClassOf R X (Work.Cohomology.cup R X α β) hαβ := by
  refine ⟨fun n m => (cupHMap R X hbil hleib n m).hom, ?_⟩
  intro n m α β hα hβ hαβ
  rw [show cohomologyClassOf R X α hα
      = (SSetCochainComplex R X).homologyπ n (cocycleOf R X α hα) from rfl,
    show cohomologyClassOf R X β hβ
      = (SSetCochainComplex R X).homologyπ m (cocycleOf R X β hβ) from rfl,
    cupHMap_apply R X hbil hleib n m (cocycleOf R X α hα)]
  rw [Phi_apply R X hbil hleib n m (cocycleOf R X α hα) (cocycleOf R X β hβ),
    chiZ_apply R X hbil hleib n m (cocycleOf R X α hα) (cocycleOf R X β hβ)]
  rw [cupZ_cocycleOf R X hbil hleib n m α β hα hβ hαβ]
  exact congrArg ((SSetCochainComplex R X).homologyπ (n + m))
    (cocycleOf_proof_irrel R X (Work.Cohomology.cup R X α β) _ hαβ)

/-! ## The statement to be proved -/

theorem cupH (R : Type) [CommRing R] (X : SSet) :
    ∃ cup : ∀ n m : ℕ,
        (Work.Cohomology.SSetCochainComplex R X).homology n →ₗ[R]
        (Work.Cohomology.SSetCochainComplex R X).homology m →ₗ[R]
        (Work.Cohomology.SSetCochainComplex R X).homology (n + m),
      ∀ (n m : ℕ) (α : (X.chainComplex (ModuleCat.of R R)).X n →ₗ[R] R)
        (β : (X.chainComplex (ModuleCat.of R R)).X m →ₗ[R] R)
        (hα : Work.Cohomology.cochainDiff R X α = 0)
        (hβ : Work.Cohomology.cochainDiff R X β = 0)
        (hαβ : Work.Cohomology.cochainDiff R X (Work.Cohomology.cup R X α β) = 0),
        cup n m (Work.Cohomology.cohomologyClassOf R X α hα)
                (Work.Cohomology.cohomologyClassOf R X β hβ) =
          Work.Cohomology.cohomologyClassOf R X (Work.Cohomology.cup R X α β) hαβ :=
  exists_cup_of R X (cupBilinear R X) (cupLeibniz R X)

end

end Work.Cohomology
