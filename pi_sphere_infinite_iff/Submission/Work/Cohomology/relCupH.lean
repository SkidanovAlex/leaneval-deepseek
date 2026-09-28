import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.relCupLeibniz

/-!
# The cup product on relative cohomology

For a topological space `X`, a subset `A ⊆ X` and a commutative ring `R`, the relative cup product
`relCup R X A : C^n(X,A) → C^m(X,A) → C^{n+m}(X,A)` (`Submission.Work.Cohomology.RelCup`) is a
bilinear pairing of the relative singular cochains which satisfies the Leibniz rule
(`Submission.Work.Cohomology.relCupLeibniz`).  This file proves that it descends to a pairing on
relative cohomology

  `relCupH : ∃ cup, ∀ n m a b ha hb, cup n m [a] [b] = [a ⌣ b]`,

exactly as `Submission.Work.Cohomology.cupH` does for the absolute cup product.

Since the only thing the descent argument needs about the relative cochain complex is that it is a
cochain complex of `R`-modules equipped with a bilinear product obeying the Leibniz rule, the
argument is carried out once, for an abstract cochain complex `K` and an abstract product `cup`
satisfying `LeibnizRule`; the relative statement is then the instantiation `K = relComplex R X A`,
`cup = relCup R X A`.

## Main results

* `exists_cup_of_generic` — the abstract descent;
* `LeibnizRule.relComplex_relCup` — the relative Leibniz rule is an instance of `LeibnizRule`;
* `iCycles_relCocycleOf` — the relative cocycle associated with a relative cocycle;
* `relCocycleOf_eq_cocycleOfK` — comparison of `relCocycleOf` with the generic construction;
* `relCupH` — the announced pairing on relative cohomology.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## The abstract descent argument -/

section Generic

variable {R : Type} [CommRing R]

/-- The Leibniz rule for a bilinear cochain-level product `cup` on a cochain complex `K`:

  `δ(a ⌣ b) = (δa) ⌣ b + (-1)^n · a ⌣ (δb)`. -/
def LeibnizRule (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) : Prop :=
  ∀ {n m : ℕ} (a : K.X n) (b : K.X m),
    (K.d (n + m) (n + m + 1)).hom (cup n m a b) =
      (Nat.add_right_comm n 1 m ▸ cup (n + 1) m ((K.d n (n + 1)).hom a) b) +
      ((-1 : R) ^ n) • cup n (m + 1) a ((K.d m (m + 1)).hom b)

/-! ### Bilinearity of `cup` -/

variable {K : CochainComplex (ModuleCat R) ℕ}
variable {cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)}

/-- The product is additive in its first argument. -/
lemma cupc_add_left (n m : ℕ) (a a' : K.X n) (b : K.X m) :
    cup n m (a + a') b = cup n m a b + cup n m a' b := by
  rw [map_add, LinearMap.add_apply]

/-- The product is homogeneous in its first argument. -/
lemma cupc_smul_left (n m : ℕ) (c : R) (a : K.X n) (b : K.X m) :
    cup n m (c • a) b = c • cup n m a b := by
  rw [map_smul, LinearMap.smul_apply]

/-- The product vanishes if its first argument does. -/
lemma cupc_zero_left (n m : ℕ) (b : K.X m) : cup n m 0 b = 0 := by
  rw [map_zero, LinearMap.zero_apply]

/-- The product is additive in its second argument. -/
lemma cupc_add_right (n m : ℕ) (a : K.X n) (b b' : K.X m) :
    cup n m a (b + b') = cup n m a b + cup n m a b' :=
  map_add (cup n m a) b b'

/-- The product is homogeneous in its second argument. -/
lemma cupc_smul_right (n m : ℕ) (c : R) (a : K.X n) (b : K.X m) :
    cup n m a (c • b) = c • cup n m a b :=
  map_smul (cup n m a) c b

/-- The product vanishes if its second argument does. -/
lemma cupc_zero_right (n m : ℕ) (a : K.X n) : cup n m a 0 = 0 :=
  map_zero (cup n m a)

/-! ### Elementary API for the cochain complex `K` -/

/-- The inclusion of the cycles is injective. -/
lemma iCycles_injective_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) :
    Function.Injective ((K.iCycles n).hom) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- The value of `liftCycles` on an element, formulated for the underlying elements of a
morphism out of a module object. -/
lemma liftCycles_i_apply_K (K : CochainComplex (ModuleCat R) ℕ) {n : ℕ} {A : ModuleCat R}
    (k : A ⟶ K.X n) (j : ℕ) (hj : (ComplexShape.up ℕ).next n = j)
    (hk : k ≫ K.d n j = 0) (a : A) :
    (K.iCycles n).hom ((K.liftCycles k j hj hk).hom a) = k.hom a := by
  have hli := HomologicalComplex.liftCycles_i K k j hj hk
  have h' := congrArg (fun (g : A ⟶ K.X n) => g.hom a) hli
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'

/-- The differential kills cycles. -/
lemma iCycles_d_apply_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ)
    (z : K.cycles n) : (K.d n (n + 1)).hom ((K.iCycles n).hom z) = 0 := by
  have h := HomologicalComplex.iCycles_d K n (n + 1)
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  have h3 : (K.d n (n + 1)).hom ((K.iCycles n).hom z) = 0 := by
    have hh := congrFun (congrArg DFunLike.coe h2) z
    simpa using hh
  exact h3

lemma iCycles_add_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) (z z' : K.cycles n) :
    (K.iCycles n).hom (z + z') = (K.iCycles n).hom z + (K.iCycles n).hom z' :=
  map_add ((K.iCycles n).hom) z z'

lemma iCycles_smul_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) (a : R) (z : K.cycles n) :
    (K.iCycles n).hom (a • z) = a • (K.iCycles n).hom z :=
  map_smul ((K.iCycles n).hom) a z

lemma homologyπ_add_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) (w w' : K.cycles n) :
    (K.homologyπ n).hom (w + w') = (K.homologyπ n).hom w + (K.homologyπ n).hom w' :=
  map_add ((K.homologyπ n).hom) w w'

lemma homologyπ_smul_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) (a : R) (w : K.cycles n) :
    (K.homologyπ n).hom (a • w) = a • (K.homologyπ n).hom w :=
  map_smul ((K.homologyπ n).hom) a w

/-- **Descent.** To define a morphism `Hⁿ(K) ⟶ A` it suffices to give a morphism on `n`-cycles
killing the image of the boundary map `K.toCycles (prev n) n`. -/
noncomputable def descH_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) {A : ModuleCat R}
    (k : K.cycles n ⟶ A)
    (hk : K.toCycles ((ComplexShape.up ℕ).prev n) n ≫ k = 0) : K.homology n ⟶ A :=
  Cofork.IsColimit.desc (K.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl) k (by simpa using hk)

/-- The computation rule for `descH_K`. -/
lemma homologyπ_descH_K (K : CochainComplex (ModuleCat R) ℕ) (n : ℕ) {A : ModuleCat R}
    (k : K.cycles n ⟶ A)
    (hk : K.toCycles ((ComplexShape.up ℕ).prev n) n ≫ k = 0) :
    K.homologyπ n ≫ descH_K K n k hk = k :=
  Cofork.IsColimit.π_desc (t := CokernelCofork.ofπ k (by simpa using hk))
    (K.homologyIsCokernel ((ComplexShape.up ℕ).prev n) n rfl)

/-- Computation rule for `descH_K` on the class of a cycle. -/
lemma descH_apply_K (K : CochainComplex (ModuleCat R) ℕ) {n : ℕ} {A : ModuleCat R}
    (k : K.cycles n ⟶ A)
    (hk : K.toCycles ((ComplexShape.up ℕ).prev n) n ≫ k = 0) (w : K.cycles n) :
    (descH_K K n k hk).hom ((K.homologyπ n).hom w) = k.hom w := by
  have h := homologyπ_descH_K K n k hk
  have h2 := congrArg (fun (g : K.cycles n ⟶ A) => g.hom w) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

lemma iCycles_toCycles_K (K : CochainComplex (ModuleCat R) ℕ) (i j : ℕ) (y : K.X i) :
    (K.iCycles j).hom ((K.toCycles i j).hom y) = (K.d i j).hom y := by
  have h := HomologicalComplex.toCycles_i K i j
  have h' := congrArg (fun (g : K.X i ⟶ K.X j) => g.hom y) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h'

lemma homologyπ_toCycles_K (K : CochainComplex (ModuleCat R) ℕ) (i j : ℕ) (y : K.X i) :
    (K.homologyπ j).hom ((K.toCycles i j).hom y) = 0 := by
  have h := HomologicalComplex.toCycles_comp_homologyπ K i j
  have h' := congrArg (fun (g : K.X i ⟶ K.homology j) => g.hom y) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h'

/-- A cycle whose `iCycles` image is a boundary of degree `n` has zero cohomology class. -/
lemma homologyπ_eq_zero_of_d_K (K : CochainComplex (ModuleCat R) ℕ) (n i : ℕ)
    (z : K.cycles n) (y : K.X i) (h : (K.iCycles n).hom z = (K.d i n).hom y) :
    (K.homologyπ n).hom z = 0 := by
  have hz : K.toCycles i n y = z := by
    apply iCycles_injective_K K n
    rw [iCycles_toCycles_K]
    exact h.symm
  rw [← hz]
  exact homologyπ_toCycles_K K i n y

/-- Transporting along an equality of degrees commutes with the underlying element. -/
lemma XIsoOfEq_hom_apply_K (K : CochainComplex (ModuleCat R) ℕ) {a b : ℕ} (h : a = b)
    (y : K.X a) : (K.XIsoOfEq h).hom y = h ▸ y := by
  cases h; rfl

lemma XIsoOfEq_inv_apply_K (K : CochainComplex (ModuleCat R) ℕ) {a b : ℕ} (h : a = b)
    (y : K.X b) : (K.XIsoOfEq h).inv y = h.symm ▸ y := by
  cases h; rfl

lemma eqRec_symm_eqRec_self_K (K : CochainComplex (ModuleCat R) ℕ) {a b : ℕ} (h : a = b)
    (x : K.X a) : h.symm ▸ (h ▸ x) = x := by
  cases h; rfl

lemma eqRec_zero_K (K : CochainComplex (ModuleCat R) ℕ) {a b : ℕ} (h : a = b) :
    (h ▸ (0 : K.X a)) = (0 : K.X b) := by
  cases h; rfl

/-- The cycle associated with a cocycle of the abstract complex `K`. -/
noncomputable def cocycleOfK (K : CochainComplex (ModuleCat R) ℕ) {n : ℕ} (α : K.X n)
    (h : (K.d n (n + 1)).hom α = 0) : K.cycles n :=
  (K.liftCycles
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) α))
    (n + 1) ((ComplexShape.up ℕ).next_eq' (i := n) (j := n + 1) rfl) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        ModuleCat.hom_zero, LinearMap.zero_apply]
      rw [LinearMap.toSpanSingleton_apply, map_smul, h, smul_zero])).hom 1

/-- The `iCycles` image of the cycle associated with a cocycle is the cocycle. -/
lemma iCycles_cocycleOfK (K : CochainComplex (ModuleCat R) ℕ) {n : ℕ} (α : K.X n)
    (h : (K.d n (n + 1)).hom α = 0) :
    (K.iCycles n).hom (cocycleOfK K α h) = α := by
  rw [cocycleOfK]
  rw [liftCycles_i_apply_K K (ModuleCat.ofHom (LinearMap.toSpanSingleton R (K.X n) α))
    (n + 1) _ _ (1 : R)]
  exact ofHom_toSpanSingleton_one R (K.X n) α

/-- `cocycleOfK` does not depend on the proof that the cochain is a cocycle. -/
lemma cocycleOfK_proof_irrel (K : CochainComplex (ModuleCat R) ℕ) {n : ℕ} (α : K.X n)
    (h h' : (K.d n (n + 1)).hom α = 0) : cocycleOfK K α h = cocycleOfK K α h' :=
  congrArg (fun h : (K.d n (n + 1)).hom α = 0 => cocycleOfK K α h) (Subsingleton.elim h h')

/-! ### The Leibniz rule, right and left -/

/-- Leibniz rule in the second variable: for a cocycle `α` of degree `n` and an arbitrary cochain
`x` of degree `m`, `δ(α ⌣ x) = (-1)ⁿ α ⌣ δx`. -/
lemma leibniz_right_K (K : CochainComplex (ModuleCat R) ℕ)
    {cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)}
    (hleib : LeibnizRule K cup) (n m : ℕ) (α : K.X n)
    (hα : (K.d n (n + 1)).hom α = 0) (x : K.X m) :
    (K.d (n + m) (n + (m + 1))).hom (cup n m α x) =
      ((-1 : R) ^ n) • cup n (m + 1) α ((K.d m (m + 1)).hom x) := by
  have h := hleib α x
  rw [hα, cupc_zero_left, eqRec_zero_K, zero_add] at h
  exact h

/-- Leibniz rule in the first variable: for an arbitrary cochain `x` of degree `n` and a cocycle
`β` of degree `m`, `δ(x ⌣ β) = δx ⌣ β`. -/
lemma leibniz_left_K (K : CochainComplex (ModuleCat R) ℕ)
    {cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)}
    (hleib : LeibnizRule K cup) (n m : ℕ) (x : K.X n) (β : K.X m)
    (hβ : (K.d m (m + 1)).hom β = 0) :
    (K.d (n + m) ((n + 1) + m)).hom (cup n m x β) = cup (n + 1) m ((K.d n (n + 1)).hom x) β := by
  have hh : (n + 1) + m = n + m + 1 := Nat.add_right_comm n 1 m
  set γ : K.X ((n + 1) + m) := cup (n + 1) m ((K.d n (n + 1)).hom x) β with hγ
  have h : (K.d (n + m) (n + m + 1)).hom (cup n m x β) = hh ▸ γ := by
    have h0 := hleib x β
    rw [hβ, cupc_zero_right, smul_zero, add_zero] at h0
    exact h0
  have hd := HomologicalComplex.d_comp_XIsoOfEq_inv K hh (n + m)
  have hd2 : (K.d (n + m) ((n + 1) + m)).hom (cup n m x β) =
      (K.XIsoOfEq hh).inv ((K.d (n + m) (n + m + 1)).hom (cup n m x β)) := by
    have hd' := congrArg (fun (g : K.X (n + m) ⟶ K.X ((n + 1) + m)) => g.hom (cup n m x β)) hd
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd'
    exact hd'.symm
  have key : (K.XIsoOfEq hh).inv (hh ▸ γ) = γ := by
    rw [XIsoOfEq_inv_apply_K, eqRec_symm_eqRec_self_K]
  calc (K.d (n + m) ((n + 1) + m)).hom (cup n m x β)
      = (K.XIsoOfEq hh).inv ((K.d (n + m) (n + m + 1)).hom (cup n m x β)) := hd2
    _ = (K.XIsoOfEq hh).inv (hh ▸ γ) := by rw [h]
    _ = γ := key

/-- The product of two cocycles of `K` is a cocycle. -/
lemma cup_cocycles_K (K : CochainComplex (ModuleCat R) ℕ)
    {cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)}
    (hleib : LeibnizRule K cup) (n m : ℕ) (z : K.cycles n) (w : K.cycles m) :
    (K.d (n + m) (n + m + 1)).hom (cup n m ((K.iCycles n).hom z) ((K.iCycles m).hom w)) = 0 := by
  have h := hleib ((K.iCycles n).hom z) ((K.iCycles m).hom w)
  rw [iCycles_d_apply_K, iCycles_d_apply_K] at h
  rw [cupc_zero_left, cupc_zero_right, smul_zero, add_zero, eqRec_zero_K] at h
  exact h

/-! ### The cup product of two cycles and its linearity -/

/-- The product of two cycles, as a cycle. -/
noncomputable def cupZK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) (w : K.cycles m) : K.cycles (n + m) :=
  cocycleOfK K (cup n m ((K.iCycles n).hom z) ((K.iCycles m).hom w))
    (cup_cocycles_K K hleib n m z w)

/-- The underlying cochain of a product of cycles. -/
lemma iCycles_cupZK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) (w : K.cycles m) :
    (K.iCycles (n + m)).hom (cupZK K cup hleib n m z w) =
      cup n m ((K.iCycles n).hom z) ((K.iCycles m).hom w) :=
  iCycles_cocycleOfK K _ _

lemma cupZK_add_left (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z z' : K.cycles n) (w : K.cycles m) :
    cupZK K cup hleib n m (z + z') w =
      cupZK K cup hleib n m z w + cupZK K cup hleib n m z' w := by
  apply iCycles_injective_K K (n + m)
  rw [iCycles_add_K, iCycles_cupZK, iCycles_add_K, iCycles_cupZK, iCycles_cupZK]
  exact cupc_add_left n m _ _ _

lemma cupZK_smul_left (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (a : R) (z : K.cycles n) (w : K.cycles m) :
    cupZK K cup hleib n m (a • z) w = a • cupZK K cup hleib n m z w := by
  apply iCycles_injective_K K (n + m)
  rw [iCycles_smul_K, iCycles_cupZK, iCycles_smul_K, iCycles_cupZK]
  exact cupc_smul_left n m a _ _

lemma cupZK_add_right (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) (w w' : K.cycles m) :
    cupZK K cup hleib n m z (w + w') =
      cupZK K cup hleib n m z w + cupZK K cup hleib n m z w' := by
  apply iCycles_injective_K K (n + m)
  rw [iCycles_add_K, iCycles_cupZK, iCycles_add_K, iCycles_cupZK, iCycles_cupZK]
  exact cupc_add_right n m _ _ _

lemma cupZK_smul_right (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (a : R) (z : K.cycles n) (w : K.cycles m) :
    cupZK K cup hleib n m z (a • w) = a • cupZK K cup hleib n m z w := by
  apply iCycles_injective_K K (n + m)
  rw [iCycles_smul_K, iCycles_cupZK, iCycles_smul_K, iCycles_cupZK]
  exact cupc_smul_right n m a _ _

/-- The product with a fixed cycle, as a linear map on the cycles of the other variable. -/
noncomputable def cupZWK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) : K.cycles m →ₗ[R] K.cycles (n + m) where
  toFun w := cupZK K cup hleib n m z w
  map_add' w w' := cupZK_add_right K cup hleib n m z w w'
  map_smul' a w := cupZK_smul_right K cup hleib n m a z w

lemma cupZWK_apply (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) (w : K.cycles m) :
    cupZWK K cup hleib n m z w = cupZK K cup hleib n m z w := rfl

/-! ### The two descent steps -/

/-- The map on cycles `w ↦ [α ⌣ w]`, where `α = iCycles z`. -/
noncomputable def chiZK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) : K.cycles m ⟶ K.homology (n + m) :=
  ModuleCat.ofHom (((K.homologyπ (n + m)).hom).comp (cupZWK K cup hleib n m z))

lemma chiZK_apply (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) (w : K.cycles m) :
    (chiZK K cup hleib n m z).hom w = (K.homologyπ (n + m)).hom (cupZK K cup hleib n m z w) :=
  rfl

/-- A boundary in the second variable is killed by `chiZK`. -/
lemma toCycles_chiZK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) :
    K.toCycles ((ComplexShape.up ℕ).prev m) m ≫ chiZK K cup hleib n m z = 0 := by
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
    have hchain : (K.iCycles (m' + 1)).hom ((K.toCycles m' (m' + 1)).hom x) =
        (K.d m' (m' + 1)).hom x :=
      iCycles_toCycles_K K m' (m' + 1) x
    have hZ : (chiZK K cup hleib n (m' + 1) z).hom ((K.toCycles m' (m' + 1)).hom x) = 0 := by
      rw [chiZK_apply]
      refine homologyπ_eq_zero_of_d_K K (n + (m' + 1)) (n + m')
        (cupZK K cup hleib n (m' + 1) z ((K.toCycles m' (m' + 1)).hom x))
        (((-1 : R) ^ n) • cup n m' ((K.iCycles n).hom z) x) ?_
      rw [iCycles_cupZK, hchain, map_smul]
      rw [leibniz_right_K K hleib n m' ((K.iCycles n).hom z) (iCycles_d_apply_K K n z) x,
        smul_smul, neg_one_pow_mul_self, one_smul]
    simpa using hZ

/-- The underlying linear map of the second descent: `[w] ↦ [α ⌣ w]`. -/
noncomputable def PhiFunK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) : K.homology m →ₗ[R] K.homology (n + m) :=
  (descH_K K m (chiZK K cup hleib n m z) (toCycles_chiZK K cup hleib n m z)).hom

lemma PhiFunK_apply (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) (w : K.cycles m) :
    PhiFunK K cup hleib n m z ((K.homologyπ m).hom w) =
      (chiZK K cup hleib n m z).hom w :=
  descH_apply_K K _ _ w

lemma PhiFunK_add (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z z' : K.cycles n) :
    PhiFunK K cup hleib n m (z + z') =
      PhiFunK K cup hleib n m z + PhiFunK K cup hleib n m z' := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((K.homologyπ m))).mp inferInstance y
  rw [LinearMap.add_apply, PhiFunK_apply, PhiFunK_apply, PhiFunK_apply, chiZK_apply, chiZK_apply,
    chiZK_apply, cupZK_add_left, homologyπ_add_K]

lemma PhiFunK_smul (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (a : R) (z : K.cycles n) :
    PhiFunK K cup hleib n m (a • z) = a • PhiFunK K cup hleib n m z := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((K.homologyπ m))).mp inferInstance y
  rw [LinearMap.smul_apply, PhiFunK_apply, PhiFunK_apply, chiZK_apply, chiZK_apply,
    cupZK_smul_left, homologyπ_smul_K]

/-- Descent in the second variable. -/
noncomputable def PhiK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) : K.cycles n →ₗ[R] (K.homology m →ₗ[R] K.homology (n + m)) where
  toFun := PhiFunK K cup hleib n m
  map_add' := PhiFunK_add K cup hleib n m
  map_smul' := PhiFunK_smul K cup hleib n m

lemma PhiK_apply (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) (w : K.cycles m) :
    PhiK K cup hleib n m z ((K.homologyπ m).hom w) = (chiZK K cup hleib n m z).hom w :=
  PhiFunK_apply K cup hleib n m z w

/-- A boundary in the first variable is killed by `PhiK`. -/
lemma toCycles_PhiK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) :
    K.toCycles ((ComplexShape.up ℕ).prev n) n ≫ ModuleCat.ofHom (PhiK K cup hleib n m) = 0 := by
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
    have hx : PhiK K cup hleib (n' + 1) m ((K.toCycles n' (n' + 1)).hom x) = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨w, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((K.homologyπ m))).mp inferInstance y
      rw [PhiK_apply, chiZK_apply]
      have hchain : (K.iCycles (n' + 1)).hom ((K.toCycles n' (n' + 1)).hom x) =
          (K.d n' (n' + 1)).hom x :=
        iCycles_toCycles_K K n' (n' + 1) x
      refine homologyπ_eq_zero_of_d_K K ((n' + 1) + m) (n' + m)
        (cupZK K cup hleib (n' + 1) m ((K.toCycles n' (n' + 1)).hom x) w)
        (cup n' m x ((K.iCycles m).hom w)) ?_
      rw [iCycles_cupZK, hchain]
      exact (leibniz_left_K K hleib n' m x ((K.iCycles m).hom w) (iCycles_d_apply_K K m w)).symm
    simpa using hx

/-- The cup product pairing on the cohomology of `K`. -/
noncomputable def cupHMapK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) :
    K.homology n ⟶ ModuleCat.of R (K.homology m →ₗ[R] K.homology (n + m)) :=
  descH_K K n (ModuleCat.ofHom (PhiK K cup hleib n m)) (toCycles_PhiK K cup hleib n m)

lemma cupHMapK_apply (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (z : K.cycles n) :
    (cupHMapK K cup hleib n m).hom ((K.homologyπ n).hom z) = PhiK K cup hleib n m z :=
  descH_apply_K K _ _ z

lemma cupZK_cocycleOfK (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup)
    (n m : ℕ) (α : K.X n) (β : K.X m)
    (hα : (K.d n (n + 1)).hom α = 0) (hβ : (K.d m (m + 1)).hom β = 0)
    (h : (K.d (n + m) (n + m + 1)).hom (cup n m α β) = 0) :
    cupZK K cup hleib n m (cocycleOfK K α hα) (cocycleOfK K β hβ) =
      cocycleOfK K (cup n m α β) h := by
  apply iCycles_injective_K K (n + m)
  rw [iCycles_cupZK, iCycles_cocycleOfK, iCycles_cocycleOfK, iCycles_cocycleOfK]

/-- **The abstract descent.**  A bilinear product on the cochains of a cochain complex `K`
satisfying the Leibniz rule induces a bilinear product on the cohomology of `K`, which on the
classes of two cocycles is the class of their product. -/
theorem exists_cup_of_generic (K : CochainComplex (ModuleCat R) ℕ)
    (cup : ∀ n m : ℕ, K.X n →ₗ[R] K.X m →ₗ[R] K.X (n + m)) (hleib : LeibnizRule K cup) :
    ∃ cupH : ∀ n m : ℕ, K.homology n →ₗ[R] K.homology m →ₗ[R] K.homology (n + m),
      ∀ (n m : ℕ) (α : K.X n) (β : K.X m)
        (hα : (K.d n (n + 1)).hom α = 0) (hβ : (K.d m (m + 1)).hom β = 0)
        (h : (K.d (n + m) (n + m + 1)).hom (cup n m α β) = 0),
        cupH n m ((K.homologyπ n).hom (cocycleOfK K α hα))
                 ((K.homologyπ m).hom (cocycleOfK K β hβ)) =
          (K.homologyπ (n + m)).hom (cocycleOfK K (cup n m α β) h) := by
  refine ⟨fun n m => (cupHMapK K cup hleib n m).hom, ?_⟩
  intro n m α β hα hβ h
  rw [cupHMapK_apply, PhiK_apply, chiZK_apply, cupZK_cocycleOfK K cup hleib n m α β hα hβ h]

end Generic

/-! ## The relative cup product on cohomology -/

section Relative

variable (R : Type) [CommRing R] (X : TopCat) (A : Set X)

/-- The differential of the relative cochain complex, evaluated. -/
lemma relComplex_d_apply {n : ℕ} (γ : (relComplex R X A).X n) :
    ((relComplex R X A).d n (n + 1)).hom γ = relDiffLM R X A n γ := by
  rw [relComplex_d]
  rfl

/-- The relative Leibniz rule is an instance of the abstract `LeibnizRule`. -/
lemma LeibnizRule.relComplex_relCup :
    LeibnizRule (relComplex R X A) (relCup R X A) := by
  intro n m a b
  simp only [relComplex_d_apply]
  exact relCupLeibniz R X A a b

/-- The `iCycles` image of the relative cycle associated with a relative cocycle is the cocycle. -/
lemma iCycles_relCocycleOf {n : ℕ} (a : relKern R X A n)
    (h : relDiffLM R X A n a = 0) :
    ((relComplex R X A).iCycles n).hom (relCocycleOf R X A a h) = a := by
  rw [relCocycleOf]
  rw [liftCycles_i_apply_K (relComplex R X A)
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R (relKern R X A n) a))
    (n + 1) _ _ (1 : R)]
  exact ofHom_toSpanSingleton_one R (relKern R X A n) a

/-- The relative cocycle associated with a relative cocycle agrees with the generic construction
`cocycleOfK`. -/
lemma relCocycleOf_eq_cocycleOfK {n : ℕ} (a : relKern R X A n)
    (h : relDiffLM R X A n a = 0) (h' : ((relComplex R X A).d n (n + 1)).hom a = 0) :
    relCocycleOf R X A a h = cocycleOfK (relComplex R X A) a h' := by
  apply iCycles_injective_K (relComplex R X A) n
  rw [iCycles_relCocycleOf, iCycles_cocycleOfK]

/-- The relative cohomology class of a relative cocycle is the generic class. -/
lemma relClassOf_eq_homologyπ_cocycleOfK {n : ℕ} (a : relKern R X A n)
    (h : relDiffLM R X A n a = 0) (h' : ((relComplex R X A).d n (n + 1)).hom a = 0) :
    relClassOf R X A a h =
      ((relComplex R X A).homologyπ n).hom (cocycleOfK (relComplex R X A) a h') := by
  rw [relClassOf, relCocycleOf_eq_cocycleOfK R X A a h h']

/-- **The cup product on relative cohomology.** -/
theorem relCupH (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    ∃ cup : ∀ n m : ℕ,
        Work.Cohomology.relCohomology R X A n →ₗ[R] Work.Cohomology.relCohomology R X A m →ₗ[R] Work.Cohomology.relCohomology R X A (n + m),
      ∀ (n m : ℕ) (a : Work.Cohomology.relKern R X A n) (b : Work.Cohomology.relKern R X A m)
        (ha : Work.Cohomology.relDiffLM R X A n a = 0) (hb : Work.Cohomology.relDiffLM R X A m b = 0),
        cup n m (Work.Cohomology.relClassOf R X A a ha) (Work.Cohomology.relClassOf R X A b hb) =
          Work.Cohomology.relClassOf R X A (Work.Cohomology.relCup R X A n m a b)
            (Work.Cohomology.relDiffLM_relCup_of_cocycles R X A a b ha hb) := by
  obtain ⟨cupH, hcupH⟩ :=
    exists_cup_of_generic (relComplex R X A) (relCup R X A) (LeibnizRule.relComplex_relCup R X A)
  refine ⟨fun n m => cupH n m, ?_⟩
  intro n m a b ha hb
  have ha' : ((relComplex R X A).d n (n + 1)).hom a = 0 := by
    rw [relComplex_d_apply]; exact ha
  have hb' : ((relComplex R X A).d m (m + 1)).hom b = 0 := by
    rw [relComplex_d_apply]; exact hb
  have hab' : ((relComplex R X A).d (n + m) (n + m + 1)).hom (relCup R X A n m a b) = 0 := by
    rw [relComplex_d_apply]
    exact relDiffLM_relCup_of_cocycles R X A a b ha hb
  rw [relClassOf_eq_homologyπ_cocycleOfK R X A a ha ha',
      relClassOf_eq_homologyπ_cocycleOfK R X A b hb hb',
      relClassOf_eq_homologyπ_cocycleOfK R X A (relCup R X A n m a b)
        (relDiffLM_relCup_of_cocycles R X A a b ha hb) hab']
  exact hcupH n m a b ha' hb' hab'

end Relative

end

end Work.Cohomology
