import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.CupRing
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Change of coefficients `ℤ → ℤ/p` for the cochains of a simplicial set

This file constructs, for a simplicial set `X` and a prime `p`, the reduction map

* `kappa p X n : C_n(X; ℤ) → C_n(X; ℤ/p)` on chains (the extension of scalars map, i.e. reduction
  of the coefficients of an integral chain modulo `p`), and
* `gammaLM p X n : C^n(X; ℤ) → C^n(X; ℤ/p)` on cochains,

satisfying the four properties needed downstream:

1. `kappa` is a map of chain complexes (commutes with the differential `d`);
2. `kappa` sends the generator of the `σ`-th summand to the generator of the `σ`-th summand
   (`ιChainComplex`); this pins down `kappa` uniquely as "reduce the coefficients mod `p`";
3. `Γ α (κ y) = α y mod p`, i.e. `Γ` is the transpose of `κ` followed by the reduction of scalars;
4. `Γ` is compatible with the Alexander–Whitney cup product.

Everything is built from the coproduct universal property of the chains
(`SSet.isColimitChainComplexXCofan`): the `ℤ`-module `C_n(X;R)` of a simplicial set is the
coproduct of copies of `R` indexed by the `n`-simplices, so a map out of it is determined by its
values on the generators `ιChainComplex σ`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial

namespace Work.Pi6.K2Z

noncomputable section

variable (p : ℕ) [Fact p.Prime] (X : SSet)

/-- The integral `n`-chains of `X`, as an object of `ModuleCat ℤ`. -/
abbrev chZ (n : ℕ) : ModuleCat ℤ := (X.chainComplex (ModuleCat.of ℤ ℤ)).X n

/-- The `ℤ/p`-chains of `X`, as an object of `ModuleCat (ZMod p)`. -/
abbrev chP (n : ℕ) : ModuleCat (ZMod p) :=
  (X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))).X n

/-! ## The chain-level comparison `kappa` -/

/-- **The `ℤ`-linear reduction map on `n`-chains**, as a morphism of `ModuleCat ℤ`: it is the map
of coproducts which on the `σ`-th summand is the ring homomorphism `ℤ → ℤ/p`
(`LinearMap.toSpanSingleton ℤ _ (generator σ)`), i.e. coefficient reduction modulo `p`. -/
def kappaCat (n : ℕ) : chZ X n ⟶ ModuleCat.of ℤ ↥(chP p X n) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
    (Cofan.mk (ModuleCat.of ℤ ↥(chP p X n))
      (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(chP p X n)
        ((X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1))))

/-- The reduction map on `n`-chains, as a `ℤ`-linear map. -/
def kappa (n : ℕ) : ↥(chZ X n) →ₗ[ℤ] ↥(chP p X n) := (kappaCat p X n).hom

/-- `kappa` sends the generator of the `σ`-th summand to the generator of the `σ`-th summand. -/
lemma kappaCat_gen (n : ℕ) (σ : X _⦋n⦌) :
    (kappaCat p X n).hom ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) =
      (X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1 := by
  have h : X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ kappaCat p X n =
      ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ↥(chP p X n)
        ((X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1)) :=
    Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n) _ σ
  show (ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ kappaCat p X n)) 1 = _
  rw [h, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]

/-- The same statement for the `ℤ`-linear map `kappa`. -/
lemma kappa_gen (n : ℕ) (σ : X _⦋n⦌) :
    kappa p X n ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) =
      (X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1 :=
  kappaCat_gen p X n σ

/-! ## The differential

`ιChainComplex_d` describes the differential on generators in any coefficient category; evaluating
at the generator of `ℤ` (resp. `ℤ/p`) gives the formula used in `kappa_comm`. -/

/-- The differential of the integral chains, evaluated on the generator of a simplex. -/
lemma dZ_genEval (n : ℕ) (σ : X _⦋n + 1⦌) :
    ((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom
        ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) (X.δ i σ)).hom 1) := by
  have h := congrArg (fun (f : ModuleCat.of ℤ ℤ ⟶ chZ X n) => f.hom 1)
      (SSet.ιChainComplex_d X (ModuleCat.of ℤ ℤ) σ)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.comp_apply] at h
  rw [h, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

/-- The differential of the `ℤ/p`-chains, evaluated on the generator of a simplex. -/
lemma dP_genEval (n : ℕ) (σ : X _⦋n + 1⦌) :
    ((X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))).d (n + 1) n).hom
        ((X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1)
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) •
          ((X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) (X.δ i σ)).hom 1) := by
  have h := congrArg (fun (f : ModuleCat.of (ZMod p) (ZMod p) ⟶ chP p X n) => f.hom 1)
      (SSet.ιChainComplex_d X (ModuleCat.of (ZMod p) (ZMod p)) σ)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_smul, LinearMap.comp_apply] at h
  rw [h, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]

/-- **`kappa` is a map of chain complexes**: it commutes with the differentials. -/
lemma kappa_comm (n : ℕ) :
    (X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n ≫ kappaCat p X n =
      kappaCat p X (n + 1) ≫ ModuleCat.ofHom (LinearMap.restrictScalars ℤ
        (((X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))).d (n + 1) n).hom)) := by
  apply SSet.chainComplex_hom_ext (X := X) (R := ModuleCat.of ℤ ℤ)
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply]
  rw [dZ_genEval X n σ, kappaCat_gen p X (n + 1) σ, dP_genEval p X n σ]
  rw [map_sum]
  simp only [map_zsmul, kappaCat_gen p X n]

/-- The elementwise form of `kappa_comm`. -/
lemma kappa_comm_elem (n : ℕ) (y : ↥(chZ X (n + 1))) :
    (kappaCat p X n).hom (((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom y) =
      (((X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))).d (n + 1) n).hom)
        ((kappaCat p X (n + 1)).hom y) := by
  have h := congrArg (fun (f : chZ X (n + 1) ⟶ ModuleCat.of ℤ ↥(chP p X n)) => f.hom y)
    (kappa_comm p X n)
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply] using h

/-! ## The cochain-level comparison `gamma` -/

/-- **The reduction map on `n`-cochains.**  A `ℤ/p`-linear functional on `C_n(X; ℤ/p)` is
determined by its values on the generators; on the `σ`-th summand we put multiplication by the
reduction modulo `p` of the value of `α` on the `σ`-th integral generator. -/
def gammaCat (n : ℕ) (α : Work.Cohomology.Cochain ℤ X n) :
    chP p X n ⟶ ModuleCat.of (ZMod p) (ZMod p) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of (ZMod p) (ZMod p)) n).desc
    (Cofan.mk (ModuleCat.of (ZMod p) (ZMod p))
      (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton (ZMod p) (ZMod p)
        (((Work.Cohomology.genEval ℤ X α σ : ℤ) : ZMod p)))))

/-- The value of `gammaCat n α` on the generator of a simplex. -/
lemma gammaCat_genEval (n : ℕ) (α : Work.Cohomology.Cochain ℤ X n) (σ : X _⦋n⦌) :
    (gammaCat p X n α).hom ((X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1)
      = ((Work.Cohomology.genEval ℤ X α σ : ℤ) : ZMod p) := by
  have h : X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ ≫ gammaCat p X n α =
      ModuleCat.ofHom (LinearMap.toSpanSingleton (ZMod p) (ZMod p)
        (((Work.Cohomology.genEval ℤ X α σ : ℤ) : ZMod p))) :=
    Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of (ZMod p) (ZMod p)) n) _ σ
  show (ModuleCat.Hom.hom (X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ ≫
    gammaCat p X n α)) 1 = _
  rw [h, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]

/-- Additivity of `gammaCat` in the cochain. -/
lemma gammaCat_add (n : ℕ) (α α' : Work.Cohomology.Cochain ℤ X n) :
    gammaCat p X n (α + α') = gammaCat p X n α + gammaCat p X n α' := by
  apply SSet.chainComplex_hom_ext (X := X) (R := ModuleCat.of (ZMod p) (ZMod p))
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, Preadditive.comp_add, ModuleCat.hom_add,
    LinearMap.add_apply]
  rw [gammaCat_genEval p X n (α + α') σ, gammaCat_genEval p X n α σ,
    gammaCat_genEval p X n α' σ]
  simp only [Work.Cohomology.genEval, LinearMap.add_apply, Int.cast_add]

/-- `ℤ`-homogeneity of `gammaCat` in the cochain. -/
lemma gammaCat_smul (n : ℕ) (c : ℤ) (α : Work.Cohomology.Cochain ℤ X n) :
    gammaCat p X n (c • α) = c • gammaCat p X n α := by
  apply SSet.chainComplex_hom_ext (X := X) (R := ModuleCat.of (ZMod p) (ZMod p))
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul, LinearMap.smul_apply]
  rw [gammaCat_genEval p X n (c • α) σ, gammaCat_genEval p X n α σ]
  simp only [Work.Cohomology.genEval, LinearMap.smul_apply, zsmul_eq_mul, Int.cast_mul, Int.cast_id]

/-- **The reduction map on cochains**, a `ℤ`-linear map
`C^n(X; ℤ) → C^n(X; ℤ/p)`. -/
def gammaLM (n : ℕ) :
    Work.Cohomology.Cochain ℤ X n →ₗ[ℤ] Work.Cohomology.Cochain (ZMod p) X n where
  toFun α := (gammaCat p X n α).hom
  map_add' α α' := by
    show (gammaCat p X n (α + α')).hom = (gammaCat p X n α).hom + (gammaCat p X n α').hom
    rw [gammaCat_add p X n α α', ModuleCat.hom_add]
  map_smul' c α := by
    show (gammaCat p X n (c • α)).hom = c • (gammaCat p X n α).hom
    rw [gammaCat_smul p X n c α, ModuleCat.hom_smul]

/-! ## The four required properties -/

/-- Two `ℤ`-linear maps out of the integral chains agreeing on the generators agree. -/
lemma chZ_linExtZ {n : ℕ} {f g : ↥(chZ X n) →ₗ[ℤ] ZMod p}
    (h : ∀ σ : X _⦋n⦌, f ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) =
      g ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) : f = g := by
  have hfg : (ModuleCat.ofHom (R := ℤ) f : chZ X n ⟶ ModuleCat.of ℤ (ZMod p)) =
      ModuleCat.ofHom (R := ℤ) g := by
    apply SSet.chainComplex_hom_ext (X := X) (R := ModuleCat.of ℤ ℤ)
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
    exact h σ
  simpa only [ModuleCat.hom_ofHom] using congrArg ModuleCat.Hom.hom hfg

/-- **`gamma` is the transpose of `kappa` composed with reduction of scalars:**
`Γ α (κ y) = α y mod p`.  The composite `α ↦ (gammaCat n α) ∘ (kappa n)` is exhibited as a
`ℤ`-linear map via `LinearMap.restrictScalars`. -/
lemma gamma_comp_kappa (n : ℕ) (α : Work.Cohomology.Cochain ℤ X n) :
    (LinearMap.restrictScalars ℤ ((gammaCat p X n α).hom)).comp (kappa p X n)
      = (LinearMap.toSpanSingleton ℤ (ZMod p) (1 : ZMod p)).comp α := by
  apply chZ_linExtZ p X
  intro σ
  show (gammaCat p X n α).hom ((kappaCat p X n).hom
      ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))
    = (LinearMap.toSpanSingleton ℤ (ZMod p) (1 : ZMod p))
      (α ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1))
  rw [kappaCat_gen p X n σ]
  rw [gammaCat_genEval p X n α σ]
  simp only [Work.Cohomology.genEval]
  rw [LinearMap.toSpanSingleton_apply, zsmul_eq_mul, mul_one]

/-- **`gamma` is compatible with the Alexander–Whitney cup product.**

Both sides are `ℤ/p`-linear functionals on `C_{n+m}(X; ℤ/p)`, so it suffices to compare their
values on the generator of a simplex; there the cup product is the product of the evaluations on
the front and back faces (`cup_apply`), and `gammaCat_genEval` describes the values of `gammaCat`
so that the statement reduces to `Int.cast_mul`. -/
lemma gamma_cup (n m : ℕ) (α : Work.Cohomology.Cochain ℤ X n)
    (β : Work.Cohomology.Cochain ℤ X m) :
    gammaCat p X (n + m) (Work.Cohomology.cup ℤ X α β) =
      Work.Cohomology.cupHom (ZMod p) X (gammaCat p X n α).hom (gammaCat p X m β).hom := by
  apply SSet.chainComplex_hom_ext (X := X) (R := ModuleCat.of (ZMod p) (ZMod p))
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  show (gammaCat p X (n + m) (Work.Cohomology.cup ℤ X α β)).hom
      ((X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1)
    = Work.Cohomology.genEval (ZMod p) X
      (Work.Cohomology.cup (ZMod p) X (gammaCat p X n α).hom (gammaCat p X m β).hom) σ
  rw [gammaCat_genEval p X (n + m) (Work.Cohomology.cup ℤ X α β) σ]
  rw [Work.Cohomology.cup_apply ℤ X α β σ]
  rw [Work.Cohomology.cup_apply (ZMod p) X (gammaCat p X n α).hom (gammaCat p X m β).hom σ]
  rw [show Work.Cohomology.genEval (ZMod p) X (gammaCat p X n α).hom
        (Work.Cohomology.frontFace X n (n + m) (Nat.le_add_right n m) σ)
      = ((Work.Cohomology.genEval ℤ X α
          (Work.Cohomology.frontFace X n (n + m) (Nat.le_add_right n m) σ) : ℤ) : ZMod p) from
    gammaCat_genEval p X n α _]
  rw [show Work.Cohomology.genEval (ZMod p) X (gammaCat p X m β).hom
        (Work.Cohomology.backFace X n m σ)
      = ((Work.Cohomology.genEval ℤ X β (Work.Cohomology.backFace X n m σ) : ℤ) : ZMod p) from
    gammaCat_genEval p X m β _]
  rw [Int.cast_mul]

/-- **Change of coefficients from `ℤ` to `ℤ/p` for cochains of a simplicial set.** -/
theorem coeffChange (p : ℕ) [Fact p.Prime] (X : SSet) :
    ∃ (Γ : ∀ n : ℕ, Work.Cohomology.Cochain ℤ X n →ₗ[ℤ] Work.Cohomology.Cochain (ZMod p) X n)
      (κ : ∀ n : ℕ, (X.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ]
                     (X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))).X n),
      (∀ (n : ℕ) (y : (X.chainComplex (ModuleCat.of ℤ ℤ)).X (n + 1)),
        κ n (((X.chainComplex (ModuleCat.of ℤ ℤ)).d (n + 1) n).hom y) =
          ((X.chainComplex (ModuleCat.of (ZMod p) (ZMod p))).d (n + 1) n).hom (κ (n + 1) y)) ∧
      (∀ (n : ℕ) (σ : X.obj (Opposite.op (SimplexCategory.mk n))),
        κ n ((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1) =
          (X.ιChainComplex (R := ModuleCat.of (ZMod p) (ZMod p)) σ).hom 1) ∧
      (∀ (n : ℕ) (α : Work.Cohomology.Cochain ℤ X n)
        (y : (X.chainComplex (ModuleCat.of ℤ ℤ)).X n),
        Γ n α (κ n y) = ((α y : ℤ) : ZMod p)) ∧
      (∀ (n m : ℕ) (α : Work.Cohomology.Cochain ℤ X n) (β : Work.Cohomology.Cochain ℤ X m),
        Γ (n + m) (Work.Cohomology.cup ℤ X α β) = Work.Cohomology.cup (ZMod p) X (Γ n α) (Γ m β)) := by
  refine ⟨fun n => gammaLM p X n, fun n => (kappaCat p X n).hom, ?_, ?_, ?_, ?_⟩
  · intro n y
    exact kappa_comm_elem p X n y
  · intro n σ
    exact kappaCat_gen p X n σ
  · intro n α y
    show (LinearMap.restrictScalars ℤ ((gammaCat p X n α).hom)).comp (kappa p X n) y
      = ((α y : ℤ) : ZMod p)
    rw [gamma_comp_kappa p X n α]
    rw [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, zsmul_eq_mul, mul_one]
  · intro n m α β
    show (gammaCat p X (n + m) (Work.Cohomology.cup ℤ X α β)).hom
      = (Work.Cohomology.cupHom (ZMod p) X (gammaCat p X n α).hom (gammaCat p X m β).hom).hom
    rw [gamma_cup p X n m α β]

end

end Work.Pi6.K2Z
