import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.BocksteinDefs
import Submission.Work.CFT.ClassFormation.Schur.finite_HnZ
import Submission.Work.CFT.ClassFormation.Schur.module_finite_groupHomology
import Submission.Work.Tower.Shafarevich.CFT.BocksteinChain
import Submission.Work.Tower.Shafarevich.CFT.HnZp_equiv_HnHomFp
import Submission.Work.Tower.Shafarevich.CFT.HnZ_finite
import Submission.Work.Tower.Shafarevich.CFT.HnZ_natCard_smul_eq_zero
import Submission.Work.Tower.Shafarevich.CFT.HnHomFp_finite

open scoped TensorProduct Pointwise
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.CFT.ClassFormation.Schur

open Work.Tower.Shafarevich.CFT

noncomputable section

/-! ## The `p`-cokernel and `p`-torsion of an abelian group -/

/-- Multiplication by `p` on `A`, as the `ℤ`-linear map `a ↦ p • a`. -/
abbrev mulByP (p : ℕ) (A : Type*) [AddCommGroup A] : A →ₗ[ℤ] A :=
  (p : ℤ) • (LinearMap.id : A →ₗ[ℤ] A)

/-- The pointwise value of a scalar multiple of the identity `ℤ`-linear map. -/
lemma smul_id_apply {M : Type*} [AddCommGroup M] (c : ℤ) (x : M) :
    (c • (LinearMap.id : M →ₗ[ℤ] M)) x = c • x := by
  rw [LinearMap.smul_apply, LinearMap.id_apply]

/-- `∃ y, f y = x` is membership in the range of `f`. -/
lemma exists_eq_iff_mem_range {A M : Type*} [AddCommGroup A] [AddCommGroup M]
    (f : A →ₗ[ℤ] M) (x : M) : (∃ y, f y = x) ↔ x ∈ LinearMap.range f :=
  LinearMap.mem_range.symm

/-- `f x = 0` is membership in the kernel of `f`. -/
lemma eq_zero_iff_mem_ker {A M : Type*} [AddCommGroup A] [AddCommGroup M]
    (f : A →ₗ[ℤ] M) (x : A) : f x = 0 ↔ x ∈ LinearMap.ker f :=
  LinearMap.mem_ker.symm

/-- Transport of finite generation along an equality of module structures. -/
lemma Module.Finite.of_module_eq {R M : Type*} [Semiring R] [AddCommGroup M]
    {m₁ m₂ : Module R M} (h : m₁ = m₂) (hm : @Module.Finite R M _ _ m₁) :
    @Module.Finite R M _ _ m₂ := h ▸ hm

/-- **Cokernel of multiplication by `p`.**  For an abelian group `A`, the quotient `A ⧸ pA` is
additively equivalent to the tensor product `𝔽_p ⊗_ℤ A`: both are the universal quotient of `A`
killed by `p`. -/
theorem coker_mulByP_equiv_tensor (p : ℕ) (A : Type) [AddCommGroup A] :
    Nonempty ((A ⧸ LinearMap.range (mulByP p A)) ≃+ (TensorProduct ℤ (ZMod p) A)) := by
  have hsub : LinearMap.range (mulByP p A) = (p : ℤ) • (⊤ : Submodule ℤ A) := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  rw [hsub]
  have e1 : (A ⧸ (p : ℤ) • (⊤ : Submodule ℤ A)) ≃+ ((ℤ ⧸ Ideal.span {(p : ℤ)}) ⊗[ℤ] A) :=
    (QuotSMulTop.equivQuotTensor (p : ℤ) A).toAddEquiv
  have h := (Int.quotientSpanEquivZMod (p : ℤ)).toAddEquiv
  rw [Int.natAbs_natCast] at h
  have e2 : ((ℤ ⧸ Ideal.span {(p : ℤ)}) ⊗[ℤ] A) ≃+ (TensorProduct ℤ (ZMod p) A) :=
    (TensorProduct.congr h.toIntLinearEquiv (LinearEquiv.refl ℤ A)).toAddEquiv
  exact ⟨e1.trans e2⟩

/-- **Cardinality of `𝔽_p ⊗ A`.**  For a finitely generated abelian group `A`, the `𝔽_p`-vector
space `𝔽_p ⊗_ℤ A` is finite of cardinality `p ^ rankP p A`. -/
theorem natCard_tensor_eq_pow_rankP (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A]
    [Module.Finite ℤ A] :
    Nat.card (TensorProduct ℤ (ZMod p) A) = p ^ rankP p A := by
  haveI : Module.Finite (ZMod p) (TensorProduct ℤ (ZMod p) A) := Module.Finite.base_change ℤ (ZMod p) A
  haveI : Finite (TensorProduct ℤ (ZMod p) A) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (TensorProduct ℤ (ZMod p) A) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod p) (V := TensorProduct ℤ (ZMod p) A), ZMod.card p]
  rfl

/-- **The `p`-cokernel as a power of `p`.**  For a finitely generated abelian group `A`,
`|A ⧸ pA| = p ^ rankP p A`. -/
theorem natCard_coker_eq_pow_rankP (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A]
    [Module.Finite ℤ A] :
    Nat.card (A ⧸ LinearMap.range (mulByP p A)) = p ^ rankP p A := by
  rw [Nat.card_congr (coker_mulByP_equiv_tensor p A).some.toEquiv]
  exact natCard_tensor_eq_pow_rankP p A

/-- **The `p`-torsion as a power of `p`.**  For a finite abelian group `A`, the `p`-torsion
subgroup `A[p]` has the same cardinality as the `p`-cokernel `A ⧸ pA`, namely `p ^ rankP p A`. -/
theorem natCard_ker_eq_pow_rankP (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A] [Finite A]
    [Module.Finite ℤ A] :
    Nat.card ↥(LinearMap.ker (mulByP p A)) = p ^ rankP p A := by
  have hker : Nat.card A = Nat.card (A ⧸ LinearMap.ker (mulByP p A)) *
      Nat.card ↥(LinearMap.ker (mulByP p A)) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker (mulByP p A)).toAddSubgroup
  have hrange : Nat.card A = Nat.card (A ⧸ LinearMap.range (mulByP p A)) *
      Nat.card ↥(LinearMap.range (mulByP p A)) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range (mulByP p A)).toAddSubgroup
  have hqr : Nat.card (A ⧸ LinearMap.ker (mulByP p A)) =
      Nat.card ↥(LinearMap.range (mulByP p A)) :=
    Nat.card_congr (LinearMap.quotKerEquivRange (mulByP p A)).toEquiv
  rw [hqr] at hker
  haveI : Nonempty ↥(LinearMap.range (mulByP p A)) := ⟨⟨0, (LinearMap.range (mulByP p A)).zero_mem⟩⟩
  haveI : Finite ↥(LinearMap.range (mulByP p A)) := inferInstance
  have hpos : 0 < Nat.card ↥(LinearMap.range (mulByP p A)) := Nat.card_pos
  have hthis : Nat.card ↥(LinearMap.range (mulByP p A)) * Nat.card ↥(LinearMap.ker (mulByP p A)) =
      Nat.card ↥(LinearMap.range (mulByP p A)) *
        Nat.card (A ⧸ LinearMap.range (mulByP p A)) := by
    rw [hker.symm, hrange]
    exact mul_comm _ _
  have hcancel : Nat.card ↥(LinearMap.ker (mulByP p A)) =
      Nat.card (A ⧸ LinearMap.range (mulByP p A)) :=
    Nat.eq_of_mul_eq_mul_left hpos hthis
  rw [hcancel, natCard_coker_eq_pow_rankP p A]

/-- **Cardinality of the middle term of a short exact sequence.**  If
`A --f--> A --g--> M --δ--> C --h--> C` is exact at the three middle spots, then the
cardinality of `M` is the product of the cardinalities of `A ⧸ range f` and `ker h`. -/
theorem natCard_eq_mul_of_exact {A M C : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup C]
    (f : A →ₗ[ℤ] A) (g : A →ₗ[ℤ] M) (δ : M →ₗ[ℤ] C) (h : C →ₗ[ℤ] C)
    (e1 : ∀ x, (∃ y, f y = x) ↔ g x = 0)
    (e2 : ∀ x, (∃ y, g y = x) ↔ δ x = 0)
    (e3 : ∀ x, (∃ y, δ y = x) ↔ h x = 0) :
    Nat.card M = Nat.card (A ⧸ LinearMap.range f) * Nat.card ↥(LinearMap.ker h) := by
  have e1' : LinearMap.range f = LinearMap.ker g := by
    ext x; rw [LinearMap.mem_range, LinearMap.mem_ker]; exact e1 x
  have e2' : LinearMap.range g = LinearMap.ker δ := by
    ext x; rw [LinearMap.mem_range, LinearMap.mem_ker]; exact e2 x
  have e3' : LinearMap.range δ = LinearMap.ker h := by
    ext x; rw [LinearMap.mem_range, LinearMap.mem_ker]; exact e3 x
  have h1 : Nat.card M = Nat.card (M ⧸ LinearMap.ker δ) * Nat.card ↥(LinearMap.ker δ) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.ker δ).toAddSubgroup
  rw [Nat.card_congr (LinearMap.quotKerEquivRange δ).toEquiv, e3'] at h1
  have h2 : Nat.card ↥(LinearMap.ker δ) = Nat.card (A ⧸ LinearMap.range f) := by
    rw [← e2', ← Nat.card_congr (LinearMap.quotKerEquivRange g).toEquiv, ← e1']
  have hcomm : Nat.card ↥(LinearMap.ker h) * Nat.card (A ⧸ LinearMap.range f) =
      Nat.card (A ⧸ LinearMap.range f) * Nat.card ↥(LinearMap.ker h) := mul_comm _ _
  rw [h2, hcomm] at h1
  exact h1

/-- **The Bockstein cardinality computation.**  If
`A --f--> A --g--> M --δ--> C --h--> C` is exact at the three middle spots with `f` and `h`
multiplication by `p`, and `A`, `M`, `C` are finitely generated (with `C` finite), then
`|M| = p ^ rankP p A * p ^ rankP p C`. -/
theorem natCard_bockstein (p : ℕ) [Fact p.Prime] {A M C : Type} [AddCommGroup A]
    [AddCommGroup M] [AddCommGroup C] [Module.Finite ℤ A] [Module.Finite ℤ M] [Finite C]
    [Module.Finite ℤ C]
    (f : A →ₗ[ℤ] A) (g : A →ₗ[ℤ] M) (δ : M →ₗ[ℤ] C) (h : C →ₗ[ℤ] C)
    (hf : ∀ x, f x = (p : ℤ) • x) (hh : ∀ x, h x = (p : ℤ) • x)
    (e1 : ∀ x, (∃ y, f y = x) ↔ g x = 0)
    (e2 : ∀ x, (∃ y, g y = x) ↔ δ x = 0)
    (e3 : ∀ x, (∃ y, δ y = x) ↔ h x = 0) :
    Nat.card M = p ^ rankP p A * p ^ rankP p C := by
  have hfm : f = mulByP p A := LinearMap.ext fun x => by rw [hf]; simp [mulByP]
  have hhm : h = mulByP p C := LinearMap.ext fun x => by rw [hh]; simp [mulByP]
  rw [natCard_eq_mul_of_exact f g δ h e1 e2 e3, hfm, hhm, natCard_coker_eq_pow_rankP p A,
    natCard_ker_eq_pow_rankP p C]

/-- **Homology Bockstein sequence.**  For a finite group `G`, a prime `p`, and `n ≥ 2`, the
long exact homology sequence of the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` of trivial
`G`-modules gives
`dim_𝔽_p H_n(G, 𝔽_p) = dim_𝔽_p (H_n(G, ℤ) ⊗ 𝔽_p) + dim_𝔽_p (H_{n-1}(G, ℤ) ⊗ 𝔽_p)`.
The connecting map exhibits `H_n(G,𝔽_p)` as an extension of the `p`-torsion subgroup
`H_{n-1}(G,ℤ)[p]` by `H_n(G,ℤ)/p`; for `n ≥ 2` both `H_n(G,ℤ)` and `H_{n-1}(G,ℤ)` are finite
abelian groups, so `dim_𝔽_p (H_k(G,ℤ)[p]) = dim_𝔽_p (H_k(G,ℤ) ⊗ 𝔽_p)`.  `rankP p A` is
`dim_𝔽_p (𝔽_p ⊗_ℤ A)`. -/
theorem finrank_homology_fp_eq
    (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (n : ℕ) (hn : 2 ≤ n) :
    Module.finrank (ZMod p) (Work.CFT.ClassFormation.HnHomFp p G n) =
      Work.CFT.ClassFormation.rankP p (Work.CFT.ClassFormation.HnZ G n : Type)
        + Work.CFT.ClassFormation.rankP p (Work.CFT.ClassFormation.HnZ G (n - 1) : Type) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- the two `ℤ`-module structures on the underlying abelian group agree
  have hmi : (HnZ G n).isModule = AddCommGroup.toIntModule ↥(HnZ G n) := Subsingleton.elim _ _
  have hmi' : (HnZ G (n - 1)).isModule = AddCommGroup.toIntModule ↥(HnZ G (n - 1)) :=
    Subsingleton.elim _ _
  -- work with the canonical `ℤ`-module structure (the one used by `rankP`)
  letI : Module ℤ ↥(HnZ G n) := AddCommGroup.toIntModule ↥(HnZ G n)
  letI : Module ℤ ↥(HnZ G (n - 1)) := AddCommGroup.toIntModule ↥(HnZ G (n - 1))
  letI : Module ℤ ↥(HnZp p G n) := AddCommGroup.toIntModule ↥(HnZp p G n)
  -- finiteness
  haveI hfinA : @Module.Finite ℤ ↥((chainCz G).homology n) _ _
      (AddCommGroup.toIntModule ↥((chainCz G).homology n)) :=
    Module.Finite.of_module_eq hmi (finite_HnZ' G n)
  haveI hfinC' : @Module.Finite ℤ ↥((chainCz G).homology (n - 1)) _ _
      (AddCommGroup.toIntModule ↥((chainCz G).homology (n - 1))) :=
    Module.Finite.of_module_eq hmi' (finite_HnZ' G (n - 1))
  haveI hfinM : @Module.Finite ℤ ↥((chainCF p G).homology n) _ _
      (AddCommGroup.toIntModule ↥((chainCF p G).homology n)) :=
    Module.Finite.of_module_eq (Subsingleton.elim _ _)
      (module_finite_groupHomology ℤ G (V := ZMod p) n)
  haveI hfinC : Finite ↥(HnZ G (n - 1)) :=
    HnZ_finite G (n - 1) (by omega) (fun y => HnZ_natCard_smul_eq_zero G (n - 1) (by omega) y)
  -- the connecting degree of the chain-level Bockstein short exact sequence
  have hij : (ComplexShape.down ℕ).Rel n (n - 1) := by
    show (n - 1) + 1 = n
    omega
  have hS : (bockChainSES p G).ShortExact := bockChainSES_shortExact p G
  -- the long exact sequence, in degrees `n` and `n - 1`
  have e1 : LinearMap.range (HomologicalComplex.homologyMap (mulChain p G) n).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (redChain p G) n).hom :=
    (hS.homology_exact₂ n).moduleCat_range_eq_ker
  have e2 : LinearMap.range (HomologicalComplex.homologyMap (redChain p G) n).hom =
      LinearMap.ker (hS.δ n (n - 1) hij).hom :=
    (hS.homology_exact₃ n (n - 1) hij).moduleCat_range_eq_ker
  have e3 : LinearMap.range (hS.δ n (n - 1) hij).hom =
      LinearMap.ker (HomologicalComplex.homologyMap (mulChain p G) (n - 1)).hom :=
    (hS.homology_exact₁ n (n - 1) hij).moduleCat_range_eq_ker
  -- the four maps, transported to the canonical structure of the underlying abelian groups
  let fz := AddMonoidHom.toIntLinearMap
    ((HomologicalComplex.homologyMap (mulChain p G) n).hom.toAddMonoidHom :
      ↥(HnZ G n) →+ ↥(HnZ G n))
  let gz := AddMonoidHom.toIntLinearMap
    ((HomologicalComplex.homologyMap (redChain p G) n).hom.toAddMonoidHom :
      ↥(HnZ G n) →+ ↥(HnZp p G n))
  let δz := AddMonoidHom.toIntLinearMap
    ((hS.δ n (n - 1) hij).hom.toAddMonoidHom : ↥(HnZp p G n) →+ ↥(HnZ G (n - 1)))
  let hz := AddMonoidHom.toIntLinearMap
    ((HomologicalComplex.homologyMap (mulChain p G) (n - 1)).hom.toAddMonoidHom :
      ↥(HnZ G (n - 1)) →+ ↥(HnZ G (n - 1)))
  have hfzfun : ⇑fz = ⇑(HomologicalComplex.homologyMap (mulChain p G) n).hom := rfl
  have hgzfun : ⇑gz = ⇑(HomologicalComplex.homologyMap (redChain p G) n).hom := rfl
  have hδzfun : ⇑δz = ⇑(hS.δ n (n - 1) hij).hom := rfl
  have hhzfun : ⇑hz = ⇑(HomologicalComplex.homologyMap (mulChain p G) (n - 1)).hom := rfl
  have hfzp : ∀ x, fz x = (p : ℤ) • x := by
    intro x
    rw [hfzfun]
    refine (congrArg (fun (f : (chainCz G).homology n ⟶ (chainCz G).homology n) =>
      (ModuleCat.Hom.hom f) x) (homologyMap_mulChain p G n)).trans ?_
    have h1 : ((p : ℤ) • (𝟙 ((chainCz G).homology n) :
        (chainCz G).homology n ⟶ (chainCz G).homology n)).hom
        = (p : ℤ) • (𝟙 ((chainCz G).homology n) :
          (chainCz G).homology n ⟶ (chainCz G).homology n).hom := rfl
    rw [h1, ModuleCat.hom_id]
    exact smul_id_apply (p : ℤ) x
  have hhzp : ∀ x, hz x = (p : ℤ) • x := by
    intro x
    rw [hhzfun]
    refine (congrArg (fun (f : (chainCz G).homology (n - 1) ⟶ (chainCz G).homology (n - 1)) =>
      (ModuleCat.Hom.hom f) x) (homologyMap_mulChain p G (n - 1))).trans ?_
    have h1 : ((p : ℤ) • (𝟙 ((chainCz G).homology (n - 1)) :
        (chainCz G).homology (n - 1) ⟶ (chainCz G).homology (n - 1))).hom
        = (p : ℤ) • (𝟙 ((chainCz G).homology (n - 1)) :
          (chainCz G).homology (n - 1) ⟶ (chainCz G).homology (n - 1)).hom := rfl
    rw [h1, ModuleCat.hom_id]
    exact smul_id_apply (p : ℤ) x
  have e1z : ∀ x, (∃ y, fz y = x) ↔ gz x = 0 := fun x =>
    (show (∃ y, fz y = x) ↔ (∃ y, (HomologicalComplex.homologyMap (mulChain p G) n).hom y = x) from
      exists_congr (fun y => by rw [hfzfun])).trans
      (((SetLike.ext_iff.mp e1) x).trans
        (LinearMap.mem_ker (f := (HomologicalComplex.homologyMap (redChain p G) n).hom) (y := x)))
  have e2z : ∀ x, (∃ y, gz y = x) ↔ δz x = 0 := fun x =>
    (show (∃ y, gz y = x) ↔ (∃ y, (HomologicalComplex.homologyMap (redChain p G) n).hom y = x) from
      exists_congr (fun y => by rw [hgzfun])).trans
      ((LinearMap.mem_range (f := (HomologicalComplex.homologyMap (redChain p G) n).hom) (x := x)).symm.trans
        (((SetLike.ext_iff.mp e2) x).trans
          ((LinearMap.mem_ker (f := (hS.δ n (n - 1) hij).hom) (y := x)).trans Iff.rfl)))
  have e3z : ∀ x, (∃ y, δz y = x) ↔ hz x = 0 := fun x =>
    (show (∃ y, δz y = x) ↔ (∃ y, (hS.δ n (n - 1) hij).hom y = x) from
      exists_congr (fun y => by rw [hδzfun])).trans
      ((LinearMap.mem_range (f := (hS.δ n (n - 1) hij).hom) (x := x)).symm.trans
        (((SetLike.ext_iff.mp e3) x).trans
          ((LinearMap.mem_ker (f := (HomologicalComplex.homologyMap (mulChain p G) (n - 1)).hom)
            (y := x)).trans Iff.rfl)))
  -- finiteness instances, stated in the exact forms the transported maps demand
  haveI hFinA2 : Module.Finite ℤ (HnZ G n : Type) := hfinA
  haveI hFinM2 : Module.Finite ℤ (HnZp p G n : Type) := hfinM
  haveI hFinC2 : Module.Finite ℤ (HnZ G (n - 1) : Type) := hfinC'
  haveI hFinCfin : Finite (HnZ G (n - 1) : Type) := hfinC
  haveI hfinX1 : @Module.Finite ℤ ↥((bockChainSES p G).X₁.homology n) _ _
      (AddCommGroup.toIntModule ↥((bockChainSES p G).X₁.homology n)) := hfinA
  haveI hfinX3 : @Module.Finite ℤ ↥((bockChainSES p G).X₃.homology n) _ _
      (AddCommGroup.toIntModule ↥((bockChainSES p G).X₃.homology n)) := hfinM
  haveI hFinX1 : Finite ↥((bockChainSES p G).X₁.homology (n - 1)) := hfinC
  haveI hfinX1' : @Module.Finite ℤ ↥((bockChainSES p G).X₁.homology (n - 1)) _ _
      (AddCommGroup.toIntModule ↥((bockChainSES p G).X₁.homology (n - 1))) := hfinC'
  -- the Bockstein cardinality computation
  have key : Nat.card ↥(HnZp p G n) =
      p ^ (rankP p (HnZ G n : Type) + rankP p (HnZ G (n - 1) : Type)) := by
    rw [pow_add]
    exact natCard_bockstein p fz gz δz hz hfzp hhzp e1z e2z e3z
  -- cardinality of `H_n(G, 𝔽_p)` as a power of `p`
  have hcardM : Nat.card ↥(HnZp p G n) = Nat.card ↥(HnHomFp p G n) := by
    obtain ⟨e⟩ := HnZp_equiv_HnHomFp p G n
    exact (Nat.card_congr e.toEquiv).symm
  have hpowM : p ^ Module.finrank (ZMod p) (HnHomFp p G n) = Nat.card ↥(HnHomFp p G n) := by
    haveI : Finite ↥(HnHomFp p G n) := HnHomFp_finite p G n
    haveI : Fintype ↥(HnHomFp p G n) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := ↥(HnHomFp p G n))
    rw [ZMod.card p, ← Nat.card_eq_fintype_card] at h
    exact h.symm
  have h1 : p ^ Module.finrank (ZMod p) (HnHomFp p G n)
      = p ^ (rankP p (HnZ G n : Type) + rankP p (HnZ G (n - 1) : Type)) := by
    rw [hpowM, ← hcardM]
    exact key
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h1

end

end Work.CFT.ClassFormation.Schur
