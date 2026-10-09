import Mathlib
import Submission.Work.SSGRoute.CycLevel.rat_pow_eq_nat_pow
import Submission.Work.SSGRoute.CycLevel.not_pow_of_mem_adjoin_primitiveRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace Work.SSGRoute.CycLevel

open Polynomial IntermediateField
open scoped Classical

noncomputable section

theorem kummerCyc_data (q e m : ℕ) (hq : q.Prime) (hq2 : 2 < q) (he : 0 < e)
    (hm : 0 < m) (hmq : ¬ ∃ m' : ℕ, 0 < m' ∧ m = m' ^ q) :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : Algebra ℚ N)
      (_ : FiniteDimensional ℚ N) (_ : IsGalois ℚ N) (ζ α : N) (σ : N ≃ₐ[ℚ] N),
      IsPrimitiveRoot ζ (q ^ e) ∧ α ^ q = algebraMap ℚ N (m : ℚ) ∧ σ ζ = ζ ∧
        σ α = ζ ^ (q ^ (e - 1)) * α := by
  classical
  have hqpos : 0 < q := hq.pos
  have hqne : q ≠ 0 := hq.ne_zero
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hqe_ne : q ^ e ≠ 0 := (pow_pos hqpos e).ne'
  haveI hneq : NeZero q := ⟨hqne⟩
  haveI hneqe : NeZero (q ^ e) := ⟨hqe_ne⟩
  -- `m` is not a `q`-th power in `ℚ`
  have hmQ : ∀ y : ℚ, y ^ q ≠ (m : ℚ) := fun y hy => by
    obtain ⟨m', hm', hmq'⟩ := rat_pow_eq_nat_pow hm hy
    exact hmq ⟨m', hm', hmq'⟩
  -- the ambient field and a primitive root of unity
  haveI hAlgΩ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI hintΩ : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.isIntegral
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (q ^ e) := by
    haveI : NeZero ((q ^ e : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hqe_ne⟩
    haveI hcc : IsCyclotomicExtension {q ^ e} ℚ (CyclotomicField (q ^ e) ℚ) :=
      CyclotomicField.isCyclotomicExtension (q ^ e) ℚ
    refine ⟨IsAlgClosed.lift (R := ℚ) (S := CyclotomicField (q ^ e) ℚ)
      (M := AlgebraicClosure ℚ)
      (IsCyclotomicExtension.zeta (q ^ e) ℚ (CyclotomicField (q ^ e) ℚ)), ?_⟩
    exact (IsCyclotomicExtension.zeta_spec (q ^ e) ℚ (CyclotomicField (q ^ e) ℚ)).map_of_injective
      (RingHom.injective _)
  -- the cyclotomic base field `K = ℚ⟮ζ⟯`
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))
  have hζKmem : ζ ∈ K := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)
  let ζK : ↥K := ⟨ζ, hζKmem⟩
  have hζK : IsPrimitiveRoot ζK (q ^ e) :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp (by simpa [ζK] using hζ)
  haveI hcycK : IsCyclotomicExtension {q ^ e} ℚ ↥K :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI hfdK : FiniteDimensional ℚ ↥K := IsCyclotomicExtension.finiteDimensional {q ^ e} ℚ ↥K
  haveI hgalK : IsGalois ℚ ↥K := IsCyclotomicExtension.isGalois {q ^ e} ℚ ↥K
  haveI hnfK : NumberField ↥K := NumberField.of_module_finite ℚ ↥K
  -- a primitive `q`-th root of unity in `K`
  have hζq : IsPrimitiveRoot (ζK ^ q ^ (e - 1)) q := by
    have h2 : q ^ e = q ^ (e - 1) * q := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ e from he)]
      rw [pow_succ]
    have hdiv : q ^ e / q ^ (e - 1) = q := by
      rw [h2, Nat.mul_div_cancel_left q (pow_pos hqpos (e - 1))]
    have h := hζK.pow_of_dvd (pow_ne_zero (e - 1) hqne) (Nat.pow_dvd_pow q (Nat.sub_le e 1))
    simpa only [hdiv] using h
  -- the Kummer polynomial over `K`
  have hirr : Irreducible (X ^ q - C (algebraMap ℚ ↥K (m : ℚ))) := by
    refine X_pow_sub_C_irreducible_of_odd hqodd ?_
    intro p hp hpq b hb
    have hpeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp hpq
    rw [hpeq] at hb
    have h : (b : AlgebraicClosure ℚ) ^ q = algebraMap ℚ (AlgebraicClosure ℚ) (m : ℚ) := by
      have h1 : ((b ^ q : ↥K) : AlgebraicClosure ℚ) =
          algebraMap ℚ (AlgebraicClosure ℚ) (m : ℚ) := by
        rw [hb, IsScalarTower.algebraMap_apply ℚ ↥K (AlgebraicClosure ℚ) (m : ℚ)]
        simp
      rwa [SubmonoidClass.coe_pow] at h1
    exact not_pow_of_mem_adjoin_primitiveRoot q e m hq hq2 he hm hmQ ζ hζ
      (b : AlgebraicClosure ℚ) b.2 h
  -- the Kummer field `L = K[q√m]`
  let a : ↥K := algebraMap ℚ ↥K (m : ℚ)
  haveI hfact : Fact (Irreducible (X ^ q - C a)) := ⟨hirr⟩
  let L := AdjoinRoot (X ^ q - C a)
  have hf_ne : (X ^ q - C a : (↥K)[X]) ≠ 0 := X_pow_sub_C_ne_zero hqpos a
  have hroot : (AdjoinRoot.root (X ^ q - C a)) ^ q = algebraMap ↥K L a := by
    have h := AdjoinRoot.eval₂_root (f := (X ^ q - C a : (↥K)[X]))
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
    rwa [AdjoinRoot.algebraMap_eq]
  -- the automorphism over `K` sending `α` to `ζ_q α`
  let η : rootsOfUnity q ↥K := ⟨(hζq.isUnit hqne).unit, by
    rw [mem_rootsOfUnity', IsUnit.unit_spec]
    exact hζq.pow_eq_one⟩
  have hηcoe : (((η : rootsOfUnity q ↥K) : Units ↥K) : ↥K) = ζK ^ q ^ (e - 1) :=
    (hζq.isUnit hqne).unit_spec
  let αL : L := AdjoinRoot.root (X ^ q - C a)
  let ζL : L := algebraMap ↥K L ζK
  have hζL : IsPrimitiveRoot ζL (q ^ e) := hζK.map_of_injective (algebraMap ↥K L).injective
  have hζL_pow : ζL ^ (q ^ e) = 1 := hζL.pow_eq_one
  have hζqL : IsPrimitiveRoot (algebraMap ↥K L (ζK ^ q ^ (e - 1))) q :=
    hζq.map_of_injective (algebraMap ↥K L).injective
  have hαL : αL ^ q = algebraMap ℚ L (m : ℚ) := by
    rw [hroot, AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq' (S := ℚ), RingHom.comp_apply]
  let σK : L ≃ₐ[↥K] L := autAdjoinRootXPowSubC q a η
  have hσKroot : σK αL = (algebraMap ↥K L (ζK ^ q ^ (e - 1))) * αL := by
    have h := autAdjoinRootXPowSubC_root (n := q) a η
    rw [Algebra.smul_def] at h
    simpa only [σK, αL, hηcoe] using h
  have hcomm : ∀ r : ℚ, σK (algebraMap ℚ L r) = algebraMap ℚ L r := fun r => by
    rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply]
    exact σK.commutes (algebraMap ℚ ↥K r)
  let σ : L ≃ₐ[ℚ] L :=
    { toFun := σK
      invFun := σK.symm
      left_inv := fun x => σK.left_inv x
      right_inv := fun x => σK.right_inv x
      map_mul' := fun x y => map_mul σK x y
      map_add' := fun x y => map_add σK x y
      commutes' := hcomm }
  have hσζ : σ ζL = ζL := by
    show σK ζL = ζL
    exact σK.commutes ζK
  have hσα : σ αL = ζL ^ (q ^ (e - 1)) * αL := by
    show σK αL = ζL ^ (q ^ (e - 1)) * αL
    rw [hσKroot,
      show (algebraMap ↥K L (ζK ^ q ^ (e - 1))) = ζL ^ (q ^ (e - 1)) from by
        rw [← map_pow]]
  -- `L` is Galois over `ℚ`
  set p : ℚ[X] := (X ^ q - C (m : ℚ)) * (X ^ (q ^ e) - C 1) with hpdef
  have hp_ne : p ≠ 0 := by
    rw [hpdef]
    exact mul_ne_zero (X_pow_sub_C_ne_zero hqpos (m : ℚ))
      (X_pow_sub_C_ne_zero (pow_pos hqpos e) (1 : ℚ))
  have hp_map_ne : p.map (algebraMap ℚ L) ≠ 0 := by
    intro h0
    refine hp_ne ?_
    have h1 : p.map (algebraMap ℚ L) = (0 : ℚ[X]).map (algebraMap ℚ L) := by
      rw [Polynomial.map_zero]; exact h0
    exact Polynomial.map_injective (algebraMap ℚ L) (algebraMap ℚ L).injective h1
  have hsplit : (p.map (algebraMap ℚ L)).Splits := by
    rw [hpdef, Polynomial.map_mul]
    refine Splits.mul ?_ ?_
    · have h := X_pow_sub_C_splits_of_isPrimitiveRoot hζqL hαL
      simpa using h
    · have h := X_pow_sub_C_splits_of_isPrimitiveRoot (α := ζL) hζL hζL_pow
      simpa using h
  have hgen : Algebra.adjoin ℚ (p.rootSet L) = ⊤ := by
    let A : Subalgebra ℚ L := Algebra.adjoin ℚ (p.rootSet L)
    show A = ⊤
    have hζL_root : ζL ∈ p.rootSet L := by
      rw [mem_rootSet']
      refine ⟨hp_map_ne, ?_⟩
      rw [hpdef]
      simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C, map_one]
      rw [hζL_pow, sub_self, mul_zero]
    have hαL_root : αL ∈ p.rootSet L := by
      rw [mem_rootSet']
      refine ⟨hp_map_ne, ?_⟩
      rw [hpdef]
      simp only [map_mul, map_sub, map_pow, aeval_X, aeval_C, map_one]
      rw [hαL, sub_self, zero_mul]
    have hζL_mem : ζL ∈ A := Algebra.subset_adjoin hζL_root
    have hαL_mem : αL ∈ A := Algebra.subset_adjoin hαL_root
    -- `ℚ⟮ζK⟯` is the `ℚ`-subalgebra generated by `ζK`
    have htopK : Algebra.adjoin ℚ ({ζK} : Set ↥K) = ⊤ := by
      haveI hspfK : IsSplittingField ℚ ↥K ((X : ℚ[X]) ^ (q ^ e) - 1) :=
        IsCyclotomicExtension.isSplittingField_X_pow_sub_one (q ^ e) ℚ ↥K
      refine top_le_iff.mp ?_
      rw [← IsSplittingField.adjoin_rootSet ↥K ((X : ℚ[X]) ^ (q ^ e) - 1)]
      refine Algebra.adjoin_le_iff.mpr ?_
      intro y hy
      obtain ⟨-, hyae⟩ := (mem_rootSet').mp hy
      have hy1 : y ^ (q ^ e) = 1 := by
        have h2 : y ^ (q ^ e) - 1 = 0 := by simpa using hyae
        exact sub_eq_zero.mp h2
      obtain ⟨i, -, hi⟩ := hζK.eq_pow_of_pow_eq_one hy1
      rw [← hi]
      exact pow_mem (Algebra.subset_adjoin (Set.mem_singleton ζK)) i
    -- the image of `↥K` lies in `A`
    have hrange : ∀ c : ↥K, algebraMap ↥K L c ∈ A := by
      intro c
      have hc : c ∈ Algebra.adjoin ℚ ({ζK} : Set ↥K) := by rw [htopK]; trivial
      refine Algebra.adjoin_induction (p := fun x _ => algebraMap ↥K L x ∈ A) ?_ ?_ ?_ ?_ hc
      · intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simpa only [ζL] using hζL_mem
      · intro r
        rw [show algebraMap ↥K L (algebraMap ℚ ↥K r) = algebraMap ℚ L r from by
          rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq' (S := ℚ), RingHom.comp_apply]]
        exact A.algebraMap_mem r
      · intro x y hx hy ihx ihy
        rw [map_add]; exact A.add_mem ihx ihy
      · intro x y hx hy ihx ihy
        rw [map_mul]; exact A.mul_mem ihx ihy
    -- every element of `L` is a `K`-polynomial in `αL`
    refine le_antisymm le_top ?_
    intro x _
    have hx : x ∈ Algebra.adjoin ↥K ({AdjoinRoot.root (X ^ q - C a)} : Set L) := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    refine Algebra.adjoin_induction (p := fun y _ => y ∈ A) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      simpa only [αL] using hαL_mem
    · intro r; exact hrange r
    · intro y z hy hz ihy ihz; exact A.add_mem ihy ihz
    · intro y z hy hz ihy ihz; exact A.mul_mem ihy ihz
  have hspfL : IsSplittingField ℚ L p := IsSplittingField.mk hsplit hgen
  haveI hfinKL : Module.Finite ↥K L :=
    Polynomial.Monic.finite_adjoinRoot (monic_X_pow_sub_C a hqne)
  haveI hnfL : NumberField L := NumberField.of_module_finite ↥K L
  haveI hfdL : FiniteDimensional ℚ L := inferInstance
  haveI hintL : Algebra.IsIntegral ℚ L := Algebra.IsIntegral.of_finite ℚ L
  haveI hgalL : IsGalois ℚ L :=
    { to_isSeparable := Algebra.IsSeparable.of_integral ℚ L
      to_normal := @Normal.of_isSplittingField ℚ _ L _ _ p hspfL }
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ζL, αL, σ, hζL, hαL, hσζ, hσα⟩


end

end Work.SSGRoute.CycLevel
