import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.CohomologicalShrinking.naturalAlpha.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.naturalAlpha

open scoped TensorProduct
open Work.CohomologicalShrinking.universalCoefficient

/-! ## Elementary lemmas on `𝔽_p`-modules -/

/-- The additive map `v ↦ m ⊗ v`. -/
def psiLin_tmulHom {R : Type*} [CommSemiring R] {M V : Type*} [AddCommMonoid M] [AddCommMonoid V]
    [Module R M] [Module R V] (m : M) : V →+ M ⊗[R] V where
  toFun := fun n => m ⊗ₜ[R] n
  map_zero' := TensorProduct.tmul_zero V m
  map_add' := fun a b => TensorProduct.tmul_add m a b

/-- `psiLin_tmulHom` is additive in `m`. -/
lemma psiLin_tmulHom_add {R : Type*} [CommSemiring R] {M V : Type*} [AddCommMonoid M]
    [AddCommMonoid V] [Module R M] [Module R V] (m m' : M) :
    psiLin_tmulHom (R := R) (V := V) (m + m') =
      psiLin_tmulHom (R := R) (V := V) m + psiLin_tmulHom (R := R) (V := V) m' := by
  ext n; exact TensorProduct.add_tmul m m' n

/-- `(p : ℤ) • v = 0` for a module over `ZMod p`. -/
theorem psiLin_zsmul_prime_eq_zero (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (v : V) : (p : ℤ) • v = 0 := by
  rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul (ZMod p) p v, ZMod.natCast_self, zero_smul]

/-- If `m` is a multiple of `p` then `m ⊗ v = 0` for an `𝔽_p`-module `V`. -/
theorem psiLin_zsmul_prime_tmul_eq_zero (p : ℕ) {M V : Type*} [AddCommGroup M] [AddCommGroup V]
    [Module (ZMod p) V] (m : M) (v : V) : ((p : ℤ) • m) ⊗ₜ[ℤ] v = 0 := by
  rw [TensorProduct.smul_tmul, psiLin_zsmul_prime_eq_zero p, TensorProduct.tmul_zero]

/-- The `ZMod p`-scalar action is the action of the `ℕ`-valued representative. -/
theorem psiLin_zmod_smul_eq_nsmul (p : ℕ) [NeZero p] {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (r : ZMod p) (m : M) : r • m = r.val • m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val r]
  rw [Nat.cast_smul_eq_nsmul]

/-! ## The canonical section `N/N^p[N,N] → A → Nᵃᵇ ⊗_ℤ A` -/

/-- **The canonical section.**  For an `𝔽_p`-module `V` and a group `N` there is an additive
map `S : Additive (N/N^p[N,N]) →+ (V →+ Nᵃᵇ ⊗_ℤ V)` sending the class of `x` to `⟦x⟧ ⊗ -`.
Well defined because `N^p[N,N]` maps into `p · Nᵃᵇ` under abelianization. -/
theorem psiLin_pQuotSection (p : ℕ) [Fact p.Prime] (N : Type) [Group N]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] :
    ∃ S : Additive (Work.Shrinking.pCentralQuotient p N 0) →+ V →+
        Additive (Abelianization N) ⊗[ℤ] V,
      ∀ (x : ↥(Work.Shrinking.pCentralSeries p N 0)) (a : V),
        S (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N 0)) x)) a
          = Additive.ofMul (Abelianization.of (x : N)) ⊗ₜ[ℤ] a := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- an element of `N^p[N,N]` has `p`-divisible abelianization class
  have key : ∀ (k : N), k ∈ Work.Shrinking.pCentralSeries p N 1 → ∀ a : V,
      Additive.ofMul (Abelianization.of k) ⊗ₜ[ℤ] a = 0 := by
    intro k hk a
    have h1 : pQuotMap p N k = 1 := by
      set x : ↥(Work.Shrinking.pCentralSeries p N 0) :=
        ⟨k, by rw [Work.Shrinking.pCentralSeries_zero]; exact Subgroup.mem_top k⟩ with hx
      have hxk : (x : N) = k := rfl
      have h2 : pQuotMap p N k = QuotientGroup.mk' ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
          (Work.Shrinking.pCentralSeries p N 0)) x := rfl
      rw [h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hxk]
      exact hk
    have hzero : pQuotAddHom p N (Additive.ofMul (Abelianization.of k)) = 0 := by
      have h3 : abToPQuot p N (Abelianization.of k) = 1 := by rw [abToPQuot_of, h1]
      show Additive.ofMul (abToPQuot p N
        (Additive.toMul (Additive.ofMul (Abelianization.of k)))) = 0
      rw [show Additive.toMul (Additive.ofMul (Abelianization.of k)) = Abelianization.of k
        from rfl, h3]
      rfl
    obtain ⟨z, hz⟩ := pQuotAddHom_ker p N _ hzero
    rw [hz]
    exact psiLin_zsmul_prime_tmul_eq_zero p z a
  -- the monoid hom `N → Multiplicative (V →+ Nᵃᵇ ⊗ V)` given by `x ↦ (a ↦ ⟦x⟧ ⊗ a)`
  let φ : ↥(Work.Shrinking.pCentralSeries p N 0) →*
      Multiplicative (V →+ Additive (Abelianization N) ⊗[ℤ] V) :=
  { toFun := fun x => Multiplicative.ofAdd (psiLin_tmulHom (Additive.ofMul (Abelianization.of (x : N))))
    map_one' := by
      apply Multiplicative.ext
      ext a
      simp [psiLin_tmulHom]
    map_mul' := by
      intro x y
      apply Multiplicative.ext
      show psiLin_tmulHom (Additive.ofMul (Abelianization.of
            ((x * y : ↥(Work.Shrinking.pCentralSeries p N 0)) : N)))
          = psiLin_tmulHom (Additive.ofMul (Abelianization.of (x : N)))
            + psiLin_tmulHom (Additive.ofMul (Abelianization.of (y : N)))
      have hxy : Additive.ofMul (Abelianization.of
            ((x * y : ↥(Work.Shrinking.pCentralSeries p N 0)) : N))
          = Additive.ofMul (Abelianization.of (x : N))
            + Additive.ofMul (Abelianization.of (y : N)) := by
        rw [show ((x * y : ↥(Work.Shrinking.pCentralSeries p N 0)) : N) = (x : N) * (y : N)
          from rfl]
        rw [map_mul]
        rfl
      rw [hxy, psiLin_tmulHom_add] }
  have hφker : ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
      (Work.Shrinking.pCentralSeries p N 0)) ≤ φ.ker := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [MonoidHom.mem_ker]
    apply Multiplicative.ext
    ext a
    show psiLin_tmulHom (Additive.ofMul (Abelianization.of (k : N))) a = 0
    exact key (k : N) hk a
  refine ⟨{ toFun := fun u => Multiplicative.toAdd (QuotientGroup.lift _ φ hφker (Additive.toMul u))
            map_zero' := by
              rw [show Additive.toMul (0 : Additive (Work.Shrinking.pCentralQuotient p N 0)) = 1
                from rfl]
              rw [map_one]
              rfl
            map_add' := by
              intro u v
              rw [show Additive.toMul (u + v) = Additive.toMul u * Additive.toMul v from rfl]
              rw [map_mul]
              rfl }, ?_⟩
  intro x a
  show Multiplicative.toAdd (QuotientGroup.lift _ φ hφker
      (Additive.toMul (Additive.ofMul (QuotientGroup.mk' _ x)))) a = _
  rw [show Additive.toMul (Additive.ofMul (QuotientGroup.mk' _ x)) = QuotientGroup.mk' _ x
    from rfl]
  rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
  rfl

/-! ## The main statement -/

theorem exists_psiLin (p : ℕ) [Fact p.Prime] (N : Type) [Group N]
    (A : Rep (ZMod p) N) [A.IsTrivial] :
    ∃ ψ : TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p N 0)) A.V →+ groupHomology.H1 A,
      Function.Surjective ψ ∧
      ∀ (x : ↥(Work.Shrinking.pCentralSeries p N 0)) (a : A.V),
        ψ (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
              ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
                (Work.Shrinking.pCentralSeries p N 0)) x) :
            Additive (Work.Shrinking.pCentralQuotient p N 0)) a)
          = groupHomology.H1π A ⟨Finsupp.single (x : N) a,
              (groupHomology.single_mem_cycles₁_iff (x : N) a).2
                (Representation.isTrivial_apply A.ρ (x : N) a)⟩ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨S, hS⟩ := psiLin_pQuotSection p N A.V
  -- `S` is balanced for the `𝔽_p`-tensor product
  have hbal : ∀ (r : ZMod p) (u : Additive (Work.Shrinking.pCentralQuotient p N 0)) (a : A.V),
      S (r • u) a = S u (r • a) := by
    intro r u a
    rw [psiLin_zmod_smul_eq_nsmul p r u, psiLin_zmod_smul_eq_nsmul p r a,
      map_nsmul, map_nsmul]
    rfl
  let L : TensorProduct (ZMod p) (Additive (Work.Shrinking.pCentralQuotient p N 0)) A.V →+
      Additive (Abelianization N) ⊗[ℤ] A.V := TensorProduct.liftAddHom S hbal
  have hL : Function.Surjective L := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero L⟩
    | tmul m a =>
        obtain ⟨n, hn⟩ := QuotientGroup.mk'_surjective (commutator N) (Additive.toMul m)
        have hm : Additive.ofMul (Abelianization.of n) = m := hn
        refine ⟨Additive.ofMul (QuotientGroup.mk' _
            (⟨n, by rw [Work.Shrinking.pCentralSeries_zero]; exact Subgroup.mem_top n⟩ :
              ↥(Work.Shrinking.pCentralSeries p N 0))) ⊗ₜ[ZMod p] a, ?_⟩
        rw [show L (Additive.ofMul (QuotientGroup.mk' _
              (⟨n, _⟩ : ↥(Work.Shrinking.pCentralSeries p N 0))) ⊗ₜ[ZMod p] a)
              = S (Additive.ofMul (QuotientGroup.mk' _
              (⟨n, _⟩ : ↥(Work.Shrinking.pCentralSeries p N 0)))) a
            from TensorProduct.liftAddHom_tmul S hbal _ a]
        rw [hS ⟨n, _⟩ a]
        rw [show Additive.ofMul (Abelianization.of
              ((⟨n, _⟩ : ↥(Work.Shrinking.pCentralSeries p N 0)) : N))
              = Additive.ofMul (Abelianization.of n) from rfl, hm]
    | add x y hx hy =>
        obtain ⟨x', hx'⟩ := hx
        obtain ⟨y', hy'⟩ := hy
        exact ⟨x' + y', by rw [map_add, hx', hy']⟩
  refine ⟨(groupHomology.H1AddEquivOfIsTrivial A).symm.toAddMonoidHom.comp L, ?_, ?_⟩
  · intro y
    obtain ⟨w, hw⟩ := hL (groupHomology.H1AddEquivOfIsTrivial A y)
    refine ⟨w, ?_⟩
    show (groupHomology.H1AddEquivOfIsTrivial A).symm (L w) = y
    rw [hw]
    exact AddEquiv.apply_symm_apply _ _
  · intro x a
    show (groupHomology.H1AddEquivOfIsTrivial A).symm
      (L (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
        ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
          (Work.Shrinking.pCentralSeries p N 0)) x)) a)) = _
    rw [show L (TensorProduct.tmul (ZMod p) (Additive.ofMul (QuotientGroup.mk'
        ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
          (Work.Shrinking.pCentralSeries p N 0)) x)) a)
        = S (Additive.ofMul (QuotientGroup.mk'
        ((Work.Shrinking.pCentralSeries p N 1).subgroupOf
          (Work.Shrinking.pCentralSeries p N 0)) x)) a
        from TensorProduct.liftAddHom_tmul S hbal _ a]
    rw [hS x a]
    rw [groupHomology.H1AddEquivOfIsTrivial_symm_tmul]
    congr 1

end Work.CohomologicalShrinking.naturalAlpha
