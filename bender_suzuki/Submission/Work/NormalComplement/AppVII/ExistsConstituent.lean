import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.card_extraspecial
import Submission.Work.Hering.AppVII.special_abelian
import Submission.Work.CharPrelim.weightSpace_span_of_primitiveRoot
import Submission.Work.CharPrelim.exists_simple_subrepresentation_nontrivial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.AppVII

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped TensorProduct IsMulCommutative
open Classical

universe u w

/-- **Universe lift.**  A finite-dimensional `k`-representation of `A` (with `k` in universe `0`,
`V` an arbitrary universe `w`) can be re-realised on a type in an arbitrary prescribed universe
`u`, preserving irreducibility, the property that a given subgroup `S ≤ A` is not contained in the
kernel, and the property that a given subgroup `P ≤ A` has no nonzero fixed vector.

The witness is `ULift.{u,0} (Fin (finrank k V) → k)`, transported along the `k`-linear equivalence
`e : V ≃ₗ[k] V'` built from `(Module.finBasis k V).equivFun`, with `ρ' a := e ∘ ρ a ∘ e.symm`. -/
theorem lift_universe {k : Type} [Field k] {A : Type*} [Group A] {V : Type w}
    [AddCommGroup V] [Module k V] [Module.Finite k V]
    (ρ : Representation k A V) (hirr : ρ.IsIrreducible) (S P : Subgroup A)
    (hker : ¬ S ≤ ρ.ker) (hfix : ∀ x : V, (∀ s ∈ P, ρ s x = x) → x = 0) :
    ∃ (V' : Type u) (_ : AddCommGroup V') (_ : Module k V') (_ : Module.Finite k V')
      (ρ' : Representation k A V'),
      ρ'.IsIrreducible ∧ (¬ S ≤ ρ'.ker) ∧
      (∀ x : V', (∀ s ∈ P, ρ' s x = x) → x = 0) := by
  classical
  haveI : Module.Free k V := Module.Free.of_divisionRing k V
  let e : V ≃ₗ[k] ULift.{u, 0} (Fin (Module.finrank k V) → k) :=
    (Module.finBasis k V).equivFun.trans
      (ULift.moduleEquiv (R := k) (M := Fin (Module.finrank k V) → k)).symm
  let ρ' : Representation k A (ULift.{u, 0} (Fin (Module.finrank k V) → k)) :=
    { toFun := fun a => e.toLinearMap.comp ((ρ a).comp e.symm.toLinearMap)
      map_one' := by
        apply LinearMap.ext
        intro x
        simp [LinearEquiv.apply_symm_apply]
      map_mul' := by
        intro a b
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.mul_apply,
          LinearEquiv.symm_apply_apply]
        rw [map_mul, Module.End.mul_apply] }
  have hker_iff : ∀ a : A, ρ' a = 1 ↔ ρ a = 1 := by
    intro a
    constructor
    · intro h
      apply LinearMap.ext
      intro y
      have h2 : ρ' a (e y) = e y := by rw [h]; rfl
      have h3 : ρ' a (e y) = e (ρ a y) := by
        show e (ρ a (e.symm (e y))) = e (ρ a y)
        rw [LinearEquiv.symm_apply_apply]
      rw [h3] at h2
      exact e.injective h2
    · intro h
      apply LinearMap.ext
      intro x
      show e (ρ a (e.symm x)) = x
      have h2 : ρ a (e.symm x) = e.symm x := by rw [h]; rfl
      rw [h2, LinearEquiv.apply_symm_apply]
  have hker' : ¬ S ≤ ρ'.ker := by
    intro h
    apply hker
    intro a ha
    rw [MonoidHom.mem_ker]
    exact (hker_iff a).mp (MonoidHom.mem_ker.mp (h ha))
  have hfix' : ∀ x : ULift.{u, 0} (Fin (Module.finrank k V) → k),
      (∀ s ∈ P, ρ' s x = x) → x = 0 := by
    intro x hx
    have h1 : e.symm x = 0 := by
      apply hfix
      intro s hs
      have h2 : ρ' s x = x := hx s hs
      have h3 : e (ρ s (e.symm x)) = x := h2
      have h4 : e (ρ s (e.symm x)) = e (e.symm x) := by
        rw [LinearEquiv.apply_symm_apply]
        exact h3
      exact e.injective h4
    have h2 : e (e.symm x) = x := LinearEquiv.apply_symm_apply e x
    rw [h1, map_zero] at h2
    exact h2.symm
  have hIso : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map e.toLinearMap, by
        intro a x hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
        refine Submodule.mem_map.mpr ⟨ρ a y, U.apply_mem_toSubmodule a hy, ?_⟩
        show e (ρ a y) = ρ' a (e y)
        simp [ρ', LinearEquiv.symm_apply_apply]⟩
      invFun := fun U => ⟨U.toSubmodule.comap e.toLinearMap, by
        intro a x hx
        have h2 : e (ρ a x) = ρ' a (e x) := by simp [ρ', LinearEquiv.symm_apply_apply]
        show e (ρ a x) ∈ U.toSubmodule
        rw [h2]
        exact U.apply_mem_toSubmodule a hx⟩
      left_inv := fun U => Subrepresentation.ext (by
        show (U.toSubmodule.map e.toLinearMap).comap e.toLinearMap = U.toSubmodule
        rw [Submodule.comap_map_eq, LinearMap.ker_eq_bot.mpr e.injective, sup_bot_eq])
      right_inv := fun U => Subrepresentation.ext (by
        show (U.toSubmodule.comap e.toLinearMap).map e.toLinearMap = U.toSubmodule
        rw [Submodule.map_comap_eq, LinearMap.range_eq_top.mpr e.surjective, top_inf_eq])
      map_rel_iff' := by
        intro U₁ U₂
        constructor
        · intro h x hx
          obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (h (Submodule.mem_map.mpr ⟨x, hx, rfl⟩))
          have hyx' : y = x := e.injective hyx
          rwa [hyx'] at hy
        · intro h
          exact Submodule.map_mono h }
  refine ⟨ULift.{u, 0} (Fin (Module.finrank k V) → k), inferInstance, inferInstance,
    Module.Finite.equiv (ULift.moduleEquiv (R := k) (M := Fin (Module.finrank k V) → k)).symm,
    ρ', ?_, hker', hfix'⟩
  exact hIso.isSimpleOrder_iff.mp hirr

/-- In the setting of `ExtraspecialCase` (`A` acting faithfully and irreducibly on the nontrivial
elementary abelian `r`-group `K`, with `C_K(P) = 1`), there exists an irreducible
`k[A]`-representation (`k = F̄_r`) on which `Z(Q)` acts nontrivially and which has no nonzero
`P`-fixed vector.  (Such a representation is a simple constituent of `k ⊗_{F_r} K`.) -/
theorem ExistsConstituent {A : Type*} [Group A] [Finite A] (Q P : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hcardP : Nat.card ↥P = p) (hpQ : ¬ p ∣ Nat.card ↥Q)
    (hQcard : Nat.card ↥Q = q ^ (2 * m + 1)) (hm : 1 ≤ m)
    (hQext : Work.PGroup.IsExtraspecial q (⊤ : Subgroup ↥Q))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set A) = (Subgroup.center ↥Q).map Q.subtype)
    {K : Type*} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) {r : ℕ} [Fact r.Prime]
    (hKexp : ∀ x : K, x ^ r = 1) (hKcomm : IsMulCommutative K) (hKne : Nontrivial K)
    (hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1)
    (hPfpf : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1) :
    ∃ (V : Type*) (_ : AddCommGroup V) (_ : Module (AlgebraicClosure (ZMod r)) V)
      (_ : Module.Finite (AlgebraicClosure (ZMod r)) V)
      (ρ : Representation (AlgebraicClosure (ZMod r)) A V),
      ρ.IsIrreducible ∧
      (¬ (Subgroup.center ↥Q).map Q.subtype ≤ ρ.ker) ∧
      (∀ v : V, (∀ s ∈ P, ρ s v = v) → v = 0) := by
  classical
  haveI hQnI : Q.Normal := hQn
  haveI : IsMulCommutative K := hKcomm
  letI hQfin : Fintype ↥Q := Fintype.ofFinite _
  letI hPfin : Fintype ↥P := Fintype.ofFinite _
  have hr : r.Prime := Fact.out
  -- ## `K` is a nontrivial elementary abelian `r`-group
  have hrK : r ∣ Nat.card K := by
    obtain ⟨x, hx⟩ := exists_ne (1 : K)
    have h1 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hKexp x)
    have h2 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
    have h3 : orderOf x = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf x) h1 with h | h
      · exact absurd h h2
      · exact h
    rw [← h3]; exact orderOf_dvd_natCard x
  have hrA : ¬ r ∣ Nat.card A :=
    (hr.coprime_iff_not_dvd).mp (hcop.coprime_dvd_left hrK)
  have hrQ : ¬ r ∣ Nat.card ↥Q := by
    have hQA : Nat.card ↥Q ∣ Nat.card A := Subgroup.card_subgroup_dvd_card Q
    exact (hr.coprime_iff_not_dvd).mp ((hcop.coprime_dvd_left hrK).coprime_dvd_right hQA)
  -- ## `K` as an `𝔽_r[A]`-module `M` and the representation `ρ`
  have hr0 : ∀ x : Additive K, r • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hKexp, ofMul_one]
  haveI hmod : Module (ZMod r) (Additive K) := AddCommGroup.zmodModule hr0
  haveI hfin : Module.Finite (ZMod r) (Additive K) := Module.Finite.of_finite
  haveI hnt : Nontrivial (Additive K) := inferInstance
  let g : A → (Additive K →+ Additive K) := fun a =>
    { toFun := fun v => Additive.ofMul (a • (Additive.toMul v))
      map_zero' := by apply Additive.ext; simp
      map_add' := fun u v => by
        apply Additive.ext
        simp [toMul_add, smul_mul', ofMul_mul] }
  let ρ : Representation (ZMod r) A (Additive K) :=
    { toFun := fun a => (g a).toZModLinearMap r
      map_one' := by
        apply LinearMap.ext; intro v; apply Additive.ext; simp [g]
      map_mul' := by
        intro a b
        apply LinearMap.ext; intro v; apply Additive.ext
        simp [g, mul_smul] }
  have hρ : ∀ (a : A) (k : K), ρ a (Additive.ofMul k) = Additive.ofMul (a • k) := fun _ _ => rfl
  -- ## base change to `k = F̄_r`
  let ρ' : Representation (AlgebraicClosure (ZMod r)) A
      (TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K)) :=
    { toFun := fun a => LinearMap.baseChange (AlgebraicClosure (ZMod r)) (ρ a)
      map_one' := by rw [map_one, LinearMap.baseChange_one]
      map_mul' := by intro a b; rw [map_mul, LinearMap.baseChange_mul] }
  haveI : FiniteDimensional (AlgebraicClosure (ZMod r))
      (TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K)) :=
    Module.Finite.base_change (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K)
  -- ## `P` has no nonzero fixed vector in `k ⊗ K`
  have hPfixV : ∀ x : Additive K, (∀ s : ↥P, ρ (s : A) x = x) → x = 0 := by
    intro x hx
    have h1 : ∀ a ∈ P, a • (Additive.toMul x) = Additive.toMul x := by
      intro a ha
      have h2 : ρ a x = x := hx ⟨a, ha⟩
      refine Additive.ofMul.injective ?_
      rw [← hρ a (Additive.toMul x), ← ofMul_toMul x]
      exact h2
    have h3 := hPfpf (Additive.toMul x) h1
    rw [← ofMul_toMul x, h3, ofMul_one]
  have hWfixP : ∀ v : TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K),
      (∀ s : ↥P, ρ' (s : A) v = v) → v = 0 :=
    Work.Hering.AppVII.flat_baseChange_fixedPoints (R := ZMod r)
      (S := AlgebraicClosure (ZMod r)) (V := Additive K) (ι := ↥P)
      (fun s => ρ (s : A)) hPfixV
  -- ## `Z(Q)` is a nontrivial central subgroup of `A`
  have hQcardgt : 1 < Nat.card ↥Q := by
    rw [hQcard]
    exact Nat.one_lt_pow (by omega) hq.one_lt
  haveI hQnt : Nontrivial ↥Q := (Finite.one_lt_card_iff_nontrivial).mp hQcardgt
  haveI hqFact : Fact q.Prime := ⟨hq⟩
  have hQp : IsPGroup q ↥Q := IsPGroup.of_card hQcard
  have hZne0 : Subgroup.center ↥Q ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp (hQp.center_nontrivial)
  have hZne : (Subgroup.center ↥Q).map Q.subtype ≠ ⊥ := by
    intro h
    have hle : Subgroup.center ↥Q ≤ Q.subtype.ker := (Subgroup.map_eq_bot_iff _).mp h
    rw [Subgroup.ker_subtype] at hle
    exact hZne0 (le_bot_iff.mp hle)
  -- `Z(Q)` is central in `A = Q ⋊ P`
  have hZc : (Subgroup.center ↥Q).map Q.subtype ≤ Subgroup.center A := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro a
    have ha : a ∈ Q ⊔ P := by rw [sup_comm, hsup]; trivial
    obtain ⟨qq, hqq, s, hs, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := Q) (t := P)).mp ha
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
    have h1 : qq * Q.subtype z' = Q.subtype z' * qq :=
      congrArg Q.subtype (Subgroup.mem_center_iff.mp hz' (⟨qq, hqq⟩ : ↥Q))
    have hzP : Q.subtype z' ∈ Subgroup.centralizer (P : Set A) := by
      have hmem : Q.subtype z' ∈ Q ⊓ Subgroup.centralizer (P : Set A) := by
        rw [hCQ]; exact Subgroup.mem_map_of_mem _ hz'
      exact hmem.2
    have h2 : s * Q.subtype z' = Q.subtype z' * s :=
      Subgroup.mem_centralizer_iff.mp hzP s hs
    calc qq * s * Q.subtype z' = qq * (s * Q.subtype z') := by rw [mul_assoc]
      _ = qq * (Q.subtype z' * s) := by rw [h2]
      _ = qq * Q.subtype z' * s := by rw [← mul_assoc]
      _ = Q.subtype z' * qq * s := by rw [h1]
      _ = Q.subtype z' * (qq * s) := by rw [mul_assoc]
  letI hZcomm : CommGroup ↥((Subgroup.center ↥Q).map Q.subtype) :=
    { (inferInstance : Group ↥((Subgroup.center ↥Q).map Q.subtype)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZc b.2) a.val) }
  letI hZf : Fintype ↥((Subgroup.center ↥Q).map Q.subtype) := Fintype.ofFinite _
  -- ## `Z(Q)` acts nontrivially on `k ⊗ K` (faithfulness of the `A`-action on `K`)
  have hZker : ¬ (Subgroup.center ↥Q).map Q.subtype ≤ ρ'.ker := by
    intro hker
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZne
    have hzmem : ρ' (z : A) = 1 := MonoidHom.mem_ker.mp (hker z.2)
    have hfix : ∀ k : K, (z : A) • k = k := by
      intro k
      have h1 : ρ' (z : A) ((1 : AlgebraicClosure (ZMod r)) ⊗ₜ[ZMod r] (Additive.ofMul k))
          = (1 : AlgebraicClosure (ZMod r)) ⊗ₜ[ZMod r] (Additive.ofMul k) := by
        rw [hzmem]; rfl
      rw [show ρ' (z : A) = (ρ (z : A)).baseChange (AlgebraicClosure (ZMod r)) from rfl,
        LinearMap.baseChange_tmul] at h1
      have hinj := Module.FaithfullyFlat.tensorProduct_mk_injective (A := ZMod r)
        (B := AlgebraicClosure (ZMod r)) (Additive K)
      have h2 : ρ (z : A) (Additive.ofMul k) = Additive.ofMul k := hinj h1
      have h3 := hρ (z : A) k
      rw [h3] at h2
      exact Additive.ofMul.injective h2
    exact hz1 (Subtype.ext (hfaith (z : A) hfix))
  -- ## weight space decomposition of `k ⊗ K` under `Z(Q)`
  let τ : ↥((Subgroup.center ↥Q).map Q.subtype)
      →* Module.End (AlgebraicClosure (ZMod r))
        (TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K)) :=
    ρ'.comp ((Subgroup.center ↥Q).map Q.subtype).subtype
  have hrZ : ¬ r ∣ Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) :=
    fun h => hrA (Nat.dvd_trans h (Subgroup.card_subgroup_dvd_card _))
  have hcardZ : IsUnit ((Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) : ℕ)
      : AlgebraicClosure (ZMod r)) :=
    isUnit_iff_ne_zero.mpr fun h =>
      hrZ ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod r)) r _).mp h)
  haveI hneZ : NeZero ((Nat.card ↥((Subgroup.center ↥Q).map Q.subtype) : ℕ) : ZMod r) :=
    ⟨fun h => hrZ ((CharP.cast_eq_zero_iff (ZMod r) r _).mp h)⟩
  have hrootZ : ∃ ζ : AlgebraicClosure (ZMod r),
      IsPrimitiveRoot ζ (Nat.card ↥((Subgroup.center ↥Q).map Q.subtype)) :=
    HasEnoughRootsOfUnity.exists_primitiveRoot _ _
  have hspan : (⨆ χ : ↥((Subgroup.center ↥Q).map Q.subtype) →* (AlgebraicClosure (ZMod r))ˣ,
      Work.CharPrelim.weightSpace τ χ) = ⊤ :=
    Work.CharPrelim.weightSpace_span_of_primitiveRoot τ hcardZ hrootZ
  -- some nontrivial character has a nonzero weight space
  have hex : ∃ χ : ↥((Subgroup.center ↥Q).map Q.subtype) →* (AlgebraicClosure (ZMod r))ˣ,
      χ ≠ 1 ∧ Work.CharPrelim.weightSpace τ χ ≠ ⊥ := by
    by_contra hcon
    push_neg at hcon
    have hwt1 : Work.CharPrelim.weightSpace τ
        (1 : ↥((Subgroup.center ↥Q).map Q.subtype) →* (AlgebraicClosure (ZMod r))ˣ) = ⊤ := by
      rw [eq_top_iff, ← hspan]
      refine iSup_le (fun χ => ?_)
      by_cases hχ : χ = 1
      · rw [hχ]
      · rw [hcon χ hχ]; exact bot_le
    apply hZker
    intro z hz
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    have hv : v ∈ Work.CharPrelim.weightSpace τ
        (1 : ↥((Subgroup.center ↥Q).map Q.subtype) →* (AlgebraicClosure (ZMod r))ˣ) := by
      rw [hwt1]; trivial
    have h1 := (Work.CharPrelim.mem_weightSpace τ
      (1 : ↥((Subgroup.center ↥Q).map Q.subtype) →* (AlgebraicClosure (ZMod r))ˣ) v).mp hv
      ⟨z, hz⟩
    change ρ' z v = (↑((1 : ↥((Subgroup.center ↥Q).map Q.subtype)
      →* (AlgebraicClosure (ZMod r))ˣ) ⟨z, hz⟩) : AlgebraicClosure (ZMod r)) • v at h1
    simpa using h1
  obtain ⟨χ, hχne, hWχne⟩ := hex
  -- the weight space of `χ` is `A`-invariant (as `Z(Q)` is central in `A`)
  have hχinv : ∀ a : A, ∀ v ∈ Work.CharPrelim.weightSpace τ χ,
      ρ' a v ∈ Work.CharPrelim.weightSpace τ χ := by
    intro a v hv
    rw [Work.CharPrelim.mem_weightSpace] at hv ⊢
    intro z
    have hvz : ρ' (z : A) v = (χ z : AlgebraicClosure (ZMod r)) • v := hv z
    have hcomm : ρ' a (ρ' (z : A) v) = ρ' (z : A) (ρ' a v) := by
      have h1 : ρ' (z : A) * ρ' a = ρ' a * ρ' (z : A) := by
        rw [← map_mul, ← map_mul, ← Subgroup.mem_center_iff.mp (hZc z.2) a]
      calc ρ' a (ρ' (z : A) v) = (ρ' a * ρ' (z : A)) v := by rw [Module.End.mul_apply]
        _ = (ρ' (z : A) * ρ' a) v := by rw [h1]
        _ = ρ' (z : A) (ρ' a v) := by rw [Module.End.mul_apply]
    show ρ' (z : A) (ρ' a v) = (χ z : AlgebraicClosure (ZMod r)) • (ρ' a v)
    rw [← hcomm, hvz, LinearMap.map_smul]
  -- ## take a minimal nonzero subrepresentation of the `χ`-weight space
  let Wχ : Subrepresentation ρ' :=
    ⟨Work.CharPrelim.weightSpace τ χ, fun a v hv => hχinv a v hv⟩
  have hWχne' : Wχ ≠ ⊥ := by
    intro h
    have h2 : Wχ.toSubmodule = ⊥ := by rw [h]; rfl
    exact hWχne (by simpa only [Wχ] using h2)
  let S : Set ℕ := {n | ∃ V : Subrepresentation ρ', V ≤ Wχ ∧ V ≠ ⊥ ∧
      Module.finrank (AlgebraicClosure (ZMod r)) ↥(V.toSubmodule) = n}
  have hSne : S.Nonempty := ⟨_, Wχ, le_rfl, hWχne', rfl⟩
  obtain ⟨V₀, hV₀le, hV₀ne, hV₀fr⟩ := Nat.find_spec hSne
  have hV₀min : ∀ V : Subrepresentation ρ', V ≤ Wχ → V ≠ ⊥ →
      Module.finrank (AlgebraicClosure (ZMod r)) ↥(V₀.toSubmodule)
        ≤ Module.finrank (AlgebraicClosure (ZMod r)) ↥(V.toSubmodule) := by
    intro V hV hVne
    rw [hV₀fr]
    exact Nat.find_min' hSne ⟨V, hV, hVne, rfl⟩
  have hatom : IsAtom V₀ := by
    refine ⟨hV₀ne, fun b hb => ?_⟩
    by_contra hbne
    have hble : b ≤ Wχ := le_trans hb.le hV₀le
    have h1 := hV₀min b hble hbne
    have hlt : b.toSubmodule < V₀.toSubmodule :=
      lt_of_le_of_ne (fun x hx => hb.le hx) (fun h => hb.ne (Subrepresentation.ext h))
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  -- ## assemble
  have hmain_irr :=
    Work.CharPrelim.isIrreducible_toRepresentation_of_isAtom ρ' V₀ hatom
  have hmain_ker : ¬ (Subgroup.center ↥Q).map Q.subtype ≤ V₀.toRepresentation.ker := by
    intro hker
    obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hχne
    have hzu : χ z ≠ 1 := fun h => hz (by rw [h]; rfl)
    have hzv : (χ z : AlgebraicClosure (ZMod r)) ≠ 1 := fun h => hzu (Units.ext h)
    have hzA : (z : A) ∈ V₀.toRepresentation.ker := hker z.2
    rw [MonoidHom.mem_ker] at hzA
    -- some nonzero vector of `V₀`, regarded in `W = k ⊗ K`
    obtain ⟨y, hy, hy0⟩ : ∃ y ∈ V₀.toSubmodule, y ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hV₀ne
      apply Subrepresentation.ext
      rw [show (⊥ : Subrepresentation ρ').toSubmodule = ⊥ from rfl, Submodule.eq_bot_iff]
      intro u hu
      exact hc u hu
    -- `z` acts on `y` through the scalar `χ z`, but trivially (as `z ∈ ker`)
    have h7 : τ z y = (χ z : AlgebraicClosure (ZMod r)) • y := by
      have h := (Work.CharPrelim.mem_weightSpace τ χ y).mp (hV₀le hy) z
      simpa using h
    have h8 : τ z y = y := by
      have h9 : V₀.toRepresentation (z : A) ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hzA]; rfl
      have h10 := congrArg Subtype.val h9
      have h11 : ρ' (z : A) y = y := by
        simpa [Subrepresentation.toRepresentation] using h10
      simpa [τ, MonoidHom.comp_apply] using h11
    have h10 : (χ z : AlgebraicClosure (ZMod r)) = 1 := by
      refine smul_left_injective (AlgebraicClosure (ZMod r)) hy0 ?_
      show (χ z : AlgebraicClosure (ZMod r)) • y = (1 : AlgebraicClosure (ZMod r)) • y
      rw [← h7, one_smul]
      exact h8
    exact hzv h10
  have hmain_fix : ∀ x : ↥V₀.toSubmodule, (∀ s ∈ P, V₀.toRepresentation s x = x) → x = 0 := by
    intro x hx
    have h1 : (x : TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K)) = 0 :=
      hWfixP (x : TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K))
        (fun s => by
          have h2 := congrArg Subtype.val (hx (s : A) s.2)
          simpa [Subrepresentation.toRepresentation] using h2)
    exact Subtype.ext h1
  obtain ⟨V'', i₁, i₂, i₃, ρ'', hirr'', hker'', hfix''⟩ :=
    lift_universe (k := AlgebraicClosure (ZMod r)) (A := A) (V := ↥V₀.toSubmodule)
      V₀.toRepresentation hmain_irr ((Subgroup.center ↥Q).map Q.subtype) P
      hmain_ker hmain_fix
  exact ⟨V'', i₁, i₂, i₃, ρ'', hirr'', hker'', hfix''⟩

end Work.NormalComplement.AppVII
