import Mathlib
import Submission.Work.Coprime.All
import Submission.Work.Hering.AppVII.Setup
import Submission.Work.Hering.AppVII.orbit_sum

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The abelian case of Peterfalvi's Appendix VII (`Work.Hering.AppVII.special_abelian`)

We prove the following contradiction.  Let `A = Q ⋊ P` with `Q` normal abelian, `|P| = p` prime,
`p ∤ |Q|`, `P ⊓ Q = ⊥`, `P ⊔ Q = ⊤`, `⁅P,Q⁆ = Q` and `C_Q(P) = 1`.  Let `K` be a nontrivial
elementary abelian `r`-group on which `A` acts faithfully and irreducibly, with `(|K|,|A|) = 1`,
and suppose `P` and `Q` act *fixed-point-freely* on `K` (`hPfpf`, `hQfix`).  Then we reach a
contradiction.

The argument is the orbit-sum argument of `Work.Hering.AppVII.orbit_sum` over a splitting field.
Extend scalars from `𝔽_r` to the algebraic closure `k = F̄_r`: the `k`-module `k ⊗ K` still has no
nonzero `P`- or `Q`-fixed vector (`flat_baseChange_fixedPoints`, using that `P`, `Q` are finite and
`k` is flat over `𝔽_r`).  Since `r ∤ |Q|`, `k` contains a primitive `|Q|`-th root of unity, so
`orbit_sum` applies and produces a nonzero `P`-fixed vector in `k ⊗ K`, i.e. in the base change of
`K^P`.  Descending along the same lemma contradicts `hPfpf`.

The only non-group-theoretic input (`flat_baseChange_fixedPoints`) is proved below: over a flat
algebra `S` of `R`, forming `S ⊗[R] ·` preserves the intersection of the fixed-point spaces of a
finite family of `R`-linear endomorphisms.
-/

set_option linter.style.haveILetI false

open scoped TensorProduct

namespace Work.Hering.AppVII

/-- **Flat base change commutes with simultaneous fixed points.**

Let `f : ι → V →ₗ[R] V` be a finite family of `R`-linear endomorphisms of `V` whose common
fixed-point space is trivial.  Then the base change to a flat `R`-algebra `S` has trivial common
fixed-point space.

The proof writes `Ψ v = fun i => f i v - v`, an injective `R`-linear map `V → (ι → V)`; base
changing along the flat `S` keeps it injective, and `S ⊗ (ι → V) ≃ (ι → S ⊗ V)` identifies the
components of the base-changed map with `(f i).baseChange S - 1`. -/
theorem flat_baseChange_fixedPoints {R S V ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]
    (f : ι → V →ₗ[R] V) (h : ∀ v : V, (∀ i, f i v = v) → v = 0) :
    ∀ w : TensorProduct R S V, (∀ i, (f i).baseChange S w = w) → w = 0 := by
  set Ψ : V →ₗ[R] (ι → V) := LinearMap.pi (fun i => f i - 1) with hΨdef
  have hΨ_apply : ∀ (v : V) (i : ι), Ψ v i = f i v - v := by
    intro v i; simp [hΨdef]
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    have hz : Ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hfix : ∀ i, f i (a - b) = (a - b) := by
      intro i
      have h2 := congrFun hz i
      rw [hΨ_apply] at h2
      exact sub_eq_zero.mp h2
    have h3 := h (a - b) hfix
    exact sub_eq_zero.mp h3
  have hbcinj : Function.Injective (LinearMap.baseChange S Ψ) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap Ψ hΨinj
  have hmap : ∀ w : TensorProduct R S V,
      TensorProduct.piRightHom R S S (fun _ : ι => V) (LinearMap.baseChange S Ψ w)
        = fun i => (f i).baseChange S w - w := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul s v =>
      ext i
      simp only [LinearMap.baseChange_tmul, TensorProduct.piRightHom_tmul, hΨ_apply,
        TensorProduct.tmul_sub]
    | add x y hx hy =>
      ext i
      simp only [map_add, Pi.add_apply, hx, hy]
      abel
  have hinj : Function.Injective (TensorProduct.piRightHom R S S (fun _ : ι => V)) :=
    (TensorProduct.piRight R S S (fun _ : ι => V)).injective
  intro w hw
  have hzero : LinearMap.baseChange S Ψ w = 0 := by
    apply hinj
    rw [map_zero, hmap w]
    ext i
    simp [hw]
  exact hbcinj (by rw [hzero, map_zero])

open Additive
open scoped Pointwise IsMulCommutative

theorem special_abelian {A : Type*} [Group A] [Finite A] (P Q : Subgroup A) (hQn : Q.Normal)
    (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) {p : ℕ} (hp : p.Prime) (hcardP : Nat.card ↥P = p)
    (hpQ : ¬ p ∣ Nat.card ↥Q) (hcomm : ⁅P, Q⁆ = Q) (hQab : IsMulCommutative ↥Q)
    (hCQ1 : Q ⊓ Subgroup.centralizer (P : Set A) = ⊥)
    {K : Type*} [Group K] [Finite K] [MulDistribMulAction A K]
    (hcop : Nat.Coprime (Nat.card K) (Nat.card A)) {r : ℕ} (hr : r.Prime)
    (hKexp : ∀ x : K, x ^ r = 1) (hKcomm : IsMulCommutative K) (hKne : Nontrivial K)
    (hirr : ∀ M : Subgroup K, (∀ a : A, ∀ x ∈ M, a • x ∈ M) → M ≠ ⊥ → M = ⊤)
    (hfaith : ∀ a : A, (∀ x : K, a • x = x) → a = 1)
    (hPfpf : ∀ k : K, (∀ a ∈ P, a • k = k) → k = 1)
    (hQfix : ∀ k : K, (∀ a ∈ Q, a • k = k) → k = 1) : False := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsMulCommutative K := hKcomm
  haveI hQf : Fintype ↥Q := Fintype.ofFinite _
  haveI hPf : Fintype ↥P := Fintype.ofFinite _
  -- `r` divides `|K|`, hence is coprime to `|A|` and to `|Q|`
  have hrK : r ∣ Nat.card K := by
    obtain ⟨x, hx⟩ := exists_ne (1 : K)
    have h1 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hKexp x)
    have h2 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
    have h3 : orderOf x = r := by
      rcases hr.eq_one_or_self_of_dvd (orderOf x) h1 with h | h
      · exact absurd h h2
      · exact h
    rw [← h3]; exact orderOf_dvd_natCard x
  have hrQ : ¬ r ∣ Nat.card ↥Q := by
    have hQA : Nat.card ↥Q ∣ Nat.card A := Subgroup.card_subgroup_dvd_card Q
    have hcopA : Nat.Coprime r (Nat.card A) := hcop.coprime_dvd_left hrK
    exact (hr.coprime_iff_not_dvd).mp (hcopA.coprime_dvd_right hQA)
  -- `K` is an `𝔽_r`-vector space (an elementary abelian `r`-group)
  have hr0 : ∀ x : Additive K, r • x = 0 := fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hKexp, ofMul_one]
  haveI hmod : Module (ZMod r) (Additive K) := AddCommGroup.zmodModule hr0
  haveI hfin : Module.Finite (ZMod r) (Additive K) := Module.Finite.of_finite
  haveI hnt : Nontrivial (Additive K) := inferInstance
  -- the representation of `A` on `Additive K`
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
  -- the splitting field `k = F̄_r` and a primitive `|Q|`-th root of unity in it
  haveI hne0 : NeZero ((Nat.card ↥Q : ℕ) : ZMod r) :=
    ⟨fun h => hrQ ((CharP.cast_eq_zero_iff (ZMod r) r _).mp h)⟩
  have hroot : ∃ ζ : AlgebraicClosure (ZMod r), IsPrimitiveRoot ζ (Nat.card ↥Q) :=
    HasEnoughRootsOfUnity.exists_primitiveRoot _ _
  have hcharQ : IsUnit ((Nat.card ↥Q : ℕ) : AlgebraicClosure (ZMod r)) :=
    isUnit_iff_ne_zero.mpr (fun h => hrQ ((CharP.cast_eq_zero_iff _ r _).mp h))
  -- the base-changed representation on `k ⊗ K`
  let ρ' : Representation (AlgebraicClosure (ZMod r)) A
      (TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K)) :=
    { toFun := fun a => LinearMap.baseChange (AlgebraicClosure (ZMod r)) (ρ a)
      map_one' := by rw [map_one, LinearMap.baseChange_one]
      map_mul' := by intro a b; rw [map_mul, LinearMap.baseChange_mul] }
  -- `Q` still has no nonzero fixed vector after base change
  have hQfixV : ∀ x : Additive K, (∀ q : ↥Q, ρ (q : A) x = x) → x = 0 := by
    intro x hx
    have h1 : ∀ a ∈ Q, a • (Additive.toMul x) = Additive.toMul x := by
      intro a ha
      have h2 : ρ a x = x := hx ⟨a, ha⟩
      refine Additive.ofMul.injective ?_
      rw [← hρ a (Additive.toMul x), ← ofMul_toMul x]
      exact h2
    have h3 := hQfix (Additive.toMul x) h1
    rw [← ofMul_toMul x, h3, ofMul_one]
  have hfixQ : ∀ v : TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K),
      (∀ q ∈ Q, ρ' q v = v) → v = 0 := by
    intro v hv
    refine flat_baseChange_fixedPoints (R := ZMod r) (S := AlgebraicClosure (ZMod r))
      (V := Additive K) (ι := ↥Q) (fun q => ρ (q : A)) hQfixV v ?_
    intro q
    show (ρ' (q : A)) v = v
    exact hv (q : A) q.2
  -- orbit sum: a nonzero `P`-fixed vector in `k ⊗ K`
  obtain ⟨v, hvne, hvp⟩ := orbit_sum (F := AlgebraicClosure (ZMod r))
    (M := TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K))
    ρ' Q P hQn hinf hsup hQab (by rw [hcardP]; exact hp) hcomm hroot hcharQ hfixQ inferInstance
  -- `P` still has no nonzero fixed vector after base change: contradiction
  have hPfixV : ∀ x : Additive K, (∀ q : ↥P, ρ (q : A) x = x) → x = 0 := by
    intro x hx
    have h1 : ∀ a ∈ P, a • (Additive.toMul x) = Additive.toMul x := by
      intro a ha
      have h2 : ρ a x = x := hx ⟨a, ha⟩
      refine Additive.ofMul.injective ?_
      rw [← hρ a (Additive.toMul x), ← ofMul_toMul x]
      exact h2
    have h3 := hPfpf (Additive.toMul x) h1
    rw [← ofMul_toMul x, h3, ofMul_one]
  have hMfix : ∀ w : TensorProduct (ZMod r) (AlgebraicClosure (ZMod r)) (Additive K),
      (∀ q : ↥P, (ρ (q : A)).baseChange (AlgebraicClosure (ZMod r)) w = w) → w = 0 :=
    flat_baseChange_fixedPoints (R := ZMod r) (S := AlgebraicClosure (ZMod r))
      (V := Additive K) (ι := ↥P) (fun q => ρ (q : A)) hPfixV
  refine hvne (hMfix v (fun q => ?_))
  show (ρ' (q : A)) v = v
  exact hvp (q : A) q.2

end Work.Hering.AppVII
