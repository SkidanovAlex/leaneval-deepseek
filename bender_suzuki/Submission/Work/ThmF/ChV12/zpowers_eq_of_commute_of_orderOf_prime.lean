import Mathlib
import Submission.Work.ThmF.ChV12.irreducible_of_orderOf_prime
import Submission.Work.ThmF.ChV12.mulAut_mul_comm_of_commute_of_irreducible
import Submission.Work.ThmF.ChV12.cyclic_of_abelian_faithful_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.zpowers_eq_of_commute_of_orderOf_prime`

Let `A` be a finite elementary abelian `2`-group (`x * x = 1` for all `x`, hence abelian),
`|A| = 2 ^ k`, `p` a prime with `orderOf (2 : ZMod p) = k` (i.e. `p` is a primitive prime
divisor of `2 ^ k - 1`), and `σ, τ : MulAut A` two commuting automorphisms of order `p`.
Then `σ` and `τ` generate the same cyclic subgroup: `⟨σ⟩ = ⟨τ⟩`.

## Proof

`irreducible_of_orderOf_prime` shows that `σ` acts *irreducibly* on `A` (the only
`σ`-invariant subgroups are `⊥` and `⊤`).  Consequently the centralizer
`C = C_{MulAut A}(σ)` acts faithfully and irreducibly on the `𝔽₂`-vector space `Additive A`,
and `mulAut_mul_comm_of_commute_of_irreducible` shows `C` is abelian.  Schur's lemma over the
finite field `𝔽₂[σ]` then makes `C` cyclic (`centralizer_isCyclic_of_irreducible_aux`, through
`cyclic_of_abelian_faithful_irreducible`).

Both `σ` (trivially) and `τ` (by hypothesis, since `σ τ = τ σ`) lie in this cyclic centralizer
`C`, and `orderOf σ = orderOf τ = p`.  In a cyclic group two elements of the same order generate
the same subgroup (`IsCyclic.subgroup_eq_iff_card_eq`), which we transport back through the
subtype `↥C → MulAut A` to conclude `⟨σ⟩ = ⟨τ⟩`.
-/

set_option linter.style.haveILetI false

namespace Work.ThmF.ChV12

/-- The centralizer of an automorphism of a finite elementary abelian `2`-group is cyclic,
provided the automorphism acts irreducibly (its only invariant subgroups are `⊥` and `⊤`). -/
theorem centralizer_isCyclic_of_irreducible_aux {A : Type} [Group A] [Finite A] [Nontrivial A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (σ : MulAut A)
    (hirr : ∀ W : Subgroup A, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤) :
    IsCyclic ↥(Subgroup.centralizer ({σ} : Set (MulAut A))) := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  letI : CommGroup A := { (inferInstance : Group A) with mul_comm := hAc }
  -- `Additive A` is an `𝔽₂`-vector space because `A` has exponent `2`
  haveI hmod : Module (ZMod 2) (Additive A) :=
    AddCommGroup.zmodModule (fun x => by
      obtain ⟨a, rfl⟩ := Additive.ofMul.surjective x
      rw [two_nsmul, ← ofMul_mul, hA2 a]; rfl)
  let C : Subgroup (MulAut A) := Subgroup.centralizer ({σ} : Set (MulAut A))
  -- the centralizer is abelian
  have hCcomm : ∀ a b : ↥C, a * b = b * a := by
    intro a b
    have ha : ∀ x : A, (a : MulAut A) (σ x) = σ ((a : MulAut A) x) := by
      intro x
      have h := (Subgroup.mem_centralizer_iff.mp a.2) σ (by simp)
      have h' := congrFun (congrArg DFunLike.coe h) x
      simpa using h'.symm
    have hb : ∀ x : A, (b : MulAut A) (σ x) = σ ((b : MulAut A) x) := by
      intro x
      have h := (Subgroup.mem_centralizer_iff.mp b.2) σ (by simp)
      have h' := congrFun (congrArg DFunLike.coe h) x
      simpa using h'.symm
    exact Subtype.ext (mulAut_mul_comm_of_commute_of_irreducible σ hirr a b ha hb)
  -- the faithful action of `C` on the `𝔽₂`-space `Additive A`
  let ρ : ↥C →* (Additive A ≃ₗ[ZMod 2] Additive A) :=
    { toFun := fun u => ((u : MulAut A).toAdditive).toLinearEquiv (fun c x => ZMod.map_smul _ c x)
      map_one' := by ext x; rfl
      map_mul' := by intro u v; ext x; rfl }
  have hfaith : Function.Injective ρ := by
    intro u v huv
    have h2 : (u : MulAut A).toAdditive = (v : MulAut A).toAdditive := by
      apply AddEquiv.ext
      intro x
      have h3 := congrFun (congrArg
        (fun e : Additive A ≃ₗ[ZMod 2] Additive A => (e : Additive A → Additive A)) huv) x
      simpa [ρ] using h3
    exact Subtype.ext (MulEquiv.toAdditive.injective h2)
  -- the action of `C` on `Additive A` is irreducible, since it extends that of `σ`
  have hhirr : ∀ W : Submodule (ZMod 2) (Additive A), W ≠ ⊥ →
      (∀ t : ↥C, ∀ x ∈ W, ρ t x ∈ W) → W = ⊤ := by
    intro W hWne hWinv
    have hW'mem : ∀ a : A, a ∈ AddSubgroup.toSubgroup' W.toAddSubgroup ↔
        Additive.ofMul a ∈ W := fun a => Iff.rfl
    have hW'ne : AddSubgroup.toSubgroup' W.toAddSubgroup ≠ ⊥ := by
      intro h
      apply hWne
      have h2 : W.toAddSubgroup = ⊥ := by
        have h3 := congrArg (OrderIso.symm AddSubgroup.toSubgroup') h
        rw [OrderIso.symm_apply_apply] at h3
        simpa using h3
      rw [← Submodule.toAddSubgroup_toZModSubmodule (n := 2) W, h2, OrderIso.map_bot]
    have hW'inv : ∀ x ∈ AddSubgroup.toSubgroup' W.toAddSubgroup,
        σ x ∈ AddSubgroup.toSubgroup' W.toAddSubgroup := by
      intro x hx
      rw [hW'mem] at hx ⊢
      have hσC : σ ∈ C := by
        change σ ∈ Subgroup.centralizer ({σ} : Set (MulAut A))
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
      have hh := hWinv ⟨σ, hσC⟩ (Additive.ofMul x) hx
      rwa [show ρ ⟨σ, hσC⟩ (Additive.ofMul x) = Additive.ofMul (σ x) from rfl] at hh
    have htop := hirr _ hW'ne hW'inv
    have h2 : W.toAddSubgroup = ⊤ := by
      have h3 := congrArg (OrderIso.symm AddSubgroup.toSubgroup') htop
      rw [OrderIso.symm_apply_apply] at h3
      simpa using h3
    rw [← Submodule.toAddSubgroup_toZModSubmodule (n := 2) W, h2]
    exact OrderIso.map_top _
  exact (cyclic_of_abelian_faithful_irreducible hCcomm ρ hfaith hhirr).1

theorem zpowers_eq_of_commute_of_orderOf_prime {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k p : ℕ}
    (hk : Nat.card A = 2 ^ k) (hp : Nat.Prime p) (hord : orderOf (2 : ZMod p) = k)
    (σ τ : MulAut A) (hσ : orderOf σ = p) (hτ : orderOf τ = p) (hcomm : σ * τ = τ * σ) :
    Subgroup.zpowers σ = Subgroup.zpowers τ := by
  have hirr : ∀ W : Subgroup A, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤ :=
    irreducible_of_orderOf_prime hA2 hAc hk hp hord σ hσ
  -- `A` is nontrivial: otherwise `MulAut A` is trivial and `orderOf σ = 1 ≠ p`
  haveI : Nontrivial A := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    haveI : Subsingleton A := h
    have hσ1 : σ = 1 := MulEquiv.ext (fun x => Subsingleton.elim _ _)
    rw [hσ1, orderOf_one] at hσ
    exact hp.ne_one hσ.symm
  let C : Subgroup (MulAut A) := Subgroup.centralizer ({σ} : Set (MulAut A))
  have hCcyc : IsCyclic ↥C := centralizer_isCyclic_of_irreducible_aux hA2 hAc σ hirr
  haveI : IsCyclic ↥C := hCcyc
  have hσC : σ ∈ C := by
    change σ ∈ Subgroup.centralizer ({σ} : Set (MulAut A))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
  have hτC : τ ∈ C := by
    change τ ∈ Subgroup.centralizer ({σ} : Set (MulAut A))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm
  let σC : ↥C := ⟨σ, hσC⟩
  let τC : ↥C := ⟨τ, hτC⟩
  have hordC : orderOf σC = orderOf τC := by
    have h1 : (σC : MulAut A) = σ := rfl
    have h2 : (τC : MulAut A) = τ := rfl
    rw [← Subgroup.orderOf_coe σC, ← Subgroup.orderOf_coe τC, h1, h2, hσ, hτ]
  -- inside the cyclic group `C`, equal orders give equal cyclic subgroups
  have hEqC : Subgroup.zpowers σC = Subgroup.zpowers τC := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hordC]
  have hmem : σ ∈ Subgroup.zpowers τ := by
    have h1 : σC ∈ Subgroup.zpowers τC := hEqC ▸ Subgroup.mem_zpowers σC
    rw [Subgroup.mem_zpowers_iff] at h1
    obtain ⟨j, hj⟩ := h1
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨j, ?_⟩
    have h2 := congrArg (fun x : ↥C => (x : MulAut A)) hj
    simpa [σC, τC] using h2
  have hmem' : τ ∈ Subgroup.zpowers σ := by
    have h1 : τC ∈ Subgroup.zpowers σC := hEqC ▸ Subgroup.mem_zpowers τC
    rw [Subgroup.mem_zpowers_iff] at h1
    obtain ⟨j, hj⟩ := h1
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨j, ?_⟩
    have h2 := congrArg (fun x : ↥C => (x : MulAut A)) hj
    simpa [σC, τC] using h2
  exact le_antisymm (Subgroup.zpowers_le.mpr hmem) (Subgroup.zpowers_le.mpr hmem')

end Work.ThmF.ChV12
