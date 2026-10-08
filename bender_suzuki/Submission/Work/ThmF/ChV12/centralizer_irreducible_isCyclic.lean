import Mathlib
import Submission.Work.ThmF.ChV12.mulAut_mul_comm_of_commute_of_irreducible
import Submission.Work.ThmF.ChV12.adjoin_sigma_card_and_domain
import Submission.Work.ThmF.ChV12.centralizer_mulAut_linear_equiv
import Submission.Work.ThmF.ChV12.card_centralizer_le_card_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The centralizer of an irreducible automorphism of an elementary abelian `2`-group is cyclic

Let `A` be a finite elementary abelian `2`-group (`hA2`, `hAc`) of order `2 ^ k` (`k ≥ 1`), and let
`σ : MulAut A` be *irreducible*: the only `σ`-invariant subgroups of `A` are `⊥` and `⊤`.

Then the centralizer of `σ` in `MulAut A` is cyclic of order `2 ^ k - 1`.

The mathematical content is Schur's lemma: putting `Q = Additive A` (a `ZMod 2`-module) and
`A_σ = 𝔽₂[σ] ⊆ End Q`, irreducibility says `Q` is a simple `𝔽₂[σ]`-module.  Then `A_σ` is a finite
domain, hence a field (`adjoin_sigma_card_and_domain`), and `Q` is a 1-dimensional `A_σ`-vector
space, so `Nat.card A_σ = Nat.card Q`.  Every unit of `A_σ` is an automorphism of `Q` commuting with
`σ`, i.e. an element of the centralizer, and (by cardinality) conversely; the centralizer is thus
`A_σˣ`, of order `Nat.card Q - 1`, cyclic because the unit group of a finite field is cyclic.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Work.ThmF.ChV12

/-- Irreducibility of a linear automorphism of a `ZMod 2`-module, stated for `Submodule`s, follows
from the same statement for additive subgroups (`AddSubgroup`) — the two notions of subobject have
the same underlying sets. -/
theorem hirr_submodule_of_hirr_addSubgroup {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    (σ : Q ≃ₗ[ZMod 2] Q)
    (hirr : ∀ W : AddSubgroup Q, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤) :
    ∀ W : Submodule (ZMod 2) Q, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤ := by
  intro W hWne hinv
  have hne : W.toAddSubgroup ≠ ⊥ := by
    intro h
    apply hWne
    have hx : (↑W.toAddSubgroup : Set Q) = ({0} : Set Q) := by
      have h' := congrArg (fun s : AddSubgroup Q => (s : Set Q)) h
      rwa [AddSubgroup.coe_bot] at h'
    have hx2 : (W : Set Q) = ({0} : Set Q) := by rwa [Submodule.coe_toAddSubgroup] at hx
    refine SetLike.ext (fun x => ?_)
    rw [Submodule.mem_bot]
    exact (Set.ext_iff.mp hx2 x).trans Set.mem_singleton_iff
  have hinv' : ∀ x ∈ W.toAddSubgroup, σ x ∈ W.toAddSubgroup := by
    intro x hx
    exact hinv x hx
  have htop := hirr W.toAddSubgroup hne hinv'
  exact (Submodule.toAddSubgroup_eq_top).mp htop

/-- The centralizer of an irreducible linear automorphism of a finite nontrivial `ZMod 2`-module
`Q` is cyclic of order `|Q| - 1` (Schur's lemma; the centralizer is the unit group of the field
`𝔽₂[σ] ≅ 𝔽_{|Q|}`). -/
theorem linear_centralizer_isCyclic {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]
    [Finite Q] [Nontrivial Q] (σ : Q ≃ₗ[ZMod 2] Q)
    (hirr : ∀ W : Submodule (ZMod 2) Q, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤) :
    IsCyclic ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) ∧
      Nat.card ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) = Nat.card Q - 1 := by
  classical
  let A : Subalgebra (ZMod 2) (Module.End (ZMod 2) Q) :=
    Algebra.adjoin (ZMod 2) ({(σ : Q →ₗ[ZMod 2] Q)} : Set (Module.End (ZMod 2) Q))
  obtain ⟨hdom, hcommA, hcardA⟩ := adjoin_sigma_card_and_domain σ hirr
  haveI : Finite (Module.End (ZMod 2) Q) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) Q => (f : Q → Q)) DFunLike.coe_injective
  haveI : Finite A := Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Finite (Q ≃ₗ[ZMod 2] Q) :=
    Finite.of_injective (fun f : Q ≃ₗ[ZMod 2] Q => (f : Q → Q))
      (fun a b h => LinearEquiv.ext (fun x => congrFun h x))
  letI : CommRing A :=
    { (inferInstance : Ring A) with mul_comm := fun a b => isMulCommutative_iff.mp hcommA a b }
  haveI : IsDomain A := hdom
  haveI : DecidableEq A := Classical.decEq A
  letI : Field A := Fintype.fieldOfDomain A
  -- `Aˣ` is cyclic (the unit group of a finite field) of order `|A| - 1 = |Q| - 1`.
  haveI hcycA : IsCyclic Aˣ :=
    isCyclic_of_injective_ringHom (Units.coeHom A) (fun _ _ h => Units.ext h)
  -- The natural homomorphism `Aˣ → centralizer of σ`: a unit of `A` is an automorphism of `Q`
  -- commuting with `σ`.
  let ψ : Aˣ →* (Q ≃ₗ[ZMod 2] Q) :=
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Q).toMonoidHom).comp
      (Units.map (Subalgebra.val A).toRingHom.toMonoidHom)
  have hψ_val : ∀ u : Aˣ, ((ψ u : Q ≃ₗ[ZMod 2] Q) : Q →ₗ[ZMod 2] Q)
      = ((u : A) : Module.End (ZMod 2) Q) := fun u => rfl
  have hcommg : ∀ u : A, (u : Module.End (ZMod 2) Q) * (σ : Module.End (ZMod 2) Q)
      = (σ : Module.End (ZMod 2) Q) * (u : Module.End (ZMod 2) Q) := by
    intro u
    exact (Algebra.commute_of_mem_adjoin_self (R := ZMod 2) (a := (σ : Module.End (ZMod 2) Q))
      (b := (u : Module.End (ZMod 2) Q)) u.2).eq.symm
  have hψmem : ∀ u : Aˣ, ψ u ∈ Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q)) := by
    intro u
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have key : ((σ * ψ u : Q ≃ₗ[ZMod 2] Q) : Q →ₗ[ZMod 2] Q)
        = (((ψ u) * σ : Q ≃ₗ[ZMod 2] Q) : Q →ₗ[ZMod 2] Q) := by
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, hψ_val u,
        hcommg (u : A)]
    exact LinearEquiv.ext (fun x => congrArg (fun f : Q →ₗ[ZMod 2] Q => f x) key)
  have hψinj : Function.Injective ψ := by
    intro u v huv
    have h2 : ((u : A) : Module.End (ZMod 2) Q) = ((v : A) : Module.End (ZMod 2) Q) := by
      rw [← hψ_val u, ← hψ_val v, huv]
    exact Units.ext (Subtype.ext h2)
  -- Lower bound: `Aˣ` injects into the centralizer.
  have hlow : Nat.card Aˣ
      ≤ Nat.card ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) := by
    have hle : (ψ.range : Set (Q ≃ₗ[ZMod 2] Q))
        ⊆ ((Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) : Set (Q ≃ₗ[ZMod 2] Q)) := by
      intro x hx
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
      exact hψmem u
    calc Nat.card Aˣ = Nat.card ↥ψ.range :=
          Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
      _ ≤ Nat.card ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) :=
          Nat.card_le_card_of_injective (Set.inclusion hle) (Set.inclusion_injective hle)
  -- Upper bound: an element of the centralizer is determined by its value at a nonzero vector.
  have hup : Nat.card ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q)))
      ≤ Nat.card Q - 1 :=
    card_centralizer_le_card_sub_one σ hirr
  have hunits : Nat.card Aˣ = Nat.card Q - 1 := by
    rw [Nat.card_units, hcardA]
  have heq : Nat.card ↥(Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) = Nat.card Q - 1 :=
    le_antisymm hup (by rw [← hunits]; exact hlow)
  -- Consequently the range of `ψ` is all of the centralizer.
  have hrange : ψ.range = Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q)) := by
    refine Subgroup.eq_of_le_of_card_ge (K := Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q)))
      (fun x hx => ?_) (le_of_eq ?_)
    · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hx
      exact hψmem u
    · rw [heq, ← hunits, Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]
  have hsurj : Function.Surjective
      (ψ.codRestrict (Subgroup.centralizer ({σ} : Set (Q ≃ₗ[ZMod 2] Q))) hψmem) := by
    intro w
    have hw : (w : Q ≃ₗ[ZMod 2] Q) ∈ ψ.range := by rw [hrange]; exact w.2
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hw
    exact ⟨u, Subtype.ext (by simpa using hu)⟩
  exact ⟨isCyclic_of_surjective _ hsurj, heq⟩

theorem centralizer_irreducible_isCyclic {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : Nat.card A = 2 ^ k) (σ : MulAut A)
    (hirr : ∀ W : Subgroup A, W ≠ ⊥ → (∀ x ∈ W, σ x ∈ W) → W = ⊤) :
    IsCyclic ↥(Subgroup.centralizer ({σ} : Set (MulAut A))) ∧
      Nat.card ↥(Subgroup.centralizer ({σ} : Set (MulAut A))) = 2 ^ k - 1 := by
  classical
  letI : CommGroup A := { ‹Group A› with mul_comm := hAc }
  have hexp : ∀ x : Additive A, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    exact Additive.ext (show (x + x).toMul = (0 : Additive A).toMul from hA2 x.toMul)
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule hexp
  haveI : Fintype A := Fintype.ofFinite A
  have hcard_gt : 1 < Fintype.card A := by
    rw [← Nat.card_eq_fintype_card, hk]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
  haveI : Nontrivial A := Fintype.one_lt_card_iff_nontrivial.mp hcard_gt
  haveI : Nontrivial (Additive A) := inferInstance
  let σL : Additive A ≃ₗ[ZMod 2] Additive A :=
    (σ.toAdditive).toLinearEquiv (fun (c : ZMod 2) x => ZMod.map_smul _ c x)
  have hirr_lin : ∀ W : Submodule (ZMod 2) (Additive A), W ≠ ⊥ →
      (∀ x ∈ W, σL x ∈ W) → W = ⊤ := by
    refine hirr_submodule_of_hirr_addSubgroup σL ?_
    intro W hWne hWinv
    exact hirr_additive (A := A) σ hirr W hWne (fun x hx => by
      have hx' : σL x = σ x := rfl
      rw [← hx']; exact hWinv x hx)
  obtain ⟨hcyc_lin, hcard_lin⟩ := linear_centralizer_isCyclic σL hirr_lin
  haveI : IsCyclic ↥(Subgroup.centralizer ({σL} : Set (Additive A ≃ₗ[ZMod 2] Additive A))) :=
    hcyc_lin
  obtain ⟨e⟩ := centralizer_mulAut_linear_equiv (A := A) σ
  refine ⟨?_, ?_⟩
  · exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  · rw [Nat.card_congr e.toEquiv, hcard_lin]
    have hQ : Nat.card (Additive A) = 2 ^ k := by
      rw [Nat.card_congr Additive.toMul]; exact hk
    rw [hQ]

end Work.ThmF.ChV12
