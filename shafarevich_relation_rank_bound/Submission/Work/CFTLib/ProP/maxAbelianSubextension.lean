import Mathlib
import Submission.Work.CFTLib.ShafDeps
import Submission.Work.CFTLib.Basic
import Submission.Work.CFTLib.ProP.Galois
import Submission.Work.CFTLib.ProP.le_maximalUnramifiedProPF
import Submission.Work.CFTLib.Unramified.isEverywhereUnramified_iff
import Submission.Work.CFTLib.Transport.isUnramified_algEquiv
import Submission.Work.CFTLib.ProP.embeds_abelian_unramifiedP_sc

/-!
# The maximal abelian unramified `p`-subextension inside `F^{un,p}`

This file proves `Work.CFTLib.ProP.maxAbelianSubextension`.  See the docstring of the main theorem
for the statement; the auxiliary lemmas developed here are

* `isUnramified_sup`: the compositum of two everywhere-unramified extensions is everywhere
  unramified (finite primes: the proven
  `Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup`; infinite places: the proven
  `Work.CFTLib.ProP.isUnramifiedAtInfinitePlaces_sup`);
* `unramified_of_unramified_tower`: unramifiedness descends from the top field of a tower;
* `isUnramified_isPGroup_of_le`: transfer of the proven `le_maximalUnramifiedProPF` to subfields of
  `F^{un,p}` presented over `F^{un,p}` itself;
* `toF`, `overK`: change of base field for subfields of `F^{un,p}` (the underlying set is
  unchanged);
* `Good`: the family of finite abelian unramified `p`-subextensions of `K` inside `F^{un,p}`, with
  its bottom element and its closure under `⊔`.
-/

open NumberField
open scoped Classical

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

namespace Work.CFTLib.ProP

noncomputable section

variable {F : Type} [Field F] [NumberField F]

/-! ## Unramifiedness: composita and towers -/

/-- **The compositum of two everywhere-unramified extensions is everywhere unramified.** -/
theorem isUnramified_sup {F A : Type} [Field F] [NumberField F] [Field A] [Algebra F A]
    (E₁ E₂ : IntermediateField F A) [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    [NumberField ↥E₁] [NumberField ↥E₂] [NumberField ↥(E₁ ⊔ E₂)]
    (h₁ : CFTLib.IsUnramified F ↥E₁) (h₂ : CFTLib.IsUnramified F ↥E₂) :
    CFTLib.IsUnramified F ↥(E₁ ⊔ E₂) := by
  haveI hfin : FiniteDimensional F ↥(E₁ ⊔ E₂) := IntermediateField.finiteDimensional_sup E₁ E₂
  refine ⟨?_, ?_⟩
  · exact Work.CFTLib.differentIdeal_of_forallPrimes
      (Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup
        (Work.CFTLib.forallPrimes_of_differentIdeal h₁.1)
        (Work.CFTLib.forallPrimes_of_differentIdeal h₂.1))
  · exact isUnramifiedAtInfinitePlaces_sup F A E₁ E₂ h₁.2 h₂.2

/-- **Unramifiedness descends from the top field of a tower.** -/
theorem unramified_of_unramified_tower {F K M : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Field M] [NumberField M] [Algebra F K] [Algebra F M] [Algebra K M]
    [IsScalarTower F K M] [FiniteDimensional F K] [FiniteDimensional F M]
    (h : CFTLib.IsUnramified F M) : CFTLib.IsUnramified K M := by
  refine ⟨?_, ?_⟩
  · have h1 := differentIdeal_eq_differentIdeal_mul_differentIdeal (𝓞 F) (𝓞 K) (𝓞 M)
    rw [h.1] at h1
    have htop : (⊤ : Ideal (𝓞 M)) ≤ differentIdeal (𝓞 K) (𝓞 M) := by
      rw [h1]
      exact Ideal.mul_le_left
    exact top_le_iff.mp htop
  · haveI := h.2
    exact IsUnramifiedAtInfinitePlaces.top F K M

/-! ## Transferring `le_maximalUnramifiedProPF` to fields over `F^{un,p}` -/

/-- **Every finite Galois subfield of `F^{un,p}`, presented over `F^{un,p}` itself, is an
everywhere-unramified `p`-extension of `F`.** -/
theorem isUnramified_isPGroup_of_le (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [FiniteDimensional F K] [IsGalois F K]
    [NumberField ↥K] :
    CFTLib.IsUnramified F ↥K ∧ IsPGroup p (↥K ≃ₐ[F] ↥K) := by
  let M : IntermediateField F (AlgebraicClosure F) := K.map (E F p).val
  have hMle : M ≤ E F p := by
    intro x hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  let e : ↥K ≃ₐ[F] ↥M := IntermediateField.equivMap K (E F p).val
  haveI hfd : FiniteDimensional F ↥M := Module.Finite.equiv e.toLinearEquiv
  haveI hgal : IsGalois F ↥M := IsGalois.of_algEquiv e
  haveI hnf : NumberField ↥M := NumberField.of_module_finite F ↥M
  obtain ⟨hunr, hp⟩ := le_maximalUnramifiedProPF F p M hMle
  refine ⟨?_, ?_⟩
  · exact Work.CFTLib.Transport.isUnramified_algEquiv e.symm
      ((Work.CFTLib.Unramified.isEverywhereUnramified_iff F ↥M).mp hunr)
  · exact IsPGroup.of_equiv hp (AlgEquiv.autCongr e).symm

/-! ## Change of base field for subfields of `F^{un,p}` -/

/-- An `↥K`-intermediate field of `↥(F^{un,p})`, viewed as an `F`-intermediate field: the
underlying set is unchanged. -/
def toF (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) (M : IntermediateField ↥K ↥(E F p)) :
    IntermediateField F ↥(E F p) where
  __ := M.toSubfield
  algebraMap_mem' := fun x => by
    rw [IsScalarTower.algebraMap_apply F ↥K ↥(E F p)]
    exact M.algebraMap_mem _

/-- An `F`-intermediate subfield containing `K`, viewed as an `↥K`-intermediate field: the
underlying set is unchanged. -/
def overK (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) (N : IntermediateField F ↥(E F p)) (h : K ≤ N) :
    IntermediateField ↥K ↥(E F p) where
  __ := N.toSubfield
  algebraMap_mem' := fun x => h x.2

theorem toF_le_toF (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    {K : IntermediateField F ↥(E F p)} {M N : IntermediateField ↥K ↥(E F p)}
    (h : M ≤ N) : toF F p K M ≤ toF F p K N := fun _ hx => h hx

/-- The product of two `p`-groups is a `p`-group. -/
theorem isPGroup_prod {p : ℕ} {G H : Type*} [Group G] [Group H]
    (hG : IsPGroup p G) (hH : IsPGroup p H) : IsPGroup p (G × H) := by
  intro g
  obtain ⟨k, hk⟩ := hG g.1
  obtain ⟨l, hl⟩ := hH g.2
  refine ⟨k + l, ?_⟩
  have e1 : g.1 ^ p ^ (k + l) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
  have e2 : g.2 ^ p ^ (k + l) = 1 := by rw [pow_add, mul_comm, pow_mul, hl, one_pow]
  rw [Prod.ext_iff]
  exact ⟨by simpa using e1, by simpa using e2⟩

/-- The bottom member `K` of the family, as a subfield of `F^{un,p}`, is unramified over `K`. -/
theorem isUnramified_bot (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    [hnf : NumberField ↥(⊥ : IntermediateField ↥K ↥(E F p))]
    (hKunr : CFTLib.IsUnramified F ↥K) :
    CFTLib.IsUnramified ↥K ↥(⊥ : IntermediateField ↥K ↥(E F p)) := by
  haveI hfin : FiniteDimensional F ↥(⊥ : IntermediateField ↥K ↥(E F p)) :=
    Module.Finite.trans ↥K (⊥ : IntermediateField ↥K ↥(E F p))
  have e : ↥(⊥ : IntermediateField ↥K ↥(E F p)) ≃ₐ[F] ↥K :=
    (IntermediateField.botEquiv ↥K ↥(E F p)).restrictScalars F
  have hunr : CFTLib.IsUnramified F ↥(⊥ : IntermediateField ↥K ↥(E F p)) :=
    Work.CFTLib.Transport.isUnramified_algEquiv e.symm hKunr
  exact unramified_of_unramified_tower (F := F) (K := ↥K)
    (M := ↥(⊥ : IntermediateField ↥K ↥(E F p))) hunr

/-- **A finite Galois everywhere-unramified `p`-extension of `F` is contained in `F^{un,p}`.**

This is the `le_iSup` half of the trusted definition of `maximalUnramifiedProPF`, made available
through the `iSup`-reformulation `shaf_maximalUnramifiedProPF_eq_iSup`. -/
theorem le_maximalUnramifiedProPF_of_isPGroup (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact (Nat.Prime p)] (N : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F N]
    [IsGalois F N] [NumberField ↥N] (hU : LeanEval.NumberTheory.IsEverywhereUnramified F ↥N)
    (hp : IsPGroup p (N ≃ₐ[F] N)) : N ≤ LeanEval.NumberTheory.maximalUnramifiedProPF F p := by
  rw [shaf_maximalUnramifiedProPF_eq_iSup F p]
  exact le_iSup (fun i : ShafExt F p => i.M)
    ⟨N, inferInstance, inferInstance, hp, inferInstance, hU⟩

/-! ## The family of finite abelian unramified `p`-subextensions -/

/-- Members of the family: finite Galois subextensions of `F^{un,p}/K` with abelian `p`-group
Galois group, unramified over `K`. -/
structure Good (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [NumberField ↥K] where
  /-- the subextension, as an intermediate field of `F^{un,p}` over `K` -/
  M : IntermediateField ↥K ↥(E F p)
  /-- it is finite over `K` -/
  finite : FiniteDimensional ↥K M
  /-- it is Galois over `K` -/
  galois : IsGalois ↥K M
  /-- its Galois group over `K` is abelian -/
  comm : ∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a
  /-- its Galois group over `K` is a `p`-group -/
  isP : IsPGroup p (↥M ≃ₐ[↥K] ↥M)
  /-- it is a number field -/
  nf : NumberField ↥M
  /-- it is unramified over `K` -/
  unram : CFTLib.IsUnramified ↥K ↥M

attribute [instance] Good.finite Good.galois Good.nf

/-- The automorphism group over `K` of the bottom subfield `K ⊆ F^{un,p}` is trivial. -/
theorem subsingleton_gal_bot (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [NumberField ↥K] :
    Subsingleton (↥(⊥ : IntermediateField ↥K ↥(E F p)) ≃ₐ[↥K] ↥(⊥ : IntermediateField ↥K ↥(E F p))) := by
  refine ⟨fun σ τ => ?_⟩
  exact (AlgEquiv.autCongr (IntermediateField.botEquiv ↥K ↥(E F p))).injective
    (Subsingleton.elim _ _)

/-- The trivial member: `K` itself. -/
def Good.bot (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    (hKunr : CFTLib.IsUnramified F ↥K) : Good F p K where
  M := ⊥
  finite := inferInstance
  galois := inferInstance
  comm := fun a b => by
    haveI hsub : Subsingleton (↥(⊥ : IntermediateField ↥K ↥(E F p)) ≃ₐ[↥K] ↥(⊥ : IntermediateField ↥K ↥(E F p))) :=
      subsingleton_gal_bot F p K
    exact Subsingleton.elim (a * b) (b * a)
  isP := by
    haveI hsub : Subsingleton (↥(⊥ : IntermediateField ↥K ↥(E F p)) ≃ₐ[↥K] ↥(⊥ : IntermediateField ↥K ↥(E F p))) :=
      subsingleton_gal_bot F p K
    exact IsPGroup.of_subsingleton p _
  nf := NumberField.of_module_finite ↥K ↥(⊥ : IntermediateField ↥K ↥(E F p))
  unram := isUnramified_bot F p K (hnf := NumberField.of_module_finite ↥K ↥(⊥ : IntermediateField ↥K ↥(E F p))) hKunr

/-- The compositum of two members of the family is a member. -/
def Good.sup (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [NumberField ↥K]
    (s₁ s₂ : Good F p K) : Good F p K where
  M := s₁.M ⊔ s₂.M
  finite := inferInstance
  galois := inferInstance
  comm := fun a b => by
    haveI hN₁ : Normal ↥K ↥s₁.M := s₁.galois.to_normal
    haveI hN₂ : Normal ↥K ↥s₂.M := s₂.galois.to_normal
    refine (IntermediateField.restrictNormalHomSupProd_injective s₁.M s₂.M) ?_
    simp only [map_mul]
    exact Prod.ext (s₁.comm _ _) (s₂.comm _ _)
  isP := by
    haveI hN₁ : Normal ↥K ↥s₁.M := s₁.galois.to_normal
    haveI hN₂ : Normal ↥K ↥s₂.M := s₂.galois.to_normal
    exact IsPGroup.of_injective (isPGroup_prod s₁.isP s₂.isP)
      (IntermediateField.restrictNormalHomSupProd s₁.M s₂.M)
      (IntermediateField.restrictNormalHomSupProd_injective s₁.M s₂.M)
  nf := NumberField.of_module_finite ↥K ↥(s₁.M ⊔ s₂.M)
  unram := by
    haveI : NumberField ↥(s₁.M ⊔ s₂.M) := NumberField.of_module_finite ↥K ↥(s₁.M ⊔ s₂.M)
    exact isUnramified_sup (F := ↥K) (A := ↥(E F p)) s₁.M s₂.M s₁.unram s₂.unram

/-! ## The lemma on embedding abelian unramified `p`-extensions -/

/-- **Every finite Galois abelian unramified `p`-extension of `K` embeds into a member of the
family.**  This is
`Work.CFTLib.ProP.embeds_abelian_unramifiedP_sc` (proved in the sibling file
`Submission/Work/CFTLib/ProP/embeds_abelian_unramifiedP_sc.lean`; the file
`.../embeds_abelian_unramifiedP.lean` contains the same result but imports this module, so this
self-contained copy is the one used here). -/
theorem embeds_abelian_unramifiedP_aux (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    (hKunr : CFTLib.IsUnramified F ↥K)
    (L : Type) [Field L] [NumberField L] [Algebra ↥K L] [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (hLcom : ∀ a b : L ≃ₐ[↥K] L, a * b = b * a) (hLp : IsPGroup p (L ≃ₐ[↥K] L))
    (hLunr : CFTLib.IsUnramified ↥K L) :
    ∃ (M : IntermediateField ↥K ↥(E F p)) (_ : NumberField ↥M),
      FiniteDimensional ↥K M ∧ IsGalois ↥K M ∧
      (∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a) ∧ IsPGroup p (↥M ≃ₐ[↥K] ↥M) ∧
      CFTLib.IsUnramified ↥K ↥M ∧ Nonempty (L →ₐ[↥K] ↥M) :=
  embeds_abelian_unramifiedP_sc F p K hKunr L hLcom hLp hLunr

/-! ## The main theorem -/

/-- **The maximal abelian unramified `p`-subextension of `K` inside `F^{un,p}`, made Galois over
`F`, is finite (given `hab`).**

Let `F` be a number field, `p` a prime, `E = F^{un,p} = maximalUnramifiedProPF F p` and `K ≤ E` a
finite Galois intermediate field of `E/F`.  Assume `hgalE : IsGalois F E` and
`hab : CFTLib.UnramifiedAbelianDegreeLe` (every finite unramified abelian extension `L/K` of a
number field satisfies `[L : K] ≤ Nat.card (ClassGroup (𝓞 K))`).

Then there is a finite Galois intermediate field `K'` of `E/F` with `K ≤ K'` such that

* `K'` contains (receives a `K`-algebra homomorphism from) **every** finite Galois unramified
  abelian `p`-extension `L/K`, and
* `CFTLib.IsUnramified F K'` and `IsPGroup p (Gal(K'/F))`.

These are exactly the hypotheses of `CFTLib.RelShafBound` at the pair `(K, K')`. -/
theorem maxAbelianSubextension
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (hab : CFTLib.UnramifiedAbelianDegreeLe)
    (hgalE : IsGalois F ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p))
    (K : IntermediateField F ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p))
    [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K] :
    ∃ (K' : IntermediateField F ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p)) (_ : K ≤ K')
      (_ : FiniteDimensional F K') (_ : IsGalois F K') (_ : NumberField ↥K')
      (_ : Algebra ↥K ↥K') (_ : IsScalarTower F ↥K ↥K'),
      (∀ (L : Type) [Field L] [NumberField L] [Algebra ↥K L] [FiniteDimensional ↥K L]
        [IsGalois ↥K L], (∀ a b : L ≃ₐ[↥K] L, a * b = b * a) → IsPGroup p (L ≃ₐ[↥K] L) →
        CFTLib.IsUnramified ↥K L → Nonempty (L →ₐ[↥K] ↥K')) ∧
      CFTLib.IsUnramified F ↥K' ∧ IsPGroup p (Gal(↥K'/F)) := by
  classical
  obtain ⟨hKunr, -⟩ := isUnramified_isPGroup_of_le F p K
  -- The degrees of the members of the family are bounded by the class number of `K`.
  have hdeg_bound : ∀ s : Good F p K, Module.finrank ↥K ↥s.M ≤ Nat.card (ClassGroup (𝓞 ↥K)) :=
    fun s => hab ↥K ↥s.M s.comm s.unram
  have hne : ({n : ℕ | ∃ s : Good F p K, Module.finrank ↥K ↥s.M = n}).Nonempty :=
    ⟨_, ⟨Good.bot F p K hKunr, rfl⟩⟩
  have hbdd : BddAbove {n : ℕ | ∃ s : Good F p K, Module.finrank ↥K ↥s.M = n} :=
    ⟨_, fun n ⟨s, hs⟩ => hs ▸ hdeg_bound s⟩
  obtain ⟨M₀, hM₀⟩ := Nat.sSup_mem hne hbdd
  -- every member is contained in `M₀`
  have hmax : ∀ s : Good F p K, s.M ≤ M₀.M := by
    intro s
    have h1 : Module.finrank ↥K ↥(s.M ⊔ M₀.M) ≤ Module.finrank ↥K ↥M₀.M := by
      rw [hM₀]
      exact le_csSup hbdd ⟨Good.sup F p K s M₀, rfl⟩
    have h2 : Module.finrank ↥K ↥M₀.M ≤ Module.finrank ↥K ↥(s.M ⊔ M₀.M) :=
      IntermediateField.finrank_le_of_le_right le_sup_right
    have heq : M₀.M = s.M ⊔ M₀.M :=
      IntermediateField.eq_of_le_of_finrank_eq le_sup_right (le_antisymm h2 h1)
    rw [heq]
    exact le_sup_left
  -- the Galois closure of `M₀` over `F` inside `F^{un,p}`
  haveI hfdM₀F : FiniteDimensional F ↥(toF F p K M₀.M) := by
    haveI : FiniteDimensional F ↥M₀.M := by
      letI : Algebra F ↥M₀.M :=
        ((algebraMap ↥K ↥M₀.M).comp (algebraMap F ↥K)).toAlgebra
      haveI : IsScalarTower F ↥K ↥M₀.M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      exact Module.Finite.trans (A := ↥K) (M := ↥M₀.M)
    exact ‹FiniteDimensional F ↥M₀.M›
  let K' : IntermediateField F ↥(E F p) :=
    IntermediateField.normalClosure F ↥(toF F p K M₀.M) ↥(E F p)
  haveI hfin' : FiniteDimensional F ↥K' := inferInstance
  haveI hgal' : IsGalois F ↥K' := inferInstance
  haveI hnf' : NumberField ↥K' := NumberField.of_module_finite F ↥K'
  have hM₀le' : toF F p K M₀.M ≤ K' := IntermediateField.le_normalClosure _
  have hKleM₀ : K ≤ toF F p K M₀.M := by
    intro x hx
    exact M₀.M.algebraMap_mem (⟨x, hx⟩ : ↥K)
  have hKle' : K ≤ K' := hKleM₀.trans hM₀le'
  obtain ⟨hK'unr, hK'p⟩ := isUnramified_isPGroup_of_le F p K'
  letI alg : Algebra ↥K ↥K' := (IntermediateField.inclusion hKle').toAlgebra
  have hST : IsScalarTower F ↥K ↥K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨K', hKle', hfin', hgal', hnf', alg, hST, ?_, hK'unr, hK'p⟩
  intro L _ _ _ _ _ hLcom hLp hLunr
  obtain ⟨M, hnfM, hMfd, hMgal, hMcom, hMp, hMunr, ⟨φ⟩⟩ :=
    embeds_abelian_unramifiedP_aux F p K hKunr L hLcom hLp hLunr
  let s : Good F p K := ⟨M, hMfd, hMgal, hMcom, hMp, hnfM, hMunr⟩
  have h1 : M ≤ M₀.M := hmax s
  have h2 : M₀.M ≤ overK F p K K' hKle' := fun x hx => hM₀le' hx
  exact ⟨(IntermediateField.inclusion h2).comp ((IntermediateField.inclusion h1).comp φ)⟩

end

end Work.CFTLib.ProP
