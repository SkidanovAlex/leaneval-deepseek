import Mathlib
import Submission.Work.CFTLib.ShafDeps
import Submission.Work.CFTLib.Basic
import Submission.Work.CFTLib.Unramified.isEverywhereUnramified_iff
import Submission.Work.CFTLib.Transport.isUnramified_algEquiv
import Submission.Work.CFTLib.ProP.isUnramifiedAtInfinitePlaces_sup
import Submission.Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup
import Submission.Work.Tower.Unramified.Compositum
import Submission.Work.Tower.Unramified.maxElemAbUnram3_isUnramified

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.CFTLib.ProP

noncomputable section

/-! ## The defining family of `F^{un,p}` as a directed set

The trusted definition `LeanEval.NumberTheory.maximalUnramifiedProPF F p` is the supremum
`⨆ (M) (_ : FiniteDimensional F M) (_ : IsGalois F M) (_ : IsPGroup p (M ≃ₐ[F] M))
(_ : NumberField M) (_ : IsEverywhereUnramified F M), M`.  We re-index it by a structure
`ShafExt F p` so that the family becomes a `Directed` family of intermediate fields, which lets us
use `IntermediateField.coe_iSup_of_directed`. -/

/-- The product of two `p`-groups is a `p`-group. -/
private lemma shaf_isPGroup_prod {p : ℕ} {G H : Type*} [Group G] [Group H]
    (hG : IsPGroup p G) (hH : IsPGroup p H) : IsPGroup p (G × H) := by
  intro g
  obtain ⟨k, hk⟩ := hG g.1
  obtain ⟨l, hl⟩ := hH g.2
  refine ⟨k + l, ?_⟩
  have e1 : g.1 ^ p ^ (k + l) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
  have e2 : g.2 ^ p ^ (k + l) = 1 := by rw [pow_add, mul_comm, pow_mul, hl, one_pow]
  rw [Prod.ext_iff]
  exact ⟨by simpa using e1, by simpa using e2⟩

/-- The data of a finite Galois everywhere-unramified `p`-extension of `F`, presented as an
intermediate field of the fixed algebraic closure `AlgebraicClosure F`. -/
structure ShafExt (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] where
  /-- The field, as an intermediate field of the algebraic closure. -/
  M : IntermediateField F (AlgebraicClosure F)
  /-- `M/F` is finite. -/
  finite : FiniteDimensional F M
  /-- `M/F` is Galois. -/
  galois : IsGalois F M
  /-- `Gal(M/F)` is a `p`-group. -/
  isP : IsPGroup p (↥M ≃ₐ[F] ↥M)
  /-- `↥M` is a number field. -/
  nf : NumberField ↥M
  /-- `M/F` is everywhere unramified. -/
  unram : LeanEval.NumberTheory.IsEverywhereUnramified F ↥M

/-- The trivial extension `⊥ ≅ F` is a finite Galois everywhere-unramified `p`-extension of `F`;
this exhibits the defining family of `F^{un,p}` as nonempty. -/
def shafBotExt (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    ShafExt F p := by
  haveI hnf : NumberField ↥(⊥ : IntermediateField F (AlgebraicClosure F)) :=
    NumberField.of_module_finite F ↥(⊥ : IntermediateField F (AlgebraicClosure F))
  refine ⟨⊥, inferInstance, inferInstance, ?_, hnf, ?_⟩
  · haveI : Subsingleton (↥(⊥ : IntermediateField F (AlgebraicClosure F)) ≃ₐ[F]
        ↥(⊥ : IntermediateField F (AlgebraicClosure F))) := by
      refine ⟨fun σ τ => AlgEquiv.ext fun x => ?_⟩
      obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp x.2
      apply Subtype.ext
      have hx : x = algebraMap F ↥(⊥ : IntermediateField F (AlgebraicClosure F)) a := by
        apply Subtype.ext
        exact ha.symm
      rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]
    exact IsPGroup.of_subsingleton p _
  · rw [Work.CFTLib.Unramified.isEverywhereUnramified_iff]
    refine ⟨Work.CFTLib.differentIdeal_of_forallPrimes
      (Work.Tower.Unramified.bot_isUnramified F).forallPrimes, ?_⟩
    exact Work.CFTLib.Transport.unramifiedAtInfinitePlaces_algEquiv
      (e := (IntermediateField.botEquiv F (AlgebraicClosure F)).symm)
      (IsUnramifiedAtInfinitePlaces.id F)

/-- **The compositum of two everywhere-unramified extensions of `F` is everywhere unramified.**
The finite-prime part is the compositum theorem for `IsUnramifiedExtensionForallPrimes`; the
archimedean part is `Work.CFTLib.ProP.isUnramifiedAtInfinitePlaces_sup`. -/
private lemma shaf_isEverywhereUnramified_sup (F : Type) [Field F] [NumberField F]
    (E₁ E₂ : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F ↥E₁] [FiniteDimensional F ↥E₂]
    [NumberField ↥E₁] [NumberField ↥E₂] [NumberField ↥(E₁ ⊔ E₂)]
    (h₁ : LeanEval.NumberTheory.IsEverywhereUnramified F ↥E₁)
    (h₂ : LeanEval.NumberTheory.IsEverywhereUnramified F ↥E₂) :
    LeanEval.NumberTheory.IsEverywhereUnramified F ↥(E₁ ⊔ E₂) := by
  haveI hfin : FiniteDimensional F ↥(E₁ ⊔ E₂) := IntermediateField.finiteDimensional_sup E₁ E₂
  refine ⟨?_, ?_⟩
  · have hd₁ : differentIdeal (𝓞 F) (𝓞 ↥E₁) = ⊤ :=
      (Work.CFTLib.Unramified.differentIdeal_eq_top_iff_forall_mem_primesOver F ↥E₁).mpr h₁.1
    have hd₂ : differentIdeal (𝓞 F) (𝓞 ↥E₂) = ⊤ :=
      (Work.CFTLib.Unramified.differentIdeal_eq_top_iff_forall_mem_primesOver F ↥E₂).mpr h₂.1
    have hfp : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥(E₁ ⊔ E₂) :=
      Work.Tower.Unramified.isUnramifiedExtensionForallPrimes_sup
        (Work.CFTLib.forallPrimes_of_differentIdeal hd₁)
        (Work.CFTLib.forallPrimes_of_differentIdeal hd₂)
    exact (Work.CFTLib.Unramified.differentIdeal_eq_top_iff_forall_mem_primesOver
      F ↥(E₁ ⊔ E₂)).mp (Work.CFTLib.differentIdeal_of_forallPrimes hfp)
  · have hinf₁ : IsUnramifiedAtInfinitePlaces F ↥E₁ :=
      (Work.CFTLib.Unramified.isUnramifiedAtInfinitePlaces_iff F ↥E₁).mpr h₁.2
    have hinf₂ : IsUnramifiedAtInfinitePlaces F ↥E₂ :=
      (Work.CFTLib.Unramified.isUnramifiedAtInfinitePlaces_iff F ↥E₂).mpr h₂.2
    have hsup : IsUnramifiedAtInfinitePlaces F ↥(E₁ ⊔ E₂) :=
      isUnramifiedAtInfinitePlaces_sup F (AlgebraicClosure F) E₁ E₂ hinf₁ hinf₂
    exact (Work.CFTLib.Unramified.isUnramifiedAtInfinitePlaces_iff F ↥(E₁ ⊔ E₂)).mp hsup

/-- The compositum of two finite everywhere-unramified Galois `p`-extensions of `F` is again a
finite everywhere-unramified Galois `p`-extension of `F`.  In particular the defining family of
`F^{un,p}` is directed. -/
def shafSupExt (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (i j : ShafExt F p) : ShafExt F p := by
  haveI hi : FiniteDimensional F ↥i.M := i.finite
  haveI hj : FiniteDimensional F ↥j.M := j.finite
  haveI hgi : IsGalois F ↥i.M := i.galois
  haveI hgj : IsGalois F ↥j.M := j.galois
  haveI hni : NumberField ↥i.M := i.nf
  haveI hnj : NumberField ↥j.M := j.nf
  haveI : Normal F ↥i.M := i.galois.to_normal
  haveI : Normal F ↥j.M := j.galois.to_normal
  haveI hnfM : NumberField ↥(i.M ⊔ j.M) := NumberField.of_module_finite F ↥(i.M ⊔ j.M)
  haveI hgalM : IsGalois F ↥(i.M ⊔ j.M) := by
    rw [isGalois_iff]
    exact ⟨inferInstance, inferInstance⟩
  haveI hisPM : IsPGroup p (↥(i.M ⊔ j.M) ≃ₐ[F] ↥(i.M ⊔ j.M)) :=
    IsPGroup.of_injective (shaf_isPGroup_prod i.isP j.isP)
      (IntermediateField.restrictNormalHomSupProd i.M j.M)
      (IntermediateField.restrictNormalHomSupProd_injective i.M j.M)
  exact ⟨i.M ⊔ j.M, IntermediateField.finiteDimensional_sup i.M j.M, hgalM, hisPM, hnfM,
    shaf_isEverywhereUnramified_sup F i.M j.M i.unram j.unram⟩

/-- `maximalUnramifiedProPF F p` is the supremum of the (directed) family of its defining
members. -/
theorem shaf_maximalUnramifiedProPF_eq_iSup (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact (Nat.Prime p)] :
    LeanEval.NumberTheory.maximalUnramifiedProPF F p = ⨆ i : ShafExt F p, i.M := by
  refine le_antisymm ?_ ?_
  · rw [LeanEval.NumberTheory.maximalUnramifiedProPF]
    apply iSup_le; intro M
    apply iSup_le; intro h1
    apply iSup_le; intro h2
    apply iSup_le; intro h3
    apply iSup_le; intro h4
    apply iSup_le; intro h5
    exact le_iSup (fun i : ShafExt F p => i.M) ⟨M, h1, h2, h3, h4, h5⟩
  · refine iSup_le (fun i => ?_)
    rw [LeanEval.NumberTheory.maximalUnramifiedProPF]
    exact le_iSup_of_le i.M
      (le_iSup_of_le i.finite
        (le_iSup_of_le i.galois
          (le_iSup_of_le i.isP
            (le_iSup_of_le i.nf
              (le_iSup_of_le i.unram le_rfl)))))

/-- In a directed family of intermediate fields, a finite set of elements whose images each lie in
some member lies entirely in a single member. -/
private lemma shaf_exists_forall_mem_of_finset {K₀ E : Type} [Field K₀] [Field E] [Algebra K₀ E]
    {ι : Type*} [Nonempty ι] {K : ι → IntermediateField K₀ E} (hdir : Directed (· ≤ ·) K)
    {α : Type*} (s : Finset α) (g : α → E) (h : ∀ x ∈ s, ∃ i, g x ∈ K i) :
    ∃ i, ∀ x ∈ s, g x ∈ K i := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | insert a s ha ih =>
      obtain ⟨i, hi⟩ := h a (Finset.mem_insert_self a s)
      have h' : ∀ x ∈ s, ∃ j, g x ∈ K j := fun x hx => h x (Finset.mem_insert_of_mem hx)
      obtain ⟨j, hj⟩ := ih h'
      obtain ⟨k, hik, hjk⟩ := hdir i j
      refine ⟨k, fun x hx => ?_⟩
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hik hi
      · exact hjk (hj x hx)

/-- `IsEverywhereUnramified` is inherited by a finite intermediate field `K` of an everywhere
unramified extension `M` of `F`. -/
private lemma shaf_isEverywhereUnramified_of_le (F : Type) [Field F] [NumberField F]
    (K M : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F M] [FiniteDimensional F K]
    [NumberField ↥M] [NumberField ↥K]
    (hunram : LeanEval.NumberTheory.IsEverywhereUnramified F ↥M) (h : K ≤ M) :
    LeanEval.NumberTheory.IsEverywhereUnramified F ↥K := by
  let K' : IntermediateField F ↥M := IntermediateField.restrict h
  have hK' : CFTLib.IsUnramified F ↥K' := by
    refine ⟨?_, ?_⟩
    · have hMdiff : differentIdeal (𝓞 F) (𝓞 ↥M) = ⊤ :=
        (Work.CFTLib.Unramified.differentIdeal_eq_top_iff_forall_mem_primesOver F ↥M).mpr
          hunram.1
      have hMfp : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥M :=
        Work.CFTLib.forallPrimes_of_differentIdeal hMdiff
      have hK'fp : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K' := hMfp.tower.1
      exact Work.CFTLib.differentIdeal_of_forallPrimes hK'fp
    · haveI hMinf : IsUnramifiedAtInfinitePlaces F ↥M :=
        (Work.CFTLib.Unramified.isUnramifiedAtInfinitePlaces_iff F ↥M).mpr hunram.2
      haveI : Algebra.IsAlgebraic ↥K' ↥M := by
        haveI hfin : Module.Finite ↥K' ↥M :=
          Module.Finite.of_restrictScalars_finite F ↥K' ↥M
        exact Algebra.IsAlgebraic.of_finite ↥K' ↥M
      exact IsUnramifiedAtInfinitePlaces.bot F ↥K' ↥M
  have hK : CFTLib.IsUnramified F ↥K :=
    Work.CFTLib.Transport.isUnramified_algEquiv
      (e := (IntermediateField.restrictAlgEquiv h).symm) hK'
  exact (Work.CFTLib.Unramified.isEverywhereUnramified_iff F ↥K).mpr hK

/-- **Every finite Galois subextension of `F^{un,p}` is itself an everywhere-unramified Galois
`p`-extension of `F`.**

`E = maximalUnramifiedProPF F p` is the compositum, inside `AlgebraicClosure F`, of all finite
Galois everywhere-unramified extensions of `F` with `p`-group Galois group.  Conversely, if
`K ≤ E` is a finite Galois intermediate field, then `K/F` is everywhere unramified (ramification
index `1` at every nonzero prime of `𝓞 F`, real places stay real) and `Gal(K/F)` is a `p`-group.

Proof: the defining family is directed under compositum (`shafSupExt`: the compositum of two
everywhere-unramified Galois `p`-extensions is again one: finite, Galois, unramified at all finite
primes and at infinity, and `Gal(E₁E₂/F) ↪ Gal(E₁/F) × Gal(E₂/F)`); since `K/F` is finite and
generated by finitely many elements and the family is directed, `K` lies in a *single* member `M`;
then `K/F` is a subextension of the everywhere-unramified `p`-extension `M/F`. -/
theorem le_maximalUnramifiedProPF
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F K] [IsGalois F K]
    [NumberField ↥K] (hle : K ≤ LeanEval.NumberTheory.maximalUnramifiedProPF F p) :
    LeanEval.NumberTheory.IsEverywhereUnramified F ↥K ∧ IsPGroup p (K ≃ₐ[F] K) := by
  classical
  -- The defining family is nonempty and directed, so its supremum is the union of its members.
  haveI hne : Nonempty (ShafExt F p) := ⟨shafBotExt F p⟩
  have hdir : Directed (· ≤ ·) (fun i : ShafExt F p => i.M) :=
    fun i j => ⟨shafSupExt F p i j, le_sup_left, le_sup_right⟩
  have hcoe : ((⨆ i : ShafExt F p, i.M : IntermediateField F (AlgebraicClosure F)) :
      Set (AlgebraicClosure F)) = ⋃ (i : ShafExt F p), (i.M : Set (AlgebraicClosure F)) :=
    IntermediateField.coe_iSup_of_directed hdir
  rw [shaf_maximalUnramifiedProPF_eq_iSup F p] at hle
  -- Every element of `K` lies in some member of the family.
  have hmem : ∀ x : ↥K, ∃ i : ShafExt F p, (x : AlgebraicClosure F) ∈ i.M := fun x => by
    have hx : (x : AlgebraicClosure F) ∈
        ((⨆ i : ShafExt F p, i.M : IntermediateField F (AlgebraicClosure F)) :
          Set (AlgebraicClosure F)) := hle x.2
    rw [hcoe] at hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact ⟨i, hi⟩
  -- `K/F` is finite, so a finite set generates `K` as an `F`-vector space.
  obtain ⟨s, hsf, hs⟩ :=
    Submodule.fg_def.mp (Module.finite_def.mp (inferInstance : Module.Finite F ↥K))
  -- ... and, by directedness, all its elements lie in a single member `i₀`.
  obtain ⟨i₀, hi₀⟩ := shaf_exists_forall_mem_of_finset hdir hsf.toFinset
    (fun x : ↥K => (x : AlgebraicClosure F)) (fun x _ => hmem x)
  have hispan : ∀ x ∈ (s : Set ↥K), (x : AlgebraicClosure F) ∈ i₀.M :=
    fun x hx => hi₀ x (hsf.mem_toFinset.mpr hx)
  have hLK : K ≤ i₀.M := by
    intro y hy
    have hy1 : (⟨y, hy⟩ : ↥K) ∈ Submodule.span F (s : Set ↥K) := by rw [hs]; trivial
    have hsub : Submodule.span F (s : Set ↥K) ≤
        Submodule.comap (IntermediateField.val K).toLinearMap (i₀.M).toSubmodule :=
      Submodule.span_le.mpr hispan
    have hmem' := hsub hy1
    rw [Submodule.mem_comap] at hmem'
    simpa using hmem'
  haveI hifin : FiniteDimensional F ↥i₀.M := i₀.finite
  haveI hinf : NumberField ↥i₀.M := i₀.nf
  haveI higal : IsGalois F ↥i₀.M := i₀.galois
  haveI hinorm : Normal F ↥i₀.M := i₀.galois.to_normal
  refine ⟨?_, ?_⟩
  · -- `K/F` is a subextension of the everywhere-unramified `i₀.M/F`.
    exact shaf_isEverywhereUnramified_of_le F K i₀.M i₀.unram hLK
  · -- `Gal(K/F)` is a quotient of the `p`-group `Gal(i₀.M/F)`.
    haveI : IsGalois F ↥(IntermediateField.restrict hLK) :=
      IsGalois.of_algEquiv (IntermediateField.restrictAlgEquiv hLK)
    haveI : Normal F ↥(IntermediateField.restrict hLK) :=
      (inferInstance : IsGalois F ↥(IntermediateField.restrict hLK)).to_normal
    have hp1 : IsPGroup p Gal(↥(IntermediateField.restrict hLK)/F) :=
      IsPGroup.of_surjective i₀.isP
        (AlgEquiv.restrictNormalHom (K₁ := ↥i₀.M) (↥(IntermediateField.restrict hLK)))
        (AlgEquiv.restrictNormalHom_surjective (E := ↥i₀.M)
          (K₁ := ↥(IntermediateField.restrict hLK)))
    exact IsPGroup.of_equiv hp1 (AlgEquiv.autCongr (IntermediateField.restrictAlgEquiv hLK)).symm

end

end Work.CFTLib.ProP
