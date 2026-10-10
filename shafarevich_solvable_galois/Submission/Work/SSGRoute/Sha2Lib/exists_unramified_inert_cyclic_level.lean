import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.CycLevel.card_stabilizer_eq_of_localNormSubgroup_index
import Submission.Work.SSGRoute.PTW.compact_connected_abelian_pow_surjective
import Submission.Work.SSGRoute.PTW.ideleClassGroup_quotient_instances
import Submission.Work.SSGRoute.Sha2Lib.Sha2Interface
import Submission.Work.SSGRoute.Sha2Lib.Sha2LocalChar
import Submission.Work.SSGRoute.Sha2Lib.Sha2Pieces
import Submission.Work.SSGRoute.Sha2Lib.aux_unramified_inert_level_of_character
import Submission.Work.SSGRoute.Sha2Lib.cyclic_degree_two_unramified_inert_at_place
import Submission.Work.SSGRoute.glue_involution_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open scoped NumberField Pointwise

set_option maxHeartbeats 8000000

variable {p : ℕ} {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

omit [NumberField k] in
/-- A place of `Ω` which is finite over `k` is finite over any intermediate level. -/
lemma comap_ne_top_of_isFinPlace (K : IntermediateField k Ω) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
  intro htop
  refine hA ?_
  have h : (A.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) = ⊤ := by rw [htop]; rfl
  rwa [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq k ↥K Ω] at h

omit [NumberField k] in
/-- `IsFinPlace` is invariant under the action of `G_k`. -/
lemma isFinPlace_smul (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (σ : Ω ≃ₐ[k] Ω) : SSGRoute.IsFinPlace k (σ • A) := by
  show (σ • A).comap (algebraMap k Ω) ≠ ⊤
  rw [SSGRoute.comap_algebraMap_smul]
  exact hA

omit [NumberField k] in
/-- The inertia group is closed under powers. -/
lemma isInertia_pow {A : ValuationSubring Ω} {σ : Ω ≃ₐ[k] Ω} (hσ : SSGRoute.IsInertia k A σ)
    (n : ℕ) : SSGRoute.IsInertia k A (σ ^ n) :=
  (Work.SSGRoute.mem_inertiaSub k Ω A (σ ^ n)).mp
    (Subgroup.pow_mem _ ((Work.SSGRoute.mem_inertiaSub k Ω A σ).mpr hσ) n)

/-- **The internal form of the target**: `Ω` is an algebraic closure of `k`.

The proof is the Grünwald–Wang route: over the cyclotomic level `K = k⟮ζ_p⟯` one prescribes at the
places of `K` above `l` the unramified Frobenius character `Work.SSGRoute.Sha2Lib.UnramLocalDatum`,
glues it by `Work.HRec.grunwald_surjective_odd_over_same`, averages over `Gal(K/k)` and inflates by
`Work.HRec.exists_inflated_of_invariant`, and takes the fixed field of the resulting global
character. -/
theorem exists_unramified_inert_cyclic_level_of_algClosure (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    ∃ (F : IntermediateField k Ω), ∃ (_ : NumberField ↥F) (_ : FiniteDimensional k ↥F)
      (_ : IsGalois k ↥F),
      IsCyclic (↥F ≃ₐ[k] ↥F) ∧ Nat.card (↥F ≃ₐ[k] ↥F) = p ∧
      (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F),
        q'.asIdeal.LiesOver l.asIdeal →
          q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
          q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hpp : p.Prime := Fact.out
  -- ## the cyclotomic base `K = k⟮ζ⟯`
  obtain ⟨ζ, hζ, hfdK, hnfK, hgalK, hcopK⟩ := cycloSetup p hpp k Ω
  let K : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hfdK' : FiniteDimensional k K := hfdK
  haveI hnfK' : NumberField ↥K := hnfK
  haveI hgalK' : IsGalois k K := hgalK
  have hcop : Nat.Coprime (Nat.card (K ≃ₐ[k] K)) p := hcopK
  have hζK : ζ ∈ K := IntermediateField.subset_adjoin k ({ζ} : Set Ω) (Set.mem_singleton ζ)
  -- ## the index of `G_K` in `G_k` and its basic properties
  have hker_eq : (AlgEquiv.restrictNormalHom ↥K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  haveI hfinQ : Fintype ((Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) :=
    Fintype.ofEquiv (K ≃ₐ[k] K)
      ((QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom ↥K)
        (AlgEquiv.restrictNormalHom_surjective Ω)).symm.toEquiv.trans
        (Equiv.cast (congrArg (fun N => ((Ω ≃ₐ[k] Ω) ⧸ N)) hker_eq)))
  let dq : ℕ := Nat.card ((Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup)
  have hcard_eq : dq = Nat.card (K ≃ₐ[k] K) := by
    change Nat.card ((Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) = Nat.card (K ≃ₐ[k] K)
    rw [← hker_eq]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (AlgEquiv.restrictNormalHom_surjective Ω)).toEquiv
  have hdq : Nat.Coprime dq p := by
    rw [hcard_eq]; exact hcop
  have hdq_ne : (dq : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((dq : ℤ) : ZMod p) = 0 := by rw [Int.cast_natCast]; exact h0
    have hdvdZ : (p : ℤ) ∣ (dq : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (dq : ℤ) p).mp h0'
    have hdvd : p ∣ dq := Int.natCast_dvd_natCast.mp hdvdZ
    have h1 : p ∣ 1 := by
      have h2 : p ∣ Nat.gcd dq p := Nat.dvd_gcd hdvd (dvd_refl p)
      rwa [hdq.gcd_eq_one] at h2
    exact hpp.not_dvd_one h1
  /- every `dq`-th power lies in `G_K` -/
  have hpow_mem_ker : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ dq ∈ K.fixingSubgroup := by
    intro σ
    have h1 : (QuotientGroup.mk (σ ^ dq) : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) = 1 := by
      have h2 : ((QuotientGroup.mk σ : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup)) ^ dq = 1 :=
        pow_card_eq_one' (G := (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup)
          (x := (QuotientGroup.mk σ : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup))
      have h3 : (QuotientGroup.mk (σ ^ dq) : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) =
          ((QuotientGroup.mk σ : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup)) ^ dq :=
        map_pow (QuotientGroup.mk' K.fixingSubgroup) σ dq
      rw [h3, h2]
    exact (QuotientGroup.eq_one_iff (σ ^ dq)).mp h1
  -- ## place bookkeeping: one place of `Ω` per prime of `K` above `l`
  let S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) := {l}
  have hSmem : l ∈ S := Finset.mem_singleton_self l
  let d := placeData_aux k Ω K S
  let P₀ : ValuationSubring Ω := d.base ⟨l, hSmem⟩
  have hP₀mem : P₀ ∈ d.T := d.hbase_mem ⟨l, hSmem⟩
  have hP₀fin : SSGRoute.IsFinPlace k P₀ := d.hTfin P₀ hP₀mem
  have hP₀comap : P₀.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k l := d.hbase_comap ⟨l, hSmem⟩
  have hvOf : ∀ P : ↥d.T, d.base (d.vOf P) = P₀ := by
    intro P
    have h1 : d.vOf P = ⟨l, hSmem⟩ := Subtype.ext (Finset.mem_singleton.mp (d.vOf P).2)
    rw [h1]
  -- ## the local datum at the base place: the unramified Frobenius character
  have hDatum : UnramLocalDatum p k Ω K P₀ := by
    -- extract the character and its properties (`Classical.choice`, since the datum is data)
    let φ : (Ω ≃ₐ[k] Ω) → ZMod p :=
      Classical.choose (localUnramChar p k Ω P₀ hP₀fin)
    have hspec := Classical.choose_spec (localUnramChar p k Ω P₀ hP₀fin)
    have hspec' : (∀ a b : Ω ≃ₐ[k] Ω, a ∈ SSGRoute.decomp k P₀ →
          b ∈ SSGRoute.decomp k P₀ → φ (a * b) = φ a + φ b) ∧
        (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω P₀ → φ σ = 0) ∧
        (∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k P₀ ∧ φ σ ≠ 0) ∧
        (∀ σ τ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k P₀ → τ ∈ SSGRoute.decomp k P₀ →
          φ (τ * σ * τ⁻¹) = φ σ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k P₀) φ := hspec
    have haddφ : ∀ a b : Ω ≃ₐ[k] Ω, a ∈ SSGRoute.decomp k P₀ →
        b ∈ SSGRoute.decomp k P₀ → φ (a * b) = φ a + φ b := hspec'.1
    have hzeroφ : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω P₀ → φ σ = 0 :=
      hspec'.2.1
    have hneφ : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k P₀ ∧ φ σ ≠ 0 := hspec'.2.2.1
    have hconjφ : ∀ σ τ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k P₀ → τ ∈ SSGRoute.decomp k P₀ →
        φ (τ * σ * τ⁻¹) = φ σ := hspec'.2.2.2.1
    have hlcφ : SSGRoute.IsLocConstOn (SSGRoute.decomp k P₀) φ := hspec'.2.2.2.2
    have hφ1 : φ 1 = 0 := by
      have h := haddφ 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _)
      rw [mul_one] at h
      exact add_right_cancel (by rw [zero_add]; exact h.symm)
    -- the element of `D_{P₀} ⊓ G_K` witnessing non-triviality
    let σ₀ : Ω ≃ₐ[k] Ω := Classical.choose hneφ
    have hσ₀D : σ₀ ∈ SSGRoute.decomp k P₀ := (Classical.choose_spec hneφ).1
    have hσ₀ne : φ σ₀ ≠ 0 := (Classical.choose_spec hneφ).2
    have hpow_formula : ∀ n : ℕ, φ (σ₀ ^ n) = (n : ZMod p) * φ σ₀ := by
      intro n
      induction n with
      | zero => rw [pow_zero, hφ1, Nat.cast_zero, zero_mul]
      | succ k ih =>
          rw [pow_succ, haddφ (σ₀ ^ k) σ₀ (Subgroup.pow_mem _ hσ₀D k) hσ₀D, ih, Nat.cast_succ,
            add_mul, one_mul]
    -- the open subgroup on which `φ` vanishes
    have hlc' : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
        ∀ g ∈ SSGRoute.decomp k P₀, ∀ u ∈ U, u ∈ SSGRoute.decomp k P₀ → φ (g * u) = φ g :=
      hlcφ
    let U : Subgroup (Ω ≃ₐ[k] Ω) := Classical.choose hlc'
    have hUopen : IsOpen (U : Set (Ω ≃ₐ[k] Ω)) := (Classical.choose_spec hlc').1
    have hU : ∀ g ∈ SSGRoute.decomp k P₀, ∀ u ∈ U, u ∈ SSGRoute.decomp k P₀ →
        φ (g * u) = φ g := (Classical.choose_spec hlc').2
    refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
    · -- additivity, restricted to `D_{P₀} ⊓ G_K`
      intro g hg h hh
      exact haddφ g h (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hh).1
    · -- local constancy
      refine ⟨U, hUopen, ?_⟩
      intro x hx hxmem
      have h := hU 1 (Subgroup.one_mem _) x hx (Subgroup.mem_inf.mp hxmem).1
      rw [one_mul] at h
      rw [h, hφ1]
    · -- non-triviality, on `D_{P₀} ⊓ G_K`
      refine ⟨σ₀ ^ dq, Subgroup.mem_inf.mpr
        ⟨Subgroup.pow_mem _ hσ₀D dq, hpow_mem_ker σ₀⟩, ?_⟩
      rw [hpow_formula dq]
      exact mul_ne_zero hdq_ne hσ₀ne
    · -- invariance under conjugation by `D_{P₀}`
      intro σ hσ δ hδ
      exact hconjφ δ σ (Subgroup.mem_inf.mp hδ).1 hσ
    · -- vanishing on the inertia
      intro δ hδ hδI
      exact hzeroφ δ ((Work.SSGRoute.mem_inertiaSub k Ω P₀ δ).mpr hδI)
  -- ## the transported data at the places of `T`
  let fP : (P : ↥d.T) →
      ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup) → ZMod p :=
    fun P δ => hDatum.f (d.u P * (δ : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹)
  haveI hKnorm : (K.fixingSubgroup).Normal := inferInstance
  have hfPadd : ∀ (P : ↥d.T)
      (a b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)),
      fP P (a * b) = fP P a + fP P b := by
    intro P a b
    show hDatum.f (d.u P *
        ((a * b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) :
          Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) =
      hDatum.f (d.u P * (a : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) +
        hDatum.f (d.u P * (b : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹)
    have hconj_eq : d.u P *
        ((a * b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) :
          Ω ≃ₐ[k] Ω) * (d.u P)⁻¹ =
        (d.u P * (a : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) *
          (d.u P * (b : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) := by
      rw [Subgroup.coe_mul]; group
    rw [hconj_eq]
    refine hDatum.hadd _ ?_ _ ?_
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hu : d.u P • (P : ValuationSubring Ω) = P₀ := by rw [d.hu P, hvOf P]
        calc (d.u P * (a : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) • P₀
            = d.u P • ((a : Ω ≃ₐ[k] Ω) • ((d.u P)⁻¹ • P₀)) := by rw [mul_smul, mul_smul]
          _ = d.u P • ((a : Ω ≃ₐ[k] Ω) • (P : ValuationSubring Ω)) := by
                rw [← hu, inv_smul_smul]
          _ = d.u P • (P : ValuationSubring Ω) := by
                rw [MulAction.mem_stabilizer_iff.mp a.2.1]
          _ = P₀ := hu
      · exact hKnorm.conj_mem (a : Ω ≃ₐ[k] Ω) a.2.2 (d.u P)
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hu : d.u P • (P : ValuationSubring Ω) = P₀ := by rw [d.hu P, hvOf P]
        calc (d.u P * (b : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) • P₀
            = d.u P • ((b : Ω ≃ₐ[k] Ω) • ((d.u P)⁻¹ • P₀)) := by rw [mul_smul, mul_smul]
          _ = d.u P • ((b : Ω ≃ₐ[k] Ω) • (P : ValuationSubring Ω)) := by
                rw [← hu, inv_smul_smul]
          _ = d.u P • (P : ValuationSubring Ω) := by
                rw [MulAction.mem_stabilizer_iff.mp b.2.1]
          _ = P₀ := hu
      · exact hKnorm.conj_mem (b : Ω ≃ₐ[k] Ω) b.2.2 (d.u P)
  have hP₀memT : P₀ ∈ d.T := hP₀mem
  have hzmem : ∀ P : ↥d.T, d.u P • (P : ValuationSubring Ω) = P₀ := by
    intro P; rw [d.hu P, hvOf P]
  have hfPcont : ∀ P : ↥d.T,
      ∃ U : Subgroup ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) ∧
        ∀ x ∈ U, fP P x = 0 := by
    intro P
    obtain ⟨U, hUopen, hUz⟩ := hDatum.hcont
    let cg : (Ω ≃ₐ[k] Ω) →* (Ω ≃ₐ[k] Ω) :=
      { toFun := fun x => d.u P * x * (d.u P)⁻¹
        map_one' := by simp
        map_mul' := fun a b => by group }
    have hcg_cont : Continuous (cg : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω)) := by
      show Continuous (fun x : Ω ≃ₐ[k] Ω => d.u P * x * (d.u P)⁻¹)
      exact (continuous_const.mul continuous_id).mul continuous_const
    have hpre_open : IsOpen ((Subgroup.comap cg U : Subgroup (Ω ≃ₐ[k] Ω)) :
        Set (Ω ≃ₐ[k] Ω)) := by
      rw [Subgroup.coe_comap]
      exact hUopen.preimage hcg_cont
    refine ⟨Subgroup.comap
      (Subgroup.subtype (SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup))
      (Subgroup.comap cg U), ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      exact hpre_open.preimage continuous_subtype_val
    · intro x hx
      have hxU : cg ((x : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) :
          Ω ≃ₐ[k] Ω) ∈ U := hx
      have hxmem : cg ((x : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) :
          Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k P₀ ⊓ K.fixingSubgroup := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have hu : d.u P • (P : ValuationSubring Ω) = P₀ := hzmem P
          calc (d.u P * (x : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) • P₀
              = d.u P • ((x : Ω ≃ₐ[k] Ω) • ((d.u P)⁻¹ • P₀)) := by rw [mul_smul, mul_smul]
            _ = d.u P • ((x : Ω ≃ₐ[k] Ω) • (P : ValuationSubring Ω)) := by
                  rw [← hu, inv_smul_smul]
            _ = d.u P • (P : ValuationSubring Ω) := by
                  rw [MulAction.mem_stabilizer_iff.mp x.2.1]
            _ = P₀ := hu
        · exact hKnorm.conj_mem (x : Ω ≃ₐ[k] Ω) x.2.2 (d.u P)
      show hDatum.f (cg ((x : ↥(SSGRoute.decomp k (P : ValuationSubring Ω)
        ⊓ K.fixingSubgroup)) : Ω ≃ₐ[k] Ω)) = 0
      exact hUz _ hxU hxmem
  -- ## Grünwald
  obtain ⟨z, hzadd, hzloc, hzagree⟩ :=
    Work.HRec.grunwald_surjective_odd_over_same p hp k Ω K ζ hζ hζK d.T d.hTfin d.hTinj
      fP hfPadd hfPcont
  have hz1 : z 1 = 0 := by
    have h := hzadd 1 K.fixingSubgroup.one_mem 1 K.fixingSubgroup.one_mem
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (add_zero (z 1)).symm)
  have hzconj : ∀ a b : Ω ≃ₐ[k] Ω, a ∈ K.fixingSubgroup → b ∈ K.fixingSubgroup →
      z (a * b * a⁻¹) = z b := by
    intro a b ha hb
    have hab : a * b ∈ K.fixingSubgroup := K.fixingSubgroup.mul_mem ha hb
    rw [hzadd (a * b) hab a⁻¹ (K.fixingSubgroup.inv_mem ha), hzadd a ha b hb]
    have h2 : z a⁻¹ = - z a := by
      have h3 := hzadd a ha a⁻¹ (K.fixingSubgroup.inv_mem ha)
      rw [mul_inv_cancel, hz1] at h3
      exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h3.symm)
    rw [h2]; abel
  let zN : ↥(K.fixingSubgroup) → ZMod p := fun δ => z δ
  have hzNadd : ∀ a b : ↥(K.fixingSubgroup), zN (a * b) = zN a + zN b := fun a b =>
    hzadd a a.2 b b.2
  let sec : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup → (Ω ≃ₐ[k] Ω) :=
    fun x => (QuotientGroup.mk_surjective x).choose
  have hsec : ∀ x, QuotientGroup.mk (sec x) = x :=
    fun x => (QuotientGroup.mk_surjective x).choose_spec
  let zbar : ↥(K.fixingSubgroup) → ZMod p :=
    fun δ => ∑ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup, zN (conjN K.fixingSubgroup (sec x) δ)
  have hzbar_add : ∀ a b : ↥(K.fixingSubgroup), zbar (a * b) = zbar a + zbar b :=
    (conjAvg_aux p (Ω ≃ₐ[k] Ω) K.fixingSubgroup zN hzNadd sec hsec).1
  have hzbar_inv : ∀ (σ : Ω ≃ₐ[k] Ω) (τ : ↥(K.fixingSubgroup))
      (h : σ * (τ : Ω ≃ₐ[k] Ω) * σ⁻¹ ∈ K.fixingSubgroup),
      zbar ⟨σ * (τ : Ω ≃ₐ[k] Ω) * σ⁻¹, h⟩ = zbar τ := by
    intro σ τ h
    rw [show (⟨σ * (τ : Ω ≃ₐ[k] Ω) * σ⁻¹, h⟩ : ↥(K.fixingSubgroup))
      = conjN K.fixingSubgroup σ τ from Subtype.ext rfl]
    exact (conjAvg_aux p (Ω ≃ₐ[k] Ω) K.fixingSubgroup zN hzNadd sec hsec).2 σ τ
  have hzbar_cont : ∃ U : Subgroup ↥(K.fixingSubgroup),
      IsOpen (U : Set ↥(K.fixingSubgroup)) ∧ ∀ x ∈ U, zbar x = 0 := by
    obtain ⟨U, hUopen, hUz⟩ := hzloc
    have hUz0 : ∀ u : Ω ≃ₐ[k] Ω, u ∈ U → u ∈ K.fixingSubgroup → z u = 0 := by
      intro u hu huK
      have h := hUz 1 K.fixingSubgroup.one_mem u hu huK
      rw [one_mul] at h
      rw [h, hz1]
    have hcont : ∀ g : Ω ≃ₐ[k] Ω, IsOpen
        ((Subgroup.comap (MulAut.conjNormal g).toMonoidHom
          (Subgroup.comap (Subgroup.subtype K.fixingSubgroup) U) :
          Subgroup ↥(K.fixingSubgroup)) : Set ↥(K.fixingSubgroup)) := by
      intro g
      have hgcont : Continuous (fun x : ↥(K.fixingSubgroup) =>
          MulAut.conjNormal g x) := by
        refine Continuous.subtype_mk ?_ _
        show Continuous (fun x : ↥(K.fixingSubgroup) => g * (x : Ω ≃ₐ[k] Ω) * g⁻¹)
        exact (continuous_const.mul continuous_subtype_val).mul continuous_const
      have hbase_open : IsOpen ((Subgroup.comap (Subgroup.subtype K.fixingSubgroup) U :
          Subgroup ↥(K.fixingSubgroup)) : Set ↥(K.fixingSubgroup)) := by
        rw [Subgroup.coe_comap]
        exact hUopen.preimage continuous_subtype_val
      rw [Subgroup.coe_comap]
      exact hbase_open.preimage hgcont
    haveI hfinite : Finite ((Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) := Fintype.finite hfinQ
    refine ⟨⨅ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
      Subgroup.comap (MulAut.conjNormal (H := K.fixingSubgroup) (sec x)).toMonoidHom
        (Subgroup.comap (Subgroup.subtype K.fixingSubgroup) U), ?_, ?_⟩
    · rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite (fun x => by rw [Subgroup.coe_comap]; exact hcont (sec x))
    · intro δ hδ
      have hterm : ∀ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
          zN (conjN K.fixingSubgroup (sec x) δ) = 0 := by
        intro x
        have hx : MulAut.conjNormal (sec x) δ ∈
            Subgroup.comap (Subgroup.subtype K.fixingSubgroup) U := (Subgroup.mem_iInf.mp hδ) x
        have hxU : ((MulAut.conjNormal (sec x) δ : ↥(K.fixingSubgroup)) :
            Ω ≃ₐ[k] Ω) ∈ U := hx
        show z (((MulAut.conjNormal (sec x) δ : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω)) = 0
        exact hUz0 _ hxU (MulAut.conjNormal (sec x) δ).2
      show (∑ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
        zN (conjN K.fixingSubgroup (sec x) δ)) = 0
      rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_const_zero]
  obtain ⟨η, hηadd, hηext, hηcontU⟩ :=
    Work.HRec.exists_inflated_of_invariant p hpp (Ω ≃ₐ[k] Ω) K.fixingSubgroup dq
      rfl hdq zbar hzbar_add hzbar_cont hzbar_inv
  have hη1 : η 1 = 0 := by
    have h := hηadd 1 1
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (add_zero (η 1)).symm)
  have hη_pow : ∀ (n : ℕ) (σ : Ω ≃ₐ[k] Ω), η (σ ^ n) = (n : ZMod p) * η σ := by
    intro n σ
    induction n with
    | zero => rw [pow_zero, hη1, Nat.cast_zero, zero_mul]
    | succ k ih => rw [pow_succ, hηadd, ih, Nat.cast_succ, add_mul, one_mul]
  -- ## the key computation: `z` is constant on the conjugates of `decomp P₀`-elements
  have hkey : ∀ (x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) (δ : ↥(K.fixingSubgroup)),
      (δ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k P₀ →
      z ((sec x) * (δ : Ω ≃ₐ[k] Ω) * (sec x)⁻¹) = hDatum.f δ := by
    intro x δ hδ
    have hBfin : SSGRoute.IsFinPlace k ((sec x) • P₀) := isFinPlace_smul P₀ hP₀fin (sec x)
    have hBcomap : ((sec x) • P₀).comap (algebraMap k Ω) = P₀.comap (algebraMap k Ω) :=
      SSGRoute.comap_algebraMap_smul P₀ (sec x)
    obtain ⟨P, hPT, ρ, hρK, hρP⟩ :=
      d.hcover ⟨l, hSmem⟩ ((sec x) • P₀) hBfin
        (by rw [hBcomap, hP₀comap])
    set γ : Ω ≃ₐ[k] Ω := ρ⁻¹ with hγdef
    have hγK : γ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hρK
    have hγs : (γ * sec x) • P₀ = (P : ValuationSubring Ω) := by
      rw [mul_smul, ← hρP, hγdef, smul_smul, inv_mul_cancel, one_smul]
    have hu : d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω) = P₀ := hzmem ⟨P, hPT⟩
    have hw : (d.u ⟨P, hPT⟩ * (γ * sec x)) • P₀ = P₀ := by
      rw [mul_smul, hγs, hu]
    have hmem : (γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹ ∈
        SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hgs : (γ * sec x) • P₀ = (P : ValuationSubring Ω) := hγs
        calc ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) • (P : ValuationSubring Ω)
            = (γ * sec x) • ((δ : Ω ≃ₐ[k] Ω) • ((γ * sec x)⁻¹ • (P : ValuationSubring Ω))) := by
                rw [mul_smul, mul_smul]
          _ = (γ * sec x) • ((δ : Ω ≃ₐ[k] Ω) • P₀) := by
                rw [← hgs, inv_smul_smul]
          _ = (γ * sec x) • P₀ := by rw [MulAction.mem_stabilizer_iff.mp hδ]
          _ = (P : ValuationSubring Ω) := hgs
      · exact hKnorm.conj_mem (δ : Ω ≃ₐ[k] Ω) δ.2 (γ * sec x)
    have hzγ : z ((sec x) * (δ : Ω ≃ₐ[k] Ω) * (sec x)⁻¹) =
        z ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) := by
      have hconjK : (sec x) * (δ : Ω ≃ₐ[k] Ω) * (sec x)⁻¹ ∈ K.fixingSubgroup :=
        hKnorm.conj_mem (δ : Ω ≃ₐ[k] Ω) δ.2 (sec x)
      have h1 : γ * ((sec x) * (δ : Ω ≃ₐ[k] Ω) * (sec x)⁻¹) * γ⁻¹ =
          (γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹ := by group
      rw [← h1]
      exact (hzconj γ ((sec x) * (δ : Ω ≃ₐ[k] Ω) * (sec x)⁻¹) hγK hconjK).symm
    have hzag : z ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) =
        hDatum.f ((d.u ⟨P, hPT⟩) * ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) *
          (d.u ⟨P, hPT⟩)⁻¹) :=
      hzagree ⟨P, hPT⟩ ⟨_, hmem⟩
    have hw_eq : (d.u ⟨P, hPT⟩ * (γ * sec x)) * (δ : Ω ≃ₐ[k] Ω) *
        (d.u ⟨P, hPT⟩ * (γ * sec x))⁻¹ =
        (d.u ⟨P, hPT⟩) * ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) *
          (d.u ⟨P, hPT⟩)⁻¹ := by group
    have hfin : hDatum.f ((d.u ⟨P, hPT⟩) * ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) *
        (d.u ⟨P, hPT⟩)⁻¹) = hDatum.f δ := by
      rw [← hw_eq]
      exact hDatum.hinv (d.u ⟨P, hPT⟩ * (γ * sec x))
        (MulAction.mem_stabilizer_iff.mpr hw) δ (Subgroup.mem_inf.mpr ⟨hδ, δ.2⟩)
    rw [hzγ, hzag, hfin]
  have hzbar_const : ∀ (δ : ↥(K.fixingSubgroup)),
      (δ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k P₀ → zbar δ = (dq : ZMod p) * hDatum.f δ := by
    intro δ hδ
    have h1 : zbar δ = ∑ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
        zN (conjN K.fixingSubgroup (sec x) δ) := rfl
    rw [h1]
    have h2 : ∀ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
        zN (conjN K.fixingSubgroup (sec x) δ) = hDatum.f δ := by
      intro x
      show z (((conjN K.fixingSubgroup (sec x) δ : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω)) =
        hDatum.f δ
      have hcoe : ((conjN K.fixingSubgroup (sec x) δ : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) =
          sec x * δ * (sec x)⁻¹ := rfl
      rw [hcoe]
      exact hkey x δ hδ
    rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hcard : Fintype.card ((Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) = dq :=
      Nat.card_eq_fintype_card.symm
    rw [hcard]
  -- ## `z` vanishes on inertia elements of `G_K` above `l`
  have hz_kill_inertia : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (hAcomap : A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k l)
      (τ : Ω ≃ₐ[k] Ω), τ ∈ K.fixingSubgroup → SSGRoute.IsInertia k A τ → z τ = 0 := by
    intro A hA hAcomap τ hτK hτI
    obtain ⟨P, hPT, ρ, hρK, hρP⟩ :=
      d.hcover ⟨l, hSmem⟩ A hA (by rw [hAcomap, hP₀comap])
    set γ : Ω ≃ₐ[k] Ω := ρ⁻¹ with hγdef
    have hγK : γ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hρK
    have hγA : γ • A = (P : ValuationSubring Ω) := by
      rw [hγdef, ← hρP, smul_smul, inv_mul_cancel, one_smul]
    have hconjI : SSGRoute.IsInertia k (P : ValuationSubring Ω) (γ * τ * γ⁻¹) := by
      have h := SSGRoute.isInertia_conj A γ τ
      rw [hγA] at h
      exact h.mpr hτI
    have hconjK : γ * τ * γ⁻¹ ∈ K.fixingSubgroup := hKnorm.conj_mem τ hτK γ
    have hzγ : z τ = z (γ * τ * γ⁻¹) := by
      rw [hzconj γ τ hγK hτK]
    have hu : d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω) = P₀ := hzmem ⟨P, hPT⟩
    have htransport : d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹ ∈
        SSGRoute.decomp k P₀ ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · calc (d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) • P₀
            = d.u ⟨P, hPT⟩ • ((γ * τ * γ⁻¹) • ((d.u ⟨P, hPT⟩)⁻¹ • P₀)) := by
                rw [mul_smul, mul_smul]
          _ = d.u ⟨P, hPT⟩ • ((γ * τ * γ⁻¹) • (P : ValuationSubring Ω)) := by
                rw [← hu, inv_smul_smul]
          _ = d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω) := by
                rw [MulAction.mem_stabilizer_iff.mp hconjI.1]
          _ = P₀ := hu
      · exact hKnorm.conj_mem (γ * τ * γ⁻¹) hconjK (d.u ⟨P, hPT⟩)
    have htransportI : SSGRoute.IsInertia k P₀
        (d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) := by
      have h := SSGRoute.isInertia_conj (P : ValuationSubring Ω) (d.u ⟨P, hPT⟩) (γ * τ * γ⁻¹)
      rw [hu] at h
      exact h.mpr hconjI
    have hmem : γ * τ * γ⁻¹ ∈
        SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup :=
      Subgroup.mem_inf.mpr ⟨hconjI.1, hconjK⟩
    have hzag : z (γ * τ * γ⁻¹) = hDatum.f
        (d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) :=
      hzagree ⟨P, hPT⟩ ⟨_, hmem⟩
    rw [hzγ, hzag]
    exact hDatum.hinertia _ htransport htransportI
  -- ## the local properties of `η`
  have hη_kills : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (hAcomap : A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k l)
      (σ : Ω ≃ₐ[k] Ω), SSGRoute.IsInertia k A σ → η σ = 0 := by
    intro A hA hAcomap σ hσ
    have hpow_mem : σ ^ dq ∈ K.fixingSubgroup := hpow_mem_ker σ
    have hpowI : SSGRoute.IsInertia k A (σ ^ dq) := isInertia_pow hσ dq
    have hz0 : z (σ ^ dq) = 0 := hz_kill_inertia A hA hAcomap _ hpow_mem hpowI
    have hext : η (σ ^ dq) = zbar ⟨σ ^ dq, hpow_mem⟩ := hηext ⟨σ ^ dq, hpow_mem⟩
    have hzbar0 : zbar ⟨σ ^ dq, hpow_mem⟩ = 0 := by
      have h1 : zbar ⟨σ ^ dq, hpow_mem⟩ = ∑ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
          zN (conjN K.fixingSubgroup (sec x) ⟨σ ^ dq, hpow_mem⟩) := rfl
      rw [h1]
      refine Finset.sum_eq_zero fun x _ => ?_
      have hxI : SSGRoute.IsInertia k ((sec x) • A) (sec x * (σ ^ dq) * (sec x)⁻¹) := by
        have h := SSGRoute.isInertia_conj A (sec x) (σ ^ dq)
        exact h.mpr hpowI
      have hxcomap : ((sec x) • A).comap (algebraMap k Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k l := by
        rw [SSGRoute.comap_algebraMap_smul, hAcomap]
      have hxmem : ((conjN K.fixingSubgroup (sec x) ⟨σ ^ dq, hpow_mem⟩ :
          ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) = sec x * (σ ^ dq) * (sec x)⁻¹ := rfl
      show z (((conjN K.fixingSubgroup (sec x) ⟨σ ^ dq, hpow_mem⟩ :
        ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω)) = 0
      rw [hxmem]
      exact hz_kill_inertia ((sec x) • A) (isFinPlace_smul A hA (sec x)) hxcomap _
        (conjN K.fixingSubgroup (sec x) ⟨σ ^ dq, hpow_mem⟩).2 hxI
    have hmul : (dq : ZMod p) * η σ = 0 := by
      rw [← hη_pow dq σ, hext, hzbar0]
    exact (mul_eq_zero.mp hmul).resolve_left hdq_ne
  -- ## non-triviality of `η` on the decomposition group of `P₀`
  obtain ⟨δ₀, hδ₀mem, hδ₀ne⟩ := hDatum.hne
  have hδ₀D : (δ₀ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k P₀ := (Subgroup.mem_inf.mp hδ₀mem).1
  have hδ₀K : (δ₀ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hδ₀mem).2
  have hzbar_ne : zbar ⟨δ₀, hδ₀K⟩ ≠ 0 := by
    rw [hzbar_const ⟨δ₀, hδ₀K⟩ hδ₀D]
    exact mul_ne_zero hdq_ne hδ₀ne
  have hηne : η (δ₀ : Ω ≃ₐ[k] Ω) ≠ 0 := by
    rw [hηext ⟨δ₀, hδ₀K⟩]
    exact hzbar_ne
  -- ## the level, from the global character
  have hηloc : SSGRoute.IsLocConstOn ⊤ η := by
    obtain ⟨U, hUopen, hU⟩ := hηcontU
    refine ⟨U, hUopen, ?_⟩
    intro g _ u hu _
    rw [hηadd g u, hU u hu, add_zero]
  have hηinn : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω P₀ → η σ = 0 := by
    intro σ hσ
    exact hη_kills P₀ hP₀fin hP₀comap σ ((Work.SSGRoute.mem_inertiaSub k Ω P₀ σ).mp hσ)
  have hηnon : ∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k P₀ ∧ η σ ≠ 0 :=
    ⟨(δ₀ : Ω ≃ₐ[k] Ω), hδ₀D, hηne⟩
  exact unramified_inert_level_of_character p k Ω l P₀ hP₀comap η hηadd hηloc hηinn hηnon

/-- **Transport of the ramification index along an isomorphism of number fields.**

If `e : 𝓞 K ≃ₐ[𝓞 k] 𝓞 L` is an isomorphism of rings of integers over `𝓞 k`, `l` is a finite place
of `k` and `q` is a prime of `𝓞 L` lying over `l`, then the conjugate prime `q.comap e` of `𝓞 K`
lying over `l` has the same ramification index over `𝓞 k` as `q`. -/
theorem ramificationIdx_comap_algEquiv (K L : Type) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra k K] [Algebra k L]
    (e : 𝓞 K ≃ₐ[𝓞 k] 𝓞 L) (l : IsDedekindDomain.HeightOneSpectrum (𝓞 k))
    (q : Ideal (𝓞 L)) [q.IsPrime] [q.LiesOver l.asIdeal] :
    (Ideal.comap e q).ramificationIdx (𝓞 k) = q.ramificationIdx (𝓞 k) := by
  haveI hlies : (Ideal.comap e q).LiesOver l.asIdeal :=
    Ideal.LiesOver.of_eq_comap l.asIdeal e rfl
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (S := 𝓞 L) l.asIdeal q l.ne_bot,
    ← Ideal.ramificationIdx'_eq_ramificationIdx (S := 𝓞 K) l.asIdeal (Ideal.comap e q)
      l.ne_bot,
    Ideal.ramificationIdx'_comap_eq (S := 𝓞 K) (S₁ := 𝓞 L) l.asIdeal e q]

/-- **Transport of the inertia degree along an isomorphism of number fields.**

If `e : 𝓞 K ≃ₐ[𝓞 k] 𝓞 L` is an isomorphism of rings of integers over `𝓞 k`, `l` is a finite place
of `k` and `q` is a prime of `𝓞 L` lying over `l`, then the conjugate prime `q.comap e` of `𝓞 K`
lying over `l` has the same inertia degree over `𝓞 k` as `q`. -/
theorem inertiaDeg_comap_algEquiv (K L : Type) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra k K] [Algebra k L]
    (e : 𝓞 K ≃ₐ[𝓞 k] 𝓞 L) (l : IsDedekindDomain.HeightOneSpectrum (𝓞 k))
    (q : Ideal (𝓞 L)) [q.IsPrime] [q.IsMaximal] [q.LiesOver l.asIdeal] :
    (Ideal.comap e q).inertiaDeg (𝓞 k) = q.inertiaDeg (𝓞 k) := by
  haveI hlies : (Ideal.comap e q).LiesOver l.asIdeal :=
    Ideal.LiesOver.of_eq_comap l.asIdeal e rfl
  rw [← Ideal.inertiaDeg'_eq_inertiaDeg (p := l.asIdeal) (P := q),
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := l.asIdeal) (P := Ideal.comap e q),
    Ideal.inertiaDeg'_comap_eq (S := 𝓞 K) (S₁ := 𝓞 L) l.asIdeal e q]

/-- **A cyclic degree-`p` level which is unramified and inert at a prescribed finite place.**

For a prime `p`, a number field `k`, an algebraically closed field `Ω` with `k → Ω` and a finite
place `l` of `k`: there is a level `F ⊆ Ω`, finite Galois over `k`, cyclic of degree `p`, such that
every prime `q'` of `𝓞 ↥F` above `l` is unramified with inertia degree `p`.

This is the per-place input for the Sha-2 dual control argument of the Shafarevich route. -/
theorem exists_unramified_inert_cyclic_level (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (l : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    ∃ (F : IntermediateField k Ω), ∃ (_ : NumberField ↥F) (_ : FiniteDimensional k ↥F)
      (_ : IsGalois k ↥F),
      IsCyclic (↥F ≃ₐ[k] ↥F) ∧ Nat.card (↥F ≃ₐ[k] ↥F) = p ∧
      (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F),
        q'.asIdeal.LiesOver l.asIdeal →
          q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
          q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = p) := by
  by_cases hp2 : p = 2
  · subst hp2
    exact cyclic_degree_two_unramified_inert_at_place k Ω l
  · -- ## the odd case: build the level in an algebraic closure of `k`, then embed it into `Ω`
    obtain ⟨F₀, hnf₀, hfd₀, hgal₀, hcyc₀, hcard₀, hloc₀⟩ :=
      exists_unramified_inert_cyclic_level_of_algClosure p hp2 k (AlgebraicClosure k) l
    haveI hnf₀' : NumberField ↥F₀ := hnf₀
    haveI hfd₀' : FiniteDimensional k ↥F₀ := hfd₀
    haveI hgal₀' : IsGalois k ↥F₀ := hgal₀
    -- a `k`-embedding of an algebraic closure of `k` into `Ω`
    let ι : AlgebraicClosure k →ₐ[k] Ω := IsAlgClosed.lift
    let F : IntermediateField k Ω := F₀.map ι
    let e : ↥F₀ ≃ₐ[k] ↥F := IntermediateField.equivMap F₀ ι
    haveI hfdF : FiniteDimensional k ↥F := e.toLinearEquiv.finiteDimensional
    haveI hfdQF : FiniteDimensional ℚ ↥F := FiniteDimensional.trans ℚ k ↥F
    haveI hnfF : NumberField ↥F := NumberField.mk
    haveI hgalF : IsGalois k ↥F := IsGalois.of_algEquiv e
    refine ⟨F, hnfF, hfdF, hgalF, (AlgEquiv.autCongr e).isCyclic.mp hcyc₀, ?_, ?_⟩
    · rw [← Nat.card_congr (AlgEquiv.autCongr e).toEquiv]
      exact hcard₀
    · intro q' hq'
      -- the conjugate prime of `𝓞 ↥F₀`
      let eO : 𝓞 ↥F₀ ≃ₐ[𝓞 k] 𝓞 ↥F := NumberField.RingOfIntegers.mapAlgEquiv e
      let f : 𝓞 ↥F₀ →+* 𝓞 ↥F := eO
      have hfs : Function.Surjective f := fun y => eO.surjective y
      let q₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F₀) :=
        IsDedekindDomain.HeightOneSpectrum.comap f hfs q'
      have hq₀ : q₀.asIdeal = Ideal.comap eO q'.asIdeal := rfl
      have hlies₀ : q₀.asIdeal.LiesOver l.asIdeal :=
        Ideal.LiesOver.of_eq_comap l.asIdeal eO rfl
      obtain ⟨h1, h2⟩ := hloc₀ q₀ hlies₀
      haveI hqprime : q'.asIdeal.IsPrime := q'.isPrime
      haveI hqmax : q'.asIdeal.IsMaximal := q'.isMaximal
      haveI hqLies : q'.asIdeal.LiesOver l.asIdeal := hq'
      have hram : q₀.asIdeal.ramificationIdx (𝓞 k) = q'.asIdeal.ramificationIdx (𝓞 k) := by
        rw [hq₀]
        exact ramificationIdx_comap_algEquiv ↥F₀ ↥F eO l q'.asIdeal
      have hiner : q₀.asIdeal.inertiaDeg (𝓞 k) = q'.asIdeal.inertiaDeg (𝓞 k) := by
        rw [hq₀]
        exact inertiaDeg_comap_algEquiv ↥F₀ ↥F eO l q'.asIdeal
      exact ⟨hram ▸ h1, hiner ▸ h2⟩

end Work.SSGRoute.Sha2Lib
