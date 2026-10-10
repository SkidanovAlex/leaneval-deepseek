import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.Sha2Lib.split_inert_level_of_character
import Submission.Work.SSGRoute.grunwald_surjective_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open scoped NumberField Pointwise

attribute [local instance] Classical.decEq

noncomputable section

set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]

omit [NumberField k] in
/-- A place of `Ω` is unchanged, as a place over an intermediate level `K`, by the action of an
element of the fixing subgroup of `K`. -/
lemma comap_algebraMap_smul_fixingSubgroup (K : IntermediateField k Ω) (A : ValuationSubring Ω)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup) :
    (σ • A).comap (algebraMap ↥K Ω) = A.comap (algebraMap ↥K Ω) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hfix : (σ⁻¹ : Ω ≃ₐ[k] Ω) • (algebraMap ↥K Ω x) = algebraMap ↥K Ω x := by
    rw [AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff K (σ⁻¹)).mp (K.fixingSubgroup.inv_mem hσ)
      (x : Ω) x.2
  rw [hfix]

/-- The local datum at a finite place, without the non-triviality requirement: it is additive and
locally constant on `D_P ⊓ G_K`, invariant under conjugation by the full decomposition group
`D_P`, and it vanishes on the inertia subgroup.  Both the (unramified) Frobenius character and the
zero character are instances. -/
structure MixLocDatum (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (P : ValuationSubring Ω) where
  /-- the local character -/
  f : (Ω ≃ₐ[k] Ω) → ZMod p
  /-- additivity on the decomposition group of `P` over `K` -/
  hadd : ∀ g ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup,
    ∀ h ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f (g * h) = f g + f h
  /-- local constancy -/
  hcont : ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
    ∀ x ∈ U, x ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup → f x = 0
  /-- invariance under conjugation by the decomposition group of `P` over `k` -/
  hinv : ∀ (σ : Ω ≃ₐ[k] Ω), σ ∈ SSGRoute.decomp k P →
    ∀ δ ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup, f (σ * δ * σ⁻¹) = f δ
  /-- the character vanishes on the inertia group of `P` -/
  hinertia : ∀ δ ∈ SSGRoute.decomp k P ⊓ K.fixingSubgroup,
    SSGRoute.IsInertia k P δ → f δ = 0

/-- The zero local datum: it prescribes that the place splits completely. -/
noncomputable def zeroLocDatum (p : ℕ) (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) (P : ValuationSubring Ω) : MixLocDatum p k Ω K P where
  f := fun _ => 0
  hadd := by intro g hg h hh; simp
  hcont := ⟨⊤, by simpa using isOpen_univ, fun x hx hx2 => rfl⟩
  hinv := by intro σ hσ δ hδ; rfl
  hinertia := by intro δ hδ hI; rfl

/-- **The unramified local datum, normalized to the finite index `dq`.**

`localUnramChar` gives a locally constant additive character `φ` of the decomposition group `D_A`
which is trivial on the inertia and non-trivial on `D_A`.  Since every `dq`-th power of an element
of `G_k` lies in `G_K = K.fixingSubgroup` (with `dq` coprime to `p`), the element `δ₀ ^ dq` is a
witness of non-triviality inside `D_A ⊓ G_K`. -/
theorem exists_unramMixDatum (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (dq : ℕ) (hdqmem : ∀ σ : Ω ≃ₐ[k] Ω, σ ^ dq ∈ K.fixingSubgroup)
    (hdq : Nat.Coprime dq p) :
    ∃ D : MixLocDatum p k Ω K A, ∃ δ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, D.f δ ≠ 0 := by
  classical
  obtain ⟨φ, haddφ, hzeroφ, hneφ, hconjφ, hlcφ⟩ :=
    Work.SSGRoute.Sha2Lib.localUnramChar p k Ω A hA
  have hφ1 : φ 1 = 0 := by
    have h := haddφ 1 1 (Subgroup.one_mem _) (Subgroup.one_mem _)
    rw [mul_one] at h
    exact add_right_cancel (by rw [zero_add]; exact h.symm)
  obtain ⟨σ₀, hσ₀D, hσ₀ne⟩ := hneφ
  have hpow_formula : ∀ n : ℕ, φ (σ₀ ^ n) = (n : ZMod p) * φ σ₀ := by
    intro n
    induction n with
    | zero => rw [pow_zero, hφ1, Nat.cast_zero, zero_mul]
    | succ k ih =>
        rw [pow_succ, haddφ (σ₀ ^ k) σ₀ (Subgroup.pow_mem _ hσ₀D k) hσ₀D, ih, Nat.cast_succ,
          add_mul, one_mul]
  have hdq_ne : (dq : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((dq : ℤ) : ZMod p) = 0 := by rw [Int.cast_natCast]; exact h0
    have hdvdZ : (p : ℤ) ∣ (dq : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (dq : ℤ) p).mp h0'
    have hdvd : p ∣ dq := Int.natCast_dvd_natCast.mp hdvdZ
    have h1 : p ∣ 1 := by
      have h2 : p ∣ Nat.gcd dq p := Nat.dvd_gcd hdvd (dvd_refl p)
      rwa [hdq.gcd_eq_one] at h2
    exact (Fact.out : p.Prime).not_dvd_one h1
  obtain ⟨U, hUopen, hU⟩ := hlcφ
  refine ⟨⟨φ, ?_, ⟨U, hUopen, ?_⟩, ?_, ?_⟩, σ₀ ^ dq,
    Subgroup.mem_inf.mpr ⟨Subgroup.pow_mem _ hσ₀D dq, hdqmem σ₀⟩, ?_⟩
  · intro g hg h hh
    exact haddφ g h (Subgroup.mem_inf.mp hg).1 (Subgroup.mem_inf.mp hh).1
  · intro x hx hxmem
    have h := hU 1 (Subgroup.one_mem _) x hx (Subgroup.mem_inf.mp hxmem).1
    rw [one_mul, hφ1] at h
    exact h
  · intro σ hσ δ hδ
    exact hconjφ δ σ (Subgroup.mem_inf.mp hδ).1 hσ
  · intro δ hδ hI
    exact hzeroφ δ ((Work.SSGRoute.mem_inertiaSub k Ω A δ).mpr hI)
  · change φ (σ₀ ^ dq) ≠ 0
    rw [hpow_formula dq]
    exact mul_ne_zero hdq_ne hσ₀ne

/-- **The Grünwald descent for the mixed split/inert datum.**

Given the cyclotomic level `K = k⟮ζ_p⟯`, a finite set `Ss` of primes of `k`, a prime `q ∉ Ss`,
place bookkeeping `d` for the set `insert q Ss` and a Grünwald engine over `K` (supplied by
`Work.HRec.grunwald_surjective_odd_over_same` for odd `p` and by
`Work.SSGRoute.grunwald_surjective_two` for `p = 2`), one prescribes the *zero* datum at the places
above the primes of `Ss` and the *unramified* Frobenius datum at the place above `q`, glues by the
engine, averages over `Gal(K/k)` and inflates to a global additive character `η : G_k → ZMod p`
which is locally constant, non-zero, kills the decomposition groups of all places over `Ss` (so
these primes split completely in the fixed field of `ker η`) and kills the inertia, but not the
decomposition group, of every place over `q` (so `q` is inert). -/
theorem exists_char_split_inert_aux
    (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Ss : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (hqS : q ∉ Ss)
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (hcop : Nat.Coprime (Nat.card (K ≃ₐ[k] K)) p)
    (d : PlaceData k Ω K (insert q Ss))
    (hengine : ∀ (f : (P : {P // P ∈ d.T}) →
        ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup) → ZMod p),
        (∀ (P : ↥d.T), ∀ a b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
          f P (a * b) = f P a + f P b) →
        (∀ (P : ↥d.T), ∃ U : Subgroup ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
          IsOpen (U : Set ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) ∧
          ∀ x ∈ U, f P x = 0) →
        ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
          (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
          SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
          (∀ (P : {P // P ∈ d.T})
            (δ : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)),
            z (δ : Ω ≃ₐ[k] Ω) = f P δ)) :
    ∃ η : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ a b : Ω ≃ₐ[k] Ω, η (a * b) = η a + η b) ∧
      (∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ ∀ x ∈ U, η x = 0) ∧
      (∃ x : Ω ≃ₐ[k] Ω, η x ≠ 0) ∧
      (∀ 𝔭 ∈ Ss, ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
        A.comap (algebraMap k Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 →
        ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A → η σ = 0) ∧
      (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
        A.comap (algebraMap k Ω) =
          IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k q →
        (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω A → η σ = 0) ∧
        (∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧ η σ ≠ 0)) := by
  classical
  haveI hAlgClosed : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have hpp : p.Prime := Fact.out
  have hqmem : q ∈ insert q Ss := Finset.mem_insert_self q Ss
  have hSsmem : ∀ 𝔭 ∈ Ss, 𝔭 ∈ insert q Ss := fun 𝔭 h𝔭 => Finset.mem_insert_of_mem h𝔭
  -- ## the index `dq` of `G_K` in `G_k`
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
  have hdq : Nat.Coprime dq p := by rw [hcard_eq]; exact hcop
  have hdq_ne : (dq : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((dq : ℤ) : ZMod p) = 0 := by rw [Int.cast_natCast]; exact h0
    have hdvdZ : (p : ℤ) ∣ (dq : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (dq : ℤ) p).mp h0'
    have hdvd : p ∣ dq := Int.natCast_dvd_natCast.mp hdvdZ
    have h1 : p ∣ 1 := by
      have h2 : p ∣ Nat.gcd dq p := Nat.dvd_gcd hdvd (dvd_refl p)
      rwa [hdq.gcd_eq_one] at h2
    exact hpp.not_dvd_one h1
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
  haveI hKnorm : (K.fixingSubgroup).Normal := inferInstance
  -- ## the mixed local datum
  have hUnramEx : ∀ v : {v // v ∈ insert q Ss}, ∃ D : MixLocDatum p k Ω K (d.base v),
      ∃ δ ∈ SSGRoute.decomp k (d.base v) ⊓ K.fixingSubgroup, D.f δ ≠ 0 :=
    fun v => exists_unramMixDatum p k Ω K (d.base v) (d.hTfin _ (d.hbase_mem v)) dq
      hpow_mem_ker hdq
  let unramDat : (v : {v // v ∈ insert q Ss}) → MixLocDatum p k Ω K (d.base v) :=
    fun v => Classical.choose (hUnramEx v)
  let dat : (v : {v // v ∈ insert q Ss}) → MixLocDatum p k Ω K (d.base v) :=
    fun v => if (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) = q
      then unramDat v else zeroLocDatum p k Ω K (d.base v)
  have hdat_q : dat ⟨q, hqmem⟩ = unramDat ⟨q, hqmem⟩ := by
    dsimp only [dat]
    exact if_pos rfl
  have hdat_s : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
      (h𝔭 : 𝔭 ∈ Ss), dat ⟨𝔭, hSsmem 𝔭 h𝔭⟩ =
        zeroLocDatum p k Ω K (d.base ⟨𝔭, hSsmem 𝔭 h𝔭⟩) := by
    intro 𝔭 h𝔭
    have hne : ((⟨𝔭, hSsmem 𝔭 h𝔭⟩ : {v // v ∈ insert q Ss}) :
        IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) ≠ q := by
      intro h
      exact hqS (h ▸ h𝔭)
    dsimp only [dat]
    exact if_neg hne
  -- ## the transported datum on `T`
  let fP : (P : {P // P ∈ d.T}) →
      ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup) → ZMod p :=
    fun P δ => (dat (d.vOf P)).f (d.u P * (δ : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹)
  have hfPadd : ∀ (P : {P // P ∈ d.T})
      (a b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)),
      fP P (a * b) = fP P a + fP P b := by
    intro P a b
    show (dat (d.vOf P)).f (d.u P *
        ((a * b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) :
          Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) =
      (dat (d.vOf P)).f (d.u P * (a : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) +
        (dat (d.vOf P)).f (d.u P * (b : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹)
    have hconj_eq : d.u P *
        ((a * b : ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) :
          Ω ≃ₐ[k] Ω) * (d.u P)⁻¹ =
        (d.u P * (a : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) *
          (d.u P * (b : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) := by
      rw [Subgroup.coe_mul]; group
    rw [hconj_eq]
    refine (dat (d.vOf P)).hadd _ ?_ _ ?_
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hu : d.u P • (P : ValuationSubring Ω) = d.base (d.vOf P) := d.hu P
        calc (d.u P * (a : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) • d.base (d.vOf P)
            = d.u P • ((a : Ω ≃ₐ[k] Ω) • ((d.u P)⁻¹ • d.base (d.vOf P))) := by
                rw [mul_smul, mul_smul]
          _ = d.u P • ((a : Ω ≃ₐ[k] Ω) • (P : ValuationSubring Ω)) := by
                rw [← hu, inv_smul_smul]
          _ = d.u P • (P : ValuationSubring Ω) := by
                congr 1
                exact MulAction.mem_stabilizer_iff.mp a.2.1
          _ = d.base (d.vOf P) := hu
      · exact hKnorm.conj_mem (a : Ω ≃ₐ[k] Ω) a.2.2 (d.u P)
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have hu : d.u P • (P : ValuationSubring Ω) = d.base (d.vOf P) := d.hu P
        calc (d.u P * (b : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) • d.base (d.vOf P)
            = d.u P • ((b : Ω ≃ₐ[k] Ω) • ((d.u P)⁻¹ • d.base (d.vOf P))) := by
                rw [mul_smul, mul_smul]
          _ = d.u P • ((b : Ω ≃ₐ[k] Ω) • (P : ValuationSubring Ω)) := by
                rw [← hu, inv_smul_smul]
          _ = d.u P • (P : ValuationSubring Ω) := by
                congr 1
                exact MulAction.mem_stabilizer_iff.mp b.2.1
          _ = d.base (d.vOf P) := hu
      · exact hKnorm.conj_mem (b : Ω ≃ₐ[k] Ω) b.2.2 (d.u P)
  have hfPcont : ∀ P : {P // P ∈ d.T},
      ∃ U : Subgroup ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup),
        IsOpen (U : Set ↥(SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup)) ∧
        ∀ x ∈ U, fP P x = 0 := by
    intro P
    obtain ⟨U, hUopen, hUz⟩ := (dat (d.vOf P)).hcont
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
          Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k (d.base (d.vOf P)) ⊓ K.fixingSubgroup := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have hu : d.u P • (P : ValuationSubring Ω) = d.base (d.vOf P) := d.hu P
          calc (d.u P * (x : Ω ≃ₐ[k] Ω) * (d.u P)⁻¹) • d.base (d.vOf P)
              = d.u P • ((x : Ω ≃ₐ[k] Ω) • ((d.u P)⁻¹ • d.base (d.vOf P))) := by
                  rw [mul_smul, mul_smul]
            _ = d.u P • ((x : Ω ≃ₐ[k] Ω) • (P : ValuationSubring Ω)) := by
                  rw [← hu, inv_smul_smul]
            _ = d.u P • (P : ValuationSubring Ω) := by
                  congr 1
                  exact MulAction.mem_stabilizer_iff.mp x.2.1
            _ = d.base (d.vOf P) := hu
        · exact hKnorm.conj_mem (x : Ω ≃ₐ[k] Ω) x.2.2 (d.u P)
      show (dat (d.vOf P)).f (cg ((x : ↥(SSGRoute.decomp k (P : ValuationSubring Ω)
        ⊓ K.fixingSubgroup)) : Ω ≃ₐ[k] Ω)) = 0
      exact hUz _ hxU hxmem
  obtain ⟨z, hzadd, hzloc, hzagree⟩ := hengine fP hfPadd hfPcont
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
  have hzNadd : ∀ a b : ↥(K.fixingSubgroup), zN (a * b) = zN a + zN b :=
    fun a b => hzadd a a.2 b b.2
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
  have hηinv : ∀ x : Ω ≃ₐ[k] Ω, η x⁻¹ = - η x := by
    intro x
    have h := hηadd x x⁻¹
    rw [mul_inv_cancel, hη1] at h
    exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h.symm)
  have hηconj : ∀ a b : Ω ≃ₐ[k] Ω, η (a * b * a⁻¹) = η b := by
    intro a b
    rw [hηadd (a * b) a⁻¹, hηadd a b, hηinv a]
    abel
  have hη_pow : ∀ (n : ℕ) (σ : Ω ≃ₐ[k] Ω), η (σ ^ n) = (n : ZMod p) * η σ := by
    intro n σ
    induction n with
    | zero => rw [pow_zero, hη1, Nat.cast_zero, zero_mul]
    | succ k ih => rw [pow_succ, hηadd, ih, Nat.cast_succ, add_mul, one_mul]
  -- ## the key computation
  have hkey : ∀ (v : {v // v ∈ insert q Ss}) (x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup)
      (δ : ↥(K.fixingSubgroup)),
      (δ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k (d.base v) →
      z ((sec x) * (δ : Ω ≃ₐ[k] Ω) * (sec x)⁻¹) = (dat v).f δ := by
    intro v x δ hδ
    have hBfin : SSGRoute.IsFinPlace k ((sec x) • (d.base v)) :=
      isFinPlace_smul (d.base v) (d.hTfin _ (d.hbase_mem v)) (sec x)
    have hBcomap : ((sec x) • (d.base v)).comap (algebraMap k Ω) =
        (d.base v).comap (algebraMap k Ω) :=
      SSGRoute.comap_algebraMap_smul (d.base v) (sec x)
    obtain ⟨P, hPT, ρ, hρK, hρP⟩ := d.hcover v ((sec x) • (d.base v)) hBfin hBcomap
    set γ : Ω ≃ₐ[k] Ω := ρ⁻¹ with hγdef
    have hγK : γ ∈ K.fixingSubgroup := K.fixingSubgroup.inv_mem hρK
    have hγs : (γ * sec x) • (d.base v) = (P : ValuationSubring Ω) := by
      rw [mul_smul, ← hρP, hγdef, smul_smul, inv_mul_cancel, one_smul]
    have hvOf : d.vOf ⟨P, hPT⟩ = v := by
      apply Subtype.ext
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := k)
      rw [← d.hbase_comap (d.vOf ⟨P, hPT⟩), ← d.hbase_comap v]
      have e1 : d.base (d.vOf ⟨P, hPT⟩) = d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω) :=
        (d.hu ⟨P, hPT⟩).symm
      have e2 : (d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω)).comap (algebraMap k Ω) =
          (P : ValuationSubring Ω).comap (algebraMap k Ω) :=
        SSGRoute.comap_algebraMap_smul (P : ValuationSubring Ω) (d.u ⟨P, hPT⟩)
      have e3 : (P : ValuationSubring Ω) = (γ * sec x) • (d.base v) := hγs.symm
      have e4 : ((γ * sec x) • (d.base v)).comap (algebraMap k Ω) =
          (d.base v).comap (algebraMap k Ω) :=
        SSGRoute.comap_algebraMap_smul (d.base v) (γ * sec x)
      rw [e1, e2, e3, e4]
    have hu : d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω) = d.base v := by
      rw [d.hu ⟨P, hPT⟩, hvOf]
    have hmem : (γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹ ∈
        SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · calc ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) • (P : ValuationSubring Ω)
            = (γ * sec x) • ((δ : Ω ≃ₐ[k] Ω) • ((γ * sec x)⁻¹ • (P : ValuationSubring Ω))) := by
                rw [mul_smul, mul_smul]
          _ = (γ * sec x) • ((δ : Ω ≃ₐ[k] Ω) • (d.base v)) := by
                rw [← hγs, inv_smul_smul]
          _ = (γ * sec x) • (d.base v) := by
                rw [show (δ : Ω ≃ₐ[k] Ω) • (d.base v) = (d.base v) from
                  MulAction.mem_stabilizer_iff.mp hδ]
          _ = (P : ValuationSubring Ω) := hγs
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
        (dat (d.vOf ⟨P, hPT⟩)).f ((d.u ⟨P, hPT⟩) *
          ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) :=
      hzagree ⟨P, hPT⟩ ⟨_, hmem⟩
    have hw : (d.u ⟨P, hPT⟩ * (γ * sec x)) • (d.base v) = d.base v := by
      rw [mul_smul, hγs, hu]
    have hw_eq : (d.u ⟨P, hPT⟩ * (γ * sec x)) * (δ : Ω ≃ₐ[k] Ω) *
        (d.u ⟨P, hPT⟩ * (γ * sec x))⁻¹ =
        (d.u ⟨P, hPT⟩) * ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) *
          (d.u ⟨P, hPT⟩)⁻¹ := by group
    have hfin : (dat v).f ((d.u ⟨P, hPT⟩) *
        ((γ * sec x) * (δ : Ω ≃ₐ[k] Ω) * (γ * sec x)⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) =
        (dat v).f δ := by
      rw [← hw_eq]
      exact (dat v).hinv (d.u ⟨P, hPT⟩ * (γ * sec x))
        (MulAction.mem_stabilizer_iff.mpr hw) δ (Subgroup.mem_inf.mpr ⟨hδ, δ.2⟩)
    rw [hzγ, hzag, hvOf]
    exact hfin
  have hzbar_const : ∀ (v : {v // v ∈ insert q Ss}) (δ : ↥(K.fixingSubgroup)),
      (δ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k (d.base v) → zbar δ = (dq : ZMod p) * (dat v).f δ := by
    intro v δ hδ
    have h1 : zbar δ = ∑ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
        zN (conjN K.fixingSubgroup (sec x) δ) := rfl
    rw [h1]
    have h2 : ∀ x : (Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup,
        zN (conjN K.fixingSubgroup (sec x) δ) = (dat v).f δ := by
      intro x
      show z (((conjN K.fixingSubgroup (sec x) δ : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω)) =
        (dat v).f δ
      have hcoe : ((conjN K.fixingSubgroup (sec x) δ : ↥(K.fixingSubgroup)) : Ω ≃ₐ[k] Ω) =
          sec x * δ * (sec x)⁻¹ := rfl
      rw [hcoe]
      exact hkey v x δ hδ
    rw [Finset.sum_congr rfl (fun x _ => h2 x), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hcard : Fintype.card ((Ω ≃ₐ[k] Ω) ⧸ K.fixingSubgroup) = dq :=
      Nat.card_eq_fintype_card.symm
    rw [hcard]
  -- ## `z` kills inertia at the places over `q`
  have hz_kill_inertia : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (hAcomap : A.comap (algebraMap k Ω) = (d.base ⟨q, hqmem⟩).comap (algebraMap k Ω))
      (τ : Ω ≃ₐ[k] Ω), τ ∈ K.fixingSubgroup → SSGRoute.IsInertia k A τ → z τ = 0 := by
    intro A hA hAcomap τ hτK hτI
    obtain ⟨P, hPT, ρ, hρK, hρP⟩ := d.hcover ⟨q, hqmem⟩ A hA hAcomap
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
    have hu : d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω) = d.base (d.vOf ⟨P, hPT⟩) := d.hu ⟨P, hPT⟩
    have htransport : d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹ ∈
        SSGRoute.decomp k (d.base (d.vOf ⟨P, hPT⟩)) ⊓ K.fixingSubgroup := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · calc (d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) • d.base (d.vOf ⟨P, hPT⟩)
            = d.u ⟨P, hPT⟩ • ((γ * τ * γ⁻¹) • ((d.u ⟨P, hPT⟩)⁻¹ • d.base (d.vOf ⟨P, hPT⟩))) := by
                rw [mul_smul, mul_smul]
          _ = d.u ⟨P, hPT⟩ • ((γ * τ * γ⁻¹) • (P : ValuationSubring Ω)) := by
                rw [← hu, inv_smul_smul]
          _ = d.u ⟨P, hPT⟩ • (P : ValuationSubring Ω) := by
                rw [MulAction.mem_stabilizer_iff.mp hconjI.1]
          _ = d.base (d.vOf ⟨P, hPT⟩) := hu
      · exact hKnorm.conj_mem (γ * τ * γ⁻¹) hconjK (d.u ⟨P, hPT⟩)
    have htransportI : SSGRoute.IsInertia k (d.base (d.vOf ⟨P, hPT⟩))
        (d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) := by
      have h := SSGRoute.isInertia_conj (P : ValuationSubring Ω) (d.u ⟨P, hPT⟩) (γ * τ * γ⁻¹)
      rw [hu] at h
      exact h.mpr hconjI
    have hmem : γ * τ * γ⁻¹ ∈
        SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ K.fixingSubgroup :=
      Subgroup.mem_inf.mpr ⟨hconjI.1, hconjK⟩
    have hzag : z (γ * τ * γ⁻¹) = (dat (d.vOf ⟨P, hPT⟩)).f
        (d.u ⟨P, hPT⟩ * (γ * τ * γ⁻¹) * (d.u ⟨P, hPT⟩)⁻¹) :=
      hzagree ⟨P, hPT⟩ ⟨_, hmem⟩
    rw [hzγ, hzag]
    exact (dat (d.vOf ⟨P, hPT⟩)).hinertia _ htransport htransportI
  -- ## `η` kills inertia at the places over `q`
  have hη_kills : ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
      (hAcomap : A.comap (algebraMap k Ω) = (d.base ⟨q, hqmem⟩).comap (algebraMap k Ω))
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
      have hxcomap : ((sec x) • A).comap (algebraMap k Ω) = (d.base ⟨q, hqmem⟩).comap (algebraMap k Ω) := by
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
  -- ## the split condition at the `Ss`-places
  have hbase_split : ∀ (v : {v // v ∈ insert q Ss}), v.val ∈ Ss →
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k (d.base v) → η σ = 0 := by
    intro v hv σ hσ
    have hvne : (v : IsDedekindDomain.HeightOneSpectrum _) ≠ q := by
      intro h; exact hqS (h ▸ hv)
    have hdatv : dat v = zeroLocDatum p k Ω K (d.base v) := by
      dsimp only [dat]
      exact if_neg hvne
    have hpow : σ ^ dq ∈ K.fixingSubgroup := hpow_mem_ker σ
    have hpowD : σ ^ dq ∈ SSGRoute.decomp k (d.base v) := Subgroup.pow_mem _ hσ dq
    have h1 : η (σ ^ dq) = zbar ⟨σ ^ dq, hpow⟩ := hηext ⟨σ ^ dq, hpow⟩
    have h2 : zbar ⟨σ ^ dq, hpow⟩ = (dq : ZMod p) * (dat v).f (σ ^ dq : Ω ≃ₐ[k] Ω) :=
      hzbar_const v ⟨σ ^ dq, hpow⟩ hpowD
    have h3 : (dat v).f (σ ^ dq : Ω ≃ₐ[k] Ω) = 0 := by rw [hdatv]; rfl
    have hmul : (dq : ZMod p) * η σ = 0 := by rw [← hη_pow dq σ, h1, h2, h3, mul_zero]
    exact (mul_eq_zero.mp hmul).resolve_left hdq_ne
  have hsplit : ∀ 𝔭 ∈ Ss, ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
      A.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 →
      ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A → η σ = 0 := by
    intro 𝔭 h𝔭 A hA hAcomap σ hσ
    let v : {v // v ∈ insert q Ss} := ⟨𝔭, hSsmem 𝔭 h𝔭⟩
    have hcomap : (d.base v).comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
      rw [d.hbase_comap v, hAcomap]
    obtain ⟨τ, hτ⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq
      (F := k) (E := Ω) (A := d.base v) (B := A) hcomap
    have hτinv : τ⁻¹ * σ * τ ∈ SSGRoute.decomp k (d.base v) := by
      rw [MulAction.mem_stabilizer_iff]
      have hσ' : σ • A = A := MulAction.mem_stabilizer_iff.mp hσ
      calc (τ⁻¹ * σ * τ) • (d.base v) = τ⁻¹ • (σ • (τ • (d.base v))) := by
            rw [mul_smul, mul_smul]
        _ = τ⁻¹ • (σ • A) := by rw [hτ]
        _ = τ⁻¹ • A := by rw [hσ']
        _ = d.base v := by rw [← hτ, inv_smul_smul]
    have h1 : η σ = η (τ⁻¹ * σ * τ) := (hηconj τ⁻¹ σ).symm
    rw [h1]
    exact hbase_split v h𝔭 (τ⁻¹ * σ * τ) hτinv
  -- ## non-triviality at `q`
  obtain ⟨δ₀, hδ₀mem, hδ₀ne⟩ := Classical.choose_spec (hUnramEx ⟨q, hqmem⟩)
  have hδ₀D : (δ₀ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k (d.base ⟨q, hqmem⟩) :=
    (Subgroup.mem_inf.mp hδ₀mem).1
  have hδ₀K : (δ₀ : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hδ₀mem).2
  have hzbar_ne : zbar ⟨δ₀, hδ₀K⟩ ≠ 0 := by
    rw [hzbar_const ⟨q, hqmem⟩ ⟨δ₀, hδ₀K⟩ hδ₀D, hdat_q]
    exact mul_ne_zero hdq_ne hδ₀ne
  have hηne : η (δ₀ : Ω ≃ₐ[k] Ω) ≠ 0 := by
    rw [hηext ⟨δ₀, hδ₀K⟩]
    exact hzbar_ne
  refine ⟨η, hηadd, hηcontU, ⟨(δ₀ : Ω ≃ₐ[k] Ω), hηne⟩, hsplit, ?_⟩
  intro A hA hAcomap
  refine ⟨?_, ?_⟩
  · intro σ hσ
    exact hη_kills A hA (hAcomap.trans (d.hbase_comap ⟨q, hqmem⟩).symm) σ
      ((Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ)
  · have hcomap : (d.base ⟨q, hqmem⟩).comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
      rw [d.hbase_comap ⟨q, hqmem⟩, hAcomap]
    obtain ⟨τ, hτ⟩ := Commons.RingTheory.Valuation.exists_smul_eq_of_comap_eq
      (F := k) (E := Ω) (A := d.base ⟨q, hqmem⟩) (B := A) hcomap
    refine ⟨τ * (δ₀ : Ω ≃ₐ[k] Ω) * τ⁻¹, ?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff]
      calc (τ * (δ₀ : Ω ≃ₐ[k] Ω) * τ⁻¹) • A
            = τ • ((δ₀ : Ω ≃ₐ[k] Ω) • (τ⁻¹ • A)) := by rw [mul_smul, mul_smul]
        _ = τ • ((δ₀ : Ω ≃ₐ[k] Ω) • d.base ⟨q, hqmem⟩) := by rw [← hτ, inv_smul_smul]
        _ = τ • d.base ⟨q, hqmem⟩ := by rw [MulAction.mem_stabilizer_iff.mp hδ₀D]
        _ = A := hτ
    · rw [hηconj τ (δ₀ : Ω ≃ₐ[k] Ω)]
      exact hηne

/-- The conclusion of the Grünwald descent: an additive locally constant character of `G_k` which
kills the decomposition groups of all places over `Ss` and kills the inertia, but not the
decomposition group, of every place over `q`. -/
def SplitInertChar (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (Ss : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (η : (Ω ≃ₐ[k] Ω) → ZMod p) : Prop :=
  (∀ a b : Ω ≃ₐ[k] Ω, η (a * b) = η a + η b) ∧
  (∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧ ∀ x ∈ U, η x = 0) ∧
  (∃ x : Ω ≃ₐ[k] Ω, η x ≠ 0) ∧
  (∀ 𝔭 ∈ Ss, ∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
    A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 →
    ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A → η σ = 0) ∧
  (∀ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A →
    A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k q →
    (∀ σ : Ω ≃ₐ[k] Ω, σ ∈ Work.SSGRoute.inertiaSub k Ω A → η σ = 0) ∧
    (∃ σ : Ω ≃ₐ[k] Ω, σ ∈ SSGRoute.decomp k A ∧ η σ ≠ 0))

/-- The Grünwald descent in the odd case `p ≠ 2`, over the cyclotomic level `k⟮ζ_p⟯` with the
engine `Work.HRec.grunwald_surjective_odd_over_same`. -/
theorem exists_char_split_inert_odd (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Ss : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (hqS : q ∉ Ss) :
    ∃ η : (Ω ≃ₐ[k] Ω) → ZMod p, SplitInertChar p k Ω Ss q η := by
  classical
  obtain ⟨ζ, hζ, hfdK, hnfK, hgalK, hcopK⟩ := cycloSetup p (Fact.out : p.Prime) k Ω
  let K : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hfdK' : FiniteDimensional k K := hfdK
  haveI hnfK' : NumberField ↥K := hnfK
  haveI hgalK' : IsGalois k K := hgalK
  have hcop : Nat.Coprime (Nat.card (K ≃ₐ[k] K)) p := hcopK
  let d : PlaceData k Ω K (insert q Ss) := placeData_aux k Ω K (insert q Ss)
  have hζK : ζ ∈ K := IntermediateField.subset_adjoin k ({ζ} : Set Ω) (Set.mem_singleton ζ)
  exact exists_char_split_inert_aux p k Ω Ss q hqS K hcop d (fun f hf hfcont =>
    Work.HRec.grunwald_surjective_odd_over_same p hp k Ω K ζ hζ hζK d.T d.hTfin d.hTinj
      f hf hfcont)

/-- The Grünwald descent in the case `p = 2`: here `k⟮ζ₂⟯ = k`, so the descent is trivial and the
engine is `Work.SSGRoute.grunwald_surjective_two`.  The place bookkeeping of `k` itself is used,
and the `PlaceData` hypothesis `hTinj` implies the `hTdisj` required by the engine because every
element of `G_k` fixes `⊥ = k` pointwise. -/
theorem exists_char_split_inert_two (p : ℕ) [Fact p.Prime] (hp2 : p = 2)
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (Ss : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) (hqS : q ∉ Ss) :
    ∃ η : (Ω ≃ₐ[k] Ω) → ZMod p, SplitInertChar p k Ω Ss q η := by
  subst hp2
  classical
  let K : IntermediateField k Ω := ⊥
  have hcardK : Nat.card (K ≃ₐ[k] K) = 1 := by
    haveI hss : Subsingleton
        (↥(⊥ : IntermediateField k Ω) ≃ₐ[k] ↥(⊥ : IntermediateField k Ω)) :=
      ⟨fun f g => AlgEquiv.ext (fun x => by
        obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp x.2
        have hx : x = algebraMap k ↥(⊥ : IntermediateField k Ω) y := Subtype.ext hy.symm
        rw [hx, AlgEquiv.commutes f y, AlgEquiv.commutes g y])⟩
    change Nat.card (↥(⊥ : IntermediateField k Ω) ≃ₐ[k] ↥(⊥ : IntermediateField k Ω)) = 1
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  have hcop : Nat.Coprime (Nat.card (K ≃ₐ[k] K)) 2 := by
    rw [hcardK]; exact Nat.coprime_one_left 2
  let d : PlaceData k Ω K (insert q Ss) := placeData_aux k Ω K (insert q Ss)
  have hGK : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup := by
    intro σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨y, hy⟩ := IntermediateField.mem_bot.mp hx
    rw [← hy, AlgEquiv.commutes]
  have hTdisj : ∀ P ∈ d.T, ∀ Q ∈ d.T, SSGRoute.IsConjPlace k P Q → P = Q := by
    intro P hP Q hQ hconj
    have hcomap : P.comap (algebraMap ↥K Ω) = Q.comap (algebraMap ↥K Ω) := by
      obtain ⟨σ, hσ⟩ := hconj
      have h1 : (σ • P).comap (algebraMap ↥K Ω) = P.comap (algebraMap ↥K Ω) :=
        comap_algebraMap_smul_fixingSubgroup K P σ (hGK σ)
      rw [hσ] at h1
      exact h1.symm
    exact Subtype.ext_iff.mp (d.hTinj ⟨P, hP⟩ ⟨Q, hQ⟩ hcomap)
  haveI hcharZero : CharZero Ω :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap k Ω))
  haveI hchar : CharP Ω 0 := CharP.ofCharZero Ω
  have hζ : IsPrimitiveRoot (-1 : Ω) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hζK : (-1 : Ω) ∈ K := by
    show (-1 : Ω) ∈ (⊥ : IntermediateField k Ω)
    exact IntermediateField.mem_bot.mpr ⟨-1, by simp⟩
  exact exists_char_split_inert_aux 2 k Ω Ss q hqS K hcop d (fun f hf hfcont =>
    grunwald_surjective_two 2 rfl k Ω K (-1) hζ hζK d.T d.hTfin hTdisj f hf hfcont)

/-- **The target statement inside an algebraic closure.** -/
theorem exists_level_split_inert_of_algClosure (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [NumberField F]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (hqS : q ∉ S) :
    ∃ (E : IntermediateField F (AlgebraicClosure F)) (_ : NumberField ↥E)
      (_ : FiniteDimensional F ↥E),
      IsGalois F ↥E ∧ Module.finrank F ↥E = p ∧
      (∀ 𝔭 ∈ S, ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver 𝔭.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) = 1) ∧
      (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver q.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) = p) := by
  classical
  obtain ⟨Aq, hAqcomap⟩ := Commons.RingTheory.Valuation.exists_valuationSubring_comap_eq
    (K := F) (L := AlgebraicClosure F)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F q)
  have hAqfin : SSGRoute.IsFinPlace F Aq := by
    rw [SSGRoute.IsFinPlace, hAqcomap]
    exact Commons.RingTheory.Valuation.valuationSubringAtPrime_ne_top q
  rcases eq_or_ne p 2 with h2 | h2
  · subst h2
    obtain ⟨η, hη⟩ := exists_char_split_inert_two 2 rfl F (AlgebraicClosure F) S q hqS
    exact split_inert_level_of_character 2 F (AlgebraicClosure F) S q η hη.1 hη.2.1 hη.2.2.1
      hη.2.2.2.1 Aq hAqfin hAqcomap (hη.2.2.2.2 Aq hAqfin hAqcomap).1
      (hη.2.2.2.2 Aq hAqfin hAqcomap).2
  · obtain ⟨η, hη⟩ := exists_char_split_inert_odd p h2 F (AlgebraicClosure F) S q hqS
    exact split_inert_level_of_character p F (AlgebraicClosure F) S q η hη.1 hη.2.1 hη.2.2.1
      hη.2.2.2.1 Aq hAqfin hAqcomap (hη.2.2.2.2 Aq hAqfin hAqcomap).1
      (hη.2.2.2.2 Aq hAqfin hAqcomap).2

theorem exists_cyclic_p_level_split_inert
    (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [IsAlgClosed Ω]

    [Algebra F Ω]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (hqS : q ∉ S)
    (hpq : ((p : NumberField.RingOfIntegers F) ∉ q.asIdeal)) :
    ∃ (E : IntermediateField F Ω), ∃ (_ : NumberField ↥E) (_ : FiniteDimensional F ↥E),
      IsGalois F ↥E ∧ Module.finrank F ↥E = p ∧
      (∀ 𝔭 ∈ S, ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver 𝔭.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) = 1) ∧
      (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥E),
        𝔮.asIdeal.LiesOver q.asIdeal →
        𝔮.asIdeal.ramificationIdx (NumberField.RingOfIntegers F) = 1 ∧
        𝔮.asIdeal.inertiaDeg (NumberField.RingOfIntegers F) = p) := by
  classical
  obtain ⟨E₀, hnf₀, hfd₀, hgal₀, hrank₀, hsplit₀, hinert₀⟩ :=
    exists_level_split_inert_of_algClosure p F S q hqS
  let ι : AlgebraicClosure F →ₐ[F] Ω := IsAlgClosed.lift
  let EE : IntermediateField F Ω := E₀.map ι
  let e : ↥E₀ ≃ₐ[F] ↥EE := IntermediateField.equivMap E₀ ι
  haveI hfdEE : FiniteDimensional F ↥EE := e.toLinearEquiv.finiteDimensional
  haveI hfdQEE : FiniteDimensional ℚ ↥EE := FiniteDimensional.trans ℚ F ↥EE
  haveI hnfEE : NumberField ↥EE := NumberField.mk
  haveI hgalEE : IsGalois F ↥EE := IsGalois.of_algEquiv e
  refine ⟨EE, hnfEE, hfdEE, hgalEE, ?_, ?_, ?_⟩
  · rw [← LinearEquiv.finrank_eq e.toLinearEquiv]
    exact hrank₀
  · intro 𝔭 h𝔭 𝔮 h𝔮
    let eO : 𝓞 ↥E₀ ≃ₐ[𝓞 F] 𝓞 ↥EE := NumberField.RingOfIntegers.mapAlgEquiv e
    let f : 𝓞 ↥E₀ →+* 𝓞 ↥EE := eO
    have hfs : Function.Surjective f := fun y => eO.surjective y
    let 𝔮₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥E₀) :=
      IsDedekindDomain.HeightOneSpectrum.comap f hfs 𝔮
    have hq₀ : 𝔮₀.asIdeal = Ideal.comap eO 𝔮.asIdeal := rfl
    have hlies₀ : 𝔮₀.asIdeal.LiesOver 𝔭.asIdeal :=
      Ideal.LiesOver.of_eq_comap 𝔭.asIdeal eO rfl
    obtain ⟨h1, h2⟩ := hsplit₀ 𝔭 h𝔭 𝔮₀ hlies₀
    haveI hqprime : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
    haveI hqmax : 𝔮.asIdeal.IsMaximal := 𝔮.isMaximal
    haveI hqLies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := h𝔮
    have hram : 𝔮₀.asIdeal.ramificationIdx (𝓞 F) = 𝔮.asIdeal.ramificationIdx (𝓞 F) := by
      rw [hq₀]
      exact ramificationIdx_comap_algEquiv ↥E₀ ↥EE eO 𝔭 𝔮.asIdeal
    have hiner : 𝔮₀.asIdeal.inertiaDeg (𝓞 F) = 𝔮.asIdeal.inertiaDeg (𝓞 F) := by
      rw [hq₀]
      exact inertiaDeg_comap_algEquiv ↥E₀ ↥EE eO 𝔭 𝔮.asIdeal
    exact ⟨hram ▸ h1, hiner ▸ h2⟩
  · intro 𝔮 h𝔮
    let eO : 𝓞 ↥E₀ ≃ₐ[𝓞 F] 𝓞 ↥EE := NumberField.RingOfIntegers.mapAlgEquiv e
    let f : 𝓞 ↥E₀ →+* 𝓞 ↥EE := eO
    have hfs : Function.Surjective f := fun y => eO.surjective y
    let 𝔮₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥E₀) :=
      IsDedekindDomain.HeightOneSpectrum.comap f hfs 𝔮
    have hq₀ : 𝔮₀.asIdeal = Ideal.comap eO 𝔮.asIdeal := rfl
    have hlies₀ : 𝔮₀.asIdeal.LiesOver q.asIdeal :=
      Ideal.LiesOver.of_eq_comap q.asIdeal eO rfl
    obtain ⟨h1, h2⟩ := hinert₀ 𝔮₀ hlies₀
    haveI hqprime : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
    haveI hqmax : 𝔮.asIdeal.IsMaximal := 𝔮.isMaximal
    haveI hqLies : 𝔮.asIdeal.LiesOver q.asIdeal := h𝔮
    have hram : 𝔮₀.asIdeal.ramificationIdx (𝓞 F) = 𝔮.asIdeal.ramificationIdx (𝓞 F) := by
      rw [hq₀]
      exact ramificationIdx_comap_algEquiv ↥E₀ ↥EE eO q 𝔮.asIdeal
    have hiner : 𝔮₀.asIdeal.inertiaDeg (𝓞 F) = 𝔮.asIdeal.inertiaDeg (𝓞 F) := by
      rw [hq₀]
      exact inertiaDeg_comap_algEquiv ↥E₀ ↥EE eO q 𝔮.asIdeal
    exact ⟨hram ▸ h1, hiner ▸ h2⟩

end

end Work.SSGRoute.Sha2Lib
