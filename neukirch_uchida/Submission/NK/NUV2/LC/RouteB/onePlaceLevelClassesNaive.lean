import Mathlib
import Submission.NK.NUV2.LC.RouteB.hasseSurjTopDefs
import Submission.NK.NUV2.LC.h2ProfiniteAddGroup
import Submission.NK.UchidaKummer.Embedding.isKummerEmbeddingProblem
import Submission.NeukirchUchida.PrimeCorrespondence
import Submission.NK.NUV2.LC.RouteB.kummerCharacter

/-!
# Level-wise one-place classes (the "naive" form)

For `p` an odd prime, a number field `F` containing a primitive `p`-th root of unity `ζ`, a
separable closure `F'` and a finite family `A i` of pairwise non-conjugate places of `F'` over
finite primes of `F`, this file constructs a *single* finite Galois level `K/F` together with
classes `x i ∈ H²(Gal(K/F), Z/p)` whose **level-wise** localisation at `A i` is non-zero and whose
level-wise localisation at `A j` vanishes for `j ≠ i`.

The construction is the Kummer-theoretic one:

* the places `A i` lie over pairwise **distinct** primes `𝔭 i` of `F` (places over one prime are
  conjugate, `Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'`);
* Kummer data (`NK.UchidaKummer.Embedding.exists_localPowClass_family`): units `b P` whose local
  `p`-th power class is non-trivial at `P` and trivial at every other prime of the chosen finite set
  `T = {𝔭 i}`;
* `K = kummerSup p T b` is the compositum of the cyclic degree-`p` extensions `E i = F(b_{𝔭 i}^{1/p})`;
* the Kummer character `χ i : Gal(F'/F) →* Multiplicative (ZMod p)` of the root of `X^p - b_{𝔭 i}`
  has kernel `Gal(F'/E i)` (`NK.NUV2.LC.RouteB.kummerCharacter`); it descends to the level group of
  `K`, and its pullback along the localisation at `A j` is
  * trivial for `j ≠ i` (because `𝔭 i` splits completely in `E j`), and
  * an isomorphism for `j = i` (the local degrees of `K/F` and `E i/F` at `𝔭 i` agree).

So the level classes are `x i = H2.map (Φ i) (gen)`, where `gen ≠ 0` generates
`H²(Multiplicative (ZMod p), Z/p) ≅ Z/p`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace NK.NUV2.LC.RouteB

open NK.BrauerHasse

noncomputable section

universe u

/-! ## Group cohomology: the pullback along a trivial homomorphism vanishes -/

/-- Computation rule for the functoriality of `H²(·, Z/p)`: the pullback along a composite is the
composite of the pullbacks. -/
lemma H2_map_comp_apply {p : ℕ} {G₁ G₂ G₃ : Type} [Group G₁] [Group G₂] [Group G₃]
    (f : G₂ →* G₃) (g : G₁ →* G₂) (x : H2 p G₃) :
    (H2.map (f.comp g)).hom x = (H2.map g).hom ((H2.map f).hom x) := by
  have h := congrArg (fun (φ : H2 p G₃ ⟶ H2 p G₁) => φ.hom x)
    (H2.map_comp (p := p) (f := f) (g := g))
  rw [h]
  rfl

/-- The pullback along the identity is the identity. -/
lemma H2_map_id_apply {p : ℕ} {G : Type} [Group G] (x : H2 p G) :
    (H2.map (MonoidHom.id G)).hom x = x := by
  have h := congrArg (fun (φ : H2 p G ⟶ H2 p G) => φ.hom x)
    (H2.map_id (p := p) (G := G))
  rw [h]
  rfl

/-- **The pullback along the trivial homomorphism is the zero map.**  The trivial homomorphism
factors through the trivial group, whose `H²` vanishes. -/
lemma H2_map_one_apply {p : ℕ} {A C : Type} [Group A] [Group C] (x : H2 p C) :
    (H2.map (1 : A →* C)).hom x = 0 := by
  have hcomp : (1 : A →* C) = (1 : PUnit →* C).comp (1 : A →* PUnit) := by
    ext y; simp
  rw [hcomp, H2_map_comp_apply]
  haveI : Subsingleton (H2 p PUnit) := NK.Indecomposed.subsingleton_H2_of_subsingleton
  rw [Subsingleton.elim ((H2.map (1 : PUnit →* C)).hom x) 0]
  exact map_zero _

/-- For a group isomorphism `e : A ≃* C`, the pullback `H²(C, Z/p) → H²(A, Z/p)` is a bijection, in
particular it does not kill non-zero classes. -/
lemma H2_map_mulEquiv_ne_zero {p : ℕ} {A C : Type} [Group A] [Group C] (e : A ≃* C)
    {x : H2 p C} (hx : x ≠ 0) : (H2.map (e : A →* C)).hom x ≠ 0 := by
  intro h0
  apply hx
  have hcomp : (e : A →* C).comp (e.symm : C →* A) = MonoidHom.id C := by
    ext y; simp
  have h := H2_map_comp_apply (p := p) (f := (e : A →* C)) (g := (e.symm : C →* A)) x
  rw [hcomp, H2_map_id_apply] at h
  rw [h0] at h
  simpa using h

/-- A surjective group homomorphism `Ψ : A →* C` induces an injective map `H²(C, Z/p) → H²(A, Z/p)`:
composing with a section of `Ψ` on cohomology inverts the pullback.  Hence the pullback along a
bijective homomorphism does not kill non-zero classes. -/
lemma H2_map_ne_zero_of_bijective {p : ℕ} {A C : Type} [Group A] [Group C] (Ψ : A →* C)
    (hbij : Function.Bijective Ψ) {x : H2 p C} (hx : x ≠ 0) :
    (H2.map Ψ).hom x ≠ 0 := by
  intro h0
  have he : ((MulEquiv.ofBijective Ψ hbij : A ≃* C) : A →* C) = Ψ := MonoidHom.ext fun _ => rfl
  exact H2_map_mulEquiv_ne_zero (MulEquiv.ofBijective Ψ hbij) hx (by rw [he]; exact h0)

/-! ## The fixing subgroup of a finite supremum of intermediate fields -/

/-- The fixing subgroup of a finite supremum of intermediate fields is the intersection of the
fixing subgroups. -/
lemma fixingSubgroup_finset_sup {k K' : Type} [Field k] [Field K'] [Algebra k K'] {β : Type}
    [DecidableEq β] (s : Finset β) (f : β → IntermediateField k K') :
    (s.sup f).fixingSubgroup = s.inf (fun b => (f b).fixingSubgroup) := by
  induction s using Finset.induction with
  | empty => simp [Finset.sup_empty, Finset.inf_empty, IntermediateField.fixingSubgroup_bot]
  | insert a s ha ih =>
      rw [Finset.sup_insert, Finset.inf_insert, IntermediateField.fixingSubgroup_sup, ih]

/-! ## A group of prime order is generated by each of its non-identity elements -/

lemma zpowers_eq_top_of_natCard_prime {C : Type} [Group C] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card C = p) {c : C} (hc : c ≠ 1) : Subgroup.zpowers c = ⊤ := by
  have hdvd : orderOf c ∣ Nat.card C := orderOf_dvd_natCard c
  have hne : orderOf c ≠ 1 := fun h => hc (orderOf_eq_one_iff.mp h)
  have hord : orderOf c = p := by
    rcases hp.eq_one_or_self_of_dvd (orderOf c) (hcard ▸ hdvd) with h | h
    · exact absurd h hne
    · exact h
  have hcardz : Nat.card ↥(Subgroup.zpowers c) = Nat.card ↥(⊤ : Subgroup C) := by
    rw [Nat.card_zpowers, hord, Subgroup.card_top, hcard]
  exact NK.LocalAnabelian.Kummer.eq_of_le_of_natCard_eq_of_ne_zero
    (by rw [Subgroup.card_top, hcard]; exact hp.ne_zero) le_top hcardz

/-! ## The kernel of the Kummer character -/

/-- **The stabiliser of a `p`-th root of `a`.**  For `α ^ p = a` and a `p`-th root of unity
`ζ ∈ k`, the Kummer field `k(α)` is the splitting field of `X ^ p - a`, so an automorphism fixes it
pointwise exactly when it fixes `α`. -/
lemma mem_fixingSubgroup_kummerField_iff {k K' : Type} [Field k] [Field K'] [Algebra k K']
    (p : ℕ) (hp : p.Prime) {ζ : k} (hζ : IsPrimitiveRoot ζ p) (a : kˣ) {α : K'}
    (hα : α ^ p = algebraMap k K' (a : k)) (σ : Gal(K'/k)) :
    σ ∈ (NK.LocalAnabelian.kummerField (K' := K') p a).fixingSubgroup ↔ σ α = α := by
  rw [NK.UchidaKummer.Kummer.kummerField_eq_adjoin_simple p hp hζ a hα]
  constructor
  · intro h
    exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp h α
      (IntermediateField.mem_adjoin_simple_self k α)
  · intro h
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact h
    | algebraMap y => exact σ.commutes y
    | add y z hy hz ihy ihz => rw [map_add, ihy, ihz]
    | mul y z hy hz ihy ihz => rw [map_mul, ihy, ihz]
    | inv y hy ihy => rw [map_inv₀, ihy]

/-! ## The cyclic group `Multiplicative (ZMod p)` of prime order `p` -/

lemma natCard_multiplicative_zmod (p : ℕ) [NeZero p] :
    Nat.card (Multiplicative (ZMod p)) = p := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

lemma mem_zpowers_ofAdd_one (p : ℕ) [NeZero p] (x : Multiplicative (ZMod p)) :
    x ∈ Subgroup.zpowers (Multiplicative.ofAdd 1) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨((Multiplicative.toAdd x).val : ℤ), ?_⟩
  rw [zpow_natCast]
  have h : (Multiplicative.ofAdd (1 : ZMod p)) ^ ((Multiplicative.toAdd x).val)
      = Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℕ) : ZMod p) := by
    induction (Multiplicative.toAdd x).val with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, ← ofAdd_add]; simp
  rw [h, ZMod.natCast_zmod_val]
  rfl

/-! ## The arithmetic input: local degrees in a Kummer field -/

section LocalDeg

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [Algebra F F'] [IsSepClosure F F']

/-- **The primes at which the radical is a local `p`-th power split completely.**  If `b Q` is a
local `p`-th power at the prime `P` (which is what `localPowClass F p P (b Q) = 1` says), then every
prime of the Kummer field `F(b Q^{1/p})` above `P` has local degree `1`.  This is the "easy"
direction of the Kummer local dichotomy in the single-field form
`NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff`. -/
lemma localDeg_eq_one_of_kummerData (p : ℕ) (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    (b : NK.Chebotarev.PrimeIdeal F → Fˣ)
    {P Q : NK.Chebotarev.PrimeIdeal F} (h : NK.UchidaKummer.localPowClass F p P (b Q) = 1)
    [FiniteDimensional F ↥(NK.LocalAnabelian.kummerField (K' := F') p (b Q))]
    [NumberField ↥(NK.LocalAnabelian.kummerField (K' := F') p (b Q))] :
    ∀ R : NK.Chebotarev.PrimeIdeal ↥(NK.LocalAnabelian.kummerField (K' := F') p (b Q)),
      R.asIdeal.LiesOver P.asIdeal → NK.UchidaKummer.localDeg R P = 1 := by
  intro R hR
  have h2 : ∃ c : (P.adicCompletion F)ˣ,
      algebraMap F (P.adicCompletion F) (b Q : F) = (c : P.adicCompletion F) ^ p :=
    NK.UchidaKummer.Embedding.exists_pow_eq_of_localPowClass_eq_one p P (b Q) h
  exact (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff p hp hζ (b Q)
    (NK.LocalAnabelian.kummerField (K' := F') p (b Q)) rfl P).mpr h2 R hR

end LocalDeg


/-! ## The level-wise one-place classes -/


theorem onePlaceLevelClassesNaive (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2)
    {F F' : Type} [Field F] [NumberField F] [Field F'] [Algebra F F'] [IsSepClosure F F']
    (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (ι : Type) [Fintype ι]
    (A : ι → NK.BrauerHasse.OverFinitePrime F F')
    (hnot : ∀ i j : ι, i ≠ j →
      ¬ NK.NUV2.LC.RouteB.InOrbit (K := F) (K' := F') ⊤ (A i).1 (A j).1) :
    ∃ K : FiniteGaloisIntermediateField F F',
      ∃ x : ι → NK.BrauerHasse.LevelH2 (K := F) (K' := F') p ⊤ K,
        (∀ i : ι, NK.BrauerHasse.locLevel p ⊤ (A i).1 K (x i) ≠ 0) ∧
        (∀ i j : ι, i ≠ j → NK.BrauerHasse.locLevel p ⊤ (A j).1 K (x i) = 0) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- ## The primes below the places, and their pairwise distinctness
  have hA : ∀ i, (A i).1.comap (algebraMap F F') ≠ ⊤ := fun i => (A i).2
  let 𝔭 : ι → NK.Chebotarev.PrimeIdeal F :=
    fun i => Submission.NeukirchUchida.primeOf (A i).1 (hA i)
  have h𝔭 : ∀ i, (A i).1.comap (algebraMap F F') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F (𝔭 i) :=
    fun i => Submission.NeukirchUchida.primeOf_spec (A i).1 (hA i)
  have hinj : Function.Injective 𝔭 := by
    intro i j hij
    by_contra hne
    apply hnot i j hne
    have hcomap : (A i).1.comap (algebraMap F F') = (A j).1.comap (algebraMap F F') := by
      rw [h𝔭 i, h𝔭 j, hij]
    obtain ⟨σ, hσ⟩ := Submission.NeukirchUchida.exists_smul_eq_of_comap_eq'
      (A := (A i).1) (B := (A j).1) (hA i) hcomap
    exact ⟨σ, Subgroup.mem_top σ, hσ⟩
  -- ## Kummer data
  let T : Finset (NK.Chebotarev.PrimeIdeal F) := Finset.univ.image 𝔭
  have hTmem : ∀ i, 𝔭 i ∈ T := fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  obtain ⟨b, hb1, hb2⟩ :=
    NK.UchidaKummer.Embedding.exists_localPowClass_family (L := F) p hp T ∅ (by simp)
  have hKnot : ∀ P ∈ T, ¬ ∃ c : (P.adicCompletion F)ˣ,
      algebraMap F (P.adicCompletion F) (b P : F) = (c : P.adicCompletion F) ^ p := by
    intro P hP h
    exact hb1 P hP (NK.UchidaKummer.Embedding.localPowClass_eq_one_of_exists_pow_eq p P (b P) h)
  have hKtriv : ∀ P ∈ T, ∀ Q ∈ T, Q ≠ P → ∃ c : (Q.adicCompletion F)ˣ,
      algebraMap F (Q.adicCompletion F) (b P : F) = (c : Q.adicCompletion F) ^ p := by
    intro P hP Q hQ hne
    exact NK.UchidaKummer.Embedding.exists_pow_eq_of_localPowClass_eq_one p Q (b P)
      (hb2 P hP Q (Finset.mem_union_right ∅ hQ) hne)
  have hnotloc : ∀ i, ¬ ∃ c : ((𝔭 i).adicCompletion F)ˣ,
      algebraMap F ((𝔭 i).adicCompletion F) (b (𝔭 i) : F) = (c : _) ^ p :=
    fun i => hKnot (𝔭 i) (hTmem i)
  -- ## The Kummer level
  let K₀ : IntermediateField F F' := NK.UchidaKummer.Embedding.kummerSup (K' := F') p T b
  have hKsup : K₀ = ⨆ P : ↥T, NK.LocalAnabelian.kummerField (K' := F') p (b P.1) := by
    change T.sup (fun P => NK.LocalAnabelian.kummerField (K' := F') p (b P))
      = ⨆ P : ↥T, NK.LocalAnabelian.kummerField (K' := F') p (b P.1)
    rw [Finset.sup_eq_iSup]
    exact le_antisymm
      (iSup_le fun i => iSup_le fun h => le_iSup_of_le ⟨i, h⟩ le_rfl)
      (iSup_le fun P => le_iSup_of_le P.1 (le_iSup_of_le P.2 le_rfl))
  have hnotpow : ∀ P ∈ T, b P ∉ NK.LocalAnabelian.powSubgroup p F := by
    intro P hP hmem
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hmem
    rw [powMonoidHom_apply] at hc
    refine hKnot P hP ⟨Units.map (algebraMap F (P.adicCompletion F)).toMonoidHom c, ?_⟩
    have h2 : ((c ^ p : Fˣ) : F) = (b P : F) := congrArg (fun u : Fˣ => (u : F)) hc
    rw [Units.val_pow_eq_pow_val] at h2
    show algebraMap F (P.adicCompletion F) (b P : F)
      = (algebraMap F (P.adicCompletion F) (c : F)) ^ p
    rw [← h2, map_pow]
  have hKdeg : Module.finrank F ↥K₀ = p ^ T.card :=
    NK.UchidaKummer.Embedding.finrank_kummerSup (K' := F') p hp hζ T b hKnot hKtriv
  haveI hKfd : FiniteDimensional F ↥K₀ :=
    FiniteDimensional.of_finrank_pos (by rw [hKdeg]; exact pow_pos hp.pos _)
  haveI hKnf : NumberField ↥K₀ :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField K₀
  haveI hKnormal : Normal F ↥K₀ := by
    haveI : ∀ P : ↥T, Normal F ↥(NK.LocalAnabelian.kummerField (K' := F') p (b P.1)) := by
      intro P
      exact (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := F) (K' := F') p hp hζ
        (b P.1) (hnotpow P.1 P.2)).1.to_normal
    rw [hKsup]
    exact IntermediateField.normal_iSup F F' _
  haveI hKgal : IsGalois F ↥K₀ := IsGalois.mk
  let KK : FiniteGaloisIntermediateField F F' :=
    { toIntermediateField := K₀, finiteDimensional := hKfd, isGalois := hKgal }
  -- ## The individual Kummer fields
  let E : ι → IntermediateField F F' := fun i => NK.LocalAnabelian.kummerField (K' := F') p (b (𝔭 i))
  have hEgal : ∀ i, IsGalois F ↥(E i) := fun i =>
    (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := F) (K' := F') p hp hζ
      (b (𝔭 i)) (hnotpow (𝔭 i) (hTmem i))).1
  have hEdeg : ∀ i, Module.finrank F ↥(E i) = p := fun i =>
    (NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (k := F) (K' := F') p hp hζ
      (b (𝔭 i)) (hnotpow (𝔭 i) (hTmem i))).2
  haveI : ∀ i, IsGalois F ↥(E i) := hEgal
  haveI : ∀ i, FiniteDimensional F ↥(E i) := fun i =>
    FiniteDimensional.of_finrank_pos (by rw [hEdeg i]; exact hp.pos)
  haveI : ∀ i, NumberField ↥(E i) := fun i =>
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (E i)
  have hEle : ∀ i, E i ≤ K₀ := fun i => by
    rw [hKsup]
    exact le_iSup_of_le ⟨𝔭 i, hTmem i⟩ le_rfl
  -- ## The Kummer characters
  have hchar : ∀ i, ∃ χ : Gal(F'/F) →* Multiplicative (ZMod p),
      ∀ σ : Gal(F'/F), χ σ = 1 ↔ σ ∈ (E i).fixingSubgroup := by
    intro i
    obtain ⟨α, hα⟩ := NK.UchidaKummer.Kummer.exists_pow_eq_algebraMap_of_isSepClosure
      (k := F) (K' := F') p hp hζ (b (𝔭 i))
    obtain ⟨χ, hχ⟩ := kummerCharacter p hp hζ (b (𝔭 i)) hα
    exact ⟨χ, fun σ => (hχ σ).trans
      (mem_fixingSubgroup_kummerField_iff p hp hζ (b (𝔭 i)) hα σ).symm⟩
  choose χ hχ using hchar
  have hdescent : ∀ i, (KK.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(F'/F))) ≤
      ((χ i).comp (Subgroup.topEquiv (G := Gal(F'/F))).toMonoidHom).ker := by
    intro i x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    refine (hχ i _).mpr ?_
    exact IntermediateField.fixingSubgroup_le (hEle i) (Subgroup.mem_subgroupOf.mp hx)
  let Φ : ι → LevelGroup (⊤ : Subgroup Gal(F'/F)) KK →* Multiplicative (ZMod p) :=
    fun i => QuotientGroup.lift (KK.fixingSubgroup.subgroupOf (⊤ : Subgroup Gal(F'/F)))
      ((χ i).comp (Subgroup.topEquiv (G := Gal(F'/F))).toMonoidHom) (hdescent i)
  -- ## A non-zero class of `H²(Multiplicative (ZMod p), Z/p)`
  obtain ⟨gen, hgen⟩ : ∃ g : H2 p (Multiplicative (ZMod p)), g ≠ 0 :=
    NK.LocalCFT.Brauer.exists_ne_zero_H2_of_finite_cyclic (p := p) (G := Multiplicative (ZMod p))
      (Multiplicative.ofAdd 1) (mem_zpowers_ofAdd_one p) (natCard_multiplicative_zmod p)
  -- ## The arithmetic inputs
  -- (1) the primes of `E l` over `𝔭 k` (`k ≠ l`) have local degree one
  have hsplit : ∀ k l : ι, k ≠ l → ∀ R : NK.Chebotarev.PrimeIdeal ↥(E l),
      R.asIdeal.LiesOver (𝔭 k).asIdeal → NK.UchidaKummer.localDeg R (𝔭 k) = 1 := by
    intro k l hkl R hR
    exact localDeg_eq_one_of_kummerData p hp hζ b
      (hb2 (𝔭 l) (hTmem l) (𝔭 k) (Finset.mem_union_right ∅ (hTmem k)) (hinj.ne hkl)) R hR
  have hG1 : ∀ k l : ι, k ≠ l → stabSubgroup (A k).1 ≤ (E l).fixingSubgroup := by
    intro k l hkl
    refine (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := F) (K' := F')
      (N := E l) (𝔭 k) (A k).1 (h𝔭 k)).mpr ?_
    exact (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one (K := F)
      (L := ↥(E l)) (𝔭 k)).mpr (hsplit k l hkl)
  -- (2) the own prime does not split completely
  have hG2 : ∀ i, ¬ (stabSubgroup (A i).1 ≤ (E i).fixingSubgroup) := by
    intro i hle
    have hsp := (NK.Reconstruct.stabilizer_le_fixingSubgroup_iff_splitCompletely (K := F) (K' := F')
      (N := E i) (𝔭 i) (A i).1 (h𝔭 i)).mp hle
    have hall := (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one (K := F)
      (L := ↥(E i)) (𝔭 i)).mp hsp
    have hloc := (NK.UchidaKummer.Kummer.localDeg_kummerField_eq_one_iff p hp hζ (b (𝔭 i))
      (E i) rfl (𝔭 i)).mp hall
    exact hnotloc i hloc
  -- (3) an automorphism of the decomposition group fixing `E i` fixes the whole level
  have hfixK : ∀ i (σ : Gal(F'/F)), σ ∈ stabSubgroup (A i).1 → σ ∈ (E i).fixingSubgroup →
      σ ∈ KK.fixingSubgroup := by
    intro i σ hσD hσE
    have key : ∀ s : Finset (NK.Chebotarev.PrimeIdeal F),
        (∀ P ∈ s, σ ∈ (NK.LocalAnabelian.kummerField (K' := F') p (b P)).fixingSubgroup) →
        σ ∈ (s.sup (fun P => NK.LocalAnabelian.kummerField (K' := F') p (b P))).fixingSubgroup := by
      intro s
      induction s using Finset.induction with
      | empty => intro _; simp [Finset.sup_empty, IntermediateField.fixingSubgroup_bot]
      | insert a s ha ih =>
          intro h
          rw [Finset.sup_insert, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
          exact ⟨h a (Finset.mem_insert_self a s),
            ih (fun P hP => h P (Finset.mem_insert_of_mem hP))⟩
    have hmem : ∀ P ∈ T, σ ∈ (NK.LocalAnabelian.kummerField (K' := F') p (b P)).fixingSubgroup := by
      intro P hP
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hP
      by_cases hk : k = i
      · subst hk; exact hσE
      · exact hG1 i k (fun h => hk h.symm) hσD
    exact key T hmem
  -- ## The non-vanishing at the own place
  have hex : ∀ i, ∃ σ : Gal(F'/F), σ ∈ stabSubgroup (A i).1 ∧ χ i σ ≠ 1 := by
    intro i
    by_contra h
    simp only [not_exists, not_and] at h
    exact hG2 i (fun σ hσ => (hχ i σ).mp (not_not.mp (h σ hσ)))
  refine ⟨KK, fun i => (H2.map (Φ i)).hom gen, ?_, ?_⟩
  · intro i
    obtain ⟨σ, hσD, hσne⟩ := hex i
    have htop : Subgroup.zpowers (χ i σ) = ⊤ :=
      zpowers_eq_top_of_natCard_prime hp (natCard_multiplicative_zmod p) hσne
    have hmemD : ∀ n : ℤ, σ ^ n ∈ (⊤ ⊓ stabSubgroup (A i).1) := fun n =>
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_top _, Subgroup.zpow_mem (stabSubgroup (A i).1) hσD n⟩
    let Ψ : LocalLevelGroup (⊤ : Subgroup Gal(F'/F)) (A i).1 KK →* Multiplicative (ZMod p) :=
      (Φ i).comp (localInclHom ⊤ (A i).1 KK)
    have hcomp : Ψ = (Φ i).comp (localInclHom ⊤ (A i).1 KK) := rfl
    have hsurj : Function.Surjective Ψ := by
      intro c
      have hc : c ∈ Subgroup.zpowers (χ i σ) := by rw [htop]; exact Subgroup.mem_top c
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      refine ⟨QuotientGroup.mk' _ ⟨σ ^ k, hmemD k⟩, ?_⟩
      show (χ i) ((Subgroup.topEquiv (Subgroup.inclusion (inf_le_left :
          (⊤ : Subgroup Gal(F'/F)) ⊓ stabSubgroup (A i).1 ≤ ⊤)
          (⟨σ ^ k, hmemD k⟩)) : Gal(F'/F))) = c
      rw [show ((Subgroup.topEquiv (Subgroup.inclusion (inf_le_left :
          (⊤ : Subgroup Gal(F'/F)) ⊓ stabSubgroup (A i).1 ≤ ⊤)
          (⟨σ ^ k, hmemD k⟩)) : Gal(F'/F))) = σ ^ k from rfl]
      rw [map_zpow, hk]
    have hinj : Function.Injective Ψ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective
        (KK.fixingSubgroup.subgroupOf (⊤ ⊓ stabSubgroup (A i).1)) y
      rw [← hy₀] at hy ⊢
      have hy' : (χ i) ((Subgroup.topEquiv (Subgroup.inclusion (inf_le_left :
          (⊤ : Subgroup Gal(F'/F)) ⊓ stabSubgroup (A i).1 ≤ ⊤) y₀))) = 1 := hy
      have hyE : (y₀ : Gal(F'/F)) ∈ (E i).fixingSubgroup := (hχ i _).mp hy'
      have hyK : (y₀ : Gal(F'/F)) ∈ KK.fixingSubgroup := hfixK i _ y₀.2.2 hyE
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff y₀).mpr (Subgroup.mem_subgroupOf.mpr hyK)
    intro h0
    exact H2_map_ne_zero_of_bijective Ψ ⟨hinj, hsurj⟩ hgen (by
      rw [hcomp, H2_map_comp_apply]
      exact h0)
  · intro i j hij
    have htriv : (Φ i).comp (localInclHom ⊤ (A j).1 KK) = 1 :=
      MonoidHom.ext fun y => by
        obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective
          (KK.fixingSubgroup.subgroupOf (⊤ ⊓ stabSubgroup (A j).1)) y
        rw [← hy₀]
        show (χ i) ((Subgroup.topEquiv (Subgroup.inclusion (inf_le_left :
            (⊤ : Subgroup Gal(F'/F)) ⊓ stabSubgroup (A j).1 ≤ ⊤) y₀)) : Gal(F'/F)) = 1
        exact (hχ i _).mpr (hG1 j i (Ne.symm hij) y₀.2.2)
    have h0 : (H2.map ((Φ i).comp (localInclHom ⊤ (A j).1 KK))).hom gen = 0 := by
      rw [htriv, H2_map_one_apply]
    show (H2.map (localInclHom ⊤ (A j).1 KK)).hom ((H2.map (Φ i)).hom gen) = 0
    rw [← H2_map_comp_apply (f := Φ i) (g := localInclHom ⊤ (A j).1 KK) (x := gen)]
    exact h0

end

end NK.NUV2.LC.RouteB
