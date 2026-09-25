import Mathlib
import Submission.Work.Defs.Basic

/-!
# A Galois closure in which splitting completely descends

This file provides `Work.Tower.Glue.exists_galois_closure_split`: for a number field `F`
and a finite extension `E/F`, there is a number field `N` which is Galois over `ℚ`, comes
with an `F`-algebra embedding `E →ₐ[F] N`, and has the property that any rational prime
which splits completely in `N` splits completely in `E` as well.

The natural choice is the normal closure of `E` over `ℚ` inside an algebraic closure of `E`.
Since the existential quantifier in the requested statement places `N` in an arbitrary
universe, the construction is first carried out inside `AlgebraicClosure ℚ` (which lives in
`Type 0`) and then transported to the target universe along `ULift`.

The mathematical core is the standard fact, proved here for arbitrary number fields: if `q`
splits completely in `N` and `E` embeds into `N`, then `q` splits completely in `E`.  The proof
goes through ramification indices and inertia degrees in the tower `ℤ → 𝓞 E → 𝓞 N`.
-/

namespace Work.Tower.Glue

open NumberField

universe u

/-- Auxiliary counting lemma: if a finite sum of natural numbers, each at least `1`, equals
the number of summands, then every summand is `1`. -/
lemma sum_eq_card_imp_eq_one {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (h1 : ∀ x ∈ s, 1 ≤ f x) (h2 : ∑ x ∈ s, f x = s.card) : ∀ x ∈ s, f x = 1 := by
  intro x hx
  have h3 := Finset.sum_erase_add s f hx
  have h4 : (s.erase x).card ≤ ∑ y ∈ s.erase x, f y := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum (fun y hy => h1 y (Finset.mem_of_mem_erase hy))
  have h5 : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
  have h6 := h1 x hx
  omega

/-- A field `A` mapping into `ZMod q` and of the same cardinality is isomorphic to `ZMod q`. -/
lemma ringEquiv_zmod_of_ringHom (q : ℕ) [Fact q.Prime] {A : Type*} [Field A]
    (f : A →+* ZMod q) (hcard : Nat.card A = q) : Nonempty (A ≃+* ZMod q) := by
  have hq := Fact.out (p := q.Prime)
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq.ne_zero)
  haveI : Fintype A := Fintype.ofFinite A
  have hcard' : Fintype.card A = Fintype.card (ZMod q) := by
    rw [← Nat.card_eq_fintype_card, hcard, ZMod.card]
  have e := Fintype.equivOfCardEq hcard'
  have hinj : Function.Injective f := f.injective
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hinj.surjective_of_finite e⟩⟩

/-- **Core transfer lemma.**  If `q` splits completely in a number field `N` and `E` is a
number field embedded in `N`, then `q` splits completely in `E`. -/
theorem splitsCompletely_of_algHom
    {E N : Type*} [Field E] [NumberField E] [Field N] [NumberField N] [Algebra E N]
    (q : ℕ) (hq : Nat.Prime q) (hsplit : Work.Defs.SplitsCompletely q N) :
    Work.Defs.SplitsCompletely q E := by
  classical
  obtain ⟨𝔮, h𝔮prime, h𝔮mem, h𝔮quot, h𝔮nonle, h𝔮prod⟩ := hsplit
  set p : Ideal ℤ := Ideal.span {(q : ℤ)} with hp_def
  have hqnz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hp_ne : p ≠ ⊥ := by rw [hp_def, Ne, Ideal.span_singleton_eq_bot]; exact hqnz
  have hp_max : p.IsMaximal := by
    rw [hp_def]
    exact ((Ideal.span_singleton_prime hqnz).mpr (Nat.prime_iff_prime_int.mp hq)).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hqnz)
  haveI : p.IsMaximal := hp_max
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hmapN : Ideal.map (algebraMap ℤ (𝓞 N)) p = Ideal.span {(q : 𝓞 N)} := by
    rw [hp_def, Ideal.map_span, Set.image_singleton]; simp
  have hmapE : Ideal.map (algebraMap ℤ (𝓞 E)) p = Ideal.span {(q : 𝓞 E)} := by
    rw [hp_def, Ideal.map_span, Set.image_singleton]; simp
  -- Each `𝔮 i` is a prime of `𝓞 N` lying over `p`.
  have h𝔮_liesOver : ∀ i, (𝔮 i).LiesOver p := by
    intro i
    refine ⟨?_⟩
    rw [Ideal.under_def]
    have h1 : Ideal.map (algebraMap ℤ (𝓞 N)) p ≤ 𝔮 i := by
      rw [hmapN]; exact Ideal.span_singleton_le_iff_mem _ |>.mpr (h𝔮mem i)
    have h2 : p ≤ Ideal.comap (algebraMap ℤ (𝓞 N)) (𝔮 i) := (Ideal.map_le_iff_le_comap).mp h1
    have h3 : Ideal.comap (algebraMap ℤ (𝓞 N)) (𝔮 i) ≠ ⊤ := by
      intro h
      have h4 : (1 : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 N)) (𝔮 i) := by rw [h]; trivial
      rw [Ideal.mem_comap] at h4
      exact (h𝔮prime i).ne_top ((Ideal.eq_top_iff_one (𝔮 i)).mpr (by simpa using h4))
    exact (hp_max.eq_of_le h3 h2).symm ▸ rfl
  have h𝔮_inj : Function.Injective 𝔮 := by
    intro i j hij
    by_contra hne
    exact h𝔮nonle i j hne (le_of_eq hij)
  have hmem_primesOver : ∀ i, 𝔮 i ∈ p.primesOver (𝓞 N) := fun i => ⟨h𝔮prime i, h𝔮_liesOver i⟩
  -- Conversely every prime of `𝓞 N` over `p` is one of the `𝔮 i`.
  have hprimesOver_eq : ∀ 𝔓 : Ideal (𝓞 N), 𝔓 ∈ p.primesOver (𝓞 N) → ∃ i, 𝔓 = 𝔮 i := by
    intro 𝔓 h𝔓
    have hqmem : (q : 𝓞 N) ∈ 𝔓 := by
      have h1 : Ideal.map (algebraMap ℤ (𝓞 N)) p ≤ 𝔓 :=
        (Ideal.map_le_iff_le_comap).mpr h𝔓.2.over.le
      rw [hmapN] at h1
      exact h1 (Ideal.subset_span (Set.mem_singleton _))
    have hle : (∏ i, 𝔮 i) ≤ 𝔓 := by
      rw [← h𝔮prod]; exact Ideal.span_singleton_le_iff_mem _ |>.mpr hqmem
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_le h𝔓.1).mp hle
    refine ⟨i, ?_⟩
    have hmax := Ideal.primesOver.isMaximal (p := p)
      (⟨𝔮 i, hmem_primesOver i⟩ : p.primesOver (𝓞 N))
    exact (hmax.eq_of_le h𝔓.1.ne_top hi).symm
  -- The primes over `p` in `𝓞 N` are exactly `[N : ℚ]` in number, and all have `e = f = 1`.
  have hN_ef : ∀ 𝔓 : Ideal (𝓞 N), 𝔓 ∈ p.primesOver (𝓞 N) →
      𝔓.ramificationIdx ℤ = 1 ∧ 𝔓.inertiaDeg ℤ = 1 := by
    have hcardN : Fintype.card (p.primesOver (𝓞 N)) = Module.finrank ℚ N := by
      have e : Fin (Module.finrank ℚ N) ≃ p.primesOver (𝓞 N) :=
        Equiv.ofBijective (fun i => (⟨𝔮 i, hmem_primesOver i⟩ : p.primesOver (𝓞 N)))
          ⟨fun i j hij => h𝔮_inj (Subtype.ext_iff.mp hij), fun x => by
              obtain ⟨i, hi⟩ := hprimesOver_eq x.1 x.2
              exact ⟨i, Subtype.ext hi.symm⟩⟩
      rw [← Fintype.card_congr e, Fintype.card_fin]
    have hsum := Ideal.sum_ramification_inertia_eq_finrank (p) (𝓞 N)
    have hfinrank : Module.finrank ℤ (𝓞 N) = Module.finrank ℚ N :=
      NumberField.RingOfIntegers.rank N
    intro 𝔓 h𝔓
    haveI : 𝔓.IsPrime := h𝔓.1
    have hgroup : ∀ x ∈ (Finset.univ : Finset (p.primesOver (𝓞 N))),
        1 ≤ x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ := fun x _ =>
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (Ideal.ramificationIdx_pos x.1 ℤ).ne'
        (Ideal.inertiaDeg_pos x.1 ℤ).ne')
    have hsum2 : ∑ x ∈ (Finset.univ : Finset (p.primesOver (𝓞 N))),
        x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ
          = (Finset.univ : Finset (p.primesOver (𝓞 N))).card := by
      rw [Finset.card_univ, hcardN, hsum, hfinrank]
    have hmain := sum_eq_card_imp_eq_one _ _ hgroup hsum2 ⟨𝔓, h𝔓⟩ (Finset.mem_univ _)
    exact (mul_eq_one_iff_of_one_le (Ideal.ramificationIdx_pos 𝔓 ℤ)
      (Ideal.inertiaDeg_pos 𝔓 ℤ)).mp hmain
  have hquotN : ∀ 𝔓 : Ideal (𝓞 N), 𝔓 ∈ p.primesOver (𝓞 N) →
      Nonempty (𝓞 N ⧸ 𝔓 ≃+* ZMod q) := by
    intro 𝔓 h𝔓
    obtain ⟨i, rfl⟩ := hprimesOver_eq 𝔓 h𝔓
    exact h𝔮quot i
  -- The same for the primes over `p` in `𝓞 E`, by multiplicativity in the tower.
  have hE_ef : ∀ 𝔭 : Ideal (𝓞 E), 𝔭 ∈ p.primesOver (𝓞 E) →
      𝔭.ramificationIdx ℤ = 1 ∧ 𝔭.inertiaDeg ℤ = 1 := by
    intro 𝔭 h𝔭
    haveI : 𝔭.IsPrime := h𝔭.1
    haveI : 𝔭.LiesOver p := h𝔭.2
    obtain ⟨𝔓, h𝔓⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 N)))
    haveI : 𝔓.LiesOver 𝔭 := h𝔓.2
    haveI : 𝔓.IsPrime := h𝔓.1
    have h𝔓p : 𝔓 ∈ p.primesOver (𝓞 N) := ⟨h𝔓.1, Ideal.LiesOver.trans 𝔓 𝔭 p⟩
    have h := hN_ef 𝔓 h𝔓p
    refine ⟨?_, ?_⟩
    · have hdvd := Ideal.ramificationIdx_below_dvd (R := ℤ) 𝔭 𝔓
      rw [h.1] at hdvd
      exact Nat.dvd_one.mp hdvd
    · have hdvd := Ideal.inertiaDeg_below_dvd (R := ℤ) 𝔭 𝔓
      rw [h.2] at hdvd
      exact Nat.dvd_one.mp hdvd
  -- Hence there are exactly `[E : ℚ]` primes over `q` in `𝓞 E`.
  have hcardE : Fintype.card (p.primesOver (𝓞 E)) = Module.finrank ℚ E := by
    have hsumE := Ideal.sum_ramification_inertia_eq_finrank (p) (𝓞 E)
    have hfinrankE : Module.finrank ℤ (𝓞 E) = Module.finrank ℚ E :=
      NumberField.RingOfIntegers.rank E
    have hterms : ∀ x : p.primesOver (𝓞 E), x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ = 1 := by
      intro x
      rw [(hE_ef x.1 x.2).1, (hE_ef x.1 x.2).2, mul_one]
    have h1 : ∑ x : p.primesOver (𝓞 E), x.1.ramificationIdx ℤ * x.1.inertiaDeg ℤ
        = Fintype.card (p.primesOver (𝓞 E)) := by
      rw [Finset.sum_congr rfl (fun x _ => hterms x), Finset.sum_const, Finset.card_univ,
        smul_eq_mul, mul_one]
    rw [← h1, hsumE, hfinrankE]
  -- The ideal `(q)` in `𝓞 E` is the product of those primes.
  have hprodE : Ideal.span {(q : 𝓞 E)} = ∏ P ∈ (p.primesOver (𝓞 E)).toFinset, P := by
    rw [← hmapE, Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 E) (p := p) hp_ne]
    refine Finset.prod_congr rfl (fun P hP => ?_)
    rw [(hE_ef P ((Set.mem_toFinset).mp hP)).1, pow_one]
  -- The residue field at every such prime is `𝔽_q`.
  have hp_card : p.cardQuot = q := by
    rw [hp_def, Submodule.cardQuot_apply]
    haveI : NeZero (Int.natAbs (q:ℤ)) := ⟨by simpa using hq.ne_zero⟩
    rw [Nat.card_congr (Int.quotientSpanEquivZMod (q:ℤ)).toEquiv]
    rw [Nat.card_eq_fintype_card, ZMod.card]; simp
  have hresE : ∀ 𝔭 : Ideal (𝓞 E), 𝔭 ∈ p.primesOver (𝓞 E) →
      Nonempty (𝓞 E ⧸ 𝔭 ≃+* ZMod q) := by
    intro 𝔭 h𝔭
    haveI : 𝔭.IsPrime := h𝔭.1
    haveI : 𝔭.LiesOver p := h𝔭.2
    haveI : 𝔭.IsMaximal := Ideal.primesOver.isMaximal (⟨𝔭, h𝔭⟩ : p.primesOver (𝓞 E))
    obtain ⟨𝔓, h𝔓⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 N)))
    haveI : 𝔓.LiesOver 𝔭 := h𝔓.2
    haveI : 𝔓.IsPrime := h𝔓.1
    have h𝔓p : 𝔓 ∈ p.primesOver (𝓞 N) := ⟨h𝔓.1, Ideal.LiesOver.trans 𝔓 𝔭 p⟩
    obtain ⟨e⟩ := hquotN 𝔓 h𝔓p
    have key : ∀ a ∈ 𝔭, (Ideal.Quotient.mk 𝔓) (algebraMap (𝓞 E) (𝓞 N) a) = 0 := by
      intro a ha
      rw [Ideal.Quotient.eq_zero_iff_mem]
      rw [h𝔓.2.over] at ha
      exact Ideal.mem_comap.mp ha
    let ψ : 𝓞 E ⧸ 𝔭 →+* 𝓞 N ⧸ 𝔓 :=
      Ideal.Quotient.lift 𝔭 ((Ideal.Quotient.mk 𝔓).comp (algebraMap (𝓞 E) (𝓞 N))) key
    have hcard : Nat.card (𝓞 E ⧸ 𝔭) = q := by
      have hcq := Ideal.cardQuot_pow_inertiaDeg (R := ℤ) p 𝔭
      rw [(hE_ef 𝔭 h𝔭).2, pow_one] at hcq
      have h𝔭q : 𝔭.cardQuot = Nat.card (𝓞 E ⧸ 𝔭) := Submodule.cardQuot_apply 𝔭
      rw [← h𝔭q, ← hcq, hp_card]
    letI : Field (𝓞 E ⧸ 𝔭) := Ideal.Quotient.field 𝔭
    exact ringEquiv_zmod_of_ringHom q (e.toRingHom.comp ψ) hcard
  -- Assemble the data of `SplitsCompletely q E`.
  let e : Fin (Module.finrank ℚ E) ≃ p.primesOver (𝓞 E) :=
    (finCongr hcardE).symm.trans (Fintype.equivFin (p.primesOver (𝓞 E))).symm
  have hprod_conv : Ideal.span {(q : 𝓞 E)} = ∏ i, (e i).1 := by
    rw [hprodE, ← Finset.prod_set_coe (s := p.primesOver (𝓞 E))
      (f := fun P : Ideal (𝓞 E) => P)]
    exact Fintype.prod_equiv e.symm _ _ (fun x => by rw [e.apply_symm_apply])
  refine ⟨fun i => (e i).1, fun i => (e i).2.1, ?_, fun i => hresE _ (e i).2, ?_, hprod_conv⟩
  · intro i
    haveI : (e i).1.LiesOver p := (e i).2.2
    have h := (e i).2.2.over
    have hmem : (q : ℤ) ∈ p := by rw [hp_def]; exact Ideal.subset_span (Set.mem_singleton _)
    rw [h] at hmem
    simpa using Ideal.mem_comap.mp hmem
  · intro i j hij hle
    apply hij
    have := (Ideal.IsMaximal.eq_of_le (Ideal.primesOver.isMaximal (e i)) (e j).2.1.ne_top hle)
    exact e.injective (Subtype.ext this)

/-- The normal closure of `E` over `ℚ`, taken inside `AlgebraicClosure ℚ`, is a number field
which is Galois over `ℚ` and receives `E`; its underlying type lives in `Type 0`.  This is the
construction used to build the witness of `exists_galois_closure_split`. -/
theorem exists_galois_closure_split_aux
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] :
    ∃ (N : Type u) (_ : Field N) (_ : NumberField N) (_ : Algebra F N)
      (_ : IsScalarTower ℚ F N) (_ : IsGalois ℚ N) (_ : FiniteDimensional F N)
      (φ : E →ₐ[F] N),
      ∀ (q : ℕ), Nat.Prime q → Work.Defs.SplitsCompletely q N →
        Work.Defs.SplitsCompletely q E := by
  classical
  let φL : E →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift (R := ℚ) (S := E) (M := AlgebraicClosure ℚ)
  letI : Algebra E (AlgebraicClosure ℚ) := RingHom.toAlgebra φL.toRingHom
  haveI hST : IsScalarTower ℚ E (AlgebraicClosure ℚ) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show algebraMap ℚ (AlgebraicClosure ℚ) x = algebraMap E (AlgebraicClosure ℚ) (algebraMap ℚ E x)
    rw [RingHom.algebraMap_toAlgebra]
    exact (φL.commutes x).symm
  haveI hNC : IsNormalClosure ℚ E
      ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (F := ℚ) (K := E) (L := AlgebraicClosure ℚ)
      (fun _ => IsAlgClosed.splits _)
  haveI hNor : Normal ℚ ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) :=
    IsNormalClosure.normal (F := ℚ) (K := E)
      (L := ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)))
  haveI hGal₀ : IsGalois ℚ ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) :=
    inferInstance
  haveI hNF₀ : NumberField ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) :=
    NumberField.of_module_finite ℚ ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))
  haveI hST₀ : IsScalarTower ℚ E ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) :=
    inferInstance
  -- The `F`-algebra structure on the normal closure.
  letI hAF₀ : Algebra F ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) :=
    RingHom.toAlgebra ((algebraMap E ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))).comp
      (algebraMap F E))
  haveI hSTFE₀ : IsScalarTower F E ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hSTQF₀ : IsScalarTower ℚ F ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    show algebraMap ℚ ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) x
      = algebraMap F ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)) (algebraMap ℚ F x)
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply ℚ F E,
      ← IsScalarTower.algebraMap_apply ℚ E ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))]
  -- Transport along `ULift` to the target universe.
  letI hAlgQ : Algebra ℚ (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    ULift.algebra
  letI hAE : Algebra E (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    ULift.algebra
  letI hAF : Algebra F (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    ULift.algebra
  haveI hNF : NumberField (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    NumberField.of_module_finite ℚ
      (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)))
  haveI hGal : IsGalois ℚ
      (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    IsGalois.of_algEquiv (F := ℚ)
      (E := ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)))
      (ULift.algEquiv (R := ℚ)
        (A := ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)))).symm
  haveI hST2 : IsScalarTower ℚ E
      (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    ULift.isScalarTower''
  haveI hST3 : IsScalarTower F E
      (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    ULift.isScalarTower''
  haveI hST4 : IsScalarTower ℚ F
      (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    ULift.isScalarTower''
  haveI hFD : FiniteDimensional F
      (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))) :=
    Module.Finite.of_restrictScalars_finite ℚ F _
  refine ⟨ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ)),
    inferInstance, hNF, hAF, hST4, hGal, hFD,
    IsScalarTower.toAlgHom F E
      (ULift.{u, 0} ↥(IntermediateField.normalClosure ℚ E (AlgebraicClosure ℚ))), ?_⟩
  intro q hq hsplit
  exact splitsCompletely_of_algHom q hq hsplit

/-- **The requested statement.**  Every finite extension `E/F` of number fields embeds into a
number field `N` that is Galois over `ℚ`, and any rational prime splitting completely in `N`
splits completely in `E`. -/
theorem exists_galois_closure_split
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] :
    ∃ (N : Type*) (_ : Field N) (_ : NumberField N) (_ : Algebra F N)
      (_ : IsScalarTower ℚ F N) (_ : IsGalois ℚ N) (_ : FiniteDimensional F N)
      (φ : E →ₐ[F] N),
      ∀ (q : ℕ), Nat.Prime q → Work.Defs.SplitsCompletely q N →
        Work.Defs.SplitsCompletely q E :=
  exists_galois_closure_split_aux F E

end Work.Tower.Glue
