import Mathlib
import Submission.Work.Defs.Basic

namespace Work.Arithmetic

open scoped nonZeroDivisors
open NumberField

/-- Unital ring endomorphisms of `ZMod q` (`q ≠ 0`) are the identity: every element of
`ZMod q` is an integer multiple of `1`. -/
lemma zmod_ringHom_eq_id (q : ℕ) [NeZero q] (f : ZMod q →+* ZMod q) :
    f = RingHom.id (ZMod q) := by
  ext y
  rw [← ZMod.natCast_zmod_val y, map_natCast, RingHom.id_apply, ZMod.natCast_zmod_val]

/-- Any two unital ring homs between rings that are both isomorphic to `ZMod q` agree. -/
lemma ringHom_eq_of_equiv_zmod {R S : Type*} [CommRing R] [CommRing S] (q : ℕ) [NeZero q]
    (α : R ≃+* ZMod q) (β : S ≃+* ZMod q) (f g : R →+* S) : f = g := by
  have h1 : ∀ h : R →+* ZMod q, h = α.toRingHom := by
    intro h
    have h2 : h.comp α.symm.toRingHom = RingHom.id (ZMod q) := zmod_ringHom_eq_id q _
    ext x
    have h3 := RingHom.congr_fun h2 (α x)
    simpa using h3
  have h4 : β.toRingHom.comp f = β.toRingHom.comp g := by
    rw [h1 (β.toRingHom.comp f), h1 (β.toRingHom.comp g)]
  exact RingHom.ext fun x => β.injective (RingHom.congr_fun h4 x)

/-- The quotient of the ring of integers of a number field by the principal ideal `(m)`
has cardinality `m ^ [L : ℚ]`. -/
lemma card_quot_span_nat (L : Type*) [Field L] [NumberField L] (m : ℕ) :
    Nat.card (𝓞 L ⧸ Ideal.span {(m : 𝓞 L)}) = m ^ Module.finrank ℚ L := by
  rw [← Submodule.cardQuot_apply (R := 𝓞 L), ← Ideal.absNorm_apply, Ideal.absNorm_span_natCast,
    NumberField.RingOfIntegers.rank]

/-- For a CM-field `K`, the degree is twice the degree of its maximal real subfield. -/
lemma finrank_eq_two_mul (K : Type*) [Field K] [NumberField K] [IsCMField K] :
    Module.finrank ℚ K = 2 * Module.finrank ℚ (maximalRealSubfield K) := by
  have h2 : Module.finrank (maximalRealSubfield K) K = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rw [← Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K, h2, mul_comm]

/-- Composition of `Ideal.map`s along ring homs whose composite is the identity. -/
lemma map_map_of_id {R : Type*} [Semiring R] (f g : R →+* R) (h : g.comp f = RingHom.id R)
    (I : Ideal R) : Ideal.map g (Ideal.map f I) = I := by
  rw [Ideal.map_map, h, Ideal.map_id]

/-- The "even/odd" decomposition map `a ↦ (a + ca, a - ca)` scaled by `m` is injective
whenever `2 * m = 1`. -/
lemma pairMap_injective {A : Type*} [CommRing A] (c : A ≃+* A) (m : A) (hm : 2 * m = 1) :
    Function.Injective (fun a : A => ((a + c a) * m, (a - c a) * m)) := by
  intro a b h
  have h1 : (a + c a) * m = (b + c b) * m := congrArg Prod.fst h
  have h2 : (a - c a) * m = (b - c b) * m := congrArg Prod.snd h
  have h3 : (2 * a) * m = (2 * b) * m := by
    calc (2 * a) * m = (a + c a) * m + (a - c a) * m := by ring
      _ = (b + c b) * m + (b - c b) * m := by rw [h1, h2]
      _ = (2 * b) * m := by ring
  have ha : a = (2 * a) * m := by
    calc a = a * 1 := by ring
      _ = a * (2 * m) := by rw [hm]
      _ = (2 * a) * m := by ring
  have hb : b = (2 * b) * m := by
    calc b = b * 1 := by ring
      _ = b * (2 * m) := by rw [hm]
      _ = (2 * b) * m := by ring
  rw [ha, hb, h3]

theorem Splitting (K : Type*) [Field K] [NumberField K] [NumberField.IsCMField K]
    (q : ℕ) (hq : Nat.Prime q) (hq4 : q % 4 = 1)
    (hsplit : Work.Defs.SplitsCompletely q K) :
    ∃ P : Fin (Module.finrank ℚ (NumberField.maximalRealSubfield K)) → Ideal (𝓞 K),
      (∀ i, (P i).IsPrime) ∧ (∀ i, (q : 𝓞 K) ∈ P i) ∧
      (∀ i j, i ≠ j → P i ≠ P j) ∧
      (∀ i j, Ideal.map (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingHom (P i) ≠ P j) := by
  classical
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨𝔮, h𝔮prime, h𝔮mem, h𝔮quot, h𝔮nonle, h𝔮prod⟩ := hsplit
  -- ---------------------------------------------------------------- basic ideal theory
  have h𝔮inj : Function.Injective 𝔮 := by
    intro i j hij
    by_contra hne
    exact h𝔮nonle i j hne (le_of_eq hij)
  have h𝔮max : ∀ i, (𝔮 i).IsMaximal := by
    intro i
    refine Ideal.IsPrime.isMaximal (h𝔮prime i) ?_
    intro hbot
    have h0 : (q : 𝓞 K) = 0 := by simpa [hbot] using h𝔮mem i
    exact hq.ne_zero (Nat.cast_eq_zero.mp h0)
  have hcop : Pairwise (fun i j => IsCoprime (𝔮 i) (𝔮 j)) := by
    intro i j hij
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (h𝔮max i) (h𝔮max j) fun h => hij (h𝔮inj h)
  have hprodeq : (∏ i, 𝔮 i) = ⨅ i, 𝔮 i := by
    have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) (J := 𝔮)
      (by intro i _ j _ hij; exact hcop hij)
    simpa using h
  have hinf : (⨅ i, 𝔮 i) = Ideal.span {(q : 𝓞 K)} := hprodeq.symm.trans h𝔮prod.symm
  have hspan_le : ∀ i, Ideal.span {(q : 𝓞 K)} ≤ 𝔮 i :=
    fun i => (Ideal.span_singleton_le_iff_mem _).mpr (h𝔮mem i)
  have hcard𝔮 : ∀ i, Nat.card (𝓞 K ⧸ 𝔮 i) = q := by
    intro i
    obtain ⟨e⟩ := h𝔮quot i
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]
  haveI : ∀ i, Finite (𝓞 K ⧸ 𝔮 i) :=
    fun i => Nat.finite_of_card_ne_zero (by rw [hcard𝔮 i]; exact hq.ne_zero)
  -- characterizing the primes above `q`
  have exists_eq_𝔮 : ∀ P : Ideal (𝓞 K), P.IsPrime → (q : 𝓞 K) ∈ P → ∃ j, P = 𝔮 j := by
    intro P hP hPq
    have hle : (∏ i, 𝔮 i) ≤ P := by
      rw [← h𝔮prod, Ideal.span_singleton_le_iff_mem]; exact hPq
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_le hP).mp hle
    exact ⟨i, ((h𝔮max i).eq_of_le hP.ne_top hi).symm⟩
  -- ---------------------------------------------------------------- conjugation data
  let c : 𝓞 K ≃+* 𝓞 K := (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv
  have hcc : ∀ x : 𝓞 K, c (c x) = x := by
    intro x
    apply RingOfIntegers.ext
    show ((NumberField.IsCMField.ringOfIntegersComplexConj K)
      ((NumberField.IsCMField.ringOfIntegersComplexConj K) x) : K) = ((x : 𝓞 K) : K)
    rw [NumberField.IsCMField.coe_ringOfIntegersComplexConj,
      NumberField.IsCMField.coe_ringOfIntegersComplexConj,
      NumberField.IsCMField.complexConj_apply_apply]
  have hcKp : ∀ z : 𝓞 (maximalRealSubfield K),
      c (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) z) =
        algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) z := by
    intro z
    show (NumberField.IsCMField.ringOfIntegersComplexConj K) _ = _
    exact AlgEquiv.commutes _ z
  have hσhex : ∀ i : Fin (Module.finrank ℚ K),
      ∃ j, Ideal.map c.toRingHom (𝔮 i) = 𝔮 j := by
    intro i
    haveI : (𝔮 i).IsPrime := h𝔮prime i
    exact exists_eq_𝔮 _ (Ideal.map_isPrime_of_equiv c) (by
      rw [← map_natCast c.toRingHom q]
      exact Ideal.mem_map_of_mem c.toRingHom (h𝔮mem i))
  let σ : Fin (Module.finrank ℚ K) → Fin (Module.finrank ℚ K) :=
    fun i => Classical.choose (hσhex i)
  have hσ : ∀ i, Ideal.map c.toRingHom (𝔮 i) = 𝔮 (σ i) :=
    fun i => Classical.choose_spec (hσhex i)
  have hσσ : ∀ i, σ (σ i) = i := by
    intro i
    apply h𝔮inj
    have hcomp : c.toRingHom.comp c.toRingHom = RingHom.id (𝓞 K) :=
      RingHom.ext fun x => hcc x
    have h1 : Ideal.map c.toRingHom
        (Ideal.map c.toRingHom (𝔮 i)) = 𝔮 i := map_map_of_id c.toRingHom c.toRingHom hcomp _
    have h2 : Ideal.map c.toRingHom
        (Ideal.map c.toRingHom (𝔮 i)) = 𝔮 (σ (σ i)) := by
      rw [hσ i, hσ (σ i)]
    exact h2.symm.trans h1
  let R : Finset (Fin (Module.finrank ℚ K)) := Finset.univ.filter (fun i => i < σ i)
  have hR_iff : ∀ i, i ∈ R ↔ i < σ i := by
    intro i
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
  -- ---------------------------------------------------------------- the quotient `A` and `ĉ`
  let A := 𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}
  let ĉ : A →+* A := Ideal.Quotient.lift (Ideal.span {(q : 𝓞 K)})
    ((Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)})).comp c.toRingHom) (by
      intro x hx
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      refine Ideal.mem_span_singleton.mpr ⟨c.toRingHom y, ?_⟩
      rw [map_mul, map_natCast])
  have hĉ_mk : ∀ x : 𝓞 K, ĉ (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) x) =
      Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (c x) := fun x => rfl
  have hĉ2 : ∀ a : A, ĉ (ĉ a) = a := by
    intro a
    induction a using Quotient.inductionOn with
    | _ x =>
      change ĉ (ĉ (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) x)) =
        Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) x
      rw [hĉ_mk, hĉ_mk, hcc]
  have hAcard : Nat.card A = q ^ (2 * Module.finrank ℚ (maximalRealSubfield K)) := by
    change Nat.card (𝓞 K ⧸ Ideal.span {(q : 𝓞 K)}) = _
    rw [card_quot_span_nat, finrank_eq_two_mul]
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hAcard]; exact pow_ne_zero _ hq.ne_zero)
  -- `2` is invertible modulo `q`
  have h2m_nat : 2 * ((q + 1) / 2) = q + 1 := by omega
  have h2m_A : (2 : A) * (((q + 1) / 2 : ℕ) : A) = 1 := by
    have h1 : (((2 * ((q + 1) / 2) : ℕ)) : A) = (2 : A) * (((q + 1) / 2 : ℕ) : A) :=
      Nat.cast_mul 2 ((q + 1) / 2)
    rw [← h1, h2m_nat]
    push_cast
    have hq0 : (q : A) = 0 := by
      change Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (q : 𝓞 K) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Set.mem_singleton _)
    rw [hq0, zero_add]
  have h2m_K : (((q + 1) / 2 : ℕ) : 𝓞 K) * (2 : 𝓞 K) = ((q + 1 : ℕ) : 𝓞 K) := by
    rw [show (2 : 𝓞 K) = ((2 : ℕ) : 𝓞 K) from by norm_num, ← Nat.cast_mul, Nat.mul_comm,
      h2m_nat]
  -- `2 * x ∈ I ⟹ x ∈ I` for ideals `I` above `q`
  have h2unit : ∀ {I : Ideal (𝓞 K)}, (q : 𝓞 K) ∈ I → ∀ x : 𝓞 K, (2 : 𝓞 K) * x ∈ I → x ∈ I := by
    intro I hqI x hx
    have h1 : ((q + 1 : ℕ) : 𝓞 K) * x ∈ I := by
      rw [show ((q + 1 : ℕ) : 𝓞 K) * x = (((q + 1) / 2 : ℕ) : 𝓞 K) * ((2 : 𝓞 K) * x) from by
        rw [← mul_assoc, h2m_K]]
      exact I.mul_mem_left _ hx
    have h2 : ((q : ℕ) : 𝓞 K) * x ∈ I := I.mul_mem_right x hqI
    have h3 : x = ((q + 1 : ℕ) : 𝓞 K) * x - ((q : ℕ) : 𝓞 K) * x := by push_cast; ring
    rw [h3]
    exact I.sub_mem h1 h2
  -- ---------------------------------------------------------------- invariants and
  -- anti-invariants of `ĉ` on `A`
  let φ : (𝓞 (maximalRealSubfield K) ⧸ Ideal.span {(q : 𝓞 (maximalRealSubfield K))}) →+* A :=
    Ideal.Quotient.lift (Ideal.span {(q : 𝓞 (maximalRealSubfield K))})
      ((Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)})).comp
        (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K))) (by
      intro x hx
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      exact Ideal.mem_span_singleton.mpr ⟨algebraMap _ _ y, by rw [map_mul, map_natCast]⟩)
  have hφ_mk : ∀ z : 𝓞 (maximalRealSubfield K),
      φ (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 (maximalRealSubfield K))}) z) =
        Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (algebraMap _ _ z) := fun z => rfl
  have hφ_fix : ∀ z : 𝓞 (maximalRealSubfield K) ⧸
      Ideal.span {(q : 𝓞 (maximalRealSubfield K))}, ĉ (φ z) = φ z := by
    intro z
    induction z using Quotient.inductionOn with
    | _ x =>
      change ĉ (φ (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 (maximalRealSubfield K))}) x)) =
        φ (Ideal.Quotient.mk (Ideal.span {(q : 𝓞 (maximalRealSubfield K))}) x)
      rw [hφ_mk, hĉ_mk]
      congr 1
      exact hcKp x
  have hφ_surj : ∀ a : A, ĉ a = a →
      ∃ z : 𝓞 (maximalRealSubfield K) ⧸ Ideal.span {(q : 𝓞 (maximalRealSubfield K))}, φ z = a := by
    intro a ha
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hcm : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (c x) =
        Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) x := by
      rw [← hĉ_mk x]; exact ha
    have hy : c ((x + c x) * (((q + 1) / 2 : ℕ) : 𝓞 K)) =
        (x + c x) * (((q + 1) / 2 : ℕ) : 𝓞 K) := by
      rw [map_mul, map_add, hcc x, map_natCast]
      ring
    obtain ⟨z, hz⟩ := (NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff K _).mp hy
    refine ⟨Ideal.Quotient.mk _ z, ?_⟩
    rw [hφ_mk, hz]
    calc Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) ((x + c x) * (((q + 1) / 2 : ℕ) : 𝓞 K))
        = (Ideal.Quotient.mk _ x + Ideal.Quotient.mk _ (c x)) *
            (((q + 1) / 2 : ℕ) : A) := by
          rw [map_mul, map_add, map_natCast]
      _ = (Ideal.Quotient.mk _ x + Ideal.Quotient.mk _ x) * (((q + 1) / 2 : ℕ) : A) := by
          rw [hcm]
      _ = ((2 : A) * (((q + 1) / 2 : ℕ) : A)) * Ideal.Quotient.mk _ x := by ring
      _ = Ideal.Quotient.mk _ x := by rw [h2m_A, one_mul]
  haveI : Finite (𝓞 (maximalRealSubfield K) ⧸
      Ideal.span {(q : 𝓞 (maximalRealSubfield K))}) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_quot_span_nat]; exact pow_ne_zero _ hq.ne_zero)
  have hS1 : Nat.card {a : A // ĉ a = a} ≤
      q ^ Module.finrank ℚ (maximalRealSubfield K) := by
    have hsurj : Function.Surjective (fun z : 𝓞 (maximalRealSubfield K) ⧸
        Ideal.span {(q : 𝓞 (maximalRealSubfield K))} =>
        (⟨φ z, hφ_fix z⟩ : {a : A // ĉ a = a})) := by
      rintro ⟨a, ha⟩
      obtain ⟨z, hz⟩ := hφ_surj a ha
      exact ⟨z, Subtype.ext hz⟩
    calc Nat.card {a : A // ĉ a = a}
        ≤ Nat.card (𝓞 (maximalRealSubfield K) ⧸
            Ideal.span {(q : 𝓞 (maximalRealSubfield K))}) :=
          Nat.card_le_card_of_surjective _ hsurj
      _ = q ^ Module.finrank ℚ (maximalRealSubfield K) := card_quot_span_nat _ q
  -- the "even/odd" splitting of `A`
  have hsplit_card : Nat.card A ≤ Nat.card {a : A // ĉ a = a} * Nat.card {a : A // ĉ a = -a} := by
    have hinj : Function.Injective (fun a : A =>
        ((⟨(a + ĉ a) * (((q + 1) / 2 : ℕ) : A), by
            rw [map_mul, map_add, hĉ2, map_natCast]; ring⟩ : {a : A // ĉ a = a}),
         (⟨(a - ĉ a) * (((q + 1) / 2 : ℕ) : A), by
            rw [map_mul, map_sub, hĉ2, map_natCast]; ring⟩ : {a : A // ĉ a = -a}))) := by
      intro a b hab
      have h1 : (a + ĉ a) * (((q + 1) / 2 : ℕ) : A) = (b + ĉ b) * (((q + 1) / 2 : ℕ) : A) := by
        simpa using congrArg (fun p => p.1.val) hab
      have h2 : (a - ĉ a) * (((q + 1) / 2 : ℕ) : A) = (b - ĉ b) * (((q + 1) / 2 : ℕ) : A) := by
        simpa using congrArg (fun p => p.2.val) hab
      have h3 : (2 * a) * (((q + 1) / 2 : ℕ) : A) = (2 * b) * (((q + 1) / 2 : ℕ) : A) := by
        calc (2 * a) * (((q + 1) / 2 : ℕ) : A)
            = (a + ĉ a) * (((q + 1) / 2 : ℕ) : A) + (a - ĉ a) * (((q + 1) / 2 : ℕ) : A) := by
              ring
          _ = (b + ĉ b) * (((q + 1) / 2 : ℕ) : A) + (b - ĉ b) * (((q + 1) / 2 : ℕ) : A) := by
              rw [h1, h2]
          _ = (2 * b) * (((q + 1) / 2 : ℕ) : A) := by ring
      have ha : a = (2 * a) * (((q + 1) / 2 : ℕ) : A) := by
        calc a = a * 1 := by ring
          _ = a * (2 * (((q + 1) / 2 : ℕ) : A)) := by rw [h2m_A]
          _ = (2 * a) * (((q + 1) / 2 : ℕ) : A) := by ring
      have hb : b = (2 * b) * (((q + 1) / 2 : ℕ) : A) := by
        calc b = b * 1 := by ring
          _ = b * (2 * (((q + 1) / 2 : ℕ) : A)) := by rw [h2m_A]
          _ = (2 * b) * (((q + 1) / 2 : ℕ) : A) := by ring
      rw [ha, hb, h3]
    calc Nat.card A ≤ Nat.card ({a : A // ĉ a = a} × {a : A // ĉ a = -a}) :=
          Nat.card_le_card_of_injective _ hinj
      _ = Nat.card {a : A // ĉ a = a} * Nat.card {a : A // ĉ a = -a} := Nat.card_prod _ _
  -- the anti-invariants embed into the coordinates indexed by `R`
  have hS2 : Nat.card {a : A // ĉ a = -a} ≤ q ^ R.card := by
    have hinj : Function.Injective (fun (a : {a : A // ĉ a = -a}) =>
        fun i : R => Ideal.Quotient.factor (hspan_le i.val) a.val) := by
      intro a b hab
      obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (a : A)
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (b : A)
      have hxsum : x + c x ∈ Ideal.span {(q : 𝓞 K)} := by
        have h : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (c x) =
            -Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) x := by
          rw [← hĉ_mk x, hx, a.2]
        have h2 : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (x + c x) = 0 := by
          rw [map_add, h, add_neg_cancel]
        rwa [Ideal.Quotient.eq_zero_iff_mem] at h2
      have hysum : y + c y ∈ Ideal.span {(q : 𝓞 K)} := by
        have h : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (c y) =
            -Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) y := by
          rw [← hĉ_mk y, hy, b.2]
        have h2 : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (y + c y) = 0 := by
          rw [map_add, h, add_neg_cancel]
        rwa [Ideal.Quotient.eq_zero_iff_mem] at h2
      have key : ∀ j, x - y ∈ 𝔮 j := by
        intro j
        by_cases hj : j ∈ R
        · have h2 : Ideal.Quotient.mk (𝔮 j) x = Ideal.Quotient.mk (𝔮 j) y := by
            simpa only [← hx, ← hy, Ideal.Quotient.factor_mk] using congrFun hab ⟨j, hj⟩
          exact (Submodule.Quotient.eq (𝔮 j)).mp h2
        · by_cases hfix : σ j = j
          · have hcs : ∀ z : 𝓞 K, c z - z ∈ 𝔮 j := by
              have hmapj : Ideal.map c.toRingHom (𝔮 j) = 𝔮 j := by rw [hσ j, hfix]
              have hle : 𝔮 j ≤ RingHom.ker ((Ideal.Quotient.mk (𝔮 j)).comp c.toRingHom) := by
                intro z hz
                rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
                  ← hmapj]
                exact Ideal.mem_map_of_mem c.toRingHom hz
              have hcsj : Ideal.Quotient.lift (𝔮 j)
                    ((Ideal.Quotient.mk (𝔮 j)).comp c.toRingHom) hle = RingHom.id _ :=
                ringHom_eq_of_equiv_zmod q (Classical.choice (h𝔮quot j))
                  (Classical.choice (h𝔮quot j)) _ _
              intro z
              have hh : Ideal.Quotient.mk (𝔮 j) (c z) = Ideal.Quotient.mk (𝔮 j) z := by
                have h2 := RingHom.congr_fun hcsj (Ideal.Quotient.mk (𝔮 j) z)
                simpa using h2
              exact (Submodule.Quotient.eq (𝔮 j)).mp hh
            have h2x : (2 : 𝓞 K) * x ∈ 𝔮 j := by
              have hh : (2 : 𝓞 K) * x = (x + c x) - (c x - x) := by ring
              rw [hh]; exact sub_mem (hspan_le j hxsum) (hcs x)
            have h2y : (2 : 𝓞 K) * y ∈ 𝔮 j := by
              have hh : (2 : 𝓞 K) * y = (y + c y) - (c y - y) := by ring
              rw [hh]; exact sub_mem (hspan_le j hysum) (hcs y)
            have h2d : (2 : 𝓞 K) * (x - y) ∈ 𝔮 j := by
              rw [mul_sub]; exact sub_mem h2x h2y
            exact h2unit (h𝔮mem j) (x - y) h2d
          · have hnotlt : ¬ (j < σ j) := fun hlt => hj ((hR_iff j).mpr hlt)
            have hmemR : σ j ∈ R := by
              rw [hR_iff, hσσ j]
              exact lt_of_le_of_ne (not_lt.mp hnotlt) hfix
            have h2 : Ideal.Quotient.mk (𝔮 (σ j)) x = Ideal.Quotient.mk (𝔮 (σ j)) y := by
              simpa only [← hx, ← hy, Ideal.Quotient.factor_mk] using
                congrFun hab ⟨σ j, hmemR⟩
            have hxy : x - y ∈ 𝔮 (σ j) := (Submodule.Quotient.eq (𝔮 (σ j))).mp h2
            have hcd : c x - c y ∈ 𝔮 j := by
              have hmap : Ideal.map c.toRingHom (𝔮 (σ j)) = 𝔮 j := by rw [hσ (σ j), hσσ j]
              have hmem : c (x - y) ∈ Ideal.map c.toRingHom (𝔮 (σ j)) :=
                Ideal.mem_map_of_mem c.toRingHom hxy
              rw [hmap, map_sub] at hmem
              exact hmem
            have h3 : (x - y) + (c x - c y) ∈ 𝔮 j := by
              have hh : (x + c x) - (y + c y) = (x - y) + (c x - c y) := by ring
              rw [← hh]; exact sub_mem (hspan_le j hxsum) (hspan_le j hysum)
            have hh : x - y = ((x - y) + (c x - c y)) - (c x - c y) := by ring
            rw [hh]; exact sub_mem h3 hcd
      have hmem : x - y ∈ Ideal.span {(q : 𝓞 K)} := by
        rw [← hinf]
        exact (Submodule.mem_iInf 𝔮).mpr key
      have hzero : Ideal.Quotient.mk (Ideal.span {(q : 𝓞 K)}) (x - y) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub] at hzero
      exact Subtype.ext (by rw [← hx, ← hy]; exact sub_eq_zero.mp hzero)
    calc Nat.card {a : A // ĉ a = -a} ≤ Nat.card ((i : R) → 𝓞 K ⧸ 𝔮 i.val) :=
          Nat.card_le_card_of_injective _ hinj
      _ = q ^ R.card := by
          rw [Nat.card_pi]
          simp only [hcard𝔮]
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  -- the count forces `R` to have exactly one element per conjugate pair
  have hRcard : R.card = Module.finrank ℚ (maximalRealSubfield K) := by
    refine le_antisymm ?_ ?_
    · have hinjσ : Function.Injective σ := fun i j h => by rw [← hσσ i, h, hσσ j]
      have hdisj : Disjoint R (R.image σ) := by
        rw [Finset.disjoint_left]
        intro i hi hii
        rw [hR_iff] at hi
        obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hii
        rw [hR_iff] at hj
        have h1 : i < j := by
          have : σ i = j := by rw [← hji, hσσ j]
          rwa [this] at hi
        have h2 : j < i := by rw [hji] at hj; exact hj
        exact absurd (lt_trans h1 h2) (lt_irrefl i)
      have hcard : (R ∪ R.image σ).card = 2 * R.card := by
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinjσ]
        ring
      have hle : 2 * R.card ≤ Module.finrank ℚ K := by
        rw [← hcard]
        simpa using Finset.card_le_univ (R ∪ R.image σ)
      have hdeg := finrank_eq_two_mul K
      omega
    · have h1 : q ^ (2 * Module.finrank ℚ (maximalRealSubfield K)) ≤
          q ^ (Module.finrank ℚ (maximalRealSubfield K) + R.card) := by
        calc q ^ (2 * Module.finrank ℚ (maximalRealSubfield K)) = Nat.card A := hAcard.symm
          _ ≤ Nat.card {a : A // ĉ a = a} * Nat.card {a : A // ĉ a = -a} := hsplit_card
          _ ≤ q ^ Module.finrank ℚ (maximalRealSubfield K) * q ^ R.card :=
              Nat.mul_le_mul hS1 hS2
          _ = q ^ (Module.finrank ℚ (maximalRealSubfield K) + R.card) := (pow_add _ _ _).symm
      have := (Nat.pow_le_pow_iff_right hq.one_lt).mp h1
      omega
  -- assemble the family of primes
  let e : Fin (Module.finrank ℚ (maximalRealSubfield K)) ≃ R :=
    (finCongr hRcard).symm.trans (Finset.equivFin R).symm
  refine ⟨fun i => 𝔮 (e i).val, fun i => h𝔮prime _, fun i => h𝔮mem _, ?_, ?_⟩
  · intro i j hij h
    exact hij (e.injective (Subtype.ext (h𝔮inj h)))
  · intro i j h
    exfalso
    have h1 : 𝔮 (σ (e i).val) = 𝔮 (e j).val := by
      rw [← hσ (e i).val]
      exact h
    have h2 : σ (e i).val = (e j).val := h𝔮inj h1
    have hnotin : σ (e i).val ∉ R := by
      intro hcon
      rw [hR_iff] at hcon
      rw [hσσ] at hcon
      exact absurd (lt_trans ((hR_iff (e i).val).mp (e i).2) hcon) (lt_irrefl _)
    rw [h2] at hnotin
    exact hnotin (e j).2

end Work.Arithmetic
