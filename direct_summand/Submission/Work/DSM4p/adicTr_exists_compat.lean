import Mathlib

universe a

namespace Work.DSM4p

open AdicCompletion

/-- The `evalₐ`-counterpart of `AdicCompletion.transitionMap_comp_eval`: the maps
`AdicCompletion.evalₐ I n : AdicCompletion I R →ₐ[R] R ⧸ I ^ n` form a compatible tower. -/
theorem adicTrCompat_factor_evalₐ {R : Type*} [CommRing R] (I : Ideal R) {m n : ℕ}
    (hle : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) (AdicCompletion.evalₐ I n x)
      = AdicCompletion.evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | _ f =>
    rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have hmem : (f.val m : R) - f.val n ∈ (I ^ m • ⊤ : Submodule R R) :=
      SModEq.sub_mem.mp (f.property hle)
    have htop : (I ^ m • ⊤ : Submodule R R) = (I ^ m : Ideal R) := by ext y; simp
    rw [htop] at hmem
    simpa only [neg_sub] using neg_mem hmem

/-- For a ring hom `f` mapping the natural number `p` to itself, the `m`-th power of
`Ideal.span {p}` is mapped into the `m`-th power of `Ideal.span {p}`. -/
theorem adicTrCompat_pow_map_le {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A')
    (p : ℕ) (m : ℕ) :
    ((Ideal.span {(p : A)}) ^ m).map f ≤ (Ideal.span {(p : A')}) ^ m := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
    map_pow, map_natCast]

/-- **Functoriality of adic completion along a `B`-algebra map.**  If the `B`-algebra map
`f : A →ₐ[B] A'` sends the ideal `I` into the ideal `J` to all powers (i.e. `f (I ^ m) ⊆ J ^ m`),
then it induces a `B`-algebra map of the completions, compatible with the structure maps
`AdicCompletion.of`.  This is the `AdicCompletion`-counterpart of the fact that `AdicCompletion`
commutes with the relevant limits: the family of the quotient maps `A ⧸ I ^ m →ₐ[B] A' ⧸ J ^ m`
is compatible, and one applies `AdicCompletion.liftAlgHom` (the universal property of the
completion as the limit of the quotients). -/
theorem adicTrCompat_exists_completion_map {B A A' : Type*} [CommRing B] [CommRing A]
    [CommRing A'] [Algebra B A] [Algebra B A'] (I : Ideal A) (J : Ideal A') (f : A →ₐ[B] A')
    (hIJ : ∀ m : ℕ, (I ^ m).map f ≤ J ^ m) :
    ∃ g : AdicCompletion I A →ₐ[B] AdicCompletion J A',
      ∀ y : A, g (AdicCompletion.of I A y) = AdicCompletion.of J A' (f y) := by
  classical
  -- the vanishing condition making `f` descend to the quotients modulo `I ^ m`
  have hq : ∀ m, ∀ a ∈ I ^ m, ((Ideal.Quotient.mkₐ B (J ^ m)).comp f) a = 0 := by
    intro m a ha
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hIJ m (Ideal.mem_map_of_mem f ha)
  -- the induced algebra maps on the quotients
  let q : (m : ℕ) → A ⧸ I ^ m →ₐ[B] A' ⧸ J ^ m :=
    fun m => Ideal.Quotient.liftₐ (I ^ m) ((Ideal.Quotient.mkₐ B (J ^ m)).comp f) (hq m)
  have hq_mk : ∀ m (y : A),
      q m (Ideal.Quotient.mk (I ^ m) y) = Ideal.Quotient.mk (J ^ m) (f y) := by
    intro m y
    have h := congr($(Ideal.Quotient.liftₐ_comp (I ^ m)
      ((Ideal.Quotient.mkₐ B (J ^ m)).comp f) (hq m)) y)
    simpa [q, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using h
  have hq_compat : ∀ {m k : ℕ} (hle : m ≤ k) (z : A ⧸ I ^ k),
      (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle)) (q k z) =
        q m ((Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle)) z) := by
    intro m k hle z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hq_mk, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk, hq_mk]
  -- the compatible family `AdicCompletion I A →ₐ[B] A' ⧸ J ^ m`
  let fam : (m : ℕ) → AdicCompletion I A →ₐ[B] A' ⧸ J ^ m :=
    fun m => (q m).comp ((AdicCompletion.evalₐ I m).restrictScalars B)
  have hfam : ∀ {m k : ℕ} (hle : m ≤ k),
      (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle)).comp (fam k) = fam m := by
    intro m k hle
    ext x
    show (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle))
        (q k (AdicCompletion.evalₐ I k x)) = q m (AdicCompletion.evalₐ I m x)
    have h1 : AdicCompletion.evalₐ I m x =
        (Ideal.Quotient.factorₐ B (Ideal.pow_le_pow_right hle))
          (AdicCompletion.evalₐ I k x) := by
      rw [Ideal.Quotient.factorₐ_apply]
      exact (adicTrCompat_factor_evalₐ I hle x).symm
    rw [h1, hq_compat hle]
  refine ⟨AdicCompletion.liftAlgHom J fam hfam, fun y => ?_⟩
  refine AdicCompletion.ext_evalₐ fun m => ?_
  rw [AdicCompletion.evalₐ_liftAlgHom]
  show q m (AdicCompletion.evalₐ I m (AdicCompletion.of I A y)) = _
  rw [AdicCompletion.evalₐ_of, hq_mk, AdicCompletion.evalₐ_of]

theorem adicTr_exists_compat {p : ℕ} {B : Type a} [CommRing B]
    {E : ℕ → Type a} [∀ n, CommRing (E n)] [∀ n, Algebra B (E n)]
    (tr : ∀ n, E (n + 1) →ₐ[B] E n) :
    ∃ tr' : ∀ n, AdicCompletion (Ideal.span {((p : E (n + 1)))}) (E (n + 1)) →ₐ[B]
        AdicCompletion (Ideal.span {((p : E n))}) (E n),
      ∀ (n : ℕ) (y : E (n + 1)),
        tr' n (AdicCompletion.of (Ideal.span {((p : E (n+1)))}) (E (n+1)) y)
          = AdicCompletion.of (Ideal.span {((p : E n))}) (E n) (tr n y) := by
  classical
  have key : ∀ n, ∃ g : AdicCompletion (Ideal.span {(p : E (n+1))}) (E (n+1)) →ₐ[B]
      AdicCompletion (Ideal.span {(p : E n)}) (E n),
      ∀ y : E (n+1), g (AdicCompletion.of (Ideal.span {(p : E (n+1))}) (E (n+1)) y)
        = AdicCompletion.of (Ideal.span {(p : E n)}) (E n) (tr n y) := by
    intro n
    exact adicTrCompat_exists_completion_map (I := Ideal.span {(p : E (n+1))})
      (J := Ideal.span {(p : E n)}) (tr n) (fun m => adicTrCompat_pow_map_le (tr n).toRingHom p m)
  choose tr' htr' using key
  exact ⟨tr', htr'⟩

end Work.DSM4p
