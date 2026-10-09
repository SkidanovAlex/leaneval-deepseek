import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.RouteB

/-- **Abstract form of the key number-theoretic input.**

Let `q` be a prime, `E`, `K`, `F` number fields.  Assume `K` is a cyclotomic extension of `ℚ` of
conductor `q` and that `F` is unramified at `q`.  If `E` embeds into both `K` and `F`, then
`E = ℚ`.

The proof is the classical discriminant argument: `discr E` divides both `discr K = ± q ^ (q-2)`
and `discr F`; since `q ∤ discr F` the only prime that could divide `discr E` is `q`, but it does
not divide it, so `discr E = ±1`, and a number field of rank `> 1` has `|discr| > 2`. -/
theorem finrank_eq_one_of_isCyclotomic_of_unramified
    {E K F : Type*} [Field E] [NumberField E] [Field K] [NumberField K] [Field F] [NumberField F]
    (q : ℕ) (hq : q.Prime) [IsCyclotomicExtension {q} ℚ K]
    (hunr : ∀ P : Ideal (NumberField.RingOfIntegers F), P.IsPrime →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) → P.ramificationIdx ℤ = 1)
    (i₁ : E →+* K) (i₂ : E →+* F) : Module.finrank ℚ E = 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- `q` is unramified in `F`, hence does not divide `discr F`.
  have hqndF : ¬ (q : ℤ) ∣ NumberField.discr F := by
    have hqZ : Prime ((q : ℤ)) := (Nat.prime_iff_prime_int (p := q)).mp hq
    rw [NumberField.not_dvd_discr_iff_forall_liesOver F (NumberField.RingOfIntegers F) hqZ]
    intro P hPmax hP
    exact (Ideal.ramificationIdx_eq_one_iff).mp (hunr P hPmax.isPrime hP)
  letI algK : Algebra E K := i₁.toAlgebra
  letI algF : Algebra E F := i₂.toAlgebra
  have h1 : NumberField.discr E ∣ NumberField.discr K := NumberField.discr_dvd_discr E K
  have h2 : NumberField.discr E ∣ NumberField.discr F := NumberField.discr_dvd_discr E F
  have hdiscK : NumberField.discr K = (-1) ^ ((q - 1) / 2) * (q : ℤ) ^ (q - 2) :=
    IsCyclotomicExtension.Rat.discr_prime q K
  have hqndE : ¬ (q : ℤ) ∣ NumberField.discr E := fun h => hqndF (h.trans h2)
  -- `discr E` divides `q ^ (q - 2)`;
  have hn : (NumberField.discr E).natAbs ∣ q ^ (q - 2) := by
    have := Int.natAbs_dvd_natAbs.mpr h1
    rw [hdiscK, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
      one_pow, one_mul, Int.natAbs_natCast] at this
    exact this
  have hnq : ¬ q ∣ (NumberField.discr E).natAbs := by
    intro h
    apply hqndE
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact h
  -- ... but the only prime dividing `q ^ (q - 2)` is `q` itself, which does not divide it,
  have hn1 : (NumberField.discr E).natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hne
    have hpdiv : p ∣ q ^ (q - 2) := dvd_trans hpn hn
    have hpdiv' : p ∣ q := hp.dvd_of_dvd_pow hpdiv
    have hpq : p = q := by
      rcases hq.eq_one_or_self_of_dvd p hpdiv' with h | h
      · exact absurd h hp.ne_one
      · exact h
    exact hnq (hpq ▸ hpn)
  have hunit : IsUnit (NumberField.discr E) := by
    rcases (Int.natAbs_eq_iff.mp hn1) with h | h <;> rw [h] <;> simp
  -- so `discr E = ±1`, forcing `finrank ℚ E = 1`.
  by_contra hne
  have hgt : 1 < Module.finrank ℚ E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have h2' := NumberField.abs_discr_gt_two (K := E) hgt
  rw [Int.isUnit_iff_abs_eq.mp hunit] at h2'
  omega

/-- **A number field unramified at `q` meets `ℚ(ζ_q)` in `ℚ`.**  Let `F` be a number field
embedded as a subfield of a field `Ω`, let `q` be a prime which is unramified in `F`, and let
`ζ ∈ Ω` be a primitive `q`-th root of unity.  Then the subfield `ℚ(ζ) ∩ F` of `Ω` is `ℚ`.

Proof sketch.  Put `E := ℚ⟮ζ⟯ ⊓ (⊥ : IntermediateField F Ω).restrictScalars ℚ` (this is
`ℚ(ζ) ∩ F`, a number field).  Since `q ∤ discr F`, `q ∤ discr ℚ⟮ζ⟯` is false for no other prime:
the only prime that can divide `discr ℚ⟮ζ⟯` is `q` (if `p ≠ q` then every prime of `𝓞 ℚ⟮ζ⟯` above
`p` has ramification index `1` by `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`, so
`¬ p ∣ discr ℚ⟮ζ⟯` by `NumberField.not_dvd_discr_iff_forall_liesOver` plus
`Ideal.ramificationIdx_eq_one_iff`).  Also `discr ↥((⊥ : IntermediateField F Ω).restrictScalars ℚ)
= discr F` (`NumberField.discr_eq_discr_of_algEquiv` along the canonical isomorphism).  Hence
`IsCoprime (discr ℚ⟮ζ⟯) (discr ↥((⊥ : IntermediateField F Ω).restrictScalars ℚ))`, and since
`ℚ⟮ζ⟯/ℚ` is Galois, `NumberField.linearDisjoint_of_isGalois_isCoprime_discr` (applied inside the
*compositum* `ℚ⟮ζ⟯ ⊔ F`, which is a number field — the ambient `Ω` is not!) gives
`ℚ⟮ζ⟯.LinearDisjoint _`, whence `ℚ⟮ζ⟯ ⊓ _ = ⊥` by `IntermediateField.LinearDisjoint.inf_eq_bot`. -/
theorem intersect_cyclotomic_eq_bot {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [Algebra ℚ Ω] [IsScalarTower ℚ F Ω]
    (q : ℕ) (hq : Nat.Prime q)
    (hunr : ∀ P : Ideal (NumberField.RingOfIntegers F), P.IsPrime →
      P.LiesOver (Ideal.span ({(q : ℤ)} : Set ℤ)) → P.ramificationIdx ℤ = 1)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ q) :
    (IntermediateField.adjoin ℚ ({ζ} : Set Ω) : IntermediateField ℚ Ω) ⊓
      (⊥ : IntermediateField F Ω).restrictScalars ℚ = ⊥ := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  -- `ζ` is algebraic over `ℚ` (it is a root of `X ^ q - 1`).
  have hζalg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.X ^ q - Polynomial.C 1, ?_, ?_⟩
    · exact (Polynomial.monic_X_pow_sub_C (1 : ℚ) hq.ne_zero).ne_zero
    · simp [Polynomial.aeval_X_pow, hζ.pow_eq_one]
  -- The two subfields of `Ω` whose intersection is to be computed.
  let K₁ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω)
  let K₂ : IntermediateField ℚ Ω := (⊥ : IntermediateField F Ω).restrictScalars ℚ
  change K₁ ⊓ K₂ = ⊥
  -- `ℚ⟮ζ⟯` is a cyclotomic extension of conductor `q`.
  have hm : K₁.toSubalgebra = Algebra.adjoin ℚ ({ζ} : Set Ω) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
  have e1 := Subalgebra.equivOfEq _ _ hm
  have hcycA := by
    letI : Algebra ℚ ↥K₁ := K₁.algebra'
    haveI h0 : IsCyclotomicExtension {q} ℚ ↥(Algebra.adjoin ℚ ({ζ} : Set Ω)) :=
      hζ.adjoin_isCyclotomicExtension ℚ
    exact IsCyclotomicExtension.equiv {q} ℚ ↥(Algebra.adjoin ℚ ({ζ} : Set Ω)) e1.symm
  -- `↥K₁` carries two (provably equal) `ℚ`-algebra structures; we work in the canonical one.
  have heq : (K₁).algebra' = (DivisionRing.toRatAlgebra : Algebra ℚ ↥K₁) := Subsingleton.elim _ _
  haveI hcyc1 : IsCyclotomicExtension {q} ℚ ↥K₁ := heq ▸ hcycA
  haveI hN1 : NumberField ↥K₁ := IsCyclotomicExtension.numberField {q} ℚ ↥K₁
  -- The intersection, transported to `F` along `algebraMap F Ω`.
  let φ : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let E_F : IntermediateField ℚ F := K₁.comap φ
  haveI hE : NumberField ↥E_F := NumberField.of_intermediateField (K := ℚ) (L := F) E_F
  have hi1 : ↥E_F →+* ↥K₁ := by
    refine (AlgHom.codRestrict (φ.comp E_F.val) K₁.toSubalgebra (fun y => ?_)).toRingHom
    exact y.2
  have hi2 : ↥E_F →+* F := E_F.val.toRingHom
  have hfin : Module.finrank ℚ ↥E_F = 1 :=
    finrank_eq_one_of_isCyclotomic_of_unramified (E := ↥E_F) (K := ↥K₁) (F := F)
      q hq hunr hi1 hi2
  have hEF : E_F = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin
  -- Elementwise conclusion: every element of the intersection lies in the image of `ℚ`.
  rw [eq_bot_iff]
  intro x hx
  rw [IntermediateField.mem_inf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot] at hx2
  obtain ⟨f, rfl⟩ := hx2
  rw [IntermediateField.mem_bot]
  have hf : f ∈ E_F := hx1
  rw [hEF, IntermediateField.mem_bot] at hf
  obtain ⟨c, rfl⟩ := hf
  exact ⟨c, IsScalarTower.algebraMap_apply ℚ F Ω c⟩

end NK.CFTLib.RouteB
