/-
# Singer data for `PSU3` Stage A

The main theorem `Work.PSU3.StageA.singer_data` says: a fixed-point-free `F`-linear
endomorphism `T` of the two-dimensional `F`-space `F × F` whose order divides `|F| + 1`
(`F` a field with `|F| = 2 ^ n`) is, after an identification of `F × F` with `E = GF(2 ^ (2n))`
as `F`-spaces, multiplication by a norm-one element `e ∈ Eˣ` of the same order as `T`.

The mathematical content, in the order in which it is formalised here.

* `fpf_no_eigenvector` — `T` has no eigenvalue at all in `F`: if `T v = μ • v` with `v ≠ 0`,
  then `μ ^ orderOf T = 1` (so `μ` is a unit) and `μ ^ (|F| - 1) = 1` by Lagrange.  As `|F|` is
  even, `|F| - 1` is odd, so `μ` has order `1`, i.e. `μ = 1`, contradicting `hfpf`.
  In particular `T` is invertible (no kernel) and `T` is not a scalar.

* `minpoly_irreducible_of_no_eigenvector` — consequently the minimal polynomial `P = minpoly F T`
  is irreducible of degree `2`: it divides the characteristic polynomial (degree `2`), has degree
  `≥ 1`, and has no root, a root `μ` giving an eigenvector.

* `natCard_adjoinRoot` — `|K[X]/(f)| = |K| ^ natDegree f` for `f ≠ 0`; hence the field
  `R = F[X]/(P) = AdjoinRoot P` has `|F| ^ 2 = 2 ^ (2n)` elements.

* `orderOf_adjoinRoot_root_minpoly` — the class `α` of `X` in `R` has the same order as `T`.

* `exists_linearEquiv_adjoinRoot` — the `F[X]`-module structure on `V` given by `T` identifies
  `V` with `R` *for every* nonzero vector `v₀` (which is therefore cyclic): there is
  `Φ : R ≃ₗ[F] V` with `Φ 1 = v₀` and `Φ (α * r) = T (Φ r)`.

* `singer_data` — assembling: `R ≅ E` as rings by uniqueness of finite fields
  (`FiniteField.ringEquivOfCardEq`), `α` is transported to `e`, `F` is embedded in `E` by
  `c ↦ χ (algebraMap F R c)` (whose image lies in the fixed field of the Frobenius, since
  `c ^ |F| = c`), and `β = χ ∘ Φ⁻¹` is the required semilinear bijection.  Finally
  `orderOf e = orderOf T ∣ |F| + 1` gives `e ^ (|F| + 1) = 1`, whence
  `σE e = e ^ (2 ^ n) = e ^ |F| = e⁻¹` and `e * σE e = 1`.

The Frobenius `σE` of `E = GF(2 ^ (2n))` is the `2ⁿ`-power Frobenius, so `σE x = x ^ (2 ^ n)`;
this is `rfl` by the instance `Work.PSU3.galoisFieldFrobInv`.
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

/-! ## Auxiliary lemmas -/

/-- **No eigenvalue.**  A fixed-point-free `F`-linear endomorphism `T` of an `F`-space whose
order divides `|F| + 1` (with `|F| = 2 ^ n`) has no nonzero eigenvector: `T v = μ • v` implies
`v = 0`. -/
theorem fpf_no_eigenvector {n : ℕ} (hn : 1 ≤ n) {F V : Type} [Field F] [Fintype F]
    [AddCommGroup V] [Module F V] (hcard : Nat.card F = 2 ^ n) (T : V →ₗ[F] V)
    (hfpf : ∀ v : V, T v = v → v = 0) (hdvd : orderOf T ∣ Nat.card F + 1) :
    ∀ (μ : F) (v : V), T v = μ • v → v = 0 := by
  intro μ v hv
  by_contra hv0
  have hqpos : 0 < Nat.card F + 1 := Nat.succ_pos _
  have hdpos : 0 < orderOf T := Nat.pos_of_dvd_of_pos hdvd hqpos
  have hpow : ∀ k : ℕ, (T ^ k) v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hv, LinearMap.map_smul, ih, ← mul_smul, pow_succ']
  have hdv : v = μ ^ orderOf T • v := by
    have h := hpow (orderOf T)
    rwa [pow_orderOf_eq_one, Module.End.one_eq_id, LinearMap.id_apply] at h
  have hμd : μ ^ orderOf T = 1 := by
    have h : (μ ^ orderOf T - 1) • v = 0 := by rw [sub_smul, one_smul, ← hdv, sub_self]
    rcases smul_eq_zero.mp h with h1 | h2
    · linear_combination h1
    · exact absurd h2 hv0
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, zero_pow hdpos.ne'] at hμd
    exact zero_ne_one hμd
  have hord1 : orderOf μ ∣ orderOf T := orderOf_dvd_iff_pow_eq_one.mpr hμd
  have hq1 : μ ^ (Nat.card F + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hord1.trans hdvd)
  have hqm1 : μ ^ (Nat.card F - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [Fintype.card_eq_nat_card] at h
  have hμ2 : μ ^ 2 = 1 := by
    have h3 : μ ^ (Nat.card F + 1) = μ ^ (Nat.card F - 1) * μ ^ 2 := by
      rw [← pow_add]
      congr 1
      have h1 : 1 ≤ Nat.card F := by rw [hcard]; exact Nat.one_le_two_pow
      omega
    rw [hq1, hqm1, one_mul] at h3
    exact h3.symm
  have hord2 : orderOf μ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hμ2
  have hord3 : orderOf μ ∣ Nat.card F - 1 := orderOf_dvd_iff_pow_eq_one.mpr hqm1
  have hμ1 : μ = 1 := by
    have hodd : Odd (Nat.card F - 1) := by
      rw [hcard]
      refine Nat.Even.sub_odd (Nat.one_le_two_pow (n := n)) ?_ odd_one
      rw [even_iff_two_dvd]
      exact dvd_pow_self 2 (by omega)
    have hcop : Nat.Coprime 2 (Nat.card F - 1) := Nat.coprime_two_left.mpr hodd
    have hdvd1 : orderOf μ ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hord2 hord3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  exact hv0 (hfpf v (by rw [hv, hμ1, one_smul]))

/-- **The minimal polynomial is an irreducible quadratic.**  With no eigenvalue at all, the
minimal polynomial of `T : F × F →ₗ[F] F × F` is irreducible of degree `2`. -/
theorem minpoly_irreducible_of_no_eigenvector {F : Type} [Field F]
    (T : F × F →ₗ[F] F × F) (hnoeig : ∀ (μ : F) (v : F × F), T v = μ • v → v = 0) :
    Irreducible (minpoly F T) ∧ (minpoly F T).natDegree = 2 := by
  have hInt : IsIntegral F T := LinearMap.isIntegral T
  have hPne : minpoly F T ≠ 0 := (minpoly.monic hInt).ne_zero
  have hP1 : minpoly F T ≠ 1 := by
    intro h
    have h0 := minpoly.aeval F T
    rw [h, map_one] at h0
    exact one_ne_zero h0
  have hfr : Module.finrank F (F × F) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hdeg_le : (minpoly F T).natDegree ≤ 2 := by
    have hdvd := LinearMap.minpoly_dvd_charpoly T
    have hchar : T.charpoly ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
    have h := Polynomial.natDegree_le_of_dvd hdvd hchar
    rwa [LinearMap.charpoly_natDegree, hfr] at h
  have hdeg_ge : 1 ≤ (minpoly F T).natDegree := by
    by_contra h
    have h0 : (minpoly F T).natDegree = 0 := by omega
    refine hP1 ?_
    have hC : minpoly F T = Polynomial.C ((minpoly F T).coeff 0) :=
      Polynomial.eq_C_of_natDegree_le_zero (by omega)
    have hc1 : (minpoly F T).coeff 0 = 1 := by
      have := (minpoly.monic hInt).coeff_natDegree
      rwa [h0] at this
    rw [hC, hc1, Polynomial.C_1]
  have hnotroot : ∀ μ : F, ¬ (minpoly F T).IsRoot μ := by
    intro μ hroot
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    have heval : (T - algebraMap F (Module.End F (F × F)) μ) * (Polynomial.aeval T) Q = 0 := by
      have h : (Polynomial.aeval T) ((Polynomial.X - Polynomial.C μ) * Q) = 0 := by
        rw [← hQ]; exact minpoly.aeval F T
      rwa [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at h
    by_cases hQ0 : (Polynomial.aeval T) Q = 0
    · have hdvd : minpoly F T ∣ Q := minpoly.dvd F T hQ0
      have hQne : Q ≠ 0 := by
        intro h; rw [h, mul_zero] at hQ; exact hPne hQ
      have hle := Polynomial.natDegree_le_of_dvd hdvd hQne
      have hnat : (minpoly F T).natDegree = 1 + Q.natDegree := by
        have h1 := Polynomial.natDegree_mul (p := Polynomial.X - Polynomial.C μ) (q := Q)
          (Polynomial.X_sub_C_ne_zero μ) hQne
        rw [← hQ, Polynomial.natDegree_X_sub_C] at h1
        exact h1
      omega
    · obtain ⟨v, hv⟩ : ∃ v, (Polynomial.aeval T) Q v ≠ 0 := by
        by_contra h
        have h' : ∀ v, (Polynomial.aeval T) Q v = 0 :=
          fun v => not_not.mp (not_exists.mp h v)
        exact hQ0 (LinearMap.ext h')
      have h1 : (T - algebraMap F (Module.End F (F × F)) μ) ((Polynomial.aeval T) Q v) = 0 := by
        have h2 := congrArg (fun f : Module.End F (F × F) => f v) heval
        rwa [Module.End.mul_apply, LinearMap.zero_apply] at h2
      have h2 : T ((Polynomial.aeval T) Q v) = μ • ((Polynomial.aeval T) Q v) := by
        rw [LinearMap.sub_apply, sub_eq_zero] at h1
        simpa using h1
      exact hv (hnoeig μ _ h2)
  have hIrr : Irreducible (minpoly F T) :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      (by rw [Finset.mem_Icc]; exact ⟨hdeg_ge, by omega⟩) hnotroot
  refine ⟨hIrr, ?_⟩
  rcases eq_or_lt_of_le hdeg_le with h | h
  · exact h
  · have h1 : (minpoly F T).natDegree = 1 := by omega
    have hdeg1 : (minpoly F T).degree = 1 := by
      rw [← Nat.cast_one, Polynomial.degree_eq_iff_natDegree_eq_of_pos (by norm_num : (0:ℕ) < 1)]
      exact h1
    obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one hdeg1
    exact absurd hx (hnotroot x)

/-- The order of the class of `X` in `K[X]/(minpoly K φ)` is the order of `φ`. -/
theorem orderOf_adjoinRoot_root_minpoly {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] (φ : V →ₗ[K] V) :
    orderOf (AdjoinRoot.root (minpoly K φ)) = orderOf φ := by
  rw [orderOf_eq_orderOf_iff]
  intro k
  have key : ((AdjoinRoot.root (minpoly K φ)) ^ k = 1) ↔
      (Polynomial.aeval φ ((Polynomial.X : Polynomial K) ^ k - 1) = 0) := by
    have hroot : AdjoinRoot.root (minpoly K φ) =
        AdjoinRoot.mk (minpoly K φ) Polynomial.X := rfl
    rw [hroot, ← map_pow (AdjoinRoot.mk (minpoly K φ)) Polynomial.X k,
      ← map_one (AdjoinRoot.mk (minpoly K φ)), ← sub_eq_zero, ← map_sub,
      AdjoinRoot.mk_eq_zero, minpoly.dvd_iff]
  rw [key, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero]

/-- `AdjoinRoot f` over a finite field has `|K| ^ natDegree f` elements (for `f ≠ 0`). -/
theorem natCard_adjoinRoot {K : Type} [Field K] [Finite K] {f : Polynomial K} (hf : f ≠ 0) :
    Nat.card (AdjoinRoot f) = (Nat.card K) ^ f.natDegree := by
  haveI : Module.Finite K (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hf).basis
  have hfr : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf), AdjoinRoot.powerBasis_dim hf]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f), hfr]

/-- `AdjoinRoot f` is the quotient `K[X]/(f)` (as a ring homomorphism). -/
private noncomputable def adjoinRootToQuotient {K : Type*} [CommRing K] (f : Polynomial K) :
    AdjoinRoot f →+* (Polynomial K ⧸ Ideal.span {f}) where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The universal property of `K[X]/(minpoly K φ)`: `aeval φ` descends to it. -/
private lemma exists_quotient_endHom {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (φ : V →ₗ[K] V) :
    ∃ ρ : AdjoinRoot (minpoly K φ) →+* Module.End K V,
      ρ (AdjoinRoot.root (minpoly K φ)) = φ ∧
        (∀ Q : Polynomial K, ρ (AdjoinRoot.mk (minpoly K φ) Q) = Polynomial.aeval φ Q) := by
  have hker : ∀ a ∈ Ideal.span {minpoly K φ}, (Polynomial.aeval φ) a = 0 := by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, minpoly.aeval, zero_mul]
  refine ⟨(Ideal.Quotient.lift (Ideal.span {minpoly K φ}) (Polynomial.aeval φ).toRingHom hker).comp
    (adjoinRootToQuotient (minpoly K φ)), ?_, ?_⟩
  · have h1 : adjoinRootToQuotient (minpoly K φ) (AdjoinRoot.root (minpoly K φ))
        = Ideal.Quotient.mk _ (Polynomial.X) := rfl
    rw [RingHom.comp_apply, h1, Ideal.Quotient.lift_mk]
    exact Polynomial.aeval_X φ
  · intro Q
    rw [RingHom.comp_apply]
    show (Ideal.Quotient.lift (Ideal.span {minpoly K φ}) (Polynomial.aeval φ).toRingHom hker)
      (Ideal.Quotient.mk _ Q) = Polynomial.aeval φ Q
    exact Ideal.Quotient.lift_mk _ _ hker

/-- **Cyclicity.**  If the minimal polynomial of `T : V →ₗ[F] V` is irreducible of degree
`finrank F V`, then every nonzero `v₀` is a cyclic vector: there is an `F`-linear isomorphism
`AdjoinRoot (minpoly F T) ≃ₗ[F] V` sending `1` to `v₀` and multiplication by the class of `X`
to `T`. -/
theorem exists_linearEquiv_adjoinRoot {F V : Type} [Field F] [Fintype F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (T : V →ₗ[F] V) (v₀ : V) (hv₀ : v₀ ≠ 0)
    (hirr : Irreducible (minpoly F T))
    (hdeg : (minpoly F T).natDegree = Module.finrank F V) :
    ∃ Φ : AdjoinRoot (minpoly F T) ≃ₗ[F] V, Φ 1 = v₀ ∧
      ∀ r : AdjoinRoot (minpoly F T), Φ (AdjoinRoot.root (minpoly F T) * r) = T (Φ r) := by
  classical
  haveI : Fact (Irreducible (minpoly F T)) := ⟨hirr⟩
  haveI : Finite V := Module.finite_of_finite F
  have hPne : minpoly F T ≠ 0 := hirr.ne_zero
  obtain ⟨ρ, hρroot, hρmk⟩ := exists_quotient_endHom T
  have hρC : ∀ c : F, ρ (algebraMap F (AdjoinRoot (minpoly F T)) c) =
      algebraMap F (Module.End F V) c := by
    intro c
    rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C, hρmk, Polynomial.aeval_C]
  let Ψ : AdjoinRoot (minpoly F T) →ₗ[F] V :=
    { toFun := fun r => ρ r v₀
      map_add' := fun a b => by rw [map_add, LinearMap.add_apply]
      map_smul' := fun c r => by
        rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hρC]
        simp }
  have hΨ1 : Ψ 1 = v₀ := by
    show ρ 1 v₀ = v₀
    simp
  have hΨmul : ∀ s r : AdjoinRoot (minpoly F T), Ψ (s * r) = ρ s (Ψ r) := by
    intro s r
    show ρ (s * r) v₀ = ρ s (ρ r v₀)
    rw [map_mul, Module.End.mul_apply]
  have hΨroot : ∀ r : AdjoinRoot (minpoly F T),
      Ψ (AdjoinRoot.root (minpoly F T) * r) = T (Ψ r) := by
    intro r
    rw [hΨmul, hρroot]
  have hinj : Function.Injective Ψ := by
    intro a b hab
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    let u : (AdjoinRoot (minpoly F T))ˣ := Units.mk0 (a - b) hsub
    have hu : (u : AdjoinRoot (minpoly F T)) = a - b := rfl
    have hzero : Ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 : Ψ ((↑u⁻¹ : AdjoinRoot (minpoly F T)) * (a - b)) = 0 := by
      rw [hΨmul, hzero, map_zero]
    have h3 : Ψ 1 = 0 := by rwa [← hu, Units.inv_mul] at h2
    exact hv₀ (hΨ1 ▸ h3)
  have hcard : Nat.card (AdjoinRoot (minpoly F T)) = Nat.card V := by
    rw [natCard_adjoinRoot hPne, hdeg, ← Module.natCard_eq_pow_finrank (K := F) (V := V)]
  have hsurj : Function.Surjective Ψ := by
    have hrange : Set.range Ψ = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [Set.ncard_range_of_injective hinj, Set.ncard_univ, hcard]
    intro v
    have hv : v ∈ Set.range Ψ := by rw [hrange]; exact Set.mem_univ v
    exact hv
  exact ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, hΨ1, fun r => hΨroot r⟩

/-! ## The main theorem -/

/-- **Singer data.** A two-dimensional `F`-space carrying an `F`-linear endomorphism `T` of order
dividing `|F|+1` without non-zero fixed vector is, as an `F[x]`-module, obtained from the
quadratic field extension: there are `e ∈ (E n)ˣ` with `e · σE e = 1` and `orderOf e = orderOf T`,
a ring embedding `ι : F →+* E n` with image the fixed field of `σE`, and an additive bijection
`β : F × F → E n` with `β (T v) = e · β v` and `β (c • v) = ι c · β v`. -/
theorem singer_data {n : ℕ} (hn : 1 ≤ n) (F : Type) [Field F] [Fintype F]
    (hcard : Nat.card F = 2 ^ n) (T : F × F →ₗ[F] F × F)
    (hfpf : ∀ v : F × F, T v = v → v = 0)
    (hdvd : orderOf T ∣ Nat.card F + 1) :
    ∃ (e : (Work.PSU3.E n)ˣ) (ι : F →+* Work.PSU3.E n) (β : F × F → Work.PSU3.E n),
      (e : Work.PSU3.E n) * Work.PSU3.σE (e : Work.PSU3.E n) = 1 ∧
      orderOf e = orderOf T ∧
      (∀ c : F, Work.PSU3.σE (ι c) = ι c) ∧ Function.Injective ι ∧
      (∀ a b : F × F, β (a + b) = β a + β b) ∧ Function.Bijective β ∧
      (∀ v : F × F, β (T v) = (e : Work.PSU3.E n) * β v) ∧
      (∀ (c : F) (v : F × F), β (c • v) = ι c * β v) := by
  classical
  -- the distinguished Frobenius is the `2 ^ n`-power map
  have hσE : ∀ x : GaloisField 2 (2 * n), Work.PSU3.σE x = x ^ (2 ^ n) := fun x => rfl
  -- `T` has no eigenvalue, so `minpoly F T` is an irreducible quadratic
  have hnoeig := fpf_no_eigenvector hn hcard T hfpf hdvd
  obtain ⟨hirr, hdeg⟩ := minpoly_irreducible_of_no_eigenvector T hnoeig
  haveI : Fact (Irreducible (minpoly F T)) := ⟨hirr⟩
  have hPne : minpoly F T ≠ 0 := hirr.ne_zero
  have hfr : Module.finrank F (F × F) = 2 := by rw [Module.finrank_prod, Module.finrank_self]
  have hv0 : (0, 1) ≠ (0 : F × F) := by simp
  -- cyclicity of any nonzero vector
  obtain ⟨Φ, hΦ1, hΦroot⟩ :=
    exists_linearEquiv_adjoinRoot T (0, 1) hv0 hirr (by rw [hdeg, hfr])
  -- the field `R = F[X]/(minpoly F T)` has `2 ^ (2n) = |E|` elements
  have hRcard : Nat.card (AdjoinRoot (minpoly F T)) = (Nat.card F) ^ 2 := by
    rw [natCard_adjoinRoot hPne, hdeg]
  have hcardR : Nat.card (AdjoinRoot (minpoly F T)) = 2 ^ (2 * n) := by
    rw [hRcard, hcard, ← pow_mul]
    congr 1
    ring
  have hEcard : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
    GaloisField.card 2 (2 * n) (by omega)
  haveI : Module.Finite F (AdjoinRoot (minpoly F T)) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hPne).basis
  haveI : Finite (AdjoinRoot (minpoly F T)) := Module.finite_of_finite F
  haveI : Fintype (AdjoinRoot (minpoly F T)) := Fintype.ofFinite _
  haveI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  -- uniqueness of finite fields
  obtain ⟨χ⟩ : Nonempty (AdjoinRoot (minpoly F T) ≃+* GaloisField 2 (2 * n)) :=
    ⟨FiniteField.ringEquivOfCardEq (by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardR, hEcard])⟩
  let α : AdjoinRoot (minpoly F T) := AdjoinRoot.root (minpoly F T)
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : AdjoinRoot.mk (minpoly F T) Polynomial.X = 0 := h0
    have hdvd : minpoly F T ∣ Polynomial.X := AdjoinRoot.mk_eq_zero.mp h1
    have hle := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X.ne_zero)
    rw [Polynomial.natDegree_X] at hle
    omega
  have he0 : χ α ≠ 0 := fun h => hαne (χ.injective (by rw [h, map_zero]))
  let e : (GaloisField 2 (2 * n))ˣ := Units.mk0 (χ α) he0
  let ι : F →+* GaloisField 2 (2 * n) := χ.toRingHom.comp (algebraMap F (AdjoinRoot (minpoly F T)))
  let β : F × F → GaloisField 2 (2 * n) := fun v => χ (Φ.symm v)
  have he_val : (e : GaloisField 2 (2 * n)) = χ α := rfl
  have hι_val : ∀ c : F, ι c = χ (algebraMap F (AdjoinRoot (minpoly F T)) c) := fun c => rfl
  have hβ_val : ∀ v : F × F, β v = χ (Φ.symm v) := fun v => rfl
  have hord_χα : orderOf (χ α) = orderOf T :=
    (orderOf_injective χ.toMonoidHom χ.injective α).trans (orderOf_adjoinRoot_root_minpoly T)
  have hιinj : Function.Injective (algebraMap F (AdjoinRoot (minpoly F T))) :=
    FaithfulSMul.algebraMap_injective F _
  refine ⟨e, ι, β, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `e` has norm one
    have hpow : (e : GaloisField 2 (2 * n)) ^ (Nat.card F + 1) = 1 := by
      rw [he_val]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord_χα]; exact hdvd)
    have hinv : (e : GaloisField 2 (2 * n)) ^ (2 ^ n) = ((e : GaloisField 2 (2 * n)))⁻¹ := by
      have h2 : (e : GaloisField 2 (2 * n)) ^ Nat.card F * (e : GaloisField 2 (2 * n)) = 1 := by
        rw [← pow_succ, hpow]
      have h3 : (e : GaloisField 2 (2 * n)) ^ Nat.card F = ((e : GaloisField 2 (2 * n)))⁻¹ :=
        eq_inv_of_mul_eq_one_left h2
      rw [← hcard]
      exact h3
    rw [hσE, hinv, mul_inv_cancel₀]
    rw [he_val]
    exact he0
  · -- the order of `e` is the order of `T`
    rw [← orderOf_units, he_val, hord_χα]
  · -- `ι` takes values in the fixed field of `σE`
    intro c
    have hcq : (algebraMap F (AdjoinRoot (minpoly F T)) c) ^ (2 ^ n) =
        algebraMap F (AdjoinRoot (minpoly F T)) c := by
      have h : c ^ (2 ^ n) = c := by
        rw [← hcard, ← Fintype.card_eq_nat_card]
        exact FiniteField.pow_card c
      rw [← map_pow, h]
    calc Work.PSU3.σE (ι c)
        = Work.PSU3.σE (χ (algebraMap F (AdjoinRoot (minpoly F T)) c)) := by rw [hι_val]
      _ = (χ (algebraMap F (AdjoinRoot (minpoly F T)) c)) ^ (2 ^ n) := hσE _
      _ = χ ((algebraMap F (AdjoinRoot (minpoly F T)) c) ^ (2 ^ n)) := (map_pow χ _ _).symm
      _ = χ (algebraMap F (AdjoinRoot (minpoly F T)) c) := by rw [hcq]
      _ = ι c := (hι_val c).symm
  · -- `ι` is injective
    intro a b hab
    rw [hι_val a, hι_val b] at hab
    exact hιinj (χ.injective hab)
  · -- `β` is additive
    intro a b
    calc β (a + b) = χ (Φ.symm (a + b)) := hβ_val _
      _ = χ (Φ.symm a + Φ.symm b) := by rw [map_add Φ.symm a b]
      _ = χ (Φ.symm a) + χ (Φ.symm b) := map_add χ _ _
      _ = β a + β b := by rw [hβ_val, hβ_val]
  · -- `β` is bijective
    exact ⟨χ.injective.comp Φ.symm.injective, χ.surjective.comp Φ.symm.surjective⟩
  · -- `β` intertwines `T` with multiplication by `e`
    intro v
    have hαv : Φ.symm (T v) = α * Φ.symm v := by
      have h := hΦroot (Φ.symm v)
      rw [LinearEquiv.apply_symm_apply] at h
      have h2 := congrArg Φ.symm h
      rw [LinearEquiv.symm_apply_apply] at h2
      exact h2.symm
    calc β (T v) = χ (Φ.symm (T v)) := hβ_val _
      _ = χ (α * Φ.symm v) := by rw [hαv]
      _ = χ α * χ (Φ.symm v) := map_mul χ _ _
      _ = (e : GaloisField 2 (2 * n)) * χ (Φ.symm v) := by rw [he_val]
      _ = (e : GaloisField 2 (2 * n)) * β v := by rw [hβ_val]
  · -- `β` is semilinear (compatible with the embedding `ι`)
    intro c v
    calc β (c • v) = χ (Φ.symm (c • v)) := hβ_val _
      _ = χ (c • Φ.symm v) := by rw [map_smul Φ.symm c v]
      _ = χ (algebraMap F (AdjoinRoot (minpoly F T)) c * Φ.symm v) := by rw [Algebra.smul_def]
      _ = χ (algebraMap F (AdjoinRoot (minpoly F T)) c) * χ (Φ.symm v) := map_mul χ _ _
      _ = ι c * β v := by rw [hι_val, hβ_val]

end Work.PSU3.StageA
