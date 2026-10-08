import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Polynomial Module

namespace Work.Higman

/-- The identity map, viewed as a ring hom between the two presentations of the same quotient. -/
private noncomputable def adjoinRootToQuotient {K : Type*} [CommRing K] (f : Polynomial K) :
    AdjoinRoot f →+* (Polynomial K ⧸ Ideal.span {f}) where
  toFun x := x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The coercion from linear automorphisms to endomorphisms preserves `orderOf`. -/
private lemma orderOf_toLinearMap {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (e : V ≃ₗ[K] V) : orderOf (e : V →ₗ[K] V) = orderOf e :=
  orderOf_injective (LinearEquiv.automorphismGroup.toLinearMapMonoidHom) (fun a b h =>
    LinearEquiv.ext (fun v => by
      have := congr_arg (fun f : V →ₗ[K] V => f v) h
      simpa using this)) e

/-- The cardinality of `AdjoinRoot f` over a finite field `K`. -/
private lemma natCard_adjoinRoot {K : Type*} [Field K] [Finite K] {f : Polynomial K} (hf : f ≠ 0) :
    Nat.card (AdjoinRoot f) = Nat.card K ^ f.natDegree := by
  haveI : Module.Finite K (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hf).basis
  have hfr : Module.finrank K (AdjoinRoot f) = f.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf), AdjoinRoot.powerBasis_dim hf]
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f), hfr]

/-- A finite nontrivial commutative ring with an element whose order is one less than its
cardinality is a field, and in that case its cardinality is `N + 1`. -/
private lemma isField_and_natCard_of_orderOf_card {R : Type*} [CommRing R] [Nontrivial R]
    [Finite R] (α : R) {N : ℕ} (hcard : Nat.card R ≤ N + 1) (hord : orderOf α = N) :
    IsField R ∧ Nat.card R = N + 1 := by
  classical
  haveI : Fintype R := Fintype.ofFinite R
  rw [Nat.card_eq_fintype_card] at hcard
  have hαN : α ^ N = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
  have hinj : ∀ a b : ℕ, a < N → b < N → α ^ a = α ^ b → a = b := by
    intro a b ha hb hab
    exact pow_injOn_Iio_orderOf (by simpa [hord] using ha) (by simpa [hord] using hb) hab
  have hne0 : ∀ k : ℕ, k < N → α ^ k ≠ 0 := by
    intro k hk hk0
    have h1 : α ^ k * α ^ (N - k) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hk), hαN]
    rw [hk0, zero_mul] at h1
    exact zero_ne_one h1
  have hS : ((Finset.range N).image (fun k => α ^ k)).card = N := by
    rw [Finset.card_image_of_injOn (fun a ha b hb h =>
      hinj a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) h), Finset.card_range]
  have hsub : (Finset.range N).image (fun k => α ^ k) ⊆ (Finset.univ : Finset R).erase 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact Finset.mem_erase.mpr ⟨hne0 k (Finset.mem_range.mp hk), Finset.mem_univ _⟩
  have hErase : ((Finset.univ : Finset R).erase 0).card = Fintype.card R - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ]
  have hle : N + 1 ≤ Fintype.card R := by
    have h := Finset.card_le_card hsub
    rw [hS, hErase] at h
    have h2 : 1 < Fintype.card R := Fintype.one_lt_card_iff_nontrivial.mpr ‹Nontrivial R›
    omega
  have hEq : Nat.card R = N + 1 := by
    rw [Nat.card_eq_fintype_card]; omega
  have hunit : ∀ x : R, x ≠ 0 → IsUnit x := by
    intro x hx
    have hset : (Finset.range N).image (fun k => α ^ k) = (Finset.univ : Finset R).erase 0 := by
      refine Finset.eq_of_subset_of_card_le hsub ?_
      rw [hS, hErase]
      omega
    have hxmem : x ∈ (Finset.range N).image (fun k => α ^ k) := by
      rw [hset]
      exact Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩
    rw [Finset.mem_image] at hxmem
    obtain ⟨k, hk, rfl⟩ := hxmem
    have hk' : k < N := Finset.mem_range.mp hk
    exact isUnit_iff_exists.mpr ⟨α ^ (N - k),
      by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hk'), hαN],
      by rw [← pow_add, Nat.sub_add_cancel (le_of_lt hk'), hαN]⟩
  refine ⟨⟨⟨0, 1, zero_ne_one⟩, fun x y => mul_comm x y, fun {a} ha => ?_⟩, hEq⟩
  exact (hunit a ha).exists_right_inv

/-- The order of the class of `X` in `K[X]/(minpoly K φ)` is the order of `φ`. -/
private lemma orderOf_adjoinRoot_root {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (φ : V →ₗ[K] V) :
    orderOf (AdjoinRoot.root (minpoly K φ)) = orderOf φ := by
  rw [orderOf_eq_orderOf_iff]
  intro k
  have key : ((AdjoinRoot.root (minpoly K φ)) ^ k = 1) ↔
      (Polynomial.aeval φ ((Polynomial.X : Polynomial K) ^ k - 1) = 0) := by
    have hroot : AdjoinRoot.root (minpoly K φ) = AdjoinRoot.mk (minpoly K φ) Polynomial.X := rfl
    rw [hroot, ← map_pow (AdjoinRoot.mk (minpoly K φ)) Polynomial.X k,
      ← map_one (AdjoinRoot.mk (minpoly K φ)), ← sub_eq_zero, ← map_sub,
      AdjoinRoot.mk_eq_zero, minpoly.dvd_iff]
  rw [key, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero]

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

/-- **Singer cycle = field multiplication.**  A linear automorphism `ξ` of an `𝔽₂`-vector space
`V` of cardinality `2 ^ n` whose order is `2 ^ n - 1` and which has no nonzero fixed vector
identifies `V` with the field `GF(2 ^ n)` in such a way that `ξ` becomes multiplication by a
primitive element. -/
theorem exists_singer_iso {n : ℕ} (hn : 0 < n) {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (hV : Nat.card V = 2 ^ n) (ξ : V ≃ₗ[ZMod 2] V)
    (hord : orderOf ξ = 2 ^ n - 1) (hfree : ∀ v : V, ξ v = v → v = 0) :
    ∃ (φ : V ≃ₗ[ZMod 2] GaloisField 2 n) (lam : (GaloisField 2 n)ˣ),
      orderOf lam = 2 ^ n - 1 ∧ ∀ v : V, φ (ξ v) = (lam : GaloisField 2 n) * φ v := by
  classical
  have hpow : 2 ^ n - 1 + 1 = 2 ^ n := Nat.succ_pred_eq_of_pos (pow_pos (by norm_num) n)
  -- ## Step 0: dimension and nontriviality
  have hfin : Module.finrank (ZMod 2) V = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact Nat.pow_right_injective (le_refl 2) h.symm
  haveI : Nontrivial V := by
    haveI : Fintype V := Fintype.ofFinite V
    refine Fintype.one_lt_card_iff_nontrivial.mp ?_
    rw [← Nat.card_eq_fintype_card, hV]
    exact Nat.one_lt_pow hn.ne' (by norm_num)
  haveI hEndnt : Nontrivial (Module.End (ZMod 2) V) := ⟨1, 0, fun h => by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (by simpa using congr_arg (fun f : Module.End (ZMod 2) V => f v) h)⟩
  -- ## Step 1: `φ₀ = ξ`, `P = minpoly φ₀`
  set φ₀ : V →ₗ[ZMod 2] V := ξ.toLinearMap with hφ₀
  have hφ₀ord : orderOf φ₀ = 2 ^ n - 1 := by rw [hφ₀, orderOf_toLinearMap, hord]
  set P : Polynomial (ZMod 2) := minpoly (ZMod 2) φ₀ with hP
  have hPne : P ≠ 0 := by rw [hP]; exact minpoly.ne_zero (LinearMap.isIntegral φ₀)
  have hPdeg : P.natDegree ≤ n := by
    have hdvd : P ∣ φ₀.charpoly := by rw [hP]; exact LinearMap.minpoly_dvd_charpoly φ₀
    have hne : φ₀.charpoly ≠ 0 := (LinearMap.charpoly_monic φ₀).ne_zero
    have h := Polynomial.natDegree_le_of_dvd hdvd hne
    rwa [LinearMap.charpoly_natDegree, hfin] at h
  let R := AdjoinRoot P
  have hRcard : Nat.card R = 2 ^ P.natDegree := by
    show Nat.card (AdjoinRoot P) = 2 ^ P.natDegree
    rw [natCard_adjoinRoot hPne, Nat.card_zmod]
  have hRle : Nat.card R ≤ 2 ^ n := by
    rw [hRcard]
    exact Nat.pow_le_pow_right (by norm_num) hPdeg
  haveI hRnt : Nontrivial R := by
    show Nontrivial (AdjoinRoot P)
    refine Ideal.Quotient.nontrivial_iff.mpr fun htop => ?_
    have h1 : (1 : Polynomial (ZMod 2)) ∈ Ideal.span {P} := by rw [htop]; exact Submodule.mem_top
    have hdvd : P ∣ (1 : Polynomial (ZMod 2)) := Ideal.mem_span_singleton.mp h1
    have hdvd' : minpoly (ZMod 2) φ₀ ∣ (1 : Polynomial (ZMod 2)) := by rwa [hP] at hdvd
    have h0 : (Polynomial.aeval φ₀) (1 : Polynomial (ZMod 2)) = 0 :=
      (minpoly.dvd_iff (x := φ₀)).mp hdvd'
    have h0' : (1 : Module.End (ZMod 2) V) = 0 := by simpa using h0
    exact one_ne_zero h0'
  -- ## Step 2: `α = root P` has order `2 ^ n - 1`
  set α : R := AdjoinRoot.root P with hα
  have hαord : orderOf α = 2 ^ n - 1 := by
    have h1 : orderOf (AdjoinRoot.root P) = orderOf φ₀ := by
      rw [hP]; exact orderOf_adjoinRoot_root φ₀
    rw [hα, h1, hφ₀ord]
  have hαN : α ^ (2 ^ n - 1) = 1 := by rw [← hαord]; exact pow_orderOf_eq_one α
  -- ## Step 3: `R` is a field of cardinality `2 ^ n`
  haveI : Module.Finite (ZMod 2) R :=
    Finite.of_basis (AdjoinRoot.powerBasis hPne).basis
  haveI : Finite R := Module.finite_of_finite (R := ZMod 2) (M := R)
  obtain ⟨hIsField, hRcard2⟩ :=
    isField_and_natCard_of_orderOf_card α (by rw [hpow]; exact hRle) hαord
  have hRcard3 : Nat.card R = 2 ^ n := by rw [hRcard2, hpow]
  have hNpos : 0 < 2 ^ n - 1 := by
    have : 1 < 2 ^ n := Nat.one_lt_pow hn.ne' (by norm_num)
    omega
  have hαne : α ≠ 0 := by
    intro h0
    have h1 : (0 : R) ^ (2 ^ n - 1) = 1 := h0 ▸ hαN
    rw [zero_pow hNpos.ne'] at h1
    exact zero_ne_one h1
  -- ## Step 4: the linear map `Ψ : R → V`
  obtain ⟨ρ, hρα, hρmk⟩ := exists_quotient_endHom φ₀
  obtain ⟨v0, hv0⟩ := exists_ne (0 : V)
  have hρC : ∀ c : ZMod 2,
      ρ (algebraMap (ZMod 2) R c) = algebraMap (ZMod 2) (Module.End (ZMod 2) V) c := by
    intro c
    have h3 : algebraMap (ZMod 2) R c = AdjoinRoot.mk P (Polynomial.C c) := by
      rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
    rw [h3, hρmk (Polynomial.C c), Polynomial.aeval_C]
  have hΨadd : ∀ r s : R, ρ (r + s) v0 = ρ r v0 + ρ s v0 := fun r s => by
    rw [map_add, LinearMap.add_apply]
  have hΨsmul : ∀ (c : ZMod 2) (r : R), ρ (c • r) v0 = c • (ρ r v0) := by
    intro c r
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hρC]
    rw [← End.smul_def, IsScalarTower.algebraMap_smul (Module.End (ZMod 2) V)]
  let Ψ : R →ₗ[ZMod 2] V := LinearMap.mk (AddHom.mk (fun r => ρ r v0) hΨadd) hΨsmul
  have hΨmul : ∀ a b : R, Ψ (a * b) = ρ a (Ψ b) := by
    intro a b
    show ρ (a * b) v0 = ρ a (ρ b v0)
    rw [map_mul, Module.End.mul_apply]
  have hΨ1 : Ψ 1 = v0 := by
    show ρ 1 v0 = v0
    rw [map_one, Module.End.one_eq_id, LinearMap.id_apply]
  have hΨα : ∀ b : R, Ψ (α * b) = ξ (Ψ b) := by
    intro b
    rw [hΨmul, hρα]
    rfl
  -- ## Step 5: `Ψ` is bijective
  have hinj : Function.Injective Ψ := by
    intro a b hab
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    obtain ⟨s, hs⟩ := hIsField.mul_inv_cancel hsub
    have hzero : Ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h1 : Ψ 1 = 0 := by
      have h2 : Ψ (s * (a - b)) = 0 := by rw [hΨmul, hzero, map_zero]
      rwa [mul_comm s (a - b), hs] at h2
    exact hv0 (hΨ1 ▸ h1)
  have hsurj : Function.Surjective Ψ := by
    have hrange : Set.range Ψ = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [Set.ncard_range_of_injective hinj, Set.ncard_univ, hRcard3, hV]
    intro v
    have hv : v ∈ Set.range Ψ := by rw [hrange]; exact Set.mem_univ v
    exact hv
  have hbij : Function.Bijective Ψ := ⟨hinj, hsurj⟩
  let Φ : R ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective Ψ hbij
  have hΦ_apply : ∀ r : R, Φ r = Ψ r := fun r => rfl
  have hΦα : ∀ b : R, Φ (α * b) = ξ (Φ b) := by
    intro b
    rw [hΦ_apply, hΦ_apply, hΨα]
  have hΦsymm : ∀ v : V, Φ.symm (ξ v) = α * Φ.symm v := by
    intro v
    have h := hΦα (Φ.symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    have h2 : Φ.symm (Φ (α * Φ.symm v)) = Φ.symm (ξ v) := congrArg Φ.symm h
    rw [LinearEquiv.symm_apply_apply] at h2
    exact h2.symm
  -- ## Step 6: compose with the Galois field
  let χ : R ≃ₐ[ZMod 2] GaloisField 2 n :=
    @GaloisField.algEquivGaloisField 2 (⟨Nat.prime_two⟩ : Fact (Nat.Prime 2)) n R
      hIsField.toField (inferInstance) hRcard3
  have hχαne : χ α ≠ 0 := fun h => hαne (χ.injective (by rw [h, map_zero]))
  refine ⟨Φ.symm.trans χ.toLinearEquiv, Units.mk0 (χ α) hχαne, ?_, ?_⟩
  · have hu : orderOf (Units.mk0 (χ α) hχαne) = orderOf α := by
      refine (orderOf_eq_orderOf_iff).mpr fun k => ⟨?_, ?_⟩
      · intro h
        have h1 : (χ α : GaloisField 2 n) ^ k = 1 := by
          have := congrArg (fun u : (GaloisField 2 n)ˣ => (u : GaloisField 2 n)) h
          simpa using this
        rw [← map_pow, ← map_one χ] at h1
        exact χ.injective h1
      · intro h
        have h1 : (χ α : GaloisField 2 n) ^ k = 1 := by rw [← map_pow, h, map_one]
        exact Units.ext (by simpa using h1)
    rw [hu, hαord]
  · intro v
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply,
      AlgEquiv.toLinearEquiv_apply, hΦsymm v, map_mul]
    rfl

end Work.Higman
