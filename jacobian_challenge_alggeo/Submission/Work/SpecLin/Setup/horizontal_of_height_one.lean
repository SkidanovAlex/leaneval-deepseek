import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Primes of `A ⊗[K] R` of height one containing a primitive element

Auxiliary commutative algebra: the fibres of `A ⊗[K] R` over the primes of a valuation ring `R`
are domains (the "residue fibre controls the generic fibre" argument, `HorizAux`), and the
assembly of the main theorem `Work.SpecLin.Setup.horizontal_of_height_one`.
-/

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

noncomputable section

namespace Work.SpecLin.Setup.HorizAux

/-- For a `K`-algebra `A` and a domain `R` over the field `K`, the ring `A ⊗_K R` is a domain as
soon as `A ⊗_K Frac R` is: the natural map `A ⊗_K R → A ⊗_K Frac R` is injective, because
`R ↪ Frac R` is injective and `A` is a `K`-vector space, hence flat over the field `K`. -/
theorem isDomain_tensorProduct_fractionRing {K : Type u} [Field K] {A R : Type u} [CommRing A]
    [Algebra K A] [CommRing R] [IsDomain R] [Algebra K R]
    (h : IsDomain (TensorProduct K A (FractionRing R))) : IsDomain (TensorProduct K A R) := by
  haveI : IsDomain (TensorProduct K A (FractionRing R)) := h
  let g : R →ₗ[K] FractionRing R := (IsScalarTower.toAlgHom K R (FractionRing R)).toLinearMap
  have hlin : Function.Injective (TensorProduct.map (LinearMap.id : A →ₗ[K] A) g) :=
    TensorProduct.map_injective_of_flat_flat _ _
      Function.injective_id (IsFractionRing.injective R (FractionRing R))
  let φ : TensorProduct K A R →ₐ[K] TensorProduct K A (FractionRing R) :=
    Algebra.TensorProduct.map (AlgHom.id K A) (IsScalarTower.toAlgHom K R (FractionRing R))
  have key : ∀ z : TensorProduct K A R,
      φ z = TensorProduct.map (LinearMap.id : A →ₗ[K] A) g z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a r => simp [φ, g]
    | add x y hx hy => simp [map_add, hx, hy]
  refine Function.Injective.isDomain φ fun x y hxy ↦ hlin ?_
  rw [← key x, ← key y, hxy]

section Core

variable {K : Type u} [Field K]
variable {A : Type u} [CommRing A] [Algebra K A]
variable {S : Type u} [CommRing S] [IsDomain S] [ValuationRing S] [Algebra K S]
variable {κ : Type u} [CommRing κ] [Algebra K κ] [Nontrivial κ]

/-- **Leading-term extraction.**

For a non-zero element `z` of `A ⊗[K] Frac S` there is `c ≠ 0` in `Frac S` and a "clearing of
denominators" `w ∈ A ⊗[K] S` such that `z = c · w`, with the additional property that the image
of `w` under `A ⊗[K] S → A ⊗[K] κ` is non-zero. -/
theorem exists_eq_mul_of_ne_zero (χ : S →ₐ[K] κ)
    (z : TensorProduct K A (FractionRing S)) (hz : z ≠ 0) :
    ∃ c : FractionRing S, c ≠ 0 ∧ ∃ w : TensorProduct K A S,
      Algebra.TensorProduct.includeRight c *
          (Algebra.TensorProduct.map (AlgHom.id K A)
            (IsScalarTower.toAlgHom K S (FractionRing S))) w = z ∧
      (Algebra.TensorProduct.map (AlgHom.id K A) χ) w ≠ 0 := by
  classical
  -- a `K`-basis of `A`
  let ι : Type u := ↥(Module.Basis.ofVectorSpaceIndex K A)
  let b : Module.Basis ι K A := Module.Basis.ofVectorSpace K A
  -- the `K`-linear identification `A ⊗[K] Frac S ≃ (ι →₀ Frac S)`
  let e : TensorProduct K A (FractionRing S) ≃ₗ[K] ι →₀ FractionRing S :=
    (LinearEquiv.rTensor (FractionRing S) b.repr).trans
      (TensorProduct.finsuppScalarLeft K (FractionRing S) ι)
  have e_tmul : ∀ (i : ι) (m : FractionRing S),
      e (TensorProduct.tmul K (b i) m) = Finsupp.single i m := by
    intro i m
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul, Module.Basis.repr_self]
    ext j
    rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases h : j = i <;> simp [h]
  have e_symm_single : ∀ (i : ι) (m : FractionRing S),
      e.symm (Finsupp.single i m) = TensorProduct.tmul K (b i) m :=
    fun i m => e.symm_apply_eq.mpr (e_tmul i m).symm
  -- the valuation on `Frac S`
  let v := ValuationRing.valuation S (FractionRing S)
  set u : ι →₀ FractionRing S := e z with hu
  have hu_ne : u ≠ 0 := by
    intro h
    exact hz (e.injective (by rw [← hu, h, map_zero]))
  obtain ⟨i₀, hi₀_mem, hi₀_max⟩ :=
    Finset.exists_max_image u.support (fun i => v (u i))
      (Finsupp.support_nonempty_iff.mpr hu_ne)
  set c : FractionRing S := u i₀ with hc_def
  have hc : c ≠ 0 := hc_def ▸ Finsupp.mem_support_iff.mp hi₀_mem
  have hvc_ne : v c ≠ 0 := (Valuation.ne_zero_iff v).mpr hc
  have hvc_pos : 0 < v c := lt_of_le_of_ne zero_le (Ne.symm hvc_ne)
  -- denominators cleared: `u i / c ∈ S`
  have hex : ∀ i : ι, ∃ a : S, algebraMap S (FractionRing S) a = u i / c := by
    intro i
    by_cases hi : i ∈ u.support
    · have hle : v (u i / c) ≤ 1 := by
        rw [Valuation.map_div]
        exact (div_le_one₀ hvc_pos).mpr (hi₀_max i hi)
      exact (ValuationRing.mem_integer_iff S (FractionRing S) (u i / c)).mp
        ((Valuation.mem_integer_iff v (u i / c)).mpr hle)
    · have hui : u i = 0 := by
        by_contra h
        exact hi (Finsupp.mem_support_iff.mpr h)
      exact ⟨0, by rw [map_zero, hui, zero_div]⟩
  let s : ι → S := fun i => Classical.choose (hex i)
  have hs : ∀ i, algebraMap S (FractionRing S) (s i) = u i / c :=
    fun i => Classical.choose_spec (hex i)
  have hφw : (Algebra.TensorProduct.map (AlgHom.id K A)
        (IsScalarTower.toAlgHom K S (FractionRing S)))
        (u.support.sum (fun i => TensorProduct.tmul K (b i) (s i)))
      = u.support.sum (fun i => TensorProduct.tmul K (b i) (u i / c)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.toAlgHom_apply, hs i]
  have hz_repr : z = u.support.sum (fun i => TensorProduct.tmul K (b i) (u i)) := by
    have h1 : z = e.symm u := by rw [hu, LinearEquiv.symm_apply_apply]
    rw [h1]
    have hu_sum : u = u.support.sum (fun i => Finsupp.single i (u i)) := by
      simpa only [Finsupp.sum] using (Finsupp.sum_single u).symm
    conv_lhs => rw [hu_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e_symm_single]
  -- the coefficient functional on `A ⊗[K] κ`
  let lam : ι → A →ₗ[K] K := fun i => (Finsupp.lapply i).comp b.repr.toLinearMap
  have lam_apply : ∀ i j : ι, lam i (b j) = if i = j then (1 : K) else 0 := by
    intro i j
    change (b.repr (b j)) i = if i = j then (1 : K) else 0
    rw [Module.Basis.repr_self_apply b j i]
    by_cases h : i = j <;> simp [h, eq_comm]
  let coeff : ι → TensorProduct K A κ →ₗ[K] κ := fun i =>
    (TensorProduct.lid K κ).toLinearMap.comp ((lam i).rTensor κ)
  have coeff_tmul : ∀ (i j : ι) (d : κ),
      coeff i (TensorProduct.tmul K (b j) d) = (if i = j then (1 : K) else 0) • d := by
    intro i j d
    simp only [coeff, LinearMap.comp_apply, LinearMap.rTensor_tmul, lam_apply]
    by_cases h : i = j
    · rw [if_pos h]
      exact TensorProduct.lid_tmul d (1 : K)
    · rw [if_neg h]
      exact TensorProduct.lid_tmul d (0 : K)
  have hsi₀ : s i₀ = 1 := by
    apply IsFractionRing.injective S (FractionRing S)
    rw [hs i₀, map_one]
    rw [← hc_def]
    exact div_self hc
  have hcoeff : coeff i₀ ((Algebra.TensorProduct.map (AlgHom.id K A) χ)
      (u.support.sum (fun i => TensorProduct.tmul K (b i) (s i)))) = 1 := by
    rw [map_sum, map_sum]
    rw [Finset.sum_eq_single i₀]
    · rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coeff_tmul, if_pos rfl, one_smul,
        hsi₀, map_one]
    · intro j _ hj
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, coeff_tmul, if_neg (Ne.symm hj),
        zero_smul]
    · intro h
      exact absurd hi₀_mem h
  refine ⟨c, hc, u.support.sum (fun i => TensorProduct.tmul K (b i) (s i)), ?_, ?_⟩
  · rw [hz_repr, hφw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_div_cancel₀ _ hc]
  · intro hzero
    have h01 : (0 : κ) = 1 := by rw [← hcoeff, hzero, map_zero]
    exact one_ne_zero h01.symm

end Core

section Main

variable {K : Type u} [Field K]
variable {A : Type u} [CommRing A] [Algebra K A]
variable {S : Type u} [CommRing S] [IsDomain S] [ValuationRing S] [Algebra K S]
variable {κ : Type u} [CommRing κ] [Algebra K κ] [Nontrivial κ]

/-- **The residue fibre controls the generic fibre.**

If `A ⊗[K] κ` is a domain for a `K`-algebra homomorphism `S → κ` from a valuation ring `S` over
`K`, then `A ⊗[K] Frac S` is a domain. -/
theorem isDomain_tensorProduct_fractionRing_of_algHom
    (hκ : IsDomain (TensorProduct K A κ)) (χ : S →ₐ[K] κ) :
    IsDomain (TensorProduct K A (FractionRing S)) := by
  classical
  haveI : Nontrivial (TensorProduct K A κ) := hκ.toNontrivial
  -- `A` is non-trivial
  haveI hA : Nontrivial A := by
    refine ⟨0, 1, fun h01 => ?_⟩
    have hone : (1 : TensorProduct K A κ) = 0 := by
      rw [Algebra.TensorProduct.one_def,
        ← Algebra.TensorProduct.includeLeft_apply (R := K) (S := K) (A := A) (B := κ) 1,
        ← h01, Algebra.TensorProduct.includeLeft_apply (R := K) (S := K) (A := A) (B := κ),
        TensorProduct.zero_tmul]
    exact one_ne_zero hone
  -- hence `A ⊗[K] Frac S` is non-trivial
  haveI : Nontrivial (TensorProduct K A (FractionRing S)) := by
    have hflat : Function.Injective (LinearMap.lTensor A (Algebra.linearMap K (FractionRing S))) :=
      Module.Flat.lTensor_preserves_injective_linearMap (Algebra.linearMap K (FractionRing S))
        (RingHom.injective (algebraMap K (FractionRing S)))
    exact hflat.nontrivial
  -- injectivity of the localisation map `A ⊗[K] S → A ⊗[K] Frac S`
  have hψinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id K A)
      (IsScalarTower.toAlgHom K S (FractionRing S))) := by
    have hf : Function.Injective
        ((IsScalarTower.toAlgHom K S (FractionRing S)).toLinearMap) := by
      show Function.Injective (fun x => algebraMap S (FractionRing S) x)
      exact IsFractionRing.injective S (FractionRing S)
    have hlin : Function.Injective
        (LinearMap.lTensor A ((IsScalarTower.toAlgHom K S (FractionRing S)).toLinearMap)) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hf
    have hEq : (Algebra.TensorProduct.map (AlgHom.id K A)
          (IsScalarTower.toAlgHom K S (FractionRing S))).toLinearMap
        = LinearMap.lTensor A ((IsScalarTower.toAlgHom K S (FractionRing S)).toLinearMap) := by
      apply TensorProduct.ext'
      intro a s
      simp only [AlgHom.toLinearMap_apply, LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
    intro x y hxy
    apply hlin
    rw [← hEq]
    exact hxy
  haveI hNZ : NoZeroDivisors (TensorProduct K A κ) :=
    (isDomain_iff_noZeroDivisors_and_nontrivial _).mp hκ |>.1
  rw [isDomain_iff_noZeroDivisors_and_nontrivial]
  refine ⟨⟨fun {x y} hxy => ?_⟩, inferInstance⟩
  by_contra h
  rw [not_or] at h
  obtain ⟨hx, hy⟩ := h
  obtain ⟨c, hc, w, hw, hρw⟩ := exists_eq_mul_of_ne_zero (K := K) (A := A) (S := S) (κ := κ) χ x hx
  obtain ⟨c', hc', w', hw', hρw'⟩ :=
    exists_eq_mul_of_ne_zero (K := K) (A := A) (S := S) (κ := κ) χ y hy
  have hkey : Algebra.TensorProduct.includeRight (c * c') *
      (Algebra.TensorProduct.map (AlgHom.id K A)
        (IsScalarTower.toAlgHom K S (FractionRing S))) (w * w') = 0 := by
    have h1 : Algebra.TensorProduct.includeRight (c * c') =
        Algebra.TensorProduct.includeRight c * Algebra.TensorProduct.includeRight c' :=
      map_mul (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := FractionRing S)) c c'
    have h2 : (Algebra.TensorProduct.map (AlgHom.id K A)
        (IsScalarTower.toAlgHom K S (FractionRing S))) (w * w')
        = (Algebra.TensorProduct.map (AlgHom.id K A)
            (IsScalarTower.toAlgHom K S (FractionRing S))) w
          * (Algebra.TensorProduct.map (AlgHom.id K A)
            (IsScalarTower.toAlgHom K S (FractionRing S))) w' :=
      map_mul _ w w'
    rw [h1, h2]
    calc (Algebra.TensorProduct.includeRight c * Algebra.TensorProduct.includeRight c')
          * ((Algebra.TensorProduct.map (AlgHom.id K A)
              (IsScalarTower.toAlgHom K S (FractionRing S))) w
            * (Algebra.TensorProduct.map (AlgHom.id K A)
              (IsScalarTower.toAlgHom K S (FractionRing S))) w')
        = (Algebra.TensorProduct.includeRight c
            * (Algebra.TensorProduct.map (AlgHom.id K A)
              (IsScalarTower.toAlgHom K S (FractionRing S))) w)
          * (Algebra.TensorProduct.includeRight c'
            * (Algebra.TensorProduct.map (AlgHom.id K A)
              (IsScalarTower.toAlgHom K S (FractionRing S))) w') := by ring
      _ = x * y := by rw [hw, hw']
      _ = 0 := hxy
  have hcc : c * c' ≠ 0 := mul_ne_zero hc hc'
  have hww : (Algebra.TensorProduct.map (AlgHom.id K A)
      (IsScalarTower.toAlgHom K S (FractionRing S))) (w * w') = 0 := by
    have h1 : Algebra.TensorProduct.includeRight (c * c') =
        algebraMap (FractionRing S) (TensorProduct K A (FractionRing S)) (c * c') := by
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.right_algebraMap_apply]
    rw [h1, ← Algebra.smul_def] at hkey
    rcases (smul_eq_zero.mp hkey) with h | h
    · exact absurd h hcc
    · exact h
  have hww' : w * w' = 0 := by
    apply hψinj
    rw [hww, map_zero]
  have hzero : (Algebra.TensorProduct.map (AlgHom.id K A) χ) w
      * (Algebra.TensorProduct.map (AlgHom.id K A) χ) w' = 0 := by
    rw [← map_mul, hww', map_zero]
  exact (mul_ne_zero hρw hρw') hzero

end Main

/-- **Fibres of `A ⊗[K] R` over the primes of a valuation ring `R` are domains.**

Let `K` be a field, `R` a valuation ring which is a `K`-algebra, `κ = R ⧸ 𝔪_R` its residue field
and `A` a `K`-algebra such that `A ⊗[K] κ` is a domain.  Then for **every** prime `𝔮` of `R` the
fibre `A ⊗[K] (R ⧸ 𝔮)` is a domain as well.

(`𝔮 = ⊥` gives the generic fibre `A ⊗[K] R`; `𝔮 = 𝔪_R` gives `A ⊗[K] κ`, which is the hypothesis.)

Proof sketch: `R ⧸ 𝔮` is a valuation ring (a quotient of a valuation ring by a prime) with fraction
field `L = Frac (R ⧸ 𝔮)` and residue field `κ`, so it suffices that `A ⊗[K] L` is a domain (then
`A ⊗[K] (R ⧸ 𝔮) ↪ A ⊗[K] L` by flatness of `A` over the field `K`).  For this, replace `A` by the
field `F := Frac A` (so that `F ⊗[K] κ` is still a domain, being the fraction field of the domain
`A ⊗[K] κ`) and use the *initial form* argument: choose a `K`-basis `{f_i}` of `F`, let
`v` be the valuation of the valuation ring `R ⧸ 𝔮` (trivial on `K ⊆ R ⧸ 𝔮`); every `z ∈ F ⊗[K] L`
is uniquely `Σ_i f_i ⊗ m_i`, and the "leading component"
`ℓ(z) := Σ_{i : v(m_i) minimal} f_i ⊗ (m_i/π)̄ ∈ F ⊗[K] κ` is non-zero for `z ≠ 0`, and the
level-`(γ+γ')` component of a product `ℓ(zz')` equals `ℓ(z)ℓ(z')`, because the residues `(m_i/π)̄`
of the leading coefficients are units of `κ` and `F ⊗[K] κ` is a domain.  Hence a zero divisor in
`F ⊗[K] L` produces one in `F ⊗[K] κ`. -/
theorem isDomain_tensor_quotientPrime {K : Type u} [Field K] (R : Type u) [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra K R] (A : Type u) [CommRing A] [Algebra K A]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (𝔮 : Ideal R) [𝔮.IsPrime] :
    IsDomain (TensorProduct K A (R ⧸ 𝔮)) := by
  haveI : IsDomain (R ⧸ 𝔮) := Ideal.Quotient.isDomain 𝔮
  haveI : IsLocalRing (R ⧸ 𝔮) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective
  haveI : PreValuationRing (R ⧸ 𝔮) := ⟨fun a b => by
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨c', hc'⟩ := ValuationRing.cond a' b'
    refine ⟨Ideal.Quotient.mk 𝔮 c', ?_⟩
    rcases hc' with h | h
    · exact Or.inl (by simpa using congrArg (Ideal.Quotient.mk 𝔮) h)
    · exact Or.inr (by simpa using congrArg (Ideal.Quotient.mk 𝔮) h)⟩
  haveI : ValuationRing (R ⧸ 𝔮) := ValuationRing.mk
  have hle : 𝔮 ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹𝔮.IsPrime›)
  -- the residue map `R ⧸ 𝔮 → R ⧸ 𝔪_R` as a `K`-algebra homomorphism
  have hχ : (R ⧸ 𝔮) →ₐ[K] IsLocalRing.ResidueField R :=
    Ideal.Quotient.liftₐ 𝔮
      (AlgHom.mk (IsLocalRing.residue R) (fun k => by
        rw [IsScalarTower.algebraMap_apply K R (IsLocalRing.ResidueField R)]
        rfl))
      (fun a ha => (IsLocalRing.residue_eq_zero_iff a).mpr (hle ha))
  have hfrac : IsDomain (TensorProduct K A (FractionRing (R ⧸ 𝔮))) :=
    isDomain_tensorProduct_fractionRing_of_algHom (K := K) (A := A) (S := R ⧸ 𝔮)
      (κ := IsLocalRing.ResidueField R) inferInstance hχ
  exact isDomain_tensorProduct_fractionRing (K := K) (A := A) (R := R ⧸ 𝔮) hfrac

end Work.SpecLin.Setup.HorizAux


namespace Work.SpecLin.Setup

open scoped TensorProduct

/-- In a domain, a non-zero prime ideal contained in a prime ideal of height one is equal to it. -/
theorem eq_of_le_of_ne_bot_of_height_eq_one_aux {S : Type u} [CommRing S] [IsDomain S]
    {p q : Ideal S} [p.IsPrime] [q.IsPrime] (hpq : p ≤ q) (hp : p ≠ ⊥) (hq : q.height = 1) :
    p = q := by
  have hle : p.height ≤ q.height := Ideal.height_mono hpq
  have hp1 : (1 : ℕ∞) ≤ p.height := by
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact hp (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have hpeq : p.height = 1 := le_antisymm (by rw [hq] at hle; exact hle) hp1
  haveI : p.FiniteHeight := by
    rw [Ideal.finiteHeight_iff, hpeq]
    exact Or.inr (by simp)
  exact Ideal.eq_of_le_of_height_le p hpq (by rw [hq, hpeq])

/-- For a prime `𝔮` of `R`, the ideal `𝔮 · B` of `B = A ⊗[K] R` is prime as soon as the fibre
`A ⊗[K] (R ⧸ 𝔮)` is a domain (it is then the kernel of `B → A ⊗[K] (R ⧸ 𝔮)`). -/
theorem isPrime_map_includeRight_aux {K : Type u} [Field K] (A : Type u) [CommRing A]
    [Algebra K A] (R : Type u) [CommRing R] [Algebra K R] (𝔮 : Ideal R) [𝔮.IsPrime]
    [IsDomain (TensorProduct K A (R ⧸ 𝔮))] :
    (𝔮.map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))).IsPrime := by
  have e : TensorProduct K A (R ⧸ 𝔮) ≃+*
      TensorProduct K A R ⧸
        Ideal.map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) 𝔮 :=
    (Algebra.TensorProduct.tensorQuotientEquiv (R := K) (S := K) (T := R) (A := A) 𝔮).toRingEquiv
  exact (Ideal.Quotient.isDomain_iff_prime _).mp ((MulEquiv.isDomain_iff e.toMulEquiv).mp ‹_›)

/-- A prime of `B = A ⊗[K] R` of height one containing a primitive element `u` (i.e.
`u ∉ 𝔪_R·B`) lies over the generic point of `Spec R`: its contraction to `R` is `⊥`.

Suppose `𝔭 := q.comap includeRight ≠ ⊥`.  Then `𝔭` is a nonzero prime of `R`, hence `𝔭 ⊆ 𝔪_R`,
and `𝔭·B ≠ ⊥` (the map `R → B` is injective, `B` a domain) is contained in `q`.  Every prime
strictly below the height-one prime `q` has height `0` and therefore equals `⊥` (a domain has a
unique height-zero prime), so any prime `P` with `𝔭·B ⊆ P ⊆ q` satisfies `P = q`.  Applying this
to a minimal prime over `𝔭·B` contained in `q`, the ideal `𝔭·B` has a prime minimal over it inside
`q`, which must be `q` itself; the height-one chain argument then forces `q = 𝔭·B` (a strict
inclusion would exhibit the length-two chain `⊥ ⊊ P ⊊ q`), and then
`u ∈ q = 𝔭·B ⊆ 𝔪_R·B`, contradicting `hu`. -/
theorem horizontal_of_height_one {K : Type u} [Field K] (A : Type u) [CommRing A] [IsDomain A]
    [Algebra K A] [Algebra.FiniteType K A] [Algebra.Smooth K A] [Ring.KrullDimLE 1 A]
    (hA : ¬ Ring.KrullDimLE 0 A)
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    [IsDomain (TensorProduct K A R)]
    [IsDomain (TensorProduct K A (IsLocalRing.ResidueField R))]
    (q : Ideal (TensorProduct K A R)) (hq : q.IsPrime) (hq1 : q.height = 1)
    (u : TensorProduct K A R)
    (hu : u ∉ (IsLocalRing.maximalIdeal R).map
      (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)))
    (huq : u ∈ q) :
    q.comap (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) = ⊥ := by
  classical
  -- The mathematical content: with `𝔭 = q ∩ R ≠ ⊥` the fibre `A ⊗[K] (R ⧸ 𝔭)` is a domain -- this
  -- is where the hypothesis that the *closed* fibre `A ⊗[K] κ` (`κ = R ⧸ 𝔪_R`) is a domain enters,
  -- via `HorizAux.isDomain_tensor_quotientPrime`, and it is what makes `𝔭 · B` a prime.  Since
  -- `𝔭 · B ≤ q`, `𝔭 · B ≠ ⊥` and `q.height = 1`, the height-one criterion forces `𝔭 · B = q`, and
  -- then `u ∈ q = 𝔭 · B ⊆ 𝔪_R · B`, contradicting `hu`.
  by_contra hne
  set ι := Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R) with hι
  change q.comap ι ≠ ⊥ at hne
  haveI hq' : q.IsPrime := hq
  -- `R → B` is injective because `A ≠ 0` and `R` is flat over the field `K`
  have hinj : Function.Injective ι := by
    rw [hι]
    exact Algebra.TensorProduct.includeRight_injective
      (FaithfulSMul.algebraMap_injective K A)
  -- the contraction `𝔭 = q ∩ R`
  set 𝔭 : Ideal R := q.comap ι with h𝔭
  have hne𝔭 : 𝔭 ≠ ⊥ := by rw [h𝔭]; exact hne
  haveI h𝔭prime : 𝔭.IsPrime := h𝔭.symm ▸ Ideal.IsPrime.comap ι
  -- the fibre over `𝔭` is a domain, so `𝔭 · B` is a prime
  haveI hdom : IsDomain (TensorProduct K A (R ⧸ 𝔭)) :=
    HorizAux.isDomain_tensor_quotientPrime (K := K) R A 𝔭
  haveI hpr : (𝔭.map ι).IsPrime := isPrime_map_includeRight_aux A R 𝔭
  -- `𝔭 · B ≠ ⊥` and `𝔭 · B ≤ q`, so `𝔭 · B = q` by the height-one criterion
  have hle : 𝔭.map ι ≤ q := by
    rw [Ideal.map_le_iff_le_comap, h𝔭]
  have hneq : 𝔭.map ι ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff 𝔭).mp hne𝔭
    have hm : ι a ∈ (⊥ : Ideal (TensorProduct K A R)) := hbot ▸ Ideal.mem_map_of_mem ι ha
    rw [Ideal.mem_bot] at hm
    exact ha0 (hinj (hm.trans (map_zero ι).symm))
  have heq : 𝔭.map ι = q := eq_of_le_of_ne_bot_of_height_eq_one_aux hle hneq hq1
  -- then `u ∈ 𝔭 · B ⊆ 𝔪_R · B`, contradicting the hypothesis
  refine hu ?_
  have h𝔭le : 𝔭 ≤ IsLocalRing.maximalIdeal R := IsLocalRing.le_maximalIdeal_of_isPrime 𝔭
  have hu' : u ∈ 𝔭.map ι := by rw [heq]; exact huq
  exact Ideal.map_mono h𝔭le hu'

end Work.SpecLin.Setup
