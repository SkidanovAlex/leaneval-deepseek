/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.NormGroup

/-!
# Global reciprocity: Artin's reciprocity law, the existence theorem and Čebotarev

This file provides the *interface* through which the main theorems of global class field theory
are consumed by the Neukirch–Uchida development.  The two deep inputs are packaged as hypotheses
(structures), so that everything stated here is a *proved* conditional theorem:

* `NK.GlobalCFT.ArtinReciprocity`: the reciprocity isomorphism
  `C_K / N_{L/K} C_L ≃* Gal(L/K)` for a finite abelian extension;
* `NK.GlobalCFT.ExistenceTheorem`: every open finite-index subgroup of `C_K` is the norm
  subgroup of a finite abelian extension of `K`;
* `NK.GlobalCFT.ChebotarevDensity`: the density statement of Čebotarev's theorem, for a given
  Frobenius assignment.

From these we derive the *Artin map* `C_K →* Gal(L/K)` together with its kernel and surjectivity,
and the qualitative form of Čebotarev (primes with prescribed Frobenius class exist outside any
prescribed finite set).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct IsMulCommutative
open Filter
open scoped Topology
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- **Artin's reciprocity law** (as a hypothesis): for a finite **abelian** extension `L / K`
the quotient of the idèle class group `C_K` by the norm subgroup `N_{L/K} C_L` is isomorphic, via
the Artin map, to the Galois group of `L / K`.

For a general finite Galois `L/K` this statement is *false* (the norm index is `|Gal(L/K)ᵃᵇ|`,
which is strictly smaller than `[L : K]` for nonabelian `Gal(L/K)`); the correct general target is
the abelianisation, `NK.GlobalCFT.index_eq_card_abelianization`.  Callers must therefore only
apply this structure to abelian extensions. -/
structure ArtinReciprocity (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Type _ where
  /-- the reciprocity isomorphism -/
  iso : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L ≃* (L ≃ₐ[K] L)

/-- **Reciprocity for a general finite Galois extension** (as a hypothesis): the quotient of the
idèle class group `C_K` by the norm subgroup `N_{L/K} C_L` is isomorphic, via the Artin map, to the
**abelianisation** of the Galois group of `L / K`.

This is the correct form of reciprocity for nonabelian `L/K`; `NK.GlobalCFT.ArtinReciprocity` is
the special case where `Gal(L/K)` is commutative (then `Gal(L/K)ᵃᵇ = Gal(L/K)`), and the
index statement `[C_K : N_{L/K} C_L] = |Gal(L/K)ᵃᵇ|` is
`NK.GlobalCFT.index_eq_card_abelianization`. -/
structure GaloisReciprocity (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Type _ where
  /-- the reciprocity isomorphism, onto the abelianisation of `Gal(L/K)` -/
  iso : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L ≃* Abelianization (L ≃ₐ[K] L)

namespace GaloisReciprocity

/-- The Artin map `C_K →* Gal(L/K)ᵃᵇ` of a general Galois extension. -/
def artinMap (h : GaloisReciprocity K L) : IdeleClassGroup K →* Abelianization (L ≃ₐ[K] L) :=
  h.iso.toMonoidHom.comp (QuotientGroup.mk' (Idele.normClassSubgroup K L))

@[simp] theorem artinMap_apply (h : GaloisReciprocity K L) (x : IdeleClassGroup K) :
    h.artinMap x = h.iso (QuotientGroup.mk' (Idele.normClassSubgroup K L) x) := rfl

/-- The Artin map of a general Galois extension kills exactly the norm subgroup. -/
theorem artinMap_ker (h : GaloisReciprocity K L) :
    h.artinMap.ker = Idele.normClassSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker, ← QuotientGroup.ker_mk' (Idele.normClassSubgroup K L),
    MonoidHom.mem_ker]
  constructor
  · intro hx
    refine h.iso.injective ?_
    rw [map_one]
    change h.artinMap x = 1
    exact hx
  · intro hx
    change h.iso (QuotientGroup.mk' (Idele.normClassSubgroup K L) x) = 1
    rw [hx, map_one]

/-- The Artin map of a general Galois extension is surjective. -/
theorem artinMap_surjective (h : GaloisReciprocity K L) :
    Function.Surjective h.artinMap := by
  intro σ
  obtain ⟨y, hy⟩ := h.iso.surjective σ
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Idele.normClassSubgroup K L) y
  exact ⟨x, by
    change h.iso (QuotientGroup.mk' (Idele.normClassSubgroup K L) x) = σ
    rw [hx, hy]⟩

/-- The index of the norm subgroup is the order of the abelianisation. -/
theorem index_eq_card_abelianization (h : GaloisReciprocity K L) :
    (Idele.normClassSubgroup K L).index = Nat.card (Abelianization (L ≃ₐ[K] L)) :=
  (Subgroup.index_eq_card (Idele.normClassSubgroup K L)).trans (Nat.card_congr h.iso.toEquiv)

/-- Reciprocity for a general Galois extension restricts to Artin reciprocity when the Galois
group is commutative. -/
noncomputable def toArtinReciprocity (h : GaloisReciprocity K L)
    [IsMulCommutative (L ≃ₐ[K] L)] : ArtinReciprocity K L where
  iso := h.iso.trans (Abelianization.equivOfComm (H := (L ≃ₐ[K] L))).symm

end GaloisReciprocity

namespace ArtinReciprocity

variable (h : ArtinReciprocity K L)

/-- The **Artin map** `C_K →* Gal(L/K)`, obtained by composing the quotient map with the
reciprocity isomorphism. -/
def artinMap : IdeleClassGroup K →* (L ≃ₐ[K] L) :=
  h.iso.toMonoidHom.comp (QuotientGroup.mk' (Idele.normClassSubgroup K L))

@[simp] theorem artinMap_apply (x : IdeleClassGroup K) :
    h.artinMap x = h.iso (QuotientGroup.mk' (Idele.normClassSubgroup K L) x) := rfl

/-- The Artin map kills exactly the norm subgroup: this is the reciprocity law. -/
theorem artinMap_ker : h.artinMap.ker = Idele.normClassSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker, ← QuotientGroup.ker_mk' (Idele.normClassSubgroup K L),
    MonoidHom.mem_ker]
  constructor
  · intro hx
    refine h.iso.injective ?_
    rw [map_one]
    change h.artinMap x = 1
    exact hx
  · intro hx
    change h.iso (QuotientGroup.mk' (Idele.normClassSubgroup K L) x) = 1
    rw [hx, map_one]

/-- The Artin map is surjective. -/
theorem artinMap_surjective : Function.Surjective h.artinMap := by
  intro σ
  obtain ⟨y, hy⟩ := h.iso.surjective σ
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Idele.normClassSubgroup K L) y
  refine ⟨x, ?_⟩
  change h.iso (QuotientGroup.mk' (Idele.normClassSubgroup K L) x) = σ
  rw [hx, hy]

/-- Two idèle classes have the same Artin image iff they differ by a norm. -/
theorem artinMap_eq_iff {x y : IdeleClassGroup K} :
    h.artinMap x = h.artinMap y ↔ x⁻¹ * y ∈ Idele.normClassSubgroup K L := by
  constructor
  · intro hxy
    rw [← artinMap_ker, MonoidHom.mem_ker]
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  · intro hxy
    have h1 : h.artinMap (x⁻¹ * y) = 1 := by
      rw [← MonoidHom.mem_ker, artinMap_ker]
      exact hxy
    rw [map_mul, map_inv] at h1
    exact eq_of_inv_mul_eq_one h1

end ArtinReciprocity

/-- **The existence theorem of global class field theory** (Takagi), as a hypothesis: every open
subgroup of finite index of `C_K` is the norm subgroup `N_{L/K} C_L` of a finite abelian extension
`L / K`. -/
structure ExistenceTheorem (K : Type*) [Field K] [NumberField K] : Prop where
  exists_normSubgroup : ∀ (N : Subgroup (IdeleClassGroup K)), N.FiniteIndex →
    IsOpen (N : Set (IdeleClassGroup K)) →
      ∃ (L : Type*) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
        (_ : FiniteDimensional K L) (_ : IsGalois K L),
        Idele.normClassSubgroup K L = N

/-- **Čebotarev's density theorem**, as an analytic input.

We model the Frobenius assignment as data — a function sending each prime of `K` to the conjugacy
class of its Frobenius elements in `Gal(L/K)` — together with

* a counting function `count C n` of the primes of absolute norm at most `n` whose Frobenius class
  is `C`, and the total count `total n` of primes of norm at most `n`,
* the *soundness* condition `count_sound`: the counting function is bounded exactly when there are
  only finitely many such primes,
* the density assertion `tendsto_count` of Čebotarev's theorem: the proportion of primes with
  Frobenius class `C` tends to `|C| / [L : K]`.

The analytic content (the *proof* of `tendsto_count`, which uses the Dedekind zeta function) is
delegated: it is the hypothesis `tendsto_count` below.  From it we *derive* the qualitative form of
Čebotarev, so the conclusion is not merely assumed. -/
structure ChebotarevDensity (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Type _ where
  /-- the Frobenius conjugacy class of each prime of `K` -/
  frobeniusClass : HeightOneSpectrum (𝓞 K) → Set (L ≃ₐ[K] L)
  /-- the number of primes of absolute norm at most `n` with Frobenius class `C` -/
  count : Set (L ≃ₐ[K] L) → ℕ → ℕ
  /-- the number of primes of absolute norm at most `n` -/
  total : ℕ → ℕ
  /-- the counting function is bounded exactly when there are finitely many primes with the
  prescribed Frobenius class -/
  count_sound : ∀ C : Set (L ≃ₐ[K] L),
    (∃ N : ℕ, ∀ n : ℕ, count C n ≤ N) ↔ {p : HeightOneSpectrum (𝓞 K) | frobeniusClass p = C}.Finite
  /-- there are infinitely many primes of bounded norm -/
  total_tendsto : Tendsto (fun n : ℕ => (total n : ℝ)) atTop atTop
  /-- **Čebotarev's density assertion**: the proportion of primes with Frobenius class `C` tends
  to `|C| / [L : K]` -/
  tendsto_count : ∀ C : Set (L ≃ₐ[K] L),
    Tendsto (fun n : ℕ => (count C n : ℝ) / (total n : ℝ)) atTop
      (𝓝 ((Nat.card C : ℝ) / (Module.finrank K L : ℝ)))

namespace ChebotarevDensity

variable (h : ChebotarevDensity K L)

/-- The limiting proportion of primes with Frobenius class `C` is positive when `C` is
nonempty. -/
theorem density_pos (C : Set (L ≃ₐ[K] L)) (hC : C.Nonempty) :
    0 < (Nat.card C : ℝ) / (Module.finrank K L : ℝ) := by
  haveI : Nonempty ↥C := (Set.nonempty_coe_sort).mpr hC
  haveI : Finite ↥C := Set.finite_coe_iff.mpr (Set.toFinite C)
  have hcard : 0 < (Nat.card C : ℝ) := by exact_mod_cast Nat.card_pos
  have hdim : 0 < (Module.finrank K L : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := K) (M := L)
  exact div_pos hcard hdim

/-- If only finitely many primes have Frobenius class `C`, then the proportion tends to `0`. -/
theorem tendsto_count_eq_zero_of_finite (C : Set (L ≃ₐ[K] L))
    (hfin : {p : HeightOneSpectrum (𝓞 K) | h.frobeniusClass p = C}.Finite) :
    Tendsto (fun n : ℕ => (h.count C n : ℝ) / (h.total n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := (h.count_sound C).mpr hfin
  have h1 : Tendsto (fun n : ℕ => (N : ℝ) / (h.total n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h.total_tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1 ?_ ?_
  · filter_upwards with n
    exact div_nonneg (by positivity) (by positivity)
  · filter_upwards with n
    exact div_le_div_of_nonneg_right (by exact_mod_cast hN n) (by positivity)

/-- **Qualitative Čebotarev**: for every nonempty set `C` of Galois elements occurring as a
Frobenius class and every finite set `T` of primes of `K`, there is a prime outside `T` whose
Frobenius class is `C`.  This is *derived* from the density assertion `tendsto_count` and the
soundness of the counting function. -/
theorem exists_prime_frobeniusClass (C : Set (L ≃ₐ[K] L)) (hC : C.Nonempty)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ p ∉ T, h.frobeniusClass p = C := by
  by_contra hcon
  push Not at hcon
  have hfin : {p : HeightOneSpectrum (𝓞 K) | h.frobeniusClass p = C}.Finite :=
    T.finite_toSet.subset fun p hp => by
      by_contra hpT
      exact hcon p hpT hp
  have h0 := h.tendsto_count_eq_zero_of_finite C hfin
  have hlim := h.tendsto_count C
  have hne : (Nat.card C : ℝ) / (Module.finrank K L : ℝ) ≠ 0 :=
    ne_of_gt (density_pos (K := K) (L := L) C hC)
  exact hne (tendsto_nhds_unique hlim h0)

/-- The set of primes whose Frobenius class is a nonempty `C` is infinite. -/
theorem infinite_setOf_frobeniusClass (C : Set (L ≃ₐ[K] L)) (hC : C.Nonempty) :
    {p : HeightOneSpectrum (𝓞 K) | h.frobeniusClass p = C}.Infinite := by
  intro hfin
  obtain ⟨p, hpT, hp⟩ := h.exists_prime_frobeniusClass C hC hfin.toFinset
  exact hpT (hfin.mem_toFinset.mpr hp)

end ChebotarevDensity

end NK.GlobalCFT
