import Mathlib
import Submission.Work.CharPrelim.finrank_invariants_ge_of_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharPrelim.finrank_invariants_ge_of_general_mfr`

Feit--Thompson 3.16 (iii) in fixed-point-dimension form, for an **arbitrary** (not necessarily
irreducible) representation.

Let `k` be an algebraically closed field of characteristic a prime `p`, let `G` be a finite group
with `p ∤ |G|`, let `K ⊴ G` and `E ≤ G` with `K ⊓ E = ⊥`, `K ⊔ E = ⊤` and `C_G(k') ≤ K` for every
`1 ≠ k' ∈ K` (i.e. `G = K ⋊ E` is a Frobenius group with kernel `K`), and let `ρ` be a
`k`-representation of `G` on a finite-dimensional space `V` with `K ⊄ ker ρ`.  Then for every
`E₀ ≤ E`,

  `[E : E₀] ≤ dim_k V^{E₀}`.

The irreducible case is `Work.CharPrelim.finrank_invariants_ge_of_irreducible`.  For the general
case we do not decompose `ρ` into irreducibles: instead we keep only the part of `V` that the
argument actually uses.

* Since `p ∤ |K|`, the `k[K]`-module `V` is semisimple, and `Z := V^K` is a `K`-stable submodule
  with `Z ≠ V` (else `K ≤ ker ρ`).  Taking a `K`-stable complement `C` of `Z` and a nonzero
  `K`-simple `K`-stable `U ≤ C` (Lemma `exists_simple_stable_le`), we get `U^K = U ∩ Z = 0`:
  this is the `U` on which the modular form of 3.16 (iii) applies
  (`exists_simple_invariants_bot`).
* The `E`-conjugates `ρ h • U` of `U` are pairwise independent as `k`-modules
  (`iSupIndep_map_rho_general`, the generalisation of `iSupIndep_map_rho` in which irreducibility
  of `ρ` is replaced by the vanishing of the `K`-fixed space of `U`), and `E` permutes them
  regularly.
* The orbit sums over a transversal of a subgroup `E₀ ≤ E` are `E₀`-fixed and linearly
  independent, giving `[E : E₀] ≤ dim V^{E₀}`
  (`relIndex_le_finrank_invariants_of_iSupIndep_permuted_general`, which drops the unused
  "spanning" hypothesis of `relIndex_le_finrank_invariants_of_iSupIndep_permuted`).

This module is a self-contained variant of the development in
`Submission/Work/CharPrelim/finrank_invariants_ge_of_general.lean`, placed in the namespace
`Work.CharPrelim.MFR` so that the two coexist; the target theorem only imports this one.  The
only difference is the irreducibility-free form `subrepresentation_isIrreducible_mfr`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Classical
open scoped Pointwise
open scoped QuotientGroup

namespace Work.CharPrelim.MFR

/-- `Work.CharPrelim.subrepresentation_isIrreducible` without any irreducibility hypothesis on
`ρ`: only the `K`-simplicity of `U` is used. -/
lemma subrepresentation_isIrreducible_mfr {L : Type*} [Field L] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module L V] (ρ : Representation L G V) {K : Subgroup G}
    {U : Submodule L V} (hU : U ≠ ⊥) (hstab : IsStableUnder ρ K U)
    (hsimp : ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U) :
    (Representation.subrepresentation (ρ.comp K.subtype) U hstab).IsIrreducible := by
  classical
  set ρU := Representation.subrepresentation (ρ.comp K.subtype) U hstab
  haveI hUnt : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.mpr hU
  haveI : Nontrivial (Subrepresentation ρU) :=
    ⟨⊥, ⊤, by
      intro h
      have h2 : (⊥ : Submodule L ↥U) = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact absurd h2 (by simp)⟩
  refine IsSimpleOrder.mk fun A => ?_
  have hle : A.toSubmodule.map U.subtype ≤ U := Submodule.map_subtype_le U A.toSubmodule
  have hstabW : IsStableUnder ρ K (A.toSubmodule.map U.subtype) := by
    intro k x hx
    rw [Submodule.mem_comap]
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨ρU k u, A.apply_mem_toSubmodule k hu, by
      simp [ρU, Representation.subrepresentation, LinearMap.restrict_apply]⟩
  by_cases hW : A.toSubmodule.map U.subtype = ⊥
  · left
    have hA : A.toSubmodule = ⊥ :=
      Submodule.map_injective_of_injective U.subtype_injective (by simp [hW])
    exact Subrepresentation.toSubmodule_injective (by rw [hA]; rfl)
  · right
    have hWU : A.toSubmodule.map U.subtype = U := hsimp _ hle hstabW hW
    have hA : A.toSubmodule = ⊤ :=
      Submodule.map_injective_of_injective U.subtype_injective
        (by rw [hWU, Submodule.map_subtype_top])
    exact Subrepresentation.toSubmodule_injective (by rw [hA]; rfl)


section SimpleLe

/-- Every nonzero `K`-stable submodule of a finite-dimensional representation contains a nonzero
`K`-simple `K`-stable submodule.  (Adaptation of
`Work.CharPrelim.exists_simple_stable_submodule` to an arbitrary nonzero `K`-stable subspace.) -/
lemma exists_simple_stable_le {L : Type*} [Field L] {G : Type*} [Group G] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (ρ : Representation L G V) {K : Subgroup G} {C : Submodule L V}
    (hC : C ≠ ⊥) (hCstab : IsStableUnder ρ K C) :
    ∃ U : Submodule L V, U ≤ C ∧ U ≠ ⊥ ∧ IsStableUnder ρ K U ∧
      ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U := by
  classical
  suffices h : ∀ n, ∀ C : Submodule L V, Module.finrank L C = n → C ≠ ⊥ →
      IsStableUnder ρ K C →
      ∃ U : Submodule L V, U ≤ C ∧ U ≠ ⊥ ∧ IsStableUnder ρ K U ∧
        ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U by
    exact h (Module.finrank L C) C rfl hC hCstab
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro C hdim hCne hCstab
    by_cases hsimp : ∀ W : Submodule L V, W ≤ C → IsStableUnder ρ K W → W ≠ ⊥ → W = C
    · exact ⟨C, le_rfl, hCne, hCstab, hsimp⟩
    · push Not at hsimp
      obtain ⟨W, hWC, hWstab, hWne, hWneC⟩ := hsimp
      have hlt : Module.finrank L W < n := by
        rw [← hdim]
        exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWC hWneC)
      obtain ⟨U', hU'W, hU'ne, hU'stab, hU'simp⟩ :=
        ih (Module.finrank L W) hlt W rfl hWne hWstab
      exact ⟨U', hU'W.trans hWC, hU'ne, hU'stab, hU'simp⟩

end SimpleLe

section HomVanish

/-- **The key step of Feit--Thompson 3.16 (iii), `K`-equivariant form**, without any
irreducibility assumption on `ρ`: only the vanishing of the `K`-fixed space of the `K`-simple
submodule `U` is used. -/
theorem hom_vanish_general {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    [IsAlgClosed L] {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) [FiniteDimensional L V]
    {K E : Subgroup G} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ≤ K)
    (hcop : ¬ p ∣ Nat.card G) {U : Submodule L V} (hU : U ≠ ⊥)
    (hUstab : IsStableUnder ρ K U)
    (hUsimp : ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U)
    (hinvU : (Representation.subrepresentation (ρ.comp K.subtype) U hUstab).invariants = ⊥)
    {g h : G} (hgE : g ∈ E) (hhE : h ∈ E) (hgh : g ≠ h) (f : V →ₗ[L] V)
    (hfK : ∀ k : ↥K, f.comp (ρ (k : G)) = (ρ (k : G)).comp f)
    (hfmap : ∀ u ∈ U, f (ρ g u) ∈ Submodule.map (ρ h) U) :
    ∀ u ∈ U, f (ρ g u) = 0 := by
  classical
  haveI : K.Normal := hKn
  by_cases hf0 : ∀ u ∈ U, f (ρ g u) = 0
  · exact hf0
  push Not at hf0
  obtain ⟨u₀, hu₀, hfu₀⟩ := hf0
  have hfne : ∃ u ∈ U, f (ρ g u) ≠ 0 := ⟨u₀, hu₀, hfu₀⟩
  have hinj : ∀ x ∈ Submodule.map (ρ g) U, f x = 0 → x = 0 := by
    intro x hx hfx
    have hZstab : IsStableUnder ρ K (Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥) :=
      inf_stable ρ (map_rho_stable ρ hKn hUstab g) (comap_bot_stable ρ hfK)
    have hZle : Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥ ≤ Submodule.map (ρ g) U :=
      inf_le_left
    have hZ : Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥ = ⊥ := by
      by_contra hZne
      have hz : Submodule.map (ρ g) U ≤ Submodule.comap f ⊥ := by
        rw [← map_rho_simple ρ hKn hU hUstab hUsimp g _ hZle hZstab hZne]
        exact inf_le_right
      obtain ⟨u, hu, hfu⟩ := hfne
      exact hfu (by
        have := hz (Submodule.mem_map_of_mem hu)
        simpa only [Submodule.mem_comap, Submodule.mem_bot] using this)
    have hxZ : x ∈ Submodule.map (ρ g) U ⊓ Submodule.comap f ⊥ :=
      Submodule.mem_inf.mpr ⟨hx, by simpa only [Submodule.mem_comap, Submodule.mem_bot] using hfx⟩
    rw [hZ, Submodule.mem_bot] at hxZ
    exact hxZ
  have hsurj : ∀ y ∈ Submodule.map (ρ h) U, ∃ x ∈ Submodule.map (ρ g) U, f x = y := by
    have hMstab : IsStableUnder ρ K (Submodule.map f (Submodule.map (ρ g) U)) := by
      intro k z hz
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
      rw [Submodule.mem_comap]
      have h2 := congrArg (fun t : V →ₗ[L] V => t x) (hfK k)
      simp only [LinearMap.comp_apply] at h2
      rw [← h2]
      exact Submodule.mem_map_of_mem (map_rho_stable ρ hKn hUstab g k hx)
    have hMle : Submodule.map f (Submodule.map (ρ g) U) ≤ Submodule.map (ρ h) U := by
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
      exact hfmap u hu
    have hMne : Submodule.map f (Submodule.map (ρ g) U) ≠ ⊥ := by
      intro hbot
      have hmem : f (ρ g u₀) ∈ Submodule.map f (Submodule.map (ρ g) U) :=
        Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hu₀)
      rw [hbot, Submodule.mem_bot] at hmem
      exact hfu₀ hmem
    have hM : Submodule.map f (Submodule.map (ρ g) U) = Submodule.map (ρ h) U :=
      map_rho_simple ρ hKn hU hUstab hUsimp h _ hMle hMstab hMne
    intro y hy
    rw [← hM] at hy
    obtain ⟨x, hx, hfy⟩ := Submodule.mem_map.mp hy
    exact ⟨x, hx, hfy⟩
  set σ : ↥K ≃* ↥K := MulAut.conjNormal (h⁻¹ * g) with hσdef
  set ψ : V →ₗ[L] V := (ρ h⁻¹) ∘ₗ f ∘ₗ (ρ g) with hψdef
  have hψapp : ∀ v : V, ψ v = ρ h⁻¹ (f (ρ g v)) := fun v => rfl
  have hψU : ∀ u ∈ U, ψ u ∈ U := by
    intro u hu
    obtain ⟨u'', hu'', hu''eq⟩ := Submodule.mem_map.mp (hfmap u hu)
    rw [hψapp, ← hu''eq, rho_inv_rho ρ h u'']
    exact hu''
  have hψσ : ∀ (k : ↥K) (v : V), ψ (ρ (k : G) v) = ρ ((σ k : ↥K) : G) (ψ v) := by
    intro k v
    have h1 : ψ (ρ (k : G) v) = ρ (h⁻¹ * (g * (k : G) * g⁻¹)) (f (ρ g v)) := by
      rw [hψapp]
      have e1 : ρ g (ρ (k : G) v) = ρ (g * (k : G)) v := mul_apply_eq ρ g (k : G) v
      rw [e1]
      have e2 : (ρ (g * (k : G)) : V →ₗ[L] V) = ρ (g * (k : G) * g⁻¹) * ρ g := by
        conv_lhs => rw [show g * (k : G) = (g * (k : G) * g⁻¹) * g from by group]
        rw [map_mul]
      rw [e2, Module.End.mul_apply]
      have e3 : f (ρ (g * (k : G) * g⁻¹) (ρ g v)) = ρ (g * (k : G) * g⁻¹) (f (ρ g v)) := by
        have hh := congrArg (fun t : V →ₗ[L] V => t (ρ g v))
          (hfK ⟨g * (k : G) * g⁻¹, hKn.conj_mem (k : G) k.2 g⟩)
        simpa only [LinearMap.comp_apply] using hh
      rw [e3, mul_apply_eq ρ h⁻¹ (g * (k : G) * g⁻¹) (f (ρ g v))]
    have h2 : ρ ((σ k : ↥K) : G) (ψ v) = ρ (h⁻¹ * (g * (k : G) * g⁻¹)) (f (ρ g v)) := by
      rw [hψapp]
      have e : ((σ k : ↥K) : G) = h⁻¹ * g * (k : G) * (h⁻¹ * g)⁻¹ := by
        simp only [σ, MulAut.conjNormal_apply]
      rw [e, mul_inv_rev, inv_inv]
      rw [mul_apply_eq ρ (h⁻¹ * g * (k : G) * (g⁻¹ * h)) h⁻¹ (f (ρ g v))]
      congr 1
      group
    rw [h1, h2]
  have hψU' : ∀ u ∈ U, ψ u ∈ U := hψU
  set ψU : ↥U →ₗ[L] ↥U := ψ.restrict hψU' with hψUdef
  have hψU_bij : Function.Bijective ψU := by
    constructor
    · intro x y hxy
      have h1 : ψ (x : V) = ψ (y : V) := by
        have := congrArg Subtype.val hxy
        simpa only [ψU, LinearMap.restrict_apply] using this
      have h2 : f (ρ g (x : V)) = f (ρ g (y : V)) := by
        have := congrArg (ρ h) h1
        simpa only [hψapp, rho_rho_inv ρ h] using this
      have h3 : ρ g (x : V) = ρ g (y : V) := by
        have h0 : f (ρ g (x : V) - ρ g (y : V)) = 0 := by rw [map_sub, h2, sub_self]
        have := hinj _ (Submodule.sub_mem (Submodule.map (ρ g) U)
          (Submodule.mem_map_of_mem x.2) (Submodule.mem_map_of_mem y.2)) h0
        rwa [sub_eq_zero] at this
      exact Subtype.ext (by
        have := congrArg (ρ g⁻¹) h3
        simpa only [rho_inv_rho ρ g] using this)
    · intro x
      obtain ⟨z, hz, hfz⟩ := hsurj (ρ h (x : V)) (Submodule.mem_map_of_mem x.2)
      obtain ⟨u', hu', rfl⟩ := Submodule.mem_map.mp hz
      refine ⟨⟨u', hu'⟩, ?_⟩
      apply Subtype.ext
      simp only [ψU, LinearMap.restrict_apply, hψapp, hfz, rho_inv_rho ρ h]
  have hfpf : ∀ k : ↥K, σ k = k → k = 1 := by
    intro k hk
    by_contra hkne
    have hkG : (k : G) ≠ 1 := fun hcon => hkne (Subtype.ext hcon)
    have h1 : (h⁻¹ * g) * (k : G) * (h⁻¹ * g)⁻¹ = (k : G) := by
      have := congrArg (fun t : ↥K => (t : G)) hk
      simpa only [σ, MulAut.conjNormal_apply] using this
    have hcomm : (h⁻¹ * g) * (k : G) = (k : G) * (h⁻¹ * g) := by
      calc (h⁻¹ * g) * (k : G) = ((h⁻¹ * g) * (k : G) * (h⁻¹ * g)⁻¹) * (h⁻¹ * g) := by group
        _ = (k : G) * (h⁻¹ * g) := by rw [h1]
    have hx1 : h⁻¹ * g ∈ K := by
      refine hcent (k : G) k.2 hkG ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcomm.symm
    have hx2 : h⁻¹ * g ∈ E := E.mul_mem (E.inv_mem hhE) hgE
    have hx3 : h⁻¹ * g ∈ K ⊓ E := Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
    rw [hinf, Subgroup.mem_bot] at hx3
    refine hgh ?_
    calc g = h * (h⁻¹ * g) := by group
      _ = h * 1 := by rw [hx3]
      _ = h := by rw [mul_one]
  have hcopK : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    obtain ⟨m, hm⟩ := hdvd
    exact hcop ⟨m * K.index, by rw [← Subgroup.card_mul_index K, hm, mul_assoc]⟩
  haveI hUirr : (Representation.subrepresentation (ρ.comp K.subtype) U hUstab).IsIrreducible :=
    subrepresentation_isIrreducible_mfr ρ hU hUstab hUsimp
  have hψUσ : ∀ (k : ↥K) (u : ↥U),
      ψU ((Representation.subrepresentation (ρ.comp K.subtype) U hUstab) k u)
        = (Representation.subrepresentation (ρ.comp K.subtype) U hUstab) (σ k) (ψU u) := by
    intro k u
    apply Subtype.ext
    show ψ (ρ (k : G) (u : V)) = ρ ((σ k : ↥K) : G) (ψ (u : V))
    exact hψσ k (u : V)
  exfalso
  exact no_isFixedPointFree_semilinear_bijective
    (ρ := Representation.subrepresentation (ρ.comp K.subtype) U hUstab) hinvU hcopK σ hfpf ψU
    hψU_bij hψUσ
end HomVanish

section DirectSum

/-- The `E`-conjugates of a nonzero `K`-simple `K`-stable subspace are independent, with no
irreducibility assumption on `ρ`. -/
theorem iSupIndep_map_rho_general {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    [IsAlgClosed L] {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module L V]
    (ρ : Representation L G V) [FiniteDimensional L V]
    {K E : Subgroup G} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k} : Set G) ≤ K)
    (hcop : ¬ p ∣ Nat.card G) {U : Submodule L V} (hU : U ≠ ⊥)
    (hUstab : IsStableUnder ρ K U)
    (hUsimp : ∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U)
    (hinvU : (Representation.subrepresentation (ρ.comp K.subtype) U hUstab).invariants = ⊥) :
    iSupIndep (fun h : ↥E => Submodule.map (ρ ((h : ↥E) : G)) U) := by
  classical
  haveI : K.Normal := hKn
  have hcard : (Nat.card ↥K : L) ≠ 0 := by
    intro h0
    have hdvd : p ∣ Nat.card ↥K := (CharP.cast_eq_zero_iff L p (Nat.card ↥K)).mp h0
    obtain ⟨m, hm⟩ := hdvd
    exact hcop ⟨m * K.index, by rw [← Subgroup.card_mul_index K, hm, mul_assoc]⟩
  rw [iSupIndep_iff_supIndep_univ, Finset.supIndep_iff_disjoint_erase]
  intro h _
  set W : ↥E → Submodule L V := fun t => Submodule.map (ρ ((t : ↥E) : G)) U with hWdef
  set Y : Submodule L V := (Finset.univ.erase h).sup W with hYdef
  set X : Submodule L V := W h ⊓ Y with hXdef
  have hYstab : IsStableUnder ρ K Y := by
    intro k
    rw [hYdef]
    refine Finset.sup_le fun t ht => ?_
    exact le_trans (map_rho_stable ρ hKn hUstab ((t : ↥E) : G) k)
      (Submodule.comap_mono (Finset.le_sup (f := W) ht))
  have hXstab : IsStableUnder ρ K X :=
    inf_stable ρ (map_rho_stable ρ hKn hUstab ((h : ↥E) : G)) hYstab
  obtain ⟨π, hπX, hπY, hπcomm⟩ :=
    exists_stable_proj ρ K hcard (X := X) (Y := Y) inf_le_right hXstab hYstab
  rw [disjoint_iff_inf_le]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
  have hxY : x ∈ Y := by rw [hYdef]; exact hx2
  have hxX : x ∈ X := Submodule.mem_inf.mpr ⟨hx1, hxY⟩
  rw [hYdef, Finset.sup_eq_iSup] at hxY
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum W x).mp hxY
  have hπμ : ∀ t ∈ Finset.univ.erase h, π ((μ t : ↥(W t)) : V) = 0 := by
    intro t ht
    have htne : t ≠ h := fun hth => (Finset.mem_erase.mp ht).1 hth
    obtain ⟨u', hu', hu'eq⟩ := Submodule.mem_map.mp (μ t).2
    have hvan := hom_vanish_general ρ hKn hinf hsup hcent hcop hU hUstab hUsimp hinvU
      (g := ((t : ↥E) : G)) (h := ((h : ↥E) : G)) t.2 h.2
      (fun hth => htne (Subtype.ext hth)) π hπcomm (fun u hu => ?_)
    · rw [← hu'eq]
      exact hvan u' hu'
    · have hmemY : (ρ ((t : ↥E) : G)) u ∈ Y := by
        rw [hYdef, hWdef]
        exact Finset.le_sup (f := W) ht (Submodule.mem_map_of_mem hu)
      exact (Submodule.mem_inf.mp (hπY _ hmemY)).1
  calc x = π x := (hπX x hxX).symm
    _ = π (∑ t ∈ Finset.univ.erase h, ((μ t : ↥(W t)) : V)) := by rw [hμ]
    _ = ∑ t ∈ Finset.univ.erase h, π ((μ t : ↥(W t)) : V) := map_sum π _ _
    _ = 0 := Finset.sum_eq_zero fun t ht => hπμ t ht
end DirectSum

/-- The orbit-sum argument of Feit--Thompson 3.16 (iii): for a family `W` of submodules that is
independent, nondegenerate at `1` and permuted by `E`, the `E₀`-fixed space of `V` has dimension at
least `[E : E₀]`.  (Same proof as
`Work.CharPrelim.relIndex_le_finrank_invariants_of_iSupIndep_permuted`, whose hypothesis
`⨆ e, W e = ⊤` is unused.) -/
theorem relIndex_le_finrank_invariants_of_iSupIndep_permuted_general {L : Type*} [Field L]
    {E : Type*} [Group E] [Fintype E] {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V]
    (ρ : Representation L E V) (W : E → Submodule L V) (hind : iSupIndep W)
    (hperm : ∀ (e h : E), Submodule.map (ρ e) (W h) = W (e * h))
    (hne : W 1 ≠ ⊥) (E₀ : Subgroup E) :
    E₀.index ≤ Module.finrank L ↥(Representation.invariants (ρ.comp E₀.subtype)) := by
  classical
  -- Basic pointwise multiplication rule for the representation.
  have hmul : ∀ (x y : E) (v : V), ρ x (ρ y v) = ρ (x * y) v := by
    intro x y v
    show (ρ x * ρ y) v = ρ (x * y) v
    rw [← map_mul]
  -- Every `W e` is nonzero.
  have hWe : ∀ e : E, W e ≠ ⊥ := by
    intro e hbot
    have h1 : W 1 = Submodule.map (ρ e⁻¹) (W e) := by
      rw [hperm e⁻¹ e, inv_mul_cancel]
    rw [h1, hbot, Submodule.map_bot] at hne
    exact hne rfl
  -- A nonzero vector of `W 1`.
  obtain ⟨w, hwmem, hwne⟩ := (Submodule.ne_bot_iff (W 1)).mp hne
  have hmem : ∀ g : E, (ρ g) w ∈ W g := by
    intro g
    have h1 := hperm g 1
    rw [mul_one] at h1
    rw [← h1]
    exact Submodule.mem_map_of_mem hwmem
  have hρw : ∀ g : E, ρ g w ≠ 0 := by
    intro g hz
    have h1 : ρ g⁻¹ (ρ g w) = w := by rw [hmul, inv_mul_cancel]; simp
    rw [hz, map_zero] at h1
    exact hwne h1.symm
  -- The "orbit sum" map.
  let S : E → V := fun h => ∑ e : E₀, ρ ((e : E) * h) w
  -- `S h` is fixed by `E₀`.
  have hSinv : ∀ h : E, S h ∈ Representation.invariants (ρ.comp E₀.subtype) := by
    intro h
    rw [Representation.mem_invariants]
    intro a
    show ρ (a : E) (∑ e : E₀, ρ ((e : E) * h) w) = ∑ e : E₀, ρ ((e : E) * h) w
    rw [map_sum]
    rw [show (∑ e : E₀, ρ (a : E) (ρ ((e : E) * h) w)) =
        ∑ e : E₀, ρ (((a : E) * (e : E)) * h) w from by
      apply Finset.sum_congr rfl; intro e _; rw [hmul, mul_assoc]]
    rw [show (∑ e : E₀, ρ (((a : E) * (e : E)) * h) w) =
        ∑ e : E₀, ρ ((e : E) * h) w from by
      have h2 := Equiv.sum_comp (Equiv.mulLeft a) (fun e : E₀ => ρ ((e : E) * h) w)
      simpa using h2]
  -- `S` is constant on right cosets of `E₀`.
  have hSconst : ∀ (a : E₀) (h : E), S ((a : E) * h) = S h := by
    intro a h
    show (∑ e : E₀, ρ ((e : E) * ((a : E) * h)) w) = ∑ e : E₀, ρ ((e : E) * h) w
    rw [show (∑ e : E₀, ρ ((e : E) * ((a : E) * h)) w) =
        ∑ e : E₀, ρ (((e : E) * (a : E)) * h) w from by
      apply Finset.sum_congr rfl; intro e _; rw [mul_assoc]]
    rw [show (∑ e : E₀, ρ (((e : E) * (a : E)) * h) w) =
        ∑ e : E₀, ρ ((e : E) * h) w from by
      have h2 := Equiv.sum_comp (Equiv.mulRight a) (fun e : E₀ => ρ ((e : E) * h) w)
      simpa using h2]
  -- Distinct right cosets give distinct values: the support of `S h` is the coset.
  have lemma3 : ∀ (h h' : E), S h = S h' → h' * h⁻¹ ∈ E₀ := by
    intro h h' heq
    by_contra hmem'
    let μ : E₀ ⊕ E₀ → E := Sum.elim (fun e : E₀ => (e : E) * h) (fun e : E₀ => (e : E) * h')
    have hμ : Function.Injective μ := by
      intro i j hij
      cases i with
      | inl a =>
        cases j with
        | inl b =>
          simp only [μ, Sum.elim_inl] at hij
          have : (a : E) = (b : E) := mul_right_cancel hij
          exact congrArg Sum.inl (Subtype.ext this)
        | inr b =>
          exfalso
          simp only [μ, Sum.elim_inl, Sum.elim_inr] at hij
          apply hmem'
          have h2 : (b : E)⁻¹ * ((a : E) * h) = h' := by rw [hij]; group
          have hb : h' * h⁻¹ = (b : E)⁻¹ * (a : E) := by rw [← h2]; group
          rw [hb]
          exact E₀.mul_mem (E₀.inv_mem b.2) a.2
      | inr a =>
        cases j with
        | inl b =>
          exfalso
          simp only [μ, Sum.elim_inl, Sum.elim_inr] at hij
          apply hmem'
          have h2 : (a : E)⁻¹ * ((b : E) * h) = h' := by rw [← hij]; group
          have hb : h' * h⁻¹ = (a : E)⁻¹ * (b : E) := by rw [← h2]; group
          rw [hb]
          exact E₀.mul_mem (E₀.inv_mem a.2) b.2
        | inr b =>
          simp only [μ, Sum.elim_inr] at hij
          have : (a : E) = (b : E) := mul_right_cancel hij
          exact congrArg Sum.inr (Subtype.ext this)
    have hindμ : iSupIndep (W ∘ μ) := hind.comp hμ
    let u : E₀ ⊕ E₀ → V :=
      Sum.elim (fun e : E₀ => ρ ((e : E) * h) w) (fun e : E₀ => -ρ ((e : E) * h') w)
    have hmem_u : ∀ i ∈ (Finset.univ : Finset (E₀ ⊕ E₀)), u i ∈ (W ∘ μ) i := by
      intro i _
      cases i with
      | inl e => exact hmem ((e : E) * h)
      | inr e => exact Submodule.neg_mem _ (hmem ((e : E) * h'))
    have hsum_u : ∑ i : E₀ ⊕ E₀, u i = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [u, Sum.elim_inl, Sum.elim_inr]
      rw [Finset.sum_neg_distrib]
      change S h + -S h' = 0
      rw [heq]; simp
    have hdec := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (W ∘ μ)).mp hindμ
      (Finset.univ) u hmem_u hsum_u
    have h0 : u (Sum.inl (1 : E₀)) = 0 := hdec (Sum.inl 1) (Finset.mem_univ _)
    apply hρw h
    simpa [u] using h0
  -- The values `S h` form a linearly independent family in `V`.
  have lemma4 : LinearIndependent L (fun y : ↥(Set.range S) => (y.1 : V)) := by
    rw [linearIndependent_iff']
    intro s g hsum
    let f : ↥(Set.range S) → E := fun y => Classical.choose y.2
    have hf : ∀ y : ↥(Set.range S), S (f y) = y.1 := fun y => Classical.choose_spec y.2
    let ν : ↥(Set.range S) × E₀ → E := fun x => (x.2 : E) * f x.1
    have hν : Function.Injective ν := by
      intro x y hxy
      obtain ⟨x1, xe⟩ := x
      obtain ⟨y1, ye⟩ := y
      simp only [ν] at hxy
      have h2 : ((ye : E)⁻¹ * (xe : E)) * f x1 = f y1 := by rw [mul_assoc, hxy]; group
      have ha : (ye : E)⁻¹ * (xe : E) ∈ E₀ := E₀.mul_mem (E₀.inv_mem ye.2) xe.2
      have hS : S (f y1) = S (f x1) := by
        rw [← h2]
        exact hSconst ⟨_, ha⟩ (f x1)
      have hy : y1 = x1 := Subtype.ext (by rw [← hf y1, hS, hf x1])
      subst hy
      have : (xe : E) = (ye : E) := mul_right_cancel hxy
      exact Prod.ext rfl (Subtype.ext this)
    let u : ↥(Set.range S) × E₀ → V := fun x => g x.1 • ρ ((x.2 : E) * f x.1) w
    have hmem_u : ∀ x ∈ (s ×ˢ Finset.univ : Finset (↥(Set.range S) × E₀)), u x ∈ (W ∘ ν) x := by
      intro x _
      exact Submodule.smul_mem _ (g x.1) (hmem _)
    have hinner : ∀ y : ↥(Set.range S),
        (∑ e ∈ (Finset.univ : Finset E₀), u (y, e)) = g y • (y.1 : V) := by
      intro y
      simp only [u]
      rw [← Finset.smul_sum]
      congr 1
      rw [← hf y]
    have hsum_u : ∑ x ∈ (s ×ˢ Finset.univ : Finset (↥(Set.range S) × E₀)), u x = 0 := by
      rw [Finset.sum_product]
      rw [Finset.sum_congr rfl (fun y _ => hinner y)]
      exact hsum
    have hdec := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero (W ∘ ν)).mp (hind.comp hν)
      (s ×ˢ Finset.univ) u hmem_u hsum_u
    intro y hy
    have h1 : u (y, 1) = 0 := hdec (y, 1) (Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩)
    have h2 : g y • ρ (f y) w = 0 := by simpa [u] using h1
    by_contra hgy
    have h3 : (g y)⁻¹ • (g y • ρ (f y) w) = ρ (f y) w := by
      rw [← mul_smul, inv_mul_cancel₀ hgy, one_smul]
    rw [h2, smul_zero] at h3
    exact hρw (f y) h3.symm
  -- The number of distinct values of `S` is the index of `E₀`.
  haveI : Fintype ↥(Set.range S) := (Set.finite_range S).fintype
  have lemma5 : Fintype.card ↥(Set.range S) = E₀.index := by
    have hwd : ∀ x y : E, (QuotientGroup.rightRel E₀) x y → S x = S y := by
      intro x y hxy
      rw [QuotientGroup.rightRel_apply] at hxy
      have hy : y = (y * x⁻¹) * x := by group
      rw [hy]
      exact (hSconst ⟨y * x⁻¹, hxy⟩ x).symm
    let S' : Quotient (QuotientGroup.rightRel E₀) → V := Quotient.lift S hwd
    have hS' : ∀ a, S' ⟦a⟧ = S a := fun a => Quotient.lift_mk S hwd a
    have hinj : Function.Injective S' := by
      intro p q hpq
      induction p using Quotient.inductionOn with
      | h a =>
        induction q using Quotient.inductionOn with
        | h b =>
          rw [hS' a, hS' b] at hpq
          exact Quotient.sound (show (QuotientGroup.rightRel E₀) a b from
            (QuotientGroup.rightRel_apply).mpr (lemma3 a b hpq))
    have hrange : Set.range S = Set.range S' := by
      apply Set.ext
      intro v
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨⟦a⟧, hS' a⟩
      · rintro ⟨q, rfl⟩
        induction q using Quotient.inductionOn with
        | h a => exact ⟨a, (hS' a).symm⟩
    haveI : Fintype ↥(Set.range S') := (Set.finite_range S').fintype
    calc Fintype.card ↥(Set.range S) = Fintype.card ↥(Set.range S') :=
          Fintype.card_congr (Set.equivOfEq hrange)
      _ = Fintype.card (Quotient (QuotientGroup.rightRel E₀)) :=
          Fintype.card_congr (Equiv.ofInjective S' hinj).symm
      _ = Fintype.card (E ⧸ E₀) := QuotientGroup.card_quotient_rightRel E₀
      _ = E₀.index := by rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  -- Assemble.
  have hb : Fintype.card ↥(Set.range S) ≤
      Module.finrank L ↥(Representation.invariants (ρ.comp E₀.subtype)) := by
    have hli : LinearIndependent L (fun y : ↥(Set.range S) =>
        (⟨y.1, by rw [← Classical.choose_spec y.2]; exact hSinv (Classical.choose y.2)⟩ :
          ↥(Representation.invariants (ρ.comp E₀.subtype)))) :=
      LinearIndependent.of_comp (Submodule.subtype _) (by
        show LinearIndependent L (fun y : ↥(Set.range S) => (y.1 : V))
        exact lemma4)
    exact hli.fintype_card_le_finrank
  rw [← lemma5]
  exact hb

section Descent

/-- **Existence of the good `K`-simple subspace.**  If `K ⊴ G` is not contained in the kernel of
`ρ` and `p ∤ |G|` (so that `k[K]` is semisimple, where `p = char k`), then `V` has a nonzero
`K`-stable `K`-simple submodule `U` on which `K` has no nonzero fixed vector.

Taking a `K`-stable complement of the `K`-invariants `Z = V^K` (which is a proper submodule, as
`K ⊄ ker ρ`) reduces this to `exists_simple_stable_le`. -/
theorem exists_simple_invariants_bot {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] {K : Subgroup G} (hKn : K.Normal) (hcop : ¬ p ∣ Nat.card G)
    (ρ : Representation L G V) (hker : ¬ K ≤ ρ.ker) :
    ∃ U : Submodule L V, ∃ hUstab : IsStableUnder ρ K U, U ≠ ⊥ ∧
      (∀ W : Submodule L V, W ≤ U → IsStableUnder ρ K W → W ≠ ⊥ → W = U) ∧
      (Representation.subrepresentation (ρ.comp K.subtype) U hUstab).invariants = ⊥ := by
  classical
  haveI : K.Normal := hKn
  -- `|K|` is invertible in the field `L`, so the `K`-representation `V` is semisimple.
  haveI : NeZero (Nat.card ↥K : L) := ⟨by
    intro h0
    exact hcop (dvd_trans ((CharP.cast_eq_zero_iff L p (Nat.card ↥K)).mp h0)
      (Subgroup.card_subgroup_dvd_card K))⟩
  set Z : Submodule L V := Representation.invariants (ρ.comp K.subtype) with hZ
  -- `Z = V^K` is a `K`-stable subspace.
  have hZstab : IsStableUnder ρ K Z := fun k => by
    rw [hZ]
    exact Representation.le_comap_invariants ρ K (k : G)
  -- `K` does not act trivially on `V`.
  have hZne : Z ≠ ⊤ := by
    intro hZtop
    refine hker ?_
    intro k hk
    rw [MonoidHom.mem_ker]
    ext v
    have hv : v ∈ Z := by rw [hZtop]; trivial
    rw [hZ] at hv
    rw [Representation.mem_invariants] at hv
    simpa using hv ⟨k, hk⟩
  -- A `K`-stable complement `C` of `Z` (Maschke).
  let Zsub : Subrepresentation (ρ.comp K.subtype) :=
    ⟨Z, fun k v hv => by
      have h := hZstab k hv
      rwa [Submodule.mem_comap] at h⟩
  obtain ⟨C, hCcompl⟩ := exists_isCompl Zsub
  have hCne : C.toSubmodule ≠ ⊥ := by
    intro hCbot
    have hCbot' : C = ⊥ := Subrepresentation.toSubmodule_injective (by
      rw [hCbot]; rfl)
    have htop : Zsub = ⊤ := by
      have h := hCcompl.sup_eq_top
      rw [hCbot', sup_bot_eq] at h
      exact h
    have hZtop : Z = ⊤ := by
      have h := congrArg Subrepresentation.toSubmodule htop
      simpa [Zsub,
        show (⊤ : Subrepresentation (ρ.comp K.subtype)).toSubmodule = ⊤ from rfl] using h
    exact hZne hZtop
  have hCstab : IsStableUnder ρ K C.toSubmodule :=
    fun k v hv => C.apply_mem_toSubmodule k hv
  obtain ⟨U, hUC, hUne, hUstab, hUsimp⟩ := exists_simple_stable_le ρ hCne hCstab
  -- `U` lies in a complement of `Z`, hence has no nonzero `K`-fixed vector.
  have hUZ : U ⊓ Z = ⊥ := by
    have hbot : C.toSubmodule ⊓ Zsub.toSubmodule = ⊥ := by
      rw [inf_comm]
      simpa [show (⊥ : Subrepresentation (ρ.comp K.subtype)).toSubmodule = ⊥ from rfl] using
        congrArg Subrepresentation.toSubmodule hCcompl.inf_eq_bot
    exact le_bot_iff.mp ((le_inf (inf_le_left.trans hUC) inf_le_right).trans (le_of_eq hbot))
  refine ⟨U, hUstab, hUne, hUsimp, ?_⟩
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply Subtype.ext
  have hxZ : (x : V) ∈ Z := by
    have h := hx
    rw [Representation.mem_invariants] at h
    rw [hZ]
    rw [Representation.mem_invariants]
    intro kk
    have h2 := congrArg Subtype.val (h kk)
    simpa [Representation.subrepresentation, LinearMap.restrict_apply] using h2
  have hxUZ : (x : V) ∈ U ⊓ Z := ⟨x.2, hxZ⟩
  rw [hUZ, Submodule.mem_bot] at hxUZ
  exact hxUZ

end Descent

/-- **`Work.CharPrelim.finrank_invariants_ge_of_general_mfr`.**  Feit--Thompson 3.16 (iii) in
fixed-point-dimension form, for an arbitrary (not necessarily irreducible) representation. -/
theorem finrank_invariants_ge_of_general_mfr {k : Type*} [Field k] [IsAlgClosed k] {p : ℕ}
    [Fact p.Prime] [CharP k p]
    {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    {K E E₀ : Subgroup G} (hKn : K.Normal) (hinf : K ⊓ E = ⊥) (hsup : K ⊔ E = ⊤)
    (hKne : K ≠ ⊥) (hEne : E ≠ ⊥)
    (hcent : ∀ k' ∈ K, k' ≠ 1 → Subgroup.centralizer ({k'} : Set G) ≤ K)
    (hcop : ¬ p ∣ Nat.card G)
    (ρ : Representation k G V) (hker : ¬ K ≤ ρ.ker) (hE₀ : E₀ ≤ E) :
    E₀.relIndex E ≤ Module.finrank k ↥(Representation.invariants (ρ.comp E₀.subtype)) := by
  classical
  haveI : K.Normal := hKn
  -- a nonzero `K`-simple `K`-stable subspace on which `K` has no nonzero fixed vector
  obtain ⟨U, hUstab, hU, hUsimp, hinvU⟩ := exists_simple_invariants_bot (p := p) hKn hcop ρ hker
  set W : ↥E → Submodule k V := fun t => Submodule.map (ρ ((t : ↥E) : G)) U with hWdef
  -- the `E`-conjugates of `U` are independent
  have hind : iSupIndep W := by
    rw [hWdef]
    exact iSupIndep_map_rho_general (p := p) ρ hKn hinf hsup hcent hcop hU hUstab hUsimp hinvU
  -- `E` permutes them
  have hperm : ∀ (e h : ↥E), Submodule.map ((ρ.comp E.subtype) e) (W h) = W (e * h) := by
    intro e h
    rw [hWdef]
    show Submodule.map (ρ ((e : ↥E) : G)) (Submodule.map (ρ ((h : ↥E) : G)) U)
      = Submodule.map (ρ (((e * h : ↥E)) : G)) U
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul]
    rfl
  have hne : W 1 ≠ ⊥ := by
    rw [hWdef]
    intro h2
    refine hU ?_
    have h4 : Submodule.map (ρ (1 : G)) U = ⊥ := h2
    rwa [map_one, Module.End.one_eq_id, Submodule.map_id] at h4
  have h := relIndex_le_finrank_invariants_of_iSupIndep_permuted_general (ρ := ρ.comp E.subtype)
    W hind hperm hne (E₀.subgroupOf E)
  have hinv_eq : Representation.invariants ((ρ.comp E.subtype).comp (E₀.subgroupOf E).subtype)
      = Representation.invariants (ρ.comp E₀.subtype) := by
    ext v
    simp only [Representation.mem_invariants]
    constructor
    · intro hh y
      exact hh ⟨⟨(y : G), hE₀ y.2⟩, y.2⟩
    · intro hh x
      exact hh ⟨((x : ↥E) : G), x.2⟩
  have hfin : Module.finrank k
        ↥(Representation.invariants ((ρ.comp E.subtype).comp (E₀.subgroupOf E).subtype))
      = Module.finrank k ↥(Representation.invariants (ρ.comp E₀.subtype)) :=
    congrArg (fun s : Submodule k V => Module.finrank k ↥s) hinv_eq
  rw [hfin] at h
  exact h

end Work.CharPrelim.MFR
