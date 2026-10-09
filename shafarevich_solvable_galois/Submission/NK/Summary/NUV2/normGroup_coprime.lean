import Mathlib
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NK.LocalCFT.Reduction.Defs
import Submission.NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

/-!
# The second class-formation axiom in the *coprime* case

Local class field theory is organised around the two axioms of the local class formation
`(G_F, F̄ˣ)`:

* **(A1) transitivity of norms**: `N_{L₂/F} L₂ˣ ≤ N_{L₁/F} L₁ˣ` for `L₁ ≤ L₂` (proved in
  `NK.LocalReciprocity.normGroup_le_of_tower`, and the group-level identity
  `N_{M/F} Mˣ = N_{E/F}(N_{M/E} Mˣ)` as `NK.LocalReciprocity.normGroup_trans`);
* **(A2) the second axiom**: `N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F}L₁ˣ ∩ N_{L₂/F}L₂ˣ` — equivalently
  `N_{L₁∩L₂/F}(L₁∩L₂)ˣ = N_{L₁/F}L₁ˣ · N_{L₂/F}L₂ˣ`, i.e. the norm-group map is an
  order-reversing *embedding* of the lattice of abelian levels into the lattice of finite-index
  subgroups of `Fˣ`.  This is Hasse's *Normensatz* / Umkehrsatz, and it is the single classical
  residue of the local theory in this workspace.

This file proves **(A2) in the case of coprime degrees**, where it is *elementary* and requires
no input beyond (A1) and the norm index theorem.  The argument is Bezout on the degrees:

> if `d₁ = [L₁ : F]` and `d₂ = [L₂ : F]` are coprime, then for every `x ∈ Fˣ` we have
> `x = (x^{d₁})^{a} · (x^{d₂})^{b}` for suitable `a b ∈ ℤ` (Bezout), and the tower identity of
> norms (`Algebra.norm_norm` together with `Algebra.norm_algebraMap`) gives
> `x^{d₁} = N_{L₁/F} x` and `x^{d₂} = N_{L₂/F} x`.  Hence `Fˣ = N(L₁) · N(L₂)`, i.e.
> `N(L₁) ⊔ N(L₂) = ⊤ = N(F) = N(L₁ ∩ L₂)` (coprime degrees force `L₁ ∩ L₂ = F`): the *product form*
> of (A2).  The *intersection form* `N(L₁L₂) = N(L₁) ⊓ N(L₂)` then follows from the two index
> computations

* `[Fˣ : N(L)] = [L : F]` (the norm index theorem of local class field theory), and
* `[Fˣ : N(L₁) ⊓ N(L₂)] = [Fˣ : N(L₁)] · [Fˣ : N(L₂)] ⧸ [Fˣ : N(L₁) ⊔ N(L₂)]`
  (the elementary subgroup identity `index_inf_mul_index_sup` below),

together with Mathlib's `IntermediateField.LinearDisjoint.of_finrank_coprime`, which converts
coprime degrees into linear disjointness and hence into the degree identity
`[L₁L₂ : F] = [L₁ : F] · [L₂ : F]`.

Consequently the residual (A2) — and hence the whole local `Normensatz` — may be assumed to be
*ℓ-primary*: the general case follows from the `ℓ`-power-degree case for each prime `ℓ` by
decomposing a level into its `ℓ`-primary parts (pairwise coprime degrees) and applying the results
of this file.

## Main results

* `NK.Summary.NUV2.normGroup_sup_eq_top_of_coprime` — (A2) in product form, *unconditional*;
* `NK.Summary.NUV2.index_inf_mul_index_sup` — the subgroup index identity above;
* `NK.Summary.NUV2.eq_of_le_of_index_eq` — a subgroup of finite index is determined by its index
  among the subgroups containing it;
* `NK.Summary.NUV2.normGroup_sup_eq_inf_of_coprime_of_index` — (A2) in intersection form, from the
  norm index theorem at the three levels involved;
* `NK.Summary.NUV2.normGroup_sup_eq_inf_of_coprime_adicCompletion` — the same at a `p`-adic
  completion `F = Q.adicCompletion K`, where the norm index theorem is a theorem
  (`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`), so the only hypothesis is
  the coprimality of the two degrees.
-/

open scoped Classical

namespace NK.Summary.NUV2

universe u v w

/-! ## The Bezout input and the tower identity of norms -/

/-- **Bezout in a commutative group**: if `d₁` and `d₂` are coprime, every element is the product
of a `d₁`-th power and a `d₂`-th power (of that same element). -/
theorem exists_zpow_mul_zpow_eq_of_coprime {G : Type w} [CommGroup G] {d₁ d₂ : ℕ}
    (h : Nat.Coprime d₁ d₂) (x : G) :
    ∃ a b : ℤ, x = (x ^ d₁) ^ a * (x ^ d₂) ^ b := by
  have hgcd : (d₁ : ℤ).gcd (d₂ : ℤ) = 1 := by
    simp [Int.gcd_natCast_natCast, h.gcd_eq_one]
  refine ⟨(d₁ : ℤ).gcdA (d₂ : ℤ), (d₁ : ℤ).gcdB (d₂ : ℤ), ?_⟩
  have hab : (d₁ : ℤ) * (d₁ : ℤ).gcdA (d₂ : ℤ)
      + (d₂ : ℤ) * (d₁ : ℤ).gcdB (d₂ : ℤ) = 1 := by
    rw [← Int.gcd_eq_gcd_ab, hgcd]
    simp
  have h1 : ((x : G) ^ d₁) ^ (d₁ : ℤ).gcdA (d₂ : ℤ)
      = x ^ ((d₁ : ℤ) * (d₁ : ℤ).gcdA (d₂ : ℤ)) := by
    rw [← zpow_natCast x d₁, zpow_mul]
  have h2 : ((x : G) ^ d₂) ^ (d₁ : ℤ).gcdB (d₂ : ℤ)
      = x ^ ((d₂ : ℤ) * (d₁ : ℤ).gcdB (d₂ : ℤ)) := by
    rw [← zpow_natCast x d₂, zpow_mul]
  rw [h1, h2, ← zpow_add, hab, zpow_one]

/-- The `d`-th power of a unit, for `d = [L : F]`, is a norm from `L`.  This is the tower identity
of norms at a single element: `N_{L/F}(x) = x^{[L:F]}` for `x ∈ F ⊆ L`
(`Algebra.norm_algebraMap`). -/
theorem pow_finrank_mem_normGroup {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F']
    (L : IntermediateField F F') [FiniteDimensional F ↥L] (x : Fˣ) :
    x ^ (Module.finrank F ↥L) ∈ NK.LocalReciprocity.normGroup F ↥L := by
  rw [NK.LocalReciprocity.mem_normGroup_iff]
  refine ⟨Units.map (algebraMap F ↥L : F →* ↥L) x, ?_⟩
  rw [Units.coe_map]
  change Algebra.norm F (algebraMap F ↥L (x : F)) = ((x ^ Module.finrank F ↥L : Fˣ) : F)
  rw [Algebra.norm_algebraMap, Units.val_pow_eq_pow_val]

/-! ## (A2) in product form, and the coprime case -/

/-- **(A2) in the coprime case, product form.**  For finite-dimensional levels `L₁, L₂` of
`F' / F` whose degrees over `F` are coprime, the norm groups generate all of `Fˣ`:
`N_{L₁/F}L₁ˣ · N_{L₂/F}L₂ˣ = Fˣ`.

Equivalently (the two sides are trivially ordered the other way) this is the second
class-formation axiom `N_{L₁∩L₂} = N_{L₁}·N_{L₂}` in the case in which the two levels are linearly
disjoint.  The proof is Bezout on the degrees, and it is *elementary*: no local class field theory
beyond the tower identity of norms is used. -/
theorem normGroup_sup_eq_top_of_coprime {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] (L₁ L₂ : IntermediateField F F') [FiniteDimensional F ↥L₁]
    [FiniteDimensional F ↥L₂]
    (h : Nat.Coprime (Module.finrank F ↥L₁) (Module.finrank F ↥L₂)) :
    NK.LocalReciprocity.normGroup F ↥L₁ ⊔ NK.LocalReciprocity.normGroup F ↥L₂ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, hab⟩ := exists_zpow_mul_zpow_eq_of_coprime h x
  rw [hab]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (pow_finrank_mem_normGroup L₁ x) a))
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (pow_finrank_mem_normGroup L₂ x) b))

/-! ## Two group-theoretic tools -/

/-- **The subgroup index identity** `[G : A ⊓ B] · [G : A ⊔ B] = [G : A] · [G : B]`, for finite
index subgroups of a commutative group. -/
theorem index_inf_mul_index_sup {G : Type w} [CommGroup G] (A B : Subgroup G)
    [A.FiniteIndex] [B.FiniteIndex] :
    (A ⊓ B).index * (A ⊔ B).index = A.index * B.index := by
  have hAB : (A ⊓ B).index = B.relIndex A * A.index := by
    rw [← Subgroup.inf_relIndex_left A B, Subgroup.relIndex_mul_index inf_le_left]
  have hB : B.index = B.relIndex A * (A ⊔ B).index := by
    rw [← Subgroup.relIndex_sup_right A B, Subgroup.relIndex_mul_index le_sup_right]
  rw [hAB, hB]
  ring

/-- A subgroup of finite index is determined by its index among the subgroups containing it. -/
theorem eq_of_le_of_index_eq {G : Type w} [Group G] {A B : Subgroup G} (h : A ≤ B)
    [A.FiniteIndex] (hidx : B.index = A.index) : A = B := by
  by_contra hne
  have hlt : A < B := lt_of_le_of_ne h hne
  have := Subgroup.index_strictAnti hlt
  rw [hidx] at this
  exact lt_irrefl _ this

/-! ## (A2) in intersection form, from the norm index theorem -/

/-- **(A2) in the coprime case, intersection form.**  If the degrees of the levels `L₁, L₂` over
`F` are coprime and the norm index theorem `[Fˣ : N(L)] = [L : F]` holds at `L₁`, `L₂` and
`L₁ ⊔ L₂`, then Hasse's norm correspondence holds for the pair:

`N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F}L₁ˣ ⊓ N_{L₂/F}L₂ˣ`.

(For `F = Q.adicCompletion K` the three index hypotheses are theorems,
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`; see
`normGroup_sup_eq_inf_of_coprime_adicCompletion` below.) -/
theorem normGroup_sup_eq_inf_of_coprime_of_index {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] [IsGalois F F']
    (L₁ L₂ : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F ↥L₁] [FiniteDimensional F ↥L₂]
    (h : Nat.Coprime (Module.finrank F ↥L₁) (Module.finrank F ↥L₂))
    (h₁ : (NK.LocalReciprocity.normGroup F ↥L₁).index = Module.finrank F ↥L₁)
    (h₂ : (NK.LocalReciprocity.normGroup F ↥L₂).index = Module.finrank F ↥L₂)
    (h₁₂ : (NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂)).index
      = Module.finrank F ↥(L₁ ⊔ L₂)) :
    NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂)
      = NK.LocalReciprocity.normGroup F ↥L₁ ⊓ NK.LocalReciprocity.normGroup F ↥L₂ := by
  set A := NK.LocalReciprocity.normGroup F ↥L₁ with hA
  set B := NK.LocalReciprocity.normGroup F ↥L₂ with hB
  have htop : A ⊔ B = ⊤ := normGroup_sup_eq_top_of_coprime L₁ L₂ h
  haveI hAfin : A.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [hA, h₁]; exact (Module.finrank_pos).ne')
  haveI hBfin : B.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [hB, h₂]; exact (Module.finrank_pos).ne')
  -- coprime degrees give linear disjointness, hence the degree identity at the compositum
  have hld : L₁.LinearDisjoint L₂ := IntermediateField.LinearDisjoint.of_finrank_coprime h
  have hsup : Module.finrank F ↥(L₁ ⊔ L₂) = Module.finrank F ↥L₁ * Module.finrank F ↥L₂ :=
    hld.finrank_sup
  -- the two index computations
  have hidx : (A ⊓ B).index = (NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂)).index := by
    have hmain := index_inf_mul_index_sup A B
    rw [htop, Subgroup.index_top, mul_one] at hmain
    rw [hA, h₁, hB, h₂, ← hsup, ← h₁₂] at hmain
    exact hmain
  haveI hCfin : (NK.LocalReciprocity.normGroup F ↥(L₁ ⊔ L₂)).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [h₁₂]; exact (Module.finrank_pos).ne')
  refine eq_of_le_of_index_eq ?_ hidx
  exact le_inf (NK.LocalCFT.normGroup_le_of_le (le_sup_left : L₁ ≤ L₁ ⊔ L₂))
    (NK.LocalCFT.normGroup_le_of_le (le_sup_right : L₂ ≤ L₁ ⊔ L₂))

/-- **(A2) in the coprime case at a `p`-adic completion.**  For `F = Q.adicCompletion K` the norm
index theorem is a theorem of this workspace, so the only hypothesis is the coprimality of the two
degrees: for finite abelian levels `L₁, L₂` of `F^{ab}` of coprime degree over `F`,

`N_{L₁L₂/F}(L₁L₂)ˣ = N_{L₁/F}L₁ˣ ⊓ N_{L₂/F}L₂ˣ`. -/
theorem normGroup_sup_eq_inf_of_coprime_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L₁ L₂ : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) ↥L₁] [Normal (Q.adicCompletion K) ↥L₁]
    [FiniteDimensional (Q.adicCompletion K) ↥L₂] [Normal (Q.adicCompletion K) ↥L₂]
    [FiniteDimensional (Q.adicCompletion K) ↥(L₁ ⊔ L₂)]
    [Normal (Q.adicCompletion K) ↥(L₁ ⊔ L₂)]
    (h : Nat.Coprime (Module.finrank (Q.adicCompletion K) ↥L₁)
      (Module.finrank (Q.adicCompletion K) ↥L₂)) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(L₁ ⊔ L₂)
      = NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₁
        ⊓ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L₂ :=
  normGroup_sup_eq_inf_of_coprime_of_index L₁ L₂ h
    (NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q L₁)
    (NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q L₂)
    (NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion Q (L₁ ⊔ L₂))

/-! ## The tower covering in the coprime case -/

/-- An intermediate field of finite degree over `F` is determined by its degree among the
intermediate fields containing it. -/
theorem eq_of_le_of_finrank_eq_iField {F : Type u} {F' : Type v} [Field F] [Field F']
    [Algebra F F'] {E M : IntermediateField F F'} [FiniteDimensional F ↥E]
    [FiniteDimensional F ↥M]
    (h : E ≤ M) (hfd : Module.finrank F ↥M = Module.finrank F ↥E) : E = M := by
  have h' : E.toSubalgebra ≤ M.toSubalgebra := h
  have hfd' : Module.finrank F ↥E.toSubalgebra = Module.finrank F ↥M.toSubalgebra := hfd.symm
  exact IntermediateField.toSubalgebra_injective (Subalgebra.eq_of_le_of_finrank_eq h' hfd')

/-- **The tower covering of the Normensatz in the coprime case.**  If `E` is a finite abelian level
whose degree over `F` is coprime to that of `L`, and `N_{E/F} Eˣ ≤ N_{L/F} Lˣ`, then `L ≤ E`
(i.e. `E` is the maximal field whose norm group contains `N(E)`).

This is the hypothesis `hcov` of
`NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_adicCompletion_of_towerCover`, proved
here for pairs of coprime degree: `N(E) ≤ N(L)` forces `N(E ⊔ L) = N(E) ⊓ N(L) = N(E)` by (A2)
in the coprime case, whence `[EL : F] = [Fˣ : N(EL)] = [Fˣ : N(E)] = [E : F]` by the norm
index theorem, i.e. `EL = E`. -/
theorem le_of_normGroup_le_of_coprime_adicCompletion {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L E : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) ↥L] [Normal (Q.adicCompletion K) ↥L]
    [FiniteDimensional (Q.adicCompletion K) ↥E] [Normal (Q.adicCompletion K) ↥E]
    [FiniteDimensional (Q.adicCompletion K) ↥(L ⊔ E)] [Normal (Q.adicCompletion K) ↥(L ⊔ E)]
    (hcop : Nat.Coprime (Module.finrank (Q.adicCompletion K) ↥L)
      (Module.finrank (Q.adicCompletion K) ↥E))
    (h : NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥E
      ≤ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L) :
    L ≤ E := by
  have hA2 := normGroup_sup_eq_inf_of_coprime_adicCompletion (K := K) Q E L
    (by rwa [Nat.coprime_comm] at hcop)
  have hEq : NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(E ⊔ L)
      = NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥E := by
    rw [hA2, inf_eq_left.mpr h]
  have hidx : (NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥(E ⊔ L)).index
      = (NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥E).index := by rw [hEq]
  have hfin : Module.finrank (Q.adicCompletion K) ↥(E ⊔ L)
      = Module.finrank (Q.adicCompletion K) ↥E := by
    rw [← NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion (K := K) Q (E ⊔ L),
      ← NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion (K := K) Q E]
    exact hidx
  have hsup : E ⊔ L = E :=
    (eq_of_le_of_finrank_eq_iField (E := E) (M := E ⊔ L) le_sup_left hfin).symm
  exact hsup ▸ le_sup_right

end NK.Summary.NUV2
