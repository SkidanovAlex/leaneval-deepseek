/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area ZASS, step Z6.5 infrastructure: the coordinate bijection `X ≃ ℙ¹(E)`

Step Z5 (`Work.ZASS.exists_field_coordinates`) identifies the unipotent radical `U = F` of the
Borel subgroup `G_∞` with the additive group of a field `E` of order `q = p ^ k`, and the torus
`H = G_{∞0}` with the group `(Eˣ)²` of squares, acting by multiplication.  The present file
combines that with Z3 (`u ↦ u • 0` is a bijection `U ≃ X ∖ {∞}`) to produce the *coordinate
bijection*

  `Φ : X ≃ ℙ¹(E)`,  `Φ ∞ = ∞`,  `Φ 0 = 0`,

under which

* `u ∈ U` acts as the translation `x ↦ x + Φ'(u)` (`Work.PSL2.pslUnipotent`), and
* `h ∈ H` acts as the multiplication `x ↦ a² x` where `φ h = a²` (`Work.PSL2.pslDiag`).

This transports the Borel subgroup `G_∞` into `PSL(2, E)`.  It is the input to the remaining
part of step Z6.5 (HB III XI 1.9–1.12): the second generator `s` of `G = ⟨G_∞, s⟩`
(`Work.ZASS.bruhat_decomposition`) must be shown to act on `ℙ¹(E)` by an element of `PSL(2, E)`.
-/
import Mathlib
import Submission.Work.ZASS.Defs
import Submission.Work.ZASS.Basic
import Submission.Work.ZASS.Z2Unipotent
import Submission.Work.ZASS.isMulCommutative_of_zass
import Submission.Work.ZASS.exponent_dvd_p_of_zass
import Submission.Work.ZASS.exists_field_coordinates
import Submission.Work.ZASS.equiv_unipotent_compl
import Submission.Work.ZASS.conjBy_smul_zero
import Submission.Work.ZASS.psl_smul_ptOf

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.ZASS

open Work.GW2 (ZassHyps2)
open Work.Zassenhaus (borel pairStab fixesOnly fixesSome)

/-- **Step Z6.5, coordinates.**  From the Z5 field and torus coordinates on the unipotent
radical `U ≤ G_∞` one gets a bijection `Φ : X ≃ ℙ¹(E)` carrying `∞` to `∞` and `0` to `0`, under
which `U` acts by translations and `H = G_{∞0}` acts by multiplications `x ↦ a²x`. -/
theorem exists_coordinate_equiv {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    (h : ZassHyps2 G X (p ^ k)) {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (hUB : U ≤ borel G inf)
    (hcardU : Nat.card U = p ^ k)
    (hcardH : Nat.card (pairStab G inf zero) = (p ^ k - 1) / 2)
    (hN : (U.subgroupOf (borel G inf)).Normal)
    (hcyc : IsCyclic (pairStab G inf zero))
    (hfix : FixedPointFreeConj U (pairStab G inf zero)) :
    ∃ (E : Type) (_ : Field E) (_ : Fintype E) (_ : CharP E p)
      (Φ' : U ≃* Multiplicative E)
      (φ : pairStab G inf zero →* Eˣ)
      (Φ : X ≃ Projectivization E (Fin 2 → E)),
      Nat.card E = p ^ k ∧ Function.Injective φ ∧
      (∀ e : Eˣ, e ∈ φ.range ↔ ∃ f : Eˣ, f ^ 2 = e) ∧
      (Φ inf = Work.PSL2.ptInf E) ∧ (Φ zero = Work.PSL2.ptZero E) ∧
      (∀ u : U, ∀ x : X, Φ ((u : G) • x) =
        Work.PSL2.pslUnipotent E (Multiplicative.toAdd (Φ' u)) • Φ x) ∧
      (∀ (hh : G) (hhm : hh ∈ pairStab G inf zero), ∃ a : Eˣ,
        φ ⟨hh, hhm⟩ = a ^ 2 ∧ ∀ x : X, Φ (hh • x) = Work.PSL2.pslDiag E a • Φ x) := by
  classical
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hq; omega
    · exact hkpos
  have hcomm : IsMulCommutative U :=
    isMulCommutative_of_zass hp hk rfl hUB hcardU hcardH hN hfix
  have hexp : ∀ u ∈ U, u ^ p = 1 :=
    exponent_dvd_p_of_zass hp hk rfl hUB hcardU hcardH hN hcomm hfix
  obtain ⟨E, hE, hEF, hEc, Φ', φ, hcardE, hφinj, hφrange, hequiv⟩ :=
    exists_field_coordinates hp hk rfl hne hUB hcardU hcardH hN hcomm hexp hcyc hfix
  -- `U ⊓ H = ⊥`: the two orders are coprime.
  have hdis : U ⊓ pairStab G inf zero = ⊥ := by
    have hcop : Nat.Coprime (Nat.card U) (Nat.card (pairStab G inf zero)) := by
      rw [hcardU, hcardH]
      exact Work.Zassenhaus.zass_coprime_pow_half (Fact.out) hp hk
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  obtain ⟨e, he⟩ := equiv_unipotent_compl (U := U) hne hUB hcardU hcardH hdis h.2.1
  -- The coordinate map on `X ∖ {∞}`.
  let g : {x : X // x ≠ inf} → Projectivization E (Fin 2 → E) :=
    fun x => Work.PSL2.ptOf E (Multiplicative.toAdd (Φ' (e.symm x)))
  -- Its extension to `X` sending `∞` to the point at infinity.
  let f : X → Projectivization E (Fin 2 → E) := fun x =>
    if hx : x = inf then Work.PSL2.ptInf E else g ⟨x, hx⟩
  have hf_apply : ∀ (x : X) (hx : x ≠ inf), f x = g ⟨x, hx⟩ := by
    intro x hx
    simp only [f, dif_neg hx]
  have hf_inf : f inf = Work.PSL2.ptInf E := by
    simp only [f, dif_pos rfl]
  have hg_inj : Function.Injective g := by
    intro a b hab
    have h1 : Multiplicative.toAdd (Φ' (e.symm a)) = Multiplicative.toAdd (Φ' (e.symm b)) :=
      ptOf_injective E hab
    have h2 : e.symm a = e.symm b := Φ'.injective (Multiplicative.toAdd.injective h1)
    exact e.symm.injective h2
  have hf_inj : Function.Injective f := by
    intro x y hxy
    by_cases hx : x = inf
    · by_cases hy : y = inf
      · rw [hx, hy]
      · exfalso
        have h' : Work.PSL2.ptInf E = g ⟨y, hy⟩ := by
          simpa only [hx, hf_inf, hf_apply y hy] using hxy
        exact ptOf_ne_ptInf E _ h'.symm
    · by_cases hy : y = inf
      · exfalso
        have h' : g ⟨x, hx⟩ = Work.PSL2.ptInf E := by
          simpa only [hy, hf_inf, hf_apply x hx] using hxy
        exact ptOf_ne_ptInf E _ h'
      · have h1 : (⟨x, hx⟩ : {x : X // x ≠ inf}) = ⟨y, hy⟩ := by
          apply hg_inj
          simpa only [hf_apply x hx, hf_apply y hy] using hxy
        exact congrArg Subtype.val h1
  have hcardX : Nat.card X = p ^ k + 1 := h.2.1
  have hfinrank : Module.finrank E (Fin 2 → E) = 2 := Module.finrank_fin_fun (R := E)
  have hcardP' : Nat.card (Projectivization E (Fin 2 → E)) = Nat.card E + 1 := by
    rw [Projectivization.card_of_finrank (k := E) (V := Fin 2 → E) hfinrank]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, Nat.reduceAdd]
    omega
  have hcardP : Nat.card (Projectivization E (Fin 2 → E)) = p ^ k + 1 := by
    rw [hcardP', hcardE]
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype (Projectivization E (Fin 2 → E)) := Fintype.ofFinite _
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hf_inj, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardP, hcardX]⟩
  -- The inverse of `e` evaluated on a point of `X ∖ {∞}`.
  have hsymm : ∀ (y : X) (hy : y ≠ inf) (v : U), (v : G) • zero = y →
      e.symm ⟨y, hy⟩ = v := by
    intro y hy v hv
    have h1 : (⟨y, hy⟩ : {x : X // x ≠ inf}) = e v :=
      Subtype.ext (hv.symm.trans (he v).symm)
    rw [h1, Equiv.symm_apply_apply]
  -- `U` acts on `ℙ¹(E)` by translations.
  have hU : ∀ (u : U) (x : X), f ((u : G) • x) =
      Work.PSL2.pslUnipotent E (Multiplicative.toAdd (Φ' u)) • f x := by
    intro u x
    by_cases hx : x = inf
    · have hux : (u : G) • x = inf := by
        rw [hx]; exact Work.Zassenhaus.mem_borel_iff.mp (hUB u.2)
      rw [hux, hf_inf, hx, hf_inf]
      exact (Work.ZASS.pslUnipotent_smul_ptInf E _).symm
    · have hux : (u : G) • x ≠ inf := by
        intro hcon
        have h1 : (u : G)⁻¹ • ((u : G) • x) = x := by
          rw [← mul_smul, inv_mul_cancel, one_smul]
        rw [hcon, Work.Zassenhaus.mem_borel_iff.mp ((borel G inf).inv_mem (hUB u.2))] at h1
        exact hx h1.symm
      rw [hf_apply x hx, hf_apply ((u : G) • x) hux]
      simp only [g]
      have h1 : e.symm ⟨(u : G) • x, hux⟩ = u * e.symm ⟨x, hx⟩ := by
        refine hsymm ((u : G) • x) hux (u * e.symm ⟨x, hx⟩) ?_
        rw [Subgroup.coe_mul, mul_smul]
        have h2 : x = ((e.symm ⟨x, hx⟩ : U) : G) • zero := by
          simpa using he (e.symm ⟨x, hx⟩)
        rw [← h2]
      rw [h1, map_mul, toAdd_mul, Work.ZASS.psl_smul_ptOf_unipotent, add_comm]
  -- `H = G_{∞0}` acts on `ℙ¹(E)` by multiplications.
  have hH : ∀ (hh : G) (hhm : hh ∈ pairStab G inf zero), ∃ a : Eˣ,
      φ ⟨hh, hhm⟩ = a ^ 2 ∧ ∀ x : X, f (hh • x) = Work.PSL2.pslDiag E a • f x := by
    intro hh hhm
    obtain ⟨a, ha⟩ := (hφrange (φ ⟨hh, hhm⟩)).mp ⟨⟨hh, hhm⟩, rfl⟩
    have hhB : hh ∈ borel G inf := Work.Zassenhaus.pairStab_le_borel inf zero hhm
    refine ⟨a, ha.symm, ?_⟩
    intro x
    by_cases hx : x = inf
    · have hfix_inf : hh • inf = inf := Work.Zassenhaus.mem_borel_iff.mp hhB
      rw [hx, hfix_inf, hf_inf]
      exact (Work.ZASS.pslDiag_smul_ptInf E a).symm
    · have hfix_inf : hh • inf = inf := Work.Zassenhaus.mem_borel_iff.mp hhB
      have hhx : hh • x ≠ inf := by
        intro hcon
        have h1 : hh⁻¹ • (hh • x) = x := by rw [← mul_smul, inv_mul_cancel, one_smul]
        rw [hcon, Work.Zassenhaus.mem_borel_iff.mp ((borel G inf).inv_mem hhB)] at h1
        exact hx h1.symm
      rw [hf_apply x hx, hf_apply (hh • x) hhx]
      simp only [g]
      have hmem : conjBy hh ((e.symm ⟨x, hx⟩ : U) : G) ∈ U :=
        mem_conjBy_of_subgroupOf_normal hUB hN hhm.2 (e.symm ⟨x, hx⟩).2
      have h1 : e.symm ⟨hh • x, hhx⟩ = ⟨conjBy hh ((e.symm ⟨x, hx⟩ : U) : G), hmem⟩ := by
        refine hsymm (hh • x) hhx ⟨_, hmem⟩ ?_
        rw [Subgroup.coe_mk, conjBy_smul_zero hhm]
        have h2 : x = ((e.symm ⟨x, hx⟩ : U) : G) • zero := by
          simpa using he (e.symm ⟨x, hx⟩)
        rw [← h2]
      rw [h1, hequiv hh hhm ((e.symm ⟨x, hx⟩ : U) : G) (e.symm ⟨x, hx⟩).2]
      rw [ha.symm]
      simp only [pow_two, Work.ZASS.psl_smul_ptOf_diag]
      rfl
  refine ⟨E, hE, hEF, hEc, Φ', φ, Equiv.ofBijective f hbij, hcardE, hφinj, hφrange,
    ?_, ?_, ?_, ?_⟩
  · rw [Equiv.coe_ofBijective]; exact hf_inf
  · rw [Equiv.coe_ofBijective, hf_apply zero (Ne.symm hne)]
    simp only [g]
    have h1 : e.symm ⟨zero, (Ne.symm hne : zero ≠ inf)⟩ = (1 : U) := by
      refine hsymm zero (Ne.symm hne) 1 ?_
      simp
    rw [h1, map_one]
    change Work.PSL2.ptOf E 0 = Work.PSL2.ptZero E
    rw [Work.PSL2.ptZero]
  · intro u x
    exact hU u x
  · intro hh hhm
    obtain ⟨a, ha, hx⟩ := hH hh hhm
    exact ⟨a, ha, hx⟩

end Work.ZASS
