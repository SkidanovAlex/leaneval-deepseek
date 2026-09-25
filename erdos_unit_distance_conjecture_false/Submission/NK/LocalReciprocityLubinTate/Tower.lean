import Submission.NK.LocalReciprocityLubinTate.Basic

/-!
# Consequences of the Lubin–Tate tower: the existence theorem

`NK.LocalReciprocityLubinTate.LubinTateTower` (in `Basic.lean`) is the classical output of
Lubin–Tate theory: a two-parameter family of finite abelian levels `E_{m,n}` of `F^{ab}` whose norm
groups are `⟨π^{m+1}⟩ · U^{n+1}`.  (The structure has five fields; the local Kronecker–Weber field
`exhaust` was deleted in §16.2 of `README.md` because no theorem of the chapter consumes it.)

This file derives the first classical consequence: the **existence theorem** of local class field
theory,

`NK.LocalCFT.ExistenceTheorem F F'`:  every finite-index subgroup `M ≤ Fˣ` contains the norm group
`N_{L/F} Lˣ` of a finite abelian extension `L/F`

(Serre, *Local Fields*, Ch. XI §2; Neukirch, *Algebraic Number Theory*, V §4).  The classical proof
is exactly the argument formalised here:

* a finite-index subgroup contains a positive power `π^k` of the uniformiser
  (`exists_pow_mem_of_finiteIndex`), and
* it contains `U^n` for large `n`, because the groups `U^n` are cofinal among the finite-index
  subgroups of `Fˣ` (`NK.LocalReciprocityLubinTate.higherUnits_cofinal`),

so it contains the norm group `⟨π^k⟩ · U^n` of the Lubin–Tate level `E_{k-1,n-1}`.

## Main results

* `NK.LocalReciprocityLubinTate.exists_pow_mem_of_finiteIndex`;
* `NK.LocalReciprocityLubinTate.existenceTheorem_of_tower`.
-/

open scoped ValuativeRel

namespace NK.LocalReciprocityLubinTate

universe u v

noncomputable section

/-- **A finite-index subgroup contains a positive power of every element.**  (Applied to the
uniformiser `π ∈ Fˣ`, this is the statement that some power of `π` lies in the given norm group, the
first step of the existence theorem; in the abelian group `Fˣ` every subgroup is normal, so the
quotient `G ⧸ M` is a group and Lagrange's theorem applies.) -/
theorem exists_pow_mem_of_finiteIndex {G : Type*} [Group G] (M : Subgroup G) [M.Normal]
    (hM : M.FiniteIndex) (g : G) : ∃ k : ℕ, 0 < k ∧ g ^ k ∈ M := by
  have hcard : Nat.card (G ⧸ M) ≠ 0 := by
    rw [← Subgroup.index_eq_card]
    exact Subgroup.finiteIndex_iff.mp hM
  have hFin : Finite (G ⧸ M) := (Nat.card_ne_zero.mp hcard).2
  letI := hFin
  haveI : Fintype (G ⧸ M) := Fintype.ofFinite _
  refine ⟨Fintype.card (G ⧸ M), ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]; exact Nat.pos_of_ne_zero hcard
  · have h1 : (QuotientGroup.mk' M g) ^ Fintype.card (G ⧸ M) = 1 := pow_card_eq_one
    have h2 : QuotientGroup.mk' M (g ^ Fintype.card (G ⧸ M)) = 1 := by rw [map_pow, h1]
    rw [QuotientGroup.mk'_apply] at h2
    exact (QuotientGroup.eq_one_iff (g ^ Fintype.card (G ⧸ M))).mp h2

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']

/-- **The existence theorem from the Lubin–Tate tower.**

Let `T` be a Lubin–Tate tower with norm groups `⟨π^{m+1}⟩ · U^{n+1}`, and assume
that the filtration `U` is decreasing and cofinal among the finite-index subgroups of `Fˣ`.  Then
every finite-index subgroup `M ≤ Fˣ` contains the norm group of one of the levels `E_{m,n}`, which
is precisely the existence theorem of local class field theory.

The proof is the classical one: `M` contains `π^k` for some `k > 0` and `U^n` for some `n`, hence
contains `⟨π^k⟩ · U^n = N_{E_{k-1,n-1}/F} E_{k-1,n-1}ˣ`. -/
theorem existenceTheorem_of_tower {π : Fˣ} {U : ℕ → Subgroup Fˣ} {q : ℕ}
    (T : LubinTateTower F F' π U q) (hUanti : Antitone U)
    (hU : ∀ M : Subgroup Fˣ, M.FiniteIndex → ∃ n, U n ≤ M) :
    NK.LocalCFT.ExistenceTheorem F F' := by
  intro M hM
  obtain ⟨k, hk, hkg⟩ := exists_pow_mem_of_finiteIndex M hM π
  obtain ⟨n, hn⟩ := hU M hM
  refine ⟨T.level (k - 1) n, T.finiteDimensional _ _, T.normal _ _, T.commutative _ _, ?_⟩
  rw [T.normGroup_eq]
  refine sup_le ?_ ((hUanti (Nat.le_succ n)).trans hn)
  rw [Nat.sub_add_cancel hk]
  exact Subgroup.zpowers_le.mpr hkg

end

end NK.LocalReciprocityLubinTate
