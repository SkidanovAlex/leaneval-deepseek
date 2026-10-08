/-
Group-theoretic inputs for `NOrbProp` (Bender–Glauberman 1981, Theorem 4.3) when `D.n = 2`:
`S ≅ V₄` is a Klein four group, and writing `C = C_G(S)`, `N = N_G(S)` one has `|N : C| ∈ {1,3}`
(`C.relIndex N ∣ 6` by the faithful action of `N/C` on the three non-identity elements of `S`,
and oddness from `S` being a Sylow `2`-subgroup with `S ≤ C`).

`caseA_nOrbCosets` is then the statement of `Work.BG.nOrbCosets` proved from these two lemmas
and `Work.BG.nOrbCosetIndexThree` (the coset covering for a normal subgroup of index `3`).
-/
import Mathlib
import Submission.Work.BG.Defs
import Submission.Work.BG.nOrbCosets
import Submission.Work.BG.nOrbCosetIndexThree

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2

/-- The action of `MulAut V` on the non-identity elements of `V`, as a homomorphism into the
symmetric group on that set. -/
noncomputable def caseA_mulAutPerm (V : Type*) [Group V] :
    MulAut V →* Equiv.Perm {x : V // x ≠ 1} where
  toFun σ :=
    { toFun := fun x => ⟨σ x.1, fun h => x.2 (σ.injective (by rw [h, map_one]))⟩
      invFun := fun x => ⟨σ.symm x.1, fun h => x.2 (σ.symm.injective (by rw [h, map_one]))⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply x.1) }
  map_one' := by ext x; rfl
  map_mul' := by intro σ τ; ext x; rfl

/-- `MulAut V` acts faithfully on the non-identity elements of `V`. -/
theorem caseA_mulAutPerm_injective (V : Type*) [Group V] :
    Function.Injective (caseA_mulAutPerm V) := by
  intro σ τ h
  have h' : ∀ x : V, x ≠ 1 → σ x = τ x := by
    intro x hx
    have h2 := congrArg (fun p : Equiv.Perm {x : V // x ≠ 1} => (p ⟨x, hx⟩ : V)) h
    exact h2
  ext x
  by_cases hx : x = 1
  · rw [hx, map_one, map_one]
  · exact h' x hx

/-- `|Aut V| ∣ 6` for a finite group `V` with `|V| = 4`. -/
theorem caseA_mulAut_card_dvd_six {V : Type*} [Group V] [Fintype V]
    (hV : Fintype.card V = 4) : Nat.card (MulAut V) ∣ 6 := by
  classical
  have hinj : Function.Injective (caseA_mulAutPerm V) := caseA_mulAutPerm_injective V
  have hker : (caseA_mulAutPerm V).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hinj
  have hrange : Nat.card ↥(caseA_mulAutPerm V).range ∣
      Nat.card (Equiv.Perm {x : V // x ≠ 1}) := Subgroup.card_subgroup_dvd_card _
  have hperm : Nat.card (Equiv.Perm {x : V // x ≠ 1}) = 6 := by
    have h3 : Fintype.card {x : V // x ≠ 1} = 3 := by
      have hc := Fintype.card_subtype_compl (fun x : V => x = 1)
      rw [Fintype.card_subtype_eq, hV] at hc
      omega
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, h3]
    norm_num
  have hcard : Nat.card (MulAut V) = Nat.card ↥(caseA_mulAutPerm V).range := by
    have hc := Subgroup.card_ker_mul_card_range (caseA_mulAutPerm V)
    rw [hker] at hc
    have hbot : Nat.card ↥(⊥ : Subgroup (MulAut V)) = 1 := Subgroup.card_bot
    rw [hbot, one_mul] at hc
    exact hc.symm
  rw [hperm] at hrange
  rw [hcard]
  exact hrange

/-- `|N_G(V) : C_G(V)| ∣ 6` for a subgroup `V` of order `4`. -/
theorem caseA_nOrbIndexDvdSix {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : Nat.card ↥V = 4) :
    (Subgroup.centralizer (V : Set G)).relIndex (Subgroup.normalizer (V : Set G)) ∣ 6 := by
  haveI : Fintype ↥V := Fintype.ofFinite _
  have hker := Subgroup.normalizerMonoidHom_ker V
  have hindex : (Subgroup.centralizer (V : Set G)).relIndex (Subgroup.normalizer (V : Set G))
      = Nat.card ↥((Subgroup.normalizerMonoidHom V).range) := by
    change ((Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G))).index = _
    rw [Subgroup.index_eq_card, ← hker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (Subgroup.normalizerMonoidHom V)).toEquiv
  rw [hindex]
  refine dvd_trans (Subgroup.card_subgroup_dvd_card _) ?_
  refine caseA_mulAut_card_dvd_six ?_
  rw [Fintype.card_eq_nat_card]
  exact hV

/-- `|N_G(S) : C_G(S)|` is odd for an abelian Sylow `2`-subgroup `S`. -/
theorem caseA_nOrbIndexOdd {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (hcomm : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y = y * x) :
    Odd ((Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex
      (Subgroup.normalizer ((S : Subgroup G) : Set G))) := by
  set V : Subgroup G := (S : Subgroup G) with hVdef
  have hSV : V ≤ Subgroup.centralizer (V : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y hy).symm
  have h1 : (Subgroup.centralizer (V : Set G)).relIndex (Subgroup.normalizer (V : Set G))
      ∣ V.relIndex (Subgroup.normalizer (V : Set G)) :=
    Subgroup.relIndex_dvd_of_le_left _ hSV
  have h2 : V.relIndex (Subgroup.normalizer (V : Set G)) ∣ V.index :=
    Subgroup.relIndex_dvd_index_of_le (Subgroup.le_normalizer)
  have h3 : Odd V.index := by
    have hnot : ¬ 2 ∣ V.index := by
      rw [hVdef]
      exact Sylow.not_dvd_index S
    exact Nat.not_even_iff_odd.mp fun he => hnot (even_iff_two_dvd.mp he)
  exact Odd.of_dvd_nat h3 (dvd_trans h1 h2)

end Work.BG
