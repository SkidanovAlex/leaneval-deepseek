import Mathlib
import Submission.Work.SmallRank.Defs
import Submission.Work.PGroup.Basic
import Submission.Work.SmallRank.exists_maximalOrder_normal_abelian
import Submission.Work.PGroup.centralizer_inf_eq_of_maximal_normal_abelian
import Submission.Work.SmallRank.card_le_prime_of_pgroup_mulAut

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open scoped Classical Pointwise commutatorElement
open Subgroup

noncomputable section
namespace Work.SmallRank

-- The formalisation below follows the plan above with two adjustments: `A` is taken *normal* in
-- `H` and maximal among the abelian normal subgroups of `H`, so that `C_H(A) = A`
-- (`Work.PGroup.centralizer_inf_eq_of_maximal_normal_abelian`) and `H` acts on `A` by conjugation;
-- and `|A| ≤ p ^ 2` is derived from `hE` by Sylow's theorem (`Sylow.exists_subgroup_le_card_pow_
-- prime_of_le_card`).  The bound `|H : A| ≤ p` is then `Work.SmallRank.card_le_prime_of_pgroup_mulAut`.
/-- L2 of the SmallRank plan: an exponent-`p` subgroup of an `E_{p³}`-free `p`-group has order at
most `p^3`.  Direct proof (no L1 needed): let `A` be a maximal abelian subgroup of `H`; if `|A| ≥ p³`
then `A` is elementary abelian of order `≥ p³` (exponent `p` and abelian), so it contains an
elementary abelian subgroup of order `p³`, contradicting `hE`; and if `|A| ≤ p²` then `H/A` embeds
in `Aut(A)`, whose `p`-part is `≤ p` for `|A| ≤ p²`, giving `|H| ≤ p³`. -/
theorem card_le_p3_of_exponent_p {p : ℕ} (hp : p.Prime) {X : Type*} [Group X] [Finite X]
    (hX : IsPGroup p X) (hE : NoElementaryP3 p X) (H : Subgroup X)
    (hexp : ∀ h : H, h ^ p = 1) : Nat.card H ≤ p ^ 3 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨A₀, hA₀norm, hA₀comm, hA₀max⟩ := exists_maximalOrder_normal_abelian (X := ↥H)
  set A : Subgroup X := A₀.map H.subtype with hAdef
  have hAle : A ≤ H := Subgroup.map_subtype_le A₀
  have hAcomm : IsMulCommutative A := Work.PGroup.map_subtype_isMulCommutative H A₀ hA₀comm
  have hAnorm : ∀ g : X, g ∈ H → Work.PGroup.conjBy g A = A := fun g hg =>
    Work.PGroup.map_subtype_conj_eq_self H A₀ (fun g => hA₀norm.conj_smul_eq_self g A₀) g hg
  have hAmax : ∀ B : Subgroup X, B ≤ H → (∀ g : X, g ∈ H → Work.PGroup.conjBy g B = B) →
      IsMulCommutative B → A ≤ B → B = A := by
    intro B hBH hBnorm hBcomm hAB
    have hB'norm : (B.subgroupOf H).Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact Work.PGroup.conjBy_mul_mem (hBnorm (g : X) g.2) hn
    haveI hB'comm : IsMulCommutative ↥(B.subgroupOf H) :=
      Subgroup.comap_injective_isMulCommutative (f := H.subtype) B Subtype.coe_injective
    have hA₀B' : A₀ ≤ B.subgroupOf H := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hAB (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hcard1 : Nat.card ↥(B.subgroupOf H) ≤ Nat.card ↥A₀ := hA₀max _ hB'norm hB'comm
    have hcardB : Nat.card ↥(B.subgroupOf H) = Nat.card ↥B :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
    have hcardA : Nat.card ↥A = Nat.card ↥A₀ := by
      rw [hAdef]
      exact Subgroup.card_map_of_injective (K := A₀) H.subtype_injective
    have hle : Nat.card ↥B ≤ Nat.card ↥A := by rw [← hcardB, hcardA]; exact hcard1
    exact (Subgroup.eq_of_le_of_card_ge hAB hle).symm
  have hC : H ⊓ Subgroup.centralizer (A : Set X) = A :=
    Work.PGroup.centralizer_inf_eq_of_maximal_normal_abelian (p := p) hp H A (hX.to_subgroup H) hAle hAnorm hAcomm hAmax
  have hAelem : Work.PGroup.IsElementaryAbelian p A := by
    refine ⟨hAcomm, fun a => ?_⟩
    refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact congrArg Subtype.val (hexp ⟨a.1, hAle a.2⟩)
  have hAcard : Nat.card A ≤ p ^ 2 := by
    by_contra h
    rw [not_le] at h
    have hAp : IsPGroup p ↥A := hAelem.isPGroup
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hAp
    have hn2 : 2 < n := by
      rw [hn] at h
      exact (Nat.pow_lt_pow_iff_right hp.one_lt).mp h
    have h3 : p ^ 3 ≤ Nat.card A := by
      rw [hn]
      exact Nat.pow_le_pow_right hp.pos (by omega)
    obtain ⟨E, hEA, hEcard⟩ :=
      Sylow.exists_subgroup_le_card_pow_prime_of_le_card (n := 3) hp hX (H := A) h3
    exact hE ⟨E, hAelem.mono hEA, hEcard⟩
  have hHN : H ≤ Subgroup.normalizer (A : Set X) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact Work.PGroup.conjBy_mul_mem (hAnorm g hg) hn
    · intro hn
      have hgn : (g⁻¹) * (g * n * g⁻¹) * (g⁻¹)⁻¹ ∈ A :=
        Work.PGroup.conjBy_mul_mem (hAnorm g⁻¹ (H.inv_mem hg)) hn
      have heq : (g⁻¹) * (g * n * g⁻¹) * (g⁻¹)⁻¹ = n := by group
      rwa [heq] at hgn
  let ψ : ↥H →* MulAut ↥A := (Subgroup.normalizerMonoidHom (H := A)).comp (Subgroup.inclusion hHN)
  have hψker : ψ.ker = A.subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hh
      have hmem : (Subgroup.inclusion hHN h) ∈ (Subgroup.normalizerMonoidHom (H := A)).ker := hh
      rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hmem
      have h2 : (h : X) ∈ H ⊓ Subgroup.centralizer (A : Set X) := ⟨h.2, hmem⟩
      rwa [hC] at h2
    · intro hh
      have hcen : (h : X) ∈ Subgroup.centralizer (A : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact congrArg Subtype.val (isMulCommutative_iff.mp hAcomm ⟨a, ha⟩ ⟨(h : X), hh⟩)
      have hmem : (Subgroup.inclusion hHN h) ∈ (Subgroup.normalizerMonoidHom (H := A)).ker := by
        rw [Subgroup.normalizerMonoidHom_ker]
        exact Subgroup.mem_subgroupOf.mpr hcen
      exact MonoidHom.mem_ker.mp hmem
  have hker_card : Nat.card ↥ψ.ker = Nat.card ↥A := by
    rw [hψker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv]
  have hHp : IsPGroup p ↥H := hX.to_subgroup H
  have hrange_p : IsPGroup p ↥ψ.range :=
    hHp.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  haveI hAcommI : IsMulCommutative ↥A := hAcomm
  letI hAcommG : CommGroup ↥A := IsMulCommutative.instCommGroup
  have hrange_card : Nat.card ↥ψ.range ≤ p :=
    card_le_prime_of_pgroup_mulAut hp hAelem.pow_eq_one hAcard hrange_p (Subgroup.subtype ψ.range) Subtype.coe_injective
  have hidx : ψ.ker.index = Nat.card ↥ψ.range := by
    rw [Subgroup.index_eq_card, Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  have hcardH : Nat.card ↥H = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := by
    calc Nat.card ↥H = Nat.card ↥ψ.ker * ψ.ker.index := (Subgroup.card_mul_index ψ.ker).symm
      _ = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := by rw [hidx]
  have hfinal : Nat.card ↥H ≤ p ^ 3 := by
    rw [hcardH]
    calc Nat.card ↥ψ.ker * Nat.card ↥ψ.range ≤ p ^ 2 * p :=
          Nat.mul_le_mul (by rw [hker_card]; exact hAcard) hrange_card
      _ = p ^ 3 := by ring
  exact absurd hfinal (not_le.mpr hcon)

end Work.SmallRank
