import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.PSL.centralizer_psl_dihedral
import Submission.Work.L2F.Dihedral.sylow_dihedral_group
import Submission.Work.L2F.Conic.circle_card
import Submission.Work.L2F.Involution.lift_sq_neg_one

set_option linter.style.haveILetI false

open scoped MatrixGroups
open Matrix

namespace Work.L2F.PSL

/-! ## Two elementary preliminaries -/

/-- The square of an odd number is `1` modulo `8`: `8 ∣ q ^ 2 - 1` for odd `q`. -/
lemma eight_dvd_sq_sub_one_odd (q : ℕ) (hq : Odd q) : 8 ∣ q ^ 2 - 1 := by
  obtain ⟨k, rfl⟩ := hq
  have h : (2 * k + 1) ^ 2 = 4 * (k * (k + 1)) + 1 := by ring
  rw [h, Nat.add_sub_cancel]
  obtain ⟨j, hj⟩ : 2 ∣ k * (k + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self k)
  exact ⟨j, by rw [hj]; ring⟩

/-- `4` divides `|PSL(2,F)|` for a finite field `F` of odd characteristic.

`|PSL(2,F)| = q(q²-1)/2` with `q = |F|`, and `q` is odd (it is a power of the odd prime
`ringChar F ≠ 2`), so `8 ∣ q² - 1` and hence `8 ∣ 2·|PSL(2,F)|`, i.e. `4 ∣ |PSL(2,F)|`. -/
lemma four_dvd_card_psl (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (_h5 : 5 ≤ Nat.card F) :
    4 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have hchar : ringChar F ≠ 2 := by
    intro h
    haveI : CharP F 2 := h ▸ ringChar.charP F
    exact h2 (CharP.cast_eq_zero F 2)
  have hqodd : Odd (Nat.card F) := by
    obtain ⟨p, hpchar, n, hpprime, hpcard⟩ := FiniteField.card' F
    have hpne2 : p ≠ 2 := by
      intro hp2
      haveI : CharP F p := hpchar
      have hrp : ringChar F = p := ringChar.eq F p
      rw [hp2] at hrp
      exact hchar hrp
    have hpodd : Odd p := hpprime.odd_of_ne_two hpne2
    rw [Nat.card_eq_fintype_card, hpcard]
    exact hpodd.pow
  have h8 : 8 ∣ Nat.card F ^ 2 - 1 := eight_dvd_sq_sub_one_odd (Nat.card F) hqodd
  have hcard := Work.PSL2.card_PSL2_of_odd F hchar
  have h8q : 8 ∣ 2 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
    rw [hcard]
    have h8' : 8 ∣ Fintype.card F ^ 2 - 1 := by rw [← Nat.card_eq_fintype_card]; exact h8
    exact dvd_mul_of_dvd_right h8' (Fintype.card F)
  obtain ⟨k, hk⟩ := h8q
  exact ⟨k, by omega⟩

/-- A Sylow `2`-subgroup `S` of a finite group whose order is divisible by `4` contains an
involution `t` that is central in `S` (so `S ≤ C(t)`).

`S` is a nontrivial finite `2`-group, so its centre is nontrivial
(`IsPGroup.center_nontrivial`); the centre is a `2`-group and `2 ∣ |Z(S)|`, so by Cauchy
(`exists_prime_orderOf_dvd_card'`) it contains an element `c` of order `2`, whose image in `S`
is the desired involution. -/
lemma sylow_exists_central_involution {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : 4 ∣ Nat.card (S : Subgroup G)) :
    ∃ t : G, t ∈ S ∧ orderOf t = 2 ∧ ∀ s ∈ S, s * t = t * s := by
  haveI : Finite ↥(S : Subgroup G) := inferInstance
  have hSne : Nat.card ↥(S : Subgroup G) ≠ 0 := Nat.card_pos.ne'
  haveI : Nontrivial ↥(S : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  have hZ : Nontrivial (Subgroup.center (S : Subgroup G)) :=
    IsPGroup.center_nontrivial (p := 2) S.isPGroup'
  haveI : Finite ↥(Subgroup.center (S : Subgroup G)) := inferInstance
  have hZcyc : IsPGroup 2 (Subgroup.center (S : Subgroup G)) :=
    S.isPGroup'.to_subgroup (Subgroup.center (S : Subgroup G))
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center (S : Subgroup G)) := by
    obtain ⟨n, hn, hcard⟩ := hZcyc.nontrivial_iff_card.mp hZ
    rw [hcard]
    exact dvd_pow_self 2 hn.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  refine ⟨((c : ↥(S : Subgroup G)) : G), (c : ↥(S : Subgroup G)).2, ?_, ?_⟩
  · have h1 : orderOf (c : ↥(S : Subgroup G)) = orderOf c :=
      orderOf_injective (Subgroup.subtype (Subgroup.center (S : Subgroup G)))
        Subtype.coe_injective c
    have h2 : orderOf ((c : ↥(S : Subgroup G)) : G) = orderOf (c : ↥(S : Subgroup G)) :=
      orderOf_injective (Subgroup.subtype (S : Subgroup G)) Subtype.coe_injective _
    rw [h2, h1, hc]
  · intro s hs
    have hcomm : ⟨s, hs⟩ * (c : ↥(S : Subgroup G)) = (c : ↥(S : Subgroup G)) * ⟨s, hs⟩ :=
      Subgroup.mem_center_iff.mp c.2 ⟨s, hs⟩
    have := congrArg (fun x : ↥(S : Subgroup G) => (x : G)) hcomm
    simpa [Subgroup.coe_mul] using this

/-- Every Sylow 2-subgroup of `PSL(2,F)` (`F` finite, `q ≥ 5` odd) is dihedral of order `2n` with
`n ≥ 2`.  Proof: `S` is a nontrivial 2-group, so its centre contains an involution `t`
(`IsPGroup.center_nontrivial` plus Cauchy); then `S ≤ C(t)`, which is dihedral of order `q ∓ 1`
with `[PSL : C(t)] = q(q±1)/2` odd (`Work.PSL2.card_PSL2_of_odd`), so `S` is a Sylow 2-subgroup of
`C(t)`; a Sylow 2-subgroup of a dihedral group is dihedral (`sylow_dihedral_group`); finally
`|S| =` the 2-part of `q(q²-1)/2 ≥ 4`, so `n ≥ 2`. -/
theorem sylow_psl_dihedral (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h5 : 5 ≤ Nat.card F)
    (S : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :
    ∃ n : ℕ, 2 ≤ n ∧
      Nonempty ((S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≃*
        DihedralGroup n) := by
  classical
  haveI : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := inferInstance
  -- `4 ∣ |PSL(2,F)|`, hence the Sylow subgroup has order divisible by `4`.
  have h4 : 4 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    four_dvd_card_psl F h2 h5
  have hS4 : 4 ∣ Nat.card (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
    have := S.pow_dvd_card_of_pow_dvd_card (n := 2) (by simpa using h4)
    simpa using this
  -- A central involution `t` of `S`.
  obtain ⟨t, _htS, ht_order, ht_cent⟩ := sylow_exists_central_involution S hS4
  have hcent : (S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≤
      Subgroup.centralizer ({t} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ht_cent s hs
  -- Lift `t` to `x ∈ SL(2,F)` with `x² = -1`.
  obtain ⟨x, hx_eq, hx_sq⟩ := Work.L2F.Involution.lift_sq_neg_one F h2 t ht_order
  subst hx_eq
  -- `C(t)` is dihedral of order `2m = |circle F|`.
  obtain ⟨m, hm_circle, ⟨e⟩⟩ := Work.L2F.PSL.centralizer_psl_dihedral F h2 x hx_sq
  have hm : m ≠ 0 := by
    haveI : Finite ↥(Work.L2F.circle F) := inferInstance
    haveI : Nonempty ↥(Work.L2F.circle F) := ⟨1⟩
    have : 0 < Nat.card ↥(Work.L2F.circle F) := Nat.card_pos
    omega
  -- `S` is a Sylow 2-subgroup of `C(t)`; push it into `DihedralGroup m`.
  let Sc : Sylow 2 ↥(Subgroup.centralizer ({Work.PSL2.pslMap F x} :
      Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F))) := S.subtype hcent
  let P : Sylow 2 (DihedralGroup m) := Sc.mapSurjective (f := e.toMonoidHom) e.surjective
  -- A Sylow 2-subgroup of a dihedral group is dihedral.
  obtain ⟨n, hcardP, ⟨eP⟩⟩ := Work.L2F.Dihedral.sylow_dihedral_group m hm P
  -- Transport the isomorphism `S ≃* P` back along the two structure maps.
  have ha : ↥(S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≃* ↥Sc :=
    (Subgroup.subgroupOfEquivOfLe hcent).symm
  have hb : ↥Sc ≃* ↥(P : Subgroup (DihedralGroup m)) :=
    Subgroup.equivMapOfInjective Sc.1 e.toMonoidHom e.injective
  refine ⟨n, ?_, ⟨ha.trans (hb.trans eP)⟩⟩
  -- `|S| = |P| = 2n` and `4 ∣ |S|`, so `n ≥ 2`.
  have h1 : Nat.card ↥(P : Subgroup (DihedralGroup m)) =
      Nat.card ↥(S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    (Nat.card_congr hb.toEquiv).symm.trans (Nat.card_congr ha.toEquiv).symm
  have h2n : 2 * n =
      Nat.card ↥(S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) :=
    hcardP.symm.trans h1
  have hSne : Nat.card ↥(S : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) ≠ 0 :=
    Nat.card_pos.ne'
  omega

end Work.L2F.PSL
