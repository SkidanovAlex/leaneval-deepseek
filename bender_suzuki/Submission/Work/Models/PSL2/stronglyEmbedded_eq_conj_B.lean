import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.B_maximal
import Submission.Work.Models.PSL2.centralizer_unip
import Submission.Work.Models.PSL2.normalizer_U
import Submission.Work.Models.PSL2.involution_conj
import Submission.Work.Models.PSL2.B_stronglyEmbedded
import Submission.Work.Models.PSL2.orderOf_unip_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.PSL2.stronglyEmbedded_eq_conj_B`

In `G = SL(2,F)` for `F` a finite field of characteristic `2`, the strongly embedded
subgroups are exactly the conjugates of the standard Borel `B` (the upper triangular
matrices).

The argument is Bender's, in its shortest form for a group with a rank-one BN-pair:

* A strongly embedded subgroup `M` has even order, so it contains an involution `t`
  (`exists_involution_of_isStronglyEmbedded`, Cauchy's theorem).
* All involutions of `SL(2,F)` are conjugate (`involution_conj`), so `t = g u g⁻¹` for
  `u = unip 1` the standard transvection; conjugating the whole problem by `g` we may
  assume `u ∈ M`.
* A strongly embedded subgroup contains the centralizer of each of its involutions
  (`centralizer_le_of_isStronglyEmbedded`), so `U = C_G(unip 1) ≤ M` (`centralizer_unip`).
* A strongly embedded subgroup contains the normalizer of each of its *even-order*
  subgroups (`Work.Models.IsStronglyEmbedded.normalizer_le_of_le`), so
  `B = N_G(U) ≤ M` (`normalizer_U`).
* `B` together with any one element outside it generates `G`
  (`Work.Models.PSL2.B_maximal`), so a proper subgroup containing `B` is exactly `B`.
  As `M ≠ ⊤`, this gives `M = B`, hence the original `M` is a conjugate of `B`.

The two consequences of strong embeddedness are invoked at the *base* subgroup
(`M` after conjugation by `g`, so that it contains the standard transvection), which avoids
any transport of centralizers or normalizers along conjugation.
-/

namespace Work.Models.PSL2

open Matrix

/-- A strongly embedded subgroup of a finite group has even order, hence contains an element
of order `2` (Cauchy's theorem). -/
theorem exists_involution_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    ∃ t ∈ H, orderOf t = 2 := by
  have h2 : 2 ∣ Nat.card ↥H := even_iff_two_dvd.mp hH.2.1
  obtain ⟨x, hx⟩ :=
    @exists_prime_orderOf_dvd_card' ↥H _ _ 2 ⟨Nat.prime_two⟩ h2
  exact ⟨(x : G), x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

/-- A strongly embedded subgroup contains the centralizer of each of its involutions: an
element `x ∉ H` commuting with the involution `t ∈ H` would put `t` into `H ⊓ H^x`, a group
of odd order.  (Universe-polymorphic form of `Work.Reductions.stronglyEmbedded_centralizer_le`.) -/
theorem centralizer_le_of_isStronglyEmbedded {G : Type*} [Group G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : t ∈ H)
    (h2 : orderOf t = 2) : Subgroup.centralizer ({t} : Set G) ≤ H := by
  intro x hx
  by_contra hxH
  have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have htK : t ∈ H ⊓ H.map (MulAut.conj x).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨ht, ?_⟩
    rw [Subgroup.mem_map]
    refine ⟨t, ht, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hcomm]
    group
  have hKorder : orderOf (⟨t, htK⟩ : ↥(H ⊓ H.map (MulAut.conj x).toMonoidHom)) = 2 := by
    rw [Subgroup.orderOf_mk, h2]
  have hdvd : 2 ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj x).toMonoidHom) := by
    have h := Subgroup.card_subgroup_dvd_card
      (Subgroup.zpowers (⟨t, htK⟩ : ↥(H ⊓ H.map (MulAut.conj x).toMonoidHom)))
    rwa [Nat.card_zpowers, hKorder] at h
  exact (Nat.not_even_iff_odd.mpr (hH.2.2 x hxH)) (even_iff_two_dvd.mpr hdvd)

/-- A subgroup of `SL(2,F)` containing the standard Borel `B` and different from `B` is
everything: `B` is a maximal subgroup (this is `B_maximal`, read in the form we need). -/
theorem eq_B_of_le_of_ne_top {F : Type*} [Field F] [CharP F 2] (K : Subgroup (SL2 F))
    (hB : B (F := F) ≤ K) (hne : K ≠ ⊤) : K = B (F := F) := by
  by_contra hne'
  exact hne (B_maximal K hB hne')

/-- **The strongly embedded subgroups of `SL(2,F)`, `F` a finite field of characteristic
`2`, are the conjugates of the standard Borel.** -/
theorem stronglyEmbedded_eq_conj_B {F : Type*} [Field F] [CharP F 2] [Finite F]
    (M : Subgroup (Work.Models.SL2 F))
    (hM : LeanEval.GroupTheory.Defs.IsStronglyEmbedded M) :
    ∃ g : Work.Models.SL2 F, M = Submission.Blueprint.conj g (Work.Models.PSL2.B (F := F)) := by
  -- an involution of `M`
  obtain ⟨t, htM, ht2⟩ := exists_involution_of_isStronglyEmbedded hM
  have ht_sq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h
    exact h
  have ht_ne : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by decide)
  -- all involutions are conjugate, so `M^g` contains the standard transvection `unip 1`
  obtain ⟨g, hg⟩ := involution_conj t ht_sq ht_ne
  have hMconj : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (Submission.Blueprint.conj g M) :=
    Work.Models.IsStronglyEmbedded.conj hM g
  have hunip_mem : unip (F := F) 1 ∈ Submission.Blueprint.conj g M := by
    rw [Work.Models.mem_conj_iff]
    have h : g⁻¹ * unip (F := F) 1 * g = t := by rw [← hg]; group
    rw [h]; exact htM
  -- a strongly embedded subgroup contains the centralizer of each of its involutions
  have hUle : U (F := F) ≤ Submission.Blueprint.conj g M := by
    rw [← centralizer_unip (F := F)]
    exact centralizer_le_of_isStronglyEmbedded hMconj hunip_mem (orderOf_unip_one (F := F))
  -- ... and the normalizer of each of its even-order subgroups
  have hUeven : Even (Nat.card ↥(U (F := F))) := by
    have h := Subgroup.orderOf_dvd_natCard (U (F := F)) (unip_mem_U (F := F) 1)
    rw [orderOf_unip_one (F := F)] at h
    exact even_iff_two_dvd.mpr h
  have hBle : B (F := F) ≤ Submission.Blueprint.conj g M := by
    rw [← normalizer_U (F := F)]
    exact Work.Models.IsStronglyEmbedded.normalizer_le_of_le hMconj hUle hUeven
  -- `B` is maximal and `M^g` is proper, so `M^g = B`
  have hne_top : Submission.Blueprint.conj g M ≠ ⊤ := fun htop =>
    hM.1 (Work.Models.conj_eq_top_iff.mp htop)
  have hMB : Submission.Blueprint.conj g M = B (F := F) := eq_B_of_le_of_ne_top _ hBle hne_top
  exact ⟨g⁻¹, by rw [← Work.Models.conj_inv_conj g M, hMB]⟩

end Work.Models.PSL2
