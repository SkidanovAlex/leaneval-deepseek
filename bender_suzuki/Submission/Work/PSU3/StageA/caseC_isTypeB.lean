import Mathlib
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_zeta_action
import Submission.Work.PSU3.StageA.caseC_fpfXi
import Submission.Work.PSU3.StageA.caseC_W_semireg
import Submission.Work.Higman.typeB_of_odd_fpf
import Submission.Work.ThmF.ChV12.W_layer_safe

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageA

/-- **Case c) is of Higman type B.**

With `q = |Q₀| = |Q0sub H|`, `|Q| = q³`, `W = C_V(K) ≠ 1` and the semiregularity hypothesis
`hW`, the `K`-action `ξ = ξ = xi_{caseC_xi}` on `Q` makes `Q` of type `B`: every `ζ ∈ W^#` moves
every `ξ`-invariant layer `M` (a subgroup of order `q²` containing `Z(Q) = Q₀`), so
`Work.Higman.typeB_of_odd_fpf` applies.

The only new ingredient relative to `Work.ThmF.ChV12.WLayerSafe.W_layer_not_preserved` is that,
instead of the divisibility `|W| ∣ q + 1`, we use the *elementwise* statement
`orderOf ζ ∣ q + 1` of `Work.PSU3.StageA.caseC_zeta_action`: if `ζ` preserved a layer `M`, the
free action of `⟨conj ζ⟩` on `M ∖ Z(Q)` (semiregularity) would give `orderOf ζ ∣ q² - q`, and
`gcd(q² - q, q + 1) ∣ 2` forces `orderOf ζ = 1`, contradicting `ζ ≠ 1`. -/
theorem caseC_isTypeB {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hcard : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H)
    {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) (hζ1 : ζ ≠ 1) :
    Work.Higman.IsTypeB (Work.PSU3.StageA.caseC_xi hS hC4
      (Work.PSU3.StageA.caseC_W_ne_bot (Q := Q) hζ hζ1)) := by
  classical
  have hWne : Work.ThmF.W H t ≠ ⊥ := Work.PSU3.StageA.caseC_W_ne_bot (Q := Q) hζ hζ1
  show Work.Higman.IsTypeB (Work.PSU3.StageA.caseC_xi hS hC4 hWne)
  -- ## structural facts
  have hSuz2 : Work.Higman.IsSuzuki2Grp ↥Q := caseC_isSuzuki2Grp hS hC4 hnab hZ hWne
  have hfpf : Work.Higman.FpfXi (Work.PSU3.StageA.caseC_xi hS hC4 hWne) :=
    caseC_fpfXi hS hC4 hHig hcard hζ hζ1
  have hZeq : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    caseC_center_subgroupOf hS hHig hZ hSuz2
  have hZcard : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hZeq]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q0sub_le_Q hS.split)).toEquiv
  -- ## `ζ` lies in `D = twoPoint H t`, hence normalises `Q`
  have hζD : ζ ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint t (Work.ThmF.W_le_centD H t hζ)
  have hζN : ζ ∈ Subgroup.normalizer (Q : Set G) := hS.split.normal (Subgroup.mem_inf.mp hζD).1
  have hζz : ∀ z ∈ Work.ThmF.Q0sub H, z * ζ = ζ * z :=
    Subgroup.mem_centralizer_iff.mp (W_le_centralizer_Q0sub hS hC4 hζ)
  -- ## the generator `k` of `K = Ksub H t` and the identification `ξ = conjOnQ k`
  set k : G := ((caseC_gen hS hC4 hWne : ↥(Work.ThmF.Ksub H t)) : G) with hk
  have hkK : k ∈ Work.ThmF.Ksub H t := by rw [hk]; exact (caseC_gen hS hC4 hWne).2
  have hkKset : k ∈ Work.ThmF.Kset H t := caseC_gen_mem_Kset hS hC4 hWne
  have hkN : k ∈ Subgroup.normalizer (Q : Set G) := caseC_gen_mem_normalizer hS hC4 hWne
  have hξdef : Work.PSU3.StageA.caseC_xi hS hC4 hWne = conjOnQ k hkN := by
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    have h := caseC_xi_pow_coe hS hC4 hWne 1 y
    simp only [pow_one] at h
    rw [h, conjOnQ_coe, hk]
  have hζk : ζ * k = k * ζ := ((Work.ThmF.le_W_iff.mp hζ).2 k hkKset).symm
  -- ## the conjugation action `A` of `ζ` on `Q`
  set A : MulAut ↥Q := conjOnQ ζ hζN with hAdef
  have hA_coe : ∀ (j : ℕ) (x : ↥Q),
      (((A ^ j) x : ↥Q) : G) = ζ ^ j * (x : G) * (ζ ^ j)⁻¹ := by
    intro j x
    rw [hAdef]
    exact conjOnQ_pow_coe ζ hζN j x
  have hA_coe1 : ∀ x : ↥Q, ((A x : ↥Q) : G) = ζ * (x : G) * ζ⁻¹ := by
    intro x
    rw [hAdef]
    exact conjOnQ_coe ζ hζN x
  -- ## `A` commutes with `ξ`
  have hcomm : A * (Work.PSU3.StageA.caseC_xi hS hC4 hWne)
      = (Work.PSU3.StageA.caseC_xi hS hC4 hWne) * A := by
    rw [hξdef, hAdef]
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    simp only [MulAut.mul_apply, conjOnQ_coe]
    rw [show ζ * (k * (z : G) * k⁻¹) * ζ⁻¹ = (ζ * k) * (z : G) * (ζ * k)⁻¹ from by group,
      show (ζ * k) * (z : G) * (ζ * k)⁻¹ = (k * ζ) * (z : G) * (k * ζ)⁻¹ from by rw [hζk],
      show (k * ζ) * (z : G) * (k * ζ)⁻¹ = k * (ζ * (z : G) * ζ⁻¹) * k⁻¹ from by group]
  -- ## order facts: `Odd (orderOf A)`, `A ≠ 1`
  have hζodd : Odd (orderOf ζ) := by
    have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
      Work.ThmF.split_odd_card_twoPoint hS.split
    have hdvd : orderOf ζ ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      rw [Subgroup.orderOf_coe (⟨ζ, hζD⟩ : ↥(Submission.Blueprint.twoPoint H t))]
      exact orderOf_dvd_natCard _
    exact hodd.of_dvd_nat hdvd
  have hdvd_ord : orderOf A ∣ orderOf ζ := by
    rw [orderOf_dvd_iff_pow_eq_one, hAdef]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [conjOnQ_pow_coe, pow_orderOf_eq_one]
    simp
  have hoddA : Odd (orderOf A) := hζodd.of_dvd_nat hdvd_ord
  have hw1 : A ≠ 1 := by
    intro hA
    have hcent : ∀ q ∈ Q, ζ * q = q * ζ := by
      intro q hq
      have h1 : ζ * q * ζ⁻¹ = q :=
        (conjOnQ_eq_one_iff ζ hζN).mp (hAdef ▸ hA) q hq
      calc ζ * q = (ζ * q * ζ⁻¹) * ζ := by group
        _ = q * ζ := by rw [h1]
    exact hζ1 (eq_one_of_centralizes_Q hS hζD hcent)
  -- ## `ζ` preserves no `ξ`-invariant layer
  have hfree : ∀ M : Subgroup ↥Q,
      Work.Higman.IsXiLayer (Work.PSU3.StageA.caseC_xi hS hC4 hWne) M →
      M.map A.toMonoidHom ≠ M := by
    intro M hM hMinv
    obtain ⟨hZle, -, hMcard⟩ := hM
    have hfixZ : ∀ z ∈ Subgroup.center ↥Q, A z = z := by
      intro z hz
      have hzQ0 : (z : G) ∈ Work.ThmF.Q0sub H :=
        Subgroup.mem_subgroupOf.mp (hZeq ▸ hz)
      apply Subtype.ext
      rw [hA_coe1 z, ← hζz (z : G) hzQ0]
      group
    have hfixed : ∀ j : ℕ, 0 < j → A ^ j ≠ 1 → ∀ x ∈ M, (A ^ j) x = x →
        x ∈ Subgroup.center ↥Q := by
      intro j _ hAne x _ hfix
      have hζj_ne : ζ ^ j ≠ 1 := by
        intro h1
        apply hAne
        apply MulEquiv.ext
        intro y
        apply Subtype.ext
        rw [hA_coe j y, h1]
        simp
      have hxcomm : ζ ^ j * (x : G) = (x : G) * ζ ^ j := by
        have h1 : (((A ^ j) x : ↥Q) : G) = (x : G) := by
          simpa using congrArg (fun y : ↥Q => (y : G)) hfix
        rw [hA_coe j x] at h1
        calc ζ ^ j * (x : G) = (ζ ^ j * (x : G) * (ζ ^ j)⁻¹) * ζ ^ j := by group
          _ = (x : G) * ζ ^ j := by rw [h1]
      have hxQ0 : (x : G) ∈ Work.ThmF.Q0sub H :=
        hW (ζ ^ j) ((Work.ThmF.W H t).pow_mem hζ j) hζj_ne (x : G) x.2 hxcomm
      rw [hZeq]
      exact Subgroup.mem_subgroupOf.mpr hxQ0
    have hdvdM : orderOf A ∣ Nat.card ↥M - Nat.card ↥(Subgroup.center ↥Q) :=
      Work.ThmF.ChV12.WLayerSafe.dvd_card_sub_of_free_on_compl A (Subgroup.center ↥Q) M
        hZle hMinv hfixZ hfixed
    have hdvd1 : orderOf A ∣
        Nat.card ↥(Work.ThmF.Q0sub H) ^ 2 - Nat.card ↥(Work.ThmF.Q0sub H) := by
      rw [← hZcard, ← hMcard]
      exact hdvdM
    have hdvd2 : orderOf A ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1 :=
      hdvd_ord.trans
        (caseC_zeta_action hS hC4 hHig hcard hnab hZ hW hζ hζ1).1
    have hq : ∃ n : ℕ, Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n :=
      exists_card_Q0sub_eq_two_pow hS hC4
    have h1 : orderOf A = 1 :=
      Work.ThmF.ChV12.WLayerSafe.eq_one_of_dvd_pow_two_sub_and_dvd_add_one
        hq hoddA hdvd1 hdvd2
    exact hw1 (orderOf_eq_one_iff.mp h1)
  exact Work.Higman.typeB_of_odd_fpf hSuz2 hfpf hcomm hoddA hw1 hfree

end Work.PSU3.StageA
