import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Prelim
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.bender_prelim
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-! ## Supporting lemmas on the action on `Ω = G ⧸ H` -/

/-- Two distinct conjugates of a strongly embedded subgroup `H` are exchanged by an involution:
if `aH ≠ bH` are points of `Ω`, the lemma `Work.ThreePoints.exists_involution_smul_eq_of_ne`
provides an involution `τ` with `τ • aH = bH`, and the stabiliser of a point is the corresponding
conjugate of `H`. -/
theorem exists_involution_conj_conj {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {a b : G} (hne : conj a H ≠ conj b H) :
    ∃ τ : G, orderOf τ = 2 ∧ conj τ (conj a H) = conj b H := by
  classical
  have hab : (a : G ⧸ H) ≠ (b : G ⧸ H) := by
    intro hc
    apply hne
    rw [Work.DoubleTransitivity.mk_eq_mk_iff] at hc
    calc conj a H = conj a (conj (a⁻¹ * b) H) := by
          rw [Work.ThreePoints.conj_eq_self_of_mem hc]
      _ = conj (a * (a⁻¹ * b)) H := (Work.DoubleTransitivity.conj_mul a (a⁻¹ * b) H).symm
      _ = conj b H := by rw [show a * (a⁻¹ * b) = b from by group]
  obtain ⟨τ, hτ2, hτ⟩ := Work.ThreePoints.exists_involution_smul_eq_of_ne hH hab
  refine ⟨τ, hτ2, ?_⟩
  have h1 : MulAction.stabilizer G (τ • (a : G ⧸ H)) =
      (MulAction.stabilizer G (a : G ⧸ H)).map (MulAut.conj τ).toMonoidHom :=
    MulAction.stabilizer_smul_eq_stabilizer_map_conj τ (a : G ⧸ H)
  rw [hτ] at h1
  rw [Work.ThreePoints.stabilizer_mk H b] at h1
  rw [Work.ThreePoints.stabilizer_mk H a] at h1
  exact h1.symm

/-- The point stabiliser `H` is transitive on the conjugates of `H` different from `H`:
this is the "rank one" half of the double transitivity of `G` on `Ω = G ⧸ H`. -/
theorem exists_mem_conj_conj_of_ne {G : Type} [Group G] {H : Subgroup G}
    (hTT : IsTwoTransitiveOn H) {a b : G} (ha : conj a H ≠ H) (hb : conj b H ≠ H) :
    ∃ y ∈ H, conj y (conj a H) = conj b H := by
  classical
  have h2 : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := hTT
  rw [MulAction.is_two_pretransitive_iff] at h2
  have ha' : (Work.DoubleTransitivity.pt H : G ⧸ H) ≠ (a : G ⧸ H) := by
    intro hc
    exact ha (Work.ThreePoints.conj_eq_self_of_mem
      ((Work.DoubleTransitivity.mk_one_eq_iff (H := H)).mp hc.symm))
  have hb' : (Work.DoubleTransitivity.pt H : G ⧸ H) ≠ (b : G ⧸ H) := by
    intro hc
    exact hb (Work.ThreePoints.conj_eq_self_of_mem
      ((Work.DoubleTransitivity.mk_one_eq_iff (H := H)).mp hc.symm))
  obtain ⟨y, hy1, hy2⟩ := h2 ha' hb'
  refine ⟨y, ?_, ?_⟩
  · rw [← Work.DoubleTransitivity.conj_one (H := H),
      Work.DoubleTransitivity.mem_conj_iff_smul_fixed (x := (1 : G)) (H := H)]
    exact hy1
  · have h1 : MulAction.stabilizer G (y • (a : G ⧸ H)) =
        (MulAction.stabilizer G (a : G ⧸ H)).map (MulAut.conj y).toMonoidHom :=
      MulAction.stabilizer_smul_eq_stabilizer_map_conj y (a : G ⧸ H)
    rw [hy2] at h1
    rw [Work.ThreePoints.stabilizer_mk H b] at h1
    rw [Work.ThreePoints.stabilizer_mk H a] at h1
    exact h1.symm

/-- **The heart of Ch. I §6 Corollary 1.**  If `s` and `t` are involutions outside the strongly
embedded subgroup `H`, then `H` conjugates `s` to `t`.

Two involutions outside `H` lie in two conjugates `H(s) = conj a H`, `H(t) = conj b H` of `H`
(which contain `s`, resp. `t`).  By double transitivity `H` carries `H(s)` to `H(t)`, so
`conj y s ∈ conj b H`, and the two involutions `conj y s` and `t` lie in the conjugate
`conj b H`.  The involution `τ` conjugating `conj b H` back to `H` makes `conj b H ∩ H` a
two-point stabiliser of `conj b H`; by `BenderPrelimProp` it acts transitively on the involutions
of `conj b H`, so some `d ∈ conj b H ∩ H ⊆ H` conjugates `conj y s` to `t`; then `h = d y ∈ H`
conjugates `s` to `t`. -/
theorem exists_mem_conj_of_involutions_outside {G : Type} [Group G] [Finite G]
    (sit : Situation G) (hA : ThmAProp) (hBP : BenderPrelimProp)
    {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {s t : G} (hs : orderOf s = 2) (ht : orderOf t = 2) (hsH : s ∉ H) (htH : t ∉ H) :
    ∃ h ∈ H, h * s * h⁻¹ = t := by
  classical
  have hTT : IsTwoTransitiveOn H := hA G sit.1.1 H hH
  obtain ⟨a, hsa⟩ := Work.ThreePoints.exists_conj_mem hH hs
  obtain ⟨b, htb⟩ := Work.ThreePoints.exists_conj_mem hH ht
  have ha_ne : conj a H ≠ H := fun hc => hsH (by rw [← hc]; exact hsa)
  have hb_ne : conj b H ≠ H := fun hc => htH (by rw [← hc]; exact htb)
  obtain ⟨y, hyH, hyconj⟩ := exists_mem_conj_conj_of_ne hTT ha_ne hb_ne
  have hys_mem : MulAut.conj y s ∈ conj b H := by
    rw [← hyconj]
    exact Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hsa
  have hys2 : orderOf (MulAut.conj y s) = 2 := by
    rw [MulEquiv.orderOf_eq, hs]
  obtain ⟨τ, hτ2, hτconj⟩ :=
    exists_involution_conj_conj (a := b) (b := 1) hH
      (by rw [Work.DoubleTransitivity.conj_one]; exact hb_ne)
  rw [Work.DoubleTransitivity.conj_one] at hτconj
  have hτnot : τ ∉ conj b H := by
    intro hmem
    have hfix : conj τ (conj b H) = conj b H := Work.ThreePoints.conj_eq_self_of_mem hmem
    rw [hτconj] at hfix
    exact hb_ne hfix.symm
  have hse_b : IsStronglyEmbedded (conj b H) := Work.ThreePoints.conj_stronglyEmbedded hH b
  obtain ⟨d, hd, hdd⟩ :=
    hBP G sit (conj b H) hse_b τ hτ2 hτnot (MulAut.conj y s) ⟨hys_mem, hys2⟩ t ⟨htb, ht⟩
  have hdH : d ∈ H := by
    have hd' : d ∈ conj b H ⊓ conj τ (conj b H) := hd
    rw [hτconj] at hd'
    exact hd'.2
  refine ⟨d * y, H.mul_mem hdH hyH, ?_⟩
  rw [show d * y * s * (d * y)⁻¹ = d * MulAut.conj y s * d⁻¹ from by
        rw [MulAut.conj_apply]; group]
  exact hdd

/-! ## The main theorem -/

/-- **Ch. I §6 Corollary 1**, in the form §5 Proposition 2 (b) uses it
(`Work.NormalComplement.Design.ChISixCor1Prop`, `_design/Vocab.lean`): if `x` lies in a conjugate
`H₁` of the strongly embedded `H` with `t ∉ H₁` and `t x t⁻¹ = x⁻¹`, then `x` is conjugate to an
element of `K = J(D,t)` (with `D = twoPoint H t`, `t ∈ Inv(G ∖ H)`).

Route: every involution of `G` lies in a unique conjugate of `H`, and `G` is transitive on the
triples `(H₁,H₂,u)` with `H₁ ≠ H₂` and `u ∈ Inv(H₁)` (Ch. I §6 Cor. 1, from `ThmAProp` and
`BenderPrelimProp`).  Take `g₁` with `H₁ = H^{g₁}`; then `t^{g₁} ∉ H` and `x^{g₁} ∈ H` is inverted by
`t^{g₁}`; by the uniqueness of the conjugating involution (`BenderPrelimProp`), there is `h ∈ H`
with `t^{g₁ h} = t`, and `(x^{g₁})^{h} ∈ J(H,t) ⊆ D` is the required conjugate. -/
theorem chISixCor1Prop (hA : Submission.Blueprint.ThmAProp)
    (hBP : Work.NormalComplement.BenderPrelimProp) :
    Work.NormalComplement.Design.ChISixCor1Prop := by
  intro G _ _ sit H hH t ht2 htH g x hxg ht_not htx
  classical
  set s : G := g⁻¹ * t * g with hs_def
  set x₁ : G := g⁻¹ * x * g with hx₁_def
  -- `s` is an involution outside `H`
  have hs2 : orderOf s = 2 := by
    have h : MulAut.conj g⁻¹ t = s := by rw [hs_def, MulAut.conj_apply, inv_inv]
    rw [← h]
    exact (MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t).trans ht2
  have hsH : s ∉ H := by
    rw [hs_def]
    intro hmem
    exact ht_not ((Work.DoubleTransitivity.mem_conj g t H).mpr hmem)
  -- `x₁ ∈ H` is inverted by `s`
  have hx₁H : x₁ ∈ H := by
    rw [hx₁_def]
    exact (Work.DoubleTransitivity.mem_conj g x H).mp hxg
  have hsx : s * x₁ * s⁻¹ = x₁⁻¹ := by
    rw [hs_def, hx₁_def]
    have h1 : (g⁻¹ * t * g)⁻¹ = g⁻¹ * t⁻¹ * g := by group
    rw [h1]
    calc g⁻¹ * t * g * (g⁻¹ * x * g) * (g⁻¹ * t⁻¹ * g)
        = g⁻¹ * (t * x * t⁻¹) * g := by group
      _ = g⁻¹ * x⁻¹ * g := by rw [htx]
      _ = (g⁻¹ * x * g)⁻¹ := by group
  -- conjugate `s` to `t` inside `H`
  obtain ⟨h, hhH, hhs⟩ :=
    exists_mem_conj_of_involutions_outside sit hA hBP hH hs2 ht2 hsH htH
  refine ⟨h * g⁻¹, ?_⟩
  have hzeq : h * g⁻¹ * x * (h * g⁻¹)⁻¹ = h * x₁ * h⁻¹ := by
    rw [hx₁_def]; group
  rw [hzeq]
  rw [Work.ThreePoints.mem_invertedBy]
  have hzH : h * x₁ * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hhH hx₁H) (H.inv_mem hhH)
  have hzinv : t * (h * x₁ * h⁻¹) * t⁻¹ = (h * x₁ * h⁻¹)⁻¹ := by
    conv_lhs => rw [← hhs]
    rw [show h * s * h⁻¹ * (h * x₁ * h⁻¹) * (h * s * h⁻¹)⁻¹ = h * (s * x₁ * s⁻¹) * h⁻¹
        from by group]
    rw [hsx]
    group
  refine ⟨?_, hzinv⟩
  rw [Work.ThreePoints.mem_twoPoint]
  refine ⟨hzH, ?_⟩
  have htin : t⁻¹ = t := inv_eq_of_mul_eq_one_right
    (Work.ThreePoints.mul_self_eq_one_of_orderOf_eq_two ht2)
  have hz2 : t⁻¹ * (h * x₁ * h⁻¹) * t = (h * x₁ * h⁻¹)⁻¹ := by
    rw [htin]; rw [htin] at hzinv; exact hzinv
  rw [hz2]
  exact H.inv_mem hzH

end Work.NormalComplement
