import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.frobenius_reciprocity_transposed
import Submission.Work.Induction.Basic
import Submission.Work.Induction.sum_conj_eq_card_mul
import Submission.Work.Induction.TwoDoubleCosetSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The two-double-coset inner product formula `⟨Ind_H^G ψ, Ind_H^G ψ⟩`

If `G = H ⊔ H t H` with `t * t = 1`, `t ∉ H`, then for a class function `ψ` on `H`,
`⟨Ind_H^G ψ, Ind_H^G ψ⟩_G = ⟨ψ, ψ⟩_H + |K|⁻¹ ∑_{d ∈ K} ψ d · conj (ψ (t d t⁻¹))`
where `K = H ∩ Hᵗ`.

The proof: Frobenius reciprocity reduces the left-hand side to `⟨ψ, Res_H^G (Ind_H^G ψ)⟩_H`,
and the restriction splits as `Res_H^G (Ind_H^G ψ) = ψ + Ind_K^H (k ↦ ψ (t k t⁻¹))`
(`resFun_indFun_eq_self_add_corrOf`).  Another Frobenius reciprocity then evaluates the
correction term as the normalized inner product over `K`
(`Work.Induction.cfInner_corrOf`).
-/

namespace Work.Induction

open Classical
open scoped Pointwise

noncomputable section

variable {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype ↥H] {t : G}

/-- **The restriction of the induced function, two-double-coset case.**
`Res_H^G (Ind_H^G ψ) = ψ + Ind_K^H (k ↦ ψ (t k t⁻¹))`, where `K = H ∩ Hᵗ`.

Pointwise: `|H| · Ind_H^G ψ h = ∑_{x : x h x⁻¹ ∈ H} ψ (x h x⁻¹)`.  The `x ∈ H` part of the sum
is `|H| ψ h` (class function), and the `x ∉ H` part is `H t H`, where the parametrisation
`(a, b) ↦ a t b` of `H × H` is `|K|`-to-one (`Work.Induction.doubleCoset_sum_reindex`); the
summand then depends only on `b`, and `Work.Induction.atbSummand_sum_eq` computes it. -/
theorem resFun_indFun_eq_self_add_corrOf [Fintype ↥(DCInf H t)]
    (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a:G) * t * (b:G))
    (hDmap : ∀ d : ↥(DCInf H t), (MulAut.conj t) (d : G) ∈ DCInf H t)
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    resFun H (indFun H ψ) = ψ + corrOf t (psiT t hDmap ψ) := by
  funext h
  have hHne : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1, H.one_mem⟩, inferInstance⟩
  have hKne : (Nat.card ↥(DCInf H t) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1, (DCInf H t).one_mem⟩, inferInstance⟩
  have hA1 : ∑ x ∈ Finset.univ.filter (fun x : G => x ∈ H), resSummand H h ψ x
      = (Nat.card ↥H : ℂ) * ψ h := by
    have h1 : ∑ x ∈ Finset.univ.filter (fun x : G => x ∈ H), resSummand H h ψ x
        = ∑ x : ↥H, ψ (x * h * x⁻¹) := by
      rw [Finset.sum_subtype (p := fun x : G => x ∈ H)
        (Finset.univ.filter (fun x : G => x ∈ H)) (fun x => by simp)
        (fun x => resSummand H h ψ x)]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      show dite ((x:G)*(h:G)*(x:G)⁻¹ ∈ H)
          (fun hc => ψ ⟨(x:G)*(h:G)*(x:G)⁻¹, hc⟩) (fun _ => 0) = ψ (x * h * x⁻¹)
      rw [dite_eq_left (H.mul_mem (H.mul_mem x.2 h.2) (H.inv_mem x.2))]
      exact congrArg ψ (Subtype.ext rfl)
    rw [h1, sum_conj_eq_card_mul ψ hψ h]
  have hF : ∀ x : G, coverSummand H t h ψ x
      = dite (x ∉ H) (fun _ => resSummand H h ψ x) (fun _ => 0) := by
    intro x
    unfold coverSummand
    by_cases hQ : x ∉ H
    · rw [dite_eq_left ((notMem_H_iff ht htH hcover x).mp hQ), dite_eq_left hQ]
    · rw [dite_eq_right (fun hh => hQ ((notMem_H_iff ht htH hcover x).mpr hh)),
        dite_eq_right hQ]
  have hsum1 : ∑ x : G, coverSummand H t h ψ x
      = ∑ x ∈ Finset.univ.filter (fun x : G => x ∉ H), resSummand H h ψ x := by
    rw [show ∑ x : G, coverSummand H t h ψ x
          = ∑ x : G, dite (x ∉ H) (fun _ => resSummand H h ψ x) (fun _ => 0) from
        Finset.sum_congr rfl (fun x _ => hF x)]
    rw [Finset.sum_filter]
    rfl
  have hP1 : ∑ p : H × H, coverSummand H t h ψ ((p.1:G)*t*(p.2:G))
      = (Nat.card ↥(DCInf H t) : ℂ) * ∑ x : G, coverSummand H t h ψ x :=
    doubleCoset_sum_reindex t ht (coverSummand H t h ψ) (fun x hx => by
      unfold coverSummand
      rw [dite_eq_right (fun hh => by obtain ⟨a,b,hab⟩ := hh; exact hx a b hab)])
  have hpatb : ∑ p : H × H, coverSummand H t h ψ ((p.1:G)*t*(p.2:G))
      = ∑ p : H × H, atbSummand t ψ h p := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold coverSummand
    rw [dite_eq_left ⟨p.1, p.2, rfl⟩]
    rfl
  have hA2 : ∑ x ∈ Finset.univ.filter (fun x : G => x ∉ H), resSummand H h ψ x
      = (Nat.card ↥(DCInf H t) : ℂ)⁻¹ *
          ((Nat.card ↥H : ℂ) * ∑ y : H, corrSummand t (psiT t hDmap ψ) h y) := by
    rw [← hsum1]
    have hc : ∑ x : G, coverSummand H t h ψ x
        = (Nat.card ↥(DCInf H t) : ℂ)⁻¹ *
            ∑ p : H × H, coverSummand H t h ψ ((p.1:G)*t*(p.2:G)) := by
      rw [hP1, ← mul_assoc, inv_mul_cancel₀ hKne, one_mul]
    rw [hc, hpatb, atbSummand_sum_eq ht hDmap ψ hψ h]
  rw [resFun_apply, Pi.add_apply, indFun_apply_def]
  rw [show (∑ x : G, (if hx : x * (h:G) * x⁻¹ ∈ H
        then ψ ⟨x * (h:G) * x⁻¹, hx⟩ else 0)) = ∑ x : G, resSummand H h ψ x from rfl]
  rw [← Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset G))
        (p := fun x : G => x ∈ H) (f := fun x => resSummand H h ψ x)]
  rw [hA1, hA2, corrOf, mul_add]
  field_simp

theorem cfInner_indFun_self_twoDoubleCoset {G : Type*} [Group G] [Fintype G]
    {H : Subgroup G} [Fintype ↥H] {t : G}
    [Fintype ↥(H ⊓ (H.map (MulAut.conj t).toMonoidHom) : Subgroup G)]
    (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a:G) * t * (b:G))
    (hDmap : ∀ d : (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
        (MulAut.conj t) (d:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G))
    (ψ : H → ℂ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner (Work.Induction.indFun H ψ) (Work.Induction.indFun H ψ)
      = Work.CharCore.cfInner ψ ψ + (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
          ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
            ψ ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d:G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
  rw [frobenius_reciprocity_local H ψ (indFun H ψ) (isClassFun_indFun H ψ)]
  rw [resFun_indFun_eq_self_add_corrOf ht htH hcover hDmap ψ hψ]
  rw [CharCore.cfInner_add_right, cfInner_corrOf ht hDmap ψ hψ]
  rfl

end

end Work.Induction
