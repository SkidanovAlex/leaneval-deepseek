import Mathlib
import Submission.Work.ThmG2.cfInner_indFun_self_twoDoubleCoset
import Submission.Work.Induction.frobenius_reciprocity
import Submission.Work.Induction.isClassFun_indFun
import Submission.Work.CharCore.Defs
import Submission.Work.CharCore.CFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical

namespace Work.ZassenhausPSL2.Feit

/-- **Mackey's formula on the two double cosets `H`, `H t H` (polarised form).**  In the split
rank-one situation `G = H ∪ H t H` (`t * t = 1`, `t ∉ H`), for any class functions
`φ ψ : H → ℂ`,
`⟨Ind_H^G φ, Ind_H^G ψ⟩_G = ⟨φ, ψ⟩_H + |D|⁻¹ ∑_{d ∈ D} φ d · conj (ψ (t d t⁻¹))`,
`D = H ⊓ Hᵗ`.

The proof is the polarised version of `Work.ThmG2.cfInner_indFun_self_twoDoubleCoset`: apply
Frobenius reciprocity, use the pointwise Mackey restriction formula of `indFun` on `H`
(`Work.ThmG2.indFun_apply_mem_eq`), and then compute the "off-`H`" contribution, where the
class function property of `φ` (rather than `ψ`) performs the substitution `h ↦ b h b⁻¹`. -/
theorem mackeyPolar {G : Type} [Group G] [Fintype G] {H : Subgroup G} {t : G}
    (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G))
    (hDmap : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
        (MulAut.conj t) (d : G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G))
    (φ ψ : H → ℂ) (hφ : Work.CharCore.IsClassFun φ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner (Work.Induction.indFun H φ) (Work.Induction.indFun H ψ) =
      Work.CharCore.cfInner φ ψ +
        (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) : ℂ)⁻¹ *
          ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
            φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
  have hcardH : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hDmem : (1 : G) ∈ H ⊓ H.map (MulAut.conj t).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨H.one_mem, ?_⟩
    rw [Work.ThmG2.mem_conjMap_iff]
    simp
  have hcardD : (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1, hDmem⟩, inferInstance⟩
  -- the second term of the pointwise Mackey restriction formula
  let SS : H → ℂ := fun h => ∑ b : H,
    (if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      then ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t, Work.ThmG2.conj_apply_mem_of_mem_inf ht hb⟩
      else 0)
  let FF : H → ℂ := fun h =>
    (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ * SS h
  let T : H → H → ℂ := fun b h => φ h *
    (if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      then (starRingEnd ℂ) (ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t,
        Work.ThmG2.conj_apply_mem_of_mem_inf ht hb⟩) else 0)
  let T' : H → ℂ := fun h => φ h *
    (if hh : (h:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      then (starRingEnd ℂ) (ψ ⟨t * (h:G) * t,
        Work.ThmG2.conj_apply_mem_of_mem_inf ht hh⟩) else 0)
  -- Frobenius reciprocity
  rw [Work.Induction.frobenius_reciprocity (H := H) φ (Work.Induction.indFun H ψ)
    (Work.Induction.isClassFun_indFun H ψ)]
  -- the pointwise restriction formula of Mackey
  have hres : Work.Induction.resFun H (Work.Induction.indFun H ψ) = ψ + FF := by
    funext h
    have hpt := Work.ThmG2.indFun_apply_mem_eq (H := H) (t := t) ht htH hcover ψ hψ h
    simpa only [Work.Induction.resFun_apply, Pi.add_apply, FF, SS] using hpt
  rw [hres, Work.CharCore.cfInner_add_right]
  congr 1
  -- the norm computation
  have hstarFF : ∀ h : H, (starRingEnd ℂ) (FF h) =
      (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ * (starRingEnd ℂ) (SS h) := by
    intro h
    dsimp only [FF]
    rw [map_mul]
    congr 1
    simp
  have hstarSS : ∀ h : H, (starRingEnd ℂ) (SS h) = ∑ b : H,
      (if hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
        then (starRingEnd ℂ) (ψ ⟨t * ((b:G) * (h:G) * (b:G)⁻¹) * t,
          Work.ThmG2.conj_apply_mem_of_mem_inf ht hb⟩) else 0) := by
    intro h
    dsimp only [SS]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈
        (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
    · rw [dite_eq_left hb, dite_eq_left hb]
    · rw [dite_eq_right hb, dite_eq_right hb]
      simp
  -- step 1: expand the star of the sum
  have hstep1 : (∑ h : H, φ h * (starRingEnd ℂ) (SS h)) = ∑ b : H, ∑ h : H, T b h := by
    have h1 : ∀ h : H, φ h * (starRingEnd ℂ) (SS h) = ∑ b : H, T b h := by
      intro h
      rw [hstarSS h, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun h _ => h1 h), Finset.sum_comm]
  -- step 2: the substitution `h ↦ b⁻¹ h b` in the inner sum, using `φ` a class function
  have hstep2 : ∀ b : H, (∑ h : H, T b h) = ∑ h : H, T' h := by
    intro b
    have hterm : ∀ h : H, T b h = T' (b * h * b⁻¹) := by
      intro h
      dsimp only [T, T']
      have hcond : (((b * h * b⁻¹ : H)) : G) = (b:G) * (h:G) * (b:G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      by_cases hb : ((b:G) * (h:G) * (b:G)⁻¹) ∈
          (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
      · have hb' : ((((b * h * b⁻¹ : H)) : G)) ∈
            (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G) := by
          rw [hcond]; exact hb
        rw [dite_eq_left hb, dite_eq_left hb', hφ h b]
        exact congrArg (fun z : H => φ h * (starRingEnd ℂ) (ψ z)) (Subtype.ext rfl)
      · have hb' : ¬ ((((b * h * b⁻¹ : H)) : G)) ∈
            (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G) := by
          rw [hcond]; exact hb
        rw [dite_eq_right hb, dite_eq_right hb']
        simp
    rw [Finset.sum_congr rfl (fun h _ => hterm h),
      Finset.sum_congr rfl (fun h _ =>
        (show T' (b * h * b⁻¹) = T' ((Work.ThmG2.conjMulEquiv b) h) from rfl)),
      Equiv.sum_comp (Work.ThmG2.conjMulEquiv b) T']
  -- step 3: convert to a sum over `D`
  have hstep3 : (∑ h : H, T' h) =
      ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        φ ⟨(d:G), d.2.1⟩ *
          (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, Work.ThmG2.conj_apply_mem_of_mem_inf ht d.2⟩) := by
    have h1 : (∑ h : H, T' h) = ∑ h : H,
        (if hh : (h:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
          then φ h * (starRingEnd ℂ) (ψ ⟨t * (h:G) * t,
            Work.ThmG2.conj_apply_mem_of_mem_inf ht hh⟩) else 0) :=
      Finset.sum_congr rfl (fun h _ => by
        dsimp only [T']
        by_cases hh : (h:G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Set G)
        · rw [dite_eq_left hh, dite_eq_left hh]
        · rw [dite_eq_right hh, dite_eq_right hh]
          simp)
    rw [h1]
    exact Work.ThmG2.sum_dite_mem_eq_sum_subtype (H := H)
      (D := H ⊓ H.map (MulAut.conj t).toMonoidHom) inf_le_left
      (fun d => φ ⟨(d:G), d.2.1⟩ *
        (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, Work.ThmG2.conj_apply_mem_of_mem_inf ht d.2⟩))
  have hself : (∑ h : H, φ h * (starRingEnd ℂ) (SS h)) = (Nat.card ↥H : ℂ) *
      ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        φ ⟨(d:G), d.2.1⟩ *
          (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, Work.ThmG2.conj_apply_mem_of_mem_inf ht d.2⟩) := by
    rw [hstep1, Finset.sum_congr rfl (fun b _ => hstep2 b), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card, hstep3]
  have hmain : Work.CharCore.cfInner φ FF =
      (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ * (Fintype.card ↥H : ℂ)⁻¹ *
        (∑ h : H, φ h * (starRingEnd ℂ) (SS h)) := by
    rw [Work.CharCore.cfInner]
    rw [Finset.sum_congr rfl (fun h _ => by rw [hstarFF h])]
    rw [show (∑ h : H, φ h * ((Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
          (starRingEnd ℂ) (SS h))) =
        (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom) : ℂ)⁻¹ *
          ∑ h : H, φ h * (starRingEnd ℂ) (SS h) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun h _ => by ring)]
    ring
  -- rewrite the conjugating element `t · t` as `MulAut.conj t`
  have hDsum : (∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        φ ⟨(d:G), d.2.1⟩ *
          (starRingEnd ℂ) (ψ ⟨t * (d:G) * t, Work.ThmG2.conj_apply_mem_of_mem_inf ht d.2⟩)) =
      ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom),
        φ ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star (ψ ⟨(MulAut.conj t) (d:G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have h1 : (⟨(d:G), d.2.1⟩ : H) = ⟨(d:G), (Subgroup.mem_inf.mp d.2).1⟩ :=
      Subtype.ext rfl
    have h2 : (⟨t * (d:G) * t, Work.ThmG2.conj_apply_mem_of_mem_inf ht d.2⟩ : H) =
        ⟨(MulAut.conj t) (d:G), (Subgroup.mem_inf.mp (hDmap d)).1⟩ := by
      apply Subtype.ext
      show t * (d:G) * t = (MulAut.conj t) (d:G)
      rw [MulAut.conj_apply, inv_eq_of_mul_eq_one_right ht]
    rw [show (starRingEnd ℂ) (ψ ⟨t * (d:G) * t,
          Work.ThmG2.conj_apply_mem_of_mem_inf ht d.2⟩) =
        star (ψ ⟨t * (d:G) * t, Work.ThmG2.conj_apply_mem_of_mem_inf ht d.2⟩) from rfl,
      h1, h2]
  rw [hmain, hself, ← Nat.card_eq_fintype_card, hDsum]
  field_simp

end Work.ZassenhausPSL2.Feit
