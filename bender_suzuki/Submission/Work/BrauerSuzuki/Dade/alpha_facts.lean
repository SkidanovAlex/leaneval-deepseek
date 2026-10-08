import Mathlib
import Submission.Work.BrauerSuzuki.Dade.objects
import Submission.Work.BrauerSuzuki.Dade.sqrtSet_ti
import Submission.Work.BrauerSuzuki.Characters.resFunHom_pullback
import Submission.Work.BrauerSuzuki.Characters.vchar_of_norm_three
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet
import Submission.Work.Tame.isVChar_resFunHom
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.CFun
import Submission.Work.Induction.frobenius_reciprocity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.BrauerSuzuki.Dade

open Classical
open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

/-!
# Dade's virtual character `α` of `H = N_G(⟨σ⟩)`

`α = (1 + λ - θ) ∘ φ`, where `φ : ↥H →* ↥S` is the projection with kernel `K`.  We prove:

* `α` is a virtual character of `H`;
* `α 1 = 0`;
* `(α, α)_H = 3`;
* `α` vanishes off the TI set `√σ`.
-/

/-- `α` is the pullback along `φ` of the function `1 + λ - θ` on `↥S`. -/
theorem alpha_eq (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    alpha S d hn = Work.Induction.resFunHom (phi S d hn)
      ((fun _ => (1 : ℂ)) + lam S d - th S d) := by
  rw [alpha]
  refine congrArg (fun f : ↥S → ℂ => Work.Induction.resFunHom (phi S d hn) f) ?_
  ext x
  rfl

/-- `α` is a class function. -/
theorem alpha_isClassFun (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Work.CharCore.IsClassFun (alpha S d hn) := by
  rw [alpha_eq]
  refine (Work.BrauerSuzuki.Characters.resFunHom_pullback (phi S d hn) (phi_spec S d hn).2.2.1).1 _ ?_
  exact Work.CharCore.IsClassFun.sub
    (Work.CharCore.IsClassFun.add (Work.CharCore.isClassFun_of_mem_Irr
      (Work.CharCore.principalChar_mem_Irr (G := ↥S))) (Work.CharCore.isClassFun_of_mem_Irr (lam_mem_Irr S d)))
    (Work.CharCore.isClassFun_of_mem_Irr (th_mem_Irr S d))

/-- `α` is a virtual character of `H`. -/
theorem alpha_isVChar (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Work.CharCore.IsVChar (alpha S d hn) := by
  rw [alpha_eq]
  refine Work.Tame.isVChar_resFunHom (phi S d hn) ?_
  exact Work.CharCore.IsVChar.sub
    (Work.CharCore.IsVChar.add
      (Work.CharCore.IsVChar.of_mem_Irr (Work.CharCore.principalChar_mem_Irr (G := ↥S)))
      (Work.CharCore.IsVChar.of_mem_Irr (lam_mem_Irr S d)))
    (Work.CharCore.IsVChar.of_mem_Irr (th_mem_Irr S d))

/-- `α 1 = 0`. -/
theorem alpha_one (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : alpha S d hn 1 = 0 := by
  rw [alpha_apply, map_one, lam_apply_one, th_apply_one]
  norm_num

/-- `(α, α)_H = 3`: `1`, `λ ∘ φ` and `θ ∘ φ` are three distinct irreducible characters of
`H`. -/
theorem alpha_cfInner_self (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) : Work.CharCore.cfInner (alpha S d hn) (alpha S d hn) = 3 := by
  rw [alpha_eq]
  have hiso := (Work.BrauerSuzuki.Characters.resFunHom_pullback (phi S d hn)
    (phi_spec S d hn).2.2.1).2.2
  simp only [hiso]
  -- `1`, `λ` and `θ` are orthonormal
  have ha : (fun _ => (1 : ℂ)) ∈ Work.CharCore.Irr ↥S :=
    Work.CharCore.principalChar_mem_Irr (G := ↥S)
  have hb : lam S d ∈ Work.CharCore.Irr ↥S := lam_mem_Irr S d
  have hc : th S d ∈ Work.CharCore.Irr ↥S := th_mem_Irr S d
  have hab : (fun _ => (1 : ℂ)) ≠ lam S d := fun h => lam_ne_one S d h.symm
  have hac : (fun _ => (1 : ℂ)) ≠ th S d := fun h => th_ne_one S d h.symm
  have hbc : lam S d ≠ th S d := lam_ne_th S d
  simp only [Work.CharCore.cfInner_sub_left, Work.CharCore.cfInner_sub_right,
    Work.CharCore.cfInner_add_left, Work.CharCore.cfInner_add_right]
  rw [Work.CharCore.irr_orthonormal (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ)) ha ha,
    Work.CharCore.irr_orthonormal (fun _ => (1 : ℂ)) (lam S d) ha hb,
    Work.CharCore.irr_orthonormal (fun _ => (1 : ℂ)) (th S d) ha hc,
    Work.CharCore.irr_orthonormal (lam S d) (fun _ => (1 : ℂ)) hb ha,
    Work.CharCore.irr_orthonormal (lam S d) (lam S d) hb hb,
    Work.CharCore.irr_orthonormal (lam S d) (th S d) hb hc,
    Work.CharCore.irr_orthonormal (th S d) (fun _ => (1 : ℂ)) hc ha,
    Work.CharCore.irr_orthonormal (th S d) (lam S d) hc hb,
    Work.CharCore.irr_orthonormal (th S d) (th S d) hc hc]
  simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] <;> norm_num

/-- `(h : G) ∈ ⟨τ⟩ K` iff `φ h ∈ ⟨τ⟩`. -/
theorem mem_prod_zpowers_iff (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) (h : ↥(Hsub S d)) :
    (h : G) ∈ (Subgroup.zpowers (((d.tau : ↥S) : G)) : Set G) * (Ksub S d hn : Set G) ↔
      (phi S d hn h : ↥S) ∈ Subgroup.zpowers d.tau := by
  constructor
  · rintro ⟨t, ht, k, hk, htk⟩
    have htS : t ∈ (S : Subgroup G) := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht
      rw [← hj]
      exact (S : Subgroup G).zpow_mem d.tau.2 j
    have hkH : k ∈ Hsub S d := Ksub_le_hsub S d hn hk
    have heq : h = (⟨t, sylow_le_Hsub S d htS⟩ : ↥(Hsub S d)) * ⟨k, hkH⟩ := by
      apply Subtype.ext
      show (h : G) = t * k
      exact htk.symm
    have hφt : phi S d hn ⟨t, sylow_le_Hsub S d htS⟩ = (⟨t, htS⟩ : ↥S) :=
      (phi_spec S d hn).1 ⟨t, htS⟩
    have hφk : phi S d hn ⟨k, hkH⟩ = 1 := ((phi_spec S d hn).2.1 ⟨k, hkH⟩).mpr hk
    have hmain : phi S d hn h = (⟨t, htS⟩ : ↥S) := by
      rw [heq, map_mul, hφt, hφk, mul_one]
    rw [hmain]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hj
  · intro hτ
    obtain ⟨k, hk, hkdec⟩ := (phi_spec S d hn).2.2.2 h
    refine Set.mem_mul.mpr ⟨((phi S d hn h : ↥S) : G), ?_, k, hk, hkdec.symm⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hτ
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    have hcoej := congrArg (Subtype.val) hj
    simpa [Subgroup.coe_pow] using hcoej

/-- `(h : G) ∈ ⟨τ⁴⟩ K` iff `φ h ∈ ⟨τ⁴⟩`. -/
theorem mem_prod_zpowers_four_iff (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (hn : 3 ≤ d.n) (h : ↥(Hsub S d)) :
    (h : G) ∈ (Subgroup.zpowers ((((d.tau : ↥S) : G)) ^ 4) : Set G) * (Ksub S d hn : Set G) ↔
      (phi S d hn h : ↥S) ∈ Subgroup.zpowers ((d.tau : ↥S) ^ 4) := by
  constructor
  · rintro ⟨t, ht, k, hk, htk⟩
    have htS : t ∈ (S : Subgroup G) := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht
      rw [← hj]
      exact (S : Subgroup G).zpow_mem ((S : Subgroup G).pow_mem d.tau.2 4) j
    have hkH : k ∈ Hsub S d := Ksub_le_hsub S d hn hk
    have heq : h = (⟨t, sylow_le_Hsub S d htS⟩ : ↥(Hsub S d)) * ⟨k, hkH⟩ := by
      apply Subtype.ext
      show (h : G) = t * k
      exact htk.symm
    have hφt : phi S d hn ⟨t, sylow_le_Hsub S d htS⟩ = (⟨t, htS⟩ : ↥S) :=
      (phi_spec S d hn).1 ⟨t, htS⟩
    have hφk : phi S d hn ⟨k, hkH⟩ = 1 := ((phi_spec S d hn).2.1 ⟨k, hkH⟩).mpr hk
    have hmain : phi S d hn h = (⟨t, htS⟩ : ↥S) := by
      rw [heq, map_mul, hφt, hφk, mul_one]
    rw [hmain]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using hj
  · intro h4
    obtain ⟨k, hk, hkdec⟩ := (phi_spec S d hn).2.2.2 h
    refine Set.mem_mul.mpr ⟨((phi S d hn h : ↥S) : G), ?_, k, hk, hkdec.symm⟩
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h4
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, ?_⟩
    have hcoej := congrArg (Subtype.val) hj
    simpa [Subgroup.coe_pow] using hcoej

/-- `α` vanishes off the TI set `√σ`. -/
theorem alpha_support (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S)
    (hn : 3 ≤ d.n) :
    Work.BrauerSuzuki.SupportLeSub (alpha S d hn) (Work.BrauerSuzuki.sqrtSet (sigma S d)) := by
  intro h hh
  rw [alpha_apply]
  by_cases h4 : (phi S d hn h : ↥S) ∈ Subgroup.zpowers ((d.tau : ↥S) ^ 4)
  · rw [one_add_lam_sub_th_zpow_four S d h4]
  · refine one_add_lam_sub_th_notMem S d (x := phi S d hn h) ?_
    intro hτ
    refine hh ?_
    rw [sqrtSet_eq_prod S d hn, Set.mem_sdiff]
    exact ⟨(mem_prod_zpowers_iff S d hn h).mpr hτ,
      fun hmem => h4 ((mem_prod_zpowers_four_iff S d hn h).mp hmem)⟩

end Work.BrauerSuzuki.Dade
