/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The normalizer of the centralizer of a semisimple element of `SL(2,F)`

If `(tr x) ^ 2 ≠ 4` in a finite field of odd characteristic, then the normalizer in `SL(2,F)` of
`C = C_{SL(2,F)}(x)` has at most `2 * |C|` elements.

Indeed `C = {a • 1 + b • W | a² - disc·b² = 1}` with `W = conjMat F x = 2 • x - tr(x) • 1`
(`Work.L2F.Mat2.mem_centralizer_iff_smul_one_add`), and `trace (a • 1 + b • W) = 2 * a`; so the
only elements of `C` of trace `tr x` are `x` and the "conjugate" element
`m = (tr x / 2) • 1 - (1/2) • W`.  For `g` in the normalizer, `g x g⁻¹ ∈ C` has trace `tr x`,
hence is `x` (whence `g ∈ C`) or `m`; and `{g | g x g⁻¹ = m}` is contained in a single coset
`g₀ * C`.  Therefore `N(C) ⊆ C ∪ g₀ C` and `|N(C)| ≤ 2 |C|`.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.centralizer_aux
import Submission.Work.L2F.Torus.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

theorem natCard_normalizer_centralizer_le (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : ((x : Matrix (Fin 2) (Fin 2) F)).trace ^ 2 ≠ 4) :
    Nat.card (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) F)))
      ≤ 2 * Nat.card (Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F))) := by
  classical
  have hdisc : Work.L2F.Torus.disc F x ≠ 0 := by
    rw [Work.L2F.Torus.disc_apply]
    exact sub_ne_zero.mpr hx
  set C : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) with hC
  set T : F := ((x : Matrix (Fin 2) (Fin 2) F)).trace with hT
  have hTdisc : Work.L2F.Torus.disc F x = T ^ 2 - 4 := by rw [hT, Work.L2F.Torus.disc_apply]
  have hxmem : x ∈ C := by
    rw [hC]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  -- `x` in terms of `T` and the traceless part
  have hxform : (x : Matrix (Fin 2) (Fin 2) F)
      = ((2 : F)⁻¹ * T) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (2 : F)⁻¹ • Work.L2F.Torus.conjMat F x := by
    rw [Work.L2F.Torus.x_eq_smul_conjMat F h2 x, hT]
    abel
  have hkey : ((2 : F)⁻¹ * T) ^ 2 - Work.L2F.Torus.disc F x * ((2 : F)⁻¹) ^ 2 = 1 := by
    rw [hTdisc]
    field_simp
    ring
  -- the "conjugate" element `m` of the centralizer
  set M : Matrix (Fin 2) (Fin 2) F := ((2 : F)⁻¹ * T) • (1 : Matrix (Fin 2) (Fin 2) F)
    - (2 : F)⁻¹ • Work.L2F.Torus.conjMat F x with hM
  have hMdet : M.det = 1 := by
    have hsplit : M = ((2 : F)⁻¹ * T) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (-(2 : F)⁻¹) • Work.L2F.Torus.conjMat F x := by
      rw [hM, neg_smul]
      abel
    rw [hsplit, det_smul_one_add_smul, Work.L2F.Torus.conjMat_trace, conjMat_det h2 x]
    linear_combination hkey
  set m : Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, hMdet⟩ with hm
  have hm_coe : ((m : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M := by
    rw [hm]
  have hm_mem : m ∈ C := by
    rw [hC, mem_centralizer_iff_smul_one_add F h2 x hx]
    refine ⟨(2 : F)⁻¹ * T, -(2 : F)⁻¹, ?_, ?_⟩
    · rw [neg_sq]
      exact hkey
    · rw [hm_coe, hM]
      module
  have hm_trace : ((m : Matrix (Fin 2) (Fin 2) F)).trace = T := by
    rw [hm_coe, hM, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      Work.L2F.Torus.conjMat_trace, Matrix.trace_one, Fintype.card_fin, smul_zero, sub_zero]
    push_cast
    have h : (2 : F)⁻¹ * T * 2 = T := by
      rw [mul_comm ((2 : F)⁻¹ * T) 2, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
    rw [smul_eq_mul, h]
  -- the only elements of the centralizer of trace `T` are `x` and `m`
  have hdich : ∀ y : C, (((y : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F).trace = T →
      (y : Matrix.SpecialLinearGroup (Fin 2) F) = x ∨
        (y : Matrix.SpecialLinearGroup (Fin 2) F) = m := by
    intro y hytr
    obtain ⟨a, b, hab, hyform⟩ :=
      (mem_centralizer_iff_smul_one_add F h2 x hx
        (y : Matrix.SpecialLinearGroup (Fin 2) F)).mp y.2
    have htr : 2 * a = T := by
      have h := hytr
      rw [hyform] at h
      rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
        Work.L2F.Torus.conjMat_trace, Matrix.trace_one, Fintype.card_fin, smul_zero,
        add_zero] at h
      push_cast at h
      have h2' : a * 2 = T := by simpa [smul_eq_mul] using h
      rw [mul_comm a 2] at h2'
      exact h2'
    have ha : a = (2 : F)⁻¹ * T := by
      rw [← htr, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
    have hb2 : b ^ 2 = ((2 : F)⁻¹) ^ 2 := by
      have h : Work.L2F.Torus.disc F x * b ^ 2 = Work.L2F.Torus.disc F x * ((2 : F)⁻¹) ^ 2 := by
        rw [ha] at hab
        linear_combination -hab + hkey
      exact mul_left_cancel₀ hdisc h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb2 with hb | hb
    · left
      apply Subtype.ext
      rw [hyform, ha, hb]
      exact hxform.symm
    · right
      apply Subtype.ext
      rw [hyform, ha, hb, hm_coe, hM, neg_smul]
      abel
  -- the normalizer
  set N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.normalizer (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)) with hN
  have hNsub : ∀ g : N, (g : Matrix.SpecialLinearGroup (Fin 2) F) ∈ C ∨
      (g : Matrix.SpecialLinearGroup (Fin 2) F) * x *
        (g : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ = m := by
    intro g
    have hconj : (g : Matrix.SpecialLinearGroup (Fin 2) F) * x *
        (g : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp g.2 x).mp hxmem
    -- the matrix of the inverse of `g`
    have hcoe : ((((g : Matrix.SpecialLinearGroup (Fin 2) F) * x *
        (g : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F)
        = (g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
          * ((g : Matrix (Fin 2) (Fin 2) F)).adjugate := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_inv]
    have hadj : ((g : Matrix (Fin 2) (Fin 2) F)).adjugate * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [Matrix.adjugate_mul, Matrix.SpecialLinearGroup.det_coe, one_smul]
    have htr : ((((g : Matrix.SpecialLinearGroup (Fin 2) F) * x *
        (g : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F).trace = T := by
      rw [hT]
      calc ((((g : Matrix.SpecialLinearGroup (Fin 2) F) * x *
              (g : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
              Matrix (Fin 2) (Fin 2) F).trace
          = ((g : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
              * ((g : Matrix (Fin 2) (Fin 2) F)).adjugate).trace := by
              rw [hcoe]
        _ = ((g : Matrix (Fin 2) (Fin 2) F) * ((x : Matrix (Fin 2) (Fin 2) F)
              * ((g : Matrix (Fin 2) (Fin 2) F)).adjugate)).trace := by
              rw [mul_assoc]
        _ = (((x : Matrix (Fin 2) (Fin 2) F) * ((g : Matrix (Fin 2) (Fin 2) F)).adjugate)
              * (g : Matrix (Fin 2) (Fin 2) F)).trace := by
              rw [Matrix.trace_mul_comm]
        _ = ((x : Matrix (Fin 2) (Fin 2) F)
              * (((g : Matrix (Fin 2) (Fin 2) F)).adjugate * (g : Matrix (Fin 2) (Fin 2) F))).trace := by
              rw [mul_assoc]
        _ = ((x : Matrix (Fin 2) (Fin 2) F) * 1).trace := by rw [hadj]
        _ = (x : Matrix (Fin 2) (Fin 2) F).trace := by rw [mul_one]
    rcases hdich ⟨_, hconj⟩ htr with h | h
    · left
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have h' : (g : Matrix.SpecialLinearGroup (Fin 2) F) * x *
          (g : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹ = x := h
      calc (g : Matrix.SpecialLinearGroup (Fin 2) F) * x
          = ((g : Matrix.SpecialLinearGroup (Fin 2) F) * x *
              (g : Matrix.SpecialLinearGroup (Fin 2) F)⁻¹)
            * (g : Matrix.SpecialLinearGroup (Fin 2) F) := by group
        _ = x * (g : Matrix.SpecialLinearGroup (Fin 2) F) := by rw [h']
    · right
      exact h
  have hN_subset : (N : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ⊆
      (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ∪
        {g : Matrix.SpecialLinearGroup (Fin 2) F | g * x * g⁻¹ = m} := by
    intro g hg
    rcases hNsub ⟨g, hg⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hfinal : (N : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard
      ≤ (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard
        + (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard := by
    by_cases hS : ∃ g₀ : Matrix.SpecialLinearGroup (Fin 2) F, g₀ * x * g₀⁻¹ = m
    · obtain ⟨g₀, hg₀⟩ := hS
      have hSsub : {g : Matrix.SpecialLinearGroup (Fin 2) F | g * x * g⁻¹ = m} ⊆
          (fun c : Matrix.SpecialLinearGroup (Fin 2) F => g₀ * c) ''
            (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
        intro g hg
        refine ⟨g₀⁻¹ * g, ?_, ?_⟩
        · rw [hC]
          refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          have hconjx : (g₀⁻¹ * g) * x * (g₀⁻¹ * g)⁻¹ = x := by
            rw [show (g₀⁻¹ * g) * x * (g₀⁻¹ * g)⁻¹ = g₀⁻¹ * (g * x * g⁻¹) * g₀ from by group,
              hg, ← hg₀]
            group
          calc (g₀⁻¹ * g) * x = ((g₀⁻¹ * g) * x * (g₀⁻¹ * g)⁻¹) * (g₀⁻¹ * g) := by group
            _ = x * (g₀⁻¹ * g) := by rw [hconjx]
        · show g₀ * (g₀⁻¹ * g) = g
          group
      have hsub3 : (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ∪
            {g : Matrix.SpecialLinearGroup (Fin 2) F | g * x * g⁻¹ = m} ⊆
          (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ∪
            (fun c : Matrix.SpecialLinearGroup (Fin 2) F => g₀ * c) ''
              (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
        intro g hg
        rcases hg with h | h
        · exact Or.inl h
        · exact Or.inr (hSsub h)
      calc (N : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard
          ≤ ((C : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ∪
              (fun c : Matrix.SpecialLinearGroup (Fin 2) F => g₀ * c) ''
                (C : Set (Matrix.SpecialLinearGroup (Fin 2) F))).ncard :=
            Set.ncard_le_ncard (hN_subset.trans hsub3) (Set.toFinite _)
        _ ≤ (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard +
              ((fun c : Matrix.SpecialLinearGroup (Fin 2) F => g₀ * c) ''
                (C : Set (Matrix.SpecialLinearGroup (Fin 2) F))).ncard :=
            Set.ncard_union_le _ _
        _ = (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard +
              (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard := by
            rw [Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
    · push Not at hS
      have hle : (N : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard
          ≤ (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard := by
        refine Set.ncard_le_ncard ?_ (Set.toFinite _)
        intro g hg
        rcases hNsub ⟨g, hg⟩ with h | h
        · exact h
        · exact absurd h (hS g)
      omega
  have hNcard : Nat.card ↥N = (N : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard :=
    Nat.card_coe_set_eq _
  have hCcard : Nat.card ↥C = (C : Set (Matrix.SpecialLinearGroup (Fin 2) F)).ncard :=
    Nat.card_coe_set_eq _
  rw [hNcard, hCcard]
  linarith [hfinal]

end Work.L2F.Mat2
