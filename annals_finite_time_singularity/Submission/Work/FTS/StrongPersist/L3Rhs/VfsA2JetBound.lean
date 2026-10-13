import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassDefs
import Submission.Work.FTS.PhiStar.Psi0Est.exists_ZClass
import Submission.Work.FTS.PhiStar.Psi0Est.exists_WBound
import Submission.Work.FTS.PhiStar.Psi0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- NOTE (proof infrastructure): the statement below uses the notation `π` for `Real.pi`, so the
-- locale `Real` has to be opened.  (Without it the file does not even elaborate.)
open scoped Real

namespace Work.FTS.StrongPersist.L3Rhs

-- `VfsA2JetBound`: the `dthU`-jets `1 ≤ i ≤ 3` of the second angular factor
-- `VfsA2 α = -α·c₂(θ)·Γ(θ)/c(α)` of the separated part of `Vfs α` are dominated by `α·B` times
-- the jets `0 ≤ m ≤ 4` of `Γ/c = VfsGc α`.  (The factor `α` on the right is genuinely present:
-- it is the single `α` of `VfsA2`.)
-- Intended namespace `Work.FTS.StrongPersist.L3Rhs`
-- (file `Submission/Work/FTS/StrongPersist/L3Rhs/VfsA2JetBound.lean`).
-- The hypothesis `hc2` is the pointwise bound on the `dthU`-jets of `c₂` (supplied by
-- `Work.FTS.StrongPersist.L3Rhs.VfsTriglJetBounds`).
-- Route: on `U = Set.Ioo 0 (π/2)`, using
-- `Work.FTS.PhiStar.Psi0Est.dthU_iter_const_mul_eqOn` (to pull out `-α`) and
-- `Work.FTS.PhiStar.Psi0Est.dthU_iter_mul_eqOn`:
-- `dthU^[i](VfsA2 α) θ = -α Σ_{j≤i} C(i,j)·dthU^[j](c₂) θ·dthU^[i-j](VfsGc α) θ`; each term is
-- at most `C(i,j)·B·|dthU^[i-j](VfsGc α) θ|`, the last one (`i-j = 0`) being `|VfsGc α θ|`, and
-- `Σ_j C(i,j) ≤ 8` for `i ≤ 3`, so `C = 8` works.  `VfsGc α = Γ/c` is `C^∞` on `U`
-- (`Work.FTS.PhiStar.Psi0Defs.contDiffOn_Gam` + `ContDiffOn.div_const`, or
-- `Work.FTS.CoercivityFix.Transfer.Gam_contDiffOn_infty`), `c₂` is `C^∞` everywhere.
theorem VfsA2JetBound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℝ), 0 < B →
        (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B) →
        ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.dthU^[i] (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ|
            ≤ C * B * α
              * (|Work.FTS.StrongPersist.L3Rhs.VfsGc α θ|
                + ∑ m ∈ Finset.Icc 1 4,
                    |Work.Spaces.dthU^[m] (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ|) := by
  refine ⟨8, by norm_num, ?_⟩
  intro B hB hc2 α hα hα1 i hi1 hi3 θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (π / 2)) := isOpen_Ioo
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- ## Smoothness of the two angular factors on `U = (0, π/2)`
  have hc2sm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) Work.Construction.c2m
      (Set.Ioo (0 : ℝ) (π / 2)) := by
    have h : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
        (fun t : ℝ => Real.cos (2 * t) - Real.sin t ^ 2) := by fun_prop
    refine h.contDiffOn.congr (fun t _ => ?_)
    rw [Work.Construction.c2m_eq]
  have hgcsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (VfsGc α)
      (Set.Ioo (0 : ℝ) (π / 2)) :=
    (Work.FTS.PhiStar.contDiffOn_Gam α).div_const _
  have hprodsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Construction.c2m * VfsGc α) (Set.Ioo (0 : ℝ) (π / 2)) := hc2sm.mul hgcsm
  -- ## The inner bound: every jet of order `≤ 3` of `VfsGc α` is dominated by `inner`
  set inner : ℝ := |VfsGc α θ|
      + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ| with hinner
  have hinner_nonneg : 0 ≤ inner := by
    rw [hinner]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun m _ => abs_nonneg _))
  have hgc_le : ∀ m : ℕ, m ≤ 3 → |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ inner := by
    intro m hm3
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [hinner]
      simp only [Function.iterate_zero, id_eq]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => abs_nonneg _))
    · have hmem : m ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hmpos, by omega⟩
      rw [hinner]
      exact le_trans
        (Finset.single_le_sum (s := Finset.Icc 1 4)
          (f := fun x => |Work.Spaces.dthU^[x] (VfsGc α) θ|)
          (fun x _ => abs_nonneg _) hmem)
        (le_add_of_nonneg_left (abs_nonneg _))
  -- ## The Leibniz expansion of the jets of `VfsA2 α = -α · (c₂ · VfsGc α)`
  have hfe : VfsA2 α = fun t : ℝ => -α * ((Work.Construction.c2m * VfsGc α) t) := by
    funext t; rw [VfsA2, Pi.mul_apply]; ring
  have hexp : Work.Spaces.dthU^[i] (VfsA2 α) θ
      = -α * ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) *
          (Work.Spaces.dthU^[a] Work.Construction.c2m θ
            * Work.Spaces.dthU^[i - a] (VfsGc α) θ) := by
    rw [hfe]
    rw [show Work.Spaces.dthU^[i]
          (fun t : ℝ => -α * ((Work.Construction.c2m * VfsGc α) t)) θ
        = -α * Work.Spaces.dthU^[i] (Work.Construction.c2m * VfsGc α) θ from by
      simpa using Work.FTS.PhiStar.Psi0Est.dthU_iter_const_mul_eqOn hU (-α) hprodsm i hθ]
    congr 1
    simpa using Work.FTS.PhiStar.Psi0Est.dthU_iter_mul_eqOn hU hc2sm hgcsm i hθ
  rw [hexp]
  set S : ℝ := ∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) *
      (Work.Spaces.dthU^[a] Work.Construction.c2m θ
        * Work.Spaces.dthU^[i - a] (VfsGc α) θ) with hSdef
  -- ## Termwise bound of the binomial sum
  have hterm : ∀ a ∈ Finset.range (i + 1),
      |((i.choose a : ℕ) : ℝ) *
        (Work.Spaces.dthU^[a] Work.Construction.c2m θ
          * Work.Spaces.dthU^[i - a] (VfsGc α) θ)|
        ≤ ((i.choose a : ℕ) : ℝ) * (B * inner) := by
    intro a ha
    have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hchoose : (0 : ℝ) ≤ ((i.choose a : ℕ) : ℝ) := by positivity
    have hc2a : |Work.Spaces.dthU^[a] Work.Construction.c2m θ| ≤ B :=
      hc2 a (by omega) θ hθI
    have hgca : |Work.Spaces.dthU^[i - a] (VfsGc α) θ| ≤ inner := hgc_le (i - a) (by omega)
    have hprod : |Work.Spaces.dthU^[a] Work.Construction.c2m θ|
        * |Work.Spaces.dthU^[i - a] (VfsGc α) θ| ≤ B * inner :=
      mul_le_mul hc2a hgca (abs_nonneg _) (le_of_lt hB)
    rw [abs_mul, abs_of_nonneg hchoose, abs_mul]
    exact mul_le_mul_of_nonneg_left hprod hchoose
  have hS : |S| ≤ ∑ a ∈ Finset.range (i + 1),
      ((i.choose a : ℕ) : ℝ) * (B * inner) := by
    rw [hSdef]
    exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hterm)
  have hsum_eq : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) * (B * inner))
      = (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) * (B * inner) := by
    rw [Finset.sum_mul]
  -- ## The binomial sum is at most `2 ^ i ≤ 8`
  have hbin : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) ≤ 8 := by
    have hN : (∑ a ∈ Finset.range (i + 1), i.choose a) ≤ 8 := by
      have h2 : (∑ a ∈ Finset.range (i + 1), i.choose a) = 2 ^ i := Nat.sum_range_choose i
      rw [h2]
      calc 2 ^ i ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hi3
        _ = 8 := by norm_num
    exact_mod_cast hN
  -- ## Assembly
  calc |-α * S| = α * |S| := by rw [abs_mul, abs_neg, abs_of_pos hα]
    _ ≤ α * (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) * (B * inner)) :=
        mul_le_mul_of_nonneg_left hS hα.le
    _ = α * ((∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) * (B * inner)) := by
        rw [hsum_eq]
    _ ≤ α * (8 * (B * inner)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbin (by positivity)) hα.le
    _ = 8 * B * α * inner := by ring

end Work.FTS.StrongPersist.L3Rhs
