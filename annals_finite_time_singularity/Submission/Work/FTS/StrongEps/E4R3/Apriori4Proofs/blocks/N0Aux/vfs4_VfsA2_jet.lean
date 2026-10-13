import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsA2JetBound
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsAngMassDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- NOTE: the statement uses the notation `π` for `Real.pi`, so the locale `Real` has to be
-- opened (as in the sibling `VfsA2JetBound`).
open scoped Real

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open Work.FTS.StrongPersist.L3Rhs (VfsA2 VfsGc)

/-- The order-4 version of `Work.FTS.StrongPersist.L3Rhs.VfsA2JetBound`: the `dthU`-jets of
`VfsA2 α = -α·c₂·(Γ/c)` up to order `4` are dominated by `α·B` times the jets `0 ≤ m ≤ 4` of
`Γ/c = VfsGc α`.

The hypothesis on `c₂` is exactly the order-4 jet bound `|dthU^[j] c₂| ≤ B` (`j ≤ 4`), so the
only change with respect to `VfsA2JetBound` is that the binomial sum
`Σ_{a ≤ i} C(i,a)` is now bounded by `2^i ≤ 2^4 = 16`; the constant is `16`.

Route: `dthU^[i](VfsA2 α) θ = -α Σ_{a≤i} C(i,a)·dthU^[a](c₂) θ·dthU^[i-a](VfsGc α) θ`
(iterated Leibniz rule on the open set `(0,π/2)`, plus linearity for the constant factor `-α`);
every term is at most `C(i,a)·B·inner` with
`inner = |VfsGc α θ| + Σ_{1≤m≤4}|dthU^[m](VfsGc α) θ|`. -/
theorem vfs4_VfsA2_jet :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B : ℝ), 0 < B →
        (∀ j ≤ 4, ∀ θ ∈ Work.Spaces.Iθ,
          |Work.Spaces.dthU^[j] Work.Construction.c2m θ| ≤ B) →
        ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
        ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.dthU^[i]
              (Work.FTS.StrongPersist.L3Rhs.VfsA2 α) θ|
            ≤ C * B * α
              * (|Work.FTS.StrongPersist.L3Rhs.VfsGc α θ|
                + ∑ m ∈ Finset.Icc 1 4,
                    |Work.Spaces.dthU^[m]
                      (Work.FTS.StrongPersist.L3Rhs.VfsGc α) θ|) := by
  refine ⟨16, by norm_num, ?_⟩
  intro B hB hc2 α hα hα1 i hi1 hi4 θ hθ
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
  -- ## The inner bound: every jet of order `≤ 4` of `VfsGc α` is dominated by `inner`
  set inner : ℝ := |VfsGc α θ|
      + ∑ m ∈ Finset.Icc 1 4, |Work.Spaces.dthU^[m] (VfsGc α) θ| with hinner
  have hinner_nonneg : 0 ≤ inner := by
    rw [hinner]
    exact add_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun m _ => abs_nonneg _))
  have hgc_le : ∀ m : ℕ, m ≤ 4 → |Work.Spaces.dthU^[m] (VfsGc α) θ| ≤ inner := by
    intro m hm4
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [hinner]
      simp only [Function.iterate_zero, id_eq]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => abs_nonneg _))
    · have hmem : m ∈ Finset.Icc 1 4 := Finset.mem_Icc.mpr ⟨hmpos, hm4⟩
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
  -- ## The binomial sum is at most `2 ^ i ≤ 16`
  have hbin : (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) ≤ 16 := by
    have hN : (∑ a ∈ Finset.range (i + 1), i.choose a) ≤ 16 := by
      have h2 : (∑ a ∈ Finset.range (i + 1), i.choose a) = 2 ^ i := Nat.sum_range_choose i
      rw [h2]
      calc 2 ^ i ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hi4
        _ = 16 := by norm_num
    exact_mod_cast hN
  -- ## Assembly
  calc |-α * S| = α * |S| := by rw [abs_mul, abs_neg, abs_of_pos hα]
    _ ≤ α * (∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ) * (B * inner)) :=
        mul_le_mul_of_nonneg_left hS hα.le
    _ = α * ((∑ a ∈ Finset.range (i + 1), ((i.choose a : ℕ) : ℝ)) * (B * inner)) := by
        rw [hsum_eq]
    _ ≤ α * (16 * (B * inner)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbin (by positivity)) hα.le
    _ = 16 * B * α * inner := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
