/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsRHSP_slotSup_val5` — order-five mixed slots of the projected right-hand side

This is the order-`5` companion of `Work.FTS.StrongEps.EpsRHSP_slotSup_val` (which proves the
same statement for the slots `j + i ≤ 4`).  The proof is the same *value*-bound argument: every
derivative falling on the mollified profile is routed onto the (smooth, compactly supported)
mollifier kernel (`mixed_Jeps_kernel_partial` at `j' = i' = 0`), and the routed kernel
`Kd (Jker ρ ε) j i` is supported in the ball of radius `ε`, so only the *values* of the profile
at the shifted points enter.  Nothing in that argument is order-sensitive
(`abs_mixed_Jeps_le_val` holds for every `j i`), and neither is the splitting
`epsRHSP s = J_ε (epsWP s) − (L₁₂(...)(0)/pzNorm)·bump` (`PZeroAux.mixed_Pz` holds for every
`j i`).  Only two finite bookkeeping devices need to be enlarged from the fifteen slots
`j + i ≤ 4` to the twenty-one slots `j + i ≤ 5`:

* the uniform bound of the mixed slots of the fixed correction profile `bump` on the compact
  `K ⊆ Q0` (`exists_bound_mixed_bump5` below, with the range `6` instead of `5`);
* the total mass of the routed kernels (`KmassTot5`, again with range `6`).

Both are proved here from scratch; the argument proper is a verbatim adaptation of the proof of
`EpsRHSP_slotSup_val`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_val
import Submission.Work.FTS.StrongEps.PZeroScheme

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

/-! ## A uniform pointwise bound for the mixed derivatives of the correction profile

`bump` is `C^∞` on the open quadrant (`smoothOpen_bump`), so each `D_z^jD_θ^i bump` is `C^∞`
on `Q0` (`SmoothOpen.mixed`), hence in particular continuous on the compact `K ⊆ Q0`; the sum of
the absolute values of the finitely many slots of order `≤ 5` is a continuous function on `K`,
and its supremum bounds every single slot. -/

theorem exists_bound_mixed_bump5 (K : Set (ℝ × ℝ)) (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (j i : ℕ), j + i ≤ 5 → ∀ p ∈ K,
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb := by
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ∑ j ∈ Finset.range 6, ∑ i ∈ Finset.range 6,
      |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|) K := by
    refine continuousOn_finsetSum _ (fun j _ => continuousOn_finsetSum _ (fun i _ => ?_))
    exact ((Work.FTS.StrongEps.smoothOpen_bump.mixed j i).continuousOn.mono hKQ).abs
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro j i hji p hp
  have hj : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hi : i ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have h1 : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
      ≤ ∑ i' ∈ Finset.range 6,
          |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2| :=
    Finset.single_le_sum
      (f := fun i' => |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2|)
      (fun i' _ => abs_nonneg _) hi
  have h2 : (∑ i' ∈ Finset.range 6,
        |Work.Spaces.mixed j i' Work.FTS.StrongEps.bump p.1 p.2|)
      ≤ ∑ j' ∈ Finset.range 6, ∑ i' ∈ Finset.range 6,
          |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2| :=
    Finset.single_le_sum
      (f := fun j' => ∑ i' ∈ Finset.range 6,
        |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2|)
      (fun j' _ => Finset.sum_nonneg (fun i' _ => abs_nonneg _)) hj
  have h3 : (∑ j' ∈ Finset.range 6, ∑ i' ∈ Finset.range 6,
        |Work.Spaces.mixed j' i' Work.FTS.StrongEps.bump p.1 p.2|) ≤ M := by
    have hMp := hM p hp
    rw [Real.norm_eq_abs] at hMp
    exact le_trans (le_abs_self _) hMp
  linarith [le_max_left M 0]

/-! ## The mass of the routed kernels over the slots of order `≤ 5` -/

/-- The total mass over the twenty-one slots of order `≤ 5`, which dominates every single one of
them (together with the factor `2 ^ i` coming from the `θ`-routing).  This is
`Work.FTS.StrongEps.KmassTot` with the ranges enlarged from `5` to `6`. -/
noncomputable def KmassTot5 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 6, ∑ i ∈ Finset.range 6, (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i

theorem KmassTot5_nonneg (ρ : ℝ × ℝ → ℝ) (ε : ℝ) : 0 ≤ KmassTot5 ρ ε := by
  unfold KmassTot5
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ =>
    mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i)

/-- Every slot of order `≤ 5` is dominated by the total mass. -/
theorem two_pow_mul_Kmass_le_KmassTot5 (ρ : ℝ × ℝ → ℝ) (ε : ℝ) {j i : ℕ}
    (hji : j + i ≤ 5) : (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i ≤ KmassTot5 ρ ε := by
  have hj : j ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hi : i ∈ Finset.range 6 := Finset.mem_range.mpr (by omega)
  have hinner : ∀ i' ∈ Finset.range 6,
      (0 : ℝ) ≤ (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j i' :=
    fun i' _ => mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j i')
  calc (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i
      ≤ ∑ i' ∈ Finset.range 6, (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j i' :=
        Finset.single_le_sum
          (f := fun i' => (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j i') hinner hi
    _ ≤ KmassTot5 ρ ε := by
        unfold KmassTot5
        refine Finset.single_le_sum
          (f := fun j' => ∑ i' ∈ Finset.range 6, (2 : ℝ) ^ i' * Work.FTS.StrongEps.Kmass ρ ε j' i')
          (fun j' _ => ?_) hj
        exact Finset.sum_nonneg fun i' _ =>
          mul_nonneg (by positivity) (Work.FTS.StrongEps.Kmass_nonneg ρ ε j' i')

/-! ## The target -/

theorem EpsRHSP_slotSup_val5 {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hreg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    (hwin : ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
      (∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ 1 → |q.2| ≤ 1 →
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2) ∈ K') ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K',
        |Work.FTS.StrongEps.epsWP α ρ ε Φs E g s p.1 p.2| ≤ B)
    (hnorm : ∃ KW : ℝ, 0 ≤ KW ∧ ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j i : ℕ), j + i ≤ 5 → ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∀ p ∈ K, |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2| ≤ C := by
  obtain ⟨K', hK'c, hK'Q, hKK', hshift, B, hB, hbdd⟩ := hwin
  obtain ⟨KW, hKW, hnorm'⟩ := hnorm
  obtain ⟨Cb, hCb0, hbump⟩ := exists_bound_mixed_bump5 K hK hKQ
  obtain ⟨CL, hCL0, hCL⟩ := Work.FTS.StrongEps.abs_L12_Jeps_le (ρ := ρ) hρ
  have hpzpos : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨B * KmassTot5 ρ ε + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hB (KmassTot5_nonneg ρ ε))
      (mul_nonneg (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le) hCb0)
  · intro j i hji s hs p hp
    obtain ⟨hmems, hnormbs⟩ := hnorm' s hs
    have hpQ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    have hz : 0 < p.1 := hpQ.1
    have hθ : p.2 ∈ Set.Ioo 0 (π / 2) := ⟨hpQ.2.1, hpQ.2.2⟩
    have hsm : ∀ n : ℕ, ContDiffOn ℝ n
        (Function.uncurry (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s))
        Work.FTS.StrongEps.Quad := (hreg s hs).forall
    -- the *value* bound of `epsWP` transfers to the shifted points inside the kernel's ball
    have hF : ∀ q : ℝ × ℝ, |q.1| ≤ ε → |q.2| ≤ ε →
        |Work.FTS.StrongEps.epsWP α ρ ε Φs E g s
            (Work.FTS.StrongEps.zShift p.1 q.1) (Work.FTS.StrongEps.thShift p.2 q.2)| ≤ B :=
      fun q hq1 hq2 => hbdd s hs
        (Work.FTS.StrongEps.zShift p.1 q.1, Work.FTS.StrongEps.thShift p.2 q.2)
        (hshift p hp q (le_trans hq1 hε.2) (le_trans hq2 hε.2))
    have hmain : |Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
        ≤ B * KmassTot5 ρ ε := by
      refine le_trans
        (Work.FTS.StrongEps.abs_mixed_Jeps_le_val (ρ := ρ) hρ hε.1 hsm hz hθ hF j i) ?_
      calc (2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i * B
          = ((2 : ℝ) ^ i * Work.FTS.StrongEps.Kmass ρ ε j i) * B := by ring
        _ ≤ KmassTot5 ρ ε * B :=
            mul_le_mul_of_nonneg_right (two_pow_mul_Kmass_le_KmassTot5 ρ ε hji) hB
        _ = B * KmassTot5 ρ ε := by ring
    have hcorr : |(Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm) * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb := by
      rw [abs_mul]
      have hL : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0|
          ≤ CL * KW := hCL hα hε.1 hε.2 hKW hsm hmems hnormbs
      have hal : |Work.Construction.L12
          (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
            / Work.FTS.StrongEps.pzNorm| ≤ CL * KW / Work.FTS.StrongEps.pzNorm := by
        rw [abs_div, abs_of_pos hpzpos]
        exact div_le_div_of_nonneg_right hL hpzpos.le
      have hb : |Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| ≤ Cb :=
        hbump j i hji p hp
      exact mul_le_mul hal hb (abs_nonneg _)
        (div_nonneg (mul_nonneg hCL0 hKW) hpzpos.le)
    have hsplit : Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) p.1 p.2
        = Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2 := by
      rw [Work.FTS.StrongEps.epsRHSP_eq_Pz_Jeps_epsWP,
        Work.FTS.StrongEps.PZeroAux.mixed_Pz
          (Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε.1 hsm) hz hθ j i]
    rw [hsplit]
    calc |Work.Spaces.mixed j i
            (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2
          - (Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2|
        ≤ |Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2|
          + |(Work.Construction.L12
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                / Work.FTS.StrongEps.pzNorm)
            * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2| := by
          have h := abs_add_le (Work.Spaces.mixed j i
              (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) p.1 p.2)
            (-((Work.Construction.L12
                (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s)) 0
                  / Work.FTS.StrongEps.pzNorm)
                * Work.Spaces.mixed j i Work.FTS.StrongEps.bump p.1 p.2))
          simpa only [sub_eq_add_neg, abs_neg] using h
      _ ≤ B * KmassTot5 ρ ε + (CL * KW / Work.FTS.StrongEps.pzNorm) * Cb :=
          add_le_add hmain hcorr

end Work.FTS.StrongEps.E5G
