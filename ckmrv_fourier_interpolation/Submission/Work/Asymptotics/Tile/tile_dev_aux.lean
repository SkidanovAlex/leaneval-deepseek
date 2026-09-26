/-
# Shared context for the cusp-`±1` tile window `tile_dev_low`

The cusp-`±1` tile machinery (`Work.Asymptotics.Tile.tileCoincidence`, the cusp model
bound `Work.Asymptotics.Tile.tile_Gfun_bound`) and the branch vanishings of the cleared
kernel live here so that the two window halves (`tile_Kfun_far`, `tile_Kfun_near`) can
import them without importing `tile_dev_low.lean` itself (which in turn needs the two
halves). -/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.Gcusp_tile_bound
import Submission.Work.Asymptotics.EtailE.Assembly
import Submission.Work.Asymptotics.AfunFun_S_vadd_eq_zero
import Submission.Work.Asymptotics.Tile.tile_KfunClear_shift_vanish
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Kernels.Kernels


namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

/-- `j` is unchanged by the translation `n +ᵥ ·` for `n = ±1`. -/
lemma jInvariantFun_vadd_int' (n : ℤ) (hn : n = 1 ∨ n = -1) (w : UpperHalfPlane) :
    Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w := by
  rcases hn with h | h
  · subst h
    push_cast
    exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
  · subst h
    push_cast
    have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ w)
    rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w by rw [← add_vadd]; norm_num] at h1
    exact h1.symm

/-- **The classification of the coincidences on the cusp-`±1` tiles.**  For `w` in the cusp-`0`
neighbourhood `E = KEpsilon`, `n = ±1` and `t ∈ [1,3]`, the coincidence `j (n +ᵥ w) = j (i t)`
forces `w = i/t`. -/
lemma tileCoincidence (w : UpperHalfPlane) (hw : w ∈ Work.Asymptotics.KEpsilon) (n : ℤ)
    (hn : n = 1 ∨ n = -1) (t : ℝ) (ht : 0 < t) (h1 : 1 ≤ t) (h3 : t ≤ 3)
    (h : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    w = Work.Kernels.imagAxis (t⁻¹) (inv_pos.mpr ht) := by
  have hσD : ModularGroup.S • w ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.S_smul_mem_DomainD (Work.Asymptotics.KEpsilon_subset_DomainD hw)
  have hjσ : Work.Kernels.jInvariantFun (ModularGroup.S • w)
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul, ← jInvariantFun_vadd_int' n hn w, h]
  have hzre : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ).re = 0 := by
    simp [Work.Kernels.imagAxis]
  rcases Work.Asymptotics.eq_or_eq_S_of_re_eq_zero' hσD hzre hjσ with hcase | hcase
  · have : w = ModularGroup.S • (Work.Kernels.imagAxis t ht) := by
      rw [hcase, Work.Asymptotics.S_smul_S_smul]
    rw [this, Work.Asymptotics.imagAxis_smul_S t ht]
  · rw [Work.Asymptotics.S_smul_S_smul] at hcase
    have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
    have hle := Work.Asymptotics.tile_im_le_half hw
    rw [← hcase, him] at hle
    linarith

/-- The norm of a point of the imaginary axis. -/
lemma norm_imagAxis_coe (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ)‖ = t := by
  rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl]
  rw [Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht]

/-- `‖Ept (i t)‖^{-2} = e^{2πt}`. -/
lemma norm_Ept_inv_sq (t : ℝ) (ht : 0 < t) :
    ‖(Work.Residues.Ept (Work.Kernels.imagAxis t ht)) ^ (-2 : ℤ)‖ = Real.exp (2 * Real.pi * t) := by
  have h1 : ‖Work.Residues.Ept (Work.Kernels.imagAxis t ht)‖ = Real.exp (-(Real.pi * t)) := by
    rw [Work.Residues.norm_Ept]
    have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
    rw [him]
  rw [norm_zpow, h1]
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from rfl, _root_.zpow_neg, _root_.zpow_natCast,
    ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  ring

/-- **Polynomial bound for the cusp model `Gfun` on the cusp-`±1` tiles.** -/
theorem tile_Gfun_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ, (n = 1 ∨ n = -1) →
        ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t → t ≤ 3 →
          ‖Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.Gcusp_tile_bound ℓ d hd
  refine ⟨(C + 3 * C) * (1 + Real.exp (6 * Real.pi)) + 1, N, by positivity, hN, ?_⟩
  intro w hw n hn t ht h1 h3
  set τ : UpperHalfPlane := (n : ℝ) +ᵥ w with hτdef
  set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hzdef
  have hgc : ∀ i j : Fin 2, ‖Work.Asymptotics.Compact.Gcoef d ℓ i j τ‖ ≤ C * (Work.Kernels.scale w) ^ N := by
    intro i j
    rw [← Work.Asymptotics.Gcusp_eq_Gcoef ℓ d hd]
    exact hb w n hn hw i j
  have hzn : ‖(z : ℂ)‖ = t := by
    rw [hzdef]; exact norm_imagAxis_coe t ht
  have hzt : ‖(z : ℂ)‖ ≤ 3 := by rw [hzn]; exact h3
  have hEn : ‖(Work.Residues.Ept z) ^ (-2 : ℤ)‖ ≤ Real.exp (6 * Real.pi) := by
    rw [hzdef, norm_Ept_inv_sq t ht]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos] )
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hpos : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ N := Real.rpow_nonneg hs0.le N
  have hkey : ‖(z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 0 1 τ‖ ≤ 3 * (C * (Work.Kernels.scale w) ^ N) := by
    rw [norm_mul]
    exact mul_le_mul hzt (hgc 0 1) (norm_nonneg _) (by norm_num)
  have hkey2 : ‖(z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 1 1 τ‖ ≤ 3 * (C * (Work.Kernels.scale w) ^ N) := by
    rw [norm_mul]
    exact mul_le_mul hzt (hgc 1 1) (norm_nonneg _) (by norm_num)
  have hsum1 : ‖Work.Asymptotics.Compact.Gcoef d ℓ 0 0 τ + (z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 0 1 τ‖
      ≤ 4 * (C * (Work.Kernels.scale w) ^ N) := by
    refine le_trans (norm_add_le _ _) ?_
    have := hgc 0 0
    nlinarith [hkey, this, hpos, hC.le]
  have hsum2 : ‖Work.Asymptotics.Compact.Gcoef d ℓ 1 0 τ + (z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 1 1 τ‖
      ≤ 4 * (C * (Work.Kernels.scale w) ^ N) := by
    refine le_trans (norm_add_le _ _) ?_
    have := hgc 1 0
    nlinarith [hkey2, this, hpos, hC.le]
  have hprod : ‖(Work.Residues.Ept z) ^ (-2 : ℤ) * (Work.Asymptotics.Compact.Gcoef d ℓ 1 0 τ
        + (z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 1 1 τ)‖
      ≤ Real.exp (6 * Real.pi) * (4 * (C * (Work.Kernels.scale w) ^ N)) := by
    rw [norm_mul]
    refine mul_le_mul hEn hsum2 (by positivity) (Real.exp_pos _).le
  calc ‖Work.Asymptotics.Compact.Gfun d ℓ τ z‖
      = ‖(Work.Asymptotics.Compact.Gcoef d ℓ 0 0 τ + (z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 0 1 τ)
          + (Work.Residues.Ept z) ^ (-2 : ℤ) * (Work.Asymptotics.Compact.Gcoef d ℓ 1 0 τ
              + (z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 1 1 τ)‖ := by
        rw [Work.Asymptotics.Compact.Gfun]
    _ ≤ ‖Work.Asymptotics.Compact.Gcoef d ℓ 0 0 τ + (z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 0 1 τ‖
        + ‖(Work.Residues.Ept z) ^ (-2 : ℤ) * (Work.Asymptotics.Compact.Gcoef d ℓ 1 0 τ
              + (z : ℂ) * Work.Asymptotics.Compact.Gcoef d ℓ 1 1 τ)‖ := norm_add_le _ _
    _ ≤ 4 * (C * (Work.Kernels.scale w) ^ N)
        + Real.exp (6 * Real.pi) * (4 * (C * (Work.Kernels.scale w) ^ N)) := add_le_add hsum1 hprod
    _ ≤ ((C + 3 * C) * (1 + Real.exp (6 * Real.pi)) + 1) * (Work.Kernels.scale w) ^ N := by
        have heq : 4 * (C * (Work.Kernels.scale w) ^ N)
              + Real.exp (6 * Real.pi) * (4 * (C * (Work.Kernels.scale w) ^ N))
            = (4 + 4 * Real.exp (6 * Real.pi)) * (C * (Work.Kernels.scale w) ^ N) := by ring
        rw [heq]
        have hbig : ((C + 3 * C) * (1 + Real.exp (6 * Real.pi)) + 1) * (Work.Kernels.scale w) ^ N
            = (4 + 4 * Real.exp (6 * Real.pi)) * (C * (Work.Kernels.scale w) ^ N)
              + (Work.Kernels.scale w) ^ N := by ring
        rw [hbig]
        linarith


/-- **The `m = 0` (`S`-)branch vanishing of the cleared kernel.**  For `n = ±1` and any `σ` the
cleared kernel vanishes at `(n +ᵥ σ, S • σ)`: this is `AfunFun_S_vadd_eq_zero` transported
through `KfunClear = Δ(τ)Δ(z)^e · AfunFun`. -/
lemma KfunClear_vadd_S_eq_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (n : ℤ) (hn : n = 1 ∨ n = -1) (σ : UpperHalfPlane) :
    Work.Kernels.KfunClear ℓ d ((n : ℝ) +ᵥ σ) (ModularGroup.S • σ) = 0 := by
  rw [Work.Asymptotics.KfunClear_eq_mul_AfunFun,
    Work.Asymptotics.AfunFun_S_vadd_eq_zero ℓ d hd n hn σ, mul_zero]

/-- **The three relevant branch vanishings of the cleared kernel**, packaged in the form the
compact-side window consumes them. -/
lemma KfunClear_shift_vanish_all (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ (n m : ℤ), (n = 1 ∨ n = -1) → (m = -1 ∨ m = 0 ∨ m = 1) → ∀ σ : UpperHalfPlane,
      Work.Kernels.KfunClear ℓ d ((n : ℝ) +ᵥ σ) ((m : ℝ) +ᵥ (ModularGroup.S • σ)) = 0 := by
  intro n m hn hm σ
  rcases hm with hm | hm | hm
  · subst hm
    have h := tile_KfunClear_shift_vanish ℓ d hd n (-1) hn (Or.inr rfl) σ
    simpa using h
  · subst hm
    have h := KfunClear_vadd_S_eq_zero ℓ d hd n hn σ
    simpa using h
  · subst hm
    have h := tile_KfunClear_shift_vanish ℓ d hd n 1 hn (Or.inl rfl) σ
    simpa using h

end Work.Asymptotics.Tile
