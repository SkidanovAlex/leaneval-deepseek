/-
# The `r`-seminorm bound for the CKMRV layer on the cusp-`0` tile `E = KEpsilon`

For `ℓ : LogLambdaData` and `d ∈ {8,24}` the `r`-seminorms of the CKMRV layer
`Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ ·` (the punctured paper layer `F₂` of
CKMRV (5.2)--(5.3), equal to `Work.Asymptotics.paperLayer` off `r = 0`) grow at most like a power
of `Work.Kernels.scale τ` on the cusp-`0` neighbourhood `E = KEpsilon = {τ ∈ 𝒟 : 2 ≤ Im (S•τ)}`.

## The route

The layer is decomposed at the `w`-dependent threshold `T w = E_T w = Im (S • w) + 1` (the height
of the highest pole of `z ↦ K(w,z)`, plus one):

* `layerLow`                     — the contour over `(0,1]`, bounded on `E` by `E_layerLow_seminorm`
  from the cusp-`0` flatness `EFlat`;
* `E_WinT = sinSq r · ∫_1^{T w} K(w,it)e^{-πr²t}dt` — bounded by `E_WinT_seminorm` from the plain
  polynomial window `EpolyWindowE_clean_far`;
* `E_DevT = sinSq r · ∫_{T w}^∞ (K - Aexp)(w,it)e^{-πr²t}dt` — bounded by `E_DevT_seminorm` from
  the sharp deviation `E_deviation_sharp`;
* `E_TailClosed (Gcusp ℓ d) (T w) w` — the closed form of `sinSq r ∫_{T w}^∞ Aexp·e^{-πr²t}`.

Two elementary identities glue the pieces (proved in separate modules):

* `Work.CKFinal.layerTrunc_split_E_T` — the splitting of the `trunc` integral at `T w`;
* `Work.CKFinal.highPart_E_TailClosed_integral` — `highPart = E_TailClosed B + sinSq r ∫_1^B Aexp`,
  an FTC identity between closed forms;

together they give `paperLayer = E_ExprT` on `E`, where
`E_ExprT = layerLow + E_WinT + E_DevT + E_TailClosed (Gcusp ℓ d) (E_T w)`.

The only genuinely new estimate is the last piece: in dimension `24` the model `Aexp` carries the
terms `e^{2πt}(G 1 0 + t i G 1 1)` whose coefficients are only `e^{-2π Im (S•w)}`-small
(`Work.Asymptotics.Gcusp_row_one_small_E`), and that is exactly what compensates the growth of
`e^{-(x-2π)B}` for `x = πr² < 2π` at `B = T w`.  This is the shape bound
`Work.CKFinal.tcLambda_shape_exp_small_uniform` applied to `Gcusp` and `B = E_T w`
(`ts_KE_tcLambda_shape` below), and the resulting seminorm bound of `E_TailClosed` is
`ts_KE_E_TailClosed_seminorm`.  All four bounds are used through the identity in the final
assembly, with the puncture at `r = 0` handled by `punctured_iteratedDeriv`.
-/
import Mathlib
import Submission.Work.Asymptotics.TSasm.cuspOneLowHalfTile_TS
import Submission.Work.Asymptotics.TSasm.layerSemi_lowHalfFunnelNegRe
import Submission.Work.HFN.seminormK_cusp0_half
import Submission.Work.CKFinal.highPart_E_TailClosed_integral
import Submission.Work.CKFinal.PBClone.Submission_Work_CKFinal_layerTrunc_split_E_T
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.E_seminorm
import Submission.Work.CKFinal.PBClone.Submission_Work_Asymptotics_SeminormK_E_clean
import Submission.Work.CKFinal.PBClone.Submission_Work_Asymptotics_cuspRegion_seminorm_disk0
import Submission.Work.Asymptotics.SKEC.E_WinT_seminorm
import Submission.Work.CKFinal.PBClone.Submission_Work_Asymptotics_EpolyWindowE_top
import Submission.Work.Asymptotics.E_TailClosed
import Submission.Work.Asymptotics.E_TailClosed_seminorm
import Submission.Work.Asymptotics.GcuspInP
import Submission.Work.Asymptotics.punctured_iteratedDeriv
import Submission.Work.CKFinal.tcLambda_shape_exp_small_uniform

noncomputable section

open scoped Topology ContDiff MatrixGroups UpperHalfPlane
open MeasureTheory Filter UpperHalfPlane

namespace Work.Asymptotics


/-! ## 1. Elementary: the layer is an even function of `r` -/

private lemma layerLow_neg_K (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.layerLow ℓ d τ (-s) = Work.Asymptotics.layerLow ℓ d τ s := by
  simp only [Work.Asymptotics.layerLow, Work.Asymptotics.sinSq]
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  rw [hsq]

private lemma layerTrunc_neg_K (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.layerTrunc G ℓ d τ (-s) = Work.Asymptotics.layerTrunc G ℓ d τ s := by
  simp only [Work.Asymptotics.layerTrunc, Work.Asymptotics.sinSq]
  have hsq : (((-s : ℝ)) : ℂ) ^ 2 = ((s : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  rw [hsq]

private lemma highPart_neg_K (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.highPart G τ (-s) = Work.Asymptotics.highPart G τ s := by
  simp only [Work.Asymptotics.highPart, neg_sq]

/-- The paper layer is even in the radial variable. -/
theorem paperLayer_neg_K (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.paperLayer G ℓ d τ (-s) = Work.Asymptotics.paperLayer G ℓ d τ s := by
  simp only [Work.Asymptotics.paperLayer]
  rw [layerLow_neg_K, layerTrunc_neg_K, highPart_neg_K]

/-! ## 2. Shape constants of `tcLambda` at the threshold `E_T w` -/

/-- **Shape bound for `tcLambda` at the threshold `E_T w`.**  Here `G = Gcusp ℓ d`: its `(0,j)`
coefficients grow at most like a power of `scale w` (`GcuspInP`), while the `(1,j)` coefficients
are `e^{-2π Im (S•w)} = e^{2π}e^{-2π E_T w}`-small (`Gcusp_row_one_small_E`), which dominates the
factor `e^{(2π-πr²)E_T w}` of the second pair of terms of `tcLambda` for all `x = πr² ≥ 0`. -/
theorem ts_KE_tcLambda_shape (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (l : ℕ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ x : ℝ, 0 ≤ x →
        ‖iteratedDeriv l
            (Work.Asymptotics.tcLambda (Work.Asymptotics.Gcusp ℓ d) (Work.Asymptotics.E_T w) w) x‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + |x|) * Real.exp (-x) := by
  obtain ⟨C1, N1, hC1pos, hN1, hG1row⟩ := Work.Asymptotics.Gcusp_row_one_small_E ℓ d hd
  obtain ⟨a0, b0, ha0, hb0, hb00⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Work.Asymptotics.KEpsilon
      (Work.Asymptotics.Gcusp ℓ d 0 0)).mp
      ((Work.Asymptotics.GcuspInP ℓ d 0 0).mono Work.Asymptotics.KEpsilon_subset_DomainD)
  obtain ⟨a1, b1, ha1, hb1, hb01⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Work.Asymptotics.KEpsilon
      (Work.Asymptotics.Gcusp ℓ d 0 1)).mp
      ((Work.Asymptotics.GcuspInP ℓ d 0 1).mono Work.Asymptotics.KEpsilon_subset_DomainD)
  obtain ⟨C, N, hC, hN, hb⟩ := Work.CKFinal.tcLambda_shape_exp_small_uniform (max a0 a1) (max b0 b1)
    (C1 * Real.exp (2 * Real.pi)) N1 (le_max_of_le_left ha0) (le_max_of_le_left hb0)
    (by positivity) hN1 l
  refine ⟨C, N, hC, hN, ?_⟩
  intro w hw x hx
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hspos : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hG0 : ∀ j : Fin 2, ‖Work.Asymptotics.Gcusp ℓ d 0 j w‖
      ≤ max a0 a1 * (Work.Kernels.scale w) ^ (max b0 b1) := by
    intro j
    have hmaxC : (0 : ℝ) ≤ max a0 a1 := le_trans ha0 (le_max_left _ _)
    fin_cases j
    · refine le_trans (hb00 w hw) (mul_le_mul (le_max_left _ _)
        (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _))
        (Real.rpow_nonneg hspos.le _) hmaxC)
    · refine le_trans (hb01 w hw) (mul_le_mul (le_max_right _ _)
        (Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _))
        (Real.rpow_nonneg hspos.le _) hmaxC)
  have hG1' : ∀ j : Fin 2, ‖Work.Asymptotics.Gcusp ℓ d 1 j w‖
      ≤ (C1 * Real.exp (2 * Real.pi)) * (Work.Kernels.scale w) ^ N1
          * Real.exp (-(2 * Real.pi * Work.Asymptotics.E_T w)) := by
    intro j
    have h := hG1row w hw j
    have he : Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
        = Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * Work.Asymptotics.E_T w)) := by
      rw [← Real.exp_add]
      congr 1
      rw [Work.Asymptotics.E_T]
      ring
    rw [he] at h
    calc ‖Work.Asymptotics.Gcusp ℓ d 1 j w‖
        ≤ C1 * (Work.Kernels.scale w) ^ N1
            * (Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * Work.Asymptotics.E_T w))) := h
      _ = (C1 * Real.exp (2 * Real.pi)) * (Work.Kernels.scale w) ^ N1
            * Real.exp (-(2 * Real.pi * Work.Asymptotics.E_T w)) := by ring
  exact hb (Work.Asymptotics.Gcusp ℓ d) w (Work.Asymptotics.E_T w) (Work.Asymptotics.one_le_E_T hw)
    (Work.Asymptotics.E_T_le_scale hw) hG0 hG1' x hx

/-! ## 3. The seminorm bound of the `E_T`-closed form -/

/-- **The `r`-seminorms of `E_TailClosed (Gcusp ℓ d) (E_T w) w` on `E`.**  This is the fourth piece
of the layer decomposition; unlike `Work.Asymptotics.E_TailClosed_seminorm_T` it needs no
`2 < r²`/`G 1 j = 0` restriction, because at the threshold `B = E_T w` the growth of the `(1,j)`-row
is compensated by its exponential smallness (`ts_KE_tcLambda_shape`). -/
theorem ts_KE_E_TailClosed_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
        (|r| ^ k) * ‖iteratedDeriv l
            (Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  intro k l
  choose Csh Nsh hCsh hNsh hsh using fun j : ℕ => ts_KE_tcLambda_shape ℓ d hd j
  obtain ⟨n, cc, m, jj, hmle, hjle, hrepr⟩ := Work.Asymptotics.E_exists_chain_repr_univ l
  obtain ⟨Bg, hBgnn, hBg⟩ := Work.Asymptotics.E_gauss_bound (k + l) 1
  have hBg' : ∀ x : ℝ, (1 + |x|) ^ (k + l) * (1 + Real.pi * x ^ 2)
      * Real.exp (-(Real.pi * x ^ 2)) ≤ Bg := by
    intro x
    simpa only [pow_one] using hBg x
  set Ctot : ℝ := ∑ j ∈ Finset.range (l + 1), Csh j with hCtotdef
  set Ntot : ℝ := ∑ j ∈ Finset.range (l + 1), max (Nsh j) 0 with hNtotdef
  have hCtot0 : 0 ≤ Ctot := by
    rw [hCtotdef]
    exact Finset.sum_nonneg (fun j _ => hCsh j)
  have hNtot0 : 0 ≤ Ntot := by
    rw [hNtotdef]
    exact Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have hCsh_le : ∀ j : ℕ, j ≤ l → Csh j ≤ Ctot := by
    intro j hj
    rw [hCtotdef]
    exact Finset.single_le_sum (fun i _ => hCsh i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hNsh_le : ∀ j : ℕ, j ≤ l → Nsh j ≤ Ntot := by
    intro j hj
    have h1 : max (Nsh j) 0 ≤ Ntot := by
      rw [hNtotdef]
      exact Finset.single_le_sum (fun i _ => le_max_right (Nsh i) 0)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    exact le_trans (le_max_left _ _) h1
  refine ⟨Bg * (∑ i : Fin n, ‖cc i‖ * Ctot), Ntot, by positivity, hNtot0, ?_⟩
  intro w hw r
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hspos : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have hC' : ∀ j : ℕ, 0 ≤ Csh j * (Work.Kernels.scale w) ^ Nsh j :=
    fun j => mul_nonneg (hCsh j) (Real.rpow_nonneg hspos.le _)
  have hJ' : ∀ j : ℕ, ∀ x : ℝ, (0 : ℝ) ≤ x →
      ‖iteratedDeriv j (Work.Asymptotics.tcLambda (Work.Asymptotics.Gcusp ℓ d)
        (Work.Asymptotics.E_T w) w) x‖
        ≤ (Csh j * (Work.Kernels.scale w) ^ Nsh j) * (1 + |x|) * Real.exp (-x) := by
    intro j x hx
    exact hsh j w hw x hx
  have hrepr' : ∀ x : ℝ, iteratedDeriv l
        (fun s : ℝ => Work.Asymptotics.tcLambda (Work.Asymptotics.Gcusp ℓ d)
          (Work.Asymptotics.E_T w) w (Real.pi * s ^ 2)) x
      = ∑ i : Fin n, cc i * (x : ℂ) ^ (m i)
          * iteratedDeriv (jj i) (Work.Asymptotics.tcLambda (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w) (Real.pi * x ^ 2) :=
    fun x => hrepr (Work.Asymptotics.tcLambda (Work.Asymptotics.Gcusp ℓ d)
      (Work.Asymptotics.E_T w) w) (Work.Asymptotics.contDiff_tcLambda _ _ _) x
  have hmain := Work.Asymptotics.E_comp_quad_bound_of_shape (J := Work.Asymptotics.tcLambda
      (Work.Asymptotics.Gcusp ℓ d) (Work.Asymptotics.E_T w) w) k l
    (fun j => Csh j * (Work.Kernels.scale w) ^ Nsh j) hC' 0 Bg hJ' cc m jj hBg' hmle hrepr'
    r (by positivity : (0 : ℝ) ≤ Real.pi * r ^ 2)
  have hfun : (Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
        (Work.Asymptotics.E_T w) w)
      = fun s : ℝ => Work.Asymptotics.tcLambda (Work.Asymptotics.Gcusp ℓ d)
          (Work.Asymptotics.E_T w) w (Real.pi * s ^ 2) := by
    funext s
    rw [Work.Asymptotics.E_TailClosed]
  rw [hfun]
  refine le_trans hmain ?_
  have hterm : ∀ i : Fin n, ‖cc i‖ * (Csh (jj i) * (Work.Kernels.scale w) ^ Nsh (jj i))
      ≤ ‖cc i‖ * (Ctot * (Work.Kernels.scale w) ^ Ntot) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine mul_le_mul (hCsh_le (jj i) (hjle i))
      (Real.rpow_le_rpow_of_exponent_le hs1 (hNsh_le (jj i) (hjle i)))
      (Real.rpow_nonneg hspos.le _) hCtot0
  calc Bg * ∑ i : Fin n, ‖cc i‖ * (Csh (jj i) * (Work.Kernels.scale w) ^ Nsh (jj i))
      ≤ Bg * ∑ i : Fin n, ‖cc i‖ * (Ctot * (Work.Kernels.scale w) ^ Ntot) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) hBgnn
    _ = Bg * ((∑ i : Fin n, ‖cc i‖ * Ctot) * (Work.Kernels.scale w) ^ Ntot) := by
        congr 1
        calc ∑ i : Fin n, ‖cc i‖ * (Ctot * (Work.Kernels.scale w) ^ Ntot)
            = ∑ i : Fin n, (‖cc i‖ * Ctot) * (Work.Kernels.scale w) ^ Ntot :=
              Finset.sum_congr rfl (fun i _ => by ring)
          _ = (∑ i : Fin n, ‖cc i‖ * Ctot) * (Work.Kernels.scale w) ^ Ntot :=
              (Finset.sum_mul Finset.univ (fun i : Fin n => ‖cc i‖ * Ctot)
                ((Work.Kernels.scale w) ^ Ntot)).symm
    _ = Bg * (∑ i : Fin n, ‖cc i‖ * Ctot) * (Work.Kernels.scale w) ^ Ntot := by ring

/-! ## 4. `paperLayer` is the `E_T`-decomposition `E_ExprT` -/

/-- **The layer identity on `E`**: the paper layer `F₂` coincides with the `T w`-decomposition
`Work.Asymptotics.E_ExprT` (`= layerLow + E_WinT + E_DevT + E_TailClosed (Gcusp ℓ d) (E_T w)`). -/
theorem ts_KE_paperLayer_eq_E_ExprT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w r
        = Work.Asymptotics.E_ExprT ℓ d w r := by
  intro w hw r
  have hsplit := Work.CKFinal.layerTrunc_split_E_T ℓ d hd w hw r
  have hhigh := Work.CKFinal.highPart_E_TailClosed_integral (Work.Asymptotics.Gcusp ℓ d) w
    (Work.Asymptotics.E_T w) r
  show Work.Asymptotics.layerLow ℓ d w r
      + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d w r
      + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) w r
    = Work.Asymptotics.layerLow ℓ d w r + Work.Asymptotics.E_WinT ℓ d w r
      + Work.Asymptotics.E_DevT ℓ d w r
      + Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d) (Work.Asymptotics.E_T w) w r
  rw [hsplit, hhigh]
  ring

/-! ## 5. The target -/

theorem layer_semi_KEpsilon_TS (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  have hflat : Work.Asymptotics.EFlat ℓ d := (Work.Asymptotics.Epoint_Kfun ℓ d hd).1
  obtain ⟨Cw, Nw, Mw, hCw, hNw, hMw, hwin0⟩ := Work.Asymptotics.EpolyWindowE_clean_far ℓ d hd
  obtain ⟨Cd, Nd, Md, hCd, hNd, hMd, hdev⟩ := Work.Asymptotics.E_deviation_sharp ℓ d hd
  set C : ℝ := max Cw (Cd * Real.exp (-Real.pi)) with hCdef
  set N : ℝ := max Nw Nd with hNdef
  set M : ℝ := max Mw Md with hMdef
  have hCpos : 0 < C := lt_max_of_lt_left hCw
  have hN0 : 0 ≤ N := le_max_of_le_left hNw
  have hM0 : 0 ≤ M := le_max_of_le_left hMw
  have hwin : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon → 1 ≤ t →
      t ≤ Work.Asymptotics.E_T w →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
    intro w t hw ht1 htT
    have hb := hwin0 w t hw (lt_of_lt_of_le zero_lt_one ht1)
      (le_trans htT (Work.Asymptotics.E_T_le_scale hw))
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hspos : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have e1 : Cw ≤ C := by rw [hCdef]; exact le_max_left _ _
    have e2 : (Work.Kernels.scale w) ^ Nw ≤ (Work.Kernels.scale w) ^ N :=
      Real.rpow_le_rpow_of_exponent_le hs1 (by rw [hNdef]; exact le_max_left _ _)
    have e3 : (1 + t) ^ Mw ≤ (1 + t) ^ M :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hMdef]; exact le_max_left _ _)
    have h0s : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
    have h0t : (0 : ℝ) ≤ 1 + t := by linarith
    have e2' : (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw
        ≤ (Work.Kernels.scale w) ^ N * (1 + t) ^ M :=
      le_trans (mul_le_mul_of_nonneg_right e2 (Real.rpow_nonneg h0t Mw))
        (mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg h0s N))
    have e1' : Cw * ((Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw)
        ≤ C * ((Work.Kernels.scale w) ^ N * (1 + t) ^ M) :=
      le_trans (mul_le_mul_of_nonneg_right e1
          (mul_nonneg (Real.rpow_nonneg h0s Nw) (Real.rpow_nonneg h0t Mw)))
        (mul_le_mul_of_nonneg_left e2' hCpos.le)
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw := hb
      _ = Cw * ((Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw) := by ring
      _ ≤ C * ((Work.Kernels.scale w) ^ N * (1 + t) ^ M) := e1'
      _ = C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by ring
  have htail : ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
      Work.Asymptotics.E_T w ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by
    intro w t hw htT
    have him : (ModularGroup.S • w).im + 1 ≤ t := by
      rw [Work.Asymptotics.E_T] at htT
      exact htT
    have hb := hdev w t hw him
    have he : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
        = Real.exp (-Real.pi) * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by
      rw [← Real.exp_add]
      congr 1
      rw [Work.Asymptotics.E_T]
      ring
    rw [he] at hb
    have hb' : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
        ≤ (Cd * Real.exp (-Real.pi)) * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
            * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
          ≤ Cd * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
              * (Real.exp (-Real.pi) * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w)))) := hb
        _ = (Cd * Real.exp (-Real.pi)) * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
              * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by ring
    have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hspos : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
    have ht0 : (1 : ℝ) ≤ 1 + t := by
      have : (1 : ℝ) ≤ t := le_trans (Work.Asymptotics.one_le_E_T hw) htT
      linarith
    have e1 : Cd * Real.exp (-Real.pi) ≤ C := by rw [hCdef]; exact le_max_right _ _
    have e2 : (Work.Kernels.scale w) ^ Nd ≤ (Work.Kernels.scale w) ^ N :=
      Real.rpow_le_rpow_of_exponent_le hs1 (by rw [hNdef]; exact le_max_right _ _)
    have e3 : (1 + t) ^ Md ≤ (1 + t) ^ M :=
      Real.rpow_le_rpow_of_exponent_le ht0 (by rw [hMdef]; exact le_max_right _ _)
    refine le_trans hb' ?_
    have h0s : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
    have h0t : (0 : ℝ) ≤ 1 + t := by linarith
    have hfac : (Cd * Real.exp (-Real.pi)) * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
        ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
      have e2' : (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
          ≤ (Work.Kernels.scale w) ^ N * (1 + t) ^ M :=
        le_trans (mul_le_mul_of_nonneg_right e2 (Real.rpow_nonneg h0t Md))
          (mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg h0s N))
      have e1' : (Cd * Real.exp (-Real.pi)) * ((Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md)
          ≤ C * ((Work.Kernels.scale w) ^ N * (1 + t) ^ M) :=
        le_trans (mul_le_mul_of_nonneg_right e1
            (mul_nonneg (Real.rpow_nonneg h0s Nd) (Real.rpow_nonneg h0t Md)))
          (mul_le_mul_of_nonneg_left e2' hCpos.le)
      calc (Cd * Real.exp (-Real.pi)) * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
          = (Cd * Real.exp (-Real.pi)) * ((Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md) := by ring
        _ ≤ C * ((Work.Kernels.scale w) ^ N * (1 + t) ^ M) := e1'
        _ = C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by ring
    calc (Cd * Real.exp (-Real.pi)) * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
          * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w)))
        ≤ (C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M)
            * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) :=
          mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _)
      _ = C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
            * Real.exp (-(Real.pi * (t - Work.Asymptotics.E_T w))) := by ring
  intro k l
  obtain ⟨c1, N1, hc1, h1⟩ := Work.Asymptotics.E_layerLow_seminorm ℓ d hd hflat k l
  obtain ⟨c2, N2, hc2, hN2, h2⟩ := Work.Asymptotics.E_WinT_seminorm ℓ d hd C N M hCpos hN0 hM0 hwin k l
  obtain ⟨c3, N3, hc3, hN3, h3⟩ := Work.Asymptotics.E_DevT_seminorm ℓ d hd C N M hCpos hN0 hM0 htail k l
  obtain ⟨c4, N4, hc4, hN4, h4⟩ := ts_KE_E_TailClosed_seminorm ℓ d hd k l
  set Ntot : ℝ := max (max (max N1 0) N2) (max N3 N4) with hNtotdef
  have hNtot0 : 0 ≤ Ntot := by
    rw [hNtotdef]
    exact le_trans hN2 (le_trans (le_max_right (max N1 0) N2)
      (le_max_left (max (max N1 0) N2) (max N3 N4)))
  have hCsum : (0 : ℝ) ≤ c1 + c2 + c3 + c4 := by linarith
  refine ⟨c1 + c2 + c3 + c4, Ntot, hCsum, hNtot0, ?_⟩
  intro w hw r
  have hN1tot : N1 ≤ Ntot := by
    rw [hNtotdef]
    exact le_trans (le_max_left N1 0)
      (le_trans (le_max_left (max N1 0) N2) (le_max_left (max (max N1 0) N2) (max N3 N4)))
  have hN2tot : N2 ≤ Ntot := by
    rw [hNtotdef]
    exact le_trans (le_max_right (max N1 0) N2) (le_max_left (max (max N1 0) N2) (max N3 N4))
  have hN3tot : N3 ≤ Ntot := by
    rw [hNtotdef]
    exact le_trans (le_max_left N3 N4) (le_max_right (max (max N1 0) N2) (max N3 N4))
  have hN4tot : N4 ≤ Ntot := by
    rw [hNtotdef]
    exact le_trans (le_max_right N3 N4) (le_max_right (max (max N1 0) N2) (max N3 N4))
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have h1' : c1 * (Work.Kernels.scale w) ^ N1 ≤ c1 * (Work.Kernels.scale w) ^ Ntot :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN1tot) hc1
  have h2' : c2 * (Work.Kernels.scale w) ^ N2 ≤ c2 * (Work.Kernels.scale w) ^ Ntot :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN2tot) hc2
  have h3' : c3 * (Work.Kernels.scale w) ^ N3 ≤ c3 * (Work.Kernels.scale w) ^ Ntot :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN3tot) hc3
  have h4' : c4 * (Work.Kernels.scale w) ^ N4 ≤ c4 * (Work.Kernels.scale w) ^ Ntot :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs1 hN4tot) hc4
  -- the four pieces are `C¹` in `r`
  have hcd1 : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r :=
    ((Work.Asymptotics.E_contDiff_omega_layerLow ℓ d hd hflat hw).contDiffAt).of_le le_top
  have hcd2 : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r :=
    ((Work.Asymptotics.E_contDiff_omega_E_WinT ℓ d hd C N M hCpos hN0 hM0 hwin hw).contDiffAt).of_le
      le_top
  have hcd3 : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r :=
    ((Work.Asymptotics.E_contDiff_omega_E_DevT ℓ d hd C N M hCpos hN0 hM0 htail hw).contDiffAt).of_le
      le_top
  have hcd4 : ContDiffAt ℝ (l : ℕ∞) (fun s : ℝ =>
      Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d) (Work.Asymptotics.E_T w) w s) r :=
    ((Work.Asymptotics.contDiff_E_TailClosed _ _ _).contDiffAt).of_le le_top
  -- the bound for the decomposition
  have hE : |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s) r‖
      ≤ (c1 + c2 + c3 + c4) * (Work.Kernels.scale w) ^ Ntot := by
    have b1 := h1 w r hw
    have b2 := h2 w hw r
    have b3 := h3 w hw r
    have b4 := h4 w hw r
    have hFE : (fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s)
        = ((fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s)
            + fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s)
          + (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w s := by
      funext s
      rw [Work.Asymptotics.E_ExprT]
      rfl
    have h1s : iteratedDeriv l (((fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s)) r
        = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r :=
      iteratedDeriv_add hcd1 hcd2
    have h2s : iteratedDeriv l ((((fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s))
          + fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r
        = iteratedDeriv l ((fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r :=
      iteratedDeriv_add (hcd1.add hcd2) hcd3
    have h3s : iteratedDeriv l (((((fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s))
          + fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w s) r
        = iteratedDeriv l (((fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s)
          + fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w s) r :=
      iteratedDeriv_add ((hcd1.add hcd2).add hcd3) hcd4
    rw [hFE, h3s, h2s, h1s]
    have hnorm : ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w s) r‖
        ≤ ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w s) r‖ := by
      have a1 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
          (Work.Asymptotics.E_T w) w s) r)
      have a2 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r
        + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r)
      have a3 := norm_add_le (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r)
        (iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r)
      linarith
    calc |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r
          + iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w s) r‖
        ≤ |r| ^ k * (‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r‖
          + ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w s) r‖) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layerLow ℓ d w s) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_WinT ℓ d w s) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_DevT ℓ d w s) r‖
          + |r| ^ k * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_TailClosed
              (Work.Asymptotics.Gcusp ℓ d) (Work.Asymptotics.E_T w) w s) r‖ := by ring
      _ ≤ c1 * (Work.Kernels.scale w) ^ N1 + c2 * (Work.Kernels.scale w) ^ N2
          + c3 * (Work.Kernels.scale w) ^ N3 + c4 * (Work.Kernels.scale w) ^ N4 := by
          linarith
      _ ≤ (c1 + c2 + c3 + c4) * (Work.Kernels.scale w) ^ Ntot := by linarith [h1', h2', h3', h4']
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    rcases eq_or_ne r 0 with hr | hr
    · subst hr
      have hz : Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w 0 = 0 := by
        rw [Work.Asymptotics.layer]
        simp
      show |(0 : ℝ)| ^ k * ‖Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w 0‖
          ≤ (c1 + c2 + c3 + c4) * (Work.Kernels.scale w) ^ Ntot
      rw [hz, norm_zero, mul_zero]
      exact mul_nonneg hCsum (Real.rpow_nonneg (Work.Kernels.scale_pos w).le _)
    · have hev : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
          =ᶠ[𝓝 r] (fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s) := by
        filter_upwards [isOpen_ne.mem_nhds hr] with s hs
        rw [Work.Asymptotics.layer, if_neg hs]
        exact ts_KE_paperLayer_eq_E_ExprT ℓ d hd w hw s
      rw [Work.Asymptotics.iteratedDeriv_congr_of_eventuallyEq hev 0]
      exact hE
  · -- `l ≥ 1`: the puncture at `r = 0` does not affect the `l`-th derivative
    have hdiffP : Differentiable ℝ
        (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) := by
      have h1eq : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
          = fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s :=
        funext (ts_KE_paperLayer_eq_E_ExprT ℓ d hd w hw)
      rw [h1eq]
      exact ((Work.Asymptotics.E_contDiff_omega_E_ExprT ℓ d hd hflat hCpos hN0 hM0 hw hwin
        htail).differentiable (by simp))
    have hpaper : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
        = fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s :=
      funext (ts_KE_paperLayer_eq_E_ExprT ℓ d hd w hw)
    have hpun : iteratedDeriv l (fun s : ℝ =>
          if s = 0 then 0 else Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
        = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) :=
      Work.Asymptotics.punctured_iteratedDeriv
        (f := fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
        (fun s => paperLayer_neg_K (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) hdiffP l hl
    have hrep : (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
        = fun s : ℝ => (if s = 0 then 0
            else Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) := by
      funext s
      rw [Work.Asymptotics.layer]
    have hstep : iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d)
          ℓ d w s)
        = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s) := by
      calc iteratedDeriv l (fun s : ℝ => Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
          = iteratedDeriv l (fun s : ℝ => (if s = 0 then 0
              else Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)) := by rw [hrep]
        _ = iteratedDeriv l (fun s : ℝ =>
              Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) := hpun
        _ = iteratedDeriv l (fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s) := by rw [hpaper]
    rw [hstep]
    exact hE

end Work.Asymptotics
