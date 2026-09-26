/-
# The `r`-seminorm bound for the CKMRV layer on the cusp-`0` tile `E = KEpsilon`
(clean, `exists_F2_socket`-compatible chain)

For `ℓ : LogLambdaData` and `d ∈ {8,24}` the `r`-seminorms of the CKMRV layer
`Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ ·` (the punctured paper layer `F₂` of
CKMRV (5.2)--(5.3), equal to `Work.Asymptotics.paperLayer` off `r = 0`) grow at most like a power
of `Work.Kernels.scale τ` on the cusp-`0` neighbourhood
`E = KEpsilon = {τ ∈ 𝒟 : 2 ≤ Im (S • τ)}`.

This is the same theorem as `Submission.Work.CKFinal.layer_semi_KEpsilon`, under a fresh name and
on the branch of the library that is compatible with the `exists_F2_socket` chain.

## Why a separate module

The library currently contains, for 241 declarations, two modules declaring the same name: the
`exists_F2_socket` chain uses `Work.Asymptotics.MiddleRange.{Main,Coincidence}`,
`Work.Asymptotics.CuspExp.smallT_bound`, `Work.Asymptotics.layer_vadd_ladder`, ... while the chain
of `Submission.Work.CKFinal.layer_semi_KEpsilon` (through `E_deviation_sharp` → `ETailE_one` and
`EtailE.Assembly`) carries the branch copies of `Work.Asymptotics.coe_S_smul` and
`Work.Asymptotics.Gcusp_eq_Gcoef`.  Consequently that module cannot be imported together with
`Submission.Work.CKFinal.exists_F2_socket` (or with the `FunnelAsm`/`TSasm` chain), and the
statement has to be *re-proved* on the compatible branch, with a fresh name so that no shadow copy
whose declarations duplicate the originals is needed.

## The branch used here

The same decomposition at the `τ`-dependent threshold `T τ = E_T τ = Im (S • τ) + 1` as in
`layer_semi_KEpsilon`, with the *compatible* copies of every input whose original lies on the
`ETailE_one` branch:

* `Submission.Work.CKFinal.tcLambda_shape_exp_small_uniform` — the shape bound for `tcLambda`
  at the threshold (`Work.CKFinal.tcLambda_shape_E_T` below); this is the genuine clean lemma,
  not the `sorry`-stub that the mechanically generated `PBClone` twin of
  `layer_semi_KEpsilon` uses;
* `Submission.Work.CKFinal.PBClone.Submission_Work_Asymptotics_{E_deviation_sharp,
  SKEC_FarWindowClean, EpolyWindowE_top}` — the sharp deviation `E_deviation_sharp`, the plain
  window `EpolyWindowE_clean_far`, and the row-smallness `Gcusp_row_one_small_E`
  (`ETailE_one`-free copies);
* `Submission.Work.CKFinal.PBClone.Submission_Work_Asymptotics_cuspRegion_seminorm_disk0` —
  the smoothness of the pieces `E_contDiff_omega_E_WinT`, `E_contDiff_omega_E_DevT` and the
  window/deviation seminorm bounds `E_WinT_seminorm`, `E_DevT_seminorm`;
* the clean room: `E_seminorm` (`E_layerLow_seminorm`, `E_contDiff_omega_layerLow`),
  `E_TailClosed`, `E_TailClosed_seminorm`, `GcuspInP`, `punctured_iteratedDeriv`.

Reference to `Work.CKFinal.layerTrunc_split_E_T` (proved there on the `ETailE_one` branch) is
replaced by the local, branch-free `Work.CKFinal.layerTrunc_split_KEpsilon`.

Every auxiliary declaration of this file is `private`: the module exports exactly the requested
theorem, so importing it can never introduce a duplicate declaration.

The two identities gluing the pieces are `layerTrunc_split_KEpsilon` (splitting of the `trunc`
integral at `T τ`) and `Work.CKFinal.highPart_E_TailClosed_integral`
(`highPart = E_TailClosed B + sinSq r ∫_1^B Aexp`), and they give `paperLayer = E_ExprT` on `E`.
The four seminorm bounds `E_layerLow_seminorm`, `E_WinT_seminorm`, `E_DevT_seminorm` and
`E_TailClosed_gcusp_T_seminorm` are then summed, and the puncture at `r = 0` is removed with
`punctured_iteratedDeriv`.
-/
import Mathlib
import Submission.Work.CKFinal.highPart_E_TailClosed_integral
import Submission.Work.CKFinal.setIntegral_Ici_eq_Ioi_of_eq_zero_below
import Submission.Work.CKFinal.tcLambda_shape_exp_small_uniform
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

noncomputable section

open scoped Topology ContDiff MatrixGroups UpperHalfPlane
open MeasureTheory Filter UpperHalfPlane

namespace Work.CKFinal

/-! ## 0. (This module needs no stubs: every input is imported.) -/

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
private theorem paperLayer_neg_K (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : UpperHalfPlane) (s : ℝ) :
    Work.Asymptotics.paperLayer G ℓ d τ (-s) = Work.Asymptotics.paperLayer G ℓ d τ s := by
  simp only [Work.Asymptotics.paperLayer]
  rw [layerLow_neg_K, layerTrunc_neg_K, highPart_neg_K]

/-! ## 2. Shape constants of `tcLambda` at the threshold `E_T w` -/

/-- **Shape bound for `tcLambda` at the threshold `E_T w`.**  Here `G = Gcusp ℓ d`: its `(0,j)`
coefficients grow at most like a power of `scale w` (`GcuspInP`), while the `(1,j)` coefficients
are `e^{-2π Im (S•w)} = e^{2π}e^{-2π E_T w}`-small (`Gcusp_row_one_small_E`), which dominates the
factor `e^{(2π-πr²)E_T w}` of the second pair of terms of `tcLambda` for all `x = πr² ≥ 0`. -/
private theorem tcLambda_shape_E_T (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (l : ℕ) :
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
  obtain ⟨C, N, hC, hN, hb⟩ := tcLambda_shape_exp_small_uniform (max a0 a1) (max b0 b1)
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
is compensated by its exponential smallness (`tcLambda_shape_E_T`). -/
private theorem E_TailClosed_gcusp_T_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
        (|r| ^ k) * ‖iteratedDeriv l
            (Work.Asymptotics.E_TailClosed (Work.Asymptotics.Gcusp ℓ d)
              (Work.Asymptotics.E_T w) w) r‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  intro k l
  choose Csh Nsh hCsh hNsh hsh using fun j : ℕ => tcLambda_shape_E_T ℓ d hd j
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

/-! ## 4. The deviation is integrable against the Gaussian on `[1,∞)` -/

/-- The modulus of the contour exponential `e^{-πr²t}`. -/
private lemma norm_exp_neg_pi_sq (r t : ℝ) :
    ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [Complex.norm_exp]
  have h : -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

/-- `t ↦ Aexp G τ t` is measurable. -/
private lemma measurable_Aexp_K (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    Measurable (fun t : ℝ => Work.Asymptotics.Aexp G τ t) := by
  unfold Work.Asymptotics.Aexp
  fun_prop

/-- On `[1, E_T w]` the kernel is integrable against the Gaussian: it is polynomially bounded by
the plain window `EpolyWindowE_clean_far`. -/
private lemma integrableOn_Kaxis_window (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w)) := by
  obtain ⟨Cw, Nw, Mw, hCw, hNw, hMw, hwin0⟩ := Work.Asymptotics.EpolyWindowE_clean_far ℓ d hd
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := (Work.Kernels.scale_pos w).le
  have hMnn : (0 : ℝ) ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + Work.Asymptotics.E_T w) ^ Mw :=
    mul_nonneg (mul_nonneg hCw.le (Real.rpow_nonneg hs0 Nw))
      (Real.rpow_nonneg (by linarith [Work.Asymptotics.three_le_E_T hw]) Mw)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (volume.restrict (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w))) :=
    ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd w).mul (by fun_prop)).aestronglyMeasurable
  have hfin : volume (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w)) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.Ioc_subset_Icc_self)
      isCompact_Icc.measure_lt_top)
  refine MeasureTheory.Integrable.mono' (g := fun _ : ℝ => Cw * (Work.Kernels.scale w) ^ Nw
      * (1 + Work.Asymptotics.E_T w) ^ Mw)
    (MeasureTheory.integrableOn_const (μ := volume) (s := Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w))
      hfin) hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
  obtain ⟨ht1, htT⟩ := ht
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
  rw [norm_mul, norm_exp_neg_pi_sq]
  have hb := hwin0 w t hw ht0 (le_trans htT (Work.Asymptotics.E_T_le_scale hw))
  have h1 : (1 + t) ^ Mw ≤ (1 + Work.Asymptotics.E_T w) ^ Mw :=
    Real.rpow_le_rpow (by linarith) (by linarith) hMw
  have h2 : Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by
      have h : (0 : ℝ) ≤ Real.pi * r ^ 2 * t :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) (le_of_lt ht0)
      linarith)
  calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ (Cw * (Work.Kernels.scale w) ^ Nw * (1 + t) ^ Mw) * 1 :=
        mul_le_mul hb h2 (Real.exp_nonneg _) (by positivity)
    _ ≤ Cw * (Work.Kernels.scale w) ^ Nw * (1 + Work.Asymptotics.E_T w) ^ Mw := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left h1 (mul_nonneg hCw.le (Real.rpow_nonneg hs0 Nw))

/-- On `[1, E_T w]` the cusp model is integrable against the Gaussian (it is continuous). -/
private lemma integrableOn_Aexp_window (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) {w : UpperHalfPlane}
    (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w)) := by
  have hcont : Continuous (fun t : ℝ => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    unfold Work.Asymptotics.Aexp
    fun_prop
  exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- Beyond `E_T w` the deviation decays like `e^{-π(t - E_T w)}`, hence is integrable against the
Gaussian for every `r`. -/
private lemma integrableOn_dev_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (Set.Ioi (Work.Asymptotics.E_T w)) := by
  obtain ⟨Cd, Nd, Md, hCd, hNd, hMd, hdev⟩ := Work.Asymptotics.E_deviation_sharp ℓ d hd
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := (Work.Kernels.scale_pos w).le
  have hT3 : (3 : ℝ) ≤ Work.Asymptotics.E_T w := Work.Asymptotics.three_le_E_T hw
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (volume.restrict (Set.Ioi (Work.Asymptotics.E_T w))) :=
    (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd w).sub (measurable_Aexp_K _ _)).mul
      (by fun_prop)).aestronglyMeasurable
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ Md * Real.exp (-(Real.pi * t)))
      (Set.Ioi (0 : ℝ)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := Md) (b := Real.pi)
      (by linarith) one_pos Real.pi_pos
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show x ^ Md * Real.exp (-Real.pi * x ^ (1 : ℝ)) = x ^ Md * Real.exp (-(Real.pi * x))
    rw [Real.rpow_one]
    congr 1
    ring
  set Mj : ℝ := Cd * (Work.Kernels.scale w) ^ Nd
    * Real.exp (Real.pi * Work.Asymptotics.E_T w) * 2 ^ Md with hMj
  have hmaj : MeasureTheory.IntegrableOn (fun t : ℝ => Mj * t ^ Md * Real.exp (-(Real.pi * t)))
      (Set.Ioi (Work.Asymptotics.E_T w)) := by
    have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => Mj * (t ^ Md * Real.exp (-(Real.pi * t))))
        (Set.Ioi (0 : ℝ)) := hbase.const_mul Mj
    have h2 : MeasureTheory.IntegrableOn (fun t : ℝ => Mj * (t ^ Md * Real.exp (-(Real.pi * t))))
        (Set.Ioi (Work.Asymptotics.E_T w)) :=
      h1.mono_set (fun t ht => by
        rw [Set.mem_Ioi] at ht ⊢
        linarith)
    refine h2.congr_fun (fun t _ => ?_) measurableSet_Ioi
    ring
  refine MeasureTheory.Integrable.mono' (g := fun t : ℝ => Mj * t ^ Md * Real.exp (-(Real.pi * t)))
    hmaj hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have htT : Work.Asymptotics.E_T w < t := ht
  have ht1 : (1 : ℝ) ≤ t := by linarith [Work.Asymptotics.three_le_E_T hw]
  have him : (ModularGroup.S • w).im + 1 ≤ t := by
    rw [show (ModularGroup.S • w).im + 1 = Work.Asymptotics.E_T w from rfl]
    exact le_of_lt htT
  have hb := hdev w t hw him
  rw [norm_mul, norm_exp_neg_pi_sq]
  have h2 : Real.exp (-(Real.pi * r ^ 2 * t)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by
      have h : (0 : ℝ) ≤ Real.pi * r ^ 2 * t :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) (by linarith)
      linarith)
  have hpow : (1 + t) ^ Md ≤ 2 ^ Md * t ^ Md := by
    have hle : 1 + t ≤ 2 * t := by linarith
    have h3 : (1 + t) ^ Md ≤ (2 * t) ^ Md := Real.rpow_le_rpow (by linarith) hle hMd
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ t)] at h3
  have hexp : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
      ≤ Real.exp (Real.pi * Work.Asymptotics.E_T w) * Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hSw : (ModularGroup.S • w).im ≤ Work.Asymptotics.E_T w := Work.Asymptotics.E_T_ge_im_S w
    nlinarith [Real.pi_pos]
  have hfac : (0 : ℝ) ≤ Cd * (Work.Kernels.scale w) ^ Nd :=
    mul_nonneg hCd.le (Real.rpow_nonneg hs0 Nd)
  calc ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)‖
        * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ (Cd * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
          * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) * 1 :=
        mul_le_mul hb h2 (Real.exp_nonneg _) (by positivity)
    _ ≤ Cd * (Work.Kernels.scale w) ^ Nd * (2 ^ Md * t ^ Md)
          * (Real.exp (Real.pi * Work.Asymptotics.E_T w) * Real.exp (-(Real.pi * t))) := by
        rw [mul_one]
        calc Cd * (Work.Kernels.scale w) ^ Nd * (1 + t) ^ Md
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
            = (Cd * (Work.Kernels.scale w) ^ Nd)
                * ((1 + t) ^ Md
                    * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))) := by ring
          _ ≤ (Cd * (Work.Kernels.scale w) ^ Nd)
                * ((2 ^ Md * t ^ Md)
                    * (Real.exp (Real.pi * Work.Asymptotics.E_T w)
                        * Real.exp (-(Real.pi * t)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hpow hexp (by positivity) (by positivity))
                hfac
          _ = Cd * (Work.Kernels.scale w) ^ Nd * (2 ^ Md * t ^ Md)
                * (Real.exp (Real.pi * Work.Asymptotics.E_T w)
                    * Real.exp (-(Real.pi * t))) := by ring
    _ = Mj * t ^ Md * Real.exp (-(Real.pi * t)) := by
        rw [hMj]
        ring

/-- **The deviation is integrable against the Gaussian on `[1,∞)`** for every `w ∈ KEpsilon` and
every `r`: on `[1, E_T w]` the kernel and the model are separately integrable, and beyond
`E_T w` the deviation decays like `e^{-π(t-E_T w)}`. -/
private theorem integrableOn_dev_exp_Ici_one_local (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici (1 : ℝ)) := by
  have hT1 : (1 : ℝ) ≤ Work.Asymptotics.E_T w := Work.Asymptotics.one_le_E_T hw
  have hunion : MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w) ∪ Set.Ioi (Work.Asymptotics.E_T w)) := by
    refine (?_ : MeasureTheory.IntegrableOn _ (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w))).union
      (integrableOn_dev_tail ℓ d hd hw r)
    refine ((integrableOn_Kaxis_window ℓ d hd hw r).sub
      (integrableOn_Aexp_window ℓ d (w := w) r)).congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [Pi.sub_apply]
    ring
  rw [Set.Ioc_union_Ioi_eq_Ioi hT1] at hunion
  have hset : volume.restrict (Set.Ioi (1 : ℝ)) = volume.restrict (Set.Ici (1 : ℝ)) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici' (by simp : volume ({(1 : ℝ)} : Set ℝ) = 0))
  change MeasureTheory.Integrable (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (volume.restrict (Set.Ici (1 : ℝ)))
  rw [← hset]
  exact hunion

/-! ## 5. Splitting the `trunc` piece at the cusp threshold `E_T w` -/

/-- `E_DevT` is the tail integral over `(E_T w, ∞)` of the deviation against the Gaussian:
below `E_T w` the integrand of `E_DevT` vanishes, and `{E_T w}` is a null set. -/
private theorem E_DevT_eq_integral_Ioi (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) {w : UpperHalfPlane}
    (hw : w ∈ Work.Asymptotics.KEpsilon) (r : ℝ) :
    Work.Asymptotics.E_DevT ℓ d w r
      = Work.Asymptotics.sinSq r * ∫ t in Set.Ioi (Work.Asymptotics.E_T w),
          (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
              * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  rw [Work.Asymptotics.E_DevT, Work.Asymptotics.tailIntegral]
  congr 1
  refine setIntegral_Ici_eq_Ioi_of_eq_zero_below (B := Work.Asymptotics.E_T w)
    (f := fun t : ℝ => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
    (Work.Asymptotics.one_le_E_T hw) ?_ ?_
  · intro t ht
    rw [if_pos ht, zero_mul]
  · intro t ht
    rw [if_neg (not_lt.mpr ht)]
    congr 1
    rw [show -(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)) = ((-(Real.pi * r ^ 2 * t) : ℝ) : ℂ) by
      push_cast; ring, ← Complex.ofReal_exp]

/-- **The `trunc` piece splits at the cusp threshold `E_T w`.**  With `T := E_T w ≥ 1`,
`∫_{[1,∞)}(Kaxis - Aexp)e^{-πr²t} = ∫_{[1,T]} Kaxis e^{-πr²t} + ∫_{(T,∞)} (Kaxis - Aexp)e^{-πr²t}
- ∫_{[1,T]} Aexp e^{-πr²t}`; after multiplication by `sinSq r` this is the asserted
decomposition of `layerTrunc (Gcusp ℓ d)`. -/
private theorem layerTrunc_split_KEpsilon (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ w : UpperHalfPlane, w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d w r
        = Work.Asymptotics.E_WinT ℓ d w r + Work.Asymptotics.E_DevT ℓ d w r
          - Work.Asymptotics.sinSq r * ∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w),
              Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t
                * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  intro w hw r
  have hT1 : (1 : ℝ) ≤ Work.Asymptotics.E_T w := Work.Asymptotics.one_le_E_T hw
  rw [Work.Asymptotics.layerTrunc, Work.Asymptotics.E_WinT, E_DevT_eq_integral_Ioi ℓ d hw r]
  set F : ℝ → ℂ := fun t => (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hF
  set Kf : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hKf
  set Af : ℝ → ℂ := fun t => Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t
      * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hAf
  have hFint : IntegrableOn F (Set.Ici (1 : ℝ)) :=
    integrableOn_dev_exp_Ici_one_local ℓ d hd hw r
  have hAint : IntegrableOn Af (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w)) := by
    have hcont : Continuous Af := by
      rw [hAf]
      unfold Work.Asymptotics.Aexp
      fun_prop
    exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hKfint : IntegrableOn Kf (Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w)) := by
    refine IntegrableOn.congr_fun ((hFint.mono_set (fun t ht => ht.1.le)).add hAint)
      (fun t _ => ?_) measurableSet_Ioc
    simp only [Pi.add_apply]
    rw [hF, hKf, hAf]
    ring
  have hsplit : ∫ t in Set.Ici (1 : ℝ), F t
      = (∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), F t)
        + ∫ t in Set.Ioi (Work.Asymptotics.E_T w), F t := by
    have h1 : ∫ t in Set.Ici (1 : ℝ), F t = ∫ t in Set.Ioi (1 : ℝ), F t :=
      setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici' (by simp)).symm
    rw [h1, ← Set.Ioc_union_Ioi_eq_Ioi hT1]
    exact setIntegral_union
      (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2)))
      measurableSet_Ioi (hFint.mono_set (fun t ht => ht.1.le))
      (hFint.mono_set (fun t ht => le_trans hT1 ht.le))
  have hsub : ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), F t
      = (∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Kf t)
        - ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Af t := by
    rw [← integral_sub hKfint hAint]
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    rw [hF, hKf, hAf]
    ring
  have hKfIoc : ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Kf t
      = ∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Kf t :=
    (intervalIntegral.integral_of_le hT1).symm
  have hAfIoc : ∫ t in Set.Ioc (1 : ℝ) (Work.Asymptotics.E_T w), Af t
      = ∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Af t :=
    (intervalIntegral.integral_of_le hT1).symm
  have hL : ∫ t in Set.Ici (1 : ℝ), F t
      = (∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Kf t)
        + (∫ t in Set.Ioi (Work.Asymptotics.E_T w), F t)
        - (∫ t in (1 : ℝ)..(Work.Asymptotics.E_T w), Af t) := by
    rw [hsplit, hsub, hKfIoc, hAfIoc]
    ring
  rw [hL]
  ring

/-! ## 6. `paperLayer` is the `E_T`-decomposition `E_ExprT` -/

/-- **The layer identity on `E`**: the paper layer `F₂` coincides with the `T w`-decomposition
`Work.Asymptotics.E_ExprT` (`= layerLow + E_WinT + E_DevT + E_TailClosed (Gcusp ℓ d) (E_T w)`). -/
private theorem paperLayer_eq_E_ExprT (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w r
        = Work.Asymptotics.E_ExprT ℓ d w r := by
  intro w hw r
  have hsplit := layerTrunc_split_KEpsilon ℓ d hd w hw r
  have hhigh := highPart_E_TailClosed_integral (Work.Asymptotics.Gcusp ℓ d) w
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

theorem layer_semi_KEpsilon_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane), τ ∈ Work.Asymptotics.KEpsilon → ∀ r : ℝ,
        |r| ^ k * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ s) r‖
          ≤ C * (Work.Kernels.scale τ) ^ N := by
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
  obtain ⟨c4, N4, hc4, hN4, h4⟩ := E_TailClosed_gcusp_T_seminorm ℓ d hd k l
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
        exact paperLayer_eq_E_ExprT ℓ d hd w hw s
      rw [Work.Asymptotics.iteratedDeriv_congr_of_eventuallyEq hev 0]
      exact hE
  · -- `l ≥ 1`: the puncture at `r = 0` does not affect the `l`-th derivative
    have hdiffP : Differentiable ℝ
        (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s) := by
      have h1eq : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
          = fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s :=
        funext (paperLayer_eq_E_ExprT ℓ d hd w hw)
      rw [h1eq]
      exact ((Work.Asymptotics.E_contDiff_omega_E_ExprT ℓ d hd hflat hCpos hN0 hM0 hw hwin
        htail).differentiable (by simp))
    have hpaper : (fun s : ℝ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d w s)
        = fun s : ℝ => Work.Asymptotics.E_ExprT ℓ d w s :=
      funext (paperLayer_eq_E_ExprT ℓ d hd w hw)
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

end Work.CKFinal
