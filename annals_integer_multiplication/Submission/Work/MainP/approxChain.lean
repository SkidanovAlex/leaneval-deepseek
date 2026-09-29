import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic
import Submission.Work.Transform.eps_mul

/-!
# `Work.MainP.approxChain`: error propagation of the Prop 5.3 pipeline

Two forward transforms `U1 ≈ F u`, `U2 ≈ F w`, a pointwise product `C ≈ U1·U2` (Corollary 2.10)
and one inverse transform `B ≈ F*(C)` combine into `B ≈ (1/S)•convC ss u w` with error
`< e1+e2+e3+2` (`S = ss.prod`) — the paper's `ε(w̃₀) < ε(F̃) + ε(F̃) + ε(F̃*) + 2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.MainP

open HvdH

/-- Sup-norm bound from coordinatewise bounds. -/
theorem norm_le_of_coord {ι : Type} [Fintype ι] {f : ι → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, ‖f i‖ ≤ c) : ‖f‖ ≤ c :=
  have h2 : @norm (ι → ℂ) Pi.seminormedAddGroup.toNorm f ≤ c :=
    (pi_norm_le_iff_of_nonneg hc).mpr h
  h2

/-- A fixed-point vector all of whose entries are in the disc has sup norm `≤ 1`. -/
theorem norm_fxVec_le (p : ℕ) {n : ℕ} {zs : List (ℤ × ℤ)} (h : HvdH.InDiscVec p n zs) :
    ‖HvdH.fxVec p n zs‖ ≤ 1 := by
  refine norm_le_of_coord zero_le_one (fun i => ?_)
  have hi : (i : ℕ) < zs.length := by rw [h.1]; exact i.isLt
  show ‖HvdH.fxC p (zs.getD (i : ℕ) (0, 0))‖ ≤ 1
  exact Work.ConvR.norm_fxC_le_one (h.2 _ (by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi))

theorem approxChain (hDFT : HvdH.DFTMathProp) (p : ℕ) (ss : List ℕ) (hpos : ∀ t ∈ ss, 0 < t)
    (us ws U1 U2 C B : List (ℤ × ℤ)) (e1 e2 e3 : ℝ)
    (hus : HvdH.InDiscVec p ss.prod us) (hws : HvdH.InDiscVec p ss.prod ws)
    (hU1 : HvdH.Approx p U1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us)) e1)
    (hU2 : HvdH.Approx p U2 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)) e2)
    (hC : HvdH.InDiscVec p ss.prod C)
    (hCM : ∀ i : Fin ss.prod, (2 : ℝ) ^ p * ‖HvdH.fxC p (C.getD i (0,0)) -
        HvdH.fxC p (U1.getD i (0,0)) * HvdH.fxC p (U2.getD i (0,0))‖ < 2)
    (hB : HvdH.Approx p B (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) e3) :
    HvdH.Approx p B ((1 / (ss.prod : ℂ)) • HvdH.convC ss (HvdH.fxVec p ss.prod us)
      (HvdH.fxVec p ss.prod ws)) (e1 + e2 + e3 + 2) := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hDFT ss hpos
  have hSpos : 0 < ss.prod := List.prod_pos hpos
  have hSne : (ss.prod : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hSpos)
  obtain ⟨hBdisc, hBerr⟩ := hB
  have hU1n : ‖HvdH.fxVec p ss.prod U1‖ ≤ 1 := norm_fxVec_le p hU1.1
  have hU2n : ‖HvdH.fxVec p ss.prod U2‖ ≤ 1 := norm_fxVec_le p hU2.1
  have hUn : ‖HvdH.fxVec p ss.prod us‖ ≤ 1 := norm_fxVec_le p hus
  have hWn : ‖HvdH.fxVec p ss.prod ws‖ ≤ 1 := norm_fxVec_le p hws
  have hFun : ‖HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us)‖ ≤ 1 := le_trans (hd1 (-1) _) hUn
  have hFwn : ‖HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)‖ ≤ 1 := le_trans (hd1 (-1) _) hWn
  -- Corollary 2.10
  have heps : ∀ i : Fin ss.prod, (2 : ℝ) ^ p *
      ‖HvdH.fxVec p ss.prod C i - HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) i *
        HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws) i‖ < e1 + e2 + 2 :=
    Work.Transform.eps_mul (HvdH.fxVec p ss.prod U1) (HvdH.fxVec p ss.prod U2)
      (HvdH.fxVec p ss.prod C)
      (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us))
      (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)) e1 e2
      (fun i => le_trans (norm_le_pi_norm _ i) hU2n)
      (fun i => le_trans (norm_le_pi_norm _ i) hFun)
      hU1.2 hU2.2 hCM
  refine ⟨hBdisc, fun i => ?_⟩
  have hconv := hd4 (HvdH.fxVec p ss.prod us) (HvdH.fxVec p ss.prod ws)
  have hsmul : ((1 / (ss.prod : ℂ)) • HvdH.convC ss (HvdH.fxVec p ss.prod us)
        (HvdH.fxVec p ss.prod ws))
      = HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
          HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)) := by
    rw [hconv, smul_smul, one_div, inv_mul_cancel₀ hSne, one_smul]
  rw [hsmul]
  have h1 : (2 : ℝ) ^ p * ‖HvdH.fxC p (B.getD i (0,0)) -
      (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i‖ < e3 := hBerr i
  have hlin : HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C) -
      HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
        HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))
      = HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C -
        HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
          HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)) := by
    set Y : Fin ss.prod → ℂ := HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
      HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)
    have h := hd2 1 (1 : ℂ) (HvdH.fxVec p ss.prod C - Y) Y
    have hL : (1 : ℂ) • (HvdH.fxVec p ss.prod C - Y) + Y = HvdH.fxVec p ss.prod C := by
      funext j; simp
    rw [hL, one_smul] at h
    rw [h]
    simp
  have h2 : (2 : ℝ) ^ p * ‖(HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i -
      (HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
        HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i‖ ≤ e1 + e2 + 2 := by
    have hsub : (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i -
        (HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
          HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i
        = (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C) -
          HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i := rfl
    rw [hsub, hlin]
    have hb : ‖HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C -
        HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
          HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))‖ ≤
        ‖HvdH.fxVec p ss.prod C - HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
          HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)‖ := hd1 1 _
    have hc : ‖HvdH.fxVec p ss.prod C - HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
        HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)‖ ≤ (e1 + e2 + 2) / (2 : ℝ) ^ p := by
      have hSne : 0 < ss.prod := List.prod_pos hpos
      have hpos1 : 0 < e1 := by
        have h := hU1.2 (⟨0, hSne⟩ : Fin ss.prod)
        have h0 : (0:ℝ) ≤ (2:ℝ)^p * ‖HvdH.fxVec p ss.prod U1 ⟨0, hSne⟩ -
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) ⟨0, hSne⟩‖ := by positivity
        exact lt_of_le_of_lt h0 h
      have hpos2 : 0 < e2 := by
        have h := hU2.2 (⟨0, hSne⟩ : Fin ss.prod)
        have h0 : (0:ℝ) ≤ (2:ℝ)^p * ‖HvdH.fxVec p ss.prod U2 ⟨0, hSne⟩ -
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws) ⟨0, hSne⟩‖ := by positivity
        exact lt_of_le_of_lt h0 h
      refine norm_le_of_coord (c := (e1 + e2 + 2) / (2 : ℝ) ^ p)
        (le_of_lt (div_pos (by linarith) (by positivity))) (fun j => ?_)
      have hj := heps j
      rw [Pi.sub_apply, Pi.mul_apply]
      refine le_of_lt ?_
      rw [lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ p)]
      calc ‖HvdH.fxVec p ss.prod C j - HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) j *
              HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws) j‖ * (2 : ℝ) ^ p
          = (2 : ℝ) ^ p * ‖HvdH.fxVec p ss.prod C j -
              HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) j *
                HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws) j‖ := by ring
        _ < e1 + e2 + 2 := hj
    calc (2 : ℝ) ^ p * ‖(HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C -
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
              HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i‖
        ≤ (2 : ℝ) ^ p * ‖HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C -
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
              HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))‖ :=
          mul_le_mul_of_nonneg_left (norm_le_pi_norm _ i) (by positivity)
      _ ≤ (2 : ℝ) ^ p * ‖HvdH.fxVec p ss.prod C - HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws)‖ :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (2 : ℝ) ^ p * ((e1 + e2 + 2) / (2 : ℝ) ^ p) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = e1 + e2 + 2 := by field_simp
  have htr : ‖HvdH.fxC p (B.getD i (0,0)) - (HvdH.dftMulti ss 1
        (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
          HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i‖
      ≤ ‖HvdH.fxC p (B.getD i (0,0)) - (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i‖ +
        ‖(HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i -
          (HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i‖ := by
    have he : HvdH.fxC p (B.getD i (0,0)) - (HvdH.dftMulti ss 1
          (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i
        = (HvdH.fxC p (B.getD i (0,0)) - (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i) +
          ((HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i -
            (HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
              HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i) := by ring
    rw [he]
    exact norm_add_le _ _
  calc (2 : ℝ) ^ p * ‖HvdH.fxC p (B.getD i (0,0)) - (HvdH.dftMulti ss 1
          (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
            HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i‖
      ≤ (2 : ℝ) ^ p * (‖HvdH.fxC p (B.getD i (0,0)) - (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i‖ +
          ‖(HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i -
            (HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
              HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i‖) :=
        mul_le_mul_of_nonneg_left htr (by positivity)
    _ = (2 : ℝ) ^ p * ‖HvdH.fxC p (B.getD i (0,0)) - (HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i‖ +
          (2 : ℝ) ^ p * ‖(HvdH.dftMulti ss 1 (HvdH.fxVec p ss.prod C)) i -
            (HvdH.dftMulti ss 1 (HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod us) *
              HvdH.dftMulti ss (-1) (HvdH.fxVec p ss.prod ws))) i‖ := by ring
    _ < e3 + (e1 + e2 + 2) := by linarith [h1, h2]
    _ = e1 + e2 + e3 + 2 := by ring

end Work.MainP
