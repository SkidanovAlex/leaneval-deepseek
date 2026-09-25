import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Core.Lev.sharpCut_fderiv_bounds
import Submission.Work.NN.Core.Lev.finset_prod_fderiv_bounds
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_norm_le_holderNorm
import Submission.Work.NN.Newton.FTedat.holderNorm_zero_le_of_sup_lip
import Submission.Work.NN.Newton.FTedat.fderiv_slice_bounds

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton.FTedat

/-- `∂̄_j u` is bounded by the operator norm of the real derivative of `u`. -/
private lemma norm_dbarCoord_le {n : ℕ} (a : Fin n) (u : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) :
    ‖Work.CR.Flat.dbarCoord a u x‖ ≤ ‖fderiv ℝ u x‖ := by
  simp only [Work.CR.Flat.dbarCoord]
  exact Work.CR.Flat.Polydisc.norm_dbarCombination_le a (fderiv ℝ u x)

/-- The difference of `∂̄_j` at two points is bounded by the operator norm of the difference of
the real derivatives. -/
private lemma norm_dbarCoord_sub_le {n : ℕ} (a : Fin n) (u : (Fin n → ℂ) → ℂ)
    (x y : Fin n → ℂ) :
    ‖Work.CR.Flat.dbarCoord a u x - Work.CR.Flat.dbarCoord a u y‖
      ≤ ‖fderiv ℝ u x - fderiv ℝ u y‖ := by
  have hdiff : Work.CR.Flat.dbarCoord a u x - Work.CR.Flat.dbarCoord a u y
      = (1 / 2 : ℂ) * ((fderiv ℝ u x - fderiv ℝ u y) (Pi.single a 1)
          + Complex.I * ((fderiv ℝ u x - fderiv ℝ u y) (Pi.single a Complex.I))) := by
    simp only [Work.CR.Flat.dbarCoord, sub_apply]
    ring
  rw [hdiff]
  exact Work.CR.Flat.Polydisc.norm_dbarCombination_le a (fderiv ℝ u x - fderiv ℝ u y)

theorem ftCut_dbar_bound {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (δ : ℝ), 0 < δ → δ ≤ 1 / 4 → ∀ (a : Fin n),
      Work.CR.Flat.holderNorm 0 α
        (fun w => Work.CR.Flat.dbarCoord a
          (Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8)) w)
        Set.univ
      ≤ ENNReal.ofReal (K / δ ^ N) := by
  obtain ⟨C, hCpos, hC⟩ := Work.NN.Core.Lev.sharpCut_fderiv_bounds
  refine ⟨64 * (n : ℝ) ^ 2 * C ^ 2 + 104 * (n : ℝ) * C + 1, by positivity, 2, ?_⟩
  intro δ hδ0 hδ4 a
  set A : ℝ := 1 - 3 * δ / 4 with hA
  set B : ℝ := 1 - 5 * δ / 8 with hB
  have hδ1 : δ ≤ 1 := by linarith
  have hδ2pos : 0 < δ ^ 2 := pow_pos hδ0 2
  have hC0 : 0 ≤ C := hCpos.le
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hprod : (0 : ℝ) ≤ (n : ℝ) * C := mul_nonneg hn0 hC0
  have hA0 : 0 < A := by rw [hA]; linarith
  have hAB : A < B := by rw [hA, hB]; linarith
  obtain ⟨hd1, hd2, hd3⟩ := hC A B hA0 hAB
  set φ : ℂ → ℂ := Work.NN.Core.sharpCut A B with hφ
  have hφdiff : Differentiable ℝ φ := by
    rw [hφ]
    exact (Work.NN.Core.contDiff_sharpCut (a := A) (b := B)).differentiable (by simp)
  have hφ1 : ∀ ζ : ℂ, ‖φ ζ‖ ≤ 1 := by
    intro ζ; rw [hφ]; exact Work.NN.Core.norm_sharpCut_le_one A B ζ
  set c1 : ℝ := C * (1 / (B - A)) with hc1
  set c2 : ℝ := C * (1 / (A * (B - A)) + 1 / (B - A) ^ 2) with hc2
  have hc1nn : 0 ≤ c1 := by rw [hc1]; positivity
  have hc2nn : 0 ≤ c2 := by rw [hc2]; positivity
  -- slice bounds inherited from the one-variable bounds for `φ`
  have hslice := fderiv_slice_bounds (n := n) (φ := φ) hφdiff (M := c1) (L := c1) (Md := c2)
    hd1 hd2 hd3
  obtain ⟨hsliceM, hsliceL, hsliceMd⟩ := hslice
  have hsum1 : (∑ _j : Fin n, c1) = (n : ℝ) * c1 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum2 : (∑ _j : Fin n, c2) = (n : ℝ) * c2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- sup bound for the `∂̄` of the product cutoff
  have hsup : ∀ w : Fin n → ℂ,
      ‖Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => ∏ j, φ (z j)) w‖ ≤ (n : ℝ) * c1 := by
    intro w
    have hfd : ‖fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) w‖ ≤ (n : ℝ) * c1 := by
      have h := Work.NN.Core.Lev.fderiv_finset_prod_norm_le
        (u := fun (j : Fin n) (z : Fin n → ℂ) => φ (z j)) w
        (M := fun _ : Fin n => c1)
        (fun j => hφdiff.differentiableAt.comp w
          (ContinuousLinearMap.differentiableAt
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)))
        (fun j => hsliceM j w)
        (fun j => hφ1 (w j))
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
    calc ‖Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => ∏ j, φ (z j)) w‖
        ≤ ‖fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) w‖ := norm_dbarCoord_le a _ w
      _ ≤ (n : ℝ) * c1 := hfd
  -- Lipschitz bound for the `∂̄` of the product cutoff
  have hlip : ∀ x y : Fin n → ℂ,
      ‖Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => ∏ j, φ (z j)) x
        - Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => ∏ j, φ (z j)) y‖
      ≤ ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) * ‖x - y‖ := by
    intro x y
    have hfd : ‖fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) x
        - fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) y‖
        ≤ ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) * ‖x - y‖ := by
      have h := Work.NN.Core.Lev.fderiv_finset_prod_sub_le
        (u := fun (j : Fin n) (z : Fin n → ℂ) => φ (z j)) x y
        (L := fun _ : Fin n => c1) (M := fun _ : Fin n => c1) (Md := fun _ : Fin n => c2)
        (fun j => hφdiff.differentiableAt.comp x
          (ContinuousLinearMap.differentiableAt
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)))
        (fun j => hφdiff.differentiableAt.comp y
          (ContinuousLinearMap.differentiableAt
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j)))
        (fun _ => hc1nn) (fun _ => hc1nn) (fun _ => hc2nn)
        (fun j => hsliceM j x) (fun j => hsliceL j x y) (fun j => hsliceMd j x y)
        (fun j => hφ1 (x j)) (fun j => hφ1 (y j))
      have hb : ‖fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) x
          - fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) y‖
          ≤ (((n : ℝ) * c1) * ((n : ℝ) * c1) + (n : ℝ) * c2) * ‖x - y‖ := by
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
      calc ‖fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) x
            - fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) y‖
          ≤ (((n : ℝ) * c1) * ((n : ℝ) * c1) + (n : ℝ) * c2) * ‖x - y‖ := hb
        _ = ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) * ‖x - y‖ := by ring
    calc ‖Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => ∏ j, φ (z j)) x
          - Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => ∏ j, φ (z j)) y‖
        ≤ ‖fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) x
            - fderiv ℝ (fun z : Fin n → ℂ => ∏ j, φ (z j)) y‖ := norm_dbarCoord_sub_le a _ x y
      _ ≤ ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) * ‖x - y‖ := hfd
  have hM0 : (0 : ℝ) ≤ (n : ℝ) * c1 := mul_nonneg hn0 hc1nn
  have hL0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2 :=
    add_nonneg (by positivity) (mul_nonneg hn0 hc2nn)
  have hHolder := holderNorm_zero_le_of_sup_lip (g := fun w : Fin n → ℂ =>
      Work.CR.Flat.dbarCoord a (fun z : Fin n → ℂ => ∏ j, φ (z j)) w)
    hα0 hα1 (M := (n : ℝ) * c1) (L := (n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2)
    hM0 hL0 hsup hlip
  -- identify the function with `∂̄ a (ftCut n A B)`
  have hfun : (fun w : Fin n → ℂ => Work.CR.Flat.dbarCoord a
        (Work.NN.Newton.ftCut n A B) w)
      = (fun w : Fin n → ℂ => Work.CR.Flat.dbarCoord a
          (fun z : Fin n → ℂ => ∏ j, φ (z j)) w) := by
    funext w
    rfl
  rw [hfun]
  refine le_trans hHolder (ENNReal.ofReal_le_ofReal ?_)
  -- now the pure arithmetic
  have hBA : B - A = δ / 8 := by rw [hA, hB]; ring
  have hinvBA : 1 / (B - A) = 8 / δ := by rw [hBA]; field_simp
  have hinvBA2 : 1 / (B - A) ^ 2 = 64 / δ ^ 2 := by rw [hBA]; field_simp; norm_num
  have hAge : (1 : ℝ) / 2 ≤ A := by rw [hA]; linarith
  have hA16 : δ / 16 ≤ A * (B - A) := by
    rw [hBA]
    have := mul_le_mul_of_nonneg_right hAge (show (0 : ℝ) ≤ δ / 8 by positivity)
    linarith
  have hinvA : 1 / (A * (B - A)) ≤ 16 / δ := by
    have h16 : (0 : ℝ) < δ / 16 := by positivity
    have h := one_div_le_one_div_of_le h16 hA16
    rwa [show (1 : ℝ) / (δ / 16) = 16 / δ from by field_simp] at h
  have h16 : 16 / δ ≤ 16 / δ ^ 2 := by
    rw [div_le_div_iff₀ hδ0 hδ2pos]
    nlinarith [hδ0, hδ1]
  have hc1val : c1 = 8 * C / δ := by rw [hc1, hinvBA]; field_simp
  have hc2bound : c2 ≤ C * (80 / δ ^ 2) := by
    rw [hc2]
    refine mul_le_mul_of_nonneg_left ?_ hC0
    calc 1 / (A * (B - A)) + 1 / (B - A) ^ 2 ≤ 16 / δ + 64 / δ ^ 2 := by
          rw [hinvBA2]; linarith [hinvA]
      _ ≤ 80 / δ ^ 2 := by
          calc 16 / δ + 64 / δ ^ 2 ≤ 16 / δ ^ 2 + 64 / δ ^ 2 := add_le_add h16 le_rfl
            _ = 80 / δ ^ 2 := by ring
  -- the three key comparisons, cleared of denominators
  have hterm1 : (n : ℝ) * c1 * δ ^ 2 ≤ 8 * (n : ℝ) * C := by
    have he : (n : ℝ) * c1 * δ ^ 2 = 8 * (n : ℝ) * C * δ := by
      rw [hc1val]; field_simp
    rw [he]
    calc 8 * (n : ℝ) * C * δ ≤ 8 * (n : ℝ) * C * 1 :=
          mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = 8 * (n : ℝ) * C := by ring
  have htermA : ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) * δ ^ 2
      ≤ 64 * (n : ℝ) ^ 2 * C ^ 2 + 80 * (n : ℝ) * C := by
    have he1 : (n : ℝ) ^ 2 * c1 ^ 2 * δ ^ 2 = 64 * (n : ℝ) ^ 2 * C ^ 2 := by
      rw [hc1val]; field_simp; ring
    have he2 : (n : ℝ) * c2 * δ ^ 2 ≤ 80 * (n : ℝ) * C := by
      have h1 : c2 * δ ^ 2 ≤ C * 80 := by
        have := mul_le_mul_of_nonneg_right hc2bound hδ2pos.le
        rwa [show C * (80 / δ ^ 2) * δ ^ 2 = C * 80 from by field_simp] at this
      calc (n : ℝ) * c2 * δ ^ 2 = (n : ℝ) * (c2 * δ ^ 2) := by ring
        _ ≤ (n : ℝ) * (C * 80) := mul_le_mul_of_nonneg_left h1 hn0
        _ = 80 * (n : ℝ) * C := by ring
    have hsplit : ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) * δ ^ 2
        = (n : ℝ) ^ 2 * c1 ^ 2 * δ ^ 2 + (n : ℝ) * c2 * δ ^ 2 := by ring
    rw [hsplit, he1]
    linarith [he2]
  have htermB : (2 * ((n : ℝ) * c1)) * δ ^ 2 ≤ 64 * (n : ℝ) ^ 2 * C ^ 2 + 80 * (n : ℝ) * C := by
    have he : (2 * ((n : ℝ) * c1)) * δ ^ 2 = 16 * (n : ℝ) * C * δ := by
      rw [hc1val]; field_simp; ring
    rw [he]
    have hsq : (0 : ℝ) ≤ 64 * (n : ℝ) ^ 2 * C ^ 2 := by positivity
    calc 16 * (n : ℝ) * C * δ ≤ 16 * (n : ℝ) * C * 1 :=
          mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = 16 * (n : ℝ) * C := by ring
      _ ≤ 64 * (n : ℝ) ^ 2 * C ^ 2 + 80 * (n : ℝ) * C := by linarith [hprod, hsq]
  rw [le_div_iff₀ hδ2pos]
  have hmax : max ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) (2 * ((n : ℝ) * c1)) * δ ^ 2
      ≤ 64 * (n : ℝ) ^ 2 * C ^ 2 + 80 * (n : ℝ) * C := by
    rw [max_mul_of_nonneg _ _ hδ2pos.le]
    exact max_le htermA htermB
  rw [add_mul]
  calc (n : ℝ) * c1 * δ ^ 2
        + max ((n : ℝ) ^ 2 * c1 ^ 2 + (n : ℝ) * c2) (2 * ((n : ℝ) * c1)) * δ ^ 2
      ≤ 8 * (n : ℝ) * C + (64 * (n : ℝ) ^ 2 * C ^ 2 + 80 * (n : ℝ) * C) :=
        add_le_add hterm1 hmax
    _ = 64 * (n : ℝ) ^ 2 * C ^ 2 + 88 * (n : ℝ) * C := by ring
    _ ≤ 64 * (n : ℝ) ^ 2 * C ^ 2 + 104 * (n : ℝ) * C + 1 := by nlinarith [hprod]

end Work.NN.Newton.FTedat
