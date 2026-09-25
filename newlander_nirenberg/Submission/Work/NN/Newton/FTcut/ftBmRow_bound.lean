import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Core.Lev.sharpCut_fderiv_bounds
import Submission.Work.NN.Core.Lev.finset_prod_fderiv_bounds
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.NN.Newton.FTcut.ftCut_lipschitz
import Submission.Work.NN.Newton.FTcut.holderNorm_zero_mul_le_of_lipschitz
import Submission.Work.NN.Newton.FTcut.contDiff_ftCut_mul

namespace Work.NN.Newton.FTcut

theorem ftBmRow_bound {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) → ∀ j : Fin n,
      Work.CR.Flat.holderNorm 1 α
          (Work.NN.Core.bmRow (fun a b w =>
            Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) w * η a b w) j)
          (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))
        ≤ ENNReal.ofReal (K / δ ^ N) * ∑ a : Fin n, ∑ b : Fin n,
            Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 (fun _ => 1)) := by
  obtain ⟨Cbm, hCbm0, hCbm⟩ := Work.NN.Core.bmRow_holder (n := n) hn (α := α) hα0 hα1
      (c := (0 : Fin n → ℂ)) (r := fun _ : Fin n => (2:ℝ)) (fun _ => by norm_num) 0
  obtain ⟨Clip, hClip0, hlip⟩ := ftCut_lipschitz (n := n)
  refine ⟨Cbm * (8 * Clip + 3) + 1, ?_, 1, ?_⟩
  · have h1 : (0:ℝ) < 8 * Clip + 3 := by linarith
    exact lt_of_lt_of_le (mul_pos hCbm0 h1) (le_add_of_nonneg_right zero_le_one)
  · intro δ hδ0 hδ4 η hη j
    have ha : (0:ℝ) < 1 - 3 * δ / 4 := by linarith
    have hab : (1:ℝ) - 3 * δ / 4 < 1 - 5 * δ / 8 := by linarith
    have hb1 : (1:ℝ) - 5 * δ / 8 < 1 := by linarith
    set G : Fin n → Fin n → (Fin n → ℂ) → ℂ :=
      fun a b w => ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) w * η a b w with hGdef
    have hG_cont : ∀ a b, ContDiff ℝ 1 (G a b) := fun a b =>
      contDiff_ftCut_mul (a := 1 - 3 * δ / 4) (b := 1 - 5 * δ / 8) ha.le hab hb1 (hη a b)
    have hG_supp : ∀ a b z, (∃ i, (fun _ : Fin n => (2:ℝ)) i / 2 ≤ ‖z i - (0 : Fin n → ℂ) i‖) →
        G a b z = 0 := by
      intro a b z hz
      obtain ⟨i, hi⟩ := hz
      have h1 : (1:ℝ) ≤ ‖z i‖ := by
        have h3 : (fun _ : Fin n => (2:ℝ)) i / 2 = 1 := by norm_num
        have h4 : ‖z i - (0 : Fin n → ℂ) i‖ = ‖z i‖ := by simp
        rw [h3, h4] at hi
        exact hi
      have hzi : (1:ℝ) - 5 * δ / 8 ≤ ‖z i‖ := le_of_lt (lt_of_lt_of_le hb1 h1)
      have hz0 : ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) z = 0 :=
        ftCut_eq_zero ha.le hab hzi
      show ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) z * η a b z = 0
      rw [hz0, zero_mul]
    have hbm := hCbm G hG_cont hG_supp j
    have hpd : (2:ℝ) / 2 = 1 := by norm_num
    have hbm1 : Work.CR.Flat.holderNorm 1 α (Work.NN.Core.bmRow G j)
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => (1:ℝ))) ≤
        ENNReal.ofReal Cbm * ∑ l : Fin n, ∑ m : Fin n,
          Work.CR.Flat.holderNorm 0 α (G l m) Set.univ := by
      simpa only [hpd] using hbm
    have hmono : Work.CR.Flat.holderNorm 1 α (Work.NN.Core.bmRow G j)
        (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1 - δ))
        ≤ Work.CR.Flat.holderNorm 1 α (Work.NN.Core.bmRow G j)
          (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => (1:ℝ))) := by
      refine Work.CR.Flat.holderNorm_mono_set (Work.CR.Flat.isOpen_polydisc _ _)
        (Work.CR.Flat.isOpen_polydisc _ _) ?_ 1 α _
      intro z hz
      rw [Work.CR.Flat.mem_polydisc] at hz ⊢
      intro i
      have hi := hz i
      simp only [Pi.zero_apply] at hi ⊢
      linarith
    have hterm : ∀ l m : Fin n,
        Work.CR.Flat.holderNorm 0 α (G l m) Set.univ
          ≤ ENNReal.ofReal ((8 * Clip + 3) / δ)
              * Work.CR.Flat.holderNorm 0 α (η l m)
                  (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
      intro l m
      have hvan : Work.CR.Flat.holderNorm 0 α (G l m) Set.univ
          ≤ Work.CR.Flat.holderNorm 0 α (G l m)
              (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
        refine Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
          (c := (0 : Fin n → ℂ)) (r := fun _ : Fin n => 1 - 5 * δ / 8)
          (r' := fun _ : Fin n => 1) (k := 0) (α := α) (fun _ => hb1) hα0.le ?_
        intro z hz
        obtain ⟨i, hi⟩ := hz
        have hz0 : ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) z = 0 :=
          ftCut_eq_zero ha.le hab (by simpa using hi)
        show ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) z * η l m z = 0
        rw [hz0, zero_mul]
      have hmul := holderNorm_zero_mul_le_of_lipschitz (X := Fin n → ℂ) (α := α)
        (L := Clip * (1 / ((1 - 5 * δ / 8) - (1 - 3 * δ / 4)))) hα0 hα1.le (by positivity)
        (χ := fun w => ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8) w)
        (u := η l m) (Ω := Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1))
        (fun z => norm_ftCut_le_one (1 - 3 * δ / 4) (1 - 5 * δ / 8) z)
        (fun x y => hlip (1 - 3 * δ / 4) (1 - 5 * δ / 8) ha hab x y)
      refine hvan.trans (hmul.trans ?_)
      refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
      have hba : (1 - 5 * δ / 8) - (1 - 3 * δ / 4) = δ / 8 := by ring
      have hL : Clip * (1 / ((1 - 5 * δ / 8) - (1 - 3 * δ / 4))) + 3
          ≤ (8 * Clip + 3) / δ := by
        rw [hba, one_div, inv_div]
        have h3 : (3:ℝ) ≤ 3 / δ := by
          rw [le_div_iff₀ hδ0]; linarith
        calc Clip * (8 / δ) + 3 ≤ Clip * (8 / δ) + 3 / δ := by linarith
          _ = (8 * Clip + 3) / δ := by ring
      exact hL
    have hS : (∑ l : Fin n, ∑ m : Fin n, Work.CR.Flat.holderNorm 0 α (G l m) Set.univ)
        ≤ ENNReal.ofReal ((8 * Clip + 3) / δ)
          * ∑ l : Fin n, ∑ m : Fin n,
              Work.CR.Flat.holderNorm 0 α (η l m)
                (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
      calc ∑ l : Fin n, ∑ m : Fin n, Work.CR.Flat.holderNorm 0 α (G l m) Set.univ
          ≤ ∑ l : Fin n, ∑ m : Fin n, ENNReal.ofReal ((8 * Clip + 3) / δ)
              * Work.CR.Flat.holderNorm 0 α (η l m)
                  (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) :=
            Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun m _ => hterm l m))
        _ = ENNReal.ofReal ((8 * Clip + 3) / δ)
              * ∑ l : Fin n, ∑ m : Fin n,
                  Work.CR.Flat.holderNorm 0 α (η l m)
                    (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun l _ => by rw [Finset.mul_sum])
    refine le_trans hmono (le_trans hbm1 ?_)
    calc ENNReal.ofReal Cbm * ∑ l : Fin n, ∑ m : Fin n,
            Work.CR.Flat.holderNorm 0 α (G l m) Set.univ
        ≤ ENNReal.ofReal Cbm * (ENNReal.ofReal ((8 * Clip + 3) / δ)
            * ∑ l : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 0 α (η l m)
                  (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1))) :=
          mul_le_mul_right hS _
      _ = ENNReal.ofReal (Cbm * ((8 * Clip + 3) / δ))
            * ∑ l : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 0 α (η l m)
                  (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hCbm0)]
      _ = ENNReal.ofReal (Cbm * (8 * Clip + 3) / δ)
            * ∑ l : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 0 α (η l m)
                  (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
          rw [mul_div_assoc]
      _ ≤ ENNReal.ofReal ((Cbm * (8 * Clip + 3) + 1) / δ)
            * ∑ l : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 0 α (η l m)
                  (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
          refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
          exact div_le_div_of_nonneg_right (by linarith) hδ0.le
      _ = ENNReal.ofReal ((Cbm * (8 * Clip + 3) + 1) / δ ^ 1)
            * ∑ l : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 0 α (η l m)
                  (Work.CR.Flat.polydisc (0 : Fin n → ℂ) (fun _ => 1)) := by
          rw [pow_one]

end Work.NN.Newton.FTcut
