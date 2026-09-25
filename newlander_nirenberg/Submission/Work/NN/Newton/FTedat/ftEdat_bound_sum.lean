import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Newton.FTedat.Edat_gain_expl
import Submission.Work.NN.Newton.FTedat.bmH_norm_le_expl
import Submission.Work.NN.Newton.FTedat.ftCut_dbar_bound

namespace Work.NN.Newton.FTedat

open scoped NNReal ENNReal ContDiff
open Set

/-- The arithmetic of the final constant: for `0 < δ ≤ 1` and `0 ≤ A` the explicit constant
`A * (12 * (Kd / δ^N + 1)) + 1` produced by `Edat_gain_expl` is dominated by
`(A * 12 * (Kd + 1) + 1) / δ^N`. -/
private lemma ftEdat_arith {A Kd δ : ℝ} (N : ℕ) (hA : 0 ≤ A)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    A * (12 * (Kd / δ ^ N + 1)) + 1 ≤ (A * 12 * (Kd + 1) + 1) / δ ^ N := by
  have hδp : 0 < δ ^ N := pow_pos hδ0 N
  rw [le_div_iff₀ hδp]
  have hk : (Kd / δ ^ N) * δ ^ N = Kd := div_mul_cancel₀ Kd (ne_of_gt hδp)
  have hle : δ ^ N ≤ 1 := pow_le_one₀ hδ0.le hδ1
  have hA1 : (0 : ℝ) ≤ A * 12 + 1 := by linarith
  nlinarith [hk, mul_le_mul_of_nonneg_left hle hA1]

private lemma ennreal_natCast_mul_self (n : ℕ) :
    (n : ℝ≥0∞) * (n : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) ^ 2) := by
  rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  congr 1
  ring

theorem ftEdat_bound_sum {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ, ∀ (δ : ℝ) (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4)
      (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ 1 (η i l) (Work.CR.Flat.polydisc 0 (fun _ => 1))) →
      ∀ (T : ℝ), 1 / 2 ≤ T → T ≤ 1 →
      (∑ a : Fin n, ∑ b : Fin n,
          Work.CR.Flat.holderNorm 1 α (Work.NN.Newton.ftEdat n δ η a b)
            (Work.CR.Flat.polydisc 0 (fun _ => T)))
        ≤ ENNReal.ofReal (K / δ ^ N) * ∑ a : Fin n, ∑ b : Fin n,
            Work.CR.Flat.holderNorm 0 α (η a b) (Work.CR.Flat.polydisc 0 (fun _ => 1)) := by
  -- the quantitative `C^{0,α} → C^{1,α}` Bochner–Martinelli gain for the unit polydisc
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.NN.Core.bmPotential_gain (n := n) hn hα0 hα1
    (ρ := fun _ : Fin n => (1 : ℝ)) (fun _ => one_pos) 0
  -- the `∂̄`-bound for the product cutoff
  obtain ⟨Kd, hKdpos, Nd, hcut⟩ := ftCut_dbar_bound (n := n) hα0 hα1
  set A : ℝ := ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * (n : ℝ) with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  set K : ℝ := (n : ℝ) ^ 2 * (A * 12 * (Kd + 1) + 1) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hp : (0 : ℝ) < A * 12 * (Kd + 1) + 1 := by nlinarith [hA0, hKdpos]
    exact mul_pos (pow_pos hn0 2) hp
  refine ⟨K, hKpos, Nd, ?_⟩
  intro δ hδ0 hδ4 η hη T hT12 hT1
  have hδ01 : δ ≤ 1 := by linarith
  have hApos : (0 : ℝ) ≤ 1 - 3 * δ / 4 := by linarith
  have hAB : 1 - 3 * δ / 4 < 1 - 5 * δ / 8 := by linarith
  have hrR : ∀ j : Fin n, 1 - 5 * δ / 16 < (1 : ℝ) := fun _ => by linarith
  have hTR : ∀ j : Fin n, T ≤ (1 : ℝ) := fun _ => hT1
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8)) :=
    Work.NN.Newton.contDiff_ftCut _ _
  have hcs : HasCompactSupport (Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8)) :=
    Work.NN.Newton.hasCompactSupport_ftCut hApos hAB
  have htsupp : tsupport (Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8))
      ⊆ Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1 - 5 * δ / 16) := by
    refine (Work.NN.Newton.tsupport_ftCut hApos hAB).trans (fun z hz j => ?_)
    have h1 : ‖z j‖ ≤ 1 - 5 * δ / 8 := by simpa using hz j
    simpa using (by linarith : ‖z j‖ < 1 - 5 * δ / 16)
  have hNχpos : (0 : ℝ) < Kd / δ ^ Nd := div_pos hKdpos (pow_pos hδ0 Nd)
  have hχbar : ∀ a : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun w => Work.CR.Flat.dbarCoord a
        (Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8)) w)
      Set.univ ≤ ENNReal.ofReal (Kd / δ ^ Nd) := fun a => hcut δ hδ0 hδ4 a
  -- the `bmH`-bound feeding `Edat_gain_expl`
  have hbmH : ∀ (η : Fin n → Fin n → (Fin n → ℂ) → ℂ),
      (∀ i l, ContDiffOn ℝ (1 : ℕ∞) (η i l) (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1))) →
      ∀ j l i : Fin n,
      Work.CR.Flat.holderNorm 0 α (fun w => Work.NN.Core.bmH
          (Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8)) η j l i w) Set.univ
        ≤ ENNReal.ofReal (12 * (Kd / δ ^ Nd + 1)) * ∑ a : Fin n, ∑ b : Fin n,
            Work.CR.Flat.holderNorm 0 α (η a b)
              (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1)) := by
    intro η hη j l i
    exact bmH_norm_le_expl hα0.le hα1.le (r := fun _ : Fin n => 1 - 5 * δ / 16)
      (R := fun _ : Fin n => 1) hrR hχ hcs htsupp hNχpos hχbar η
      (fun i l => (hη i l).of_le (by simp)) j l i
  -- the `C^{0,α} → C^{1,α}` gain for `bmPot` on the unit polydisc
  have hCg' : ∀ g : Fin n → (Fin n → ℂ) → ℂ,
      (∀ j, ContDiff ℝ 1 (g j)) → (∀ j, HasCompactSupport (g j)) →
      (∀ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ < ⊤) →
      (∀ j z, (∃ i : Fin n, (1 : ℝ) ≤ ‖z i‖) → g j z = 0) →
      ContDiffOn ℝ (1 : ℕ∞) (Work.CR.Flat.Cauchy.bmPot g)
          (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1)) ∧
      Work.CR.Flat.holderNorm 1 α (Work.CR.Flat.Cauchy.bmPot g)
          (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1))
        ≤ ENNReal.ofReal Cg * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α (g j) Set.univ := by
    intro g hg hgcs hgfin hgvan
    obtain ⟨hcont, hbound⟩ := hCg g (fun j => (hg j).of_le (by simp)) hgcs hgfin hgvan
    have hfun : Work.CR.Flat.Cauchy.bmPot g = Work.CR.Flat.Cauchy.bmPotential g :=
      funext fun z => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot g z).symm
    exact ⟨by rw [hfun]; exact hcont, by rw [hfun]; exact hbound⟩
  -- the per-`(j,l)` estimate
  have hterm : ∀ j l : Fin n,
      Work.CR.Flat.holderNorm 1 α (Work.NN.Newton.ftEdat n δ η j l)
          (Work.CR.Flat.polydisc 0 (fun _ : Fin n => T))
        ≤ ENNReal.ofReal (A * (12 * (Kd / δ ^ Nd + 1)) + 1)
          * (∑ a : Fin n, ∑ b : Fin n, Work.CR.Flat.holderNorm 0 α (η a b)
              (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1))) := by
    intro j l
    have hCh : (0 : ℝ) < 12 * (Kd / δ ^ Nd + 1) := by
      have hk : (0 : ℝ) < Kd / δ ^ Nd := div_pos hKdpos (pow_pos hδ0 Nd)
      linarith
    have hEdat := Edat_gain_expl (n := n) hn hα0 hα1
      (r := fun _ : Fin n => 1 - 5 * δ / 16) (R := fun _ : Fin n => 1)
      (T := fun _ : Fin n => T) (fun _ => one_pos) hrR hTR
      (χ := Work.NN.Newton.ftCut n (1 - 3 * δ / 4) (1 - 5 * δ / 8)) hχ hcs htsupp
      (Ch := 12 * (Kd / δ ^ Nd + 1)) (Cg := Cg) hCh hCgpos hbmH hCg' η hη j l
    have hconst : ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg
          * ((n : ℝ) * (12 * (Kd / δ ^ Nd + 1))) + 1
        = A * (12 * (Kd / δ ^ Nd + 1)) + 1 := by rw [hAdef]; ring
    rw [hconst] at hEdat
    exact hEdat
  -- summation
  have hsum1 : (∑ a : Fin n, ∑ b : Fin n,
        Work.CR.Flat.holderNorm 1 α (Work.NN.Newton.ftEdat n δ η a b)
          (Work.CR.Flat.polydisc 0 (fun _ : Fin n => T)))
      ≤ ∑ a : Fin n, ∑ b : Fin n,
          ENNReal.ofReal (A * (12 * (Kd / δ ^ Nd + 1)) + 1)
            * (∑ a : Fin n, ∑ b : Fin n, Work.CR.Flat.holderNorm 0 α (η a b)
                (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1))) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
  have hsum2 : (∑ a : Fin n, ∑ b : Fin n,
        ENNReal.ofReal (A * (12 * (Kd / δ ^ Nd + 1)) + 1)
          * (∑ a : Fin n, ∑ b : Fin n, Work.CR.Flat.holderNorm 0 α (η a b)
              (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1))))
      = ENNReal.ofReal ((n : ℝ) ^ 2 * (A * (12 * (Kd / δ ^ Nd + 1)) + 1))
        * (∑ a : Fin n, ∑ b : Fin n, Work.CR.Flat.holderNorm 0 α (η a b)
            (Work.CR.Flat.polydisc 0 (fun _ : Fin n => 1))) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
    rw [← mul_assoc, ennreal_natCast_mul_self, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ ((n : ℝ)) ^ 2)]
  refine hsum1.trans ?_
  rw [hsum2]
  refine mul_le_mul_left ?_ _
  refine ENNReal.ofReal_le_ofReal ?_
  have har := ftEdat_arith (A := A) (Kd := Kd) (δ := δ) Nd hA0 hδ0 hδ01
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  calc (n : ℝ) ^ 2 * (A * (12 * (Kd / δ ^ Nd + 1)) + 1)
      ≤ (n : ℝ) ^ 2 * ((A * 12 * (Kd + 1) + 1) / δ ^ Nd) :=
        mul_le_mul_of_nonneg_left har hn2
    _ = K / δ ^ Nd := by rw [hKdef]; ring

end Work.NN.Newton.FTedat
