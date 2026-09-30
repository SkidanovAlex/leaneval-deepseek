import Mathlib
import Submission.Work.BW.Minkowski2.centroidDefs
import Submission.Work.BW.Minkowski2.shear_volume
import Submission.Work.BW.Minkowski2.shear_volume_measurable
import Submission.Work.BW.Minkowski2.diag_telescope
import Submission.Work.BW.Minkowski2.offDiag_meas_dep
import Submission.Work.BW.Minkowski2.prod_Iic_succ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

private lemma prod_le_zero {n : ℕ} {M : Type*} [CommMonoid M] (f : Fin (n+1) → M) :
    (∏ j : Fin (n+1), (if j ≤ (0 : Fin (n+1)) then f j else 1)) = f 0 := by
  refine Finset.prod_eq_single (0 : Fin (n+1)) ?_ ?_
  · intro b _ hb
    exact if_neg (fun hle => hb (Fin.ext (by simpa using hle)))
  · intro h; exact absurd (Finset.mem_univ (0 : Fin (n+1))) h

private lemma prod_le_last {n : ℕ} {M : Type*} [CommMonoid M] (f : Fin (n+1) → M) :
    (∏ j : Fin (n+1), (if j ≤ Fin.last n then f j else 1)) = ∏ j, f j := by
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [if_pos (Fin.le_last j)]

private theorem triangular_map_volume {d : ℕ} (Φ : (Fin d → ℝ) → (Fin d → ℝ))
    (cc : Fin d → ℝ) (hcc : ∀ i, 0 < cc i)
    (g : Fin d → (Fin d → ℝ) → ℝ) (hgmeas : ∀ i, Measurable (g i))
    (hgdep : ∀ (i : Fin d) (x y : Fin d → ℝ), (∀ m : Fin d, i < m → x m = y m) → g i x = g i y)
    (hΦ : ∀ (x : Fin d → ℝ) (m : Fin d), Φ x m = cc m * x m + g m x)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    MeasureTheory.volume (Φ '' A) = (∏ i : Fin d, ENNReal.ofReal (cc i)) * MeasureTheory.volume A
      ∧ MeasurableSet (Φ '' A) := by
  classical
  rcases d with _ | n
  · have hΦid : Φ = id := funext (fun x => Subsingleton.elim (Φ x) x)
    have himg : Φ '' A = A := by rw [hΦid]; exact Set.image_id A
    rw [himg]
    exact ⟨by simp, hA⟩
  · let T : Fin (n+1) → (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) :=
      fun m x => Function.update x m (cc m * x m + g m x)
    let Φp : Fin (n+1) → (Fin (n+1) → ℝ) → (Fin (n+1) → ℝ) :=
      fun m x j => if j ≤ m then Φ x j else x j
    let PK : Fin (n+1) → ENNReal :=
      fun m => ∏ j : Fin (n+1), (if j ≤ m then ENNReal.ofReal (cc j) else 1)
    have hΦp : ∀ (m : Fin (n+1)) (x : Fin (n+1) → ℝ) (j : Fin (n+1)),
        Φp m x j = if j ≤ m then Φ x j else x j := fun m x j => rfl
    have hT : ∀ (m : Fin (n+1)) (x : Fin (n+1) → ℝ),
        T m x = Function.update x m (cc m * x m + g m x) := fun m x => rfl
    have hweak : ∀ (i : Fin (n+1)) (x y : Fin (n+1) → ℝ),
        (∀ m : Fin (n+1), m ≠ i → x m = y m) → g i x = g i y := by
      intro i x y hxy
      exact hgdep i x y (fun m hm => hxy m (ne_of_gt hm))
    have hPK0 : PK 0 = ENNReal.ofReal (cc 0) := by
      show (∏ j : Fin (n+1), (if j ≤ (0 : Fin (n+1)) then ENNReal.ofReal (cc j) else 1)) = _
      exact prod_le_zero (fun j : Fin (n+1) => ENNReal.ofReal (cc j))
    have hPKl : PK (Fin.last n) = ∏ i : Fin (n+1), ENNReal.ofReal (cc i) := by
      show (∏ j : Fin (n+1), (if j ≤ Fin.last n then ENNReal.ofReal (cc j) else 1)) = _
      exact prod_le_last (fun j : Fin (n+1) => ENNReal.ofReal (cc j))
    have key : ∀ m : Fin (n+1), volume (Φp m '' A) = PK m * volume A
        ∧ MeasurableSet (Φp m '' A) := by
      intro m
      refine Fin.induction (motive := fun m => volume (Φp m '' A) = PK m * volume A
        ∧ MeasurableSet (Φp m '' A)) ?_ ?_ m
      · have h0 : Φp 0 = T 0 := by
          funext x j
          rw [hΦp, hT, Function.update_apply]
          by_cases hj : j = 0
          · subst j
            rw [if_pos le_rfl, if_pos rfl, hΦ]
          · rw [if_neg hj]
            have hlt : ¬ (j ≤ (0 : Fin (n+1))) := fun hle => hj (Fin.ext (by simpa using hle))
            rw [if_neg hlt]
        rw [h0, hPK0]
        exact shear_volume_measurable (d := n+1) (0 : Fin (n+1)) (c := cc 0) (hcc 0)
          (hgmeas 0) (hweak 0) hA
      · intro i ih
        have heq : Φp i.succ = T i.succ ∘ Φp i.castSucc := by
          funext x j
          rw [Function.comp_apply, hΦp, hT, Function.update_apply]
          by_cases hj : j = i.succ
          · subst j
            have hcast : ¬ ((i.succ : Fin (n+1)) ≤ i.castSucc) := by
              rw [Fin.le_iff_val_le_val]
              simp
            have hg_eq : g (i.succ) (Φp i.castSucc x) = g (i.succ) x :=
              hgdep i.succ (Φp i.castSucc x) x (fun m hm => by
                rw [hΦp]
                have hnot : ¬ (m ≤ i.castSucc) := by
                  rw [Fin.le_iff_val_le_val]
                  simp only [Fin.val_castSucc]
                  rw [Fin.lt_iff_val_lt_val] at hm
                  simp only [Fin.val_succ] at hm
                  omega
                rw [if_neg hnot])
            rw [if_pos le_rfl, if_pos rfl, hΦp, if_neg hcast, hΦ, hg_eq]
          · rw [if_neg hj, hΦp]
            have hiff : (j ≤ i.succ) ↔ (j ≤ i.castSucc) := by
              rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val]
              simp only [Fin.val_castSucc, Fin.val_succ]
              constructor
              · intro h
                have hjv : (j : ℕ) ≠ i.val + 1 := by
                  intro hc; exact hj (Fin.ext (by rw [hc]; rfl))
                omega
              · intro h; omega
            by_cases hle : j ≤ i.succ
            · rw [if_pos hle, if_pos (hiff.mp hle)]
            · rw [if_neg hle, if_neg (fun h => hle (hiff.mpr h))]
        have himg : (T i.succ ∘ Φp i.castSucc) '' A = T i.succ '' (Φp i.castSucc '' A) :=
          Set.image_comp (T i.succ) (Φp i.castSucc) A
        have hPKsucc : PK i.succ = PK i.castSucc * ENNReal.ofReal (cc i.succ) := by
          show (∏ j : Fin (n+1), (if j ≤ i.succ then ENNReal.ofReal (cc j) else 1)) = _
          rw [prod_Iic_succ]
        have hmain := shear_volume_measurable (d := n+1) (i.succ) (c := cc i.succ) (hcc i.succ)
          (hgmeas i.succ) (hweak i.succ) ih.2
        rw [heq, himg]
        constructor
        · rw [hmain.1, ih.1, hPKsucc]
          ac_rfl
        · exact hmain.2
    have hlast : Φp (Fin.last n) = Φ := by
      funext x j
      rw [hΦp, if_pos (Fin.le_last j)]
    have hthis := key (Fin.last n)
    rw [hlast, hPKl] at hthis
    exact hthis

private theorem centMap_eq_local {d : ℕ} (lam : Fin (d+1) → ℝ) (hlam0 : lam 0 = 0)
    (c : Fin d → (Fin d → ℝ) → (Fin d → ℝ))
    (hcfix : ∀ (i : Fin d) (x : Fin d → ℝ) (m : Fin d), i ≤ m → c i x m = x m)
    (m : Fin d) (x : Fin d → ℝ) :
    (∑ i : Fin d, lamStep lam i • c i x) m = (lam m.succ / 2) * x m + offDiag lam c m x := by
  rw [offDiag_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun i : Fin d => i ≤ m) (f := fun i : Fin d => lamStep lam i * (c i x) m)]
  have h1 : (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ m), lamStep lam i * (c i x) m)
      = (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ m), lamStep lam i) * x m := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [hcfix i x m hi.2]
  rw [h1, show (∑ i ∈ Finset.univ.filter (fun i : Fin d => i ≤ m), lamStep lam i)
      = lam m.succ / 2 from by simpa only [lamStep_apply] using diag_telescope lam hlam0 m]

theorem centroidMap_volume {d : ℕ} (lam : Fin (d+1) → ℝ) (hlam0 : lam 0 = 0)
    (hpos : ∀ i : Fin d, 0 < lam i.succ)
    (c : Fin d → (Fin d → ℝ) → (Fin d → ℝ))
    (hcmeas : ∀ i, Measurable (c i))
    (hcfix : ∀ (i : Fin d) (x : Fin d → ℝ) (m : Fin d), i ≤ m → c i x m = x m)
    (hcdep : ∀ (i : Fin d) (x y : Fin d → ℝ), (∀ m, i ≤ m → x m = y m) → c i x = c i y)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    MeasureTheory.volume.real
        ((fun x : Fin d → ℝ => ∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i x) '' A)
      = (∏ i : Fin d, lam i.succ / 2) * MeasureTheory.volume.real A
    ∧ MeasureTheory.NullMeasurableSet
        ((fun x : Fin d → ℝ => ∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i x) '' A)
        MeasureTheory.volume := by
  classical
  have hcc : ∀ i : Fin d, 0 < lam i.succ / 2 := fun i => by
    have := hpos i; linarith
  have hmain := triangular_map_volume
    (Φ := fun x : Fin d → ℝ => ∑ i : Fin d, ((lam i.succ - lam i.castSucc) / 2) • c i x)
    (cc := fun m : Fin d => lam m.succ / 2)
    (hcc := hcc)
    (g := fun (m : Fin d) (x : Fin d → ℝ) => offDiag lam c m x)
    (hgmeas := fun m => (offDiag_meas_dep lam c hcmeas hcdep m).1)
    (hgdep := fun i x y h => (offDiag_meas_dep lam c hcmeas hcdep i).2 x y h)
    (hΦ := fun x m => by
      have h := centMap_eq_local lam hlam0 c hcfix m x
      simpa only [lamStep_apply] using h)
    hA
  obtain ⟨hv, hm⟩ := hmain
  constructor
  · rw [Measure.real_def, Measure.real_def, hv, ENNReal.toReal_mul, ENNReal.toReal_prod]
    congr 1
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [ENNReal.toReal_ofReal (by have := hpos i; linarith)]
  · exact hm.nullMeasurableSet

end Work.BW.Minkowski2
