import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.PFDefs
import Submission.Work.HP.HP2.Psi_lip
import Submission.Work.HP.volume_rNorm_ball
import Submission.Work.HP.volume_rNorm_ball_lt
import Submission.Work.HP.HP2.volume_rNorm_le_ne_top
import Submission.Work.HP.MinkDefs

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset

namespace Work.HP.HP2

/-! ## 1. Continuity of the two functions defining the cone region -/

private theorem ft_continuous_rNorm (n : ℕ) :
    Continuous (fun z : Fin (n + 1) → ℝ => rNorm z) := by
  have h : Continuous (fun z : Fin (n + 1) → ℝ => ∑ i, (z i) ^ 2) :=
    continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).pow 2)
  exact Real.continuous_sqrt.comp h

private theorem ft_continuous_Psi (d n : ℕ) (a : Mon d n → ℤ) (α : ℝ) :
    Continuous (fun x : Fin (n + 1) → ℝ => Psi d n a α x) := by
  have hQ : Continuous (fun x : Fin (n + 1) → ℝ => formEvalR d n (toR a) x) := by
    simp only [formEvalR]
    refine continuous_finsetSum Finset.univ (fun m _ => ?_)
    exact continuous_const.mul (by
      simp only [veronese]
      exact continuous_finsetProd Finset.univ (fun i _ => (continuous_apply i).pow (m.1 i : ℕ)))
  have hV : Continuous (fun x : Fin (n + 1) → ℝ => veronese d n x) := by
    rw [continuous_pi_iff]
    intro m
    simp only [veronese]
    exact continuous_finsetProd Finset.univ (fun i _ => (continuous_apply i).pow (m.1 i : ℕ))
  have hS : Continuous (fun z : Mon d n → ℝ => rNorm z) := by
    have h : Continuous (fun z : Mon d n → ℝ => ∑ i, (z i) ^ 2) :=
      continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).pow 2)
    exact Real.continuous_sqrt.comp h
  simp only [Psi]
  exact (continuous_const.mul (hQ.pow 2)).sub (continuous_const.mul ((hS.comp hV).pow 2))

/-! ## 2. The frontier of the cone region -/

private theorem ft_frontier_subset_rNorm_le (d n : ℕ) (a : Mon d n → ℤ) {α T : ℝ} :
    frontier (coneRegion d n a α T) ⊆ {z : Fin (n + 1) → ℝ | rNorm z ≤ T} := by
  have hclosed : IsClosed {z : Fin (n + 1) → ℝ | rNorm z ≤ T} :=
    isClosed_le (ft_continuous_rNorm n) continuous_const
  intro y hy
  have hmono : closure (coneRegion d n a α T) ⊆ closure {z : Fin (n + 1) → ℝ | rNorm z ≤ T} :=
    closure_mono (fun z hz => hz.1)
  have hcl := hmono (frontier_subset_closure hy)
  rwa [hclosed.closure_eq] at hcl

private theorem ft_frontier_subset (d n : ℕ) (a : Mon d n → ℤ) {α T : ℝ} (hα : 0 < α) :
    frontier (coneRegion d n a α T) ⊆
      {z : Fin (n + 1) → ℝ | rNorm z = T} ∪ {z : Fin (n + 1) → ℝ | Psi d n a α z = 0} := by
  have hEq : {x : Fin (n + 1) → ℝ | rNorm x ≤ T ∧ Psi d n a α x ≤ 0}
      = {x : Fin (n + 1) → ℝ | rNorm x ≤ T} ∩ {x : Fin (n + 1) → ℝ | Psi d n a α x ≤ 0} := by
    ext x; simp
  rw [coneRegion_eq_psi a hα T, hEq]
  have hB : frontier {x : Fin (n + 1) → ℝ | rNorm x ≤ T} ⊆ {z : Fin (n + 1) → ℝ | rNorm z = T} := by
    have h := frontier_le_subset_eq (f := fun z : Fin (n + 1) → ℝ => rNorm z)
      (g := fun _ => T) (ft_continuous_rNorm n) continuous_const
    simpa using h
  have hP : frontier {x : Fin (n + 1) → ℝ | Psi d n a α x ≤ 0}
      ⊆ {z : Fin (n + 1) → ℝ | Psi d n a α z = 0} := by
    have h := frontier_le_subset_eq (f := fun z : Fin (n + 1) → ℝ => Psi d n a α z)
      (g := fun _ => (0:ℝ)) (ft_continuous_Psi d n a α) continuous_const
    simpa using h
  refine (frontier_inter_subset _ _).trans ?_
  exact Set.union_subset
    (Set.Subset.trans Set.inter_subset_left (Set.Subset.trans hB Set.subset_union_left))
    (Set.Subset.trans Set.inter_subset_right (Set.Subset.trans hP Set.subset_union_right))

/-! ## 3. The tube around the frontier is contained in a shell plus a sublevel set -/

private theorem ft_tube_subset (d n : ℕ) (a : Mon d n → ℤ) {α T ρ Clip : ℝ}
    (hα : 1 ≤ α) (hT : 1 ≤ T) (hρ : 0 < ρ) (hρT : ρ ≤ T) (hClip : 0 < Clip)
    (hlip : ∀ (R : ℝ) (x y : Fin (n + 1) → ℝ), 1 ≤ R → rNorm x ≤ R → rNorm y ≤ R →
      |Psi d n a α x - Psi d n a α y|
        ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * R ^ (2 * d - 1) * rNorm (x - y)) :
    {x : Fin (n + 1) → ℝ | ∃ y ∈ frontier (coneRegion d n a α T), rNorm (x - y) ≤ ρ} ⊆
      {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ} ∪
      {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
        |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ} := by
  intro x hx
  obtain ⟨y, hyF, hxy⟩ := hx
  have hα0 : (0:ℝ) < α := by linarith
  have hyT : rNorm y ≤ T := ft_frontier_subset_rNorm_le d n a hyF
  have hfr := ft_frontier_subset d n a hα0 hyF
  rcases hfr with hyTeq | hyPzero
  · left
    have h1 := Work.HP.LsetAux.abs_rNorm_sub_le x y
    rw [hyTeq] at h1
    have h := le_trans h1 hxy
    have h' := abs_le.mp h
    constructor <;> linarith [h'.1, h'.2]
  · right
    have hnorm := Work.HP.LsetAux.abs_rNorm_sub_le x y
    have hxT : rNorm x ≤ T + ρ := by
      have h1 : rNorm x - rNorm y ≤ rNorm (x - y) := (abs_le.mp hnorm).2
      linarith
    constructor
    · linarith
    · have hR1 : (1:ℝ) ≤ 2 * T := by linarith
      have hxR : rNorm x ≤ 2 * T := by linarith
      have hyR : rNorm y ≤ 2 * T := by linarith
      have hthis := hlip (2 * T) x y hR1 hxR hyR
      rw [hyPzero, sub_zero] at hthis
      exact le_trans hthis (mul_le_mul_of_nonneg_left hxy (by positivity))

/-! ## 4. Small power-difference inequality -/

private theorem ft_pow_sub_pow_le (m : ℕ) {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) :
    a ^ (m + 1) - b ^ (m + 1) ≤ ((m : ℝ) + 1) * a ^ m * (a - b) := by
  have ha : 0 ≤ a := le_trans hb hba
  have hab : 0 ≤ a - b := sub_nonneg.mpr hba
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : a ^ (m + 1 + 1) - b ^ (m + 1 + 1)
        = a * (a ^ (m + 1) - b ^ (m + 1)) + b ^ (m + 1) * (a - b) := by
      rw [pow_succ, pow_succ]; ring
    rw [h1]
    have h2 : a * (a ^ (m + 1) - b ^ (m + 1)) ≤ a * (((m : ℝ) + 1) * a ^ m * (a - b)) :=
      mul_le_mul_of_nonneg_left ih ha
    have h3 : b ^ (m + 1) * (a - b) ≤ a ^ (m + 1) * (a - b) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hba (m + 1)) hab
    have hid : a * (((m : ℝ) + 1) * a ^ m * (a - b)) + a ^ (m + 1) * (a - b)
        = ((m : ℝ) + 1 + 1) * a ^ (m + 1) * (a - b) := by
      rw [pow_succ]; ring
    push_cast
    linarith

/-! ## 5. Volume of the thin spherical shell -/

private theorem ft_shell_volume (n : ℕ) {T ρ : ℝ} (hT : 0 < T) (hρ : 0 < ρ) (hρT : ρ ≤ T) :
    MeasureTheory.volume {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ}
      ≤ ENNReal.ofReal (T ^ (n + 1) * ((2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) *
          (MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z ≤ 1}).toReal) * (ρ / T)) := by
  have hT0 : (0:ℝ) ≤ T := le_of_lt hT
  have hρ0 : (0:ℝ) ≤ ρ := le_of_lt hρ
  have hTρ0 : (0:ℝ) ≤ T + ρ := by linarith
  have hTmρ0 : (0:ℝ) ≤ T - ρ := by linarith
  set V1e : ENNReal := MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z ≤ 1} with hV1edef
  set V1 : ℝ := V1e.toReal with hV1def
  have hV1top : V1e ≠ ⊤ := by
    rw [hV1edef]; exact volume_rNorm_le_ne_top n 1
  have hV1nn : 0 ≤ V1 := ENNReal.toReal_nonneg
  have hV1 : ENNReal.ofReal V1 = V1e := by rw [hV1def]; exact ENNReal.ofReal_toReal hV1top
  have hA : MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ T + ρ}
      = ENNReal.ofReal ((T + ρ) ^ (n + 1)) * V1e := by
    have h := volume_rNorm_ball (ι := Fin (n + 1)) (0 : Fin (n + 1) → ℝ) (T + ρ) hTρ0
    rw [hV1edef]
    simpa [Fintype.card_fin] using h
  have hB : MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x < T - ρ}
      = ENNReal.ofReal ((T - ρ) ^ (n + 1)) * V1e := by
    have h := volume_rNorm_ball_lt (ι := Fin (n + 1)) (T - ρ) hTmρ0
    rw [hV1edef]
    simpa [Fintype.card_fin] using h
  have hBtop : MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x < T - ρ} ≠ ⊤ := by
    rw [hB]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV1top
  have hmeasB : MeasurableSet {x : Fin (n + 1) → ℝ | rNorm x < T - ρ} :=
    measurableSet_lt (ft_continuous_rNorm n).measurable measurable_const
  have hsub : {x : Fin (n + 1) → ℝ | rNorm x < T - ρ}
      ⊆ {x : Fin (n + 1) → ℝ | rNorm x ≤ T + ρ} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    linarith
  have hset : {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ}
      = {x : Fin (n + 1) → ℝ | rNorm x ≤ T + ρ} \ {x : Fin (n + 1) → ℝ | rNorm x < T - ρ} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_lt]
    tauto
  have hshell : MeasureTheory.volume {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ}
      = ENNReal.ofReal ((T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1)) * V1e := by
    rw [hset, measure_sdiff hsub hmeasB.nullMeasurableSet hBtop, hA, hB]
    rw [← ENNReal.sub_mul (a := ENNReal.ofReal ((T + ρ) ^ (n + 1)))
          (b := ENNReal.ofReal ((T - ρ) ^ (n + 1))) (c := V1e) (fun _ _ => hV1top)]
    rw [← ENNReal.ofReal_sub ((T + ρ) ^ (n + 1)) (pow_nonneg hTmρ0 _)]
  have hDnn : 0 ≤ (T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1) :=
    sub_nonneg.mpr (pow_le_pow_left₀ hTmρ0 (by linarith) (n + 1))
  have hshell2 : MeasureTheory.volume {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ}
      = ENNReal.ofReal (((T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1)) * V1) := by
    rw [hshell, ← hV1, ← ENNReal.ofReal_mul hDnn]
  have hkey : T ^ (n + 1) * (ρ / T) = T ^ n * ρ := by
    have h1 : T * (ρ / T) = ρ := by field_simp [ne_of_gt hT] <;> ring
    rw [pow_succ, mul_assoc, h1]
  have hmain : ((T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1)) * V1
      ≤ T ^ (n + 1) * ((2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) * V1) * (ρ / T) := by
    have hbale : T - ρ ≤ T + ρ := by linarith
    have hDbound : (T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1)
        ≤ (2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) * T ^ n * ρ := by
      have h := ft_pow_sub_pow_le n (a := T + ρ) (b := T - ρ) hTmρ0 hbale
      have hsub2 : (T + ρ) - (T - ρ) = 2 * ρ := by ring
      rw [hsub2] at h
      have h2 : (T + ρ) ^ n ≤ (2 * T) ^ n := pow_le_pow_left₀ hTρ0 (by linarith) n
      calc (T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1)
          ≤ ((n:ℝ) + 1) * (T + ρ) ^ n * (2 * ρ) := h
        _ ≤ ((n:ℝ) + 1) * (2 * T) ^ n * (2 * ρ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) * T ^ n * ρ := by
            rw [pow_succ, mul_pow]; ring
    have hDbound' : (T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1)
        ≤ (2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) * T ^ (n + 1) * (ρ / T) := by
      refine hDbound.trans (le_of_eq ?_)
      rw [pow_succ]
      field_simp [ne_of_gt hT] <;> ring
    calc ((T + ρ) ^ (n + 1) - (T - ρ) ^ (n + 1)) * V1
        ≤ ((2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) * T ^ (n + 1) * (ρ / T)) * V1 :=
          mul_le_mul_of_nonneg_right hDbound' hV1nn
      _ = T ^ (n + 1) * ((2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) * V1) * (ρ / T) := by ring
  rw [hshell2]
  exact ENNReal.ofReal_le_ofReal hmain

/-! ## 6. Volume of the cone-sublevel piece, via the hypothesis `hsub` -/

private theorem ft_cone_sublevel (d n : ℕ) (hd : 1 ≤ d) {Csub Ksub Clip : ℝ}
    (hCsub : 0 < Csub) (hKsub : 0 < Ksub) (hClip : 0 < Clip)
    (hsub : ∀ (a : Mon d n → ℤ) (α T lam : ℝ), a ≠ 0 → 1 ≤ α → 0 < T → 0 ≤ lam →
      (MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ T ∧
          |Psi d n a α x| ≤ lam}).toReal
        ≤ T ^ (n + 1) * Csub *
            Real.rpow (lam / (T ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / Ksub))
    (a : Mon d n → ℤ) (ha : a ≠ 0) {α T ρ : ℝ} (hα : 1 ≤ α) (hT : 1 ≤ T)
    (hρ : 0 < ρ) (hρT : ρ ≤ T) :
    MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
        |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ}
      ≤ ENNReal.ofReal (T ^ (n + 1) * ((2:ℝ) ^ (n + 1) * Csub * Real.rpow Clip (1 / Ksub))
          * Real.rpow (ρ / T) (1 / Ksub)) := by
  have hα0 : (0:ℝ) < α := by linarith
  have h2T : (0:ℝ) < 2 * T := by linarith
  have hApos : 0 < eNorm a := eNorm_pos_of_ne_zero ha
  have hL0 : 0 ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ := by positivity
  have hsubapp := hsub a α (2 * T)
    (Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ) ha hα h2T hL0
  have hS2top : MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
      |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (volume_rNorm_le_ne_top n (2 * T)) (measure_mono ?_)
    intro x hx; exact hx.1
  have hDpos : 0 ≤ (Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ) /
        ((2 * T) ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2)) := by positivity
  have hrnpos : 0 ≤ (2 * T) ^ (n + 1) * Csub *
      Real.rpow ((Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ) /
        ((2 * T) ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / Ksub) :=
    mul_nonneg (mul_nonneg (by positivity) (le_of_lt hCsub)) (Real.rpow_nonneg hDpos _)
  have h1 : MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
      |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ}
      ≤ ENNReal.ofReal ((2 * T) ^ (n + 1) * Csub *
          Real.rpow ((Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ) /
            ((2 * T) ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / Ksub)) :=
    (ENNReal.le_ofReal_iff_toReal_le hS2top hrnpos).mpr hsubapp
  have h2d : 1 ≤ 2 * d := by omega
  have hrpow_eq : (Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ) /
        ((2 * T) ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2)) = Clip * (ρ / (2 * T)) := by
    have hpw : (2 * T) ^ (2 * d) = (2 * T) ^ (2 * d - 1) * (2 * T) := by
      rw [← pow_succ, Nat.sub_add_cancel h2d]
    field_simp
    rw [hpw]
    ring
  have hrpow : Real.rpow ((Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ) /
        ((2 * T) ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / Ksub)
      = Real.rpow Clip (1 / Ksub) * Real.rpow (ρ / (2 * T)) (1 / Ksub) := by
    rw [hrpow_eq]
    exact Real.mul_rpow (le_of_lt hClip) (show (0:ℝ) ≤ ρ / (2 * T) by positivity)
  have hle1 : Real.rpow (ρ / (2 * T)) (1 / Ksub) ≤ Real.rpow (ρ / T) (1 / Ksub) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    rw [div_le_div_iff₀ (by positivity) (by linarith : (0:ℝ) < T)]
    nlinarith [le_of_lt hρ]
  have hCnn : 0 ≤ (2 * T) ^ (n + 1) * Csub * Real.rpow Clip (1 / Ksub) :=
    mul_nonneg (mul_nonneg (by positivity) (le_of_lt hCsub)) (Real.rpow_nonneg (le_of_lt hClip) _)
  have hreal : (2 * T) ^ (n + 1) * Csub *
        Real.rpow ((Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ) /
          ((2 * T) ^ (2 * d) * (α ^ 2 * (eNorm a) ^ 2))) (1 / Ksub)
      ≤ T ^ (n + 1) * ((2:ℝ) ^ (n + 1) * Csub * Real.rpow Clip (1 / Ksub))
          * Real.rpow (ρ / T) (1 / Ksub) := by
    rw [hrpow]
    calc (2 * T) ^ (n + 1) * Csub *
            (Real.rpow Clip (1 / Ksub) * Real.rpow (ρ / (2 * T)) (1 / Ksub))
        = ((2 * T) ^ (n + 1) * Csub * Real.rpow Clip (1 / Ksub))
            * Real.rpow (ρ / (2 * T)) (1 / Ksub) := by ring
      _ ≤ ((2 * T) ^ (n + 1) * Csub * Real.rpow Clip (1 / Ksub))
            * Real.rpow (ρ / T) (1 / Ksub) :=
          mul_le_mul_of_nonneg_left hle1 hCnn
      _ = T ^ (n + 1) * ((2:ℝ) ^ (n + 1) * Csub * Real.rpow Clip (1 / Ksub))
            * Real.rpow (ρ / T) (1 / Ksub) := by
          rw [mul_pow]; ring
  exact h1.trans (ENNReal.ofReal_le_ofReal hreal)

/-! ## 7. Assembly -/

theorem frontier_tube_le (d n : ℕ) (hd : 1 ≤ d) (Csub Ksub Clip : ℝ)
    (hCsub : 0 < Csub) (hKsub : 0 < Ksub) (hClip : 0 < Clip)
    (hsub : ∀ (a : Work.HP.Mon d n → ℤ) (α T lam : ℝ), a ≠ 0 → 1 ≤ α → 0 < T → 0 ≤ lam →
      (MeasureTheory.volume {x : Fin (n + 1) → ℝ | Work.HP.rNorm x ≤ T ∧
          |Work.HP.Psi d n a α x| ≤ lam}).toReal
        ≤ T ^ (n + 1) * Csub *
            Real.rpow (lam / (T ^ (2 * d) * (α ^ 2 * (Work.HP.eNorm a) ^ 2))) (1 / Ksub))
    (hlip : ∀ (a : Work.HP.Mon d n → ℤ) (α R : ℝ) (x y : Fin (n + 1) → ℝ),
      1 ≤ α → 1 ≤ R → Work.HP.rNorm x ≤ R → Work.HP.rNorm y ≤ R →
      |Work.HP.Psi d n a α x - Work.HP.Psi d n a α y|
        ≤ Clip * α ^ 2 * (Work.HP.eNorm a) ^ 2 * R ^ (2 * d - 1) * Work.HP.rNorm (x - y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Work.HP.Mon d n → ℤ) (α T ρ : ℝ),
      a ≠ 0 → 1 ≤ α → 1 ≤ T → 0 < ρ → ρ ≤ T →
      (MeasureTheory.volume {x : Fin (n + 1) → ℝ |
          ∃ y ∈ frontier (Work.HP.coneRegion d n a α T), Work.HP.rNorm (x - y) ≤ ρ}).toReal
        ≤ T ^ (n + 1) * C * (Real.rpow (ρ / T) (1 / Ksub) + ρ / T) := by
  set K1 : ℝ := (2:ℝ) ^ (n + 1) * Csub * Real.rpow Clip (1 / Ksub) with hK1def
  set K2 : ℝ := (2:ℝ) ^ (n + 1) * ((n:ℝ) + 1) *
    (MeasureTheory.volume {z : Fin (n + 1) → ℝ | rNorm z ≤ 1}).toReal with hK2def
  have hK1nn : 0 ≤ K1 := by
    rw [hK1def]
    exact mul_nonneg (mul_nonneg (by positivity) (le_of_lt hCsub))
      (Real.rpow_nonneg (le_of_lt hClip) _)
  have hK2nn : 0 ≤ K2 := by
    rw [hK2def]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) ENNReal.toReal_nonneg
  have hmaxnn : 0 ≤ max K1 K2 := le_trans hK1nn (le_max_left K1 K2)
  have hCpos : 0 < max K1 K2 + 1 := by linarith
  refine ⟨max K1 K2 + 1, hCpos, ?_⟩
  intro a α T ρ ha hα hT hρ hρT
  set w : ℝ := ρ / T with hwdef
  have hT0 : (0:ℝ) < T := by linarith
  have hw0 : 0 ≤ w := by rw [hwdef]; positivity
  have hwnn : 0 ≤ Real.rpow w (1 / Ksub) := Real.rpow_nonneg hw0 _
  have hlip' : ∀ (R : ℝ) (x y : Fin (n + 1) → ℝ), 1 ≤ R → rNorm x ≤ R → rNorm y ≤ R →
      |Psi d n a α x - Psi d n a α y|
        ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * R ^ (2 * d - 1) * rNorm (x - y) :=
    fun R x y hR hx hy => hlip a α R x y hα hR hx hy
  have hsubΩ : {x : Fin (n + 1) → ℝ |
        ∃ y ∈ frontier (coneRegion d n a α T), rNorm (x - y) ≤ ρ} ⊆
      {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ} ∪
      {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
        |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ} :=
    ft_tube_subset d n a hα hT hρ hρT hClip hlip'
  have hS1 : MeasureTheory.volume {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ}
      ≤ ENNReal.ofReal (T ^ (n + 1) * K2 * w) := by
    rw [hK2def, hwdef]
    exact ft_shell_volume n hT0 hρ hρT
  have hS2 : MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
        |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ}
      ≤ ENNReal.ofReal (T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub)) := by
    rw [hK1def, hwdef]
    exact ft_cone_sublevel d n hd hCsub hKsub hClip hsub a ha hα hT hρ hρT
  have hAnn : 0 ≤ T ^ (n + 1) * K2 * w :=
    mul_nonneg (mul_nonneg (by positivity) hK2nn) hw0
  have hBnn : 0 ≤ T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub) :=
    mul_nonneg (mul_nonneg (by positivity) hK1nn) hwnn
  have hvolΩ : MeasureTheory.volume {x : Fin (n + 1) → ℝ |
        ∃ y ∈ frontier (coneRegion d n a α T), rNorm (x - y) ≤ ρ}
      ≤ ENNReal.ofReal (T ^ (n + 1) * K2 * w + T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub)) := by
    calc MeasureTheory.volume {x : Fin (n + 1) → ℝ |
            ∃ y ∈ frontier (coneRegion d n a α T), rNorm (x - y) ≤ ρ}
        ≤ MeasureTheory.volume ({x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ} ∪
            {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
              |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ}) :=
          measure_mono hsubΩ
      _ ≤ MeasureTheory.volume {x : Fin (n + 1) → ℝ | T - ρ ≤ rNorm x ∧ rNorm x ≤ T + ρ}
            + MeasureTheory.volume {x : Fin (n + 1) → ℝ | rNorm x ≤ 2 * T ∧
              |Psi d n a α x| ≤ Clip * α ^ 2 * (eNorm a) ^ 2 * (2 * T) ^ (2 * d - 1) * ρ} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (T ^ (n + 1) * K2 * w)
            + ENNReal.ofReal (T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub)) :=
          add_le_add hS1 hS2
      _ = ENNReal.ofReal (T ^ (n + 1) * K2 * w + T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub)) :=
          (ENNReal.ofReal_add hAnn hBnn).symm
  have habnn : 0 ≤ T ^ (n + 1) * K2 * w + T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub) :=
    add_nonneg hAnn hBnn
  have harith : T ^ (n + 1) * K2 * w + T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub)
      ≤ T ^ (n + 1) * (max K1 K2 + 1) * (Real.rpow w (1 / Ksub) + w) := by
    have hTp : 0 ≤ T ^ (n + 1) := by positivity
    have h1 : T ^ (n + 1) * K2 * w ≤ T ^ (n + 1) * (max K1 K2 + 1) * w :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (le_trans (le_max_right K1 K2) (le_add_of_nonneg_right zero_le_one)) hTp) hw0
    have h2 : T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub)
        ≤ T ^ (n + 1) * (max K1 K2 + 1) * Real.rpow w (1 / Ksub) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (le_trans (le_max_left K1 K2) (le_add_of_nonneg_right zero_le_one)) hTp) hwnn
    calc T ^ (n + 1) * K2 * w + T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub)
        ≤ T ^ (n + 1) * (max K1 K2 + 1) * w
            + T ^ (n + 1) * (max K1 K2 + 1) * Real.rpow w (1 / Ksub) := add_le_add h1 h2
      _ = T ^ (n + 1) * (max K1 K2 + 1) * (Real.rpow w (1 / Ksub) + w) := by ring
  calc (MeasureTheory.volume {x : Fin (n + 1) → ℝ |
          ∃ y ∈ frontier (coneRegion d n a α T), rNorm (x - y) ≤ ρ}).toReal
      ≤ (ENNReal.ofReal (T ^ (n + 1) * K2 * w
          + T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hvolΩ
    _ = T ^ (n + 1) * K2 * w + T ^ (n + 1) * K1 * Real.rpow w (1 / Ksub) :=
        ENNReal.toReal_ofReal habnn
    _ ≤ T ^ (n + 1) * (max K1 K2 + 1) * (Real.rpow w (1 / Ksub) + w) := harith

end Work.HP.HP2
