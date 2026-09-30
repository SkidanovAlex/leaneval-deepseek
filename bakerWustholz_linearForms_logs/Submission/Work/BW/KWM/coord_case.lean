import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_succMinL_mono
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.Minkowski2.slicing_scaleFirst
import Submission.Work.BW.Minkowski2.volume_scaleLast
import Submission.Work.BW.KWM.basic
import Submission.Work.BW.KWM.coord_defs
import Submission.Work.BW.KWM.coord

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coordinate case of Minkowski's second theorem
-/

namespace Work.BW.KWM

open MeasureTheory
open scoped Pointwise
open scoped ENNReal

variable {n : ℕ}

/-- Composing `scaleFirst i ρ` with `scaleLast i ρ` multiplies by `ρ`. -/
theorem scaleLast_scaleFirst (i : ℕ) (ρ : ℝ) (x : Fin n → ℝ) :
    Work.BW.scaleLast i ρ (Work.BW.scaleFirst i ρ x) = ρ • x := by
  ext j
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases hj : (j : ℕ) < i
  · rw [Work.BW.scaleLast_apply_lt i ρ _ hj, Work.BW.scaleFirst_apply_lt i ρ x hj]
  · rw [Work.BW.scaleLast_apply_not i ρ _ hj, Work.BW.scaleFirst_apply_not i ρ x hj]

/-- `Vset F (i+1)` is the dilate of `Vset F i` by `λ_{i+1}/λ_i`. -/
theorem scaling_ratio (F : (Fin n → ℝ) → ℝ) {i : ℕ} (hLi : Work.BW.succMinL F i ≠ 0) :
    Vset F (i + 1) = (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) • Vset F i := by
  have hscal : (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i)
      * (Work.BW.succMinL F i / 2) = Work.BW.succMinL F (i + 1) / 2 := by
    rw [mul_div_assoc', div_mul_cancel₀ _ hLi]
  rw [Vset, Vset, ← mul_smul, hscal]

/-- The scaling step: dilating the low part by `ρ` and pushing forward along `scaleLast`. -/
theorem stage_step (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F)
    (q i : ℕ) (hi1 : 1 ≤ i) (hin : i + 1 ≤ n) :
    (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (n - i) *
        volume.real (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
          (Vset F i))
      ≤ volume.real (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
          (Vset F (i + 1))) := by
  have hin' : i ≤ n := by omega
  have hLi : 0 < Work.BW.succMinL F i := succMinL_pos_of_le hF hi1 hin'
  have hρ1 : 1 ≤ Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i := by
    rw [le_div_iff₀ hLi]
    simpa using Work.BW.basisRed_succMinL_mono hF (by omega) hin
  have hρ0 : 0 < Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i :=
    lt_of_lt_of_le zero_lt_one hρ1
  have hM : ∀ x ∈ rcubeLo n q i, ∀ j : Fin n, i ≤ (j : ℕ) → x j = 0 :=
    fun x hx j hj => mem_rcubeLo_apply hx j hj
  have hslice := Work.BW.Minkowski2.slicing_scaleFirst (d := n) i hρ1 (rcubeLo n q i) hM
    (Vset F i) (Vset_convex F hF i) (Vset_measurable F hF hLi)
  have hfix : ∀ m ∈ ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)),
      Work.BW.scaleLast i (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) m = m := by
    intro m hm
    ext j
    by_cases hj : (j : ℕ) < i
    · rw [Work.BW.scaleLast_apply_lt i _ m hj]
    · rw [Work.BW.scaleLast_apply_not i _ m hj, mem_rcubeLo_apply hm j (not_lt.mp hj), mul_zero]
  have hset : Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
        (Vset F (i + 1))
      = Work.BW.scaleLast i (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ''
          (Work.BW.addSet ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
            (Work.BW.scaleFirst i (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ''
              (Vset F i))) := by
    rw [scaling_ratio F (ne_of_gt hLi)]
    ext x
    rw [Work.BW.mem_addSet, Set.mem_image]
    constructor
    · rintro ⟨m, hm, y, hy, hx⟩
      obtain ⟨z, hz, hyz⟩ := hy
      have hyz' : (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) • z = y := hyz
      refine ⟨m + Work.BW.scaleFirst i (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) z,
        ⟨m, hm, Work.BW.scaleFirst i (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) z,
          ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      rw [map_add, hfix m hm, scaleLast_scaleFirst, hyz', hx]
    · rintro ⟨w, ⟨m, hm, y, hy, hw⟩, hx⟩
      obtain ⟨z, hz, hyz⟩ := hy
      refine ⟨m, hm,
        (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) • z, ⟨z, hz, rfl⟩, ?_⟩
      rw [← hx, hw, ← hyz, map_add, hfix m hm, scaleLast_scaleFirst]
  rw [hset, Work.BW.Minkowski2.volume_scaleLast hρ0]
  exact mul_le_mul_of_nonneg_left hslice (pow_nonneg hρ0.le _)

theorem rcubeHi_zero (q : ℕ) : rcubeHi n q 0 = rcube n q := by
  ext x
  simp [rcubeHi, rcube, zcubeHi, zcube]

theorem rcubeLo_zero (q : ℕ) : rcubeLo n q 0 = {(0 : Fin n → ℝ)} := by
  ext x
  rw [rcubeLo, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [zcubeLo, Fintype.mem_piFinset] at hv
    ext k
    have h : v k = 0 := by
      have h2 := hv k
      rw [if_neg (by omega : ¬ ((k : ℕ) < 0))] at h2
      simpa using h2
    simp [cvec, h]
  · rintro rfl
    refine ⟨0, ?_, ?_⟩
    · rw [zcubeLo, Fintype.mem_piFinset]
      intro k
      rw [if_neg (by omega : ¬ ((k : ℕ) < 0))]
      simp
    · ext k
      simp [cvec]

theorem addSet_singleton_zero (A : Set (Fin n → ℝ)) :
    Work.BW.addSet (({(0 : Fin n → ℝ)} : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) A = A := by
  ext x
  rw [Work.BW.mem_addSet]
  constructor
  · rintro ⟨m, hm, a, ha, hx⟩
    have hm0 : m = 0 := by simpa using hm
    rw [hm0, zero_add] at hx
    rwa [hx]
  · intro hx
    exact ⟨0, by simp, x, hx, by rw [zero_add]⟩

theorem volume_real_smul (c : ℝ) (hc : 0 ≤ c) (S : Set (Fin n → ℝ)) :
    volume.real (c • S) = c ^ n * volume.real S := by
  rw [MeasureTheory.Measure.real_def volume (c • S), MeasureTheory.Measure.real_def volume S,
    MeasureTheory.Measure.addHaar_smul_of_nonneg volume hc S, ENNReal.toReal_mul,
    Module.finrank_fin_fun, ENNReal.toReal_ofReal (pow_nonneg hc n)]

/-- **Minkowski's second theorem in the coordinate case.** -/
theorem coord_case {n : ℕ} (hn : 0 < n) (F : (Fin n → ℝ) → ℝ) (hF : Work.BW.IsLatticeNorm F)
    (hflag : ∀ (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) (x : Fin n → ℤ),
      F (cvec x) < Work.BW.succMinL F j → cvec x ∈ cflag n (j - 1)) :
    (∏ j : Fin n, Work.BW.succMinL F (j.1 + 1)) * volume.real (uBall F) ≤ (2 : ℝ) ^ n := by
  obtain ⟨c, hc, hcbound⟩ := norm_lower_bound hF
  set R : ℝ := (Work.BW.succMinL F n / 2) / c with hRdef
  have hLn : 0 < Work.BW.succMinL F n := succMinL_pos_of_le hF hn le_rfl
  have hRnn : 0 ≤ R := by rw [hRdef]; exact div_nonneg (by linarith) (le_of_lt hc)
  have hLpos : ∀ i, 1 ≤ i → i ≤ n → 0 < Work.BW.succMinL F i :=
    fun i h1 h2 => succMinL_pos_of_le hF h1 h2
  have hVn_bound : ∀ y ∈ Vset F n, ∀ k : Fin n, |y k| ≤ R := by
    intro y hy k
    rw [Vset, Set.mem_smul_set] at hy
    obtain ⟨z, hz, hyz⟩ := hy
    rw [mem_uBall] at hz
    have h2 : ‖z‖ ≤ 1 / c := (le_div_iff₀ hc).mpr (by linarith [hcbound z])
    have h3 : ‖(Work.BW.succMinL F n / 2) • z‖ ≤ R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), hRdef]
      calc (Work.BW.succMinL F n / 2) * ‖z‖ ≤ (Work.BW.succMinL F n / 2) * (1 / c) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = (Work.BW.succMinL F n / 2) / c := by ring
    calc |y k| = |((Work.BW.succMinL F n / 2) • z) k| := by rw [← hyz]
      _ ≤ ‖(Work.BW.succMinL F n / 2) • z‖ := by
          simpa only [Real.norm_eq_abs] using
            norm_le_pi_norm ((Work.BW.succMinL F n / 2) • z) k
      _ ≤ R := h3
  have hupper : ∀ q : ℕ, volume.real
      (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) (Vset F n))
      ≤ (2 * (q : ℝ) + 2 * R) ^ n := by
    intro q
    have hsub : Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
        (Vset F n) ⊆ Set.Icc (fun _ : Fin n => -((q : ℝ) + R)) (fun _ => ((q : ℝ) + R)) := by
      rintro x ⟨v, hv, y, hy, hxy⟩
      rw [hxy, Set.mem_Icc]
      constructor
      · intro k
        have h1 : -(q : ℝ) ≤ v k := (abs_le.mp (mem_rcube_apply hv k)).1
        have h2 : -R ≤ y k := (abs_le.mp (hVn_bound y hy k)).1
        simp only [Pi.add_apply]
        linarith
      · intro k
        have h1 : v k ≤ (q : ℝ) := (abs_le.mp (mem_rcube_apply hv k)).2
        have h2 : y k ≤ R := (abs_le.mp (hVn_bound y hy k)).2
        simp only [Pi.add_apply]
        linarith
    have hfin : volume (Set.Icc (fun _ : Fin n => -((q : ℝ) + R))
        (fun _ => ((q : ℝ) + R))) ≠ ∞ := by
      rw [Real.volume_Icc_pi]
      exact ENNReal.prod_ne_top (fun i _ => ENNReal.ofReal_ne_top)
    have hbox : volume.real (Set.Icc (fun _ : Fin n => -((q : ℝ) + R))
        (fun _ => ((q : ℝ) + R))) = (2 * (q : ℝ) + 2 * R) ^ n := by
      have hle : (fun _ : Fin n => -((q : ℝ) + R)) ≤ (fun _ => ((q : ℝ) + R)) := by
        intro k
        linarith [hRnn, (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))]
      rw [MeasureTheory.Measure.real_def, Real.volume_Icc_pi_toReal hle]
      have hfac : (∏ k : Fin n, (((q : ℝ) + R) - (-((q : ℝ) + R))))
          = ∏ k : Fin n, (2 * (q : ℝ) + 2 * R) :=
        Finset.prod_congr rfl (fun k _ => by ring)
      rw [hfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc volume.real (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
            (Vset F n))
        ≤ volume.real (Set.Icc (fun _ : Fin n => -((q : ℝ) + R))
            (fun _ => ((q : ℝ) + R))) := MeasureTheory.measureReal_mono hsub hfin
      _ = (2 * (q : ℝ) + 2 * R) ^ n := hbox
  have hratioIco : ∀ m : ℕ, 1 ≤ m →
      (∀ i, 1 ≤ i → i ≤ m → Work.BW.succMinL F i ≠ 0) →
      (∏ i ∈ Finset.Ico 1 m,
          (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i)) * Work.BW.succMinL F 1
        = Work.BW.succMinL F m := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base => intro _; rw [Finset.Ico_self, Finset.prod_empty, one_mul]
    | succ k hk ih =>
        intro hL
        have hk0 : Work.BW.succMinL F k ≠ 0 := hL k hk (by omega)
        have hstep : (∏ i ∈ Finset.Ico 1 k,
            (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i)) * Work.BW.succMinL F 1
            = Work.BW.succMinL F k := ih (fun i h1 h2 => hL i h1 (by omega))
        rw [Finset.prod_Ico_succ_top hk]
        calc ((∏ i ∈ Finset.Ico 1 k,
              (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i))
              * (Work.BW.succMinL F (k + 1) / Work.BW.succMinL F k))
              * Work.BW.succMinL F 1
            = ((∏ i ∈ Finset.Ico 1 k,
                (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i)) * Work.BW.succMinL F 1)
                * (Work.BW.succMinL F (k + 1) / Work.BW.succMinL F k) := by ring
          _ = Work.BW.succMinL F k
                * (Work.BW.succMinL F (k + 1) / Work.BW.succMinL F k) := by rw [hstep]
          _ = Work.BW.succMinL F (k + 1) := by rw [mul_div_cancel₀ _ hk0]
  have hid : ∀ m : ℕ, (∀ i, 1 ≤ i → i ≤ m → 0 < Work.BW.succMinL F i) →
      (∏ i ∈ Finset.Ico 1 m,
          (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (m - i))
        * Work.BW.succMinL F 1 ^ m
        = ∏ j ∈ Finset.Ico 1 (m + 1), Work.BW.succMinL F j := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
        intro hL
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm; simp
        · have h1 : (∏ i ∈ Finset.Ico 1 (m + 1),
                (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (m + 1 - i))
              = (∏ i ∈ Finset.Ico 1 m,
                  (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (m - i))
                * (∏ i ∈ Finset.Ico 1 m,
                  (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i))
                * (Work.BW.succMinL F (m + 1) / Work.BW.succMinL F m) := by
            rw [Finset.prod_Ico_succ_top hm, show m + 1 - m = 1 by omega, pow_one,
              ← Finset.prod_mul_distrib]
            congr 1
            refine Finset.prod_congr rfl (fun i hi => ?_)
            rw [Finset.mem_Ico] at hi
            rw [show m + 1 - i = (m - i) + 1 by omega, pow_succ]
          have h2 : (∏ j ∈ Finset.Ico 1 ((m + 1) + 1), Work.BW.succMinL F j)
              = (∏ j ∈ Finset.Ico 1 (m + 1), Work.BW.succMinL F j)
                * Work.BW.succMinL F (m + 1) :=
            Finset.prod_Ico_succ_top (a := 1) (b := m + 1) (by omega)
              (fun j => Work.BW.succMinL F j)
          have hP : (∏ i ∈ Finset.Ico 1 m,
                (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (m - i))
              * Work.BW.succMinL F 1 ^ m
              = ∏ j ∈ Finset.Ico 1 (m + 1), Work.BW.succMinL F j :=
            ih (fun i h1 h2 => hL i h1 (by omega))
          have hM : (∏ i ∈ Finset.Ico 1 m,
                (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i))
              * Work.BW.succMinL F 1 = Work.BW.succMinL F m :=
            hratioIco m hm (fun i h1 h2 => ne_of_gt (hL i h1 (by omega)))
          have hR : Work.BW.succMinL F m
              * (Work.BW.succMinL F (m + 1) / Work.BW.succMinL F m)
              = Work.BW.succMinL F (m + 1) := by
            rw [mul_div_cancel₀ _ (ne_of_gt (hL m hm (by omega)))]
          have he : ((∏ i ∈ Finset.Ico 1 m,
                  (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (m - i))
                * (∏ i ∈ Finset.Ico 1 m,
                  (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i))
                * (Work.BW.succMinL F (m + 1) / Work.BW.succMinL F m))
                * (Work.BW.succMinL F 1 ^ m * Work.BW.succMinL F 1)
              = ((∏ i ∈ Finset.Ico 1 m,
                  (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (m - i))
                  * Work.BW.succMinL F 1 ^ m)
                * (((∏ i ∈ Finset.Ico 1 m,
                    (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i))
                    * Work.BW.succMinL F 1)
                  * (Work.BW.succMinL F (m + 1) / Work.BW.succMinL F m)) := by ring
          rw [h1, h2, pow_succ, he, hP, hM, hR]
  have htel : ∀ (q j : ℕ), 1 ≤ j → j ≤ n →
      (∏ i ∈ Finset.Ico 1 j,
          (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (n - i))
        * volume.real (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
            (Vset F 1))
      ≤ volume.real (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
          (Vset F j)) := by
    intro q j hj1 hjn
    induction j, hj1 using Nat.le_induction with
    | base => rw [Finset.Ico_self, Finset.prod_empty, one_mul]
    | succ i hi1 ih =>
        have hin : i + 1 ≤ n := by omega
        have hprev : i ≤ n := by omega
        have hstep := stage_step F hF q i hi1 hin
        have hd1 := stage_decomp F hF hflag q i i hi1 hprev hprev (by omega)
        have hd2 := stage_decomp F hF hflag q i (i + 1) (by omega) hin (le_of_lt hin) (by omega)
        have hcard : (0 : ℝ) ≤ ((rcubeHi n q i).card : ℝ) := Nat.cast_nonneg _
        have hih := ih hprev
        calc (∏ k ∈ Finset.Ico 1 (i + 1),
                (Work.BW.succMinL F (k + 1) / Work.BW.succMinL F k) ^ (n - k))
              * volume.real (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
                  (Vset F 1))
            = (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (n - i)
                * ((∏ k ∈ Finset.Ico 1 i,
                    (Work.BW.succMinL F (k + 1) / Work.BW.succMinL F k) ^ (n - k))
                  * volume.real (Work.BW.addSet
                      ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) (Vset F 1))) := by
              rw [Finset.prod_Ico_succ_top hi1, mul_assoc, mul_left_comm]
          _ ≤ (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (n - i)
                * volume.real (Work.BW.addSet
                    ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) (Vset F i)) := by
              refine mul_le_mul_of_nonneg_left hih ?_
              exact pow_nonneg (div_nonneg (le_of_lt (hLpos (i + 1) (by omega) hin))
                (le_of_lt (hLpos i hi1 hprev))) _
          _ ≤ volume.real (Work.BW.addSet
                ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) (Vset F (i + 1))) := by
              rw [hd1, hd2]
              calc (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (n - i)
                    * (((rcubeHi n q i).card : ℝ)
                      * volume.real (Work.BW.addSet
                          ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) (Vset F i)))
                  = ((rcubeHi n q i).card : ℝ)
                    * ((Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (n - i)
                      * volume.real (Work.BW.addSet
                          ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
                          (Vset F i))) := by ring
                _ ≤ ((rcubeHi n q i).card : ℝ)
                    * volume.real (Work.BW.addSet
                        ((rcubeLo n q i : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
                        (Vset F (i + 1))) := mul_le_mul_of_nonneg_left hstep hcard
  have key : ∀ q : ℕ,
      (∏ j : Fin n, Work.BW.succMinL F (j.1 + 1)) * volume.real (uBall F)
        ≤ (2 : ℝ) ^ n * ((2 * (q : ℝ) + 2 * R) / (2 * (q : ℝ) + 1)) ^ n := by
    intro q
    have hL1 : 0 < Work.BW.succMinL F 1 := hLpos 1 le_rfl hn
    have hA1 : volume.real (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
          (Vset F 1))
        = (2 * (q : ℝ) + 1) ^ n * (Work.BW.succMinL F 1 / 2) ^ n * volume.real (uBall F) := by
      have h := stage_decomp F hF hflag q 0 1 le_rfl hn (Nat.zero_le n) (by omega)
      rw [rcubeHi_zero, card_rcube, rcubeLo_zero, addSet_singleton_zero, Vset] at h
      rw [Vset, h, volume_real_smul (Work.BW.succMinL F 1 / 2) (by linarith) (uBall F)]
      rw [Nat.cast_pow, Nat.cast_add, Nat.cast_mul]
      ring
    have ht := htel q n hn le_rfl
    have hu := hupper q
    have hidn := hid n hLpos
    have hQfin : (∏ j ∈ Finset.Ico 1 (n + 1), Work.BW.succMinL F j)
        = ∏ j : Fin n, Work.BW.succMinL F (j.1 + 1) := by
      rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_fin_eq_prod_range]
      refine Finset.prod_congr rfl (fun i hi => ?_)
      rw [Finset.mem_range] at hi
      have h1 : (if h : i < n then Work.BW.succMinL F ((⟨i, h⟩ : Fin n).1 + 1) else 1)
          = Work.BW.succMinL F (i + 1) := by
        rw [dif_pos hi]
      rw [h1, show 1 + i = i + 1 by omega]
    set P : ℝ := ∏ i ∈ Finset.Ico 1 n,
      (Work.BW.succMinL F (i + 1) / Work.BW.succMinL F i) ^ (n - i) with hPdef
    set B : ℝ := (2 * (q : ℝ) + 1) ^ n with hBdef
    set C : ℝ := (2 * (q : ℝ) + 2 * R) ^ n with hCdef
    have hBpos : 0 < B := by rw [hBdef]; positivity
    have h1 : P * volume.real (Work.BW.addSet ((rcube n q : Finset (Fin n → ℝ)) : Set (Fin n → ℝ))
          (Vset F 1)) ≤ C := by
      exact le_trans ht hu
    rw [hA1] at h1
    have h3 : (∏ j : Fin n, Work.BW.succMinL F (j.1 + 1)) * volume.real (uBall F) * B
        ≤ (2 : ℝ) ^ n * C := by
      have h2n : (Work.BW.succMinL F 1 / 2) ^ n * (2 : ℝ) ^ n = Work.BW.succMinL F 1 ^ n := by
        rw [← mul_pow, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
      have hpu : P * Work.BW.succMinL F 1 ^ n
          = ∏ j : Fin n, Work.BW.succMinL F (j.1 + 1) := by
        rw [← hQfin, hPdef]
        exact hidn
      have h := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n)
      have he : (P * (B * (Work.BW.succMinL F 1 / 2) ^ n * volume.real (uBall F)))
            * (2 : ℝ) ^ n
          = (∏ j : Fin n, Work.BW.succMinL F (j.1 + 1)) * volume.real (uBall F) * B := by
        rw [← hpu, ← h2n]
        ring
      rw [he] at h
      rwa [mul_comm C ((2 : ℝ) ^ n)] at h
    have hCB : ((2 * (q : ℝ) + 2 * R) / (2 * (q : ℝ) + 1)) ^ n = C / B := by
      rw [hBdef, hCdef, div_pow]
    rw [hCB, mul_div_assoc', le_div_iff₀ hBpos]
    exact h3
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h2n : (1 : ℝ) < (2 : ℝ) ^ n := one_lt_pow₀ (by norm_num) (Nat.pos_iff_ne_zero.mp hn)
  have h2n1 : 0 < (2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1) :=
    mul_pos (by linarith) (by linarith)
  set ε : ℝ := min 1 (δ / ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1))) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min one_pos (div_pos hδ h2n1)
  have hε1 : ε ≤ 1 := by rw [hεdef]; exact min_le_left _ _
  have hεδ : ε ≤ δ / ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1)) := by
    rw [hεdef]; exact min_le_right _ _
  obtain ⟨q, hq⟩ : ∃ q : ℕ, R / ε ≤ (q : ℝ) := exists_nat_ge (R / ε)
  have hqε : R ≤ (q : ℝ) * ε := (div_le_iff₀ hεpos).mp hq
  have hratio : (2 * (q : ℝ) + 2 * R) / (2 * (q : ℝ) + 1) ≤ 1 + ε := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ) + 1)]
    nlinarith [hqε, hεpos, (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))]
  have hpow : ∀ m : ℕ, (1 + ε) ^ m ≤ 1 + ((2 : ℝ) ^ m - 1) * ε := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        have h2k : (0 : ℝ) ≤ (2 : ℝ) ^ k - 1 := by
          have h : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
          linarith
        have hle : ((2 : ℝ) ^ k - 1) * ε ≤ (2 : ℝ) ^ k - 1 := mul_le_of_le_one_right h2k hε1
        calc (1 + ε) ^ (k + 1) = (1 + ε) ^ k * (1 + ε) := by rw [pow_succ]
          _ ≤ (1 + ((2 : ℝ) ^ k - 1) * ε) * (1 + ε) :=
              mul_le_mul_of_nonneg_right ih (by linarith)
          _ = 1 + ε + ((2 : ℝ) ^ k - 1) * ε + ((2 : ℝ) ^ k - 1) * ε * ε := by ring
          _ ≤ 1 + ((2 : ℝ) ^ (k + 1) - 1) * ε := by
              rw [pow_succ]
              nlinarith [hle, h2k, hεpos.le, hε1]
  have hrpow : ((2 * (q : ℝ) + 2 * R) / (2 * (q : ℝ) + 1)) ^ n
      ≤ 1 + ((2 : ℝ) ^ n - 1) * ε := by
    refine le_trans (pow_le_pow_left₀ ?_ hratio n) (hpow n)
    exact div_nonneg (by linarith [hRnn, (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))])
      (by linarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))])
  have hfin : (2 : ℝ) ^ n * ((2 * (q : ℝ) + 2 * R) / (2 * (q : ℝ) + 1)) ^ n
      ≤ (2 : ℝ) ^ n + δ := by
    have hb : (2 : ℝ) ^ n * (1 + ((2 : ℝ) ^ n - 1) * ε)
        = (2 : ℝ) ^ n + ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1)) * ε := by ring
    have hd : ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1)) * ε ≤ δ := by
      calc ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1)) * ε
          ≤ ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1))
              * (δ / ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1))) :=
            mul_le_mul_of_nonneg_left hεδ (le_of_lt h2n1)
        _ = δ := by rw [mul_div_cancel₀ _ (ne_of_gt h2n1)]
    calc (2 : ℝ) ^ n * ((2 * (q : ℝ) + 2 * R) / (2 * (q : ℝ) + 1)) ^ n
        ≤ (2 : ℝ) ^ n * (1 + ((2 : ℝ) ^ n - 1) * ε) :=
          mul_le_mul_of_nonneg_left hrpow (by positivity)
      _ = (2 : ℝ) ^ n + ((2 : ℝ) ^ n * ((2 : ℝ) ^ n - 1)) * ε := hb
      _ ≤ (2 : ℝ) ^ n + δ := by linarith
  linarith [key q, hfin]

end Work.BW.KWM
