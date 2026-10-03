import Mathlib
import Submission.Work.Analysis.CzShift.Defs

/-!
# Lacunary sums: counting and geometric bounds

For a finite `lam`-lacunary family of positive scales `σ : ι → ℝ` on `D : Finset ι`
(`LacunaryFam lam D σ`), any two distinct elements of `D` are separated by a factor at
least `lam > 1`.  Consequently

* at most `1 + log (b/a) / log lam` of them lie in any window `[a, b)` with `0 < a ≤ b`;
* the weighted tail sum `∑_{σ i ≥ L} L / σ i`, and the weighted head sum
  `∑_{σ i < L} σ i / L`, are both bounded by the lacunary geometric series
  `1 / (1 - 1/lam)`.

Each estimate is proved by strong induction on `D`, peeling off the extremal element of
the filtered family: the remaining elements are then pushed into the rescaled window
(`a ↦ lam * a`, resp. `L ↦ lam * L`, resp. `L ↦ L / lam`), and the induction closes with
the exact identity `1 + (1/lam) * 1/(1 - 1/lam) = 1/(1 - 1/lam)`.
-/

namespace Work.Analysis.CzShift

set_option autoImplicit false

variable {ι : Type*}

/-! ### Elementary consequences of lacunarity -/

/-- In a lacunary family, two distinct elements ordered as `σ i ≤ σ j` are separated by a
factor `lam`. -/
private theorem lacunary_gap {lam : ℝ} {D : Finset ι} {σ : ι → ℝ} (hlac : LacunaryFam lam D σ)
    {i j : ι} (hi : i ∈ D) (hj : j ∈ D) (hij : i ≠ j) (hle : σ i ≤ σ j) :
    lam * σ i ≤ σ j := by
  simpa [min_eq_left hle, max_eq_right hle] using hlac.2 i hi j hj hij

/-- Lacunarity is preserved when passing to a subfamily. -/
private theorem lacunary_subset {lam : ℝ} {D E : Finset ι} {σ : ι → ℝ} (hED : E ⊆ D)
    (hlac : LacunaryFam lam D σ) : LacunaryFam lam E σ :=
  ⟨fun i hi => hlac.1 i (hED hi), fun i hi j hj hij => hlac.2 i (hED hi) j (hED hj) hij⟩

/-- Lacunarity is preserved by removing an element. -/
private theorem lacunary_erase {lam : ℝ} {D : Finset ι} {σ : ι → ℝ} [DecidableEq ι] (i₀ : ι)
    (hlac : LacunaryFam lam D σ) : LacunaryFam lam (D.erase i₀) σ :=
  lacunary_subset (Finset.erase_subset i₀ D) hlac

/-! ### Elementary real identities used to close the inductions -/

/-- The lacunary geometric identity: `1 + t/(1-t) = 1/(1-t)` for `t < 1`. -/
private theorem one_add_mul_one_div {t : ℝ} (ht : t < 1) :
    (1 : ℝ) + t * (1 / (1 - t)) = 1 / (1 - t) := by
  have ht1 : (1 : ℝ) - t ≠ 0 := by linarith
  have hC : (1 / (1 - t)) * (1 - t) = 1 := by rw [one_div, inv_mul_cancel₀ ht1]
  refine mul_right_cancel₀ ht1 ?_
  rw [add_mul, one_mul, hC, mul_assoc, hC, mul_one]
  ring

/-- Rescaling identity for the tail sums. -/
private theorem inv_mul_mul_div {lam L s : ℝ} (hlam : lam ≠ 0) :
    lam⁻¹ * (lam * L / s) = L / s := by
  rw [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hlam, one_mul]

/-- Rescaling identity for the tail sums, with the factor on the right. -/
private theorem mul_inv_mul_div {lam L s : ℝ} (hlam : lam ≠ 0) :
    (lam * L / s) * lam⁻¹ = L / s := by
  rw [mul_comm (lam * L / s) lam⁻¹, inv_mul_mul_div hlam]

/-- Rescaling identity for the head sums. -/
private theorem inv_mul_div_div {lam L s : ℝ} (hlam : lam ≠ 0) :
    lam⁻¹ * (s / (L / lam)) = s / L := by
  rw [div_div_eq_mul_div, ← mul_div_assoc, mul_left_comm lam⁻¹ s lam, inv_mul_cancel₀ hlam,
    mul_one]

/-- Rescaling identity for the head sums, with the factor on the right. -/
private theorem mul_inv_div_div {lam L s : ℝ} (hlam : lam ≠ 0) :
    (s / (L / lam)) * lam⁻¹ = s / L := by
  rw [mul_comm (s / (L / lam)) lam⁻¹, inv_mul_div_div hlam]

/-- The logarithm of a window rescaled by `lam`. -/
private theorem log_div_mul {lam b a : ℝ} (hlam : lam ≠ 0) (ha : 0 < a) (hb : 0 < b) :
    Real.log (b / (lam * a)) = Real.log (b / a) - Real.log lam := by
  have hdiv : b / (lam * a) = (b / a) / lam := by rw [div_div, mul_comm lam a]
  rw [hdiv, Real.log_div (div_ne_zero (ne_of_gt hb) (ne_of_gt ha)) hlam]

/-- The elementary step of the counting bound. -/
private theorem log_step (X Y : ℝ) (hY : Y ≠ 0) :
    (1 + (X - Y) / Y) + 1 = 1 + X / Y := by
  rw [sub_div, div_self hY]
  ring

/-! ### Counting the elements of a lacunary family in a window -/

private theorem card_filter_le_aux {lam : ℝ} (hlam : 1 < lam) (σ : ι → ℝ) :
    ∀ D : Finset ι, LacunaryFam lam D σ → ∀ a b : ℝ, 0 < a → a ≤ b →
      ((D.filter (fun i => a ≤ σ i ∧ σ i < b)).card : ℝ) ≤
        1 + Real.log (b / a) / Real.log lam := by
  intro D
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    intro hlac a b ha hab
    classical
    have hlampos : 0 < lam := lt_trans zero_lt_one hlam
    have hloglampos : 0 < Real.log lam := Real.log_pos hlam
    have hbpos : 0 < b := lt_of_lt_of_le ha hab
    have hlogba : 0 ≤ Real.log (b / a) := by
      rw [← Real.log_one]
      exact Real.log_le_log one_pos ((one_le_div ha).mpr hab)
    by_cases hS : (D.filter (fun i => a ≤ σ i ∧ σ i < b)).Nonempty
    · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ σ hS
      have hi₀D : i₀ ∈ D := Finset.mem_of_mem_filter i₀ hi₀
      have hai₀ : a ≤ σ i₀ := (Finset.mem_filter.mp hi₀).2.1
      have hi₀b : σ i₀ < b := (Finset.mem_filter.mp hi₀).2.2
      have hpeel : ∀ i ∈ D.filter (fun i => a ≤ σ i ∧ σ i < b), i ≠ i₀ → lam * σ i₀ ≤ σ i := by
        intro i hiS hne
        exact lacunary_gap hlac hi₀D (Finset.mem_of_mem_filter i hiS) (Ne.symm hne) (hmin i hiS)
      by_cases hba : b ≤ lam * a
      · -- at most one element lies in the window
        have hsub : D.filter (fun i => a ≤ σ i ∧ σ i < b) ⊆ {i₀} := by
          intro i hi
          by_contra hmem
          have hne : i ≠ i₀ := fun h => hmem (Finset.mem_singleton.mpr h)
          have h1 : lam * a ≤ σ i :=
            le_trans (mul_le_mul_of_nonneg_left hai₀ hlampos.le) (hpeel i hi hne)
          have h2 : σ i < b := (Finset.mem_filter.mp hi).2.2
          linarith
        have hcard1 : ((D.filter (fun i => a ≤ σ i ∧ σ i < b)).card : ℝ) ≤ 1 := by
          have hle := Finset.card_le_card hsub
          rw [Finset.card_singleton] at hle
          exact_mod_cast hle
        have hlogdiv : 0 ≤ Real.log (b / a) / Real.log lam := div_nonneg hlogba hloglampos.le
        linarith
      · -- main case
        simp only [not_le] at hba
        have hlamapos : 0 < lam * a := mul_pos hlampos ha
        have hbab : lam * a ≤ b := hba.le
        have hsubst : (D.filter (fun i => a ≤ σ i ∧ σ i < b)).erase i₀ ⊆
            (D.erase i₀).filter (fun i => lam * a ≤ σ i ∧ σ i < b) := by
          intro i hi
          obtain ⟨hne, hiS⟩ := Finset.mem_erase.mp hi
          have h1 : lam * a ≤ σ i :=
            le_trans (mul_le_mul_of_nonneg_left hai₀ hlampos.le) (hpeel i hiS hne)
          have h2 : σ i < b := (Finset.mem_filter.mp hiS).2.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_of_mem_filter i hiS⟩,
            h1, h2⟩
        have hcardstep : ((D.filter (fun i => a ≤ σ i ∧ σ i < b)).card : ℝ) ≤
            (((D.erase i₀).filter (fun i => lam * a ≤ σ i ∧ σ i < b)).card : ℝ) + 1 := by
          have h1 : (D.filter (fun i => a ≤ σ i ∧ σ i < b)).card =
              ((D.filter (fun i => a ≤ σ i ∧ σ i < b)).erase i₀).card + 1 :=
            (Finset.card_erase_add_one hi₀).symm
          have h2 : (((D.filter (fun i => a ≤ σ i ∧ σ i < b)).erase i₀).card : ℝ) ≤
              (((D.erase i₀).filter (fun i => lam * a ≤ σ i ∧ σ i < b)).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsubst
          rw [h1]
          push_cast
          linarith
        have hIH : (((D.erase i₀).filter (fun i => lam * a ≤ σ i ∧ σ i < b)).card : ℝ) ≤
            1 + Real.log (b / (lam * a)) / Real.log lam :=
          ih (D.erase i₀) (Finset.erase_ssubset hi₀D) (lacunary_erase i₀ hlac) (lam * a) b
            hlamapos hbab
        calc ((D.filter (fun i => a ≤ σ i ∧ σ i < b)).card : ℝ)
            ≤ (((D.erase i₀).filter (fun i => lam * a ≤ σ i ∧ σ i < b)).card : ℝ) + 1 :=
              hcardstep
          _ ≤ (1 + Real.log (b / (lam * a)) / Real.log lam) + 1 := by linarith
          _ = 1 + Real.log (b / a) / Real.log lam := by
              rw [log_div_mul (ne_of_gt hlampos) ha hbpos]
              exact log_step (Real.log (b / a)) (Real.log lam) (ne_of_gt hloglampos)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty, Nat.cast_zero]
      have hlogdiv : 0 ≤ Real.log (b / a) / Real.log lam := div_nonneg hlogba hloglampos.le
      linarith

/-! ### The tail sum `∑_{σ i ≥ L} L / σ i` -/

private theorem tail_sum_le_aux {lam : ℝ} (hlam : 1 < lam) (σ : ι → ℝ) :
    ∀ D : Finset ι, LacunaryFam lam D σ → ∀ L : ℝ, 0 < L →
      ∑ i ∈ D.filter (fun i => L ≤ σ i), L / σ i ≤ 1 / (1 - lam⁻¹) := by
  intro D
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    intro hlac L hL
    classical
    have hlampos : 0 < lam := lt_trans zero_lt_one hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlampos
    have hCpos : 0 < 1 / (1 - lam⁻¹) :=
      div_pos one_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam))
    by_cases hS : (D.filter (fun i => L ≤ σ i)).Nonempty
    · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _ σ hS
      have hi₀D : i₀ ∈ D := Finset.mem_of_mem_filter i₀ hi₀
      have hi₀L : L ≤ σ i₀ := (Finset.mem_filter.mp hi₀).2
      have hσi₀pos : 0 < σ i₀ := hlac.1 i₀ hi₀D
      have hpeel : ∀ i ∈ D.filter (fun i => L ≤ σ i), i ≠ i₀ → lam * L ≤ σ i := by
        intro i hiS hne
        have hgap : lam * σ i₀ ≤ σ i :=
          lacunary_gap hlac hi₀D (Finset.mem_of_mem_filter i hiS) (Ne.symm hne) (hmin i hiS)
        exact le_trans (mul_le_mul_of_nonneg_left hi₀L hlampos.le) hgap
      have hE2 : (D.erase i₀).filter (fun i => L ≤ σ i) =
          (D.erase i₀).filter (fun i => lam * L ≤ σ i) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hi, hLi⟩
          exact ⟨hi, hpeel i (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hi).2, hLi⟩)
            (Finset.mem_erase.mp hi).1⟩
        · rintro ⟨hi, hlt⟩
          exact ⟨hi, le_trans (by nlinarith [hL, hlam] : L ≤ lam * L) hlt⟩
      have hsplit : ∑ i ∈ D.filter (fun i => L ≤ σ i), L / σ i =
          L / σ i₀ + ∑ i ∈ (D.filter (fun i => L ≤ σ i)).erase i₀, L / σ i := by
        simpa [add_comm] using (Finset.add_sum_erase (D.filter (fun i => L ≤ σ i))
          (fun i => L / σ i) hi₀).symm
      have hT1 : (D.filter (fun i => L ≤ σ i)).erase i₀ =
          (D.erase i₀).filter (fun i => L ≤ σ i) := by
        ext i
        simp only [Finset.mem_erase, Finset.mem_filter]
        tauto
      have hres : ∑ i ∈ (D.erase i₀).filter (fun i => lam * L ≤ σ i), L / σ i =
          (∑ i ∈ (D.erase i₀).filter (fun i => lam * L ≤ σ i), lam * L / σ i) * lam⁻¹ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (mul_inv_mul_div hlamne).symm
      have hIH : ∑ i ∈ (D.erase i₀).filter (fun i => lam * L ≤ σ i), lam * L / σ i ≤
          1 / (1 - lam⁻¹) :=
        ih (D.erase i₀) (Finset.erase_ssubset hi₀D) (lacunary_erase i₀ hlac) (lam * L)
          (mul_pos hlampos hL)
      have hkey : (1 : ℝ) + lam⁻¹ * (1 / (1 - lam⁻¹)) = 1 / (1 - lam⁻¹) :=
        one_add_mul_one_div (inv_lt_one_of_one_lt₀ hlam)
      calc ∑ i ∈ D.filter (fun i => L ≤ σ i), L / σ i
          = L / σ i₀ + (∑ i ∈ (D.erase i₀).filter (fun i => lam * L ≤ σ i),
              lam * L / σ i) * lam⁻¹ := by rw [hsplit, hT1, hE2, hres]
        _ ≤ 1 + (1 / (1 - lam⁻¹)) * lam⁻¹ := by
            have h1 : L / σ i₀ ≤ 1 := (div_le_one hσi₀pos).mpr hi₀L
            have h2 : (∑ i ∈ (D.erase i₀).filter (fun i => lam * L ≤ σ i),
                lam * L / σ i) * lam⁻¹ ≤ (1 / (1 - lam⁻¹)) * lam⁻¹ :=
              mul_le_mul_of_nonneg_right hIH (inv_nonneg.mpr hlampos.le)
            linarith
        _ = 1 / (1 - lam⁻¹) := by
            rw [mul_comm (1 / (1 - lam⁻¹)) lam⁻¹]
            exact hkey
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp only [Finset.sum_empty]
      exact hCpos.le

/-! ### The head sum `∑_{σ i < L} σ i / L` -/

private theorem head_sum_le_aux {lam : ℝ} (hlam : 1 < lam) (σ : ι → ℝ) :
    ∀ D : Finset ι, LacunaryFam lam D σ → ∀ L : ℝ, 0 < L →
      ∑ i ∈ D.filter (fun i => σ i < L), σ i / L ≤ 1 / (1 - lam⁻¹) := by
  intro D
  induction D using Finset.strongInductionOn with
  | _ D ih =>
    intro hlac L hL
    classical
    have hlampos : 0 < lam := lt_trans zero_lt_one hlam
    have hlamne : lam ≠ 0 := ne_of_gt hlampos
    have hCpos : 0 < 1 / (1 - lam⁻¹) :=
      div_pos one_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hlam))
    by_cases hS : (D.filter (fun i => σ i < L)).Nonempty
    · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ σ hS
      have hi₀D : i₀ ∈ D := Finset.mem_of_mem_filter i₀ hi₀
      have hi₀L : σ i₀ < L := (Finset.mem_filter.mp hi₀).2
      have hpeel : ∀ i ∈ D.filter (fun i => σ i < L), i ≠ i₀ → σ i < L / lam := by
        intro i hiS hne
        have hgap : lam * σ i ≤ σ i₀ :=
          lacunary_gap hlac (Finset.mem_of_mem_filter i hiS) hi₀D hne (hmax i hiS)
        have hle : σ i ≤ σ i₀ / lam := by
          rw [le_div_iff₀ hlampos]
          linarith
        have hlt : σ i₀ / lam < L / lam := div_lt_div_of_pos_right hi₀L hlampos
        linarith
      have hE2 : (D.erase i₀).filter (fun i => σ i < L) =
          (D.erase i₀).filter (fun i => σ i < L / lam) := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hi, hLi⟩
          exact ⟨hi, hpeel i (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hi).2, hLi⟩)
            (Finset.mem_erase.mp hi).1⟩
        · rintro ⟨hi, hlt⟩
          have hltL : L / lam < L := by
            rw [div_lt_iff₀ hlampos]
            nlinarith [hL, hlam]
          exact ⟨hi, lt_trans hlt hltL⟩
      have hsplit : ∑ i ∈ D.filter (fun i => σ i < L), σ i / L =
          σ i₀ / L + ∑ i ∈ (D.filter (fun i => σ i < L)).erase i₀, σ i / L := by
        simpa [add_comm] using (Finset.add_sum_erase (D.filter (fun i => σ i < L))
          (fun i => σ i / L) hi₀).symm
      have hT1 : (D.filter (fun i => σ i < L)).erase i₀ =
          (D.erase i₀).filter (fun i => σ i < L) := by
        ext i
        simp only [Finset.mem_erase, Finset.mem_filter]
        tauto
      have hres : ∑ i ∈ (D.erase i₀).filter (fun i => σ i < L / lam), σ i / L =
          (∑ i ∈ (D.erase i₀).filter (fun i => σ i < L / lam), σ i / (L / lam)) * lam⁻¹ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (mul_inv_div_div hlamne).symm
      have hIH : ∑ i ∈ (D.erase i₀).filter (fun i => σ i < L / lam), σ i / (L / lam) ≤
          1 / (1 - lam⁻¹) :=
        ih (D.erase i₀) (Finset.erase_ssubset hi₀D) (lacunary_erase i₀ hlac) (L / lam)
          (div_pos hL hlampos)
      have hkey : (1 : ℝ) + lam⁻¹ * (1 / (1 - lam⁻¹)) = 1 / (1 - lam⁻¹) :=
        one_add_mul_one_div (inv_lt_one_of_one_lt₀ hlam)
      calc ∑ i ∈ D.filter (fun i => σ i < L), σ i / L
          = σ i₀ / L + (∑ i ∈ (D.erase i₀).filter (fun i => σ i < L / lam),
              σ i / (L / lam)) * lam⁻¹ := by rw [hsplit, hT1, hE2, hres]
        _ ≤ 1 + (1 / (1 - lam⁻¹)) * lam⁻¹ := by
            have h1 : σ i₀ / L ≤ 1 := (div_le_one hL).mpr hi₀L.le
            have h2 : (∑ i ∈ (D.erase i₀).filter (fun i => σ i < L / lam),
                σ i / (L / lam)) * lam⁻¹ ≤ (1 / (1 - lam⁻¹)) * lam⁻¹ :=
              mul_le_mul_of_nonneg_right hIH (inv_nonneg.mpr hlampos.le)
            linarith
        _ = 1 / (1 - lam⁻¹) := by
            rw [mul_comm (1 / (1 - lam⁻¹)) lam⁻¹]
            exact hkey
    · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
      simp only [Finset.sum_empty]
      exact hCpos.le

theorem lacunary_sums {ι : Type*} (D : Finset ι) (σ : ι → ℝ) {lam : ℝ} (hlam : 1 < lam)
    (hlac : LacunaryFam lam D σ) :
    (∀ a b : ℝ, 0 < a → a ≤ b →
      ((D.filter (fun i => a ≤ σ i ∧ σ i < b)).card : ℝ)
        ≤ 1 + Real.log (b / a) / Real.log lam) ∧
    (∀ L : ℝ, 0 < L →
      ∑ i ∈ D.filter (fun i => L ≤ σ i), L / σ i ≤ 1 / (1 - lam⁻¹)) ∧
    (∀ L : ℝ, 0 < L →
      ∑ i ∈ D.filter (fun i => σ i < L), σ i / L ≤ 1 / (1 - lam⁻¹)) :=
  ⟨card_filter_le_aux hlam σ D hlac, tail_sum_le_aux hlam σ D hlac, head_sum_le_aux hlam σ D hlac⟩

end Work.Analysis.CzShift
