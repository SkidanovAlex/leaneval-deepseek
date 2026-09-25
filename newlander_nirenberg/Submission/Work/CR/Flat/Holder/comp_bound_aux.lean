import Mathlib
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.BilinRHS
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le

namespace Work.CR.Flat.Holder

open scoped NNReal ENNReal
open Set

/-! ### Auxiliary estimates for composite `C^{k,α}` norms -/

/-- A Lipschitz map raises the power `α` at most by the Lipschitz constant to the `α`. -/
lemma norm_sub_rpow_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X} {L α : ℝ}
    (hα : 0 < α) (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) :
    ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ^ α ≤ (max L 0) ^ α * ‖x - y‖ ^ α := by
  intro x hx y hy
  have h1 : ‖Φ x - Φ y‖ ≤ max L 0 * ‖x - y‖ := by
    rcases eq_or_ne (Φ x) (Φ y) with h | h
    · rw [h, sub_self, norm_zero]; positivity
    · have hxy : x ≠ y := fun he => h (by rw [he])
      have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero_of_ne hxy)
      have hL0 : 0 ≤ L := by
        by_contra hlt
        push Not at hlt
        have := hL x hx y hy
        nlinarith [norm_nonneg (Φ x - Φ y), hpos]
      rw [max_eq_left hL0]
      exact hL x hx y hy
  calc ‖Φ x - Φ y‖ ^ α ≤ (max L 0 * ‖x - y‖) ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) h1 (le_of_lt hα)
    _ = (max L 0) ^ α * ‖x - y‖ ^ α := Real.mul_rpow (le_max_right L 0) (norm_nonneg _)

/-- Faà di Bruno's formula, written as a sum over ordered finite partitions. -/
lemma iteratedFDerivWithin_comp_eq_sum {X Y A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {Φ : X → Y} {s : Set X} {t : Set Y} {u : Y → A} {n : ℕ} {x : X}
    (hu : ContDiffWithinAt ℝ (n : WithTop ℕ∞) u t (Φ x))
    (hΦc : ContDiffWithinAt ℝ (n : WithTop ℕ∞) Φ s x)
    (ht : UniqueDiffOn ℝ t) (hs : UniqueDiffOn ℝ s) (hx : x ∈ s) (hst : Set.MapsTo Φ s t) :
    iteratedFDerivWithin ℝ n (u ∘ Φ) s x
      = ∑ c : OrderedFinpartition n,
          c.compAlongOrderedFinpartition (iteratedFDerivWithin ℝ c.length u t (Φ x))
            (fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x) := by
  rw [iteratedFDerivWithin_comp hu hΦc ht hs hx hst (le_refl _)]
  rfl

/-- Difference estimate for a single term of the Faà di Bruno expansion. -/
lemma partition_comp_sub_le {X Y A : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {Φ : X → Y} {s : Set X} {t : Set Y} {u : Y → A} {α : ℝ}
    {n : ℕ} (c : OrderedFinpartition n) {x y : X}
    {Dstar Estar Lα ai bi : ℝ}
    (h1 : ‖iteratedFDerivWithin ℝ c.length u t (Φ x)‖ ≤ ai)
    (h2 : ‖iteratedFDerivWithin ℝ c.length u t (Φ x) - iteratedFDerivWithin ℝ c.length u t (Φ y)‖
            ≤ bi * ‖Φ x - Φ y‖ ^ α)
    (h3 : ‖(fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x)‖ ≤ Dstar)
    (h4 : ‖(fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s y)‖ ≤ Dstar)
    (h5 : ‖(fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x)
            - (fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s y)‖ ≤ Estar * ‖x - y‖ ^ α)
    (h6 : ‖Φ x - Φ y‖ ^ α ≤ Lα * ‖x - y‖ ^ α)
    (hai : 0 ≤ ai) (hbi : 0 ≤ bi) (hDs : 0 ≤ Dstar) (hEs : 0 ≤ Estar) (hLα : 0 ≤ Lα)
    (hxy : x ≠ y) :
    ‖c.compAlongOrderedFinpartition (iteratedFDerivWithin ℝ c.length u t (Φ x))
        (fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x)
      - c.compAlongOrderedFinpartition (iteratedFDerivWithin ℝ c.length u t (Φ y))
        (fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s y)‖ / ‖x - y‖ ^ α
    ≤ ai * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + bi * Lα * Dstar ^ c.length := by
  set g1 : (m : Fin c.length) → X [×c.partSize m]→L[ℝ] Y :=
    fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x with hg1
  set g2 : (m : Fin c.length) → X [×c.partSize m]→L[ℝ] Y :=
    fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s y with hg2
  set f1 : Y [×c.length]→L[ℝ] A := iteratedFDerivWithin ℝ c.length u t (Φ x) with hf1
  set f2 : Y [×c.length]→L[ℝ] A := iteratedFDerivWithin ℝ c.length u t (Φ y) with hf2
  simp only [hg1, hg2, hf1, hf2] at h1 h2 h3 h4 h5 ⊢
  have hmain := c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le f1 f2 g1 g2
  have hprod : (∏ i : Fin c.length, ‖g2 i‖) ≤ Dstar ^ c.length := by
    calc (∏ i : Fin c.length, ‖g2 i‖) ≤ ∏ _i : Fin c.length, Dstar := by
          gcongr with i
          exact (norm_le_pi_norm g2 i).trans h4
      _ = Dstar ^ c.length := by simp [Finset.prod_const, Fintype.card_fin]
  have hmax : (max ‖g1‖ ‖g2‖) ^ (c.length - 1) ≤ Dstar ^ (c.length - 1) :=
    pow_le_pow_left₀ (by positivity) (max_le h3 h4) _
  have hxypos : 0 < ‖x - y‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero_of_ne hxy)) _
  have hterm1 : ‖f1‖ * (c.length : ℝ) * (max ‖g1‖ ‖g2‖) ^ (c.length - 1) * ‖g1 - g2‖
      ≤ ai * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar * ‖x - y‖ ^ α := by
    calc ‖f1‖ * (c.length : ℝ) * (max ‖g1‖ ‖g2‖) ^ (c.length - 1) * ‖g1 - g2‖
        ≤ ai * (c.length : ℝ) * Dstar ^ (c.length - 1) * (Estar * ‖x - y‖ ^ α) := by gcongr
      _ = ai * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar * ‖x - y‖ ^ α := by ring
  have hterm2 : ‖f1 - f2‖ * (∏ i : Fin c.length, ‖g2 i‖)
      ≤ bi * Lα * Dstar ^ c.length * ‖x - y‖ ^ α := by
    calc ‖f1 - f2‖ * (∏ i : Fin c.length, ‖g2 i‖)
        ≤ (bi * ‖Φ x - Φ y‖ ^ α) * Dstar ^ c.length := by gcongr
      _ ≤ (bi * (Lα * ‖x - y‖ ^ α)) * Dstar ^ c.length := by gcongr
      _ = bi * Lα * Dstar ^ c.length * ‖x - y‖ ^ α := by ring
  rw [div_le_iff₀ hxypos]
  calc ‖c.compAlongOrderedFinpartition f1 g1 - c.compAlongOrderedFinpartition f2 g2‖
      ≤ ‖f1‖ * ↑c.length * (max ‖g1‖ ‖g2‖) ^ (c.length - 1) * ‖g1 - g2‖
        + ‖f1 - f2‖ * ∏ i, ‖g2 i‖ := hmain
    _ ≤ ai * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar * ‖x - y‖ ^ α
        + bi * Lα * Dstar ^ c.length * ‖x - y‖ ^ α := add_le_add hterm1 hterm2
    _ = (ai * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + bi * Lα * Dstar ^ c.length)
          * ‖x - y‖ ^ α := by ring

/-! ### The composition bound -/

theorem comp_bound_aux {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {Φ : X → Y} {s : Set X} {t : Set Y}
    (hst : Set.MapsTo Φ s t) (hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) Φ s)
    (hs : IsOpen s) (ht : IsOpen t) (L : ℝ)
    (hL : ∀ x ∈ s, ∀ y ∈ s, ‖Φ x - Φ y‖ ≤ L * ‖x - y‖) (α : ℝ) (hα : 0 < α)
    (D : ℕ → ℝ) (hD : ∀ (k : ℕ) (x : X), x ∈ s → ‖iteratedFDerivWithin ℝ k Φ s x‖ ≤ D k)
    (E : ℕ → ℝ)
    (hE : ∀ (k : ℕ) (x : X), x ∈ s → ∀ (y : X), y ∈ s →
      ‖iteratedFDerivWithin ℝ k Φ s x - iteratedFDerivWithin ℝ k Φ s y‖ ≤ E k * ‖x - y‖ ^ α) :
    ∀ k : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ (A : Type*) [NormedAddCommGroup A] [NormedSpace ℝ A]
      (u : Y → A), (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) u t) →
      (∑ i ∈ Finset.range (k + 1),
          (Work.CR.Flat.Holder.iDN i (u ∘ Φ) s + Work.CR.Flat.Holder.hSN i α (u ∘ Φ) s))
        ≤ ENNReal.ofReal c
          * (∑ i ∈ Finset.range (k + 1),
              (Work.CR.Flat.Holder.iDN i u t + Work.CR.Flat.Holder.hSN i α u t)) := by
  intro k
  set Dstar : ℝ := max 1 (∑ j ∈ Finset.range (k + 1), |D j|) with hDstar
  set Estar : ℝ := ∑ j ∈ Finset.range (k + 1), |E j| with hEstar
  set Lα : ℝ := (max L 0) ^ α with hLαdef
  set cstA : ℕ → ℝ := fun n => (n.factorial : ℝ) * Dstar ^ n with hcstA
  set cstR : ℕ → ℝ := fun n => 1 + ∑ c : OrderedFinpartition n,
      ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + Lα * Dstar ^ c.length) with hcstR
  have hDs1 : 1 ≤ Dstar := by rw [hDstar]; exact le_max_left _ _
  have hDs0 : 0 ≤ Dstar := le_trans zero_le_one hDs1
  have hEs0 : 0 ≤ Estar := by rw [hEstar]; positivity
  have hLα0 : 0 ≤ Lα := by
    rw [hLαdef]; exact Real.rpow_nonneg (le_max_right L 0) α
  have hDle : ∀ j, j ≤ k → D j ≤ Dstar := by
    intro j hj
    rw [hDstar]
    refine le_trans ?_ (le_max_right _ _)
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun j => |D j|) (fun i _ => abs_nonneg (D i))
      (Finset.mem_range.mpr (by omega))
  have hEle : ∀ j, j ≤ k → E j ≤ Estar := by
    intro j hj
    rw [hEstar]
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun j => |E j|) (fun i _ => abs_nonneg (E i))
      (Finset.mem_range.mpr (by omega))
  have hA0 : ∀ n, 0 < cstA n := by
    intro n; rw [hcstA]; positivity
  have hR0 : ∀ n, 0 < cstR n := by
    intro n; rw [hcstR]
    have h : 0 ≤ ∑ c : OrderedFinpartition n,
        ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + Lα * Dstar ^ c.length) := by
      positivity
    linarith
  refine ⟨∑ n ∈ Finset.range (k + 1), (cstA n + cstR n), ?_, ?_⟩
  · exact Finset.sum_nonneg fun n _ => add_nonneg (le_of_lt (hA0 n)) (le_of_lt (hR0 n))
  · intro A instA instAs u hu
    set S : ℝ≥0∞ := ∑ i ∈ Finset.range (k + 1), (iDN i u t + hSN i α u t) with hS
    set ai : ℕ → ℝ := fun i => (iDN i u t).toReal with hai
    set bi : ℕ → ℝ := fun i => (hSN i α u t).toReal with hbi
    have hSle : ∀ i, i ≤ k → iDN i u t ≤ S ∧ hSN i α u t ≤ S := by
      intro i hi
      have hmem : i ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have hsingle := Finset.single_le_sum
        (f := fun i => iDN i u t + hSN i α u t) (fun j _ => by positivity) hmem
      constructor
      · rw [hS]; exact le_trans (le_add_of_nonneg_right (by positivity : (0:ℝ≥0∞) ≤ hSN i α u t)) hsingle
      · rw [hS]; exact le_trans (le_add_of_nonneg_left (by positivity : (0:ℝ≥0∞) ≤ iDN i u t)) hsingle
    have hIDN : ∀ n, n ≤ k → iDN n (u ∘ Φ) s ≤ ENNReal.ofReal (cstA n) * S := by
      intro n hn
      refine iSup₂_le fun x hx => ?_
      by_cases hfin : S = ⊤
      · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (hA0 n))]
        exact le_top
      · have hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i u t (Φ x)‖ ≤ S.toReal := by
          intro i hi
          have hiS : iDN i u t ≤ S := (hSle i (le_trans hi hn)).1
          have hne : iDN i u t ≠ ⊤ := ne_top_of_le_ne_top hfin hiS
          calc ‖iteratedFDerivWithin ℝ i u t (Φ x)‖
              = (ENNReal.ofReal ‖iteratedFDerivWithin ℝ i u t (Φ x)‖).toReal :=
                (ENNReal.toReal_ofReal (norm_nonneg _)).symm
            _ ≤ (iDN i u t).toReal := ENNReal.toReal_mono hne (le_iDN i (hst hx))
            _ ≤ S.toReal := ENNReal.toReal_mono hfin hiS
        have hD' : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin ℝ i Φ s x‖ ≤ Dstar ^ i := by
          intro i hi1 hi2
          calc ‖iteratedFDerivWithin ℝ i Φ s x‖ ≤ D i := hD i x hx
            _ ≤ Dstar := hDle i (le_trans hi2 hn)
            _ ≤ Dstar ^ i := le_self_pow₀ hDs1 (by omega)
        have hcomp := norm_iteratedFDerivWithin_comp_le (g := u) (f := Φ)
          (N := (n : WithTop ℕ∞)) (hu n) (hΦ n) le_rfl ht.uniqueDiffOn hs.uniqueDiffOn hst hx hC hD'
        have hbound : ‖iteratedFDerivWithin ℝ n (u ∘ Φ) s x‖ ≤ cstA n * S.toReal := by
          calc ‖iteratedFDerivWithin ℝ n (u ∘ Φ) s x‖
              ≤ (n.factorial : ℝ) * S.toReal * Dstar ^ n := hcomp
            _ = cstA n * S.toReal := by rw [hcstA]; ring
        calc ENNReal.ofReal ‖iteratedFDerivWithin ℝ n (u ∘ Φ) s x‖
            ≤ ENNReal.ofReal (cstA n * S.toReal) := ENNReal.ofReal_le_ofReal hbound
          _ = ENNReal.ofReal (cstA n) * ENNReal.ofReal S.toReal :=
              ENNReal.ofReal_mul (le_of_lt (hA0 n))
          _ = ENNReal.ofReal (cstA n) * S := by rw [ENNReal.ofReal_toReal hfin]
    have hHSN : ∀ n, n ≤ k → hSN n α (u ∘ Φ) s ≤ ENNReal.ofReal (cstR n) * S := by
      intro n hn
      rw [hSN]
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
      by_cases hfin : S = ⊤
      · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (hR0 n))]
        exact le_top
      · have hxyp : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero_of_ne hxy)) _
        have hFBx := iteratedFDerivWithin_comp_eq_sum (n := n)
          ((hu n).contDiffWithinAt (hst hx)) ((hΦ n).contDiffWithinAt hx)
          ht.uniqueDiffOn hs.uniqueDiffOn hx hst
        have hFBy := iteratedFDerivWithin_comp_eq_sum (n := n)
          ((hu n).contDiffWithinAt (hst hy)) ((hΦ n).contDiffWithinAt hy)
          ht.uniqueDiffOn hs.uniqueDiffOn hy hst
        set G : OrderedFinpartition n → (X [×n]→L[ℝ] A) :=
          fun c => c.compAlongOrderedFinpartition (iteratedFDerivWithin ℝ c.length u t (Φ x))
              (fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x)
            - c.compAlongOrderedFinpartition (iteratedFDerivWithin ℝ c.length u t (Φ y))
              (fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s y) with hG
        have hdiff : iteratedFDerivWithin ℝ n (u ∘ Φ) s x - iteratedFDerivWithin ℝ n (u ∘ Φ) s y
            = ∑ c : OrderedFinpartition n, G c := by
          rw [hFBx, hFBy, Finset.sum_sub_distrib]
        have h1c : ∀ c : OrderedFinpartition n,
            ‖iteratedFDerivWithin ℝ c.length u t (Φ x)‖ ≤ ai c.length := by
          intro c
          rw [hai, ← ENNReal.toReal_ofReal (norm_nonneg _)]
          exact ENNReal.toReal_mono
            (ne_top_of_le_ne_top hfin (hSle c.length (le_trans c.length_le hn)).1)
            (le_iDN c.length (hst hx))
        have h2c : ∀ c : OrderedFinpartition n,
            ‖iteratedFDerivWithin ℝ c.length u t (Φ x)
              - iteratedFDerivWithin ℝ c.length u t (Φ y)‖
              ≤ bi c.length * ‖Φ x - Φ y‖ ^ α := by
          intro c
          rcases eq_or_ne (Φ x) (Φ y) with heq | hne
          · rw [heq, sub_self, norm_zero]; positivity
          · have hle : ENNReal.ofReal (‖iteratedFDerivWithin ℝ c.length u t (Φ x)
                - iteratedFDerivWithin ℝ c.length u t (Φ y)‖ / ‖Φ x - Φ y‖ ^ α)
                ≤ hSN c.length α u t := le_hSN c.length α (hst hx) (hst hy) hne
            have hbne : hSN c.length α u t ≠ ⊤ :=
              ne_top_of_le_ne_top hfin (hSle c.length (le_trans c.length_le hn)).2
            have hr : ‖iteratedFDerivWithin ℝ c.length u t (Φ x)
                - iteratedFDerivWithin ℝ c.length u t (Φ y)‖ / ‖Φ x - Φ y‖ ^ α ≤ bi c.length := by
              rw [hbi, ← ENNReal.toReal_ofReal
                (div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg (Φ x - Φ y)) α))]
              exact ENNReal.toReal_mono hbne hle
            rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero_of_ne hne)) _)] at hr
            exact hr
        have h3c : ∀ c : OrderedFinpartition n,
            ‖(fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x)‖ ≤ Dstar := by
          intro c
          rw [pi_norm_le_iff_of_nonneg hDs0]
          intro m
          exact le_trans (hD (c.partSize m) x hx) (hDle _ (le_trans (c.partSize_le m) hn))
        have h4c : ∀ c : OrderedFinpartition n,
            ‖(fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s y)‖ ≤ Dstar := by
          intro c
          rw [pi_norm_le_iff_of_nonneg hDs0]
          intro m
          exact le_trans (hD (c.partSize m) y hy) (hDle _ (le_trans (c.partSize_le m) hn))
        have h5c : ∀ c : OrderedFinpartition n,
            ‖(fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s x)
              - (fun m => iteratedFDerivWithin ℝ (c.partSize m) Φ s y)‖
              ≤ Estar * ‖x - y‖ ^ α := by
          intro c
          rw [pi_norm_le_iff_of_nonneg (by positivity)]
          intro m
          exact le_trans (hE (c.partSize m) x hx y hy)
            (mul_le_mul_of_nonneg_right (hEle _ (le_trans (c.partSize_le m) hn))
              (Real.rpow_nonneg (norm_nonneg (x - y)) α))
        have h6 : ‖Φ x - Φ y‖ ^ α ≤ Lα * ‖x - y‖ ^ α := by
          rw [hLαdef]; exact norm_sub_rpow_le hα hL x hx y hy
        have hstep : ‖iteratedFDerivWithin ℝ n (u ∘ Φ) s x
              - iteratedFDerivWithin ℝ n (u ∘ Φ) s y‖ / ‖x - y‖ ^ α
            ≤ ∑ c : OrderedFinpartition n,
                (ai c.length * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar
                  + bi c.length * Lα * Dstar ^ c.length) := by
          rw [hdiff]
          have h1 : ‖∑ c : OrderedFinpartition n, G c‖ ≤ ∑ c : OrderedFinpartition n, ‖G c‖ :=
            norm_sum_le _ _
          calc ‖∑ c : OrderedFinpartition n, G c‖ / ‖x - y‖ ^ α
              ≤ (∑ c : OrderedFinpartition n, ‖G c‖) / ‖x - y‖ ^ α :=
                div_le_div_of_nonneg_right h1 (le_of_lt hxyp)
            _ = ∑ c : OrderedFinpartition n, ‖G c‖ / ‖x - y‖ ^ α := Finset.sum_div _ _ _
            _ ≤ ∑ c : OrderedFinpartition n,
                (ai c.length * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar
                  + bi c.length * Lα * Dstar ^ c.length) := by
                refine Finset.sum_le_sum fun c _ => ?_
                exact partition_comp_sub_le c (h1c c) (h2c c) (h3c c) (h4c c) (h5c c) h6
                  (by rw [hai]; positivity) (by rw [hbi]; positivity) hDs0 hEs0 hLα0 hxy
        have hsum : ∑ c : OrderedFinpartition n,
                (ai c.length * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar
                  + bi c.length * Lα * Dstar ^ c.length) ≤ cstR n * S.toReal := by
          have hb : ∀ c : OrderedFinpartition n,
              ai c.length * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar
                + bi c.length * Lα * Dstar ^ c.length
              ≤ ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + Lα * Dstar ^ c.length)
                  * S.toReal := by
            intro c
            have haic : ai c.length ≤ S.toReal := by
              rw [hai]
              exact ENNReal.toReal_mono hfin (hSle c.length (le_trans c.length_le hn)).1
            have hbic : bi c.length ≤ S.toReal := by
              rw [hbi]
              exact ENNReal.toReal_mono hfin (hSle c.length (le_trans c.length_le hn)).2
            have hX0 : 0 ≤ (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar := by positivity
            have hY0 : 0 ≤ Lα * Dstar ^ c.length := by positivity
            have hp1 : ai c.length * ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar)
                ≤ S.toReal * ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar) :=
              mul_le_mul_of_nonneg_right haic hX0
            have hp2 : bi c.length * (Lα * Dstar ^ c.length) ≤ S.toReal * (Lα * Dstar ^ c.length) :=
              mul_le_mul_of_nonneg_right hbic hY0
            calc ai c.length * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar
                  + bi c.length * Lα * Dstar ^ c.length
                = ai c.length * ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar)
                  + bi c.length * (Lα * Dstar ^ c.length) := by ring
              _ ≤ S.toReal * ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar)
                  + S.toReal * (Lα * Dstar ^ c.length) := add_le_add hp1 hp2
              _ = ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + Lα * Dstar ^ c.length)
                  * S.toReal := by ring
          calc ∑ c : OrderedFinpartition n,
                  (ai c.length * (c.length : ℝ) * Dstar ^ (c.length - 1) * Estar
                    + bi c.length * Lα * Dstar ^ c.length)
              ≤ ∑ c : OrderedFinpartition n,
                  (((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + Lα * Dstar ^ c.length)
                    * S.toReal) := Finset.sum_le_sum fun c _ => hb c
            _ = (∑ c : OrderedFinpartition n,
                  ((c.length : ℝ) * Dstar ^ (c.length - 1) * Estar + Lα * Dstar ^ c.length))
                  * S.toReal := by rw [Finset.sum_mul]
            _ ≤ cstR n * S.toReal := by
                rw [hcstR]
                exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
                  ENNReal.toReal_nonneg
        calc ENNReal.ofReal
              (‖iteratedFDerivWithin ℝ n (u ∘ Φ) s x
                - iteratedFDerivWithin ℝ n (u ∘ Φ) s y‖ / ‖x - y‖ ^ α)
            ≤ ENNReal.ofReal (cstR n * S.toReal) := ENNReal.ofReal_le_ofReal (hstep.trans hsum)
          _ = ENNReal.ofReal (cstR n) * S := by
              rw [ENNReal.ofReal_mul (le_of_lt (hR0 n)), ENNReal.ofReal_toReal hfin]
    calc ∑ i ∈ Finset.range (k + 1), (iDN i (u ∘ Φ) s + hSN i α (u ∘ Φ) s)
        ≤ ∑ i ∈ Finset.range (k + 1),
            (ENNReal.ofReal (cstA i) * S + ENNReal.ofReal (cstR i) * S) :=
          Finset.sum_le_sum fun i hi =>
            add_le_add (hIDN i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
              (hHSN i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
      _ = (∑ i ∈ Finset.range (k + 1), (ENNReal.ofReal (cstA i) + ENNReal.ofReal (cstR i))) * S := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), (cstA i + cstR i)) * S := by
          congr 1
          rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => add_nonneg (le_of_lt (hA0 i)) (le_of_lt (hR0 i)))]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_add (le_of_lt (hA0 i)) (le_of_lt (hR0 i))]
      _ = ENNReal.ofReal (∑ i ∈ Finset.range (k + 1), (cstA i + cstR i))
            * (∑ i ∈ Finset.range (k + 1), (iDN i u t + hSN i α u t)) := by rw [hS]

end Work.CR.Flat.Holder
