import Mathlib
import Submission.Commons.Geometry.Ulam.noncentral_strict_convex_body_of_revolution

namespace Commons.Geometry.Ulam

open scoped Pointwise RealInnerProductSpace

set_option autoImplicit false

noncomputable def radialPoint {d : ℕ} [NeZero d] (t c : ℝ) : EuclideanSpace ℝ (Fin d) :=
  EuclideanSpace.single (0 : Fin d) t + EuclideanSpace.single (1 : Fin d) c

lemma radialPoint_zero_apply {d : ℕ} [NeZero d] (hd : 3 ≤ d) (t c : ℝ) :
    (radialPoint (d := d) t c) 0 = t := by
  dsimp [radialPoint, EuclideanSpace.single]
  simp [fin_one_ne_zero_of_three_le hd]

lemma radialPoint_tail_sum {d : ℕ} [NeZero d] (hd : 3 ≤ d) (t c : ℝ) :
    (∑ i > 0, ((radialPoint (d := d) t c) i)^2) = c^2 := by
  classical
  dsimp [radialPoint]
  have h0zero : ∀ i ∈ Finset.Ioi (0 : Fin d),
      (EuclideanSpace.single (0 : Fin d) t) i = 0 := by
    intro i hi
    have hi_ne : i ≠ 0 := by
      intro h
      have hlt : 0 < i := (Finset.mem_Ioi.mp hi)
      rw [h] at hlt
      exact lt_irrefl _ hlt
    dsimp [EuclideanSpace.single]
    simp [hi_ne]
  calc
    (∑ i ∈ Finset.Ioi (0 : Fin d),
        ((EuclideanSpace.single (0 : Fin d) t) i +
          (EuclideanSpace.single (1 : Fin d) c) i)^2)
        = ∑ i ∈ Finset.Ioi (0 : Fin d),
            (((EuclideanSpace.single (0 : Fin d) t) i)^2 +
              2 * (EuclideanSpace.single (0 : Fin d) t) i *
                (EuclideanSpace.single (1 : Fin d) c) i +
              ((EuclideanSpace.single (1 : Fin d) c) i)^2) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hz := h0zero i hi
          rw [hz]
          ring
    _ = ∑ i ∈ Finset.Ioi (0 : Fin d), ((EuclideanSpace.single (1 : Fin d) c) i)^2 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hz := h0zero i hi
          rw [hz]
          ring
    _ = c^2 := by
          rw [Finset.sum_eq_single_of_mem (1 : Fin d) (by simp [fin_one_pos_of_three_le hd])]
          · dsimp [EuclideanSpace.single]
            simp
          · intro b hb hb1
            dsimp [EuclideanSpace.single]
            simp [hb1]

lemma mem_body_radialPoint {d : ℕ} [NeZero d] (hd : 3 ≤ d) {f : ℝ → ℝ}
    {t c : ℝ} (ht : t ∈ Set.Icc (-1) 1) (hc : c^2 ≤ (f t)^2) :
    radialPoint (d := d) t c ∈ {x : EuclideanSpace ℝ (Fin d) |
      x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2} := by
  constructor
  · simpa [radialPoint_zero_apply hd] using ht
  · rw [radialPoint_tail_sum hd]
    rw [radialPoint_zero_apply hd]
    exact hc

lemma not_centrally_symmetric_body_of_revolution_of_not_even_v4 {d : ℕ} [NeZero d]
    (hd : 3 ≤ d) {f : ℝ → ℝ}
    (hf_support : Function.support f ⊆ Set.Icc (-1) 1)
    (hf_left : f (-1) = 0) (hf_right : f 1 = 0)
    (hf_pos : ∀ t ∈ Set.Ioo (-1) 1, 0 < f t)
    (hf_ne_even : ¬ ∀ t : ℝ, f (-t) = f t) :
    let K : Set (EuclideanSpace ℝ (Fin d)) :=
      {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
    ¬ ∃ p : EuclideanSpace ℝ (Fin d), K - {p} = -(K - {p}) := by
  classical
  change ¬ ∃ p : EuclideanSpace ℝ (Fin d),
    {x : EuclideanSpace ℝ (Fin d) | x 0 ∈ Set.Icc (-1) 1 ∧
      ∑ i > 0, (x i)^2 ≤ f (x 0)^2} - {p} =
      -({x : EuclideanSpace ℝ (Fin d) | x 0 ∈ Set.Icc (-1) 1 ∧
        ∑ i > 0, (x i)^2 ≤ f (x 0)^2} - {p})
  rintro ⟨p, hp⟩
  let K : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | x 0 ∈ Set.Icc (-1) 1 ∧ ∑ i > 0, (x i)^2 ≤ f (x 0)^2}
  have hpK : K - {p} = -(K - {p}) := by
    simpa [K] using hp
  have hreflect : ∀ ⦃x : EuclideanSpace ℝ (Fin d)⦄, x ∈ K → (2 : ℝ) • p - x ∈ K := by
    intro x hx
    exact mem_reflect_of_central_symm (E := EuclideanSpace ℝ (Fin d)) (s := K) hpK hx
  let vneg : EuclideanSpace ℝ (Fin d) := radialPoint (d := d) (-1) 0
  let vpos : EuclideanSpace ℝ (Fin d) := radialPoint (d := d) 1 0
  have hvneg_mem : vneg ∈ K := by
    dsimp [vneg]
    exact mem_body_radialPoint (d := d) hd (f := f) (t := -1) (c := 0)
      (by norm_num [Set.mem_Icc]) (by rw [hf_left])
  have hvpos_mem : vpos ∈ K := by
    dsimp [vpos]
    exact mem_body_radialPoint (d := d) hd (f := f) (t := 1) (c := 0)
      (by norm_num [Set.mem_Icc]) (by rw [hf_right])
  have hrneg := hreflect hvneg_mem
  have hrpos := hreflect hvpos_mem
  have hrneg0 : ((2 : ℝ) • p - vneg) 0 = 2 * p 0 + 1 := by
    dsimp [vneg]
    simp [radialPoint_zero_apply hd]
  have hrpos0 : ((2 : ℝ) • p - vpos) 0 = 2 * p 0 - 1 := by
    dsimp [vpos]
    simp [radialPoint_zero_apply hd]
  have hp0_le : p 0 ≤ 0 := by
    have h := hrneg.1.2
    nlinarith [hrneg0, h]
  have hp0_ge : 0 ≤ p 0 := by
    have h := hrpos.1.1
    nlinarith [hrpos0, h]
  have hp0 : p 0 = 0 := le_antisymm hp0_le hp0_ge
  have htail_le : (∑ i ∈ Finset.Ioi (0 : Fin d), (2 * p i)^2) ≤ 0 := by
    have hmem := hrpos.2
    have hcoord : ((2 : ℝ) • p - vpos) (0 : Fin d) = -1 := by
      rw [hrpos0, hp0]
      norm_num
    have hvpos_tail : ∀ i ∈ Finset.Ioi (0 : Fin d), vpos i = 0 := by
      intro i hi
      have hi_ne : i ≠ 0 := by
        intro h
        have hlt : 0 < i := (Finset.mem_Ioi.mp hi)
        rw [h] at hlt
        exact lt_irrefl _ hlt
      dsimp [vpos, radialPoint, EuclideanSpace.single]
      simp [hi_ne]
    have hmem' : (∑ i ∈ Finset.Ioi (0 : Fin d), (2 * p i - vpos i)^2) ≤
        (f (((2 : ℝ) • p - vpos) (0 : Fin d)))^2 := by
      simpa using hmem
    rw [hcoord, hf_left] at hmem'
    norm_num at hmem'
    have hsum_eq : (∑ i ∈ Finset.Ioi (0 : Fin d), (2 * p i - vpos i)^2) =
        ∑ i ∈ Finset.Ioi (0 : Fin d), (2 * p i)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hvpos_tail i hi]
      ring
    simpa [hsum_eq] using hmem'
  have hnonneg : ∀ i ∈ Finset.Ioi (0 : Fin d), 0 ≤ (2 * p i)^2 := by
    intro i hi
    positivity
  have hsum_eq : (∑ i ∈ Finset.Ioi (0 : Fin d), (2 * p i)^2) = 0 :=
    le_antisymm htail_le (Finset.sum_nonneg hnonneg)
  have hterms : ∀ i ∈ Finset.Ioi (0 : Fin d), (2 * p i)^2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_eq
  have hp_tail : ∀ i : Fin d, i ≠ 0 → p i = 0 := by
    intro i hi
    have hi_mem : i ∈ Finset.Ioi (0 : Fin d) := by
      rw [Finset.mem_Ioi]
      exact Fin.pos_iff_ne_zero.mpr hi
    have hterm := hterms i hi_mem
    have htwo : 2 * p i = 0 := sq_eq_zero_iff.mp hterm
    nlinarith
  have h2p_sub_eq_neg : ∀ x : EuclideanSpace ℝ (Fin d), (2 : ℝ) • p - x = -x := by
    intro x
    apply PiLp.ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp [hp0]
    · have hp_i := hp_tail i hi
      simp [hp_i]
  have hle_for : ∀ t ∈ Set.Ioo (-1) 1, f t ≤ f (-t) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (-1) 1 := Set.Ioo_subset_Icc_self ht
    let w : EuclideanSpace ℝ (Fin d) := radialPoint (d := d) t (f t)
    have hw_mem : w ∈ K := by
      dsimp [w]
      exact mem_body_radialPoint (d := d) hd (f := f) (t := t) (c := f t) htIcc (le_refl _)
    have hrefl : (2 : ℝ) • p - w ∈ K := hreflect hw_mem
    have hneg_mem : -w ∈ K := by
      simpa [h2p_sub_eq_neg w] using hrefl
    have hneg0 : (-w) 0 = -t := by
      dsimp [w]
      simp [radialPoint_zero_apply hd]
    have htail_neg : (∑ i ∈ Finset.Ioi (0 : Fin d), ((-w) i)^2) = (f t)^2 := by
      dsimp [w]
      calc
        (∑ i ∈ Finset.Ioi (0 : Fin d), ((-(radialPoint (d := d) t (f t))) i)^2)
            = ∑ i ∈ Finset.Ioi (0 : Fin d), ((radialPoint (d := d) t (f t)) i)^2 := by
              apply Finset.sum_congr rfl
              intro i hi
              change (-((radialPoint (d := d) t (f t)) i)) ^ 2 =
                ((radialPoint (d := d) t (f t)) i)^2
              ring
        _ = (f t)^2 := radialPoint_tail_sum hd t (f t)
    have hbound : (∑ i ∈ Finset.Ioi (0 : Fin d), ((-w) i)^2) ≤ (f ((-w) 0))^2 := hneg_mem.2
    rw [htail_neg, hneg0] at hbound
    have hft_pos : 0 < f t := hf_pos t ht
    have hfneg_pos : 0 < f (-t) := by
      apply hf_pos (-t)
      rw [Set.mem_Ioo]
      constructor <;> nlinarith [ht.1, ht.2]
    exact (sq_le_sq₀ hft_pos.le hfneg_pos.le).1 hbound
  have hf_even_on_Ioo : ∀ t ∈ Set.Ioo (-1) 1, f t = f (-t) := by
    intro t ht
    have ht' : -t ∈ Set.Ioo (-1) 1 := by
      rw [Set.mem_Ioo]
      constructor <;> nlinarith [ht.1, ht.2]
    have h₁ := hle_for t ht
    have h₂ := hle_for (-t) ht'
    have h₂' : f (-t) ≤ f t := by
      simpa using h₂
    exact le_antisymm h₁ h₂'
  have hf_even : ∀ t : ℝ, f (-t) = f t := by
    intro t
    by_cases ht_mem : t ∈ Set.Icc (-1) 1
    · by_cases hto : t ∈ Set.Ioo (-1) 1
      · exact (hf_even_on_Ioo t hto).symm
      · have hnot : ¬ (-1 < t ∧ t < 1) := by
          simpa [Set.mem_Ioo] using hto
        rw [Set.mem_Icc] at ht_mem
        by_cases hleft : t = -1
        · subst t
          norm_num [hf_left, hf_right]
        · have ht_one : t = 1 := by
            have hlt : -1 < t := lt_of_le_of_ne ht_mem.1 (Ne.symm hleft)
            have hle : t ≤ 1 := ht_mem.2
            by_contra hne
            have hlt1 : t < 1 := lt_of_le_of_ne hle hne
            exact hnot ⟨hlt, hlt1⟩
          subst t
          norm_num [hf_left, hf_right]
    · have hft0 : f t = 0 := (Function.support_subset_iff'.mp hf_support) t ht_mem
      have hneg_out : -t ∉ Set.Icc (-1) 1 := by
        intro hneg
        apply ht_mem
        rw [Set.mem_Icc] at hneg ⊢
        constructor <;> nlinarith
      have hfneg0 : f (-t) = 0 := (Function.support_subset_iff'.mp hf_support) (-t) hneg_out
      rw [hft0, hfneg0]
  exact hf_ne_even hf_even

end Commons.Geometry.Ulam
