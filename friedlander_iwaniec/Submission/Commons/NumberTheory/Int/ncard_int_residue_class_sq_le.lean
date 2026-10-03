import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Card

namespace Commons.NumberTheory.Int

/-- **Counting integers in a residue class.**  A finite set `s` of integers all congruent to a
fixed residue `r` modulo `d` (`d ≥ 1`) and all lying in the real interval `[-A, A]`
(`A ≥ 0`) has at most `2A/d + 1` elements.

Indeed the congruence forces the difference of two distinct elements of `s` to be a nonzero
multiple of `d`; after scaling by `1/d` the points are therefore separated by at least `1`, and an
interval of length `2A/d` can contain at most `2A/d + 1` of them. -/
theorem card_le_of_modEq_abs_le {d : ℕ} (hd : 1 ≤ d) {s : Finset ℤ} {r : ℤ} {A : ℝ}
    (hA : 0 ≤ A) (hcong : ∀ a ∈ s, a ≡ r [ZMOD d])
    (habs : ∀ a ∈ s, |(a : ℝ)| ≤ A) :
    (s.card : ℝ) ≤ 2 * A / (d : ℝ) + 1 := by
  classical
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  by_cases hs : s.Nonempty
  · let f : ℤ → ℤ := fun a => (a - r) / (d : ℤ)
    have hdvd : ∀ a ∈ s, (d : ℤ) ∣ a - r := by
      intro a ha
      have h2 : (d : ℤ) ∣ r - a := Int.modEq_iff_dvd.mp (hcong a ha)
      rw [show r - a = -(a - r) by ring] at h2
      exact Int.dvd_neg.mp h2
    have hf : ∀ a ∈ s, (d : ℤ) * f a = a - r := by
      intro a ha
      exact Int.mul_ediv_cancel' (hdvd a ha)
    have hinj : Set.InjOn f (↑s : Set ℤ) := by
      intro a ha b hb hab
      have h1 := hf a ha
      have h2 := hf b hb
      rw [hab] at h1
      omega
    let T : Finset ℤ := s.image f
    have hTcard : T.card = s.card := Finset.card_image_of_injOn hinj
    have hTne : T.Nonempty := by
      obtain ⟨a, ha⟩ := hs
      exact ⟨f a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
    have hpair : ∀ k ∈ T, ∀ k' ∈ T, |(k : ℝ) - (k' : ℝ)| ≤ 2 * A / (d : ℝ) := by
      intro k hk k' hk'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hk'
      have h1 := hf a ha
      have h2 := hf b hb
      have hmul : (d : ℤ) * (f a - f b) = a - b := by
        have h3 : (d : ℤ) * (f a - f b) = (d : ℤ) * f a - (d : ℤ) * f b := by ring
        rw [h3, h1, h2]; ring
      have hcast : (d : ℝ) * ((f a : ℝ) - (f b : ℝ)) = (a : ℝ) - (b : ℝ) := by
        have hh := congrArg (fun z : ℤ => (z : ℝ)) hmul
        push_cast at hh
        linarith [hh]
      have hdiff : (f a : ℝ) - (f b : ℝ) = ((a : ℝ) - (b : ℝ)) / (d : ℝ) := by
        field_simp
        linarith [hcast]
      rw [hdiff, abs_div, abs_of_pos hdR]
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hdR)
      calc |(a : ℝ) - (b : ℝ)| ≤ |(a : ℝ)| + |(b : ℝ)| := abs_sub _ _
        _ ≤ A + A := add_le_add (habs a ha) (habs b hb)
        _ = 2 * A := by ring
    have hmn : ((T.min' hTne : ℤ) : ℝ) ≤ ((T.max' hTne : ℤ) : ℝ) := by
      exact_mod_cast Finset.min'_le_max' T hTne
    have hspan : ((T.max' hTne : ℤ) : ℝ) - ((T.min' hTne : ℤ) : ℝ) ≤ 2 * A / (d : ℝ) := by
      have hpm := hpair (T.max' hTne) (Finset.max'_mem T hTne) (T.min' hTne) (Finset.min'_mem T hTne)
      have heq : |((T.max' hTne : ℤ) : ℝ) - ((T.min' hTne : ℤ) : ℝ)|
          = ((T.max' hTne : ℤ) : ℝ) - ((T.min' hTne : ℤ) : ℝ) :=
        abs_of_nonneg (sub_nonneg.mpr hmn)
      rwa [heq] at hpm
    have hsub : T ⊆ Finset.Icc (T.min' hTne) (T.max' hTne) := by
      intro k hk
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le T k hk, Finset.le_max' T k hk⟩
    have hcardR : (T.card : ℝ) ≤ ((T.max' hTne : ℤ) : ℝ) + 1 - ((T.min' hTne : ℤ) : ℝ) := by
      have hle := Finset.card_le_card hsub
      have hIcc : ((Finset.Icc (T.min' hTne) (T.max' hTne)).card : ℝ) =
          ((T.max' hTne : ℤ) : ℝ) + 1 - ((T.min' hTne : ℤ) : ℝ) := by
        have h := Int.card_Icc_of_le (T.min' hTne) (T.max' hTne) (by
          have := Finset.min'_le_max' T hTne; omega)
        exact_mod_cast h
      have hleR : (T.card : ℝ) ≤ ((Finset.Icc (T.min' hTne) (T.max' hTne)).card : ℝ) := by
        exact_mod_cast hle
      rwa [hIcc] at hleR
    rw [← hTcard]
    have hsplit : ((T.max' hTne : ℤ) : ℝ) + 1 - ((T.min' hTne : ℤ) : ℝ)
        = (((T.max' hTne : ℤ) : ℝ) - ((T.min' hTne : ℤ) : ℝ)) + 1 := by ring
    linarith [hcardR, hspan, hsplit]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hpos : 0 ≤ 2 * A / (d : ℝ) := div_nonneg (by linarith) (le_of_lt hdR)
    linarith

theorem ncard_int_residue_class_sq_le {d : ℕ} (hd : 1 ≤ d) (r : ℤ) (M : ℝ) :
    (({a : ℤ | a ≡ r [ZMOD d] ∧ (a : ℝ) ^ 2 ≤ M}).ncard : ℝ) ≤ 2 * Real.sqrt M / (d : ℝ) + 1 := by
  classical
  let S : Set ℤ := {a : ℤ | a ≡ r [ZMOD d] ∧ (a : ℝ) ^ 2 ≤ M}
  let N : ℕ := ⌊Real.sqrt M⌋.toNat
  have hNnonneg : (0 : ℤ) ≤ ⌊Real.sqrt M⌋ := by
    rw [Int.le_floor]
    simpa only [Int.cast_zero] using Real.sqrt_nonneg M
  have hN : (N : ℤ) = ⌊Real.sqrt M⌋ := Int.toNat_of_nonneg hNnonneg
  have hsqrt_abs : ∀ a : ℤ, (a : ℝ) ^ 2 ≤ M → |(a : ℝ)| ≤ Real.sqrt M := by
    intro a hsq
    have h1 : Real.sqrt ((a : ℝ) ^ 2) ≤ Real.sqrt M := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs] at h1
  have hsub : S ⊆ (Finset.Icc (-(N : ℤ)) (N : ℤ) : Set ℤ) := by
    intro a ha
    have hle : |(a : ℝ)| ≤ Real.sqrt M := hsqrt_abs a ha.2
    have hle' : ((|a| : ℤ) : ℝ) ≤ Real.sqrt M := by
      rw [Int.cast_abs]; exact hle
    have hle'' : |a| ≤ (N : ℤ) := by
      rw [hN]
      exact Int.le_floor.mpr hle'
    rw [Finset.mem_coe, Finset.mem_Icc]
    exact abs_le.mp hle''
  have hSfin : S.Finite := Set.Finite.subset (Finset.finite_toSet _) hsub
  have hcount := card_le_of_modEq_abs_le (d := d) hd (s := hSfin.toFinset) (r := r)
      (A := Real.sqrt M) (Real.sqrt_nonneg M)
      (fun a ha => (hSfin.mem_toFinset.mp ha).1)
      (fun a ha => hsqrt_abs a (hSfin.mem_toFinset.mp ha).2)
  change (S.ncard : ℝ) ≤ 2 * Real.sqrt M / (d : ℝ) + 1
  rw [Set.ncard_eq_toFinset_card S hSfin]
  exact hcount

end Commons.NumberTheory.Int