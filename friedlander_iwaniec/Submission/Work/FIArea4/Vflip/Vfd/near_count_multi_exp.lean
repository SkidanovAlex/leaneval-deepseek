import Mathlib
import Submission.Work.FIArea4.A4varbounds
import Submission.Work.FIPlan.Interface

namespace Work.FIArea4.Vflip.Vfd

open Finset

noncomputable section

/-- Injectivity of the linear form `(q₁,q₂) ↦ r q₂ - q₁ s` on the box `(R,2R]×(S,2S]`,
given `(r,s) = 1` and `r > R`. -/
private lemma injOn_linForm_exp {R S r s : ℕ} (hRr : R < r) (hcop : Nat.Coprime r s) :
    Set.InjOn (fun q : ℕ × ℕ => (r : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (s : ℤ))
      ↑(Finset.Ioc R (2 * R) ×ˢ Finset.Ioc S (2 * S)) := by
  intro q hq q' hq' heq
  simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_Ioc] at hq hq'
  obtain ⟨hq1, hq2⟩ := hq
  obtain ⟨hq1', hq2'⟩ := hq'
  obtain ⟨hq1lo, hq1hi⟩ := hq1
  obtain ⟨hq1lo', hq1hi'⟩ := hq1'
  dsimp only at heq
  have h2 : (r : ℤ) * ((q.2 : ℤ) - (q'.2 : ℤ)) = (s : ℤ) * ((q.1 : ℤ) - (q'.1 : ℤ)) := by
    linarith [heq]
  have h3 : r * ((q.2 : ℤ) - (q'.2 : ℤ)).natAbs = s * ((q.1 : ℤ) - (q'.1 : ℤ)).natAbs := by
    have h := congrArg Int.natAbs h2
    rwa [Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at h
  have hdvdB : r ∣ ((q.1 : ℤ) - (q'.1 : ℤ)).natAbs :=
    hcop.dvd_of_dvd_mul_left ⟨((q.2 : ℤ) - (q'.2 : ℤ)).natAbs, h3.symm⟩
  have hB : ((q.1 : ℤ) - (q'.1 : ℤ)).natAbs ≤ R - 1 := by
    rcases le_total q.1 q'.1 with h | h
    · rw [Int.natAbs_natCast_sub_natCast_of_le h]; omega
    · rw [Int.natAbs_natCast_sub_natCast_of_ge h]; omega
  have hBlt : ((q.1 : ℤ) - (q'.1 : ℤ)).natAbs < r := lt_of_le_of_lt hB (by omega)
  have hB0 : ((q.1 : ℤ) - (q'.1 : ℤ)).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvdB hBlt
  have hq1eq : q.1 = q'.1 := by
    have h := Int.natAbs_eq_zero.mp hB0
    omega
  have hq2eq : q.2 = q'.2 := by
    have hm : (r : ℤ) * ((q.2 : ℤ) - (q'.2 : ℤ)) = 0 := by
      rw [hq1eq] at h2; simpa using h2
    have hrne : (r : ℤ) ≠ 0 := by
      have : (0 : ℤ) < (r : ℤ) := by exact_mod_cast (by omega : 0 < r)
      omega
    have h := (mul_eq_zero.mp hm).resolve_left hrne
    omega
  exact Prod.ext hq1eq hq2eq

/-- The number of multiples of `d` in `[0,M]` is `M / d + 1`. -/
private lemma card_Icc_filter_dvd_exp (M d : ℕ) :
    ((Finset.Icc 0 M).filter (fun n => d ∣ n)).card = M / d + 1 := by
  have hins : (Finset.Icc 0 M).filter (fun n => d ∣ n)
      = insert 0 ((Finset.Ioc 0 M).filter (fun n => d ∣ n)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h0, hM⟩, hdvd⟩
      rcases Nat.eq_zero_or_pos n with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨h, hM⟩, hdvd⟩
    · rintro (rfl | ⟨⟨h0, hM⟩, hdvd⟩)
      · exact ⟨⟨le_refl 0, Nat.zero_le M⟩, dvd_zero d⟩
      · exact ⟨⟨Nat.zero_le n, hM⟩, hdvd⟩
  rw [hins, Finset.card_insert_of_notMem (by simp [Finset.mem_Ioc]),
    Nat.Ioc_filter_dvd_card_eq_div]

/-- The near-diagonal count with multiplicity and the explicit constant `1000`
(the `near_count_multi` bound with the existential constant inlined). -/
theorem near_count_multi_exp {R S D : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hDsq : R * S < D * D) :
    ∀ (H : ℝ) (hH : 1 ≤ H) (hHup : H ≤ (R : ℝ) * (S : ℝ) / (D : ℝ))
      (r s : ℕ) (hr : r ∈ Finset.Ioc R (2 * R)) (hs : s ∈ Finset.Ioc S (2 * S))
      (hcop : Nat.Coprime r s),
      Finset.sum (((Finset.Ioc R (2 * R)) ×ˢ (Finset.Ioc S (2 * S))).filter
          (fun q => (((r : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (s : ℤ)).natAbs : ℝ) * H
              ≤ 8 * (R : ℝ) * (S : ℝ)))
        (fun q => ((((Finset.Ioc (D / 2) (3 * D)).filter
            (fun d => d ∣ ((r : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (s : ℤ)).natAbs)).card : ℕ) : ℝ))
        ≤ 1000 * ((R : ℝ) * (S : ℝ) / H * (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
            + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H)) := by
  intro H hH hHup r s hr hs hcop
  have hHpos : (0 : ℝ) < H := by linarith
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hRS0 : (0 : ℝ) ≤ (R : ℝ) * (S : ℝ) := by positivity
  let f : ℕ × ℕ → ℤ := fun q => (r : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (s : ℤ)
  let Sd : Finset ℕ := Finset.Ioc (D / 2) (3 * D)
  let near : Finset (ℕ × ℕ) := ((Finset.Ioc R (2 * R)) ×ˢ (Finset.Ioc S (2 * S))).filter
      (fun q => ((f q).natAbs : ℝ) * H ≤ 8 * (R : ℝ) * (S : ℝ))
  set X : ℝ := 8 * (R : ℝ) * (S : ℝ) / H with hX
  have hX0 : 0 ≤ X := by
    rw [hX]; exact div_nonneg (by positivity) (le_of_lt hHpos)
  set M : ℕ := Nat.floor X with hM
  have hinj : Set.InjOn f ↑(Finset.Ioc R (2 * R) ×ˢ Finset.Ioc S (2 * S)) :=
    injOn_linForm_exp (Finset.mem_Ioc.mp hr).1 hcop
  -- Each fibre of the divisor map has at most `2 * (M / d + 1)` elements.
  have hfibre : ∀ d ∈ Sd,
      (near.filter (fun q => d ∣ (f q).natAbs)).card ≤ ((M / d) + 1) * 2 := by
    intro d hd
    have hMT : Set.MapsTo (fun q : ℕ × ℕ => ((f q).natAbs, decide (0 < f q)))
        ↑(near.filter (fun q => d ∣ (f q).natAbs))
        ↑(((Finset.Icc 0 M).filter (fun n => d ∣ n)) ×ˢ (Finset.univ : Finset Bool)) := by
      intro q hq
      rw [Finset.mem_coe] at hq
      obtain ⟨hqnear, hqdvd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqAB, hle⟩ := Finset.mem_filter.mp hqnear
      have hle' : ((f q).natAbs : ℝ) ≤ X := by
        rw [hX, le_div_iff₀ hHpos]; linarith [hle]
      have hMle : (f q).natAbs ≤ M := by
        rw [hM]; exact Nat.le_floor hle'
      rw [Finset.mem_coe]
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hMle⟩, hqdvd⟩,
          Finset.mem_univ _⟩
    have hInj : Set.InjOn (fun q : ℕ × ℕ => ((f q).natAbs, decide (0 < f q)))
        ↑(near.filter (fun q => d ∣ (f q).natAbs)) := by
      intro a ha b hb heq
      rw [Finset.mem_coe] at ha hb
      have haAB : a ∈ (Finset.Ioc R (2 * R)) ×ˢ (Finset.Ioc S (2 * S)) :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
      have hbAB : b ∈ (Finset.Ioc R (2 * R)) ×ˢ (Finset.Ioc S (2 * S)) :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
      have h1 : (f a).natAbs = (f b).natAbs := congrArg Prod.fst heq
      have h2 : decide (0 < f a) = decide (0 < f b) := congrArg Prod.snd heq
      have hfab : f a = f b := by
        by_cases hza : 0 < f a
        · have hzb : 0 < f b := by
            have hh : decide (0 < f b) = true := by rw [← h2]; exact decide_eq_true hza
            exact of_decide_eq_true hh
          rw [← Int.natAbs_of_nonneg (le_of_lt hza), ← Int.natAbs_of_nonneg (le_of_lt hzb), h1]
        · have hzb : ¬ 0 < f b := by
            have hh : decide (0 < f b) = false := by rw [← h2]; exact decide_eq_false hza
            exact of_decide_eq_false hh
          rw [Int.eq_neg_natAbs_of_nonpos (le_of_not_gt hza),
            Int.eq_neg_natAbs_of_nonpos (le_of_not_gt hzb), h1]
      exact hinj (Finset.mem_coe.mpr haAB) (Finset.mem_coe.mpr hbAB) hfab
    have hcard := Finset.card_le_card_of_injOn _ hMT hInj
    rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, card_Icc_filter_dvd_exp] at hcard
    exact hcard
  -- The multiplicity sum counts the pairs `(q,d)`, so it is the sum of the fibre sizes.
  have hswap : (∑ q ∈ near, ((Sd.filter (fun d => d ∣ (f q).natAbs)).card : ℝ))
      = ∑ d ∈ Sd, ((near.filter (fun q => d ∣ (f q).natAbs)).card : ℝ) := by
    have hnat : ∑ q ∈ near, (Sd.filter (fun d => d ∣ (f q).natAbs)).card
        = ∑ d ∈ Sd, (near.filter (fun q => d ∣ (f q).natAbs)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    have hcast : ((∑ q ∈ near, (Sd.filter (fun d => d ∣ (f q).natAbs)).card : ℕ) : ℝ)
        = ((∑ d ∈ Sd, (near.filter (fun q => d ∣ (f q).natAbs)).card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_sum] using hcast
  have hsum1 : (∑ d ∈ Sd, ((near.filter (fun q => d ∣ (f q).natAbs)).card : ℝ))
      ≤ ∑ d ∈ Sd, ((((M / d) + 1) * 2 : ℕ) : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro d hd
    exact_mod_cast hfibre d hd
  -- numeric bound on the fibre sum
  have htermR : ∀ d ∈ Sd, ((((M / d) + 1) * 2 : ℕ) : ℝ) ≤ 4 * X / (D : ℝ) + 2 := by
    intro d hd
    have hd1 : 1 ≤ d := by have := (Finset.mem_Ioc.mp hd).1; omega
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hDle : (D : ℝ) ≤ 2 * (d : ℝ) := by
      have hlt : D / 2 < d := (Finset.mem_Ioc.mp hd).1
      have : D < d * 2 := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp hlt
      have : D ≤ 2 * d := by omega
      exact_mod_cast this
    have hMd : ((M / d : ℕ) : ℝ) ≤ 2 * X / (D : ℝ) := by
      have h1 : ((M / d : ℕ) : ℝ) ≤ (M : ℝ) / (d : ℝ) := Nat.cast_div_le
      have h2 : (M : ℝ) ≤ X := by rw [hM]; exact Nat.floor_le hX0
      have h3 : (M : ℝ) / (d : ℝ) ≤ X / (d : ℝ) := by gcongr
      have h4 : X / (d : ℝ) ≤ 2 * X / (D : ℝ) := by
        rw [div_le_div_iff₀ hd0 hDpos]
        nlinarith [hDle, hX0]
      linarith
    calc ((((M / d) + 1) * 2 : ℕ) : ℝ) = 2 * ((M / d : ℕ) : ℝ) + 2 := by push_cast; ring
      _ ≤ 2 * (2 * X / (D : ℝ)) + 2 := by linarith
      _ = 4 * X / (D : ℝ) + 2 := by ring
  have hSd3 : (Sd.card : ℝ) ≤ 3 * (D : ℝ) := by
    have h : Sd.card = 3 * D - D / 2 := by simp [Sd]
    rw [h]
    exact_mod_cast (Nat.sub_le (3 * D) (D / 2))
  have hsum2 : (∑ d ∈ Sd, ((((M / d) + 1) * 2 : ℕ) : ℝ)) ≤ 13 * X := by
    calc ∑ d ∈ Sd, ((((M / d) + 1) * 2 : ℕ) : ℝ) ≤ ∑ d ∈ Sd, (4 * X / (D : ℝ) + 2) :=
          Finset.sum_le_sum htermR
      _ = (Sd.card : ℝ) * (4 * X / (D : ℝ) + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * (D : ℝ) * (4 * X / (D : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hSd3 (by positivity)
      _ = 12 * X + 6 * (D : ℝ) := by field_simp; ring
      _ ≤ 13 * X := by
          have hDH : (D : ℝ) * H ≤ (R : ℝ) * (S : ℝ) := by
            have h1 := mul_le_mul_of_nonneg_right hHup (le_of_lt hDpos)
            have h2 : H * D ≤ (R : ℝ) * (S : ℝ) := by
              rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h1
            linarith [h2]
          have hD8 : (D : ℝ) ≤ X / 8 := by
            have h3 : (D : ℝ) ≤ (R : ℝ) * (S : ℝ) / H := by
              rw [le_div_iff₀ hHpos]; linarith [hDH]
            have h4 : X / 8 = (R : ℝ) * (S : ℝ) / H := by rw [hX]; ring
            linarith [h3, h4.symm.le, h4.le]
          linarith [hD8, hX0]
  have hmain : (∑ q ∈ near, ((Sd.filter (fun d => d ∣ (f q).natAbs)).card : ℝ)) ≤ 13 * X := by
    rw [hswap]
    linarith [hsum1, hsum2]
  have hDH : (D : ℝ) * H ≤ (R : ℝ) * (S : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hHup (le_of_lt hDpos)
    have h2 : H * D ≤ (R : ℝ) * (S : ℝ) := by
      rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h1
    linarith [h2]
  have hlog : 0 ≤ Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith [hDH, hRS0]
  have hterm2 : 0 ≤ ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H) :=
    div_nonneg (Real.rpow_nonneg hRS0 _) (by positivity)
  have hY0 : 0 ≤ (R : ℝ) * (S : ℝ) / H := div_nonneg hRS0 (le_of_lt hHpos)
  have hkey : 1000 * ((R : ℝ) * (S : ℝ) / H *
        (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
        + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H))
      ≥ 1000 * ((R : ℝ) * (S : ℝ) / H * 2) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1000)
    have h1 : (R : ℝ) * (S : ℝ) / H * 2
        ≤ (R : ℝ) * (S : ℝ) / H * (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hlog]) hY0
    linarith [hterm2]
  calc (∑ q ∈ near, ((Sd.filter (fun d => d ∣ (f q).natAbs)).card : ℝ)) ≤ 13 * X := hmain
    _ = 104 * ((R : ℝ) * (S : ℝ) / H) := by rw [hX]; ring
    _ ≤ 1000 * ((R : ℝ) * (S : ℝ) / H * 2) := by linarith [hY0]
    _ ≤ 1000 * ((R : ℝ) * (S : ℝ) / H *
        (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
        + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H)) := hkey

end

end Work.FIArea4.Vflip.Vfd
