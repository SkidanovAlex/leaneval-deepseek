/-
Window-count estimate for the arithmetic core.

For `q ≥ 1`, an integer `a` coprime to `q` and `τ` within `1 / q` of `a`, the number of
`1 ≤ r ≤ q` with `qDist q (r * τ + φ) < t` is at most `2 t + 2`.

The proof writes `τ = a + δ` with `|δ| < 1/q`.  For a counted index `r` pick the nearest
multiple `q * round ((r * τ + φ) / q)` of `q` and set
`j r = r * a - q * round ((r * τ + φ) / q) ∈ ℤ`.
Then `|j r + r * δ + φ| < t`, so `j r ∈ (-t - r * δ - φ, t - r * δ - φ)`; as `r` ranges over
`[1, q]` this pins the `j r` inside an open interval of length `2 t + (q - 1) |δ| < 2 t + 1`.
Moreover `j r ≡ r * a (mod q)`, and since `a` is invertible mod `q` the `j r` are *distinct*
integers.  Hence there are at most `2 t + 2` of them.
-/
import Mathlib
import Submission.Work.TMC7Core.Fourier.ac_defs

namespace Work.TMC7Core.Fourier

open Finset

/-- A finset of integers all of whose elements lie in an open interval `(A, B)` has at most
`B - A + 1` elements (as a real number). -/
private lemma card_le_of_forall_mem_Ioo {T : Finset ℤ} {A B : ℝ} (hBA : A ≤ B + 1)
    (h : ∀ z ∈ T, A < (z : ℝ) ∧ (z : ℝ) < B) : (T.card : ℝ) ≤ B - A + 1 := by
  rcases T.eq_empty_or_nonempty with hT | hne
  · rw [hT]; simp only [Finset.card_empty, Nat.cast_zero]; linarith
  · have hmax : ((T.max' hne : ℤ) : ℝ) < B := (h _ (T.max'_mem hne)).2
    have hsub : T ⊆ Finset.Icc (T.min' hne) (T.max' hne) := by
      intro z hz
      rw [Finset.mem_Icc]
      exact ⟨Finset.min'_le T z hz, Finset.le_max' T z hz⟩
    have hcard : (T.card : ℝ) ≤ ((Finset.Icc (T.min' hne) (T.max' hne)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hle : T.min' hne ≤ T.max' hne := Finset.min'_le _ _ (Finset.max'_mem _ hne)
    have hci : ((Finset.Icc (T.min' hne) (T.max' hne)).card : ℝ)
        = ((T.max' hne : ℤ) : ℝ) - ((T.min' hne : ℤ) : ℝ) + 1 := by
      have h1 : ((Finset.Icc (T.min' hne) (T.max' hne)).card : ℤ)
          = T.max' hne - T.min' hne + 1 := by
        rw [Int.card_Icc_of_le _ _ (by omega)]
        ring
      exact_mod_cast h1
    have hmin : A < ((T.min' hne : ℤ) : ℝ) := (h _ (T.min'_mem hne)).1
    calc (T.card : ℝ) ≤ ((Finset.Icc (T.min' hne) (T.max' hne)).card : ℝ) := hcard
      _ = ((T.max' hne : ℤ) : ℝ) - ((T.min' hne : ℤ) : ℝ) + 1 := hci
      _ ≤ B - A + 1 := by linarith

theorem win_count (q : ℕ) (hq : 1 ≤ q) (a : ℤ) (hcop : Nat.Coprime (Int.natAbs a) q)
    (τ φ : ℝ) (hτ : dist τ (a : ℝ) < 1 / (q : ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (((Finset.Icc 1 q).filter (fun r : ℕ => qDist q ((r : ℝ) * τ + φ) < t)).card : ℝ) ≤ 2 * t + 2 := by
  classical
  set S : Finset ℕ := (Finset.Icc 1 q).filter (fun r : ℕ => qDist q ((r : ℝ) * τ + φ) < t) with hS
  set δ : ℝ := τ - (a : ℝ) with hδ
  set A : ℝ := -t - φ - max δ ((q : ℝ) * δ) with hA
  set B : ℝ := t - φ - min δ ((q : ℝ) * δ) with hB
  set jf : ℕ → ℤ := (fun r : ℕ => (r : ℤ) * a - (q : ℤ) * round (((r : ℝ) * τ + φ) / (q : ℝ))) with hjf
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hδabs : |δ| < 1 / (q : ℝ) := by
    have h := hτ
    rw [Real.dist_eq] at h
    simpa [hδ] using h
  -- Each counted `r` gives a distinct integer `jf r` lying in `(A, B)`.
  have hmem : ∀ r ∈ S, A < (jf r : ℝ) ∧ (jf r : ℝ) < B := by
    intro r hr
    rw [hS] at hr
    obtain ⟨hrIcc, hrcond⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hrq⟩ := Finset.mem_Icc.mp hrIcc
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hrqR : (r : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
    have hqe := qDist_eq q hq ((r : ℝ) * τ + φ)
    rw [hqe, Real.dist_eq] at hrcond
    have hkey : (r : ℝ) * τ + φ - (q : ℝ) * ((round (((r : ℝ) * τ + φ) / (q : ℝ)) : ℤ) : ℝ)
        = (jf r : ℝ) + (r : ℝ) * δ + φ := by
      rw [hjf, hδ]; push_cast; ring
    rw [hkey, abs_lt] at hrcond
    obtain ⟨hlo, hhi⟩ := hrcond
    have hrδ_le_max : (r : ℝ) * δ ≤ max δ ((q : ℝ) * δ) := by
      rcases le_or_gt δ 0 with h | h
      · have hqδ : (q : ℝ) * δ ≤ δ := by nlinarith [h, hqpos]
        rw [max_eq_left hqδ]; nlinarith [h, hr1R]
      · have hδqδ : δ ≤ (q : ℝ) * δ := by nlinarith [h, hqpos]
        rw [max_eq_right hδqδ]; nlinarith [h, hrqR]
    have hmin_le_rδ : min δ ((q : ℝ) * δ) ≤ (r : ℝ) * δ := by
      rcases le_or_gt δ 0 with h | h
      · have hqδ : (q : ℝ) * δ ≤ δ := by nlinarith [h, hqpos]
        rw [min_eq_right hqδ]; nlinarith [h, hr1R]
      · have hδqδ : δ ≤ (q : ℝ) * δ := by nlinarith [h, hqpos]
        rw [min_eq_left hδqδ]; nlinarith [h, hrqR]
    exact ⟨by rw [hA]; linarith, by rw [hB]; linarith⟩
  have hinj : Set.InjOn jf ↑S := by
    intro r hr r' hr' heq
    rw [Finset.mem_coe, hS] at hr hr'
    obtain ⟨hrIcc, _⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrIcc', _⟩ := Finset.mem_filter.mp hr'
    obtain ⟨hr1, hrq⟩ := Finset.mem_Icc.mp hrIcc
    obtain ⟨hr1', hrq'⟩ := Finset.mem_Icc.mp hrIcc'
    have hdvd : (q : ℤ) ∣ ((r : ℤ) - (r' : ℤ)) * a := by
      have h := heq
      rw [hjf] at h
      refine ⟨(round (((r : ℝ) * τ + φ) / (q : ℝ)) - round (((r' : ℝ) * τ + φ) / (q : ℝ))), ?_⟩
      ring_nf at h ⊢
      linarith
    have hcopI : IsCoprime (q : ℤ) a :=
      (Int.isCoprime_iff_nat_coprime.mpr (by simpa using hcop)).symm
    have hqdiv : (q : ℤ) ∣ ((r : ℤ) - (r' : ℤ)) := hcopI.dvd_of_dvd_mul_right hdvd
    have hbd : ((r : ℤ) - (r' : ℤ)).natAbs ≤ q - 1 := by
      rcases le_or_gt r r' with h | h
      · rw [Int.natAbs_natCast_sub_natCast_of_le h]; omega
      · rw [Int.natAbs_natCast_sub_natCast_of_ge (le_of_lt h)]; omega
    have hdvdn : q ∣ ((r : ℤ) - (r' : ℤ)).natAbs := by
      simpa using (Int.natAbs_dvd_natAbs.mpr hqdiv)
    have hzero : ((r : ℤ) - (r' : ℤ)).natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdvdn (by omega)
    have hz : (r : ℤ) = (r' : ℤ) := by
      have := Int.natAbs_eq_zero.mp hzero
      omega
    omega
  set T : Finset ℤ := S.image jf with hT
  have hTcard : T.card = S.card := by
    rw [hT]; exact Finset.card_image_of_injOn hinj
  have hL : B - A = 2 * t + ((q : ℝ) - 1) * |δ| := by
    have hmm : max δ ((q : ℝ) * δ) - min δ ((q : ℝ) * δ) = ((q : ℝ) - 1) * |δ| := by
      rw [max_sub_min_eq_abs]
      rw [show (q : ℝ) * δ - δ = ((q : ℝ) - 1) * δ by ring]
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)]
    rw [hA, hB]; linarith
  have hBA : A ≤ B + 1 := by
    have h2 : 0 ≤ ((q : ℝ) - 1) * |δ| :=
      mul_nonneg (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1) (abs_nonneg δ)
    linarith [hL]
  have hcardT : (T.card : ℝ) ≤ B - A + 1 := by
    refine card_le_of_forall_mem_Ioo hBA ?_
    intro z hz
    rw [hT] at hz
    obtain ⟨r, hrS, rfl⟩ := Finset.mem_image.mp hz
    exact hmem r hrS
  have hBAval : B - A + 1 ≤ 2 * t + 2 := by
    have hb : ((q : ℝ) - 1) * |δ| ≤ 1 := by
      have h1 : |δ| ≤ 1 / (q : ℝ) := le_of_lt hδabs
      have h2 : ((q : ℝ) - 1) * |δ| ≤ ((q : ℝ) - 1) * (1 / (q : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ (q : ℝ) - 1)
      have h3 : ((q : ℝ) - 1) * (1 / (q : ℝ)) ≤ 1 := by
        rw [mul_one_div, div_le_one hqpos]
        linarith
      linarith
    linarith [hL]
  calc (S.card : ℝ) = (T.card : ℝ) := by rw [hTcard]
    _ ≤ B - A + 1 := hcardT
    _ ≤ 2 * t + 2 := hBAval

end Work.TMC7Core.Fourier
