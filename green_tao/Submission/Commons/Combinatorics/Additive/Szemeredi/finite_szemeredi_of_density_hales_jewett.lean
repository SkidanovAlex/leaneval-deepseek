import Mathlib
import Submission.Commons.Data.Nat.sum_digits_decomp
import Submission.Commons.Data.Nat.eq_sum_digits

namespace Commons.Combinatorics.Additive.Szemeredi

open Finset

/-- Base-`k` encoding of a digit string `Fin n → Fin k` as a natural number:
the little-endian positional value `∑ i, x i * k ^ i`. -/
private def enc (k n : ℕ) (x : Fin n → Fin k) : ℕ :=
  ∑ i : Fin n, (x i : ℕ) * k ^ (i : ℕ)

/-- The encoding as a sum over `Finset.range n` (padded with zeros). -/
private lemma enc_eq_sum_range {k n : ℕ} (x : Fin n → Fin k) :
    enc k n x = ∑ i ∈ Finset.range n,
      (if h : i < n then (x ⟨i, h⟩ : ℕ) else 0) * k ^ i := by
  rw [enc, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi), dif_pos (Finset.mem_range.mp hi)]

/-- The `j`-th base-`k` digit of the encoding is the `j`-th entry of the digit string. -/
private lemma enc_digit {k n : ℕ} (x : Fin n → Fin k) {j : ℕ} (hj : j < n) :
    enc k n x / k ^ j % k = (x ⟨j, hj⟩ : ℕ) := by
  rw [enc_eq_sum_range,
    Commons.Data.Nat.sum_digits_decomp (p := k) (L := n)
      (fun i => if h : i < n then (x ⟨i, h⟩ : ℕ) else 0) (by
        intro i hi; rw [dif_pos hi]; exact (x ⟨i, hi⟩).2) j]
  rw [dif_pos hj, if_pos hj]

/-- The encoding is injective (unique base-`k` digit expansion). -/
private lemma enc_injective {k n : ℕ} : Function.Injective (enc k n) := by
  intro x y hxy
  funext i
  have h1 := enc_digit x i.2
  have h2 := enc_digit y i.2
  rw [hxy] at h1
  exact Fin.ext (h1.symm.trans h2)

/-- The encoding is surjective onto `{0, …, k ^ n - 1}`. -/
private lemma enc_surj {k n : ℕ} (hk : 2 ≤ k) {m : ℕ} (hm : m < k ^ n) :
    ∃ x : Fin n → Fin k, enc k n x = m := by
  refine ⟨fun i => ⟨m / k ^ (i : ℕ) % k, Nat.mod_lt _ (by omega)⟩, ?_⟩
  rw [enc_eq_sum_range]
  have hd := Commons.Data.Nat.eq_sum_digits (p := k) (l := n) (x := m) (by omega) hm
  calc ∑ i ∈ Finset.range n,
        (if h : i < n then
          ((⟨m / k ^ i % k, Nat.mod_lt _ (by omega)⟩ : Fin k) : ℕ) else 0) * k ^ i
      = ∑ i ∈ Finset.range n, m / k ^ i % k * k ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [dif_pos (Finset.mem_range.mp hi)]
    _ = m := hd.symm

/-- The number of digit strings whose encoding lies in `B` equals `|B|`, as long as
`B` consists of numbers below `k ^ n`. -/
private lemma card_filter_enc {k n : ℕ} (hk : 2 ≤ k) (B : Finset ℕ)
    (hB : B ⊆ Finset.range (k ^ n)) :
    ((Finset.univ : Finset (Fin n → Fin k)).filter (fun x => enc k n x ∈ B)).card
      = B.card := by
  refine Finset.card_bij (fun x _ => enc k n x) ?_ ?_ ?_
  · intro x hx; exact (Finset.mem_filter.mp hx).2
  · intro x _ y _ hxy; exact enc_injective hxy
  · intro b hb
    obtain ⟨x, hx⟩ := enc_surj hk (Finset.mem_range.mp (hB hb))
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, by rw [hx]; exact hb⟩, hx⟩

/-- Replacing the free coordinates `P` by a constant `v` turns the encoding into an affine
function of `v`: the digits outside `P` stay, and the digits on `P` contribute `v · ∑_{i∈P} k^i`. -/
private lemma enc_wildcard {k n : ℕ} (w : Fin n → Fin k) (P : Finset (Fin n)) (v : Fin k) :
    enc k n (fun i => if i ∈ P then v else w i)
      = (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ P), (w i : ℕ) * k ^ (i : ℕ))
        + (v : ℕ) * (∑ i ∈ P, k ^ (i : ℕ)) := by
  have hPeq : (Finset.univ.filter (fun i : Fin n => i ∈ P)) = P := by ext i; simp
  rw [enc]
  rw [show (∑ i : Fin n, (((fun i : Fin n => if i ∈ P then v else w i) i : Fin k) : ℕ) * k ^ (i : ℕ))
      = ∑ i : Fin n, (if i ∈ P then (v : ℕ) * k ^ (i : ℕ) else (w i : ℕ) * k ^ (i : ℕ)) from by
        apply Finset.sum_congr rfl; intro i _
        rw [show ((if i ∈ P then v else w i : Fin k) : ℕ)
            = (if i ∈ P then (v : ℕ) else (w i : ℕ)) from by
          by_cases h : i ∈ P <;> simp [h]]
        rw [ite_mul]]
  rw [Finset.sum_ite]
  rw [hPeq]
  rw [← Finset.mul_sum]
  exact add_comm _ _

/-- **Szemeredi's result from the density Hales-Jewett statement (DHJ).**
DHJ: for every `k ≥ 2` and `δ > 0` there is `n₀` such that for `n ≥ n₀` every
`T : Finset (Fin n → Fin k)` with `δ * k^n ≤ |T|` contains a combinatorial line, i.e.
there are `w : Fin n → Fin k` and a nonempty wildcard set `P` such that for every
`v : Fin k` the point agreeing with `w` outside `P` and equal to `v` on `P` lies in `T`.
Then the finitary Szemeredi statement follows: reading the digits of `Fin n → Fin k` as a
base-`k` expansion identifies `[k]^n` with `{0, …, k^n - 1}`, and a combinatorial line
becomes a `k`-term arithmetic progression of common difference `∑_{i ∈ P} k^i`. -/
theorem finite_szemeredi_of_density_hales_jewett
    (hdhj : ∀ k : ℕ, 2 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ T : Finset (Fin n → Fin k), δ * (k : ℝ) ^ n ≤ (T.card : ℝ) →
        ∃ w : Fin n → Fin k, ∃ P : Finset (Fin n), P.Nonempty ∧
          ∀ v : Fin k, (fun i => if i ∈ P then v else w i) ∈ T) :
    ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : Finset ℕ,
      B ⊆ Finset.range N → δ * (N : ℝ) ≤ (B.card : ℝ) →
        ∃ a b : ℕ, 1 ≤ b ∧ ∀ j : ℕ, j < k → a + b * j ∈ (B : Set ℕ) := by
  intro k δ hδ
  rcases lt_or_ge k 2 with hk | hk
  · -- `k ≤ 1`: a single element of `B` already witnesses the (vacuous or length-`1`) AP
    refine ⟨1, fun N hN B hB hcard => ?_⟩
    have hNpos : 0 < N := by omega
    have hBpos : 0 < B.card := by
      have h1 : (0 : ℝ) < (B.card : ℝ) :=
        lt_of_lt_of_le (mul_pos hδ (by exact_mod_cast hNpos)) hcard
      exact_mod_cast h1
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hBpos
    refine ⟨a, 1, le_refl 1, fun j hj => ?_⟩
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using ha
  · -- main case `k ≥ 2`
    have hk2 : 2 ≤ k := hk
    have hk1 : 1 < k := by omega
    obtain ⟨n₀, hn₀⟩ := hdhj k hk2 (δ / k) (by positivity)
    refine ⟨k ^ n₀, fun N hN₀ B hB hcard => ?_⟩
    have hN1 : 1 ≤ N := by
      have : 1 ≤ k ^ n₀ := Nat.one_le_pow n₀ k (by omega)
      omega
    have hNne : N ≠ 0 := by omega
    set n : ℕ := Nat.log k N + 1 with hn
    have hNlt : N < k ^ n := by
      rw [hn]
      exact Nat.lt_pow_succ_log_self hk1 N
    have hkn : k ^ n ≤ k * N := by
      have h := Nat.pow_log_le_self k hNne
      calc k ^ n = k ^ Nat.log k N * k := by rw [hn, pow_succ]
        _ ≤ N * k := Nat.mul_le_mul_right k h
        _ = k * N := by ring
    have hnn₀ : n₀ ≤ n := by
      have h := Nat.le_log_of_pow_le hk1 (show k ^ n₀ ≤ N from hN₀)
      rw [hn]; omega
    have hB' : B ⊆ Finset.range (k ^ n) := fun b hb =>
      Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp (hB hb)) hNlt)
    let T : Finset (Fin n → Fin k) :=
      (Finset.univ : Finset (Fin n → Fin k)).filter (fun x => enc k n x ∈ B)
    have hTcard : T.card = B.card := by
      dsimp only [T]
      exact card_filter_enc hk2 B hB'
    have hdens : (δ / k) * (k : ℝ) ^ n ≤ (T.card : ℝ) := by
      rw [hTcard]
      have h1 : ((k : ℝ) ^ n) ≤ (k : ℝ) * (N : ℝ) := by
        rw [← Nat.cast_pow, ← Nat.cast_mul]
        exact_mod_cast hkn
      have h3 : (δ / k) * ((k : ℝ) * (N : ℝ)) = δ * N := by
        rw [← mul_assoc, div_mul_cancel₀ δ (by positivity : (k : ℝ) ≠ 0)]
      have h4 : (δ / k) * ((k : ℝ) ^ n) ≤ (δ / k) * ((k : ℝ) * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [h3] at h4
      linarith [hcard]
    obtain ⟨w, P, hPne, hline⟩ := hn₀ n hnn₀ T hdens
    refine ⟨∑ i ∈ Finset.univ.filter (fun i : Fin n => i ∉ P), (w i : ℕ) * k ^ (i : ℕ),
      ∑ i ∈ P, k ^ (i : ℕ), ?_, ?_⟩
    · -- the common difference `∑_{i ∈ P} k^i` is positive since `P` is nonempty
      obtain ⟨i₀, hi₀⟩ := hPne
      have hle : k ^ (i₀ : ℕ) ≤ ∑ i ∈ P, k ^ (i : ℕ) :=
        Finset.single_le_sum (s := P) (f := fun i : Fin n => k ^ (i : ℕ))
          (fun i _ => Nat.zero_le _) hi₀
      have h1 : 1 ≤ k ^ (i₀ : ℕ) := Nat.one_le_pow (i₀ : ℕ) k (by omega)
      omega
    · intro j hj
      set v : Fin k := ⟨j, hj⟩ with hv
      have hmem : (fun i => if i ∈ P then v else w i) ∈ T := hline v
      have henc : enc k n (fun i => if i ∈ P then v else w i) ∈ B :=
        (Finset.mem_filter.mp hmem).2
      rw [enc_wildcard] at henc
      have hvj : (v : ℕ) = j := rfl
      rw [hvj, Nat.mul_comm j (∑ i ∈ P, k ^ (i : ℕ))] at henc
      simpa using henc

end Commons.Combinatorics.Additive.Szemeredi
