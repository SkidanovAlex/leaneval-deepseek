import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Checking `σ₁(n) ≤ C` on a range of `n` by kernel computation

`sigmaSqrt n` computes `σ₁(n)` by pairing the divisors `d ≤ √n` with `n / d`.  A bound `σ₁(n) ≤ C` on a range of `n` is
checked by `decide +kernel` on chunks `List.range' a k`, and `sigma_le_of_check` reads a single
`n` off a chunk.  Short chunks (ten values each) keep the kernel's memory per declaration small;
checking a long range in one declaration, or with `interval_cases n <;> decide` in the elaborator,
costs several GB.
-/

namespace Commons.NumberTheory.SigmaCheck

/-! ## σ computed by pairing divisors around `√n` -/

def sigmaSqrt (n : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0

lemma divisors_filter_le_sqrt_eq (n : ℕ) (hn : 0 < n) :
    n.divisors.filter (fun d => d ≤ Nat.sqrt n) =
      (Finset.Icc 1 (Nat.sqrt n)).filter (fun d => d ∣ n) := by
  ext d
  by_cases hdpos : 0 < d
  · simp [Nat.mem_divisors, Finset.mem_filter, hn.ne']
    constructor
    · intro h
      exact ⟨⟨by omega, h.2⟩, h.1⟩
    · intro h
      exact ⟨h.2, h.1.2⟩
  · have hd0 : d = 0 := by omega
    subst d
    simp [hn.ne']

lemma large_divisors_sum_eq (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => Nat.sqrt n < d), d) =
      ∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n), n / d := by
  refine Finset.sum_bij (fun d hd => n / d) ?hi ?hinj ?hsurj ?h
  · intro d hd
    have hdmem := (Finset.mem_filter.mp hd).1
    have hdgt := (Finset.mem_filter.mp hd).2
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hdmem).1
    have hdpos : 0 < d := by
      have : 0 ≤ Nat.sqrt n := Nat.zero_le _
      omega
    have hndvd : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
    have hndmem : n / d ∈ n.divisors := Nat.mem_divisors.mpr ⟨hndvd, by omega⟩
    have hdecomp0 : n / d * d = n := Nat.div_mul_cancel hdvd
    have hdecomp : n = d * (n / d) := by
      simpa [mul_comm] using hdecomp0.symm
    have hndpos : 0 < n / d := by
      exact Nat.div_pos (Nat.le_of_dvd hn hdvd) hdpos
    have hnd_lt_d : n / d < d := by
      have hmain : n < d * d := by
        rw [← Nat.sqrt_lt]
        exact hdgt
      rw [hdecomp] at hmain
      exact (Nat.mul_lt_mul_left hdpos).mp hmain
    have hmul : n / d * (n / d) < n := by
      have h1 : n / d * (n / d) < n / d * d := by
        exact (Nat.mul_lt_mul_left hndpos).mpr hnd_lt_d
      simpa [hdecomp0] using h1
    have hnd_le_sqrt : n / d ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      exact le_of_lt hmul
    have hnd_nonsq : n / d * (n / d) ≠ n := by
      omega
    exact Finset.mem_filter.mpr ⟨hndmem, ⟨hnd_le_sqrt, hnd_nonsq⟩⟩
  · intro a ha b hb hab
    have hamem := (Finset.mem_filter.mp ha).1
    have hbmem := (Finset.mem_filter.mp hb).1
    have hadvd : a ∣ n := (Nat.mem_divisors.mp hamem).1
    have hbdvd : b ∣ n := (Nat.mem_divisors.mp hbmem).1
    have hdiva : n / (n / a) = a := Nat.div_div_self hadvd (by omega)
    have hdivb : n / (n / b) = b := Nat.div_div_self hbdvd (by omega)
    calc
      a = n / (n / a) := hdiva.symm
      _ = n / (n / b) := by rw [hab]
      _ = b := hdivb
  · intro b hb
    have hbmem := (Finset.mem_filter.mp hb).1
    have hble := (Finset.mem_filter.mp hb).2.1
    have hbns := (Finset.mem_filter.mp hb).2.2
    have hbdvd : b ∣ n := (Nat.mem_divisors.mp hbmem).1
    have hbpos : 0 < b := by
      by_contra hb0
      have hb0' : b = 0 := by omega
      subst b
      simp at hbdvd
      omega
    have hdpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos
    have hdecomp0 : n / b * b = n := Nat.div_mul_cancel hbdvd
    have hdecomp : n = b * (n / b) := by
      simpa [mul_comm] using hdecomp0.symm
    have hb_le_sq : b * b ≤ n := by
      rw [Nat.le_sqrt] at hble
      exact hble
    have hb_sq_lt : b * b < n := lt_of_le_of_ne hb_le_sq hbns
    have hb_lt_nd : b < n / b := by
      rw [hdecomp] at hb_sq_lt
      exact (Nat.mul_lt_mul_left hbpos).mp hb_sq_lt
    have hndgt : Nat.sqrt n < n / b := by
      rw [Nat.sqrt_lt]
      have h1 : b * (n / b) < (n / b) * (n / b) := by
        exact (Nat.mul_lt_mul_right hdpos).mpr hb_lt_nd
      calc
        n = b * (n / b) := hdecomp
        _ < (n / b) * (n / b) := h1
    have hndvd : n / b ∣ n := Nat.div_dvd_of_dvd hbdvd
    have hndmem : n / b ∈ n.divisors := Nat.mem_divisors.mpr ⟨hndvd, by omega⟩
    refine ⟨n / b, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hndmem, hndgt⟩
    · rw [Nat.div_div_self hbdvd (by omega)]
  · intro a ha
    have hamem := (Finset.mem_filter.mp ha).1
    have hadvd : a ∣ n := (Nat.mem_divisors.mp hamem).1
    exact (Nat.div_div_self hadvd (by omega)).symm

lemma sigma_eq_sigmaSqrt (n : ℕ) (hn : 0 < n) :
    (ArithmeticFunction.sigma 1 n : ℕ) = sigmaSqrt n := by
  rw [ArithmeticFunction.sigma_one_apply]
  unfold sigmaSqrt
  let s : Finset ℕ := n.divisors.filter (fun d => d ≤ Nat.sqrt n)
  let t : Finset ℕ := n.divisors.filter (fun d => Nat.sqrt n < d)
  have hset := divisors_filter_le_sqrt_eq n hn
  have hsmall_final : (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0 := by
    change (∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.sqrt n), (if d * d = n then d else d + n / d)) =
      ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0
    rw [hset]
    rw [Finset.sum_filter]
  have hsplit_total : (∑ d ∈ n.divisors, d) =
      (∑ d ∈ s, d) + (∑ d ∈ t, d) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => d ≤ Nat.sqrt n) (f := fun d : ℕ => d)
    change (∑ d ∈ n.divisors, d) = (∑ d ∈ s, d) + (∑ d ∈ t, d)
    simpa [s, t, not_le] using h.symm
  have hsplit_small_id : (∑ d ∈ s, d) =
      (∑ d ∈ s.filter (fun d => d * d = n), d) +
        (∑ d ∈ s.filter (fun d => d * d ≠ n), d) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun d => d * d = n) (f := fun d : ℕ => d)
    simpa using h.symm
  have hsplit_small_f : (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
      (∑ d ∈ s.filter (fun d => d * d = n), d) +
        (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by
    have h := Finset.sum_filter_add_sum_filter_not (s := s) (p := fun d => d * d = n) (f := fun d : ℕ => (if d * d = n then d else d + n / d))
    have hsq : (∑ d ∈ s.filter (fun d => d * d = n), (if d * d = n then d else d + n / d)) =
        ∑ d ∈ s.filter (fun d => d * d = n), d := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d * d = n := (Finset.mem_filter.mp hd).2
      simp [hd']
    have hnsq : (∑ d ∈ s.filter (fun d => d * d ≠ n), (if d * d = n then d else d + n / d)) =
        ∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hd' : d * d ≠ n := (Finset.mem_filter.mp hd).2
      simp [hd']
    calc
      (∑ d ∈ s, (if d * d = n then d else d + n / d)) =
          (∑ d ∈ s.filter (fun d => d * d = n), (if d * d = n then d else d + n / d)) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), (if d * d = n then d else d + n / d)) := h.symm
      _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by rw [hsq, hnsq]
  have hlarge := large_divisors_sum_eq n hn
  have hlarge' : (∑ d ∈ t, d) =
      ∑ d ∈ s.filter (fun d => d * d ≠ n), n / d := by
    change (∑ d ∈ n.divisors.filter (fun d => Nat.sqrt n < d), d) =
      ∑ d ∈ s.filter (fun d => d * d ≠ n), n / d
    rw [hlarge]
    have hfilter : n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n) =
        s.filter (fun d => d * d ≠ n) := by
      change n.divisors.filter (fun d => d ≤ Nat.sqrt n ∧ d * d ≠ n) =
          (n.divisors.filter (fun d => d ≤ Nat.sqrt n)).filter (fun d => d * d ≠ n)
      rw [Finset.filter_filter]
    rw [hfilter]
  calc
    ∑ d ∈ n.divisors, d = (∑ d ∈ s, d) + (∑ d ∈ t, d) := hsplit_total
    _ = ((∑ d ∈ s.filter (fun d => d * d = n), d) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), d)) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), n / d) := by rw [hsplit_small_id, hlarge']
    _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
          ((∑ d ∈ s.filter (fun d => d * d ≠ n), d) +
            (∑ d ∈ s.filter (fun d => d * d ≠ n), n / d)) := by omega
    _ = (∑ d ∈ s.filter (fun d => d * d = n), d) +
          (∑ d ∈ s.filter (fun d => d * d ≠ n), (d + n / d)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ d ∈ s, (if d * d = n then d else d + n / d) := by
          rw [hsplit_small_f]
    _ = ∑ d ∈ Finset.Icc 1 (Nat.sqrt n), if d ∣ n then (if d * d = n then d else d + n / d) else 0 := hsmall_final

/-- The check at one `m`: `m > 0` and `σ₁(m) ≤ C`, with `σ₁` computed by `sigmaSqrt`. -/
def sigmaChk (C m : ℕ) : Bool := decide (0 < m) && decide (sigmaSqrt m ≤ C)

/-- Read `σ₁(n) ≤ C` off a kernel-checked chunk `[a, a + k)` containing `n`. -/
theorem sigma_le_of_check {C a k : ℕ}
    (h : (List.range' a k).all (sigmaChk C) = true)
    (n : ℕ) (h1 : a ≤ n) (h2 : n < a + k) : (ArithmeticFunction.sigma 1 n : ℕ) ≤ C := by
  have hn := List.all_eq_true.mp h n (List.mem_range'_1.mpr ⟨h1, h2⟩)
  simp only [sigmaChk, Bool.and_eq_true, decide_eq_true_eq] at hn
  rw [sigma_eq_sigmaSqrt n hn.1]
  exact hn.2

end Commons.NumberTheory.SigmaCheck
