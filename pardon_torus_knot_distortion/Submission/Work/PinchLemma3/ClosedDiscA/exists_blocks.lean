import Mathlib
import Submission.Work.SurgeryInvariance.Defs

namespace Work.PinchLemma3.ClosedDiscA

/-- `Work.PinchLemma3.ClosedDiscA.exists_blocks` : a non-constant `N`-periodic Boolean
sequence on `ℕ` admits a decomposition of a fundamental period into an even number `2 k` of
consecutive constant blocks of alternating values, starting with `true`.

The proof picks a "true-run start" `e0 ∈ [0, N)` (a site with value `true` whose cyclic
predecessor has value `false`) and lets `e` enumerate the successive maximal-run starts.
Since the run starts of a periodic word are themselves `N`-periodic, the run through `e0`
returns to `e0 + N` after an even number of steps. -/
theorem exists_blocks {N : ℕ} (hN : 0 < N) (ℓ : ℕ → Bool) (hper : ∀ i, ℓ (i + N) = ℓ i)
    (hex : ∃ i j, i < N ∧ j < N ∧ ℓ i ≠ ℓ j) :
    ∃ (k : ℕ) (_ : 0 < k) (e : ℕ → ℕ),
      (∀ i, i < 2 * k → e i < e (i + 1)) ∧ e 0 < N ∧ e (2 * k) = e 0 + N ∧
      (∀ i, i < 2 * k → (ℓ (e i) = true ↔ Even i)) ∧
      (∀ i, i < 2 * k → ∀ j, e i ≤ j → j < e (i + 1) → ℓ j = ℓ (e i)) := by
  -- (0) periodicity:  ℓ (n + N * t) = ℓ n
  have perK : ∀ (n t : ℕ), ℓ (n + N * t) = ℓ n := by
    intro n t
    induction t with
    | zero => simp
    | succ t ih =>
      have h : n + N * (t + 1) = (n + N * t) + N := by rw [Nat.mul_succ]; omega
      rw [h, hper, ih]
  have bnt : ∀ b : Bool, ¬ (b = true) → b = false := by
    intro b h; cases b <;> simp_all
  have bnf : ∀ b : Bool, ¬ (b = false) → b = true := by
    intro b h; cases b <;> simp_all
  -- (1) there is a false site and a true site in `[0, N)`
  obtain ⟨i0, j0, hi0, hj0, hij⟩ := hex
  have hle : ∀ a b : Bool, a ≠ b → a = false ∨ b = false := by
    intro a b hab; cases a <;> cases b <;> simp_all
  have htr : ∀ a b : Bool, a ≠ b → a = true ∨ b = true := by
    intro a b hab; cases a <;> cases b <;> simp_all
  have hfex : ∃ f, f < N ∧ ℓ f = false := by
    rcases hle (ℓ i0) (ℓ j0) hij with h | h
    · exact ⟨i0, hi0, h⟩
    · exact ⟨j0, hj0, h⟩
  obtain ⟨f, hfN, hffalse⟩ := hfex
  have htex : ∃ t, t < N ∧ ℓ t = true := by
    rcases htr (ℓ i0) (ℓ j0) hij with h | h
    · exact ⟨i0, hi0, h⟩
    · exact ⟨j0, hj0, h⟩
  obtain ⟨t0, ht0N, ht0true⟩ := htex
  -- (2) a true site to the "cyclic right" of `f`, within one period
  have hexw : ∃ w, f < w ∧ w ≤ f + N ∧ ℓ w = true := by
    by_cases hft : f < t0
    · exact ⟨t0, hft, by omega, ht0true⟩
    · refine ⟨t0 + N, by omega, by omega, ?_⟩
      rw [hper t0, ht0true]
  obtain ⟨w0, hw0gt, hw0le, hw0true⟩ := hexw
  have hQ : ∃ p, f < p ∧ ℓ p = true := ⟨w0, hw0gt, hw0true⟩
  let p := Nat.find hQ
  have hp_gt : f < p := (Nat.find_spec hQ).1
  have hp_true : ℓ p = true := (Nat.find_spec hQ).2
  have hp_le : p ≤ f + N :=
    le_trans (Nat.find_le (show f < w0 ∧ ℓ w0 = true from ⟨hw0gt, hw0true⟩)) hw0le
  -- `p` is the start of a maximal `true`-run
  have hp_min : ∀ m, f ≤ m → m < p → ℓ m = false := by
    intro m hfm hmp
    rcases eq_or_lt_of_le hfm with h | h
    · rw [← h]; exact hffalse
    · have hnot : ¬ (f < m ∧ ℓ m = true) := Nat.find_min hQ hmp
      have hm : ¬ (ℓ m = true) := fun hh => hnot ⟨h, hh⟩
      exact bnt (ℓ m) hm
  have hp_pred : ℓ (p - 1) = false := hp_min (p - 1) (by omega) (by omega)
  -- (3) reduce `p` into the fundamental window `[0, N)`
  let e0 := if p < N then p else p - N
  have he0N : e0 < N := by
    by_cases hpN : p < N
    · simp only [e0, if_pos hpN]; exact hpN
    · simp only [e0, if_neg hpN]
      have hpN' : N ≤ p := not_lt.mp hpN
      omega
  have he0true : ℓ e0 = true := by
    by_cases hpN : p < N
    · simp only [e0, if_pos hpN]; exact hp_true
    · simp only [e0, if_neg hpN]
      have hpN' : N ≤ p := not_lt.mp hpN
      have h1 : p - N + N = p := by omega
      have h2 : ℓ (p - N + N) = ℓ (p - N) := hper (p - N)
      rw [h1] at h2
      rw [← h2]; exact hp_true
  have he0Nm1 : ℓ (e0 + N - 1) = false := by
    by_cases hpN : p < N
    · simp only [e0, if_pos hpN]
      have h1 : p + N - 1 = (p - 1) + N := by omega
      rw [h1, hper]; exact hp_pred
    · simp only [e0, if_neg hpN]
      have hpN' : N ≤ p := not_lt.mp hpN
      have h1 : p - N + N - 1 = p - 1 := by omega
      rw [h1]; exact hp_pred
  have he0Ntrue : ℓ (e0 + N) = true := by
    have := hper e0; rw [this, he0true]
  -- (4) the "next different value" map
  have hEx : ∀ s, ∃ m, s < m ∧ ℓ m ≠ ℓ s := by
    intro s
    have hmul : s + 1 ≤ N * (s + 1) := by
      have h := Nat.mul_le_mul hN (le_refl (s + 1))
      simpa using h
    have hgt1 : s < i0 + N * (s + 1) := by omega
    have hgt2 : s < j0 + N * (s + 1) := by omega
    have h1 : ℓ (i0 + N * (s + 1)) = ℓ i0 := perK i0 (s + 1)
    have h2 : ℓ (j0 + N * (s + 1)) = ℓ j0 := perK j0 (s + 1)
    by_cases hcase : ℓ i0 = ℓ s
    · refine ⟨j0 + N * (s + 1), hgt2, ?_⟩
      rw [h2]
      intro hjj
      exact hij (hcase.trans hjj.symm)
    · refine ⟨i0 + N * (s + 1), hgt1, ?_⟩
      rw [h1]; exact hcase
  let nxt : ℕ → ℕ := fun s => Nat.find (hEx s)
  have nxt_gt : ∀ s, s < nxt s := fun s => (Nat.find_spec (hEx s)).1
  have nxt_ne : ∀ s, ℓ (nxt s) ≠ ℓ s := fun s => (Nat.find_spec (hEx s)).2
  have nxt_min : ∀ s m, s < m → m < nxt s → ℓ m = ℓ s := by
    intro s m h1 h2
    have hnot := Nat.find_min (hEx s) h2
    by_contra hne
    exact hnot ⟨h1, hne⟩
  -- (5) the run-start sequence
  let S : ℕ → ℕ := fun t => (nxt^[t]) e0
  have S_zero : S 0 = e0 := Function.iterate_zero_apply nxt e0
  have S_succ : ∀ t, S (t + 1) = nxt (S t) := by
    intro t
    exact Function.iterate_succ_apply' nxt t e0
  have S_inc : ∀ t, S t < S (t + 1) := by
    intro t; rw [S_succ t]; exact nxt_gt (S t)
  have S_mono : ∀ t, e0 + t ≤ S t := by
    intro t
    induction t with
    | zero => simp [S_zero]
    | succ t ih => have := S_inc t; omega
  have S_const : ∀ t j, S t ≤ j → j < S (t + 1) → ℓ j = ℓ (S t) := by
    intro t j hj1 hj2
    rcases eq_or_lt_of_le hj1 with h | h
    · rw [h]
    · have h2 : j < nxt (S t) := by rw [S_succ t] at hj2; exact hj2
      exact nxt_min (S t) j h h2
  have S_alt : ∀ t, (ℓ (S t) = true ↔ Even t) := by
    intro t
    induction t with
    | zero =>
      rw [S_zero]
      exact ⟨fun _ => ⟨0, rfl⟩, fun _ => he0true⟩
    | succ t ih =>
      have hne : ℓ (S (t + 1)) ≠ ℓ (S t) := by rw [S_succ t]; exact nxt_ne (S t)
      have hiff : (ℓ (S (t + 1)) = true) ↔ ¬ (ℓ (S t) = true) := by
        cases ha : ℓ (S (t + 1)) <;> cases hb : ℓ (S t) <;> simp_all
      rw [hiff, Nat.even_add_one]
      exact not_congr ih
  -- (6) first index with `S t ≥ e0 + N`
  have hP : ∃ t, e0 + N ≤ S t := ⟨N, S_mono N⟩
  let M := Nat.find hP
  have hM_spec : e0 + N ≤ S M := Nat.find_spec hP
  have hM_min : ∀ t, t < M → S t < e0 + N := by
    intro t ht
    have hnot : ¬ (e0 + N ≤ S t) := Nat.find_min hP ht
    exact not_le.mp hnot
  have hM_pos : 0 < M := by
    by_contra h
    have h0 : M = 0 := by omega
    rw [h0, S_zero] at hM_spec
    omega
  -- (7) `M` is even, using that `e0 + N` is a genuine "descent"
  have hM_even : Even M := by
    by_contra h
    have hodd : Odd M := Nat.not_even_iff_odd.mp h
    obtain ⟨c, hc⟩ := hodd
    have hme : Even (M - 1) := ⟨c, by rw [hc]; omega⟩
    have hSM1_true : ℓ (S (M - 1)) = true := (S_alt (M - 1)).2 hme
    have hlt : S (M - 1) < e0 + N := hM_min (M - 1) (by omega)
    have hge : S (M - 1) ≤ e0 + N - 1 := by omega
    have hlt2 : e0 + N - 1 < S M := by omega
    have hlt' : e0 + N - 1 < S ((M - 1) + 1) := by
      rw [show (M - 1) + 1 = M by omega]; exact hlt2
    have hconst : ℓ (e0 + N - 1) = ℓ (S (M - 1)) := S_const (M - 1) (e0 + N - 1) hge hlt'
    rw [hSM1_true] at hconst
    rw [he0Nm1] at hconst
    exact Bool.false_ne_true hconst
  -- (8) `S M = e0 + N`
  obtain ⟨k, hk⟩ := hM_even
  have hkpos : 0 < k := by omega
  have h2k : 2 * k = M := by rw [two_mul, hk]
  have hSM : S M = e0 + N := by
    have hk1 : 1 ≤ k := by omega
    have hoddM1 : Odd (M - 1) := ⟨k - 1, by rw [hk]; omega⟩
    have hodd : ¬ Even (M - 1) := Nat.not_even_iff_odd.mpr hoddM1
    have hSM1_false : ℓ (S (M - 1)) = false := by
      by_contra h
      have ht : ℓ (S (M - 1)) = true := bnf _ h
      exact hodd ((S_alt (M - 1)).1 ht)
    have hlt : S (M - 1) < e0 + N := hM_min (M - 1) (by omega)
    have h2 : ℓ (e0 + N) ≠ ℓ (S (M - 1)) := by
      rw [he0Ntrue, hSM1_false]
      intro hh
      exact Bool.false_ne_true hh.symm
    have hle : nxt (S (M - 1)) ≤ e0 + N := Nat.find_min' (hEx (S (M - 1))) ⟨hlt, h2⟩
    have hSMeq : S M = nxt (S (M - 1)) := by
      have hMsplit : M = (M - 1) + 1 := by omega
      conv_lhs => rw [hMsplit]
      exact S_succ (M - 1)
    rw [hSMeq] at hM_spec
    rw [hSMeq]
    omega
  -- (9) assemble
  let e : ℕ → ℕ := fun i => if i ≤ 2 * k then S i else S (2 * k) + (i - 2 * k)
  have he_lt : ∀ i, i ≤ 2 * k → e i = S i := by
    intro i hi
    show (if i ≤ 2 * k then S i else S (2 * k) + (i - 2 * k)) = S i
    rw [if_pos hi]
  refine ⟨k, hkpos, e, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [he_lt i (by omega), he_lt (i + 1) (by omega)]
    exact S_inc i
  · rw [he_lt 0 (by omega), S_zero]; exact he0N
  · rw [he_lt (2 * k) le_rfl, h2k, hSM, he_lt 0 (by omega), S_zero]
  · intro i hi
    rw [he_lt i (by omega)]
    exact S_alt i
  · intro i hi j hj1 hj2
    rw [he_lt i (by omega)] at hj1
    rw [he_lt (i + 1) (by omega)] at hj2
    rw [he_lt i (by omega)]
    exact S_const i j hj1 hj2

end Work.PinchLemma3.ClosedDiscA
