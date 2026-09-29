import Mathlib
import Submission.Work.Resample.buQWdefs
import Submission.Work.Resample.buQWhs
import Submission.Work.Resample.buR1_vsz_buColsT

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.Resample

open HvdH

/-!
# `Work.Resample.buQWtab`: the size of the static table entries of the `B̃` word

The word `q` of the one-dimensional `B̃` map reads, besides the five scalars, five static table
entries off the value stack: the two key lists `buKeysT`, `buKeysS`, the diagonal weights `buWdL`,
the columns of shift weights `buColsT` and the list of signs `buSignsT` of the Neumann fold.  Each
of them is used as the cost parameter (`vsz`) of a `WordR` triple, so the five bounds below are the
bridging estimates between the program-level statement and the `O(s·p)` cost budget of the paper
(Lemmas 4.10--4.12).

All five are pure list arithmetic: `vsz (zl l) = l.length + 1 + Σ isz` for a list of integers and
`vsz (ofList l) = l.length + 1 + Σ vsz` for a window; the integer entries are bounded by the two
hypotheses `hwt` (weights `< 2^{p+1}`) and `hwd` (diagonal weights `< 2^p`), the key entries by
`s + t ≤ 2^{p+1}`.
-/

/-- `isz z ≤ k + 3` when `|z| ≤ 2^k` (the `≤` version of `Work.Fx.isz_le_of_natAbs_lt`). -/
private lemma buQWtab_isz_le_of_le {z : ℤ} {k : ℕ} (h : z.natAbs ≤ 2 ^ k) : isz z ≤ k + 3 := by
  have h1 : z.natAbs < 2 ^ (k + 1) :=
    lt_of_le_of_lt h (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self k))
  have h2 := Work.Fx.isz_le_of_natAbs_lt (a := z) (n := k + 1) h1
  omega

/-- `Σ isz` over a list of integers, bounded termwise. -/
private lemma buQWtab_sum_le {l : List ℤ} {M : ℕ} (h : ∀ z ∈ l, isz z ≤ M) :
    (l.map isz).sum ≤ l.length * M := by
  have hb : ∀ x ∈ l.map isz, x ≤ M := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
    exact h z hz
  simpa using buR1_sum_le_length_mul hb

/-- `Σ vsz` over a window of values, bounded termwise. -/
private lemma buQWtab_val_sum_le {l : List Val} {M : ℕ} (h : ∀ x ∈ l, vsz x ≤ M) :
    (l.map vsz).sum ≤ l.length * M := by
  have hb : ∀ x ∈ l.map vsz, x ≤ M := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
    exact h z hz
  simpa using buR1_sum_le_length_mul hb

/-- A list of `c` entries of `isz`-size `≤ p+4` has `vsz ≤ 2(c+1)(p+4)`: the numeric end of the
three `zl`-bounds below. -/
private lemma buQWtab_last {c S p : ℕ} (hS : S ≤ c * (p + 4)) :
    c + 1 + S ≤ 2 * (c + 1) * (p + 4) := by
  have h2 : c + 1 ≤ (c + 1) * (p + 4) := by
    simpa using Nat.mul_le_mul_left (c + 1) (show 1 ≤ p + 4 by omega)
  have h3 : c * (p + 4) ≤ (c + 1) * (p + 4) := Nat.mul_le_mul_right _ (by omega)
  linarith

/-- **Key list of the fused `C̃ ∘ P̃_t` step.**  The entries `egLam s t i` are either `< s` or
`s + i`, hence `< 2^{p+1}`; there are `t` of them. -/
private lemma buQWtab_keysT (p s t : ℕ) (hst : s < t) (htp : t < 2 ^ p) :
    vsz (buKeysT s t) ≤ 2 * (t + 1) * (p + 4) := by
  have hpw : (2 : ℕ) ^ (p + 1) = 2 * 2 ^ p := by rw [pow_succ]; ring
  have hmem : ∀ z ∈ List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ)), isz z ≤ p + 4 := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    have hlt : (egLam s t (i : ℕ) : ℤ).natAbs < 2 ^ (p + 1) := by
      have hi : (i : ℕ) < t := i.isLt
      rw [egLam]
      split_ifs with h
      · rw [Int.natAbs_natCast, hpw]
        have := (Classical.choose h : Fin s).isLt
        omega
      · rw [Int.natAbs_natCast, hpw]
        omega
    have h2 := Work.Fx.isz_le_of_natAbs_lt hlt
    omega
  have hsum : ((List.ofFn (fun i : Fin t => (egLam s t (i : ℕ) : ℤ))).map isz).sum ≤
      t * (p + 4) := by
    have h := buQWtab_sum_le hmem
    simpa using h
  unfold buKeysT
  rw [buR1_vsz_zl, List.length_ofFn]
  exact le_trans (Nat.add_le_add_left hsum (t + 1)) (buQWtab_last le_rfl)

/-- **Key list of the final `P̃_sᵀ` step.**  The entries `(t i) mod s` are `< s < 2^p`. -/
private lemma buQWtab_keysS (p s t : ℕ) (hs : 0 < s) (hst : s < t) (htp : t < 2 ^ p) :
    vsz (buKeysS s t) ≤ 2 * (s + 1) * (p + 4) := by
  have hmem : ∀ z ∈ List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ)), isz z ≤ p + 4 := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    have hlt : ((egKeyS s t (i : ℕ) : ℕ) : ℤ).natAbs < 2 ^ p := by
      rw [Int.natAbs_natCast]
      show (t * (i : ℕ)) % s < 2 ^ p
      have := Nat.mod_lt (t * (i : ℕ)) hs
      omega
    have h2 := Work.Fx.isz_le_of_natAbs_lt hlt
    omega
  have hsum : ((List.ofFn (fun i : Fin s => (egKeyS s t (i : ℕ) : ℤ))).map isz).sum ≤
      s * (p + 4) := by
    have h := buQWtab_sum_le hmem
    simpa using h
  unfold buKeysS
  rw [buR1_vsz_zl, List.length_ofFn]
  exact le_trans (Nat.add_le_add_left hsum (s + 1)) (buQWtab_last le_rfl)

/-- **Diagonal weights.**  `hwd` gives `|buWd| < 2^p`, so each of the `s` entries has `isz ≤ p+2`. -/
private lemma buQWtab_wdL (p α s t : ℕ)
    (hwd : ∀ ℓ : ℤ, 8 * (buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p) :
    vsz (buWdL p α s t) ≤ 2 * (s + 1) * (p + 4) := by
  have hmem : ∀ z ∈ List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ)), isz z ≤ p + 4 := by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    have hlt : (buWd p α s t (i : ℤ)).natAbs < 2 ^ p := by
      have h1 := hwd (i : ℤ)
      have h2 : 3 * 2 ^ p < 8 * 2 ^ p :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) (Nat.two_pow_pos p)
      exact Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 h2)
    have h2 := Work.Fx.isz_le_of_natAbs_lt hlt
    omega
  have hsum : ((List.ofFn (fun i : Fin s => buWd p α s t (i : ℤ))).map isz).sum ≤
      s * (p + 4) := by
    have h := buQWtab_sum_le hmem
    simpa using h
  unfold buWdL
  rw [buR1_vsz_zl, List.length_ofFn]
  exact le_trans (Nat.add_le_add_left hsum (s + 1)) (buQWtab_last le_rfl)

/-- **Columns of shift weights.**  `2·egM p α` entries `cons (int h) (col h)`, each of size
`≤ 3(s+1)(p+4)`, and the window bound `(2·egM+1)·3 ≤ 8(egM+1)`. -/
private lemma buQWtab_colsT (p α s t : ℕ)
    (hwt : ∀ ℓ h : ℤ, h ≠ 0 → (buWt p α s t ℓ h).natAbs ≤ 2 ^ (p + 1)) :
    vsz (buColsT p α s t) ≤ 8 * (egM p α + 1) * (s + 1) * (p + 4) := by
  obtain ⟨_, _, hlen, hne, hle, _⟩ := buQWhs (egM p α)
  have hMle : egM p α ≤ p + 1 := buR1_egM_le p α
  have hcol : ∀ h ∈ egHs (egM p α), vsz (buCol p α s t h) ≤ s + 1 + s * (p + 4) := by
    intro h hh
    have hb : ∀ z ∈ List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h), isz z ≤ p + 4 := by
      intro z hz
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact buQWtab_isz_le_of_le (hwt (i : ℤ) h (hne h hh))
    have hsum : ((List.ofFn (fun ℓ : Fin s => buWt p α s t (ℓ : ℤ) h)).map isz).sum ≤
        s * (p + 4) := by
      have h := buQWtab_sum_le hb
      simpa using h
    unfold buCol
    rw [buR1_vsz_zl, List.length_ofFn]
    omega
  have hel : ∀ h ∈ egHs (egM p α),
      vsz (Val.cons (.int h) (buCol p α s t h)) ≤ 3 * ((s + 1) * (p + 4)) := by
    intro h hh
    rw [Work.Fx.vsz_cons, Work.Fx.vsz_int]
    have hhle : h.natAbs ≤ p + 1 := le_trans (hle h hh) hMle
    have hlt2 : h.natAbs < 2 ^ (p + 1) :=
      lt_of_le_of_lt hhle (Nat.lt_two_pow_self (n := p + 1))
    have hhiz : isz h ≤ p + 3 := by
      have h := Work.Fx.isz_le_of_natAbs_lt (a := h) (n := p + 1) hlt2
      omega
    have hc := hcol h hh
    have key : (p + 3) + (s + 1 + s * (p + 4)) + 1 ≤ 3 * ((s + 1) * (p + 4)) := by
      have hA : s ≤ s * (p + 4) := by
        simpa using Nat.mul_le_mul_left s (show 1 ≤ p + 4 by omega)
      have hB : p + 5 ≤ 3 * (p + 4) := by omega
      have e1 : 3 * ((s + 1) * (p + 4)) = 3 * (s * (p + 4)) + 3 * (p + 4) := by ring
      rw [e1]
      linarith [hA, hB, Nat.zero_le (s * (p + 4))]
    exact le_trans (Nat.add_le_add (Nat.add_le_add hhiz hc) (le_refl 1)) key
  unfold buColsT
  rw [buR1_vsz_ofList]
  have hlen2 : (List.map (fun h => Val.cons (.int h) (buCol p α s t h)) (egHs (egM p α))).length =
      2 * egM p α := by
    rw [List.length_map, hlen]
  have hsum2 : ((List.map (fun h => Val.cons (.int h) (buCol p α s t h))
      (egHs (egM p α))).map vsz).sum ≤ 2 * egM p α * (3 * ((s + 1) * (p + 4))) := by
    have hb : ∀ x ∈ List.map (fun h => Val.cons (.int h) (buCol p α s t h)) (egHs (egM p α)),
        vsz x ≤ 3 * ((s + 1) * (p + 4)) := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨h, hh, rfl⟩
      exact hel h hh
    have h := buQWtab_val_sum_le hb
    simp only [List.length_map] at h
    rw [hlen] at h
    exact h
  rw [hlen2]
  have hS1 : 1 ≤ (s + 1) * (p + 4) := by
    have := Nat.mul_le_mul (show 1 ≤ s + 1 by omega) (show 1 ≤ p + 4 by omega)
    simpa using this
  have key : 2 * egM p α + 1 + 2 * egM p α * (3 * ((s + 1) * (p + 4))) ≤
      8 * (egM p α + 1) * (s + 1) * (p + 4) := by
    have hM : egM p α ≤ egM p α * ((s + 1) * (p + 4)) := by
      simpa using Nat.mul_le_mul_left (egM p α) hS1
    have h2 : 1 ≤ 8 * ((s + 1) * (p + 4)) := by linarith [hS1]
    have h3 : 2 * egM p α * (3 * ((s + 1) * (p + 4))) =
        6 * (egM p α * ((s + 1) * (p + 4))) := by ring
    have h4 : 8 * (egM p α + 1) * (s + 1) * (p + 4) =
        8 * (egM p α * ((s + 1) * (p + 4))) + 8 * ((s + 1) * (p + 4)) := by ring
    rw [h3, h4]
    linarith [hM, h2]
  exact le_trans (Nat.add_le_add_left hsum2 (2 * egM p α + 1)) key

/-- **Sign list of the Neumann fold.**  Every entry is `±1`, of `isz`-size `3`. -/
private lemma buQWtab_signsT (p α s t : ℕ) :
    vsz (buSignsT p α s t) ≤ 8 * (egN p α s t + 1) := by
  have hmem : ∀ z ∈ (List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1)), isz z ≤ 3 := by
    intro z hz
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hz
    rw [isz]
    have h1 : ((-1 : ℤ) ^ (j + 1)).natAbs = 1 := by
      rw [Int.natAbs_pow]
      norm_num
    rw [h1]
    norm_num
  have hsum : (((List.range (egN p α s t - 1)).map (fun j => (-1 : ℤ) ^ (j + 1))).map isz).sum ≤
      (egN p α s t - 1) * 3 := by
    have h := buQWtab_sum_le hmem
    simpa using h
  unfold buSignsT
  rw [buR1_vsz_zl, List.length_map, List.length_range]
  omega

theorem buQWtab (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (htp : t < 2 ^ p) (hα : 2 ≤ α)
    (hp : 100 ≤ p)
    (hwt : ∀ ℓ h : ℤ, h ≠ 0 → (Work.Resample.buWt p α s t ℓ h).natAbs ≤ 2 ^ (p + 1))
    (hwd : ∀ ℓ : ℤ, 8 * (Work.Resample.buWd p α s t ℓ).natAbs ≤ 3 * 2 ^ p) :
    HvdH.vsz (Work.Resample.buKeysT s t) ≤ 2 * (t + 1) * (p + 4) ∧
    HvdH.vsz (Work.Resample.buKeysS s t) ≤ 2 * (s + 1) * (p + 4) ∧
    HvdH.vsz (Work.Resample.buWdL p α s t) ≤ 2 * (s + 1) * (p + 4) ∧
    HvdH.vsz (Work.Resample.buColsT p α s t) ≤ 8 * (Work.Resample.egM p α + 1) * (s + 1) * (p + 4) ∧
    HvdH.vsz (Work.Resample.buSignsT p α s t) ≤ 8 * (Work.Resample.egN p α s t + 1) := by
  have hs0 : 0 < s := by omega
  exact ⟨buQWtab_keysT p s t hst htp, buQWtab_keysS p s t hs0 hst htp, buQWtab_wdL p α s t hwd,
    buQWtab_colsT p α s t hwt, buQWtab_signsT p α s t⟩

end Work.Resample
