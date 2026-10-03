import Mathlib
import Submission.Work.FatouCoord.Setup

/-!
# Extending a Fatou coordinate along the orbit

Generic skeleton used by `exists_left_chart_coordinate`.  Given `G : ℂ → ℂ` (in the
application `G = wMap F`), a level `N` and a Fatou coordinate `ψ` with `ψ (G x) = ψ x + 1`
on `{N < x.re}`, we extend `ψ` to the escaping set `Esc N G = {x | ∃ n, Good N G x n}` by
`Psi N G ψ x = ψ (G^[nIdx N G x] x) - nIdx N G x`, where `nIdx` is the first index at which
the orbit enters `{N < ·.re}`.
-/

open Classical

namespace Work.Parab.leftCoord

open Set Filter Metric
open scoped Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {N : ℝ} {G ψ : ℂ → ℂ} {x : ℂ} {k n : ℕ}

/-- The first `n` iterates of `x` stay outside the disc of radius `N`, the real parts stay
below `N` up to step `n - 1`, and at step `n` the real part exceeds `N`. -/
def Good (N : ℝ) (G : ℂ → ℂ) (x : ℂ) (n : ℕ) : Prop :=
  (∀ k ≤ n, N < ‖G^[k] x‖) ∧ (∀ k < n, (G^[k] x).re < N) ∧ N < (G^[n] x).re

/-- The escaping set. -/
def Esc (N : ℝ) (G : ℂ → ℂ) : Set ℂ := {x | ∃ n, Good N G x n}

/-- The first index at which the orbit enters `{Re > N}`. -/
noncomputable def nIdx (N : ℝ) (G : ℂ → ℂ) (x : ℂ) : ℕ :=
  if h : ∃ n, Good N G x n then Nat.find h else 0

/-- The extension of `ψ` to the escaping set. -/
noncomputable def Psi (N : ℝ) (G : ℂ → ℂ) (ψ : ℂ → ℂ) (x : ℂ) : ℂ :=
  ψ (G^[nIdx N G x] x) - (nIdx N G x : ℂ)

lemma iterate_shift (G : ℂ → ℂ) (k : ℕ) (x : ℂ) : G^[k] (G x) = G^[k+1] x := by
  rw [Function.iterate_add_apply, Function.iterate_one]

lemma nIdx_spec (h : Esc N G x) : Good N G x (nIdx N G x) := by
  obtain ⟨n, hn⟩ := h
  unfold nIdx
  rw [dif_pos ⟨n, hn⟩]
  exact Nat.find_spec ⟨n, hn⟩

lemma nIdx_le (h : Good N G x n) : nIdx N G x ≤ n := by
  unfold nIdx
  rw [dif_pos ⟨n, h⟩]
  exact Nat.find_min' ⟨n, h⟩ h

lemma Psi_apply : Psi N G ψ x = ψ (G^[nIdx N G x] x) - (nIdx N G x : ℂ) := rfl

lemma mem_Esc_iff : x ∈ Esc N G ↔ ∃ n, Good N G x n := Iff.rfl

lemma Good.zero (h : N < x.re) : Good N G x 0 := by
  refine ⟨?_, fun k hk => absurd hk (Nat.not_lt_zero k), by simpa using h⟩
  intro k hk
  rw [Nat.le_zero.mp hk, Function.iterate_zero_apply]
  exact lt_of_lt_of_le h (Complex.re_le_norm x)

lemma Psi_eq_of_re (h : N < x.re) : Psi N G ψ x = ψ x := by
  have h0 : nIdx N G x ≤ 0 := nIdx_le (Good.zero h)
  have hz : nIdx N G x = 0 := Nat.le_zero.mp h0
  simp [Psi_apply, hz]

/-- `Esc` is forward invariant as soon as `G` maps `{Re > N}` into itself. -/
lemma Esc_map (hG : ∀ x, N < x.re → N < (G x).re) (hx : Esc N G x) : Esc N G (G x) := by
  obtain ⟨h1, h2, h3⟩ := nIdx_spec hx
  by_cases hn0 : nIdx N G x = 0
  · have hxN : N < x.re := by
      have h := h3; rw [hn0] at h; simpa using h
    exact ⟨0, ⟨fun k hk => by
        rw [Nat.le_zero.mp hk, Function.iterate_zero_apply]
        exact lt_of_lt_of_le (hG x hxN) (Complex.re_le_norm (G x)),
      fun k hk => absurd hk (Nat.not_lt_zero k), by simpa using hG x hxN⟩⟩
  · have hnpos : 0 < nIdx N G x := Nat.pos_of_ne_zero hn0
    have hs : nIdx N G x - 1 + 1 = nIdx N G x := Nat.sub_add_cancel (by omega)
    refine ⟨nIdx N G x - 1, ?_, ?_, ?_⟩
    · intro k hk
      have hk' : k + 1 ≤ nIdx N G x := by omega
      have h := h1 (k + 1) hk'
      rwa [← iterate_shift] at h
    · intro k hk
      have hk' : k + 1 < nIdx N G x := by omega
      have h := h2 (k + 1) hk'
      rwa [← iterate_shift] at h
    · have h := h3
      rw [← hs] at h
      rwa [← iterate_shift] at h

/-- On `{Good N G · n}` the index equals `n`. -/
lemma nIdx_eq_of_good (h1 : ∀ k ≤ n, N < ‖G^[k] x‖)
    (h2 : ∀ k < n, (G^[k] x).re < N) (h3 : N < (G^[n] x).re) : nIdx N G x = n := by
  have hg : Good N G x n := ⟨h1, h2, h3⟩
  refine le_antisymm (nIdx_le hg) ?_
  by_contra hlt
  push_neg at hlt
  have hspec := nIdx_spec ⟨n, hg⟩
  exact absurd hspec.2.2 (not_lt.mpr (le_of_lt (hg.2.1 _ hlt)))

/-- **Abel equation for the extension.** -/
lemma Psi_abel (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hx : Esc N G x) : Psi N G ψ (G x) = Psi N G ψ x + 1 := by
  obtain ⟨h1, h2, h3⟩ := nIdx_spec hx
  by_cases hn0 : nIdx N G x = 0
  · have hxN : N < x.re := by
      have h := h3; rw [hn0] at h; simpa using h
    have hGxN : N < (G x).re := hG x hxN
    rw [Psi_eq_of_re hGxN, Psi_eq_of_re hxN]
    exact habel x hxN
  · have hnpos : 0 < nIdx N G x := Nat.pos_of_ne_zero hn0
    set m := nIdx N G x with hm
    have hgood : Good N G (G x) (m - 1) := by
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        have hk' : k + 1 ≤ m := by omega
        have h := h1 (k + 1) hk'
        rwa [← iterate_shift] at h
      · intro k hk
        have hk' : k + 1 < m := by omega
        have h := h2 (k + 1) hk'
        rwa [← iterate_shift] at h
      · have hs : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        have h := h3
        rw [← hs] at h
        rwa [← iterate_shift] at h
    have hle : nIdx N G (G x) ≤ m - 1 := nIdx_le hgood
    have hge : m - 1 ≤ nIdx N G (G x) := by
      by_contra hcon
      push_neg at hcon
      have hspec := nIdx_spec (Esc_map hG hx)
      have hmgood : Good N G x (nIdx N G (G x) + 1) := by
        refine ⟨?_, ?_, ?_⟩
        · intro k hk
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0; simpa using h1 0 (Nat.zero_le m)
          · have hk1 : k - 1 ≤ nIdx N G (G x) := by omega
            have hkk : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
            have h := hspec.1 (k - 1) hk1
            rwa [iterate_shift, hkk] at h
        · intro k hk
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0; simpa using h2 0 (by omega)
          · have hk1 : k - 1 < nIdx N G (G x) := by omega
            have hkk : k - 1 + 1 = k := Nat.sub_add_cancel (by omega : 1 ≤ k)
            have h := hspec.2.1 (k - 1) hk1
            rwa [iterate_shift, hkk] at h
        · have h := hspec.2.2
          rwa [iterate_shift] at h
      have hcontra := nIdx_le hmgood
      rw [← hm] at hcontra
      omega
    have heq : nIdx N G (G x) = m - 1 := le_antisymm hle hge
    have hiter : G^[m - 1] (G x) = G^[m] x := by
      rw [iterate_shift, Nat.sub_add_cancel (by omega : 1 ≤ m)]
    have hcast : ((m : ℕ) : ℂ) = ((m - 1 : ℕ) : ℂ) + 1 := by
      rw [← Nat.sub_add_cancel (by omega : 1 ≤ m)]; push_cast; ring
    rw [Psi_apply, Psi_apply, heq, ← hm, hiter, hcast]
    ring

/-- The set `{Good N G · n}` is open. -/
lemma isOpen_good (hcont : Continuous G) (n : ℕ) : IsOpen {x : ℂ | Good N G x n} := by
  have h1 : IsOpen {x : ℂ | ∀ k ≤ n, N < ‖G^[k] x‖} := by
    rw [show {x : ℂ | ∀ k ≤ n, N < ‖G^[k] x‖}
        = ⋂ k ∈ Finset.range (n + 1), {x : ℂ | N < ‖G^[k] x‖} by
      ext x; simp [Finset.mem_range, Nat.lt_succ_iff]]
    exact isOpen_biInter_finset fun k _ => isOpen_lt continuous_const ((hcont.iterate k).norm)
  have h2 : IsOpen {x : ℂ | ∀ k < n, (G^[k] x).re < N} := by
    rw [show {x : ℂ | ∀ k < n, (G^[k] x).re < N}
        = ⋂ k ∈ Finset.range n, {x : ℂ | (G^[k] x).re < N} by
      ext x; simp [Finset.mem_range]]
    exact isOpen_biInter_finset fun k _ =>
      isOpen_lt (Complex.continuous_re.comp (hcont.iterate k)) continuous_const
  have h3 : IsOpen {x : ℂ | N < (G^[n] x).re} :=
    isOpen_lt continuous_const (Complex.continuous_re.comp (hcont.iterate n))
  exact h1.inter (h2.inter h3)

/-- The escaping set is open. -/
lemma isOpen_Esc (hcont : Continuous G) : IsOpen (Esc N G) := by
  rw [show Esc N G = ⋃ n, {x : ℂ | Good N G x n} by ext x; simp [Esc, mem_Esc_iff]]
  exact isOpen_iUnion fun n => isOpen_good hcont n

end Work.Parab.leftCoord
