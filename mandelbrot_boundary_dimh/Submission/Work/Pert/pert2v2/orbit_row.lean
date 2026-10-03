import Mathlib
import Submission.Work.Pert.pert2v2.orbit_pieces
import Submission.Work.Pert.pert2v2.level_offsets_shift

/-!
# `Work.Pert.pert2v2.orbit_row` — the SOLE remaining row of the `orbit` field

`PertData.orbit`'s value statement `φ w' = f^n (φ w)` for `w' = R^m w + n` is produced by
`orbit_pieces`, a telescoping whose free offsets `t` satisfy

`k j + t (j+1) ≥ m₀`  (the level of the low piece's relation)

with `k j` the chart shift (`R^[j] w = x j + k j`).  The canonical choice `t j = n` gives the huge
`k j + n`, which forces the shifted point `P (b j) (x j) + lo j` far outside the chart (`hymem`) and
the segment (`hseg`) far away from the chart point.

This file records the **correct choice** `t j := -k j` (`1 ≤ j ≤ m-1`), for which

* `k j + t j = 0`, so `hseg` is the single point `x j ∈ Dφ` (from `hside`);
* `P (b j) (x j) + lo j = x (j+1)` for `j + 1 < m` (and `= w'` for `j = m-1`), so `hymem` is
  `hside` again;
* `lo j = k j - k (j+1) ≥ m₀` — the level condition, available as a `δ₀`-condition because
  `k j - k (j+1) ≈ Re (1/α)` can be made larger than the datum constant `m₀` (the crux's landing
  time) by shrinking `δ₀`.

`level_offsets_shift` supplies the offsets and `orbit_pieces` performs the telescoping.
-/

namespace Work.Pert.pert2v2

open Work.Pert Complex Set

noncomputable section

/-- **The `orbit` row.**  With the two chart pieces `P true` (on `Ulow`) and `P false` (on
`Uhigh`), the piece relations `φ (P b y + l) = f^l (φ y)`, the chart decomposition of the walk
`R^[j] w = x j + k j` (with `k` antitone, `k 0 = 0`, `k j ≤ 0`), the returns `R (R^[j] w)` given by
the piece of the chart, the memberships of the *reduced* points `x (j+1)` and of `w'`, and the
level conditions `k j - k (j+1) ≥ m₀`, `k (m-1) + n ≥ m₀`, `-k (m-1) ≤ n`, one gets

  `φ w' = f^n (φ w)`  for  `w' = R^m w + n`.

All hypotheses are of the shape the design produces: `hside` from `DR = ⋃ n, (·+n)''(Ulow ∪ Uhigh)`,
`hR` from the T-equivariance of `R` and the chart formulas, `hmem1` from the chart membership of the
reduced walk points, `hseg`/`hymem` become empty/free by the choice of `t`. -/
theorem orbit_row {f φ R : ℂ → ℂ} {Df Dφ : Set ℂ} {P : Bool → ℂ → ℂ} {Ulow Uhigh : Set ℂ}
    {m₀ m n : ℕ} {w w' : ℂ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hpiece : ∀ (b : Bool) (y : ℂ), (b = true → y ∈ Ulow) → (b = false → y ∈ Uhigh) →
      ∀ l : ℕ, (b = true → m₀ ≤ l) → P b y + (l : ℂ) ∈ Dφ →
        φ (P b y + (l : ℂ)) = f^[l] (φ y))
    (hUlowDφ : Ulow ⊆ Dφ) (hUhighDφ : Uhigh ⊆ Dφ)
    {x : ℕ → ℂ} {k : ℕ → ℤ} {b : ℕ → Bool}
    (hm : 1 ≤ m) (hk0 : k 0 = 0)
    (hdec : ∀ j < m, R^[j] w = x j + (k j : ℂ))
    (hside : ∀ j < m, (b j = true → x j ∈ Ulow) ∧ (b j = false → x j ∈ Uhigh))
    (hR : ∀ j < m, R (R^[j] w) = P (b j) (x j) + (k j : ℂ))
    (hanti : ∀ j, j + 1 < m → k (j+1) ≤ k j)
    (hneg : ∀ j, 1 ≤ j → j ≤ m - 1 → k j ≤ 0)
    (hmem1 : ∀ j, j + 1 < m → x (j+1) ∈ Dφ)
    (hw' : w' = R^[m] w + (n : ℂ)) (hw'Dφ : w' ∈ Dφ)
    (hlvl : ∀ j, j + 1 < m → (m₀ : ℤ) ≤ k j - k (j+1))
    (hnmono : ((-k (m-1)).toNat : ℕ) ≤ n)
    (hmemlast : (m₀ : ℤ) ≤ k (m-1) + (n : ℤ)) :
    φ w' = f^[n] (φ w) := by
  classical
  obtain ⟨t, ht0, htm, htmono, htform, htlev⟩ :=
    level_offsets_shift (m₀ := m₀) (m := m) (n := n) (k := k) hm hanti hneg hnmono hmemlast hlvl
  -- the levels `lo j := k j + t (j+1)`
  set lo : ℕ → ℕ := fun j => (k j + (t (j+1) : ℤ)).toNat with hlo
  have hlocast : ∀ j < m, ((lo j : ℕ) : ℤ) = k j + (t (j+1) : ℤ) := by
    intro j hj
    have hge : (0 : ℤ) ≤ k j + (t (j+1) : ℤ) := by
      have h1 := htlev j hj
      have h2 : (0 : ℤ) ≤ (m₀ : ℤ) := Int.natCast_nonneg m₀
      linarith
    simp only [hlo]
    exact Int.toNat_of_nonneg hge
  -- `t j = - k j` for `1 ≤ j ≤ m-1`
  have htj : ∀ j, 1 ≤ j → j ≤ m - 1 → (t j : ℤ) = - k j := by
    intro j hj1 hjm
    have h := htform (j - 1) (by omega)
    have hcast : j - 1 + 1 = j := by omega
    rwa [hcast] at h
  -- `k j + t j = 0` as complex numbers, for `j < m`
  have hkt : ∀ j, j < m → (k j : ℂ) + ((t j : ℕ) : ℂ) = 0 := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [ht0, hk0]
      simp
    · have hjm : j ≤ m - 1 := by omega
      have hnn : (0 : ℤ) ≤ - k j := by
        have := hneg j hpos hjm
        linarith
      have h1 : (t j : ℤ) = - k j := htj j hpos hjm
      have h2 : (t j : ℕ) = (- k j).toNat := by
        have h2' : (t j : ℤ) = (((- k j).toNat : ℕ) : ℤ) := by
          rw [h1]
          exact (Int.toNat_of_nonneg hnn).symm
        exact_mod_cast h2'
      rw [h2]
      have h3 : ((((- k j).toNat : ℕ)) : ℂ) = ((- k j : ℤ) : ℂ) := by
        have h4 : ((((- k j).toNat : ℕ)) : ℤ) = (- k j : ℤ) := Int.toNat_of_nonneg hnn
        exact_mod_cast h4
      rw [h3]
      push_cast
      ring
  -- and the same identity in `ℤ`
  have hktZ : ∀ j, j < m → k j + (t j : ℤ) = 0 := by
    intro j hj
    have h2 := hkt j hj
    have h3 : ((k j + (t j : ℤ) : ℤ) : ℂ) = 0 := by
      push_cast
      exact h2
    exact_mod_cast h3
  -- `hseg`: the integer segment is the single point `x j`
  have hseg : ∀ j < m, ∀ i : ℤ,
      i ∈ Set.Icc (min (k j + (t j : ℤ)) 0) (max (k j + (t j : ℤ)) 0) →
        x j + (i : ℂ) ∈ Dφ := by
    intro j hj i hi
    rw [hktZ j hj] at hi
    simp only [Set.mem_Icc, min_self, max_self] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp only [Int.cast_zero, add_zero]
    rcases hside j hj with ⟨hU, hV⟩
    cases hbj : b j with
    | true => exact hUlowDφ (hU hbj)
    | false => exact hUhighDφ (hV hbj)
  -- `hymem`: the shifted point is the next reduced chart point, resp. `w'`
  have hymem : ∀ j < m, P (b j) (x j) + (lo j : ℂ) ∈ Dφ := by
    intro j hj
    have hRj : R (R^[j] w) = R^[j+1] w := (Function.iterate_succ_apply' R j w).symm
    have hloc : ((lo j : ℕ) : ℂ) = (k j : ℂ) + ((t (j+1) : ℕ) : ℂ) := by
      have h := hlocast j hj
      exact_mod_cast h
    have h1 : P (b j) (x j) + (k j : ℂ) = R^[j+1] w := by
      rw [← hR j hj, hRj]
    have hkey : P (b j) (x j) + (lo j : ℂ) = R^[j+1] w + ((t (j+1) : ℕ) : ℂ) := by
      calc P (b j) (x j) + (lo j : ℂ)
          = (P (b j) (x j) + (k j : ℂ)) + ((t (j+1) : ℕ) : ℂ) := by rw [hloc]; ring
        _ = R^[j+1] w + ((t (j+1) : ℕ) : ℂ) := by rw [h1]
    rw [hkey]
    rcases lt_or_eq_of_le (Nat.succ_le_iff.mpr hj) with hlt | heq
    · have h2 := hkt (j+1) hlt
      have h3 : R^[j+1] w + ((t (j+1) : ℕ) : ℂ) = x (j+1) := by
        rw [hdec (j+1) hlt]
        linear_combination h2
      rw [h3]
      exact hmem1 j hlt
    · have hjm : j + 1 = m := heq
      have h3 : R^[j+1] w + ((t (j+1) : ℕ) : ℂ) = w' := by
        rw [show j + 1 = m from hjm, htm, ← hw']
      rw [h3]
      exact hw'Dφ
  have hlo₀ : ∀ j < m, b j = true → m₀ ≤ lo j := by
    intro j hj _
    have h1 : ((lo j : ℕ) : ℤ) = k j + (t (j+1) : ℤ) := hlocast j hj
    have h2 : (m₀ : ℤ) ≤ ((lo j : ℕ) : ℤ) := by rw [h1]; exact htlev j hj
    exact_mod_cast h2
  exact orbit_pieces P (fun z hz hz1 => (hAbel z hz hz1).2) hpiece t x k b lo ht0 htm htmono
    hdec hR hside hlocast hlo₀ hseg hymem hw'

end

end Work.Pert.pert2v2
