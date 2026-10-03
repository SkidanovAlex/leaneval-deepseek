import Mathlib
import Submission.Work.Pert.pert2v2.orbit_pieces
import Submission.Work.Pert.pert2v2.level_offsets_shift
import Submission.Work.Pert.pert2v2.orbit_row

/-!
# `Work.Pert.pert2v2.orbit_row_mem` — the `orbit` row WITH the membership clause

`PertData.orbit`'s conclusion carries, besides the value statement `φ w' = f^n (φ w)`, the
membership clause `∀ i < n, f^[i] (φ w) ∈ Df` (the `n` iterates are honest values of the
perturbation, not junk of the total function `f`).

The value statement is `pert2v2.orbit_row` (PROVED); the membership clause is produced here from
the *same* telescoping, once the piece relations `hpiece` are known to carry their own membership
`∀ i < l, f^[i] (φ y) ∈ Df`.

## Why the membership is covered

With the canonical offsets `t j = -k j` (`level_offsets_shift`) one has `k j + t j = 0`, so the
chart point `R^[j] w + t j` coincides with the *reduced* point `x j` (`hzx`), and the level of the
`j`-th piece is `lo j = k j + t (j+1) = t (j+1) - t j` (`hlot`).  Hence `t j + lo j = t (j+1)`:
the index intervals `[t j, t j + lo j)` **tile** `[0, n) = [0, t m)`.  Since the telescoping gives
`φ (R^[j] w + t j) = f^[t j] (φ w)` (`hkey`), the membership clause of the `j`-th piece —
`∀ i < lo j, f^[i] (φ (x j)) ∈ Df` — converts into
`∀ i < lo j, f^[t j + i] (φ w) ∈ Df`, and the tiling covers every index `i < n`.
-/

namespace Work.Pert.pert2v2

open Work.Pert Complex Set

noncomputable section

/-- **The `orbit` row with the membership clause.**  Same telescoping as `orbit_pieces`, with the
offsets `t` satisfying the cancellation `k j + t j = 0` (the canonical choice of
`level_offsets_shift`); the piece relations additionally carry `∀ i < l, f^[i] (φ y) ∈ Df`, and
the conclusion carries the corresponding membership `∀ i < n, f^[i] (φ w) ∈ Df`. -/
lemma orbit_pieces_mem {f φ R : ℂ → ℂ} {Df Dφ : Set ℂ} {P : Bool → ℂ → ℂ}
    {Ulow Uhigh : Set ℂ} {m₀ m n : ℕ} {w w' : ℂ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hpiece : ∀ (b : Bool) (y : ℂ), (b = true → y ∈ Ulow) → (b = false → y ∈ Uhigh) →
      ∀ l : ℕ, (b = true → m₀ ≤ l) → P b y + (l : ℂ) ∈ Dφ →
        φ (P b y + (l : ℂ)) = f^[l] (φ y) ∧ ∀ i : ℕ, i < l → f^[i] (φ y) ∈ Df)
    (hUlowDφ : Ulow ⊆ Dφ) (hUhighDφ : Uhigh ⊆ Dφ)
    {x : ℕ → ℂ} {k : ℕ → ℤ} {b : ℕ → Bool} {t lo : ℕ → ℕ}
    (ht0 : t 0 = 0) (htm : t m = n) (htmono : Monotone t)
    (hkt : ∀ j, j < m → (k j : ℂ) + (t j : ℂ) = 0)
    (hdec : ∀ j < m, R^[j] w = x j + (k j : ℂ))
    (hside : ∀ j < m, (b j = true → x j ∈ Ulow) ∧ (b j = false → x j ∈ Uhigh))
    (hR : ∀ j < m, R (R^[j] w) = P (b j) (x j) + (k j : ℂ))
    (hlcast : ∀ j < m, ((lo j : ℕ) : ℤ) = k j + (t (j + 1) : ℤ))
    (hlom₀ : ∀ j < m, b j = true → m₀ ≤ lo j)
    (hymem : ∀ j < m, P (b j) (x j) + (lo j : ℂ) ∈ Dφ)
    (hw' : w' = R^[m] w + (n : ℂ)) :
    φ w' = f^[n] (φ w) ∧ ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df := by
  classical
  -- the cancellation in `ℤ`
  have hktZ : ∀ j, j < m → k j + (t j : ℤ) = 0 := by
    intro j hj
    have h2 := hkt j hj
    have h3 : ((k j + (t j : ℤ) : ℤ) : ℂ) = 0 := by
      push_cast
      exact h2
    exact_mod_cast h3
  -- the integer segment of the telescoping is the single point `x j`
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
  -- the value statement (the PROVED `orbit_pieces`)
  have hval : φ w' = f^[n] (φ w) :=
    orbit_pieces P (fun z hz hz1 => (hAbel z hz hz1).2)
      (fun b y h1 h2 l hl hmem => (hpiece b y h1 h2 l hl hmem).1)
      t x k b lo ht0 htm htmono hdec hR hside hlcast hlom₀ hseg hymem hw'
  refine ⟨hval, ?_⟩
  -- the piece relation, its two halves
  have hpiece_val : ∀ j < m, φ (P (b j) (x j) + (lo j : ℂ)) = f^[lo j] (φ (x j)) :=
    fun j hj =>
      (hpiece (b j) (x j) (hside j hj).1 (hside j hj).2 (lo j) (hlom₀ j hj) (hymem j hj)).1
  have hpiece_mem : ∀ j < m, ∀ i : ℕ, i < lo j → f^[i] (φ (x j)) ∈ Df :=
    fun j hj i hi =>
      (hpiece (b j) (x j) (hside j hj).1 (hside j hj).2 (lo j) (hlom₀ j hj) (hymem j hj)).2 i hi
  -- the chart point at level `j` is the reduced point `x j`
  have hzx : ∀ j < m, R^[j] w + ((t j : ℕ) : ℂ) = x j := by
    intro j hj
    rw [hdec j hj, add_assoc, hkt j hj, add_zero]
  -- the piece is applied at the chart point of level `j + 1`
  have hRj : ∀ j < m,
      P (b j) (x j) + ((lo j : ℕ) : ℂ) = R^[j+1] w + ((t (j+1) : ℕ) : ℂ) := by
    intro j hj
    have h1 : R (R^[j] w) = R^[j+1] w := (Function.iterate_succ_apply' R j w).symm
    have hloC : ((lo j : ℕ) : ℂ) = (k j : ℂ) + ((t (j+1) : ℕ) : ℂ) := by
      have h := hlcast j hj
      exact_mod_cast h
    rw [hloC, ← h1, hR j hj]
    ring
  -- the one-step identity of the telescoping
  have hstep : ∀ j < m,
      φ (R^[j+1] w + ((t (j+1) : ℕ) : ℂ))
        = f^[lo j] (φ (R^[j] w + ((t j : ℕ) : ℂ))) := by
    intro j hj
    rw [← hRj j hj, hpiece_val j hj, hzx j hj]
  -- the level of the `j`-th piece is `t (j+1) - t j`
  have hlot : ∀ j < m, lo j = t (j+1) - t j := by
    intro j hj
    have h1 : ((lo j : ℕ) : ℤ) = (t (j+1) : ℤ) - (t j : ℤ) := by
      have h := hlcast j hj
      have h2 := hktZ j hj
      linarith
    have h2 : ((t (j+1) - t j : ℕ) : ℤ) = (t (j+1) : ℤ) - (t j : ℤ) :=
      Nat.cast_sub (htmono (Nat.le_succ j))
    have h3 : ((lo j : ℕ) : ℤ) = ((t (j+1) - t j : ℕ) : ℤ) := by rw [h1, h2]
    exact_mod_cast h3
  -- the telescoping value identity
  have hkey : ∀ j ≤ m, φ (R^[j] w + ((t j : ℕ) : ℂ)) = f^[t j] (φ w) := by
    intro j
    induction j with
    | zero => intro _; simp [ht0]
    | succ j ih =>
      intro hj
      have hj' : j < m := Nat.lt_of_succ_le hj
      rw [hstep j hj', ih (Nat.le_of_lt hj'), ← Function.iterate_add_apply, hlot j hj',
        Nat.sub_add_cancel (htmono (Nat.le_succ j))]
  -- the memberships of the pieces tile `[0, n)`
  have hmemind : ∀ j ≤ m, ∀ i : ℕ, i < t j → f^[i] (φ w) ∈ Df := by
    intro j
    induction j with
    | zero => intro _ i hi; rw [ht0] at hi; omega
    | succ j ih =>
      intro hj i hi
      have hj' : j < m := Nat.lt_of_succ_le hj
      rcases lt_or_ge i (t j) with hlt | hge
      · exact ih (Nat.le_of_lt hj') i hlt
      · have hkeyj : f^[t j] (φ w) = φ (x j) := by
          rw [← hkey j (Nat.le_of_lt hj'), hzx j hj']
        have h2 : i - t j < lo j := by
          have := hlot j hj'
          omega
        have h1 : i = (i - t j) + t j := by omega
        rw [h1, Function.iterate_add_apply, hkeyj]
        exact hpiece_mem j hj' (i - t j) h2
  intro i hi
  rw [← htm] at hi
  exact hmemind m le_rfl i hi

/-- `PertData.orbit`'s full row: value and membership, for the walk `R^[j] w = x j + k j` with
antitone nonpositive shifts `k` and the canonical offsets `t j = -k j`.  The value statement is
`orbit_row`'s; the membership is `orbit_pieces_mem`'s. -/
theorem orbit_row_mem {f φ R : ℂ → ℂ} {Df Dφ : Set ℂ} {P : Bool → ℂ → ℂ} {Ulow Uhigh : Set ℂ}
    {m₀ m n : ℕ} {w w' : ℂ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ z ∈ Df ∧ φ (z + 1) = f (φ z))
    (hpiece : ∀ (b : Bool) (y : ℂ), (b = true → y ∈ Ulow) → (b = false → y ∈ Uhigh) →
      ∀ l : ℕ, (b = true → m₀ ≤ l) → P b y + (l : ℂ) ∈ Dφ →
        φ (P b y + (l : ℂ)) = f^[l] (φ y) ∧ ∀ i : ℕ, i < l → f^[i] (φ y) ∈ Df)
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
    φ w' = f^[n] (φ w) ∧ ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df := by
  classical
  obtain ⟨t, ht0, htm, htmono, htform, htlev⟩ :=
    level_offsets_shift (m₀ := m₀) (m := m) (n := n) (k := k) hm hanti hneg hnmono hmemlast hlvl
  -- the levels `lo j := k j + t (j+1) ≥ m₀`
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
  -- the cancellation `k j + t j = 0`
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
  -- the shifted point is the next reduced chart point, resp. `w'`
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
  -- the level condition
  have hlo₀ : ∀ j < m, b j = true → m₀ ≤ lo j := by
    intro j hj _
    have h1 : ((lo j : ℕ) : ℤ) = k j + (t (j+1) : ℤ) := hlocast j hj
    have h2 : (m₀ : ℤ) ≤ ((lo j : ℕ) : ℤ) := by rw [h1]; exact htlev j hj
    exact_mod_cast h2
  exact orbit_pieces_mem hAbel hpiece hUlowDφ hUhighDφ ht0 htm htmono hkt hdec hside hR
    hlocast hlo₀ hymem hw'

end

end Work.Pert.pert2v2
