import Mathlib

namespace Work.Pert.pert2v2

open Complex Set

/-- **Abel iteration along the positive unit steps of `Dφ`.**

If `φ` increases by `f` under the translation `z ↦ z + 1` (whenever both points lie in `Dφ`), and
`a, a+1, …, a+N ∈ Dφ`, then `φ (a + N) = f^[N] (φ a)`. -/
lemma abel_iterate {f φ : ℂ → ℂ} {Dφ : Set ℂ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ (z + 1) = f (φ z)) (a : ℂ) :
    ∀ N : ℕ, (∀ i ≤ N, a + (i : ℂ) ∈ Dφ) → φ (a + (N : ℂ)) = f^[N] (φ a) := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro h
    have hN : ∀ i ≤ N, a + (i : ℂ) ∈ Dφ := fun i hi => h i (Nat.le_succ_of_le hi)
    have ih' := ih hN
    have eq1 : a + ((Nat.succ N : ℕ) : ℂ) = (a + (N : ℂ)) + 1 := by push_cast; ring
    have hmem1 : a + (N : ℂ) ∈ Dφ := h N (Nat.le_succ N)
    have hmem2 : (a + (N : ℂ)) + 1 ∈ Dφ := by rw [← eq1]; exact h (Nat.succ N) le_rfl
    rw [eq1, hAbel _ hmem1 hmem2, ih', Function.iterate_succ_apply']

/-- **The one-step value comparison.**

`φ` is `f`-equivariant under `z ↦ z+1` on `Dφ`; the whole integer segment between `x` and
`x + (k + t_j)` lies in `Dφ`; `lo = k + t_{j+1}` and `t_j ≤ t_{j+1}`.  Then the `lo`-fold iterate
from `φ x` equals the `(t_{j+1} - t_j)`-fold iterate from the value at the shifted point
`x + (k + t_j)`.

This is the arithmetic/telescoping core of `orbit_pieces`: the integer part `k` cancels. -/
lemma phi_step {f φ : ℂ → ℂ} {Dφ : Set ℂ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ (z + 1) = f (φ z))
    {x : ℂ} {k : ℤ} {tj tj1 lo : ℕ}
    (hlo : (lo : ℤ) = k + (tj1 : ℤ)) (hmono : tj ≤ tj1)
    (hseg : ∀ i : ℤ, i ∈ Set.Icc (min (k + (tj : ℤ)) 0) (max (k + (tj : ℤ)) 0) →
      x + (i : ℂ) ∈ Dφ) :
    f^[lo] (φ x) = f^[tj1 - tj] (φ (x + (((k + (tj : ℤ) : ℤ)) : ℂ))) := by
  set K : ℤ := k + (tj : ℤ) with hK
  have hΔZ : ((tj1 - tj : ℕ) : ℤ) = (tj1 : ℤ) - (tj : ℤ) := by omega
  rcases le_or_gt 0 K with hK0 | hK0
  · -- `K ≥ 0`: walk forward from `x` to `x + K`, then iterate the remaining `t_{j+1} - t_j` steps.
    have hKN : ((K.toNat : ℕ) : ℤ) = K := Int.toNat_of_nonneg hK0
    have hmem : ∀ i ≤ K.toNat, x + (i : ℂ) ∈ Dφ := by
      intro i hi
      have hiZ : (i : ℤ) ∈ Set.Icc (min K 0) (max K 0) := by
        simp only [Set.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [min_eq_right hK0]; exact Int.natCast_nonneg i
        · rw [max_eq_left hK0]
          have hh : (i : ℤ) ≤ (K.toNat : ℤ) := by exact_mod_cast hi
          rwa [hKN] at hh
      have h1 := hseg (i : ℤ) hiZ
      simpa using h1
    have key := abel_iterate hAbel x K.toNat hmem
    have hcast : ((K.toNat : ℕ) : ℂ) = ((K : ℤ) : ℂ) := by exact_mod_cast hKN
    have hsum : (tj1 - tj) + K.toNat = lo := by
      have hh : (((tj1 - tj) + K.toNat : ℕ) : ℤ) = (lo : ℤ) := by
        push_cast
        rw [hΔZ, hKN, hK, hlo]
        ring
      exact_mod_cast hh
    rw [← hsum, Function.iterate_add_apply, ← key, hcast]
  · -- `K < 0`: walk backward from `x + K` to `x` (that leg has length `-K`).
    have hneg : 0 < -K := by omega
    have hKN : (((-K).toNat : ℕ) : ℤ) = -K := Int.toNat_of_nonneg (le_of_lt hneg)
    have hmem : ∀ i ≤ (-K).toNat, (x + ((K : ℤ) : ℂ)) + (i : ℂ) ∈ Dφ := by
      intro i hi
      have hiZ : (K + (i : ℤ)) ∈ Set.Icc (min K 0) (max K 0) := by
        simp only [Set.mem_Icc]
        refine ⟨?_, ?_⟩
        · rw [min_def]; split <;> omega
        · rw [max_def]; split <;> omega
      have h1 := hseg (K + (i : ℤ)) hiZ
      have h2 : x + ((K + (i : ℤ) : ℤ) : ℂ) = (x + ((K : ℤ) : ℂ)) + (i : ℂ) := by
        push_cast; ring
      rwa [h2] at h1
    have key := abel_iterate hAbel (x + ((K : ℤ) : ℂ)) (-K).toNat hmem
    have hxeq : φ x = f^[(-K).toNat] (φ (x + ((K : ℤ) : ℂ))) := by
      rw [← key]
      congr 1
      have hh : (((-K).toNat : ℕ) : ℂ) = ((-K : ℤ) : ℂ) := by exact_mod_cast hKN
      rw [hh]; push_cast; ring
    have hsum : lo + (-K).toNat = tj1 - tj := by
      have hh : ((lo + (-K).toNat : ℕ) : ℤ) = ((tj1 - tj : ℕ) : ℤ) := by
        push_cast
        rw [hKN, hΔZ, hK, hlo]
        ring
      exact_mod_cast hh
    rw [hxeq, ← Function.iterate_add_apply, hsum]

/-- **The `orbit` value statement from the two piece relations.**  The R-block is glued from two
charts `Ulow`, `Uhigh`; on each chart there is a shift relation `φ (P b y + l) = f^l (φ y)` for
`l ≥ m₀` (low, `b = true`) resp. `l ≥ 0` (high, `b = false`).  Then `φ w' = f^n (φ w)` whenever
`w' = R^m w + n`.  The integer offsets `t_j` (`y_j := R^j w + t_j`) are free: the step of the
induction cancels `k_j` and only needs `t_j ≤ t_{j+1}` and `k_j + t_{j+1} ≥ m₀`. -/
theorem orbit_pieces
    {f φ R : ℂ → ℂ} {Dφ : Set ℂ} {w w' : ℂ} {m n m₀ : ℕ}
    (P : Bool → ℂ → ℂ) {Ulow Uhigh : Set ℂ}
    (hAbel : ∀ z ∈ Dφ, z + 1 ∈ Dφ → φ (z + 1) = f (φ z))
    (hpiece : ∀ (b : Bool) (y : ℂ), (b = true → y ∈ Ulow) → (b = false → y ∈ Uhigh) →
      ∀ l : ℕ, (b = true → m₀ ≤ l) → P b y + (l : ℂ) ∈ Dφ →
        φ (P b y + (l : ℂ)) = f^[l] (φ y))
    (t : ℕ → ℕ) (x : ℕ → ℂ) (k : ℕ → ℤ) (b : ℕ → Bool) (lo : ℕ → ℕ)
    (ht0 : t 0 = 0) (htm : t m = n) (htmono : Monotone t)
    (hdec : ∀ j < m, R^[j] w = x j + (k j : ℂ))
    (hR : ∀ j < m, R (R^[j] w) = P (b j) (x j) + (k j : ℂ))
    (hside : ∀ j < m, (b j = true → x j ∈ Ulow) ∧ (b j = false → x j ∈ Uhigh))
    (hlcast : ∀ j < m, ((lo j : ℕ) : ℤ) = k j + (t (j + 1) : ℤ))
    (hlom₀ : ∀ j < m, b j = true → m₀ ≤ lo j)
    (hseg : ∀ j < m, ∀ i : ℤ,
      i ∈ Set.Icc (min (k j + (t j : ℤ)) 0) (max (k j + (t j : ℤ)) 0) → x j + (i : ℂ) ∈ Dφ)
    (hymem : ∀ j < m, P (b j) (x j) + (lo j : ℂ) ∈ Dφ)
    (hw' : w' = R^[m] w + (n : ℂ)) :
    φ w' = f^[n] (φ w) := by
  -- The one-step recurrence for `z_j := R^[j] w + t_j`:
  -- `φ z_{j+1} = f^[t_{j+1} - t_j] (φ z_j)`.
  have hstep : ∀ j < m,
      φ (R^[j+1] w + ((t (j+1) : ℕ) : ℂ))
        = f^[t (j+1) - t j] (φ (R^[j] w + ((t j : ℕ) : ℂ))) := by
    intro j hj
    have hp := hpiece (b j) (x j) (hside j hj).1 (hside j hj).2 (lo j) (hlom₀ j hj) (hymem j hj)
    -- the piece relation is stated at the point `z_{j+1}`
    have hARG : P (b j) (x j) + ((lo j : ℕ) : ℂ)
        = R^[j+1] w + ((t (j+1) : ℕ) : ℂ) := by
      have hRj : R (R^[j] w) = R^[j+1] w := (Function.iterate_succ_apply' R j w).symm
      have hloC : ((lo j : ℕ) : ℂ) = (k j : ℂ) + ((t (j+1) : ℕ) : ℂ) := by
        have h := hlcast j hj
        exact_mod_cast h
      rw [hloC, ← hRj, hR j hj]
      ring
    -- `z_j = x j + (k j + t j)`
    have hxK : R^[j] w + ((t j : ℕ) : ℂ) = x j + (((k j + (t j : ℤ) : ℤ)) : ℂ) := by
      rw [hdec j hj]; push_cast; ring
    rw [← hARG, hp, hxK]
    exact phi_step hAbel (hlcast j hj) (htmono (Nat.le_succ j)) (hseg j hj)
  -- telescoping: `φ z_j = f^[t_j] (φ w)`
  have key : ∀ j ≤ m, φ (R^[j] w + ((t j : ℕ) : ℂ)) = f^[t j] (φ w) := by
    intro j
    induction j with
    | zero => intro _; simp [ht0]
    | succ j ih =>
      intro hj
      have hj' : j < m := Nat.lt_of_succ_le hj
      have hprev := ih (Nat.le_of_lt hj')
      rw [hstep j hj', hprev, ← Function.iterate_add_apply,
        Nat.sub_add_cancel (htmono (Nat.le_succ j))]
  have hm := key m le_rfl
  rw [htm] at hm
  rw [hw']
  exact hm

end Work.Pert.pert2v2
