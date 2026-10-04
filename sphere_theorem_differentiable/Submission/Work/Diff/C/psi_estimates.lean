import Mathlib
import Submission.Work.Diff.C.flat_at_const

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped ContDiff
open scoped Topology

/-- Pointwise estimates for the cutoff `ψ` used in the classical sphere theorem.  `ψ` is smooth,
monotone, has derivative in `[0,2]`, equals the identity on `[-1+2c, ∞)` and the constant `-1+c`
on `(-∞,-1+c]`.  Then `ψ` takes values in `[-1+c, max s (-1+2c)]`, satisfies `|ψ s - s| ≤ 2c`
above `-1+c`, has derivative `1` above `-1+2c` and `0` below `-1+c`, and is *flat* at `-1+c` (all
iterated derivatives of order ≥ 1 vanish there, since it is constant on a left-neighbourhood). -/
theorem psi_estimates {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ ∧ Monotone ψ ∧ (∀ s : ℝ, 0 ≤ deriv ψ s ∧ deriv ψ s ≤ 2) ∧
      (∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s) ∧ (∀ s : ℝ, s ≤ -1 + c → ψ s = -1 + c)) :
    (∀ s : ℝ, s ≤ -1 + c → ψ s = -1 + c) ∧
    (∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s) ∧
    (∀ s : ℝ, -1 + c ≤ ψ s) ∧
    (∀ s : ℝ, ψ s ≤ max s (-1 + 2 * c)) ∧
    (∀ s : ℝ, -1 + c ≤ s → |ψ s - s| ≤ 2 * c) ∧
    (∀ s : ℝ, -1 + 2 * c < s → deriv ψ s = 1) ∧
    (∀ s : ℝ, s ≤ -1 + c → deriv ψ s = 0) ∧
    (∀ u : ℝ, u ≤ 0 → ψ (u - 1 + c) = -1 + c) ∧
    (∀ k : ℕ, iteratedDeriv (k + 1) (fun u : ℝ => ψ (u - 1 + c)) 0 = 0) ∧
    (∀ k : ℕ, iteratedDeriv (k + 1) ψ (-1 + c) = 0) := by
  obtain ⟨hcd, hmono, _hderiv, hid, hconst⟩ := hψ
  have h1 : ∀ s : ℝ, s ≤ -1 + c → ψ s = -1 + c := hconst
  have h2 : ∀ s : ℝ, -1 + 2 * c ≤ s → ψ s = s := hid
  -- `ψ` never drops below `-1 + c`
  have h3 : ∀ s : ℝ, -1 + c ≤ ψ s := by
    intro s
    rcases le_or_gt s (-1 + c) with hs | hs
    · rw [hconst s hs]
    · rcases le_or_gt s (-1 + 2 * c) with hs2 | hs2
      · have h := hmono (le_of_lt hs)
        rwa [hconst (-1 + c) le_rfl] at h
      · rw [hid s (le_of_lt hs2)]
        linarith
  -- `ψ s ≤ max s (-1 + 2c)`
  have h4 : ∀ s : ℝ, ψ s ≤ max s (-1 + 2 * c) := by
    intro s
    rcases le_or_gt s (-1 + 2 * c) with hs | hs
    · have h := hmono hs
      rw [hid (-1 + 2 * c) le_rfl] at h
      exact le_trans h (le_max_right _ _)
    · rw [hid s (le_of_lt hs)]
      exact le_max_left _ _
  -- `|ψ s - s| ≤ 2c` above `-1 + c`
  have h5 : ∀ s : ℝ, -1 + c ≤ s → |ψ s - s| ≤ 2 * c := by
    intro s hs
    rw [abs_le]
    rcases le_or_gt s (-1 + 2 * c) with hs2 | hs2
    · have hup : ψ s ≤ -1 + 2 * c := by
        have h := hmono hs2
        rwa [hid (-1 + 2 * c) le_rfl] at h
      have hlow := h3 s
      constructor <;> linarith
    · rw [hid s (le_of_lt hs2)]
      constructor <;> linarith
  -- derivative `1` above `-1 + 2c`
  have h6 : ∀ s : ℝ, -1 + 2 * c < s → deriv ψ s = 1 := by
    intro s hs
    have hev : ψ =ᶠ[𝓝 s] (fun x : ℝ => x) :=
      Filter.eventually_of_mem (isOpen_Ioi.mem_nhds hs) (fun y hy => hid y (le_of_lt hy))
    rw [hev.deriv_eq]
    exact congrFun deriv_id'' s
  -- derivative `0` below `-1 + c`
  have h7 : ∀ s : ℝ, s ≤ -1 + c → deriv ψ s = 0 := by
    intro s hs
    rcases lt_or_eq_of_le hs with hlt | heq
    · have hev : ψ =ᶠ[𝓝 s] (fun _ : ℝ => -1 + c) :=
        Filter.eventually_of_mem (isOpen_Iio.mem_nhds hlt) (fun y hy => hconst y (le_of_lt hy))
      rw [hev.deriv_eq]
      exact deriv_const s (-1 + c)
    · subst heq
      have hh := flat_at_const hcd (fun x hx => hconst x hx) 0
      simpa only [Nat.zero_add, iteratedDeriv_one] using hh
  have h8 : ∀ u : ℝ, u ≤ 0 → ψ (u - 1 + c) = -1 + c := by
    intro u hu
    exact hconst (u - 1 + c) (by linarith)
  -- flatness of `u ↦ ψ (u - 1 + c)` at `0`
  have h9 : ∀ k : ℕ, iteratedDeriv (k + 1) (fun u : ℝ => ψ (u - 1 + c)) 0 = 0 := by
    have hcd' : ContDiff ℝ ∞ (fun u : ℝ => ψ (u - 1 + c)) := by fun_prop
    exact fun k => flat_at_const hcd' (fun x hx => h8 x hx) k
  -- flatness of `ψ` at `-1 + c`
  have h10 : ∀ k : ℕ, iteratedDeriv (k + 1) ψ (-1 + c) = 0 :=
    fun k => flat_at_const hcd (fun x hx => hconst x hx) k
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

end Work.Diff.C
