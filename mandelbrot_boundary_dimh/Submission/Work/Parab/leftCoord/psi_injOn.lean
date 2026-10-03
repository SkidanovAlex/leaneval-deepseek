import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.leftCoord.extension

/-!
# Injectivity of the extended Fatou coordinate

`Psi N G ψ` extends a Fatou coordinate `ψ` (satisfying the Abel equation
`ψ (G x) = ψ x + 1` on `{N < x.re}`) to the escaping set `Esc N G`.  The main result
here is that `Psi` is injective on `Esc N G` provided that

* `ψ` is injective on `{N < x.re}`,
* `G` is injective on `{N < ‖·‖}`,
* `G` does not decrease real parts on `{N < ‖·‖}` (hypothesis `hmono`).

The proof pushes the equality `Psi x = Psi y` to a common index `K = max (nIdx x) (nIdx y)`
by iterating the Abel equation along the orbits (possible because from the entry index on
the orbits stay in `{N < ·.re}`), uses injectivity of `ψ` to get `G^[K] x = G^[K] y`, and
then walks the equality backwards using injectivity of `G`.
-/

open Classical

namespace Work.Parab.leftCoord

open Set Filter Metric
open scoped Topology

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

variable {N : ℝ} {G ψ : ℂ → ℂ} {x y : ℂ} {k n : ℕ}

/-- From the entry index `nIdx N G x` onwards, the real parts along the orbit of an escaping
point stay `> N`.  (This uses only that `G` does not decrease real parts on `{N < ‖·‖}`: once
a point has real part `> N` its norm exceeds `N`, so `hmono` applies, and the property
propagates.) -/
lemma re_gt_of_nIdx (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re) (hx : Esc N G x) :
    ∀ k, nIdx N G x ≤ k → N < (G^[k] x).re := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact (nIdx_spec hx).2.2
  | succ k hk ih =>
      have hnorm : N < ‖G^[k] x‖ := lt_of_lt_of_le ih (Complex.re_le_norm _)
      have hle := hmono (G^[k] x) hnorm
      rw [← Function.iterate_succ_apply' G k x] at hle
      exact lt_of_lt_of_le ih hle

/-- Every iterate of an escaping point has norm `> N`. -/
lemma norm_gt_of_Esc (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re) (hx : Esc N G x) :
    ∀ k, N < ‖G^[k] x‖ := by
  intro k
  rcases lt_or_ge (nIdx N G x) k with hlt | hge
  · exact lt_of_lt_of_le (re_gt_of_nIdx hmono hx k (le_of_lt hlt)) (Complex.re_le_norm _)
  · exact (nIdx_spec hx).1 k hge

/-- Iterating the Abel equation along the orbit of an escaping point. -/
lemma iterate_abel (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re) (hx : Esc N G x) :
    ∀ k, nIdx N G x ≤ k →
      ψ (G^[k] x) = ψ (G^[nIdx N G x] x) + ((k - nIdx N G x : ℕ) : ℂ) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
      have hre : N < (G^[k] x).re := re_gt_of_nIdx hmono hx k hk
      have hstep : ψ (G (G^[k] x)) = ψ (G^[k] x) + 1 := habel (G^[k] x) hre
      rw [Function.iterate_succ_apply', hstep, ih]
      have : (k + 1 - nIdx N G x : ℕ) = (k - nIdx N G x) + 1 := by omega
      rw [this]; push_cast; ring

/-- The orbit of an escaping point stays in the escaping set. -/
lemma Esc_iterate (hG : ∀ x, N < x.re → N < (G x).re) (hx : Esc N G x) (k : ℕ) :
    Esc N G (G^[k] x) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact Esc_map hG ih

/-- The extension `Psi` satisfies the same Abel equation along the whole orbit. -/
lemma Psi_iterate (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hx : Esc N G x) (k : ℕ) :
    Psi N G ψ (G^[k] x) = Psi N G ψ x + (k : ℂ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Psi_abel hG habel (Esc_iterate hG hx k), ih]
      push_cast; ring

/-- At the entry point the value of `ψ` is `Psi x + nIdx x`. -/
lemma psi_nIdx (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hx : Esc N G x) :
    ψ (G^[nIdx N G x] x) = Psi N G ψ x + (nIdx N G x : ℂ) := by
  have h3 : N < (G^[nIdx N G x] x).re := (nIdx_spec hx).2.2
  have h := Psi_eq_of_re (N := N) (G := G) (ψ := ψ) (x := G^[nIdx N G x] x) h3
  rw [← h]
  exact Psi_iterate hG habel hx (nIdx N G x)

/-- For any `K` beyond the entry index, `ψ` at the `K`-th iterate of `x` equals `Psi x + K`. -/
lemma psi_iterate_ge (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re)
    (hx : Esc N G x) {K : ℕ} (hK : nIdx N G x ≤ K) :
    ψ (G^[K] x) = Psi N G ψ x + (K : ℂ) := by
  rw [iterate_abel habel hmono hx K hK, psi_nIdx hG habel hx,
    Nat.cast_sub (R := ℂ) hK]
  ring

/-- Walking an equality of `K`-th iterates backwards, using injectivity of `G` on
`{N < ‖·‖}`. -/
lemma eq_of_iterate_eq (hGinj : Set.InjOn G {x : ℂ | N < ‖x‖}) {K : ℕ}
    (hx : ∀ k ≤ K, N < ‖G^[k] x‖) (hy : ∀ k ≤ K, N < ‖G^[k] y‖)
    (h : G^[K] x = G^[K] y) : x = y := by
  have hmain : ∀ j ≤ K, G^[j] x = G^[j] y := by
    have haux : ∀ d, ∀ j, K - j = d → j ≤ K → G^[j] x = G^[j] y := by
      intro d
      induction d with
      | zero =>
          intro j hj hle
          have hjeq : j = K := by omega
          rw [hjeq]; exact h
      | succ d ih =>
          intro j hj hle
          have hjlt : j < K := by omega
          have hnext : G (G^[j] x) = G (G^[j] y) := by
            rw [← Function.iterate_succ_apply' G j x, ← Function.iterate_succ_apply' G j y]
            exact ih (j + 1) (by omega) (by omega)
          exact hGinj (hx j (le_of_lt hjlt)) (hy j (le_of_lt hjlt)) hnext
    intro j hj
    exact haux (K - j) j rfl hj
  simpa using hmain 0 (Nat.zero_le K)

theorem psi_injOn {G ψ : ℂ → ℂ} {N : ℝ}
    (hG : ∀ x, N < x.re → N < (G x).re)
    (habel : ∀ x, N < x.re → ψ (G x) = ψ x + 1)
    (hmono : ∀ x, N < ‖x‖ → x.re ≤ (G x).re)
    (hψinj : Set.InjOn ψ {x : ℂ | N < x.re})
    (hGinj : Set.InjOn G {x : ℂ | N < ‖x‖}) :
    Set.InjOn (Work.Parab.leftCoord.Psi N G ψ) (Work.Parab.leftCoord.Esc N G) := by
  intro x hx y hy hxy
  have heq : G^[max (nIdx N G x) (nIdx N G y)] x
      = G^[max (nIdx N G x) (nIdx N G y)] y := by
    have hKx : ψ (G^[max (nIdx N G x) (nIdx N G y)] x)
        = Psi N G ψ x + ((max (nIdx N G x) (nIdx N G y) : ℕ) : ℂ) :=
      psi_iterate_ge hG habel hmono hx (le_max_left (nIdx N G x) (nIdx N G y))
    have hKy : ψ (G^[max (nIdx N G x) (nIdx N G y)] y)
        = Psi N G ψ y + ((max (nIdx N G x) (nIdx N G y) : ℕ) : ℂ) :=
      psi_iterate_ge hG habel hmono hy (le_max_right (nIdx N G x) (nIdx N G y))
    have hreKx : N < (G^[max (nIdx N G x) (nIdx N G y)] x).re :=
      re_gt_of_nIdx hmono hx _ (le_max_left (nIdx N G x) (nIdx N G y))
    have hreKy : N < (G^[max (nIdx N G x) (nIdx N G y)] y).re :=
      re_gt_of_nIdx hmono hy _ (le_max_right (nIdx N G x) (nIdx N G y))
    apply hψinj hreKx hreKy
    rw [hKx, hKy, hxy]
  refine eq_of_iterate_eq (x := x) (y := y)
    (K := max (nIdx N G x) (nIdx N G y)) hGinj
    (fun k _ => norm_gt_of_Esc hmono hx k) (fun k _ => norm_gt_of_Esc hmono hy k) heq

end Work.Parab.leftCoord
