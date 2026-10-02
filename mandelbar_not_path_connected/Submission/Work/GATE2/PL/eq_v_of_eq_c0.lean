import Mathlib
import Submission.Work.GATE2.PL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function

/-- The Abel equation `φ ∘ F = φ + 1` on a forward-invariant set `Pa`, iterated: `φ` advances by
`m` along the `m`-th iterate of `F`. -/
theorem fatou_iterate_of_shift {F : ℂ → ℂ} {Pa : Set ℂ} {φ : ℂ → ℂ}
    (hmaps : Set.MapsTo F Pa Pa) (hshift : ∀ z ∈ Pa, φ (F z) = φ z + 1)
    (m : ℕ) {z : ℂ} (hz : z ∈ Pa) : φ ((F)^[m] z) = φ z + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have hz' : (F)^[m] z ∈ Pa := Work.FatouCoord.mapsTo_iterate_of_mapsTo hmaps m hz
    rw [hshift _ hz', ih]
    push_cast; ring

/-- If a `Good` function on `Dom v X k` (see `Submission/Work/GATE2/PL/Defs.lean`) takes the
value `c₀` at `w`, then `w = v`.

Proof: iteration of the equivariance `ψ (w + n) = F^[n] (ψ w)` pushes `w` far enough to the right
that `far` applies and `ψ` is the inverse Fatou coordinate there; comparing that level with the
level of the critical orbit given by `hv` (through the Abel equation `FF.shift` on `fl.Pa`) gives
`w + N = v + N`. -/
theorem eq_v_of_eq_c0 {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁}
    {FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁ fl.Pa fl.φa}
    {v X : ℝ} {k : ℕ} {ψ : ℂ → ℂ} (hψ : Work.GATE2.PL.Good fl FF v X k ψ)
    (hv : ∃ N : ℕ, (Work.EL.F c₀)^[N] c₀ ∈ fl.Pa ∧
      fl.φa ((Work.EL.F c₀)^[N] c₀) = (((v + N : ℝ)) : ℂ))
    {w : ℂ} (hw : w ∈ Work.GATE2.PL.Dom v X k) (hval : ψ w = c₀) : w = (v : ℂ) := by
  obtain ⟨n0, hn0mem, hn0φa⟩ := hv
  -- Push `w` far enough to the right through the equivariance `ψ (w + N) = F^[N] (ψ w)`, so that
  -- `ψ` is the inverse Fatou coordinate there.
  obtain ⟨k', hk'⟩ := exists_nat_gt (X - w.re)
  set N := max k' n0 with hNdef
  have hNge : n0 ≤ N := le_max_right _ _
  have hk'N : k' ≤ N := le_max_left _ _
  have hXN : X < (w + (N : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have : X - w.re < (N : ℝ) := lt_of_lt_of_le hk' (by exact_mod_cast hk'N)
    linarith
  obtain ⟨hPgwN, hφawN⟩ := hψ.far (w + (N : ℂ)) hXN
  have hiter := Good.iterate_shift fl FF hψ hw N
  rw [hval] at hiter
  -- The level of `c₀` read off at the far right: `φa (F^[N] c₀) = w + N`.
  have hwN : fl.φa ((Work.EL.F c₀)^[N] c₀) = w + (N : ℂ) := by
    rw [← hiter]; exact hφawN
  -- The level of `c₀` read off along the critical orbit: `φa (F^[N] c₀) = v + N`.
  have hcast : ((v + (N : ℝ) : ℝ) : ℂ) =
      ((v + (n0 : ℝ) : ℝ) : ℂ) + ((N - n0 : ℕ) : ℂ) := by
    have h1 : (N : ℝ) = (n0 : ℝ) + ((N - n0 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hNge]; ring
    rw [h1]; push_cast; ring
  have hvN : fl.φa ((Work.EL.F c₀)^[N] c₀) = ((v + (N : ℝ) : ℝ) : ℂ) := by
    have hiterN : (Work.EL.F c₀)^[N] c₀ =
        (Work.EL.F c₀)^[N - n0] ((Work.EL.F c₀)^[n0] c₀) := by
      have h1 : N = (N - n0) + n0 := by omega
      conv_lhs => rw [h1]
      rw [Function.iterate_add_apply]
    rw [hiterN, fatou_iterate_of_shift fl.mapsTo_Pa FF.shift (N - n0) hn0mem, hn0φa]
    exact hcast.symm
  have hkey : w + (N : ℂ) = ((v + (N : ℝ) : ℝ) : ℂ) := hwN.symm.trans hvN
  have hcast2 : ((v + (N : ℝ) : ℝ) : ℂ) = (v : ℂ) + (N : ℂ) := by push_cast; ring
  rw [hcast2] at hkey
  exact add_right_cancel hkey

end Work.GATE2.PL
