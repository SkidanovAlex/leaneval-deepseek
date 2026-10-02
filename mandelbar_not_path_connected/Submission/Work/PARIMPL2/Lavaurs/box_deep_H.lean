import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.AttrNorm
import Submission.Work.FlowerGlue2.box_deep_of_transient_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Lavaurs

/-- **The deepening of a windowed `φa`-box, with the `H`-restricted transient bound** (item (2) of
the lead's directive: a *proved* replacement, inside this directory, of the still-stubbed
`Work.FlowerGlue2.box_deep_attr`).

Given the attracting comparison `A` (`AttrCompare`: `φa = approxCoord κ₀ (w0 ·) + sa + O(1/Re w0)`
below depth `A.N`) and the restricted transient bound `hLB` *at the height `H` of the box*, every
box point `y` (level in `[X₁, X₁+W]`, height `≤ H`) has, after `j ≥ J` steps, `Re (w0 (F^j y)) > X`
and the log-bounded height
`|Im (w0 (F^j y))| ≤ H + |Im sa| + 2‖κ₀‖ log (X₁+W+j+2) + 4`.

Only box points are fed to `hLB` (`|Im φa y| ≤ H`), and along the orbit the height is preserved
exactly (`φa (F z) = φa z + 1` is a *real* shift, so `Im (φa (F^j y)) = Im (φa y)`), which is why the
`H`-restricted form suffices and the unrestricted one is not needed.  This is the hypothesis
`hdeep` of `Work.PARIMPL2.Lavaurs.lockstep_complex`, and it is discharged from
`Work.PARIMPL2.Lavaurs.hLB_H` (which supplies `hLB` for every `H`).

The proof is the delivered `Work.FlowerGlue2.box_deep_of_transient_bound` argument (which is
`sorry`-free) with the restricted `hLB` in place of the unrestricted one: in that proof `hLB'` is
used in exactly one place, the `hdeep` step at `z = (Ft c₀)^[j] y`, where the extra antecedent
`|Im (φa z)| ≤ H` is available from `φa (F^j y) = φa y + j`. -/
theorem box_deep_H {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (A : Work.FlowerGlue2.AttrCompare P fl.Pa fl.φa) (X₁ W H : ℝ)
    (hLB : ∃ M M' : ℝ, A.N ≤ M ∧ ∀ z ∈ fl.Pa,
      (Work.PARIMPL2.w0 P z).re ≤ M → |(fl.φa z).im| ≤ H → (fl.φa z).re ≤ M') :
    ∀ X : ℝ, ∃ J : ℕ, ∀ y ∈ fl.Pa,
      X₁ ≤ (fl.φa y).re → (fl.φa y).re ≤ X₁ + W → |(fl.φa y).im| ≤ H →
        ∀ j ≥ J, X < (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[j] y)).re ∧
          |(Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[j] y)).im|
            ≤ H + |(A.sa).im| + 2 * ‖P.κ c₀‖ * Real.log (X₁ + W + j + 2) + 4 := by
  obtain ⟨M, M', hMN, hLB'⟩ := hLB
  have hMpos : 0 < M := lt_of_lt_of_le A.N_pos hMN
  intro X
  obtain ⟨L₀, hL₀⟩ := Work.FlowerGlue2.deep_box_eventually (κ := P.κ c₀) (sa := A.sa) (K := A.K)
    (M := M) (H := H) (W := W) (X := X) A.K_nonneg hMpos
  obtain ⟨J₀, hJ₀⟩ := exists_nat_gt (M' - X₁)
  obtain ⟨J₁, hJ₁⟩ := exists_nat_gt (L₀ - X₁ - W - 2)
  refine ⟨max J₀ J₁, ?_⟩
  intro y hy hy1 hy2 hy3 j hj
  have hj0 : J₀ ≤ j := le_trans (le_max_left _ _) hj
  have hj1 : J₁ ≤ j := le_trans (le_max_right _ _) hj
  have hj0' : M' - X₁ < (j : ℝ) := lt_of_lt_of_le hJ₀ (by exact_mod_cast hj0)
  have hj1' : L₀ - X₁ - W - 2 < (j : ℝ) := lt_of_lt_of_le hJ₁ (by exact_mod_cast hj1)
  have hzmem_gen : ∀ n : ℕ, (Work.PARIMPL.Ft c₀)^[n] y ∈ fl.Pa := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ k ih => rw [Function.iterate_succ_apply']; exact A.mapsTo_Pa ih
  set z : ℂ := (Work.PARIMPL.Ft c₀)^[j] y with hz_def
  have hzmem : z ∈ fl.Pa := by rw [hz_def]; exact hzmem_gen j
  have hz₁ : z ≠ d.z₁ := by
    intro h
    rw [h] at hzmem
    exact Work.FlowerGlue2.z₁_not_mem_loc P A hzmem
  have hphi : fl.φa z = fl.φa y + j := by
    rw [hz_def]; exact Work.FlowerGlue2.phi_iterate_loc P A hy j
  have hRe : (fl.φa z).re = (fl.φa y).re + (j : ℝ) := by
    have hcast : ((j : ℂ)).re = (j : ℝ) := by simp
    rw [hphi, Complex.add_re, hcast]
  have him_H : |(fl.φa z).im| ≤ H := by
    have hcasti : ((j : ℂ)).im = 0 := by simp
    rw [hphi, Complex.add_im, hcasti, add_zero]
    exact hy3
  have hdeep : M < (Work.FlowerGlue2.w0 P z).re := by
    by_contra hle
    push Not at hle
    have h1 := hLB' z hzmem hle him_H
    linarith [hRe, hy1]
  exact hL₀ (X₁ + W + (j : ℝ) + 2) (by linarith) (Work.FlowerGlue2.w0 P z) (fl.φa z)
    (le_of_lt hdeep)
    (by
      have hN : A.N < (Work.FlowerGlue2.w0 P z).re := lt_of_le_of_lt hMN hdeep
      have h := A.asymp z hzmem hz₁ hN
      have heq : fl.φa z
            - (Work.FatouCoord.approxCoord (P.κ c₀) (Work.FlowerGlue2.w0 P z) + A.sa)
          = fl.φa z - A.sa
            - (Work.FlowerGlue2.w0 P z - P.κ c₀ * Complex.log (Work.FlowerGlue2.w0 P z)) := by
        simp only [Work.FatouCoord.approxCoord]; ring
      rw [heq] at h
      exact h)
    (by linarith [hRe, hy1])
    (by linarith [hRe, hy2])
    him_H

end Work.PARIMPL2.Lavaurs
