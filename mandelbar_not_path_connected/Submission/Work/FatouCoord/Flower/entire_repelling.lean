/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The entire repelling coordinate

Given a *repelling coordinate* `Ψ₀` for a holomorphic map `F` on a left half plane
`{Re w < -R}` (`IsRepellingCoord F z₀ R Ψ₀`), we extend it to an entire function
`Ψ : ℂ → ℂ` which is still equivariant for `F`, agrees with `Ψ₀` on `{Re w < -R}`,
tends to `z₀` at the far left end and is injective on a far left half plane.

The construction is the standard one: for `w` far to the left the value `Ψ w` is `Ψ₀ w`;
moving one unit to the right means applying `F` once.  Concretely, for any `n` with
`(w - n).re < -R` the value `F^[n] (Ψ₀ (w - n))` does not depend on `n`
(lemma `rA_eq`), so we may pick the explicit representative `n = rIdx w = ⌈w.re + R⌉₊ + 1`
and set `Ψ w = F^[rIdx w] (Ψ₀ (w - rIdx w))`.  This is manifestly holomorphic: near a point
`w` the index `rIdx` may be replaced by the fixed value `rIdx w`, and on the open set
`{v | v.re < rIdx w - R}` the function `Ψ` agrees with `F^[rIdx w] ∘ Ψ₀ ∘ (· - rIdx w)`,
a composition of entire maps with a holomorphic map on the half plane.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Flower

open Work.FatouCoord

namespace EntireRepelling

noncomputable section

variable {F : ℂ → ℂ} {z₀ : ℂ} {Ψ₀ : ℂ → ℂ} {R : ℝ} {w : ℂ}

/-- An explicit index which is far enough to the left, i.e. `(w - rIdx R w).re < -R`. -/
def rIdx (R : ℝ) (w : ℂ) : ℕ := Nat.ceil (w.re + R) + 1

/-- The `n`-th candidate value of the repelling coordinate at `w`, obtained by iterating `F`
`n` times and evaluating `Ψ₀` at `w - n`. -/
def rA (F : ℂ → ℂ) (Ψ₀ : ℂ → ℂ) (R : ℝ) (w : ℂ) (n : ℕ) : ℂ :=
  F^[n] (Ψ₀ (w - (n : ℂ)))

/-- The entire repelling coordinate, defined by picking an explicit far-left representative. -/
def rΨ (F : ℂ → ℂ) (Ψ₀ : ℂ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  rA F Ψ₀ R w (rIdx R w)

lemma rIdx_spec (R : ℝ) (w : ℂ) : (w - ((rIdx R w : ℕ) : ℂ)).re < -R := by
  rw [Complex.sub_re, Complex.natCast_re]
  have hle : w.re + R ≤ ((Nat.ceil (w.re + R) : ℕ) : ℝ) := Nat.le_ceil _
  have hc : ((rIdx R w : ℕ) : ℝ) = ((Nat.ceil (w.re + R) : ℕ) : ℝ) + 1 := by simp [rIdx]
  rw [hc]; linarith

/-- One step of the constancy of the candidate values, using the equivariance of `Ψ₀`. -/
lemma rA_succ_val (hshift : ∀ u : ℂ, u.re < -R → Ψ₀ (u+1) = F (Ψ₀ u)) (n : ℕ)
    (h : (w - (((n+1 : ℕ)) : ℂ)).re < -R) :
    rA F Ψ₀ R w (n+1) = rA F Ψ₀ R w n := by
  simp only [rA]
  rw [Function.iterate_succ_apply]
  congr 2
  have h1 : Ψ₀ ((w - ((n+1 : ℕ) : ℂ)) + 1) = F (Ψ₀ (w - ((n+1 : ℕ) : ℂ))) := hshift _ h
  have h2 : (w - ((n+1 : ℕ) : ℂ)) + 1 = w - ((n:ℕ) : ℂ) := by push_cast; ring
  rw [← h2]
  exact h1.symm

/-- If the index `n+1` is admissible for `w`, then all larger indices are admissible as well,
and the candidate values for `n` and for any `m ≥ n` coincide. -/
lemma rA_const (hshift : ∀ u : ℂ, u.re < -R → Ψ₀ (u+1) = F (Ψ₀ u)) {n m : ℕ} (hnm : n ≤ m)
    (h : (w - (((n+1 : ℕ)) : ℂ)).re < -R) : rA F Ψ₀ R w n = rA F Ψ₀ R w m := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      have hvalid : (w - (((m+1 : ℕ)) : ℂ)).re < -R := by
        rw [Complex.sub_re, Complex.natCast_re] at h ⊢
        have h1 : ((n+1 : ℕ) : ℝ) ≤ ((m+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hnm
        linarith
      rw [rA_succ_val hshift m hvalid]
      exact ih

/-- If the index `n` itself is admissible and `n ≤ m`, the candidate values at `n` and `m`
coincide. -/
lemma rA_const_of_valid (hshift : ∀ u : ℂ, u.re < -R → Ψ₀ (u+1) = F (Ψ₀ u)) {n m : ℕ}
    (hnm : n ≤ m) (h : (w - (n:ℂ)).re < -R) : rA F Ψ₀ R w n = rA F Ψ₀ R w m := by
  refine rA_const hshift hnm ?_
  rw [Complex.sub_re, Complex.natCast_re] at h ⊢
  have hc : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
  rw [hc]; linarith

/-- **Well-definedness**: any admissible index gives the same value, namely `rΨ`. -/
lemma rA_eq (hshift : ∀ u : ℂ, u.re < -R → Ψ₀ (u+1) = F (Ψ₀ u)) (n : ℕ)
    (h : (w - (n:ℂ)).re < -R) : rA F Ψ₀ R w n = rΨ F Ψ₀ R w := by
  unfold rΨ
  rcases le_total n (rIdx R w) with hle | hle
  · exact rA_const_of_valid hshift hle h
  · exact (rA_const_of_valid hshift hle (rIdx_spec R w)).symm

/-- The shift relation, before taking representatives. -/
lemma rA_succ_shift (w : ℂ) (n : ℕ) : rA F Ψ₀ R (w+1) (n+1) = F (rA F Ψ₀ R w n) := by
  simp only [rA, Function.iterate_succ_apply']
  congr 2
  push_cast
  ring_nf

/-- `rΨ` agrees with `Ψ₀` on the left half plane. -/
lemma rΨ_eq_Ψ₀ (hshift : ∀ u : ℂ, u.re < -R → Ψ₀ (u+1) = F (Ψ₀ u)) (hw : w.re < -R) :
    rΨ F Ψ₀ R w = Ψ₀ w := by
  have h0 : (w - ((0:ℕ):ℂ)).re < -R := by simpa using hw
  have h1 := rA_eq hshift (0:ℕ) h0
  simp only [rA, Function.iterate_zero_apply] at h1
  simpa using h1.symm

/-- `rΨ` is equivariant for the unit shift and for `F`. -/
lemma rΨ_shift (hshift : ∀ u : ℂ, u.re < -R → Ψ₀ (u+1) = F (Ψ₀ u)) :
    rΨ F Ψ₀ R (w+1) = F (rΨ F Ψ₀ R w) := by
  have hj : 1 ≤ rIdx R (w+1) := by simp [rIdx]
  have hpred : (rIdx R (w+1) - 1) + 1 = rIdx R (w+1) := Nat.succ_pred_eq_of_pos hj
  have hshift1 : rA F Ψ₀ R (w+1) (rIdx R (w+1)) =
      F (rA F Ψ₀ R w (rIdx R (w+1) - 1)) := by
    conv_lhs => rw [← hpred]
    exact rA_succ_shift w (rIdx R (w+1) - 1)
  have hcast : ((rIdx R (w+1) - 1 : ℕ) : ℂ) = (rIdx R (w+1) : ℂ) - 1 := by
    rw [Nat.cast_sub hj, Nat.cast_one]
  have hvalid : (w - (((rIdx R (w+1)) - 1 : ℕ) : ℂ)).re < -R := by
    have h := rIdx_spec R (w+1)
    rw [hcast]
    simp only [Complex.sub_re, Complex.natCast_re, Complex.add_re, Complex.one_re] at h ⊢
    linarith
  simp only [rΨ]
  rw [hshift1, rA_eq hshift _ hvalid]
  rfl

/-- Local holomorphy of the candidate expression `v ↦ F^[n] (Ψ₀ (v - n))`. -/
lemma differentiableAt_iter (hF : Differentiable ℂ F)
    (hdiff : DifferentiableOn ℂ Ψ₀ {v : ℂ | v.re < -R}) {n : ℕ} {w : ℂ}
    (h : (w - (n:ℂ)).re < -R) :
    DifferentiableAt ℂ (fun v : ℂ => F^[n] (Ψ₀ (v - (n:ℂ)))) w := by
  have hinner : DifferentiableAt ℂ (fun v : ℂ => v - (n:ℂ)) w := differentiableAt_id.sub_const _
  have hhalf : {v : ℂ | v.re < -R} ∈ 𝓝 (w - (n:ℂ)) :=
    (isOpen_lt Complex.continuous_re continuous_const).mem_nhds h
  have hΨ0 : DifferentiableAt ℂ Ψ₀ (w - (n:ℂ)) := hdiff.differentiableAt hhalf
  have hcomp : DifferentiableAt ℂ (fun v : ℂ => Ψ₀ (v - (n:ℂ))) w := hΨ0.comp w hinner
  exact (hF.iterate n).differentiableAt.comp w hcomp

/-- The entire repelling coordinate is holomorphic on all of `ℂ`. -/
lemma rΨ_differentiable (hF : Differentiable ℂ F)
    (hshift : ∀ u : ℂ, u.re < -R → Ψ₀ (u+1) = F (Ψ₀ u))
    (hdiff : DifferentiableOn ℂ Ψ₀ {v : ℂ | v.re < -R}) : Differentiable ℂ (rΨ F Ψ₀ R) := by
  intro w
  have hwv : (w - (((rIdx R w : ℕ)) : ℂ)).re < -R := rIdx_spec R w
  have hwre : w.re < (rIdx R w : ℝ) - R := by
    simp only [Complex.sub_re, Complex.natCast_re] at hwv
    linarith
  have hopen : IsOpen {v : ℂ | v.re < (rIdx R w : ℝ) - R} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hU : {v : ℂ | v.re < (rIdx R w : ℝ) - R} ∈ 𝓝 w := hopen.mem_nhds hwre
  have hev : rΨ F Ψ₀ R =ᶠ[𝓝 w]
      fun v : ℂ => F^[rIdx R w] (Ψ₀ (v - (((rIdx R w : ℕ)) : ℂ))) := by
    refine eventually_of_mem hU ?_
    intro v hv
    have hv' : (v - (((rIdx R w : ℕ)) : ℂ)).re < -R := by
      have hv2 : v.re < (rIdx R w : ℝ) - R := hv
      rw [Complex.sub_re, Complex.natCast_re]
      linarith
    show rΨ F Ψ₀ R v = F^[rIdx R w] (Ψ₀ (v - (((rIdx R w : ℕ)) : ℂ)))
    rw [← rA_eq hshift (rIdx R w) hv']
    rfl
  exact (differentiableAt_iter hF hdiff hwv).congr_of_eventuallyEq hev

end

end EntireRepelling

theorem entire_repelling {F : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} {Ψ₀ : ℂ → ℂ} (hF : Differentiable ℂ F) (h : IsRepellingCoord F z₀ R Ψ₀) : ∃ Ψ : ℂ → ℂ, Differentiable ℂ Ψ ∧ (∀ w : ℂ, Ψ (w + 1) = F (Ψ w)) ∧ (∀ w : ℂ, w.re < -R → Ψ w = Ψ₀ w) ∧ (∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, ∀ w : ℂ, w.re < -R' → Ψ w ≠ z₀ ∧ ‖Ψ w - z₀‖ < ε) ∧ (∃ R₀ : ℝ, Set.InjOn Ψ {w : ℂ | w.re < -R₀}) := by
  refine ⟨EntireRepelling.rΨ F Ψ₀ R, ?_, ?_, ?_, ?_, ?_⟩
  · exact EntireRepelling.rΨ_differentiable hF h.shift h.diff
  · exact fun w => EntireRepelling.rΨ_shift h.shift
  · exact fun w hw => EntireRepelling.rΨ_eq_Ψ₀ h.shift hw
  · intro ε hε
    obtain ⟨R', hR'⟩ := h.small ε hε
    refine ⟨max R' R, ?_⟩
    intro w hw
    have hwR : w.re < -R := by
      have := le_max_right R' R
      linarith
    have hwR' : w.re < -R' := by
      have := le_max_left R' R
      linarith
    rw [EntireRepelling.rΨ_eq_Ψ₀ h.shift hwR]
    exact ⟨h.ne_zero w hwR, hR' w hwR'⟩
  · refine ⟨R, ?_⟩
    intro a ha b hb hab
    refine h.inj ha hb ?_
    rw [← EntireRepelling.rΨ_eq_Ψ₀ h.shift ha, ← EntireRepelling.rΨ_eq_Ψ₀ h.shift hb]
    exact hab

end Work.FatouCoord.Flower
