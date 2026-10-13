/-
# `pzIter_smoothCptQ` — the iterated `z`-partials of a `CptQ` source are again `CptQ`

`Work.FTS.PhiStar.Honesty.SmoothCptQ G` says that `G` is `C^n` on all of `ℝ²` for every
`n : ℕ` (these are the *finite* orders: the order `↑n : ℕ∞ω` with `n : ℕ`), and that `G` is
supported in a rectangle `[a,b] × [c,d]` with `0 < a < b`, `0 < c < d < π/2` (all in the
*open* quadrant).  The statement proved here is that the iterated plain `z`-partial
`∂_z^j G = Work.Spaces.pzIter j G` has the same property.

Both halves are immediate from facts already in the workspace:

* **Smoothness.**  `∂_z^k` costs `k` orders of differentiability, so
  `ContDiff ℝ (n+j) (uncurry G)` gives `ContDiff ℝ n (uncurry (∂_z^j G))` — the finite-order
  chain rule `contDiffOn_uncurry_pzIter_le` below, which is `fderiv_of_isOpen` iterated.
* **Support.**  Off the rectangle the source vanishes on an *open* neighbourhood of each
  point (either the whole `θ`-line is zero, when `θ ∉ [c,d]`, or the whole `z`-line is zero
  in a neighbourhood of `z`, when `z ∉ [a,b]`); by `Work.Stability.pzIter_eq_zero_of_vanishOn`
  all `z`-derivatives vanish there.

This is the "honest-for-free" package of `Honesty/ellWeakPos_psiSeries_of_cptQ`: it lets the
whole compactly-supported machinery be run for the `z`-iterates of a source (as needed for
example in `cmode_iteratedDeriv_facts`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.Spaces.pz_aux
import Submission.Work.Stability.ZcutSmoothCompact
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

set_option autoImplicit false

/-! ## Finite-order smoothness of the iterated `z`-partials

(`∂_z` is the curried partial derivative `Work.Spaces.pz`; the order type `WithTop ℕ∞` is the
one of `ContDiffOn`, and `↑n` with `n : ℕ` is the honest finite order `C^n`.) -/

/-- **The `z`-partial derivative costs one order of differentiability**, on an open set and at
a finite order.  The partial derivative is the Fréchet derivative in the direction `(1,0)`
(`Work.Spaces.pz_eq_fderiv`), and `ContDiffOn.fderiv_of_isOpen` lowers the order by one. -/
theorem contDiffOn_uncurry_pz_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (Function.uncurry G) V) :
    ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := fun p hp =>
    Work.Spaces.pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V :=
    h.fderiv_of_isOpen hV (by simp)
  have hcomp : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ ((n : ℕ) : WithTop ℕ∞)
        (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  exact hcomp.congr hchain

/-- **The iterated `z`-partial `∂_z^i` costs `i` orders of differentiability**: from
`C^N` on the open set `V` one gets `∂_z^i G ∈ C^k` on `V` whenever `i + k ≤ N`. -/
theorem contDiffOn_uncurry_pzIter_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {N : ℕ}
    (h : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (Function.uncurry G) V) :
    ∀ i k : ℕ, i + k ≤ N →
      ContDiffOn ℝ ((k : ℕ) : WithTop ℕ∞) (Function.uncurry (Work.Spaces.pzIter i G)) V := by
  intro i
  induction i with
  | zero => intro k hk; simpa using h.of_le (Nat.cast_le.mpr (show k ≤ N by omega))
  | succ i ih =>
      intro k hik
      have h2 : ContDiffOn ℝ (((k + 1 : ℕ)) : WithTop ℕ∞)
          (Function.uncurry (Work.Spaces.pzIter i G)) V := ih (k + 1) (by omega)
      simpa [Work.Spaces.pzIter_succ] using contDiffOn_uncurry_pz_le hV h2

/-! ## The support rectangle of the `z`-iterates -/

/-- If every slice of `G` is supported in `[c,d]` then so is every slice of `∂_z^j G`: off
`[c,d]` the whole `z`-line of `G` is zero, so its `j`-th derivative is zero. -/
theorem pzIter_eq_zero_of_theta_not_mem {G : ℝ → ℝ → ℝ} {c d : ℝ}
    (hG : ∀ z θ : ℝ, G z θ ≠ 0 → θ ∈ Set.Icc c d) (j : ℕ) {t θ : ℝ}
    (hθ : θ ∉ Set.Icc c d) : Work.Spaces.pzIter j G t θ = 0 := by
  refine Work.Stability.pzIter_eq_zero_of_vanishOn
    (V := Set.univ ×ˢ (Set.Icc c d)ᶜ) (isOpen_univ.prod isClosed_Icc.isOpen_compl) ?_ j t θ ?_
  · intro z θ' hzθ'
    by_contra hne
    exact hzθ'.2 (hG z θ' hne)
  · exact ⟨Set.mem_univ t, hθ⟩

/-- If every slice of `G` is supported in `[a,b]` in the `z`-variable then so is every slice
of `∂_z^j G`: off `[a,b]` the source vanishes on a whole *neighbourhood* of each point, so
the derivative vanishes there. -/
theorem pzIter_eq_zero_of_z_not_mem {G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hG : ∀ z θ : ℝ, G z θ ≠ 0 → z ∈ Set.Icc a b) (j : ℕ) {t θ : ℝ}
    (ht : t ∉ Set.Icc a b) : Work.Spaces.pzIter j G t θ = 0 := by
  refine Work.Stability.pzIter_eq_zero_of_vanishOn
    (V := (Set.Icc a b)ᶜ ×ˢ Set.univ) (isClosed_Icc.isOpen_compl.prod isOpen_univ) ?_ j t θ ?_
  · intro z θ' hzθ'
    by_contra hne
    exact hzθ'.1 (hG z θ' hne)
  · exact ⟨ht, Set.mem_univ θ⟩

/-! ## The main statement -/

theorem pzIter_smoothCptQ {G : ℝ → ℝ → ℝ} (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) (j : ℕ) :
    Work.FTS.PhiStar.Honesty.SmoothCptQ (Work.Spaces.pzIter j G) := by
  refine ⟨fun n => ?_, ?_⟩
  · exact contDiffOn_univ.mp
      (contDiffOn_uncurry_pzIter_le (V := Set.univ) isOpen_univ (hG.1 (j + n)).contDiffOn
        j n (by omega))
  · obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := hG.2
    refine ⟨a, b, c, d, ha, hab, hc, hcd, hd, ?_⟩
    intro z θ hne
    refine ⟨?_, ?_⟩
    · by_contra hz
      exact hne (pzIter_eq_zero_of_z_not_mem (fun z θ h => (H z θ h).1) j hz)
    · by_contra hθ
      exact hne (pzIter_eq_zero_of_theta_not_mem (fun z θ h => (H z θ h).2) j hθ)

end Work.FTS.PhiStar.Honesty.CptQSmooth
