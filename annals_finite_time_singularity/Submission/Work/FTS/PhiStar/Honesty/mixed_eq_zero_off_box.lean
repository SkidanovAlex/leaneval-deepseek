import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open scoped Topology
open Filter

/-- `VanishOff a b c d H` says that `H` vanishes at every point lying off the closed
box `[a,b] × [c,d]` (in either coordinate). -/
private def VanishOff (a b c d : ℝ) (H : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) → H z θ = 0

/-- The plain `z`-derivative of a function vanishing off the box again vanishes off the
box: off the box the `z`-slice is identically zero on a whole neighbourhood, hence its
(totalised) `deriv` is `0`. -/
private lemma pz_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.pz H) := by
  intro z θ hb
  have hev : (fun z' : ℝ => H z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    rcases hb with hz | hθ
    · filter_upwards [(isClosed_Icc (a := a) (b := b)).isOpen_compl.mem_nhds hz] with z' hz'
      exact h z' θ (Or.inl hz')
    · filter_upwards with z'
      exact h z' θ (Or.inr hθ)
  change deriv (fun z' : ℝ => H z' θ) z = 0
  rw [hev.deriv_eq, deriv_const]

/-- The plain `θ`-derivative of a function vanishing off the box again vanishes off the
box. -/
private lemma pth_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.pth H) := by
  intro z θ hb
  have hev : (fun θ' : ℝ => H z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    rcases hb with hz | hθ
    · filter_upwards with θ'
      exact h z θ' (Or.inl hz)
    · filter_upwards [(isClosed_Icc (a := c) (b := d)).isOpen_compl.mem_nhds hθ] with θ' hθ'
      exact h z θ' (Or.inr hθ')
  change deriv (fun θ' : ℝ => H z θ') θ = 0
  rw [hev.deriv_eq, deriv_const]

/-- `D_z H = z ∂_z H` of a function vanishing off the box again vanishes off the box. -/
private lemma Dz_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.Dz H) := by
  intro z θ hb
  change z * Work.Spaces.pz H z θ = 0
  rw [pz_vanishOff h z θ hb, mul_zero]

/-- `D_θ H = sin(2θ) ∂_θ H` of a function vanishing off the box again vanishes off the box. -/
private lemma Dth_vanishOff {a b c d : ℝ} {H : ℝ → ℝ → ℝ} (h : VanishOff a b c d H) :
    VanishOff a b c d (Work.Spaces.Dth H) := by
  intro z θ hb
  change Real.sin (2 * θ) * Work.Spaces.pth H z θ = 0
  rw [pth_vanishOff h z θ hb, mul_zero]

theorem mixed_eq_zero_off_box {G : ℝ → ℝ → ℝ} {a b c d : ℝ}
    (hG : ∀ z θ, G z θ ≠ 0 → z ∈ Set.Icc a b ∧ θ ∈ Set.Icc c d) :
    ∀ j i : ℕ, ∀ z θ : ℝ, (z ∉ Set.Icc a b ∨ θ ∉ Set.Icc c d) →
      Work.Spaces.mixed j i G z θ = 0 := by
  have hGQ : VanishOff a b c d G := by
    intro z θ hb
    by_contra hne
    rcases hG z θ hne with ⟨h1, h2⟩
    rcases hb with hz | hθ
    · exact hz h1
    · exact hθ h2
  -- every pure `θ`-iterate of `G` vanishes off the box
  have hDth : ∀ i : ℕ, VanishOff a b c d (Work.Spaces.DthIter i G) := by
    intro i
    induction i with
    | zero => exact hGQ
    | succ i ih => exact Dth_vanishOff ih
  intro j i z θ hb
  -- and then so does every further `z`-iterate
  have hDz : ∀ j : ℕ, VanishOff a b c d (Work.Spaces.DzIter j (Work.Spaces.DthIter i G)) := by
    intro j
    induction j with
    | zero => exact hDth i
    | succ j ih => exact Dz_vanishOff ih
  exact hDz j z θ hb

end Work.FTS.PhiStar.Honesty
