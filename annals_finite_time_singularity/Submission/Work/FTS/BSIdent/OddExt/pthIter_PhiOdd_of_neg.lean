import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdent.OddExt

open Filter
open scoped Topology

/-! ## Derivatives of the odd extension at a negative point

Write `H s = if 0 ≤ s then G s else -G (-s)` for the odd extension of a one-variable function `G`.
At a point `θ < 0` one has, as long as `G` is smooth enough at `-θ`,

  `H'(θ) = G'(-θ)`,   `H''(θ) = -G''(-θ)`.

The two lemmas below are the formal versions of these identities (everything is expressed directly
in terms of `deriv`, so that they apply to `Work.Spaces.pthIter`, which is an iterated `deriv`). -/

/-- **First derivative of the odd extension at a negative point.** -/
private lemma deriv_oddExt {G : ℝ → ℝ} {θ : ℝ} (hθ : θ < 0)
    (hG : DifferentiableAt ℝ G (-θ)) :
    deriv (fun s => if 0 ≤ s then G s else -G (-s)) θ = deriv G (-θ) := by
  have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 θ := isOpen_Iio.mem_nhds hθ
  have hev : (fun s : ℝ => if 0 ≤ s then G s else -G (-s)) =ᶠ[𝓝 θ] (fun s => -G (-s)) :=
    Filter.eventually_of_mem hmem (fun s hs => by
      have hs' : ¬ (0 ≤ s) := not_le.mpr hs
      simp [hs'])
  rw [hev.deriv_eq]
  have h := (hG.hasDerivAt.comp θ (hasDerivAt_neg θ)).neg
  have hv : (-(deriv G (-θ) * -1) : ℝ) = deriv G (-θ) := by ring
  rw [hv] at h
  exact h.deriv

/-- **Second derivative of the odd extension at a negative point.** -/
private lemma deriv_deriv_oddExt {G : ℝ → ℝ} {θ : ℝ} (hθ : θ < 0)
    (hG2 : ContDiffAt ℝ 2 G (-θ)) :
    deriv (fun s => deriv (fun t => if 0 ≤ t then G t else -G (-t)) s) θ
      = - deriv (fun s => deriv G s) (-θ) := by
  -- `deriv G` is differentiable at `-θ`, because `G` is `C²` there
  have hdiff : DifferentiableAt ℝ (deriv G) (-θ) := by
    obtain ⟨u, hu, hGon⟩ :=
      hG2.contDiffOn (m := 2) le_rfl (by intro h; exact absurd h (by norm_num))
    obtain ⟨v, hv_sub, hv_open, hv_mem⟩ := mem_nhds_iff.mp hu
    have hGon' : ContDiffOn ℝ 2 G v := hGon.mono hv_sub
    have hd : ContDiffOn ℝ 1 (deriv G) v := hGon'.deriv_of_isOpen hv_open (by norm_num)
    exact (hd.contDiffAt (hv_open.mem_nhds hv_mem)).differentiableAt_one
  -- the first derivative of the odd extension is `s ↦ deriv G (-s)` near `θ`
  have heq : (fun s => deriv (fun t => if 0 ≤ t then G t else -G (-t)) s)
      =ᶠ[𝓝 θ] (fun s => deriv G (-s)) := by
    have h1 : ∀ᶠ y in 𝓝 (-θ), ContDiffAt ℝ 2 G y := hG2.eventually (by norm_num)
    have htend : Tendsto (fun s : ℝ => -s) (𝓝 θ) (𝓝 (-θ)) := continuous_neg.tendsto θ
    have hnear : ∀ᶠ s in 𝓝 θ, DifferentiableAt ℝ G (-s) :=
      (htend.eventually h1).mono fun s hs => (hs.of_le (by norm_num)).differentiableAt_one
    filter_upwards [hnear, isOpen_Iio.mem_nhds hθ] with s hs hs0
    exact deriv_oddExt hs0 hs
  rw [heq.deriv_eq]
  have h := hdiff.hasDerivAt.comp θ (hasDerivAt_neg θ)
  have hv : (deriv (deriv G) (-θ) * (-1)) = - deriv (deriv G) (-θ) := by ring
  rw [hv] at h
  exact h.deriv

theorem pthIter_PhiOdd_of_neg {Φ : Work.FTS.BSIdent.Fam} {z θ τ : ℝ} (hθ : θ < 0)
    (hΦ : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (z, -θ)) :
    Work.Spaces.pthIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = -(Work.Spaces.pthIter 2 (fun z' θ' => Φ z' θ' τ) z (-θ)) := by
  -- the `θ`-slice of `Φ` is `C²` at `-θ`
  have hG2 : ContDiffAt ℝ 2 (fun s : ℝ => Φ z s τ) (-θ) := by
    have hincl : ContDiffAt ℝ 2 (fun s : ℝ => (z, s)) (-θ) := by fun_prop
    exact hΦ.comp (-θ) hincl
  have hmain := deriv_deriv_oddExt hθ hG2
  -- unfold the two `pthIter 2`s into iterated `deriv`s of the relevant slices
  have hL : Work.Spaces.pthIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
        = deriv (fun s => deriv (fun t => (if 0 ≤ t then (fun s => Φ z s τ) t
            else -((fun s => Φ z s τ) (-t)))) s) θ := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth,
      Work.FTS.BSIdent.PhiOdd]
  have hR : Work.Spaces.pthIter 2 (fun z' θ' => Φ z' θ' τ) z (-θ)
        = deriv (fun s => deriv (fun t => (fun s => Φ z s τ) t) s) (-θ) := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [hL, hR]
  simpa using hmain

end Work.FTS.BSIdent.OddExt
