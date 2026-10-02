import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.boundedOrbit_of_ball
import Submission.Work.LandLeaves.tantibar_family_continuous
import Submission.Work.LandLeaves.deriv_tantibar_family_continuous
import Submission.Work.LandLeaves.continuous_family_fixedpoint

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The local repelling branch family of the tricorn

`Work.LandLeaves.local_repelling_branch_family` is the parametric form of the local model of the
repelling dynamics of the tricorn `T_c z = z̄² + c`: at a repelling periodic point `y` of odd
period `k` the holomorphic second return map `τ_c = (T_c)^[2k]` has a fixed point, and this fixed
point, together with a local inverse branch of `τ_c` around it, depends continuously on the
parameter `c`, uniformly on a ball.

The proof is the parametric Banach fixed point theorem
(`Work.LandLeaves.continuous_family_fixedpoint`) applied twice to the *frozen Newton map*
`z ↦ z - (τ_f z - z)/D` (`D = deriv τ_c y`, of modulus `> 1`), whose derivative
`1 - τ_f'/D` is small near `(c,y)`, and to the moving-target version
`z ↦ z - (τ_f z - (yf f + u))/D`, whose inverse branch is the required `gg`.
-/

open Function Filter
open scoped Topology

set_option maxHeartbeats 800000

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open scoped Classical

namespace Work.LandLeaves

private lemma frozen_fixed_lip {k : ℕ} {f : ℂ} {D : ℂ} {y : ℂ} {ρ ε : ℝ}
    (hτ : Differentiable ℂ (fun w : ℂ => (Tantibar f)^[2 * k] w))
    (hD : 0 < ‖D‖) (hDne : D ≠ 0)
    (hb : ∀ ξ : ℂ, ‖ξ - y‖ ≤ ρ → ‖deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - D‖ ≤ ε) :
    ∀ z z' : ℂ, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ →
      ‖(z - ((Tantibar f)^[2 * k] z - z)/D) - (z' - ((Tantibar f)^[2 * k] z' - z')/D)‖
        ≤ ((1 + ε) / ‖D‖) * ‖z - z'‖ := by
  intro z z' hz hz'
  have hderiv : ∀ ξ ∈ Metric.closedBall y ρ,
      HasDerivWithinAt (fun w : ℂ => w - ((Tantibar f)^[2 * k] w - w)/D)
        (1 - (deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - 1)/D)
        (Metric.closedBall y ρ) ξ := by
    intro ξ _
    have hτ' : HasDerivAt (fun w : ℂ => (Tantibar f)^[2 * k] w)
        (deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ) ξ :=
      hτ.differentiableAt.hasDerivAt
    have hA : HasDerivAt (fun w : ℂ => (Tantibar f)^[2 * k] w - w)
        (deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - 1) ξ :=
      hτ'.sub (hasDerivAt_id ξ)
    have hB : HasDerivAt (fun w : ℂ => ((Tantibar f)^[2 * k] w - w)/D)
        ((deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - 1)/D) ξ :=
      hA.div_const D
    exact ((hasDerivAt_id ξ).sub hB).hasDerivWithinAt
  have hbound : ∀ ξ ∈ Metric.closedBall y ρ,
      ‖1 - (deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - 1)/D‖ ≤ (1 + ε)/‖D‖ := by
    intro ξ hξ
    have hξ' : ‖ξ - y‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hξ
    have hdb := hb ξ hξ'
    have hkey : 1 - (deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - 1)/D
        = (D - (deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - 1))/D := by
      field_simp
    rw [hkey, norm_div]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hD)
    have heq : D - (deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - 1)
        = (D - deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ) + 1 := by ring
    rw [heq]
    have h2 : ‖D - deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ‖ ≤ ε := by
      rw [norm_sub_rev]; exact hdb
    calc ‖(D - deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ) + 1‖
        ≤ ‖D - deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ ε + 1 := by rw [norm_one]; linarith
      _ = 1 + ε := by ring
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_closedBall y ρ)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz') (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

private lemma frozen_target_lip {k : ℕ} {f w : ℂ} {D : ℂ} {y : ℂ} {ρ ε : ℝ}
    (hτ : Differentiable ℂ (fun z : ℂ => (Tantibar f)^[2 * k] z))
    (hD : 0 < ‖D‖) (hDne : D ≠ 0)
    (hb : ∀ ξ : ℂ, ‖ξ - y‖ ≤ ρ → ‖deriv (fun z : ℂ => (Tantibar f)^[2 * k] z) ξ - D‖ ≤ ε) :
    ∀ z z' : ℂ, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ →
      ‖(z - ((Tantibar f)^[2 * k] z - w)/D) - (z' - ((Tantibar f)^[2 * k] z' - w)/D)‖
        ≤ (ε / ‖D‖) * ‖z - z'‖ := by
  intro z z' hz hz'
  have hderiv : ∀ ξ ∈ Metric.closedBall y ρ,
      HasDerivWithinAt (fun u : ℂ => u - ((Tantibar f)^[2 * k] u - w)/D)
        (1 - deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ / D)
        (Metric.closedBall y ρ) ξ := by
    intro ξ _
    have hτ' : HasDerivAt (fun u : ℂ => (Tantibar f)^[2 * k] u)
        (deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ) ξ :=
      hτ.differentiableAt.hasDerivAt
    have hA : HasDerivAt (fun u : ℂ => (Tantibar f)^[2 * k] u - w)
        (deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ) ξ :=
      hτ'.sub_const w
    have hB : HasDerivAt (fun u : ℂ => ((Tantibar f)^[2 * k] u - w)/D)
        (deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ / D) ξ :=
      hA.div_const D
    exact ((hasDerivAt_id ξ).sub hB).hasDerivWithinAt
  have hbound : ∀ ξ ∈ Metric.closedBall y ρ,
      ‖1 - deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ / D‖ ≤ ε/‖D‖ := by
    intro ξ hξ
    have hξ' : ‖ξ - y‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hξ
    have hdb := hb ξ hξ'
    have hkey : 1 - deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ / D
        = (D - deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ)/D := by
      field_simp
    rw [hkey, norm_div]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hD)
    rw [norm_sub_rev]; exact hdb
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_closedBall y ρ)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz') (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)

private lemma iterate_lip {k : ℕ} {f : ℂ} {D : ℂ} {y : ℂ} {ρ ε : ℝ}
    (hτ : Differentiable ℂ (fun z : ℂ => (Tantibar f)^[2 * k] z))
    (hb : ∀ ξ : ℂ, ‖ξ - y‖ ≤ ρ → ‖deriv (fun z : ℂ => (Tantibar f)^[2 * k] z) ξ - D‖ ≤ ε) :
    ∀ z z' : ℂ, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ →
      ‖(Tantibar f)^[2 * k] z - (Tantibar f)^[2 * k] z'‖ ≤ (‖D‖ + ε) * ‖z - z'‖ := by
  intro z z' hz hz'
  have hderiv : ∀ ξ ∈ Metric.closedBall y ρ,
      HasDerivWithinAt (fun u : ℂ => (Tantibar f)^[2 * k] u)
        (deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ) (Metric.closedBall y ρ) ξ := by
    intro ξ _
    exact (hτ.differentiableAt.hasDerivAt).hasDerivWithinAt
  have hbound : ∀ ξ ∈ Metric.closedBall y ρ,
      ‖deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ‖ ≤ ‖D‖ + ε := by
    intro ξ hξ
    have hξ' : ‖ξ - y‖ ≤ ρ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hξ
    have hdb := hb ξ hξ'
    have heq : deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ
        = (deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ - D) + D := by ring
    calc ‖deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ‖
        = ‖(deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ - D) + D‖ := by
            conv_lhs => rw [heq]
      _ ≤ ‖deriv (fun u : ℂ => (Tantibar f)^[2 * k] u) ξ - D‖ + ‖D‖ := norm_add_le _ _
      _ ≤ ε + ‖D‖ := by linarith
      _ = ‖D‖ + ε := by ring
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_closedBall y ρ)
    (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz') (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz)


theorem local_repelling_branch_family {c : ℂ} {k : ℕ} {y : ℂ}
    (h : Work.Landing.IsRepelling c k y) :
    ∃ (δ r r' κ : ℝ) (yf : ℂ → ℂ) (gg : ℂ → ℂ → ℂ),
      0 < δ ∧ 0 < r ∧ r < r' ∧ 0 ≤ κ ∧ κ < 1 ∧ yf c = y ∧ ContinuousAt yf c ∧
      (∀ f : ℂ, ‖f - c‖ < δ → (LeanEval.ComplexAnalysis.Tantibar f)^[2 * k] (yf f) = yf f) ∧
      (∀ f : ℂ, ‖f - c‖ < δ → ∀ w : ℂ, ‖w - yf f‖ ≤ r' → ‖gg f w - yf f‖ ≤ κ * ‖w - yf f‖) ∧
      (∀ f : ℂ, ‖f - c‖ < δ → ∀ w : ℂ, ‖w - yf f‖ ≤ r' → (LeanEval.ComplexAnalysis.Tantibar f)^[2 * k] (gg f w) = w) ∧
      (∀ f : ℂ, ‖f - c‖ < δ → ∀ z : ℂ, ‖z - yf f‖ ≤ r' → gg f ((LeanEval.ComplexAnalysis.Tantibar f)^[2 * k] z) = z) ∧
      (∀ f : ℂ, ‖f - c‖ < δ → Set.InjOn (fun z : ℂ => (LeanEval.ComplexAnalysis.Tantibar f)^[2 * k] z) (Metric.ball (yf f) r')) ∧
      ContinuousOn (fun p : ℂ × ℂ => gg p.1 p.2) {p : ℂ × ℂ | ‖p.1 - c‖ < δ ∧ ‖p.2 - yf p.1‖ < r'} := by
  obtain ⟨hper, hmult⟩ := h
  have hiter (f : ℂ) : (Work.Landing.Tsq f)^[k] = (Tantibar f)^[2 * k] := by
    rw [Work.LandLeaves.Tsq_eq_iterate_two, Function.iterate_mul]
  have hτdiff (f : ℂ) : Differentiable ℂ (fun z : ℂ => (Tantibar f)^[2 * k] z) := by
    have h1 : Differentiable ℂ (Work.Landing.Tsq f) := by
      show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star f) ^ 2 + f)
      fun_prop
    simpa only [hiter f] using h1.iterate k
  have hy : (Tantibar c)^[2 * k] y = y := by
    rw [show 2 * k = k * 2 from by ring, Function.iterate_mul]
    exact (show Function.IsFixedPt ((Tantibar c)^[k]) y from hper.2).iterate 2
  set D : ℂ := deriv (fun z : ℂ => (Tantibar c)^[2 * k] z) y with hDdef
  have hDval : D = Work.Landing.multiplier2 c k y := by
    rw [hDdef, Work.Landing.multiplier2]
    simp only [hiter c]
  have hD1 : 1 < ‖D‖ := by rw [hDval]; exact hmult
  have hDpos : 0 < ‖D‖ := by linarith
  have hDne : D ≠ 0 := fun h0 => absurd (by rw [h0, norm_zero] at hD1; exact hD1) (by norm_num)
  set ε : ℝ := (‖D‖ - 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hεlt : ε < ‖D‖ := by rw [hεdef]; linarith
  set κH : ℝ := ε / ‖D‖ with hκHdef
  have hκH0 : 0 ≤ κH := by rw [hκHdef]; positivity
  have hκH1 : κH < 1 := by rw [hκHdef, div_lt_one hDpos]; exact hεlt
  set κG : ℝ := (1 + ε) / ‖D‖ with hκGdef
  have hκG0 : 0 ≤ κG := by rw [hκGdef]; positivity
  have hκG1 : κG < 1 := by rw [hκGdef, div_lt_one hDpos]; linarith
  have h1κG : (1 - κG) * ‖D‖ = (‖D‖ - 1) / 2 := by
    rw [hκGdef, sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hDpos), hεdef]; ring
  have h1κH : (1 - κH) * ‖D‖ = (‖D‖ + 1) / 2 := by
    rw [hκHdef, sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hDpos), hεdef]; ring
  have h1κHpos : 0 < 1 - κH := by linarith
  have h1κGpos : 0 < 1 - κG := by linarith
  have h1κG'' : 1 - κG = (‖D‖ - 1) / (2 * ‖D‖) := by
    rw [eq_div_iff (by positivity : (2:ℝ) * ‖D‖ ≠ 0)]
    linarith [h1κG]
  -- (A) derivative bound near c, uniform on a ball
  obtain ⟨δa, hδapos, hδa⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ f : ℂ, ‖f - c‖ < δ → ∀ z : ℂ, ‖z - y‖ ≤ δ / 2 →
        ‖deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) z - D‖ ≤ ε := by
    have hlim : Tendsto (fun p : ℂ × ℂ => deriv (fun w : ℂ => (Tantibar p.1)^[2 * k] w) p.2)
        (𝓝 (c, y)) (𝓝 D) := (deriv_tantibar_family_continuous k).continuousAt
    have h2 : ∀ᶠ p : ℂ × ℂ in 𝓝 (c, y),
        dist (deriv (fun w : ℂ => (Tantibar p.1)^[2 * k] w) p.2) D < ε :=
      (Metric.tendsto_nhds.mp hlim) ε hεpos
    rw [Metric.eventually_nhds_iff] at h2
    obtain ⟨δ, hδpos, hδ⟩ := h2
    refine ⟨δ, hδpos, fun f hf z hz => ?_⟩
    have hdist : dist (f, z) (c, y) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [dist_eq_norm] using hf, by rw [dist_eq_norm]; linarith⟩
    have := hδ hdist
    rw [dist_eq_norm] at this
    exact le_of_lt this
  -- (B) continuity of `f ↦ τ_f y` with an arbitrary threshold
  have hcont_eta : ∀ T : ℝ, 0 < T → ∃ δ : ℝ, 0 < δ ∧
      ∀ f : ℂ, ‖f - c‖ < δ → ‖(Tantibar f)^[2 * k] y - y‖ ≤ T := by
    intro T hT
    have hlim : Tendsto (fun p : ℂ × ℂ => (Tantibar p.1)^[2 * k] p.2) (𝓝 (c, y))
        (𝓝 ((Tantibar c)^[2 * k] y)) :=
      (tantibar_family_continuous k).continuousAt (x := (c, y))
    rw [hy] at hlim
    have h2 : ∀ᶠ p : ℂ × ℂ in 𝓝 (c, y), dist ((Tantibar p.1)^[2 * k] p.2) y < T :=
      (Metric.tendsto_nhds.mp hlim) T hT
    rw [Metric.eventually_nhds_iff] at h2
    obtain ⟨δ, hδpos, hδ⟩ := h2
    refine ⟨δ, hδpos, fun f hf => ?_⟩
    have hdist : dist (f, y) (c, y) < δ := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [dist_eq_norm] using hf, by rw [dist_self]; exact hδpos⟩
    have := hδ hdist
    rw [dist_eq_norm] at this
    exact le_of_lt this
  -- scale and thresholds
  set ρ : ℝ := min (δa / 2) (1 / 2) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact lt_min (by linarith) (by norm_num)
  have hρ_le : ρ ≤ δa / 2 := by rw [hρdef]; exact min_le_left _ _
  have hρ_le1 : ρ ≤ 1 / 2 := by rw [hρdef]; exact min_le_right _ _
  have hDminus : 0 < ‖D‖ - 1 := by linarith
  set Tσ : ℝ := ρ * (‖D‖ - 1) / 64 with hTσdef
  have hTσpos : 0 < Tσ := by
    rw [hTσdef]; exact div_pos (mul_pos hρpos hDminus) (by norm_num)
  set Te : ℝ := ρ * min 1 (min ((‖D‖ - 1) / 8) ((‖D‖ + 1) / 16)) / 8 with hTedef
  have hTepos : 0 < Te := by
    rw [hTedef]
    have h1 : 0 < min 1 (min ((‖D‖ - 1) / 8) ((‖D‖ + 1) / 16)) :=
      lt_min (by norm_num) (lt_min (by linarith) (by linarith))
    exact div_pos (mul_pos hρpos h1) (by norm_num)
  have hTe_le : Te ≤ ρ / 8 := by
    rw [hTedef]
    have hm : min 1 (min ((‖D‖ - 1) / 8) ((‖D‖ + 1) / 16)) ≤ 1 := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_left hm (le_of_lt hρpos)
    rw [mul_one] at hmul
    linarith
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hcont_eta Te hTepos
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := hcont_eta Tσ hTσpos
  set δG : ℝ := min δa δ₂ with hδGdef
  set δH : ℝ := min δG (min δ₁ (ρ / 4)) with hδHdef
  have hδGpos : 0 < δG := by rw [hδGdef]; exact lt_min hδapos hδ₂pos
  have hδHpos : 0 < δH := by
    rw [hδHdef]; exact lt_min hδGpos (lt_min hδ₁pos (by linarith))
  have hδG_le_a : δG ≤ δa := by rw [hδGdef]; exact min_le_left _ _
  have hδG_le_2 : δG ≤ δ₂ := by rw [hδGdef]; exact min_le_right _ _
  have hδH_le_G : δH ≤ δG := by rw [hδHdef]; exact min_le_left _ _
  have hδH_le_1 : δH ≤ δ₁ := by
    rw [hδHdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδH_le_ρ4 : δH ≤ ρ / 4 := by
    rw [hδHdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδH_le_a : δH ≤ δa := le_trans hδH_le_G hδG_le_a
  have hderiv_bound : ∀ f : ℂ, ‖f - c‖ < δa → ∀ z : ℂ, ‖z - y‖ ≤ ρ →
      ‖deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) z - D‖ ≤ ε :=
    fun f hf z hz => hδa f hf z (le_trans hz hρ_le)
  -- the frozen Newton map for the fixed point
  set Gmap : ℂ → ℂ → ℂ := fun f z => z - ((Tantibar f)^[2 * k] z - z)/D with hGmap
  have hbaseG : Gmap c y = y := by
    show y - ((Tantibar c)^[2 * k] y - y)/D = y
    rw [hy, sub_self, zero_div, sub_zero]
  have hmapsG : ∀ f : ℂ, dist f c < δG → ‖Gmap f y - y‖ ≤ (1 - κG) * ρ := by
    intro f hf
    have hf' : ‖f - c‖ < δG := by rwa [dist_eq_norm] at hf
    have h1 : Gmap f y - y = -(((Tantibar f)^[2 * k] y - y)/D) := by
      show y - ((Tantibar f)^[2 * k] y - y)/D - y = -(((Tantibar f)^[2 * k] y - y)/D)
      ring
    have h2 : ‖Gmap f y - y‖ = ‖(Tantibar f)^[2 * k] y - y‖ / ‖D‖ := by
      rw [h1, norm_neg, norm_div]
    rw [h2]
    have h3 : ‖(Tantibar f)^[2 * k] y - y‖ ≤ Tσ := hδ₂ f (lt_of_lt_of_le hf' hδG_le_2)
    have h4 : Tσ / ‖D‖ ≤ (1 - κG) * ρ := by
      have hrearr : ((1 - κG) * ρ) * ‖D‖ = ρ * ((1 - κG) * ‖D‖) := by ring
      rw [div_le_iff₀ hDpos, hrearr, h1κG, hTσdef]
      have h64 : ρ * (‖D‖ - 1) / 64 ≤ ρ * ((‖D‖ - 1) / 2) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 64)]
        nlinarith [hρpos, hD1]
      linarith [h64]
    calc ‖(Tantibar f)^[2 * k] y - y‖ / ‖D‖ ≤ Tσ / ‖D‖ :=
          div_le_div_of_nonneg_right h3 (le_of_lt hDpos)
      _ ≤ (1 - κG) * ρ := h4
  have hlipG : ∀ f : ℂ, dist f c < δG → ∀ z z' : ℂ, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ →
      ‖Gmap f z - Gmap f z'‖ ≤ κG * ‖z - z'‖ := by
    intro f hf z z' hz hz'
    have hf' : ‖f - c‖ < δa := by
      have h1 : ‖f - c‖ < δG := by rwa [dist_eq_norm] at hf
      linarith [hδG_le_a]
    have hb : ∀ ξ : ℂ, ‖ξ - y‖ ≤ ρ →
        ‖deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - D‖ ≤ ε :=
      fun ξ hξ => hderiv_bound f hf' ξ hξ
    have h := frozen_fixed_lip (k := k) (f := f) (D := D) (hτ := hτdiff f) hDpos hDne hb z z' hz hz'
    have hgoal : ‖Gmap f z - Gmap f z'‖ = ‖(z - ((Tantibar f)^[2 * k] z - z)/D)
        - (z' - ((Tantibar f)^[2 * k] z' - z')/D)‖ := by
      congr 1 <;> exact rfl
    rw [hgoal, hκGdef]
    exact h
  have hcontG : ContinuousOn (fun q : ℂ × ℂ => Gmap q.1 q.2)
      {q : ℂ × ℂ | dist q.1 c < δG ∧ ‖q.2 - y‖ ≤ ρ} := by
    have hτs : ContinuousOn (fun q : ℂ × ℂ => (Tantibar q.1)^[2 * k] q.2)
        {q : ℂ × ℂ | dist q.1 c < δG ∧ ‖q.2 - y‖ ≤ ρ} :=
      (tantibar_family_continuous k).continuousOn
    have h1 : ∀ q : ℂ × ℂ, Gmap q.1 q.2 = q.2 - ((Tantibar q.1)^[2 * k] q.2 - q.2)/D :=
      fun q => rfl
    simp only [h1]
    exact (continuousOn_snd : ContinuousOn (fun q : ℂ × ℂ => q.2) _).sub
      ((hτs.sub continuousOn_snd).div_const D)
  -- fixed point family
  obtain ⟨yf, hyfc, hyfcont, hyffix, hyfbound, hyfuniq⟩ :=
    continuous_family_fixedpoint (ι := ℂ) (E := ℂ) (F := Gmap) (c := c) (y := y)
      (δ := δG) (ρ := ρ) (κ := κG) hδGpos hρpos hκG0 hκG1 hbaseG hmapsG hlipG hcontG
  -- the drift of the fixed point
  have hyf_drift : ∀ f : ℂ, ‖f - c‖ < δG → ‖yf f - y‖ ≤ ρ / 32 := by
    intro f hf
    have h1 : ‖yf f - y‖ ≤ ‖Gmap f y - y‖ / (1 - κG) := hyfbound f (by rwa [dist_eq_norm])
    have h2 : Gmap f y - y = -(((Tantibar f)^[2 * k] y - y)/D) := by
      show y - ((Tantibar f)^[2 * k] y - y)/D - y = -(((Tantibar f)^[2 * k] y - y)/D)
      ring
    have h3 : ‖Gmap f y - y‖ = ‖(Tantibar f)^[2 * k] y - y‖ / ‖D‖ := by
      rw [h2, norm_neg, norm_div]
    rw [h3] at h1
    have h4 : ‖(Tantibar f)^[2 * k] y - y‖ ≤ Tσ := hδ₂ f (lt_of_lt_of_le hf hδG_le_2)
    have h5 : ‖(Tantibar f)^[2 * k] y - y‖ / ‖D‖ ≤ Tσ / ‖D‖ :=
      div_le_div_of_nonneg_right h4 (le_of_lt hDpos)
    have h6 : Tσ / ‖D‖ / (1 - κG) = ρ / 32 := by
      have hDn : (2 : ℝ) * ‖D‖ ≠ 0 := by positivity
      have hKm : (1 - κG) ≠ 0 := ne_of_gt h1κGpos
      have hD1n : ‖D‖ - 1 ≠ 0 := ne_of_gt hDminus
      rw [hTσdef, h1κG'']
      field_simp
      ring
    calc ‖yf f - y‖ ≤ ‖(Tantibar f)^[2 * k] y - y‖ / ‖D‖ / (1 - κG) := h1
      _ ≤ Tσ / ‖D‖ / (1 - κG) := div_le_div_of_nonneg_right h5 h1κGpos.le
      _ = ρ / 32 := h6
  -- the moving-target frozen Newton map
  set Hmap : (ℂ × ℂ) → ℂ → ℂ := fun p z => z - ((Tantibar p.1)^[2 * k] z - (yf p.1 + p.2))/D
    with hHmap
  have hbaseH : Hmap (c, 0) y = y := by
    show y - ((Tantibar c)^[2 * k] y - (yf c + (0:ℂ)))/D = y
    rw [hy, hyfc, add_zero, sub_self, zero_div, sub_zero]
  have hmapsH : ∀ p : ℂ × ℂ, dist p (c, 0) < δH → ‖Hmap p y - y‖ ≤ (1 - κH) * ρ := by
    intro p hp
    rw [Prod.dist_eq, max_lt_iff] at hp
    have hp1 : ‖p.1 - c‖ < δH := by simpa [dist_eq_norm] using hp.1
    have hp2 : ‖p.2‖ < δH := by simpa [dist_eq_norm] using hp.2
    have hfG : ‖p.1 - c‖ < δG := lt_of_lt_of_le hp1 hδH_le_G
    have h1 : Hmap p y - y = -(((Tantibar p.1)^[2 * k] y - (yf p.1 + p.2))/D) := by
      show y - ((Tantibar p.1)^[2 * k] y - (yf p.1 + p.2))/D - y
        = -(((Tantibar p.1)^[2 * k] y - (yf p.1 + p.2))/D)
      ring
    have h2 : ‖Hmap p y - y‖ = ‖(Tantibar p.1)^[2 * k] y - (yf p.1 + p.2)‖ / ‖D‖ := by
      rw [h1, norm_neg, norm_div]
    rw [h2]
    have h3 : ‖(Tantibar p.1)^[2 * k] y - (yf p.1 + p.2)‖ ≤ 13 * ρ / 32 := by
      have hA : ‖(Tantibar p.1)^[2 * k] y - (yf p.1 + p.2)‖
          ≤ ‖(Tantibar p.1)^[2 * k] y - y‖ + ‖y - (yf p.1 + p.2)‖ := by
        simpa only [dist_eq_norm, norm_sub_rev] using
          dist_triangle ((Tantibar p.1)^[2 * k] y) y (yf p.1 + p.2)
      have hB : ‖y - (yf p.1 + p.2)‖ ≤ ‖y - yf p.1‖ + ‖p.2‖ := by
        calc ‖y - (yf p.1 + p.2)‖ = ‖(y - yf p.1) + (-p.2)‖ := by congr 1; ring
          _ ≤ ‖y - yf p.1‖ + ‖-p.2‖ := norm_add_le _ _
          _ = ‖y - yf p.1‖ + ‖p.2‖ := by rw [norm_neg]
      have hC : ‖(Tantibar p.1)^[2 * k] y - y‖ ≤ Te := hδ₁ p.1 (lt_of_lt_of_le hp1 hδH_le_1)
      have hD' : ‖yf p.1 - y‖ ≤ ρ / 32 := hyf_drift p.1 hfG
      have hE : ‖y - yf p.1‖ ≤ ρ / 32 := by rw [norm_sub_rev]; exact hD'
      have hF : ‖p.2‖ ≤ ρ / 4 := le_of_lt (lt_of_lt_of_le hp2 hδH_le_ρ4)
      linarith [hA, hB, hC, hE, hF, hTe_le]
    have h4 : (13 * ρ / 32) / ‖D‖ ≤ (1 - κH) * ρ := by
      have hrearr : ((1 - κH) * ρ) * ‖D‖ = ρ * ((1 - κH) * ‖D‖) := by ring
      rw [div_le_iff₀ hDpos, hrearr, h1κH]
      nlinarith [hρpos, hD1]
    calc ‖(Tantibar p.1)^[2 * k] y - (yf p.1 + p.2)‖ / ‖D‖ ≤ (13 * ρ / 32) / ‖D‖ :=
          div_le_div_of_nonneg_right h3 (le_of_lt hDpos)
      _ ≤ (1 - κH) * ρ := h4
  have hlipH : ∀ p : ℂ × ℂ, dist p (c, 0) < δH → ∀ z z' : ℂ, ‖z - y‖ ≤ ρ → ‖z' - y‖ ≤ ρ →
      ‖Hmap p z - Hmap p z'‖ ≤ κH * ‖z - z'‖ := by
    intro p hp z z' hz hz'
    rw [Prod.dist_eq, max_lt_iff] at hp
    have hp1 : ‖p.1 - c‖ < δa := by
      have h1 : ‖p.1 - c‖ < δH := by simpa [dist_eq_norm] using hp.1
      linarith [hδH_le_a]
    have hb : ∀ ξ : ℂ, ‖ξ - y‖ ≤ ρ →
        ‖deriv (fun w : ℂ => (Tantibar p.1)^[2 * k] w) ξ - D‖ ≤ ε :=
      fun ξ hξ => hderiv_bound p.1 hp1 ξ hξ
    have h := frozen_target_lip (k := k) (f := p.1) (w := yf p.1 + p.2) (D := D)
      (hτ := hτdiff p.1) hDpos hDne hb z z' hz hz'
    have hgoal : ‖Hmap p z - Hmap p z'‖ = ‖(z - ((Tantibar p.1)^[2 * k] z - (yf p.1 + p.2))/D)
        - (z' - ((Tantibar p.1)^[2 * k] z' - (yf p.1 + p.2))/D)‖ := by
      congr 1 <;> exact rfl
    rw [hgoal, hκHdef]
    exact h
  have hcontH : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => Hmap q.1 q.2)
      {q : (ℂ × ℂ) × ℂ | dist q.1 (c, 0) < δH ∧ ‖q.2 - y‖ ≤ ρ} := by
    set s : Set ((ℂ × ℂ) × ℂ) := {q | dist q.1 (c, 0) < δH ∧ ‖q.2 - y‖ ≤ ρ} with hsdef
    have hπ : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => q.1.1) s :=
      (continuous_fst.comp continuous_fst).continuousOn
    have hπmem : ∀ q ∈ s, q.1.1 ∈ {f : ℂ | dist f c < δG} := by
      intro q hq
      rw [hsdef, Set.mem_setOf_eq, Prod.dist_eq, max_lt_iff] at hq
      exact lt_of_lt_of_le hq.1.1 hδH_le_G
    have hyfs : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => yf q.1.1) s :=
      hyfcont.comp hπ (fun q hq => hπmem q hq)
    have hτs : ContinuousOn (fun q : (ℂ × ℂ) × ℂ => (Tantibar q.1.1)^[2 * k] q.2) s :=
      (tantibar_family_continuous k).comp_continuousOn
        (Continuous.prodMk (continuous_fst.comp continuous_fst) continuous_snd).continuousOn
    have h1 : ∀ q : (ℂ × ℂ) × ℂ,
        Hmap q.1 q.2 = q.2 - ((Tantibar q.1.1)^[2 * k] q.2 - (yf q.1.1 + q.1.2))/D := fun q => rfl
    simp only [h1, hsdef]
    refine ContinuousOn.sub continuousOn_snd (ContinuousOn.div_const ?_ D)
    exact ContinuousOn.sub hτs
      (ContinuousOn.add hyfs ((continuous_snd.comp continuous_fst).continuousOn))
  -- target inverse family
  obtain ⟨ψ, hψbase, hψcont, hψfix, hψbound, hψuniq⟩ :=
    continuous_family_fixedpoint (ι := ℂ × ℂ) (E := ℂ) (F := Hmap) (c := (c, 0)) (y := y)
      (δ := δH) (ρ := ρ) (κ := κH) hδHpos hρpos hκH0 hκH1 hbaseH hmapsH hlipH hcontH
  -- final constants
  set r' : ℝ := min (δH / (16 * (‖D‖ + ε + 1))) (ρ / 16) with hr'def
  set r : ℝ := r' / 2 with hrdef
  set κ' : ℝ := ((1 - κH) * ‖D‖)⁻¹ with hκ'def
  set gg : ℂ → ℂ → ℂ := fun f w => ψ (f, w - yf f) with hggdef
  have hDεpos : 0 < ‖D‖ + ε + 1 := by positivity
  have hr'pos : 0 < r' := by
    rw [hr'def]; exact lt_min (div_pos hδHpos (by positivity)) (by linarith)
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrr' : r < r' := by rw [hrdef]; linarith
  have hr'_le1 : r' ≤ δH / (16 * (‖D‖ + ε + 1)) := by rw [hr'def]; exact min_le_left _ _
  have hr'_le2 : r' ≤ ρ / 16 := by rw [hr'def]; exact min_le_right _ _
  have hr'_lt_δH : r' < δH := by
    have h1 : δH / (16 * (‖D‖ + ε + 1)) < δH := by
      have h16 : (1:ℝ) < 16 * (‖D‖ + ε + 1) := by linarith
      rw [div_lt_iff₀ (by positivity)]
      calc δH = δH * 1 := by ring
        _ < δH * (16 * (‖D‖ + ε + 1)) := mul_lt_mul_of_pos_left h16 hδHpos
    exact lt_of_le_of_lt hr'_le1 h1
  have hDε_r' : (‖D‖ + ε) * r' < δH := by
    have hstep : (‖D‖ + ε) * (δH / (16 * (‖D‖ + ε + 1))) < δH := by
      have h16 : (‖D‖ + ε) < 16 * (‖D‖ + ε + 1) := by linarith
      rw [mul_div_assoc', div_lt_iff₀ (by positivity : (0:ℝ) < 16 * (‖D‖ + ε + 1))]
      calc (‖D‖ + ε) * δH = δH * (‖D‖ + ε) := by ring
        _ < δH * (16 * (‖D‖ + ε + 1)) := mul_lt_mul_of_pos_left h16 hδHpos
    calc (‖D‖ + ε) * r' ≤ (‖D‖ + ε) * (δH / (16 * (‖D‖ + ε + 1))) :=
          mul_le_mul_of_nonneg_left hr'_le1 (by positivity)
      _ < δH := hstep
  have hκ'0 : 0 ≤ κ' := by rw [hκ'def]; positivity
  have hκ'1 : κ' < 1 := by
    rw [hκ'def, h1κH]
    exact inv_lt_one_of_one_lt₀ (by linarith)
  have hyfAt : ContinuousAt yf c := by
    have hmem : {f : ℂ | dist f c < δG} ∈ 𝓝 c :=
      Metric.mem_nhds_iff.mpr ⟨δG, hδGpos, fun x hx => hx⟩
    exact hyfcont.continuousAt hmem
  have hfix : ∀ f : ℂ, ‖f - c‖ < δH → (Tantibar f)^[2 * k] (yf f) = yf f := by
    intro f hf
    have h1 : Gmap f (yf f) = yf f := hyffix f (by rw [dist_eq_norm]; exact lt_of_lt_of_le hf hδH_le_G)
    have h1' : yf f - ((Tantibar f)^[2 * k] (yf f) - yf f)/D = yf f := h1
    have h2 : ((Tantibar f)^[2 * k] (yf f) - yf f)/D = 0 := sub_eq_self.mp h1'
    rw [div_eq_zero_iff] at h2
    rcases h2 with h2 | h2
    · exact sub_eq_zero.mp h2
    · exact absurd h2 hDne
  have hcontr : ∀ f : ℂ, ‖f - c‖ < δH → ∀ w : ℂ, ‖w - yf f‖ ≤ r' →
      ‖gg f w - yf f‖ ≤ κ' * ‖w - yf f‖ := by
    intro f hf w hw
    have hfG : ‖f - c‖ < δG := lt_of_lt_of_le hf hδH_le_G
    have hu : ‖w - yf f‖ < δH := lt_of_le_of_lt hw hr'_lt_δH
    have hpar : dist (f, w - yf f) (c, 0) < δH := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [dist_eq_norm] using hf, by simpa [dist_eq_norm] using hu⟩
    have hfixu : Hmap (f, w - yf f) (ψ (f, w - yf f)) = ψ (f, w - yf f) := hψfix _ hpar
    have hfixu' : ψ (f, w - yf f)
        - ((Tantibar f)^[2 * k] (ψ (f, w - yf f)) - (yf f + (w - yf f)))/D
        = ψ (f, w - yf f) := hfixu
    have hψle : ‖ψ (f, w - yf f) - y‖ ≤ ρ := by
      have h1 := hψbound (f, w - yf f) hpar
      have h2 := hmapsH (f, w - yf f) hpar
      have h3 : ‖Hmap (f, w - yf f) y - y‖ / (1 - κH) ≤ ρ := by
        rw [div_le_iff₀ h1κHpos]
        linarith
      linarith
    have hyfle : ‖yf f - y‖ ≤ ρ := by
      have h := hyf_drift f hfG
      linarith [hρpos, h]
    have hLips := hlipH (f, w - yf f) hpar (ψ (f, w - yf f)) (yf f) hψle hyfle
    have hkey2 : Hmap (f, w - yf f) (yf f) - yf f = (w - yf f)/D := by
      have h' : Hmap (f, w - yf f) (yf f)
          = yf f - ((Tantibar f)^[2 * k] (yf f) - (yf f + (w - yf f)))/D := rfl
      rw [h', hfix f hf]
      ring
    have hdecomp : ψ (f, w - yf f) - yf f
        = (Hmap (f, w - yf f) (ψ (f, w - yf f)) - Hmap (f, w - yf f) (yf f))
          + (Hmap (f, w - yf f) (yf f) - yf f) := by
      rw [hfixu]
      ring
    have hstep : ‖ψ (f, w - yf f) - yf f‖
        ≤ κH * ‖ψ (f, w - yf f) - yf f‖ + ‖w - yf f‖/‖D‖ := by
      calc ‖ψ (f, w - yf f) - yf f‖
          = ‖(Hmap (f, w - yf f) (ψ (f, w - yf f)) - Hmap (f, w - yf f) (yf f))
              + (Hmap (f, w - yf f) (yf f) - yf f)‖ := by rw [hdecomp]
        _ ≤ ‖Hmap (f, w - yf f) (ψ (f, w - yf f)) - Hmap (f, w - yf f) (yf f)‖
              + ‖Hmap (f, w - yf f) (yf f) - yf f‖ := norm_add_le _ _
        _ ≤ κH * ‖ψ (f, w - yf f) - yf f‖ + ‖(w - yf f)/D‖ := by
              rw [hkey2]
              exact add_le_add hLips le_rfl
        _ = κH * ‖ψ (f, w - yf f) - yf f‖ + ‖w - yf f‖/‖D‖ := by rw [norm_div]
    have hfinal : ‖ψ (f, w - yf f) - yf f‖ ≤ κ' * ‖w - yf f‖ := by
      have h1 : ‖ψ (f, w - yf f) - yf f‖ ≤ (‖w - yf f‖/‖D‖)/(1 - κH) := by
        rw [le_div_iff₀ h1κHpos]
        linarith
      refine le_trans h1 (le_of_eq ?_)
      have h1K : (1 - κH) ≠ 0 := ne_of_gt h1κHpos
      have h2K : ‖D‖ ≠ 0 := ne_of_gt hDpos
      have hK : (1 - κH) * ‖D‖ ≠ 0 := mul_ne_zero h1K h2K
      rw [hκ'def, inv_mul_eq_div, div_div, mul_comm (1 - κH) ‖D‖]
    rw [hggdef]
    exact hfinal
  have hright : ∀ f : ℂ, ‖f - c‖ < δH → ∀ w : ℂ, ‖w - yf f‖ ≤ r' →
      (Tantibar f)^[2 * k] (gg f w) = w := by
    intro f hf w hw
    have hu : ‖w - yf f‖ < δH := lt_of_le_of_lt hw hr'_lt_δH
    have hpar : dist (f, w - yf f) (c, 0) < δH := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [dist_eq_norm] using hf, by simpa [dist_eq_norm] using hu⟩
    have hfixu : Hmap (f, w - yf f) (ψ (f, w - yf f)) = ψ (f, w - yf f) := hψfix _ hpar
    have hfixu' : ψ (f, w - yf f)
        - ((Tantibar f)^[2 * k] (ψ (f, w - yf f)) - (yf f + (w - yf f)))/D
        = ψ (f, w - yf f) := hfixu
    have h0 : ((Tantibar f)^[2 * k] (ψ (f, w - yf f)) - (yf f + (w - yf f)))/D = 0 :=
      sub_eq_self.mp hfixu'
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · have h1 : (Tantibar f)^[2 * k] (ψ (f, w - yf f)) = yf f + (w - yf f) := sub_eq_zero.mp h0
      show (Tantibar f)^[2 * k] (gg f w) = w
      rw [hggdef, h1]
      ring
    · exact absurd h0 hDne
  have hleft : ∀ f : ℂ, ‖f - c‖ < δH → ∀ z : ℂ, ‖z - yf f‖ ≤ r' →
      gg f ((Tantibar f)^[2 * k] z) = z := by
    intro f hf z hz
    have hfG : ‖f - c‖ < δG := lt_of_lt_of_le hf hδH_le_G
    have hyfle : ‖yf f - y‖ ≤ ρ := by
      have h := hyf_drift f hfG
      linarith [hρpos, h]
    have hzρ : ‖z - y‖ ≤ ρ := by
      have h2 : ‖yf f - y‖ ≤ ρ / 32 := hyf_drift f hfG
      have h3 : z - y = (z - yf f) + (yf f - y) := by ring
      rw [h3]
      have h4 := norm_add_le (z - yf f) (yf f - y)
      have h5 : ‖z - yf f‖ ≤ ρ / 16 := le_trans hz hr'_le2
      linarith
    have hτz : ‖(Tantibar f)^[2 * k] z - yf f‖ < δH := by
      have hb : ∀ ξ : ℂ, ‖ξ - y‖ ≤ ρ →
          ‖deriv (fun w : ℂ => (Tantibar f)^[2 * k] w) ξ - D‖ ≤ ε :=
        fun ξ hξ => hderiv_bound f (lt_of_lt_of_le hf hδH_le_a) ξ hξ
      have h1 := iterate_lip (k := k) (f := f) (D := D) (hτ := hτdiff f) hb z (yf f) hzρ hyfle
      rw [hfix f hf] at h1
      have h2 : (‖D‖ + ε) * ‖z - yf f‖ ≤ (‖D‖ + ε) * r' :=
        mul_le_mul_of_nonneg_left hz (by positivity)
      linarith [h1, h2, hDε_r']
    have hpar : dist (f, (Tantibar f)^[2 * k] z - yf f) (c, 0) < δH := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by simpa [dist_eq_norm] using hf, by simpa [dist_eq_norm] using hτz⟩
    have hfixz : Hmap (f, (Tantibar f)^[2 * k] z - yf f) z = z := by
      show z - ((Tantibar f)^[2 * k] z - (yf f + ((Tantibar f)^[2 * k] z - yf f)))/D = z
      ring_nf
    have huniq := hψuniq (f, (Tantibar f)^[2 * k] z - yf f) hpar z hzρ hfixz
    rw [hggdef]
    exact huniq.symm
  have hinj : ∀ f : ℂ, ‖f - c‖ < δH →
      Set.InjOn (fun z : ℂ => (Tantibar f)^[2 * k] z) (Metric.ball (yf f) r') := by
    intro f hf z hz z' hz' hzz
    rw [Metric.mem_ball, dist_eq_norm] at hz hz'
    have h1 : ‖z - yf f‖ ≤ r' := le_of_lt hz
    have h2 : ‖z' - yf f‖ ≤ r' := le_of_lt hz'
    have hzz' : (Tantibar f)^[2 * k] z = (Tantibar f)^[2 * k] z' := by simpa using hzz
    calc z = gg f ((Tantibar f)^[2 * k] z) := (hleft f hf z h1).symm
      _ = gg f ((Tantibar f)^[2 * k] z') := by rw [hzz']
      _ = z' := hleft f hf z' h2
  have hcontgg : ContinuousOn (fun p : ℂ × ℂ => gg p.1 p.2)
      {p : ℂ × ℂ | ‖p.1 - c‖ < δH ∧ ‖p.2 - yf p.1‖ < r'} := by
    set U : Set (ℂ × ℂ) := {p : ℂ × ℂ | ‖p.1 - c‖ < δH ∧ ‖p.2 - yf p.1‖ < r'} with hUdef
    have hfst : ContinuousOn (fun p : ℂ × ℂ => p.1) U := continuous_fst.continuousOn
    have hyfU : ContinuousOn (fun p : ℂ × ℂ => yf p.1) U := by
      refine hyfcont.comp hfst ?_
      intro p hp
      rw [hUdef, Set.mem_setOf_eq] at hp
      have h1 : dist p.1 c < δG := by
        rw [dist_eq_norm]
        exact lt_of_lt_of_le hp.1 hδH_le_G
      exact h1
    have hΦ : ContinuousOn (fun p : ℂ × ℂ => (p.1, p.2 - yf p.1)) U :=
      ContinuousOn.prodMk hfst (continuousOn_snd.sub hyfU)
    have hmap : Set.MapsTo (fun p : ℂ × ℂ => (p.1, p.2 - yf p.1)) U (Metric.ball (c, 0) δH) := by
      intro p hp
      rw [hUdef, Set.mem_setOf_eq] at hp
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
      exact ⟨hp.1, by simpa using lt_trans hp.2 hr'_lt_δH⟩
    have h1 : ∀ p : ℂ × ℂ, gg p.1 p.2 = ψ (p.1, p.2 - yf p.1) := fun p => rfl
    simp only [h1, hUdef]
    exact hψcont.comp hΦ hmap
  refine ⟨δH, r, r', κ', yf, gg, hδHpos, hrpos, hrr', hκ'0, hκ'1, hyfc, hyfAt,
    hfix, hcontr, hright, hleft, hinj, hcontgg⟩

end Work.LandLeaves
