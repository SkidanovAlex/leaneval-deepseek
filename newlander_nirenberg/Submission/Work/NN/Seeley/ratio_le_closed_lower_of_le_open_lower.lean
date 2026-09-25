/-
# Extending the Hölder bound from `(-δ, 0)` to the closed strip `(-δ, 0]`

If `f` is `C^{i+1}` on the strip `-δ < p.2 ≤ 0` and the ratio
`‖D^i f x - D^i f y‖ / ‖x - y‖^α` is bounded by `K` for pairs of *interior* points
(`-δ < p.2 < 0`), then the same bound holds for all pairs of points of the closed strip.
The boundary values are limits of interior values along the direction `(0, t)` with `t → 0⁻`,
using `ContDiffAt.continuousAt_iteratedFDeriv` for the continuity of the iterated derivative
and the fact that `‖x - y‖ > 0` is kept fixed along that direction.
-/
import Mathlib
import Submission.Work.NN.Seeley.Glob

namespace Work.NN.Seeley

open Filter Set
open scoped Topology

theorem ratio_le_closed_lower_of_le_open_lower {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X × ℝ → ℂ} {i : ℕ} {α δ K : ℝ}
    (hf : ∀ x : X × ℝ, -δ < x.2 → x.2 ≤ 0 → ContDiffAt ℝ (i + 1) f x)
    (h : ∀ x y : X × ℝ, -δ < x.2 → x.2 < 0 → -δ < y.2 → y.2 < 0 → x ≠ y →
      ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α ≤ K)
    {x y : X × ℝ} (hxδ : -δ < x.2) (hx : x.2 ≤ 0) (hyδ : -δ < y.2) (hy : y.2 ≤ 0)
    (hxy : x ≠ y) :
    ‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α ≤ K := by
  have hcx : ContinuousAt (iteratedFDeriv ℝ i f) x :=
    (hf x hxδ hx).continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have hcy : ContinuousAt (iteratedFDeriv ℝ i f) y :=
    (hf y hyδ hy).continuousAt_iteratedFDeriv (k := i) (by exact_mod_cast Nat.le_succ i)
  have hφ : Tendsto (fun t : ℝ => (x.1, x.2 + t)) (𝓝[<] (0 : ℝ)) (𝓝 x) := by
    have h1 : Tendsto (fun t : ℝ => (x.1, x.2 + t)) (𝓝 (0 : ℝ)) (𝓝 ((x.1, x.2 + 0))) :=
      (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
    simp only [add_zero] at h1
    rw [show ((x.1, x.2) : X × ℝ) = x from Prod.ext rfl rfl] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hψ : Tendsto (fun t : ℝ => (y.1, y.2 + t)) (𝓝[<] (0 : ℝ)) (𝓝 y) := by
    have h1 : Tendsto (fun t : ℝ => (y.1, y.2 + t)) (𝓝 (0 : ℝ)) (𝓝 ((y.1, y.2 + 0))) :=
      (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
    simp only [add_zero] at h1
    rw [show ((y.1, y.2) : X × ℝ) = y from Prod.ext rfl rfl] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have htx : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (x.1, x.2 + t)) (𝓝[<] (0 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i f x)) := hcx.tendsto.comp hφ
  have hty : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i f (y.1, y.2 + t)) (𝓝[<] (0 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i f y)) := hcy.tendsto.comp hψ
  have hlim : Tendsto
      (fun t : ℝ => ‖iteratedFDeriv ℝ i f (x.1, x.2 + t)
        - iteratedFDeriv ℝ i f (y.1, y.2 + t)‖ / ‖x - y‖ ^ α)
      (𝓝[<] (0 : ℝ))
      (𝓝 (‖iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i f y‖ / ‖x - y‖ ^ α)) :=
    (htx.sub hty).norm.div_const _
  refine le_of_tendsto hlim ?_
  have hIx : Set.Ioi (-(x.2 + δ)) ∈ 𝓝[<] (0 : ℝ) :=
    (Filter.le_def.mp nhdsWithin_le_nhds) _
      (isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith))
  have hIy : Set.Ioi (-(y.2 + δ)) ∈ 𝓝[<] (0 : ℝ) :=
    (Filter.le_def.mp nhdsWithin_le_nhds) _
      (isOpen_Ioi.mem_nhds (by simp only [Set.mem_Ioi]; linarith))
  filter_upwards [self_mem_nhdsWithin, hIx, hIy] with t ht htx' hty'
  have ht0 : t < 0 := ht
  have hxa : -δ < x.2 + t := by simp only [Set.mem_Ioi] at htx'; linarith
  have hya : -δ < y.2 + t := by simp only [Set.mem_Ioi] at hty'; linarith
  have hxb : x.2 + t < 0 := by linarith
  have hyb : y.2 + t < 0 := by linarith
  have hne : (x.1, x.2 + t) ≠ (y.1, y.2 + t) := by
    intro hcontra
    obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hcontra
    exact hxy (Prod.ext h1 (by linarith))
  have hd : ((x.1, x.2 + t) : X × ℝ) - (y.1, y.2 + t) = x - y := by ext <;> simp
  rw [← hd]
  exact h (x.1, x.2 + t) (y.1, y.2 + t) hxa hxb hya hyb hne

end Work.NN.Seeley
