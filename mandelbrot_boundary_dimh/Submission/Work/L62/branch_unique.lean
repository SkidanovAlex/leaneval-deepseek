import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# L62 — uniqueness of the inverse branch of `ĥ = Ẽ - β` (Lemma 6.2 support)

Let `d : ParabData g₀ D` be the §4.1 data of a parabolic germ and `hd : HornData d` its horn data,
so that `d.E = Φ ∘ φ` is the lifted horn map.  `hd.Bu` is the component of `φ⁻¹(B)` containing the
upper half plane: it is open, connected and contained in `d.DE`, hence `d.E` is holomorphic on it.

The lemma proved here is the *uniqueness of a holomorphic section of `ĥ = d.E - β` over `hd.Bu`*:
if `H, H' : ℂ → ℂ` are differentiable on `hd.Bu`, both satisfy `ĥ (H w) = w` with `H w ∈ hd.Bu`
(resp. `H'`), and agree at one point `w₀`, then they agree on all of `hd.Bu`.

The proof is the standard one for sections of a locally biholomorphic map:

* `d.E` is holomorphic on the open set `hd.Bu` (chain rule from `Φ_holo`, `φ_holo` and
  `hd.sub : Bu ∪ Bl ⊆ d.DE`), so it is analytic there, and so is `ĥ`;
* differentiating `ĥ ∘ H = id` near `w₀` (chain rule) shows `deriv ĥ (H w₀) ≠ 0`; hence `ĥ` has a
  local inverse near `q = H w₀` — concretely, `AnalyticAt.hasStrictDerivAt.localInverse` gives a
  neighbourhood `U ∋ q` on which `ĥ` is injective;
* by continuity of `H` and `H'` at `w₀`, both `H w` and `H' w` lie in `U` for `w` near `w₀`, and
  both are pushed by `ĥ` to `w`, so `H = H'` near `w₀`;
* the difference `H - H'` is holomorphic on the open connected set `hd.Bu` and vanishes on a
  neighbourhood of `w₀`, so it vanishes identically (identity theorem
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).
-/

namespace Work.L62

open MandelDim Set Filter
open scoped Topology

/-- **Local injectivity from a nonvanishing derivative.**  A function analytic at `x` with
`deriv f x ≠ 0` is injective on a neighbourhood of `x`.  (The neighbourhood is the set where the
local inverse of `f` inverts `f`; see `HasStrictDerivAt.eventually_left_inverse`.) -/
lemma injOn_nhds_of_analyticAt_deriv_ne_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hfd : deriv f x ≠ 0) :
    ∃ U ∈ 𝓝 x, Set.InjOn f U := by
  have hd : HasStrictDerivAt f (deriv f x) x := hf.hasStrictDerivAt
  refine ⟨{z | HasStrictDerivAt.localInverse f (deriv f x) x hd hfd (f z) = z}, ?_, ?_⟩
  · exact hd.eventually_left_inverse hfd
  · intro y hy z hz hyz
    have h : HasStrictDerivAt.localInverse f (deriv f x) x hd hfd (f y) =
             HasStrictDerivAt.localInverse f (deriv f x) x hd hfd (f z) := by rw [hyz]
    rw [hy, hz] at h
    exact h

theorem branch_unique {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) (hd : HornData d) {β : ℂ}
    {H H' : ℂ → ℂ} (hHo : DifferentiableOn ℂ H hd.Bu) (hH'o : DifferentiableOn ℂ H' hd.Bu)
    (hH : ∀ w ∈ hd.Bu, (fun u => d.E u - β) (H w) = w ∧ H w ∈ hd.Bu)
    (hH' : ∀ w ∈ hd.Bu, (fun u => d.E u - β) (H' w) = w ∧ H' w ∈ hd.Bu)
    {w₀ : ℂ} (hw₀ : w₀ ∈ hd.Bu) (heq : H w₀ = H' w₀) :
    ∀ w ∈ hd.Bu, H w = H' w := by
  -- `d.E = Φ ∘ φ` is holomorphic on `hd.Bu`, since `hd.Bu ⊆ d.DE`
  have hφ_Bu : DifferentiableOn ℂ d.φ hd.Bu :=
    d.φ_holo.mono fun w hw => (hd.sub (Or.inl hw)).1
  have hE_diff : DifferentiableOn ℂ d.E hd.Bu :=
    d.Φ_holo.comp hφ_Bu fun w hw => (hd.sub (Or.inl hw)).2
  have hE_ana : AnalyticOnNhd ℂ d.E hd.Bu := hE_diff.analyticOnNhd hd.Bu_open
  have hq : H w₀ ∈ hd.Bu := (hH w₀ hw₀).2
  -- the derivative of `ĥ = d.E - β` at `q = H w₀` is nonzero: differentiate `ĥ ∘ H = id`
  have hq_ne : deriv (fun u => d.E u - β) (H w₀) ≠ 0 := by
    have hH_at : DifferentiableAt ℂ H w₀ := hHo.differentiableAt (hd.Bu_open.mem_nhds hw₀)
    have hqE_at : DifferentiableAt ℂ d.E (H w₀) :=
      hE_diff.differentiableAt (hd.Bu_open.mem_nhds hq)
    have hψ_at : DifferentiableAt ℂ (fun u => d.E u - β) (H w₀) := hqE_at.sub_const β
    have hev : (fun w => (fun u => d.E u - β) (H w)) =ᶠ[𝓝 w₀] id :=
      Filter.eventually_of_mem (hd.Bu_open.mem_nhds hw₀) fun w hw => (hH w hw).1
    have h1 : HasDerivAt (fun w => (fun u => d.E u - β) (H w)) 1 w₀ :=
      HasDerivAt.congr_of_eventuallyEq (hasDerivAt_id w₀) hev
    have h2 : HasDerivAt (fun w => (fun u => d.E u - β) (H w))
        (deriv (fun u => d.E u - β) (H w₀) * deriv H w₀) w₀ := by
      have h := (hψ_at.hasDerivAt).comp w₀ (hH_at.hasDerivAt)
      simpa [Function.comp_def] using h
    have huniq := h1.unique h2
    intro hzero
    rw [hzero, zero_mul] at huniq
    exact one_ne_zero huniq
  -- `ĥ` is injective on a neighbourhood `U` of `q`
  have hψ_ana : AnalyticAt ℂ (fun u => d.E u - β) (H w₀) :=
    (hE_ana (H w₀) hq).sub (analyticAt_const (v := β) (x := H w₀))
  obtain ⟨U, hU, hUinj⟩ := injOn_nhds_of_analyticAt_deriv_ne_zero hψ_ana hq_ne
  -- both `H` and `H'` land in `U` near `w₀`, so `H = H'` in a neighbourhood of `w₀`
  have hHc : ContinuousAt H w₀ := (hHo.differentiableAt (hd.Bu_open.mem_nhds hw₀)).continuousAt
  have hH'c : ContinuousAt H' w₀ := (hH'o.differentiableAt (hd.Bu_open.mem_nhds hw₀)).continuousAt
  have hpre : H ⁻¹' U ∈ 𝓝 w₀ := hHc.preimage_mem_nhds hU
  have hpre' : H' ⁻¹' U ∈ 𝓝 w₀ := hH'c.preimage_mem_nhds (heq ▸ hU)
  have hev2 : (fun w => H w - H' w) =ᶠ[𝓝 w₀] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [hpre, hpre', hd.Bu_open.mem_nhds hw₀] with w hwU hwU' hwB
    have h1 : (fun u => d.E u - β) (H w) = w := (hH w hwB).1
    have h2 : (fun u => d.E u - β) (H' w) = w := (hH' w hwB).1
    have hEqw : H w = H' w := hUinj hwU hwU' (by rw [h1, h2])
    simp [hEqw]
  -- identity theorem on the connected open set `hd.Bu`
  have hF_ana : AnalyticOnNhd ℂ (fun w => H w - H' w) hd.Bu :=
    (hHo.sub hH'o).analyticOnNhd hd.Bu_open
  have hEq : Set.EqOn (fun w => H w - H' w) (fun _ : ℂ => (0:ℂ)) hd.Bu :=
    hF_ana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      hd.Bu_conn.isPreconnected hw₀ hev2
  intro w hw
  exact sub_eq_zero.mp (hEq hw)

end Work.L62
