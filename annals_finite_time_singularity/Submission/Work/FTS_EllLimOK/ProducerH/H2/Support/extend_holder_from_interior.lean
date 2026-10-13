import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS_EllLimOK.RulingELF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.H2.Support

open scoped Topology
open Filter Set

set_option autoImplicit false

/-- **Hölder continuity extends from a dense subset.**  If `F` is continuous on `s` and
`β`-Hölder (with constant `K`) on a subset `t ⊆ s` whose closure contains `s`, then `F` is
`β`-Hölder with the same constant on all of `s`.

The proof picks, for `p, q ∈ s`, sequences `u n, v n ∈ t` with `u n → p`, `v n → q`
(Fréchet–Urysohn), applies the interior bound and passes to the limit: both sides converge,
using the continuity of `F` on `s` and of `x ↦ x ^ β` at nonnegative points. -/
theorem holderOn_of_dense {X : Type*} [NormedAddCommGroup X] [FrechetUrysohnSpace X]
    {E : Type*} [NormedAddCommGroup E] {F : X → E} {t s : Set X} {K β : ℝ}
    (hβ : 0 < β) (hts : t ⊆ s) (hdense : s ⊆ closure t) (hcont : ContinuousOn F s)
    (hint : ∀ p ∈ t, ∀ q ∈ t, ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β) :
    ∀ p ∈ s, ∀ q ∈ s, ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β := by
  intro p hp q hq
  obtain ⟨u, hu_mem, hu_tend⟩ := mem_closure_iff_seq_limit.mp (hdense hp)
  obtain ⟨v, hv_mem, hv_tend⟩ := mem_closure_iff_seq_limit.mp (hdense hq)
  have hu_s : ∀ n, u n ∈ s := fun n => hts (hu_mem n)
  have hv_s : ∀ n, v n ∈ s := fun n => hts (hv_mem n)
  have huW : Tendsto u atTop (𝓝[s] p) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u hu_tend
      (Eventually.of_forall hu_s)
  have hvW : Tendsto v atTop (𝓝[s] q) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v hv_tend
      (Eventually.of_forall hv_s)
  have hlhs : Tendsto (fun n => ‖F (u n) - F (v n)‖) atTop (𝓝 ‖F p - F q‖) :=
    ((Filter.Tendsto.comp (hcont.continuousWithinAt hp) huW).sub
      (Filter.Tendsto.comp (hcont.continuousWithinAt hq) hvW)).norm
  have hrhs : Tendsto (fun n => K * ‖u n - v n‖ ^ β) atTop (𝓝 (K * ‖p - q‖ ^ β)) :=
    (((Real.continuousAt_rpow_const (‖p - q‖) β (Or.inr hβ.le)).tendsto.comp
      ((hu_tend.sub hv_tend).norm))).const_mul K
  exact le_of_tendsto_of_tendsto' hlhs hrhs
    (fun n => hint (u n) (hu_mem n) (v n) (hv_mem n))

theorem extend_holder_from_interior {a b K β : ℝ}
    {E : Type*} [NormedAddCommGroup E] {F : ℝ × ℝ → E} (hab : a < b) (hβ : 0 < β)
    (hcont : ContinuousOn F (Work.FTS_EllLimOK.cbox a b))
    (hint : ∀ p ∈ (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      ∀ q ∈ (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)),
      ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β) :
    ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
      ‖F p - F q‖ ≤ K * ‖p - q‖ ^ β := by
  -- the open quadrant `(a,b) × (0,π/2)` is dense in the closed box `[a,b] × [0,π/2]`
  have hdense : Work.FTS_EllLimOK.cbox a b ⊆
      closure (Set.Ioo a b ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    rw [closure_prod_eq, closure_Ioo (ne_of_lt hab), closure_Ioo (ne_of_lt Real.pi_div_two_pos)]
    intro x hx
    simpa only [Work.FTS_EllLimOK.cbox] using hx
  refine holderOn_of_dense hβ ?_ hdense hcont hint
  intro x hx
  exact ⟨⟨hx.1.1.le, hx.1.2.le⟩, ⟨hx.2.1.le, hx.2.2.le⟩⟩

end Work.FTS_EllLimOK.ProducerH.H2.Support
