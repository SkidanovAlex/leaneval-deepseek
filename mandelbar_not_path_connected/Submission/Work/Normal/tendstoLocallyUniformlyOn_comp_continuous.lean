import Mathlib
import Submission.Work.Normal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Normal

open Filter Set Topology
open scoped Uniformity

/-- Post-composing with a continuous function preserves locally uniform convergence, provided the
limit function is continuous on the set in question.  (`TendstoLocallyUniformlyOn` is the weak
neighbourhood-wise form, so mere continuity of `e` does not suffice when the limit `g` is
unbounded; `hg` is exactly the missing hypothesis: `g` is, in the intended applications, the
locally uniform limit of continuous functions, hence continuous.) -/
theorem tendstoLocallyUniformlyOn_comp_continuous {u : ℕ → ℂ → ℂ} {g e : ℂ → ℂ} {U : Set ℂ}
    (he : Continuous e) (hg : ContinuousOn g U) (hu : TendstoLocallyUniformlyOn u g atTop U) :
    TendstoLocallyUniformlyOn (fun n => e ∘ u n) (e ∘ g) atTop U := by
  -- We use the pointwise form of locally uniform convergence.
  intro W hW x hx
  -- `K` is a compact neighbourhood of `g x`; it will be the set on which `e` is uniformly
  -- continuous (Heine–Cantor).
  obtain ⟨K, hKc, hKmem⟩ := exists_compact_mem_nhds (g x)
  -- The "uniform continuity of `e` at the compact set `K`" gives an entourage `V` of `ℂ` such
  -- that points `a ∈ K` and `b` close to `a` have `(e a, e b) ∈ W`.
  have hV : {p : ℂ × ℂ | p.1 ∈ K → (e p.1, e p.2) ∈ W} ∈ 𝓤 ℂ :=
    hKc.uniformContinuousAt_of_continuousAt e (fun a _ => he.continuousAt) hW
  -- Continuity of `g` at `x` (within `U`) makes `g ⁻¹' K` a neighbourhood of `x` in `U`.
  have hpre : g ⁻¹' K ∈ 𝓝[U] x := hg.continuousWithinAt hx hKmem
  -- Local uniform convergence of `u` to `g` applies with the entourage `V`.
  obtain ⟨t₁, ht₁, hev⟩ := hu _ hV x hx
  refine ⟨g ⁻¹' K ∩ t₁, Filter.inter_mem hpre ht₁, ?_⟩
  filter_upwards [hev] with n hn y hy
  exact hn y hy.2 hy.1

end Work.Normal
