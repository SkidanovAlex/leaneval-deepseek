import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.montel_locallyBounded

namespace Work.Param

open Filter Topology

/-- **Montel + identity theorem: convergence on a nonempty open subset propagates.**  Let `F : ℕ → ℂ → ℂ`
be a sequence of holomorphic functions on a preconnected open set `U`, locally bounded on `U`
(`Work.Normal.IsLocallyBoundedOn`), and let `z` be holomorphic on `U`.  If `F n t → z t` for every
`t` in a nonempty open `A ⊆ U`, then `F n t → z t` for every `t ∈ U`.

(Proof: `Work.Normal.montel_locallyBounded` gives, for every subsequence, a further subsequence
converging locally uniformly on `U` to a holomorphic `h` (the `→∞` alternative is excluded by
local boundedness); `h = z` on `A`, hence on `U` by the identity theorem; conclude with
`Filter.tendsto_of_subseq_tendsto`.) -/
theorem vitali {U : Set ℂ} (hUo : IsOpen U) (hUpc : IsPreconnected U)
    {F : ℕ → ℂ → ℂ} {z : ℂ → ℂ}
    (hhol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hbdd : Work.Normal.IsLocallyBoundedOn (Set.range F) U)
    (hz : DifferentiableOn ℂ z U)
    {A : Set ℂ} (hAo : IsOpen A) (hAne : A.Nonempty) (hAU : A ⊆ U)
    (hconv : ∀ t ∈ A, Filter.Tendsto (fun n : ℕ => F n t) Filter.atTop (nhds (z t))) :
    ∀ t ∈ U, Filter.Tendsto (fun n : ℕ => F n t) Filter.atTop (nhds (z t)) := by
  -- Montel: the family of all the `F n` is normal on `U`
  have hnorm : Work.Normal.IsNormalFamily (Set.range F) U :=
    Work.Normal.montel_locallyBounded hUo (by rintro f ⟨n, rfl⟩; exact hhol n) hbdd
  -- a point of the (nonempty, open) set `A ⊆ U` where we know convergence
  obtain ⟨a, haA⟩ := hAne
  have haU : a ∈ U := hAU haA
  -- local boundedness at `a` rules out the `→∞` alternative
  have hbdd_a : ∃ M : ℝ, ∀ n : ℕ, ‖F n a‖ ≤ M := by
    obtain ⟨M, hM⟩ := hbdd {a} (by rintro x rfl; exact haU) isCompact_singleton
    exact ⟨M, fun n => hM (F n) ⟨n, rfl⟩ a rfl⟩
  -- key: every subsequence has a further subsequence converging pointwise on `U` to `z`
  have key : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ t ∈ U, Tendsto (fun k => F (ns (σ k)) t) atTop (nhds (z t)) := by
    intro ns hns
    obtain ⟨σ, hσ, hlim | hinf⟩ := hnorm (fun n => F (ns n)) (fun n => ⟨ns n, rfl⟩)
    · -- the convergent alternative
      obtain ⟨g, hg⟩ := hlim
      have hgdiff : DifferentiableOn ℂ g U :=
        hg.differentiableOn (Eventually.of_forall (fun n => hhol (ns (σ n)))) hUo
      -- `g` and `z` agree on `A`, hence on all of `U` by the identity theorem
      have hgA : Set.EqOn g z A := by
        intro t ht
        refine tendsto_nhds_unique (hg.tendsto_at (hAU ht)) ?_
        exact ((hconv t ht).comp hns).comp hσ.tendsto_atTop
      have hgU : Set.EqOn g z U :=
        (hgdiff.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
          (hz.analyticOnNhd hUo) hUpc haU (by
            filter_upwards [hAo.mem_nhds haA] with t ht using hgA ht)
      refine ⟨σ, hσ, fun t ht => ?_⟩
      have := hg.tendsto_at ht
      rw [hgU ht] at this
      exact this
    · -- the `→∞` alternative contradicts local boundedness at `a`
      obtain ⟨M, hM⟩ := hbdd_a
      obtain ⟨N, hN⟩ := hinf {a} (by rintro x rfl; exact haU) isCompact_singleton (M + 1)
      have h1 := hN N le_rfl a rfl
      have h2 := hM (ns (σ N))
      linarith
  -- every subsequence of `(F n t)` has a subsequence converging to `z t`
  intro t ht
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨σ, hσ, hkey⟩ := key ns hns
  exact ⟨σ, hkey t ht⟩

end Work.Param
