import Mathlib
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.L62C.continuousOn_pair
import Submission.Work.L62.eqOn_of_tendstoLocallyUniformlyOn

/-!
# Lemma 6.2, part (a): joint continuity of a family of self-maps of a bounded domain

Let `Ω ⊆ ℂ` be open, bounded, preconnected, with `0 ∈ Ω`, let `g` be holomorphic on `Ω` with
`g 0 = 0` and `g'(0) ≠ 0`, let `Λ` be compact, `c : ℂ → ℂ` continuous on `Λ`, and let
`H : ℂ → ℂ → ℂ` be a family with, for every `β ∈ Λ`:

* `H β` holomorphic on `Ω`, `H β '' Ω ⊆ Ω`, `H β 0 = 0`,
* `g (H β ζ) = c β · ζ` for every `ζ ∈ Ω`.

Then the evaluation map `(β, ζ) ↦ H β ζ` is continuous on `Λ × Ω`.

The mathematical content is that `H β` is *uniquely* determined by its equation: `g` is injective
near `0` (it has a nonzero derivative there), and `H β` is a self-map of the connected domain `Ω`,
so the identity theorem forces uniqueness.  Since `Ω` is bounded, the family `{H β}` is locally
bounded on `Ω` and hence normal (Montel); a locally uniform limit of a sequence `H βₙ` with
`βₙ → β₀` therefore satisfies the same equation and (by the uniqueness statement
`Work.L62.eqOn_of_tendstoLocallyUniformlyOn`) must equal `H β₀`.  This gives continuity in `β`
uniform on compacta of `Ω`, and `Work.L62C.continuousOn_pair` converts that into joint continuity.
-/

namespace Work.L62

open Set Filter
open scoped Topology

set_option linter.unusedVariables false

theorem cont_family_of_selfmap {Ω Λ : Set ℂ} {g : ℂ → ℂ} {H : ℂ → ℂ → ℂ} {c : ℂ → ℂ}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩc : IsPreconnected Ω) (h0 : (0 : ℂ) ∈ Ω)
    (hΛc : IsCompact Λ)
    (hg : DifferentiableOn ℂ g Ω) (hg0 : g 0 = 0) (hgd : deriv g 0 ≠ 0)
    (hc : ContinuousOn c Λ)
    (hHdiff : ∀ β ∈ Λ, DifferentiableOn ℂ (H β) Ω)
    (hHmap : ∀ β ∈ Λ, Set.MapsTo (H β) Ω Ω)
    (hHfix : ∀ β ∈ Λ, H β 0 = 0)
    (heq : ∀ β ∈ Λ, ∀ ζ ∈ Ω, g (H β ζ) = c β * ζ) :
    ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) (Λ ×ˢ Ω) := by
  refine Work.L62C.continuousOn_pair (fun β hβ => (hHdiff β hβ).continuousOn) ?_
  -- It remains to prove continuity in `β` uniformly on compact subsets of `Ω`.
  intro β₀ hβ₀ S hSΩ hSc ε hε
  by_contra hcon
  push Not at hcon
  -- A failing sequence of parameters and of points of `S`.
  have hex : ∀ n : ℕ, ∃ β z : ℂ,
      β ∈ Λ ∧ ‖β - β₀‖ < 1 / ((n : ℝ) + 1) ∧ z ∈ S ∧ ε ≤ ‖H β z - H β₀ z‖ := by
    intro n
    obtain ⟨β, hβ, hδ, z, hz, hbad⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨β, z, hβ, hδ, hz, hbad⟩
  choose b z hbΛ hbδ hzS hbad using hex
  have hbtend : Filter.Tendsto b Filter.atTop (nhds β₀) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hbδ n)) ?_
    simpa only using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Boundedness of `Ω` gives a uniform bound for the family, hence normality (Montel).
  obtain ⟨M, hM⟩ := hΩb.exists_norm_le
  have hhol : ∀ f ∈ Set.range (fun n => H (b n)), DifferentiableOn ℂ f Ω := by
    rintro f ⟨n, rfl⟩
    exact hHdiff _ (hbΛ n)
  have hbdd : Work.Normal.IsLocallyBoundedOn (Set.range (fun n => H (b n))) Ω := by
    intro K hKΩ _hKc
    exact ⟨M, fun f hf w hw => by
      obtain ⟨n, rfl⟩ := hf
      exact hM _ (hHmap _ (hbΛ n) (hKΩ hw))⟩
  have hnormal := Work.Normal.montel_locallyBounded hΩo hhol hbdd
  obtain ⟨φ, hφ, hlim | hatop⟩ := hnormal (fun n => H (b n)) (fun n => ⟨n, rfl⟩)
  · -- The extracted subsequence converges locally uniformly to some `H'`.
    obtain ⟨H', hH'lim⟩ := hlim
    -- Uniqueness of the limit function.
    have hEqOn : Set.EqOn H' (H β₀) Ω :=
      eqOn_of_tendstoLocallyUniformlyOn hΩo hΩc h0 hg hgd hc hHdiff hHfix heq
        hbΛ hβ₀ hbtend hφ hH'lim
    -- ... hence uniform convergence on the compact set `S`, contradicting the lower bound.
    have hTUnif : TendstoUniformlyOn (fun n => H (b (φ n))) (H β₀) Filter.atTop S :=
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hΩo).mp
        (hH'lim.congr_right hEqOn)) S hSΩ hSc
    have hev : ∀ᶠ n in Filter.atTop,
        dist (H β₀ (z (φ n))) (H (b (φ n)) (z (φ n))) < ε := by
      filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hTUnif) ε hε] with n hn
      exact hn (z (φ n)) (hzS (φ n))
    obtain ⟨n, hn⟩ := hev.exists
    have h1 : ε ≤ ‖H (b (φ n)) (z (φ n)) - H β₀ (z (φ n))‖ := hbad (φ n)
    have h2 : ‖H (b (φ n)) (z (φ n)) - H β₀ (z (φ n))‖ < ε := by
      simpa [dist_eq_norm, norm_sub_rev] using hn
    linarith
  · -- The alternative `H (b n) → ∞` locally uniformly is impossible: the maps fix `0`.
    obtain ⟨N, hN⟩ := hatop ({0} : Set ℂ) (Set.singleton_subset_iff.mpr h0)
      isCompact_singleton (1 : ℝ)
    have h1 : (1 : ℝ) ≤ ‖H (b (φ N)) 0‖ := hN N le_rfl 0 (Set.mem_singleton 0)
    rw [hHfix _ (hbΛ _)] at h1
    norm_num at h1

end Work.L62
