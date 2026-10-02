import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.lowDegreeVanishingAndRanks

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The low-degree rational cohomology of the oriented Grassmannian: vanishing and dimensions

For `k, m ≥ 10`, with `G = G̃r_k(ℝ^{k+m})`:

* `H^j(G;ℚ)` is trivial for `j ∈ lowDegrees = {1,2,3,5,6,7}`,
* `H^4(G;ℚ)` is one-dimensional,
* `H^8(G;ℚ)` is two-dimensional.

The vanishing clause is `Work.ThomBordism.Grassmann.grassmannianLowDegreeVanishing` (the Borel
chain of Gysin windows, `Submission/Work/ThomBordism/Grassmann/grassmannianLowDegreeVanishing.lean`).
The upper bounds `rank H⁴ ≤ 1` and `rank H⁸ ≤ 2` are `lowDegreeVanishingAndRanks`.
The lower bound `2 ≤ rank H⁸` comes from the two probes `ℂP⁴ → G̃r_k(ℝ^{k+m})` of
`LowDegree.p1SqProbe` and `LowDegree.p2ProbeCP4_of_base`; the latter's base case at `(k,m) = (4,8)`
is supplied by the explicit gauge `V₄ ≅ Z₄` of `Submission/Work/ThomBordism/Grassmann/InclCrux/`
(`InclCrux.p2ProbeBase8_of_gauge InclCrux.gaugeIso`), so that the whole statement rests on
`p1Sq_p2_linearIndependent_via_probes` — constructed from the completed gauge of
`Submission/Work/ThomBordism/Grassmann/InclCrux/`, and not from the still unfinished continuity
lemma of `Submission/Work/ThomBordism/Grassmann/P2Base/gaugeIso.lean`.

Finally `Module.finrank = Cardinal.toNat ∘ Module.rank` over the field `ℚ`, so `rank = 1` resp.
`rank = 2` gives `finrank = 1` resp. `finrank = 2`.
-/

namespace Work.ThomBordism.Grassmann

open scoped TensorProduct

noncomputable section

/-! ## The `p₂`-probe, and hence the second independent class in degree eight -/

/-- **The `p₂`-probe at the base case `(4,8)`**, from the explicit gauge `V₄ ≅ Z₄` of
`InclCrux.p2GaugeSnap`: the pullback of `p₂(γ)` along `p2Map : ℂP⁴ → G̃r₄(ℝ¹²)` is `c₄(tautSum4)`,
which is rationally non-zero. -/
theorem p2ProbeBase8_of_gauge :
    ∃ σ : C(Work.Projective.CP 4, OG 4 8),
      TensorProduct.tmul ℤ (1 : ℚ) ((Work.Thom.CohMap σ ℤ 8).hom (p2 4 8)) ≠ 0 :=
  InclCrux.p2ProbeBase8_of_gauge InclCrux.gaugeIso

/-- **`2 ≤ rank H⁸(G̃r_k(ℝ^{k+m});ℚ)` for `k, m ≥ 10`**: the probes `LowDegree.p1SqProbe` and the
`p₂`-probe exhibit the linearly independent classes `p₁(γ)²` and `p₂(γ)`.  The independence is
`p1Sq_p2_linearIndependent_via_probes`, whose `p₂`-probe input is built from the `InclCrux` gauge
above (and *not* from the unfinished `P2Base/gaugeIso.lean`). -/
theorem two_le_rank_eight_of_gauge (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    2 ≤ Module.rank ℚ (Work.SignatureBordism.ratCohomology 8 (sset (OG k m))) := by
  have hind := p1Sq_p2_linearIndependent_via_probes k m hk hm
  have hcard := hind.cardinal_le_rank
  simpa using hcard

/-! ## The target -/

/-- **Vanishing and dimensions of the low-degree rational cohomology of the oriented
Grassmannian**: for `k, m ≥ 10`, `H^j(G̃r_k(ℝ^{k+m});ℚ) = 0` for `j ∈ {1,2,3,5,6,7}`, while
`H⁴` is one-dimensional and `H⁸` is two-dimensional over `ℚ`. -/
theorem lowDegreeVanishingAndDimensionsProbeIsland (k m : ℕ) (hk : 10 ≤ k) (hm : 10 ≤ m) :
    (∀ j ∈ Work.ThomBordism.Grassmann.lowDegrees,
      Subsingleton (Work.SignatureBordism.ratCohomology j
        (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.OG k m)))) ∧
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 4
        (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.OG k m))) = 1 ∧
    Module.finrank ℚ (Work.SignatureBordism.ratCohomology 8
        (Work.ThomBordism.Grassmann.sset (Work.ThomBordism.Grassmann.OG k m))) = 2 := by
  refine ⟨grassmannianLowDegreeVanishing k m hk hm, ?_, ?_⟩
  · exact Module.finrank_eq_of_rank_eq
      (le_antisymm (rank_four_le_one k m hk hm) (one_le_rank_four k m hk hm))
  · exact Module.finrank_eq_of_rank_eq
      (le_antisymm (rank_eight_le_two k m hk hm) (two_le_rank_eight_of_gauge k m hk hm))

end

end Work.ThomBordism.Grassmann
