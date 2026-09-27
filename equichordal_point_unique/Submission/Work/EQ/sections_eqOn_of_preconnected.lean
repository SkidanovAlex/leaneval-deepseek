import Mathlib
import Submission.Work.EQ.EquiLocalDefs

namespace Work.EQ

/-- **Rigidity of local sections of `ψ₁ : H0 ⊆ ChainData → ℂ` over a preconnected set.**  Two continuous maps `f, g : ℂ → ChainData` whose values lie in `H0 a h` and satisfy `ψ₁ (f u) = w u = ψ₁ (g u)` on a preconnected set `U` (for an *arbitrary* function `w : ℂ → ℂ`, in particular the parametrisation `w u = u₀ + uᵏ` of a chart leg) are equal on `U` as soon as they agree at a single point of `U`.  No hypothesis on `w` is needed.  This generalises `Work.EQ.sections_agree_nearby` (the case `w = id` on a ball around the base value of a single point `q ∈ H0`) to arbitrary preconnected `U` and arbitrary `w`.

Proof.  The agreement set `A = {u ∈ U | f u = g u}` is closed (`ChainData` is Hausdorff, `f, g` are continuous) and open in `U`: at `u ∈ A`, `LocalInj` (clause 1 of `Work.EQ.H0_structure`, packaged by the hypothesis `hLI : LocalInj a h`) gives an open neighbourhood `V` of `f u = g u` on which `ψ₁` is injective on `V ∩ H0`; by continuity of `f, g` at `u`, for `u'` near `u` both `f u'` and `g u'` lie in `V`, they lie in `H0` and have equal `ψ₁`-value `w u'`, so `f u' = g u'`.  Hence `A` is clopen in `U`; `U` is preconnected and `A ∋ u₀` is nonempty, so `A = U`.  A convenient formalisation is to view `U` as a subtype (`IsConnected` gives `ConnectedSpace ↥U`; see `Work.EQ.Chart.stab_invariance_of_one_point` for the same argument in a special case) and use `IsClopen.eq_univ`, or to use `IsPreconnected.subset_left_of_subset_union` with the open sets `U ∩ A` and `U \ A`. -/
theorem sections_eqOn_of_preconnected {a : ℝ} {h : ℂ → ℂ} {U : Set ℂ}
    (hLI : LocalInj a h) (hU : IsPreconnected U) {w : ℂ → ℂ} {f g : ℂ → ChainData}
    (hf : ContinuousOn f U) (hg : ContinuousOn g U)
    (hfm : ∀ u ∈ U, f u ∈ H0 a h ∧ (f u).2.1 = w u)
    (hgm : ∀ u ∈ U, g u ∈ H0 a h ∧ (g u).2.1 = w u)
    {u₀ : ℂ} (hu₀ : u₀ ∈ U) (heq : f u₀ = g u₀) :
    ∀ u ∈ U, f u = g u := by
  -- View `U` as a topological space: it is preconnected, hence the subtype is `PreconnectedSpace`.
  have : PreconnectedSpace ↥U := isPreconnected_iff_preconnectedSpace.mp hU
  -- The agreement set, as a subset of the subtype `↥U`.
  set A : Set ↥U := {u | f (u : ℂ) = g (u : ℂ)} with hA
  have hAmem : ∀ u : ↥U, u ∈ A ↔ f (u : ℂ) = g (u : ℂ) := by
    intro u; rw [hA]; exact Iff.rfl
  -- `A` is closed: it is the preimage of the diagonal of the Hausdorff space `ChainData`.
  have hclosed : IsClosed A := by
    rw [hA]
    exact isClosed_eq hf.domRestrict hg.domRestrict
  -- `A` is open: near a point of `U` the `ψ₁`-values match, and `ψ₁` is locally injective.
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro u hu
    obtain ⟨V, hVo, hfV, hVinj⟩ := hLI (f (u : ℂ)) (hfm (u : ℂ) u.2).1
    set N : Set ↥U := U.domRestrict f ⁻¹' V ∩ U.domRestrict g ⁻¹' V with hN
    have hNopen : IsOpen N := by
      rw [hN]; exact (hVo.preimage hf.domRestrict).inter (hVo.preimage hg.domRestrict)
    have huN : u ∈ N := by
      rw [hN, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage]
      refine ⟨?_, ?_⟩
      · exact hfV
      · change g (u : ℂ) ∈ V; rw [← (hAmem u).mp hu]; exact hfV
    have hNA : N ⊆ A := by
      intro u' hu'
      rw [hN, Set.mem_inter_iff, Set.mem_preimage, Set.mem_preimage] at hu'
      obtain ⟨h1, h2⟩ := hu'
      rw [hAmem]
      exact hVinj (f (u' : ℂ)) h1 (hfm (u' : ℂ) u'.2).1 (g (u' : ℂ)) h2 (hgm (u' : ℂ) u'.2).1
        (by rw [(hfm (u' : ℂ) u'.2).2, (hgm (u' : ℂ) u'.2).2])
    exact Filter.mem_of_superset (hNopen.mem_nhds huN) hNA
  -- `A` is a nonempty clopen subset of the preconnected space `↥U`, hence everything.
  have hne : A.Nonempty := ⟨⟨u₀, hu₀⟩, (hAmem _).mpr heq⟩
  have huniv : A = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  intro u hu
  have : (⟨u, hu⟩ : ↥U) ∈ A := by rw [huniv]; exact Set.mem_univ _
  exact (hAmem _).mp this

end Work.EQ
