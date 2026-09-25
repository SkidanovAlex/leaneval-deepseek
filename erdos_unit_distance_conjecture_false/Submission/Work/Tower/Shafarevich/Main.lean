import Mathlib
import Submission.Work.Tower.Defs
import Submission.Work.Tower.Shafarevich.Defs
import Submission.Work.Tower.Shafarevich.Estimate
import Submission.Work.Tower.Shafarevich.Group.generatorRank_eq_finrank_H1

/-!
# Shafarevich's relation-rank estimate: the target statement and the efficiency obstruction

This file relates the deliverable `Work.Tower.shafarevich_relation_bound` (paper
Proposition 3.5 / A.10) to

* the arithmetic input `Work.Tower.Shafarevich.H2Estimate` (Shafarevich's estimate on
  `dim H²(Gal(K/F), 𝔽₃)`), and
* the **efficiency** of finite `3`-groups (`Work.Tower.Shafarevich.IsEfficient`).

## The issue with the abstract relation rank

The deliverable states its conclusion with `Work.Tower.relationRankWith G (generatorRank G)`, the
minimal number of relators in an **abstract** presentation on a minimal generating set.  For a
finite `p`-group this quantity always satisfies

`dim_{𝔽_p} H²(G, 𝔽_p) ≤ relationRankWith G (generatorRank G)`

(Shafarevich's estimate bounds the left-hand side from above, not the right-hand side), and the
inequality is an equality exactly when `G` is **efficient**.  Whether every finite `p`-group is
efficient is Mann's Question 18 (Kourovka notebook), still open; the discrepancy is the
*deficiency* gap `def(G) ≤ rk(H₁(G, ℤ)) - d(H₂(G, ℤ))` of Gardam, *Finite groups of arbitrary
deficiency*, arXiv:1705.02040, inequality (⋆).

Consequently:

* if one uses the **pro-`p` relation rank** `Work.Tower.Shafarevich.proPRelationRank p G =
  dim_{𝔽_p} H²(G, 𝔽_p)` — the invariant Shafarevich's theorem actually bounds — then the estimate
  `H2Estimate` transfers directly (see `shafarevich_relation_bound_proP_of_H2_estimate`);
* to obtain the deliverable as literally stated, one needs in addition the efficiency of the
  finite `3`-groups `Gal(K/F)` arising (see
  `shafarevich_relation_bound_of_H2_estimate_of_efficient`).
-/

open NumberField
open scoped Classical

namespace Work.Tower

/-- **Shafarevich's relation-rank estimate with the pro-`p` relation rank.**  Given the arithmetic
input `H2Estimate C₀`, the pro-`p` relation rank `dim_{𝔽₃} H²(Gal(K/F), 𝔽₃)` of `Gal(K/F)` is at
most `generatorRank (Gal(K/F)) + C₀ + |T|`, where `K` is a finite everywhere-unramified Galois
`3`-extension of a totally real cubic field `F` which is maximal among those in which the primes of
`T` split completely. -/
theorem shafarevich_relation_bound_proP_of_H2_estimate (C₀ : ℕ)
    (h : Work.Tower.Shafarevich.H2Estimate C₀) :
    ∃ C₀' : ℕ, ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
      Module.finrank ℚ F = 3 →
      ∀ (K : Type) [Field K] [NumberField K] [Algebra F K]
        [FiniteDimensional F K] [IsGalois F K],
        Work.Tower.IsUnramifiedExtension F K →
        IsPGroup 3 (Gal(K/F)) →
        ∀ (T : Finset (Ideal (𝓞 F))) (hT : ∀ 𝔭 ∈ T, 𝔭.IsPrime),
          Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T →
          Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T →
          Work.Tower.Shafarevich.proPRelationRank 3 (Gal(K/F))
            ≤ Work.Tower.generatorRank (Gal(K/F)) + C₀' + T.card := by
  refine ⟨C₀, ?_⟩
  intro F _ _ _ hF K _ _ _ _ _ hKur h3 T hT hfr hmax
  haveI : Finite (Gal(K/F)) := inferInstance
  have h9 := Work.Tower.Shafarevich.generatorRank_eq_finrank_H1 3 (Gal(K/F)) h3
  have hb := h F hF K hKur h3 T hfr hmax
  rw [Work.Tower.Shafarevich.proPRelationRank, h9]
  exact hb

/-- **Shafarevich's relation-rank estimate for the abstract relation rank** (the deliverable), from
the arithmetic input `H2Estimate` together with the **efficiency** of the finite `3`-groups
`Gal(K/F)`: `relationRankWith (Gal(K/F)) (generatorRank (Gal(K/F))) = dim_{𝔽₃} H²(Gal(K/F), 𝔽₃)`.

The efficiency hypothesis is not known in general (Mann's Question 18); this theorem makes explicit
that the deliverable as stated needs it, in addition to Shafarevich's estimate. -/
theorem shafarevich_relation_bound_of_H2_estimate_of_efficient (C₀ : ℕ)
    (h : Work.Tower.Shafarevich.H2Estimate C₀)
    (heff : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
      Module.finrank ℚ F = 3 →
      ∀ (K : Type) [Field K] [NumberField K] [Algebra F K]
        [FiniteDimensional F K] [IsGalois F K],
        Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
        Work.Tower.relationRankWith (Gal(K/F)) (Work.Tower.generatorRank (Gal(K/F))) =
          Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H2Fp 3 (Gal(K/F)))) :
    ∃ C₀' : ℕ, ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F],
      Module.finrank ℚ F = 3 →
      ∀ (K : Type) [Field K] [NumberField K] [Algebra F K]
        [FiniteDimensional F K] [IsGalois F K],
        Work.Tower.IsUnramifiedExtension F K →
        IsPGroup 3 (Gal(K/F)) →
        ∀ (T : Finset (Ideal (𝓞 F))) (hT : ∀ 𝔭 ∈ T, 𝔭.IsPrime),
          Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T →
          Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T →
          Work.Tower.relationRankWith (Gal(K/F)) (Work.Tower.generatorRank (Gal(K/F)))
            ≤ Work.Tower.generatorRank (Gal(K/F)) + C₀' + T.card := by
  refine ⟨C₀, ?_⟩
  intro F _ _ _ hF K _ _ _ _ _ hKur h3 T hT hfr hmax
  haveI : Finite (Gal(K/F)) := inferInstance
  have h9 := Work.Tower.Shafarevich.generatorRank_eq_finrank_H1 3 (Gal(K/F)) h3
  have hb := h F hF K hKur h3 T hfr hmax
  have he := heff F hF K hKur h3
  calc Work.Tower.relationRankWith (Gal(K/F)) (Work.Tower.generatorRank (Gal(K/F)))
      = Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H2Fp 3 (Gal(K/F))) := he
    _ ≤ Module.finrank (ZMod 3) (Work.Tower.Shafarevich.H1Fp 3 (Gal(K/F))) + C₀ + T.card := hb
    _ = Work.Tower.generatorRank (Gal(K/F)) + C₀ + T.card := by rw [← h9]

end Work.Tower
