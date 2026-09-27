import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.LAFree
import Submission.Work.EQ.Ladf.la_values_card
import Submission.Work.EQ.Ladf.la_components_card

/-!
# `Work.EQ.la_datum_finite`

The "determinacy" input `∃ δ, DatumFinite a h δ` of the limit analysis (Rychlik Lemma 5.1 /
Theorem 8(3)-(4)); see `Submission/Work/EQ/LAFree.lean` (`DatumSet`/`DatumFinite`) and the
comment in `limit_analysis`, which instantiates (
`limit_analysis_of ha0 ha1 hh ⟨_,la_tail_bound_seq …⟩ ⟨_,la_datum_finite …⟩ (…la_regular_periodic…)`.

## Shape of the argument (per `Submission/Work/EQ/DESIGN_LA.md`, item 5)

The target is definitionally `∃ δ, LAFree.DatumFinite a h δ`: finiteness of the set
`DatumSet a h r₁ r₂ M f b` of pairs `(c, S)` — a value and a regular component of that value —
realising the fixed reading datum `(f, [], b, M)` over the annulus `Ann r₁ r₂`.

Two independent statements about the datum give it:

* `Ladf.la_values_card` — **at most `2^M` values `c`.**  A witness `q` of `(c,S)` at `z₀` is the
  candidate chain `candChain a h f [] b M c z₀`; the section of `⁰H` through it has both its tails
  at depth `M` on a neighbourhood (`Ladf.wsec_tails_ball`), so the sheet
  `z ↦ (ugermC a h (λ^M c/z)).2` agrees there with the section's `(-M)`-th coordinate, which is one
  of the `2^M` labelled values `(bwdP a σ (fan a h f z)).2`.  The symmetric product
  `Q_c z = ∏_{|σ|=M} ((ugermC a h (λ^M c/z)).2 − (bwdP a σ (fan a h f z)).2)` is therefore
  label-free (hence analytic, `Submission.Work.EQ.bwdFanDefs`/`bwdP_fan_degenerate_countable`),
  vanishes on an open set and hence on the connected complement of the countable degenerate locus;
  it then vanishes at one fixed `z*`, where `ugermC.2` is injective (`germC_facts`) — so only the
  `2^M` values of `λ^M c/z*` survive.

* `Ladf.la_components_card` — **at most `2^M` components per value `c`.**

Given both, the projection `DatumSet → ℂ`, `(c,S) ↦ c` has finite image, and each fibre is the
image of a finite set (the components of that value) under `S ↦ (c,S)`; a set covered by finitely
many finite fibres is finite.
-/

namespace Work.EQ

theorem la_datum_finite {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < δ →
      1 / eqLam a < r₂ / r₁ →
      ∀ (M : ℕ) (f b : List Bool), f.length = M → b.length = M →
      (eqLam a : ℝ) ^ M * r₂ < δ →
      (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ →
        ({p : ℂ × Set ChainData |
            IsRegComp a h p.2 p.1 ∧ ‖p.1‖ ≤ 2 * rhoStar a h ∧
            ∃ q ∈ p.2, q.2.1 ∈ Ann r₁ r₂ ∧ q = candChain a h f [] b M p.1 q.2.1 ∧
              (∀ k : ℕ, M ≤ k → q.1 (k : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.1)) ∧
              (∀ k : ℕ, M ≤ k → q.1 (-(k : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ k * q.2.2))}
          : Set (ℂ × Set ChainData)).Finite := by
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Ladf.la_components_card ha0 ha1 hh hpos
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Ladf.la_values_card ha0 ha1 hh hpos
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro r₁ r₂ h1 h12 h2 h3 M f b hf hb h4 h5
  show (LAFree.DatumSet a h r₁ r₂ M f b).Finite
  have h2₁ : r₂ < δ₁ := lt_of_lt_of_le h2 (min_le_left _ _)
  have h2₂ : r₂ < δ₂ := lt_of_lt_of_le h2 (min_le_right _ _)
  have h4₁ : (eqLam a : ℝ) ^ M * r₂ < δ₁ := lt_of_lt_of_le h4 (min_le_left _ _)
  have h4₂ : (eqLam a : ℝ) ^ M * r₂ < δ₂ := lt_of_lt_of_le h4 (min_le_right _ _)
  have h5₁ : (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ₁ :=
    lt_of_lt_of_le h5 (min_le_left _ _)
  have h5₂ : (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ₂ :=
    lt_of_lt_of_le h5 (min_le_right _ _)
  have hVfin : {c : ℂ | ∃ S : Set ChainData, (c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b}.Finite :=
    hδ₂ r₁ r₂ M f b h1 h12 h2₂ h3 hf hb h4₂ h5₂
  rw [show LAFree.DatumSet a h r₁ r₂ M f b =
      ⋃ c ∈ {c : ℂ | ∃ S : Set ChainData, (c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b},
        ({p : ℂ × Set ChainData | p.1 = c} ∩ LAFree.DatumSet a h r₁ r₂ M f b) from by
    ext p
    constructor
    · intro hp
      exact Set.mem_biUnion (show p.1 ∈ _ from ⟨p.2, hp⟩) ⟨rfl, hp⟩
    · intro hp
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
      obtain ⟨-, hp'⟩ := Set.mem_iUnion.mp hc
      exact hp'.2]
  refine hVfin.biUnion (fun c hc => ?_)
  have hF : ({p : ℂ × Set ChainData | p.1 = c} ∩ LAFree.DatumSet a h r₁ r₂ M f b) =
      (fun S : Set ChainData => (c, S)) '' {S : Set ChainData |
        (c, S) ∈ LAFree.DatumSet a h r₁ r₂ M f b} := by
    ext p
    constructor
    · rintro ⟨hp1, hp2⟩
      have hp1' : p.1 = c := by simpa using hp1
      exact ⟨p.2, by rw [← hp1']; exact hp2, by rw [← hp1']⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨rfl, hS⟩
  rw [hF]
  exact (hδ₁ r₁ r₂ M f b h1 h12 h2₁ h3 hf hb h4₁ h5₁ c).image _

end Work.EQ
