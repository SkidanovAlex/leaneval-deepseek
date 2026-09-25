import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.Hypotheses
import Submission.Work.Tower.Shafarevich.Group.generatorRank_eq_finrank_H1
import Submission.Work.Tower.Shafarevich.TowerStep

/-!
# Shafarevich's relation-rank estimate from the Kummer-theoretic input

This file derives **Shafarevich's relation-rank estimate** for the maximal pro-`p` extension of a
number field from the two named arithmetic hypotheses of `Work.CFT.Kummer.Hypotheses`
(facts **(a)** and **(b)** of Koch's Chapter 11), and transfers it to finite quotients of the
pro-`p` group using **Koch's transfer** (`Work.CFT.Kummer.KochTransfer`).

## Main results

* `Work.CFT.Kummer.finrank_H2Fp_le_finrank_kummerDual` — fact (a) alone: `dim H²(G_∅,𝔽_p) ≤ dim 𝓒_∅`.
* `Work.CFT.Kummer.finrank_H2Fp_le_H1Fp_add` — **Shafarevich's estimate**, `S = ∅`:
  `dim H²(G_∅,𝔽_p) ≤ dim H¹(G_∅,𝔽_p) + (r₁+r₂-1) + δ_{K,p}`.
* `Work.CFT.Kummer.finrank_H2Fp_le_H1Fp_add_two_of_rank_delta` — the shape used by the tower for
  a totally real cubic field `K` and `p = 3`: `dim H² ≤ dim H¹ + 2`.
* `Work.CFT.Kummer.finrank_H2Fp_quotient_le` — **the finite-quotient (Koch transfer) form**: for a
  quotient `G ⧸ N` with `N` the normal closure of `k` elements and `dim H¹(G ⧸ N) = dim H¹(G)`
  (the Frattini situation), `dim H²(G ⧸ N) ≤ dim H¹(G ⧸ N) + (r₁+r₂-1) + δ_{K,p} + k`.
* `Work.CFT.Kummer.finrank_H1Fp_quotient_frattini` — the Frattini hypothesis
  `dim H¹(G ⧸ N) = dim H¹(G)` holds automatically when `N` is the normal closure of elements of
  `Φ(G)` in a finite `p`-group `G`.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) (G : Type) [Group G]

variable [Fact p.Prime]

/-- **Fact (a)** of Koch's Chapter 11 (the Shafarevich injection) at `S = ∅`:
`dim_{𝔽_p} H²(G_∅, 𝔽_p) ≤ dim_{𝔽_p} 𝓒_∅`, where `𝓒_∅ = Hom(V_∅/K^{×p}, 𝔽_p)` is the Kummer
character group. -/
theorem finrank_H2Fp_le_finrank_kummerDual [h : UnramifiedShafarevich K p G] :
    Module.finrank (ZMod p) (H2Fp p G) ≤ Module.finrank (ZMod p) (kummerDual K p ∅) := by
  exact LinearMap.finrank_le_finrank_of_injective h.sha_injective

/-- **Shafarevich's relation-rank estimate at `S = ∅`** (the shape of paper Proposition 3.5 /
A.10, with `C₀ = r₁ + r₂ - 1 + δ_{K,p}`):
`dim_{𝔽_p} H²(G_∅, 𝔽_p) ≤ dim_{𝔽_p} H¹(G_∅, 𝔽_p) + (r₁+r₂-1) + δ_{K,p}`, where
`r₁ + r₂ - 1 = NumberField.Units.rank K` and `δ_{K,p} = deltaK K p`.

This is exactly [Koch, *Galois theory of p-extensions*, Ch. 11] plus the injection `Ш²_∅ ↪ 𝓒_∅`;
both are the hypotheses of `UnramifiedShafarevich`. -/
theorem finrank_H2Fp_le_H1Fp_add [h : UnramifiedShafarevich K p G] :
    Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (H1Fp p G) + NumberField.Units.rank K + deltaK K p := by
  have h1 := finrank_H2Fp_le_finrank_kummerDual K p G
  rw [h.rank_formula] at h1
  exact h1

/-- The estimate in the shape used by the tower for a **totally real cubic field** and `p = 3`:
`dim_{𝔽₃} H²(G_∅, 𝔽₃) ≤ dim_{𝔽₃} H¹(G_∅, 𝔽₃) + 2`.

The two numerical inputs are the unit rank `r₁ + r₂ - 1 = 2` and `δ_{K,3} = 0` (a totally real
field contains no primitive cube root of unity); they are isolated as hypotheses here and proved in
`Work.CFT.Kummer.TotallyRealCubic`. -/
theorem finrank_H2Fp_le_H1Fp_add_two_of_rank_delta [h : UnramifiedShafarevich K 3 G]
    (hrank : NumberField.Units.rank K = 2) (hdelta : deltaK K 3 = 0) :
    Module.finrank (ZMod 3) (H2Fp 3 G) ≤ Module.finrank (ZMod 3) (H1Fp 3 G) + 2 := by
  have h1 := finrank_H2Fp_le_H1Fp_add K 3 G
  rw [hrank, hdelta] at h1
  simpa using h1

/-- **The finite-quotient form** (Koch's transfer): if `N ◁ G` is the normal closure of `k`
elements and `dim H¹(G ⧸ N, 𝔽_p) = dim H¹(G, 𝔽_p)` — the situation when the killed elements lie
in the Frattini subgroup, see `finrank_H1Fp_quotient_frattini` — then

`dim H²(G ⧸ N, 𝔽_p) ≤ dim H¹(G ⧸ N, 𝔽_p) + (r₁+r₂-1) + δ_{K,p} + k`.

This is the form in which Shafarevich's estimate is applied to a finite level of the class field
tower (a maximal everywhere-unramified extension in which `k` primes with trivial Frattini
Frobenius class split completely). -/
theorem finrank_H2Fp_quotient_le [h : UnramifiedShafarevich K p G] (hk : KochTransfer p G)
    (k : ℕ) (g : Fin k → G)
    (hgen : Module.finrank (ZMod p) (H1Fp p (G ⧸ Subgroup.normalClosure (Set.range g))) =
      Module.finrank (ZMod p) (H1Fp p G)) :
    Module.finrank (ZMod p) (H2Fp p (G ⧸ Subgroup.normalClosure (Set.range g))) ≤
      Module.finrank (ZMod p) (H1Fp p (G ⧸ Subgroup.normalClosure (Set.range g))) +
        NumberField.Units.rank K + deltaK K p + k := by
  have h2 := hk (Subgroup.normalClosure (Set.range g)) k g rfl
  have h1 := finrank_H2Fp_le_H1Fp_add K p G
  rw [← hgen] at h1
  omega

/-- The finite-quotient form for a **totally real cubic field** and `p = 3`:
`dim H²(G ⧸ N, 𝔽₃) ≤ dim H¹(G ⧸ N, 𝔽₃) + 2 + k`. -/
theorem finrank_H2Fp_quotient_le_two_of_rank_delta [h : UnramifiedShafarevich K 3 G]
    (hk : KochTransfer 3 G) (k : ℕ) (g : Fin k → G)
    (hgen : Module.finrank (ZMod 3) (H1Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) =
      Module.finrank (ZMod 3) (H1Fp 3 G))
    (hrank : NumberField.Units.rank K = 2) (hdelta : deltaK K 3 = 0) :
    Module.finrank (ZMod 3) (H2Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) ≤
      Module.finrank (ZMod 3) (H1Fp 3 (G ⧸ Subgroup.normalClosure (Set.range g))) + 2 + k := by
  have h1 := finrank_H2Fp_quotient_le K 3 G hk k g hgen
  rw [hrank, hdelta] at h1
  simpa using h1

end Work.CFT.Kummer

namespace Work.CFT.Kummer

/-- The **Frattini (tower-cutting) hypothesis** of `finrank_H2Fp_quotient_le` is automatic: if
`g i` lie in the Frattini subgroup `Φ(G)` of a finite `p`-group `G`, then quotienting by their
normal closure does not change the generator rank (paper Proposition 3.3 / A.8,
`Work.Tower.Shafarevich.generatorRank_quotient_frattini_and_relationRankWith_le`), hence
(Burnside's basis theorem, `Work.Tower.Shafarevich.generatorRank_eq_finrank_H1`) does not change
`dim_{𝔽_p} H¹`. -/
theorem finrank_H1Fp_quotient_frattini {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
    (hG : IsPGroup p G) (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattini G) :
    Module.finrank (ZMod p) (H1Fp p (G ⧸ Subgroup.normalClosure (Set.range g))) =
      Module.finrank (ZMod p) (H1Fp p G) := by
  haveI : Finite (G ⧸ Subgroup.normalClosure (Set.range g)) := Quotient.finite _
  have hpG : IsPGroup p (G ⧸ Subgroup.normalClosure (Set.range g)) :=
    IsPGroup.to_quotient hG (Subgroup.normalClosure (Set.range g))
  have h := (Work.Tower.Shafarevich.generatorRank_quotient_frattini_and_relationRankWith_le
    hG k g hg).1
  rw [← Work.Tower.Shafarevich.generatorRank_eq_finrank_H1 p G hG,
    ← Work.Tower.Shafarevich.generatorRank_eq_finrank_H1 p
      (G ⧸ Subgroup.normalClosure (Set.range g)) hpG]
  exact h

end Work.CFT.Kummer
