import Submission.Work.CFT.ShafarevichCore.Reduction

/-!
# The tower's relation-rank input needs only fact (a), not (b′)

## The finding

`Work.Tower.Shafarevich.H2Estimate` (hence `Work.CFT.ShafarevichTarget`) is the *uniform* statement

  `dim_{𝔽₃} H²(Γ, 𝔽₃) ≤ dim_{𝔽₃} H¹(Γ, 𝔽₃) + C₀ + |T|`

for the finite maximal `T`-split everywhere-unramified `3`-extension `Γ = Gal(K/F)`.  It is proved
(`Work.CFT.ShafarevichCore.finrank_H2Fp_le_H1Fp_add`) from Koch's two facts (a) and (b′).

The observation of this file is that the **tower construction itself** does not need that uniform
form.  Its Golod–Šafarevič endgame
(`Work.Tower.TowerCutProP.unramified_tower_gs_proP`) only uses the bound on the *maximal*
everywhere-unramified group, and there the relation rank is bounded *in terms of the class group*
by fact (a) **alone**:

  `dim_{𝔽₃} H²(G_∅, 𝔽₃) ≤ dim_{𝔽₃} 𝓒_∅ = dim_{𝔽₃} Cl_F[3] + (r₁+r₂-1) + δ`      (fact (a) + the
                                                                      *proved* Kummer computation)

For a totally real cubic field this is `≤ dim Cl_F[3] + 2`.  The generator rank, on the other
hand, is bounded *below* by the explicit genus field `M/F` (`Work.Tower.exists_cubic_unramified_extension_data`):
`d(G_∅) ≥ ℓ - 1`.  So the endgame condition `r(Ḡ) ≤ d(Ḡ)²/4` (after the `T`-cutting adding `|T|`)
becomes, with `M := dim Cl_F[3] + 2`,

  `M + |T| ≤ (ℓ-1)²/4`,

and this is exactly what **Minkowski's class-number bound** gives: for the cyclotomic cubic `F` of
conductor `∏_{i} r_i` one has `rd F = (∏ rᵢ)^{2/3}` and therefore
`dim Cl_F[3] ≤ log₃ h(F) ≤ (2/log 3) ∑ᵢ log rᵢ + O(log log(∏ rᵢ))`, which is `O(ℓ log ℓ)`,
while `|T| = 3⌊(ℓ-1)²/100⌋ = O(ℓ²)` and `(ℓ-1)²/4 = Ω(ℓ²)`.  Hence the condition holds for `ℓ`
large.

**Conclusion.** Artin reciprocity (fact (b′), the class-group rank formula) is **not** needed for
the tower: the relation-rank side of the Golod–Šafarevič estimate is supplied by (a) plus the
(already available) Minkowski class-number bound.  The single remaining arithmetic input of the
whole project is therefore **Koch's fact (a)** — the Shafarevich injection / Hasse principle for
the `p`-torsion of the Brauer group, i.e. `Work.CFT.ShafarevichCore.ShafarevichInjection`.

## This file

Records the key inequality in the vocabulary of `Work.CFT.ShafarevichCore`: the relation-rank
bound from (a) alone.
-/

open NumberField
open scoped Classical nonZeroDivisors

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.MinkowskiCut

open Work.CFT.ShafarevichCore

/-- **The tower's relation-rank bound from fact (a) alone.**  For the maximal everywhere-unramified
pro-`p` group `G` of `F`, Koch's injection alone gives

`dim_{𝔽_p} H²(G, 𝔽_p) ≤ dim_{𝔽_p} Cl_F[p] + (r₁ + r₂ - 1) + δ_{F,p}`,

because `H²(G,𝔽_p)` injects into `𝓒_∅ = Hom(V_∅/F^{×p}, 𝔽_p)` whose dimension is
`dim Cl_F[p] + NumberField.Units.rank F + deltaK F p` (the *proved* Kummer computation), and
`NumberField.Units.rank F = r₁ + r₂ - 1`.  No class-group rank formula (b′) is used. -/
theorem finrank_H2Fp_le_classGroupRank_add (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact p.Prime] (G : Type) [Group G] (h : ShafarevichInjection F p G) :
    Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (Work.CFT.Kummer.classGroupTorsion F p) + NumberField.Units.rank F +
        Work.CFT.Kummer.deltaK F p := by
  have ha : Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (Work.CFT.Kummer.kummerDual F p ∅) :=
    Work.CFT.ShafarevichCore.finrank_H2Fp_le_kummerDual F p G h
  have hK : Module.finrank (ZMod p) (Work.CFT.Kummer.kummerDual F p ∅) =
      Module.finrank (ZMod p) (Work.CFT.Kummer.classGroupTorsion F p) +
        NumberField.Units.rank F + Work.CFT.Kummer.deltaK F p :=
    Work.CFT.Kummer.finrank_kummerDual_empty F p
  omega

/-- The totally real cubic form used by the tower: `dim_{𝔽₃} H²(G,𝔽₃) ≤ dim_{𝔽₃} Cl_F[3] + 2`. -/
theorem finrank_H2Fp_le_classGroupRank_add_two_of_totallyReal_cubic (F : Type) [Field F]
    [NumberField F] [NumberField.IsTotallyReal F] (hdeg : Module.finrank ℚ F = 3)
    (G : Type) [Group G] (h : ShafarevichInjection F 3 G) :
    Module.finrank (ZMod 3) (H2Fp 3 G) ≤
      Module.finrank (ZMod 3) (Work.CFT.Kummer.classGroupTorsion F 3) + 2 := by
  have h1 := finrank_H2Fp_le_classGroupRank_add F 3 G h
  rw [Work.CFT.Kummer.units_rank_eq_two_of_totallyReal_cubic F hdeg,
    Work.CFT.Kummer.deltaK_eq_zero_of_totallyReal F 3 (by norm_num) (by norm_num)] at h1
  simpa using h1

end Work.CFT.MinkowskiCut
