import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotV.Defs
import Submission.Work.MotK.CensusFibre.kleinFibre_eq_ker
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotK.TGen.STRulingDiv
import Submission.Work.MotK.TGen.ZTwistDiv

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The census clause of the source ruling divisor `sT` of the T-twisted Crauder--Katz link

`Work.MotK.TGen.sT a b h = kleinTwS a b h (kleinTwStereo a b h (pRa a b h) (chart3))` is the
degree-`10` *source ruling divisor* of the T-twisted Crauder--Katz link
(`Submission/Work/MotK/TGen/CensusFactors.lean`).  The claim of this file (the statement requested
as `Work.MotK.TGen.STClass`, and the second conjunct of `Work.MotK.TGenCensus`) is that *every*
codimension-one point `x` of `𝔸³_K` on which `sT` vanishes has residue field
`RatFunc ↥(twistFieldTG K D (h ^ 2))` — the function field of the residual curve `C' = Jac²(C_h)`,
tensored with one rational parameter — or else is *junk* in the sense of `Work.MotV.JunkClass`
(residue field a rational function field over some field, i.e. the divisor is ruled over a
curve of genus zero).

## The decomposition used here

The paper's argument (and the area's design, `TGen/GUIDE_CENSUS.md`, `MotK/GUIDE_K5K6.md`) splits
the statement into two *independent* geometric inputs, neither of which mentions both `sT` and
`twistFieldTG` at once:

* **the ruling (K5)** — `Work.MotK.TGen.STRulingDiv`: the divisor `{sT = 0}` is ruled over the
  residual curve `Z = V(Zcub a b h)` (the curve of positive-dimensional fibres of the twisted
  quadro map, `Work.MotK.TwCensus.ZI`); i.e. for every codimension-one point `x ∋ sT` the residue
  field is `FractionRing (Polynomial (K[x] ⧸ radical ZI))` — the function field of `Z × 𝔸¹` — or
  junk.  Unlike `Work.MotK.TwCensus.STRuling` this form is stated for *every* height-one prime
  containing `sT` (not only for the principal prime `(sT)`), so it covers the degenerate locus
  `{a = b} ∧ {h² = 1}` on which `sT` acquires the extra factor
  `linT = kleinTwBilin a b h pRa chart3` (whose prime is junk, `TGen.JunkClassKleinTwBilinChart`).
* **the base-curve identification (K6)** — `Work.MotK.TGen.ZTwistDiv`: the function field of the
  residual curve `Z` times `𝔸¹` is `RatFunc ↥(twistFieldTG K D (h ^ 2))`, i.e. `C' = Jac²(C_h)`
  whose twist class is `2T`.

`STClass` is then the two-line gluing of the two, which is what this file proves; the mathematical
content (the ruling and the Jacobian identification) is exactly the content of the two inputs.
The auxiliary `class_or_junk_of_mul` is the standard bookkeeping used when a divisor is only known
through an explicit *factorisation* (the case of the degenerate locus above, where
`sT = linT · g`).
-/

namespace Work.MotK.TGen

/-- **Gluing along a factorisation.**  If every codimension-one point containing `g` (resp. `g'`)
has residue field `RatFunc P` or is junk, then the same holds for every codimension-one point
containing the product `g * g'`: such a point is prime, hence contains one of the factors.

This is the bookkeeping step used for the degenerate locus of `sT` (`sT = linT · g` when
`a = b` and `h² = 1`), where the factor `linT` contributes only junk points. -/
theorem class_or_junk_of_mul {K : Type} [Field K] (P : Type) [Field P] [Algebra K P]
    (g g' : MvPolynomial (Fin 3) K)
    (hg : ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → g ∈ x.asIdeal →
      Nonempty (Work.MotV.resF K x ≃ₐ[K] RatFunc P) ∨ Work.MotV.JunkClass K x)
    (hg' : ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → g' ∈ x.asIdeal →
      Nonempty (Work.MotV.resF K x ≃ₐ[K] RatFunc P) ∨ Work.MotV.JunkClass K x) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → g * g' ∈ x.asIdeal →
      Nonempty (Work.MotV.resF K x ≃ₐ[K] RatFunc P) ∨ Work.MotV.JunkClass K x := by
  intro x hcx hx
  have hxprime : x.asIdeal.IsPrime := x.2
  rcases hxprime.mem_or_mem hx with hx | hx
  · exact hg x hcx hx
  · exact hg' x hcx hx

/-- **The census clause of the source ruling divisor `sT`** (the requested statement): every
codimension-one point of `𝔸³_K` which `sT` vanishes at has residue field
`RatFunc ↥(twistFieldTG K D (h ^ 2))` — the function field of the residual curve `C' = Jac²(C_h)`
times one rational parameter — or is junk.

The proof is the gluing of the ruling (`Work.MotK.TGen.STRulingDiv`, node K5: `{sT = 0}` is ruled
over the residual curve, with the extra components in the degenerate locus junk) with the
identification of the residual curve's function field (`Work.MotK.TGen.ZTwistDiv`, node K6:
`C' = Jac²(C_h)` has twist class `2T`, so its function field is the `h²`-twist field). -/
theorem STClass (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → Work.MotK.TGen.sT D.a D.b h ∈ x.asIdeal →
      Nonempty (Work.MotV.resF K x ≃ₐ[K] RatFunc ↥(Work.MotK.twistFieldTG K D (h ^ 2))) ∨
        Work.MotV.JunkClass K x := by
  intro x hcx hx
  obtain ⟨e₂⟩ := ZTwistDiv K hk D hD h hh
  rcases STRulingDiv K hk D hD h hh x hcx hx with hR | hj
  · obtain ⟨e₁⟩ := hR
    exact Or.inl ⟨e₁.trans e₂⟩
  · exact Or.inr hj

end Work.MotK.TGen
