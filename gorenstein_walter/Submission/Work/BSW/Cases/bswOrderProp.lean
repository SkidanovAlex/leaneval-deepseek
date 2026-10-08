import Submission.Work.BSW.Cases.Order.Assembly

namespace Work.BSW.Cases

/-- **Bender 1974, §2, "The order of G"** (`REFS/bender1974_bsw.txt`, pp. 230–232), `k = |K| > 4`.

Choose linear characters `ρ₁`, `ρ₂` of the abelian group `K` with `ρᵢ(t) = ±1` and `ρᵢ` not fixed
by the action of `s` (possible since `k ≥ 6`); put `α := (1_K − ρ₁)^H`, `β := (ρ₁ − ρ₂)^H` in the
class-function sense, with `⟨α,α⟩ = 3`, `⟨α,β⟩ = -1`, `⟨β,β⟩ = 2` on `H`.  By the Brauer–Suzuki TI
isometry (`OddOrder.RepresentationTheory.ClassFunction.inner_induce_eq_of_isTISubset`) the same
relations hold for the induced `α*`, `β*` on `G`, and `α*`, `β*` agree with `α`, `β` on `K`.
Frobenius reciprocity gives `⟨α*,1⟩ = 1`, `⟨β*,1⟩ = 0`, so `α* = 1_G + ψ₁ − ψ₂` and
`β* = λ₁ − λ₂` for irreducible characters of `G`.  Combining the involution-product formula
(Gorenstein 9.4.21) for `i(x) = #{u involution : x^u = x⁻¹}` with the values of `⟨α*, i⟩` and
`⟨β*, i⟩` gives `|G : H|` and then `|G| = (2k−1)(k−1)(2k)` or `|G| = (2k+1)(k+1)(2k)`. -/
theorem bswOrderProp : Work.BSW.BSWOrderProp := Work.BSW.Order.bswOrderProp_aux

end Work.BSW.Cases
