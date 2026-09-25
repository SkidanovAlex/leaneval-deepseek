import Mathlib
import Submission.Work.CFTLib.fiveTerm_transgression

/-!
# The dimension identity of the five-term inflation–restriction sequence

Let `π : G' →* G` be a surjective homomorphism of finite groups, `N = ker π`, and work with
trivial `𝔽_p`-coefficients.  This file assembles the dimension count

`dim im(H²(G) → H²(G')) + dim H¹(N)^{G'} + dim H¹(G) = dim H²(G) + dim H¹(G')`,

i.e. `e + c + a = d + b` with `a = dim H¹(G)`, `b = dim H¹(G')`, `c = dim H¹(N)^{G'}`,
`d = dim H²(G)` and `e = dim im(inf)`.

The count is pure linear algebra applied to the exact sequence

`Hom(G,𝔽_p) → Hom(G',𝔽_p) → H¹(N,𝔽_p)^{G'} → H²(G,𝔽_p) → H²(G',𝔽_p)`:

* `b = r + a` where `r = dim im(beta)` (rank–nullity for the restriction map, whose kernel is
  the range of the inflation `alpha`);
* `c = K + r` where `K = dim ker(inf)` (rank–nullity for the transgression, whose range is
  `ker inf` and whose kernel is `im beta`);
* `d = e + K` (rank–nullity for the inflation itself).

The three rank–nullity facts are taken as hypotheses here so that this file records only the
exactness bookkeeping; they are supplied in `fiveTerm_finrank`.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

variable (p : ℕ) [Fact p.Prime] {G G' : Type} [Group G] [Group G']

/-- **The dimension identity of the five-term inflation–restriction sequence**, given the three
rank–nullity facts for the inflation on characters, the transgression and the inflation on `H²`. -/
theorem fiveTerm_finrank_abstract_of_nullity [Fintype G] [Fintype G'] (π : G' →* G)
    (hπ : Function.Surjective π)
    (hβ : Module.finrank (ZMod p) (Additive G' →+ ZMod p)
      = Module.finrank (ZMod p) (LinearMap.ker (beta (p := p) π))
        + Module.finrank (ZMod p) (LinearMap.range (beta (p := p) π)))
    (htg : Module.finrank (ZMod p) (invCharSubmodule p π.ker)
      = Module.finrank (ZMod p) (LinearMap.ker (transgression p π hπ))
        + Module.finrank (ZMod p) (LinearMap.range (transgression p π hπ)))
    (hinf : Module.finrank (ZMod p) (H2 p G)
      = Module.finrank (ZMod p) (LinearMap.ker (inflMap p π))
        + Module.finrank (ZMod p) (LinearMap.range (inflMap p π))) :
    Module.finrank (ZMod p) (LinearMap.range (groupCohomology.map π
        (𝟙 _ : Rep.res π (Rep.trivial (ZMod p) G (ZMod p)) ⟶
          Rep.trivial (ZMod p) G' (ZMod p)) 2).hom)
      + Module.finrank (ZMod p) (invCharSubmodule p π.ker)
      + Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 1)
    = Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G (ZMod p)) 2)
      + Module.finrank (ZMod p) (groupCohomology (Rep.trivial (ZMod p) G' (ZMod p)) 1) := by
  -- abbreviations for the five numbers
  set e := Module.finrank (ZMod p) (LinearMap.range (inflMap p π)) with he
  set K := Module.finrank (ZMod p) (LinearMap.ker (inflMap p π)) with hK
  set r := Module.finrank (ZMod p) (LinearMap.range (beta (p := p) π)) with hr
  set c := Module.finrank (ZMod p) (invCharSubmodule p π.ker) with hc
  set a := Module.finrank (ZMod p) (H1 p G) with ha
  set b := Module.finrank (ZMod p) (H1 p G') with hb
  set d := Module.finrank (ZMod p) (H2 p G) with hd
  -- the kernel of `beta` is the range of the injective inflation `alpha`
  have hkerα : Module.finrank (ZMod p) (LinearMap.ker (beta (p := p) π))
      = Module.finrank (ZMod p) (Additive G →+ ZMod p) := by
    rw [ker_beta_eq_range_alpha (p := p) π hπ]
    exact LinearMap.finrank_range_of_inj (alpha_injective (p := p) π hπ)
  have h1 : b = r + a := by
    rw [← finrank_H1_eq (p := p) G'] at hβ
    rw [hkerα, ← finrank_H1_eq (p := p) G] at hβ
    omega
  have h2 : c = K + r := by
    rw [range_transgression_eq_ker_infl p π hπ,
      ker_transgression_eq_range_beta p π hπ] at htg
    omega
  have h3 : d = e + K := by
    omega
  change e + c + a = d + b
  omega

end

end Work.CFTLib
