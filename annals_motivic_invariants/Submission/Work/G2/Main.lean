import Submission.Work.G2.LayerC
import Submission.Work.G2.stronglyBirational_of_exDiv_eq_singletons
import Submission.Work.G2.nonempty_iso_baseChangeZ_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.G2.Main` — the `G₂`-Grassmannian geometric datum of the CY3 L-link

Single entry point of the **`G₂`-area** of `annals_motivic_invariants`: one import,
`import Submission.Work.G2.Main`, brings in

* `Work.G2.G2ZModel` (`Submission/Work/G2/LayerA.lean`) — the `ℤ`-model of Layer 1 of `thm:CY3`:
  the split simply connected simple group scheme `G` of type `G₂` over `ℤ` with its Borel `B`, its
  two maximal parabolics `P`, `P'`, the quotients `G/B`, `G/P`, `G/P'`, the two projections and the
  ample bundle `L = p*M ⊗ p'*M'` (Milne Thm 13.33, SGA3 Cor. XXII.5.8.5, Raynaud Prop. VII.1.5,
  IMOUG2, RamRam Thm 3);
* `Work.G2.CY3ZModel` (`Submission/Work/G2/LayerB.lean`) — the `ℤ`-model of Layer 2: the general
  section `σ` of `L`, the zero loci `X = Z(σ) ⊂ G/B`, `Z = Z(p_*σ) ⊂ G/P`, `Z' = Z(p'_*σ) ⊂ G/P'`,
  the two blow-ups `τ`, `τ'` (Danilov Thm 2 + Grothendieck–Lefschetz) and the birational map
  `ψ = τ' ∘ τ⁻¹` with its two exceptional divisors;
* `Work.G2.G2ZModel.stronglyRational_P`, `Work.G2.G2ZModel.stronglyRational_P'` — the paper's
  `lem:GP-strongly-rational`: the two `G₂`-Grassmannians are *strongly rational*, derived from the
  Bruhat chart clauses by `Work.G2.isStronglyRational_of_exDiv_eq_singletons`;
* `Work.G2.CY3DatumZ` (`Submission/Work/G2/LayerC.lean`) — the `ℤ`-model of Layer 3: the
  `K`-triviality and Picard-rank-one facts about the centres, the two cubic self-intersections
  `c₁(M|_Z)³ = 14`, `c₁(M'|_{Z'})³ = 42` (IMOUG2), the `ℙ¹`-bundle bridge and the two transports to
  `𝔸⁵` with vanishing coefficient at the base point.

## The main results

* **the construction of `thm:CY3`, base-change-uniformly in the field**:

  ```lean
  Work.G2.CY3DatumZ.toCY3Data  (M : CY3DatumZ) (𝕜) [Field 𝕜] [Infinite 𝕜] : CY3Data 𝕜
  Work.G2.CY3DatumZ.toCY3Input (M : CY3DatumZ) (𝕜) [Field 𝕜] [Infinite 𝕜]
      (C : CubicInput 𝕜) : CY3Input 𝕜
  ```

  i.e. the geometric datum of the `G₂`-Grassmannian L-link over **every** infinite field `𝕜`, from a
  single `ℤ`-model — this is the paper's "the construction extends to an arbitrary infinite field";
* **`notIso` is proved, not assumed**: `Work.G2.CY3DatumZ.notIso` shows that the two centres are not
  isomorphic over `𝕜`, from the two cubic self-intersections `14` and `42` of the model and the
  named input `Work.G2.CubicInput` (the cubic self-intersection is an isomorphism invariant), via
  the arithmetic `14 ≠ 42` (`Work.G2.fourteen_ne_fortyTwo`);
* **the challenge-level statements** (from the model, the cubic input, Totaro's input and the
  stabilisation input of the CY3 chapter):

  ```lean
  Work.G2.not_gen_of_G2_infiniteField_five : [Field 𝕜] [Infinite 𝕜] → CY3DatumZ →
      CubicInput 𝕜 → Work.CY3.TotaroInput 𝕜 → ¬ GenByPseudoRegularizable 𝕜 5
  Work.G2.not_gen_of_G2_infiniteField      : 5 ≤ n → … → Work.CY3.CY3Stabilisation 𝕜 n →
      ¬ GenByPseudoRegularizable 𝕜 n
  ```

* **the base-change layer** (`Submission.Work.G2.Defs`, `Submission.Work.G2.BaseChangeAPI`):
  `Work.G2.baseChangeZ`, `Work.G2.baseChangeZMap`, `Work.G2.instVarietyZ`
  (the base change of a geometrically integral `Spec ℤ`-scheme with separated / locally of finite
  type / quasicompact structure morphism is a `𝕜`-variety — *proved*),
  `Work.G2.baseChangeZMap_isOver`, `Work.G2.smooth_baseChangeZMap` (base change preserves
  smoothness), `Work.G2.baseChangeZMap_id`, `Work.G2.baseChangeZMap_comp` (functoriality),
  `Work.G2.isClosedImmersion_baseChangeZMap`, `Work.G2.isoOver_baseChangeZ` — all *proved*.

## What is *not* here

The `G₂` group scheme itself, its root data, the Borels and the parabolics, the quotients, `Pic`,
the ample bundle `L` and its very ampleness, Bertini, blow-ups, intersection numbers: Mathlib has
none of these, so each is a named input of the `ℤ`-model (with its citation in the docstring of the
field).  See `Submission/Work/G2/NOTES.md` for the complete list, the exact residual set, and the
roadmap.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.G2

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- **The geometric datum of the `G₂`-Grassmannian L-link exists over every infinite field**: the
construction of `thm:CY3`, from the `ℤ`-model and the isomorphism-invariance of the cubic
self-intersection. -/
theorem exists_CY3Input [Infinite 𝕜] (M : CY3DatumZ) (C : CubicInput 𝕜)
    (hZ : C.cubic (baseChangeZ 𝕜 M.ZZ) = 14) (hZ' : C.cubic (baseChangeZ 𝕜 M.ZZ') = 42) :
    Nonempty (Work.CY3.CY3Input 𝕜) :=
  ⟨M.toCY3Input 𝕜 C hZ hZ'⟩

/-- **`thm:CY3` of Lin–Shinder**: over every infinite field there exists a *motivically
non-trivial* smooth projective L-link whose two ends are the five-dimensional `G₂`-Grassmannians
`G_𝕜/P_𝕜`, `G_𝕜/P'_𝕜` and whose two centres `Z_𝕜`, `Z'_𝕜` are `K`-trivial threefolds of Picard
rank one.

In the vocabulary of the CY3 chapter this is a term `Work.CY3.CY3Link 𝕜` whose invariant
coefficient is `≠ 0`: the link is `M.toCY3Link 𝕜 C T` (the model's datum plus the non-isomorphism
of the centres, proved from `14 ≠ 42`, plus Totaro's input), and its coefficient is exactly `1`
(`Work.G2.CY3DatumZ.inv_eq_one`). -/
theorem thm_CY3 [Infinite 𝕜] (M : CY3DatumZ) (C : CubicInput 𝕜)
    (hZ : C.cubic (baseChangeZ 𝕜 M.ZZ) = 14) (hZ' : C.cubic (baseChangeZ 𝕜 M.ZZ') = 42)
    (T : Work.CY3.TotaroInputAt 𝕜 (Work.G2.baseChangeZ 𝕜 M.ZZ) (Work.G2.baseChangeZ 𝕜 M.ZZ')) :
    ∃ L : Work.CY3.CY3Link 𝕜, L.inv ≠ 0 :=
  ⟨M.toCY3Link 𝕜 C hZ hZ' T, Work.CY3.CY3Link.inv_ne_zero _⟩

/-- **The `Cr 𝕜 5`-coefficient of the transported CY3 link does not vanish**, directly from the
`ℤ`-model: this is the existential consumed by `Work.Motivic.not_gen_of_cInv_ne_zero` and hence the
`n = 5` case of Theorem 1.2 (3) of the challenge. -/
theorem exists_cInv_ne_zero [Infinite 𝕜] (M : CY3DatumZ) (C : CubicInput 𝕜)
    (hZ : C.cubic (baseChangeZ 𝕜 M.ZZ) = 14) (hZ' : C.cubic (baseChangeZ 𝕜 M.ZZ') = 42)
    (T : Work.CY3.TotaroInputAt 𝕜 (Work.G2.baseChangeZ 𝕜 M.ZZ) (Work.G2.baseChangeZ 𝕜 M.ZZ')) :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Work.CY3.Affine 𝕜 5).BirationalMap (Work.CY3.Affine 𝕜 5)) ≠ 0 :=
  Work.CY3.exists_cInv_ne_zero_infiniteField 𝕜 (M.toCY3Input 𝕜 C hZ hZ') T

end

end Work.G2
