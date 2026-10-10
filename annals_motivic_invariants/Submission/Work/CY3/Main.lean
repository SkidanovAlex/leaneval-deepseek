import Submission.Work.CY3.Totaro
import Submission.Work.CY3.Invariance
import Submission.Work.CY3.StronglyRational
import Submission.Work.CY3.projectiveLine_birational_affineLine
import Submission.Work.CY3.isP1Fibration_projectiveSpaceToSpec_one
import Submission.Work.CY3.resEquiv_genericPoint_birationalMap
import Submission.Work.CY3.Bridge
import Submission.Work.Motivic.not_gen_of_cInv_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Main` — the `n ≥ 5` case of Theorem 1.2 (3): packaging and stabilisation

Single entry point of the CY3 area of `annals_motivic_invariants`:
`import Submission.Work.CY3.Main` brings in everything — the vocabulary, the `G₂`-Grassmannian
infrastructure (Layer 1), the general-section/blow-up data (Layer 2), the L-link and its invariant
coefficient `1`, the named inputs (Bertini, Danilov, Grothendieck–Lefschetz, Totaro), and the two
target statements.

## The main results

* `Work.CY3.exists_cInv_ne_zero_infiniteField` — **the `n = 5` shape** of Theorem 1.2 (3) of the
  challenge: for every infinite field `𝕜`, given the named inputs, there is a Cremona
  transformation `φ` of `𝔸⁵` over `𝕜` whose `[κ(Z)(t)]`-coefficient does not vanish;
* `Work.CY3.not_gen_of_CY3_infiniteField_five` — the same, wired to `GenByPseudoRegularizable 𝕜 5`;
* `Work.CY3.not_gen_of_CY3_infiniteField` — the same for `n ≥ 5`, from the (named) stabilisation
  of the link, i.e. the paper's `c(φ × id_W)` step of the proof of `thm:bir-generation` (c) and its
  Corollary `cor-CYnSB`;
* `Work.CY3.CY3Data.exists_cInv_ne_zero` (`Submission/Work/CY3/Totaro.lean`) — the primitive form,
  with the geometric datum and the non-isomorphism of the two centres as separate hypotheses;
* `Work.CY3.CY3Link.inv_eq_one`, `…inv_ne_zero` — the computation of the invariant coefficient of
  the CY3 L-link, transported to `𝔸⁵` (`Cr 𝕜 5`);
* `Work.CY3.CY3Data.bridge_of_models` (`Submission/Work/CY3/Bridge.lean`) — the `ℙ¹`-bundle
  description of the two exceptional divisors (the paper's geometry) *implies* the bridge, so a
  producer may supply the geometry rather than the abstract implication;
* the vocabulary of *strong birationality* (`Work.CY3.StronglyBirational`, with the equivalence
  relation laws and (L2) in the paper's exact form `Work.CY3.cInv_symm_trans_eq`), of *strong
  rationality* (`Work.CY3.IsStronglyRational`, `Submission/Work/CY3/StronglyRational.lean`) and of
  `ℙ¹`-fibrations (`Work.CY3.IsP1Fibration`), together with the invariance of these notions under
  isomorphism over `𝕜` (`Submission/Work/CY3/Invariance.lean`,
  `Submission/Work/CY3/isoOver_stronglyBirational.lean`) and the `ℙ¹`–`𝔸¹` birationality
  (`Submission/Work/CY3/projectiveLine_birational_affineLine.lean`).

## The named inputs

Two, exactly as in the paper's `thm:CY3`:

| input | module | paper |
|---|---|---|
| `Work.CY3.CY3Input` | this file | Layers 1–3 of the construction: the `G₂` datum (`Work.CY3.G2Grassmannian`), the general section and the blow-up structure (`Work.CY3.CY3Section`), the two `K`-trivial threefolds of Picard rank one and the `ℙ¹`-bundle bridge (`Work.CY3.CY3Data`), and the non-isomorphism of the two centres (paper `lem-nSBG2`, from `c₁(M|_Z)³ = 14 ≠ 42 = c₁(M'|_{Z'})³`) |
| `Work.CY3.TotaroInput` | `Submission/Work/CY3/Totaro.lean` | `thm:BurtCY`, `cor-CYnSB` |
| `Work.CY3.CY3Stabilisation` | this file | the stabilisation `c(φ × id_W) ≠ 0`, `W = 𝔸^{n-5}` separably rationally connected |

The *existence* of a `CY3Input` over an infinite field is the content of `thm:CY3`'s construction
(Ito–Miura–Okawa–Ueda in characteristic zero, extended by the paper to an arbitrary infinite field
by the `ℤ`-models of Layer 1 plus Bertini at the infinite field) and is the part that no library can
currently supply; everything between that input and the two target statements is proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Named input: the construction of `thm:CY3`.**  Over an infinite field `𝕜` there is a CY3
datum (Layers 1–3 above) whose two centres `Z`, `Z'` are not isomorphic over `𝕜`.

Layers 1 and 2 are the paper's construction: the split `G₂` over `ℤ` with its Borel and two maximal
parabolics, the quotients `G/B`, `G/P`, `G/P'`, the ample generators `M`, `M'`, the very ample
`L = p*M ⊗ p'*M'`, the general section `σ` (Bertini; this is the only step using `Infinite 𝕜`) and
its zero loci `X`, `Z`, `Z'`, the blow-ups `τ`, `τ'` and the birational map `ψ = τ' ∘ τ⁻¹`.  The
field `notIso` is `lem-nSBG2`'s first half: the two cubic self-intersections `c₁(M|_Z)³ = 14` and
`c₁(M'|_{Z'})³ = 42` are distinct (Ito–Miura–Okawa–Ueda) and invariant under the base change that
computes `Z_𝕜`, `Z'_𝕜`, so `Z_𝕜 ≄ Z'_𝕜`.

This structure is the complete list of geometric facts assumed by the CY3 area; every result below
is proved from it and from Totaro's theorem. -/
structure CY3Input (𝕜 : Type) [Field 𝕜] where
  /-- the geometric datum of the link (Layers 1–3) -/
  data : CY3Data 𝕜
  /-- **`lem-nSBG2`** (`IMOUG2`: `c₁(M|_Z)³ = 14 ≠ 42 = c₁(M'|_{Z'})³`): the two centres are not
  isomorphic over `𝕜`. -/
  notIso : ¬ IsoOver 𝕜 data.Z data.Z'

/-- **The two centres are not stably birational** (paper `lem-nSBG2` + Totaro's `cor-CYnSB`), in
the bundled form of the input: the geometric form of the non-triviality of the link. -/
theorem CY3Input.not_stablyBirational (𝕜 : Type) [Field 𝕜] (I : CY3Input 𝕜)
    (T : TotaroInputAt 𝕜 I.data.Z I.data.Z') :
    ¬ StablyBirational 𝕜 I.data.Z I.data.Z' :=
  CY3Data.not_stablyBirational I.data T I.notIso

/-- **The `n = 5` shape of Theorem 1.2 (3) of the challenge.**

For every infinite field `𝕜`, from the named input of `thm:CY3` and Totaro's theorem, there is a
Cremona transformation `φ` of `𝔸⁵` over `𝕜` whose `[κ(Z)(t)]`-coefficient does not vanish.  The
existential is written in the exact shape of the hypothesis of
`Work.Motivic.not_gen_of_cInv_ne_zero`, so the wiring to `-GenByPseudoRegularizable` is one line.

The transported map is `φ = ε ∘ ψ ∘ δ`, where `ε : 𝔸⁵ ⤏ G/P` and `δ : G/P' ⤏ 𝔸⁵` are the affine
transports provided by the strong rationality of the two `G₂`-Grassmannians (paper
`lem:GP-strongly-rational`); their coefficients vanish, so `c(φ) = c(ψ)` (proved, not assumed). -/
theorem exists_cInv_ne_zero_infiniteField (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (I : CY3Input 𝕜)
    (T : TotaroInputAt 𝕜 I.data.Z I.data.Z') :
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Affine 𝕜 5).BirationalMap (Affine 𝕜 5)) ≠ 0 :=
  CY3Data.exists_cInv_ne_zero I.data T I.notIso

/-- **Theorem 1.2 (3) of the challenge at `n = 5`**: over every infinite field, `Cr₅(𝕜)` is not
generated by pseudo-regularizable elements, from the named inputs. -/
theorem not_gen_of_CY3_infiniteField_five (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] (I : CY3Input 𝕜)
    (T : TotaroInputAt 𝕜 I.data.Z I.data.Z') : ¬ GenByPseudoRegularizable 𝕜 5 :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 5 (exists_cInv_ne_zero_infiniteField 𝕜 I T)

/-! ## Stabilisation to `n ≥ 5` -/

/-- **Named input: the stabilisation of the CY3 link to `Cr 𝕜 n`, `n ≥ 5`.**

The paper's proof of `thm:bir-generation` (c) stabilises the `ℙ⁵`-link to `ℙ⁵ × W`
(`W = 𝔸^{n-5}`, separably rationally connected): one uses

`c(φ × id_W) = [Z × ℙ¹ × W] − [Z' × ℙ¹ × W]`,

whose `[κ(Z)(t)(W)]`-coefficient is again `1` by Corollary `cor-CYnSB`
(`Z × ℙ¹ × W` is not birational to `Z' × ℙ¹ × W` because `Z`, `Z'` are not stably birational).
Formally this is the passage from the `Cr 𝕜 5`-coefficient to the `Cr 𝕜 n`-coefficient of
`φ × id` — a statement about the exceptional divisors of a product map
(`exDiv (φ × id_W) = {x × η_W : x ∈ exDiv φ}`), which we record as a named input, exactly as in
the K3 area (`Work.K3.K3Stabilisation`). -/
structure CY3Stabilisation (𝕜 : Type) [Field 𝕜] (n : ℕ) : Prop where
  /-- a non-vanishing coefficient in `Cr 𝕜 5` yields one in `Cr 𝕜 n` -/
  stabilise : (∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 5),
      cInv 𝕜 z₀ (φ : (Affine 𝕜 5).BirationalMap (Affine 𝕜 5)) ≠ 0) →
    ∃ (Z : Scheme.{0}) (_ : Z.Over (Spec (.of 𝕜))) (z₀ : Z) (φ : Cr 𝕜 n),
      cInv 𝕜 z₀ (φ : 𝔸(Fin n; Spec (.of 𝕜)).BirationalMap
        (𝔸(Fin n; Spec (.of 𝕜)))) ≠ 0

/-- **Theorem 1.2 (3) of the challenge for `n ≥ 5`**, from the `n = 5` statement and the
stabilisation input. -/
theorem not_gen_of_CY3_infiniteField {n : ℕ} (_hn : 5 ≤ n) (𝕜 : Type) [Field 𝕜] [Infinite 𝕜]
    (I : CY3Input 𝕜) (T : TotaroInputAt 𝕜 I.data.Z I.data.Z') (S : CY3Stabilisation 𝕜 n) :
    ¬ GenByPseudoRegularizable 𝕜 n :=
  Work.Motivic.not_gen_of_cInv_ne_zero 𝕜 n
    (S.stabilise (exists_cInv_ne_zero_infiniteField 𝕜 I T))

end

end Work.CY3
