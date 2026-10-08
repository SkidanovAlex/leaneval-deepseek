import Submission.Work.ZassenhausSuzuki.CoreV2
import Submission.Work.ZassenhausSuzuki.szA_symm_equiv
import Submission.Work.ZassenhausSuzuki.suzukiFProp

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausSuzuki`: the corrected `f`-half of the Suzuki core

`SuzukiFProp` (`Core.lean`) is **false**: its hypothesis on the coordinatisation `e` is only
that the two-point stabiliser acts through the torus `Λ = h(Kˣ)`, and that hypothesis is
invariant under the twist `e ↦ h_μ ∘ e` (Λ is abelian) while the conclusion `f = τ` is not,
since `σ ∘ h_μ = h_{μ⁻¹} ∘ σ`.  The unconditional refutation is
`Work.ZassenhausSuzuki.not_suzukiFProp` (`suzukiFProp.lean`), which uses the literal model
`Sz(8) = SzModel 1` to exhibit two admissible coordinatisations demanding two different values
of the book's map `f`.

The correct statement — and the one the recognition step actually consumes, exactly as in
`IsSuzukiConfiguration` (`Prelim.lean`), where `e` and the `f`-formula are *bundled* — records
that a good coordinatisation can be *chosen*:

* `SuzukiCoordsProp`: given an admissible `e`, there is another admissible `e'` in which
  `f = τ`;
* `suzukiCoreProp_of_coords`: `SuzukiDataProp0` + `SuzukiTitsProp` + `SuzukiCoordsProp` give
  `SuzukiCoreProp` (the `θ ↔ θ⁻¹` case uses the proved `szA_symm_equiv`, and `hF` is applied a
  second time with `θ.symm`, whose Tits-ness is exactly what `SuzukiTitsProp` provides).

The Suzuki computation (`NOTES_SzFrel.md`, BG 5.16–5.21) is the statement that this good
coordinatisation exists; mathematically it is the same theorem as before, with the twist
ambiguity absorbed into the existential quantifier.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.ZassenhausSuzuki

/-- **The `f`-half of the Suzuki core, corrected.**  If `e` coordinatises `Q` by `A(K,θ)` with
`D = twoPoint H t` acting through the torus `Λ` (in the `e`-coordinates), then there is a
coordinatisation `e'` with the same property in which the book's map `f` is the Suzuki map `τ`.

(The universal form with `e' = e` is false — see `not_suzukiFProp` in `suzukiFProp.lean`: the
admissible coordinatisations form a `Λ`-torsor on which `τ` transforms by `h_{μ⁻²}`.) -/
def SuzukiCoordsProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ (H Q : Subgroup G) (t : G), IsSplitRankOne H Q t → IsZassenhaus H →
      ∀ (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m), IsTitsTheta θ →
        ∀ e : Q ≃* SzA (GaloisField 2 m) θ, TorusCoords (GaloisField 2 m) θ H Q t e →
          ∃ e' : Q ≃* SzA (GaloisField 2 m) θ, TorusCoords (GaloisField 2 m) θ H Q t e' ∧
            ∀ x : Q, x ≠ 1 → FRel H t (x : G) (((e'.symm (SzA.sigma θ (e' x)) : Q) : G))

/-- **The Suzuki core, from the structure half, the Tits half and the corrected `f` half.** -/
theorem suzukiCoreProp_of_coords (hD : SuzukiDataProp0) (hT : SuzukiTitsProp)
    (hC : SuzukiCoordsProp) : SuzukiCoreProp := by
  intro G hGrp hFin hsimple H Q t hsplit hzass h2grp hnab
  letI := hGrp
  letI := hFin
  obtain ⟨m, hm3, θ, hθ1, hθodd, e, htorus⟩ := hD G hsimple H Q t hsplit hzass h2grp hnab
  obtain ⟨hmodd, hTits | hTits⟩ := hT G hsimple H Q t hsplit hzass m θ hθ1 hθodd e htorus
  · obtain ⟨e', _, hfrel⟩ := hC G hsimple H Q t hsplit hzass m θ hTits e htorus
    exact ⟨m, hmodd, hm3, θ, hTits,
      ⟨{ split := hsplit, zassenhaus := hzass, nonabelian := hnab, e := e',
         frel := hfrel }⟩⟩
  · obtain ⟨φ, hφ⟩ := szA_symm_equiv θ
    have htorus' : TorusCoords (GaloisField 2 m) θ.symm H Q t (e.trans φ) := by
      intro d hd
      obtain ⟨lam, hlam⟩ := htorus d hd
      refine ⟨Units.map θ.toMonoidHom lam, ?_⟩
      intro x
      obtain ⟨y, hy, hye⟩ := hlam x
      refine ⟨y, hy, ?_⟩
      have hcoe : ((Units.map θ.toMonoidHom lam : (GaloisField 2 m)ˣ) : GaloisField 2 m)
          = θ (lam : GaloisField 2 m) := rfl
      rw [hcoe, MulEquiv.trans_apply, MulEquiv.trans_apply, hye, hφ]
    obtain ⟨e', _, hfrel⟩ := hC G hsimple H Q t hsplit hzass m θ.symm hTits (e.trans φ) htorus'
    exact ⟨m, hmodd, hm3, θ.symm, hTits,
      ⟨{ split := hsplit, zassenhaus := hzass, nonabelian := hnab, e := e',
         frel := hfrel }⟩⟩

end Work.ZassenhausSuzuki
