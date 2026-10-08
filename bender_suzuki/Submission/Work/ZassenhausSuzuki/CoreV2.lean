import Submission.Work.ZassenhausSuzuki.Core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Area `ZassenhausSuzuki`: the corrected decomposition of the Suzuki core

`SuzukiCoreProp` (Recognition.lean) is split along the lines of the lead's design note
`NOTES_LEAD_probe1630.md` (probe 16:30, 2026-10-03):

* `SuzukiDataProp0` — the **structure of `Q`**: `Q ≅ A(GF(2ᵐ), θ)` with `θ ≠ 1` of odd order,
  the two-point stabiliser acting through the standard torus `Λ`.  No Tits condition and no
  oddness of `m` here: `A(n,θ)` is a Suzuki 2-group for *every* `θ ≠ 1` of odd order, so these
  cannot be forced by `Q` and the torus action.  Route (leaf by leaf in the note):
  `twoPoint_inverted` (Suzuki Prop. 3), `twoPoint_cyclic`, `Q_suzuki_sq` (with `|Q| = q²` as
  a named literature input, BG 4.6/5.6), Higman (`szA_of_isSuzukiTwoGroup`), Suzuki's
  Lemma 6 (`SuzukiLemma6Prop`) and `mem_torus_of_conj`.
* `SuzukiTitsProp` — the `t`-dependent part (BG 5.16–5.21 / Suzuki §4–5): `m` is odd and `θ`
  **or** `θ⁻¹` is a Tits endomorphism.  (Higman fixes `θ` only up to `θ ↔ θ⁻¹`: for `Sz(8)`,
  `θ = x⁴` is Tits but `θ⁻¹ = x²` — equivalently `x²` — is not.)
* `SzASymmProp` (L5 of the note) — the isomorphism `A(K,θ) ≅ A(K,θ⁻¹)`, `(a,b) ↦ (θa, b+aθa)`,
  intertwining `h_λ` with `h_{θλ}`.
* `SuzukiFProp` (Core.lean, unchanged) — the computation of `f = τ` in the coordinates of the
  data.

`suzukiCoreProp_of0` assembles the three into `SuzukiCoreProp`; in the `θ⁻¹` case `e` is
transported along `SzASymmProp`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

namespace Work.ZassenhausSuzuki

/-- **The structure half of the Suzuki core, corrected.**  A simple split rank-one Zassenhaus
configuration with non-abelian 2-group `Q` admits a parametrisation of `Q` by Higman's group
`A(GF(2ᵐ), θ)` (`θ ≠ 1` of odd order, `m ≥ 3`) under which the two-point stabiliser acts
through the standard torus `Λ`. -/
def SuzukiDataProp0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ (H Q : Subgroup G) (t : G), IsSplitRankOne H Q t → IsZassenhaus H →
      IsPGroup 2 Q → ¬ IsAbelianSubgroup Q →
      ∃ (m : ℕ) (_ : 3 ≤ m) (θ : GaloisField 2 m ≃+* GaloisField 2 m),
        θ ≠ 1 ∧ Odd (orderOf θ) ∧ ∃ e : Q ≃* SzA (GaloisField 2 m) θ,
          ∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
            ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
              e y = SzA.hLam θ (lam : GaloisField 2 m) (e x)

/-- **L5 (`szA_symm_equiv`) of the lead's note.**  Higman's classification fixes the field
automorphism only up to `θ ↔ θ⁻¹`: `A(K,θ) ≅ A(K,θ⁻¹)` through `(a,b) ↦ (θ a, b + a·θ a)`,
and this map carries `h_λ` to `h_{θλ}`. -/
def SzASymmProp : Prop :=
  ∀ (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m),
    ∃ φ : SzA (GaloisField 2 m) θ ≃* SzA (GaloisField 2 m) θ.symm,
      ∀ (lam : GaloisField 2 m) (x : SzA (GaloisField 2 m) θ),
        φ (SzA.hLam θ lam x) = SzA.hLam θ.symm (θ lam) (φ x)

/-- **The Tits half of the Suzuki core** (BG 5.16–5.21 / Suzuki §4–5): in the coordinates of
`SuzukiDataProp0`, `m` is odd and `θ` or `θ⁻¹` is a Tits endomorphism. -/
def SuzukiTitsProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
    ∀ (H Q : Subgroup G) (t : G), IsSplitRankOne H Q t → IsZassenhaus H →
      ∀ (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m), θ ≠ 1 → Odd (orderOf θ) →
        ∀ e : Q ≃* SzA (GaloisField 2 m) θ,
          (∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
            ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
              e y = SzA.hLam θ (lam : GaloisField 2 m) (e x)) →
          Odd m ∧ (IsTitsTheta θ ∨ IsTitsTheta θ.symm)

/-- **Assembly.**  `SuzukiDataProp0` + `SzASymmProp` + `SuzukiTitsProp` + `SuzukiFProp` give
`SuzukiCoreProp`. -/
theorem suzukiCoreProp_of0 (hSymm : SzASymmProp) (hD : SuzukiDataProp0) (hT : SuzukiTitsProp)
    (hF : SuzukiFProp) : SuzukiCoreProp := by
  intro G hGrp hFin hsimple H Q t hsplit hzass h2grp hnab
  letI := hGrp
  letI := hFin
  obtain ⟨m, hm3, θ, hθ1, hθodd, e, htorus⟩ := hD G hsimple H Q t hsplit hzass h2grp hnab
  obtain ⟨hmodd, hTits | hTits⟩ := hT G hsimple H Q t hsplit hzass m θ hθ1 hθodd e htorus
  · exact ⟨m, hmodd, hm3, θ, hTits,
      ⟨{ split := hsplit, zassenhaus := hzass, nonabelian := hnab, e := e,
         frel := hF G hsimple H Q t hsplit hzass m θ hTits e htorus }⟩⟩
  · obtain ⟨φ, hφ⟩ := hSymm m θ
    refine ⟨m, hmodd, hm3, θ.symm, hTits,
      ⟨{ split := hsplit, zassenhaus := hzass, nonabelian := hnab, e := e.trans φ, frel := ?_ }⟩⟩
    have htorus' : ∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          (e.trans φ) y = SzA.hLam θ.symm (lam : GaloisField 2 m) ((e.trans φ) x) := by
      intro d hd
      obtain ⟨lam, hlam⟩ := htorus d hd
      refine ⟨Units.map θ.toMonoidHom lam, ?_⟩
      intro x
      obtain ⟨y, hy, hye⟩ := hlam x
      refine ⟨y, hy, ?_⟩
      have hcoe : ((Units.map θ.toMonoidHom lam : (GaloisField 2 m)ˣ) : GaloisField 2 m)
          = θ (lam : GaloisField 2 m) := rfl
      rw [hcoe]
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hye, hφ]
    exact hF G hsimple H Q t hsplit hzass m θ.symm hTits (e.trans φ) htorus'

end Work.ZassenhausSuzuki
