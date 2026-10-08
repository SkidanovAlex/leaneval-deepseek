import Mathlib
import Submission.Work.Higman.clo_hard_defs
import Submission.Work.Higman.H8.pairing_foundations
import Submission.Work.Higman.h8_squaring_polar
import Submission.Work.Higman.bracket_expansion
import Submission.Work.Higman.squaring_layer
import Submission.Work.Higman.clo_sM_aux
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.h8_comm_calc
import Submission.Work.Higman.h8_bracket
import Submission.Work.Higman.clo_pair_props
import Submission.Work.Higman.clo_sM_props
import Submission.Work.Higman.CommAux.clo_betaV_props_v2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman

/-- **The polar identity and the two pairings of the hard case of Higman's Lemma 8.**  In the
situation of `CloH8Data`, the power map `cloSM : C/A → Ω₁(P)` is quadratic with polar form the
commutator pairing `cloBPair`, which is biadditive, alternating, `ξ`-equivariant and non-trivial;
the bracket `cloBetaV : C/A × Ω₁(P) → Ω₁(P)` is biadditive, `ξ`-equivariant, non-trivial and
satisfies `cloBetaV x (cloSM x) = 1`.

Route.  `h8_squaring_polar` gives the polar identity on representatives,
`(u v) ^ 2 ^ e = u ^ 2 ^ e * v ^ 2 ^ e * ⁅v,u⁆ ^ 2 ^ (e-1)`; `cloBPair` is defined through the
chosen representatives `cloRepC`, which differ from `u`, `v` by elements of `A`; the effect of that
on the commutator lies in `A² = ⁅A,C⁆`, and `A²` has exponent `2 ^ (e-1)`, so the `2 ^ (e-1)`-st
powers agree.  Biadditivity of `cloBPair` follows from `h8_comm_calc` (the commutator is additive
modulo `A²` in each variable), alternation from `⁅u⁻¹,u⁆ = 1`, and non-triviality from `A ⊄ A²`.
The clauses for `cloBetaV` use `cloRepC_mul_inv_mem`, `cloLiftA_spec`, `A²` of exponent `2 ^ (e-1)`,
`h8_bracket` (biadditivity modulo `A⁴`, and `⁅u, a b⁆ = ⁅u,a⁆ ⁅u,b⁆` exactly), `A⁴` of exponent
`2 ^ (e-2)`, and `cloBetaV x (cloSM x) = 1` from `⁅u,u²⁆ = 1`. -/
theorem h8_pairing_props {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) {A C : Subgroup P}
    [A.Normal] (S : CloH8Data h A C) :
    (∀ x y : ↥C ⧸ (A.subgroupOf C),
        cloSM S (x * y) = cloSM S x * cloSM S y * cloBPair S x y) ∧
      (∀ x y z : ↥C ⧸ (A.subgroupOf C),
        cloBPair S (x * y) z = cloBPair S x z * cloBPair S y z) ∧
      (∀ x y z : ↥C ⧸ (A.subgroupOf C),
        cloBPair S x (y * z) = cloBPair S x y * cloBPair S x z) ∧
      (∀ x : ↥C ⧸ (A.subgroupOf C), cloBPair S x x = 1) ∧
      (∀ x y : ↥C ⧸ (A.subgroupOf C),
        cloXiOm h (cloBPair S x y) =
          cloBPair S (cloXiQuot h S.hA.map_eq S.hCinv x)
            (cloXiQuot h S.hA.map_eq S.hCinv y)) ∧
      (∃ x y : ↥C ⧸ (A.subgroupOf C), cloBPair S x y ≠ 1) ∧
      (∀ x x' : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(omega1 P),
        cloBetaV S (x * x') w = cloBetaV S x w * cloBetaV S x' w) ∧
      (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w w' : ↥(omega1 P),
        cloBetaV S x (w * w') = cloBetaV S x w * cloBetaV S x w') ∧
      (∀ x : ↥C ⧸ (A.subgroupOf C), ∀ w : ↥(omega1 P),
        cloXiOm h (cloBetaV S x w) =
          cloBetaV S (cloXiQuot h S.hA.map_eq S.hCinv x) (cloXiOm h w)) ∧
      (∀ x : ↥C ⧸ (A.subgroupOf C), cloBetaV S x (cloSM S x) = 1) ∧
      (∃ x : ↥C ⧸ (A.subgroupOf C), ∃ w : ↥(omega1 P), cloBetaV S x w ≠ 1) := by
  -- The polar identity is the last conjunct of `clo_sM_props`.
  obtain ⟨-, -, -, -, hpolar⟩ := clo_sM_props (h := h) S
  -- Biadditivity, alternation, `ξ`-equivariance and non-triviality of `cloBPair`.
  obtain ⟨-, hBL, hBR, hBD, hBX, hBN⟩ := clo_pair_props (h := h) S
  -- Biadditivity, `ξ`-equivariance, the relator and non-triviality of `cloBetaV`.
  obtain ⟨-, hβL, hβR, hβX, hβrel, hβN⟩ := CommAux.clo_betaV_props_v2 (h := h) S
  exact ⟨hpolar, hBL, hBR, hBD, hBX, hBN, hβL, hβR, hβX, hβrel, hβN⟩

end Work.Higman
