/-
  WilC4/Route : the lead's C4 route (2026-10-10), from
  `sources/wilkiesC4route/wilkies_C4_route.lean` (design: `wilkies_C4_route.md`, review:
  `wilkies_C4_route_REVIEW.md`).

  ULPM (uniform log-piecewise-monomiality, H1) ⟹ Gap lemma (H3) ⟹ PreparationStep (H4, via
  Steinitz exchange) ⟹ `ValIneq` (this area's `valIneq_of_preparation`, already proved).

  The vocabulary `SameSide`, `ModelULPM`, `GapLemma` lives in `WilC4/ULPMDefs.lean` (same
  namespace), so that the lemmas about them can be proved in sibling files without seeing the
  statements recorded here.  Siblings (namespace `Work.WilC4`, wired in as they land, see
  `NOTES.md` §8): `realULPM` (H1, research, still open), `transferOfULPM` (H2),
  `gapLemma_of_ULPM` (H3), `preparationStep_of_gap` (H4), `pb_poly_bound`, `pb_exponent_rational`
  (the R-side tools of H1).

  DEPENDENCY NOTE (for the final wiring).  `WilC2.dcl_exchange`, used by H4, takes
  `hC0 : ∀ n X, (∅ : Set ℝ).Definable LRc X → RExpExist X` and `hUF : UnifFiniteRExp`.  The
  sibling `preparationStep_of_gap` therefore carries both as explicit hypotheses: `hC0` is
  discharged by the proved `WilkiesDesign.CG.C0_rexp_syntax_proved hR`, and `hUF` is either the
  frozen `E0b_unif_finite` or a proved version (in `WilE10` it is proved modulo `E7`; see
  `NOTES.md` §8 for a possible route to `hUF` from `hOM` alone).
-/
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC0.Main
import Submission.Work.WilC4.Assembly
import Submission.Work.WilC4.realULPM
import Submission.Work.WilC4.pb_poly_bound
import Submission.Work.WilC4.pb_decay
import Submission.Work.WilC4.transferOfULPM
import Submission.Work.WilC4.gapLemma_of_ULPM
import Submission.Work.WilC4.pb_exponent_rational
import Submission.Work.WilC4.unifFinite_of_omin
import Submission.Work.WilC4.preparationStep_of_gap

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4.Route
open WilkiesDesign WilkiesDesign.CG FirstOrder FirstOrder.Language Work.WilC4

/-- R-tool 1 (from `hPB` + `C0_rexp_syntax`): a `∅`-definable function on `ℝ` is polynomially
bounded at `+∞` (used to kill every "superpolynomial diagonal" `Φ(B) ≥ B^B`). -/
theorem pb_poly_bound
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ) (hPB : PolyBoundedRExp)
    {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable LRc Y)
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y') :
    ∃ n : ℕ, ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → |y| ≤ x ^ n :=
  Work.WilC4.pb_poly_bound hR hPB hY hfun

/-- R-tool 3 (decay variant of `hPB`): a `∅`-definable function of `B` that tends to `0` at `+∞`
decays at least like a negative rational power.  Needed for P5 of H1. -/
theorem pb_decay
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ) (hPB : PolyBoundedRExp)
    {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable LRc Y)
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → y < ε) :
    ∃ (η : ℚ) (β : ℝ), 0 < η ∧ 0 < β ∧
      ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y → y ≤ β * x ^ (-(η : ℝ)) :=
  Work.WilC4.pb_decay hR hPB hY hfun hdec

/-- R-tool 2 (from `hPB` + `C0_rexp_syntax`): if a `∅`-definable function with unbounded domain is
`≍ x^σ` (fixed constant `C`) near `+∞`, then `σ` is rational. -/
theorem pb_exponent_rational
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ) (hPB : PolyBoundedRExp)
    {Y : Set (Fin 2 → ℝ)} (hY : (∅ : Set ℝ).Definable LRc Y)
    (hfun : ∀ x y y' : ℝ, ![x, y] ∈ Y → ![x, y'] ∈ Y → y = y')
    (hdom : ∀ R : ℝ, ∃ x y : ℝ, R ≤ x ∧ ![x, y] ∈ Y) (σ C : ℝ) (hC : 1 ≤ C)
    (hσ : ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → ![x, y] ∈ Y →
      C⁻¹ * x ^ σ ≤ |y| ∧ |y| ≤ C * x ^ σ) : ∃ q : ℚ, σ = q :=
  Work.WilC4.pb_exponent_rational hR hPB hY hfun hdom σ C hC hσ

/-- H1 (RESEARCH, ℝ-side): ULPM holds in `ℝ` ("PB-diagonal" proof, see route doc §4). -/
theorem realULPM
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hOM : OMinModels) (hPB : PolyBoundedRExp) : ModelULPM ℝ :=
  Work.WilC4.realULPM hR hOM hPB

/-- H2 (mechanical, clone of `transferOfPB`): ULPM transfers from `ℝ` to every model of `TR`. -/
theorem transferOfULPM (h : ModelULPM ℝ) :
    ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
      [rexpL.Structure M] [(constantsOn ℝ).Structure M], M ⊨ TR → ModelULPM M :=
  Work.WilC4.transferOfULPM h

/-- H3 (mechanical): ULPM in `M` gives the gap lemma (breakpoints of `T`-instances lie in `T`;
pick `x₁ := 2N·b⁻ ∈ T` on the same side as `a`; `α := F(c, x₁)·x₁^{-q}`). -/
theorem gapLemma_of_ULPM {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hM : M ⊨ TR) (hU : ModelULPM M) : GapLemma M :=
  Work.WilC4.gapLemma_of_ULPM hM hU

/-- H4 (mechanical): gap lemma + exchange (`WilC2.dcl_exchange`, with `C0_rexp_syntax hR` and
`E0b_unif_finite`) + divisibility of `Γ T` give the preparation step. -/
theorem preparationStep_of_gap
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable LRc X → RExpExist X)
    (hUF : UnifFiniteRExp)
    (hG : ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
      [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M],
      M ⊨ TR → GapLemma M) : PreparationStep :=
  Work.WilC4.preparationStep_of_gap hR hC0 hUF hG

/-- **Assembly (proved from H1–H4, `C0` and `hUF`).**  `hUF` is the statement of the frozen
`E0b_unif_finite` (the final wiring passes it in); `hC0` is discharged inside by the proved
`C0_rexp_syntax_proved`. -/
theorem C4_valuation_inequality_route
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hOM : OMinModels) (hPB : PolyBoundedRExp) : ValIneq :=
  valIneq_of_preparation (preparationStep_of_gap hR
    (fun n X hX => WilkiesDesign.CG.C0_rexp_syntax_proved hR X hX)
    (Work.WilC4.unifFinite_of_omin hOM)
    (fun M _ _ _ _ _ _ hM => gapLemma_of_ULPM hM (transferOfULPM (realULPM hR hOM hPB) M hM)))

end Work.WilC4.Route
