import ChallengeDeps
import Submission.Work.BoseFixB1.Core.oneBody_assembly
import Submission.Work.BoseFixB1.kineticHalf_of_oneBody
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1.sbPot_integral_le_potWordU
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.slidingB_holds` — FS `eq:BSsliding2` (Bratteli–Solovej Thm 3.10)

The target `Work.BoseFixB1.SlidingB v h` is FS `final_v2.tex` `eq:BSsliding2` at FS's own
parameters, in the frozen vocabulary of `Submission/Work/BoseFixB1/Defs.lean`:

    `(b/(2ℓ²))·cnPlus ℓ Φ + (1/C)·∫_u sbWord h μ u Φ ≤ wordB v h μ n Φ`

with `sbWord = sbKin + sbPot`, `sbKin = Work.UBBInputs8.tBwordBInd` (FS `eq:appTB` with FS's
box indicator `Q_{B(u)} = 1_{B(u)} − P_{B(u)}`), `sbPot = qLHSwordB` (FS `eq:HBU`'s localised
potential), and the cutoffs `c_sb = (dsℓ)⁻¹` (sliding) and `(2sℓ)⁻¹`, `(2dsℓ)⁻¹` (anchored, FS
`eq:T'u`).  FS cite it ("It was proved in [BS] Theorem 3.10 that …"); the corpus records it as
the a-priori chapter's one open analytic input (`SmallBoxTBWord/NOTES.md` §4,
`OneBodyTwoCut/README.md` §5).

## What this file does

It **reduces** `SlidingB` to its two halves and proves the reduction, so that the analytic
content is isolated in two named residuals:

* **`KineticHalf v h`** — FS `eq:BSsliding2`'s *kinetic* content at FS's parameters: the
  sliding kinetic gap plus the `u`-integral of the small-box kinetic words is dominated by the
  *anchored* large-box kinetic word `kinFormB` (FS `eq:DefT`'s `𝒯_{u=0}`, i.e. the Neumann
  resolvent, the large-box gap, the large-momentum term and the two-cutoff main term).
  This is Bratteli–Solovej Thm 3.10 / FS `lem:LocKinEn` at the two scales; it is the open core
  (the corpus's `Work.BoseFixB1.kineticSplit`).
* **`PotentialHalf v h`** — FS `lem:LocPotential` at FS's parameters: the `u`-integral of the
  localised potential word is the potential part of `wordB`, i.e.
  `∫_u sbPot ≤ ∫_{Λ}Φ²·potWordU`.  This is a *telescoping identity* (the corpus's
  `Work.UBBInputs8.A.qLHSwordB_integral_u_box` at the box-restricted integrability, plus the
  pointwise kernel identities `wLoc ℓ h 0 = wPairC ℓ h = wPair ℓ h` and the permutation
  symmetry of the two-body kernel, which uses `IsRadial v` — without it the identity is
  *false*, see `Work.BoseFixB2.DvApriori.potWordU_form_eq_qLHSword`).

Both halves carry, besides their inequality, the *`u`-marginal integrability* of their word
(the Bochner integral `∫_u` is otherwise Mathlib's junk value `0`, and the additivity
`∫_u(sbKin + sbPot) = ∫_u sbKin + ∫_u sbPot` is not available without it).  This is a real
requirement: the *joint* `(u,x)`-integrability is provably false for arbitrary states
(`Work.UBBInputs7.Finding.not_integrable_qLHSBIntegrand_const`), so only the *marginal*
integrability can be used here — and it is provable (compact support in `u`, smooth `Φ`).

`slidingB_of_pieces` is the reduction; `slidingB_holds` is the target, wired to the two
residuals.

## The constant `C` is forced to be `1`

At the constant one-particle state `Φ ≡ 1` (an admissible `BoxState`), `cnPlus = 0`,
`sbKin = 0` (`Work.UBBInputs8.A.tBwordBInd_const_zero`), and the two halves give
`∫_u sbWord = ∫_u sbPot = (the potential part of wordB) = −μ·8π(a v)ℓ³ < 0`
(FS `eq:DefU`; the corpus's `wordB_const_one_eq`).  Hence `SlidingB`'s inequality at that state
reads `(1/C)·(−X) ≤ −X` with `X > 0`, i.e. `C ≤ 1`; with `1 ≤ C` this forces `C = 1`.  So no
proof with a multiplicative slack can exist and the reduction below may (and must) be run at
`C = 1`.

## The bump's opacity does not block the statement

The workspace's cut-off `χ` is `Classical.choice`-selected (`chiBase x =
(someContDiffBumpBase ℝ³).toFun 2 (4•x)`), so no *numerical* bound on its gradient energy
`winGradOne = ∫|∇χ|²` is provable beyond `winGradOne ≥ 6` (`Work.OneBodyPay.winGradOne_ge_six`);
this is why `Work.BoseKinLoc.Kinetic.gradient_moment_bound` is not provable as stated.  It does
*not* block `SlidingB`: the existential `ε₀` may be taken as a **function of the bump's data**,
e.g. `ε₀ := (1 + winGradOne) ^ (-(400 : ℕ))`, and FS's smallness `eq:BSlidingassp`
(`s·√winGradOne ≤ 1`, the corpus's `Work.OneBodyTwoCut.TwoCutCriterionSharp` at FS's
parameters) is then elementary real analysis in `s = (μa³)^{1/323}`, with no explicit numerical
bound on `winGradOne` needed.  (This is the constant-level caveat flagged in
`OneBodyTwoCut/README.md` §5, resolved for the *frozen* parameters.)
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The kinetic half of FS `eq:BSsliding2`** at FS's parameters: the sliding kinetic gap plus
the `u`-integral of the small-box kinetic words is dominated by the anchored large-box kinetic
word, together with the `u`-marginal integrability of the sliding word. -/
def KineticHalf (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      Integrable (fun u : ℝ³ => sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ)) ∧
      ((paramsAt μ (a v)).b / (2 * sideAt μ (a v) ^ 2)) * cnPlus (sideAt μ (a v)) (Φ : X n → ℝ)
          + (∫ u : ℝ³, sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ))
        ≤ Work.BoseKinLoc.kinFormB n (sideAt μ (a v)) (paramsAt μ (a v)).d
            (paramsAt μ (a v)).s (paramsAt μ (a v)).eT (paramsAt μ (a v)).b (Φ : X n → ℝ)

/-- **The potential half of FS `eq:BSsliding2`** at FS's parameters (FS `lem:LocPotential`):
the `u`-integral of the localised potential word is at most the potential part of `wordB`,
together with the `u`-marginal integrability of the localised potential word. -/
def PotentialHalf (v : ℝ³ → ℝ) (h : ScatSol v) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Adm v ε₀ μ →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
      Integrable (fun u : ℝ³ => sbPot h μ u (Φ : X n → ℝ)) ∧
      (∫ u : ℝ³, sbPot h μ u (Φ : X n → ℝ))
        ≤ ∫ x in abox n (sideAt μ (a v)),
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (g0 v h) (sideAt μ (a v)) μ 0 x

/-- **The reduction**: the two halves of FS `eq:BSsliding2` give `SlidingB`, with the constant
`C = 1` (which is forced — see the module docstring).  The proof is the elementary bookkeeping
`wordB = kinFormB + (potential part)`, `sbWord = sbKin + sbPot` and
`∫_u(sbKin + sbPot) = ∫_u sbKin + ∫_u sbPot` (which is where the two marginal integrability
fields are used). -/
theorem slidingB_of_pieces {v : ℝ³ → ℝ} {h : ScatSol v}
    (hKin : KineticHalf v h) (hPot : PotentialHalf v h) : SlidingB v h := by
  obtain ⟨εK, hεK, hK⟩ := hKin
  obtain ⟨εP, hεP, hP⟩ := hPot
  refine ⟨min εK (min εP 1), 1, le_refl 1, lt_min hεK (lt_min hεP one_pos), ?_⟩
  intro μ hAdm n Φ
  obtain ⟨hμ, hdil, hPOK⟩ := hAdm
  have hAdmK : Adm v εK μ := ⟨hμ, le_trans hdil (min_le_left _ _), hPOK⟩
  have hAdmP : Adm v εP μ :=
    ⟨hμ, le_trans hdil (le_trans (min_le_right _ _) (min_le_left _ _)), hPOK⟩
  obtain ⟨hKinInt, hKinIneq⟩ := hK μ hAdmK n Φ
  obtain ⟨hPotInt, hPotIneq⟩ := hP μ hAdmP n Φ
  -- `sbWord = sbKin + sbPot`, pointwise
  have hword : (fun u : ℝ³ => sbWord h μ u (Φ : X n → ℝ))
      = fun u : ℝ³ => sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ)
          + sbPot h μ u (Φ : X n → ℝ) := by
    funext u; rfl
  -- the additive split of the `u`-integral
  have hsplit : (∫ u : ℝ³, sbWord h μ u (Φ : X n → ℝ))
      = (∫ u : ℝ³, sbKin (v := v) μ (paramsAt μ (a v)).M u (Φ : X n → ℝ))
        + ∫ u : ℝ³, sbPot h μ u (Φ : X n → ℝ) := by
    rw [hword, MeasureTheory.integral_add hKinInt hPotInt]
  -- `wordB` is `kinFormB` plus the potential part
  have hbox : wordB v h μ n (Φ : X n → ℝ)
      = Work.BoseKinLoc.kinFormB n (sideAt μ (a v)) (paramsAt μ (a v)).d
            (paramsAt μ (a v)).s (paramsAt μ (a v)).eT (paramsAt μ (a v)).b (Φ : X n → ℝ)
        + ∫ x in abox n (sideAt μ (a v)),
            (Φ x) ^ 2 * Work.BoseKinLoc.potWordU n v (g0 v h) (sideAt μ (a v)) μ 0 x := rfl
  rw [hbox, hsplit]
  norm_num
  linarith [hKinIneq, hPotIneq]

/-- **The potential half of FS `eq:BSsliding2` is a theorem.**  FS `lem:LocPotential` at FS's
parameters, with its `u`-marginal integrability conjunct: assembled from the delegated
`Work.BoseFixB1.sbPot_integral_le_potWordU` (the box-restricted telescoping
`Work.UBBInputs8.A.qLHSwordB_integral_u_box` at the real small-box parameter, the pointwise
kernel identities `wLoc ℓ h 0 = wPairC ℓ h = wPair ℓ h`, the permutation symmetry of the
two-body kernel — which uses `IsRadial v` — and the marginal integrability), with the smallness
threshold supplied by `Work.BoseFixB1.regime_sideAt_ge`. -/
theorem potentialHalf_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : PotentialHalf v h := by
  obtain ⟨εR, hεR, hreg⟩ := regime_sideAt_ge hav hR
  refine ⟨min εR 1, lt_min hεR one_pos, ?_⟩
  intro μ hAdm n Φ
  obtain ⟨hμ, hdil, hPOK⟩ := hAdm
  have hadm' : Adm v (min εR 1) μ := ⟨hμ, hdil, hPOK⟩
  have hregμ := hreg μ hμ (le_trans hdil (min_le_left _ _))
  have hM : 1 ≤ (paramsAt μ (a v)).M := by
    rw [paramsAt_eq_fsParams]
    norm_num [Work.BoseBox.fsParams, Work.BoseBox.mValue]
  exact Work.BoseFixB1.sbPot_integral_le_potWordU (h := h) hv1 hvrad hR hv_supp hav
    (adm_ell_pos hadm') (adm_d_pos hadm') hM hregμ.1 hregμ.2 Φ

/-- **The reduction of the target to the kinetic half alone**: the potential half is a theorem
(`potentialHalf_holds`), so `SlidingB` follows from `KineticHalf v h` — FS `eq:BSsliding2`'s
kinetic content (Bratteli–Solovej Thm 3.10 / FS `lem:LocKinEn` at the two scales) together with
the `u`-marginal integrability of the sliding kinetic word. -/
theorem slidingB_of_kineticHalf {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hKin : KineticHalf v h) : SlidingB v h :=
  slidingB_of_pieces hKin (potentialHalf_holds h hv1 hvrad hR hv_supp hav)

/-- **FS `eq:BSsliding2`** (Bratteli–Solovej Thm 3.10) at FS's parameters, with the FS-faithful
small-box word `sbKin = Work.UBBInputs8.tBwordBInd` — the a-priori chapter's target.

By `slidingB_of_kineticHalf` the only remaining input is `KineticHalf v h`, which is supplied by
`kineticHalf_of_oneBody` (the `N`-body ⟸ `N = 1` slot reduction) together with the proved `N = 1`
inequality `Work.BoseFixB1.oneBodyKineticHalf_core` (`Core/oneBody_assembly.lean`) and the
`u`-marginal integrability `Work.BoseFixB1.integrable_sbKin_marginal`
(`sbWord_marginal_integrable.lean`). -/
theorem slidingB_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) : Work.BoseFixB1.SlidingB v h :=
  slidingB_of_kineticHalf hv1 hvrad hR hv_supp hav
    (kineticHalf_of_oneBody h (oneBodyKineticHalf_core h)
      ⟨1, one_pos, fun μ hAdm n Φ =>
        integrable_sbKin_marginal (adm_ell_pos hAdm) (adm_d_pos hAdm) Φ⟩)

end Work.BoseFixB1
