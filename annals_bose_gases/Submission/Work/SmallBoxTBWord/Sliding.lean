import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxTBWord.abs_chiB_le_chiSup_sq
import Submission.Work.SmallBoxTBWord.contDiff_chiB
import Submission.Work.SmallBoxTBWord.gapCoeff_absorbs
import Submission.Work.SmallBoxTBWord.hasCompactSupport_chiB
import Submission.Work.SmallBoxTBWord.hcmp_of_tBword
import Submission.Work.SmallBoxTBWord.isCompact_dlBox
import Submission.Work.SmallBoxTBWord.tBwordKin_le_kinWord_cnPlus
import Submission.Work.SmallBoxTBWord.tBword_gap_absorbs
import Submission.Work.SmallBoxTBWord.tsupport_chiB_subset_acube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sliding-level `𝒯_B` object and the consumer-shaped assembly

`tBwordB N ℓ d ε c u Φ` (`Defs.lean`) is FS `eq:appTB`'s
`𝒯_B = ½ε_T(1+π⁻²)⁻¹(dℓ)⁻²Q_B + Q_Bχ_B[√−Δ−(dsℓ)⁻¹]₊²χ_BQ_B` at the sliding
box `B(u) = dlBox ℓ d u`, the window `χ_B = chiB ℓ d u`, the box side `dℓ`
and the ambient big box `abox N ℓ`.

This module records the two structural properties at the sliding level
(instantiated from the general theorems) and the *consumer-shaped*
assembly:

* `tBwordB_ge_gapPart` — property (a): the plain `Q_B`-gap part;
* `sliding_sum_bound_of_tBword` — the sliding-sum bound in the exact shape
  of `SmallBoxSliding.sliding_sum_identity_of_telescope`, obtained from
  `Sliding.hcmp_of_tBword` plus that theorem.  Its three mathematical inputs
  are the per-box bound `hbox` (SmallBoxA0/`SmallBoxDLBound`), the potential
  `u`-integral `hpot` (`lem:LocPotential`), and the **named residual** `hbs`
  (FS `eq:HBU`/`eq:appTB` = BS Thm 3.10, see `NOTES.md`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxTBWord

open Submission.BoseGases
open _root_.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **Property (a) at the sliding level**: the `Q_B`-gap part of `𝒯_B` is a
lower bound for the per-`u` word. -/
theorem tBwordB_ge_gapPart {N : ℕ} {ℓ d ε c : ℝ} (u : ℝ³) (Φ : X N → ℝ)
    (hℓ : 0 ≤ ℓ) :
    tbGapCoeff (ℓ * d) ε * cnPlusBoxB N ℓ d u Φ
      ≤ tBwordB N ℓ d ε c u Φ := by
  unfold tBwordB cnPlusBoxB
  exact tBword_ge_gapPart (A := dlBox ℓ d u) (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    (χ := chiB ℓ d u) hℓ

/-- **Property (a), FS `eq:appgapestimate`, at the sliding level**: in the FS
regime `2(1+π⁻²)(dℓ·C'·√(μ·a))² ≤ ε_T` the whole excited penalty at a
chemical potential `μ` and coupling `a` is absorbed by the gap part of
`𝒯_B`. -/
theorem tBwordB_gap_absorbs {N : ℕ} {ℓ d ε c μ av C' : ℝ} (u : ℝ³)
    (Φ : X N → ℝ) (hℓ : 0 < ℓ) (hav : 0 ≤ av) (hμ : 0 ≤ μ) (hC' : 0 ≤ C')
    (hd : 0 < d) (hε : 0 < ε) (hreg : 2 * (1 + (Real.pi ^ 2)⁻¹) * ((ℓ * d) * C' * Real.sqrt (μ * av)) ^ 2 ≤ ε) :
    C' ^ 2 * μ * av * cnPlusBoxB N ℓ d u Φ ≤ tBwordB N ℓ d ε c u Φ := by
  have hs : 0 < ℓ * d := mul_pos hℓ hd
  have ha : 0 ≤ ℓ := le_of_lt hℓ
  exact tBword_gap_absorbs (A := dlBox ℓ d u)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) (χ := chiB ℓ d u)
    ha (gapCoeff_absorbs hav hμ hC' hε hs hreg)

/-- **The consumer-shaped assembly** (deliverable item 2): the sliding-sum
inequality in the exact shape taken by
`Work.SmallBoxSliding.sliding_sum_identity_of_telescope`, derived from

* `hbox` — the per-box bound `eBf u ≤ tBwordB u + qLHSwordB u`
  (thm:smallbox / `SmallBoxDLBound`, with the `𝒯_B` kinetic in place of the
  plain box kinetic);
* `hpot` — the `u`-integral of the localised potential (`lem:LocPotential`);
* `hbs` — the **named residual** `(b/2ℓ²)cnPlus + ∫_u tBwordB u ≤ kinWord`
  (FS `eq:HBU`/`eq:appTB`, i.e. Bratteli–Solovej Thm 3.10; the one analytic
  input the sliding chapter cannot supply — see `NOTES.md` §4). -/
theorem sliding_sum_bound_of_tBword {N : ℕ} {ℓ d μ b C B : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {M : ℕ}
    {Φ : X N → ℝ} (eBf : ℝ³ → ℝ) (Wr ε c : ℝ)
    (hC : 0 ≤ C)
    (hintf : Integrable eBf)
    (hintmass : Integrable (fun u : ℝ³ => Work.SmallBoxSliding.chiMass M ℓ d u))
    (htelescope : (∫ u : ℝ³, eBf u) = Wr)
    (hbox : ∀ u : ℝ³, eBf u ≤ tBwordB N ℓ d ε c u Φ +
      Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ)
    (hbs : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
      (∫ u : ℝ³, tBwordB N ℓ d ε c u Φ) ≤ kinWord N ℓ Φ)
    (hpot : (∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ) ≤
      qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hintt : Integrable (fun u : ℝ³ => tBwordB N ℓ d ε c u Φ))
    (hintq : Integrable (fun u : ℝ³ => Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ))
    (hlow : ∀ u : ℝ³, - C * Work.SmallBoxSliding.chiMass M ℓ d u ≤ eBf u)
    (hmass : (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ, Work.SmallBoxSliding.chiMass M ℓ d u) ≤ B) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + (∫ u in Work.SmallBoxSliding.goodSet ℓ d μ, eBf u) - C * B
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  have hcmp : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ + Wr
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
    rw [← htelescope]
    exact hcmp_of_tBword (h := h) (eBf := eBf) (eps := ε) (c := c)
      hbox hbs hpot hintf hintt hintq
  exact Work.SmallBoxSliding.sliding_sum_identity_of_telescope (h := h) eBf Wr hC
    hintf hintmass htelescope hcmp hlow hmass

/-- The **canonical per-`u` box energy** of the sliding chapter with the `𝒯_B`
kinetic in place of the plain box kinetic:
`eBf(u) = 𝒯_B(u) + (localised potential word)`. -/
noncomputable def eBfTb {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ ε c : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  tBwordB N ℓ d ε c u Φ + Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ

/-- **The consumer-shaped assembly at the canonical per-`u` box energy**:
`F` in the exact shape of `Work.SmallBoxSliding.sliding_sum_identity_of_telescope`
with `eBf := eBfTb`, so the only mathematical inputs left are the potential
`u`-integral (`hpot`), the per-box lower bound (`hlow`) and the **named
residual** `hbs` (FS `eq:HBU`/`eq:appTB` = BS Thm 3.10). -/
theorem sliding_sum_bound_of_tBword_canonical {N : ℕ} {ℓ d μ b C B : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {M : ℕ}
    {Φ : X N → ℝ} (ε c : ℝ) (hC : 0 ≤ C)
    (hintmass : Integrable (fun u : ℝ³ => Work.SmallBoxSliding.chiMass M ℓ d u))
    (hbs : (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
      (∫ u : ℝ³, tBwordB N ℓ d ε c u Φ) ≤ kinWord N ℓ Φ)
    (hpot : (∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ) ≤
      qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hintt : Integrable (fun u : ℝ³ => tBwordB N ℓ d ε c u Φ))
    (hintq : Integrable (fun u : ℝ³ => Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ))
    (hlow : ∀ u : ℝ³, - C * Work.SmallBoxSliding.chiMass M ℓ d u ≤
      eBfTb (h := h) M ℓ d μ ε c u Φ)
    (hmass : (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
      Work.SmallBoxSliding.chiMass M ℓ d u) ≤ B) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
        (∫ u in Work.SmallBoxSliding.goodSet ℓ d μ, eBfTb (h := h) M ℓ d μ ε c u Φ) - C * B
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ := by
  refine sliding_sum_bound_of_tBword (h := h) (M := M) (Φ := Φ)
    (eBf := fun u => eBfTb (h := h) M ℓ d μ ε c u Φ) (Wr := ∫ u : ℝ³, eBfTb (h := h) M ℓ d μ ε c u Φ)
    (ε := ε) (c := c) hC ?_ hintmass rfl ?_ hbs hpot hintt hintq hlow hmass
  · exact hintt.add hintq
  · intro u
    exact le_refl _

/-- **Property (b) at the sliding level, window error absorbed**: the spectral
half of the sliding `𝒯_B` is dominated by `2·chiSup⁴·kinWord` plus `2B` times
the box excited count, where `B` bounds `Σ_k(∂_kχ_B)²` pointwise (the FS shape in
which the window error is absorbed into the `n₊`-gap). -/
theorem tBwordKinB_le_cnPlus {n : ℕ} {ℓ d c B : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hc : 0 ≤ c)
    (hB0 : 0 ≤ B) (u : ℝ³)
    (hB : ∀ x : ℝ³, (∑ k : Fin 3, (fderiv ℝ (chiB ℓ d u) x (kcStdBasis k)) ^ 2) ≤ B)
    {Ψ : X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ) :
    tBwordKinB (n + 1) ℓ d c u Ψ
      ≤ 2 * chiSup ^ 4 * kinWord (n + 1) ℓ Ψ + 2 * B * cnPlusBoxB (n + 1) ℓ d u Ψ := by
  have h := tBwordKin_le_kinWord_cnPlus (a := ℓ) (A := dlBox ℓ d u)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u) (χ := chiB ℓ d u) (Cχ := chiSup ^ 2)
    (B := B) (c := c) hℓ hc (sq_nonneg chiSup) hB0
    (contDiff_chiB hℓ hd u) (hasCompactSupport_chiB hℓ hd u)
    (tsupport_chiB_subset_acube hℓ hd u) (isCompact_dlBox hℓ hd u)
    (fun x => abs_chiB_le_chiSup_sq u x) hB hΨ
  have h' : 2 * (chiSup ^ 2) ^ 2 = 2 * chiSup ^ 4 := by ring
  simpa [tBwordKinB, cnPlusBoxB, h'] using h

alias sliding_sum_identity_of_tBword := sliding_sum_bound_of_tBword

/-- **The residual of the chapter, named.**  FS `eq:HBU` + `eq:appTB` read as
the sliding localisation inequality

    `(b/2ℓ²)·cnPlus ℓ Φ + ∫_u 𝒯_B(B(u)) du ≤ kinWord N ℓ Φ` ,

i.e. Bratteli–Solovej Thm 3.10 / FS `lem:LocKinEn` with the small-box family
`B(u) = dlBox ℓ d u` and the renormalised box kinetic `tBwordB`.  This is the
single analytic input of the sliding chapter that the corpus cannot yet
supply; `NOTES.md` §4 records why it is not a word-level consequence of
`tBwordKin_le_kinWord` (the per-`u` domination) and what operator-layer
infrastructure would discharge it. -/
def tBLocalisation (N : ℕ) (ℓ d b ε c : ℝ) (Φ : X N → ℝ) : Prop :=
  (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
      (∫ u : ℝ³, tBwordB N ℓ d ε c u Φ) ≤ kinWord N ℓ Φ

/-- **The consumer-shaped assembly with the named residual**: the same theorem
as `sliding_sum_bound_of_tBword`, with `hbs` read as `tBLocalisation`. -/
theorem sliding_sum_bound_of_tBLocalisation {N : ℕ} {ℓ d μ b C B : ℝ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {M : ℕ}
    {Φ : X N → ℝ} (eBf : ℝ³ → ℝ) (Wr ε c : ℝ)
    (hC : 0 ≤ C)
    (hintf : Integrable eBf)
    (hintmass : Integrable (fun u : ℝ³ => Work.SmallBoxSliding.chiMass M ℓ d u))
    (htelescope : (∫ u : ℝ³, eBf u) = Wr)
    (hbox : ∀ u : ℝ³, eBf u ≤ tBwordB N ℓ d ε c u Φ +
      Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ)
    (hbs : tBLocalisation N ℓ d b ε c Φ)
    (hpot : (∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ) ≤
      qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ)
    (hintt : Integrable (fun u : ℝ³ => tBwordB N ℓ d ε c u Φ))
    (hintq : Integrable (fun u : ℝ³ => Work.SmallBoxSliding.qLHSwordB h M ℓ d μ u Φ))
    (hlow : ∀ u : ℝ³, - C * Work.SmallBoxSliding.chiMass M ℓ d u ≤ eBf u)
    (hmass : (∫ u in (Work.SmallBoxSliding.goodSet ℓ d μ)ᶜ,
      Work.SmallBoxSliding.chiMass M ℓ d u) ≤ B) :
    (b / (2 * ℓ ^ 2)) * cnPlus ℓ Φ +
        (∫ u in Work.SmallBoxSliding.goodSet ℓ d μ, eBf u) - C * B
      ≤ kinWord N ℓ Φ + qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ :=
  sliding_sum_bound_of_tBword (h := h) (M := M) (Φ := Φ) eBf Wr (ε := ε) (c := c)
    hC hintf hintmass htelescope hbox hbs hpot hintt hintq hlow hmass

end Work.SmallBoxTBWord
