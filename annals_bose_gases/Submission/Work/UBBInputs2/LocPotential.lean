import ChallengeDeps
import Submission.Work.UBBInputs2.Canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs2.LocPotential` — the potential-localisation residual and the
`hpot` discharge

FS `lem:LocPotential` is the *identity*

    −μ Σ_i ∫ g(x_i−y)dy + Σ_{i<j} v(x_i−x_j)
      = ∫_u [ −μ Σ_i ∫ w_{1,u}(x_i,y)dy + Σ_{i<j} w_u(x_i,x_j) ] du

("a straightforward computation similar to Proposition 3.1 in [BS]").  In the
corpus this identity is **DELIVERED in its two halves**
(`Work.SmallBoxSliding.qLHSwordB_integral_u`):

    ∫_u qLHSwordB h M ℓ d μ u Φ du = qLHSwordChi h M ℓ d μ Φ ,

where the *reference* word `qLHSwordChi` is the corpus `qLHSword` at the
unrenormalised kernels `χ_M(·/ℓ)·v(·−·)·χ_M(·/ℓ)` (and likewise for `g₀`).

So the content of FS `lem:LocPotential` at the corpus's kernels is exactly the
*comparison of two explicit words*

    `LocPotentialCorpus` :  qLHSwordChi h M ℓ d μ Φ ≤ qLHSword ℓ μ (wPairC ℓ v)
                              (wPairC ℓ (g0 v h)) Φ ,

i.e. that the `χ_M²`-weighted localised kernel word is below the corpus
(chosen-kernel) word.  This module names that comparison and proves that it,
together with the DELIVERED integral identity, is *exactly* the `hpot` field of
`BoxSumBoundCanon` (`boxSumBoundCanon_of_kernel`) — so the field is split into
one delivered identity plus one explicit word comparison, with nothing else.

The integrability side of the delivered identity (the joint integrand in
`(u,x)`) is carried as a hypothesis of the reduction; it holds for the corpus
states (globally smooth `Φ` with `tsupport Φ ⊆ interior(box N L)`, hence
compactly supported, against kernels that are themselves compactly supported in
`(u,x)`) and is therefore pure bookkeeping — see `README.md`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs2

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open _root_.BoseGases
open Submission.BoseGases
open Work.UBB
open Work.UBBInputs

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **FS `lem:LocPotential` at the corpus's kernels** — the `χ_M`-localised
reference potential word is below the corpus per-box potential word. -/
def LocPotentialCorpus (v : ℝ³ → ℝ) (h : ScatSol v) (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
    Work.SmallBoxSliding.qLHSwordChi (N := N) h M L d (dens N L) (Φ : X N → ℝ)
      ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
          (Φ : X N → ℝ)

/-- **`BoxSumBoundCanon` with the `hpot` field removed** — the residual bundle
whose only potential-side input is `LocPotentialCorpus` (the word comparison),
the delivered integral identity being supplied by the reduction below. -/
def BoxSumBoundKernel (v : ℝ³ → ℝ) (h : ScatSol v) (b K_B R' J ε₀ : ℝ)
    (d M : ℕ) : Prop :=
  ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, dens N L * (a v) ^ 3 ≤ ε₀ → ∀ Φ : CSBox N L,
    sqNormN N L (Φ : X N → ℝ) = 1 →
    WordDens N L (dens N L) v h (Φ : X N → ℝ) ≤ Theta (a v) J (dens N L) →
    ∃ (ε c C B : ℝ),
      0 ≤ C ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)) ∧
      Integrable (fun u : ℝ³ => Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u
        (Φ : X N → ℝ)) ∧
      (∀ u : ℝ³, - C * Work.SmallBoxSliding.chiMass M L d u
        ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
          + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)) ∧
      ((∫ u in (Work.SmallBoxSliding.goodSet L d (dens N L))ᶜ,
          Work.SmallBoxSliding.chiMass M L d u) ≤ B) ∧
      (R' - 4 * π * (dens N L) ^ 2 * (a v) * L ^ 3
          * (1 + K_B ^ 3 * (dens N L * (a v) ^ 3) ^ (1 / 2 : ℝ)) + C * B
        ≤ ∫ u in Work.SmallBoxSliding.goodSet L d (dens N L),
            (Work.SmallBoxTBWord.tBwordB N L d ε c u (Φ : X N → ℝ)
              + Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ)))

/-- **The `hpot` field of `BoxSumBoundCanon`, as a THEOREM (no word comparison).**

After the repoint the DELIVERED telescoping `Work.SmallBoxSliding.qLHSwordB_integral_u` is an
*equality*: `∫_u qLHSwordB h M L d μ u Φ = qLHSword L μ (wPairC L v) (wPairC L (g₀ v h)) Φ`.
Hence the `hpot` field (`∫_u qLHSwordB u ≤ qLHSword`) holds with no comparison at all — the
`χ_M`-reference-word comparison `LocPotentialCorpus` (rounds 7/8) is not used and in fact false
(`Work.UBBInputs10.not_locPotentialCorpus`). -/
theorem hpot_of_regime {v : ℝ³ → ℝ} {h : ScatSol v} {d M : ℕ}
    {R0 : ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0 : 0 < R0)
    (hM : 1 ≤ M) (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * d) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0)
    {L : ℝ} (hL : 1 ≤ L) {N : ℕ} {Φ : CSBox N L}
    (hint : Integrable (fun p : ℝ³ × X N =>
      Work.SmallBoxSliding.qLHSBIntegrand h M L d (dens N L) (Φ : X N → ℝ) p.1 p.2))
    (hintRef : IntegrableOn
      (Work.SmallBoxSliding.qLHSChiIntegrand h M L d (dens N L) (Φ : X N → ℝ))
      (abox N L)) :
    (∫ u : ℝ³, Work.SmallBoxSliding.qLHSwordB h M L d (dens N L) u (Φ : X N → ℝ))
      ≤ qLHSword (N := N) L (dens N L) (wPairC L v) (wPairC L (g0 v h))
          (Φ : X N → ℝ) := by
  have hid := Work.SmallBoxSliding.qLHSwordB_integral_u (v := v) hv_supp hR0 h
    (M := M) hM (ℓ := L) (d := (d : ℝ)) (lt_of_lt_of_le one_pos hL)
    (by exact_mod_cast (Nat.pos_of_ne_zero (by
      intro h0; rw [h0] at hdR; linarith [hdR 1 le_rfl])))
    (hdR L hL) (hdRχ L hL) (Φ := (Φ : X N → ℝ)) hint hintRef
  rw [hid]

/-- **`BoxSumBoundCanon` from `BoxSumBoundKernel`**: the only extra input is
the `hpot` field, which `hpot_of_locPotentialCorpus` supplies from
`LocPotentialCorpus` and the delivered integral identity. -/
theorem boxSumBoundCanon_of_kernel {v : ℝ³ → ℝ} {h : ScatSol v}
    {b K_B R' J ε₀ : ℝ} {d M : ℕ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R0) (hR0 : 0 < R0) (hM : 1 ≤ M)
    (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * d) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * chiR0)
    (hint : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      Integrable (fun p : ℝ³ × X N =>
        Work.SmallBoxSliding.qLHSBIntegrand h M L d (dens N L) (Φ : X N → ℝ) p.1 p.2))
    (hintRef : ∀ (L : ℝ), 1 ≤ L → ∀ N : ℕ, ∀ Φ : CSBox N L,
      IntegrableOn (Work.SmallBoxSliding.qLHSChiIntegrand h M L d (dens N L)
        (Φ : X N → ℝ)) (abox N L))
    (hK : BoxSumBoundKernel v h b K_B R' J ε₀ d M) :
    BoxSumBoundCanon v h b K_B R' J ε₀ d M := by
  intro L hL N hN Φ hnorm hlow
  obtain ⟨ε, c, C, B, hC, hintt, hintq, hlowu, hmass, hsum⟩ :=
    hK L hL N hN Φ hnorm hlow
  exact ⟨ε, c, C, B, hC,
    hpot_of_regime hv_supp hR0 hM hdR hdRχ hL (hint L hL N Φ)
      (hintRef L hL N Φ),
    hintt, hintq, hlowu, hmass, hsum⟩

end Work.UBBInputs2
