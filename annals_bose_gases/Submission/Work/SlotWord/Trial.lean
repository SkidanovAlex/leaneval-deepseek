import ChallengeDeps
import Submission.Work.SlotWord.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.SlotWord.Trial` — (R1)(b): the delivered bound at the fibre

The per-fibre residual `FibreWordBoundAt` of `Defs.lean` has two halves:

* the **trial-state (Rayleigh) half**: the *delivered* count-indexed per-box ground energy
  `Work.BlockBound4.diagWeBAt k (L·d) (dens N L) v h c (tbGapCoeff (L·d) ε)` at the box-supported
  fibre state — this is `FibreWordApprox` below, the "delivered bound at the fibre";
* the **word-comparison half**: the delivered faithful word at that fibre state is dominated by the
  *sliding* word of the fibre — this is `FibreWordCompare` below (the `DLWire` route at the sliding
  box, plus the translation/normalisation bookkeeping between `B(u)` and the centred cube);

and this module proves the composition `FibreWordBoundAt ⟸ FibreWordApprox + FibreWordCompare`.

## The two candidate fibre states

`centreFibre S e B Ψ w y` is the fibre of the *slot piece* transported to the centred cube:
`x ↦ (1_{slotSet B S}·Ψ)(slotComb S (x∘e + w) y)`.  Its support lies in `acube (L·d)^{S}` (because
`B = dlBox L d u ⊆ (L·d)•u + acube (L·d)`), and its `abox (S.card) (L·d)`-`L²` mass is exactly the
fibre mass `slotFibreMassReal B S (slotPiece B S Ψ) y` — see `Defs.pieceFibre`.  It is the state FS's
box Hamiltonian `H_{B(u)}` acts on.  It is *not* smooth on `ℝ³` (the slot-piece indicator is not), so
it is not literally a member of the corpus trial space `CSBox`; that is one of the two named
obligations of `FibreWordApprox`.

`perPiece_fibre`: the smooth companion is `PerSector.slotFibreState S e (slotPiece B S Ψ) y`, and
the two agree wherever the piece is supported.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.BlockBound4
open Work.KinPSuperadd
open Work.SmallBoxTBWord
open Classical

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-! ## 1. The trial-state half: the Rayleigh inequality at the delivered word -/

/-- **The Rayleigh (trial-state) inequality at the delivered faithful word.**  For a smooth state
`Ψ` with positive box norm, the delivered count-indexed per-box ground energy `diagWeBAt N s …`
dominates the faithful `diagW`-energy per unit mass:

    diagWeBAt N s μ v h c₀ cgap · ∫_{abox N s} Ψ² ≤ diagWWord s c₀ cgap N Ψ
        + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Ψ .

This is `Work.KinPSuperadd.rayleigh_diagSlotWord` in the Door-4 vocabulary (`diagWeBAt = slotEB`,
`blockE = diagWWord + qLHSword`); it is the *proved* half of (R1)(b). -/
theorem rayleigh_diagWeBAt {N : ℕ} {s R μ c₀ cgap : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : ∃ w : ℝ³ → ℝ, _root_.BoseGases.IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (hcgap : 0 ≤ cgap)
    (hint : ∀ (M : ℕ) (Ψ : X M → ℝ), ContDiff ℝ ∞ Ψ →
      Integrable (fun p : ℝ³ => fsKinCoeff c₀ ‖p‖ * ∑ i : Fin M, (s ^ 3)⁻¹ *
        ∫ x in abox M s, ‖pSlotAmp s p Ψ i x‖ ^ 2))
    {Ψ : X N → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) :
    diagWeBAt N s μ v h c₀ cgap * (∫ x in abox N s, (Ψ x) ^ 2)
      ≤ diagWWord s c₀ cgap N Ψ
        + qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Ψ := by
  have h0 := rayleigh_diagSlotWord hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ hcgap hint hΨ
  rwa [blockE_eq] at h0

/-! ## 2. The fibre state on the centred cube -/

/-- **The fibre of the slot piece, transported to the centred cube.**  With `w = (L·d)•u`, the
centred coordinates `x` are shifted back by `w` so that the fibre's support lands inside
`acube (L·d)^{S}`. -/
def centreFibre (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (B : Set ℝ³) (Ψ : X N → ℝ)
    (w : ℝ³) (y : SlotOut N S → ℝ³) : X S.card → ℝ :=
  fun x => slotPiece B S Ψ (slotComb S (fun i : SlotIn N S => x (e i) + w) y)

theorem centreFibre_apply (S : Finset (Fin N)) (e : SlotIn N S ≃ Fin S.card) (B : Set ℝ³)
    (Ψ : X N → ℝ) (w : ℝ³) (y : SlotOut N S → ℝ³) (x : X S.card) :
    centreFibre S e B Ψ w y x
      = slotPiece B S Ψ (slotComb S (fun i : SlotIn N S => x (e i) + w) y) := rfl

/-! ## 3. (R1)(b): the two named obligations and their composition -/

/-- **(R1)(b)-a — the delivered bound at the fibre** (the "trial-state" half).  For a.e. good `u`,
every nonempty slot set `S` and a.e. outside configuration `y`, the fibre mass times the delivered
count-indexed ground energy is dominated by the *faithful* (`diagWWord` + sharp kernels) energy of
the centred fibre:

    slotFibreMassReal · diagWeBAt k (L·d) (dens N L) v h c (tbGapCoeff (L·d) ε)
      ≤ diagWWord (L·d) c (tbGapCoeff (L·d) ε) k (centreFibre …) + qLHSword(sharp)(centreFibre …) .

Content: (i) the *proved* Rayleigh inequality `rayleigh_diagWeBAt` at smooth states; (ii) the
normalisation `∫_{abox k (L·d)} (centreFibre)² = slotFibreMassReal …` (the translation between the
box `B(u)` and the centred cube); (iii) the passage from the non-smooth box-supported fibre to the
`CSBox` trial space (the delivered `diagWeBAt` is an infimum over *globally smooth* states).
Item (iii) is the only genuinely analytic step, and it is a lower-semicontinuity statement for the
faithful word. -/
def FibreWordApprox (v : ℝ³ → ℝ) (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) : Prop :=
  ∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))),
    ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        slotFibreMassReal (dlBox L d u) S (slotPiece (dlBox L d u) S Φ) y
            * diagWeBAt S.card (L * (d : ℝ)) (dens N L) v h c (tbGapCoeff (L * (d : ℝ)) ε)
          ≤ diagWWord (L * (d : ℝ)) c (tbGapCoeff (L * (d : ℝ)) ε) S.card
              (centreFibre S e (dlBox L d u) Φ ((L * (d : ℝ)) • u) y)
            + qLHSword (N := S.card) (L * (d : ℝ)) (dens N L)
                (wPairC (L * (d : ℝ)) v) (wPairC (L * (d : ℝ)) (g0 v h))
                (centreFibre S e (dlBox L d u) Φ ((L * (d : ℝ)) • u) y)

/-- **(R1)(b)-b — the kernel/word comparison at the fibre** (the "word-comparison" half).  For a.e.
good `u`, every nonempty slot set `S`, every `e` and a.e. outside `y`, the *faithful* (`diagWWord` at
the sharp kernels `wPairC (L·d)`) energy of the centred fibre is dominated by the *sliding* word of
the fibre.

Content: the `Work.BlockBound4.Repoint` comparison (`pDiagForm ≼ kinWordB`) and the
`Work.DLWire` route at the sliding box — i.e. the honest χ-weighted Dirichlet kinetic of the fibre
dominates the faithful `Q_Bχ_B[√−Δ−c]₊²χ_BQ_B` word — together with the two kernel comparisons
`wPairC (L·d) ⟷ wSmallPair M L d u` and the translation bookkeeping. -/
def FibreWordCompare (v : ℝ³ → ℝ) (h : ScatSol v) (M : ℕ) (L d ε c : ℝ) (N : ℕ)
    (Φ : X N → ℝ) : Prop :=
  ∀ᵐ u ∂(volume.restrict (goodSet L d (dens N L))),
    ∀ S : Finset (Fin N), 0 < S.card → ∀ e : SlotIn N S ≃ Fin S.card,
      ∀ᵐ y ∂(volume.restrict (slotOutside L (dlBox L d u) S)),
        diagWWord (L * (d : ℝ)) c (tbGapCoeff (L * (d : ℝ)) ε) S.card
            (centreFibre S e (dlBox L d u) Φ ((L * (d : ℝ)) • u) y)
          + qLHSword (N := S.card) (L * (d : ℝ)) (dens N L)
              (wPairC (L * (d : ℝ)) v) (wPairC (L * (d : ℝ)) (g0 v h))
              (centreFibre S e (dlBox L d u) Φ ((L * (d : ℝ)) • u) y)
        ≤ fibreWord h M S.card L d ε c (dens N L) u
            (pieceFibre (dlBox L d u) S e Φ y)

/-- **(R1)(b) from its two halves.**  `FibreWordApprox + FibreWordCompare ⟹ FibreWordBoundAt`
with the count-indexed delivered ground energy. -/
theorem fibreWordBoundAt_of_approx_compare {v : ℝ³ → ℝ} {h : ScatSol v} {M : ℕ} {L d ε c : ℝ}
    {N : ℕ} {Φ : X N → ℝ}
    (hA : FibreWordApprox v h M L d ε c N Φ) (hC : FibreWordCompare v h M L d ε c N Φ) :
    FibreWordBoundAt h M L d ε c N Φ
      (fun k => diagWeBAt k (L * (d : ℝ)) (dens N L) v h c (tbGapCoeff (L * (d : ℝ)) ε)) := by
  filter_upwards [hA, hC] with u hAu hCu
  intro S hS e
  filter_upwards [hAu S hS e, hCu S hS e] with y hyA hyC
  exact le_trans hyA hyC

end Work.SlotWord
