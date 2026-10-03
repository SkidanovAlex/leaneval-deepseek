import Mathlib
import Submission.Work.Peluse.UControl.pelusePetChapterDefs

/-!
# The last step of the proof of Peluse's Proposition 3.4: the interface

`Work.Peluse.UControl.Prop34 P` is the paper's Proposition 3.4 for the embedded configuration
`(x, x+y, …, x+y^{d-1}, x+P(y))` (`d = deg P`).  Its proof in
`Submission/Work/Peluse/UControl/peluseProp34.lean` splits as in the source:

* `PetChapter P` (`pelusePetChapterDefs.lean`) — the PET chapter, Peluse's Lemma 4.9: from
  `γ ≤ ‖ΛMD N M P F‖` one gets, for a datum `D` and a parameter-dependent constant term `β`, the
  average over the parameter box of the modulus of the multilinear correlation along the *linear*
  configuration with the datum's directions; and
* the last step — Peluse's Lemma 4.10 applied at each parameter, plus the identification of the
  resulting direction family with the datum's own family `w ↦ dir D d c (d-1) w (pad d a)`, plus
  the averaging.

This file isolates the *one-parameter* half of that last step, `LinFibBound P D`: the fibre value
`linFib` (the modulus of the linear-configuration correlation at a single parameter `a`) controls
the box-norm power of `f` along the datum's own directions.  It is proved by applying the
workspace's Peluse Lemma 4.10 (`Work.Peluse.PetLinear.linear_boxnorm_control_paper`) to the
configuration whose coefficient vector is the datum's direction family (reordered so that the
*last* coefficient is the one of the full set of level-`(d-1)` slots), and then reindexing the
direction tuple from the complementary enumeration to the datum's own one
(`Work.Peluse.Track.boxSumPow_comp_bij_proved`); the complement identity
`dir(ω_full) - dir(ω) = dir(ω_full \ ω)` is what makes the two enumerations match.

The only reason the conclusion is stated at the support set `symIcc ((4*Cne+1)*N)` rather than
`symIcc N` is that the slot functions of the linear configuration are *translates* of `f` by
`petDir·y + β`, which the shift bound controls by `Cne·N`; the consumer transfers back down to
`symIcc N` by monotonicity of the box-norm power in the support set.
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-- The fibre of the linear-configuration average: the modulus of the multilinear correlation along
the linear configuration with the datum's directions at the single parameter `a`, the `i`-th slot
carrying `f` or its conjugate according to `b i`, at the shift `petDir·y + β`. -/
def linFib (D : IdxDatum) (l : ℕ) (c : ℤ) (N M : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (a : D.Idx l) : ℝ :=
  ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, f x *
    ∑ y ∈ Finset.Icc 1 M,
      ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
          else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖

/-- `linFamAvg` is the average of the fibres `linFib` over the parameter box (definitional). -/
theorem linFamAvg_eq (D : IdxDatum) (l : ℕ) (c : ℤ) (N M H : ℕ) (f : ℤ → ℂ)
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) :
    linFamAvg D l c N M H f b β
      = (((D.parBox l H).card : ℕ) : ℝ)⁻¹ * ∑ a ∈ D.parBox l H,
          linFib D l c N M f b β a := rfl

/-- **The one-fibre half of the last step of the proof of Proposition 3.4.**  There are an exponent
`K₄ ≥ 1` and a constant `C₄ > 0` (depending on `P` and the datum `D` only) such that, at any
parameter `a`, if the fibre value `linFib` satisfies the gauge `δ' ≤ γ₄^{K₄}/C₄` with
`γ₄ := linFib²/(2·Cne+1)²` — the normalisation of Lemma 4.10 after the support enlargement — then
the level-`|I_{d-1}|` box-norm power of `f` along the datum's own direction family is at least
`(γ₄/C₄)^{K₄}`.

The hypotheses are those of Peluse's Lemma 4.10: `f` is `1`-bounded and supported in `[-N,N]`, the
shift bound `|petDir·y + β| ≤ Cne·N` holds for `y ∈ [1,M]` (the paper's (4.11)) and the window is
nondegenerate.  The constant `2·Cne+1` is the two-point bound `|petDir| ≤ 2·Cne·N` on the
coefficient itself (compare the shift bound at `y = 1` and `y = 2`, both allowed since `M ≥ 2`),
which is what converts the translates back into a configuration of Lemma 4.10's shape; `4·Cne+1`
is the resulting support enlargement. -/
def LinFibBound (P : Polynomial ℤ) (D : IdxDatum) : Prop :=
  ∃ K4 : ℕ, 1 ≤ K4 ∧ ∃ C4 : ℝ, 0 < C4 ∧
    ∀ (N M : ℕ) (f : ℤ → ℂ) (δ' : ℝ) (Cne : ℕ) (a : D.Idx P.natDegree)
      (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
      (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
      2 ≤ P.natDegree → 2 ≤ Fintype.card (D.I (P.natDegree - 1)) → 1 ≤ N → 2 ≤ M →
      0 < δ' → 1 ≤ Cne →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      (∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
        |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i|
          ≤ (Cne : ℤ) * (N : ℤ)) →
      1 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      δ' ≤ ((linFib D P.natDegree P.leadingCoeff N M f b β a) ^ 2
              / (((2 * Cne + 1 : ℕ) : ℝ) ^ 2)) ^ K4 / C4 →
      (((linFib D P.natDegree P.leadingCoeff N M f b β a) ^ 2
              / (((2 * Cne + 1 : ℕ) : ℝ) ^ 2)) / C4) ^ K4
        ≤ Work.Peluse.boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
            (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
              Work.Peluse.arithIcc (petDir D P.natDegree P.leadingCoeff a i)
                (⌊δ' * (M : ℝ)⌋).toNat)
            (Work.Peluse.symIcc ((4 * Cne + 1) * N)) f

/-- **The global (averaged) form of Peluse's Lemma 4.10** for the datum's direction family: from a
lower bound for the *averaged* fibre value `linFamAvg` (the quantity produced by the PET chapter) and
the **global** gauge `δ' ≤ γ^{K₄}/C₄` — the gauge of the paper's Lemma 4.10 when every step is carried
out on the averaged quantity, as in `PETTwo.pet_family_boxnorm_of_configuration` — one gets the same
bound for the *averaged* level-`|I_{d-1}|` box-norm power of `f` along the datum's direction family,
at the enlarged support `symIcc ((4·Cne+1)·N)` forced by the translates `f (· + petDir·y + β)`.

This is the piece the assembly `prop34_of_chapters` should consume: the per-parameter form
(`LinFibBound`) is *not* usable, because its gauge is a power of the *fibre's* own level, while the
hypothesis available to the consumer is only the average (see
`NOTES_UControl_peluseProp34.md` §3 and §5). -/
def LinFamBound (P : Polynomial ℤ) (D : IdxDatum) : Prop :=
  ∃ K4 : ℕ, 1 ≤ K4 ∧ ∃ C4 : ℝ, 0 < C4 ∧
    ∀ (N M : ℕ) (f : ℤ → ℂ) (δ' γ : ℝ) (Cne : ℕ)
      (b : Fin (Fintype.card (D.I (P.natDegree - 1))) → Bool)
      (β : D.Idx P.natDegree → Fin (Fintype.card (D.I (P.natDegree - 1))) → ℤ),
      2 ≤ P.natDegree → 2 ≤ Fintype.card (D.I (P.natDegree - 1)) → 1 ≤ N → 2 ≤ M →
      0 < δ' → 0 < γ → γ ≤ 1 → 1 ≤ Cne →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
      (∀ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
        ∀ i : Fin (Fintype.card (D.I (P.natDegree - 1))), ∀ y ∈ Finset.Icc 1 M,
          |petDir D P.natDegree P.leadingCoeff a i * (y : ℤ) + β a i|
            ≤ (Cne : ℤ) * (N : ℤ)) →
      1 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
      γ ≤ linFamAvg D P.natDegree P.leadingCoeff N M (⌊δ' * (M : ℝ)⌋).toNat f b β →
      δ' ≤ γ ^ K4 / C4 →
      (γ / C4) ^ K4 ≤
        (((D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat).card : ℕ) : ℝ)⁻¹ *
          ∑ a ∈ D.parBox P.natDegree (⌊δ' * (M : ℝ)⌋).toNat,
            Work.Peluse.boxNormPow (Fintype.card (D.I (P.natDegree - 1)))
              (fun i : Fin (Fintype.card (D.I (P.natDegree - 1))) =>
                Work.Peluse.arithIcc (petDir D P.natDegree P.leadingCoeff a i)
                  (⌊δ' * (M : ℝ)⌋).toNat)
              (Work.Peluse.symIcc ((4 * Cne + 1) * N)) f

end

end Work.Peluse.UControl
