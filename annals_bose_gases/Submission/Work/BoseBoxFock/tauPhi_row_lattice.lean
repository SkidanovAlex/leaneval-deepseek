import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SqrtKin.kinFT_weight2_integrable
import Submission.Work.BoseBoxFock.deficit_inputs
import Submission.Work.BoseBoxFock.row_of_deficit
import Submission.Work.BoseBoxFock.tauPhi_row_closedBall
import Submission.Work.BoseBoxFock.tauSmPhiDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauPhi_row_lattice` — the kinetic row of the box↔model dictionary at the
explicit profile `tauPhi` (closed ball)

The target (below, statement unchanged) is the kinetic row

    Σ'_n ℓ⁻³·c²·tauPhi(‖k_n‖/c)·‖kinFT g k_n‖²  ≤  (2π)⁻³∫_p (‖p‖−c)₊²‖kinFT g p‖² ,
    k_n = kmomInt ℓ n = (2π/ℓ)n ,   cℓ ≥ 4π ,   tsupport g ⊆ closedBall 0 (ℓ/2) .

**What this file contains.**  `tauGapDefs.lean` proves the exact pointwise split of the left-hand
weight (`c²·tauPhi(r/c) = ρ_c(r) − Ψ_c(r)`, `ρ_c(r) = (r−3c/2)² + c₀c²`, `Ψ_c ≥ 0`,
`τ_c = 0` for `r ≤ 5c/4`, `Θ_c ≤ Ψ_c`, `F_c − τ_c ≥ max 0 (c·r − (5/4+c₀)c²)`); the corpus's two
moment identities (`L(1) = C(1)`, `L(‖·‖²) = C(‖·‖²)`, PROVED for this class) then give the
*exact* reduction

    Row  ⟺  (D)   c·(3S₁ − 2R₁) + L(Ψ_c) − C(Θ_c) ≥ (5/4+c₀)·c²·R₀ ,

with `S₁ = Σ'_n ℓ⁻³‖k_n‖·‖kinFT g k_n‖²`, `R₁ = (2π)⁻³∫‖p‖‖kinFT g p‖²`,
`R₀ = (2π)⁻³∫‖kinFT g p‖²`, `L(h) = Σ'_n ℓ⁻³ h(‖k_n‖)‖kinFT g k_n‖²`,
`C(h) = (2π)⁻³∫ h(‖p‖)‖kinFT g p‖²`, `Θ_c(r) = (c−r)₊²`, `c₀ = ∫t² tauKer t ∈ [0,1/16]`.

`tauPhi_row_lattice_of_deficit` below carries out that reduction for the actual state: it proves
the row from (D).  The abstract bridge is the delegated `Work.BoseBoxFock.row_of_deficit`, and the
state inputs (the two moment identities + the six summability/integrability side conditions) are
the delegated `Work.BoseBoxFock.deficit_inputs`.

The remaining content of the target is therefore *(D)*, a quantitative first-moment (aliasing)
bound: `3S₁ − 2R₁ = S₁ − 2D₀` with `D₀ = R₁ − S₁ ≥ 0` the Riesz/aliasing deficit, and `(D)` is
exactly the corpus's long-open `deficitAlias`/`heatSampling_le` crux in a state-adapted form (see
`FINDING_tauPhi_row_lattice.md`).  That is the only `sorry` left.

-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

/-! ## The pointwise bricks of the *shift* route

The residual `(D)` of this node has an equivalent spelling in the vocabulary of the *shift average*
(`FINDING_tauPhi_row_session2.md` §3–§4).  With

* `tauShiftW c r = 2c·r + tauTheta c r` — the *shifted* symbol `w_c` (linear plus the cap),
* `tauSmoothGap c r = tauSharp c r − c²·tauPhi (r/c)` — the smoothing gap `δ_c = F_c − τ_c ≥ 0`,

the pointwise identity `Ψ_c = δ_c + Θ_c − c·r + (5/4+c₀)c²` below gives

`(D)  ⟺  2c·R₁ + C(Θ_c) ≤ 2c·S₁ + L(Θ_c) + L(δ_c)`   (the *shift form*),

i.e. *the continuum `w_c`-form is dominated by the lattice `ψ_c = w_c + δ_c`-form*.  Together with
the PROVED shift-average identity `contForm_eq_shiftAverage` these bricks turn the pointwise-in-`q`
statement

`(Sh-pt)  ∀ q,  Σ'_n ℓ⁻³·w_c(‖k_n+q‖)·‖kinFT g (k_n+q)‖² ≤ Σ'_n ℓ⁻³·ψ_c(‖k_n‖)·‖kinFT g k_n‖²`

into a *sufficient* condition for the row.  Numerically (this session, exact `tauKer` profile,
`cℓ = 4π`, modulated ball states, `FINDING_tauPhi_row_lattice.md` §8): the excess of `(Sh-pt)` over
its `q`-average `(D)` — the fluctuation of `q ↦ S_q(w_c)` — is only `0.04–0.4 %` of `L(ψ_c)`,
against the `3.0–4.7 %` margin of `(D)`, so `(Sh-pt)` has genuine room for a lossy proof while
`(D)` itself is saturated in the single-mode limit. -/

/-- The *shifted* kinetic symbol `w_c(r) = 2c·r + Θ_c(r)`. -/
noncomputable def tauShiftW (c r : ℝ) : ℝ := 2 * c * r + tauTheta c r

lemma tauShiftW_eq (c r : ℝ) : tauShiftW c r = 2 * c * r + tauTheta c r := rfl

lemma tauShiftW_nonneg {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : 0 ≤ tauShiftW c r := by
  rw [tauShiftW]
  exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le) hr) (sq_nonneg _)

/-- **The polynomial splitting of the shifted symbol**: `w_c = ‖p‖² + c² − F_c`, i.e.
`2c·r + (c−r)₊² = r² + c² − (r−c)₊²`.  Since the `q`-shifted sampling of a polynomial weight is
`q`-independent (`Work.BoseBoxFock.lattice_moment_poly_shift`), this identity shows that the
whole fluctuation of `q ↦ S_q(w_c)` is carried by the *sharp* weight `F_c`:
`S_q(w_c) = (R₂ + c²R₀) − S_q(F_c)`. -/
lemma tauShiftW_eq_sq_add_sub_sharp (c r : ℝ) :
    tauShiftW c r = r ^ 2 + c ^ 2 - tauSharp c r := by
  rw [tauShiftW, tauTheta, tauSharp]
  rcases le_or_gt r c with h | h
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ c - r),
      max_eq_left (by linarith : r - c ≤ 0)]
    ring
  · rw [max_eq_left (by linarith : c - r ≤ 0),
      max_eq_right (by linarith : (0 : ℝ) ≤ r - c)]
    ring

/-- **The `C¹` decomposition of the sharp weight** (`FINDING_tauPhi_row_lattice.md` §7, the start of
action (3)): `F_c = ‖p‖² + c² − 2c‖p‖ − Θ_c`, i.e. the polynomial part `r² + c²`, the *kink*
`−2c·r` (the first-moment aliasing object of the corpus's `deficitAlias`) and the *compactly
supported `C¹` remainder* `−Θ_c`.

Summed against `ℓ⁻³‖kinFT g‖²` this splits `S_q(F_c)`, and the two polynomial pieces have
`q`-independent sampling (`lattice_moment_poly_shift`, `heatSampling_shift_invariant`), so the
pointwise form `(Sh-pt)` of the residual becomes

    2c·(S_q(‖·‖) − S_0(‖·‖)) + (S_q(Θ_c) − S_0(Θ_c))  ≤  L(δ_c)   for all q

— the `q`-fluctuation of the *first moment* plus that of the *cap*, paid by the lattice sampling of
the smoothing gap. -/
lemma tauSharp_eq_sq_sub_linear_sub_theta (c r : ℝ) :
    tauSharp c r = r ^ 2 - 2 * c * r + c ^ 2 - tauTheta c r := by
  rw [tauSharp, tauTheta]
  rcases le_or_gt r c with h | h
  · rw [max_eq_left (by linarith : r - c ≤ 0),
      max_eq_right (by linarith : (0 : ℝ) ≤ c - r)]
    ring
  · rw [max_eq_right (by linarith : (0 : ℝ) ≤ r - c),
      max_eq_left (by linarith : c - r ≤ 0)]
    ring

/-- **The arithmetic core of step (i) of `FINDING_tauPhi_row_lattice.md` §7.**  Given the two
*aggregate* identities

* `L(Ψ_c) = L(δ_c) + L(Θ_c) − c·S₁ + (5/4+c₀)c²·R₀`  (`hψ`),
* `L(F_c) − C(F_c) = 2c·(R₁ − S₁) + C(Θ_c) − L(Θ_c)`  (`hF`),

the deficit inequality `(D)` of this node is **equivalent** to the sharp-excess form

    (D)   ⟺   L(F_c) − C(F_c) ≤ L(δ_c)

(*the aliasing excess of the sharp kinetic weight `F_c` is at most the lattice sampling of the
smoothing gap `δ_c = F_c − τ_c`*).  This is pure algebra; the two identities are the bookkeeping
(`tauPsi_sharpExcess_decomp`, delegated) and `tauShiftW_eq_sq_add_sub_sharp` is the pointwise
input on the other side. -/
theorem deficit_iff_excess_arith {c S1 R1 R0 Lψ CΘ LΘ Lδ LF CF : ℝ}
    (hψ : Lψ = Lδ + LΘ - c * S1 + (5 / 4 + tauC0phi) * c ^ 2 * R0)
    (hF : LF - CF = 2 * c * (R1 - S1) + (CΘ - LΘ)) :
    (3 * (c * S1) - 2 * (c * R1) + Lψ - CΘ ≥ (5 / 4 + tauC0phi) * c ^ 2 * R0)
      ↔ (LF - CF ≤ Lδ) := by
  constructor
  · intro h
    rw [hψ] at h
    rw [hF]
    ring_nf at h ⊢
    linarith
  · intro h
    rw [hψ]
    rw [hF] at h
    ring_nf at h ⊢
    linarith

/-- The **smoothing gap** `δ_c(r) = F_c(r) − τ_c(r) = (r−c)₊² − c²·tauPhi (r/c) ≥ 0`. -/
noncomputable def tauSmoothGap (c r : ℝ) : ℝ := tauSharp c r - c ^ 2 * tauPhi (r / c)
lemma tauSmoothGap_nonneg {c r : ℝ} (hc : 0 < c) : 0 ≤ tauSmoothGap c r :=
  sub_nonneg.mpr (tauPhiWeight_le_tauSharp hc)

/-- `δ_c = 0` below the threshold `c`: both `F_c` and `τ_c` vanish there. -/
lemma tauSmoothGap_eq_zero_of_le {c r : ℝ} (hc : 0 < c) (hr : r ≤ c) : tauSmoothGap c r = 0 := by
  have h1 : r / c ≤ 1 := (div_le_one hc).mpr hr
  rw [tauSmoothGap, tauSharp, max_eq_left (by linarith : r - c ≤ 0),
    tauPhi_zero_of_le_one (r / c) h1]
  ring

/-- `δ_c = c·r − (5/4+c₀)c²` in the far range `r ≥ 2c` (the quadratic tail of `τ_c`). -/
lemma tauSmoothGap_eq_tail {c r : ℝ} (hc : 0 < c) (hr : 2 * c ≤ r) :
    tauSmoothGap c r = c * r - (5 / 4 + tauC0phi) * c ^ 2 := by
  have h2 : (2 : ℝ) ≤ r / c := (le_div_iff₀ hc).mpr (by linarith)
  have h0 : (0 : ℝ) ≤ r - c := by linarith
  rw [tauSmoothGap, tauSharp, max_eq_right h0, tauPhi_quad (r / c) h2, tauC0phi_def]
  field_simp
  ring

/-- **The pointwise bookkeeping identity of the shift route**:
`Ψ_c = δ_c + Θ_c − c·r + (5/4+c₀)c²`. -/
lemma tauPsi_eq_delta_add_theta {c r : ℝ} (hc : 0 < c) :
    tauPsi c r = tauSmoothGap c r + tauTheta c r - c * r + (5 / 4 + tauC0phi) * c ^ 2 := by
  rcases le_or_gt r c with hrc | hrc
  · rw [tauSmoothGap_eq_zero_of_le hc hrc, tauPsi_eq_rho_of_le hc (by linarith),
      tauTheta, max_eq_right (by linarith : (0 : ℝ) ≤ c - r), tauRho, tauC0phi_def]
    ring
  · have h0 : (0 : ℝ) ≤ r - c := by linarith
    rw [tauPsi, tauRho, tauSmoothGap, tauTheta, tauSharp, tauC0phi_def,
      max_eq_right h0, max_eq_left (by linarith : c - r ≤ 0)]
    ring

/-- Integrability of the two densities that the bridge `row_of_deficit` needs on top of
`deficit_inputs`: the unweighted density and its second moment.  Both are one-liners from the
Schwartz decay of `kinFT g`. -/
theorem deficit_inputs_extra {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖Submission.BoseGases.kinFT g p‖ ^ 2)
      ∧ Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
          ‖p‖ ^ 2 * ‖Submission.BoseGases.kinFT g p‖ ^ 2) :=
  ⟨SqrtKin.kinFT_sq_integrable hg hgc, SqrtKin.kinFT_weight2_integrable hg hgc⟩

/-- **The row follows from the deficit inequality (D).**  With `G := fun p => ‖kinFT g p‖²`, (D)
is exactly the `hdef` hypothesis of the bridge `Work.BoseBoxFock.row_of_deficit`; the moment
identities and the side conditions come from `Work.BoseBoxFock.deficit_inputs` and
`deficit_inputs_extra`. -/
theorem tauPhi_row_lattice_of_deficit {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    (hdef : c * (3 * (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
            - 2 * (((2 * Real.pi) ^ 3)⁻¹
              * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2))
          + (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * tauPsi c ‖kmomInt ℓ n‖
              * ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
          - ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
              tauTheta c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2
        ≥ (5 / 4 + tauC0phi) * c ^ 2 * (((2 * Real.pi) ^ 3)⁻¹
            * ∫ p : EuclideanSpace ℝ (Fin 3), ‖Submission.BoseGases.kinFT g p‖ ^ 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  obtain ⟨hS0, hS2, hs0, hs1, hs2, hsψ, hi1, hiθ⟩ := deficit_inputs hℓ hc hg hgc hgsupp
  obtain ⟨hi0, hi2⟩ := deficit_inputs_extra hℓ hg hgc
  exact row_of_deficit hℓ hc (fun p => ‖Submission.BoseGases.kinFT g p‖ ^ 2)
    (fun p => sq_nonneg _) hS0 hS2 hs0 hs1 hs2 hsψ hi0 hi1 hi2 hiθ hdef

/-- The kinetic row of the box↔model dictionary at the explicit profile `tauPhi`
(closed-ball class, the honest class of the assembly).  Its content is the deficit inequality
(D); see the module docstring and `FINDING_tauPhi_row_lattice.md`. -/
theorem tauPhi_row_lattice {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgc : HasCompactSupport g) (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  exact tauPhi_row_closedBall hℓ hc hcℓ hg hgc hgsupp

end Work.BoseBoxFock
