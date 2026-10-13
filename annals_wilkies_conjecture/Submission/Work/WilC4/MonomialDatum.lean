/-
  WilC4/MonomialDatum : the vocabulary of the *local preparation* input at the breakpoints of a
  definable family -- a **monomial datum with uniform threshold**.

  ## Why this file exists

  `Work.WilC4.rexp_deep_window_value_ratio` (the fibre's value ratio over a `B₀`-free window) is
  the local counterpart of `PolyBoundedRExp`, and its residue after the reduction
  `rexp_deep_window_value_ratio_of_mono_breaks` is: *monotonicity breaks of the fibre inside the
  window are harmless*.  Review showed that no statement phrased as "config + room ⟹ ratio bound"
  can isolate that residue: window-freeness of `[z/N, N z']` already forces every breakpoint to be
  at multiplicative distance `≥ N` from the pair.  The input therefore has to be phrased as a
  statement about the *local shape* of the fibre at a breakpoint, with its own vocabulary -- which
  is what this file introduces.

  ## The object

  `MonomialDatum Y B₀ c b q Λ C` says: at the breakpoint `b` (parameter `c`), whenever the
  *additive* neighbourhood `(b, b + Λ b)` meets `B₀` nowhere (so that `GoodFibre` speaks there), the
  values of the fibre normalised by `u^{q}` (`u = x - b`) are comparable up to the factor `C`, for
  any two points at additive distances `u ≤ u' ≤ 2u`.

  Three design points, all of them forced by review:

  * the *threshold* `Λ b` is additive (a neighbourhood of the breakpoint whose length is
    proportional to `b`); `Λ` is part of the *conclusion* of the existence theorem, so nothing in
    the statement fixes how long the transition region is;
  * the comparison is *normalised*: the exponent `q` ranges over a fixed finite set `Qs` and the
    *unit* factor is absorbed into `C`.  An un-normalised bound `|f (b+u)| ≍ u^q` is **false** for
    definable families (a spike `1/((x-b)²+μ²)` has two regimes), while the normalised comparison
    is exactly "monomial up to a unit";
  * the comparison is *conditional on the neighbourhood being `B₀`-free*, and the existence theorem
    assumes `B₀` has uniformly bounded fibres.  Without these, `ULPMStruct` is satisfied by
    `B₀ = Set.univ` (it is an implication on `B₀`-free intervals) and the datum fails at a zero of
    the fibre; with them, `GoodFibre` makes the fibre nonvanishing on the free part, which is what
    the two-sided comparison needs.

  ## The interface (consumers)

  * `MonomialDatum.ratio_le` : `|y'| ≤ C |y| (u'/u)^q` (one factor-2 step);
  * `MonomialDatum.ratio_le_bounded` : `|y'| ≤ (C K^Q) |y|` when `u' ≤ K u`, `q ≤ Q`, `Q ≥ 0`.

  Two further steps are delegated as `Work.WilC4.value_ratio_le_of_datum`, because they are the
  *plumbing* rather than the vocabulary:

  * the **chaining** of two factor-2 steps (`u' ≤ 4u` at the cost of `C²`; the target's
    configuration produces additive distances with `u' ≤ 3u`, not `2u`), most cleanly done in the
    rearranged form `|y'| / u'^q ≤ C |y| / u^q` of the datum;
  * the **wiring to the target's hypothesis**: the window freeness `[z/N, N z'] ∩ B₀ = ∅` supplies
    the datum's own freeness clause for `(b, b + Λ b)` as soon as `Λ b ≤ z` and `N b ≤ z`, and
    `GoodFibre` then supplies the nonvanishing;
  with conclusion `|y'| ≤ (C * C * 3^Q) |y|`.

  The existence theorem to be proved (delegated separately, since it *is* the preparation input) is
  `Work.WilC4.exists_monomialDatum`: ONE finite `Qs ⊆ ℚ`, ONE `Λ` and ONE `C` working for every
  parameter and every breakpoint.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMDefs
import Submission.Work.WilC4.ErealDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr valY ratioY)

variable {k : ℕ}

/-- **A monomial datum with uniform threshold** for the fibre of `Y` at the breakpoint `b` with
parameter `c` and breakpoint family `B₀`: with exponent `q : ℚ`, threshold factor `Λ > 0` and
constant `C ≥ 1`, whenever the additive neighbourhood `(b, b + Λ b)` is free of `B₀`, the fibre
values normalised by `u^q` (`u = x - b`, an *additive* distance from `b`) are comparable up to the
factor `C`, for any two points at additive distances with `u ≤ u' ≤ 2u`.

The pairing is the *multiplicative* one `u' ≤ 2u` (not `u' ≤ 2u + b`): the latter would let the
constant `C` grow with `b` (e.g. for the ramp `u ↦ u + μu²` one would need `C ≥ 1 + μb`), while the
factor-2 pairing is exactly what pinning the exponent is meant to control.  Larger factors are
reached by chaining two such comparisons. -/
def MonomialDatum (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ)) (c : Fin k → ℝ)
    (b : ℝ) (q : ℚ) (Λ C : ℝ) : Prop :=
  0 < b ∧ 0 < Λ ∧ 1 ≤ C ∧
    ∀ u u' y y' : ℝ, 0 < u → u ≤ u' → u' ≤ 2 * u → u' < Λ * b →
      (∀ t : ℝ, b < t → t < b + Λ * b → Fin.cons t c ∉ B₀) →
      Gr Y c (b + u) y → Gr Y c (b + u') y' → y ≠ 0 → y' ≠ 0 →
      |y'| * u ^ (q : ℝ) ≤ C * |y| * u' ^ (q : ℝ) ∧
        |y| * u' ^ (q : ℝ) ≤ C * |y'| * u ^ (q : ℝ)

namespace MonomialDatum

variable {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {b : ℝ}
  {q : ℚ} {Λ C : ℝ}

theorem b_pos (h : MonomialDatum Y B₀ c b q Λ C) : 0 < b := h.1

theorem Lam_pos (h : MonomialDatum Y B₀ c b q Λ C) : 0 < Λ := h.2.1

theorem one_le_C (h : MonomialDatum Y B₀ c b q Λ C) : 1 ≤ C := h.2.2.1

/-- The datum in "ratio" form: `|y'| ≤ C |y| (u'/u)^q`.  This is the form in which the datum
bounds the *value ratio* of the fibre over a factor-2 window inside the free part of the additive
neighbourhood of the breakpoint.

Equivalently (dividing by `u^q · u'^q > 0`), `|y'| / u'^q ≤ C · (|y| / u^q)` -- the rearranged form
in which chaining two steps of the comparison is immediate. -/
theorem ratio_le (h : MonomialDatum Y B₀ c b q Λ C) {u u' y y' : ℝ} (hu : 0 < u) (huu' : u ≤ u')
    (hu'b : u' ≤ 2 * u) (hu'Λ : u' < Λ * b)
    (hfree : ∀ t : ℝ, b < t → t < b + Λ * b → Fin.cons t c ∉ B₀)
    (hy : Gr Y c (b + u) y) (hy' : Gr Y c (b + u') y') (hne : y ≠ 0) (hne' : y' ≠ 0) :
    |y'| ≤ C * |y| * (u' / u) ^ (q : ℝ) := by
  obtain ⟨-, -, -, hmain⟩ := h
  obtain ⟨h1, -⟩ := hmain u u' y y' hu huu' hu'b hu'Λ hfree hy hy' hne hne'
  have hu0 : 0 ≤ u := le_of_lt hu
  have hu'0 : 0 ≤ u' := le_trans hu0 huu'
  have hpow : 0 < u ^ (q : ℝ) := Real.rpow_pos_of_pos hu _
  rw [Real.div_rpow hu'0 hu0]
  rw [show C * |y| * (u' ^ (q : ℝ) / u ^ (q : ℝ)) = (C * |y| * u' ^ (q : ℝ)) / u ^ (q : ℝ) by
    ring]
  rw [le_div_iff₀ hpow]
  linarith [h1]

/-- The same bound with the exponent and the factor between the two distances made explicit: if
`u' ≤ K u` with `K ≥ 1` and `q ≤ Q` with `0 ≤ Q`, then `|y'| ≤ (C K^Q) |y|`.  This is the
"bounded window, bounded exponent" form in which the datum is consumed (the factor-2 window is the
basic case `K = 2`; larger factors are reached by chaining). -/
theorem ratio_le_bounded (h : MonomialDatum Y B₀ c b q Λ C) {u u' y y' K Q : ℝ} (hK : 1 ≤ K)
    (hQ : 0 ≤ Q) (hqQ : (q : ℝ) ≤ Q) (hu : 0 < u) (huu' : u ≤ u') (hu'K : u' ≤ K * u)
    (hu'b : u' ≤ 2 * u) (hu'Λ : u' < Λ * b)
    (hfree : ∀ t : ℝ, b < t → t < b + Λ * b → Fin.cons t c ∉ B₀)
    (hy : Gr Y c (b + u) y) (hy' : Gr Y c (b + u') y') (hne : y ≠ 0) (hne' : y' ≠ 0) :
    |y'| ≤ (C * K ^ Q) * |y| := by
  have hle := h.ratio_le hu huu' hu'b hu'Λ hfree hy hy' hne hne'
  have hb1 : (1 : ℝ) ≤ u' / u := (one_le_div hu).mpr huu'
  have hbK : u' / u ≤ K := by
    rw [div_le_iff₀ hu]; linarith
  have hpow : (u' / u) ^ (q : ℝ) ≤ K ^ Q := by
    have h1 : (u' / u) ^ (q : ℝ) ≤ (u' / u) ^ Q := Real.rpow_le_rpow_of_exponent_le hb1 hqQ
    have h2 : (u' / u) ^ Q ≤ K ^ Q := Real.rpow_le_rpow (le_trans zero_le_one hb1) hbK hQ
    linarith
  have hC0 : 0 ≤ C := le_trans zero_le_one h.one_le_C
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hCy : 0 ≤ C * |y| := mul_nonneg hC0 hy0
  calc |y'| ≤ C * |y| * (u' / u) ^ (q : ℝ) := hle
    _ ≤ C * |y| * K ^ Q := mul_le_mul_of_nonneg_left hpow hCy
    _ = (C * K ^ Q) * |y| := by ring

end MonomialDatum

end Work.WilC4
