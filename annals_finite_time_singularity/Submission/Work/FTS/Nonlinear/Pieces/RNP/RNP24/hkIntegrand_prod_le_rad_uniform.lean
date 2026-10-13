import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.RNP.RNP24

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# The *uniform* radial product bound for `HkIntegrand` (row 24, radial piece)

`hkIntegrand_prod_le_rad_uniform` is the pointwise `ℋ⁴`-integrand bound for the product
`R(z)·h(z,θ)` of a *radial* function with a general function, with a constant that is
**universal**: it does not depend on `α` or on the radial size `M`:

  `HkIntegrand α 4 (R·h) z θ ≤ C · (M · HkIntegrand α 4 h z θ
     + (D_z^4 R)² w(z)² σ(θ) · Qg h θ)`,

where `M` bounds `(D_z^b R)²` for `b ≤ 3` and `Qg h θ = ∫_z (D_z h(z,θ))² w(z)² dz`.
The third hypothesis `hQh` is the radial Hardy bound `(h z θ)² ≤ Qg h θ`, which is what
lets the single slot `b = 4` of the Leibniz expansion be absorbed into the second
summand (that slot is only non-vacuous in the term `D_z^4(R·h)`, where `D_z^4 R` multiplies
`h` itself).

The proof is the Cauchy–Schwarz computation: expand the two Leibniz sums supplied as
hypotheses, apply `(∑ F_b)² ≤ card · ∑ F_b²`, and bound every summand either by
`M · HkIntegrand α 4 h` (all slots with `b ≤ 3`) or — for the single slot `b = 4` — by
`(D_z^4 R)² w² σ · Qg h` via `hQh` and `light_sq`.  No smoothness of `R` or `h` is used,
so the argument applies to the concrete nonlinear data.

The three slot lemmas below are the computation of the sibling
`RNP24/hkIntegrand_prod_le_rad` (whose explicit witness is already independent of `α` and
`M`); they are reproduced here so that the present module is self-contained and its
`C = 4194304` is manifest.  (The module deliberately imports only `radial_prod`: nothing
from `Pieces.Ctx` is used by the statement or the proof.)
-/


/-! ## The three slot estimates -/

/-- **One pure `D_z`-slot of the product, `i ≤ 3`.**  Every radial derivative has order
`b ≤ 3`, hence is controlled by `M`. -/
private theorem light_slot_le_M {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
    (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ))
    {i : ℕ} (hi : i ≤ 3) {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z) :
    (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
      ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ := by
  have hzI : z ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr hz
  have hDz' := hDz i (by omega) z hzI θ hθ
  set F : ℕ → ℝ := fun b => (i.choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z
        * (Work.Spaces.DzIter (i - b) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))) with hF
  have hkey : Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))
      = ∑ b ∈ Finset.range (i+1), F b := by
    rw [hDz', Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (i+1)) (f := F)
  have hcard : ((Finset.range (i+1)).card : ℝ) = (i:ℝ) + 1 := by
    rw [Finset.card_range]; push_cast; ring
  have hcard5 : ((Finset.range (i+1)).card : ℝ) ≤ 5 := by
    rw [hcard]; exact_mod_cast (by omega : i + 1 ≤ 5)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hterm : ∀ b ∈ Finset.range (i+1),
      F b ^ 2 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) := by
    intro b hb
    have hbi : b ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb3 : b ≤ 3 := le_trans hbi hi
    have hib : i - b ≤ 4 := by omega
    have h1 : ((i.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have hh := Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (i := i) (b := b) (by omega)
      have h0 : (0:ℝ) ≤ ((i.choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hh, h0]
    have h2 : (Work.Elliptic.DzdIter b R z)^2 ≤ M := hM b hb3 z hzI
    have h3 : (Work.Spaces.DzIter (i-b) h z θ
          * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
        ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
      Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ (i-b) hib
    have hprod : (Work.Elliptic.DzdIter b R z)^2
          * (Work.Spaces.DzIter (i-b) h z θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
        ≤ M * Work.Spaces.HkIntegrand α 4 h z θ :=
      mul_le_mul h2 h3 (sq_nonneg _) hM0
    have hprod2 : ((i.choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.DzIter (i-b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2)
        ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
      mul_le_mul h1 hprod (by positivity) (by norm_num)
    rw [hF]
    have hgoal : ((i.choose b : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.DzIter (i - b) h z θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))))) ^ 2
        = ((i.choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.DzIter (i-b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2) := by ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (i+1), F b ^ 2)
      ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
    calc (∑ b ∈ Finset.range (i+1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (i+1), (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (i+1)).card : ℝ)
            * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          have h0 : 0 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
            mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
          exact mul_le_mul_of_nonneg_right hcard5 h0
  nlinarith [hcs, hcard5, hsum, hM0, hHnn]

/-- **The top pure `D_z`-slot of the product, `i = 4`.**  The summand in which all four
`D_z`-derivatives fall on `R` pairs `D_z^4 R` with `h` itself, which is controlled by the
radial Hardy bound `(h z θ)² ≤ Qg h θ` supplied by the caller. -/
private theorem light_slot_four_le_M {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
    (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ))
    {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z)
    (hQh : ∀ z' ∈ Set.Ioi (0:ℝ), (h z' θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ) :
    (Work.Spaces.DzIter 4 (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
      ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ
        + 65536 * (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
  have hsin : 0 < Real.sin (2*θ) := Work.FTS.Nonlinear.RadialProd.sin_two_pos_of_mem_Ioo hθ
  have hzI : z ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr hz
  have hDz4 := hDz 4 (by norm_num) z hzI θ hθ
  set F : ℕ → ℝ := fun b => ((4:ℕ).choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z
        * (Work.Spaces.DzIter (4 - b) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))) with hF
  have hkey : Work.Spaces.DzIter 4 (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))
      = ∑ b ∈ Finset.range 5, F b := by
    rw [hDz4, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range 5) (f := F)
  have hcard : ((Finset.range 5).card : ℝ) = 5 := by rw [Finset.card_range]; norm_num
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg
      (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hQgnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ :=
    Work.FTS.Nonlinear.RadialProd.Qg_nonneg h θ
  have hSnn : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
      * Work.FTS.Nonlinear.RadialProd.smE θ * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    have h1 : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_nonneg (mul_nonneg h1 hsmEnn) hQgnn
  have hterm : ∀ b ∈ Finset.range 5, F b ^ 2
      ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
        + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ) := by
    intro b hb
    have hb4 : b ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have h1 : (((4:ℕ).choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have hh := Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (i := 4) (b := b) (by norm_num)
      have h0 : (0:ℝ) ≤ (((4:ℕ).choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hh, h0]
    rw [hF]
    have hgoal : (((4:ℕ).choose b : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.DzIter (4 - b) h z θ
              * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))))) ^ 2
        = (((4:ℕ).choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.DzIter (4 - b) h z θ
                  * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2) := by ring
    rw [hgoal]
    rcases (by omega : b ≤ 3 ∨ b = 4) with hb3 | hb4'
    · have h2 : (Work.Elliptic.DzdIter b R z)^2 ≤ M := hM b hb3 z hzI
      have h3 : (Work.Spaces.DzIter (4 - b) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 h z θ (4 - b) (by omega)
      have hprod : (Work.Elliptic.DzdIter b R z)^2
            * (Work.Spaces.DzIter (4 - b) h z θ
                * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          ≤ M * Work.Spaces.HkIntegrand α 4 h z θ :=
        mul_le_mul h2 h3 (sq_nonneg _) hM0
      have hprod2 := mul_le_mul h1 hprod (by positivity) (by norm_num : (0:ℝ) ≤ 256)
      have hsecond : 0 ≤ 256 * ((Work.Elliptic.DzdIter 4 R z)^2
          * (Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * Work.FTS.Nonlinear.RadialProd.Qg h θ) :=
        mul_nonneg (by norm_num) hSnn
      linarith [hprod2, hsecond]
    · subst hb4'
      have h3 : (Work.Spaces.DzIter (4 - 4) h z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          = (h z θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2 := by
        norm_num
      have hls : (h z θ * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          = (h z θ)^2 * (Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ :=
        Work.FTS.Nonlinear.RadialProd.light_sq (h z θ) z θ hsin
      have hQg' : (h z θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ := hQh z hzI
      have hw : 0 ≤ (Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ :=
        mul_nonneg (sq_nonneg _) hsmEnn
      have hkey4 : (Work.Elliptic.DzdIter 4 R z)^2
            * (Work.Spaces.DzIter (4 - 4) h z θ
                * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2)))^2
          ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
              * Work.FTS.Nonlinear.RadialProd.smE θ
              * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
        have hI4 : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 := sq_nonneg _
        rw [h3, hls]
        have hstep : (h z θ)^2 * ((Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ)
            ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ
              * ((Work.Spaces.w z)^2 * Work.FTS.Nonlinear.RadialProd.smE θ) :=
          mul_le_mul_of_nonneg_right hQg' hw
        have hstep2 := mul_le_mul_of_nonneg_left hstep hI4
        nlinarith [hstep2]
      have hprod2 := mul_le_mul h1 hkey4 (by positivity) (by norm_num : (0:ℝ) ≤ 256)
      have hfirst : 0 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
        mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
      linarith [hprod2, hfirst]
  have hsum : (∑ b ∈ Finset.range 5, F b ^ 2)
      ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
        + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := by
    calc (∑ b ∈ Finset.range 5, F b ^ 2)
        ≤ ∑ _b ∈ Finset.range 5, (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
                * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := Finset.sum_le_sum hterm
      _ = ((Finset.range 5).card : ℝ) * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
                * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)
            + 256 * ((Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
                * Work.FTS.Nonlinear.RadialProd.smE θ
                * Work.FTS.Nonlinear.RadialProd.Qg h θ)) := by rw [hcard]
  have hMHnn : 0 ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := mul_nonneg hM0 hHnn
  nlinarith [hcs, hcard, hsum, hMHnn, hSnn]

/-- **One mixed slot of the product.**  Since `i ≥ 1`, `j ≤ 3` and every radial derivative
in the Leibniz sum has order `b ≤ j ≤ 3`, so `M` controls all of them. -/
private theorem heavy_slot_le_M {α M : ℝ} (hM0 : 0 ≤ M) {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
    (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
    (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0:ℝ),
        ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (j+1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j-b) i h z θ))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ 4) {θ z : ℝ}
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z) :
    (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ)^2
      ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ := by
  have hzI : z ∈ Set.Ioi (0:ℝ) := Set.mem_Ioi.mpr hz
  have hj3 : j ≤ 3 := by omega
  have hMx' := hMx i j hi hij z hzI θ hθ
  set F : ℕ → ℝ := fun b => (j.choose b : ℝ)
    * (Work.Elliptic.DzdIter b R z * (Work.Spaces.mixed (j - b) i h z θ
        * Work.Spaces.Wt α z θ)) with hF
  have hkey : Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ
      = ∑ b ∈ Finset.range (j + 1), F b := by
    rw [hMx', Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [hF]; ring
  rw [hkey]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := F)
  have hcard : ((Finset.range (j + 1)).card : ℝ) ≤ 5 := by
    rw [Finset.card_range]; exact_mod_cast (by omega : j + 1 ≤ 5)
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hterm : ∀ b ∈ Finset.range (j + 1),
      F b ^ 2 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) := by
    intro b hb
    have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hb3 : b ≤ 3 := le_trans hbj hj3
    have h1 : ((j.choose b : ℕ) : ℝ) ^ 2 ≤ 256 := by
      have hh := Work.FTS.Nonlinear.RadialProd.choose_le_sixteen (i := j) (b := b) (by omega)
      have h0 : (0:ℝ) ≤ ((j.choose b : ℕ) : ℝ) := Nat.cast_nonneg _
      nlinarith [hh, h0]
    have h2 : (Work.Elliptic.DzdIter b R z)^2 ≤ M := hM b hb3 z hzI
    have h3 : (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ)^2
        ≤ Work.Spaces.HkIntegrand α 4 h z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α 4 h z θ i (j - b) hi (by omega)
    have hprod : (Work.Elliptic.DzdIter b R z)^2
          * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ)^2
        ≤ M * Work.Spaces.HkIntegrand α 4 h z θ :=
      mul_le_mul h2 h3 (sq_nonneg _) hM0
    have hprod2 := mul_le_mul h1 hprod (by positivity) (by norm_num : (0:ℝ) ≤ 256)
    rw [hF]
    have hgoal : ((j.choose b : ℝ) * (Work.Elliptic.DzdIter b R z
            * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ))) ^ 2
        = ((j.choose b : ℝ))^2
          * ((Work.Elliptic.DzdIter b R z)^2
              * (Work.Spaces.mixed (j - b) i h z θ * Work.Spaces.Wt α z θ)^2) := by ring
    rw [hgoal]
    exact hprod2
  have hsum : (∑ b ∈ Finset.range (j + 1), F b ^ 2)
      ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
    calc (∑ b ∈ Finset.range (j + 1), F b ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.range (j + 1)).card : ℝ)
            * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 5 * (256 * (M * Work.Spaces.HkIntegrand α 4 h z θ)) := by
          have h0 : 0 ≤ 256 * (M * Work.Spaces.HkIntegrand α 4 h z θ) :=
            mul_nonneg (by norm_num) (mul_nonneg hM0 hHnn)
          exact mul_le_mul_of_nonneg_right hcard h0
  have hMHnn : 0 ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := mul_nonneg hM0 hHnn
  nlinarith [hcs, hcard, hsum, hMHnn]

/-- **The uniform radial product bound.**  There is a universal constant `C` (independent
of `α` and of the radial bound `M`) with the pointwise `ℋ⁴`-integrand estimate for
`R(z)·h(z,θ)`. -/
theorem hkIntegrand_prod_le_rad_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ {α M : ℝ}, 0 ≤ M → ∀ {R : ℝ → ℝ} {h : ℝ → ℝ → ℝ}
      (hM : ∀ b ≤ 3, ∀ z ∈ Set.Ioi (0:ℝ), (Work.Elliptic.DzdIter b R z)^2 ≤ M)
      (hDz : ∀ i ≤ 4, ∀ z ∈ Set.Ioi (0:ℝ), ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (i+1), (i.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.DzIter (i-b) h z θ))
      (hMx : ∀ i j : ℕ, 1 ≤ i → i + j ≤ 4 → ∀ z ∈ Set.Ioi (0:ℝ),
        ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi/2),
        Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ
          = ∑ b ∈ Finset.range (j+1), (j.choose b : ℝ)
              * (Work.Elliptic.DzdIter b R z * Work.Spaces.mixed (j-b) i h z θ))
      {θ z : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) (hz : 0 < z)
      (hQh : ∀ z' ∈ Set.Ioi (0:ℝ), (h z' θ)^2 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ),
      Work.Spaces.HkIntegrand α 4 (fun z θ => R z * h z θ) z θ
        ≤ C * (M * Work.Spaces.HkIntegrand α 4 h z θ
            + (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
              * Work.FTS.Nonlinear.RadialProd.smE θ
              * Work.FTS.Nonlinear.RadialProd.Qg h θ) := by
  refine ⟨4194304, by norm_num, ?_⟩
  intro α M hM0 R h hM hDz hMx θ z hθ hz hQh
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α 4 h z θ := Work.Spaces.HkIntegrand_nonneg α 4 h z θ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg
      (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hQgnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.Qg h θ :=
    Work.FTS.Nonlinear.RadialProd.Qg_nonneg h θ
  have hSnn : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
      * Work.FTS.Nonlinear.RadialProd.smE θ * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    have h1 : 0 ≤ (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_nonneg (mul_nonneg h1 hsmEnn) hQgnn
  have hMHnn : 0 ≤ M * Work.Spaces.HkIntegrand α 4 h z θ := mul_nonneg hM0 hHnn
  rw [Work.Spaces.HkIntegrand]
  -- the pure `D_z`-sum
  have hZ : (∑ i ∈ Finset.range 5, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
      ≤ 5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ)
        + 65536 * (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
          * Work.FTS.Nonlinear.RadialProd.smE θ * Work.FTS.Nonlinear.RadialProd.Qg h θ := by
    rw [Finset.sum_range_succ (fun i => (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2) 4]
    have hlow : (∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
        ≤ 4 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
      calc (∑ i ∈ Finset.range 4, (Work.Spaces.DzIter i (fun z θ => R z * h z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range 4, (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) :=
            Finset.sum_le_sum fun i hi => light_slot_le_M hM0 hM hDz
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hθ hz
        _ = 4 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    have htop : (Work.Spaces.DzIter 4 (fun z θ => R z * h z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2*θ)) ^ (Work.Spaces.eta/2))) ^ 2
        ≤ 65536 * M * Work.Spaces.HkIntegrand α 4 h z θ
          + 65536 * (Work.Elliptic.DzdIter 4 R z)^2 * (Work.Spaces.w z)^2
            * Work.FTS.Nonlinear.RadialProd.smE θ
            * Work.FTS.Nonlinear.RadialProd.Qg h θ :=
      light_slot_four_le_M hM0 hM hDz hθ hz hQh
    linarith [hlow, htop, hSnn, hMHnn]
  -- the mixed sum
  have hMsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0))
      ≤ 25 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
    have hinner : ∀ i ∈ Finset.range 5,
        (∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
          (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)) ≤ 5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
      intro i hi
      calc (∑ j ∈ Finset.range 5, (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
          ≤ ∑ _j ∈ Finset.range 5, (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
            refine Finset.sum_le_sum fun j hj => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 4
            · rw [ite_eq_left hc]
              exact heavy_slot_le_M hM0 hM hMx hc.1 hc.2 hθ hz
            · rw [ite_eq_right hc]
              exact mul_nonneg (mul_nonneg (by norm_num) hM0) hHnn
        _ = 5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => R z * h z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
        ≤ ∑ _i ∈ Finset.range 5, (5 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ)) :=
          Finset.sum_le_sum hinner
      _ = 25 * (65536 * M * Work.Spaces.HkIntegrand α 4 h z θ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  nlinarith [hZ, hMsum, hMHnn, hSnn]

end Work.FTS.Nonlinear.Pieces.RNP.RNP24
