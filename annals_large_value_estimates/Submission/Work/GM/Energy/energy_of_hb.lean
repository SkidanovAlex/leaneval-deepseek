import Mathlib
import Submission.GM.Interfaces
import Submission.Work.GM.Energy.EnergyCore2.assembly_eta
import Submission.Work.GM.Energy.EnergyCore2.energy_le_R_cube
import Submission.Work.GM.Energy.RLocal2.Rfun_local
import Submission.Work.GM.Energy.EnergyCore.gcd_large2

/-! ## GM §11 (Energy): the architecture of the proof of `energy_of_hb`

The target `Submission.GM.EnergyStatement` (GM Proposition 11.1) is proved here as

  `EnergyCore2.assembly_eta hHB EnergyCore2.energy_le_R_cube RLocal2.Rfun_local gcd_large2'`

with the three ingredients

* `EnergyCore2.energy_le_R_cube` — GM (11.4): the additive energy is bounded by the discrete third
  moment `Σ_{n₁,n₂∼N} ‖R(n₁/n₂)‖³` (up to a window error that the assembly absorbs);
* `RLocal2.Rfun_local` — GM (11.7): `R` is locally constant at scale `1/T`;
* `EnergyCore.gcd_large2` — GM (11.9) (large gcd terms, split at `D = N²/T`), in the **`K`-free**
  form: it consumes the discrete second and fourth moment bounds (GM 11.5/11.6, each carrying a
  `T^ε` loss) *at every scale* and returns the large-gcd third-moment bound with an `N^{2ε}` loss.

`EnergyCore2.assembly_eta` is the assembly of Proposition 11.1 and differs from the earlier
`EnergyCore2.assembly` only in its `hL9` slot: the `K`-exposed fourth-moment hypothesis (whose window
cost `(K+1)²` cannot be absorbed — exactly the statement `EnergyCore/gcd_large_K`, which its prover
REFUTED) is replaced by the `K`-free one.  Inside `assembly_eta`

* the fourth moment comes from `EnergyCore2.fourth_moment_Kfree`, which converts the `K`-exposed
  GM (11.6) (`EnergyCore.fourth_moment_Rfun`) into a `K`-free bound with a defect `T^{ε+2η}`, by
  taking the locality window to be the *single* value `K = T^η` (window cost `(K+1)² ≤ 4T^{2η}`) and
  using `m·η ≥ 12`, which absorbs the error term `((M+1)/K^m)²E(W)|W|²` into the main term;
* the assembly then runs with `ε = δ/32`, `η = δ/64`, exponent `ε₂ = ε + 2η = δ/16` and
  `m ≥ 768/δ`, so that `12/m + 4ε₂ ≤ δ` (the `Λ ≤ N^δ` bookkeeping) and `m·η ≥ 12`.

**Import hygiene.**  `EnergyCore/gcd_small.lean` (GM 11.8, used inside `assembly_eta`) imports
`EnergyCore/GcdSetup.lean`, which defines `EnergyCore.card_le_add_one` — the same fully qualified
name as `EnergyCore/Setup.lean`'s lemma (used by the `gcd_large` chain).  The two therefore cannot be
imported into one file, so the `Setup` chain needed by GM 11.9 has been copied *verbatim* (with the
clashing lemma renamed `setup2_card_le_add_one`) as `Setup2`, `sum_Md_le2`, `sum_Md_sq_le2`,
`cs_reduction2`, `gcd_decomp2`, `second_moment_sum_le2`, `fourth_moment_sum_le2`, `assembly_le2`, and
`gcd_large2` (the copy of `gcd_large`).  Nothing else imports them.

For the record, two earlier routes are dead: the sharp *arbitrary*-coefficient unit-window locality
(`LocalConstancy/localize_unit`) is FALSE, and GM (11.9) from the `K`-exposed fourth moment
(`EnergyCore/gcd_large_K`) is not provable (its window cost exceeds the `N^{2ε}` budget). -/

namespace Work.GM.Energy

open Complex Finset
open scoped BigOperators
set_option autoImplicit false

/-- `‖n^{it}‖ = 1` for `n ≥ 1`. -/
lemma norm_natCast_cpow_I_mul {n : ℕ} (hn : 1 ≤ n) (t : ℝ) :
    ‖(n : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := by
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < (n : ℝ))]
  simp

/-- The trivial bound `‖D(t)‖ ≤ C_w Σ_{n∈[N,2N]} ‖b n‖` for the smoothed polynomial. -/
lemma exists_smoothedPoly_norm_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (b : ℕ → ℂ) (t : ℝ),
      ‖Submission.LargeValues.smoothedPoly N b t‖
        ≤ C * ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ := by
  obtain ⟨C, hC0, hC⟩ := Submission.LargeValues.bumpW_deriv_bdd 0
  refine ⟨max C 1, le_trans hC0 (le_max_left C 1), ?_⟩
  intro N hN b t
  have hCmax : ∀ x : ℝ, |Submission.LargeValues.bumpW x| ≤ max C 1 := by
    intro x; exact (hC x).trans (le_max_left _ _)
  calc ‖Submission.LargeValues.smoothedPoly N b t‖
      ≤ ∑ n ∈ Finset.Icc N (2 * N),
          ‖(((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ))) : ℝ) : ℂ) * b n
            * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ := by
        rw [Submission.LargeValues.smoothedPoly]; exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc N (2 * N), max C 1 * ‖b n‖ := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn1 : 1 ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
        have hnat : ‖(n : ℂ) ^ (Complex.I * (t : ℂ))‖ = 1 := norm_natCast_cpow_I_mul hn1 t
        calc ‖(((Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ))) : ℝ) : ℂ) * b n
              * (n : ℂ) ^ (Complex.I * (t : ℂ))‖
            = |Submission.LargeValues.bumpW ((n : ℝ) / (N : ℝ))| * ‖b n‖ := by
              rw [norm_mul, norm_mul, hnat, mul_one]; congr 1; simp
          _ ≤ max C 1 * ‖b n‖ := by
              have := norm_nonneg (b n); nlinarith [hCmax ((n : ℝ) / (N : ℝ))]
    _ = max C 1 * ∑ n ∈ Finset.Icc N (2 * N), ‖b n‖ := by rw [Finset.mul_sum]

/-- Rearrangement of `E ≤ A √E + B` into `E ≤ 2A² + 2B`. -/
lemma le_two_mul_sq_add_two_mul_of_le_mul_sqrt_add {E A B : ℝ} (hE : 0 ≤ E) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h : E ≤ A * Real.sqrt E + B) : E ≤ 2 * A ^ 2 + 2 * B := by
  set x := Real.sqrt E with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg E
  have hx2 : x ^ 2 = E := Real.sq_sqrt hE
  rw [← hx2] at h ⊢
  have h1 : x ≤ A + Real.sqrt B := by
    by_contra hcon
    push Not at hcon
    have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
    have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    nlinarith [sq_nonneg (x - A - Real.sqrt B), sq_nonneg (x - A + Real.sqrt B)]
  have hy0 : 0 ≤ A + Real.sqrt B := le_trans hx0 h1
  calc x ^ 2 ≤ (A + Real.sqrt B) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (add_nonneg hy0 hx0)]
    _ ≤ 2 * A ^ 2 + 2 * B := by
        have hsB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
        have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
        nlinarith [sq_nonneg (A - Real.sqrt B)]

/-- GM §11 (Lemmas 11.3–11.9, Prop 11.1), assuming Heath-Brown; see `Submission/GM/Interfaces.lean`. -/
theorem energy_of_hb (hHB : Submission.GM.HBStatement) : Submission.GM.EnergyStatement :=
  Work.GM.Energy.EnergyCore2.assembly_eta hHB
    Work.GM.Energy.EnergyCore2.energy_le_R_cube
    Work.GM.Energy.RLocal2.Rfun_local
    (by
      -- `EnergyCore.gcd_large2` (the sanitatised copy of `EnergyCore.gcd_large`, whose import chain
      -- avoids the `Setup`/`GcdSetup` clash) has its binders ordered as
      -- `∀ C₂, 0 < C₂ → ∀ C₄, 0 < C₄ → hyp₂ → hyp₄ → ...`, whereas the slot takes
      -- `∀ C₂, 0 < C₂ → hyp₂ → ∀ C₄, 0 < C₄ → hyp₄ → ...`; reorder.
      intro eps2 heps2
      obtain ⟨C9, hC9pos, hC9⟩ := Work.GM.Energy.EnergyCore.gcd_large2 eps2 heps2
      exact ⟨C9, hC9pos,
        fun C2 hC2 hyp2 C4 hC4 hyp4 => hC9 C2 hC2 C4 hC4 hyp2 hyp4⟩)

end Work.GM.Energy
