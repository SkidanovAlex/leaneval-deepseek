import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.T2Defs
import Submission.Work.FTS.H2.T2EasyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## Auxiliary facts for `HeasyBlocksId`

The identity is purely combinatorial: expanding `Heasy = H4PairInt - Hhard` and
splitting off the "top" (`D_z⁴` and `i + j = 4`) slots leaves exactly the block
products of `EasyZ · GblkZ` and `EasyM · GblkM`.  The only analytic input is the two
`rpow` identities squaring the weights of the flat pairing, which need
`sin(2θ) > 0`, i.e. precisely the hypothesis `θ ∈ (0, π/2)`.
-/

/-- `sin (2θ) ≥ 0` for `θ ∈ (0, π/2)` (indeed `sin (2θ) > 0` there). -/
theorem hbi_sin_two_nonneg {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- `Thard g k = D_z^{4-k} D_θ^k g`, uniformly in `k : Fin 5`. -/
theorem hbi_Thard_eq_mixed (g : ℝ → ℝ → ℝ) (k : Fin 5) :
    Thard g k = fun z θ => Work.Spaces.mixed (4 - k.val) k.val g z θ := by
  fin_cases k <;> rfl

/-- `sghard α k = sin(2θ)^{-η}` for `k = 0` and `sin(2θ)^{-γ}` for `k ≠ 0`. -/
theorem hbi_sghard_eq (α : ℝ) (k : Fin 5) :
    sghard α k = fun θ => (Real.sin (2 * θ)) ^
      (-(if k.val = 0 then Work.Spaces.eta else Work.Spaces.gam α)) := by
  fin_cases k <;> rfl

/-- `Whz z θ ^ 2 = w z ^ 2 · sin(2θ)^{-η}` for `sin(2θ) ≥ 0`. -/
theorem hbi_Whz_sq (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    Whz z θ ^ 2 = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
  have h1 : Whz z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [Whz_eq, div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta / 2)]
  have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    rw [pow_two, ← Real.rpow_add' hs (by rw [Work.Spaces.eta]; norm_num)]
    congr 1
    ring
  rw [h1, mul_pow, h2]

/-- `Wm α z θ ^ 2 = w z ^ 2 · sin(2θ)^{-γ}` for `sin(2θ) ≥ 0`. -/
theorem hbi_Wm_sq (α : ℝ) (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    Wm α z θ ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have h1 : Wm α z θ
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) := by
    rw [Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  rcases eq_or_ne (Work.Spaces.gam α) 0 with hg | hg
  · have hy : -(Work.Spaces.gam α / 2) = 0 := by rw [hg]; ring
    have hz : -(Work.Spaces.gam α) = 0 := by rw [hg]; ring
    rw [h1, hy, hz, Real.rpow_zero]
    ring
  · have h2 : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [pow_two, ← Real.rpow_add' hs (by
        intro h
        exact hg (by linarith))]
      congr 1
      ring
    rw [h1, mul_pow, h2]

/-- The "easy part" `Heasy α f g = H4PairInt α (f · D_z g) g − Hhard α f g` of the
`D_z`-transport pairing decomposes into the block products by which `EasyZ`, `EasyM`,
`GblkZ`, `GblkM` are defined.  For `θ ∈ (0, π/2)` this is pure algebra (no differentiability
of `f`, `g` is needed).  Expanding `H4PairInt α (f · D_z g) g` gives the termwise identity
`(D^i(f D_z g)·Whz)(D^i g·Whz) = EasyZ f g i · GblkZ g i` for `i ≤ 3`, and for `i = 4`
`(D^4(fD_zg)·Whz)(D^4g·Whz) = EasyZ f g 4 · GblkZ g 4 + f·D_z^5 g·D^4 g·Whz²` since
`EasyZ f g 4 = (D^4(fD_zg) − f·D_z^5 g)·Whz`; likewise for the mixed blocks, where for
`i + j = 4` the block `EasyM α f g j i` has `f·D_z(mixed j i g)` subtracted.  The five "hard"
summands of `Hhard` are exactly these correction terms: with `Thard g k = mixed (4-k) k g`
and `z·∂_z Θ = D_z Θ`,
`Hhard = f·z·∑_k ∂_z(Thard g k)·Thard g k·w²·sghard α k`
`= f·D_z^5 g·D^4 g·Whz² + ∑_{k=1}^4 f·D_z(mixed (4-k) k g)·mixed (4-k) k g·Wm²`,
using the weight identities `Whz z θ ^ 2 = w z ^ 2 * sin(2θ)^(-η)` and
`Wm α z θ ^ 2 = w z ^ 2 * sin(2θ)^(-γ)`, which hold for `θ ∈ (0,π/2)` because there
`sin(2θ) > 0` (`Real.rpow_add`).  The statement is in namespace `Work.FTS.H2`, with
`Heasy`, `EasyZ`, `GblkZ`, `EasyM`, `GblkM` all defined in `Submission/Work/FTS/H2/`. -/
theorem HeasyBlocksId (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.H2.Heasy α f g z θ =
      (∑ i ∈ Finset.range 5, Work.FTS.H2.EasyZ f g i z θ * Work.FTS.H2.GblkZ g i z θ)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              Work.FTS.H2.EasyM α f g j i z θ * Work.FTS.H2.GblkM α g j i z θ else 0) := by
  have hs : 0 ≤ Real.sin (2 * θ) := hbi_sin_two_nonneg hθ
  have hWhz := hbi_Whz_sq z θ hs
  have hWm := hbi_Wm_sq α z θ hs
  -- Normal form of `Hhard`: a sum over `range 5` of the five order-`5` slots, reindexed
  -- from `Fin 5` to `ℕ`.
  set fZ : ℕ → ℝ := fun i => Work.Spaces.pz (Work.Spaces.mixed (4 - i) i g) z θ
      * Work.Spaces.mixed (4 - i) i g z θ * (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(if i = 0 then Work.Spaces.eta else Work.Spaces.gam α)) with hfZ
  have hsum : (∑ k : Fin 5, Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
        * (Work.Spaces.w z) ^ 2 * sghard α k θ)
      = ∑ i ∈ Finset.range 5, fZ i := by
    rw [show (∑ k : Fin 5, Work.Spaces.pz (Thard g k) z θ * Thard g k z θ
          * (Work.Spaces.w z) ^ 2 * sghard α k θ) = ∑ k : Fin 5, fZ k.val from
        Finset.sum_congr rfl (fun k _ => by
          rw [hfZ, hbi_Thard_eq_mixed g k, hbi_sghard_eq α k])]
    exact Fin.sum_univ_eq_sum_range fZ 5
  have hhard : Hhard α f g z θ = f z θ * z * ∑ i ∈ Finset.range 5, fZ i := by
    unfold Hhard
    rw [hsum]
  rw [Heasy, hhard]
  -- Expand every sum into its finitely many explicit terms.
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hfZ, H4PairInt, EasyZ, EasyM,
    GblkZ, GblkM, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_succ,
    Work.Spaces.DzIter_zero, Work.Spaces.Dz]
  -- Reduce the (now ground) `if`-conditions and the `beta`-redexes.
  dsimp
  -- The remaining goal is a polynomial identity in the atoms, given the two weight squares.
  ring_nf
  rw [hWhz, hWm]
  ring

end Work.FTS.H2
