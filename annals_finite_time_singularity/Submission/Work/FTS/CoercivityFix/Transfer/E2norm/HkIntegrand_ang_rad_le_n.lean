import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer.E2norm

set_option maxHeartbeats 800000

/-- **Pointwise separation of an angular profile and a radial function in the `ℋⁿ`-integrand,
`n ≤ 4`.**

This is the level-`n` (`n ≤ 4`) version of `Work.FTS.NonlinRows.AuxAngRad.HkIntegrand_ang_rad_le`.
The proof is the same pointwise computation: the two separation identities
`dzIter_ang_rad`/`mixed_ang_rad` split every iterate of `z ↦ a θ * r z` into the angular factor
`D_θ^i a` times the radial factor `D_z^j r`, the two squared-weight identities
`light_sq_nn`/`heavy_sq_nn` (valid on all of `Iθ`, including the endpoints where `sin(2θ) = 0`)
convert the weights, and the angular factor is bounded termwise using `ha0` and `ha1`.

The only difference from the `n = 4` statement is that the sums now run over `range (n+1)`
rather than `range 5`; the coefficient `4` is the number of angular orders `i ∈ {1,2,3,4}`, and
the sum over the genuinely occurring orders `1 ≤ i ≤ n` is extended to all four of them
(`(range (n+1)).filter (1 ≤ ·) ⊆ (range 5).filter (1 ≤ ·)`) using the nonnegativity of the
summands. -/
theorem HkIntegrand_ang_rad_le_n {n : ℕ} (hn : n ≤ 4) {α : ℝ} {a : ℝ → ℝ} {r : ℝ → ℝ} {G : ℝ → ℝ}
    {B0 B1 : ℝ}
    (ha0 : ∀ θ ∈ Work.Spaces.Iθ, |a θ| ≤ B0)
    (ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ n → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ| ≤ B1 * G θ)
    {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α n (fun z θ => a θ * r z) z θ
      ≤ (∑ i ∈ Finset.range (n + 1), (Work.Elliptic.DzdIter i r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
  have hsmEnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smE θ :=
    Work.FTS.Nonlinear.RadialProd.smE_nonneg hθ
  have hsmGnn : 0 ≤ Work.FTS.Nonlinear.RadialProd.smG α θ :=
    Work.FTS.Nonlinear.RadialProd.smG_nonneg hθ
  -- ## The angular factor, bounded with the (at most) four available orders
  have hsum_ang : (∑ i ∈ Finset.range (n + 1),
        (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
          * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
      ≤ 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    rw [← Finset.sum_filter]
    have hcnn : 0 ≤ B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hsmGnn
    have hstep : ∀ i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i),
        (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
            * Work.FTS.Nonlinear.RadialProd.smG α θ
          ≤ B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨hin, h1⟩ := hi
      have hb := ha1 i h1 (by omega) θ hθ
      have h3 : (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
          ≤ B1 ^ 2 * (G θ) ^ 2 := by
        have h4 := pow_le_pow_left₀ (abs_nonneg _) hb 2
        rw [sq_abs, mul_pow] at h4
        exact h4
      exact mul_le_mul_of_nonneg_right h3 hsmGnn
    calc ∑ i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i),
            (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ
        ≤ ∑ _i ∈ (Finset.range (n + 1)).filter (fun i => 1 ≤ i),
            B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ :=
          Finset.sum_le_sum hstep
      _ ≤ ∑ _i ∈ (Finset.range 5).filter (fun i => 1 ≤ i),
            B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hcnn)
          intro i hi
          rw [Finset.mem_filter, Finset.mem_range] at hi ⊢
          exact ⟨by omega, hi.2⟩
      _ = 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
          rw [show (Finset.range 5).filter (fun i => 1 ≤ i) = Finset.Icc 1 4 from by decide,
            Finset.sum_const, Nat.card_Icc]
          norm_num
          ring
  -- ## The pure `D_z`-slots
  have hpure : (∑ i ∈ Finset.range (n + 1),
        (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.FTS.Nonlinear.Pieces.dzIter_ang_rad,
      show (a θ * Work.Elliptic.DzdIter i r z
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = ((a θ * Work.Elliptic.DzdIter i r z)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        from by ring,
      Work.FTS.NonlinRows.AuxAngRad.light_sq_nn _ z θ hs]
    ring
  -- ## The mixed slots
  have hmix : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
        if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ (∑ i ∈ Finset.range (n + 1),
            (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
          * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    have hterm2 : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (n + 1),
        (if 1 ≤ i ∧ i + j ≤ n then
          (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
        ≤ (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
            * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      intro i hi j hj
      by_cases h1 : 1 ≤ i
      · by_cases h2 : i + j ≤ n
        · rw [if_pos ⟨h1, h2⟩, if_pos h1]
          rw [Work.FTS.Nonlinear.Pieces.mixed_ang_rad,
            show (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
                  * Work.Elliptic.DzdIter j r z * Work.Spaces.Wt α z θ) ^ 2
                = ((Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ
                    * Work.Elliptic.DzdIter j r z) * Work.Spaces.Wt α z θ) ^ 2
              from by ring,
            Work.FTS.NonlinRows.AuxAngRad.heavy_sq_nn α _ z θ hs]
          exact le_of_eq (by ring)
        · rw [if_neg (fun h => h2 h.2), if_pos h1]
          exact mul_nonneg (mul_nonneg (sq_nonneg _) hsmGnn)
            (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · rw [if_neg (fun h => h1 h.1), if_neg h1]
        simp
    calc (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), if 1 ≤ i ∧ i + j ≤ n then
            (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
        ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0)
              * ((Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm2 i hi j hj
      _ = (∑ i ∈ Finset.range (n + 1),
              (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
            * (∑ j ∈ Finset.range (n + 1),
                (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
          (Finset.sum_mul_sum _ _ _ _).symm
  -- ## Assembly
  have hRnn : 0 ≤ ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hM : (a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + (∑ i ∈ Finset.range (n + 1),
            (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
              * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
      ≤ B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
        + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ := by
    refine add_le_add ?_ hsum_ang
    have h2 : (a θ) ^ 2 ≤ B0 ^ 2 := by
      have h3 := pow_le_pow_left₀ (abs_nonneg (a θ)) (ha0 θ hθ) 2
      rwa [sq_abs] at h3
    exact mul_le_mul_of_nonneg_right h2 hsmEnn
  calc Work.Spaces.HkIntegrand α n (fun z θ => a θ * r z) z θ
      = (∑ i ∈ Finset.range (n + 1), (Work.Spaces.DzIter i (fun z θ => a θ * r z) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
            if 1 ≤ i ∧ i + j ≤ n then
              (Work.Spaces.mixed j i (fun z θ => a θ * r z) z θ
                * Work.Spaces.Wt α z θ) ^ 2
            else 0) := by
          rw [Work.Spaces.HkIntegrand]
    _ ≤ (a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
          * (∑ j ∈ Finset.range (n + 1),
              (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          + (∑ i ∈ Finset.range (n + 1),
              (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))
            * (∑ j ∈ Finset.range (n + 1),
                (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
        add_le_add (le_of_eq hpure) hmix
    _ = (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * ((a θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + (∑ i ∈ Finset.range (n + 1),
                  (if 1 ≤ i then (Work.Spaces.DthIter i (fun _ (θ' : ℝ) => a θ') 0 θ) ^ 2
                    * Work.FTS.Nonlinear.RadialProd.smG α θ else 0))) := by
        rw [mul_add]
        congr 1
        · exact mul_comm _ _
        · exact mul_comm _ _
    _ ≤ (∑ j ∈ Finset.range (n + 1),
            (Work.Elliptic.DzdIter j r z) ^ 2 * (Work.Spaces.w z) ^ 2)
          * (B0 ^ 2 * Work.FTS.Nonlinear.RadialProd.smE θ
              + 4 * B1 ^ 2 * (G θ) ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) :=
        mul_le_mul_of_nonneg_left hM hRnn

end Work.FTS.CoercivityFix.Transfer.E2norm
