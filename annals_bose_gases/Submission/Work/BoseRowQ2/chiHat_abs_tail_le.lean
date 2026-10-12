import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.chiHatSq_tsum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseRowQ2

/-- **Auxiliary: the `|χ̂|`-tail over a finite set of dual-lattice indices.**

There is a constant `C ≥ 0` such that for every `R ≥ 1` and every finite set `S` of lattice
indices whose momenta `vec n = 2πn` all have norm at least `R`, the sum of `|χ̂(vec n)|` over `S`
is at most `C/R^101`.

Proof: the first conjunct of the pointwise decay `Work.BoseK15.ChiReg_corpus 52` gives
`|χ̂(p)|·(1+‖p‖²)^52 ≤ Cchi`, i.e. `|χ̂(p)| ≤ Cchi·(1+‖p‖²)^{-52}`; summing over `S` and applying
the lattice tail estimate `Work.BoseK15.sum_inv_one_add_norm_tail 52 101` (legal since
`101 + 3 ≤ 2·52 = 104`) gives the claim with `C = Cchi·Ctail`. -/
theorem chiHat_abs_finset_tail_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (S : Finset (Fin 3 → ℤ)), 1 ≤ R →
      (∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) →
      (∑ n ∈ S, |chiHat (Work.BoseB4.vec n)|) ≤ C / R ^ 101 := by
  obtain ⟨Cchi, hCchi_nn, hChi⟩ := Work.BoseK15.ChiReg_corpus 52
  obtain ⟨Ctail, _hCtail_nn, hCtail⟩ :=
    Work.BoseK15.sum_inv_one_add_norm_tail 52 101 (by norm_num)
  refine ⟨Cchi * Ctail, by positivity, ?_⟩
  intro R S hR hS
  -- the pointwise bound `|χ̂(vec n)| ≤ Cchi·(1+‖vec n‖²)^{-52}`
  have hpoint : ∀ n ∈ S, |chiHat (Work.BoseB4.vec n)|
      ≤ Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
    intro n _hn
    have hD : (0 : ℝ) < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by positivity
    have hle : |chiHat (Work.BoseB4.vec n)|
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52 := by
      rw [le_div_iff₀ hD]
      simpa only [chiHat] using hChi.1 (Work.BoseB4.vec n)
    rw [div_eq_mul_inv] at hle
    exact hle
  calc (∑ n ∈ S, |chiHat (Work.BoseB4.vec n)|)
      ≤ ∑ n ∈ S, Cchi * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ :=
        Finset.sum_le_sum hpoint
    _ = Cchi * ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi * (Ctail / R ^ 101) :=
        mul_le_mul_of_nonneg_left (hCtail R S hR hS) hCchi_nn
    _ = (Cchi * Ctail) / R ^ 101 := by ring

/-- The lattice tail of `|χ̂|`: there is `C ≥ 0` with `Σ_{‖2πn‖ ≥ R} |χ̂(2πn)| ≤ C/R^101` for `R ≥ 1`
(`χ̂(p) = ∫χ(x)cos⟪p,x⟫`, `vec n = 2πn`, `chiHat = Work.BoseK15.corpusBox.hatChi`).
Both pointwise decay (`Work.BoseK15.ChiReg_corpus 52`, whose first conjunct gives
`|χ̂(p)|·(1+‖p‖²)^52 ≤ Cchi`) and the lattice tail
(`Work.BoseK15.sum_inv_one_add_norm_tail 52 101`, legal since `101 + 3 ≤ 2*52`)
are already proved in the corpus; the file `Submission/Work/BoseRowQ2/corpusBox_hatChi_sq_tsum_le.lean`
proves the same statement for squares and is the template. -/
theorem chiHat_abs_tail_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖},
        |Work.BoseRowQ2.chiHat (Work.BoseB4.vec n.val)|) ≤ C / R ^ 101 := by
  obtain ⟨C, hC0, hC⟩ := chiHat_abs_finset_tail_sum
  exact ⟨C, hC0, fun R hR =>
    tsum_subtype_le_of_finset (fun n => abs_nonneg _) hC0 hC R hR⟩

end Work.BoseRowQ2
