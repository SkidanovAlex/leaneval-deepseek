import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.EpsConv
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.E5Aux.contDiffOn_zero_mixed_le
import Submission.Work.FTS.StrongEps.E5Aux.exists_dist_sPhi_le
import Submission.Work.FTS.StrongEps.E5Aux.jeps_tendstoUniformlyOn_of_continuousOn_of_shift
import Submission.Work.FTS.StrongEps.E5Aux.abs_Jeps_sub_Jeps_le_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5Aux

set_option autoImplicit false

noncomputable section

open scoped Real Topology
open Filter MeasureTheory Set

/-- **The slots of `J_ε G_ε` converge uniformly to the slots of the limit.**

The proof is the standard mollifier argument, in three pieces:

* `mixed_Jeps` (E1) turns the slot of the mollified profile into the mollified slot:
  `D_z^jD_θ^i (J_ε G_n) = J_ε (D_z^jD_θ^i G_n)` on the open quadrant;
* the slot error `D_z^jD_θ^i G_n - D_z^jD_θ^i f` is estimated by its supremum on a compact
  neighbourhood `S` of `K` which contains all points at which the mollifier samples the profile
  (`abs_Jeps_sub_Jeps_le_of_bound`);
* the remaining error `J_ε (D_z^jD_θ^i f) - D_z^jD_θ^i f` is the peak estimate for the *fixed*
  continuous profile `D_z^jD_θ^i f` (`jeps_tendstoUniformlyOn_of_continuousOn_of_shift`), whose
  uniform version needs the uniform continuity of the shift `sPhi` on `K`
  (`exists_dist_sPhi_le`) and the local uniformity of `K` inside the open quadrant.

The neighbourhood `S` is the closed thickening `cthickening δ₀ K`, with `δ₀` chosen so small that
`S` stays inside the open quadrant: for `ε n ≤ δ₁` (where `δ₁` is the modulus of `sPhi` on `K`
for the tolerance `δ₀`) every sampled point `sPhi p q` lies in `S`, where the slots of the
sequence converge uniformly by `hconv`. -/
theorem mixed_Jeps_tendstoUniformlyOn {ρ : ℝ × ℝ → ℝ}
    (hmoll : Work.FTS.StrongEps.IsMollKernel ρ)
    {α B : ℝ} {G : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ε : ℕ → ℝ}
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n)) Work.FTS.EllipticEst.Q0)
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hεpos : ∀ n : ℕ, 0 < ε n) (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hji : j + i ≤ 4) :
    TendstoUniformlyOn
      (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i
        (Work.FTS.StrongEps.Jeps ρ (ε n) (G n)) p.1 p.2)
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2) Filter.atTop K := by
  classical
  -- the slots `D_z^jD_θ^i G_n`, as functions on `ℝ × ℝ`, are continuous on the open quadrant
  have hcontG : ∀ n : ℕ,
      ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i (G n) q.1 q.2)
        Work.FTS.StrongEps.Quad := fun n =>
    contDiffOn_zero.mp (contDiffOn_zero_mixed_le (G := G n) (n := j + i) (j := j) (i := i)
      (hsm n (j + i)) le_rfl)
  have hcontf : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    contDiffOn_zero.mp (contDiffOn_zero_mixed_le (G := f) (n := 4) (j := j) (i := i)
      hconv.contDiffOn hji)
  -- a compact neighbourhood `S` of `K` inside the open quadrant
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ :=
    hK.exists_cthickening_subset_open Work.FTS.EllipticEst.isOpen_Q0 hKQ
  set S : Set (ℝ × ℝ) := Metric.cthickening δ₀ K with hS
  have hSc : IsCompact S := by
    rw [hS]
    exact hK.cthickening
  have hSQ : S ⊆ Work.FTS.EllipticEst.Q0 := by
    rw [hS]
    exact hδ₀sub
  -- the uniform convergence of the slots on the larger compact set
  have hslot := hconv.conv S hSc hSQ j i hji
  -- the uniform continuity of the shift on `K`
  have hshift : ∀ η > 0, ∃ δ > 0, ∀ p ∈ K, ∀ q : ℝ × ℝ, ‖q‖ ≤ δ →
      dist (Work.FTS.StrongEps.sPhi p.1 p.2 q) p ≤ η :=
    fun η hη => exists_dist_sPhi_le hK hKQ hη
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hshift δ₀ hδ₀pos
  -- the peak estimate for the fixed profile `D_z^jD_θ^i f`
  have hpeak := jeps_tendstoUniformlyOn_of_continuousOn_of_shift hmoll hεpos hε0 hcontf hK hKQ hshift
  rw [Metric.tendstoUniformlyOn_iff] at hslot hpeak ⊢
  intro η hη
  have h2 : 0 < η / 2 := by linarith
  have hA := hslot (η / 2) h2
  have hB := hpeak (η / 2) h2
  have hε1 : ∀ᶠ n : ℕ in Filter.atTop, ε n ≤ δ₁ := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hε0 δ₁ hδ₁pos
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    have h' := abs_lt.mp h
    linarith [h'.2]
  filter_upwards [hA, hB, hε1] with n hnA hnB hnε1
  intro p hpK
  have hpQ : (p.1, p.2) ∈ Work.FTS.StrongEps.Quad := hKQ hpK
  have hz : 0 < p.1 := hpQ.1
  have hth : p.2 ∈ Set.Ioo 0 (π / 2) := hpQ.2
  -- (E1): the slot of the mollified profile is the mollified slot
  have hcomm : Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ (ε n) (G n)) p.1 p.2
      = Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2 :=
    Work.FTS.StrongEps.mixed_Jeps ρ hmoll (hεpos n) (hsm n) hz hth j i
  -- the slot error, estimated on the compact neighbourhood `S`
  have hA' : |Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2
      - Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2| ≤ η / 2 := by
    refine abs_Jeps_sub_Jeps_le_of_bound hmoll hz hth (hεpos n) (hcontG n) hcontf ?_
    intro q hq
    have hxS : Work.FTS.StrongEps.sPhi p.1 p.2 q ∈ S := by
      rw [hS]
      exact Metric.mem_cthickening_of_dist_le _ p δ₀ K hpK
        (hδ₁ p hpK q (le_trans hq hnε1))
    have h := hnA _ hxS
    rw [dist_comm, Real.dist_eq] at h
    exact le_of_lt (by simpa only [Work.FTS.StrongEps.sPhi] using h)
  -- the peak estimate for the limit slot
  have hB' : dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2)
      (Work.Spaces.mixed j i f p.1 p.2) < η / 2 := by
    rw [dist_comm]
    exact hnB p hpK
  -- assemble
  rw [dist_comm]
  calc dist (Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ (ε n) (G n)) p.1 p.2)
        (Work.Spaces.mixed j i f p.1 p.2)
      = dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2)
          (Work.Spaces.mixed j i f p.1 p.2) := by rw [hcomm]
    _ ≤ dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i (G n)) p.1 p.2)
          (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2)
        + dist (Work.FTS.StrongEps.Jeps ρ (ε n) (Work.Spaces.mixed j i f) p.1 p.2)
          (Work.Spaces.mixed j i f p.1 p.2) := dist_triangle _ _ _
    _ < η / 2 + η / 2 := add_lt_add_of_le_of_lt (by rw [Real.dist_eq]; exact hA') hB'
    _ = η := by ring

end

end Work.FTS.StrongEps.E5Aux
