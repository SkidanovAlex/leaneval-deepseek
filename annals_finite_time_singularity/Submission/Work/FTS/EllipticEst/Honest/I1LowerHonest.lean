import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.Honest.SharpHardyCosWeight
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `I1LowerHonest` — the `I₁` lower bound of Step 2 of `prop:H2`, honest class

Target: `∃ C > 0, ∀ α F Ψ, Hon α F Ψ → HkMem α 0 (z ∂_z Ψ) → -C α² (A + √A √B) ≤ α² D`
where `A = IP (z∂_zΨ) (z∂_zΨ)`, `B = IP (∂_θθΨ) (∂_θθΨ)`, `D = IP (z²∂_zzΨ) (∂_θθΨ)` and
`IP g h = ∫_z ∫_θ g h w²σ` (`σ = sin(2θ)^{-η}`, `η = 99/100`).

The statement is **true**; it is (after dividing by `α² > 0`) the pure quadratic-form inequality
`D ≥ -C (A + √A √B)`, which does not involve `F` at all.  The route and the verified identities
are recorded in `NOTES_I1LowerHonest.md`; in outline, with `T = z∂_z`, `G = TΨ`, `Bf = Ψ_θθ`,
`P := ‖G_θ‖²_ρ`, `N := ∫∫ G² cos²(2θ) sin(2θ)^{-(2+η)} w²`:

* **z-IBP** (`Honest/SliceIbpZ`) : `⟨T²Ψ, Bf⟩_ρ = -⟨G, T Bf⟩_ρ + ⟨G, c·Bf⟩_ρ`, `c(z) = (3-z)/(1+z)`;
* **θ-IBP** (`Honest/SliceIbpTheta`) : `⟨G, T Bf⟩_ρ = -P + 2η(1+η)N + 2ηA`;
  hence `D = P - 2η(1+η)N - 2ηA + ⟨G,(c-1)Bf⟩_ρ` with `|c-1| ≤ 2`;
* **sharp θ-Hardy** (`SharpHardyCosWeight`) : `2η(1+η) N ≤ (2η/(1+η)) P + C' A`, where
  `2η/(1+η) = 0.99497 < 1`;
* dropping the positive `((1-η)/(1+η)) P` term gives `D ≥ -(C'+2η)(A + √A√B)`.

`I1_lower_of_pieces` below is the (fully proved) algebraic core of that reduction: it is the
last step of any proof of the target, whatever route produced the three inputs.  The remaining
gap is the honest-class justification of the two IBPs — in particular the finiteness of
`P = ‖z∂_z∂_θΨ‖²_ρ`, which is *not* among the hypotheses (`Hon` only gives `HkMem` of
`F`, `z²∂_zzΨ`, `∂_θθΨ`, and the target's own hypothesis adds `HkMem (z∂_zΨ)`).
-/

namespace Work.FTS.EllipticEst.Honest

/-- **Algebraic core of `I1LowerHonest`.**  If `D` dominates `Pp - 2η(1+η)N - 2ηA + X` with
`X ≥ -2√(AB)`, if the sharp `θ`-Hardy bound `2η(1+η)N ≤ (2η/(1+η))Pp + C'A` holds, and if
`Pp ≥ 0`, then `D ≥ -((C'+2η)+2)(A + √(AB))`. -/
theorem I1_lower_of_pieces {η C' A B D Pp N X : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hC' : 0 ≤ C') (hA : 0 ≤ A) (hB : 0 ≤ B) (hP : 0 ≤ Pp)
    (hid : D ≥ Pp - 2 * η * (1 + η) * N - 2 * η * A + X)
    (hX : X ≥ -2 * Real.sqrt (A * B))
    (hN : 2 * η * (1 + η) * N ≤ (2 * η / (1 + η)) * Pp + C' * A) :
    D ≥ -((C' + 2 * η) + 2) * (A + Real.sqrt (A * B)) := by
  have hpos : (0 : ℝ) < 1 + η := by linarith
  have hcoef : 0 ≤ 1 - 2 * η / (1 + η) := by
    rw [sub_nonneg, div_le_one hpos]; linarith
  have hs : 0 ≤ Real.sqrt (A * B) := Real.sqrt_nonneg _
  have h1 : D ≥ (1 - 2 * η / (1 + η)) * Pp - (C' + 2 * η) * A - 2 * Real.sqrt (A * B) := by
    nlinarith [hid, hX, hN]
  have h2 : 0 ≤ (1 - 2 * η / (1 + η)) * Pp := mul_nonneg hcoef hP
  have h3 : (C' + 2 * η) * A + 2 * Real.sqrt (A * B)
      ≤ ((C' + 2 * η) + 2) * (A + Real.sqrt (A * B)) := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ C' + 2 * η) hs, hA]
  linarith

/-- **The pointwise slice rate** (`H2W.Ae.AeDzSliceRate`, the workspace's recorded "single
remaining analytic gap"): almost every `z`-slice of `z∂_zΨ` is bounded by a multiple of
`sin(2θ)`.  It is a *sup-type* statement, hence not an `L²`-consequence of `Hon`; it is consumed
here only as an explicit hypothesis. -/
def SliceRate (Ψ : ℝ → ℝ → ℝ) : Prop :=
  ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |z * Work.Spaces.pz Ψ z θ| ≤ K * Real.sin (2 * θ)

/-- **The bridge from the honest class to the fleet's `AeData` class** (which carries the whole
`SlotA` Chain 1: `I1_z_ibp_open`, `I1_cross_bookkeeping`, `cross_theta_ibp`,
`cw_pair_lower_bound`, all proved).  `AeData` is `Hon` with the two orthogonality conditions only
a.e. in `z` and without the decay field, so the instance is immediate.  It is the glue that lets
the `Hon`-class conditional below consume the `AeData`-class chain. -/
theorem honAeData {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    Work.FTS.EllipticEst.H2W.Ae.AeData α Ψ F :=
  ⟨h.hα, h.hα4, h.eq, h.d0, h.dπ, h.sm, h.memF, h.memA, h.memB,
    Filter.Eventually.of_forall h.orthΨ, Filter.Eventually.of_forall h.orthF⟩

/-- **Conditional form of `I1LowerHonest`, against the slice rate alone** (see
`NOTES_I1LowerHonest.md` §11, ruling (c)): with `SliceRate Ψ` as the single remaining input, the
target's exact inequality holds for `Hon α F Ψ` with `HkMem α 0 (z∂_zΨ)`.  The proof is Chain 1 of
`Honest/MixedHon/NOTES_MixedInterpHon.md` (`SliceRate → SlotA chain → AeI1Lower`), which never
touches the mixed `(1,2)`-term `∫∫ρ(∂_θ²G)²` — so `aeStepI1ZibpMix`'s refuted mixed `HkMem` is
bypassed rather than consumed.  `I1LowerHonest` itself is unchanged. -/
theorem I1LowerHonest_of_sliceRate
    (hRate : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
      SliceRate Ψ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
        Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
        - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
                (fun z θ => z * Work.Spaces.pz Ψ z θ)
            + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
                  (fun z θ => z * Work.Spaces.pz Ψ z θ))
              * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 Ψ)
                  (Work.Spaces.pthIter 2 Ψ)))
        ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            (Work.Spaces.pthIter 2 Ψ) := by sorry

theorem I1LowerHonest : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.Honest.Hon α F Ψ →
      Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz Ψ z θ) →
      - C * α ^ 2 * (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
              (fun z θ => z * Work.Spaces.pz Ψ z θ)
          + Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z * Work.Spaces.pz Ψ z θ)
                (fun z θ => z * Work.Spaces.pz Ψ z θ))
            * Real.sqrt (Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 Ψ)
                (Work.Spaces.pthIter 2 Ψ)))
      ≤ α ^ 2 * Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          (Work.Spaces.pthIter 2 Ψ) := by sorry

end Work.FTS.EllipticEst.Honest
