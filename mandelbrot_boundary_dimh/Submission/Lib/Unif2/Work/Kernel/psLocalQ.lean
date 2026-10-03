import Mathlib
import Submission.Lib.Unif2.Work.Kernel.GreenCover
import Submission.Lib.Unif2.Work.Drive.pairIntegrable_transfer
import Submission.Lib.Unif2.Work.Drive.greenEnergyQ0

/-!
# A *working* copy of `Work.Kernel.pairing_harmonic_zero_kernel`

The file `Submission/Work/Kernel/pairing_harmonic_zero_kernel.lean` does not compile at the moment: a
refactor moved four lemmas from the namespace `Work.Drive` into `Work.Drive.GreenRung` and this
consumer was not updated.  To stay independent of that file this module carries a byte-for-byte copy
of its proof, with the four names qualified and **every declaration renamed** by the suffix `PS` (so
that the two modules can be imported together without a name clash).

The two lemmas exported for the use of `Work.Kernel.pairing_pole_smooth` are

* `Work.Kernel.psPairIntegrable_congr_weight`, and
* `Work.Kernel.psPairingHarmonicZeroKernel`.
-/

open MeasureTheory Set Filter
open scoped Manifold Topology Gradient

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Kernel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]

/-- **Integrability locality in the weight** (self-contained version, so that this module does not
depend on the work-in-progress pairing files). -/
theorem psPairIntegrable_congr_weight {x : X} {ρ σ : ℝ} {W W' f g : X → ℝ}
    (htgt : Metric.ball ((chartAt ℂ x) x) ρ ⊆ (chartAt ℂ x).target) (hσρ : σ < ρ)
    (h : ∀ y ∈ tsupport g, W y = W' y) :
    Work.Drive.PairIntegrable x ρ σ W f g → Work.Drive.PairIntegrable x ρ σ W' f g := by
  intro hh
  rw [Work.Drive.PairIntegrable] at hh ⊢
  refine hh.congr (Filter.Eventually.of_forall fun z => ?_)
  dsimp only
  by_cases hb : z ∈ Metric.ball ((chartAt ℂ x) x) σ
  · by_cases hz : z ∈ tsupport (Work.Drive.clampedPullback x ρ g)
    · have hzρ : z ∈ Metric.ball ((chartAt ℂ x) x) ρ :=
        Metric.ball_subset_ball (le_of_lt hσρ) hb
      have hy : (chartAt ℂ x).symm z ∈ tsupport g :=
        Work.Drive.GreenRung.symm_mem_tsupport_of_mem_tsupport_clampedPullback htgt (Metric.mem_ball.mp hzρ) hz
      simp only [Work.Drive.clampedPullback_apply_of_mem hb, h _ hy]
    · rw [Work.Analysis.Harmonic.gradient_eq_zero_of_notMem_tsupport hz, inner_zero_right,
        mul_zero, mul_zero]
  · simp only [Work.Drive.clampedPullback_eq_zero_of_notMem_ball hb, zero_mul]

namespace GreenCover

variable {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : GreenCover ι Ω K a b)

/-- The overlap of the chart balls of the charts at `y i` and `y j`, with the two poles removed. -/
def regionPS (i j : ι) : Set X :=
  (((chartAt ℂ (E.y i)).source ∩
      (chartAt ℂ (E.y i)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i))
    ∩ ((chartAt ℂ (E.y j)).source ∩
      (chartAt ℂ (E.y j)) ⁻¹' Metric.ball ((chartAt ℂ (E.y j)) (E.y j)) (E.ρ j)))
    \ ({a, b} : Set X)

theorem region_subset_source_leftPS (i j : ι) :
    E.regionPS i j ⊆ (chartAt ℂ (E.y i)).source :=
  fun x hx => hx.1.1.1

theorem region_subset_source_rightPS (i j : ι) :
    E.regionPS i j ⊆ (chartAt ℂ (E.y j)).source :=
  fun x hx => hx.1.2.1

/-- The overlap of the two `ρ`-balls lies in `Ω` (via the source-aware ball field). -/
theorem region_subset_ΩPS (i j : ι) : E.regionPS i j ⊆ Ω :=
  fun x hx => E.hballΩ i ⟨hx.1.1.1, hx.1.1.2⟩

theorem isOpen_regionPS (i j : ι) : IsOpen (E.regionPS i j) := by
  have h1 : IsOpen ((chartAt ℂ (E.y i)).source ∩
      (chartAt ℂ (E.y i)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i)) :=
    (chartAt ℂ (E.y i)).continuousOn.isOpen_inter_preimage (chartAt ℂ (E.y i)).open_source
      Metric.isOpen_ball
  have h2 : IsOpen ((chartAt ℂ (E.y j)).source ∩
      (chartAt ℂ (E.y j)) ⁻¹' Metric.ball ((chartAt ℂ (E.y j)) (E.y j)) (E.ρ j)) :=
    (chartAt ℂ (E.y j)).continuousOn.isOpen_inter_preimage (chartAt ℂ (E.y j)).open_source
      Metric.isOpen_ball
  have hcl : IsClosed ({a, b} : Set X) := ((Set.finite_singleton b).insert a).isClosed
  rw [regionPS]
  exact ((h1.inter h2).sdiff hcl)

/-- For `i ≠ j` the product `ψ i * β j` vanishes at the pole `a`. -/
theorem notMem_a_tsupport_mulPS (i j : ι) (hij : i ≠ j) : a ∉ tsupport (E.ψ i * E.β j) := by
  intro hcon
  have hmem_i := E.hψsupp i (tsupport_mul_subset_left (f := E.ψ i) (g := E.β j) hcon)
  have hmem_j := E.hβsupp j (tsupport_mul_subset_right (f := E.ψ i) (g := E.β j) hcon)
  have h1 : a ∈ Submission.chartClosedBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i))
      (E.σ i) :=
    ⟨hmem_i.1, Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_of_lt (E.hsσ i)) hmem_i.2)⟩
  have h2 : a ∈ Submission.chartClosedBall (chartAt ℂ (E.y j)) ((chartAt ℂ (E.y j)) (E.y j))
      (E.σ j) :=
    ⟨hmem_j.1, Metric.ball_subset_closedBall hmem_j.2⟩
  have hi : i = E.ia := by
    by_contra hne
    exact E.ha_nmem i hne h1
  have hj : j = E.ia := by
    by_contra hne
    exact E.ha_nmem j hne h2
  exact hij (hi.trans hj.symm)

/-- For `i ≠ j` the product `ψ i * β j` vanishes at the pole `b`. -/
theorem notMem_b_tsupport_mulPS (i j : ι) (hij : i ≠ j) : b ∉ tsupport (E.ψ i * E.β j) := by
  intro hcon
  have hmem_i := E.hψsupp i (tsupport_mul_subset_left (f := E.ψ i) (g := E.β j) hcon)
  have hmem_j := E.hβsupp j (tsupport_mul_subset_right (f := E.ψ i) (g := E.β j) hcon)
  have h1 : b ∈ Submission.chartClosedBall (chartAt ℂ (E.y i)) ((chartAt ℂ (E.y i)) (E.y i))
      (E.σ i) :=
    ⟨hmem_i.1, Metric.ball_subset_closedBall (Metric.ball_subset_ball (le_of_lt (E.hsσ i)) hmem_i.2)⟩
  have h2 : b ∈ Submission.chartClosedBall (chartAt ℂ (E.y j)) ((chartAt ℂ (E.y j)) (E.y j))
      (E.σ j) :=
    ⟨hmem_j.1, Metric.ball_subset_closedBall hmem_j.2⟩
  have hi : i = E.ib := by
    by_contra hne
    exact E.hb_nmem i hne h1
  have hj : j = E.ib := by
    by_contra hne
    exact E.hb_nmem j hne h2
  exact hij (hi.trans hj.symm)

theorem tsupport_mul_subset_regionPS (i j : ι) (hij : i ≠ j) :
    tsupport (E.ψ i * E.β j) ⊆ E.regionPS i j := by
  intro x hx
  have hxψ : x ∈ tsupport (E.ψ i) := tsupport_mul_subset_left (f := E.ψ i) (g := E.β j) hx
  have hxβ : x ∈ tsupport (E.β j) := tsupport_mul_subset_right (f := E.ψ i) (g := E.β j) hx
  obtain ⟨hsrc_i, hball_i⟩ := E.hψsupp i hxψ
  obtain ⟨hsrc_j, hball_j⟩ := E.hβsupp j hxβ
  have h1 : (chartAt ℂ (E.y i)) x ∈ Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.ρ i) :=
    Metric.ball_subset_ball (le_of_lt (lt_trans (E.hsσ i) (E.hσρ i))) hball_i
  have h2 : (chartAt ℂ (E.y j)) x ∈ Metric.ball ((chartAt ℂ (E.y j)) (E.y j)) (E.ρ j) :=
    Metric.ball_subset_ball (le_of_lt (E.hσρ j)) hball_j
  refine ⟨⟨⟨hsrc_i, h1⟩, hsrc_j, h2⟩, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨fun hxa => E.notMem_a_tsupport_mulPS i j hij (hxa ▸ hx),
    fun hxb => E.notMem_b_tsupport_mulPS i j hij (hxb ▸ hx)⟩

theorem tsupport_mul_subset_ball_leftPS (i j : ι) :
    tsupport (E.ψ i * E.β j) ⊆
      (chartAt ℂ (E.y i)) ⁻¹' Metric.ball ((chartAt ℂ (E.y i)) (E.y i)) (E.σ i) :=
  fun x hx =>
    Metric.ball_subset_ball (le_of_lt (E.hsσ i))
      ((E.hψsupp i (tsupport_mul_subset_left (f := E.ψ i) (g := E.β j) hx)).2)

theorem tsupport_mul_subset_ball_rightPS (i j : ι) :
    tsupport (E.ψ i * E.β j) ⊆
      (chartAt ℂ (E.y j)) ⁻¹' Metric.ball ((chartAt ℂ (E.y j)) (E.y j)) (E.σ j) :=
  fun x hx => (E.hβsupp j (tsupport_mul_subset_right (f := E.ψ i) (g := E.β j) hx)).2

/-- `β k` is `1` on the support of `ψ k * φ`. -/
theorem β_eq_one_of_memPS {k : ι} {φ : X → ℝ} {x : X}
    (hx : x ∈ tsupport (E.ψ k * φ)) : E.β k x = 1 := by
  obtain ⟨hsrc, hball⟩ := E.hψsupp k (tsupport_mul_subset_left (f := E.ψ k) (g := φ) hx)
  exact E.hβone k x ⟨hsrc, Metric.ball_subset_closedBall hball⟩

/-- `∑ i, ψ i = 1` on the support of `ψ k * φ`, when the latter lies in `K`. -/
theorem sum_ψ_eq_one_of_memPS {k : ι} {φ : X → ℝ} {x : X} (hφK : tsupport φ ⊆ K)
    (hx : x ∈ tsupport (E.ψ k * φ)) : ∑ i, E.ψ i x = 1 :=
  E.hsum x (hφK (tsupport_mul_subset_right (f := E.ψ k) (g := φ) hx))

/-- The product `∑ i, ψ i * β k` equals `(∑ i, ψ i) * β k`. -/
theorem sum_ψ_mul_β_eqPS (k : ι) : (∑ i, E.ψ i * E.β k) = (∑ i, E.ψ i) * E.β k := by
  funext x
  simp only [Finset.sum_apply, Pi.mul_apply, Finset.sum_mul]

end GreenCover

namespace GreenCover

section Transfer

variable {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X} (E : GreenCover ι Ω K a b)
variable [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The differentiability data needed to transfer the `(i,j)`-term to the chart at `E.y j`. -/
theorem region_differentiablePS (i j : ι) {f φ : X → ℝ}
    (hf : Work.Drive.ChartDiff (chartAt ℂ (E.y j)) f (Ω \ ({a, b} : Set X)))
    (hψdiff : Work.Drive.ChartDiff (chartAt ℂ (E.y j)) (E.ψ j) Ω)
    (hφdiff : Work.Drive.ChartDiff (chartAt ℂ (E.y j)) φ Ω) :
    (∀ y ∈ E.regionPS i j, DifferentiableAt ℝ
        (fun w : ℂ => f ((chartAt ℂ (E.y j)).symm w)) ((chartAt ℂ (E.y j)) y)) ∧
      (∀ y ∈ E.regionPS i j, DifferentiableAt ℝ
        (fun w : ℂ => (E.ψ j * φ) ((chartAt ℂ (E.y j)).symm w)) ((chartAt ℂ (E.y j)) y)) := by
  have hsrc : ∀ y ∈ E.regionPS i j, y ∈ (chartAt ℂ (E.y j)).source :=
    E.region_subset_source_rightPS i j
  have hΩ : ∀ y ∈ E.regionPS i j, y ∈ Ω := E.region_subset_ΩPS i j
  have hne : ∀ y ∈ E.regionPS i j, y ∉ ({a, b} : Set X) := fun y hy => hy.2
  constructor
  · intro y hy
    exact hf y ⟨⟨hΩ y hy, hne y hy⟩, hsrc y hy⟩
  · intro y hy
    have h1 := hψdiff y ⟨hΩ y hy, hsrc y hy⟩
    have h2 := hφdiff y ⟨hΩ y hy, hsrc y hy⟩
    exact h1.mul h2

/-- **Chart transfer of the `(i,j)`-term of the pairing.** -/
theorem pairTerm_transfer_regionPS (i j : ι) (hij : i ≠ j) {f φ : X → ℝ}
    (hfdiff : Work.Drive.ChartDiff (chartAt ℂ (E.y j)) f (Ω \ ({a, b} : Set X)))
    (hψdiff : Work.Drive.ChartDiff (chartAt ℂ (E.y j)) (E.ψ j) Ω)
    (hφdiff : Work.Drive.ChartDiff (chartAt ℂ (E.y j)) φ Ω) :
    Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i * E.β j) f (E.ψ j * φ)
      = Work.Drive.pairTerm (E.y j) (E.ρ j) (E.σ j) (E.ψ i * E.β j) f (E.ψ j * φ) := by
  obtain ⟨hf₂, hg₂⟩ := E.region_differentiablePS i j hfdiff hψdiff hφdiff
  exact Work.Drive.pairTerm_transfer (x := E.y i) (x' := E.y j) (ρ := E.ρ i) (σ := E.σ i)
    (ρ' := E.ρ j) (σ' := E.σ j) (V := E.regionPS i j) (E.isOpen_regionPS i j)
    (E.region_subset_source_leftPS i j) (E.region_subset_source_rightPS i j)
    (E.htgt i) (E.htgt j) (E.tsupport_mul_subset_regionPS i j hij)
    (E.hσρ i) (E.hσρ j) (E.tsupport_mul_subset_ball_leftPS i j)
    (E.tsupport_mul_subset_ball_rightPS i j) hf₂ hg₂

/-- **Integrability transfer of the `(i,j)`-term of the pairing.** -/
theorem pairIntegrable_transfer_regionPS (i j : ι) (hij : i ≠ j) {f φ : X → ℝ}
    (hf₂ : ∀ y ∈ E.regionPS i j, DifferentiableAt ℝ
        (fun w : ℂ => f ((chartAt ℂ (E.y j)).symm w)) ((chartAt ℂ (E.y j)) y))
    (hg₂ : ∀ y ∈ E.regionPS i j, DifferentiableAt ℝ
        (fun w : ℂ => (E.ψ j * φ) ((chartAt ℂ (E.y j)).symm w)) ((chartAt ℂ (E.y j)) y))
    (h : Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i * E.β j) f (E.ψ j * φ)) :
    Work.Drive.PairIntegrable (E.y j) (E.ρ j) (E.σ j) (E.ψ i * E.β j) f (E.ψ j * φ) :=
  Work.Drive.pairIntegrable_transfer (x := E.y i) (x' := E.y j) (ρ := E.ρ i) (σ := E.σ i)
    (ρ' := E.ρ j) (σ' := E.σ j) (V := E.regionPS i j) (E.isOpen_regionPS i j)
    (E.region_subset_source_leftPS i j) (E.region_subset_source_rightPS i j)
    (E.htgt i) (E.htgt j) (E.tsupport_mul_subset_regionPS i j hij)
    (E.hσρ i) (E.hσρ j) (E.tsupport_mul_subset_ball_leftPS i j)
    (E.tsupport_mul_subset_ball_rightPS i j) hf₂ hg₂ h

/-- **The chart-local Green identity for the `j`-th chart of the cover.** -/
theorem pairTerm_weight_one_eq_zeroPS (j : ι) {f φ : X → ℝ}
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hφc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (φ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hharm : ∀ x ∈ tsupport φ, Submission.HarmonicOnXAt f x) :
    Work.Drive.pairTerm (E.y j) (E.ρ j) (E.σ j) (fun _ => (1 : ℝ)) f (E.ψ j * φ) = 0 :=
  Work.Drive.GreenRung.integral_inner_gradient_eq_zero_weight_one (x₀ := E.y j) (h := f) (φ := E.ψ j * φ)
    (ρ := E.ρ j) (σ := E.σ j)
    (le_of_lt (lt_trans (E.hspos j) (E.hsσ j))) (E.hσρ j) (E.htgt j)
    (fun x hx => by
      have h1 := hψc1 j j x hx
      have h2 := hφc1 j x hx
      exact h1.mul h2)
    (fun x hx => Metric.ball_subset_ball (le_of_lt (E.hsσ j))
      ((E.hψsupp j (tsupport_mul_subset_left (f := E.ψ j) (g := φ) hx)).2))
    (fun y hy => hharm y (tsupport_mul_subset_right (f := E.ψ j) (g := φ) hy))

end Transfer

end GreenCover

/-- **The harmonic case of the pole identity on the source-aware cover.**

If `f` is harmonic on the topological support of `φ` then the chart-wise Dirichlet pairing
`∑ᵢ pairTerm (y i) (ρ i) (σ i) (ψ i) f φ` vanishes.  The two `C¹` requirements on the weights that
the (refuted) `Work.Drive.GreenCover` carried as fields are explicit hypotheses here. -/
theorem psPairingHarmonicZeroKernel {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {ι : Type*} [Fintype ι] {Ω K : Set X} {a b : X}
    (E : GreenCover ι Ω K a b) {f φ : X → ℝ}
    (hφdiff : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) φ Ω)
    (hφc1 : ∀ k, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 (φ ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hφK : tsupport φ ⊆ K) (hφΩ : tsupport φ ⊆ Ω)
    (hharm : ∀ x ∈ tsupport φ, Submission.HarmonicOnXAt f x)
    (hf : ∀ k, Work.Drive.ChartDiff (chartAt ℂ (E.y k)) f (Ω \ ({a, b} : Set X)))
    (hψc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.ψ i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hβc1 : ∀ k i, ∀ x ∈ (chartAt ℂ (E.y k)).source,
      ContDiffAt ℝ 1 ((E.β i) ∘ (chartAt ℂ (E.y k)).symm) ((chartAt ℂ (E.y k)) x))
    (hint1 : ∀ i k, ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      DifferentiableAt ℝ (Work.Drive.clampedPullback (E.y i) (E.ρ i) (E.ψ k * φ)) z)
    (hint2 : ∀ i k, Work.Drive.PairIntegrable (E.y i) (E.ρ i) (E.σ i) (E.ψ i * E.β k) f (E.ψ k * φ)) :
    Work.Drive.pairing E.y E.ρ E.σ E.ψ f φ = 0 := by
  classical
  -- The partition of unity: `∑ j, ψ j * φ = φ`.
  have hφsum : (∑ j : ι, E.ψ j * φ) = φ := by
    funext x
    by_cases hx : φ x = 0
    · simp only [Finset.sum_apply, Pi.mul_apply, hx, mul_zero, Finset.sum_const, smul_zero]
    · have hxK : x ∈ K := hφK (subset_tsupport φ (Function.mem_support.mpr hx))
      have h1 : ∑ j, E.ψ j x = 1 := E.hsum x hxK
      calc (∑ j : ι, E.ψ j * φ) x = ∑ j, E.ψ j x * φ x := by
            simp only [Finset.sum_apply, Pi.mul_apply]
        _ = (∑ j, E.ψ j x) * φ x := (Finset.sum_mul (Finset.univ) (fun j => E.ψ j x) (φ x)).symm
        _ = 1 * φ x := by rw [h1]
        _ = φ x := one_mul _
  -- Replace `φ` by the sum.
  have hpair : Work.Drive.pairing E.y E.ρ E.σ E.ψ f φ
      = Work.Drive.pairing E.y E.ρ E.σ E.ψ f (∑ j, E.ψ j * φ) := by
    simp only [Work.Drive.pairing]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Work.Drive.pairTerm_congr (fun z hz => rfl) (fun z hz => ?_)
    rw [hφsum]
  -- Linearity in the third argument.
  have hlin : Work.Drive.pairing E.y E.ρ E.σ E.ψ f (∑ j, E.ψ j * φ)
      = ∑ j, Work.Drive.pairing E.y E.ρ E.σ E.ψ f (E.ψ j * φ) :=
    Work.Drive.pairing_finset_sum (χ := fun j => E.ψ j * φ) (fun i j => hint1 i j)
      (fun i j => Work.Kernel.psPairIntegrable_congr_weight (E.htgt i) (E.hσρ i)
        (fun y hy => by rw [Pi.mul_apply, E.β_eq_one_of_memPS hy, mul_one]) (hint2 i j))
  rw [hpair, hlin]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  -- The `j`-th term.
  have hterm : Work.Drive.pairing E.y E.ρ E.σ E.ψ f (E.ψ j * φ)
      = Work.Drive.pairTerm (E.y j) (E.ρ j) (E.σ j) (fun _ => (1 : ℝ)) f (E.ψ j * φ) := by
    simp only [Work.Drive.pairing]
    calc ∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i) f (E.ψ j * φ)
        = ∑ i, Work.Drive.pairTerm (E.y i) (E.ρ i) (E.σ i) (E.ψ i * E.β j) f (E.ψ j * φ) :=
          Finset.sum_congr rfl (fun i _ => Work.Drive.GreenRung.pairTerm_congr_weight (E.htgt i) (E.hσρ i)
            (fun y hy => by rw [Pi.mul_apply, E.β_eq_one_of_memPS hy, mul_one]))
      _ = ∑ i, Work.Drive.pairTerm (E.y j) (E.ρ j) (E.σ j) (E.ψ i * E.β j) f (E.ψ j * φ) :=
          Finset.sum_congr rfl (fun i _ => by
            by_cases hij : i = j
            · subst hij; rfl
            · exact E.pairTerm_transfer_regionPS i j hij (hf j) (E.hψdiff j j) (hφdiff j))
      _ = Work.Drive.pairTerm (E.y j) (E.ρ j) (E.σ j) (∑ i, E.ψ i * E.β j) f (E.ψ j * φ) :=
          (Work.Drive.pairTerm_weight_finset_sum Finset.univ (fun i _ => by
            by_cases hij : i = j
            · subst hij
              exact hint2 _ _
            · exact E.pairIntegrable_transfer_regionPS i j hij
                (E.region_differentiablePS i j (hf j) (E.hψdiff j j) (hφdiff j)).1
                (E.region_differentiablePS i j (hf j) (E.hψdiff j j) (hφdiff j)).2
                (hint2 i j))).symm
      _ = Work.Drive.pairTerm (E.y j) (E.ρ j) (E.σ j) (E.β j) f (E.ψ j * φ) :=
          Work.Drive.GreenRung.pairTerm_congr_weight (E.htgt j) (E.hσρ j) (fun y hy => by
            have hyK : y ∈ K := hφK (tsupport_mul_subset_right (f := E.ψ j) (g := φ) hy)
            have h1 : ∑ i, E.ψ i y = 1 := E.hsum y hyK
            have h2 : (∑ i, E.ψ i * E.β j) y = (∑ i, E.ψ i) y * E.β j y := by
              simp only [E.sum_ψ_mul_β_eqPS j, Pi.mul_apply]
            rw [h2, Finset.sum_apply, h1, one_mul])
      _ = Work.Drive.pairTerm (E.y j) (E.ρ j) (E.σ j) (fun _ => (1 : ℝ)) f (E.ψ j * φ) :=
          Work.Drive.GreenRung.pairTerm_congr_weight (E.htgt j) (E.hσρ j)
            (fun y hy => by simpa using E.β_eq_one_of_memPS hy)
  rw [hterm]
  exact E.pairTerm_weight_one_eq_zeroPS j hψc1 hφc1 hharm

end Work.Kernel
