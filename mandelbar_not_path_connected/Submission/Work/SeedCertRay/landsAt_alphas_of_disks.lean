import Mathlib
import Submission.Work.SeedCertRay.Disk
import Submission.Work.SeedCertRay.Basic
import Submission.Work.SeedCertRay.isPreconnected_seg
import Submission.Work.SeedCertRay.chain_sound_sets
import Submission.Work.SeedCertRay.landsN_of_petal_of_isDynBottcher
import Submission.Work.SeedCertRay.landsAt_alpha1_of_landsN
import Submission.Work.SeedCertRay.landsN_alpha2_of_landsN_alpha1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open Classical Set Function Filter
open scoped Topology ComplexConjugate

/-! ## The disk layer is a special case of the set-valued chain

The certificate data `(D, v)` of the disk chain is turned into a *set*-valued chain
`C k j = diskUnion (D k j)`: `Work.SeedCertRay.chain_sound_sets` then supplies the covering of
every ray piece.  Two facts about a finite union of disks are needed to feed it: the union is
closed, and the half-plane hypothesis `hHP` makes the union separated from its own reflection
and from the reflection of the previous union. -/

/-- A disk (a closed ball with rational centre and radius) is a closed set. -/
theorem isClosed_disk_toSet (D : Work.SeedCertRay.Disk) : IsClosed D.toSet := by
  have h : D.toSet = Metric.closedBall D.center (D.r : ℝ) := by
    ext z
    rw [Disk.mem_toSet, Disk.mem, Metric.mem_closedBall, dist_eq_norm]
  rw [h]
  exact Metric.isClosed_closedBall

/-- A finite union of disks is closed. -/
theorem isClosed_diskUnion {N : ℕ} (D : Fin N → Work.SeedCertRay.Disk) :
    IsClosed (Work.SeedCertRay.diskUnion D) := by
  show IsClosed (⋃ i, (D i).toSet)
  exact isClosed_iUnion_of_finite (fun i => isClosed_disk_toSet (D i))

/-- If every disk of a finite family lies in the open half-plane `halfplane v`, then so does
their union. -/
theorem diskUnion_subset_halfplane {N : ℕ} {D : Fin N → Work.SeedCertRay.Disk} {v : ℚ × ℚ}
    (h : ∀ i, (D i).toSet ⊆ Work.SeedCertRay.halfplane v) :
    Work.SeedCertRay.diskUnion D ⊆ Work.SeedCertRay.halfplane v := by
  intro z hz
  rw [Work.SeedCertRay.mem_diskUnion] at hz
  obtain ⟨i, hi⟩ := hz
  exact h i hi

/-- Two sets contained in the same open half-plane `{z | 0 < p * z.re + q * z.im}` are
separated from the reflection of one another: the defining linear functional changes sign
under `z ↦ -z`, so no point can lie in `A` while its negative lies in `B`. -/
theorem disjoint_neg_of_halfplane {A B : Set ℂ} {v : ℚ × ℚ}
    (hA : A ⊆ Work.SeedCertRay.halfplane v) (hB : B ⊆ Work.SeedCertRay.halfplane v) :
    Disjoint A (-B) := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  rw [Set.mem_neg] at hzB
  have h1 := hA hzA
  have h2 := hB hzB
  simp only [Work.SeedCertRay.halfplane, Set.mem_setOf_eq, Complex.neg_re, Complex.neg_im]
    at h1 h2
  linarith

theorem landsAt_alphas_of_disks {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) (z₁ A : ℂ) (R δ ρ₁ : ℝ) (ρ : ℕ → ℝ) (K : ℕ) (hg : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁) (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) (hα : Work.EL.T^[10] Work.EL.alpha1 = Work.EL.alpha1) (θ : ℕ → ℝ) (hθ : ∀ j, θ (j + 1) = Work.EL.T (θ j)) (hθ0 : θ 0 = Work.EL.alpha1) (X : Work.SeedCertRay.Box) (hcX : X.mem c) (N : ℕ) (D : ℕ → ℕ → Fin N → Work.SeedCertRay.Disk) (v : ℕ → ℕ → ℚ × ℚ) (hD0 : ∀ j, Work.SeedCertRay.seg hN (θ j) (ρ 1) (ρ 0) ⊆ Work.SeedCertRay.diskUnion (D 0 j)) (hD1 : ∀ k j i, Work.SeedCertRay.DiskCover (D k (j + 1) i) X (D (k + 1) j i)) (hHP : ∀ k j, (∀ i, (D (k + 1) j i).toSet ⊆ Work.SeedCertRay.halfplane (v k j)) ∧ (∀ i, (D k j i).toSet ⊆ Work.SeedCertRay.halfplane (v k j))) (hQ : ∀ k, K ≤ k → k ≤ K + 9 → Work.SeedCertRay.diskUnion (D k 0) ⊆ Work.SeedCertRay.Petal z₁ A R) (hρ₁ : 0 < ρ₁) (hδ : 0 < δ) (hA : A ≠ 0) (hRQ : 1 ≤ R * ‖A‖ * ρ₁) (hP1 : ∀ z : ℂ, ‖z - z₁‖ = ρ₁ → Work.EL.F c z ∉ Work.SeedCertRay.Petal z₁ A R) (hP2 : ∀ z : ℂ, ‖z - z₁‖ ≤ ρ₁ → Work.EL.F c z ∈ Work.SeedCertRay.Petal z₁ A R → z ∈ Work.SeedCertRay.Petal z₁ A R ∧ (Work.SeedCertRay.fatou z₁ A z).re ≤ (Work.SeedCertRay.fatou z₁ A (Work.EL.F c z)).re - δ) : Work.Landing.landsAt c Work.EL.alpha1 z₁ ∧ Work.Landing.landsAt c Work.EL.alpha2 z₁ := by
  -- ### Step 1: the disk data is a set-valued chain, fed to `chain_sound_sets`
  -- (D1) in set form: a `T_c`-preimage of a point of `C k (j+1)` lies in `C (k+1) j` up to sign.
  have hD1sets : ∀ k j, ∀ u : ℂ,
      LeanEval.ComplexAnalysis.Tantibar c u ∈ Work.SeedCertRay.diskUnion (D k (j + 1)) →
        u ∈ Work.SeedCertRay.diskUnion (D (k + 1) j) ∨
          -u ∈ Work.SeedCertRay.diskUnion (D (k + 1) j) := by
    intro k j u hu
    simp only [Work.SeedCertRay.mem_diskUnion] at hu ⊢
    obtain ⟨i, hi⟩ := hu
    rcases hD1 k j i (LeanEval.ComplexAnalysis.Tantibar c u) c u hi hcX rfl with hmem | hmem
    · exact Or.inl ⟨i, hmem⟩
    · exact Or.inr ⟨i, hmem⟩
  -- (D2) in set form: closedness (finite union of closed balls) and the two radial separations,
  -- both consequences of the half-plane hypothesis `hHP`.
  have hD2sets : ∀ k j, IsClosed (Work.SeedCertRay.diskUnion (D (k + 1) j)) ∧
      Disjoint (Work.SeedCertRay.diskUnion (D (k + 1) j))
        (-Work.SeedCertRay.diskUnion (D (k + 1) j)) ∧
      Disjoint (Work.SeedCertRay.diskUnion (D k j))
        (-Work.SeedCertRay.diskUnion (D (k + 1) j)) := by
    intro k j
    refine ⟨isClosed_diskUnion (D (k + 1) j), ?_, ?_⟩
    · exact disjoint_neg_of_halfplane (diskUnion_subset_halfplane (hHP k j).1)
        (diskUnion_subset_halfplane (hHP k j).1)
    · exact disjoint_neg_of_halfplane (diskUnion_subset_halfplane (hHP k j).2)
        (diskUnion_subset_halfplane (hHP k j).1)
  have hchain : ∀ k j, Work.SeedCertRay.seg hN (θ j) (ρ (k + 1)) (ρ k)
      ⊆ Work.SeedCertRay.diskUnion (D k j) :=
    chain_sound_sets hN hφ θ hθ ρ hρ (fun k j => Work.SeedCertRay.diskUnion (D k j))
      hD0 hD1sets hD2sets
  -- ### Step 2: restrict to the `α₁`-ray (`j = 0`), where `θ 0 = α₁`
  have hC : ∀ k, k ≤ K + 9 →
      Work.SeedCertRay.seg hN Work.EL.alpha1 (ρ (k + 1)) (ρ k)
        ⊆ Work.SeedCertRay.diskUnion (D k 0) := by
    intro k _
    have h := hchain k 0
    rwa [hθ0] at h
  -- ### Step 3: the tail induction makes the `α₁`-ray land
  have h₁ : Work.EL.LandsN hN Work.EL.alpha1 z₁ :=
    landsN_of_petal_of_isDynBottcher hN hφ z₁ A R δ ρ₁ ρ K hρ hα
      (fun k => Work.SeedCertRay.diskUnion (D k 0)) hC hQ hρ₁ hδ hA hRQ hP1 hP2
  -- ### Step 4: transfer along `(T_c)^[5]` (which fixes `z₁`) to the `α₂`-ray
  have h₂ : Work.EL.LandsN hN Work.EL.alpha2 z₁ :=
    landsN_alpha2_of_landsN_alpha1 hN hφ hg h₁
  exact ⟨(Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha1 z₁).mp h₁,
    (Work.ELTop.landsN_iff_landsAt hN hφ Work.EL.alpha2 z₁).mp h₂⟩

end Work.SeedCertRay
