import Mathlib
import Submission.Work.Drive.exists_meet3Data_of_good_family
import Submission.Work.Drive.nineBoxToMeet3
import Submission.Work.Drive.meet3Containment

/-!
# The engine's hypotheses from a good family

This file is the last bridge of the parametric-Sard route: it composes

* `Work.Drive.exists_meet3Data_of_good_family` (the merged genericity theorem: one parameter `t`
  with the nine-box transversality and face statements on the compact set `K`),
* `Work.Drive.eventually_meet3_subset_of_isOpen` (the perturbed triple locus of `G t` inside the
  nine-box stays in `interior K` for `t` near `0`, whence in `K` for the chosen `t`), and
* `Work.Drive.TParity.transHyp_of_on_compact` / `Work.Drive.TParity.faceHyp_of_on_compact` together
  with `Work.Drive.Meet3Hyp.of_nineBox` (the nine-box statements on `K` are the *global* ones when
  all triple points lie in `K`),

into the engine's input `Work.Drive.Meet3Hyp M (G t)`, at an *arbitrarily small* parameter
`‖t‖ < ε'`: the Sard theorem is applied at the radius `min ε' (min ε (δ/2))`, where `δ` is the
neighbourhood radius of `0` on which the perturbed triple locus is known to stay interior to `K`.

The only subtlety is that the containment/surjectivity hypotheses `hcontain`, `hsurj` of the family
are stated on the fixed ball of radius `ε`, while the conclusion is asked for an arbitrary `ε'`; the
radius of the Sard application is therefore the minimum of the two (and of the neighbourhood radius
`δ/2` of the perturbation).
-/

namespace Work.Drive

theorem exists_meet3Hyp_of_good_family (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (hsmooth : ∀ t : EuclideanSpace ℝ (Fin m), ∀ k : Fin 3,
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t k))
    (hseam : ∀ (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3) (x : EuclideanSpace ℝ (Fin 3)),
      Work.Drive.onSeam x → G t k x = G t k (Work.Drive.seamInv x))
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hbase : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (G 0) y → y ∈ interior K)
    (p : M) {ε : ℝ} (hε : 0 < ε)
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → ∀ k : Fin 3,
        G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → Work.Drive.TParity.chartDiff3 p (G t) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G t') y) t)) :
    ∀ ε' : ℝ, 0 < ε' →
      ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε' ∧ Work.Drive.Meet3Hyp M (G t) := by
  intro ε' hε'
  -- ## Step 1: near `0` the perturbed triple locus stays inside `interior K`
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : EuclideanSpace ℝ (Fin m), ‖t‖ < δ →
      ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
        Work.Drive.TParity.meet3 (G t) y → y ∈ interior K := by
    have hev := eventually_meet3_subset_of_isOpen (m := m) (M := M) G
      (fun k => (hG k).continuous) (U := interior K) isOpen_interior hbase
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδsub⟩ := hev
    exact ⟨δ, hδpos, fun t ht => hδsub (by rw [Metric.mem_ball, dist_zero_right]; exact ht)⟩
  -- ## Step 2: the merged genericity theorem at the radius `min ε' (min ε (δ/2))`
  set r : ℝ := min ε' (min ε (δ / 2)) with hr
  have hrpos : 0 < r := by
    rw [hr]; exact lt_min hε' (lt_min hε (by linarith))
  have hrε' : r ≤ ε' := by rw [hr]; exact min_le_left _ _
  have hrε : r ≤ ε := by
    rw [hr]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hrδ : r ≤ δ := by
    rw [hr]
    exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
  obtain ⟨t, ht, htrans, hface⟩ :=
    exists_meet3Data_of_good_family m G hG p K hK hrpos
      (fun s y hs hy k => hcontain s y (lt_of_lt_of_le hs hrε) hy k)
      (fun s y hs hy hz => hsurj s y (lt_of_lt_of_le hs hrε) hy hz)
  -- ## Step 3: the triple locus of the chosen configuration lies in `K`
  have hKin : ∀ y : EuclideanSpace ℝ (Fin 9), y ∈ Submission.Drive.unitBox 8 →
      Work.Drive.TParity.meet3 (G t) y → y ∈ K :=
    fun y hy hm => interior_subset (hδ t (lt_of_lt_of_le ht hrδ) y hy hm)
  -- ## Step 4: the nine-box statements on `K` are the global ones, and assemble `Meet3Hyp`
  exact ⟨t, lt_of_lt_of_le ht hrε',
    Meet3Hyp.of_nineBox (G t) (hsmooth t)
      (TParity.transHyp_of_on_compact (G t) K hKin htrans)
      (TParity.faceHyp_of_on_compact (G t) K hKin hface)
      (hseam t)⟩

end Work.Drive
