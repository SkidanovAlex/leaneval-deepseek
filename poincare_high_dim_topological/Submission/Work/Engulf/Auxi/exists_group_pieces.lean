import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.fine_cover_simplex
import Submission.Work.Engulf.Auxi.exists_indep_cover

/-!
# A9 aux: `exists_group_pieces` (E1a)

The dominating simplices of one chart group: given a cube chart `ψ` in which `X` is `p`-dominated,
a set `R ⊆ X ∩ ψ(closedCube ½)` and `δ > 0`, there is a finite list of simplices `Δ ⊆ ℝⁿ`, each
nonempty, affinely independent, with at most `p + 1` vertices, contained in `closedCube 5/8` and
all of whose points are within `δ` (in `M`, through `ψ`) of `R`, whose `ψ`-images cover `R`.

The construction: `DomIn` gives a finite polyhedral cover `P` of `ψ⁻¹X ∩ closedCube 1`; each of its
simplices is split, by Carathéodory, into affinely independent simplices; the standard simplex on
each such piece is subdivided until the mesh is smaller than `min (1/32) (μ/4)`, where `μ` is a
uniform-continuity modulus of `ψ` on the compact cube `closedCube 5/8`; finally one keeps the
subdivision faces meeting `ψ⁻¹R ∩ closedCube ½`.
-/

open Set Metric PL

namespace Work.Engulf.Aux

variable {n p : ℕ} {M : Type*} [MetricSpace M]

/-! ## Geometric helpers -/

/-- A simplex is contained in the closed ball of radius `r` around any point that is within `r` of
all of its vertices. -/
theorem simp_subset_closedBall {N : ℕ} {s : Finset (E N)} {v : E N} {r : ℝ}
    (h : ∀ w ∈ s, dist w v ≤ r) : simp s ⊆ Metric.closedBall v r := by
  rw [PL.simp]
  refine convexHull_min ?_ (convex_closedBall v r)
  intro w hw
  rw [Metric.mem_closedBall]
  exact h w (by simpa using hw)

/-- `|x i - y i| ≤ dist x y` for points of `ℝᴺ`. -/
theorem abs_apply_sub_le_dist {N : ℕ} (x y : E N) (i : Fin N) : |x i - y i| ≤ dist x y := by
  rw [show x i - y i = (x - y) i from rfl, dist_eq_norm]
  simpa using PiLp.norm_apply_le (x - y) i

/-- Uniform continuity of a cube chart on the closed `r`-cube, `r < 1`. -/
theorem exists_unif_closedCube (ψ : PL.CubeChart n M) {r : ℝ} (hr : r < 1) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ μ > 0, ∀ x ∈ PL.closedCube (n := n) r, ∀ y ∈ PL.closedCube (n := n) r,
      dist x y < μ → dist (ψ.toFun x) (ψ.toFun y) < δ := by
  have hc : ContinuousOn ψ.toFun (PL.closedCube (n := n) r) :=
    ψ.cont.mono (closedCube_subset_openCube hr)
  exact Metric.uniformContinuousOn_iff.1
    ((isCompact_closedCube r).uniformContinuousOn_of_continuous hc) δ hδ

/-- **`exists_group_pieces`** (E1a of `Submission/Work/NOTES_LEAD_poincare_E1fix.md` §1; binder corrected after review, where `N` was unrelated to the chart dimension `n`): the dominating simplices of one chart group.  Given a chart `ψ` in which `X` is `p`-dominated, a set `R ⊆ X ∩ ψ(closedCube ½)` and `δ > 0`, there is a finite list of simplices `Δ` of `ℝⁿ`, each nonempty, affinely independent, of at most `p+1` vertices, with `PL.simp Δ ⊆ closedCube 5/8` and with every point of `PL.simp Δ` within `δ` of `R` (`ψ`-image), whose `ψ`-images cover `R`.  Proof: take `DomIn`'s polyhedral cover `P` of `ψ⁻¹X ∩ closedCube 1`; split each simplex of `P` into affinely independent simplices, keep the fine pieces meeting `ψ⁻¹R ∩ closedCube ½`, and subdivide them with `T.fine` to mesh smaller than `min (1/8, μ)` where `μ` comes from the uniform continuity of `ψ` on the compact `PL.closedCube (n := n) (5/8)` (which sits in `openCube 1`, so `ψ` is uniformly continuous there).  A dimension-generic fine-subdivision result is available as `Work.PL.Subdiv.Util.Mesh.exists_fine_general`. -/
theorem exists_group_pieces {n p : ℕ} {M : Type*} [MetricSpace M]
    (T : Work.Engulf.SubdivTools n) {X : Set M} (ψ : PL.CubeChart n M)
    (hdom : Work.Engulf.DomIn p ψ X) {R : Set M}
    (hR : R ⊆ X ∩ ψ.toFun '' PL.closedCube (1 / 2 : ℝ)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ pieces : List (Finset (PL.E n)),
      (∀ Δ ∈ pieces, Δ.Nonempty ∧ AffineIndependent ℝ (fun v : ↥Δ => (v : PL.E n)) ∧
        Δ.card ≤ p + 1 ∧ PL.simp Δ ⊆ PL.closedCube (5 / 8 : ℝ) ∧
        ∀ y ∈ PL.simp Δ, ∃ z ∈ R, dist (ψ.toFun y) z < δ) ∧
      R ⊆ ⋃ Δ ∈ pieces, ψ.toFun '' PL.simp Δ := by
  classical
  -- ## Step 0: unpack the domination hypothesis
  obtain ⟨P, hPdom, hPmem⟩ := hdom
  obtain ⟨S, hS, hPcov⟩ := hPdom
  have hScard : ∀ s ∈ S, s.card ≤ p + 1 := fun s hs => by have := hS s hs; omega
  -- ## Step 1: uniform continuity of the chart on the `5/8`-cube
  obtain ⟨μ, hμpos, hμ⟩ := exists_unif_closedCube ψ (r := 5 / 8) (by norm_num) hδ
  set ν : ℝ := min (1 / 32) (μ / 4) with hνdef
  have hνpos : 0 < ν := lt_min (by norm_num) (by linarith)
  have hν1 : 2 * ν ≤ 1 / 16 := by
    have h := min_le_left (1 / 32 : ℝ) (μ / 4)
    rw [hνdef]; linarith
  have hν2 : 2 * ν < μ := by
    have h := min_le_right (1 / 32 : ℝ) (μ / 4)
    rw [hνdef]; linarith
  -- ## Step 2: the Carathéodory family of affinely independent pieces
  let 𝒯 : Finset (Finset (E n)) := S.biUnion (fun s => s.powerset.filter (fun t =>
    t.Nonempty ∧ AffineIndependent ℝ (fun v : ↥t => (v : E n))))
  have hmem𝒯 : ∀ t ∈ 𝒯, t.Nonempty ∧ AffineIndependent ℝ (fun v : ↥t => (v : E n)) ∧
      t.card ≤ p + 1 := by
    intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨s, hs, hts⟩ := ht
    rw [Finset.mem_filter, Finset.mem_powerset] at hts
    exact ⟨hts.2.1, hts.2.2, le_trans (Finset.card_le_card hts.1) (hScard s hs)⟩
  have hPcovT : P ⊆ ⋃ t ∈ 𝒯, simp t := by
    intro y hy
    obtain ⟨s, hs, hys⟩ := Set.mem_iUnion₂.1 (hPcov hy)
    obtain ⟨t, hts, htne, htind, hyt⟩ := Work.Engulf.Auxi.exists_indep_cover s hys
    exact Set.mem_iUnion₂.2 ⟨t, by
      rw [Finset.mem_biUnion]
      exact ⟨s, hs, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, htne, htind⟩⟩, hyt⟩
  -- ## Step 3: a fine independent cover of each simplex of `𝒯`
  have hex : ∀ t ∈ 𝒯, ∃ G : Finset (Finset (E n)),
      (∀ τ ∈ G, τ.Nonempty ∧ AffineIndependent ℝ (fun v : ↥τ => (v : E n)) ∧
        τ.card ≤ p + 1 ∧ simp τ ⊆ simp t ∧ ∀ v ∈ τ, ∀ w ∈ τ, dist v w < ν) ∧
      simp t ⊆ ⋃ τ ∈ G, simp τ := by
    intro t ht
    obtain ⟨-, hind, hcard⟩ := hmem𝒯 t ht
    exact Work.Engulf.Auxi.fine_cover_simplex T hind hcard hνpos
  let Gm : {t // t ∈ 𝒯} → Finset (Finset (E n)) := fun t => Classical.choose (hex t.1 t.2)
  have hGm : ∀ t : {t // t ∈ 𝒯},
      (∀ τ ∈ Gm t, τ.Nonempty ∧ AffineIndependent ℝ (fun v : ↥τ => (v : E n)) ∧
        τ.card ≤ p + 1 ∧ simp τ ⊆ simp t.1 ∧ ∀ v ∈ τ, ∀ w ∈ τ, dist v w < ν) ∧
      simp t.1 ⊆ ⋃ τ ∈ Gm t, simp τ := fun t => Classical.choose_spec (hex t.1 t.2)
  -- ## Step 4: keep the pieces meeting `ψ⁻¹R ∩ closedCube ½`
  let all : Finset (Finset (E n)) := (𝒯.attach.biUnion Gm).filter (fun τ =>
    ((simp τ ∩ ψ.toFun ⁻¹' R ∩ closedCube (1 / 2 : ℝ)).Nonempty))
  refine ⟨all.toList, ?_, ?_⟩
  · intro Δ hΔ
    rw [Finset.mem_toList, Finset.mem_filter] at hΔ
    obtain ⟨hΔb, hΔmeet⟩ := hΔ
    rw [Finset.mem_biUnion] at hΔb
    obtain ⟨t, ht, hΔt⟩ := hΔb
    obtain ⟨hGt, -⟩ := hGm t
    obtain ⟨hne, hind, hcard, hsub, hmesh⟩ := hGt Δ hΔt
    obtain ⟨a, ⟨⟨hasa, haR⟩, hacube⟩⟩ := hΔmeet
    obtain ⟨v, hv⟩ := hne
    have hball : simp Δ ⊆ Metric.closedBall v ν :=
      simp_subset_closedBall (fun w hw => le_of_lt (hmesh w hw v hv))
    have haν : dist a v ≤ ν := hball hasa
    have hcube5 : simp Δ ⊆ PL.closedCube (5 / 8 : ℝ) := by
      intro x hx
      have hxν : dist x v ≤ ν := hball hx
      have hxa : dist x a ≤ 2 * ν := by
        calc dist x a ≤ dist x v + dist v a := dist_triangle x v a
          _ ≤ ν + ν := by rw [dist_comm v a]; linarith
          _ = 2 * ν := by ring
      have hxa' : dist x a < 1 / 8 := lt_of_le_of_lt hxa (by linarith)
      intro i
      have h1 : |x i - a i| ≤ dist x a := abs_apply_sub_le_dist x a i
      have h2 : |a i| ≤ 1 / 2 := hacube i
      have h3 : |x i| ≤ |x i - a i| + |a i| := by
        have h := abs_add_le (x i - a i) (a i)
        rwa [sub_add_cancel] at h
      linarith
    refine ⟨⟨v, hv⟩, hind, hcard, hcube5, ?_⟩
    intro y hy
    refine ⟨ψ.toFun a, haR, ?_⟩
    have hyν : dist y v ≤ ν := hball hy
    have hya : dist y a ≤ 2 * ν := by
      calc dist y a ≤ dist y v + dist v a := dist_triangle y v a
        _ ≤ ν + ν := by rw [dist_comm v a]; linarith
        _ = 2 * ν := by ring
    exact hμ y (hcube5 hy) a (closedCube_mono (by norm_num) hacube) (lt_of_le_of_lt hya hν2)
  · intro z hz
    obtain ⟨hzX, hzψ⟩ := hR hz
    obtain ⟨a, hacube, hψa⟩ := hzψ
    have haP : a ∈ P := hPmem a (closedCube_mono (by norm_num) hacube) (by rw [hψa]; exact hzX)
    obtain ⟨s, hs, has⟩ := Set.mem_iUnion₂.1 (hPcov haP)
    obtain ⟨t, hts, htne, htind, hat⟩ := Work.Engulf.Auxi.exists_indep_cover s has
    have htT : t ∈ 𝒯 := by
      rw [Finset.mem_biUnion]
      exact ⟨s, hs, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hts, htne, htind⟩⟩
    obtain ⟨-, hcov⟩ := hGm ⟨t, htT⟩
    obtain ⟨τ, hτG, haτ⟩ := Set.mem_iUnion₂.1 (hcov hat)
    have hτall : τ ∈ all := by
      rw [Finset.mem_filter]
      refine ⟨?_, ⟨a, ⟨⟨haτ, ?_⟩, hacube⟩⟩⟩
      · rw [Finset.mem_biUnion]
        exact ⟨⟨t, htT⟩, Finset.mem_attach 𝒯 ⟨t, htT⟩, hτG⟩
      · show ψ.toFun a ∈ R
        rw [hψa]; exact hz
    exact Set.mem_iUnion₂.2 ⟨τ, by rwa [Finset.mem_toList], ⟨a, haτ, hψa⟩⟩

end Work.Engulf.Aux
