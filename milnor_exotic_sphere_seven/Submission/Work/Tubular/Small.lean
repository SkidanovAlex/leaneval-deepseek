import Mathlib
import Submission.Work.Tubular.LocalTube
import Submission.Work.Tubular.Compact

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

/-!
# Injectivity of the tubular map at small scale

For a compact embedded `V ⊆ ℝ^{8+k}`, the tubular map `(x,w) ↦ e x + w` is injective on the disc
bundle of radius `ε` for *some* `ε > 0`.  This is the "local injectivity + compactness" step of the
tubular neighbourhood theorem, and it is what turns the local tube charts
(`Work.Tubular.LocalTube`) into a global chart.

The proof is the standard one, in the form that avoids sequences:

* take a finite cover of `V` by the local-tube neighbourhoods `S x`, and shrink it to a finite
  **closed** cover `w x ⊆ S x` (the shrinking lemma: a compact Hausdorff space is normal);
* on the compact set `K = ⋃_{x ∈ t} w x × (V ∖ S x)` of pairs of points which lie in *different*
  local charts, the function `(a,b) ↦ ‖e a - e b‖` is continuous and strictly positive (because
  `a ∈ w x ⊆ S x` while `b ∉ S x` forces `a ≠ b`, and `e` is injective); it therefore has a
  positive lower bound `δ`;
* a uniform positive radius `η₀ ≤ η x` for the charts exists because `t` is finite;
* for `ε = min (δ/4) (η₀/2)`: if `p, q` are in the `ε`-disc bundle with `e p + p.vec = e q + q.vec`,
  then `‖e p.1 - e q.1‖ = ‖q.vec - p.vec‖ ≤ 2ε < δ`, so `p.1` and `q.1` cannot lie in different
  charts: both lie in a single `S x`, hence both lie in the local tube `W x` (whose uniform disc is
  contained in `W x`), where the tubular map is injective.
-/

open scoped Manifold ContDiff Topology InnerProduct
open Function Filter

namespace Work.Tubular

open Work.ThomBordism Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- A chosen local tube chart at each point: the local form of the tubular neighbourhood theorem
(`Work.Tubular.nonempty_localTube`). -/
def localTube (E : EmbeddingData V (8 + k)) (x : V.pt) : LocalTube E x :=
  Classical.choice (nonempty_localTube E x)

/-- **The tubular map is injective on a small disc bundle.**

This is the compactness step of the tubular neighbourhood theorem: at every point of `V` the tubular
map is a local homeomorphism by `Work.Tubular.LocalTube`; a finite subcover of the compact `V`
together with the shrinking lemma supplies a uniform radius. -/
theorem exists_injOn_tubeMap_small (E : EmbeddingData V (8 + k)) [Nonempty V.pt] :
    ∃ ε > 0, Set.InjOn (tubeMap E) {p : NormalTotal E | normalNorm E p ≤ ε} := by
  classical
  -- a finite cover of `V` by the local-tube neighbourhoods
  obtain ⟨t, ht⟩ := (isCompact_univ (X := V.pt)).elim_finite_subcover
    (fun x : V.pt => (localTube E x).S) (fun x => (localTube E x).hS)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, (localTube E x).mem_S⟩)
  have htne : t.Nonempty := by
    obtain ⟨x₀⟩ := ‹Nonempty V.pt›
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x₀))
    exact ⟨y, hy⟩
  -- shrink it to a finite *closed* cover
  have huo : ∀ i : {x : V.pt // x ∈ t}, IsOpen ((localTube E i.1).S) :=
    fun i => (localTube E i.1).hS
  have hus : (Set.univ : Set V.pt) ⊆ ⋃ i : {x : V.pt // x ∈ t}, (localTube E i.1).S := by
    intro x _
    obtain ⟨y, hyt, hyS⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨y, hyt⟩, hyS⟩
  have huf : ∀ x ∈ (Set.univ : Set V.pt),
      {i : {x : V.pt // x ∈ t} | x ∈ (localTube E i.1).S}.Finite := fun x _ => Set.toFinite _
  obtain ⟨v, hvcover, hvclosed, hvsub⟩ :=
    exists_subset_iUnion_closed_subset isClosed_univ huo huf hus
  -- reindex the closed refinement by `V.pt`
  set w : V.pt → Set V.pt :=
    fun x => if h : x ∈ t then v ⟨x, h⟩ else ∅ with hwdef
  have hwclosed : ∀ x, IsClosed (w x) := by
    intro x
    by_cases h : x ∈ t
    · have : w x = v ⟨x, h⟩ := by rw [hwdef]; simp only [dif_pos h]
      rw [this]; exact hvclosed ⟨x, h⟩
    · have : w x = ∅ := by rw [hwdef]; simp only [dif_neg h]
      rw [this]; exact isClosed_empty
  have hwsub : ∀ x ∈ t, w x ⊆ (localTube E x).S := by
    intro x hx
    have hwx : w x = v ⟨x, hx⟩ := by rw [hwdef]; simp only [dif_pos hx]
    rw [hwx]; exact hvsub ⟨x, hx⟩
  have hwcover : (Set.univ : Set V.pt) ⊆ ⋃ x ∈ t, w x := by
    intro y _
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp (hvcover (Set.mem_univ y))
    refine Set.mem_iUnion₂.mpr ⟨i.1, i.2, ?_⟩
    have hwx : w i.1 = v ⟨i.1, i.2⟩ := by rw [hwdef]; simp only [dif_pos i.2]
    rw [hwx]; exact hyi
  -- the compact set of pairs which lie in different charts
  set K : Set (V.pt × V.pt) :=
    ⋃ x ∈ t, (w x ×ˢ ((localTube E x).S)ᶜ) with hKdef
  have hKc : IsClosed K := by
    show IsClosed (⋃ x ∈ t, (w x ×ˢ ((localTube E x).S)ᶜ))
    exact isClosed_biUnion_finset fun x _ =>
      (hwclosed x).prod (localTube E x).hS.isClosed_compl
  have hKcomp : IsCompact K :=
    IsCompact.of_isClosed_subset
      ((isCompact_univ (X := V.pt)).prod (isCompact_univ (X := V.pt))) hKc (by rintro r -; exact ⟨Set.mem_univ _, Set.mem_univ _⟩)
  -- the distance function on it has a positive lower bound
  set Φ : V.pt × V.pt → ℝ := fun r => ‖E.e r.1 - E.e r.2‖ with hΦdef
  have hΦc : Continuous Φ := by
    show Continuous (fun r : V.pt × V.pt => ‖E.e r.1 - E.e r.2‖)
    exact ((E.smooth.continuous.comp continuous_fst).sub
      (E.smooth.continuous.comp continuous_snd)).norm
  have hΦpos : ∀ r ∈ K, 0 < Φ r := by
    intro r hr
    have hne : r.1 ≠ r.2 := by
      intro heq
      obtain ⟨x, hxt, hrx, hry⟩ := Set.mem_iUnion₂.mp hr
      have : r.2 ∈ (localTube E x).S := hwsub x hxt (heq ▸ hrx)
      exact hry this
    have hne' : E.e r.1 ≠ E.e r.2 := fun h => hne (E.closedEmbedding.injective h)
    have : E.e r.1 - E.e r.2 ≠ 0 := sub_ne_zero.mpr hne'
    simpa [Φ] using norm_pos_iff.mpr this
  obtain ⟨δ, hδpos, hδ⟩ := hKcomp.exists_forall_le' hΦc.continuousOn hΦpos
  -- a uniform radius for the local charts
  obtain ⟨η₀, hη₀pos, hη₀⟩ : ∃ η₀ > 0, ∀ x ∈ t, η₀ ≤ (localTube E x).η := by
    refine ⟨t.inf' htne (fun x => (localTube E x).η), ?_, fun x hx => Finset.inf'_le _ hx⟩
    exact (Finset.lt_inf'_iff _).2 fun x _ => (localTube E x).η_pos
  refine ⟨min (δ / 4) (η₀ / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro p hp q hq hpq
  -- the images of the base points are close
  have hsub : E.e p.1.1 - E.e q.1.1 = q.1.2 - p.1.2 := by
    refine (sub_eq_sub_iff_add_eq_add).2 ?_
    have hpq' : E.e p.1.1 + p.1.2 = E.e q.1.1 + q.1.2 := hpq
    exact hpq'.trans (add_comm _ _)
  have hclose : ‖E.e p.1.1 - E.e q.1.1‖ ≤ 2 * min (δ / 4) (η₀ / 2) := by
    have h1 : ‖E.e p.1.1 - E.e q.1.1‖ = ‖q.1.2 - p.1.2‖ := by rw [hsub]
    rw [h1]
    have h2 : ‖q.1.2 - p.1.2‖ ≤ ‖q.1.2‖ + ‖p.1.2‖ := norm_sub_le q.1.2 p.1.2
    have h3 : ‖q.1.2‖ ≤ min (δ / 4) (η₀ / 2) := by simpa [normalNorm] using hq
    have h4 : ‖p.1.2‖ ≤ min (δ / 4) (η₀ / 2) := by simpa [normalNorm] using hp
    linarith
  -- hence the base points lie in a common chart
  obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.mp (hwcover (Set.mem_univ p.1.1))
  have hqx : q.1.1 ∈ (localTube E x).S := by
    by_contra hcon
    have hmemK : (p.1.1, q.1.1) ∈ K := by
      refine Set.mem_iUnion₂.mpr ⟨x, hxt, hpx, ?_⟩
      simpa using hcon
    have hb := hδ (p.1.1, q.1.1) hmemK
    have hlt : Φ (p.1.1, q.1.1) < δ := by
      show ‖E.e p.1.1 - E.e q.1.1‖ < δ
      have := min_le_left (δ / 4) (η₀ / 2)
      linarith
    linarith
  -- both points lie in the local tube, where the tubular map is injective
  have hpxS : p.1.1 ∈ (localTube E x).S := hwsub x hxt hpx
  have hpn : ‖p.1.2‖ < (localTube E x).η := by
    have h1 : ‖p.1.2‖ ≤ η₀ / 2 := by
      have := le_trans hp (min_le_right (δ / 4) (η₀ / 2)); simpa [normalNorm] using this
    have h3 := hη₀ x hxt
    linarith
  have hqn : ‖q.1.2‖ < (localTube E x).η := by
    have h1 : ‖q.1.2‖ ≤ η₀ / 2 := by
      have := le_trans hq (min_le_right (δ / 4) (η₀ / 2)); simpa [normalNorm] using this
    have h3 := hη₀ x hxt
    linarith
  have hpW : p ∈ (localTube E x).W := (localTube E x).nbd p.1.1 hpxS p.1.2 p.2 hpn
  have hqW : q ∈ (localTube E x).W := (localTube E x).nbd q.1.1 hqx q.1.2 q.2 hqn
  exact (localTube E x).injOn hpW hqW hpq

end

end Work.Tubular
