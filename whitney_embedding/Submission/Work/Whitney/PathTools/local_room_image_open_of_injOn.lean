import Mathlib
import Submission.Work.Whitney.PathTools.exists_hyperplane_slice_isTotallyDisconnected
import Submission.Work.Whitney.PathTools.slices_totallyDisconnected
import Submission.Work.Whitney.PathTools.sphere_sdiff_isCompact_totallyDisconnected_isPreconnected
import Submission.Work.Whitney.PathTools.ball_sdiff_totallyDisconnected
import Submission.Work.Whitney.PathTools.RemovabilityGeneral
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen
import Submission.Work.Whitney.PathTools.LocalRoomAux
import Submission.Work.Whitney.PathTools.ball_sdiff_totallyDisconnected_unrestricted

/-!
# Local room at a point of the image of an open set under an injective curve

Target: `Work.Whitney.PathTools.local_room_image_open_of_injOn`.

For `n ≥ 3`, `u ⊆ ℝ` open, `γ : ℝ → ℝⁿ` continuous and injective on `u`, with `γ '' u` compact,
and `F` finite, the set `K = γ '' u ∪ F` has "local room" at every `a ∈ K`: for every `ε > 0`
there is an open `O` with `a ∈ O ⊆ ball a ε` such that `O \ K` is path connected.

## Structure

* `γ '' u` is presented as the countable union of the compact arcs `γ '' [a,b]` over the rational
  intervals `[a,b] ⊆ u` (`curveIdx`, `curvePiece`, `iUnion_curvePiece_image`).

* `slices_totallyDisconnected` (a Baire argument over the countable family of rational intervals)
  gives a direction in which every level set of `K` is totally disconnected; applied to a single
  compact arc it shows that each piece `γ '' [a,b]` has empty interior
  (`curvePiece_interior_empty`), hence that `K` is meager (`curve_union_meagre`).

* A second Baire argument over the same countable family produces a "good centre" `y` near any
  point such that every sphere around `y` meets `K` in a totally disconnected set
  (`exists_good_center`); and `exists_hyperplane_slice_isTotallyDisconnected` produces, through
  every point outside `K`, a hyperplane meeting `K` in a totally disconnected set
  (`exists_hyperplane_slice_td`).

* Finally `local_room_of_good_center` assembles these: with `y` a good centre close to `a`, the
  spine `H ∩ ball y R` of a hyperplane `H` through `y` is path connected, every shell
  `sphere y t \ K` is preconnected and meets the spine, so `ball y R \ K` is preconnected, and as
  it is open in the locally path connected space it is path connected.
-/

open Set Metric Topology Filter
open scoped Topology

namespace Work.Whitney.PathTools

variable {n : ℕ}

/-! ## The curve as a countable union of compact arcs -/

/-- Index of the compact pieces of `γ '' u`: the rational intervals contained in `u`. -/
abbrev curveIdx (u : Set ℝ) : Type := {p : ℚ × ℚ // p.1 < p.2 ∧ Set.Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ u}

instance instCountableCurveIdx (u : Set ℝ) : Countable (curveIdx u) := by
  unfold curveIdx; infer_instance

/-- The `p`-th piece of the curve, parametrised by `[0,1]`. -/
def curvePiece (γ : ℝ → EuclideanSpace ℝ (Fin n)) (u : Set ℝ) (p : curveIdx u) :
    ℝ → EuclideanSpace ℝ (Fin n) :=
  fun s => γ ((p.1.1 : ℝ) + s * ((p.1.2 : ℝ) - (p.1.1 : ℝ)))

/-- For `s ∈ u` there is a rational interval in `u` containing `s`. -/
lemma exists_curveIdx_mem {u : Set ℝ} (hu : IsOpen u) {s : ℝ} (hs : s ∈ u) :
    ∃ p : curveIdx u, s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) := by
  obtain ⟨δ, hδpos, hδu⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds hs)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show s - δ < s by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show s < s + δ by linarith)
  have hab : (a : ℝ) < (b : ℝ) := lt_trans ha2 hb1
  refine ⟨⟨(a, b), by exact_mod_cast hab, ?_⟩, ⟨ha2.le, hb1.le⟩⟩
  intro z hz
  apply hδu
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hz.1, hz.2, ha1, hb2]

lemma curvePiece_continuous {u : Set ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin n)} (hγ : Continuous γ)
    (p : curveIdx u) : Continuous (curvePiece γ u p) :=
  hγ.comp (continuous_const.add (continuous_id.mul continuous_const))

lemma curvePiece_mem (u : Set ℝ) (p : curveIdx u) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (p.1.1 : ℝ) + s * ((p.1.2 : ℝ) - (p.1.1 : ℝ)) ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) := by
  have hab : (p.1.1 : ℝ) < (p.1.2 : ℝ) := by exact_mod_cast p.2.1
  constructor
  · nlinarith [hs.1, hab]
  · nlinarith [hs.2, hab]

lemma curvePiece_injOn {u : Set ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin n)} (hγinj : Set.InjOn γ u)
    (p : curveIdx u) : Set.InjOn (curvePiece γ u p) (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hs' : (p.1.1 : ℝ) + s * ((p.1.2 : ℝ) - (p.1.1 : ℝ)) ∈ u :=
    p.2.2 (curvePiece_mem u p hs)
  have ht' : (p.1.1 : ℝ) + t * ((p.1.2 : ℝ) - (p.1.1 : ℝ)) ∈ u :=
    p.2.2 (curvePiece_mem u p ht)
  have h1 := hγinj hs' ht' hst
  have hab : ((p.1.2 : ℝ) - (p.1.1 : ℝ)) ≠ 0 := by
    have h : (p.1.1 : ℝ) < (p.1.2 : ℝ) := by exact_mod_cast p.2.1
    linarith
  have h2 : s * ((p.1.2 : ℝ) - (p.1.1 : ℝ)) = t * ((p.1.2 : ℝ) - (p.1.1 : ℝ)) := by
    linarith
  exact mul_right_cancel₀ hab h2

lemma curvePiece_image_subset (u : Set ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin n))
    (p : curveIdx u) : curvePiece γ u p '' Set.Icc (0 : ℝ) 1 ⊆ γ '' u := by
  rintro z ⟨s, hs, rfl⟩
  exact ⟨_, p.2.2 (curvePiece_mem u p hs), rfl⟩

/-- The image of a piece, parametrised by `[0,1]`, is the arc over the rational interval. -/
lemma curvePiece_image_Icc (u : Set ℝ) (γ : ℝ → EuclideanSpace ℝ (Fin n)) (p : curveIdx u) :
    curvePiece γ u p '' Set.Icc (0 : ℝ) 1 = γ '' Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) := by
  have hab : (p.1.1 : ℝ) < (p.1.2 : ℝ) := by exact_mod_cast p.2.1
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨_, curvePiece_mem u p hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(s - (p.1.1 : ℝ)) / ((p.1.2 : ℝ) - (p.1.1 : ℝ)), ⟨?_, ?_⟩, ?_⟩
    · rw [div_nonneg_iff]
      left
      exact ⟨by linarith [hs.1], by linarith⟩
    · rw [div_le_one (by linarith : (0 : ℝ) < (p.1.2 : ℝ) - (p.1.1 : ℝ))]
      linarith [hs.2]
    · show γ ((p.1.1 : ℝ) + ((s - (p.1.1 : ℝ)) / ((p.1.2 : ℝ) - (p.1.1 : ℝ)))
        * ((p.1.2 : ℝ) - (p.1.1 : ℝ))) = γ s
      congr 1
      rw [div_mul_cancel₀ _ (ne_of_gt (by linarith : (0 : ℝ) < (p.1.2 : ℝ) - (p.1.1 : ℝ)))]
      ring

lemma iUnion_curvePiece_image {u : Set ℝ} (hu : IsOpen u) (γ : ℝ → EuclideanSpace ℝ (Fin n)) :
    (⋃ p : curveIdx u, curvePiece γ u p '' Set.Icc (0 : ℝ) 1) = γ '' u := by
  ext z
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hz
    exact curvePiece_image_subset u γ p hp
  · rintro ⟨s, hsu, rfl⟩
    obtain ⟨p, hp⟩ := exists_curveIdx_mem hu hsu
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    rw [curvePiece_image_Icc]
    exact ⟨s, hp, rfl⟩

lemma isCompact_iUnion_curvePiece_image {u : Set ℝ} (hu : IsOpen u)
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} (hcpt : IsCompact (γ '' u)) :
    IsCompact (⋃ p : curveIdx u, curvePiece γ u p '' Set.Icc (0 : ℝ) 1) := by
  rw [iUnion_curvePiece_image hu γ]
  exact hcpt

/-! ## The pieces have empty interior -/

/-- A compact arc `γ '' [a,b]` (`n ≥ 2`) has empty interior: a slice direction in which all the
level sets of the arc are totally disconnected exists by `slices_totallyDisconnected`, and no
nondegenerate segment can lie in a totally disconnected slice. -/
lemma curvePiece_interior_empty (hn : 2 ≤ n) {u : Set ℝ}
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} (hγ : Continuous γ) (hγinj : Set.InjOn γ u)
    (p : curveIdx u) : interior (γ '' Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨e, he0, hslice⟩ :=
    slices_totallyDisconnected (by omega : 1 ≤ n) isCompact_Icc hγ.continuousOn (hγinj.mono p.2.2) z
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
  -- a nonzero vector orthogonal to `e`
  have he' : ‖‖e‖⁻¹ • e‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr he0)]
  obtain ⟨w, hw1, hw2⟩ :=
    exists_orthogonal_unit_vector_gen (E := EuclideanSpace ℝ (Fin n))
      (by rw [finrank_euclideanSpace_fin]; omega) he'
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw1
    norm_num at hw1
  have horth : inner ℝ w e = 0 := by
    have h1 : e = ‖e‖ • (‖e‖⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he0), one_smul]
    rw [h1, inner_smul_right, real_inner_comm, hw2, mul_zero]
  set c : ℝ := δ / (2 * ‖w‖) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set y : EuclideanSpace ℝ (Fin n) := z + c • w with hy
  have hyz : y ≠ z := by
    intro h
    have h2 : c • w = 0 := by
      have := congrArg (fun q : EuclideanSpace ℝ (Fin n) => q - z) h
      simpa [hy] using this
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (ne_of_gt hcpos)
    · exact hw0 h3
  have hyball : y ∈ Metric.ball z δ := by
    rw [Metric.mem_ball, hy, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hcpos.le, hc]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_pos_iff.mpr hw0, hδpos]
  -- the segment from `z` to `y` lies in the ball and in the slice
  have hseg_ball : segment ℝ z y ⊆ Metric.ball z δ := by
    intro q hq
    rw [segment_eq_image] at hq
    obtain ⟨θ, hθ, rfl⟩ := hq
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : (1 - θ) • z + θ • y - z = θ • (y - z) := by module
    rw [h1, norm_smul, Real.norm_of_nonneg hθ.1]
    calc θ * ‖y - z‖ ≤ 1 * ‖y - z‖ := by nlinarith [norm_nonneg (y - z), hθ.2]
      _ = ‖y - z‖ := one_mul _
      _ < δ := by simpa [dist_eq_norm] using hyball
  have hseg_slice : segment ℝ z y ⊆ {q : EuclideanSpace ℝ (Fin n) | inner ℝ (q - z) e = 0} := by
    intro q hq
    rw [segment_eq_image] at hq
    obtain ⟨θ, hθ, rfl⟩ := hq
    simp only [Set.mem_setOf_eq]
    have h1 : (1 - θ) • z + θ • y - z = θ • (y - z) := by module
    have h2 : y - z = c • w := by rw [hy]; abel
    rw [h1, h2, inner_smul_left, inner_smul_left, horth, mul_zero, mul_zero]
  have hpre : IsPreconnected (segment ℝ z y) := (convex_segment z y).isPreconnected
  have hsing := hslice 0 (segment ℝ z y) (fun q hq =>
    ⟨interior_subset (hδsub (hseg_ball hq)), hseg_slice hq⟩) hpre
  exact hyz (hsing (left_mem_segment ℝ z y) (right_mem_segment ℝ z y)).symm

/-! ## The union is meager -/

/-- A singleton is meager in a nontrivial normed space. -/
lemma isMeagre_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hnt : Nontrivial E)
    (x : E) : IsMeagre ({x} : Set E) := by
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact ⟨a - b, sub_ne_zero.mpr hab⟩
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnd : IsNowhereDense ({x} : Set E) := by
    refine (IsClosed.isNowhereDense_iff isClosed_singleton).mpr ?_
    rw [Set.eq_empty_iff_forall_notMem]
    intro y hy
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hy)
    set δ : ℝ := ε / (2 * (‖v‖ + 1)) with hδ
    have hδpos : 0 < δ := by rw [hδ]; positivity
    have hmem : y + δ • v ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hδpos.le, hδ, div_mul_eq_mul_div,
        div_lt_iff₀ (by positivity)]
      nlinarith [hvn]
    have hne : y + δ • v ≠ y := by
      intro h
      have h2 : δ • v = 0 := by
        have := congrArg (fun z : E => z - y) h
        simpa using this
      rcases smul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 (ne_of_gt hδpos)
      · exact hv h3
    have hyx : y = x := Set.mem_singleton_iff.mp (interior_subset (s := {x}) hy)
    have hyvx : y + δ • v = x :=
      Set.mem_singleton_iff.mp (interior_subset (s := {x}) (hεsub hmem))
    exact hne (by rw [hyvx, hyx])
  exact (isMeagre_iff_countable_union_isNowhereDense).mpr
    ⟨{_}, by rintro t rfl; exact hnd, Set.countable_singleton _,
      by intro y hy; exact ⟨_, rfl, hy⟩⟩

/-- The union of a compact totally disconnected set with a finite set is totally disconnected. -/
lemma isTotallyDisconnected_union_finite {X : Type*} [MetricSpace X] {A G : Set X}
    (hA : IsCompact A) (hAtd : IsTotallyDisconnected A) (hG : G.Finite) :
    IsTotallyDisconnected (A ∪ G) := by
  classical
  haveI : Countable ↥G := hG.countable.to_subtype
  have hunion : (⋃ i : Unit ⊕ ↥G,
      Sum.elim (fun _ : Unit => A) (fun g : ↥G => ({g.1} : Set X)) i) = A ∪ G := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      rcases i with u | g
      · exact Or.inl hi
      · exact Or.inr (by rw [Set.mem_singleton_iff.mp hi]; exact g.2)
    · rintro (hz | hz)
      · exact Set.mem_iUnion.mpr ⟨Sum.inl (), hz⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr ⟨z, hz⟩, by simp⟩
  rw [← hunion]
  refine isTotallyDisconnected_of_isCompact_biUnion (fun i => ?_) (fun i => ?_) ?_
  · rcases i with u | g
    · exact hA
    · exact isCompact_singleton
  · rcases i with u | g
    · exact hAtd
    · intro t ht _
      intro a ha b hb
      rw [Set.mem_singleton_iff.mp (ht ha), Set.mem_singleton_iff.mp (ht hb)]
  · rw [hunion]
    exact hA.union hG.isCompact

/-- `γ '' u ∪ F` is meager (`n ≥ 2`). -/
theorem curve_union_meagre (hn : 2 ≤ n) {u : Set ℝ} (hu : IsOpen u)
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} (hγ : Continuous γ) (hγinj : Set.InjOn γ u)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Finite) :
    IsMeagre ((γ '' u) ∪ F) := by
  classical
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  haveI : Countable ↥F := hF.countable.to_subtype
  have hpiece : ∀ p : curveIdx u, IsMeagre (curvePiece γ u p '' Set.Icc (0 : ℝ) 1) := by
    intro p
    have hnd : IsNowhereDense (curvePiece γ u p '' Set.Icc (0 : ℝ) 1) := by
      rw [curvePiece_image_Icc]
      rw [IsClosed.isNowhereDense_iff (isCompact_Icc.image hγ).isClosed]
      exact curvePiece_interior_empty hn hγ hγinj p
    exact (isMeagre_iff_countable_union_isNowhereDense).mpr
      ⟨{_}, by rintro t rfl; exact hnd, Set.countable_singleton _,
        by intro y hy; exact ⟨_, rfl, hy⟩⟩
  have hFm : IsMeagre (⋃ f : ↥F, ({f.1} : Set (EuclideanSpace ℝ (Fin n)))) :=
    isMeagre_iUnion (fun f => isMeagre_singleton inferInstance f.1)
  have htot : IsMeagre ((⋃ p : curveIdx u, curvePiece γ u p '' Set.Icc (0 : ℝ) 1)
      ∪ (⋃ f : ↥F, ({f.1} : Set (EuclideanSpace ℝ (Fin n))))) :=
    (isMeagre_iUnion hpiece).union hFm
  rw [iUnion_curvePiece_image hu γ] at htot
  rw [show (⋃ f : ↥F, ({f.1} : Set (EuclideanSpace ℝ (Fin n)))) = F from by
    ext z; simp] at htot
  exact htot


/-! ## Points equidistant from two distinct points -/

/-- The set of points equidistant from two distinct points of a real inner product space has empty
interior. -/
lemma interior_setOf_dist_eq_empty' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {u v : E} (huv : u ≠ v) : interior {y : E | dist u y = dist v y} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hz)
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  have hpos : 0 < ‖v - u‖ := norm_pos_iff.mpr hvu
  set t : ℝ := ε / (2 * (‖v - u‖ + 1)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have htε : t * ‖v - u‖ < ε := by
    rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set y : E := z + t • (v - u) with hy
  have hyball : y ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, hy, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg htpos.le]
    exact htε
  have hzS : dist u z = dist v z :=
    interior_subset (s := {y : E | dist u y = dist v y}) hz
  have hyS : dist u y = dist v y :=
    interior_subset (s := {y : E | dist u y = dist v y}) (hεsub hyball)
  have hz2 : ‖z - u‖ ^ 2 = ‖z - v‖ ^ 2 := by
    have h := hzS
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev u z, norm_sub_rev v z] at h
    rw [h]
  have hy2 : ‖y - u‖ ^ 2 = ‖y - v‖ ^ 2 := by
    have h := hyS
    rw [dist_eq_norm, dist_eq_norm, norm_sub_rev u y, norm_sub_rev v y] at h
    rw [h]
  have hkey : ‖y - u‖ ^ 2 - ‖y - v‖ ^ 2
      = (‖z - u‖ ^ 2 - ‖z - v‖ ^ 2) + 2 * t * ‖v - u‖ ^ 2 := by
    have h1 : y - u = (z - u) + t • (v - u) := by rw [hy]; abel
    have h2 : y - v = (z - v) + t • (v - u) := by rw [hy]; abel
    rw [h1, h2, norm_add_sq_real, norm_add_sq_real]
    have h3 : inner ℝ (z - u) (t • (v - u)) - inner ℝ (z - v) (t • (v - u))
        = t * ‖v - u‖ ^ 2 := by
      rw [real_inner_smul_right, real_inner_smul_right, ← mul_sub, ← inner_sub_left]
      have h4 : (z - u) - (z - v) = v - u := by abel
      rw [h4, real_inner_self_eq_norm_sq]
    linarith
  rw [hy2, hz2] at hkey
  have hzero : 2 * t * ‖v - u‖ ^ 2 = 0 := by linarith
  rcases mul_eq_zero.mp hzero with h2 | h2
  · nlinarith [htpos, hpos]
  · exact absurd h2 (pow_ne_zero 2 (ne_of_gt hpos))

/-! ## A good centre -/

/-- **Good centre.**  Near every point there is a centre `y` outside `K = γ '' u ∪ F` such that
every sphere around `y` meets `K` in a totally disconnected set. -/
theorem exists_good_center (hn : 2 ≤ n) {u : Set ℝ} (hu : IsOpen u)
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} (hγ : Continuous γ) (hγinj : Set.InjOn γ u)
    (hcpt : IsCompact (γ '' u)) (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Finite)
    (x : EuclideanSpace ℝ (Fin n)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ y : EuclideanSpace ℝ (Fin n), dist y x < ρ ∧ y ∉ (γ '' u) ∪ F ∧
      ∀ t : ℝ, IsTotallyDisconnected (((γ '' u) ∪ F) ∩ Metric.sphere y t) := by
  classical
  -- the bad centres: for each rational interval, the equidistant hyperplane of its endpoints
  have hbad : ∀ p : curveIdx u, IsMeagre
      {y : EuclideanSpace ℝ (Fin n) | dist (γ (p.1.1 : ℝ)) y = dist (γ (p.1.2 : ℝ)) y} := by
    intro p
    have hab : (p.1.1 : ℝ) < (p.1.2 : ℝ) := by exact_mod_cast p.2.1
    have hne : γ (p.1.1 : ℝ) ≠ γ (p.1.2 : ℝ) := fun hcon =>
      (ne_of_lt hab) (hγinj (p.2.2 ⟨le_rfl, le_of_lt hab⟩) (p.2.2 ⟨le_of_lt hab, le_rfl⟩) hcon)
    have hnd : IsNowhereDense
        {y : EuclideanSpace ℝ (Fin n) | dist (γ (p.1.1 : ℝ)) y = dist (γ (p.1.2 : ℝ)) y} := by
      refine (IsClosed.isNowhereDense_iff (isClosed_eq (continuous_const.dist continuous_id)
        (continuous_const.dist continuous_id))).mpr ?_
      exact interior_setOf_dist_eq_empty' hne
    exact (isMeagre_iff_countable_union_isNowhereDense).mpr
      ⟨{_}, by rintro t rfl; exact hnd, Set.countable_singleton _,
        by intro y hy; exact ⟨_, rfl, hy⟩⟩
  have hB : IsMeagre (⋃ p : curveIdx u,
      {y : EuclideanSpace ℝ (Fin n) | dist (γ (p.1.1 : ℝ)) y = dist (γ (p.1.2 : ℝ)) y}) :=
    isMeagre_iUnion hbad
  have hKm : IsMeagre ((γ '' u) ∪ F) := curve_union_meagre hn hu hγ hγinj F hF
  have htot : IsMeagre ((⋃ p : curveIdx u,
      {y : EuclideanSpace ℝ (Fin n) | dist (γ (p.1.1 : ℝ)) y = dist (γ (p.1.2 : ℝ)) y})
      ∪ ((γ '' u) ∪ F)) := hB.union hKm
  -- a point of `ball x ρ` avoiding the whole bad set
  have hne : ∃ y : EuclideanSpace ℝ (Fin n), y ∈ Metric.ball x ρ ∧
      y ∉ (⋃ p : curveIdx u,
        {y : EuclideanSpace ℝ (Fin n) | dist (γ (p.1.1 : ℝ)) y = dist (γ (p.1.2 : ℝ)) y})
        ∪ ((γ '' u) ∪ F) := by
    by_contra hcon
    refine not_isMeagre_of_isOpen Metric.isOpen_ball ⟨x, mem_ball_self hρ⟩
      (IsMeagre.mono (t := Metric.ball x ρ) (fun y hy => ?_) htot)
    by_contra hyS
    exact hcon ⟨y, hy, hyS⟩
  obtain ⟨y, hyball, hyout⟩ := hne
  have hyB : ∀ p : curveIdx u,
      dist (γ (p.1.1 : ℝ)) y ≠ dist (γ (p.1.2 : ℝ)) y := fun p hcon =>
    hyout (Or.inl (Set.mem_iUnion.mpr ⟨p, hcon⟩))
  have hyK : y ∉ (γ '' u) ∪ F := fun h => hyout (Or.inr h)
  refine ⟨y, Metric.mem_ball.mp hyball, hyK, fun t => ?_⟩
  -- the "good" property of the centre
  have hgood : ∀ p : curveIdx u, ∃ s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ),
      dist (γ s) y ≠ dist (γ (p.1.1 : ℝ)) y := by
    intro p
    by_contra hcon
    push_neg at hcon
    exact hyB p (hcon (p.1.2 : ℝ) ⟨le_of_lt (by exact_mod_cast p.2.1), le_rfl⟩).symm
  -- the parameter sets of the slices
  have hQcpt : ∀ p : curveIdx u, IsCompact
      {s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) ∧ dist (γ s) y = t} := fun p =>
    isCompact_Icc.of_isClosed_subset
      (isClosed_Icc.inter (isClosed_eq ((hγ.comp continuous_id).dist continuous_const)
        continuous_const)) (fun z hz => hz.1)
  have hQtd : ∀ p : curveIdx u, IsTotallyDisconnected
      {s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) ∧ dist (γ s) y = t} := by
    intro p
    rw [isTotallyDisconnected_iff_lt]
    intro s hs s' hs' hss'
    by_contra hcon
    have hsub : Set.Ioo s s' ⊆
        {s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) ∧ dist (γ s) y = t} := by
      intro z hz
      by_contra hzq
      exact hcon ⟨z, hzq, hz⟩
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hss'
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
    have hab : (a : ℝ) < (b : ℝ) := hb1
    have hIccu : Set.Icc (a : ℝ) (b : ℝ) ⊆ u := fun z hz =>
      p.2.2 (hsub ⟨lt_of_lt_of_le ha1 hz.1, lt_of_le_of_lt hz.2 hb2⟩).1
    obtain ⟨c, hc, hcne⟩ := hgood ⟨(a, b), by exact_mod_cast hab, hIccu⟩
    have hcq := hsub ⟨lt_of_lt_of_le ha1 hc.1, lt_of_le_of_lt hc.2 hb2⟩
    have haq := hsub ⟨ha1, lt_trans hab hb2⟩
    exact hcne (by rw [hcq.2, haq.2])
  have hpiece : ∀ p : curveIdx u, IsTotallyDisconnected
      (γ '' {s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) ∧ dist (γ s) y = t}) := by
    intro p
    haveI : CompactSpace ↥{s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
        ∧ dist (γ s) y = t} := isCompact_iff_compactSpace.mp (hQcpt p)
    have hcont : Continuous fun τ : ↥{s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
        ∧ dist (γ s) y = t} => γ (τ : ℝ) := hγ.comp continuous_subtype_val
    have hinj : Function.Injective fun τ : ↥{s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
        ∧ dist (γ s) y = t} => γ (τ : ℝ) :=
      fun a b hab' => Subtype.ext (hγinj (p.2.2 a.2.1) (p.2.2 b.2.1) hab')
    have hclosedmap : IsClosedMap fun τ : ↥{s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
        ∧ dist (γ s) y = t} => γ (τ : ℝ) := fun s hs =>
      (hs.isCompact.image hcont).isClosed
    have hemb : Topology.IsEmbedding fun τ : ↥{s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
        ∧ dist (γ s) y = t} => γ (τ : ℝ) :=
      (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hcont hinj hclosedmap).isEmbedding
    have hrange : (fun τ : ↥{s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
        ∧ dist (γ s) y = t} => γ (τ : ℝ)) '' Set.univ
        = γ '' {s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ) ∧ dist (γ s) y = t} := by
      ext z
      constructor
      · rintro ⟨τ, -, rfl⟩; exact ⟨τ.1, τ.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩; exact ⟨⟨s, hs⟩, trivial, rfl⟩
    rw [← hrange]
    haveI : TotallyDisconnectedSpace ↥{s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
        ∧ dist (γ s) y = t} := totallyDisconnectedSpace_subtype_iff.mpr (hQtd p)
    exact (hemb.isTotallyDisconnected_image (s := Set.univ)).mpr
      TotallyDisconnectedSpace.isTotallyDisconnected_univ
  have hUnion : (⋃ p : curveIdx u, γ '' {s : ℝ | s ∈ Set.Icc (p.1.1 : ℝ) (p.1.2 : ℝ)
      ∧ dist (γ s) y = t}) = (γ '' u) ∩ Metric.sphere y t := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hz
      obtain ⟨s, hs, rfl⟩ := hp
      exact ⟨⟨s, p.2.2 hs.1, rfl⟩, Metric.mem_sphere.mpr hs.2⟩
    · rintro ⟨⟨s, hsu, rfl⟩, hz⟩
      obtain ⟨p, hp⟩ := exists_curveIdx_mem hu hsu
      exact Set.mem_iUnion.mpr ⟨p, ⟨s, ⟨hp, Metric.mem_sphere.mp hz⟩, rfl⟩⟩
  have hcompact : IsCompact ((γ '' u) ∩ Metric.sphere y t) := hcpt.inter_right Metric.isClosed_sphere
  have htd : IsTotallyDisconnected ((γ '' u) ∩ Metric.sphere y t) := by
    rw [← hUnion]
    exact isTotallyDisconnected_of_isCompact_biUnion (fun p => (hQcpt p).image hγ)
      (fun p => hpiece p) (by rw [hUnion]; exact hcompact)
  rw [Set.union_inter_distrib_right]
  exact isTotallyDisconnected_union_finite hcompact htd (hF.subset (fun z hz => hz.1))

/-! ## A hyperplane slice through an exterior point -/

/-- **A hyperplane slice.**  Through every point outside `γ '' u ∪ F` there is a hyperplane whose
intersection with `γ '' u ∪ F` is totally disconnected. -/
theorem exists_hyperplane_slice_td (hn : 3 ≤ n) {u : Set ℝ} (hu : IsOpen u)
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} (hγ : Continuous γ) (hγinj : Set.InjOn γ u)
    (hcpt : IsCompact (γ '' u)) (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Finite)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ (γ '' u) ∪ F) :
    ∃ e : EuclideanSpace ℝ (Fin n), e ≠ 0 ∧ IsTotallyDisconnected
      (((γ '' u) ∪ F) ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - x) e = 0}) := by
  obtain ⟨e, he0, htd⟩ := exists_hyperplane_slice_isTotallyDisconnected (n := n) hn
    (g := curvePiece γ u) (fun p => curvePiece_continuous hγ p) (fun p => curvePiece_injOn hγinj p)
    (x := x) (fun p hz => hx (Or.inl (curvePiece_image_subset u γ p hz)))
    (isCompact_iUnion_curvePiece_image hu hcpt)
  refine ⟨e, he0, ?_⟩
  rw [iUnion_curvePiece_image hu γ] at htd
  rw [Set.union_inter_distrib_right]
  have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - x) e = 0} :=
    isClosed_eq ((continuous_id.sub continuous_const).inner continuous_const) continuous_const
  exact isTotallyDisconnected_union_finite (hcpt.inter_right hclosed) htd
    (hF.subset (fun z hz => hz.1))


/-! ## Local room from totally disconnected shells -/

/-! ## Spheres in a hyperplane -/

section SliceSpine

/-- In the hyperplane `{z | ⟪z - c, e⟫ = 0}` through `c` orthogonal to `e ≠ 0`, the spheres around
`c` are the images of the spheres of the orthogonal complement of `e`. -/
lemma hyperplane_sphere_eq {n : ℕ} {c e : EuclideanSpace ℝ (Fin n)} {t : ℝ} :
    {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - c) e = 0} ∩ Metric.sphere c t
      = (fun w : ↥((ℝ ∙ e)ᗮ) => c + (w : EuclideanSpace ℝ (Fin n))) ''
          Metric.sphere (0 : ↥((ℝ ∙ e)ᗮ)) t := by
  ext z
  constructor
  · rintro ⟨hz1, hz2⟩
    have hmem : z - c ∈ (ℝ ∙ e)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [real_inner_smul_left, real_inner_comm, hz1, mul_zero]
    refine ⟨⟨z - c, hmem⟩, ?_, ?_⟩
    · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, Submodule.coe_norm]
      have h' := Metric.mem_sphere.mp hz2
      rw [dist_eq_norm] at h'
      exact h'
    · show c + ((⟨z - c, hmem⟩ : ↥((ℝ ∙ e)ᗮ)) : EuclideanSpace ℝ (Fin n)) = z
      rw [Subtype.coe_mk]
      abel
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · show inner ℝ (c + (w : EuclideanSpace ℝ (Fin n)) - c) e = 0
      rw [add_sub_cancel_left, real_inner_comm]
      exact (Submodule.mem_orthogonal (ℝ ∙ e) _).mp w.2 e (Submodule.mem_span_singleton_self e)
    · rw [Metric.mem_sphere, dist_eq_norm]
      have hwn : ‖(w : EuclideanSpace ℝ (Fin n))‖ = t := by
        have h' := Metric.mem_sphere.mp hw
        rw [dist_eq_norm, sub_zero, Submodule.coe_norm] at h'
        exact h'
      simpa [add_sub_cancel_left] using hwn

/-- A sphere in a hyperplane is preconnected (`3 ≤ n`). -/
lemma hyperplane_sphere_preconnected {n : ℕ} (hn : 3 ≤ n) {c e : EuclideanSpace ℝ (Fin n)}
    (he : e ≠ 0) {t : ℝ} :
    IsPreconnected ({z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - c) e = 0}
      ∩ Metric.sphere c t) := by
  have hfin : 2 ≤ Module.finrank ℝ ↥((ℝ ∙ e)ᗮ) := by
    have h1 : Module.finrank ℝ ↥(ℝ ∙ e) = 1 := finrank_span_singleton he
    have h2 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
    rw [finrank_euclideanSpace_fin, h1] at h2
    omega
  have hrank : (1 : Cardinal) < Module.rank ℝ ↥((ℝ ∙ e)ᗮ) := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (by omega : 1 < Module.finrank ℝ ↥((ℝ ∙ e)ᗮ))
  rw [hyperplane_sphere_eq]
  exact (isPreconnected_sphere hrank 0 t).image _ (by fun_prop)

/-- A sphere in a hyperplane is nondegenerate (`3 ≤ n`, `0 < t`). -/
lemma hyperplane_sphere_nondegenerate {n : ℕ} (hn : 3 ≤ n) {c e : EuclideanSpace ℝ (Fin n)}
    (he : e ≠ 0) {t : ℝ} (ht : 0 < t) :
    ∃ p q, p ≠ q ∧
      p ∈ ({z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - c) e = 0} ∩ Metric.sphere c t) ∧
      q ∈ ({z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - c) e = 0} ∩ Metric.sphere c t) := by
  have hfin : 2 ≤ Module.finrank ℝ ↥((ℝ ∙ e)ᗮ) := by
    have h1 : Module.finrank ℝ ↥(ℝ ∙ e) = 1 := finrank_span_singleton he
    have h2 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
    rw [finrank_euclideanSpace_fin, h1] at h2
    omega
  haveI : Nontrivial ↥((ℝ ∙ e)ᗮ) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : ↥((ℝ ∙ e)ᗮ), w₀ ≠ 0 := exists_ne 0
  have hw₀n : 0 < ‖w₀‖ := norm_pos_iff.mpr hw₀
  set w : ↥((ℝ ∙ e)ᗮ) := (t / ‖w₀‖) • w₀ with hw
  have hwn : ‖w‖ = t := by
    rw [hw, norm_smul, Real.norm_of_nonneg (by positivity),
      div_mul_cancel₀ _ (ne_of_gt hw₀n)]
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwn
    linarith
  have hmem : w ∈ Metric.sphere (0 : ↥((ℝ ∙ e)ᗮ)) t :=
    Metric.mem_sphere.mpr (by rw [dist_eq_norm, sub_zero]; exact hwn)
  have hmem' : -w ∈ Metric.sphere (0 : ↥((ℝ ∙ e)ᗮ)) t :=
    Metric.mem_sphere.mpr (by rw [dist_eq_norm, sub_zero, norm_neg]; exact hwn)
  have hφinj : Function.Injective (fun u : ↥((ℝ ∙ e)ᗮ) => c + (u : EuclideanSpace ℝ (Fin n))) :=
    fun a b hab => Subtype.ext (add_left_cancel hab)
  have hne : c + (w : EuclideanSpace ℝ (Fin n))
      ≠ c + ((-w : ↥((ℝ ∙ e)ᗮ)) : EuclideanSpace ℝ (Fin n)) := by
    intro h
    have h' : w = -w := hφinj h
    have h2 : w + w = 0 := by
      simpa only [neg_add_cancel] using congrArg (fun u : ↥((ℝ ∙ e)ᗮ) => u + w) h'
    have h3 : (2 : ℝ) • w = 0 := by rw [two_smul]; exact h2
    rcases smul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact hwne h4
  exact ⟨c + (w : EuclideanSpace ℝ (Fin n)),
    c + ((-w : ↥((ℝ ∙ e)ᗮ)) : EuclideanSpace ℝ (Fin n)), hne,
    (hyperplane_sphere_eq ▸ Set.mem_image_of_mem _ hmem),
    (hyperplane_sphere_eq ▸ Set.mem_image_of_mem _ hmem')⟩

end SliceSpine

/-- A union of preconnected sets each meeting a common preconnected set is preconnected. -/
lemma isPreconnected_iUnion_of_meet {X : Type*} [TopologicalSpace X] {S : Set X} {ι : Type*}
    {F : ι → Set X} (hS : IsPreconnected S) (hF : ∀ i, IsPreconnected (F i))
    (hmeet : ∀ i, (F i ∩ S).Nonempty) : IsPreconnected (S ∪ ⋃ i, F i) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv huvd
  have hSuv : S ⊆ u ∪ v := fun z hz => huv (Or.inl hz)
  have hSd : S ∩ (u ∩ v) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hzu, hzv⟩
    exact Set.eq_empty_iff_forall_notMem.mp huvd z ⟨Or.inl hz, hzu, hzv⟩
  have hFid : ∀ i, F i ∩ (u ∩ v) = ∅ := by
    intro i
    rw [Set.eq_empty_iff_forall_notMem]
    rintro w ⟨hw, hwu, hwv⟩
    exact Set.eq_empty_iff_forall_notMem.mp huvd w
      ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, hw⟩), hwu, hwv⟩
  have hFiuv : ∀ i, F i ⊆ u ∪ v := fun i w hw =>
    huv (Or.inr (Set.mem_iUnion.mpr ⟨i, hw⟩))
  rcases (isPreconnected_iff_subset_of_disjoint.mp hS) u v hu hv hSuv hSd with h | h
  · left
    intro z hz
    rcases hz with hz | hz
    · exact h hz
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      rcases (isPreconnected_iff_subset_of_disjoint.mp (hF i)) u v hu hv (hFiuv i) (hFid i)
        with h' | h'
      · exact h' hi
      · exfalso
        obtain ⟨w, hwF, hwS⟩ := hmeet i
        exact Set.eq_empty_iff_forall_notMem.mp hSd w ⟨hwS, h hwS, h' hwF⟩
  · right
    intro z hz
    rcases hz with hz | hz
    · exact h hz
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      rcases (isPreconnected_iff_subset_of_disjoint.mp (hF i)) u v hu hv (hFiuv i) (hFid i)
        with h' | h'
      · exfalso
        obtain ⟨w, hwF, hwS⟩ := hmeet i
        exact Set.eq_empty_iff_forall_notMem.mp hSd w ⟨hwS, h' hwF, h hwS⟩
      · exact h' hi

/-- **Local room at a point of a compact set with totally disconnected shells.** -/
theorem local_room_of_good_center {n : ℕ} (hn : 3 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ K) {ε : ℝ} (hε : 0 < ε)
    (hcenter : ∀ x : EuclideanSpace ℝ (Fin n), ∀ ρ : ℝ, 0 < ρ →
      ∃ y : EuclideanSpace ℝ (Fin n), dist y x < ρ ∧ y ∉ K ∧
        ∀ t : ℝ, IsTotallyDisconnected (K ∩ Metric.sphere y t))
    (hslice : ∀ x : EuclideanSpace ℝ (Fin n), x ∉ K →
      ∃ e : EuclideanSpace ℝ (Fin n), e ≠ 0 ∧
        IsTotallyDisconnected (K ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - x) e = 0}))
    (hspine : ∀ {y : EuclideanSpace ℝ (Fin n)}, y ∉ K →
      ∀ {e : EuclideanSpace ℝ (Fin n)}, e ≠ 0 →
      IsTotallyDisconnected (K ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0}) →
      ∀ R : ℝ, 0 < R → IsPathConnected
        (({z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0} ∩ Metric.ball y R) \ K)) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ a ∈ O ∧ O ⊆ Metric.ball a ε ∧
      IsPathConnected (O \ K) := by
  classical
  obtain ⟨y₁, hy₁dist, hy₁K, hcen⟩ := hcenter a (ε / 4) (by linarith)
  have hya : dist y₁ a < ε / 4 := hy₁dist
  set R : ℝ := ε / 2 with hR
  have hRpos : 0 < R := by rw [hR]; linarith
  have ha_mem : a ∈ Metric.ball y₁ R := by
    rw [Metric.mem_ball, dist_comm a y₁]; linarith
  have hsub : Metric.ball y₁ R ⊆ Metric.ball a ε := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    calc dist z a ≤ dist z y₁ + dist y₁ a := dist_triangle _ _ _
      _ < R + ε / 4 := by linarith
      _ ≤ ε := by rw [hR]; linarith
  -- the hyperplane through `y₁`
  obtain ⟨e, he0, hHtd⟩ := hslice y₁ hy₁K
  set H : Set (EuclideanSpace ℝ (Fin n)) := {z | inner ℝ (z - y₁) e = 0} with hHdef
  have hHtd' : IsTotallyDisconnected (K ∩ H) := hHtd
  -- the spine
  have hspine' : IsPathConnected ((H ∩ Metric.ball y₁ R) \ K) := hspine hy₁K he0 hHtd' R hRpos
  -- the shells are preconnected
  have hshell : ∀ t : ℝ, IsPreconnected (Metric.sphere y₁ t \ K) := by
    intro t
    by_cases ht : t ≤ 0
    · have hsub' : Metric.sphere y₁ t \ K ⊆ ({y₁} : Set (EuclideanSpace ℝ (Fin n))) := by
        intro z hz
        rw [Set.mem_singleton_iff]
        have h1 : dist z y₁ = t := Metric.mem_sphere.mp hz.1
        have h3 : (0 : ℝ) ≤ dist z y₁ := dist_nonneg
        rw [h1] at h3
        have ht0 : t = 0 := le_antisymm ht h3
        exact dist_eq_zero.mp (by rw [h1, ht0])
      have hsing : (Metric.sphere y₁ t \ K).Subsingleton :=
        fun x hx y hy => (Set.mem_singleton_iff.mp (hsub' hx)).trans
          (Set.mem_singleton_iff.mp (hsub' hy)).symm
      refine isPreconnected_iff_subset_of_disjoint.mpr ?_
      intro u v hu hv huv huvd
      by_cases hne : (Metric.sphere y₁ t \ K).Nonempty
      · obtain ⟨x, hx⟩ := hne
        rcases huv hx with hxu | hxv
        · exact Or.inl fun y hy => by rw [hsing hy hx]; exact hxu
        · exact Or.inr fun y hy => by rw [hsing hy hx]; exact hxv
      · exact Or.inl fun y hy => absurd ⟨y, hy⟩ hne
    · have h := sphere_sdiff_isCompact_totallyDisconnected_isPreconnected
        (E := EuclideanSpace ℝ (Fin n)) (by rw [finrank_euclideanSpace_fin]; omega)
        (not_le.mp ht)
        (K := K ∩ Metric.sphere y₁ t) (hK.inter_right Metric.isClosed_sphere)
        Set.inter_subset_right (hcen t)
      rwa [show Metric.sphere y₁ t \ (K ∩ Metric.sphere y₁ t) = Metric.sphere y₁ t \ K from by
        ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto] at h
  -- every shell meets the spine
  have hmeet : ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) R →
      ((Metric.sphere y₁ t \ K) ∩ ((H ∩ Metric.ball y₁ R) \ K)).Nonempty := by
    intro t ht
    have hpre := hyperplane_sphere_preconnected hn he0 (c := y₁) (t := t)
    obtain ⟨p, q, hpq, hp, hq⟩ := hyperplane_sphere_nondegenerate hn he0 (c := y₁) ht.1
    have hex : ∃ z, z ∈ H ∩ Metric.sphere y₁ t ∧ z ∉ K := by
      by_contra hcon
      have hKsub : H ∩ Metric.sphere y₁ t ⊆ K := by
        intro z hz
        by_contra hzK
        exact hcon ⟨z, hz, hzK⟩
      have hsing : (H ∩ Metric.sphere y₁ t).Subsingleton :=
        (hcen t) _ (fun w hw => ⟨hKsub hw, hw.2⟩) hpre
      exact hpq (hsing hp hq)
    obtain ⟨z, hz, hzK⟩ := hex
    exact ⟨z, ⟨hz.2, hzK⟩, ⟨hz.1, Metric.mem_ball.mpr (by
      rw [Metric.mem_sphere.mp hz.2]; exact ht.2)⟩, hzK⟩
  -- the spine together with the shells is the room
  have hset : ((H ∩ Metric.ball y₁ R) \ K)
      ∪ ⋃ t : ↥(Set.Ioo (0 : ℝ) R), (Metric.sphere y₁ (t : ℝ) ∩ Metric.ball y₁ R) \ K
      = Metric.ball y₁ R \ K := by
    apply Subset.antisymm
    · intro z hz
      rcases hz with hz | hz
      · exact ⟨hz.1.2, hz.2⟩
      · obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
        exact ⟨ht.1.2, ht.2⟩
    · intro z hz
      rcases eq_or_ne z y₁ with rfl | hz1
      · exact Or.inl ⟨⟨by simp [hHdef], Metric.mem_ball_self hRpos⟩, hy₁K⟩
      · right
        have htd : dist z y₁ ∈ Set.Ioo (0 : ℝ) R :=
          ⟨dist_pos.mpr hz1, Metric.mem_ball.mp hz.1⟩
        exact Set.mem_iUnion.mpr ⟨⟨dist z y₁, htd⟩,
          ⟨⟨Metric.mem_sphere.mpr rfl, hz.1⟩, hz.2⟩⟩
  have hpc : IsPreconnected (Metric.ball y₁ R \ K) := by
    rw [← hset]
    refine isPreconnected_iUnion_of_meet hspine'.isConnected.2 (fun t => ?_) (fun t => ?_)
    · -- a shell piece is preconnected
      rw [show (Metric.sphere y₁ (t : ℝ) ∩ Metric.ball y₁ R) \ K = Metric.sphere y₁ (t : ℝ) \ K
        from by
        ext z; constructor
        · rintro ⟨⟨hz1, hz2⟩, hzK⟩; exact ⟨hz1, hzK⟩
        · rintro ⟨hz1, hzK⟩
          exact ⟨⟨hz1, Metric.mem_ball.mpr (by
            rw [Metric.mem_sphere.mp hz1]; exact t.2.2)⟩, hzK⟩]
      exact hshell (t : ℝ)
    · -- it meets the spine
      obtain ⟨z, hz⟩ := hmeet (t : ℝ) t.2
      exact ⟨z, ⟨⟨hz.1.1, hz.2.1.2⟩, hz.1.2⟩, hz.2⟩
  have hOpc : IsPathConnected (Metric.ball y₁ R \ K) := by
    have hopen : IsOpen (Metric.ball y₁ R \ K) := Metric.isOpen_ball.sdiff hK.isClosed
    rw [← hopen.isConnected_iff_isPathConnected]
    exact ⟨⟨y₁, Metric.mem_ball_self hRpos, hy₁K⟩, hpc⟩
  exact ⟨Metric.ball y₁ R, Metric.isOpen_ball, ha_mem, hsub, hOpc⟩


/-! ## Unrestricted ball removability, and the spine -/

/-- **Removability in a ball.**  In a finite dimensional real inner product space of dimension
`≥ 2`, an open ball minus a compact totally disconnected set is path connected (no hypothesis that
the set lie in the ball).  This is the classical fact that a compact zero-dimensional set does not
separate a ball. -/
theorem ball_sdiff_compact_td {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hm : 2 ≤ Module.finrank ℝ E)
    {c : E} {r : ℝ} (hr : 0 < r) {K : Set E} (hK : IsCompact K)
    (htd : IsTotallyDisconnected K) : IsPathConnected (Metric.ball c r \ K) :=
  ball_sdiff_totallyDisconnected_unrestricted hm hr hK htd

/-- The slice of a ball by a hyperplane through its centre, with a totally disconnected compact set
removed, is path connected (`3 ≤ n`). -/
theorem slice_ball_sdiff_pathConnected {n : ℕ} (hn : 3 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {y e : EuclideanSpace ℝ (Fin n)} (he : e ≠ 0)
    (hHtd : IsTotallyDisconnected (K ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0}))
    {R : ℝ} (hR : 0 < R) :
    IsPathConnected (({z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0}
      ∩ Metric.ball y R) \ K) := by
  classical
  have hfin : 2 ≤ Module.finrank ℝ ↥((ℝ ∙ e)ᗮ) := by
    have h1 : Module.finrank ℝ ↥(ℝ ∙ e) = 1 := finrank_span_singleton he
    have h2 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ e)
    rw [finrank_euclideanSpace_fin, h1] at h2
    omega
  set φ : ↥((ℝ ∙ e)ᗮ) → EuclideanSpace ℝ (Fin n) :=
    fun w => y + (w : EuclideanSpace ℝ (Fin n)) with hφ
  have hφcont : Continuous φ := continuous_const.add continuous_subtype_val
  have hφinj : Function.Injective φ := fun a b hab => Subtype.ext (add_left_cancel hab)
  set K' : Set ↥((ℝ ∙ e)ᗮ) := φ ⁻¹' K with hK'
  have hmemH : ∀ w : ↥((ℝ ∙ e)ᗮ), inner ℝ (φ w - y) e = 0 := by
    intro w
    show inner ℝ (y + (w : EuclideanSpace ℝ (Fin n)) - y) e = 0
    rw [add_sub_cancel_left, real_inner_comm]
    exact (Submodule.mem_orthogonal (ℝ ∙ e) _).mp w.2 e (Submodule.mem_span_singleton_self e)
  have hball_eq : φ '' Metric.ball (0 : ↥((ℝ ∙ e)ᗮ)) R
      = {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0} ∩ Metric.ball y R := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hmemH w, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm]
      have h' := Metric.mem_ball.mp hw
      rw [dist_eq_norm, sub_zero, Submodule.coe_norm] at h'
      simpa [hφ, add_sub_cancel_left] using h'
    · rintro ⟨hz1, hz2⟩
      have hmem : z - y ∈ (ℝ ∙ e)ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [real_inner_smul_left, real_inner_comm, hz1, mul_zero]
      refine ⟨⟨z - y, hmem⟩, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, sub_zero, Submodule.coe_norm]
        have h' := Metric.mem_ball.mp hz2
        rw [dist_eq_norm] at h'
        exact h'
      · show y + ((⟨z - y, hmem⟩ : ↥((ℝ ∙ e)ᗮ)) : EuclideanSpace ℝ (Fin n)) = z
        rw [Subtype.coe_mk]
        abel
  have hK'_eq : φ '' K' = K ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0} := by
    apply Subset.antisymm
    · rintro z ⟨w, hw, rfl⟩
      exact ⟨hw, hmemH w⟩
    · rintro z ⟨hzK, hzH⟩
      have hmem : z - y ∈ (ℝ ∙ e)ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [real_inner_smul_left, real_inner_comm, hzH, mul_zero]
      refine ⟨⟨z - y, hmem⟩, ?_, ?_⟩
      · show y + ((⟨z - y, hmem⟩ : ↥((ℝ ∙ e)ᗮ)) : EuclideanSpace ℝ (Fin n)) ∈ K
        rw [show y + ((⟨z - y, hmem⟩ : ↥((ℝ ∙ e)ᗮ)) : EuclideanSpace ℝ (Fin n)) = z from by
          rw [Subtype.coe_mk]; abel]
        exact hzK
      · show y + ((⟨z - y, hmem⟩ : ↥((ℝ ∙ e)ᗮ)) : EuclideanSpace ℝ (Fin n)) = z
        rw [Subtype.coe_mk]
        abel
  have hK'cpt : IsCompact K' := by
    have hclosed : IsClosed K' := hK.isClosed.preimage hφcont
    have hbdd : Bornology.IsBounded K' := by
      obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall y).mp hK.isBounded
      refine (Metric.isBounded_iff_subset_closedBall (0 : ↥((ℝ ∙ e)ᗮ))).mpr ⟨R₀, ?_⟩
      intro w hw
      rw [Metric.mem_closedBall]
      rw [hK'] at hw
      have h1 := hR₀ hw
      rw [Metric.mem_closedBall] at h1
      have h2 : dist w 0 = dist (φ w) y := by
        simp only [dist_eq_norm, hφ, sub_zero, Submodule.coe_norm, add_sub_cancel_left]
      rw [h2]
      exact h1
    exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩
  have hK'td : IsTotallyDisconnected K' := by
    intro P hPK hPpre
    have himgP : IsPreconnected (φ '' P) := hPpre.image φ hφcont.continuousOn
    have hsubP : φ '' P ⊆ K ∩ {z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0} := by
      rintro z ⟨w, hw, rfl⟩
      exact ⟨hPK hw, hmemH w⟩
    have hsing : (φ '' P).Subsingleton := hHtd _ hsubP himgP
    intro a ha b hb
    exact hφinj (hsing ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩)
  have hpc : IsPathConnected (Metric.ball (0 : ↥((ℝ ∙ e)ᗮ)) R \ K') :=
    ball_sdiff_compact_td hfin hR hK'cpt hK'td
  have himg : φ '' (Metric.ball (0 : ↥((ℝ ∙ e)ᗮ)) R \ K')
      = ({z : EuclideanSpace ℝ (Fin n) | inner ℝ (z - y) e = 0} ∩ Metric.ball y R) \ K := by
    rw [Set.image_sdiff hφinj, hball_eq, hK'_eq]
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [← himg]
  exact hpc.image hφcont

/-- **Local room at a point of the image of an open set under an injective curve.** -/
theorem local_room_image_open_of_injOn {n : ℕ} (hn : 3 ≤ n)
    {u : Set ℝ} (hu : IsOpen u) {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    (hγ : Continuous γ) (hγinj : Set.InjOn γ u) (hcpt : IsCompact (γ '' u))
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Finite)
    {a : EuclideanSpace ℝ (Fin n)} (ha : a ∈ (γ '' u) ∪ F) {ε : ℝ} (hε : 0 < ε) :
    ∃ O : Set (EuclideanSpace ℝ (Fin n)), IsOpen O ∧ a ∈ O ∧ O ⊆ Metric.ball a ε ∧
      IsPathConnected (O \ ((γ '' u) ∪ F)) := by
  classical
  have hKcpt : IsCompact ((γ '' u) ∪ F) := hcpt.union hF.isCompact
  exact local_room_of_good_center hn hKcpt ha hε
    (fun x ρ hρ => exists_good_center (by omega) hu hγ hγinj hcpt F hF x hρ)
    (fun x hx => exists_hyperplane_slice_td hn hu hγ hγinj hcpt F hF hx)
    (hspine := by
      intro y hyK e he hHtd R hR
      exact slice_ball_sdiff_pathConnected (K := (γ '' u) ∪ F) hn hKcpt he hHtd hR)

end Work.Whitney.PathTools
