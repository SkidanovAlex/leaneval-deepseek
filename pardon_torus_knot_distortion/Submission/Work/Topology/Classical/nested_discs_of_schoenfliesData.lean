import Mathlib
import Submission.Work.Topology.Classical.Defs

/-!
# The open discs of a `SchoenfliesData` are nested

Let `D : SchoenfliesData A ι c` be the conclusion of Jordan–Schoenflies on a sphere `A ⊆ ℝ³`
for a finite family of curves `c i`, and suppose the curve `c j` meets the *interior* of the
disc `e i` of `i` (i.e. `e i z ∈ range (c j)` for some interior point `z : 𝔻`).  Then the whole
open disc of `e j` is contained in the open disc of `e i`:

`{x ∈ A | ∃ z, ‖z‖ < 1 ∧ e j z = x} ⊆ {x ∈ A | ∃ z, ‖z‖ < 1 ∧ e i z = x}`.

This is the standard-position / nesting statement which makes the *innermost* argument work:
a curve lying inside the disc of `i` bounds therein a sub-disc which also lies inside it.

The proof only uses the clauses of `SchoenfliesData` (the covering clause `cover`, the
"the two discs meet exactly in the curve" clause `meet`, the openness of the interiors, and
the nesting clause `nested`), together with the elementary connectedness of the open unit disc
and the fact that the parametrised boundary of `𝔻` is the unit circle.

The argument is clean and purely topological.

* `A` is the disjoint union of the open disc `U i` of `e i`, the curve `K i = range (c i)`,
  and the open disc `U' i` of `e' i` (`range (e i)` is `U i ∪ K i` by the boundary
  parametrisation `circlePoint`, and `A` is the union of the two closed discs).
* `U i` and `U' i` are disjoint: a point of both lies in `range (e i) ∩ range (e' i) = range (c i)`.
* The nesting clause, applied in both orders, gives `rank j < rank i` (from `hint`) while
  *forbidding* `U j ∩ K i ≠ ∅` (a witness there would give `rank i < rank j`).  Hence
  `U j ∩ K i = ∅`, so `U j ⊆ U i ∪ U' i`.
* `U j` is connected (it is the image of the connected open unit disc under the continuous
  embedding `e j`), and it meets `U i` (a point of `U i` on the curve `c j` is the image of a
  boundary point of `𝔻`, and a point of `𝔻` just inside it maps into the open neighbourhood
  `U i` of that curve point).
* Two disjoint open sets (`U i`, `U' i`) covering a connected set (`U j`) that meets one of them:
  `U j ⊆ U i`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

theorem nested_discs_of_schoenfliesData
    {A : Set LeanEval.KnotTheory.PardonDistortion.R3}
    {ι : Type} [Fintype ι]
    {c : ι → ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (D : Work.Topology.Classical.SchoenfliesData A ι c)
    {i j : ι} (hij : i ≠ j)
    (hint : ∃ z : Work.InnermostDisk.Disc,
      ‖(z : ℂ)‖ < 1 ∧ D.e i z ∈ Set.range (c j)) :
    {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ D.e j z = (x : LeanEval.KnotTheory.PardonDistortion.R3)}
      ⊆ {x : A | ∃ z : Work.InnermostDisk.Disc, ‖(z : ℂ)‖ < 1 ∧ D.e i z = (x : LeanEval.KnotTheory.PardonDistortion.R3)} := by
  have _ : i ≠ j := hij
  -- the three pieces of `A` cut out by the curve `i`
  let U : ι → Set A := fun k => {x : A | ∃ z : Disc, ‖(z:ℂ)‖ < 1 ∧ D.e k z = (x : R3)}
  let U' : ι → Set A := fun k => {x : A | ∃ z : Disc, ‖(z:ℂ)‖ < 1 ∧ D.e' k z = (x : R3)}
  let K : ι → Set A := fun k => {x : A | (x : R3) ∈ Set.range (c k)}
  let DA : ι → Disc → A := fun k z => ⟨D.e k z, D.mem k z⟩
  let DA' : ι → Disc → A := fun k z => ⟨D.e' k z, D.mem' k z⟩
  have hzle : ∀ z : Disc, ‖(z:ℂ)‖ ≤ 1 := fun z => by
    have h := Metric.mem_closedBall.mp z.2
    simpa using h
  -- every point of the unit circle is `circlePoint t`
  have hnorm_circle : ∀ t : ℝ, ‖((circlePoint t : Disc) : ℂ)‖ = 1 := fun t => by
    rw [circlePoint_coe, Complex.norm_exp_ofReal_mul_I]
  -- `range (DA k) = U k ∪ K k`: the closed disc is its interior plus the curve
  have hran : ∀ k, Set.range (DA k) = U k ∪ K k := by
    intro k
    ext x
    constructor
    · rintro ⟨z, hzx⟩
      have hval : D.e k z = (x : R3) := congrArg Subtype.val hzx
      rcases lt_or_eq_of_le (hzle z) with hlt | heq
      · exact Or.inl ⟨z, hlt, hval⟩
      · obtain ⟨t, ht⟩ := exists_circlePoint_eq (z : ℂ) heq
        refine Or.inr ⟨t, ?_⟩
        rw [← D.boundary k t, Subtype.ext ht, hval]
    · rintro (⟨z, hz, hzx⟩ | ⟨t, ht⟩)
      · exact ⟨z, Subtype.ext hzx⟩
      · exact ⟨circlePoint t, Subtype.ext (by
          change D.e k (circlePoint t) = (x : R3)
          rw [D.boundary k t]; exact ht)⟩
  have hran' : ∀ k, Set.range (DA' k) = U' k ∪ K k := by
    intro k
    ext x
    constructor
    · rintro ⟨z, hzx⟩
      have hval : D.e' k z = (x : R3) := congrArg Subtype.val hzx
      rcases lt_or_eq_of_le (hzle z) with hlt | heq
      · exact Or.inl ⟨z, hlt, hval⟩
      · obtain ⟨t, ht⟩ := exists_circlePoint_eq (z : ℂ) heq
        refine Or.inr ⟨t, ?_⟩
        rw [← D.boundary' k t, Subtype.ext ht, hval]
    · rintro (⟨z, hz, hzx⟩ | ⟨t, ht⟩)
      · exact ⟨z, Subtype.ext hzx⟩
      · exact ⟨circlePoint t, Subtype.ext (by
          change D.e' k (circlePoint t) = (x : R3)
          rw [D.boundary' k t]; exact ht)⟩
  -- the two closed discs cover `A`
  have hcoverA : ∀ k, Set.range (DA k) ∪ Set.range (DA' k) = Set.univ := by
    intro k
    apply Set.eq_univ_of_forall
    intro x
    have hsub : A ⊆ Set.range (D.e k) ∪ Set.range (D.e' k) := by rw [D.cover k]
    rcases hsub x.2 with h | h
    · left; obtain ⟨z, hz⟩ := h; exact ⟨z, Subtype.ext hz⟩
    · right; obtain ⟨z, hz⟩ := h; exact ⟨z, Subtype.ext hz⟩
  -- the two closed discs meet exactly in the curve
  have hmeetA : ∀ k, Set.range (DA k) ∩ Set.range (DA' k) = K k := by
    intro k
    ext x
    constructor
    · rintro ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩
      have hmem : (x : R3) ∈ Set.range (D.e k) ∩ Set.range (D.e' k) :=
        ⟨⟨z, congrArg Subtype.val hz⟩, ⟨z', congrArg Subtype.val hz'⟩⟩
      rwa [D.meet k] at hmem
    · intro hx
      obtain ⟨t, ht⟩ := hx
      exact ⟨⟨circlePoint t, Subtype.ext (by
              change D.e k (circlePoint t) = (x : R3); rw [D.boundary k t]; exact ht)⟩,
             ⟨circlePoint t, Subtype.ext (by
              change D.e' k (circlePoint t) = (x : R3); rw [D.boundary' k t]; exact ht)⟩⟩
  -- the open disc and the curve are disjoint
  have hdisj_UK : ∀ k, Disjoint (U k) (K k) := by
    intro k
    rw [Set.disjoint_left]
    intro x hxU hxK
    obtain ⟨z, hz, hzx⟩ := hxU
    obtain ⟨t, ht⟩ := hxK
    have h1 : D.e k z = D.e k (circlePoint t) := by rw [D.boundary k t]; exact hzx.trans ht.symm
    have h2 : z = circlePoint t := D.inj k h1
    have h3 : ‖(z:ℂ)‖ = 1 := by rw [h2]; exact hnorm_circle t
    linarith
  have hdisj_U'K : ∀ k, Disjoint (U' k) (K k) := by
    intro k
    rw [Set.disjoint_left]
    intro x hxU hxK
    obtain ⟨z, hz, hzx⟩ := hxU
    obtain ⟨t, ht⟩ := hxK
    have h1 : D.e' k z = D.e' k (circlePoint t) := by rw [D.boundary' k t]; exact hzx.trans ht.symm
    have h2 : z = circlePoint t := D.inj' k h1
    have h3 : ‖(z:ℂ)‖ = 1 := by rw [h2]; exact hnorm_circle t
    linarith
  -- the two open discs are disjoint
  have hdisj_UU' : ∀ k, Disjoint (U k) (U' k) := by
    intro k
    rw [Set.disjoint_left]
    intro x hxU hxU'
    obtain ⟨z, hz, hzx⟩ := hxU
    obtain ⟨z', hz', hz'x⟩ := hxU'
    have hmem : x ∈ K k := by
      show (x : R3) ∈ Set.range (c k)
      rw [← D.meet k]
      exact ⟨⟨z, hzx⟩, ⟨z', hz'x⟩⟩
    exact (Set.disjoint_left.mp (hdisj_UK k)) ⟨z, hz, hzx⟩ hmem
  -- the open disc of `j` misses the curve of `i`
  have hUj_disj_Ki : Disjoint (U j) (K i) := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    obtain ⟨z, hz, hzx⟩ := hxU
    obtain ⟨t, ht⟩ := hxK
    have hej : D.e j z ∈ Set.range (c i) := ⟨t, ht.trans hzx.symm⟩
    have hlt : D.rank i < D.rank j := D.nested j i ⟨z, hz, hej⟩
    have hrank : D.rank j < D.rank i := D.nested i j hint
    omega
  -- hence `U j` is contained in the two open discs of `i`
  have hsub : U j ⊆ U i ∪ U' i := by
    intro x hx
    have h1 : x ∈ Set.range (DA i) ∪ Set.range (DA' i) := by
      rw [hcoverA i]; exact Set.mem_univ x
    rw [hran i, hran' i] at h1
    rcases h1 with (h | h) | (h | h)
    · exact Or.inl h
    · exact absurd h ((Set.disjoint_left.mp hUj_disj_Ki) hx)
    · exact Or.inr h
    · exact absurd h ((Set.disjoint_left.mp hUj_disj_Ki) hx)
  -- the open disc of `j` is connected
  have hcontDA : ∀ k, Continuous (DA k) := fun k =>
    Continuous.subtype_mk (D.e k).continuous (D.mem k)
  have hpre_disc : IsPreconnected ({z : Disc | ‖(z:ℂ)‖ < 1} : Set Disc) := by
    rw [← (Topology.IsInducing.subtypeVal (t := Metric.closedBall (0:ℂ) 1)).isPreconnected_image]
    have himg : (Subtype.val '' {z : Disc | ‖(z:ℂ)‖ < 1}) = Metric.ball (0:ℂ) 1 := by
      ext w
      simp only [Set.mem_image, Metric.mem_ball, dist_zero_right]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro hw
        exact ⟨⟨w, by simp only [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt hw⟩,
          hw, rfl⟩
    rw [himg]
    exact Metric.isPreconnected_ball
  have hpre : IsPreconnected (U j) := by
    have himg : U j = DA j '' {z : Disc | ‖(z:ℂ)‖ < 1} := by
      ext x
      constructor
      · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, Subtype.ext hzx⟩
      · rintro ⟨z, hz, hzx⟩; exact ⟨z, hz, congrArg Subtype.val hzx⟩
    rw [himg]
    exact hpre_disc.image (DA j) (hcontDA j).continuousOn
  -- points of `𝔻` arbitrarily close to a boundary point on the interior side
  have approx : ∀ (w₀ : Disc), ‖(w₀ : ℂ)‖ = 1 → ∀ δ > 0,
      ∃ w : Disc, ‖(w : ℂ)‖ < 1 ∧ dist w w₀ < δ := by
    intro w₀ hw₀ δ hδ
    set t : ℝ := min δ 1 / 2 with ht
    have htpos : 0 < t := by
      have : 0 < min δ 1 := lt_min hδ one_pos
      positivity
    have htle : t ≤ 1/2 := by
      have : min δ 1 ≤ 1 := min_le_right _ _
      linarith
    have htlt : t < δ := by
      have : min δ 1 ≤ δ := min_le_left _ _
      linarith
    refine ⟨⟨(1 - t) • (w₀ : ℂ), ?_⟩, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, hw₀, mul_one]
      rw [abs_le]; constructor <;> linarith
    · rw [norm_smul, Real.norm_eq_abs, hw₀, mul_one, abs_of_nonneg (by linarith)]
      linarith
    · rw [Subtype.dist_eq, dist_eq_norm]
      change ‖(1 - t) • (w₀ : ℂ) - (w₀ : ℂ)‖ < δ
      have hmove : (1 - t) • (w₀ : ℂ) - (w₀ : ℂ) = (-t) • (w₀ : ℂ) := by module
      rw [hmove, norm_smul, Real.norm_eq_abs, hw₀, mul_one, abs_neg, abs_of_pos htpos]
      exact htlt
  -- `U j` meets `U i`: the curve of `j` enters the open disc of `i` through its boundary
  have hmeet : (U j ∩ U i).Nonempty := by
    obtain ⟨z, hz, hzi⟩ := hint
    obtain ⟨t, ht⟩ := hzi
    have hpU : (⟨D.e i z, D.mem i z⟩ : A) ∈ U i := ⟨z, hz, rfl⟩
    have hpj : DA j (circlePoint t) = (⟨D.e i z, D.mem i z⟩ : A) := by
      apply Subtype.ext
      change D.e j (circlePoint t) = D.e i z
      rw [D.boundary j t]
      exact ht
    have hnhds : U i ∈ nhds (⟨D.e i z, D.mem i z⟩ : A) := (D.open_interior i).mem_nhds hpU
    rw [Metric.mem_nhds_iff] at hnhds
    obtain ⟨ε, hεpos, hεball⟩ := hnhds
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.mp ((hcontDA j).continuousAt (x := circlePoint t)) ε hεpos
    obtain ⟨w, hwlt, hwdist⟩ := approx (circlePoint t) (hnorm_circle t) δ hδpos
    refine ⟨DA j w, ⟨⟨w, hwlt, rfl⟩, ?_⟩⟩
    have hdist : dist (DA j w) (⟨D.e i z, D.mem i z⟩ : A) < ε := by
      have h2 := hδ (x := w) hwdist
      rwa [hpj] at h2
    exact hεball (Metric.mem_ball.mpr hdist)
  -- a connected set lying in two disjoint open sets and meeting one of them lies in it
  show U j ⊆ U i
  exact IsPreconnected.subset_left_of_subset_union (D.open_interior i) (D.open_interior' i)
    (hdisj_UU' i) hsub hmeet hpre

end Work.Topology.Classical
