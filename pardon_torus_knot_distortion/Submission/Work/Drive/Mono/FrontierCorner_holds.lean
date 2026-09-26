import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# The frontier of a level of the tilted sweep: the corner point-set computation

`Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam` is Pardon's box with the *closed* tilted
slab `{|⟪v,·⟫ - (⟪v,c⟫ + u)| ≤ h}` cut away on the side `{ℓ < lam}`.  The frontier of that removed
set, met inside the box, is the trace of the level (this is what `Mono/Split.lean` and
`Mono/Trace_eq_*` consume).  This file computes it exactly:

* a point `y` of the box which lies *above* the cut plane (`⟪v,c⟫ + u < ⟪v,y⟫`) is on the frontier of
  the removed set **iff** it sits on the far wall `{⟪v,·⟫ = ⟪v,c⟫ + u + h}` and not beyond the wall
  `{ℓ = lam}`, or it sits on the wall `{ℓ = lam}` and not beyond the far wall.

The two ingredients are purely point-set and are the reason the hypothesis `hanti` (the level
functional `ℓ` is *not* parallel to `⟪v,·⟫`) is needed:

* `closure (slab ∩ {ℓ < lam}) = slab ∩ {ℓ ≤ lam}`: on the boundary of the slab one has to move
  *along* the slab in order to decrease `ℓ`, which is possible precisely because `ℓ` does not vanish
  on `ker ⟪v,·⟫`;
* `interior (slab ∩ {ℓ < lam}) = {|⟪v,·⟫ - a| < h} ∩ {ℓ < lam}`: the interior of the slab is the open
  slab (here `v ≠ 0` is used: `⟪v,·⟫` is surjective).

The frontier statement itself is then the general fact that for open `B` and `y ∈ B`,
`y ∈ frontier (B \ A) ↔ y ∈ frontier A`, with `A` the slab piece cut away.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Drive.Mono

noncomputable section

variable {v : R3} {ℓ : R3 →L[ℝ] ℝ}

/-- Along a *non-zero* `v`, the functional `⟪v,·⟫` is surjective: some `u` has `⟪v,u⟫ = 1`. -/
lemma exists_inner_eq_one (hv : v ≠ 0) : ∃ u : R3, inner ℝ v u = 1 := by
  refine ⟨(‖v‖ ^ 2)⁻¹ • v, ?_⟩
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp

/-- If `ℓ` is not parallel to `⟪v,·⟫` (with `v ≠ 0`), then it does not vanish on `ker ⟪v,·⟫`:
there is `w` with `⟪v,w⟫ = 0` and `ℓ w < 0` (the sign is a choice of orientation). -/
lemma exists_ker_inner_ne {v : R3} (hv : v ≠ 0) {ℓ : R3 →L[ℝ] ℝ}
    (hanti : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v) :
    ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w < 0 := by
  have hex : ∃ w : R3, inner ℝ v w = 0 ∧ ℓ w ≠ 0 := by
    by_contra h
    push Not at h
    set u : R3 := (‖v‖ ^ 2)⁻¹ • v with hu
    have hu1 : inner ℝ v u = 1 := by
      rw [hu, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hlin : ℓ = (ℓ u) • (innerSL ℝ) v := by
      ext w
      have hker : inner ℝ v (w - (inner ℝ v w) • u) = 0 := by
        rw [inner_sub_right, real_inner_smul_right, hu1, mul_one, sub_self]
      have hstep : ℓ w = (inner ℝ v w) * ℓ u := by
        conv_lhs => rw [show w = (inner ℝ v w) • u + (w - (inner ℝ v w) • u) by module]
        rw [map_add, map_smul, h _ hker, add_zero, smul_eq_mul]
      rw [hstep]
      simp [innerSL, mul_comm]
    exact hanti (ℓ u) hlin
  obtain ⟨w, hw0, hwne⟩ := hex
  rcases lt_or_gt_of_ne hwne with h | h
  · exact ⟨w, hw0, h⟩
  · refine ⟨-w, ?_, ?_⟩
    · simp [hw0]
    · rw [map_neg]; linarith

/-- **The closure of the cut slab.**  `closure (slab ∩ {ℓ < lam}) = slab ∩ {ℓ ≤ lam}`. -/
lemma closure_closedSlab_inter {v : R3} (hv : v ≠ 0) {ℓ : R3 →L[ℝ] ℝ}
    (hanti : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v) (a h lam : ℝ) :
    closure ({x : R3 | |inner ℝ v x - a| ≤ h} ∩ {x : R3 | ℓ x < lam}) =
      {x : R3 | |inner ℝ v x - a| ≤ h} ∩ {x : R3 | ℓ x ≤ lam} := by
  apply Subset.antisymm
  · intro z hz
    refine ⟨?_, ?_⟩
    · have h1 : z ∈ closure {x : R3 | |inner ℝ v x - a| ≤ h} := closure_mono Set.inter_subset_left hz
      have hcl : IsClosed {x : R3 | |inner ℝ v x - a| ≤ h} :=
        isClosed_le (continuous_abs.comp ((continuous_const.inner continuous_id).sub continuous_const)) continuous_const
      rwa [hcl.closure_eq] at h1
    · have h1 : z ∈ closure {x : R3 | ℓ x < lam} := closure_mono Set.inter_subset_right hz
      have hsub : closure {x : R3 | ℓ x < lam} ⊆ {x : R3 | ℓ x ≤ lam} :=
        closure_minimal (fun x hx => le_of_lt (Set.mem_ofPred_eq.mp hx))
          (isClosed_le ℓ.continuous continuous_const)
      exact hsub h1
  · intro z hz
    obtain ⟨hzS, hzL⟩ := hz
    rw [Set.mem_ofPred_eq] at hzS
    rw [Set.mem_ofPred_eq] at hzL
    by_cases hlt : ℓ z < lam
    · exact subset_closure ⟨by rw [Set.mem_ofPred_eq]; exact hzS, by rw [Set.mem_ofPred_eq]; exact hlt⟩
    · -- on the wall `{ℓ = lam}` we move inside the slab along `w ∈ ker ⟪v,·⟫` with `ℓ w < 0`
      have heq : ℓ z = lam := le_antisymm hzL (not_lt.mp hlt)
      obtain ⟨w, hw0, hwneg⟩ := exists_ker_inner_ne hv hanti
      have hwpos : (0:ℝ) < ‖w‖ + 1 := by positivity
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hcpos : 0 < ε / (‖w‖ + 1) := div_pos hε hwpos
      refine ⟨z + (ε / (‖w‖ + 1)) • w, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · rw [Set.mem_ofPred_eq]
          have : inner ℝ v (z + (ε / (‖w‖ + 1)) • w) = inner ℝ v z := by
            rw [inner_add_right, real_inner_smul_right, hw0, mul_zero, add_zero]
          rw [this]; exact hzS
        · rw [Set.mem_ofPred_eq]
          have h1 : ℓ (z + (ε / (‖w‖ + 1)) • w) = lam + (ε / (‖w‖ + 1)) * ℓ w := by
            rw [map_add, map_smul, smul_eq_mul, heq]
          rw [h1]
          nlinarith [mul_neg_of_pos_of_neg hcpos hwneg]
      · rw [dist_eq_norm, show z - (z + (ε / (‖w‖ + 1)) • w) = -((ε / (‖w‖ + 1)) • w) by abel,
          norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
        rw [div_mul_eq_mul_div, div_lt_iff₀ hwpos]
        nlinarith [norm_nonneg w, hε]

/-- **The interior of the closed slab is the open slab.**  Here `v ≠ 0` is used, i.e. the
surjectivity of `⟪v,·⟫`. -/
lemma slab_interior_sub {v : R3} (hv : v ≠ 0) (a h : ℝ) :
    interior {x : R3 | |inner ℝ v x - a| ≤ h} ⊆ {x : R3 | |inner ℝ v x - a| < h} := by
  intro z hz
  have hzS := interior_subset hz
  simp only [Set.mem_ofPred_eq] at hzS
  obtain ⟨u, hu1⟩ := exists_inner_eq_one hv
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  have hu0 : (0:ℝ) ≤ ‖u‖ := norm_nonneg u
  have hden : (0:ℝ) < 2 * (‖u‖ + 1) := by linarith
  have hδ1 : 0 < δ / (2 * (‖u‖ + 1)) := div_pos hδpos hden
  have hδ1n : (0:ℝ) ≤ δ / (2 * (‖u‖ + 1)) := le_of_lt hδ1
  have hball : ∀ c : ℝ, |c| ≤ δ / (2 * (‖u‖ + 1)) → z + c • u ∈ Metric.ball z δ := by
    intro c hc
    rw [Metric.mem_ball]
    rw [dist_eq_norm, show z + c • u - z = c • u by abel, norm_smul, Real.norm_eq_abs]
    have h3 : |c| * ‖u‖ ≤ (δ / (2 * (‖u‖ + 1))) * (‖u‖ + 1) := by
      have h6 : ‖u‖ ≤ ‖u‖ + 1 := by linarith
      exact mul_le_mul hc h6 hu0 hδ1n
    have h4 : (δ / (2 * (‖u‖ + 1))) * (‖u‖ + 1) = δ / 2 := by
      rw [div_mul_eq_mul_div, mul_div_mul_right δ 2 (by linarith : (‖u‖ + 1) ≠ 0)]
    linarith
  have hmem_of : ∀ c : ℝ, |c| ≤ δ / (2 * (‖u‖ + 1)) → |inner ℝ v (z + c • u) - a| ≤ h := by
    intro c hc
    have hh := hδ (hball c hc)
    simpa only [Set.mem_ofPred_eq] using hh
  by_contra hlt
  rw [Set.mem_ofPred_eq] at hlt
  have hge : h ≤ |inner ℝ v z - a| := not_lt.mp hlt
  have heq : |inner ℝ v z - a| = h := le_antisymm hzS hge
  have hhpos : (0:ℝ) ≤ h := by linarith [abs_nonneg (inner ℝ v z - a)]
  have hval : ∀ c : ℝ, inner ℝ v (z + c • u) - a = (inner ℝ v z - a) + c := by
    intro c
    rw [inner_add_right, real_inner_smul_right, hu1, mul_one]
    ring
  rcases abs_eq hhpos |>.mp heq with hcase | hcase
  · have hnew : |inner ℝ v (z + (δ / (2 * (‖u‖ + 1))) • u) - a| =
        h + δ / (2 * (‖u‖ + 1)) := by
      rw [hval, hcase, abs_of_nonneg (by linarith)]
    have h1 := hmem_of _ (le_of_eq (abs_of_pos hδ1))
    rw [hnew] at h1
    linarith
  · have hnew : |inner ℝ v (z + (-(δ / (2 * (‖u‖ + 1)))) • u) - a| =
        h + δ / (2 * (‖u‖ + 1)) := by
      rw [hval]
      have hinner : inner ℝ v z - a + -(δ / (2 * (‖u‖ + 1))) = -h - δ / (2 * (‖u‖ + 1)) := by
        rw [hcase]; ring
      rw [hinner, abs_of_nonpos (by linarith)]
      ring
    have hneg : |-(δ / (2 * (‖u‖ + 1)))| ≤ δ / (2 * (‖u‖ + 1)) := by
      rw [abs_neg, abs_of_pos hδ1]
    have h1 := hmem_of _ hneg
    rw [hnew] at h1
    linarith

/-- **The open slab is the interior of the closed slab** (the other inclusion). -/
lemma mem_interior_closedSlab_of_abs_lt {v : R3} (hv : v ≠ 0) {a h : ℝ} {z : R3}
    (hz : |inner ℝ v z - a| < h) :
    z ∈ interior {x : R3 | |inner ℝ v x - a| ≤ h} := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  have hpos : 0 < h - |inner ℝ v z - a| := sub_pos.mpr hz
  have hden : (0:ℝ) < ‖v‖ + 1 := by positivity
  refine ⟨(h - |inner ℝ v z - a|) / (‖v‖ + 1), div_pos hpos hden, ?_⟩
  intro w hw
  rw [Set.mem_ofPred_eq]
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h1 : |inner ℝ v w - a| ≤ |inner ℝ v w - inner ℝ v z| + |inner ℝ v z - a| :=
    abs_sub_le _ _ _
  have h2 : |inner ℝ v w - inner ℝ v z| ≤ ‖v‖ * ‖w - z‖ := by
    rw [← inner_sub_right]; exact abs_real_inner_le_norm v (w - z)
  have hkey : ‖v‖ * ((h - |inner ℝ v z - a|) / (‖v‖ + 1)) ≤ h - |inner ℝ v z - a| := by
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith [norm_nonneg v, le_of_lt hpos]
  have hstrict : ‖v‖ * ‖w - z‖ < h - |inner ℝ v z - a| :=
    lt_of_lt_of_le (mul_lt_mul_of_pos_left hw (norm_pos_iff.mpr hv)) hkey
  linarith

/-- **The interior of the closed slab is the open slab.** -/
lemma interior_closedSlab {v : R3} (hv : v ≠ 0) (a h : ℝ) :
    interior {x : R3 | |inner ℝ v x - a| ≤ h} = {x : R3 | |inner ℝ v x - a| < h} :=
  Subset.antisymm (slab_interior_sub hv a h)
    (fun _ hz => mem_interior_closedSlab_of_abs_lt hv hz)

/-- **The interior of the cut slab.**  `interior (slab ∩ {ℓ < lam}) = openSlab ∩ {ℓ < lam}`. -/
lemma interior_inter_ltSlab {v : R3} (hv : v ≠ 0) {ℓ : R3 →L[ℝ] ℝ} (a h lam : ℝ) :
    interior ({x : R3 | |inner ℝ v x - a| ≤ h} ∩ {x : R3 | ℓ x < lam})
      = {x : R3 | |inner ℝ v x - a| < h} ∩ {x : R3 | ℓ x < lam} := by
  rw [interior_inter, interior_closedSlab hv a h]
  congr 1
  exact (isOpen_lt ℓ.continuous continuous_const).interior_eq

/-- **Frontier of a set minus another, seen inside an open set.**  For open `B` and `z ∈ B`, the
frontier of `B \ A` at `z` is the frontier of `A` at `z`: near an interior point of the open `B` the
two sets differ exactly by `A`. -/
lemma mem_frontier_sdiff_of_isOpen {B A : Set R3} (hB : IsOpen B) {z : R3} (hzB : z ∈ B) :
    z ∈ frontier (B \ A) ↔ z ∈ frontier A := by
  have hBmem : B ∈ nhds z := hB.mem_nhds hzB
  have h1 : z ∈ closure (B \ A) ↔ z ∉ interior A := by
    constructor
    · intro hz
      have hsub : closure (B \ A) ⊆ closure Aᶜ := closure_mono (fun x hx => hx.2)
      have hz' := hsub hz
      rwa [closure_compl] at hz'
    · intro hz
      rw [mem_closure_iff_nhds]
      intro t ht
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hsub : t ∩ B ⊆ A := by
        intro x hx
        by_contra hxA
        have hmem : x ∈ t ∩ (B \ A) := ⟨hx.1, hx.2, hxA⟩
        rw [hcon] at hmem
        exact hmem
      have hAmem : A ∈ nhds z := Filter.mem_of_superset (Filter.inter_mem ht hBmem) hsub
      exact hz (mem_interior_iff_mem_nhds.mpr hAmem)
  have h2 : z ∈ interior (B \ A) ↔ z ∉ closure A := by
    have heq : interior (B \ A) = interior B ∩ (closure A)ᶜ := by
      rw [Set.sdiff_eq, interior_inter, interior_compl, hB.interior_eq]
    rw [heq, Set.mem_inter_iff, Set.mem_compl_iff]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [hB.interior_eq]; exact hzB, h⟩
  have hL : z ∈ frontier (B \ A) ↔ (z ∈ closure (B \ A) ∧ z ∉ interior (B \ A)) := Iff.rfl
  have hR : z ∈ frontier A ↔ (z ∈ closure A ∧ z ∉ interior A) := Iff.rfl
  rw [hL, hR]
  constructor
  · rintro ⟨hc, hi⟩
    refine ⟨?_, h1.mp hc⟩
    by_contra hcl
    exact hi (h2.mpr hcl)
  · rintro ⟨hcl, hi⟩
    refine ⟨h1.mpr hi, ?_⟩
    intro h
    exact h2.mp h hcl

/-- **The corner computation.**  Let `B` be open, `v ≠ 0`, and let `ℓ` be not parallel to `⟪v,·⟫`.
For `y ∈ B` above the cut plane `a` (i.e. `a < ⟪v,y⟫`), `y` lies on the frontier of
`B \ (slab ∩ {ℓ < lam})` exactly when it lies on the far wall `{⟪v,·⟫ = a + h}` and not beyond
`{ℓ = lam}`, or on `{ℓ = lam}` and not beyond the far wall. -/
lemma frontier_sdiff_closedSlab {B : Set R3} (hB : IsOpen B) {v : R3} (hv : v ≠ 0)
    {ℓ : R3 →L[ℝ] ℝ} (hanti : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v)
    {a h lam : ℝ} {y : R3} (hyB : y ∈ B) (habove : a < inner ℝ v y) :
    y ∈ frontier (B \ ({x : R3 | |inner ℝ v x - a| ≤ h} ∩ {x : R3 | ℓ x < lam})) ↔
      (inner ℝ v y = a + h ∧ ℓ y ≤ lam) ∨ (ℓ y = lam ∧ inner ℝ v y < a + h) := by
  set S : Set R3 := {x : R3 | |inner ℝ v x - a| ≤ h} with hS
  set L : Set R3 := {x : R3 | ℓ x < lam} with hLdef
  have hcl_eq : closure (S ∩ L) = S ∩ {x : R3 | ℓ x ≤ lam} := by
    rw [hS, hLdef]; exact closure_closedSlab_inter hv hanti a h lam
  have hint_eq : interior (S ∩ L) = {x : R3 | |inner ℝ v x - a| < h} ∩ L := by
    rw [hS, hLdef]; exact interior_inter_ltSlab hv a h lam
  have hmemS : y ∈ S ↔ inner ℝ v y ≤ a + h := by
    rw [hS, Set.mem_ofPred_eq, abs_of_pos (by linarith : 0 < inner ℝ v y - a)]
    constructor <;> intro hh <;> linarith
  have hmemS' : (y ∈ {x : R3 | |inner ℝ v x - a| < h}) ↔ inner ℝ v y < a + h := by
    rw [Set.mem_ofPred_eq, abs_of_pos (by linarith : 0 < inner ℝ v y - a)]
    constructor <;> intro hh <;> linarith
  have hclm : (y ∈ closure (S ∩ L)) ↔ (inner ℝ v y ≤ a + h ∧ ℓ y ≤ lam) := by
    rw [hcl_eq]
    constructor
    · intro hz; exact ⟨hmemS.mp hz.1, hz.2⟩
    · intro hz; exact ⟨hmemS.mpr hz.1, hz.2⟩
  have hintm : (y ∈ interior (S ∩ L)) ↔ (inner ℝ v y < a + h ∧ ℓ y < lam) := by
    rw [hint_eq]
    constructor
    · intro hz; exact ⟨hmemS'.mp hz.1, hz.2⟩
    · intro hz; exact ⟨hmemS'.mpr hz.1, hz.2⟩
  have hfr : y ∈ frontier (B \ (S ∩ L)) ↔ y ∈ frontier (S ∩ L) :=
    mem_frontier_sdiff_of_isOpen hB hyB
  rw [hfr]
  have hmf : y ∈ frontier (S ∩ L) ↔
      ((inner ℝ v y ≤ a + h ∧ ℓ y ≤ lam) ∧ ¬(inner ℝ v y < a + h ∧ ℓ y < lam)) := by
    have hzero : (y ∈ frontier (S ∩ L)) ↔ (y ∈ closure (S ∩ L) ∧ y ∉ interior (S ∩ L)) :=
      Iff.rfl
    rw [hzero, hclm, hintm]
  rw [hmf]
  constructor
  · rintro ⟨⟨hXle, hlam⟩, hnot⟩
    by_cases hlt : inner ℝ v y < a + h
    · refine Or.inr ⟨?_, hlt⟩
      by_contra hne
      exact hnot ⟨hlt, lt_of_le_of_ne hlam hne⟩
    · exact Or.inl ⟨le_antisymm hXle (not_lt.mp hlt), hlam⟩
  · rintro (⟨hX, hlam⟩ | ⟨hlam, hlt⟩)
    · refine ⟨⟨by linarith, hlam⟩, ?_⟩
      intro hc
      linarith [hc.1]
    · refine ⟨⟨le_of_lt hlt, le_of_eq hlam⟩, ?_⟩
      intro hc
      linarith [hc.2, hlam]

theorem FrontierCorner_holds {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {v : LeanEval.KnotTheory.PardonDistortion.R3} {h : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {lam : ℝ}
    {y : LeanEval.KnotTheory.PardonDistortion.R3}
    (hv : v ≠ 0)
    (hanti : ∀ t : ℝ, ℓ ≠ t • (innerSL ℝ) v)
    (hy : y ∈ Submission.PBox s c σ)
    (habove : inner ℝ v c + u < inner ℝ v y) :
    y ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) ↔
      (inner ℝ v y = inner ℝ v c + u + h ∧ ℓ y ≤ lam) ∨
      (ℓ y = lam ∧ inner ℝ v y < inner ℝ v c + u + h) := by
  rw [Work.Drive.Mono.tiltedLevelRemoved, Work.Drive.EpsForm.tiltedSlabClosed]
  exact frontier_sdiff_closedSlab (Work.Topology.SphereSlicing.isOpen_PBox s c σ) hv hanti hy habove

end

end Work.Drive.Mono
