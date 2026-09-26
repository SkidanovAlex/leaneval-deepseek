import Mathlib
import Submission.Work.Drive.Mono.PlanarPi.Defs
import Submission.Work.Drive.Mono.eq_segment_of_convex_compact_interior_empty

namespace Work.Drive.Mono.PlanarPi

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In `ℝ`, `|x - a| ≤ h` means `a - h ≤ x ≤ a + h`. -/
lemma abs_sub_le_iff' (a h x : ℝ) : |x - a| ≤ h ↔ a - h ≤ x ∧ x ≤ a + h := by
  rw [abs_le]; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The interior of a closed halfspace `{x | c ≤ p x}` cut out by a nonzero functional is the
open halfspace `{x | c < p x}`. -/
lemma interior_Ici_clm [CompleteSpace E] {p : E →L[ℝ] ℝ} (hp : p ≠ 0) (c : ℝ) :
    interior {x : E | c ≤ p x} = {x : E | c < p x} := by
  have hp' : p.toLinearMap ≠ 0 := by
    intro h
    exact hp (ContinuousLinearMap.ext fun x => by simpa using LinearMap.congr_fun h x)
  have hsurj : Function.Surjective (⇑p) :=
    LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hp')
  have h := (p.isOpenMap hsurj).preimage_interior_eq_interior_preimage p.continuous (Set.Ici c)
  rw [interior_Ici] at h
  simpa [Set.preimage, Set.mem_Ioi] using h.symm

/-- The interior of the opposite closed halfspace `{x | p x ≤ c}`. -/
lemma interior_Iic_clm [CompleteSpace E] {p : E →L[ℝ] ℝ} (hp : p ≠ 0) (c : ℝ) :
    interior {x : E | p x ≤ c} = {x : E | p x < c} := by
  have h := interior_Ici_clm (E := E) (p := -p) (neg_ne_zero.mpr hp) (-c)
  simpa [neg_le_neg_iff, neg_lt_neg_iff] using h

/-- The interior of the closed strip `{|p x - a| ≤ h}` cut out by a nonzero functional. -/
lemma interior_abs_le_clm [CompleteSpace E] {p : E →L[ℝ] ℝ} (hp : p ≠ 0) (a h : ℝ) :
    interior {x : E | |p x - a| ≤ h} = {x : E | |p x - a| < h} := by
  have hset : {x : E | |p x - a| ≤ h} = {x : E | a - h ≤ p x} ∩ {x : E | p x ≤ a + h} := by
    ext x; simp only [mem_setOf_eq, mem_inter_iff, abs_sub_le_iff']
  rw [hset, interior_inter, interior_Ici_clm hp (a - h), interior_Iic_clm hp (a + h)]
  ext x; simp only [mem_setOf_eq, mem_inter_iff]; rw [abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The closed strip `{|p x - a| ≤ h}` is convex. -/
lemma convex_abs_sub_le_clm {p : E →L[ℝ] ℝ} (a h : ℝ) : Convex ℝ {x : E | |p x - a| ≤ h} := by
  rw [show {x : E | |p x - a| ≤ h} = {x : E | a - h ≤ p x} ∩ {x : E | p x ≤ a + h} from by
    ext x; simp only [mem_setOf_eq, mem_inter_iff, abs_sub_le_iff']]
  exact ((convex_Ici (a - h)).linear_preimage p.toLinearMap).inter
    ((convex_Iic (a + h)).linear_preimage p.toLinearMap)

/-- The closed strip `{|p x - a| ≤ h}` is closed. -/
lemma isClosed_abs_sub_le_clm {p : E →L[ℝ] ℝ} (a h : ℝ) : IsClosed {x : E | |p x - a| ≤ h} := by
  rw [show {x : E | |p x - a| ≤ h} = {x : E | a - h ≤ p x} ∩ {x : E | p x ≤ a + h} from by
    ext x; simp only [mem_setOf_eq, mem_inter_iff, abs_sub_le_iff']]
  exact (isClosed_le continuous_const p.continuous).inter (isClosed_le p.continuous continuous_const)

/-- A nonzero functional on a space of dimension at least two has nontrivial kernel. -/
lemma exists_ne_zero_mem_ker [FiniteDimensional ℝ E] (h2 : 2 ≤ Module.finrank ℝ E)
    {p : E →L[ℝ] ℝ} (hp : p ≠ 0) : ∃ w : E, w ≠ 0 ∧ p w = 0 := by
  have hp' : p.toLinearMap ≠ 0 := by
    intro h
    exact hp (ContinuousLinearMap.ext fun x => by simpa using LinearMap.congr_fun h x)
  have hker : Module.finrank ℝ (LinearMap.ker p.toLinearMap) + 1 = Module.finrank ℝ E :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hp'
  have hpos : 0 < Module.finrank ℝ (LinearMap.ker p.toLinearMap) := by omega
  have hne : LinearMap.ker p.toLinearMap ≠ ⊥ := by
    intro hbot
    rw [hbot] at hpos
    exact absurd hpos (by simp)
  obtain ⟨w, hw, hwne⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨w, hwne, hw⟩

/-- A nonzero level set of a nonzero functional on a space of dimension at least two meets every
ball in at least two points. -/
lemma exists_pair_mem_hyperplane_ball [FiniteDimensional ℝ E] (h2 : 2 ≤ Module.finrank ℝ E)
    {p : E →L[ℝ] ℝ} (hp : p ≠ 0) {x : E} {ε : ℝ} (hε : 0 < ε) :
    ∃ u v : E, u ≠ v ∧ u ∈ Metric.ball x ε ∧ v ∈ Metric.ball x ε ∧ p u = p x ∧ p v = p x := by
  obtain ⟨w, hwne, hw0⟩ := exists_ne_zero_mem_ker h2 hp
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hdpos : 0 < ε / (2 * ‖w‖) := by positivity
  have hkey : (ε / (2 * ‖w‖)) * ‖w‖ = ε / 2 := by field_simp
  have hkey2 : (2 * (ε / (2 * ‖w‖))) * ‖w‖ = ε := by field_simp
  have hnorm : ‖(ε / (2 * ‖w‖)) • w‖ = ε / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (le_of_lt hdpos), hkey]
  refine ⟨x + (ε / (2 * ‖w‖)) • w, x - (ε / (2 * ‖w‖)) • w, ?_, ?_, ?_, ?_, ?_⟩
  · intro huv
    have h1 : ‖(x + (ε / (2 * ‖w‖)) • w) - (x - (ε / (2 * ‖w‖)) • w)‖ = ε := by
      rw [show (x + (ε / (2 * ‖w‖)) • w) - (x - (ε / (2 * ‖w‖)) • w)
            = (2 * (ε / (2 * ‖w‖))) • w by module]
      rw [norm_smul, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (ε / (2 * ‖w‖)))]
      exact hkey2
    rw [huv, sub_self, norm_zero] at h1
    linarith
  · rw [Metric.mem_ball, dist_eq_norm,
      show x + (ε / (2 * ‖w‖)) • w - x = (ε / (2 * ‖w‖)) • w by module, hnorm]
    linarith
  · rw [Metric.mem_ball, dist_eq_norm,
      show x - (ε / (2 * ‖w‖)) • w - x = -((ε / (2 * ‖w‖)) • w) by module, norm_neg, hnorm]
    linarith
  · simp [map_add, map_smul, hw0]
  · simp [map_sub, map_smul, hw0]

/-- Interpolation lemma: in a convex set, if `p x < c < p y` and `q > lam` at both `x` and `y`,
there is a point of the convex set with `p = c` and `q > lam`. -/
lemma exists_mem_convex_p_eq_of_lt_lt {Q : Set E} (hQ : Convex ℝ Q) {x y : E} (hx : x ∈ Q)
    (hy : y ∈ Q) {p q : E →L[ℝ] ℝ} {c lam : ℝ} (h1 : p x < c) (h2 : c < p y)
    (h3 : lam < q x) (h4 : lam < q y) : ∃ z ∈ Q, p z = c ∧ lam < q z := by
  have hden : 0 < p y - p x := by linarith
  set t : ℝ := (c - p x) / (p y - p x) with ht
  have ht0 : 0 < t := by rw [ht]; exact div_pos (by linarith) hden
  have ht1 : t < 1 := by rw [ht, div_lt_one hden]; linarith
  refine ⟨(1 - t) • x + t • y, hQ hx hy (by linarith) (le_of_lt ht0) (by ring), ?_, ?_⟩
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have htz : t * (p y - p x) = c - p x := by rw [ht, div_mul_cancel₀ _ (ne_of_gt hden)]
    linarith
  · rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have ha : (1 - t) * lam < (1 - t) * q x := mul_lt_mul_of_pos_left h3 (by linarith)
    have hb : t * lam < t * q y := mul_lt_mul_of_pos_left h4 ht0
    linarith

/-- **The three convex pieces of the planar `Π`-region.**  Let `Q` be open convex bounded in the plane, `B = closure Q`, and suppose the crux hypotheses hold: there are points of `Q` strictly beyond the `+`-face of the strip `|p - a| ≤ h` and above the wall `q = lam` (`hcruxP`), and likewise strictly beyond the `-`-face (`hcruxM`).  Then the two caps `K₁ = piCapP B p (a+h)`, `K₂ = piCapM B p (a-h)` and the wall piece `Kw = piWall B p q a h lam` are compact convex with non-empty interior; the caps are disjoint; `K₁ ∩ Kw` and `K₂ ∩ Kw` are convex, consist of points with `p = a ± h`, contain two distinct points, and are contained in the frontiers of both pieces; the interiors of the caps are disjoint from the interior of `Kw`; the interior of a cap lies strictly beyond the corresponding face of the strip and the interior of `Kw` lies strictly inside the strip and strictly above the wall; and the whole `Π`-region `piRegion B p q a h lam` is the union `K₁ ∪ Kw ∪ K₂`. -/
theorem planarPi_pieces
    {a h lam : ℝ} (hh : 0 < h)
    (Q : Set (EuclideanSpace ℝ (Fin 2))) (hQc : Convex ℝ Q) (hQo : IsOpen Q)
    (hQb : Bornology.IsBounded Q)
    (p q : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (hcruxP : ∃ x ∈ Q, a + h < p x ∧ lam < q x)
    (hcruxM : ∃ x ∈ Q, p x < a - h ∧ lam < q x) :
    Convex ℝ (closure Q) ∧ IsCompact (closure Q) ∧
    Convex ℝ (piCapP (closure Q) p (a + h)) ∧
      IsCompact (piCapP (closure Q) p (a + h)) ∧
      (interior (piCapP (closure Q) p (a + h))).Nonempty ∧
      interior (piCapP (closure Q) p (a + h)) ⊆ {x | a + h < p x} ∧
    Convex ℝ (piCapM (closure Q) p (a - h)) ∧
      IsCompact (piCapM (closure Q) p (a - h)) ∧
      (interior (piCapM (closure Q) p (a - h))).Nonempty ∧
      interior (piCapM (closure Q) p (a - h)) ⊆ {x | p x < a - h} ∧
    Convex ℝ (piWall (closure Q) p q a h lam) ∧
      IsCompact (piWall (closure Q) p q a h lam) ∧
      (interior (piWall (closure Q) p q a h lam)).Nonempty ∧
      interior (piWall (closure Q) p q a h lam) ⊆ {x | |p x - a| < h} ∧
      interior (piWall (closure Q) p q a h lam) ⊆ {x | lam < q x} ∧
    piCapP (closure Q) p (a + h) ∩ piCapM (closure Q) p (a - h) = ∅ ∧
    Convex ℝ (piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam) ∧
      piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam ⊆ {x | p x = a + h} ∧
      (∃ x ∈ piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam,
        ∃ y ∈ piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam, x ≠ y) ∧
      piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam
        ⊆ frontier (piCapP (closure Q) p (a + h)) ∩ frontier (piWall (closure Q) p q a h lam) ∧
    Convex ℝ (piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam) ∧
      piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam ⊆ {x | p x = a - h} ∧
      (∃ x ∈ piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam,
        ∃ y ∈ piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam, x ≠ y) ∧
      piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam
        ⊆ frontier (piCapM (closure Q) p (a - h)) ∩ frontier (piWall (closure Q) p q a h lam) ∧
    interior (piCapP (closure Q) p (a + h)) ∩ interior (piWall (closure Q) p q a h lam) = ∅ ∧
    interior (piCapM (closure Q) p (a - h)) ∩ interior (piWall (closure Q) p q a h lam) = ∅ ∧
    piRegion (closure Q) p q a h lam
      = piCapP (closure Q) p (a + h) ∪ piWall (closure Q) p q a h lam
        ∪ piCapM (closure Q) p (a - h) := by
  have hBc : Convex ℝ (closure Q) := hQc.closure
  have hBcl : IsClosed (closure Q) := isClosed_closure
  have hBcomp : IsCompact (closure Q) := hQb.isCompact_closure
  have h2 : 2 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by simp
  obtain ⟨xP, hxPQ, hxPp, hxPq⟩ := hcruxP
  obtain ⟨xM, hxMQ, hxMp, hxMq⟩ := hcruxM
  have hp0 : p ≠ 0 := by
    intro hp
    rw [hp] at hxPp hxMp
    simp only [ContinuousLinearMap.zero_apply] at hxPp hxMp
    linarith
  have hQsub : Q ⊆ interior (closure Q) := by
    simpa [hQo.interior_eq] using interior_mono (subset_closure (s := Q))
  -- points of `Q` on the two relevant level sets, above the wall
  obtain ⟨xH, hxHQ, hxHp, hxHq⟩ :=
    exists_mem_convex_p_eq_of_lt_lt (p := p) (q := q) hQc hxMQ hxPQ (c := a + h)
      (by linarith) hxPp hxMq hxPq
  obtain ⟨xL, hxLQ, hxLp, hxLq⟩ :=
    exists_mem_convex_p_eq_of_lt_lt (p := p) (q := q) hQc hxMQ hxPQ (c := a - h)
      hxMp (by linarith) hxMq hxPq
  obtain ⟨x0, hx0Q, hx0p, hx0q⟩ :=
    exists_mem_convex_p_eq_of_lt_lt (p := p) (q := q) hQc hxMQ hxPQ (c := a)
      (by linarith) (by linarith) hxMq hxPq
  -- convexity, closedness, compactness of the three pieces
  have hK1conv : Convex ℝ (piCapP (closure Q) p (a + h)) := by
    unfold piCapP
    exact hBc.inter ((convex_Ici (a + h)).linear_preimage p.toLinearMap)
  have hK1comp : IsCompact (piCapP (closure Q) p (a + h)) :=
    hBcomp.inter_right (isClosed_le continuous_const p.continuous)
  have hK2conv : Convex ℝ (piCapM (closure Q) p (a - h)) := by
    unfold piCapM
    exact hBc.inter ((convex_Iic (a - h)).linear_preimage p.toLinearMap)
  have hK2comp : IsCompact (piCapM (closure Q) p (a - h)) :=
    hBcomp.inter_right (isClosed_le p.continuous continuous_const)
  have hKwconv : Convex ℝ (piWall (closure Q) p q a h lam) := by
    unfold piWall
    exact (hBc.inter (convex_abs_sub_le_clm a h)).inter
      ((convex_Ici lam).linear_preimage q.toLinearMap)
  have hKwcomp : IsCompact (piWall (closure Q) p q a h lam) :=
    (hBcomp.inter_right (isClosed_abs_sub_le_clm a h)).inter_right
      (isClosed_le continuous_const q.continuous)
  -- nonempty interiors
  have hK1int_ne : (interior (piCapP (closure Q) p (a + h))).Nonempty := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hQsub hxPQ))
        ((isOpen_lt continuous_const p.continuous).mem_nhds hxPp))
    refine ⟨xP, interior_maximal ?_ Metric.isOpen_ball (Metric.mem_ball_self hε)⟩
    intro y hy
    obtain ⟨hy1, hy2⟩ := hεsub hy
    have hy2' : a + h < p y := hy2
    exact ⟨hy1, le_of_lt hy2'⟩
  have hK2int_ne : (interior (piCapM (closure Q) p (a - h))).Nonempty := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hQsub hxMQ))
        ((isOpen_lt p.continuous continuous_const).mem_nhds hxMp))
    refine ⟨xM, interior_maximal ?_ Metric.isOpen_ball (Metric.mem_ball_self hε)⟩
    intro y hy
    obtain ⟨hy1, hy2⟩ := hεsub hy
    have hy2' : p y < a - h := hy2
    exact ⟨hy1, le_of_lt hy2'⟩
  have hKwint_ne : (interior (piWall (closure Q) p q a h lam)).Nonempty := by
    have hstrip : {y : EuclideanSpace ℝ (Fin 2) | |p y - a| < h} ∈ nhds x0 := by
      refine (isOpen_lt ((p.continuous.sub continuous_const).abs) continuous_const).mem_nhds ?_
      show |p x0 - a| < h
      rw [hx0p, sub_self, abs_zero]; exact hh
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hQsub hx0Q)) hstrip)
        ((isOpen_lt continuous_const q.continuous).mem_nhds hx0q))
    refine ⟨x0, interior_maximal ?_ Metric.isOpen_ball (Metric.mem_ball_self hε)⟩
    intro y hy
    obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hεsub hy
    have hy2' : |p y - a| < h := hy2
    have hy3' : lam < q y := hy3
    exact ⟨⟨hy1, le_of_lt hy2'⟩, le_of_lt hy3'⟩
  -- the interiors are on the correct side of the faces and of the wall
  have hK1int_p : interior (piCapP (closure Q) p (a + h)) ⊆ {x | a + h < p x} := by
    intro x hx
    have h1 : x ∈ interior {y | a + h ≤ p y} := interior_mono (fun y hy => hy.2) hx
    rw [interior_Ici_clm hp0 (a + h)] at h1
    simpa using h1
  have hK2int_p : interior (piCapM (closure Q) p (a - h)) ⊆ {x | p x < a - h} := by
    intro x hx
    have h1 : x ∈ interior {y | p y ≤ a - h} := interior_mono (fun y hy => hy.2) hx
    rw [interior_Iic_clm hp0 (a - h)] at h1
    simpa using h1
  have hKwint_abs : interior (piWall (closure Q) p q a h lam) ⊆ {x | |p x - a| < h} := by
    intro x hx
    have h1 : x ∈ interior {y | |p y - a| ≤ h} := interior_mono (fun y hy => hy.1.2) hx
    rw [interior_abs_le_clm hp0 a h] at h1
    simpa using h1
  have hKwint_q : interior (piWall (closure Q) p q a h lam) ⊆ {x | lam < q x} := by
    intro x hx
    by_cases hq : q = 0
    · rw [hq] at hxPq ⊢
      simpa using hxPq
    · have h1 : x ∈ interior {y | lam ≤ q y} := interior_mono (fun y hy => hy.2) hx
      rw [interior_Ici_clm hq lam] at h1
      simpa using h1
  -- the caps are disjoint
  have hK1K2 : piCapP (closure Q) p (a + h) ∩ piCapM (closure Q) p (a - h) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [piCapP, piCapM, mem_inter_iff, mem_setOf_eq] at hx1 hx2
    linarith [hx1.2, hx2.2, hh]
  -- the two junctions are level set pieces
  have hK1wall_p : piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam
      ⊆ {x | p x = a + h} := by
    intro x hx
    obtain ⟨⟨-, hx1⟩, ⟨⟨-, hx2⟩, -⟩⟩ := hx
    simp only [mem_setOf_eq] at hx1 hx2 ⊢
    have := (abs_le.mp hx2).2
    linarith
  have hK2wall_p : piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam
      ⊆ {x | p x = a - h} := by
    intro x hx
    obtain ⟨⟨-, hx1⟩, ⟨⟨-, hx2⟩, -⟩⟩ := hx
    simp only [mem_setOf_eq] at hx1 hx2 ⊢
    have := (abs_le.mp hx2).1
    linarith
  -- each junction contains two distinct points
  have hK1wall_two : ∃ x ∈ piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam,
      ∃ y ∈ piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam, x ≠ y := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hQsub hxHQ))
        ((isOpen_lt continuous_const q.continuous).mem_nhds hxHq))
    obtain ⟨u, v, huv, hu, hv, hpu, hpv⟩ := exists_pair_mem_hyperplane_ball h2 hp0 hε
    have huB : u ∈ closure Q := (hεsub hu).1
    have hvB : v ∈ closure Q := (hεsub hv).1
    have huq : lam < q u := (hεsub hu).2
    have hvq : lam < q v := (hεsub hv).2
    refine ⟨u, ⟨⟨huB, by show a + h ≤ p u; rw [hpu, hxHp]⟩,
        ⟨⟨huB, by show |p u - a| ≤ h; rw [hpu, hxHp, add_sub_cancel_left, abs_of_pos hh]⟩,
          le_of_lt huq⟩⟩,
      v, ⟨⟨hvB, by show a + h ≤ p v; rw [hpv, hxHp]⟩,
        ⟨⟨hvB, by show |p v - a| ≤ h; rw [hpv, hxHp, add_sub_cancel_left, abs_of_pos hh]⟩,
          le_of_lt hvq⟩⟩, huv⟩
  have hK2wall_two : ∃ x ∈ piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam,
      ∃ y ∈ piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam, x ≠ y := by
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hQsub hxLQ))
        ((isOpen_lt continuous_const q.continuous).mem_nhds hxLq))
    obtain ⟨u, v, huv, hu, hv, hpu, hpv⟩ := exists_pair_mem_hyperplane_ball h2 hp0 hε
    have huB : u ∈ closure Q := (hεsub hu).1
    have hvB : v ∈ closure Q := (hεsub hv).1
    have huq : lam < q u := (hεsub hu).2
    have hvq : lam < q v := (hεsub hv).2
    refine ⟨u, ⟨⟨huB, by show p u ≤ a - h; rw [hpu, hxLp]⟩,
        ⟨⟨huB, by show |p u - a| ≤ h; rw [hpu, hxLp, sub_sub_cancel_left, abs_neg,
          abs_of_pos hh]⟩, le_of_lt huq⟩⟩,
      v, ⟨⟨hvB, by show p v ≤ a - h; rw [hpv, hxLp]⟩,
        ⟨⟨hvB, by show |p v - a| ≤ h; rw [hpv, hxLp, sub_sub_cancel_left, abs_neg,
          abs_of_pos hh]⟩, le_of_lt hvq⟩⟩, huv⟩
  -- the junctions lie in the frontiers
  have hK1front : piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam
      ⊆ frontier (piCapP (closure Q) p (a + h)) := by
    intro x hx
    have hxpx : p x = a + h := hK1wall_p hx
    rw [frontier]
    refine ⟨subset_closure hx.1, fun hxint => ?_⟩
    have h1 : x ∈ interior {y | a + h ≤ p y} := interior_mono (fun y hy => hy.2) hxint
    rw [interior_Ici_clm hp0 (a + h)] at h1
    simp only [mem_setOf_eq] at h1
    linarith
  have hKwfront1 : piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam
      ⊆ frontier (piWall (closure Q) p q a h lam) := by
    intro x hx
    have hxpx : p x = a + h := hK1wall_p hx
    rw [frontier]
    refine ⟨subset_closure hx.2, fun hxint => ?_⟩
    have h1 : x ∈ interior {y | |p y - a| ≤ h} := interior_mono (fun y hy => hy.1.2) hxint
    rw [interior_abs_le_clm hp0 a h] at h1
    simp only [mem_setOf_eq] at h1
    rw [hxpx, add_sub_cancel_left, abs_of_pos hh] at h1
    exact absurd h1 (lt_irrefl h)
  have hK2front : piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam
      ⊆ frontier (piCapM (closure Q) p (a - h)) := by
    intro x hx
    have hxpx : p x = a - h := hK2wall_p hx
    rw [frontier]
    refine ⟨subset_closure hx.1, fun hxint => ?_⟩
    have h1 : x ∈ interior {y | p y ≤ a - h} := interior_mono (fun y hy => hy.2) hxint
    rw [interior_Iic_clm hp0 (a - h)] at h1
    simp only [mem_setOf_eq] at h1
    linarith
  have hKwfront2 : piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam
      ⊆ frontier (piWall (closure Q) p q a h lam) := by
    intro x hx
    have hxpx : p x = a - h := hK2wall_p hx
    rw [frontier]
    refine ⟨subset_closure hx.2, fun hxint => ?_⟩
    have h1 : x ∈ interior {y | |p y - a| ≤ h} := interior_mono (fun y hy => hy.1.2) hxint
    rw [interior_abs_le_clm hp0 a h] at h1
    simp only [mem_setOf_eq] at h1
    rw [hxpx, sub_sub_cancel_left, abs_neg, abs_of_pos hh] at h1
    exact absurd h1 (lt_irrefl h)
  -- the caps meet the wall piece only along the frontier
  have hK1int_wall : interior (piCapP (closure Q) p (a + h))
      ∩ interior (piWall (closure Q) p q a h lam) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have h1 : a + h < p x := hK1int_p hx.1
    have h2 : |p x - a| < h := hKwint_abs hx.2
    have h3 : p x < a + h := by have := (abs_lt.mp h2).2; linarith
    linarith
  have hK2int_wall : interior (piCapM (closure Q) p (a - h))
      ∩ interior (piWall (closure Q) p q a h lam) = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro x hx
    have h1 : p x < a - h := hK2int_p hx.1
    have h2 : |p x - a| < h := hKwint_abs hx.2
    have h3 : a - h < p x := by have := (abs_lt.mp h2).1; linarith
    linarith
  -- convexity of the junctions
  have hK1wall_conv : Convex ℝ (piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam) :=
    hK1conv.inter hKwconv
  have hK2wall_conv : Convex ℝ (piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam) :=
    hK2conv.inter hKwconv
  have hK1wall_front : piCapP (closure Q) p (a + h) ∩ piWall (closure Q) p q a h lam
      ⊆ frontier (piCapP (closure Q) p (a + h)) ∩ frontier (piWall (closure Q) p q a h lam) :=
    fun x hx => ⟨hK1front hx, hKwfront1 hx⟩
  have hK2wall_front : piCapM (closure Q) p (a - h) ∩ piWall (closure Q) p q a h lam
      ⊆ frontier (piCapM (closure Q) p (a - h)) ∩ frontier (piWall (closure Q) p q a h lam) :=
    fun x hx => ⟨hK2front hx, hKwfront2 hx⟩
  -- the whole `Π`-region is the union of the three pieces
  have hregion : piRegion (closure Q) p q a h lam
      = piCapP (closure Q) p (a + h) ∪ piWall (closure Q) p q a h lam
        ∪ piCapM (closure Q) p (a - h) := by
    ext x
    simp only [piRegion, piCapP, piWall, piCapM, mem_inter_iff, Set.mem_union, mem_setOf_eq]
    constructor
    · rintro ⟨hxB, hAB | hC⟩
      · rcases hAB with hA | hB'
        · exact Or.inl (Or.inl ⟨hxB, hA⟩)
        · exact Or.inr ⟨hxB, hB'⟩
      · by_cases hle : a + h ≤ p x
        · exact Or.inl (Or.inl ⟨hxB, hle⟩)
        · push_neg at hle
          by_cases hle' : p x ≤ a - h
          · exact Or.inr ⟨hxB, hle'⟩
          · push_neg at hle'
            exact Or.inl (Or.inr ⟨⟨hxB, (abs_sub_le_iff' a h (p x)).mpr
              ⟨by linarith, by linarith⟩⟩, hC⟩)
    · rintro ((⟨hxB, hA⟩ | ⟨⟨hxB, hS⟩, hC⟩) | ⟨hxB, hB'⟩)
      · exact ⟨hxB, Or.inl (Or.inl hA)⟩
      · exact ⟨hxB, Or.inr hC⟩
      · exact ⟨hxB, Or.inl (Or.inr hB')⟩
  exact ⟨hBc, hBcomp, hK1conv, hK1comp, hK1int_ne, hK1int_p, hK2conv, hK2comp, hK2int_ne,
    hK2int_p, hKwconv, hKwcomp, hKwint_ne, hKwint_abs, hKwint_q, hK1K2, hK1wall_conv,
    hK1wall_p, hK1wall_two, hK1wall_front, hK2wall_conv, hK2wall_p, hK2wall_two, hK2wall_front,
    hK1int_wall, hK2int_wall, hregion⟩

end Work.Drive.Mono.PlanarPi
