import Submission.Work.S4Seams
import Submission.Work.GeneralChord

open OptimalMoebius Topology
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# T1-ii Layer 1: frontier components of a flat component are full chords

Given a flat component `C = flatComponent f p` (bounded, green), each
connected component `K(e)` of `𝓕 := ∂C ∩ stripInterior` is a bounded
straight open segment with real parameters (S4) whose two ends lie on the
seam lines `x0 = 0` and `x0 = 1` (S3/S4).  Hence `K(e)` is a FULL-WIDTH
open chord of the strip:

    ∃ α β : ℝ, K(e) = {x | x ∈ stripInterior ∧ x 1 = sideH₁ α β (x 0)}.

Build: `lake build Submission.Work.FlatBetween` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- The full-width open chord of the strip from `(0, α)` to `(1, β)`:
points `x` of the open strip whose height equals the affine interpolation
`sideH₁ α β (x0) = (1−x0)·α + x0·β` between the seam heights. -/
def stripChord (α β : ℝ) : Set ℝ² :=
  {x | x ∈ stripInterior ∧ x 1 = sideH₁ α β (x 0)}

/-- Membership in a strip chord. -/
lemma mem_stripChord {α β : ℝ} {x : ℝ²} :
    x ∈ stripChord α β ↔ x ∈ stripInterior ∧ x 1 = sideH₁ α β (x 0) := by rfl

/-- Chord points lie in the open strip. -/
lemma stripChord_subset_stripInterior {α β : ℝ} : stripChord α β ⊆ stripInterior := by
  intro x hx
  exact (mem_stripChord.mp hx).1

/-- The chord meets `x0 = 0` at height `α`. -/
lemma sideH₁_zero (α β : ℝ) : sideH₁ α β 0 = α := by
  dsimp [sideH₁]; ring

/-- The chord meets `x0 = 1` at height `β`. -/
lemma sideH₁_one (α β : ℝ) : sideH₁ α β 1 = β := by
  dsimp [sideH₁]; ring

/-- Coordinate form of chord membership. -/
lemma mem_stripChord_coords {α β : ℝ} {x : ℝ²} :
    x ∈ stripChord α β ↔ 0 < x 0 ∧ x 0 < 1 ∧ x 1 = sideH₁ α β (x 0) := by
  rw [mem_stripChord, stripInterior]
  constructor
  · intro hx; exact ⟨hx.1.1, hx.1.2, hx.2⟩
  · intro hx; exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩

/-- The point of the chord over `x0 ∈ (0,1)`. -/
lemma chord_point_mem {α β x0 : ℝ} (hx0 : 0 < x0) (hx1 : x0 < 1) :
    (!₂[x0, sideH₁ α β x0] : ℝ²) ∈ stripChord α β := by
  rw [mem_stripChord_coords]
  exact ⟨hx0, hx1, by simp⟩

/-- Subtracting two affine segment points: `(e+(α+δ)•u) − (e+α•u) = δ•u`. -/
lemma seg_sub_seg (e u : ℝ²) (α δ : ℝ) :
    (e + (α + δ) • u) - (e + α • u) = δ • u := by
  ext i <;> fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    smul_eq_mul, add_mul] <;> ring

/-- Subtracting two affine segment points, general form. -/
lemma seg_sub_seg' (e u : ℝ²) (s α : ℝ) :
    (e + s • u) - (e + α • u) = (s - α) • u := by
  ext i <;> fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    smul_eq_mul, add_mul] <;> ring

/-- Scalar smul difference. -/
lemma smul_sub_vec (s α : ℝ) (u : ℝ²) : (s - α) • u = s • u - α • u := by
  ext i <;> fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    smul_eq_mul, add_mul] <;> ring

/-- A parametrized open straight segment of the plane. -/
def paramSegment (e u : ℝ²) (α β : ℝ) : Set ℝ² :=
  {x | ∃ s : ℝ, α < s ∧ s < β ∧ x = e + s • u}

/-- Membership in a parametrized segment. -/
lemma mem_paramSegment {e u : ℝ²} {α β : ℝ} {x : ℝ²} :
    x ∈ paramSegment e u α β ↔ ∃ s : ℝ, α < s ∧ s < β ∧ x = e + s • u := by rfl

/-- The left endpoint of a (nondegenerate) parametrized segment is not on
the segment. -/
lemma endpoint_not_mem_paramSegment {e u : ℝ²} {α β : ℝ} (hu : u ≠ 0) :
    e + α • u ∉ paramSegment e u α β := by
  intro hz
  rcases hz with ⟨s, has, hsb, heq⟩
  have hαu : α • u = s • u := add_left_cancel heq
  have hdiff : (s - α) • u = 0 := by
    calc (s - α) • u = s • u - α • u := smul_sub_vec s α u
      _ = 0 := sub_eq_zero.mpr hαu.symm
  have hsα : s = α := by
    by_contra hsne
    have : u = 0 := (smul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hsne)
    exact hu this
  linarith

/-- The right endpoint of a (nondegenerate) parametrized segment is not on
the segment. -/
lemma endpoint_not_mem_paramSegment' {e u : ℝ²} {α β : ℝ} (hu : u ≠ 0) (hαβ : α < β) :
    e + β • u ∉ paramSegment e u α β := by
  intro hz
  rcases hz with ⟨s, has, hsb, heq⟩
  have hβu : β • u = s • u := add_left_cancel heq
  have hdiff : (s - β) • u = 0 := by
    calc (s - β) • u = s • u - β • u := smul_sub_vec s β u
      _ = 0 := sub_eq_zero.mpr hβu.symm
  have hsβ : s = β := by
    by_contra hsne
    have : u = 0 := (smul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hsne)
    exact hu this
  linarith

/-- The left endpoint of a parametrized segment lies in its closure. -/
lemma endpoint_mem_closure_paramSegment {e u : ℝ²} {α β : ℝ} (hu₁ : ‖u‖ = 1)
    (hαβ : α < β) :
    e + α • u ∈ closure (paramSegment e u α β) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min ε (β - α) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (sub_pos.mpr hαβ))
  have hδβ : δ < β - α := by
    have hle : min ε (β - α) / 2 ≤ (β - α) / 2 :=
      div_le_div_of_nonneg_right (min_le_right ε (β - α)) (by norm_num)
    have hlt : (β - α) / 2 < β - α := by linarith
    exact lt_of_le_of_lt hle hlt
  have hδε : δ < ε := by
    have hle : min ε (β - α) / 2 ≤ ε / 2 :=
      div_le_div_of_nonneg_right (min_le_left ε (β - α)) (by norm_num)
    have hlt : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt hle hlt
  refine ⟨e + (α + δ) • u, ?_, ?_⟩
  · rw [mem_paramSegment]
    refine ⟨α + δ, ?_, ?_, rfl⟩
    · linarith
    · have h1 : α + δ < α + (β - α) := by linarith
      simpa using h1
  · rw [dist_eq_norm, norm_sub_rev, seg_sub_seg]
    rw [norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt hδ), hu₁]
    simpa using hδε

/-- The right endpoint of a parametrized segment lies in its closure. -/
lemma endpoint_mem_closure_paramSegment' {e u : ℝ²} {α β : ℝ} (hu₁ : ‖u‖ = 1)
    (hαβ : α < β) :
    e + β • u ∈ closure (paramSegment e u α β) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let δ : ℝ := min ε (β - α) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (sub_pos.mpr hαβ))
  have hδβ : δ < β - α := by
    have hle : min ε (β - α) / 2 ≤ (β - α) / 2 :=
      div_le_div_of_nonneg_right (min_le_right ε (β - α)) (by norm_num)
    have hlt : (β - α) / 2 < β - α := by linarith
    exact lt_of_le_of_lt hle hlt
  have hδε : δ < ε := by
    have hle : min ε (β - α) / 2 ≤ ε / 2 :=
      div_le_div_of_nonneg_right (min_le_left ε (β - α)) (by norm_num)
    have hlt : ε / 2 < ε := by linarith
    exact lt_of_le_of_lt hle hlt
  refine ⟨e + (β - δ) • u, ?_, ?_⟩
  · rw [mem_paramSegment]
    refine ⟨β - δ, ?_, ?_, rfl⟩
    · have h1 : β - δ > β - (β - α) := by linarith
      simpa using h1
    · linarith
  · rw [dist_eq_norm]
    have hvec : (e + (β - δ) • u) - (e + β • u) = -(δ • u) := by
      ext i <;> fin_cases i <;> simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
        smul_eq_mul, add_mul] <;> ring
    rw [norm_sub_rev, hvec, norm_neg, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt hδ), hu₁]
    simpa using hδε

/-- The frontier component through a strip-interior frontier point of a
flat component lies in the strip interior (components of `𝓕` are subsets
of `𝓕`, hence of `stripInterior`). -/
lemma frontierComponent_subset_stripInterior (f : ℝ² → ℝ³) {p e : ℝ²} :
    connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e ⊆
      stripInterior := by
  intro x hx
  exact (connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e hx).2

/-- An affine segment point: `(1−t)•(e+α•u) + t•(e+β•u) = e + ((1−t)α+tβ)•u`. -/
lemma affine_combo_seg (e u : ℝ²) (α β t : ℝ) :
    (1 - t) • (e + α • u) + t • (e + β • u) = e + ((1 - t) * α + t * β) • u := by
  ext i <;> fin_cases i <;> simp [smul_eq_mul, add_mul, mul_add] <;> ring

/-- `(1−t)α + tβ` lies strictly between `α` and `β` for `t ∈ (0,1)`. -/
lemma affine_combo_mem_Ioo {α β t : ℝ} (hαβ : α < β) (ht : t ∈ Set.Ioo 0 1) :
    (1 - t) * α + t * β ∈ Set.Ioo α β := by
  rw [Set.mem_Ioo]
  rcases (Set.mem_Ioo.mp ht) with ⟨ht0, ht1⟩
  constructor <;> nlinarith

/-- Scalar coordinate of the affine combination at `x0` (used with the
end-point hypotheses `e0+αu0=0`, `e0+βu0=1`). -/
lemma scalar_combo0 {e0 u0 α β t : ℝ} (hA : e0 + α * u0 = 0) (hB : e0 + β * u0 = 1) :
    (1 - t) * e0 + (1 - t) * (α * u0) + t * e0 + t * (β * u0) = t := by
  calc
    (1 - t) * e0 + (1 - t) * (α * u0) + t * e0 + t * (β * u0)
        = (1 - t) * (e0 + α * u0) + t * (e0 + β * u0) := by ring
    _ = (1 - t) * 0 + t * 1 := by rw [hA, hB]
    _ = t := by ring

/-- Under the good orientation, the interpolated point
`(1−t)•(e+α•u) + t•(e+β•u)` sits on the chord `stripChord ((e+α•u)1)
((e+β•u)1)` at height `t`. -/
lemma combo_point_coords {e u : ℝ²} {α β t : ℝ}
    (hψα : (e + α • u) 0 = 0) (hψβ : (e + β • u) 0 = 1) :
    (1 - t) • (e + α • u) + t • (e + β • u) = !₂[t, sideH₁ ((e + α • u) 1) ((e + β • u) 1) t] := by
  ext i <;> fin_cases i
  · simp
    have hA0 : (e) 0 + α * (u) 0 = 0 := by
      simpa [smul_eq_mul, add_mul] using hψα
    have hB0 : (e) 0 + β * (u) 0 = 1 := by
      simpa [smul_eq_mul, add_mul] using hψβ
    have hsc := scalar_combo0 (t := t) hA0 hB0
    ring_nf at hsc ⊢
    exact hsc
  · simp
    dsimp [sideH₁]
    ring

/-- **Chord form (aux, good orientation)**: if the parametrized open
segment `{e+s•u | α<s<β}` has its left end over `x0 = 0` and its right
end over `x0 = 1`, then it is exactly the full chord
`stripChord ((e+α•u)1) ((e+β•u)1)`.

Proof by reparametrisation `t := (s−α)/(β−α) ∈ (0,1)`: every point of
the segment is the affine combination
`(1−t)•(e+α•u) + t•(e+β•u)` whose coordinates are `(t, sideH₁ α' β' t)`
(`combo_point_coords`), i.e. the chord point over `x0 = t`; conversely a
chord point over `x0 = t` is that affine combination, hence lies on the
segment with parameter `(1−t)α + tβ ∈ (α,β)`. -/
lemma paramSegment_eq_stripChord_of_ends {e u : ℝ²} {α β : ℝ} (hαβ : α < β)
    (hψα : (e + α • u) 0 = 0) (hψβ : (e + β • u) 0 = 1) :
    paramSegment e u α β = stripChord ((e + α • u) 1) ((e + β • u) 1) := by
  ext x
  constructor
  · intro hx
    rcases (mem_paramSegment.mp hx) with ⟨s, has, hsb, hxeq⟩
    let t : ℝ := (s - α) / (β - α)
    have ht : t ∈ Set.Ioo 0 1 := by
      rw [Set.mem_Ioo]
      have hpos : 0 < β - α := sub_pos.mpr hαβ
      constructor
      · dsimp [t]
        exact div_pos (by linarith) hpos
      · dsimp [t]
        rw [div_lt_one hpos]
        linarith
    have hscombo : s = (1 - t) * α + t * β := by
      dsimp [t]
      have hba : β - α ≠ 0 := by linarith
      field_simp [hba]
      ring
    have hx' : x = (1 - t) • (e + α • u) + t • (e + β • u) := by
      calc
        x = e + s • u := hxeq
        _ = e + ((1 - t) * α + t * β) • u := by rw [← hscombo]
        _ = (1 - t) • (e + α • u) + t • (e + β • u) := (affine_combo_seg e u α β t).symm
    have hc0 : ((1 - t) • (e + α • u) + t • (e + β • u)) 0 = t := by
      have hcombo := combo_point_coords (e := e) (u := u) (α := α) (β := β) (t := t) hψα hψβ
      have hc := congrArg (fun w : ℝ² => w 0) hcombo
      simpa using hc
    have hc1 : ((1 - t) • (e + α • u) + t • (e + β • u)) 1 =
        sideH₁ ((e + α • u) 1) ((e + β • u) 1) t := by
      have hcombo := combo_point_coords (e := e) (u := u) (α := α) (β := β) (t := t) hψα hψβ
      have hc := congrArg (fun w : ℝ² => w 1) hcombo
      simpa using hc
    rw [mem_stripChord_coords]
    have hx0 : x 0 = t := by
      rw [hx']
      exact hc0
    have hx1 : x 1 = sideH₁ ((e + α • u) 1) ((e + β • u) 1) t := by
      rw [hx']
      exact hc1
    rw [hx0]
    constructor
    · exact (Set.mem_Ioo.mp ht).1
    constructor
    · exact (Set.mem_Ioo.mp ht).2
    · exact hx1
  · intro hx
    rw [mem_stripChord_coords] at hx
    rcases hx with ⟨hx0, hx1, hφ⟩
    let t : ℝ := x 0
    have ht : t ∈ Set.Ioo 0 1 := by
      exact ⟨hx0, hx1⟩
    let s : ℝ := (1 - t) * α + t * β
    have hs : s ∈ Set.Ioo α β := affine_combo_mem_Ioo hαβ ht
    have hc0 : ((1 - t) • (e + α • u) + t • (e + β • u)) 0 = t := by
      have hcombo := combo_point_coords (e := e) (u := u) (α := α) (β := β) (t := t) hψα hψβ
      have hc := congrArg (fun w : ℝ² => w 0) hcombo
      simpa using hc
    have hc1 : ((1 - t) • (e + α • u) + t • (e + β • u)) 1 =
        sideH₁ ((e + α • u) 1) ((e + β • u) 1) t := by
      have hcombo := combo_point_coords (e := e) (u := u) (α := α) (β := β) (t := t) hψα hψβ
      have hc := congrArg (fun w : ℝ² => w 1) hcombo
      simpa using hc
    have hx0e : x 0 = t := by rfl
    have hx1e : x 1 = sideH₁ ((e + α • u) 1) ((e + β • u) 1) t := by
      dsimp [t]
      exact hφ
    have hvec : e + s • u = (1 - t) • (e + α • u) + t • (e + β • u) := by
        dsimp [s]
        exact (affine_combo_seg e u α β t).symm
    have h0e : (e + s • u) 0 = t := by
      rw [hvec]
      exact hc0
    have h1e : (e + s • u) 1 = sideH₁ ((e + α • u) 1) ((e + β • u) 1) t := by
      rw [hvec]
      exact hc1
    have hx0c : x 0 = (e + s • u) 0 := hx0e.trans h0e.symm
    have hx1c : x 1 = (e + s • u) 1 := hx1e.trans h1e.symm
    have hx' : x = e + s • u := by
      ext i <;> fin_cases i <;> simp [hx0c, hx1c]
    rw [mem_paramSegment]
    refine ⟨s, (Set.mem_Ioo.mp hs).1, (Set.mem_Ioo.mp hs).2, hx'⟩


/-- Double negation on scalar smul: `(-s)•(-u) = s•u`. -/
lemma smul_neg_neg_vec (s : ℝ) (u : ℝ²) : (-s) • (-u) = s • u := by
  ext i <;> fin_cases i <;> simp [smul_eq_mul] <;> ring

/-- Reparametrising a parametrized segment by the flipped parameter
`s ↦ −s` gives the segment with `(−β, −α, −u)`. -/
lemma paramSegment_flip (e u : ℝ²) (α β : ℝ) :
    paramSegment e u α β = paramSegment e (-u) (-β) (-α) := by
  ext x
  constructor
  · intro hx
    rcases (mem_paramSegment.mp hx) with ⟨s, has, hsb, hxeq⟩
    rw [mem_paramSegment]
    refine ⟨-s, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · rw [hxeq, smul_neg_neg_vec]
  · intro hx
    rcases (mem_paramSegment.mp hx) with ⟨s, has, hsb, hxeq⟩
    rw [mem_paramSegment]
    refine ⟨-s, ?_, ?_, ?_⟩
    · linarith
    · linarith
    · calc
        x = e + s • (-u) := hxeq
        _ = e + (-(-s)) • (-u) := by ring_nf
        _ = e + (-s) • u := by rw [smul_neg_neg_vec]

/-- The frontier component of `∂C ∩ stripInterior` through `e`. -/
abbrev frComp (f : ℝ² → ℝ³) (p e : ℝ²) : Set ℝ² :=
  connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e

theorem frontierComponent_full_chord {a : ℝ} {f : ℝ² → ℝ³} (hf : IsMoebiusEmbedding a f)
    (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f)) {e : ℝ²}
    (heS : e ∈ stripInterior) (heF : e ∈ frontier (flatComponent f p)) :
    ∃ α β : ℝ, frComp f p e = stripChord α β := by
  rcases frontierComponent_bounded_real_segment hf ha hp heS heF with ⟨u, hu₁, α, β, hαβ, hK⟩
  have hK' : frComp f p e = paramSegment e u α β := by
    change frComp f p e = {x : ℝ² | ∃ s : ℝ, α < s ∧ s < β ∧ x = e + s • u}
    exact hK
  have hu_ne : u ≠ 0 := by
    intro hu0
    rw [hu0] at hu₁
    norm_num at hu₁
  have hCsub : frComp f p e ⊆ stripInterior := frontierComponent_subset_stripInterior f (p := p) (e := e)
  -- endpoints of the segment lie on the seams
  have hψα0 : (e + α • u) 0 = 0 ∨ (e + α • u) 0 = 1 := by
    apply frontierComponent_closure_point_on_seam hf ha heS heF (z := e + α • u)
    · have hcl : e + α • u ∈ closure (paramSegment e u α β) :=
        endpoint_mem_closure_paramSegment hu₁ hαβ
      change e + α • u ∈ closure (frComp f p e)
      rw [hK']
      exact hcl
    · intro hz
      have hnm : e + α • u ∉ paramSegment e u α β := endpoint_not_mem_paramSegment hu_ne
      change e + α • u ∈ frComp f p e at hz
      rw [hK'] at hz
      exact hnm hz
  have hψβ0 : (e + β • u) 0 = 0 ∨ (e + β • u) 0 = 1 := by
    apply frontierComponent_closure_point_on_seam hf ha heS heF (z := e + β • u)
    · have hcl : e + β • u ∈ closure (paramSegment e u α β) :=
        endpoint_mem_closure_paramSegment' hu₁ hαβ
      change e + β • u ∈ closure (frComp f p e)
      rw [hK']
      exact hcl
    · intro hz
      have hnm : e + β • u ∉ paramSegment e u α β := endpoint_not_mem_paramSegment' hu_ne hαβ
      change e + β • u ∈ frComp f p e at hz
      rw [hK'] at hz
      exact hnm hz
  -- the two ends are over DIFFERENT seams
  have hψα_ne : (e + α • u) 0 ≠ (e + β • u) 0 := by
    intro hEq
    let m : ℝ := (1 - (1 / 2 : ℝ)) * α + (1 / 2 : ℝ) * β
    let z : ℝ² := e + m • u
    have ht : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
    have hm : m ∈ Set.Ioo α β := affine_combo_mem_Ioo hαβ ht
    have hzC : z ∈ frComp f p e := by
      rw [hK']
      rw [mem_paramSegment]
      exact ⟨m, hm.1, hm.2, rfl⟩
    have hzS : z ∈ stripInterior := hCsub hzC
    have hzcombo : z = (1 - (1 / 2 : ℝ)) • (e + α • u) + (1 / 2 : ℝ) • (e + β • u) := by
      dsimp [z, m]
      exact (affine_combo_seg e u α β (1 / 2)).symm
    have hz0c : z 0 = (e + α • u) 0 := by
      rw [hzcombo]
      have hnorm : ((1 - (1 / 2 : ℝ)) • (e + α • u) + (1 / 2 : ℝ) • (e + β • u)) 0 =
          (1 - (1 / 2 : ℝ)) * (e + α • u) 0 + (1 / 2 : ℝ) * (e + β • u) 0 := by
        simp [smul_eq_mul, add_mul, mul_add]
      rw [hnorm, hEq]
      ring
    rcases hψα0 with h0 | h1
    · rw [stripInterior] at hzS
      have hz0 : 0 < z 0 := hzS.1
      rw [hz0c, h0] at hz0
      norm_num at hz0
    · rw [stripInterior] at hzS
      have hz1 : z 0 < 1 := hzS.2
      rw [hz0c, h1] at hz1
      norm_num at hz1
  -- case split on the orientation of the ends
  by_cases hα0 : (e + α • u) 0 = 0
  · have hβ1 : (e + β • u) 0 = 1 := by
      rcases hψβ0 with hb0 | hb1
      · exfalso
        exact hψα_ne (by rw [hα0, hb0])
      · exact hb1
    have hEq' : frComp f p e = stripChord ((e + α • u) 1) ((e + β • u) 1) := by
      rw [hK']
      exact paramSegment_eq_stripChord_of_ends hαβ hα0 hβ1
    exact ⟨(e + α • u) 1, (e + β • u) 1, hEq'⟩
  · have hα1 : (e + α • u) 0 = 1 := by
      rcases hψα0 with ha0 | ha1
      · exact False.elim (hα0 ha0)
      · exact ha1
    have hβ0 : (e + β • u) 0 = 0 := by
      rcases hψβ0 with hb0 | hb1
      · exact hb0
      · exfalso
        exact hψα_ne (by rw [hα1, hb1])
    have hflip : paramSegment e u α β = paramSegment e (-u) (-β) (-α) :=
      paramSegment_flip e u α β
    have hb' : -β < -α := by linarith
    have hψ'α : (e + (-β) • (-u)) 0 = 0 := by
      rw [smul_neg_neg_vec]
      exact hβ0
    have hψ'β : (e + (-α) • (-u)) 0 = 1 := by
      rw [smul_neg_neg_vec]
      exact hα1
    have hEq' : frComp f p e = stripChord ((e + β • u) 1) ((e + α • u) 1) := by
      have hpar : paramSegment e (-u) (-β) (-α) =
          stripChord ((e + (-β) • (-u)) 1) ((e + (-α) • (-u)) 1) :=
        paramSegment_eq_stripChord_of_ends hb' hψ'α hψ'β
      have hstrip : stripChord ((e + (-β) • (-u)) 1) ((e + (-α) • (-u)) 1) =
          stripChord ((e + β • u) 1) ((e + α • u) 1) := by
        congr 1 <;> rw [smul_neg_neg_vec]
      calc
        frComp f p e = paramSegment e u α β := hK'
        _ = paramSegment e (-u) (-β) (-α) := hflip
        _ = stripChord ((e + (-β) • (-u)) 1) ((e + (-α) • (-u)) 1) := hpar
        _ = stripChord ((e + β • u) 1) ((e + α • u) 1) := hstrip
    exact ⟨(e + β • u) 1, (e + α • u) 1, hEq'⟩

