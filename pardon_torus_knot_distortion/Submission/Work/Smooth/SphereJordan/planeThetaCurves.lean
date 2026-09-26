import Mathlib
import Submission.Work.Smooth.SphereJordan.thetaPlaneJordanCurve
import Submission.Work.Smooth.SphereJordan.DiscCurve
import Submission.Work.Smooth.SphereJordan.planeArcSetup
import Submission.Work.Smooth.SphereJordan.planeTwoDiscs
import Submission.Work.Smooth.SphereJordan.radialWinding

/-!
# The four four-arc curves of the plane theta graph

Two disjoint embedded discs joined by two arcs; the two boundary arcs of each disc, together with
the two joining arcs, form four simple closed plane curves.  This file fixes that configuration
(`ThetaSetup`, `ThetaSetup.arcA₁`, ...) together with the four curves `ThetaSetup.cur`, and records
the elementary incidence facts.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The boundary arc of a disc map between two parameters -/

/-- An arc of the boundary circle: `θ ↦ F (e^{i(x + t (y - x))})`. -/
abbrev bArc (F : C(Disc, ℂ)) (x y : ℝ) : C(Set.Icc (0 : ℝ) 1, ℂ) := discArc F x y

theorem bArc_apply (F : C(Disc, ℂ)) (x y : ℝ) (t : Set.Icc (0 : ℝ) 1) :
    bArc F x y t = F (circlePoint (x + (t : ℝ) * (y - x))) := rfl

theorem bArc_zero (F : C(Disc, ℂ)) (x y : ℝ) :
    bArc F x y ⟨0, by norm_num⟩ = F (circlePoint x) := discArc_zero F x y

theorem bArc_one (F : C(Disc, ℂ)) (x y : ℝ) :
    bArc F x y ⟨1, by norm_num⟩ = F (circlePoint y) := discArc_one F x y

/-- The boundary parameter of `circlePoint` is determined modulo `2π`. -/
theorem circlePoint_eq_iff_exists_int (a b : ℝ) :
    circlePoint a = circlePoint b ↔ ∃ n : ℤ, a = b + (n : ℝ) * (2 * Real.pi) := by
  constructor
  · intro hab
    have h : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) := by
      have := congrArg (fun z : Disc => (z : ℂ)) hab
      simpa [Work.Smooth.Jordan.circlePoint_coe] using this
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simpa using this
  · rintro ⟨n, rfl⟩
    exact _root_.Work.Smooth.SphereJordan.circlePoint_add_int_mul b n

/-- `circlePoint` is injective on intervals of length `< 2π`:  if two parameters differ by less
than `2π` in absolute value, they are equal as soon as the boundary points agree. -/
theorem circlePoint_inj_of_abs_lt {a b : ℝ} (h : |a - b| < 2 * Real.pi)
    (hab : circlePoint a = circlePoint b) : a = b := by
  obtain ⟨n, hn⟩ := (circlePoint_eq_iff_exists_int a b).mp hab
  have h1 : |(n : ℝ) * (2 * Real.pi)| < 2 * Real.pi := by
    have h2 : a - b = (n : ℝ) * (2 * Real.pi) := by rw [hn]; ring
    rw [← h2]
    exact h
  have h2 : |(n : ℝ)| < 1 := by
    rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 * Real.pi by positivity)] at h1
    nlinarith [Real.pi_pos]
  have h3 : |n| < 1 := by exact_mod_cast h2
  have hn0 : n = 0 := by
    have := abs_lt.mp h3
    omega
  rw [hn, hn0]
  push_cast
  ring

/-- **The boundary arc is injective** when the parameter interval has length `< 2π`. -/
theorem bArc_injective (F : C(Disc, ℂ)) (hF : Function.Injective F) {x y : ℝ}
    (hxy : |y - x| < 2 * Real.pi) (hne : y ≠ x) : Function.Injective (bArc F x y) := by
  intro s t hst
  have h1 : circlePoint (x + (s : ℝ) * (y - x)) = circlePoint (x + (t : ℝ) * (y - x)) := hF hst
  have h2 : (x + (s : ℝ) * (y - x)) - (x + (t : ℝ) * (y - x)) = ((s : ℝ) - t) * (y - x) := by ring
  have h3 : |((s : ℝ) - t) * (y - x)| < 2 * Real.pi := by
    rw [abs_mul]
    have h4 : |((s : ℝ) - t)| ≤ 1 := by
      rw [abs_sub_le_iff]
      exact ⟨by linarith [s.2.2, t.2.1], by linarith [t.2.2, s.2.1]⟩
    nlinarith [abs_nonneg (y - x), abs_nonneg ((s:ℝ) - t), hxy]
  have h4 := circlePoint_inj_of_abs_lt (a := x + (s:ℝ)*(y-x)) (b := x + (t:ℝ)*(y-x))
    (by rw [h2]; exact h3) h1
  have h5 : ((s : ℝ) - t) * (y - x) = 0 := by linarith [h4]
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact Subtype.ext (by linarith)
  · exact absurd (by linarith : y = x) hne


/-! ## The theta configuration -/

/-- The data of the plane theta graph: two disjoint embedded discs `D₁`, `D₂`, two joining arcs
`α`, `β`, and the boundary parameters of the four endpoints used to cut the two boundary circles
into arcs. -/
structure ThetaSetup (D₁ D₂ : Set ℂ) where
  /-- the first disc -/
  f : C(Disc, ℂ)
  hf : Function.Injective f
  hfr : Set.range f = D₁
  /-- the second disc -/
  g : C(Disc, ℂ)
  hg : Function.Injective g
  hgr : Set.range g = D₂
  /-- the discs are disjoint -/
  hdisj : Disjoint D₁ D₂
  /-- the first joining arc -/
  α : C(Set.Icc (0 : ℝ) 1, ℂ)
  /-- the second joining arc -/
  β : C(Set.Icc (0 : ℝ) 1, ℂ)
  hαinj : Function.Injective α
  hβinj : Function.Injective β
  hα₀ : α ⟨0, by norm_num⟩ ∈ D₁
  hα₁ : α ⟨1, by norm_num⟩ ∈ D₂
  hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁
  hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂
  hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂
  hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂
  hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
    α s ≠ β t
  hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩
  hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩
  /-- boundary parameter of `β 0` -/
  θq : ℝ
  /-- boundary parameter of `α 0` -/
  θp : ℝ
  /-- boundary parameter of `α 1` -/
  φa : ℝ
  /-- boundary parameter of `β 1` -/
  φb : ℝ
  hθq : f (circlePoint θq) = β ⟨0, by norm_num⟩
  hθp_lt : θq < θp
  hθp_ub : θp < θq + 2 * Real.pi
  hθp : f (circlePoint θp) = α ⟨0, by norm_num⟩
  hφb : g (circlePoint φb) = β ⟨1, by norm_num⟩
  hφa_lt : φb < φa
  hφa_ub : φa < φb + 2 * Real.pi
  hφa : g (circlePoint φa) = α ⟨1, by norm_num⟩

namespace ThetaSetup

variable {D₁ D₂ : Set ℂ} (T : ThetaSetup D₁ D₂)

/-- The point `β 0`. -/
def q : ℂ := T.β ⟨0, by norm_num⟩
/-- The point `α 0`. -/
def p : ℂ := T.α ⟨0, by norm_num⟩
/-- The point `α 1`. -/
def a : ℂ := T.α ⟨1, by norm_num⟩
/-- The point `β 1`. -/
def b : ℂ := T.β ⟨1, by norm_num⟩

/-- The first boundary arc of `∂D₁`, from `q` to `p`. -/
def arcA₁ : C(Set.Icc (0 : ℝ) 1, ℂ) := discArc T.f T.θq T.θp
/-- The second boundary arc of `∂D₁`, from `q` to `p` (going the other way). -/
def arcA₂ : C(Set.Icc (0 : ℝ) 1, ℂ) := discArc T.f T.θq (T.θp - 2 * Real.pi)
/-- The first boundary arc of `∂D₂`, from `a` to `b`. -/
def arcB₁ : C(Set.Icc (0 : ℝ) 1, ℂ) := discArc T.g T.φa (T.φb + 2 * Real.pi)
/-- The second boundary arc of `∂D₂`, from `a` to `b` (going the other way). -/
def arcB₂ : C(Set.Icc (0 : ℝ) 1, ℂ) := discArc T.g T.φa T.φb

/-- The two boundary arcs of `∂D₁`, indexed by a boolean. -/
def arcA (i : Bool) : C(Set.Icc (0 : ℝ) 1, ℂ) := if i then T.arcA₁ else T.arcA₂
/-- The two boundary arcs of `∂D₂`, indexed by a boolean. -/
def arcB (j : Bool) : C(Set.Icc (0 : ℝ) 1, ℂ) := if j then T.arcB₁ else T.arcB₂

theorem arcA₁_zero : T.arcA₁ ⟨0, by norm_num⟩ = T.q := by
  rw [arcA₁, bArc_zero]; exact T.hθq

theorem arcA₁_one : T.arcA₁ ⟨1, by norm_num⟩ = T.p := by
  rw [arcA₁, bArc_one]; exact T.hθp

theorem arcA₂_zero : T.arcA₂ ⟨0, by norm_num⟩ = T.q := by
  rw [arcA₂, bArc_zero]; exact T.hθq

theorem arcA₂_one : T.arcA₂ ⟨1, by norm_num⟩ = T.p := by
  rw [arcA₂, bArc_one]
  have h : circlePoint (T.θp - 2 * Real.pi) = circlePoint T.θp := by
    have h1 := _root_.Work.Smooth.SphereJordan.circlePoint_add_int_mul T.θp (-1)
    rwa [show T.θp + ((-1 : ℤ) : ℝ) * (2 * Real.pi) = T.θp - 2 * Real.pi by push_cast; ring] at h1
  rw [h]; exact T.hθp

theorem arcB₁_zero : T.arcB₁ ⟨0, by norm_num⟩ = T.a := by
  rw [arcB₁, bArc_zero]; exact T.hφa

theorem arcB₁_one : T.arcB₁ ⟨1, by norm_num⟩ = T.b := by
  rw [arcB₁, bArc_one]
  have h : circlePoint (T.φb + 2 * Real.pi) = circlePoint T.φb := by
    have h1 := _root_.Work.Smooth.SphereJordan.circlePoint_add_int_mul T.φb 1
    rwa [show T.φb + ((1 : ℤ) : ℝ) * (2 * Real.pi) = T.φb + 2 * Real.pi by push_cast; ring] at h1
  rw [h]; exact T.hφb

theorem arcB₂_zero : T.arcB₂ ⟨0, by norm_num⟩ = T.a := by
  rw [arcB₂, bArc_zero]
  exact T.hφa

theorem arcB₂_one : T.arcB₂ ⟨1, by norm_num⟩ = T.b := by
  rw [arcB₂, bArc_one]; exact T.hφb

theorem arcA_zero (i : Bool) : T.arcA i ⟨0, by norm_num⟩ = T.q := by
  cases i
  · simpa [arcA] using T.arcA₂_zero
  · simpa [arcA] using T.arcA₁_zero

theorem arcA_one (i : Bool) : T.arcA i ⟨1, by norm_num⟩ = T.p := by
  cases i
  · simpa [arcA] using T.arcA₂_one
  · simpa [arcA] using T.arcA₁_one

theorem arcB_zero (j : Bool) : T.arcB j ⟨0, by norm_num⟩ = T.a := by
  cases j
  · simpa [arcB] using T.arcB₂_zero
  · simpa [arcB] using T.arcB₁_zero

theorem arcB_one (j : Bool) : T.arcB j ⟨1, by norm_num⟩ = T.b := by
  cases j
  · simpa [arcB] using T.arcB₂_one
  · simpa [arcB] using T.arcB₁_one

/-- Each boundary arc is injective. -/
theorem arcA_injective (i : Bool) : Function.Injective (T.arcA i) := by
  cases i
  · -- `arcA₂ = discArc f θq (θp - 2π)`
    refine bArc_injective T.f T.hf ?_ ?_
    · rw [abs_of_neg (by linarith [T.hθp_ub] : T.θp - 2 * Real.pi - T.θq < 0)]
      linarith [T.hθp_lt]
    · linarith [T.hθp_ub]
  · refine bArc_injective T.f T.hf ?_ ?_
    · rw [abs_of_pos (by linarith [T.hθp_lt] : (0:ℝ) < T.θp - T.θq)]
      linarith [T.hθp_ub]
    · linarith [T.hθp_lt]

theorem arcB_injective (j : Bool) : Function.Injective (T.arcB j) := by
  cases j
  · -- `arcB₂ = discArc g φa φb`
    refine bArc_injective T.g T.hg ?_ ?_
    · rw [abs_of_neg (by linarith [T.hφa_lt] : T.φb - T.φa < 0)]
      linarith [T.hφa_ub]
    · linarith [T.hφa_lt]
  · refine bArc_injective T.g T.hg ?_ ?_
    · rw [abs_of_pos (by linarith [T.hφa_ub] : (0:ℝ) < T.φb + 2 * Real.pi - T.φa)]
      linarith [T.hφa_lt]
    · linarith [T.hφa_ub]


/-! ## The four four-arc curves -/

/-- The boundary arcs of `D₁` as paths from `q` to `p`. -/
def pathA (i : Bool) : Path T.q T.p := ⟨T.arcA i, T.arcA_zero i, T.arcA_one i⟩

/-- The boundary arcs of `D₂` as paths from `a` to `b`. -/
def pathB (j : Bool) : Path T.a T.b := ⟨T.arcB j, T.arcB_zero j, T.arcB_one j⟩

/-- The joining arc `α` as a path from `p` to `a`. -/
def pathα : Path T.p T.a := ⟨T.α, rfl, rfl⟩

/-- The joining arc `β` reversed, as a path from `b` to `q`. -/
def pathβ : Path T.b T.q := (⟨T.β, rfl, rfl⟩ : Path T.q T.b).symm

/-- The first half of the loop: `q → p → a → b`. -/
def halfP (i j : Bool) : Path T.q T.b := (T.pathA i).trans ((T.pathα).trans (T.pathB j))

/-- The loop of the four arcs. -/
def loopP (i j : Bool) : Path T.q T.q := (T.halfP i j).trans (T.pathβ)

/-- The loop of the four arcs as a function on `[0,1]`. -/
def loopC (i j : Bool) : Set.Icc (0 : ℝ) 1 → ℂ := fun t => T.loopP i j t

/-- The loop of the four arcs as a continuous map on `[0,1]`. -/
def loopCf (i j : Bool) : C(Set.Icc (0 : ℝ) 1, ℂ) := ⟨T.loopC i j, (T.loopP i j).continuous⟩

theorem loopC_zero (i j : Bool) : T.loopC i j ⟨0, by norm_num⟩ = T.q := Path.source (T.loopP i j)

theorem loopC_one (i j : Bool) : T.loopC i j ⟨1, by norm_num⟩ = T.q := Path.target (T.loopP i j)

theorem loopC_closed (i j : Bool) : T.loopCf i j ⟨0, by norm_num⟩ = T.loopCf i j ⟨1, by norm_num⟩ :=
  (T.loopC_zero i j).trans (T.loopC_one i j).symm

/-- **The four-arc curve** `J_{ij}`: the boundary arc `i` of `D₁`, the arc `α`, the boundary arc
`j` of `D₂` and the reversed arc `β`. -/
def cur (i j : Bool) : Work.Smooth.Jordan.PlaneCurve :=
  loopCurve (T.loopCf i j) (T.loopC_closed i j)

/-! ## Range computations -/

theorem range_arcA_subset (i : Bool) : Set.range (T.arcA i) ⊆ D₁ := by
  intro x hx
  have hsub : (discCurve T.f).trace ⊆ D₁ := by
    rintro y ⟨θ, rfl⟩
    have h : T.f (circlePoint θ) ∈ Set.range T.f := ⟨circlePoint θ, rfl⟩
    rwa [T.hfr] at h
  cases i
  · exact hsub (discArc_trace_subset T.f T.θq (T.θp - 2 * Real.pi)
      (by simpa [arcA, arcA₂] using hx))
  · exact hsub (discArc_trace_subset T.f T.θq T.θp (by simpa [arcA, arcA₁] using hx))

theorem range_arcB_subset (j : Bool) : Set.range (T.arcB j) ⊆ D₂ := by
  intro x hx
  have hsub : (discCurve T.g).trace ⊆ D₂ := by
    rintro y ⟨θ, rfl⟩
    have h : T.g (circlePoint θ) ∈ Set.range T.g := ⟨circlePoint θ, rfl⟩
    rwa [T.hgr] at h
  cases j
  · exact hsub (discArc_trace_subset T.g T.φa T.φb
      (by simpa [arcB, arcB₂] using hx))
  · exact hsub (discArc_trace_subset T.g T.φa (T.φb + 2 * Real.pi)
      (by simpa [arcB, arcB₁] using hx))

theorem range_α_inter_left : Set.range T.α ∩ D₁ = {T.p} :=
  range_inter_left T.hdisj T.hα₀ T.hα₁ T.hαint

theorem range_α_inter_right : Set.range T.α ∩ D₂ = {T.a} :=
  range_inter_right T.hdisj T.hα₀ T.hα₁ T.hαint

theorem range_β_inter_left : Set.range T.β ∩ D₁ = {T.q} :=
  range_inter_left T.hdisj T.hβ₀ T.hβ₁ T.hβint

theorem range_β_inter_right : Set.range T.β ∩ D₂ = {T.b} :=
  range_inter_right T.hdisj T.hβ₀ T.hβ₁ T.hβint

theorem disjoint_range_αβ : Disjoint (Set.range T.α) (Set.range T.β) :=
  disjoint_range_of_ends T.hdisj T.hα₀ T.hα₁ T.hβ₀ T.hβ₁ T.hαint T.hβint T.hsep T.hαβ₀ T.hαβ₁

theorem range_arcA_inter_α (i : Bool) : Set.range (T.arcA i) ∩ Set.range T.α ⊆ {T.p} := by
  intro x hx
  have h : x ∈ Set.range T.α ∩ D₁ := ⟨hx.2, T.range_arcA_subset i hx.1⟩
  rw [T.range_α_inter_left] at h
  exact h

theorem range_arcA_inter_arcB (i j : Bool) :
    Set.range (T.arcA i) ∩ Set.range (T.arcB j) ⊆ (∅ : Set ℂ) := by
  intro x hx
  exact Set.disjoint_left.mp T.hdisj (T.range_arcA_subset i hx.1) (T.range_arcB_subset j hx.2)

theorem range_α_inter_arcB (j : Bool) : Set.range T.α ∩ Set.range (T.arcB j) ⊆ {T.a} := by
  intro x hx
  have h : x ∈ Set.range T.α ∩ D₂ := ⟨hx.1, T.range_arcB_subset j hx.2⟩
  rw [T.range_α_inter_right] at h
  exact h

theorem range_arcA_inter_β (i : Bool) : Set.range (T.arcA i) ∩ Set.range T.β ⊆ {T.q} := by
  intro x hx
  have h : x ∈ Set.range T.β ∩ D₁ := ⟨hx.2, T.range_arcA_subset i hx.1⟩
  rw [T.range_β_inter_left] at h
  exact h

theorem range_arcB_inter_β (j : Bool) : Set.range (T.arcB j) ∩ Set.range T.β ⊆ {T.b} := by
  intro x hx
  have h : x ∈ Set.range T.β ∩ D₂ := ⟨hx.2, T.range_arcB_subset j hx.1⟩
  rw [T.range_β_inter_right] at h
  exact h

theorem halfP_range (i j : Bool) :
    Set.range (T.halfP i j) = Set.range (T.arcA i) ∪ Set.range T.α ∪ Set.range (T.arcB j) := by
  rw [ThetaSetup.halfP, path_range_trans, path_range_trans]
  ext x
  simp only [Set.mem_union]
  tauto

theorem halfP_injective (i j : Bool) : Function.Injective (T.halfP i j) := by
  refine path_inj_trans (T.pathA i) ((T.pathα).trans (T.pathB j)) (T.arcA_injective i) ?_ ?_
  · refine path_inj_trans (T.pathα) (T.pathB j) T.hαinj (T.arcB_injective j) ?_
    intro x hx
    exact T.range_α_inter_arcB j hx
  · intro x hx
    have h := hx
    rw [path_range_trans] at h
    rcases h.2 with h2 | h2
    · exact T.range_arcA_inter_α i ⟨h.1, h2⟩
    · exact (T.range_arcA_inter_arcB i j ⟨h.1, h2⟩).elim

theorem halfP_inter_β (i j : Bool) :
    Set.range (T.halfP i j) ∩ Set.range T.β ⊆ {T.q, T.b} := by
  rw [T.halfP_range i j]
  intro x hx
  rcases hx.1 with (h | h) | h
  · have h1 := T.range_arcA_inter_β i ⟨h, hx.2⟩
    rw [Set.mem_singleton_iff] at h1
    rw [h1]
    exact Set.mem_insert_iff.mpr (Or.inl rfl)
  · exact (Set.disjoint_left.mp T.disjoint_range_αβ h hx.2).elim
  · have h1 := T.range_arcB_inter_β j ⟨h, hx.2⟩
    rw [Set.mem_singleton_iff] at h1
    rw [h1]
    exact Set.mem_insert_iff.mpr (Or.inr rfl)

theorem loopP_injOn (i j : Bool) :
    Set.InjOn (T.loopC i j) {t : Set.Icc (0 : ℝ) 1 | (t : ℝ) < 1} := by
  refine path_injOn_trans_loop (T.halfP i j) (T.pathβ) (T.halfP_injective i j)
    (path_injective_symm T.hβinj) ?_
  rw [show Set.range (T.pathβ) = Set.range T.β from Path.symm_range _]
  exact T.halfP_inter_β i j

/-- **Each four-arc curve is a simple closed plane curve.** -/
theorem cur_isSimple (i j : Bool) : (T.cur i j).IsSimple :=
  loopCurve_isSimple (T.loopCf i j) (T.loopC_closed i j) (T.loopP_injOn i j)

theorem cur_range (i j : Bool) :
    (T.cur i j).trace = Set.range (T.arcA i) ∪ Set.range T.α ∪ Set.range (T.arcB j)
      ∪ Set.range T.β := by
  have h1 : Set.range (T.loopCf i j)
      = Set.range (T.arcA i) ∪ Set.range T.α ∪ Set.range (T.arcB j) ∪ Set.range T.β := by
    rw [show Set.range (T.loopCf i j) = Set.range (T.loopC i j) from rfl]
    rw [show Set.range (T.loopC i j) = Set.range (T.halfP i j) ∪ Set.range (T.pathβ) from
      path_range_trans _ _]
    rw [T.halfP_range i j,
      show Set.range (T.pathβ) = Set.range T.β from Path.symm_range _]
  rw [ThetaSetup.cur, Work.Smooth.Jordan.PlaneCurve.trace, range_loopCurve]
  exact h1

theorem cur_subset (i j : Bool) :
    (T.cur i j).trace ⊆ D₁ ∪ D₂ ∪ Set.range T.α ∪ Set.range T.β := by
  rw [T.cur_range i j]
  intro x hx
  rcases hx with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (T.range_arcA_subset i h)))
  · exact Or.inl (Or.inr h)
  · exact Or.inl (Or.inl (Or.inr (T.range_arcB_subset j h)))
  · exact Or.inr h

theorem range_α_subset_cur (i j : Bool) : Set.range T.α ⊆ (T.cur i j).trace := by
  rw [T.cur_range i j]
  intro x hx
  simp only [Set.mem_union]
  tauto

theorem range_β_subset_cur (i j : Bool) : Set.range T.β ⊆ (T.cur i j).trace := by
  rw [T.cur_range i j]
  intro x hx
  simp only [Set.mem_union]
  tauto

end ThetaSetup


/-! ## Choosing the boundary parameters -/

/-- Reduction of a real number modulo `2π` into `[0, 2π)`. -/
def angMod (τ : ℝ) : ℝ := τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)

theorem angMod_mem (τ : ℝ) : angMod τ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨?_, ?_⟩
  · have := (le_div_iff₀ hpos).mp (Int.floor_le (τ / (2 * Real.pi)))
    rw [angMod]; linarith
  · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (τ / (2 * Real.pi)))
    rw [angMod]; linarith

/-- **A boundary parameter in a prescribed half-open period.**  If `p` is the image of some boundary
point of the disc map `F`, then it is the image of a boundary parameter in the interval
`(w, w + 2π)`, provided `F (e^{iw}) ≠ p`. -/
theorem exists_parameter_Ioo {F : C(Disc, ℂ)} {w : ℝ} {p : ℂ}
    (hp : ∃ θ : ℝ, F (circlePoint θ) = p) (hne : F (circlePoint w) ≠ p) :
    ∃ θ ∈ Set.Ioo w (w + 2 * Real.pi), F (circlePoint θ) = p := by
  obtain ⟨ρ, hρ⟩ := hp
  set k : ℤ := ⌊(ρ - w) / (2 * Real.pi)⌋ with hk
  have hper : angMod (ρ - w) = (ρ - w) - (k : ℝ) * (2 * Real.pi) := by
    rw [angMod, hk]
  refine ⟨w + angMod (ρ - w), ⟨?_, ?_⟩, ?_⟩
  · rcases eq_or_lt_of_le (angMod_mem (ρ - w)).1 with h0 | h0
    · exfalso
      have hz : (ρ - w) - (k : ℝ) * (2 * Real.pi) = 0 := by rw [← hper]; exact h0.symm
      have hshift : ρ = w + (k : ℝ) * (2 * Real.pi) := by linarith
      have : circlePoint ρ = circlePoint w := by
        rw [hshift]
        exact _root_.Work.Smooth.SphereJordan.circlePoint_add_int_mul w k
      exact hne (by rw [← hρ, this])
    · linarith
  · have := (angMod_mem (ρ - w)).2
    linarith
  · have hshift : w + angMod (ρ - w) = ρ - (k : ℝ) * (2 * Real.pi) := by
      rw [hper]; ring
    rw [hshift]
    have h2 : ρ - (k : ℝ) * (2 * Real.pi) = ρ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [h2, _root_.Work.Smooth.SphereJordan.circlePoint_add_int_mul ρ (-k)]
    exact hρ

/-- **The four-arc configuration from the raw hypotheses of the theta graph.** -/
theorem exists_thetaSetup
    (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {D₁ D₂ : Set ℂ}
    (hD₁ : ∃ f : C(Disc, ℂ), Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Disc, ℂ), Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, ℂ)) (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ T : ThetaSetup D₁ D₂, T.α = α ∧ T.β = β := by
  obtain ⟨f, hf, hfr⟩ := hD₁
  obtain ⟨g, hg, hgr⟩ := hD₂
  obtain ⟨-, hβ₀fr, hα₁fr, hβ₁fr⟩ :=
    endpoints_mem_frontier ⟨f, hf, hfr⟩ ⟨g, hg, hgr⟩ α β hα₀ hα₁ hβ₀ hβ₁ hαint hβint
  have hα₀fr : α ⟨0, by norm_num⟩ ∈ frontier D₁ :=
    mem_frontier_of_mem_of_arc_avoid (isClosed_of_range_disc ⟨f, hf, hfr⟩) hα₀ rfl
      (fun t ht h => hαint t ht (Or.inl h))
  have hα₀fr' : α ⟨0, by norm_num⟩ ∈ frontier (Set.range f) := by rw [hfr]; exact hα₀fr
  have hβ₀fr' : β ⟨0, by norm_num⟩ ∈ frontier (Set.range f) := by rw [hfr]; exact hβ₀fr
  have hβ₁fr' : β ⟨1, by norm_num⟩ ∈ frontier (Set.range g) := by rw [hgr]; exact hβ₁fr
  have hα₁fr' : α ⟨1, by norm_num⟩ ∈ frontier (Set.range g) := by rw [hgr]; exact hα₁fr
  obtain ⟨θq, hθq⟩ := mem_trace_discCurve_of_mem_frontier (f := f) hf hβ₀fr'
  obtain ⟨φb, hφb⟩ := mem_trace_discCurve_of_mem_frontier (f := g) hg hβ₁fr'
  obtain ⟨θp, hθp_mem, hθp⟩ := exists_parameter_Ioo (w := θq) (p := α ⟨0, by norm_num⟩)
    (mem_trace_discCurve_of_mem_frontier (f := f) hf hα₀fr')
    (fun hcon => hαβ₀ (hcon.symm.trans hθq))
  obtain ⟨φa, hφa_mem, hφa⟩ := exists_parameter_Ioo (w := φb) (p := α ⟨1, by norm_num⟩)
    (mem_trace_discCurve_of_mem_frontier (f := g) hg hα₁fr')
    (fun hcon => hαβ₁ (hcon.symm.trans hφb))
  exact ⟨ThetaSetup.mk f hf hfr g hg hgr hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint
    hsep hαβ₀ hαβ₁ θq θp φa φb hθq hθp_mem.1 hθp_mem.2 hθp hφb hφa_mem.1 hφa_mem.2 hφa, rfl,
    rfl⟩

end

end Work.Smooth.SphereJordan
