import Mathlib
import Submission.Work.Drive.OrderDefs
import Submission.Work.Drive.rot90
import Submission.Work.Drive.dirC_half_perp

/-!
# The midpoint curve of a direction (Emch's picture for the inscribed square)

For a plane curve `γ` and a nonzero direction `u`, `MidFig γ u` is the set of midpoints of chords of `γ`
parallel to `u`:

`m ∈ MidFig γ u ↔ ∃ x y : Circle, x ≠ y ∧ (∃ c : ℝ, γ x - γ y = c • u) ∧ γ x + γ y = 2 • m`.

The classical proof of the inscribed square (Emch 1916) intersects the two curves `MidFig γ u` and
`MidFig γ (rot90 u)`:

* a common point `m` is the centre of an inscribed **rhombus** — two chords with the same midpoint `m`
  whose directions are perpendicular;
* as `u` rotates through a right angle the two curves are interchanged, so the two diagonal lengths of
  the rhombus are exchanged, while they vary continuously; by the intermediate value theorem some
  direction gives equal diagonals, i.e. an inscribed **square**.

`IsRhombusCentre γ u m` is the common-point condition. -/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- Midpoints of chords of `γ` parallel to the direction `u`. -/
def MidFig (γ : Circle → ℝ × ℝ) (u : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {m | ∃ x y : Circle, x ≠ y ∧ (∃ c : ℝ, γ x - γ y = c • u) ∧ γ x + γ y = 2 • m}

lemma mem_MidFig {γ : Circle → ℝ × ℝ} {u m : ℝ × ℝ} :
    m ∈ MidFig γ u ↔ ∃ x y : Circle, x ≠ y ∧ (∃ c : ℝ, γ x - γ y = c • u) ∧
      γ x + γ y = 2 • m := Iff.rfl

/-- `m` is the centre of an inscribed rhombus of `γ` with diagonals parallel to `u` and `rot90 u`. -/
def IsRhombusCentre (γ : Circle → ℝ × ℝ) (u m : ℝ × ℝ) : Prop :=
  m ∈ MidFig γ u ∧ m ∈ MidFig γ (rot90 u)

lemma isRhombusCentre_iff {γ : Circle → ℝ × ℝ} {u m : ℝ × ℝ} :
    IsRhombusCentre γ u m ↔ m ∈ MidFig γ u ∧ m ∈ MidFig γ (rot90 u) := Iff.rfl

/-- The coordinate of a point of the plane in the direction `u`. -/
def coord (u p : ℝ × ℝ) : ℝ := Submission.Geometry.eucDot p u

/-- `x` is an extreme point of the level set of the `rot90 u`-coordinate of `γ` at height `c`: a point
of `γ` of that height realising the least, or the greatest, `u`-coordinate along the line.  The chords
joining such extreme pairs are Emch's "outermost chords" ("shell-1 pairing"): they form a canonically
chosen, continuously varying sub-family of `MidFig γ u`, which is why the classical proof of the
inscribed square can avoid choosing a branch of the full intersection `MidFig γ u ∩ MidFig γ (rot90 u)`
(whose fibres are odd but carry no continuous selection). -/
def IsExtremeLevel (γ : Circle → ℝ × ℝ) (u : ℝ × ℝ) (c : ℝ) (x : Circle) : Prop :=
  coord (rot90 u) (γ x) = c ∧
    ((∀ y : Circle, coord (rot90 u) (γ y) = c → coord u (γ y) ≤ coord u (γ x)) ∨
     (∀ y : Circle, coord (rot90 u) (γ y) = c → coord u (γ x) ≤ coord u (γ y)))

/-- The midpoints of the outermost chords of `γ` in the direction `u`: the pairs of extreme points of
the level sets of the `rot90 u`-coordinate.  This is the canonical sub-arc of `MidFig γ u` used by the
parity argument in `Drive/INSCRIBED_SQUARE_STATUS.md`. -/
def OutermostFig (γ : Circle → ℝ × ℝ) (u : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {m | ∃ x x' : Circle, IsExtremeLevel γ u (coord (rot90 u) (γ x)) x ∧
      IsExtremeLevel γ u (coord (rot90 u) (γ x)) x' ∧ γ x + γ x' = 2 • m}

/-- A nonzero vector parallel to `rot90 u` has doubled direction `dirC u + 1 / 2`. -/
lemma dirC_of_parallel_rot90 {u v : ℝ × ℝ} (hu : u ≠ 0)
    (hv : ∃ c : ℝ, c ≠ 0 ∧ v = c • rot90 u) :
    Submission.Collision.dirC v = Submission.Collision.dirC u + ((1 / 2 : ℝ) : UnitAddCircle) := by
  obtain ⟨c, hc, rfl⟩ := hv
  have hcv : c • rot90 u ≠ 0 := by
    intro h0
    rcases smul_eq_zero.mp h0 with h | h
    · exact hc h
    · exact rot90_ne_zero hu h
  rw [dirC_half_perp hcv hu]
  simp only [Submission.Geometry.eucDot, rot90, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- **A rhombus with equal diagonals is an inscribed square.**  If two chords of `γ` have a common
midpoint, perpendicular directions (one parallel to `u ≠ 0`, the other to `rot90 u`) and equal length,
then their doubled directions differ by `1 / 2`, so `1 / 2 ∈ GoodC γ`: the two chords are the diagonals
of an inscribed square.  This is the link from Emch's rhombus picture to the collision condition at
`u = 1 / 2`, and together with `rhombusCentre_exists` and the intermediate-value step over the rotating
direction it yields the inscribed square. -/
theorem half_mem_GoodC_of_rhombus {γ : Circle → ℝ × ℝ} {u : ℝ × ℝ} (hu : u ≠ 0)
    {x y x' y' : Circle} (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hpar : ∃ c : ℝ, c ≠ 0 ∧ γ x - γ y = c • u)
    (hpar' : ∃ c : ℝ, c ≠ 0 ∧ γ x' - γ y' = c • rot90 u)
    (hmid : γ x + γ y = γ x' + γ y')
    (hlen : Submission.Geometry.eucNorm (γ x - γ y) = Submission.Geometry.eucNorm (γ x' - γ y')) :
    ((1 / 2 : ℝ) : UnitAddCircle) ∈ Submission.Configuration.GoodC γ := by
  obtain ⟨c, hc, hc'⟩ := hpar
  obtain ⟨c', hc'ne, hc''⟩ := hpar'
  have h1 : Submission.Collision.dirC (γ x - γ y) = Submission.Collision.dirC u := by
    rw [hc']; exact dirC_smul_ne hc u
  have h2 : Submission.Collision.dirC (γ x' - γ y') =
      Submission.Collision.dirC u + ((1 / 2 : ℝ) : UnitAddCircle) := by
    exact dirC_of_parallel_rot90 hu ⟨c', hc'ne, hc''⟩
  refine ⟨x, y, x', y', hxy, hx'y', ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (γ x + γ y) / 2 = (γ x' + γ y') / 2
    rw [hmid]
  · show Submission.Collision.dirC (γ x - γ y) =
      Submission.Collision.dirC (γ x' - γ y') + ((1 / 2 : ℝ) : UnitAddCircle)
    have hhalf : ((1 / 2 : ℝ) : UnitAddCircle) + ((1 / 2 : ℝ) : UnitAddCircle) = 0 := by
      rw [← AddCircle.coe_add, AddCircle.coe_eq_zero_iff]
      exact ⟨1, by norm_num⟩
    rw [h1, h2, add_assoc, hhalf, add_zero]
  · show Submission.Geometry.eucNorm (γ x - γ y) = Submission.Geometry.eucNorm (γ x' - γ y')
    rw [hlen]

/-- **Emch's intermediate-value step.**  If two continuous functions exchange their values under the
shift `θ ↦ θ + π / 2` — the two diagonal lengths of an inscribed rhombus under rotation of the
direction through a right angle — then they agree somewhere, i.e. some direction gives a square. -/
theorem exists_eq_of_continuous_swap (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hswap : ∀ θ, a (θ + Real.pi / 2) = b θ ∧ b (θ + Real.pi / 2) = a θ) :
    ∃ θ, a θ = b θ := by
  by_contra hcon
  push_neg at hcon
  set f : ℝ → ℝ := fun θ => a θ - b θ with hf
  have hcont : Continuous f := ha.sub hb
  have hanti : ∀ θ, f (θ + Real.pi / 2) = - f θ := by
    intro θ
    simp only [hf]
    rw [(hswap θ).1, (hswap θ).2]
    ring
  have hpos : 0 < Real.pi / 2 := by positivity
  have hf0 : f (Real.pi / 2) = - f 0 := by
    have := hanti 0
    simpa using this
  have hne0 : f 0 ≠ 0 := by
    intro h0
    refine hcon 0 ?_
    have := (sub_eq_zero.mp (show a 0 - b 0 = 0 from h0))
    simpa using this
  rcases lt_or_gt_of_ne hne0 with hlt | hgt
  · have h2 : 0 < f (Real.pi / 2) := by rw [hf0]; linarith
    obtain ⟨x, -, hfx⟩ :=
      intermediate_value_Icc hpos.le hcont.continuousOn (show (0:ℝ) ∈ Set.Icc (f 0) (f (Real.pi / 2))
        from ⟨hlt.le, h2.le⟩)
    refine hcon x ?_
    simpa using (sub_eq_zero.mp (show a x - b x = 0 from hfx))
  · have h2 : f (Real.pi / 2) < 0 := by rw [hf0]; linarith
    have hpi : f Real.pi = - f (Real.pi / 2) := by
      have := hanti (Real.pi / 2)
      rwa [show Real.pi / 2 + Real.pi / 2 = Real.pi by ring] at this
    have h3 : 0 < f Real.pi := by rw [hpi]; linarith
    obtain ⟨x, -, hfx⟩ :=
      intermediate_value_Icc (show Real.pi / 2 ≤ Real.pi by linarith) hcont.continuousOn
        (show (0:ℝ) ∈ Set.Icc (f (Real.pi / 2)) (f Real.pi) from ⟨h2.le, h3.le⟩)
    refine hcon x ?_
    simpa using (sub_eq_zero.mp (show a x - b x = 0 from hfx))

end Work.Drive
