import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.LandLeaves.dynRay_local_subset
import Submission.Work.LandLeaves.ccBet_angDouble_of_typeSet_short
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.ELTop.All
import Submission.Work.TopJordan.Main
import Submission.Work.TopJordan.SidesAPI
import Submission.Work.LandLeaves.isDynBottcherHomeo_of_isDynBottcher
import Submission.Work.LandLeaves.preconnected_rayAccum
import Submission.Work.LandLeaves.InArcHard.type_ccBet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

/-! ## Arithmetic: `ccBet` in terms of the three arc lengths

For three angles `a, b, x` with the three cyclic arcs
`p = fract (b - a)`, `q = fract (x - b)`, `r = fract (a - x)` (all non-zero), the cyclic
betweenness `ccBet a b x` is equivalent to `p + q + r = 2`.  The sum is always an integer and
lies in `[0,3)`, so it takes one of the values `0,1,2`. -/

/-- `fract (x - a) = fract (fract (x - b) + fract (b - a))`. -/
theorem fract_sub_eq_fract_add (a b x : ℝ) :
    Int.fract (x - a) = Int.fract (Int.fract (x - b) + Int.fract (b - a)) := by
  rw [Int.fract_eq_fract]
  refine ⟨⌊x - b⌋ + ⌊b - a⌋, ?_⟩
  have h1 : x - b - Int.fract (x - b) = (⌊x - b⌋ : ℝ) := Int.self_sub_fract _
  have h2 : b - a - Int.fract (b - a) = (⌊b - a⌋ : ℝ) := Int.self_sub_fract _
  push_cast
  linarith

/-- The sum of the three cyclic arc lengths of a triple of angles is an integer. -/
theorem fract_arcSum_cast (a b x : ℝ) :
    ∃ m : ℤ, Int.fract (b - a) + Int.fract (x - b) + Int.fract (a - x) = (m : ℝ) := by
  refine ⟨-(⌊b - a⌋ + ⌊x - b⌋ + ⌊a - x⌋), ?_⟩
  have h1 : b - a - Int.fract (b - a) = (⌊b - a⌋ : ℝ) := Int.self_sub_fract _
  have h2 : x - b - Int.fract (x - b) = (⌊x - b⌋ : ℝ) := Int.self_sub_fract _
  have h3 : a - x - Int.fract (a - x) = (⌊a - x⌋ : ℝ) := Int.self_sub_fract _
  push_cast
  linarith

/-- The sum of the three cyclic arc lengths of a triple of angles lies in `[0,3)`. -/
theorem fract_arcSum_bounds (a b x : ℝ) :
    0 ≤ Int.fract (b - a) + Int.fract (x - b) + Int.fract (a - x) ∧
      Int.fract (b - a) + Int.fract (x - b) + Int.fract (a - x) < 3 := by
  have h1 := Int.fract_nonneg (b - a)
  have h2 := Int.fract_nonneg (x - b)
  have h3 := Int.fract_nonneg (a - x)
  have h4 := Int.fract_lt_one (b - a)
  have h5 := Int.fract_lt_one (x - b)
  have h6 := Int.fract_lt_one (a - x)
  constructor <;> linarith

/-- The sum of the three cyclic arc lengths of a triple of angles is at most `2`. -/
theorem fract_arcSum_le_two (a b x : ℝ) :
    Int.fract (b - a) + Int.fract (x - b) + Int.fract (a - x) ≤ 2 := by
  obtain ⟨m, hm⟩ := fract_arcSum_cast a b x
  obtain ⟨-, hlt⟩ := fract_arcSum_bounds a b x
  rw [hm] at hlt ⊢
  have : m ≤ (2 : ℤ) := by
    have h : m < (3 : ℤ) := by exact_mod_cast hlt
    omega
  exact_mod_cast this

/-- **`ccBet` in terms of the three arc lengths.** -/
theorem ccBet_iff_arcSum {a b x : ℝ} (hq : 0 < Int.fract (x - b))
    (hr : 0 < Int.fract (a - x)) :
    ccBet a b x ↔ Int.fract (b - a) + Int.fract (x - b) + Int.fract (a - x) = 2 := by
  set p := Int.fract (b - a) with hp
  set q := Int.fract (x - b) with hqdef
  set r := Int.fract (a - x) with hrdef
  have hp0 : 0 ≤ p := Int.fract_nonneg _
  have hp1 : p < 1 := Int.fract_lt_one _
  have hq1 : q < 1 := Int.fract_lt_one _
  have hr1 : r < 1 := Int.fract_lt_one _
  have hq0 : 0 < q := hq
  have hr0 : 0 < r := hr
  have hfsub : Int.fract (x - a) = Int.fract (q + p) := by
    have := fract_sub_eq_fract_add a b x
    rwa [← hp, ← hqdef] at this
  have hfract_gt : 1 < q + p → Int.fract (q + p) = q + p - 1 := by
    intro h
    have h1 : 0 ≤ q + p - 1 := by linarith
    have h2 : q + p - 1 < 1 := by linarith
    have h3 : Int.fract (q + p - 1) = q + p - 1 := Int.fract_eq_self.mpr ⟨h1, h2⟩
    have h4 : Int.fract (q + p) = Int.fract (q + p - 1) := by
      conv_lhs => rw [show q + p = (q + p - 1) + ((1 : ℤ) : ℝ) by push_cast; ring]
      exact Int.fract_add_intCast _ 1
    rw [h4, h3]
  -- the key arithmetic equivalence
  have hkey : (0 < Int.fract (q + p) ∧ Int.fract (q + p) < p) ↔ 1 < q + p := by
    constructor
    · rintro ⟨hpos, hlt⟩
      by_contra hcon
      push_neg at hcon
      rcases lt_or_eq_of_le hcon with hlt1 | heq
      · have : Int.fract (q + p) = q + p := Int.fract_eq_self.mpr ⟨by linarith, hlt1⟩
        rw [this] at hlt; linarith
      · have : Int.fract (q + p) = 0 := by rw [heq]; exact Int.fract_eq_zero_iff.mpr ⟨1, by norm_num⟩
        rw [this] at hpos; exact lt_irrefl 0 hpos
    · intro h
      rw [hfract_gt h]
      exact ⟨by linarith, by linarith⟩
  rw [ccBet, hfsub, hkey]
  constructor
  · intro h
    have hle2 : p + q + r ≤ 2 := by
      have := fract_arcSum_le_two a b x
      rwa [← hp, ← hqdef, ← hrdef] at this
    obtain ⟨m, hm⟩ := fract_arcSum_cast a b x
    rw [← hp, ← hqdef, ← hrdef] at hm
    have hm2 : m = 2 := by
      have h1 : (1 : ℤ) < m := by
        have : (1 : ℝ) < (m : ℝ) := by rw [← hm]; linarith
        exact_mod_cast this
      have h2 : m ≤ (2 : ℤ) := by
        have : (m : ℝ) ≤ 2 := by rw [← hm]; exact hle2
        exact_mod_cast this
      omega
    rw [hm, hm2]; norm_num
  · intro h
    linarith


/-- `ccBet` is invariant under cyclic rotation of the triple. -/
theorem ccBet_rot_local {A B X : ℝ} (h : ccBet A B X) : ccBet B X A := by
  obtain ⟨h1, h2⟩ := h
  have hA : Int.fract (B - A) ≠ 0 := ne_of_gt (lt_trans h1 h2)
  have hAB : Int.fract (A - B) = 1 - Int.fract (B - A) := by
    have h' : A - B = -(B - A) := by ring
    rw [h', Int.fract_neg hA]
  have hsplit : X - B = (X - A) - (B - A) := by ring
  have hXB : Int.fract (X - B) = Int.fract (X - A) - Int.fract (B - A) + 1 := by
    rw [hsplit]
    have hw : X - A = Int.fract (X - A) + (⌊X - A⌋ : ℝ) := by
      have := Int.fract_add_floor (X - A); linarith
    have hv : B - A = Int.fract (B - A) + (⌊B - A⌋ : ℝ) := by
      have := Int.fract_add_floor (B - A); linarith
    have hkey : (X - A) - (B - A) =
        (Int.fract (X - A) - Int.fract (B - A) + 1) + ((⌊X - A⌋ - ⌊B - A⌋ - 1 : ℤ) : ℝ) := by
      push_cast; linarith
    have h1 : 0 ≤ Int.fract (X - A) - Int.fract (B - A) + 1 := by
      linarith [Int.fract_nonneg (X - A), Int.fract_lt_one (B - A)]
    have h2' : Int.fract (X - A) - Int.fract (B - A) + 1 < 1 := by linarith
    rw [hkey, Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨h1, h2'⟩]
  rw [ccBet, hAB, hXB]
  constructor <;> linarith [Int.fract_lt_one (B - A)]

/-! ## The cyclic order of the rays at a level

The external rays `R(θ)` (`θ ∈ K`, i.e. `rayAccum c φ θ = {y}`) all land at `y`.  At a fixed
level `R < ...` the ray `R(θ)` meets the level circle in the point `rayPt θ R`; the cyclic order
of these points on the level circle is a `ccBet`-relation on the angles, obtained by comparing
the arguments (as seen from `y`) of the level points.

`levelBet u v w` is the assertion that the level point of `w` lies on the counterclockwise arc
from the level point of `u` to the level point of `v`.  It is a genuine betweenness relation
(`levelBet_rot`), and it is the *plane* betweenness, to be compared with the *angle* betweenness
`ccBet`. -/

/-- The argument (in turns) of the level-`2` ray point of angle `θ`, as seen from `y`. -/
noncomputable def levelArg {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (y : ℂ) (θ : ℝ) : ℝ :=
  Complex.arg (Work.EL.rayPt hN θ 2 - y) / (2 * Real.pi)

/-- **The plane betweenness at level `2`**: the level point of `w` lies on the counterclockwise
arc from the level point of `u` to the level point of `v`, as seen from `y`. -/
noncomputable def levelBet {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (y : ℂ)
    (u v w : ℝ) : Prop :=
  ccBet (levelArg hN y u) (levelArg hN y v) (levelArg hN y w)

/-- `levelBet` is a betweenness relation: it is invariant under cyclic rotations. -/
theorem levelBet_rot {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (y : ℂ) {u v w : ℝ}
    (h : levelBet hN y u v w) : levelBet hN y v w u :=
  ccBet_rot_local h

/-- `levelBet` is a betweenness relation: it is invariant under cyclic rotations (equivalence). -/
theorem levelBet_rot_iff {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (y : ℂ) {u v w : ℝ} :
    levelBet hN y u v w ↔ levelBet hN y v w u := by
  constructor
  · exact levelBet_rot hN y
  · intro h
    have := levelBet_rot hN y (levelBet_rot hN y h)
    simpa [levelBet, ccBet] using this

theorem ccBet_angDouble_of_hard_case {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hp : 1 < (4 : ℝ) ^ k * Int.fract (b - a))
    (hq : 1 < (4 : ℝ) ^ k * Int.fract (x - b))
    (hr : 1 < (4 : ℝ) ^ k * Int.fract (a - x))
    (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  exact Work.LandLeaves.InArcHard.type_ccBet hφ hrep ha hb hx hab

end Work.LandLeaves
