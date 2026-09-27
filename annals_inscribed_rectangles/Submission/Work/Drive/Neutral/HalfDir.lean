import Mathlib
import Submission.Work.Drive.CrossingDefs
import Submission.Work.Drive.WindingNumber
import Submission.Work.Drive.degree_crossing_count
import Submission.Work.Drive.DegreeTools
import Submission.Work.Drive.arg_div_pi_coe_eq_zero_iff
import Submission.Work.Drive.finite_of_isCompact_of_isolated
import Submission.Work.Drive.curve_local_tangent_unique

/-!
# (Neutral copy) The half-direction of a closed plane curve, and line crossings

This is a **neutral copy** of `Submission/Work/Drive/line_crossings_even.lean` in the namespace
`Work.Drive.NH`, with two changes:

* the import of `Submission.Work.Drive.winding_eq_crossing_sum` is replaced by four local
  declarations (`toC`, `continuous_toC`, `toC_injective`, `toC_eq_zero_iff`) copied verbatim from it;
  this removes the *only* channel by which the declaration `Work.Drive.toC` — which clashes with the
  identically named declaration of `Submission/Work/Drive/UmlaufSetup.lean` (used throughout the
  capping world) — enters the chord-parity chapter;
* the final theorem `line_crossings_even`, the only consumer of `winding_eq_crossing_sum` and unused
  anywhere in the workspace, is dropped with it.

The consequent declarations of this file are `rescaleAngle`, `halfDir`, `halfDir_apply`,
`continuous_halfDir`, `halfDir_add_self` (and the `dirC`/crossing bookkeeping around them), which are
what the `GRB` chapter (`grbLevel`, `grbTransport`, `winding_eq_two_mul_degree_halfDir`,
`grbDeg_eq_straight`) actually uses.  The consumers are the neutral copies of those files in the
namespace `Work.Surf.ChordN`, leading to `Work.Surf.ChordN.chord_crossing_parity` — the strict base
case of the mod-2 intersection form of `ℝP²`, importable next to the capping world.
-/
/-!
# The crossings of a line with a smooth Jordan curve are even in number

Fix a smooth Jordan curve `γ : ℝ/ℤ → ℝ²`, a point `p` off the curve and a direction `u ≠ 0`, and
suppose that the line `L = p + ℝu` meets `γ` only transversally (hypothesis `htrans`).  Then the set
of parameters at which `γ` crosses `L` is finite and has even cardinality.

This is the elementary mod-2 fact behind the "signed crossing count" description of the winding
number (`Work.Drive.winding_eq_crossing_sum`): a closed curve meets a line in an even number of
points.  The argument is a parity count.  The directed distance to the line,
`d t = det (γ t - p, u)`, is a `1`-periodic `C¹` function whose zero set in a period is exactly the
crossing set, and which has non-zero derivative at each of its zeros (`htrans`).  Hence every crossing
is a *regular* crossing, contributing a sign `±1` to the signed crossing count of the level `0`, which
on the one hand is the winding number of `γ` about `p`
(`Work.Drive.winding_eq_crossing_sum`), and on the other hand is congruent modulo `2` to the number of
crossings.  Finally the winding number is *even*: `Submission.Collision.dirC = arg / π` is the
*doubled* direction, so the direction map of the curve has a continuous square root, namely
`t ↦ arg (γ t - p) / (2π)`, and the degree of a square is twice the degree (`Work.Drive.degree_add`).
-/

namespace Work.Drive.NH

/-! ## The complexification `(x, y) ↦ x + y i` (neutral copy)

These four declarations are copied verbatim from `Submission/Work/Drive/winding_eq_crossing_sum.lean`,
where they are the only part of that file used by this one.  They are repeated here (in the namespace
`Work.Drive.NH`) so that this module — and hence the chord-parity chapter built on it — does **not**
import `winding_eq_crossing_sum.lean`, whose declaration `Work.Drive.toC` clashes with the identically
named declaration of `Submission/Work/Drive/UmlaufSetup.lean` (needed by the capping world). -/

/-- The complexification `(x, y) ↦ x + y i` of a point of the plane. -/
def toC (z : ℝ × ℝ) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

theorem continuous_toC : Continuous toC := by
  unfold toC
  fun_prop

theorem toC_injective : Function.Injective toC := by
  intro z w h
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp only [toC, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    zero_add] at h1 h2
  exact Prod.ext h1 h2

theorem toC_eq_zero_iff {z : ℝ × ℝ} : toC z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h1 : z = 0 := toC_injective (by rw [h]; simp [toC])
    exact h1
  · intro h
    rw [h]
    simp [toC]


open scoped Topology
open Set Filter

noncomputable section

/-! ## The direction class classifies the direction of the line -/

/-- `Submission.Collision.dirC` is `dirCz` read through the identification of `ℝ × ℝ` with `ℂ`. -/
lemma dirC_eq_dirCz' (v : ℝ × ℝ) : Submission.Collision.dirC v = dirCz (toC v) := by
  show ((Complex.arg (⟨v.1, v.2⟩ : ℂ) / Real.pi : ℝ) : UnitAddCircle)
      = ((Complex.arg (toC v) / Real.pi : ℝ) : UnitAddCircle)
  rw [show (⟨v.1, v.2⟩ : ℂ) = toC v from by apply Complex.ext <;> simp [toC]]

/-- Scaling a plane vector corresponds to multiplying the associated complex number. -/
lemma toC_smul' (a : ℝ) (p : ℝ × ℝ) : toC (a • p) = (a : ℂ) * toC p := by
  apply Complex.ext <;> simp [toC, Prod.smul_fst, Prod.smul_snd]

/-- The doubled direction class is invariant under non-zero scaling: it only sees the *line*. -/
lemma dirC_smul_eq {c : ℝ} {w : ℝ × ℝ} (hc : c ≠ 0) (hw : w ≠ 0) :
    Submission.Collision.dirC (c • w) = Submission.Collision.dirC w := by
  rw [dirC_eq_dirCz', dirC_eq_dirCz', toC_smul',
    dirCz_mul (by exact_mod_cast hc) (fun h => hw (toC_eq_zero_iff.mp h))]
  have h0 : dirCz ((c : ℂ)) = 0 := (arg_div_pi_coe_eq_zero_iff _).mpr (by simp)
  rw [h0, zero_add]

/-- **The doubled undirected direction classifies the line through the origin**: two non-zero plane
vectors have the same class exactly when they are parallel. -/
theorem dirC_eq_iff_parallel {v w : ℝ × ℝ} (hv : v ≠ 0) (hw : w ≠ 0) :
    Submission.Collision.dirC v = Submission.Collision.dirC w ↔ ∃ c : ℝ, c ≠ 0 ∧ v = c • w := by
  have hzv : toC v ≠ 0 := fun h => hv (toC_eq_zero_iff.mp h)
  have hzw : toC w ≠ 0 := fun h => hw (toC_eq_zero_iff.mp h)
  constructor
  · intro h
    have h' : dirCz (toC v) = dirCz (toC w) := by rwa [dirC_eq_dirCz', dirC_eq_dirCz'] at h
    have h1 : dirCz (toC v * (toC w)⁻¹) = 0 := by
      rw [dirCz_mul hzv (inv_ne_zero hzw), dirCz_inv hzw, h', add_neg_cancel]
    have him : (toC v * (toC w)⁻¹).im = 0 := (arg_div_pi_coe_eq_zero_iff _).mp h1
    obtain ⟨c, hc⟩ : ∃ c : ℝ, toC v * (toC w)⁻¹ = (c : ℂ) :=
      ⟨_, Complex.ext rfl (by rw [Complex.ofReal_im]; exact him)⟩
    have hmul : toC v = (c : ℂ) * toC w := by
      have h2 := congrArg (· * toC w) hc
      rwa [mul_assoc, inv_mul_cancel₀ hzw, mul_one] at h2
    refine ⟨c, ?_, ?_⟩
    · intro hc0
      rw [hc0] at hmul
      simp at hmul
      exact hzv hmul
    · refine toC_injective ?_
      rw [hmul, toC_smul']
  · rintro ⟨c, hc, rfl⟩
    exact dirC_smul_eq hc hw

/-! ## The crossing set is the level set of the doubled direction -/

/-- The crossing set of the line through `p` in direction `u` is exactly the set of `t` in one period
at which the doubled direction of `γ t - p` equals that of `u`. -/
lemma crossings_eq_dirC_level {γ : UnitAddCircle → ℝ × ℝ} {p u : ℝ × ℝ} (hp : p ∉ Set.range γ)
    (hu : u ≠ 0) :
    crossings γ p u =
      {t : ℝ | t ∈ Set.Ico 0 1 ∧ Submission.Collision.dirC (γ (t : UnitAddCircle) - p) =
        Submission.Collision.dirC u} := by
  ext t
  constructor
  · rintro ⟨ht, s, hs⟩
    refine ⟨ht, ?_⟩
    have hsne : s ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hs
      exact hp ⟨t, sub_eq_zero.mp hs⟩
    rw [hs]
    exact dirC_smul_eq hsne hu
  · rintro ⟨ht, hdir⟩
    have hv : γ (t : UnitAddCircle) - p ≠ 0 := by
      intro h
      exact hp ⟨t, sub_eq_zero.mp h⟩
    obtain ⟨c, hc, hcv⟩ := (dirC_eq_iff_parallel hv hu).mp hdir
    exact ⟨ht, c, hcv⟩

/-! ## Splitting the crossings by the sign of the crossing -/

/-- The set of crossings at which the curve crosses the line in the positive sense. -/
def posCross (γ : UnitAddCircle → ℝ × ℝ) (p u : ℝ × ℝ) : Set ℝ :=
  {t : ℝ | t ∈ Set.Ico 0 1 ∧ Submission.Collision.dirC (γ (t : UnitAddCircle) - p) =
      Submission.Collision.dirC u ∧
    0 < (γ (t : UnitAddCircle) - p).1 * (deriv (fun s : ℝ => γ (s : UnitAddCircle)) t).2
      - (γ (t : UnitAddCircle) - p).2 * (deriv (fun s : ℝ => γ (s : UnitAddCircle)) t).1}

/-- The set of crossings at which the curve crosses the line in the negative sense. -/
def negCross (γ : UnitAddCircle → ℝ × ℝ) (p u : ℝ × ℝ) : Set ℝ :=
  {t : ℝ | t ∈ Set.Ico 0 1 ∧ Submission.Collision.dirC (γ (t : UnitAddCircle) - p) =
      Submission.Collision.dirC u ∧
    (γ (t : UnitAddCircle) - p).1 * (deriv (fun s : ℝ => γ (s : UnitAddCircle)) t).2
      - (γ (t : UnitAddCircle) - p).2 * (deriv (fun s : ℝ => γ (s : UnitAddCircle)) t).1 < 0}

/-- Every transversal crossing of the line is a regular zero of the directed distance to the line. -/
lemma cross_term_ne_zero {γ : UnitAddCircle → ℝ × ℝ} {p u : ℝ × ℝ} (hp : p ∉ Set.range γ)
    (hu : u ≠ 0) (htrans : ∀ t ∈ crossings γ p u, cross2 u (cderiv γ t) ≠ 0)
    {t : ℝ} (ht : t ∈ Set.Ico 0 1)
    (hdir : Submission.Collision.dirC (γ (t : UnitAddCircle) - p) =
      Submission.Collision.dirC u) :
    cross2 (γ (t : UnitAddCircle) - p) (cderiv γ t) ≠ 0 := by
  have hv : γ (t : UnitAddCircle) - p ≠ 0 := by
    intro h; exact hp ⟨t, sub_eq_zero.mp h⟩
  obtain ⟨c, hc, hcv⟩ := (dirC_eq_iff_parallel hv hu).mp hdir
  have hcross : t ∈ crossings γ p u := by
    rw [crossings_eq_dirC_level hp hu]
    exact ⟨ht, hdir⟩
  rw [hcv, cross2_smul_left]
  exact mul_ne_zero hc (htrans t hcross)

lemma posCross_subset_crossings {γ : UnitAddCircle → ℝ × ℝ} {p u : ℝ × ℝ} (hp : p ∉ Set.range γ)
    (hu : u ≠ 0) : posCross γ p u ⊆ crossings γ p u := by
  intro t ht
  rw [crossings_eq_dirC_level hp hu]
  exact ⟨ht.1, ht.2.1⟩

lemma negCross_subset_crossings {γ : UnitAddCircle → ℝ × ℝ} {p u : ℝ × ℝ} (hp : p ∉ Set.range γ)
    (hu : u ≠ 0) : negCross γ p u ⊆ crossings γ p u := by
  intro t ht
  rw [crossings_eq_dirC_level hp hu]
  exact ⟨ht.1, ht.2.1⟩

lemma disjoint_posCross_negCross (γ : UnitAddCircle → ℝ × ℝ) (p u : ℝ × ℝ) :
    Disjoint (posCross γ p u) (negCross γ p u) := by
  rw [Set.disjoint_left]
  rintro t ⟨-, -, h1⟩ ⟨-, -, h2⟩
  linarith

/-- The crossing set splits into the positive and the negative crossings. -/
lemma crossings_eq_pos_union_neg (γ : UnitAddCircle → ℝ × ℝ)
    {p u : ℝ × ℝ} (hp : p ∉ Set.range γ) (hu : u ≠ 0)
    (htrans : ∀ t ∈ crossings γ p u, cross2 u (cderiv γ t) ≠ 0) :
    crossings γ p u = posCross γ p u ∪ negCross γ p u := by
  rw [crossings_eq_dirC_level hp hu]
  ext t
  constructor
  · rintro ⟨ht, hdir⟩
    have hne := cross_term_ne_zero hp hu htrans ht hdir
    show t ∈ posCross γ p u ∪ negCross γ p u
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨ht, hdir, h⟩
    · exact Or.inl ⟨ht, hdir, h⟩
  · intro ht
    rcases ht with ⟨ht, hdir, -⟩ | ⟨ht, hdir, -⟩
    · exact ⟨ht, hdir⟩
    · exact ⟨ht, hdir⟩

/-- A non-negative integer which is even as an integer is even. -/
lemma even_nat_of_even_int {n : ℕ} (h : Even (n : ℤ)) : Even n := by
  obtain ⟨k, hk⟩ := h
  have hk0 : 0 ≤ k := by
    have h1 : (0 : ℤ) ≤ k + k := by rw [← hk]; exact Int.natCast_nonneg n
    linarith
  refine ⟨k.toNat, ?_⟩
  have h2 : ((k.toNat : ℕ) : ℤ) + ((k.toNat : ℕ) : ℤ) = (n : ℤ) := by
    rw [Int.toNat_of_nonneg hk0, hk]
  exact_mod_cast h2.symm

/-! ## Finiteness of the crossing set

The directed distance to the line, `g t = cross2 u (γ t - p)`, is a `1`-periodic continuous function
with non-zero derivative at each of its zeros; hence every zero is isolated.  Its zero set in the
compact interval `[0,1]` is therefore finite, and the crossing set sits inside it. -/

/-- The chain rule for the directed distance along a curve. -/
lemma hasDerivAt_cross2_comp' {G : ℝ → ℝ × ℝ} {u V : ℝ × ℝ} {t : ℝ}
    (h : HasDerivAt G V t) : HasDerivAt (fun s => cross2 u (G s)) (cross2 u V) t := by
  have h1 : HasDerivAt (fun s : ℝ => (G s).1) V.1 t := by
    simpa using h.hasFDerivAt.fst.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (G s).2) V.2 t := by
    simpa using h.hasFDerivAt.snd.hasDerivAt
  have h3 : HasDerivAt (fun s : ℝ => u.1 * (G s).2 - u.2 * (G s).1)
      (u.1 * V.2 - u.2 * V.1) t := (h2.const_mul u.1).sub (h1.const_mul u.2)
  simpa only [cross2] using h3

/-- The derivative of a curve on the circle of circumference `1` is periodic. -/
lemma cderiv_add_one' (γ : UnitAddCircle → ℝ × ℝ) (t : ℝ) : cderiv γ (t + 1) = cderiv γ t := by
  have hfun : (fun s : ℝ => γ ((s + 1 : ℝ) : UnitAddCircle)) =
      (fun s : ℝ => γ (s : UnitAddCircle)) := by
    funext s
    rw [AddCircle.coe_add_period (1 : ℝ) s]
  have h := deriv_comp_add_const (fun s : ℝ => γ (s : UnitAddCircle)) 1 t
  rw [hfun] at h
  simpa [cderiv] using h.symm

/-- **The crossing set is finite.** -/
lemma crossings_finite_aux (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    (hsmooth : ContDiff ℝ 1 (fun t : ℝ => γ (t : UnitAddCircle)))
    {p u : ℝ × ℝ} (hp : p ∉ Set.range γ) (hu : u ≠ 0)
    (htrans : ∀ t ∈ crossings γ p u, cross2 u (cderiv γ t) ≠ 0) :
    (crossings γ p u).Finite := by
  classical
  set g : ℝ → ℝ := fun t => cross2 u (γ (t : UnitAddCircle) - p) with hgdef
  have hFdiff : Differentiable ℝ (fun t : ℝ => γ (t : UnitAddCircle)) :=
    hsmooth.differentiable (by norm_num)
  have hgcont : Continuous g := by
    rw [hgdef]; simp only [cross2]; fun_prop
  have hgper : ∀ t : ℝ, g (t + 1) = g t := by
    intro t
    rw [hgdef]
    simp only
    rw [AddCircle.coe_add_period (1 : ℝ) t]
  have hderiv : ∀ t : ℝ, HasDerivAt g (cross2 u (cderiv γ t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => γ (s : UnitAddCircle) - p) (cderiv γ t) t :=
      (hFdiff.differentiableAt (x := t)).hasDerivAt.sub_const p
    exact hasDerivAt_cross2_comp' h1
  have hgz : ∀ t : ℝ, g t = 0 ↔ ∃ s : ℝ, γ (t : UnitAddCircle) - p = s • u := by
    intro t
    rw [hgdef]
    exact cross2_eq_zero_iff_of_ne hu
  have hcross : crossings γ p u = {t : ℝ | g t = 0 ∧ t ∈ Set.Ico 0 1} := by
    ext t
    exact ⟨fun ⟨ht, s, hs⟩ => ⟨(hgz t).mpr ⟨s, hs⟩, ht⟩,
      fun ⟨h0, ht⟩ => ⟨ht, (hgz t).mp h0⟩⟩
  set K : Set ℝ := {t : ℝ | g t = 0 ∧ t ∈ Set.Icc 0 1} with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact (isClosed_eq hgcont continuous_const).inter isClosed_Icc
  have hKcompact : IsCompact K :=
    IsCompact.of_isClosed_subset isCompact_Icc hKclosed fun _ ht => ht.2
  have hisol : ∀ t ∈ K, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧ U ∩ K ⊆ {t} := by
    intro t ht
    have hgt : g t = 0 := ht.1
    rcases eq_or_lt_of_le (Set.mem_Icc.mp ht.2).2 with h1 | hlt
    · -- the possible endpoint `t = 1`
      subst h1
      have hg0 : g 0 = 0 := by
        have h := hgper 0
        rw [zero_add] at h
        rw [← h]
        exact hgt
      have h0cross : (0 : ℝ) ∈ crossings γ p u := by
        rw [hcross]
        exact ⟨hg0, le_refl 0, by norm_num⟩
      have hne0 : cross2 u (cderiv γ 0) ≠ 0 := htrans 0 h0cross
      have hne1 : cross2 u (cderiv γ 1) ≠ 0 := by
        have h := cderiv_add_one' γ 0
        rw [zero_add] at h
        rw [h]
        exact hne0
      obtain ⟨δ, hδpos, hδ⟩ := exists_ne_of_hasDerivAt_ne (hderiv 1) hne1
      refine ⟨Metric.ball (1 : ℝ) δ, Metric.isOpen_ball, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_self]; exact hδpos
      · rintro s ⟨hsU, hsK⟩
        have hdist : |s - 1| < δ := by
          rw [Metric.mem_ball, Real.dist_eq] at hsU
          exact hsU
        simp only [Set.mem_singleton_iff]
        by_contra hne
        exact hne (hδ s hdist (by rw [hsK.1, hgt]))
    · -- an interior point `t < 1`
      obtain ⟨ht0, ht1⟩ := Set.mem_Icc.mp ht.2
      have hcross_t : t ∈ crossings γ p u := by
        rw [hcross]
        exact ⟨hgt, ht0, hlt⟩
      have hne : cross2 u (cderiv γ t) ≠ 0 := htrans t hcross_t
      obtain ⟨δ, hδpos, hδ⟩ := exists_ne_of_hasDerivAt_ne (hderiv t) hne
      refine ⟨Metric.ball t δ, Metric.isOpen_ball, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_self]; exact hδpos
      · rintro s ⟨hsU, hsK⟩
        have hdist : |s - t| < δ := by
          rw [Metric.mem_ball, Real.dist_eq] at hsU
          exact hsU
        simp only [Set.mem_singleton_iff]
        by_contra hne'
        exact hne' (hδ s hdist (by rw [hsK.1, hgt]))
  have hKfin : K.Finite := finite_of_isCompact_of_isolated hKcompact hisol
  rw [hcross]
  exact hKfin.subset fun t ht => ⟨ht.1, Set.Ico_subset_Icc_self ht.2⟩

/-! ## The winding number of a closed curve about a point off it is even

`Submission.Collision.dirC v = arg v / π` is the *doubled* direction, so the direction map of the
curve has a continuous square root: the half direction `t ↦ arg (γ t - p) / (2π)`, realised as the
image of the angle of `γ t - p` under the rescaling homeomorphism `ℝ/2πℤ → ℝ/ℤ`.  The degree of a
square is twice the degree, by additivity of the degree. -/

theorem twoPiNeZero : (2 * Real.pi : ℝ) ≠ 0 := by positivity

/-- The rescaling homeomorphism `ℝ/2πℤ → ℝ/ℤ`, `x ↦ x / 2π`. -/
noncomputable def rescaleAngle : Real.Angle ≃ₜ UnitAddCircle :=
  AddCircle.homeomorphAddCircle (2 * Real.pi) 1 twoPiNeZero one_ne_zero

lemma rescaleAngle_apply_mk (x : ℝ) :
    rescaleAngle ((x : ℝ) : Real.Angle) = ((x / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
  change (AddCircle.homeomorphAddCircle (2 * Real.pi) 1 twoPiNeZero one_ne_zero)
      ((x : ℝ) : AddCircle (2 * Real.pi)) = ((x / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  congr 1
  rw [mul_one, div_eq_mul_inv]

/-- The half direction `t ↦ arg (γ t - p) / (2π)` of the curve as seen from `p`. -/
noncomputable def halfDir (γ : UnitAddCircle → ℝ × ℝ) (p : ℝ × ℝ) : UnitAddCircle → UnitAddCircle :=
  fun t => rescaleAngle (((Complex.arg (toC (γ t - p)) : ℝ) : Real.Angle))

lemma halfDir_apply (γ : UnitAddCircle → ℝ × ℝ) (p : ℝ × ℝ) (t : UnitAddCircle) :
    halfDir γ p t =
      ((Complex.arg (toC (γ t - p)) / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
  change rescaleAngle (((Complex.arg (toC (γ t - p)) : ℝ) : Real.Angle)) = _
  change (AddCircle.homeomorphAddCircle (2 * Real.pi) 1 twoPiNeZero one_ne_zero)
      ((Complex.arg (toC (γ t - p)) : ℝ) : AddCircle (2 * Real.pi)) = _
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  congr 1
  rw [mul_one, div_eq_mul_inv]

lemma continuous_halfDir (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) : Continuous (halfDir γ p) := by
  have hinner : Continuous fun t : UnitAddCircle =>
      (((Complex.arg (toC (γ t - p)) : ℝ)) : Real.Angle) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hne : toC (γ t - p) ≠ 0 :=
      fun h => hp ⟨t, sub_eq_zero.mp (toC_eq_zero_iff.mp h)⟩
    have h2 : ContinuousAt (fun s : UnitAddCircle => toC (γ s - p)) t :=
      continuous_toC.continuousAt.comp (hγ.continuousAt.sub continuousAt_const)
    exact (Complex.continuousAt_arg_coe_angle hne).comp
      (f := fun s : UnitAddCircle => toC (γ s - p)) (x := t) h2
  exact rescaleAngle.continuous.comp hinner

lemma halfDir_add_self (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) (t : UnitAddCircle) :
    halfDir γ p t + halfDir γ p t = dirCurve γ hγ p hp t := by
  have h1 : halfDir γ p t =
      ((Complex.arg (toC (γ t - p)) / (2 * Real.pi) : ℝ) : UnitAddCircle) := halfDir_apply γ p t
  have h2 : dirCurve γ hγ p hp t =
      ((Complex.arg (toC (γ t - p)) / Real.pi : ℝ) : UnitAddCircle) := by
    change Submission.Collision.dirC (γ t - p) = _
    rw [dirC_eq_dirCz']
    rfl
  rw [h1, h2, ← AddCircle.coe_add]
  congr 1
  field_simp
  ring

/-- **The winding number of any closed plane curve about a point off it is even.** -/
theorem even_winding_curve (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ) {p : ℝ × ℝ}
    (hp : p ∉ Set.range γ) : Even (winding γ hγ hp) := by
  have hHc : Continuous (halfDir γ p) := continuous_halfDir γ hγ hp
  have hGcont : Continuous fun t : ℝ => 2 * liftOf (halfDir γ p) hHc t :=
    continuous_const.mul (liftOf_continuous (halfDir γ p) hHc)
  have hlift : ∀ t : ℝ, ((2 * liftOf (halfDir γ p) hHc t : ℝ) : UnitAddCircle)
      = dirCurve γ hγ p hp (t : UnitAddCircle) := by
    intro t
    have h1 : (2 * liftOf (halfDir γ p) hHc t : ℝ) =
        liftOf (halfDir γ p) hHc t + liftOf (halfDir γ p) hHc t := by ring
    rw [h1, AddCircle.coe_add, liftOf_lifts]
    exact halfDir_add_self γ hγ hp (t : UnitAddCircle)
  have hmono : ∀ t : ℝ, (fun t : ℝ => 2 * liftOf (halfDir γ p) hHc t) (t + 1)
      = (fun t : ℝ => 2 * liftOf (halfDir γ p) hHc t) t
        + ((2 * degree (halfDir γ p) hHc : ℤ) : ℝ) := by
    intro t
    show 2 * liftOf (halfDir γ p) hHc (t + 1) = 2 * liftOf (halfDir γ p) hHc t
      + ((2 * degree (halfDir γ p) hHc : ℤ) : ℝ)
    rw [liftOf_add_one (halfDir γ p) hHc t]
    push_cast
    ring
  have hkey : winding γ hγ hp = 2 * degree (halfDir γ p) hHc := by
    rw [winding]
    exact (degree_eq_of_lift (continuous_dirCurve γ hγ p hp) hGcont hlift hmono).symm
  rw [hkey]
  exact ⟨degree (halfDir γ p) hHc, by ring⟩

end

end Work.Drive.NH
