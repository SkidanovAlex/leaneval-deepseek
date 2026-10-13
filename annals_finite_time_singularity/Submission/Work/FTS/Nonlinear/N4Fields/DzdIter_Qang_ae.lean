/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `D_z`-iterates of the angular moment `Qang g 0`

The angular moments `Qang g j z = ∫_θ K(θ)·(D_z^j g)(z,θ) dθ` satisfy

  `(z ∂_z)^i (Qang g 0) z = Qang g i z`  for almost every `z > 0`,  `i ≤ 4`,

in the interior class `SmoothQuad g + HkMem α 4 g` (no analyticity hypothesis).

This is the identity that turns the `z`-profile `FK g = Qang g 0 = -D_z L₁₂(g)` into an honest
`ℋ⁴`-function: it identifies all the pure `D_z`-slots of `HkIntegrand α 4 (fun z _ => Qang g 0 z)`
with the angular moments `Qang g i`, `i ≤ 4` (needed for the field `N4Norm.fkH`, row 20 of the
§8 table).

Proof.  `Work.FTS.H2.Qang_primitive` exhibits `Qang g j` as the primitive of
`x ↦ Qang g (j+1) x / x` on `(0,∞)` for `j ≤ 3`, whence

* `DzdIter i (Qang g 0) = Qang g i` **pointwise on `(0,∞)`** for every `i ≤ 3`, by induction:
  the `(i+1)`-st iterate is `z ↦ z·∂_z(DzdIter i (Qang g 0))`, and `DzdIter i (Qang g 0)`
  agrees with `Qang g i` on a neighbourhood of every `z > 0`, so the derivatives agree and
  `Work.FTS.H2.hasDerivAt_Qang` identifies them (`j ≤ 2` needs the continuity of `Qang g (j+1)`,
  `j + 1 ≤ 3`, which is `Work.FTS.H2.continuousOn_Qang`);
* the fourth iterate needs `∂_z (Qang g 3) z = Qang g 4 z / z`, i.e. the derivative of a
  primitive of `x ↦ Qang g 4 x / x`, and *this* is only a Lebesgue-almost-everywhere statement
  (continuity of `Qang g 4` is not available: it would require the `D_z^5`-slot, i.e.
  `HkMem α 5 g`).  It is supplied by the Lebesgue differentiation theorem, applied on the
  countable cover `(0,∞) = ⋃_n uIcc (1/(n+2)) (n+2)` on each piece of which the integrand is
  integrable (`Work.FTS.H2.QangBoxIntegrable`, `j = 3`).

The almost-everywhere qualifier in the statement is therefore *sharp* for this route, and it is
exactly what the consumers need (all `fkH`-slot estimates are integrated in `z` against the
weight `w²`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.H2.QangDiff
import Submission.Work.FTS.H2.QangBox

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology MeasureTheory
open MeasureTheory Filter Function

namespace Work.FTS.Nonlinear.N4Fields

set_option autoImplicit false

/-! ## The iterated `z ∂_z`-identity from a primitive relation -/

/-- If `u = Φ 0` and `Φ j` has derivative `Φ (j+1) z / z` at every `z > 0` (for `j ≤ 2`), then
`DzdIter i u = Φ i` on `(0,∞)` for every `i ≤ 3`.

This is the pointwise half of the main theorem, stated for an abstract pair `(u, Φ)` so that
the induction is independent of `Qang`.  The hypothesis `j ≤ 2` is what makes
`z * ∂_z(Φ j) z = Φ (j+1) z` hold: `DzdIter i u` agrees with `Φ i` on the open half-line, so
their derivatives at `z > 0` agree, and the divided derivative `Φ (j+1) z / z` is undone by the
multiplication by `z`. -/
private theorem DzdIter_eq_of_hasDerivAt {u : ℝ → ℝ} {Φ : ℕ → ℝ → ℝ}
    (h0 : ∀ z, u z = Φ 0 z)
    (hder : ∀ j ≤ 2, ∀ z, 0 < z → HasDerivAt (Φ j) (Φ (j + 1) z / z) z) :
    ∀ i ≤ 3, ∀ z, 0 < z → Work.Elliptic.DzdIter i u z = Φ i z := by
  intro i
  induction i with
  | zero => intro _ z _; exact h0 z
  | succ i ih =>
    intro _ z hz
    have hprev : Work.Elliptic.DzdIter i u =ᶠ[𝓝 z] Φ i := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact ih (by omega) w hw
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd]
    rw [hprev.deriv_eq, (hder i (by omega) z hz).deriv]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hz)]

/-! ## The main identity -/

theorem DzdIter_Qang_ae {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ᵐ z ∂(MeasureTheory.volume), 0 < z → ∀ i ∈ Finset.range 5,
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z := by
  -- the divided derivative of `Qang g j` for `j ≤ 2` (continuity of `Qang g (j+1)`, `j+1 ≤ 3`)
  have hder2 : ∀ j ≤ 2, ∀ z : ℝ, 0 < z →
      HasDerivAt (fun z => Work.Elliptic.Qang g j z) (Work.Elliptic.Qang g (j + 1) z / z) z := by
    intro j hj z hz
    exact Work.FTS.H2.hasDerivAt_Qang α g hsm hmem hj hz
      (Work.FTS.H2.continuousOn_Qang α g hsm hmem (by omega))
  -- the pointwise identity for `i ≤ 3`
  have hpoint : ∀ i ≤ 3, ∀ z, 0 < z →
      Work.Elliptic.DzdIter i (fun z => Work.Elliptic.Qang g 0 z) z = Work.Elliptic.Qang g i z :=
    DzdIter_eq_of_hasDerivAt (fun z => rfl) hder2
  -- the integrand `x ↦ Qang g 4 x / x` is interval integrable on every compact subinterval of
  -- `(0,∞)`: this is the `j = 3` instance of the Fubini/box integrability
  have hφint : ∀ n : ℕ, IntervalIntegrable (fun x => Work.Elliptic.Qang g 4 x / x) volume
      (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have ha : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact intervalIntegrable_iff.mpr
      (Work.FTS.H2.QangBoxIntegrable hsm hmem (j := 3) le_rfl ha hab).2
  -- the Lebesgue differentiation theorem on each piece of the countable cover
  have hldt : ∀ᵐ z ∂volume, ∀ n : ℕ, (z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) →
      ∀ c ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
        HasDerivAt (fun y => ∫ t in c..y, Work.Elliptic.Qang g 4 t / t)
          (Work.Elliptic.Qang g 4 z / z) z) :=
    MeasureTheory.ae_all_iff.mpr fun n => (hφint n).ae_hasDerivAt_integral
  -- every `z > 0` lies in one of the pieces of the cover
  have hcover : ∀ z : ℝ, 0 < z → ∃ n : ℕ, z ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / z) z)
    refine ⟨n, ?_⟩
    have hnz : z < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
    have hn1 : 1 / z < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    have hzn : 1 < z * (n : ℝ) := by
      rw [div_lt_iff₀ hz] at hn1
      linarith
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith, by linarith⟩
  -- `1` lies in every piece of the cover, so the primitive can be taken from `1`
  have h1mem : ∀ n : ℕ, (1 : ℝ) ∈ Set.uIcc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    intro n
    have hab : 1 / ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [Set.uIcc_of_le hab, Set.mem_Icc]
    exact ⟨by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
      by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  -- a.e. differentiability of the primitive `y ↦ ∫_1^y Qang g 4 t / t`
  have hprim : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => ∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
        (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hldt] with z hz hzpos
    obtain ⟨n, hn⟩ := hcover z hzpos
    exact hz n hn 1 (h1mem n)
  -- hence `Qang g 3` is differentiable a.e. with the divided derivative `Qang g 4 z / z`
  have hderiv3 : ∀ᵐ z ∂volume, 0 < z →
      HasDerivAt (fun y => Work.Elliptic.Qang g 3 y) (Work.Elliptic.Qang g 4 z / z) z := by
    filter_upwards [hprim] with z hz hzpos
    have hev : (fun y => Work.Elliptic.Qang g 3 y) =ᶠ[𝓝 z]
        (fun y => (∫ t in (1 : ℝ)..y, Work.Elliptic.Qang g 4 t / t)
          + Work.Elliptic.Qang g 3 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with y hy
      have h := Work.FTS.H2.Qang_primitive α g hsm hmem (j := 3) (by norm_num) hy
        (by norm_num : (0 : ℝ) < 1)
      linarith
    exact ((hz hzpos).add_const _).congr_of_eventuallyEq hev
  -- the fourth iterate
  have h4 : ∀ᵐ z ∂volume, 0 < z →
      Work.Elliptic.DzdIter 4 (fun z => Work.Elliptic.Qang g 0 z) z
        = Work.Elliptic.Qang g 4 z := by
    filter_upwards [hderiv3] with z hz3 hzpos
    have h3eq : Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z) =ᶠ[𝓝 z]
        (fun w => Work.Elliptic.Qang g 3 w) := by
      filter_upwards [isOpen_Ioi.mem_nhds hzpos] with w hw
      exact hpoint 3 le_rfl w hw
    have hd : deriv (Work.Elliptic.DzdIter 3 (fun z => Work.Elliptic.Qang g 0 z)) z
        = Work.Elliptic.Qang g 4 z / z := by
      rw [h3eq.deriv_eq, (hz3 hzpos).deriv]
    rw [Work.Elliptic.DzdIter_succ, Work.Elliptic.Dzd, hd]
    rw [mul_comm z, div_mul_cancel₀ _ (ne_of_gt hzpos)]
  filter_upwards [h4] with z hz4 hz i hi
  have hi4 : i ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rcases Nat.lt_or_ge i 4 with hlt | hge
  · exact hpoint i (by omega) z hz
  · have hieq : i = 4 := by omega
    subst hieq
    exact hz4 hz

end Work.FTS.Nonlinear.N4Fields
