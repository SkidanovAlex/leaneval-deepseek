/-
# Basic properties of the `1`-periodisation `perR`

`Work.Diff.STE.B3.perR f z = ∑' m : Fin n → ℤ, f (z + m)` is the `1`-periodisation of a function on
`Fin n → ℝ` (the real analogue of `D.Rper` of `B3/Comp.lean`).  For a smooth `f` whose support is
contained in the ball of radius `R ≤ 1 / 2` around `0` this file proves the three properties that the
transport needs:

* `perR f` is smooth;
* `perR f` is `1`-periodic in every coordinate (`Periodic1`);
* `perR f` agrees with `f` on the closed ball `‖z‖ ≤ R`.

The proof is the standard local-finiteness argument.  Since the support of `f` is contained in the
ball of radius `R ≤ 1 / 2`, and the unit lattice vectors `m ≠ 0` satisfy `‖m‖ ≥ 1`, the translates
`z ↦ f (z + m)` have pairwise disjoint supports.  Consequently, near a point `x` only the
multi-indices `m` with `|m i| < ⌊|x i|⌋ + 2` (for every coordinate `i`) can contribute, a *finite*
set `S`; on the open box `∏ᵢ (xᵢ - 1/2, xᵢ + 1/2)` the periodisation therefore coincides with the
finite sum `∑ m ∈ S, f (· + m)`, which is smooth.  (The same argument, over `ℂ` and with the support
in the open unit cube, is `Work.Diff.STE.periodization_contDiff_periodic` of
`STE/periodization_contDiff_periodic.lean`; here we need the real-valued version with the ball
hypothesis used by `Work.Diff.STE.B3.Afun`.)

The identification on the closed ball `‖z‖ ≤ R` is *not* a triviality at the boundary `‖z‖ = R`: for
`m ≠ 0` one has `‖z + m‖ ≥ ‖m‖ - ‖z‖ ≥ 1 - R ≥ R`, so `z + m` never lies in the *open* ball of
radius `R`, hence `f (z + m) = 0`; the sum thus reduces to its `m = 0` term.

This module is the input of `Work.Diff.STE.B3.perR_jet_bound`, which requires exactly these facts to
differentiate the periodised coefficient matrix `Work.Diff.STE.B3.Afun`.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.CoeffDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Function

open scoped BigOperators Topology

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The integer vector `m : Fin n → ℤ` regarded as a real vector. -/
def intVec {n : ℕ} (m : Fin n → ℤ) : Fin n → ℝ := fun i => (m i : ℝ)

@[simp] lemma intVec_apply {n : ℕ} (m : Fin n → ℤ) (i : Fin n) : intVec m i = (m i : ℝ) := rfl

@[simp] lemma intVec_zero {n : ℕ} : intVec (0 : Fin n → ℤ) = (0 : Fin n → ℝ) := by
  funext i
  simp [intVec]

/-- Unfolding of the periodisation `perR` in terms of the lattice vector `intVec`. -/
lemma perR_apply {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) :
    perR f z = ∑' m : Fin n → ℤ, f (z + intVec m) := rfl

/-- **Local finiteness of the periodisation.**  If `f` is supported in the ball of radius `R ≤ 1 / 2`
around the origin, and `y` is within `1 / 2` of `x` in every coordinate, then every multi-index `m`
contributing to `perR f y` satisfies `|m i| < ⌊|x i|⌋ + 2` for every `i`. -/
lemma abs_lt_floor_add_two_of_support_ball {n : ℕ} {f : (Fin n → ℝ) → ℝ} {R : ℝ}
    (hR : R ≤ 1 / 2) (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) R)
    {x y : Fin n → ℝ} (hy : ∀ i, |y i - x i| < 1 / 2) {m : Fin n → ℤ}
    (hm : f (y + intVec m) ≠ 0) (i : Fin n) :
    |m i| < ⌊|x i|⌋ + 2 := by
  have hball : y + intVec m ∈ Metric.ball (0 : Fin n → ℝ) R := hsupp hm
  rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hball
  -- the `i`-th coordinate of `y + m` is small, because `‖·‖` dominates the coordinates
  have hcoord : |y i + (m i : ℝ)| < 1 / 2 := by
    have h1 : |(y + intVec m) i| ≤ ‖y + intVec m‖ := by
      simpa using norm_le_pi_norm (y + intVec m) i
    have h2 : (y + intVec m) i = y i + (m i : ℝ) := by simp
    rw [h2] at h1
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le hball hR)
  have hyx : |y i| < 1 / 2 + |x i| := by
    calc |y i| = |(y i - x i) + x i| := by rw [sub_add_cancel]
      _ ≤ |y i - x i| + |x i| := abs_add_le _ _
      _ < 1 / 2 + |x i| := by linarith [hy i]
  have hm1 : |(m i : ℝ)| < 1 + |x i| := by
    have h02 : (m i : ℝ) = (y i + (m i : ℝ)) - y i := by ring
    rw [h02]
    calc |(y i + (m i : ℝ)) - y i| = |(y i + (m i : ℝ)) + (-y i)| := by rw [sub_eq_add_neg]
      _ ≤ |y i + (m i : ℝ)| + |-y i| := abs_add_le _ _
      _ = |y i + (m i : ℝ)| + |y i| := by rw [abs_neg]
      _ < 1 + |x i| := by linarith
  have hm2 : (1 : ℝ) + |x i| < ((⌊|x i|⌋ + 2 : ℤ) : ℝ) := by
    have := Int.lt_floor_add_one (|x i|)
    push_cast
    linarith
  have hm3 : ((|m i| : ℤ) : ℝ) < ((⌊|x i|⌋ + 2 : ℤ) : ℝ) := by
    rw [Int.cast_abs]
    exact lt_trans hm1 hm2
  exact_mod_cast hm3

/-- The periodisation of a smooth function supported in the ball of radius `R ≤ 1 / 2` is smooth at
every point: near `x` only finitely many translates can contribute. -/
lemma contDiffAt_perR {n : ℕ} {f : (Fin n → ℝ) → ℝ} {R : ℝ} (hR : R ≤ 1 / 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) R)
    (x : Fin n → ℝ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (perR f) x := by
  classical
  set N : Fin n → ℤ := fun i => ⌊|x i|⌋ + 2 with hNdef
  set S : Finset (Fin n → ℤ) := Fintype.piFinset (fun i => Finset.Icc (-(N i)) (N i)) with hSdef
  have hfin : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => ∑ m ∈ S, f (y + intVec m)) := by
    apply ContDiff.sum
    intro m _
    have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => y + intVec m) := by
      simpa using
        (contDiff_id.add (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Fin n → ℝ => intVec m)))
    exact hf.comp hshift
  have hBopen : IsOpen (Set.pi Set.univ (fun i : Fin n => Set.Ioo (x i - 1 / 2) (x i + 1 / 2))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hxB : x ∈ Set.pi Set.univ (fun i : Fin n => Set.Ioo (x i - 1 / 2) (x i + 1 / 2)) := by
    rw [Set.mem_pi]
    intro i _
    rw [Set.mem_Ioo]
    constructor <;> linarith
  have hEq : (fun y : Fin n → ℝ => ∑ m ∈ S, f (y + intVec m)) =ᶠ[nhds x] (perR f) := by
    refine Filter.eventually_of_mem (hBopen.mem_nhds hxB) ?_
    intro y hy
    show (∑ m ∈ S, f (y + intVec m)) = perR f y
    rw [perR_apply]
    refine (tsum_eq_sum (s := S) ?_).symm
    intro m hm
    by_contra hc
    have hyabs : ∀ i, |y i - x i| < 1 / 2 := by
      intro i
      have := Set.mem_pi.mp hy i (Set.mem_univ i)
      rw [Set.mem_Ioo] at this
      rw [abs_lt]
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hbound : ∀ i, m i ∈ Finset.Icc (-(N i)) (N i) := by
      intro i
      have h1 : |m i| < N i := by
        have := abs_lt_floor_add_two_of_support_ball hR hsupp hyabs hc i
        simpa [hNdef] using this
      rw [Finset.mem_Icc]
      have h2 := abs_lt.mp h1
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    exact hm (by rw [hSdef, Fintype.mem_piFinset]; exact hbound)
  exact hfin.contDiffAt.congr_of_eventuallyEq hEq.symm

/-- The periodisation `z ↦ ∑' m, f (z + m)` is `1`-periodic in every coordinate: this is a
reindexing of the sum by the translation `m ↦ eᵢ + m` on the lattice `Fin n → ℤ`. -/
lemma periodic_perR {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Work.Diff.STE.Periodic1 (perR f) := by
  intro i x
  rw [perR_apply, perR_apply]
  refine Eq.trans (tsum_congr ?_) ((Equiv.addLeft (Pi.single i (1 : ℤ))).tsum_eq
    (fun m : Fin n → ℤ => f (x + intVec m)))
  intro m
  congr 1
  funext j
  by_cases hji : j = i
  · subst hji; simp [Pi.single_eq_same]; ring
  · simp [Pi.single_eq_of_ne hji]

/-- On the closed ball `‖z‖ ≤ R` the periodisation equals `f`: a translate `z + m` with `m ≠ 0`
satisfies `‖z + m‖ ≥ ‖m‖ - ‖z‖ ≥ 1 - R ≥ R`, so it is never in the *open* ball of radius `R` which
carries the support of `f`. -/
lemma perR_eq_self_of_mem_ball {n : ℕ} {f : (Fin n → ℝ) → ℝ} {R : ℝ} (hR : R ≤ 1 / 2)
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) R)
    {z : Fin n → ℝ} (hz : ‖z‖ ≤ R) : perR f z = f z := by
  classical
  rw [perR_apply, tsum_eq_single (0 : Fin n → ℤ) ?_]
  · rw [intVec_zero, add_zero]
  · intro m hm
    by_contra hc
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
    have hzm : z + intVec m ∈ Metric.ball (0 : Fin n → ℝ) R := hsupp hc
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hzm
    have h1 : |z i + (m i : ℝ)| < 1 / 2 := by
      have hle : |(z + intVec m) i| ≤ ‖z + intVec m‖ := by
        simpa using norm_le_pi_norm (z + intVec m) i
      have h4 : (z + intVec m) i = z i + (m i : ℝ) := by simp
      rw [h4] at hle
      exact lt_of_le_of_lt hle (lt_of_lt_of_le hzm hR)
    have h2 : |z i| ≤ 1 / 2 := by
      have hle : |z i| ≤ ‖z‖ := by simpa using norm_le_pi_norm z i
      linarith
    have h3 : |(m i : ℝ)| < 1 := by
      have h5 : (m i : ℝ) = (z i + (m i : ℝ)) - z i := by ring
      rw [h5]
      calc |(z i + (m i : ℝ)) - z i| = |(z i + (m i : ℝ)) + (-z i)| := by rw [sub_eq_add_neg]
        _ ≤ |z i + (m i : ℝ)| + |-z i| := abs_add_le _ _
        _ = |z i + (m i : ℝ)| + |z i| := by rw [abs_neg]
        _ < 1 := by linarith
    have h6 : ((|m i| : ℤ) : ℝ) < 1 := by
      rw [Int.cast_abs]; exact h3
    have h7 : |m i| < (1 : ℤ) := by exact_mod_cast h6
    have h8 : (1 : ℤ) ≤ |m i| := Int.one_le_abs hi
    omega

theorem perR_props {n : ℕ} (R : ℝ) (hR : R ≤ 1 / 2) :
    (∀ (f : (Fin n → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
        Function.support f ⊆ Metric.ball 0 R →
        ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.perR f)) ∧
      (∀ (f : (Fin n → ℝ) → ℝ), Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.perR f)) ∧
      (∀ (f : (Fin n → ℝ) → ℝ), Function.support f ⊆ Metric.ball 0 R →
        ∀ (z : Fin n → ℝ), ‖z‖ ≤ R → Work.Diff.STE.B3.perR f z = f z) :=
  ⟨fun f hf hsupp => contDiff_iff_contDiffAt.mpr (fun x => contDiffAt_perR hR hf hsupp x),
   fun f => periodic_perR f,
   fun f hsupp z hz => perR_eq_self_of_mem_ball hR hsupp hz⟩

end Work.Diff.STE.B3
