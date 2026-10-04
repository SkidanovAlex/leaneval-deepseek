import Mathlib
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.Periodic1_iVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The sup bound of the periodised localised component from the sup bound of the component

The periodisation `D.Rper i h a b z = ∑' m, R i h a b (z + m)` of the localised component
`R i h a b` (which is supported in the open centred unit cube `(-1/2,1/2)^n`) has the same sup
bound as `R i h a b` itself: at most one summand is nonzero, so

  `‖D.Rper i h a b z‖ ≤ sup_w |D.R i h a b w|`.

The precise statement proved below (`Rper_norm_le_of_R_abs_le`) is the one needed downstream, where
the sup of `|R i h a b|` over all of `ℝⁿ` is available as a hypothesis.

The proof is a general lemma about the periodisation of a function supported in the open cube
(`periodization_norm_le_of_norm_le`): for an arbitrary `z` one translates `z` by an integer vector
`m₀` so that `x := z + m₀` lies in `[-1/2,1/2]^n` in every coordinate (`m₀ j := -⌊z j + 1/2⌋`); the
periodisation is invariant under integer translations, and at `x` either `x` is in the *open* cube,
in which case `periodization_eq_self` identifies the periodisation with the function itself, or some
coordinate of `x` equals `-1/2`, in which case *every* summand vanishes (the support of the function
lies in the open cube, and `-1/2 + k ∉ (-1/2,1/2)` for every `k : ℤ`).
-/

noncomputable section

namespace Work.Diff.STE.Lead

/-- **The periodisation of a function supported in the open cube obeys any uniform norm bound.**

Let `f : (ι → ℝ) → ℂ` have its support in the open centred unit cube and be bounded by `L` in norm.
Then its `1`-periodisation `z ↦ ∑' m, f (z + m)` (the sum over the integer lattice `ℤ^ι`) is bounded
by `L` in norm: for each `z` at most one summand is nonzero, and that summand is some value of `f`.

The translation `m₀ := fun j => -⌊z j + 1 / 2⌋` puts `z + m₀` into `[-1/2,1/2)^ι`, and the
periodisation is invariant under it. -/
lemma periodization_norm_le_of_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℂ}
    (hsupp : Function.support f ⊆ Set.pi Set.univ
      (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ y, ‖f y‖ ≤ L) (z : ι → ℝ) :
    ‖∑' m : ι → ℤ, f (z + Work.Diff.STE.iVec m)‖ ≤ L := by
  classical
  -- the integer translation putting `z` into the half-open cube
  set m₀ : ι → ℤ := fun j => -⌊z j + 1 / 2⌋ with hm₀
  have hlo : ∀ j, -(1 / 2 : ℝ) ≤ z j + Work.Diff.STE.iVec m₀ j := by
    intro j
    have h1 : ((⌊z j + 1 / 2⌋ : ℤ) : ℝ) ≤ z j + 1 / 2 := Int.floor_le _
    simp only [Work.Diff.STE.iVec_apply, hm₀, Int.cast_neg]
    linarith
  have hhi : ∀ j, z j + Work.Diff.STE.iVec m₀ j < 1 / 2 := by
    intro j
    have h1 : z j + 1 / 2 < ((⌊z j + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    simp only [Work.Diff.STE.iVec_apply, hm₀, Int.cast_neg]
    linarith
  -- the periodisation is invariant under the integer translation by `m₀`
  have hper : Work.Diff.STE.Periodic1
      (fun y : ι → ℝ => ∑' m : ι → ℤ, f (y + Work.Diff.STE.iVec m)) :=
    Work.Diff.STE.periodization_periodic f
  have hinv := Work.Diff.STE.B3.Periodic1_iVec hper m₀ z
  rw [← hinv]
  by_cases hcase : ∀ j, (z + Work.Diff.STE.iVec m₀) j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  · -- the open-cube case: the periodisation is the function itself
    rw [Work.Diff.STE.periodization_eq_self hsupp hcase]
    exact hf _
  · -- the boundary case: some coordinate is `-1/2`, so every summand vanishes
    obtain ⟨j, hj⟩ := not_forall.mp hcase
    have hxj : (z + Work.Diff.STE.iVec m₀) j = -(1 / 2 : ℝ) := by
      by_contra hne
      exact hj (Set.mem_Ioo.mpr ⟨lt_of_le_of_ne (hlo j) (Ne.symm hne), hhi j⟩)
    have hzero : ∀ m : ι → ℤ, f ((z + Work.Diff.STE.iVec m₀) + Work.Diff.STE.iVec m) = 0 := by
      intro m
      by_contra hc
      have hmem := hsupp hc
      have hcoord : (z + Work.Diff.STE.iVec m₀) j + Work.Diff.STE.iVec m j ∈
          Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := Set.mem_pi.mp hmem j (Set.mem_univ j)
      rw [Set.mem_Ioo] at hcoord
      have h1 : (m j : ℝ) > 0 := by
        have := hcoord.1
        rw [hxj, Work.Diff.STE.iVec_apply] at this
        linarith
      have h2 : (m j : ℝ) < 1 := by
        have := hcoord.2
        rw [hxj, Work.Diff.STE.iVec_apply] at this
        linarith
      have h1' : (0 : ℤ) < m j := by exact_mod_cast h1
      have h2' : m j < 1 := by exact_mod_cast h2
      omega
    have hsum0 : (∑' m : ι → ℤ,
        f ((z + Work.Diff.STE.iVec m₀) + Work.Diff.STE.iVec m)) = 0 := by
      rw [show (∑' m : ι → ℤ, f ((z + Work.Diff.STE.iVec m₀) + Work.Diff.STE.iVec m))
          = ∑' m : ι → ℤ, (0 : ℂ) from tsum_congr (fun m => hzero m), tsum_zero]
    rw [hsum0, norm_zero]
    exact hL

theorem Rper_norm_le_of_R_abs_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {L : ℝ} (hL : 0 ≤ L)
    (hR : ∀ w : Fin (Module.finrank ℝ E) → ℝ, |D.R i h a b w| ≤ L) :
    ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖D.Rper i h a b z‖ ≤ L := by
  intro z
  have hsupp : Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h a b y : ℝ) : ℂ)) ⊆
      Set.pi Set.univ (fun _ : Fin (Module.finrank ℝ E) =>
        Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    exact D.R_support i h a b (by
      simpa only [Function.mem_support, Complex.ofReal_ne_zero] using hy)
  have hf : ∀ y : Fin (Module.finrank ℝ E) → ℝ,
      ‖((D.R i h a b y : ℝ) : ℂ)‖ ≤ L := by
    intro y
    rw [show ‖((D.R i h a b y : ℝ) : ℂ)‖ = |D.R i h a b y| from by simp]
    exact hR y
  show ‖(∑' m : Fin (Module.finrank ℝ E) → ℤ,
      ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ))‖ ≤ L
  exact periodization_norm_le_of_norm_le hsupp hL hf z

end Work.Diff.STE.Lead
