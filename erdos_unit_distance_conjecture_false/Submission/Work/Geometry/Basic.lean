import Mathlib
import Submission.Work.Defs.Basic

/-!
# Geometric core of the unit-distance construction: basic setup

Vocabulary for Section 2 of *Planar Point Sets with Many Unit Distances*.

* `Work.Geometry.Window K R` is the sup-norm polydisc `B_R` in the Minkowski (mixed) space
  of a number field `K`.
* `Work.Geometry.Lattice K I` is the `ℤ`-lattice attached to a fractional ideal `I`.

For a CM field `K` the mixed space is a product of copies of `ℂ` (one for each complex
place) and `Window K R` is a product of discs of radius `R`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Geometry

variable (K : Type*) [Field K] [NumberField K]

/-- The window `B_R`: the open polydisc of radius `R` in the mixed space, defined by the
sup-norm (i.e. placewise) condition. -/
def Window (R : ℝ) : Set (mixedEmbedding.mixedSpace K) :=
  {x | ∀ w : InfinitePlace K, mixedEmbedding.normAtPlace w x < R}

/-- The `ℤ`-lattice of the mixed space attached to a fractional ideal `I`. -/
def Lattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (mixedEmbedding.mixedSpace K) :=
  Submodule.span ℤ (Set.range (mixedEmbedding.fractionalIdealLatticeBasis K I))

/-- The fundamental domain of the lattice `Lattice K I`. -/
def Fund (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Set (mixedEmbedding.mixedSpace K) :=
  ZSpan.fundamentalDomain (mixedEmbedding.fractionalIdealLatticeBasis K I)

variable {K}

theorem mem_window {R : ℝ} {x : mixedEmbedding.mixedSpace K} :
    x ∈ Window K R ↔ ∀ w : InfinitePlace K, mixedEmbedding.normAtPlace w x < R := Iff.rfl

theorem Window_mono {R R' : ℝ} (h : R ≤ R') : Window K R ⊆ Window K R' :=
  fun _ hx w => lt_of_lt_of_le (hx w) h

theorem Window_neg (R : ℝ) : -Window K R = Window K R := by
  ext x
  rw [Set.mem_neg, mem_window, mem_window]
  constructor
  · intro h w; rw [← mixedEmbedding.normAtPlace_neg]; exact h w
  · intro h w; rw [mixedEmbedding.normAtPlace_neg]; exact h w

/-- The window is the metric ball of the same radius (in the sup norm). -/
theorem Window_eq_ball (R : ℝ) :
    Window K R = Metric.ball (0 : mixedEmbedding.mixedSpace K) R := by
  ext x
  rw [mem_window, Metric.mem_ball, dist_zero_right,
    mixedEmbedding.norm_eq_sup'_normAtPlace, Finset.sup'_lt_iff]
  simp

theorem isOpen_window (R : ℝ) : IsOpen (Window K R) := by
  rw [Window_eq_ball R]
  exact Metric.isOpen_ball

theorem measurableSet_window (R : ℝ) : MeasurableSet (Window K R) :=
  (isOpen_window R).measurableSet

/-- The window is the polydisc `convexBodyLT` of Mathlib. -/
theorem convexBodyLT_eq_window (f : InfinitePlace K → NNReal) {R : ℝ}
    (hf : ∀ w, (f w : ℝ) = R) :
    mixedEmbedding.convexBodyLT K f = Window K R := by
  ext x
  rw [mem_window, mixedEmbedding.convexBodyLT, Set.mem_prod]
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨h1, h2⟩ w
    rcases w.isReal_or_isComplex with hw | hw
    · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, ← hf w]
      exact h1 ⟨w, hw⟩
    · rw [mixedEmbedding.normAtPlace_apply_of_isComplex hw, ← hf w]
      exact h2 ⟨w, hw⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro w
      rw [← mixedEmbedding.normAtPlace_apply_of_isReal w.2, hf w.1]
      exact h w.1
    · intro w
      rw [← mixedEmbedding.normAtPlace_apply_of_isComplex w.2, hf w.1]
      exact h w.1

section LatticeApi

variable (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

theorem mem_lattice {x : mixedEmbedding.mixedSpace K} :
    x ∈ Lattice K I ↔ ∃ a ∈ (I : Set K), mixedEmbedding K a = x := by
  rw [Lattice, mixedEmbedding.mem_span_fractionalIdealLatticeBasis]
  exact Iff.rfl

theorem lattice_eq_idealLattice :
    Lattice K I = mixedEmbedding.idealLattice K I := by
  rw [Lattice, mixedEmbedding.span_idealLatticeBasis]

instance instLatticeDiscrete : DiscreteTopology (Lattice K I) := by
  unfold Lattice; infer_instance

instance instLatticeIsZLattice : IsZLattice ℝ (Lattice K I) := by
  unfold Lattice; infer_instance

instance instLatticeCountable : Countable (Lattice K I) := by
  unfold Lattice; infer_instance

theorem isAddFundamentalDomain_fund :
    IsAddFundamentalDomain (Lattice K I).toAddSubgroup (Fund K I) volume := by
  have h := mixedEmbedding.fundamentalDomain_idealLattice K I
  rw [Fund, lattice_eq_idealLattice]
  exact h

end LatticeApi

section NormOne

variable [IsCMField K]

/-- An element `u` with `u * conj u = 1` (a "norm one" element) has `w u = 1` at every
infinite place. -/
theorem infinitePlace_eq_one_of_mul_complexConj (u : K)
    (hu : u * IsCMField.complexConj K u = 1) (w : InfinitePlace K) : w u = 1 := by
  have h1 : w u * w u = 1 := by
    have h := congrArg w hu
    rw [map_mul, map_one, IsCMField.infinitePlace_complexConj] at h
    exact h
  have h2 : 0 ≤ w u := by rw [InfinitePlace.coe_apply]; exact w.1.nonneg u
  have h3 : (w u - 1) * (w u + 1) = 0 := by nlinarith [h1]
  rcases mul_eq_zero.mp h3 with h | h
  · linarith
  · linarith

theorem normAtPlace_eq_one_of_mul_complexConj (u : K)
    (hu : u * IsCMField.complexConj K u = 1) (w : InfinitePlace K) :
    mixedEmbedding.normAtPlace w (mixedEmbedding K u) = 1 := by
  rw [mixedEmbedding.normAtPlace_apply]
  exact infinitePlace_eq_one_of_mul_complexConj u hu w

theorem norm_embedding_eq_one_of_mul_complexConj (u : K)
    (hu : u * IsCMField.complexConj K u = 1) (w : InfinitePlace K) :
    ‖w.embedding u‖ = 1 := by
  rw [InfinitePlace.norm_embedding_eq]
  exact infinitePlace_eq_one_of_mul_complexConj u hu w

end NormOne

end Geometry
end Work
