import Mathlib
import Submission.Work.Diff.STE.B3.pdR_bound_of_support
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.B3.iteratedFDeriv_fderiv_le_of_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A global jet bound from a compact support condition

If `f : (Fin n → ℝ) → ℝ` is `C^∞` and its *topological* support is contained in the closed ball of
radius `Rb` around the origin, then all its iterated derivatives of order `≤ N`, and all its
iterated partial derivatives `pdRVec` of order `≤ N`, are bounded on the whole of `Fin n → ℝ` by a
single nonnegative constant.

The proof has three ingredients:

* on the compact ball `closedBall 0 Rb` the bound is a compactness statement
  (`Work.Diff.STE.flat.compact_iteratedFDeriv_bound`, which rests on the continuity of
  `z ↦ ‖iteratedFDeriv ℝ j f z‖`);
* outside `tsupport f` the function vanishes on a whole neighbourhood, hence so does every iterated
  derivative at such a point (`Filter.EventuallyEq.iteratedFDerivWithin_eq` for the zero function);
* the partial derivatives are the iterated derivatives evaluated on the coordinate basis vectors,
  which have norm one, so the same constant bounds them
  (`pdRVec r γ f z = D^r f z (e_{γ 0}, …, e_{γ (r-1)})`).
-/

namespace Work.Diff.STE.B3

open scoped Topology

/-- **`pdRVec` is the iterated derivative on the coordinate directions.**  For a smooth
`f : (Fin n → ℝ) → ℝ`, the iterated partial derivative of order `r` along `γ` is the value of the
`r`-th iterated derivative of `f` at `z` on the tuple of coordinate vectors `Pi.single (γ j) 1`. -/
lemma pdRVec_eq_iteratedFDeriv_eval {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (r : ℕ) (γ : Fin r → Fin n) (z : Fin n → ℝ) :
    Work.Diff.STE.pdRVec r γ f z
      = iteratedFDeriv ℝ r f z (fun j => Pi.single (γ j) (1 : ℝ)) := by
  have hK : ContDiffOn ℝ (((r + 1 : ℕ)) : WithTop ℕ∞) f Set.univ :=
    hf.contDiffOn.of_le (by exact_mod_cast (le_top : ((r + 1 : ℕ) : ℕ∞) ≤ ⊤))
  have hA : pdVecX r γ f z = iteratedFDeriv ℝ r f z (fun j => Pi.single (γ j) (1 : ℝ)) := by
    rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) r isOpen_univ (Set.mem_univ z)]
    exact (pdVecX_eq_iteratedFDerivWithin (v := Set.univ) isOpen_univ hK r γ le_rfl)
      (Set.mem_univ z)
  rw [← hA, pdVecX_eq_pdRVec]

/-- If `f` vanishes on a neighbourhood of `z`, then its `m`-th iterated derivative at `z` vanishes
as well.  (The hypothesis is stated with the topological support: `z ∉ tsupport f` is exactly
`f =ᶠ[𝓝 z] 0`, see `notMem_tsupport_iff_eventuallyEq`.) -/
lemma iteratedFDeriv_eq_zero_of_eventuallyEq_zero {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    {z : Fin n → ℝ} (h : f =ᶠ[𝓝 z] (fun _ => (0 : ℝ))) :
    iteratedFDeriv ℝ m f z = 0 := by
  have hx : f z = 0 := Filter.EventuallyEq.eq_of_nhds h
  have h1 : iteratedFDerivWithin ℝ m f Set.univ z
      = iteratedFDerivWithin ℝ m (fun _ : Fin n → ℝ => (0 : ℝ)) Set.univ z :=
    (h.filter_mono nhdsWithin_le_nhds).iteratedFDerivWithin_eq (by simpa using hx) m
  simpa [iteratedFDerivWithin_univ] using h1

theorem jet_bound_of_tsupport {n N : ℕ} (f : (Fin n → ℝ) → ℝ) (Rb : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hts : tsupport f ⊆ Metric.closedBall 0 Rb) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ (m : ℕ), m ≤ N → ∀ z : Fin n → ℝ, ‖iteratedFDeriv ℝ m f z‖ ≤ M) ∧
      (∀ (r : ℕ), r ≤ N → ∀ (γ : Fin r → Fin n) (z : Fin n → ℝ),
        |Work.Diff.STE.pdRVec r γ f z| ≤ M) := by
  classical
  -- the bound on the compact support ball
  obtain ⟨K, hK0, hK⟩ := Work.Diff.STE.flat.compact_iteratedFDeriv_bound f isOpen_univ
    hf.contDiffOn (ProperSpace.isCompact_closedBall (0 : Fin n → ℝ) Rb) (Set.subset_univ _) N
  -- inside the ball use compactness, outside it every derivative vanishes
  have hiter : ∀ (m : ℕ), m ≤ N → ∀ z : Fin n → ℝ, ‖iteratedFDeriv ℝ m f z‖ ≤ K := by
    intro m hm z
    by_cases hz : z ∈ Metric.closedBall (0 : Fin n → ℝ) Rb
    · exact hK z hz m hm
    · have hts' : z ∉ tsupport f := fun h => hz (hts h)
      rw [iteratedFDeriv_eq_zero_of_eventuallyEq_zero
        (notMem_tsupport_iff_eventuallyEq.mp hts'), norm_zero]
      exact hK0
  refine ⟨K, hK0, hiter, ?_⟩
  -- the partial derivatives are the iterated derivatives on unit vectors
  intro r hr γ z
  rw [pdRVec_eq_iteratedFDeriv_eval hf r γ z]
  calc |iteratedFDeriv ℝ r f z (fun j => Pi.single (γ j) (1 : ℝ))|
      = ‖iteratedFDeriv ℝ r f z (fun j => Pi.single (γ j) (1 : ℝ))‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖iteratedFDeriv ℝ r f z‖ * ∏ j, ‖(Pi.single (γ j) (1 : ℝ) : Fin n → ℝ)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ r f z‖ * 1 := by simp [Pi.norm_single]
    _ ≤ K := by rw [mul_one]; exact hiter r hr z

end Work.Diff.STE.B3
