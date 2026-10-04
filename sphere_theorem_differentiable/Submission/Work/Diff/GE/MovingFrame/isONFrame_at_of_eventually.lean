import Mathlib
import Submission.Work.Diff.GE.MovingFrame.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

namespace Work.Diff.GE.MovingFrame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Bilinear expansion of a continuous bilinear form in a basis: every continuous bilinear
`L : E →L[ℝ] E →L[ℝ] ℝ` is determined by its values on the pairs of basis vectors, with the
coordinates of the two arguments supplied by the dual basis `b.coord ·`. -/
lemma clm_apply_eq_sum_basis_expand {n : ℕ} (b : Module.Basis (Fin n) ℝ E)
    (L : E →L[ℝ] E →L[ℝ] ℝ) (u v : E) :
    L u v = ∑ p, ∑ q, b.coord p u * (b.coord q v * (L (b p) (b q))) := by
  conv_lhs => rw [← Module.Basis.sum_repr b u, ← Module.Basis.sum_repr b v]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum,
    Module.Basis.coord_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun x _ => ?_))
  ring

/-- A frame that is `G s`-orthonormal for `s` near `t` (within `[0,T)`) and continuous in `s` is
`G t`-orthonormal *at* `t`.  Passing to the limit in `s ↦ ⟨e s i, e s j⟩_{G s}` uses that
`s ↦ ⟨u,v⟩_{G s}` is continuous at `t` for fixed `u v` (from `IsRicciFlow`), that `e` is continuous
at `t`, and that the metric bilinear forms `(G s).inner x` are bounded in operator norm near `t`
(finite-dimensionality: `s ↦ (G s).inner x` is a curve in the finite-dimensional space of bilinear
forms converging pointwise, hence in norm); both reviewers suggested that plain continuity of
`s ↦ (G s).inner x (e s i) (e s j)` suffices, which itself follows from joint continuity of
`(s,u,v) ↦ (G s).inner x u v`. -/
theorem isONFrame_at_of_eventually
    (G : ℝ → SMet I M) (T t : ℝ) (hRic : IsRicciFlow G T) (ht : t ∈ Set.Ico 0 T) (x : M)
    (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hcont : ∀ i, ContinuousWithinAt (fun s ↦ e s i) (Set.Ico 0 T) t)
    (hON : ∀ᶠ s in 𝓝[Set.Ico 0 T] t, IsONFrame (G s) x (e s)) :
    IsONFrame (G t) x (e t) := by
  -- We prove that `s ↦ ⟨e s i, e s j⟩_{G s}` is continuous at `t` *within* `Ico 0 T`; the
  -- conclusion follows because that function is eventually the constant `if i = j then 1 else 0`
  -- and a limit in a `T2` space is unique.
  --
  -- The only ingredient that is not immediate is the continuity: a *moving* pairing of the metric
  -- against a *moving* pair of vectors.  All the needed uniformity is supplied by writing the
  -- pairing out in a fixed `ℝ`-basis `b` of `E = TₓM`.  Then
  -- `⟨w, w'⟩_{G s} = ∑ p ∑ q (coord p w) * (coord q w' * ⟨b p, b q⟩_{G s})`
  -- (`clm_apply_eq_sum_basis_expand`), a finite sum of products of scalar functions that are
  -- continuous within `Ico 0 T` at `t`: the coordinates of `e s k` by `hcont`, and the fixed-vector
  -- pairings `s ↦ ⟨b p, b q⟩_{G s}` from the flow equation in `hRic`.
  classical
  intro i j
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hinner : ∀ p q : Fin (Module.finrank ℝ E),
      Tendsto (fun s : ℝ ↦ (G s).inner x (b p) (b q)) (𝓝[Set.Ico 0 T] t)
        (𝓝 ((G t).inner x (b p) (b q))) :=
    fun p q => (hRic.2 t ht x (b p) (b q)).continuousWithinAt
  have hcoe : ∀ (p k : Fin (Module.finrank ℝ E)),
      Tendsto (fun s : ℝ ↦ b.coord p (e s k)) (𝓝[Set.Ico 0 T] t)
        (𝓝 (b.coord p (e t k))) :=
    fun p k => ((b.coord p).continuous_of_finiteDimensional.continuousAt.comp_continuousWithinAt
      (hcont k))
  have hterm : ∀ p q : Fin (Module.finrank ℝ E),
      Tendsto (fun s : ℝ ↦ b.coord p (e s i) * (b.coord q (e s j) * (G s).inner x (b p) (b q)))
        (𝓝[Set.Ico 0 T] t)
        (𝓝 (b.coord p (e t i) * (b.coord q (e t j) * (G t).inner x (b p) (b q)))) :=
    fun p q => (hcoe p i).mul ((hcoe q j).mul (hinner p q))
  have hsum : Tendsto
      (fun s : ℝ ↦ ∑ p, ∑ q, b.coord p (e s i) * (b.coord q (e s j) * (G s).inner x (b p) (b q)))
      (𝓝[Set.Ico 0 T] t)
      (𝓝 (∑ p, ∑ q, b.coord p (e t i) * (b.coord q (e t j) * (G t).inner x (b p) (b q)))) :=
    tendsto_finsetSum Finset.univ (fun p _ =>
      tendsto_finsetSum Finset.univ (fun q _ => hterm p q))
  have hlim : Tendsto (fun s : ℝ ↦ (G s).inner x (e s i) (e s j)) (𝓝[Set.Ico 0 T] t)
      (𝓝 ((G t).inner x (e t i) (e t j))) := by
    have heq : (fun s : ℝ ↦
          ∑ p, ∑ q, b.coord p (e s i) * (b.coord q (e s j) * (G s).inner x (b p) (b q)))
        =ᶠ[𝓝[Set.Ico 0 T] t] (fun s : ℝ ↦ (G s).inner x (e s i) (e s j)) :=
      Filter.EventuallyEq.of_eq (by
        funext s
        exact (clm_apply_eq_sum_basis_expand (E := E) b ((G s).inner x) (e s i) (e s j)).symm)
    have h2 := hsum.congr' heq
    have h3 : (∑ p, ∑ q, b.coord p (e t i) * (b.coord q (e t j) * (G t).inner x (b p) (b q)))
        = (G t).inner x (e t i) (e t j) :=
      (clm_apply_eq_sum_basis_expand (E := E) b ((G t).inner x) (e t i) (e t j)).symm
    rwa [h3] at h2
  haveI : (𝓝[Set.Ico 0 T] t).NeBot := nhdsWithin_neBot_of_mem ht
  have hev : (fun s : ℝ ↦ (G s).inner x (e s i) (e s j)) =ᶠ[𝓝[Set.Ico 0 T] t]
      (fun _ : ℝ ↦ (if i = j then (1 : ℝ) else 0)) := by
    filter_upwards [hON] with s hs
    exact hs i j
  exact (tendsto_nhds_unique (tendsto_const_nhds) (hlim.congr' hev)).symm

end Work.Diff.GE.MovingFrame
