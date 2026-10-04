import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE.MovingFrame

open scoped BigOperators
open Filter

/-- **Expansion of a multilinear form in a basis.**  If `b` is a basis of `V` indexed by `Fin n`,
then the value of a five-fold multilinear form `f` on a tuple `w` is the sum, over all ways `r` of
choosing a basis index `r i` for each slot `i`, of the product of the corresponding coordinates of
the arguments times the value of `f` on the tuple of basis vectors.

This is `MultilinearMap.map_sum` (multilinearity, all coordinates at once) followed by
`MultilinearMap.map_smul_univ` and `Basis.sum_repr`; no continuity is needed. -/
theorem multilinear_apply_basis
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {n : ℕ} (b : Module.Basis (Fin n) ℝ V)
    (f : MultilinearMap ℝ (fun _ : Fin 5 => V) ℝ) (w : Fin 5 → V) :
    f w = ∑ r : Fin 5 → Fin n, (∏ i, b.repr (w i) (r i)) * f (fun i => b (r i)) := by
  have hw : w = fun i => ∑ j : Fin n, (b.repr (w i)) j • b j := by
    funext i; exact (b.sum_repr (w i)).symm
  conv_lhs => rw [hw]
  rw [MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ]
  simp

/-- A family of five-fold multilinear forms on a finite-dimensional normed space that converges
pointwise is eventually bounded in operator norm.  (The pointwise limits `Ψ w` need not be assumed
to be multilinear: the proof expands `Φ s` in a basis of `V`, whose finitely many coefficients
converge hence are bounded near `l`.) -/
theorem multilinear_eventually_bounded
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {l : Filter ℝ} (Φ : ℝ → MultilinearMap ℝ (fun _ : Fin 5 => V) ℝ)
    (Ψ : (Fin 5 → V) → ℝ)
    (htend : ∀ w : Fin 5 → V, Filter.Tendsto (fun s : ℝ => Φ s w) l (nhds (Ψ w))) :
    ∃ C : ℝ, ∀ᶠ s in l, ∀ w : Fin 5 → V, |Φ s w| ≤ C * ∏ i, ‖w i‖ := by
  classical
  -- a basis of `V`, kept as a free variable `n` so that `Fin n` never unfolds to `finrank`
  obtain ⟨n, ⟨b⟩⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) ℝ V) :=
    ⟨_, ⟨Module.finBasis ℝ V⟩⟩
  -- the coordinate functionals of the basis, as *continuous* linear maps (finite dimension)
  let c : Fin n → (V →L[ℝ] ℝ) := fun j => LinearMap.toContinuousLinearMap (b.coord j)
  have hcoord : ∀ (j : Fin n) (v : V), |b.repr v j| ≤ ‖c j‖ * ‖v‖ := by
    intro j v
    have h1 : (c j) v = b.repr v j := by simp [c]
    rw [← h1]
    simpa [Real.norm_eq_abs] using ContinuousLinearMap.le_opNorm (c j) v
  -- the finitely many values on basis tuples converge, hence are eventually bounded
  have hbdd : ∀ᶠ s in l, ∀ r : Fin 5 → Fin n,
      |Φ s (fun i => b (r i))| ≤ |Ψ (fun i => b (r i))| + 1 := by
    rw [Filter.eventually_all]
    intro r
    have hmem : ∀ᶠ s in l, Φ s (fun i => b (r i)) ∈
        Set.Ioo (-(|Ψ (fun i => b (r i))| + 1)) (|Ψ (fun i => b (r i))| + 1) := by
      refine (htend (fun i => b (r i))).eventually (isOpen_Ioo.mem_nhds ⟨?_, ?_⟩)
      · linarith [neg_abs_le (Ψ (fun i => b (r i)))]
      · linarith [le_abs_self (Ψ (fun i => b (r i)))]
    filter_upwards [hmem] with s hs
    exact abs_le.mpr ⟨hs.1.le, hs.2.le⟩
  set B : ℝ := ∑ r : Fin 5 → Fin n, (|Ψ (fun i => b (r i))| + 1) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]; exact Finset.sum_nonneg fun r _ => by positivity
  refine ⟨(∑ r : Fin 5 → Fin n, ∏ i, ‖c (r i)‖) * B, ?_⟩
  filter_upwards [hbdd] with s hs
  intro w
  -- termwise bound: coordinates are bounded by `‖c ·‖ * ‖w i‖`, and the basis-tuple values by `B`
  have hterm : ∀ r : Fin 5 → Fin n,
      (∏ i, |b.repr (w i) (r i)|) * |Φ s (fun i => b (r i))|
        ≤ (∏ i, (‖c (r i)‖ * ‖w i‖)) * B := by
    intro r
    have h1 : ∏ i, |b.repr (w i) (r i)| ≤ ∏ i, (‖c (r i)‖ * ‖w i‖) :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ => hcoord (r i) (w i)
    have h2 : |Φ s (fun i => b (r i))| ≤ B := by
      rw [hB]
      exact (hs r).trans (Finset.single_le_sum
        (f := fun r' => |Ψ (fun i => b (r' i))| + 1) (fun r' _ => by positivity)
        (Finset.mem_univ r))
    exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have hexp : Φ s w
      = ∑ r : Fin 5 → Fin n, (∏ i, b.repr (w i) (r i)) * Φ s (fun i => b (r i)) :=
    multilinear_apply_basis b (Φ s) w
  calc |Φ s w|
      = |∑ r : Fin 5 → Fin n, (∏ i, b.repr (w i) (r i)) * Φ s (fun i => b (r i))| := by
          rw [hexp]
    _ ≤ ∑ r : Fin 5 → Fin n,
          |(∏ i, b.repr (w i) (r i)) * Φ s (fun i => b (r i))| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r : Fin 5 → Fin n,
          (∏ i, |b.repr (w i) (r i)|) * |Φ s (fun i => b (r i))| := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [abs_mul, Finset.abs_prod]
    _ ≤ ∑ r : Fin 5 → Fin n, (∏ i, (‖c (r i)‖ * ‖w i‖)) * B :=
          Finset.sum_le_sum fun r _ => hterm r
    _ = ∑ r : Fin 5 → Fin n, (∏ i, ‖c (r i)‖) * (∏ i, ‖w i‖) * B := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.prod_mul_distrib]
    _ = (∑ r : Fin 5 → Fin n, ∏ i, ‖c (r i)‖) * (∏ i, ‖w i‖) * B := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ = (∑ r : Fin 5 → Fin n, ∏ i, ‖c (r i)‖) * B * ∏ i, ‖w i‖ := by ring

end Work.Diff.GE.MovingFrame
