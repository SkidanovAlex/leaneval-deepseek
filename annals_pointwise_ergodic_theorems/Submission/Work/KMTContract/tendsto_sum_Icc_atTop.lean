import Mathlib

/-!
# Symmetric partial sums over `ℤ` converge to the sum

For an unconditionally summable family `g : ℤ → G` the symmetric interval sums
`∑_{j ∈ Icc (n - K) (n + K)} g j` converge to `∑' j, g j` as `K → ∞`.

The content is that the intervals `Icc (n - K) (n + K)` are *cofinal* in the directed set of
finite subsets of `ℤ` (ordered by inclusion): every finite set is contained in one of them. Since
unconditional summability is the convergence of the partial sums over all finite subsets along this
directed set, the statement follows by composition.
-/

namespace Work.KMTContract

/-- The intervals `Icc (n - K) (n + K)` are cofinal among the finite subsets of `ℤ`, hence tend
to `atTop`. -/
private lemma tendsto_Icc_atTop_cofinal (n : ℤ) :
    Filter.Tendsto (fun K : ℕ => Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)))
      Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro t
  rw [Filter.eventually_atTop]
  -- a finite set is contained in `Icc (n - K) (n + K)` as soon as `K` dominates the distances of
  -- its elements from `n`, in both directions
  refine ⟨max (t.sup fun x : ℤ => (x - n).natAbs) (t.sup fun x : ℤ => (n - x).natAbs),
    fun K hK => ?_⟩
  intro x hx
  rw [Finset.mem_Icc]
  have h1 : (x - n).natAbs ≤ K :=
    le_trans (le_trans (Finset.le_sup (f := fun x : ℤ => (x - n).natAbs) hx) (le_max_left _ _)) hK
  have h2 : (n - x).natAbs ≤ K :=
    le_trans (le_trans (Finset.le_sup (f := fun x : ℤ => (n - x).natAbs) hx) (le_max_right _ _)) hK
  have h1' : ((x - n).natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast h1
  have h2' : ((n - x).natAbs : ℤ) ≤ (K : ℤ) := by exact_mod_cast h2
  rw [Int.natCast_natAbs] at h1' h2'
  obtain ⟨ha, hb⟩ := abs_le.mp h1'
  obtain ⟨hc, hd⟩ := abs_le.mp h2'
  constructor <;> omega

theorem tendsto_sum_Icc_atTop {G : Type*} [AddCommMonoid G] [TopologicalSpace G]
    {g : ℤ → G} (hg : Summable g) (n : ℤ) :
    Filter.Tendsto (fun K : ℕ => ∑ j ∈ Finset.Icc (n - (K : ℤ)) (n + (K : ℤ)), g j)
      Filter.atTop (nhds (∑' j, g j)) := by
  have hK := tendsto_Icc_atTop_cofinal n
  have h := hg.hasSum
  have hcomp := h.comp hK
  simpa [HasSum, Function.comp_def] using hcomp

end Work.KMTContract
