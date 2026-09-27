import Mathlib
import Submission.Work.Mostow.discreteSubgroupGap
import Submission.Work.Mostow.isAddCyclicEqZmultiples

namespace Work.Mostow

/-- **A discrete (or: locally finite) additive subgroup of `ℝ` is cyclic.**
If `S ≤ ℝ` meets every compact interval `[-R, R]` in a finite set, then
`S` is the set of integer multiples of a single real number `c`
(so `S = cℤ`, with `c = 0` when `S` is trivial).

Proof: `discreteSubgroupGap` produces a gap `ε > 0` around `0`, hence every
point of `S` is isolated in `S` and the subgroup is topologically discrete.
An Archimedean linearly ordered discrete additive group is cyclic
(`AddSubgroup.discrete_iff_addCyclic`), and a cyclic additive subgroup of `ℝ`
consists of the integral multiples of one real number
(`isAddCyclicEqZmultiples`). -/
theorem addSubgroupEqZmultiples (S : AddSubgroup ℝ)
    (hfin : ∀ R : ℝ, ((S : Set ℝ) ∩ Set.Icc (-R) R).Finite) :
    ∃ c : ℝ, (S : Set ℝ) = Set.range (fun m : ℤ => (m : ℝ) * c) := by
  obtain ⟨ε, hε, hgap⟩ := discreteSubgroupGap S hfin
  have hdisc : DiscreteTopology ↥S := by
    have his : IsDiscrete (S : Set ℝ) := by
      rw [isDiscrete_iff_forall_mem_exists_isOpen]
      intro y hy
      refine ⟨Set.Ioo (y - ε) (y + ε), isOpen_Ioo, ?_⟩
      ext z
      constructor
      · rintro ⟨⟨hz1, hz2⟩, hzS⟩
        have hd : z - y ∈ S := S.sub_mem hzS hy
        have habs : |z - y| < ε := by rw [abs_lt]; exact ⟨by linarith, by linarith⟩
        have hzy : z - y = 0 := hgap (z - y) hd habs
        have hzy' : z = y := by linarith
        simp [hzy']
      · intro hz
        have hzy : z = y := by simpa using hz
        subst hzy
        exact ⟨⟨by linarith, by linarith⟩, hy⟩
    exact isDiscrete_iff_discreteTopology.mp his
  exact isAddCyclicEqZmultiples S (AddSubgroup.discrete_iff_addCyclic.mpr hdisc)

end Work.Mostow
