import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.goodSet_E1_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The good/bad sets and the parameters of the bad-set analysis

The bad-set stage of the proof of `Work.BMF.MRDirichletL2Direct` (Matomäki–Radziwiłł §8.3)
runs its *own* Buchstab/Ramaré decomposition of the Dirichlet polynomial, at a parameter set
whose prime-window scales are as large as possible: this is what makes both

* the saving `exp(-log P_j / (log T)^{2/3+ε})` of the prime large-values lemma
  (`Work.BMF.prime_large_values`), and
* the count `|T_L| ≪ exp(o(log Y))` of the large values of the prime polynomial
  (`Work.BMF.mr_direct.primePoly_large_values_window`)

available simultaneously.  The parameters are

* `Q = exp(log Y / log log Y)` — the upper end of the prime range (log-scale `≈ log Y/log log Y`);
* `P = Q^a` — the lower end, with `a ∈ (0,1/2]` a fixed constant (the extreme case
  `a = 1/2` gives `Q = exp((log Y)/(2 log log Y))`, still huge);
* the resolution `K` is *any* constant `≥ 3` (the number of windows is `≈ K log(Q/P)`,
  and the error term `1/K` forces `K ≳ 1/ε`).

These are deliberately *different* from the good-set parameters `P = (log Y)^40`,
`Q = H^{1/2}`, `K = P^{1/6-1/100}/(log Q)^{1/3}` of the `E_1`/good-set analysis: with the
latter, `log Q/log P ≍ log Y/log log Y` is unbounded, which the factor `log(Q/P)/log P` of the
large-values estimate cannot absorb.

The key point that makes a *single* system sufficient here (where MR need two, a fine one for
the good set and a coarse one for the bad set) is that at these parameters the ratio
`log Q/log P = 1/a` is a *constant*, so the *same* system can serve both: the good set
`Work.BMF.goodSetR` with its MVT-based bound, and the bad sets
`Work.BMF.mr_direct.badSetR` where the prime polynomials are large — the latter being exactly
what the large-values count and the saving `exp(-log P_j/(log T)^{2/3+ε})` need.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open scoped BigOperators

noncomputable section

/-- The upper scale `Q = exp(log Y / log log Y)` of the bad-set decomposition. -/
def badQ (Y : ℝ) : ℝ := Real.exp (Real.log Y / Real.log (Real.log Y))

/-- The lower scale `P = Q^a` of the bad-set decomposition. -/
def badP (a Y : ℝ) : ℝ := badQ Y ^ a

/-- The **bad set** at the resolution `K` for the index `j`: the points of `[-S,S]` where the
`j`-th prime-supported Dirichlet polynomial `primePoly cc K j` exceeds the good-set threshold
`exp(-(j/(4K)))`.  Inside `[-S,S]` the complement of `Work.BMF.goodSetR cc K P Q S` is the union
of the `badSetR cc K S j` over `j ∈ indexSet K P Q`. -/
def badSetR (cc : ℕ → ℂ) (K S : ℝ) (j : ℕ) : Set ℝ :=
  {t | t ∈ Set.Icc (-S) S ∧
    Real.exp (-((1 : ℝ) / 4 * (j : ℝ) / K)) < ‖Work.BMF.mrDirect.primePoly cc K j t‖}

/-- The part of the bad set where `‖Q_{j,K}‖` is *above* the auxiliary threshold `Θ` (the
`T_L` part of the large-values analysis, where the count of well-spaced points and the prime
large-values estimate `le:Hallargevalprimes` are brought to bear). -/
def badSetRL (cc : ℕ → ℂ) (K S Θ : ℝ) (j : ℕ) : Set ℝ :=
  Work.BMF.mr_direct.badSetR cc K S j ∩
    {t : ℝ | Θ ≤ ‖Work.BMF.mrDirect.primePoly cc K j t‖}

/-- The part of the bad set where `‖Q_{j,K}‖` is *below* the auxiliary threshold `Θ` (the
`T_S` part, where the trivial bound `‖Q_{j,K}‖ < Θ` suffices). -/
def badSetRS (cc : ℕ → ℂ) (K S Θ : ℝ) (j : ℕ) : Set ℝ :=
  Work.BMF.mr_direct.badSetR cc K S j ∩
    {t : ℝ | ‖Work.BMF.mrDirect.primePoly cc K j t‖ < Θ}

/-- `badSetR` is measurable: `[-S,S]` minus a closed set. -/
lemma measurableSet_badSetR (cc : ℕ → ℂ) (K S : ℝ) (j : ℕ) :
    MeasurableSet (Work.BMF.mr_direct.badSetR cc K S j) := by
  have hset : Work.BMF.mr_direct.badSetR cc K S j
      = Set.Icc (-S) S ∩
        {t : ℝ | Real.exp (-((1 : ℝ) / 4 * (j : ℝ) / K)) <
          ‖Work.BMF.mrDirect.primePoly cc K j t‖} := by
    ext t
    simp only [Work.BMF.mr_direct.badSetR, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [hset]
  exact MeasurableSet.inter measurableSet_Icc
    (isOpen_lt continuous_const
      (Work.BMF.mr_direct.continuous_primePoly cc K j).norm).measurableSet

lemma measurableSet_badSetRL (cc : ℕ → ℂ) (K S Θ : ℝ) (j : ℕ) :
    MeasurableSet (Work.BMF.mr_direct.badSetRL cc K S Θ j) :=
  (measurableSet_badSetR cc K S j).inter
    (isClosed_le continuous_const
      (Work.BMF.mr_direct.continuous_primePoly cc K j).norm).measurableSet

lemma measurableSet_badSetRS (cc : ℕ → ℂ) (K S Θ : ℝ) (j : ℕ) :
    MeasurableSet (Work.BMF.mr_direct.badSetRS cc K S Θ j) :=
  (measurableSet_badSetR cc K S j).inter
    (isOpen_lt (Work.BMF.mr_direct.continuous_primePoly cc K j).norm
      continuous_const).measurableSet

/-- `badSetR` is the union of its `T_L` and `T_S` parts. -/
lemma badSetR_eq_union (cc : ℕ → ℂ) (K S Θ : ℝ) (j : ℕ) :
    Work.BMF.mr_direct.badSetR cc K S j =
      Work.BMF.mr_direct.badSetRL cc K S Θ j ∪
        Work.BMF.mr_direct.badSetRS cc K S Θ j := by
  ext t
  constructor
  · intro ht
    by_cases h : Θ ≤ ‖Work.BMF.mrDirect.primePoly cc K j t‖
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, lt_of_not_ge h⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

lemma disjoint_badSetRL_badSetRS (cc : ℕ → ℂ) (K S Θ : ℝ) (j : ℕ) :
    Disjoint (Work.BMF.mr_direct.badSetRL cc K S Θ j)
      (Work.BMF.mr_direct.badSetRS cc K S Θ j) := by
  refine Set.disjoint_left.mpr fun t h1 h2 => ?_
  rw [Work.BMF.mr_direct.badSetRL] at h1
  rw [Work.BMF.mr_direct.badSetRS] at h2
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at h1 h2
  exact absurd h1.2 (not_le.mpr h2.2)

end

end Work.BMF.mr_direct

namespace Work.BMF

open MeasureTheory intervalIntegral
open scoped BigOperators

noncomputable section

/-- The good set at resolution `K`, inside `[-S,S]`: every prime polynomial at resolution `K` is
small.  This is the set hypothesis of the general-range good-set bound
`Work.BMF.mr_direct.goodSet_bound_range3`. -/
def goodSetR (cc : ℕ → ℂ) (K P Q S : ℝ) : Set ℝ :=
  {t | t ∈ Set.Icc (-S) S ∧
    ∀ j ∈ Work.BMF.mrDirect.indexSet K P Q,
      ‖Work.BMF.mrDirect.primePoly cc K j t‖ ≤ Real.exp (-((1 : ℝ) / 4 * (j : ℝ) / K))}

/-- `goodSetR` is measurable: it is the intersection of `[-S,S]` with finitely many closed sets. -/
lemma measurableSet_goodSetR (cc : ℕ → ℂ) (K P Q S : ℝ) :
    MeasurableSet (goodSetR cc K P Q S) := by
  have hset : goodSetR cc K P Q S
      = Set.Icc (-S) S ∩ ⋂ j ∈ (Work.BMF.mrDirect.indexSet K P Q : Set ℕ),
          {t : ℝ | ‖Work.BMF.mrDirect.primePoly cc K j t‖ ≤
            Real.exp (-((1 : ℝ) / 4 * (j : ℝ) / K))} := by
    ext t
    simp only [goodSetR, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_coe]
  rw [hset]
  refine MeasurableSet.inter measurableSet_Icc ?_
  exact MeasurableSet.biInter (Work.BMF.mrDirect.indexSet K P Q).countable_toSet
    fun j _ => (isClosed_le (Work.BMF.mr_direct.continuous_primePoly cc K j).norm
      continuous_const).measurableSet

/-- Inside `[-S,S]`, the complement of the good set is contained in the union of the bad sets. -/
lemma compl_goodSetR_subset_badSetR (cc : ℕ → ℂ) (K P Q S : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc (-S) S) (hnot : t ∉ goodSetR cc K P Q S) :
    ∃ j ∈ Work.BMF.mrDirect.indexSet K P Q,
      t ∈ Work.BMF.mr_direct.badSetR cc K S j := by
  rw [goodSetR] at hnot
  simp only [Set.mem_setOf_eq, not_and] at hnot
  have h2 := hnot ht
  push_neg at h2
  obtain ⟨j, hj, hlt⟩ := h2
  exact ⟨j, hj, ht, hlt⟩

end

end Work.BMF
