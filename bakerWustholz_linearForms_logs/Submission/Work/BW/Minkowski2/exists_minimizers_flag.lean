import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_exists_indep
import Submission.Work.BW.basisRed_min_outside
import Submission.Work.BW.basisRed_succMinL_mono
import Submission.Work.BW.Minkowski2.flag_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A flag of minimisers realising the successive minima

For a "lattice norm" `F` on `ℝᵈ` (see `Work.BW.IsLatticeNorm`) and its successive minima
`λ_j = succMinL F j` we construct lattice vectors `u 0, …, u (d-1)` such that

* `u` is `ℝ`-linearly independent,
* `F (u k) = λ_{k+1}` for every `k`,
* every lattice vector of `F`-norm `< λ_{k+1}` lies in the span of `u 0, …, u (k-1)`.

The construction is the greedy one: `u k` minimises `F` among the lattice vectors outside the
span `W_k` of `u 0, …, u (k-1)`.  The existing lemma `Work.BW.min_outside_le_succMinL` gives
`F (u k) ≤ λ_{k+1}`; the reverse inequality is the point of the file.  Since `u k` is a
minimiser outside `W_k`, one has `F (u j) ≤ F (u k)` for `j ≤ k` (each `u j` minimises over the
larger set of vectors outside the smaller space `W_j ⊆ W_k`).  Hence the span of the lattice
vectors of `F`-norm at most `F (u k)` contains all of `W_k` as well as `u k` itself, so its
dimension is at least `k+1`; by definition of `λ_{k+1}` as the infimum of those levels,
`λ_{k+1} ≤ F (u k)`.  The flag property is then immediate from the minimising property.
-/

namespace Work.BW.Minkowski2

/-- Reduction of `Fin.snoc` at an index whose value is `< k`. -/
lemma snoc_eq_of_val_lt {k : ℕ} {α : Type*} (v : Fin k → α) (w : α) (j : Fin (k + 1))
    (hj : (j : ℕ) < k) : (Fin.snoc v w : Fin (k + 1) → α) j = v ⟨(j : ℕ), hj⟩ := by
  have hjeq : j = (⟨(j : ℕ), hj⟩ : Fin k).castSucc := by ext; simp
  conv_lhs => rw [hjeq, Fin.snoc_castSucc]

/-- `spanPrev` is unchanged at the old indices when a vector is appended with `Fin.snoc`. -/
theorem spanPrev_snoc_castSucc {d k : ℕ} (v : Fin k → (Fin d → ℤ)) (w : Fin d → ℤ) (i : Fin k) :
    spanPrev (Fin.snoc v w) i.castSucc = spanPrev v i := by
  simp only [spanPrev]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨j, hj⟩, rfl⟩
    simp only [Fin.val_castSucc] at hj
    have hjlt : (j : ℕ) < k := lt_trans hj i.isLt
    refine Submodule.subset_span ⟨⟨⟨(j : ℕ), hjlt⟩, hj⟩, ?_⟩
    show castVec (v ⟨(j : ℕ), hjlt⟩) = castVec ((Fin.snoc v w : Fin (k + 1) → (Fin d → ℤ)) j)
    rw [snoc_eq_of_val_lt v w j hjlt]
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨j, hj⟩, rfl⟩
    refine Submodule.subset_span ⟨⟨j.castSucc, ?_⟩, ?_⟩
    · simp only [Fin.val_castSucc]; exact hj
    · show castVec ((Fin.snoc v w : Fin (k + 1) → (Fin d → ℤ)) (Fin.castSucc j)) = castVec (v j)
      rw [Fin.snoc_castSucc]

/-- `spanPrev` at the last index of `Fin.snoc v w` is the span of all of `v`. -/
theorem spanPrev_snoc_last {d k : ℕ} (v : Fin k → (Fin d → ℤ)) (w : Fin d → ℤ) :
    spanPrev (Fin.snoc v w) (Fin.last k)
      = Submodule.span ℝ (Set.range (fun j : Fin k => castVec (v j))) := by
  simp only [spanPrev]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨⟨j, hj⟩, rfl⟩
    rw [Fin.val_last] at hj
    refine Submodule.subset_span ⟨⟨(j : ℕ), hj⟩, ?_⟩
    show castVec (v ⟨(j : ℕ), hj⟩) = castVec ((Fin.snoc v w : Fin (k + 1) → (Fin d → ℤ)) j)
    rw [snoc_eq_of_val_lt v w j hj]
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨j.castSucc, ?_⟩, ?_⟩
    · simp only [Fin.val_last, Fin.val_castSucc]; exact j.isLt
    · show castVec ((Fin.snoc v w : Fin (k + 1) → (Fin d → ℤ)) (Fin.castSucc j)) = castVec (v j)
      rw [Fin.snoc_castSucc]

/-- The lower bound `succMinL F (k+1) ≤ F w`: if `w` lies outside the span of the independent
family `v` while every `v j` has `F`-norm at most `F w`, then the span of the lattice vectors of
`F`-norm at most `F w` is strictly larger than `span v`, hence has dimension `≥ k+1`, so
`F w` is an admissible level for the `(k+1)`-st successive minimum. -/
theorem succMinL_le_of_span_lt {d k : ℕ} {F : (Fin d → ℝ) → ℝ} (hF : IsLatticeNorm F)
    {v : Fin k → (Fin d → ℤ)} (hv : LinearIndependent ℝ (fun j : Fin k => castVec (v j)))
    {w : Fin d → ℤ}
    (hw : castVec w ∉ Submodule.span ℝ (Set.range (fun j : Fin k => castVec (v j))))
    (hmono : ∀ j : Fin k, F (castVec (v j)) ≤ F (castVec w)) :
    succMinL F (k + 1) ≤ F (castVec w) := by
  set W : Submodule ℝ (Fin d → ℝ) :=
    Submodule.span ℝ (Set.range (fun j : Fin k => castVec (v j))) with hW
  set t : ℝ := F (castVec w) with ht
  have hWle : W ≤ basisRed_succSpanL F t := by
    rw [hW]
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    refine Submodule.subset_span ⟨⟨v j, rfl⟩, ?_⟩
    rw [ht]; exact hmono j
  have hwS : castVec w ∈ basisRed_succSpanL F t := by
    refine Submodule.subset_span ⟨⟨w, rfl⟩, ?_⟩
    exact le_of_eq ht.symm
  have hlt : W < basisRed_succSpanL F t := by
    refine lt_of_le_of_ne hWle ?_
    intro heq
    rw [heq] at hw
    exact hw hwS
  have hfrW : Module.finrank ℝ W = k := by
    rw [hW, finrank_span_eq_card hv, Fintype.card_fin]
  have hk : k + 1 ≤ Module.finrank ℝ (basisRed_succSpanL F t) := by
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hmem : t ∈ basisRed_succSetL F (k + 1) := hk
  rw [basisRed_succMinL_eq_sInf]
  exact csInf_le ⟨0, fun s hs => basisRed_succSetL_nonneg hF (by omega) hs⟩ hmem

/-- Greedy construction of a family of minimisers of length `k ≤ d`. -/
theorem exists_greedy_flag {d : ℕ} (F : (Fin d → ℝ) → ℝ) (hF : IsLatticeNorm F) :
    ∀ k : ℕ, k ≤ d → ∃ v : Fin k → (Fin d → ℤ),
      LinearIndependent ℝ (fun i : Fin k => castVec (v i)) ∧
      (∀ i : Fin k, F (castVec (v i)) = succMinL F (i.1 + 1)) ∧
      (∀ i : Fin k, castVec (v i) ∉ spanPrev v i) ∧
      (∀ i : Fin k, ∀ z : Fin d → ℤ, castVec z ∉ spanPrev v i →
        F (castVec (v i)) ≤ F (castVec z)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hvind, hvE, hvnm, hvmin⟩ := ih (by omega)
    set W : Submodule ℝ (Fin d → ℝ) :=
      Submodule.span ℝ (Set.range (fun j : Fin k => castVec (v j))) with hW
    have hfrW : Module.finrank ℝ W = k := by
      rw [hW, finrank_span_eq_card hvind, Fintype.card_fin]
    have hspanW : ∀ j : Fin k, spanPrev v j ≤ W := by
      intro j
      simp only [spanPrev]
      rw [hW]
      apply Submodule.span_le.mpr
      rintro x ⟨l, rfl⟩
      exact Submodule.subset_span ⟨l, rfl⟩
    have hWne : W ≠ ⊤ := by
      intro htop
      have hd : Module.finrank ℝ W = d := by
        rw [htop]; simp
      omega
    obtain ⟨w, hwW, hwmin⟩ := exists_min_outside hF W hWne
    have hw_le : F (castVec w) ≤ succMinL F (k + 1) := by
      have h := min_outside_le_succMinL hF W (by rw [hfrW]; omega) hwmin
      rwa [hfrW] at h
    have hmono : ∀ j : Fin k, F (castVec (v j)) ≤ F (castVec w) := by
      intro j
      exact hvmin j w (fun hmem => hwW (hspanW j hmem))
    have hw_ge : succMinL F (k + 1) ≤ F (castVec w) :=
      succMinL_le_of_span_lt hF hvind hwW hmono
    have hwEq : F (castVec w) = succMinL F (k + 1) := le_antisymm hw_le hw_ge
    refine ⟨Fin.snoc v w, ?_, ?_, ?_, ?_⟩
    · have hsnoc : (fun i : Fin (k + 1) => castVec ((Fin.snoc v w : Fin (k + 1) → (Fin d → ℤ)) i))
          = Fin.snoc (fun i : Fin k => castVec (v i)) (castVec w) := by
        funext i
        rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        · rw [Fin.snoc_last, Fin.snoc_last]
      rw [hsnoc]
      exact hvind.finSnoc hwW
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        simpa using hvE j
      · rw [Fin.snoc_last, Fin.val_last]
        exact hwEq
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc, spanPrev_snoc_castSucc]
        exact hvnm j
      · rw [Fin.snoc_last, spanPrev_snoc_last, ← hW]
        exact hwW
    · intro i z hz
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        rw [spanPrev_snoc_castSucc] at hz
        exact hvmin j z hz
      · rw [Fin.snoc_last]
        rw [spanPrev_snoc_last, ← hW] at hz
        exact hwmin z hz

theorem exists_minimizers_flag {d : ℕ} {F : (Fin d → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    ∃ u : Fin d → (Fin d → ℤ),
      LinearIndependent ℝ (fun k : Fin d => (fun i => ((u k) i : ℝ))) ∧
      (∀ k : Fin d, F (fun i => ((u k) i : ℝ)) = Work.BW.succMinL F (k.1 + 1)) ∧
      (∀ (k : Fin d) (w : Fin d → ℤ), F (fun i => (w i : ℝ)) < Work.BW.succMinL F (k.1 + 1) →
        (fun i => (w i : ℝ)) ∈ Submodule.span ℝ
          (Set.range (fun j : {j : Fin d // j.1 < k.1} => (fun i => ((u j) i : ℝ))))) := by
  obtain ⟨u, hind, hE, hnm, hmin⟩ := exists_greedy_flag F hF d le_rfl
  refine ⟨u, hind, hE, ?_⟩
  intro k w hw
  change castVec w ∈ spanPrev u k
  by_contra hmem
  have h1 := hmin k w hmem
  have h2 := hE k
  change F (castVec w) < succMinL F (k.1 + 1) at hw
  linarith

end Work.BW.Minkowski2
