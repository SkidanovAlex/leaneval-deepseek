import Mathlib
import Submission.Subspace.Classical
import Submission.Commons.Analysis.Normed.finite_bounded_int_vectors

set_option linter.unnecessarySimpa false

/-!
# Stage F glue: finitely many points lie in finitely many proper ℚ-subspaces

The bounded-height (bounded ‖·‖) solutions of the subspace inequality form a finite
set (`Commons.Analysis.Normed.finite_bounded_int_vectors`).  Such a finite set of
nonzero integer points is contained in a finite family of proper ℚ-subspaces (one
1-dimensional span per point), which is exactly the covering data consumed by
`SubspaceTheoremSubspaces` / `subspaces_imp_normals`.
-/

open scoped BigOperators

namespace Submission.Subspace

section StageF

variable {σ : Type*} [Fintype σ]

/-- The ℚ-span of a single vector is a proper subspace as soon as the ambient space
has dimension at least two (no nonzeroness of the vector is needed). -/
lemma span_singleton_ne_top_of_two_le_card (hσ : 2 ≤ Fintype.card σ) (v : σ → ℚ) :
    Submodule.span ℚ ({v} : Set (σ → ℚ)) ≠ ⊤ := by
  intro htop
  have hfull : Module.finrank ℚ (σ → ℚ) = Fintype.card σ := by
    simpa using (Module.finrank_fintype_fun_eq_card (R := ℚ) (η := σ))
  have hfinW : Module.finrank ℚ (Submodule.span ℚ ({v} : Set (σ → ℚ))) ≤ 1 := by
    simpa using (finrank_span_le_card (R := ℚ) (M := σ → ℚ) ({v} : Set (σ → ℚ)))
  have hWfin : Module.finrank ℚ (Submodule.span ℚ ({v} : Set (σ → ℚ))) = Fintype.card σ := by
    rw [htop]
    simpa using (Module.finrank_top ℚ (σ → ℚ)).trans hfull
  linarith

/-- Every finite set of nonzero integer points is contained in a finite family of
proper ℚ-subspaces of `σ → ℚ` (one per point: its one-dimensional span). -/
theorem finite_points_in_proper_subspaces (hσ : 2 ≤ Fintype.card σ)
    (s : Finset (σ → ℤ)) (hs0 : (0 : σ → ℤ) ∉ s) :
    ∃ T : Set (Submodule ℚ (σ → ℚ)), T.Finite ∧
      (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : σ → ℤ, x ∈ s → ∃ W ∈ T, (fun i : σ => (x i : ℚ)) ∈ W := by
  classical
  let v : (σ → ℤ) → (σ → ℚ) := fun x i => (x i : ℚ)
  have hv_ne (x : σ → ℤ) (hx : x ∈ s) : v x ≠ 0 := by
    intro h
    have : x = 0 := by
      funext i
      have hc := congrFun h i
      have hci : ((x i : ℤ) : ℚ) = 0 := by simpa [v] using hc
      exact_mod_cast hci
    exact hs0 (by simpa [this] using hx)
  let Tf : Finset (Submodule ℚ (σ → ℚ)) :=
    s.image (fun x => Submodule.span ℚ ({v x} : Set (σ → ℚ)))
  refine ⟨(Tf : Set (Submodule ℚ (σ → ℚ))), ?_, ?_, ?_⟩
  · exact Tf.finite_toSet
  · intro W hW
    rw [Finset.mem_coe, Finset.mem_image] at hW
    rcases hW with ⟨x, hx, rfl⟩
    exact span_singleton_ne_top_of_two_le_card hσ (v x)
  · intro x hx
    refine ⟨Submodule.span ℚ ({v x} : Set (σ → ℚ)), ?_, ?_⟩
    · rw [Finset.mem_coe, Finset.mem_image]
      exact ⟨x, hx, rfl⟩
    · exact Submodule.subset_span (by simp [v])


/-- The set of nonzero small points of sup norm `< B` is finite. -/
lemma small_bounded_finite (L : σ → σ → ℂ) (ε : ℝ) (B : ℝ) :
    {x : σ → ℤ | x ≠ 0 ∧ Small L ε x ∧ ‖x‖ < B}.Finite := by
  refine Set.Finite.subset ?_ (by intro x hx; exact le_of_lt hx.2.2)
  exact Commons.Analysis.Normed.finite_bounded_int_vectors B

/-- Cover all small points with `‖x‖ < B` by finitely many proper subspaces. -/
theorem small_bounded_subspaces (hσ : 2 ≤ Fintype.card σ) (L : σ → σ → ℂ)
    (ε : ℝ) (B : ℝ) :
    ∃ T : Set (Submodule ℚ (σ → ℚ)), T.Finite ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : σ → ℤ, x ≠ 0 → Small L ε x → ‖x‖ < B →
        ∃ W ∈ T, (fun i : σ => (x i : ℚ)) ∈ W := by
  classical
  let S : Set (σ → ℤ) := {x | x ≠ 0 ∧ Small L ε x ∧ ‖x‖ < B}
  have hSfin : S.Finite := small_bounded_finite L ε B
  let s : Finset (σ → ℤ) := hSfin.toFinset
  have hs0 : (0 : σ → ℤ) ∉ s := by
    rw [Set.Finite.mem_toFinset]
    exact fun h => h.1 rfl
  rcases finite_points_in_proper_subspaces (σ := σ) hσ s hs0 with ⟨T, hTfin, hTprop, hTcov⟩
  refine ⟨T, hTfin, hTprop, ?_⟩
  intro x hx0 hx hxB
  have hxS : x ∈ S := ⟨hx0, hx, hxB⟩
  exact hTcov x (by rw [Set.Finite.mem_toFinset]; exact hxS)

/-- If, for some bound `B`, all *large* solutions (with `B ≤ ‖x‖`) lie in a fixed
finite family of proper subspaces, then all solutions do (the bounded part is a
finite set, covered by finitely many one-dimensional spans). -/
theorem cover_all_of_cover_large (hσ : 2 ≤ Fintype.card σ) (L : σ → σ → ℂ) (ε : ℝ)
    (T : Set (Submodule ℚ (σ → ℚ))) (hTfin : T.Finite) (hTprop : ∀ W ∈ T, W ≠ ⊤)
    (B : ℝ) (hTcov : ∀ x : σ → ℤ, x ≠ 0 → Small L ε x → B ≤ ‖x‖ →
        ∃ W ∈ T, (fun i : σ => (x i : ℚ)) ∈ W) :
    ∃ T' : Set (Submodule ℚ (σ → ℚ)), T'.Finite ∧ (∀ W ∈ T', W ≠ ⊤) ∧
      ∀ x : σ → ℤ, x ≠ 0 → Small L ε x →
        ∃ W ∈ T', (fun i : σ => (x i : ℚ)) ∈ W := by
  classical
  rcases small_bounded_subspaces (σ := σ) hσ L ε B with ⟨Ts, hTsfin, hTsprop, hTscov⟩
  refine ⟨T ∪ Ts, hTfin.union hTsfin, ?_, ?_⟩
  · intro W hW
    rcases hW with hW | hW
    · exact hTprop W hW
    · exact hTsprop W hW
  · intro x hx0 hx
    by_cases hB : B ≤ ‖x‖
    · rcases hTcov x hx0 hx hB with ⟨W, hW, hxW⟩
      exact ⟨W, Or.inl hW, hxW⟩
    · have hxB : ‖x‖ < B := lt_of_not_ge hB
      rcases hTscov x hx0 hx hxB with ⟨W, hW, hxW⟩
      exact ⟨W, Or.inr hW, hxW⟩

/-- Master interface: if for every `ε > 0` there are finitely many proper subspaces
and a bound `B` covering all *large* solutions (`B ≤ ‖x‖`), then the full subspace
form of the theorem holds (bounded solutions are finite). -/
theorem subspaces_of_unbounded_cover (L : σ → σ → ℂ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set (Submodule ℚ (σ → ℚ)), T.Finite ∧
        (∀ W ∈ T, W ≠ ⊤) ∧ ∃ B : ℝ, ∀ x : σ → ℤ, x ≠ 0 → Small L ε x → B ≤ ‖x‖ →
          ∃ W ∈ T, (fun i : σ => (x i : ℚ)) ∈ W)
    (hσ : 2 ≤ Fintype.card σ) :
    Submission.Subspace.SubspaceTheoremSubspaces σ L := by
  intro ε hε
  rcases h ε hε with ⟨T, hTfin, hTprop, B, hTcov⟩
  rcases cover_all_of_cover_large (σ := σ) hσ L ε T hTfin hTprop B hTcov with
    ⟨T', hT'fin, hT'prop, hT'cov⟩
  exact ⟨T', hT'fin, hT'prop, fun x hx0 hx => hT'cov x hx0 hx⟩

/-- The ℚ-subspace of points where the `i`-th form vanishes. -/
def formZeroSubmodule (L : σ → σ → ℂ) (i : σ) : Submodule ℚ (σ → ℚ) where
  carrier := {v | ∑ j : σ, L i j * (v j : ℂ) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change (∑ j : σ, L i j * ((x + y) j : ℂ)) = 0
    have hx' : (∑ j : σ, L i j * (x j : ℂ)) = 0 := hx
    have hy' : (∑ j : σ, L i j * (y j : ℂ)) = 0 := hy
    rw [show (∑ j : σ, L i j * ((x + y) j : ℂ)) =
        (∑ j : σ, L i j * (x j : ℂ)) + (∑ j : σ, L i j * (y j : ℂ)) from by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by
        simp only [Pi.add_apply]; push_cast; ring)]
    rw [hx', hy', add_zero]
  smul_mem' := by
    intro c x hx
    change (∑ j : σ, L i j * ((c • x) j : ℂ)) = 0
    have hx' : (∑ j : σ, L i j * (x j : ℂ)) = 0 := hx
    rw [show (∑ j : σ, L i j * ((c • x) j : ℂ)) =
        (c : ℂ) * (∑ j : σ, L i j * (x j : ℂ)) from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by
        simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring)]
    rw [hx', mul_zero]

theorem formZeroSubmodule_ne_top (L : σ → σ → ℂ) (ind : LinearIndependent ℂ L) (i : σ) :
    formZeroSubmodule L i ≠ ⊤ := by
  classical
  intro htop
  have hrow : L i = 0 := by
    funext j
    let e : σ → ℚ := fun x => if x = j then 1 else 0
    have hmem : e ∈ formZeroSubmodule L i := by rw [htop]; trivial
    have hsum : (∑ x : σ, L i x * (e x : ℂ)) = 0 := hmem
    have hsum' : (∑ x : σ, L i x * (e x : ℂ)) = L i j := by
      rw [Finset.sum_eq_single j]
      · simp [e]
      · intro b _ hb
        simp [e, hb]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [hsum'] at hsum
    exact hsum
  exact (LinearIndependent.ne_zero i ind) hrow


/-- The integer points where some form vanishes are covered by the `|σ|` fixed
proper ℚ-subspaces `{Lᵢ = 0}`. -/
theorem formZero_cover (L : σ → σ → ℂ) (ind : LinearIndependent ℂ L) :
    ∃ T : Set (Submodule ℚ (σ → ℚ)), T.Finite ∧ (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : σ → ℤ, (∃ i : σ, (∑ j : σ, L i j * (x j : ℂ)) = 0) →
        ∃ W ∈ T, (fun j : σ => (x j : ℚ)) ∈ W := by
  classical
  refine ⟨Set.range (formZeroSubmodule L), Set.finite_range _, ?_, ?_⟩
  · rintro W ⟨i, rfl⟩
    exact formZeroSubmodule_ne_top L ind i
  · rintro x ⟨i, hi⟩
    refine ⟨formZeroSubmodule L i, ⟨i, rfl⟩, ?_⟩
    change (∑ j : σ, L i j * ((x j : ℚ) : ℂ)) = 0
    simpa using hi

end StageF

end Submission.Subspace
