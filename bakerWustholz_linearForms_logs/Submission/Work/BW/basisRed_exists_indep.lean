import Mathlib
import Submission.Work.BW.basisRed_defs
import Submission.Work.BW.basisRed_succMinL_mono

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Existence of an `F`-reduced independent family of lattice vectors

For a "lattice norm" `F` on `ℝⁿ` (see `Work.BW.IsLatticeNorm`) there is a family
`u 0, …, u (n-1)` of lattice vectors that is `ℝ`-linearly independent and whose `F`-norms are
bounded by the successive minima: `F (u k) ≤ succMinL F (k+1)`.

The construction is the greedy one: `u k` minimises `F` among the lattice points outside the span
of `u 0, …, u (k-1)`.  The minimising property forces `F (u k)` to be at most the `(k+1)`-st
successive minimum `λ_{k+1} = succMinL F (k+1)`: if `F (u k) > λ_{k+1}` then some level `t` below
`F (u k)` and strictly above `λ_{k+1}` has the property that the lattice points of `F`-norm at
most `t` span a subspace of dimension `> k`, hence some such point lies outside the span of
`u 0, …, u (k-1)`, contradicting minimality.
-/

namespace Work.BW

variable {n : ℕ}

/-- The real vector underlying an integer vector (the inclusion `ℤⁿ ↪ ℝⁿ`). -/
def castVec {n : ℕ} (v : Fin n → ℤ) : Fin n → ℝ := fun i => (v i : ℝ)

theorem castVec_injective : Function.Injective (castVec (n := n)) := by
  intro a b h
  funext i
  have h' := congrFun h i
  simp only [castVec] at h'
  exact_mod_cast h'

/-- If all lattice points of `F`-norm at most `t` lie in a subspace `W`, then so does their span. -/
theorem succSpanL_le_of_mem {F : (Fin n → ℝ) → ℝ} {t : ℝ} {W : Submodule ℝ (Fin n → ℝ)}
    (h : ∀ v : Fin n → ℤ, F (castVec v) ≤ t → castVec v ∈ W) : basisRed_succSpanL F t ≤ W := by
  rw [basisRed_succSpanL, Submodule.span_le]
  rintro x ⟨⟨v, rfl⟩, hx⟩
  exact h v hx

/-! ## Lattice points outside a proper subspace -/

/-- For a proper subspace `W` there is always a lattice point outside `W`. -/
theorem exists_latticeVec_not_mem {F : (Fin n → ℝ) → ℝ} (hF : IsLatticeNorm F)
    {W : Submodule ℝ (Fin n → ℝ)} (hW : W ≠ ⊤) : ∃ v : Fin n → ℤ, castVec v ∉ W := by
  by_contra h
  simp only [not_exists, not_not] at h
  obtain ⟨t, ht⟩ := basisRed_succSetL_nonempty (F := F) hF (le_refl n)
  have htop : basisRed_succSpanL F t = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Module.finrank_fin_fun]
    have h1 : Module.finrank ℝ (basisRed_succSpanL F t) ≤ n := by
      have h2 := Submodule.finrank_le (basisRed_succSpanL F t)
      rwa [Module.finrank_fin_fun] at h2
    have h3 : n ≤ Module.finrank ℝ (basisRed_succSpanL F t) := ht
    omega
  have hle : basisRed_succSpanL F t ≤ W := succSpanL_le_of_mem (fun v _ => h v)
  rw [htop] at hle
  exact hW (top_le_iff.mp hle)

/-- Among the lattice points outside a proper subspace `W` there is one of minimal `F`-norm. -/
theorem exists_min_outside {F : (Fin n → ℝ) → ℝ} (hF : IsLatticeNorm F)
    (W : Submodule ℝ (Fin n → ℝ)) (hW : W ≠ ⊤) :
    ∃ v : Fin n → ℤ, castVec v ∉ W ∧
      ∀ w : Fin n → ℤ, castVec w ∉ W → F (castVec v) ≤ F (castVec w) := by
  classical
  obtain ⟨v0, hv0⟩ := exists_latticeVec_not_mem (F := F) hF hW
  have hT : ({w : Fin n → ℤ | F (castVec w) ≤ F (castVec v0)}).Finite := hF.finite _
  set s : Finset (Fin n → ℤ) := hT.toFinset.filter (fun w => castVec w ∉ W) with hs
  have hv0s : v0 ∈ s := by
    rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨Set.mem_ofPred.mpr le_rfl, hv0⟩
  obtain ⟨v, hvs, hvmin⟩ := Finset.exists_min_image s (fun w => F (castVec w)) ⟨v0, hv0s⟩
  have hvs' := hvs
  rw [hs, Finset.mem_filter] at hvs'
  have hvle : F (castVec v) ≤ F (castVec v0) := by
    have h1 : v ∈ hT.toFinset := hvs'.1
    exact Set.mem_ofPred.mp ((Set.Finite.mem_toFinset hT).mp h1)
  refine ⟨v, hvs'.2, fun w hw => ?_⟩
  rcases le_or_gt (F (castVec w)) (F (castVec v0)) with hle | hlt
  · refine hvmin w ?_
    rw [hs, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨Set.mem_ofPred.mpr hle, hw⟩
  · linarith

/-- If `succMinL F j < c` with `1 ≤ j ≤ n`, some level `t` of the successive-minimum level set
`basisRed_succSetL F j` lies strictly below `c`. -/
theorem exists_level_lt {F : (Fin n → ℝ) → ℝ} (hF : IsLatticeNorm F) {j : ℕ}
    (hj1 : 1 ≤ j) (hjn : j ≤ n) {c : ℝ} (hc : succMinL F j < c) :
    ∃ t ∈ basisRed_succSetL F j, t < c := by
  rw [basisRed_succMinL_eq_sInf] at hc
  exact (csInf_lt_iff ⟨0, fun t ht => basisRed_succSetL_nonneg hF hj1 ht⟩
    (basisRed_succSetL_nonempty hF hjn)).mp hc

/-! ## The crux -/

/-- A lattice vector minimising `F` outside a proper subspace `W` has `F`-norm at most the
`(dim W + 1)`-st successive minimum. -/
theorem min_outside_le_succMinL {F : (Fin n → ℝ) → ℝ} (hF : IsLatticeNorm F)
    (W : Submodule ℝ (Fin n → ℝ)) (hW : Module.finrank ℝ W < n) {v : Fin n → ℤ}
    (hmin : ∀ w : Fin n → ℤ, castVec w ∉ W → F (castVec v) ≤ F (castVec w)) :
    F (castVec v) ≤ succMinL F (Module.finrank ℝ W + 1) := by
  by_contra hc
  rw [not_le] at hc
  obtain ⟨t, htS, htc⟩ := exists_level_lt hF (j := Module.finrank ℝ W + 1)
    (by omega) (by omega) hc
  have hle : basisRed_succSpanL F t ≤ W :=
    succSpanL_le_of_mem (fun w hw => by
      by_contra hwW
      have h1 := hmin w hwW
      linarith)
  have h1 : Module.finrank ℝ W + 1 ≤ Module.finrank ℝ (basisRed_succSpanL F t) := htS
  have h2 : Module.finrank ℝ (basisRed_succSpanL F t) ≤ Module.finrank ℝ W :=
    Submodule.finrank_mono hle
  omega

/-! ## The theorem -/

theorem basisRed_exists_indep {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F) :
    ∃ u : Fin n → (Fin n → ℤ),
      LinearIndependent ℝ (fun k : Fin n => (fun i => ((u k) i : ℝ))) ∧
      ∀ k : Fin n, F (fun i => ((u k) i : ℝ)) ≤ Work.BW.succMinL F (k.1 + 1) := by
  have key : ∀ k : ℕ, k ≤ n → ∃ v : Fin k → (Fin n → ℤ),
      LinearIndependent ℝ (fun i : Fin k => castVec (v i)) ∧
      ∀ i : Fin k, F (castVec (v i)) ≤ succMinL F (i.1 + 1) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨v, hvind, hvbd⟩ := ih (by omega)
      set W : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range (fun i : Fin k => castVec (v i)))
        with hWdef
      have hfrW : Module.finrank ℝ W = k := by
        rw [hWdef, finrank_span_eq_card hvind, Fintype.card_fin]
      have hne : W ≠ ⊤ := by
        intro htop
        have h2 : Module.finrank ℝ W = n := by
          rw [htop, finrank_top, Module.finrank_fin_fun]
        omega
      obtain ⟨w, hwW, hwmin⟩ := exists_min_outside hF W hne
      have hwbd : F (castVec w) ≤ succMinL F (k + 1) := by
        have h := min_outside_le_succMinL hF W (by omega) hwmin
        simpa [hfrW] using h
      refine ⟨Fin.snoc v w, ?_, ?_⟩
      · have hsnoc : (fun i : Fin (k + 1) => castVec ((Fin.snoc v w : Fin (k + 1) → (Fin n → ℤ)) i))
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
          exact hvbd j
        · rw [Fin.snoc_last, Fin.val_last]
          exact hwbd
  obtain ⟨u, hu, hub⟩ := key n le_rfl
  exact ⟨u, hu, hub⟩

end Work.BW
