import Mathlib
import Submission.Work.BW.basisRed_succMinL_mono

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A lattice vector of minimal norm outside a proper subspace

`Work.BW.basisRed_min_outside`: for a "lattice norm" `F` on `ℝⁿ` (see `Work.BW.IsLatticeNorm`)
and a proper subspace `W ⊊ ℝⁿ` there is an integer vector `v ∉ W` whose `F`-norm is minimal
among all integer vectors outside `W`.

The only point to observe is that `W ≠ ⊤` forces some lattice point to lie outside `W`
(otherwise the span `ℝⁿ` of `ℤⁿ` would be contained in `W`), and that `F` has finite sublevel
sets on the lattice, so the minimum is attained on the (nonempty, finite) set of lattice points
of norm at most the norm of one such point.
-/

namespace Work.BW

variable {n : ℕ}

/-- Some integer vector lies outside every proper subspace of `ℝⁿ`: since `ℤⁿ` spans `ℝⁿ` over
`ℝ`, a subspace containing the whole lattice is everything. -/
theorem basisRed_exists_intVec_notMem {W : Submodule ℝ (Fin n → ℝ)} (hW : W ≠ ⊤) :
    ∃ v : Fin n → ℤ, (fun i => (v i : ℝ)) ∉ W := by
  by_contra h
  push Not at h
  apply hW
  have hr : Set.range (fun k : Fin n => (Pi.single k (1:ℝ) : Fin n → ℝ)) ⊆ W := by
    rintro x ⟨k, rfl⟩
    change (Pi.single k (1:ℝ) : Fin n → ℝ) ∈ W
    have hsingle : (fun i => ((Pi.single k (1:ℤ) : Fin n → ℤ) i : ℝ))
        = (Pi.single k (1:ℝ) : Fin n → ℝ) := by
      ext i; simp [Pi.single_apply]
    rw [← hsingle]
    exact h _
  have hle : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ W := by
    rw [← basisRed_span_single_one_eq_top n]
    exact Submodule.span_le.mpr hr
  exact top_le_iff.mp hle

/-- A lattice vector of `F`-minimal norm among all lattice vectors outside a proper subspace. -/
theorem basisRed_min_outside {n : ℕ} {F : (Fin n → ℝ) → ℝ} (hF : Work.BW.IsLatticeNorm F)
    (W : Submodule ℝ (Fin n → ℝ)) (hW : W ≠ ⊤) :
    ∃ v : Fin n → ℤ, (fun i => (v i : ℝ)) ∉ W ∧
      ∀ w : Fin n → ℤ, (fun i => (w i : ℝ)) ∉ W →
        F (fun i => (v i : ℝ)) ≤ F (fun i => (w i : ℝ)) := by
  classical
  obtain ⟨v0, hv0⟩ := basisRed_exists_intVec_notMem (n := n) hW
  set t : ℝ := F (fun i => (v0 i : ℝ)) with ht
  have hfinite : ({v : Fin n → ℤ | F (fun i => (v i : ℝ)) ≤ t}).Finite := hF.finite t
  set s : Finset (Fin n → ℤ) :=
    hfinite.toFinset.filter (fun v => (fun i => (v i : ℝ)) ∉ W) with hs
  have hv0s : v0 ∈ s := by
    rw [hs, Finset.mem_filter, hfinite.mem_toFinset]
    exact ⟨le_of_eq ht.symm, hv0⟩
  obtain ⟨v, hvs, hvmin⟩ :=
    Finset.exists_min_image s (fun v : Fin n → ℤ => F (fun i => (v i : ℝ))) ⟨v0, hv0s⟩
  rw [hs, Finset.mem_filter, hfinite.mem_toFinset] at hvs
  simp only [Set.mem_ofPred_eq] at hvs
  obtain ⟨hvt, hvW⟩ := hvs
  refine ⟨v, hvW, ?_⟩
  intro w hw
  rcases lt_or_ge (F (fun i => (w i : ℝ))) t with hwt | hwt
  · exact hvmin w (by rw [hs, Finset.mem_filter, hfinite.mem_toFinset]; exact ⟨le_of_lt hwt, hw⟩)
  · linarith

end Work.BW
