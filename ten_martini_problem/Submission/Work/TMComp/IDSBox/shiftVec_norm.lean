import Mathlib
import Submission.Work.TMComp.IDSDefs

namespace Work.TMComp.IDSBox

/-- If `m.natAbs < R` then `m` is an index of the `n`-site box window shifted by `j`,
i.e. `m = k - j` for some `k : Fin n`, provided the window `[-j, n-1-j]` covers the
support window `[-(R-1), R-1]`. -/
private theorem exists_fin_of_natAbs_lt {R n : ℕ} {j m : ℤ}
    (hj : (R : ℤ) ≤ j + 1) (hj2 : j + (R : ℤ) + 1 ≤ (n : ℤ)) (hm : m.natAbs < R) :
    ∃ k : Fin n, (k : ℤ) - j = m := by
  have hb : -(R : ℤ) < m ∧ m < (R : ℤ) := by
    have h : |m| < (R : ℤ) := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast hm
    exact abs_lt.mp h
  obtain ⟨hl, hu⟩ := hb
  have hlow : 0 ≤ m + j := by omega
  have hhigh : m + j ≤ (n : ℤ) - 1 := by omega
  refine ⟨⟨(m + j).toNat, by omega⟩, ?_⟩
  rw [Fin.val_mk, Int.toNat_of_nonneg hlow]
  ring

theorem shiftVec_norm {R : ℕ} (φ : ℤ → ℂ)
    (hsupp : ∀ m : ℤ, R ≤ m.natAbs → φ m = 0)
    (hφ : (∑' m : ℤ, ‖φ m‖ ^ 2) = 1)
    (j : ℤ) (n : ℕ) (hj : (R : ℤ) ≤ j + 1) (hj2 : j + (R : ℤ) + 1 ≤ (n : ℤ)) :
    (∑ k : Fin n, ‖Work.TMComp.shiftVec φ j n k‖ ^ 2) = 1 := by
  let g : ℤ → ℝ := fun m => ‖φ m‖ ^ 2
  let e : Fin n → ℤ := fun k => (k : ℤ) - j
  let T : Finset ℤ := Finset.univ.image e
  have hinj : Set.InjOn e (Finset.univ : Finset (Fin n)) := by
    intro a _ b _ h
    simp only [e] at h
    have hab : (a : ℤ) = (b : ℤ) := by omega
    exact Fin.ext (Int.ofNat.inj hab)
  have hT : ∑ m ∈ T, g m = ∑ k : Fin n, g (e k) := by
    have h := Finset.sum_image (f := g) (s := (Finset.univ : Finset (Fin n))) (g := e) hinj
    simpa [T] using h
  have htsum : (∑' m : ℤ, g m) = ∑ m ∈ T, g m := by
    refine tsum_eq_sum (L := SummationFilter.unconditional ℤ) (f := g) (s := T) (fun m hm => ?_)
    have hnle : R ≤ m.natAbs := by
      by_contra hlt
      have hlt' : m.natAbs < R := not_le.mp hlt
      obtain ⟨k, hk⟩ := exists_fin_of_natAbs_lt hj hj2 hlt'
      exact hm (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
    simp [g, hsupp m hnle]
  have hstep : (∑ k : Fin n, ‖Work.TMComp.shiftVec φ j n k‖ ^ 2) = ∑ k : Fin n, g (e k) := by
    simp only [g, e, Work.TMComp.shiftVec]
  rw [hstep, hT.symm, htsum.symm]
  simpa [g] using hφ

end Work.TMComp.IDSBox
