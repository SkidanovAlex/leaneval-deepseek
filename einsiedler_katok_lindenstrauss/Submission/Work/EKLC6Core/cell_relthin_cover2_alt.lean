import Mathlib
import Submission.Work.EKLC6Core.cell_relthin_cover2
import Submission.Work.EKLC6Core.cellBall_cover
import Submission.Work.EKLC6Core.sel_counting_sum
import Submission.Work.EKLC6Core.bad_subset_shells_alt

/-!
# `Work.EKLC6Core.cell_relthin_cover2_alt`

The statement of `Work.EKLC6Core.cell_relthin_cover2` proved from the three ingredient lemmas
`cellBall_cover`, `sel_counting_sum` and `bad_subset_shells_alt` (which are proved in their
own modules).  The body is the author's proof of `cell_relthin_cover2`, with the three `tmp…` stubs of
`Submission/Work/EKLC6Core/cell_relthin_cover2.lean` replaced by those lemmas; it exists so that
consumers are not blocked while the stub modules are replaced inside
`cell_relthin_cover2.lean` itself.
-/

namespace Work.EKLC6Core

open MeasureTheory
open Work.EKLContract

theorem cell_relthin_cover2_alt {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] :
    ∃ (Q : ℕ → Set Work.EKLContract.X3) (δ : ℕ → ℝ) (g : ℕ → Work.EKLContract.SL3)
      (C α : ℝ),
      (∀ k, IsOpen (Q k)) ∧ (∀ k l, k ≠ l → Disjoint (Q k) (Q l)) ∧
      μ (Set.iUnion (fun k : ℕ => Q k))ᶜ = 0 ∧
      (∀ k, 0 < δ k ∧ δ k ≤ 1 / 16) ∧
      (∀ k, Q k ⊆ (fun v : Work.EKLContract.SL3 => v • Work.EKLContract.mkX (g k)) ''
        (Work.EKLContract.V (δ k / 2))) ∧
      (∀ k (v₁ v₂ : Work.EKLContract.SL3), v₁ ∈ Work.EKLContract.V (4 * δ k) →
        v₂ ∈ Work.EKLContract.V (4 * δ k) →
        v₁ • Work.EKLContract.mkX (g k) = v₂ • Work.EKLContract.mkX (g k) → v₁ = v₂) ∧
      0 < C ∧ 0 < α ∧
      ∀ ε : ℝ, 0 < ε → μ {y : Work.EKLContract.X3 |
          ∀ k, y ∈ Q k → Work.EKLC6Core.cellMargin Q k y < ε * Work.EKLC6Core.injCap y}
        ≤ ENNReal.ofReal (C * ε ^ α) := by
  classical
  haveI hfin : MeasureTheory.IsFiniteMeasure μ := inferInstance
  obtain ⟨y, hy⟩ := exists_dense_seq_X3
  have hcover : ∀ z : X3, ∃ n : ℕ, n ∈ sel y ∧ z ∈ cellBall μ y n :=
    fun z => cellBall_cover μ y hy z
  have hcovU : (⋃ n, cellBall μ y n) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨n, -, hn⟩ := hcover z
    exact ⟨n, hn⟩
  obtain ⟨Msum, hMpos, hsum⟩ := sel_counting_sum μ y hy
  set Cc : ℝ := max (32 * deltac * Msum) (1 / epsZero) with hCc
  set g : ℕ → SL3 := fun k => Classical.choose (QuotientGroup.mk_surjective (y k)) with hgdef
  have hgmk : ∀ k, mkX (g k) = y k := fun k =>
    Classical.choose_spec (QuotientGroup.mk_surjective (y k))
  refine ⟨Qcell μ y, fun k => 2 * cellRad μ y k, g, Cc, 1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact Qcell_open μ y k
  · intro k l hkl; exact Qcell_disjoint μ y k l hkl
  · exact Qcell_conull μ y hcovU
  · intro k
    refine ⟨by have := cellRad_pos_all μ y k; linarith, ?_⟩
    have h1 : cellRad μ y k ≤ cellHi (y k) := cellRad_le_cellHi_all μ y k
    have h2 : cellHi (y k) ≤ 1 / 4096 := cellHi_le (y k)
    linarith
  · intro k z hz
    have hsub : z ∈ cellBall μ y k := Qcell_subset μ y k hz
    by_cases hk : k ∈ sel y
    · rw [cellBall_eq hk] at hsub
      obtain ⟨u, hu, huz⟩ := hsub
      refine ⟨u, ?_, ?_⟩
      · show u ∈ Work.EKLContract.V ((2 * cellRad μ y k) / 2)
        rwa [show (2 * cellRad μ y k) / 2 = cellRad μ y k by ring]
      · show u • mkX (g k) = z
        rw [hgmk k]
        exact huz
    · rw [cellBall_eq_empty hk] at hsub
      exact hsub.elim
  · intro k v₁ v₂ h₁ h₂ heq
    have h1 : v₁ ∈ Work.EKLContract.V (8 * cellRad μ y k) := by
      rw [show 4 * (2 * cellRad μ y k) = 8 * cellRad μ y k by ring] at h₁
      exact h₁
    have h2 : v₂ ∈ Work.EKLContract.V (8 * cellRad μ y k) := by
      rw [show 4 * (2 * cellRad μ y k) = 8 * cellRad μ y k by ring] at h₂
      exact h₂
    have hinj : InjAt (y k) (8 * cellRad μ y k) := by
      refine injAt_of_lt_injCap (by have := cellRad_pos_all μ y k; linarith) ?_
      have h3 : 8 * cellRad μ y k ≤ 8 * cellHi (y k) := by
        have := cellRad_le_cellHi_all μ y k; linarith
      have h4 : 8 * cellHi (y k) < injCap (y k) := by
        rw [cellHi]; have := injCap_pos (y k); linarith
      linarith
    have heq' : v₁ • y k = v₂ • y k := by
      rw [← hgmk k]
      exact heq
    exact hinj v₁ v₂ h1 h2 heq'
  · refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have : (0 : ℝ) < deltac := deltac_pos
    positivity
  · exact one_pos
  · intro ε hε
    by_cases hεs : ε ≤ epsZero
    · have hρ0 : 0 < deltac * ε := mul_pos deltac_pos hε
      have hρ1 : deltac * ε ≤ 1 := deltac_eps_le_one hεs
      have hsub : {w : X3 | ∀ k, w ∈ Qcell μ y k → cellMargin (Qcell μ y) k w < ε * injCap w}
          ⊆ (⋃ k, Qcell μ y k)ᶜ ∪ ⋃ j ∈ sel y, shell μ y (deltac * ε) j := by
        intro w hw
        by_cases hwU : w ∈ ⋃ k, Qcell μ y k
        · right
          obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hwU
          obtain ⟨j, hj, hjs⟩ := bad_subset_shells_alt μ y hcover hε hεs hk (hw k hk)
          exact Set.mem_iUnion₂.mpr ⟨j, hj, hjs⟩
        · left; exact hwU
      have hmono : μ (⋃ j ∈ sel y, shell μ y (deltac * ε) j)
          ≤ μ (⋃ j, selShell μ y (deltac * ε) j) := by
        refine measure_mono ?_
        intro w hw
        obtain ⟨j, hj, hwj⟩ := Set.mem_iUnion₂.mp hw
        exact Set.mem_iUnion.mpr ⟨j, by rw [selShell, if_pos hj]; exact hwj⟩
      have hunion : μ (⋃ j, selShell μ y (deltac * ε) j)
          ≤ ∑' j, μ (selShell μ y (deltac * ε) j) :=
        measure_iUnion_le (fun j => selShell μ y (deltac * ε) j)
      calc μ {w : X3 | ∀ k, w ∈ Qcell μ y k → cellMargin (Qcell μ y) k w < ε * injCap w}
          ≤ μ ((⋃ k, Qcell μ y k)ᶜ ∪ ⋃ j ∈ sel y, shell μ y (deltac * ε) j) :=
              measure_mono hsub
        _ ≤ μ ((⋃ k, Qcell μ y k)ᶜ) + μ (⋃ j ∈ sel y, shell μ y (deltac * ε) j) :=
              measure_union_le _ _
        _ = μ (⋃ j ∈ sel y, shell μ y (deltac * ε) j) := by
              rw [Qcell_conull μ y hcovU, zero_add]
        _ ≤ μ (⋃ j, selShell μ y (deltac * ε) j) := hmono
        _ ≤ ∑' j, μ (selShell μ y (deltac * ε) j) := hunion
        _ ≤ ∑' j, ENNReal.ofReal (32 * (deltac * ε)) * μ (countBall μ y j) :=
              ENNReal.tsum_le_tsum fun j => selShell_measure_le μ y hρ0 hρ1 j
        _ = ENNReal.ofReal (32 * (deltac * ε)) * ∑' j, μ (countBall μ y j) :=
              ENNReal.tsum_mul_left
        _ ≤ ENNReal.ofReal (32 * (deltac * ε)) * ENNReal.ofReal Msum :=
              mul_le_mul' le_rfl hsum
        _ = ENNReal.ofReal (32 * (deltac * ε) * Msum) :=
              (ENNReal.ofReal_mul
                (mul_nonneg (by norm_num : (0:ℝ) ≤ 32) (le_of_lt hρ0))).symm
        _ = ENNReal.ofReal ((32 * deltac * Msum) * ε) := by
              congr 1; ring
        _ ≤ ENNReal.ofReal (Cc * ε ^ (1:ℝ)) := by
              rw [Real.rpow_one, hCc]
              exact ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt hε))
    · have hεp : epsZero < ε := lt_of_not_ge hεs
      have hge : 1 < Cc * ε := by
        have hpos : 0 < 1 / epsZero := div_pos one_pos epsZero_pos
        have h1 : (1 / epsZero) * epsZero = 1 := by
          rw [div_mul_cancel₀ _ (ne_of_gt epsZero_pos)]
        have h2 : (1 / epsZero) * epsZero < (1 / epsZero) * ε :=
          mul_lt_mul_of_pos_left hεp hpos
        calc (1 : ℝ) = (1 / epsZero) * epsZero := h1.symm
          _ < (1 / epsZero) * ε := h2
          _ ≤ Cc * ε := by
              rw [hCc]
              exact mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hε)
      calc μ {w : X3 | ∀ k, w ∈ Qcell μ y k → cellMargin (Qcell μ y) k w < ε * injCap w}
          ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
        _ ≤ ENNReal.ofReal (Cc * ε ^ (1:ℝ)) := by
            rw [← ENNReal.ofReal_one, Real.rpow_one]
            exact ENNReal.ofReal_le_ofReal (le_of_lt hge)



end Work.EKLC6Core
