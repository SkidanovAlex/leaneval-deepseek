import Mathlib
import Submission.Work.WilC4aAL.Defs
import Submission.Work.WilC4aAL.Basic
import Submission.Work.WilC4aAL.exists_cand_idx_of_root_cover

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aAL
open WilkiesDesign.CG.C4a

theorem analytic_sign_selection {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ}
    (hc : ∀ i j, AnalyticAt ℝ (c i j) 0)
    {m : Fin k → ℕ} {ζ : ∀ i, Fin (m i) → ℝ → ℝ}
    (hζ : AnalyticBranches m ζ) (hcov : BranchCover c m ζ) (σ : Fin k → SignType)
    (hwit : ∃ r₁ > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r₁, ∃ z : ℝ, SignVectorOk c σ r z) :
    ∃ ρ : ℝ → ℝ, AnalyticAt ℝ ρ 0 ∧ ∃ r₂ > (0 : ℝ), ∀ r ∈ Set.Ioo (0 : ℝ) r₂,
      SignVectorOk c σ r (ρ r) := by
  classical
  obtain ⟨r₀, hr₀pos, hr₀cov⟩ := hcov
  obtain ⟨r₁, hr₁pos, hr₁wit⟩ := hwit
  -- the branch family, bundled over `Σ i, Fin (m i)`
  let ξ : (Σ i : Fin k, Fin (m i)) → ℝ → ℝ := fun t => ζ t.1 t.2
  have hξ : ∀ t : Σ i : Fin k, Fin (m i), AnalyticAt ℝ (ξ t) 0 := fun t => hζ t.1 t.2
  -- a constant dominating all branches on a right-neighbourhood of `0`
  obtain ⟨C, ε₁, hε₁pos, hC⟩ := exists_bound_of_analytic ξ hξ
  -- for every candidate the sign vector is eventually constant
  have hstep : ∀ j : CandIdx (Σ i : Fin k, Fin (m i)),
      ∃ p : (Fin k → SignType) × ℝ, p.2 > 0 ∧ ∀ r ∈ Set.Ioo (0 : ℝ) p.2, ∀ i,
        SignType.sign (mpoly (c i) r (cand ξ C j r)) = p.1 i := by
    intro j
    obtain ⟨σ', hσ'⟩ := eventually_signVector_of_cand hc hξ C j
    obtain ⟨ε, hε, h⟩ := eventually_nhdsGT_iff_eps.mp hσ'
    exact ⟨(σ', ε), hε, h⟩
  choose p hp using hstep
  -- the finite minimum of the radii
  have hE : ∃ E > (0 : ℝ), ∀ j, E ≤ (p j).2 := by
    let S : Finset ℝ :=
      (Finset.univ : Finset (CandIdx (Σ i : Fin k, Fin (m i)))).image (fun j => (p j).2)
    have hSne : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    have hSpos : 0 < S.min' hSne := by
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finset.min'_mem S hSne)
      rw [← hj]; exact (hp j).1
    refine ⟨S.min' hSne, hSpos, fun j => ?_⟩
    exact Finset.min'_le S ((p j).2) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  obtain ⟨E, hEpos, hEle⟩ := hE
  -- a point strictly inside every relevant interval
  obtain ⟨rs, hrs_def⟩ : ∃ rs : ℝ, rs = min (min r₀ r₁) (min ε₁ E) / 2 := ⟨_, rfl⟩
  have hminpos : 0 < min (min r₀ r₁) (min ε₁ E) :=
    lt_min (lt_min hr₀pos hr₁pos) (lt_min hε₁pos hEpos)
  have hrs_pos : 0 < rs := by rw [hrs_def]; linarith
  have hrs_lt : rs < min (min r₀ r₁) (min ε₁ E) := by rw [hrs_def]; linarith
  have hrs_lt_r₀ : rs < r₀ :=
    lt_of_lt_of_le hrs_lt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hrs_lt_r₁ : rs < r₁ :=
    lt_of_lt_of_le hrs_lt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hrs_lt_ε₁ : rs < ε₁ :=
    lt_of_lt_of_le hrs_lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hrs_lt_E : rs < E :=
    lt_of_lt_of_le hrs_lt (le_trans (min_le_right _ _) (min_le_right _ _))
  -- a witness `z` for `σ` at `rs`
  obtain ⟨z, hz⟩ := hr₁wit rs ⟨hrs_pos, hrs_lt_r₁⟩
  -- the pointwise cell decomposition at `rs` provides a candidate carrying `σ`
  have hcov_rs : ∀ i (w : ℝ), mpoly (c i) rs w = 0 → ∃ j, w = ζ i j rs :=
    fun i w hw => hr₀cov rs ⟨hrs_pos, hrs_lt_r₀⟩ i w hw
  have hbd_rs : ∀ i j, |ζ i j rs| < C := by
    intro i j
    have h := hC rs ⟨hrs_pos, hrs_lt_ε₁⟩ (⟨i, j⟩ : Σ i : Fin k, Fin (m i))
    simpa [ξ] using h
  obtain ⟨j₀, hj₀⟩ :=
    exists_cand_idx_of_root_cover (C := C) (z := z) ζ hcov_rs hbd_rs
  have hGood : SignVectorOk c σ rs (cand ξ C j₀ rs) :=
    SignVectorOk.of_sameSign hj₀.symm hz
  -- since `rs < ε_{j₀}`, the candidate `j₀` carries `σ` on all of `(0, ε_{j₀})`
  have hrs_lt_p : rs < (p j₀).2 := lt_of_lt_of_le hrs_lt_E (hEle j₀)
  have hσeq : (p j₀).1 = σ := by
    funext i
    exact ((hp j₀).2 rs ⟨hrs_pos, hrs_lt_p⟩ i).symm.trans (hGood i)
  refine ⟨cand ξ C j₀, analyticAt_cand hξ C j₀, (p j₀).2, (hp j₀).1, ?_⟩
  intro r hr i
  exact ((hp j₀).2 r hr i).trans (congrFun hσeq i)

end Work.WilC4aAL
