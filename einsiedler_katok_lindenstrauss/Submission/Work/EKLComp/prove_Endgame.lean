import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.isClosed_Thick
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.aDiag_conj_uij
import Submission.Work.EKLComp.Endgame_ae_orbit
import Submission.Work.EKLComp.Endgame_dense_rat
import Submission.Work.EKLComp.Endgame_diag_short

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is one component of the FROZEN EKL contract (Submission/Work/EKLContract/Defs.lean; the composition
ekl_of_components and the glue are PROVED, so proving all components closes the problem).

YOUR COMPONENT: C10 endgame (invariance + A-invariance contradicts compact support).

If `μ` is `A`-invariant and `U_ij`-invariant, then `μ (Thick ρ) ≠ 1`.  Suppose `μ (Thick ρ) = 1`.
The countable set `{aDiag q · u_ij r | q ∈ ℚ³, r ∈ ℚ}` is conull-orbiting, and its closure is the
whole group `A · U_ij` (whose elements are measure preserving), so the closed set
`{g | g • x ∈ Thick ρ}` contains all of `A · U_ij` for a suitable `x`.

Writing `x = k Γ₃`, some nonzero integral vector `m` satisfies `(k m)_j ≠ 0`.  A transvection
`u_ij(s)` with `s = -(k m)_i/(k m)_j` makes the `i`-th coordinate of `v = k m` vanish, and a
suitable diagonal `a = aDiag t` of determinant `1` rescales `v` so that every coordinate of
`a · u_ij(s) · v` is `≤ η < ρ`.  Hence `(a · u_ij(s)) • x` has a lattice vector of norm `< ρ`,
i.e. lies outside the closed `Thick ρ` — contradicting step 1.
-/

namespace Work.EKLComp

open MeasureTheory Filter Topology
open Work.EKLContract
open Work.EKLContract.Lemmas

/-- The projection `mkX : SL₃(ℝ) → X₃` is continuous. -/
theorem continuous_mkX : Continuous (mkX : SL3 → X3) := by
  rw [show (mkX : SL3 → X3) = QuotientGroup.mk from rfl]
  exact QuotientGroup.continuous_mk

/-- For `k : SL₃(ℝ)` and any row index `j` there is a nonzero integral vector `m` whose image
`k · m` has nonzero `j`-th coordinate: the row `j` of `k` is nonzero because `det k = 1`. -/
theorem intVec_exists (k : SL3) (j : Fin 3) :
    ∃ m : Fin 3 → ℤ, m ≠ 0 ∧
      Matrix.mulVec (toMat k) (fun l => (m l : ℝ)) j ≠ 0 := by
  obtain ⟨l, hl⟩ : ∃ l : Fin 3, toMat k j l ≠ 0 := by
    by_contra h
    push_neg at h
    have hdet : Matrix.det (toMat k) = 0 := Matrix.det_eq_zero_of_row_eq_zero j (by simpa using h)
    have hone : Matrix.det (toMat k) = 1 := by simpa [toMat] using Matrix.SpecialLinearGroup.det_coe k
    rw [hone] at hdet
    exact one_ne_zero hdet
  refine ⟨Pi.single l 1, ?_, ?_⟩
  · intro hzero
    have h1 := congr_fun hzero l
    simp [Pi.single_eq_same] at h1
  · have hvec : (fun l' : Fin 3 => ((Pi.single l (1 : ℤ) : Fin 3 → ℤ) l' : ℝ))
        = Pi.single l (1 : ℝ) := by
      funext l'
      by_cases h : l' = l
      · subst h; simp
      · rw [Pi.single_eq_of_ne' (Ne.symm h), Pi.single_eq_of_ne' (Ne.symm h), Int.cast_zero]
    rw [hvec, Matrix.mulVec_single_one]
    simpa [Matrix.col] using hl

theorem prove_Endgame : Work.EKLContract.P_Endgame := by
  intro μ hμ hA i j hij hU ρ hρ hthick
  haveI := hμ
  -- the complement of `Thick ρ` is null
  have hcompl : μ (Thick ρ)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (isClosed_Thick ρ).measurableSet, hthick]
    simp
  -- a point whose whole rational `A · U_ij`-orbit stays inside `Thick ρ`
  obtain ⟨x, hx⟩ := Endgame_ae_orbit μ hA i j hij hU (S := Thick ρ) hcompl
  -- represent the lattice `x` by a matrix
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective x
  -- a nonzero integral vector whose image has nonzero `j`-th coordinate
  obtain ⟨m, hm0, hmj⟩ := intVec_exists k j
  set v : Fin 3 → ℝ := Matrix.mulVec (toMat k) (fun l => (m l : ℝ)) with hv
  have hvj : v j ≠ 0 := by rw [hv]; exact hmj
  -- diagonal + transvection driving `v` below `ρ/2`
  obtain ⟨t, s, hbound⟩ := Endgame_diag_short hij v hvj (η := ρ / 2) (by linarith)
  -- the set of group elements keeping `x` in the closed set `Thick ρ` is closed
  have hcont : Continuous (fun g : SL3 => g • x) := by
    have h1 : (fun g : SL3 => g • x) = fun g : SL3 => mkX (g * k) := by
      funext g
      rw [← hk]
      exact mkX_mul g k
    rw [h1]
    exact continuous_mkX.comp (continuous_id.mul continuous_const)
  have hcl : IsClosed {g : SL3 | g • x ∈ Thick ρ} := (isClosed_Thick ρ).preimage hcont
  have hmem : (aDiag t * uij hij s) • x ∈ Thick ρ := by
    have hsub : Set.range (fun p : (Fin 3 → ℚ) × ℚ =>
        aDiag (fun k => (p.1 k : ℝ)) * uij hij (p.2 : ℝ)) ⊆ {g : SL3 | g • x ∈ Thick ρ} := by
      rintro g ⟨p, rfl⟩
      exact hx p
    have hdens : (aDiag t * uij hij s) ∈ closure (Set.range (fun p : (Fin 3 → ℚ) × ℚ =>
        aDiag (fun k => (p.1 k : ℝ)) * uij hij (p.2 : ℝ))) := by
      have hd := Endgame_dense_rat hij
      exact hd ⟨(t, s), rfl⟩
    exact (hcl.closure_subset_iff.mpr hsub) hdens
  -- but `(aDiag t * u_ij(s)) • x` has a lattice vector of norm `< ρ`, so it is not in `Thick ρ`
  have hnot : ¬ HasShortVec ((aDiag t * uij hij s) • x) ρ := hmem
  apply hnot
  refine ⟨(aDiag t * uij hij s) * k, ?_, m, hm0, ?_⟩
  · rw [← hk]
    exact mkX_mul (aDiag t * uij hij s) k
  · intro c
    have hle : |Matrix.mulVec (toMat ((aDiag t * uij hij s) * k))
        (fun l => (m l : ℝ)) c| ≤ ρ / 2 := by
      rw [toMat_mul, ← Matrix.mulVec_mulVec]
      exact hbound c
    exact lt_of_le_of_lt hle (by linarith)

end Work.EKLComp
