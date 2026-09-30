import Mathlib
import Submission.Work.BW.Minkowski2.defs
import Submission.Work.BW.minkowski_defs
import Submission.Work.BW.Minkowski2.mem_latOf_one
import Submission.Work.BW.Minkowski2.succMinBody_interior
import Submission.Work.BW.Minkowski2.succMinBody_pos
import Submission.Work.BW.Minkowski2.succMinBody_mono
import Submission.Work.BW.Minkowski2.vol_preimage_transZ
import Submission.Work.BW.Minkowski2.exists_min_vecs
import Submission.Work.BW.Minkowski2.isAddFundamentalDomain_comap
import Submission.Work.BW.Minkowski2.gauge_mem_interior
import Submission.Work.BW.Minkowski2.succMinBody_comap_linearEquiv
import Submission.Work.BW.Minkowski2.core_aligned
import Submission.Work.BW.Minkowski2.flag_gauge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix Module
open scoped Pointwise

namespace Work.BW.Minkowski2

/-- **Minkowski's second inequality for the standard lattice `ℤᵈ`**: for a closed, bounded, convex
body `K` symmetric about the origin with nonempty interior,
`(∏ j : Fin d, succMinBody (latOf 1) K (j+1)) * volume.real K ≤ 2^d`.

The proof is the "aligned form + pullback" route.

* `Work.BW.Minkowski2.core_aligned` is Minkowski's second inequality in aligned form: for a lattice
  `Λ` with fundamental domain `F`, if the lattice points of `K`-gauge `< λ_{i+1}` lie in the
  coordinate subspace `{x | x m = 0, m ≥ i}`, then `∏ λ ⱼ * vol K ≤ 2^d * vol F`.
* `Work.BW.Minkowski2.flag_gauge` supplies that aligned hypothesis when the standard basis
  vectors `eᵢ ∈ Λ` realise the successive minima (`eᵢ ∈ succMinBody Λ K (i+1) • K`); it is the
  `gauge` form of `succMinBody_interior`, using
  `Work.BW.Minkowski2.mem_interior_smulSet_iff_gauge_lt`.
* For a general `K`, take the realising minimisers `v` of `Work.BW.Minkowski2.exists_min_vecs K`,
  the matrix `M i j = (v j i : ℝ)` and the change of variables `Work.BW.transZ z`. Pulling `K` and
  `ℤᵈ` back along it produces the pair `Λ' = Work.BW.latPull z (latOf 1)`, `K' = transZ z ⁻¹' K`
  for which the standard basis vectors are lattice points realising the successive minima, and whose
  successive minima agree with those of `K` with respect to `ℤᵈ`
  (`Work.BW.Minkowski2.succMinBody_comap_linearEquiv`).
* `Work.BW.Minkowski2.isAddFundamentalDomain_comap` provides a fundamental domain `Fr` for `Λ'`
  (the preimage of the standard half-open cube), while `Work.BW.Minkowski2.vol_preimage_transZ`
  computes `vol K' = vol K / |det M|` and `vol Fr = 1 / |det M|`; the factor `|det M|` cancels. -/
theorem minkowski_second_lattice {d : ℕ} (K : Set (Fin d → ℝ)) (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hKcl : IsClosed K) (hKbd : Bornology.IsBounded K)
    (hKi : (interior K).Nonempty) :
    (∏ j : Fin d, Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (j.1 + 1))
      * MeasureTheory.volume.real K ≤ (2 : ℝ) ^ d := by
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have huniv : MeasureTheory.volume.real (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      rw [MeasureTheory.Measure.real_def,
        show (MeasureTheory.volume : Measure (Fin 0 → ℝ)) =
          MeasureTheory.Measure.pi (fun _ : Fin 0 => (MeasureTheory.volume : Measure ℝ)) from
          MeasureTheory.volume_pi,
        MeasureTheory.Measure.pi_empty_univ]
      norm_num
    have hle : MeasureTheory.volume.real K ≤ 1 := by
      rw [← huniv]
      exact MeasureTheory.measureReal_mono (Set.subset_univ K)
    simpa using hle
  · obtain ⟨v, hvind, hvval⟩ := Work.BW.Minkowski2.exists_min_vecs K hKc hsym hKcl hKbd hKi
    set z : Fin d → Fin d → ℝ := fun j i => ((v j i : ℤ) : ℝ) with hzdef
    set M : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i j => z j i) with hMdef
    have hMcol : M.col = (fun i => fun j => ((v i j : ℤ) : ℝ)) := by
      funext i j
      rw [hMdef]
      rfl
    have hMdet : M.det ≠ 0 := by
      have hunit : IsUnit M :=
        Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hMcol]; exact hvind)
      exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hunit)
    let T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Work.BW.transZ z
    have hTmul : T = M.mulVecLin := by
      rw [hMdef]
      rfl
    have hTinj : Function.Injective T := by
      have h2 : ⇑(M.mulVecLin) = M.mulVec := by
        funext w; exact Matrix.mulVecLin_apply M w
      have h3 : ⇑T = M.mulVec := by rw [hTmul, h2]
      rw [h3]
      exact Matrix.mulVec_injective_of_det_ne_zero hMdet
    let e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) := LinearEquiv.ofInjectiveEndo T hTinj
    have hTe : ⇑e = ⇑T := LinearEquiv.coe_ofInjectiveEndo T hTinj
    have he : e.toLinearMap = T := LinearMap.ext (fun w => congrFun hTe w)
    set K' : Set (Fin d → ℝ) := T ⁻¹' K with hK'def
    set Λ' : Submodule ℤ (Fin d → ℝ) :=
      Work.BW.latPull z (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) with hΛ'def
    have hTz : Work.BW.transZ z = e.toLinearMap := by
      rw [show (Work.BW.transZ z : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) = T from rfl, he.symm]
    have hΛeq : Λ' = ZLattice.comap ℝ (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) e.toLinearMap := by
      rw [hΛ'def, Work.BW.latPull, hTz]
    have hlam_eq (j : ℕ) : Work.BW.succMinBody Λ' K' j =
        Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K j := by
      rw [hΛeq, hK'def, ← hTe]
      exact Work.BW.Minkowski2.succMinBody_comap_linearEquiv e
        (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K j
    have hstd : ∀ i : Fin d, Work.BW.stdVec i ∈ Λ' := by
      intro i
      rw [hΛ'def, Work.BW.mem_latPull, Work.BW.transZ_stdVec]
      exact (Work.BW.Minkowski2.mem_latOf_one (fun j => ((v i j : ℤ) : ℝ))).mpr ⟨v i, rfl⟩
    have hreal : ∀ i : Fin d, Work.BW.stdVec i ∈
        Work.BW.smulSet (Work.BW.succMinBody Λ' K' (i.1 + 1)) K' := by
      intro i
      have hvi := hvval i
      rw [← hlam_eq (i.1 + 1)] at hvi
      rw [hK'def, Work.BW.mem_smulSet] at hvi ⊢
      obtain ⟨k, hk, hk_eq⟩ := hvi
      refine ⟨e.symm k, ?_, ?_⟩
      · show T (e.symm k) ∈ K
        rw [← hTe]
        simpa using hk
      · apply hTinj
        rw [map_smul]
        have h1 : T (Work.BW.stdVec i) = (fun j => ((v i j : ℤ) : ℝ)) := by
          rw [Work.BW.transZ_stdVec]
        have h2 : T (e.symm k) = k := by
          rw [← hTe]
          simp
        rw [h2, h1, hk_eq]
    have hcomp := Work.BW.Minkowski2.isAddFundamentalDomain_comap T hTinj
    set Fr : Set (Fin d → ℝ) := T ⁻¹' ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)) with hFrdef
    have hF : MeasureTheory.IsAddFundamentalDomain Λ'.toAddSubgroup Fr MeasureTheory.volume := hcomp.1
    haveI : Countable Λ' := hcomp.2
    have hvolFr : MeasureTheory.volume.real Fr = 1 / |M.det| := by
      have h1 : MeasureTheory.volume.real Fr =
          MeasureTheory.volume.real (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) / |M.det| := by
        rw [hFrdef]
        exact Work.BW.Minkowski2.vol_preimage_transZ z hMdet _
      rw [h1, ZSpan.volume_real_fundamentalDomain (Pi.basisFun ℝ (Fin d))]
      have hmat : Matrix.of (⇑(Pi.basisFun ℝ (Fin d))) = (1 : Matrix (Fin d) (Fin d) ℝ) := by
        ext i j
        simp only [Matrix.of_apply, Pi.basisFun_apply, Matrix.one_apply, Pi.single_apply]
        by_cases h : i = j <;> simp [h, eq_comm]
      rw [hmat, Matrix.det_one]
      norm_num
    have hvolK : MeasureTheory.volume.real K' = MeasureTheory.volume.real K / |M.det| := by
      rw [hK'def]
      exact Work.BW.Minkowski2.vol_preimage_transZ z hMdet K
    have hfin : MeasureTheory.volume Fr ≠ ⊤ := by
      intro htop
      have h0 : MeasureTheory.volume.real Fr = 0 := by
        rw [MeasureTheory.Measure.real_def, htop]; simp
      rw [hvolFr] at h0
      exact (div_ne_zero one_ne_zero (abs_ne_zero.mpr hMdet)) h0
    have hK'c : Convex ℝ K' := by rw [hK'def]; exact hKc.linear_preimage T
    have hK'sym : ∀ x ∈ K', -x ∈ K' := by
      intro x hx
      rw [hK'def] at hx ⊢
      show T (-x) ∈ K
      rw [map_neg]
      exact hsym (T x) hx
    have hTcont : Continuous T := T.continuous_of_finiteDimensional
    have hK'cl : IsClosed K' := by rw [hK'def]; exact hKcl.preimage hTcont
    have hK'bd : Bornology.IsBounded K' := by
      have himg : K' = (fun x => e.symm x) '' K := by
        rw [hK'def]
        ext x
        constructor
        · intro hx
          exact ⟨T x, hx, by rw [← hTe]; exact e.symm_apply_apply x⟩
        · rintro ⟨k, hk, rfl⟩
          show T (e.symm k) ∈ K
          rw [← hTe]
          simpa using hk
      rw [himg]
      exact Bornology.IsBounded.image
        (e.symm.toContinuousLinearEquiv : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) hKbd
    have hK'i : (interior K').Nonempty := by
      obtain ⟨x, hx⟩ := hKi
      have hopen : IsOpen (T ⁻¹' interior K) := isOpen_interior.preimage hTcont
      have hsub : T ⁻¹' interior K ⊆ interior K' :=
        interior_maximal (fun y hy => by simpa [hK'def] using interior_subset hy) hopen
      refine ⟨e.symm x, hsub ?_⟩
      show T (e.symm x) ∈ interior K
      rw [← hTe]
      simpa using hx
    have hposK : ∀ i : Fin d, 0 < Work.BW.succMinBody Λ' K' (i.1 + 1) := fun i =>
      Work.BW.Minkowski2.succMinBody_pos Λ' K' hreal (by omega) (by omega)
    let lam : Fin (d+1) → ℝ :=
      Fin.cases (0:ℝ) (fun i : Fin d => Work.BW.succMinBody Λ' K' (i.1 + 1))
    have hlam0 : lam 0 = 0 := by
      change Fin.cases (0:ℝ) (fun i : Fin d => Work.BW.succMinBody Λ' K' (i.1 + 1))
        (0 : Fin (d+1)) = (0:ℝ)
      exact Fin.cases_zero
    have hlamS : ∀ i : Fin d, lam i.succ = Work.BW.succMinBody Λ' K' (i.1 + 1) := by
      intro i
      change Fin.cases (0:ℝ) (fun i : Fin d => Work.BW.succMinBody Λ' K' (i.1 + 1)) i.succ
        = Work.BW.succMinBody Λ' K' (i.1 + 1)
      exact Fin.cases_succ i
    have hcore := Work.BW.Minkowski2.core_aligned Λ' Fr hF hfin K' hK'c hK'sym hK'cl hK'bd hK'i
      lam hlam0
      (fun i => by rw [hlamS i]; exact hposK i)
      (fun i j hij => by
        rw [hlamS i, hlamS j]
        exact Work.BW.Minkowski2.succMinBody_mono Λ' K' (by omega) (ne_of_gt (hposK j)))
      (fun i w hw hg => by
        rw [hlamS i] at hg
        exact Work.BW.Minkowski2.flag_gauge Λ' K' hK'c hK'sym hK'i hstd hreal i w hw hg)
    have hprod : (∏ i : Fin d, lam i.succ)
        = ∏ j : Fin d, Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (j.1 + 1) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [hlamS i, hlam_eq (i.1 + 1)]
    have hmain : (∏ j : Fin d, Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (j.1 + 1))
        * (MeasureTheory.volume.real K / |M.det|) ≤ (2:ℝ)^d * (1 / |M.det|) := by
      rw [← hprod, ← hvolK, ← hvolFr]
      exact hcore
    have hD : 0 < |M.det| := abs_pos.mpr hMdet
    have hne : |M.det| ≠ 0 := ne_of_gt hD
    have hfinal := mul_le_mul_of_nonneg_right hmain (le_of_lt hD)
    have e1 : (∏ j : Fin d, Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (j.1 + 1))
        * (MeasureTheory.volume.real K / |M.det|) * |M.det|
        = (∏ j : Fin d, Work.BW.succMinBody (Work.BW.latOf (1 : Matrix (Fin d) (Fin d) ℤ)) K (j.1 + 1))
          * MeasureTheory.volume.real K := by
      rw [mul_assoc, div_mul_cancel₀ _ hne]
    have e2 : ((2:ℝ)^d * (1 / |M.det|)) * |M.det| = (2:ℝ)^d := by
      rw [mul_assoc, one_div, inv_mul_cancel₀ hne, mul_one]
    rw [e1, e2] at hfinal
    exact hfinal


end Work.BW.Minkowski2
