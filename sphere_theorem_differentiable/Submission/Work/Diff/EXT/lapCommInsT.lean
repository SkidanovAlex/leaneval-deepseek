import Mathlib
import Submission.Work.Diff.EXT.curvDefs
import Submission.Work.Diff.EXT.curvNormK_frame_indep
import Submission.Work.Diff.EXT.commBoundDefs
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.GE.contMDiff_rmP_fields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

local notation "Tf" => TField (I := I) (M := M)

/-! ## Elementary `Function.update` bookkeeping on `Fin (j+6)`

The tuple of the second sum of the target runs over `Fin (j+6)`, which is the two curvature slots
`0`, `1` followed by the `j+4`-tuple of the insertion.  These lemmas evaluate `Function.update`
and its composition with the shift `i ↦ i.succ.succ`. -/

private lemma upd_shift_succsucc {j : ℕ} (G : Fin (j + 6) → Tf) (r : Fin (j + 4)) (W : Tf) :
    (fun i : Fin (j + 4) => (Function.update G r.succ.succ W) i.succ.succ)
      = Function.update (fun i : Fin (j + 4) => G i.succ.succ) r W := by
  funext i
  simp only [Function.update_apply]
  by_cases h : i = r
  · subst h; simp
  · have h' : ¬ (i.succ.succ = r.succ.succ) := fun hh => h (Fin.succ_inj.mp (Fin.succ_inj.mp hh))
    simp [h, h']

private lemma upd_shift_zero {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) :
    (fun i : Fin (j + 4) => (Function.update G 0 W) i.succ.succ)
      = (fun i : Fin (j + 4) => G i.succ.succ) := by
  funext i
  simp only [Function.update_apply]
  rw [if_neg (Fin.succ_ne_zero i.succ)]

private lemma upd_shift_one {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) :
    (fun i : Fin (j + 4) => (Function.update G 1 W) i.succ.succ)
      = (fun i : Fin (j + 4) => G i.succ.succ) := by
  funext i
  simp only [Function.update_apply]
  rw [if_neg]
  intro hh
  exact Fin.succ_ne_zero i (Fin.succ_inj.mp (hh.trans Fin.succ_zero_eq_one.symm))

private lemma upd_val_zero_zero {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) :
    (Function.update G 0 W) 0 = W := by
  rw [Function.update_apply, if_pos rfl]

private lemma upd_val_zero_one {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) :
    (Function.update G 0 W) 1 = G 1 := by
  rw [Function.update_apply, if_neg]
  intro hh
  exact Fin.zero_ne_one hh.symm

private lemma upd_val_zero_ss {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) (s : Fin (j + 4)) :
    (Function.update G 0 W) s.succ.succ = G s.succ.succ := by
  rw [Function.update_apply, if_neg (Fin.succ_ne_zero s.succ)]

private lemma upd_val_one_zero {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) :
    (Function.update G 1 W) 0 = G 0 := by
  rw [Function.update_apply, if_neg Fin.zero_ne_one]

private lemma upd_val_one_one {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) :
    (Function.update G 1 W) 1 = W := by
  rw [Function.update_apply, if_pos rfl]

private lemma upd_val_one_ss {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) (s : Fin (j + 4)) :
    (Function.update G 1 W) s.succ.succ = G s.succ.succ := by
  rw [Function.update_apply, if_neg]
  intro hh
  exact Fin.succ_ne_zero s (Fin.succ_inj.mp (hh.trans Fin.succ_zero_eq_one.symm))

private lemma upd_val_ss_zero {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) (r : Fin (j + 4)) :
    (Function.update G r.succ.succ W) 0 = G 0 := by
  rw [Function.update_apply, if_neg]
  intro hh
  exact Fin.succ_ne_zero r.succ hh.symm

private lemma upd_val_ss_one {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) (r : Fin (j + 4)) :
    (Function.update G r.succ.succ W) 1 = G 1 := by
  rw [Function.update_apply, if_neg]
  intro hh
  exact Fin.succ_ne_zero r (Fin.succ_inj.mp (hh.symm.trans Fin.succ_zero_eq_one.symm))

private lemma upd_val_ss_same {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) (s : Fin (j + 4)) :
    (Function.update G s.succ.succ W) s.succ.succ = W := by
  rw [Function.update_apply, if_pos rfl]

private lemma upd_val_ss_ne {j : ℕ} (G : Fin (j + 6) → Tf) (W : Tf) {r s : Fin (j + 4)}
    (h : r ≠ s) : (Function.update G r.succ.succ W) s.succ.succ = G s.succ.succ := by
  rw [Function.update_apply, if_neg]
  intro hh
  exact h (Fin.succ_inj.mp (Fin.succ_inj.mp hh)).symm

private lemma upd_upd_self {ι : Type*} [DecidableEq ι] (F : ι → Tf) (i : ι) (X Y : Tf) :
    Function.update (Function.update F i X) i Y = Function.update F i Y := by
  funext k
  simp only [Function.update_apply]
  by_cases h : k = i <;> simp [h]

/-- `SmoothF` of a difference of fields (local copy of `Work.Diff.EXT.smoothF_sub'`). -/
private lemma smoothF_subT {A B : Tf} (hA : SmoothF A) (hB : SmoothF B) : SmoothF (A - B) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ B]
  exact smoothF_add hA (smoothF_smul (contMDiff_const (c := (-1 : ℝ))) hB)

/-- **The four-term linear combination of the tower in one slot.** -/
private lemma ckt_comb4 (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (j : ℕ) {F : Fin (j + 4) → Tf} (hF : ∀ s, SmoothF (F s)) (i : Fin (j + 4))
    (Z1 Z2 Z3 Z4 : Tf) (h1 : SmoothF Z1) (h2 : SmoothF Z2) (h3 : SmoothF Z3)
    (h4 : SmoothF Z4) (x : M) :
    ckt g j (Function.update F i Z1) x - ckt g j (Function.update F i Z2) x
      - ckt g j (Function.update F i Z3) x - ckt g j (Function.update F i Z4) x
      = ckt g j (Function.update F i (Z1 - Z2 - Z3 - Z4)) x := by
  have hT := tensProp_all hLC g j
  have hsub : ∀ (A B : Tf), SmoothF A → SmoothF B →
      ckt g j (Function.update F i (A - B))
        = ckt g j (Function.update F i A) - ckt g j (Function.update F i B) := by
    intro A B hA hB
    rw [show A - B = A + (-1 : ℝ) • B from by rw [neg_one_smul, sub_eq_add_neg]]
    rw [TensProp_add (hLC) (g) (k := j) hT (F := F) hF (s := i) (X := A) (Y := (-1 : ℝ) • B)
      hA (smoothF_smul (contMDiff_const (c := (-1 : ℝ))) hB)]
    rw [show ckt g j (Function.update F i ((-1 : ℝ) • B))
        = ((-1 : ℝ) • ckt g j (Function.update F i B)) from
      TensProp_smul (hLC) (g) (k := j) hT (F := F) hF (s := i) (-1) (X := B) hB]
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul]
    ring
  have hA := hsub (Z1 - Z2 - Z3) Z4 (smoothF_subT (smoothF_subT h1 h2) h3) h4
  have hB := hsub (Z1 - Z2) Z3 (smoothF_subT h1 h2) h3
  have hC := hsub Z1 Z2 h1 h2
  rw [hA, hB, hC]
  simp only [Pi.sub_apply]

theorem lapCommInsT
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (j : ℕ) (x : M)
    (e : Work.Diff.EXT.TField (I := I) (M := M))
    (he : Work.Diff.GE.SmoothFieldT (I := I) (M := M) e)
    (G : Fin (j + 6) → Work.Diff.EXT.TField (I := I) (M := M))
    (hG : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i))
    (s : Fin (j + 4)) :
    (∑ i : Fin (j + 4), Work.Diff.EXT.ckt g j (Function.update
        (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
          (fun z => LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g) (G 0) (G 1)
            (G s.succ.succ) z)) i
        (Work.Diff.EXT.dirF g ((Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
          (fun z => LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g) (G 0) (G 1)
            (G s.succ.succ) z)) i) e)) x)
      - (∑ q : Fin (j + 6), Work.Diff.EXT.ckt g j (Function.update (fun i : Fin (j + 4) =>
            (Function.update G q (Work.Diff.EXT.dirF g (G q) e)) i.succ.succ) s
          (fun z => LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g)
            ((Function.update G q (Work.Diff.EXT.dirF g (G q) e)) 0)
            ((Function.update G q (Work.Diff.EXT.dirF g (G q) e)) 1)
            ((Function.update G q (Work.Diff.EXT.dirF g (G q) e)) s.succ.succ) z)) x)
      = Work.Diff.EXT.ckt g j (Function.update (Function.update (fun i : Fin (j + 4) => G i.succ.succ) s
          (fun z => LeanEval.Geometry.SphereTheorem.curv (Submission.Diff.lcOf g) (G 0) (G 1)
            (G s.succ.succ) z)) s
          (Work.Diff.EXT.dCurvV (Submission.Diff.lcOf g) e (G 0) (G 1) (G s.succ.succ))) x := by
  classical
  obtain ⟨hcov0, htor, hmet⟩ := hLC g
  obtain ⟨hcov⟩ := hcov0
  -- ### naming the pieces
  set A : Work.Diff.EXT.TField (I := I) (M := M) := G 0 with hA
  set Bv : Work.Diff.EXT.TField (I := I) (M := M) := G 1 with hBv
  set TL : Fin (j + 4) → Work.Diff.EXT.TField (I := I) (M := M) := fun i => G i.succ.succ with hTL
  have hTLs : G s.succ.succ = TL s := by simp only [hTL]
  rw [hTLs]
  set R : Work.Diff.EXT.TField (I := I) (M := M) := fun z => curv (Submission.Diff.lcOf g) A Bv (TL s) z with hR
  set Tp : Fin (j + 4) → Work.Diff.EXT.TField (I := I) (M := M) := Function.update TL s R with hTp
  set F : Fin (j + 6) → ℝ := fun q => ckt g j (Function.update (fun i : Fin (j + 4) =>
      (Function.update G q (dirF g (G q) e)) i.succ.succ) s
      (fun z => curv (Submission.Diff.lcOf g) (Function.update G q (dirF g (G q) e) 0)
        (Function.update G q (dirF g (G q) e) 1)
        (Function.update G q (dirF g (G q) e) s.succ.succ) z)) x with hF
  set Kr : Fin (j + 4) → ℝ := fun r => ckt g j (Function.update Tp r (dirF g (Tp r) e)) x with hKr
  -- ### smoothness of the pieces
  have hAsm : SmoothF A := by rw [hA]; exact hG 0
  have hBsm : SmoothF Bv := by rw [hBv]; exact hG 1
  have hTLsm : ∀ i : Fin (j + 4), SmoothF (TL i) := by intro i; rw [hTL]; exact hG i.succ.succ
  have hUsm : SmoothF (TL s) := hTLsm s
  have hRsm : SmoothF R := by
    rw [hR]
    exact Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hAsm hBsm hUsm
  have hTpsm : ∀ i : Fin (j + 4), SmoothF (Tp i) := by
    intro i
    rw [hTp]
    exact smoothF_update hTLsm hRsm i
  have hdsm : ∀ Z : Work.Diff.EXT.TField (I := I) (M := M), SmoothF Z → SmoothF (dirF g Z e) :=
    fun Z hZ => dirF_smooth hLC g hZ he
  set B0 : ℝ := ckt g j (Function.update Tp s
      (fun z => curv (Submission.Diff.lcOf g) (dirF g A e) Bv (TL s) z)) x with hB0
  set B1 : ℝ := ckt g j (Function.update Tp s
      (fun z => curv (Submission.Diff.lcOf g) A (dirF g Bv e) (TL s) z)) x with hB1
  set B4 : ℝ := ckt g j (Function.update Tp s
      (fun z => curv (Submission.Diff.lcOf g) A Bv (dirF g (TL s) e) z)) x with hB4
  -- ### the four summand identities
  have hF0 : F 0 = ckt g j (Function.update Tp s
      (fun z => curv (Submission.Diff.lcOf g) (dirF g A e) Bv (TL s) z)) x := by
    rw [hF]
    beta_reduce
    rw [upd_shift_zero, upd_val_zero_zero, upd_val_zero_one, upd_val_zero_ss]
    rw [← hA, ← hBv, hTLs, ← hTL]
    have hft : ∀ Z : Work.Diff.EXT.TField (I := I) (M := M), Function.update TL s Z = Function.update Tp s Z := by
      intro Z
      simp only [hTp, upd_upd_self]
    rw [hft]
  have hF1 : F 1 = ckt g j (Function.update Tp s
      (fun z => curv (Submission.Diff.lcOf g) A (dirF g Bv e) (TL s) z)) x := by
    rw [hF]
    beta_reduce
    rw [upd_shift_one, upd_val_one_zero, upd_val_one_one, upd_val_one_ss]
    rw [← hA, ← hBv, hTLs, ← hTL]
    have hft : ∀ Z : Work.Diff.EXT.TField (I := I) (M := M), Function.update TL s Z = Function.update Tp s Z := by
      intro Z
      simp only [hTp, upd_upd_self]
    rw [hft]
  have hFs : F s.succ.succ = ckt g j (Function.update Tp s
      (fun z => curv (Submission.Diff.lcOf g) A Bv (dirF g (TL s) e) z)) x := by
    rw [hF]
    beta_reduce
    rw [upd_shift_succsucc, upd_val_ss_zero, upd_val_ss_one, upd_val_ss_same]
    rw [← hA, ← hBv, hTLs, ← hTL]
    have hft : ∀ Z : Work.Diff.EXT.TField (I := I) (M := M),
        Function.update (Function.update TL s (dirF g (TL s) e)) s Z
          = Function.update Tp s Z := by
      intro Z
      simp only [hTp, upd_upd_self]
    rw [hft]
  have hFr : ∀ r : Fin (j + 4), r ≠ s →
      F r.succ.succ = ckt g j (Function.update Tp r (dirF g (Tp r) e)) x := by
    intro r hrs
    have hTpr : (Function.update TL s R) r = G r.succ.succ := by
      rw [Function.update_of_ne hrs, hTL]
    rw [hF]
    beta_reduce
    rw [upd_shift_succsucc, upd_val_ss_zero, upd_val_ss_one, upd_val_ss_ne _ _ hrs]
    rw [← hA, ← hBv, hTLs, ← hR, ← hTL]
    have hft : Function.update (Function.update TL r (dirF g (G r.succ.succ) e)) s R
        = Function.update Tp r (dirF g (Tp r) e) := by
      rw [hTp]
      rw [Function.update_comm hrs]
      rw [hTpr]
    rw [hft]
  -- ### the summation
  rw [← hB0] at hF0
  rw [← hB1] at hF1
  rw [← hB4] at hFs
  have hsplit : (∑ q : Fin (j + 6), F q) = F 0 + (F 1 + ∑ r : Fin (j + 4), F r.succ.succ) := by
    rw [Fin.sum_univ_succ (f := F)]
    rw [Fin.sum_univ_succ (f := fun q : Fin (j + 5) => F q.succ)]
    rw [Fin.succ_zero_eq_one]
  have hred : (∑ r : Fin (j + 4), F r.succ.succ)
      = (∑ r : Fin (j + 4), Kr r) + (B4 - Kr s) := by
    have h1 : (∑ r : Fin (j + 4), (F r.succ.succ - Kr r)) = F s.succ.succ - Kr s := by
      refine Finset.sum_eq_single s ?_ ?_
      · intro r _ hrs
        rw [hFr r hrs]
        simp only [hKr]
        ring
      · intro hmem
        exact absurd (Finset.mem_univ s) hmem
    rw [hFs] at h1
    rw [Finset.sum_sub_distrib] at h1
    linarith
  -- ### the value identity for the curvature insertion
  have hZvalue : dirF g (Tp s) e
        - (fun z => curv (Submission.Diff.lcOf g) (dirF g A e) Bv (TL s) z)
        - (fun z => curv (Submission.Diff.lcOf g) A (dirF g Bv e) (TL s) z)
        - (fun z => curv (Submission.Diff.lcOf g) A Bv (dirF g (TL s) e) z)
      = dCurvV (Submission.Diff.lcOf g) e A Bv (TL s) := by
    have hTps : Tp s = R := by rw [hTp, Function.update_apply, if_pos rfl]
    rw [hTps, hR]
    funext y
    simp only [dCurvV, dirF, Pi.sub_apply]
    abel
  -- ### the four-term combination
  have hcomb : ckt g j (Function.update Tp s (dirF g (Tp s) e)) x
        - ckt g j (Function.update Tp s
            (fun z => curv (Submission.Diff.lcOf g) (dirF g A e) Bv (TL s) z)) x
        - ckt g j (Function.update Tp s
            (fun z => curv (Submission.Diff.lcOf g) A (dirF g Bv e) (TL s) z)) x
        - ckt g j (Function.update Tp s
            (fun z => curv (Submission.Diff.lcOf g) A Bv (dirF g (TL s) e) z)) x
      = ckt g j (Function.update Tp s (dCurvV (Submission.Diff.lcOf g) e A Bv (TL s))) x := by
    rw [ckt_comb4 hLC g j hTpsm s (dirF g (Tp s) e)
      (fun z => curv (Submission.Diff.lcOf g) (dirF g A e) Bv (TL s) z)
      (fun z => curv (Submission.Diff.lcOf g) A (dirF g Bv e) (TL s) z)
      (fun z => curv (Submission.Diff.lcOf g) A Bv (dirF g (TL s) e) z)
      (hdsm _ (hTpsm s))
      (Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov (hdsm A hAsm) hBsm hUsm)
      (Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hAsm (hdsm Bv hBsm) hUsm)
      (Work.Diff.GE.contMDiff_curv_fields (Submission.Diff.lcOf g) hcov hAsm hBsm (hdsm (TL s) hUsm))
      x]
    rw [hZvalue]
  -- ### assembly
  rw [hsplit, hF0, hF1, hred]
  have harith : (∑ r : Fin (j + 4), Kr r)
        - (B0 + (B1 + ((∑ r : Fin (j + 4), Kr r) + (B4 - Kr s))))
      = ckt g j (Function.update Tp s (dirF g (Tp s) e)) x - B0 - B1 - B4 := by
    simp only [hKr]
    ring
  rw [harith, hB0, hB1, hB4]
  exact hcomb

end Work.Diff.EXT
