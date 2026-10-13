/-
  WilE9G / Amb — the dictionary between the frozen ambient strata `Stratum 0 N` and the
  ambient strata `AmbStratum N` used by the `G1`/`G3` statements.

  `Stratum 0 N` carries a semi-Pfaffian set in `ℝ^{0+N}`; `AmbStratum N` carries one in `ℝ^N`.
  The two ambient dimensions are canonically isomorphic (`Fin.cast (Nat.zero_add N)`,
  which is *not* definitional), so the transport is the coordinate reindexing
  `Work.WilE7.SemiPf.reindex (finCongr (Nat.zero_add N))` together with the same renaming
  of the equations `h`.

  The only mathematical content is that the `Good` condition is transported: the symbolic
  derivative `eaD` commutes with the reindexing (`reindex_eaD`), whence the Jacobian matrices
  of the two strata agree entrywise and the locality conditions correspond under the
  (continuous) coordinate relabelling.
-/
import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9.Sharp.SemiPf_castFin_set

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Filter MeasureTheory

namespace Work.WilE9G.Amb

open WilkiesDesign WilkiesDesign.E

/-! ## The coordinate equivalence `Fin (0 + N) ≃ Fin N` -/

/-- The value-preserving equivalence between `Fin (0 + N)` and `Fin N`.  Its `toFun` is
literally `Fin.cast (Nat.zero_add N)`, its `symm` is `Fin.natAdd 0`. -/
def castEquiv (N : ℕ) : Fin (0 + N) ≃ Fin N := finCongr (Nat.zero_add N)

theorem castEquiv_symm_apply_natAdd (N : ℕ) (l : Fin N) :
    (castEquiv N).symm l = Fin.natAdd 0 l := by
  show Fin.cast (Nat.zero_add N).symm l = Fin.natAdd 0 l
  rw [Fin.natAdd_zero]

/-- The fibre of the base projection in dimension `0` is a single point, so the vacuous
Cauchy condition `projFirst 0 N z' = projFirst 0 N z` of `Stratum.Good` is automatic. -/
theorem projFirst_zero_eq {N : ℕ} (w w' : Fin (0 + N) → ℝ) :
    projFirst 0 N w = projFirst 0 N w' :=
  funext fun i => i.elim0

/-! ## The symbolic derivative commutes with a coordinate reindexing -/

/-- `eaD` commutes with the coordinate reindexing of `Work.WilE7`: the derivative of a
renamed polynomial in a renamed direction is the rename of the derivative in the
corresponding direction. -/
theorem reindex_eaD {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r) (Q : EAPoly k r)
    (l : Fin K) :
    Work.WilE7.EAPoly.reindex e (eaD c (e.symm l) Q) =
      eaD (Work.WilE7.EAChain.reindex e c) l (Work.WilE7.EAPoly.reindex e Q) := by
  have hinj : Function.Injective (Sum.map e id : Fin k ⊕ Fin r → Fin K ⊕ Fin r) := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (e.injective (Sum.inl.inj h))
      | inr b => exact absurd h Sum.inl_ne_inr
    | inr a =>
      cases b with
      | inl b => exact absurd h Sum.inr_ne_inl
      | inr b => simpa using h
  simp only [eaD, Work.WilE7.EAPoly.reindex, Work.WilE7.EAChain.reindex, map_add, map_sum]
  rw [← MvPolynomial.pderiv_rename hinj (Sum.inl (e.symm l)) Q]
  simp only [Sum.map_inl, Equiv.apply_symm_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X, Sum.map_inr, id_eq,
    ← MvPolynomial.pderiv_rename hinj (Sum.inr j) Q]

/-- The evaluated form of `reindex_eaD`: the reindexed Jacobian entry at a reindexed point
is the original Jacobian entry at the point obtained by the coordinate relabelling. -/
theorem eaEval_reindex_eaD {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r) (Q : EAPoly k r)
    (l : Fin K) (y : Fin K → ℝ) :
    eaEval (Work.WilE7.EAChain.reindex e c)
        (eaD (Work.WilE7.EAChain.reindex e c) l (Work.WilE7.EAPoly.reindex e Q)) y =
      eaEval c (eaD c (e.symm l) Q) (fun i => y (e i)) := by
  rw [← reindex_eaD e c Q l, Work.WilE7.eaEval_reindex]

/-! ## The Jacobian matrix of the reindexed stratum -/

/-- The Jacobian matrix of the reindexed ambient stratum, read at `y`, is the Jacobian
matrix of the frozen stratum read at the reindexed point `i ↦ y (Fin.cast (Nat.zero_add N) i)`. -/
theorem reindexMatrix_eq {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) (y : Fin N → ℝ) :
    (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
      eaEval (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c)
        (eaD (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c) l
          (Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a))) y) =
    (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a))
        (fun i : Fin (0 + N) => y (castEquiv N i))) := by
  have hfun : (fun (a : Fin S.j) (l : Fin N) =>
      eaEval (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c)
        (eaD (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c) l
          (Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a))) y) =
      (fun (a : Fin S.j) (l : Fin N) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a))
          (fun i : Fin (0 + N) => y (castEquiv N i))) := by
    funext a l
    rw [eaEval_reindex_eaD (castEquiv N) S.X.c (S.h a) l y, castEquiv_symm_apply_natAdd]
  rw [hfun]

/-! ## The Jacobian matrix of the reindexed stratum, as a formula -/

/-- The matrix entry of the reindexed stratum coincides with the corresponding entry of the
frozen stratum, in the pointwise form used below. -/
theorem reindexMatrix_eq_apply {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) (y : Fin N → ℝ)
    (a : Fin S.j) (l : Fin N) :
    eaEval (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c)
        (eaD (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c) l
          (Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a))) y =
      eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a))
        (fun i : Fin (0 + N) => y (castEquiv N i)) := by
  rw [eaEval_reindex_eaD (castEquiv N) S.X.c (S.h a) l y, castEquiv_symm_apply_natAdd]

/-! ## The two directions of the transport of `Good` -/

/-- If the reindexed ambient stratum is `Good`, then so is the frozen stratum. -/
theorem good_fwd {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    (AmbStratum.Good ⟨Work.WilE7.SemiPf.reindex (castEquiv N) S.X, S.j,
        fun a => Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a)⟩) →
      WilkiesDesign.E.Stratum.Good S := by
  intro hG
  simp only [AmbStratum.Good] at hG
  intro z hz
  have hset : (Work.WilE7.SemiPf.reindex (castEquiv N) S.X).set =
      {y : Fin N → ℝ | (fun i : Fin (0 + N) => y (castEquiv N i)) ∈ S.X.set} :=
    Work.WilE7.reindex_eval.2 (castEquiv N) S.X
  set y : Fin N → ℝ := fun i => z ((castEquiv N).symm i) with hy
  have hyz : (fun i : Fin (0 + N) => y (castEquiv N i)) = z := by
    funext i
    rw [hy]
    exact congrArg z (Equiv.symm_apply_apply (castEquiv N) i)
  have hymem : y ∈ (Work.WilE7.SemiPf.reindex (castEquiv N) S.X).set := by
    rw [hset, Set.mem_ofPred_eq, hyz]
    exact hz
  have hg := hG y hymem
  refine ⟨?_, ?_, ?_⟩
  · intro a
    have h : eaEval (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c)
        (Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a)) y = 0 := hg.1 a
    rw [Work.WilE7.eaEval_reindex, hyz] at h
    exact h
  · have hrank := hg.2.1
    have hmat := reindexMatrix_eq S y
    rw [hyz] at hmat
    rw [← hmat]
    exact hrank
  · have hEv := hg.2.2
    have hcont : Continuous
        (fun w : Fin (0 + N) → ℝ => fun i : Fin N => w ((castEquiv N).symm i)) := by
      rw [continuous_pi_iff]
      intro i
      exact continuous_apply _
    have htend : Tendsto (fun w : Fin (0 + N) → ℝ => fun i : Fin N => w ((castEquiv N).symm i))
        (𝓝 z) (𝓝 y) := hcont.continuousAt
    filter_upwards [htend.eventually hEv] with z' hz'
    intro _ h0
    have h1 : (fun i : Fin (0 + N) =>
        (fun j : Fin N => z' ((castEquiv N).symm j)) (castEquiv N i)) = z' := by
      funext i
      exact congrArg z' (Equiv.symm_apply_apply (castEquiv N) i)
    have h2 : (∀ a, eaEval (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c)
        (Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a))
          (fun j : Fin N => z' ((castEquiv N).symm j)) = 0) := by
      intro a
      rw [Work.WilE7.eaEval_reindex, h1]
      exact h0 a
    have h3 := hz' h2
    rw [hset, Set.mem_ofPred_eq] at h3
    rwa [h1] at h3

/-- If the frozen stratum is `Good`, then so is the reindexed ambient stratum. -/
theorem good_bwd {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    WilkiesDesign.E.Stratum.Good S →
      (AmbStratum.Good ⟨Work.WilE7.SemiPf.reindex (castEquiv N) S.X, S.j,
        fun a => Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a)⟩) := by
  intro hG y hy
  have hset : (Work.WilE7.SemiPf.reindex (castEquiv N) S.X).set =
      {y : Fin N → ℝ | (fun i : Fin (0 + N) => y (castEquiv N i)) ∈ S.X.set} :=
    Work.WilE7.reindex_eval.2 (castEquiv N) S.X
  rw [hset, Set.mem_ofPred_eq] at hy
  set z : Fin (0 + N) → ℝ := fun i => y (castEquiv N i) with hz
  have hg := hG z hy
  refine ⟨?_, ?_, ?_⟩
  · intro a
    show eaEval (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c)
        (Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a)) y = 0
    rw [Work.WilE7.eaEval_reindex]
    exact hg.1 a
  · have hrank := hg.2.1
    have hmat := reindexMatrix_eq S y
    show (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
        eaEval (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c)
          (eaD (Work.WilE7.EAChain.reindex (castEquiv N) S.X.c) l
            (Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a))) y).rank = S.j
    rw [hmat]
    exact hrank
  · have hEv := hg.2.2
    have hcont : Continuous (fun w : Fin N → ℝ => fun i : Fin (0 + N) => w (castEquiv N i)) := by
      rw [continuous_pi_iff]
      intro i
      exact continuous_apply _
    have htend : Tendsto (fun w : Fin N → ℝ => fun i : Fin (0 + N) => w (castEquiv N i))
        (𝓝 y) (𝓝 z) := hcont.continuousAt
    filter_upwards [htend.eventually hEv] with y' hy'
    intro h0
    rw [hset, Set.mem_ofPred_eq]
    refine hy' (projFirst_zero_eq _ _) ?_
    intro a
    rw [← Work.WilE7.eaEval_reindex (castEquiv N) S.X.c (S.h a) y']
    exact h0 a

/-! ## The transport -/

theorem stratum_zero_to_amb {N : ℕ} (S : WilkiesDesign.E.Stratum 0 N) :
    ∃ S' : Work.WilE9G.AmbStratum N,
      (S'.X.set = {z : Fin N → ℝ | (fun i : Fin (0 + N) => z (Fin.cast (Nat.zero_add N) i)) ∈ S.X.set}) ∧
      (S'.Good ↔ S.Good) ∧ S'.j = S.j ∧ S'.X.r = S.X.r ∧ S'.X.fmt = S.X.fmt ∧
      S'.X.deg = S.X.deg ∧ S'.X.basics.length = S.X.basics.length := by
  refine ⟨⟨Work.WilE7.SemiPf.reindex (castEquiv N) S.X, S.j,
      fun a => Work.WilE7.EAPoly.reindex (castEquiv N) (S.h a)⟩, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · show (Work.WilE7.SemiPf.reindex (castEquiv N) S.X).set =
      {z : Fin N → ℝ | (fun i : Fin (0 + N) => z (Fin.cast (Nat.zero_add N) i)) ∈ S.X.set}
    exact Work.WilE7.reindex_eval.2 (castEquiv N) S.X
  · exact ⟨good_fwd S, good_bwd S⟩
  · show (Work.WilE7.SemiPf.reindex (castEquiv N) S.X).fmt = S.X.fmt
    rw [Work.WilE8.Star.semipf_fmt_reindex]
    simp only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add]
  · show (Work.WilE7.SemiPf.reindex (castEquiv N) S.X).deg = S.X.deg
    exact Work.WilE8.Star.semipf_deg_reindex (castEquiv N) S.X
  · show (Work.WilE7.SemiPf.reindex (castEquiv N) S.X).basics.length = S.X.basics.length
    simp only [Work.WilE7.SemiPf.reindex, List.length_map]

end Work.WilE9G.Amb
