/-
  WilE9 / Sharp — **smoothness of `f` at the base point reconstructed from a point of the extended
  set.**

  This is the strengthened form of the soundness statement `exSemiPf_snd`: not only does every
  point `(y, σ)` of `exTset E L` satisfy `σ = ψ (∂_L f (ψ⁻¹ y))` (which presupposes that
  `∂_L f` exists there), but `f` is actually `C^∞` at `ψ⁻¹ y`.

  The proof repeats the constructive part of `exSemiPf_snd`: the point `z` of the extended set is
  pulled back to the point `exSub z = (x₀, y₀)` of the pulled-back system, the implicit function
  theorem (`Work.WilE9.Ift.ift_exists`) produces a `C^∞` solution `Φ` with `Φ x₀ = y₀`, the
  `ψ`-branch lemma identifies `Φ`'s `y`/`w`/`τ`-coordinates with `ψ`/`psig` of the base and of
  `Φ`'s `s`-coordinate, and the graph relation `hZ` then shows `Φ x (fS) = f x` for all `x` near
  `x₀`.  Since `x ↦ Φ x (fS)` is `C^∞` at `x₀`, so is `f`, and `x₀ = psiInvV y` is the
  reconstructed base point.

  Everything below the last step (the BNZ formula `pbP L = (∂_L f)·Q^{2|L|}`) is *not* needed
  here, which is why this proof is shorter than `exSemiPf_snd`'s.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.ExSndAux
import Submission.Work.WilE9.Sharp.pb_det_ne_zero
import Submission.Work.WilE9.Sharp.graph_rel
import Submission.Work.WilE9.Sharp.psig_psiInv_of_sq
import Submission.Work.WilE9.Sharp.circle_branch
import Submission.Work.WilE9.Sharp.AE.exStrat_mem
import Submission.Work.WilE9.Sharp.eaEval_exRaise
import Submission.Work.WilE9.Sharp.eaEval_pbRaise
import Submission.Work.WilE9.Ift.ift_exists
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.psi_psig_algebra
import Submission.Work.WilE9.Psi.psig_pos

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open WilkiesDesign WilkiesDesign.E Filter
open Classical
namespace Work.WilE9.Sharp

open Work.WilE9 (psig psiInv)

/-! ## Reading a `Fin.append`-ed pulled-back ambient point at the named coordinates -/

@[simp] private theorem append_pbX {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x y) (pbX n m i) = x i := by
  rw [show pbX n m i = Fin.castAdd (qpb n m) i from rfl, Fin.append_left]

@[simp] private theorem append_pbS {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    (Fin.append x y) (pbS n m) = y (fS n m) := by
  rw [← natAdd_fS, Fin.append_right]

@[simp] private theorem append_pbY {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x y) (pbY n m i) = y (fY n m i) := by
  rw [← natAdd_fY, Fin.append_right]

@[simp] private theorem append_pbW {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) (i : Fin n) :
    (Fin.append x y) (pbW n m i) = y (fW n m i) := by
  rw [← natAdd_fW, Fin.append_right]

@[simp] private theorem append_pbT {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    (Fin.append x y) (pbT n m) = y (fT n m) := by
  rw [← natAdd_fT, Fin.append_right]

@[simp] private theorem append_pbU {n m : ℕ} (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ) :
    (Fin.append x y) (pbU n m) = y (fU n m) := by
  rw [← natAdd_fU, Fin.append_right]

/-! ## The four branches of `pbF` needed by the branch lemma -/

private theorem pbF_fS {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) :
    pbF n m r h (fS n m) =
      ((MvPolynomial.X (Sum.inl (pbT n m)) : EAPoly (Npb n m) r)
        - MvPolynomial.X (Sum.inl (pbS n m)) * MvPolynomial.X (Sum.inl (pbU n m))) := by
  rw [pbF]
  rw [dif_pos (show ((fS n m : Fin (qpb n m)) : ℕ) = 0 from rfl)]

private theorem pbF_fY {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) :
    pbF n m r h (fY n m i) =
      ((MvPolynomial.X (Sum.inl (pbY n m i)) : EAPoly (Npb n m) r)
        - MvPolynomial.X (Sum.inl (pbX n m i)) * MvPolynomial.X (Sum.inl (pbW n m i))) := by
  rw [pbF]
  rw [dif_neg (by simp only [fY]; omega), dif_pos (by simp only [fY]; omega)]
  refine congrArg (fun i' : Fin n => (MvPolynomial.X (Sum.inl (pbY n m i')) : EAPoly (Npb n m) r)
    - MvPolynomial.X (Sum.inl (pbX n m i')) * MvPolynomial.X (Sum.inl (pbW n m i'))) ?_
  apply Fin.ext
  simp only [fY, Fin.val_mk]
  omega

private theorem pbF_fW {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) :
    pbF n m r h (fW n m i) =
      (((MvPolynomial.X (Sum.inl (pbY n m i)) : EAPoly (Npb n m) r)) ^ 2
        + (MvPolynomial.X (Sum.inl (pbW n m i))) ^ 2 - 1) := by
  rw [pbF]
  rw [dif_neg (by simp only [fW]; omega), dif_neg (by simp only [fW]; omega),
    dif_pos (by simp only [fW]; omega)]
  refine congrArg (fun i' : Fin n =>
    ((MvPolynomial.X (Sum.inl (pbY n m i')) : EAPoly (Npb n m) r)) ^ 2
      + (MvPolynomial.X (Sum.inl (pbW n m i'))) ^ 2 - 1) ?_
  apply Fin.ext
  simp only [fW, Fin.val_mk]
  omega

private theorem pbF_fT {n m r : ℕ} (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) :
    pbF n m r h (fT n m) =
      (((MvPolynomial.X (Sum.inl (pbT n m)) : EAPoly (Npb n m) r)) ^ 2
        + (MvPolynomial.X (Sum.inl (pbU n m))) ^ 2 - 1) := by
  rw [pbF]
  rw [dif_neg (by simp only [fT]; omega), dif_neg (by simp only [fT]; omega),
    dif_neg (by simp only [fT]; omega), dif_pos (by simp only [fT])]

/-! ## Evaluating those four branches -/

private theorem eaEval_pbF_fS {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fS n m)) z
      = z (pbT n m) - z (pbS n m) * z (pbU n m) := by
  rw [pbF_fS]
  simp only [eaEval_sub, eaEval_mul, eaEval_X_inl]

private theorem eaEval_pbF_fY {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fY n m i)) z
      = z (pbY n m i) - z (pbX n m i) * z (pbW n m i) := by
  rw [pbF_fY]
  simp only [eaEval_sub, eaEval_mul, eaEval_X_inl]

private theorem eaEval_pbF_fW {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (i : Fin n) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fW n m i)) z
      = z (pbY n m i) ^ 2 + z (pbW n m i) ^ 2 - 1 := by
  rw [pbF_fW]
  simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one]

private theorem eaEval_pbF_fT {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (z : Fin (Npb n m) → ℝ) :
    eaEval (pbChain c) (pbF n m r h (fT n m)) z
      = z (pbT n m) ^ 2 + z (pbU n m) ^ 2 - 1 := by
  rw [pbF_fT]
  simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one]

/-! ## The four equations satisfied by a point of the fibre over a solution -/

private theorem pbF_sol_eqs {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (x : Fin n → ℝ) (y : Fin (qpb n m) → ℝ)
    (hz : ∀ j : Fin (qpb n m), eaEval (pbChain c) (pbF n m r h j) (Fin.append x y) = 0) :
    (y (fT n m) = y (fS n m) * y (fU n m)) ∧
    (∀ i : Fin n, y (fY n m i) = x i * y (fW n m i)) ∧
    (∀ i : Fin n, y (fY n m i) ^ 2 + y (fW n m i) ^ 2 = 1) ∧
    (y (fT n m) ^ 2 + y (fU n m) ^ 2 = 1) := by
  have keyS : eaEval (pbChain c) (pbF n m r h (fS n m)) (Fin.append x y)
      = (Fin.append x y) (pbT n m)
        - (Fin.append x y) (pbS n m) * (Fin.append x y) (pbU n m) :=
    eaEval_pbF_fS c h (Fin.append x y)
  have keyY : ∀ i : Fin n, eaEval (pbChain c) (pbF n m r h (fY n m i)) (Fin.append x y)
      = (Fin.append x y) (pbY n m i)
        - (Fin.append x y) (pbX n m i) * (Fin.append x y) (pbW n m i) :=
    fun i => eaEval_pbF_fY c h i (Fin.append x y)
  have keyW : ∀ i : Fin n, eaEval (pbChain c) (pbF n m r h (fW n m i)) (Fin.append x y)
      = (Fin.append x y) (pbY n m i) ^ 2 + (Fin.append x y) (pbW n m i) ^ 2 - 1 :=
    fun i => eaEval_pbF_fW c h i (Fin.append x y)
  have keyT : eaEval (pbChain c) (pbF n m r h (fT n m)) (Fin.append x y)
      = (Fin.append x y) (pbT n m) ^ 2 + (Fin.append x y) (pbU n m) ^ 2 - 1 :=
    eaEval_pbF_fT c h (Fin.append x y)
  have hS : y (fT n m) - y (fS n m) * y (fU n m) = 0 := by
    have h1 := keyS ▸ hz (fS n m)
    rw [append_pbT, append_pbS, append_pbU] at h1
    exact h1
  have hT : y (fT n m) ^ 2 + y (fU n m) ^ 2 - 1 = 0 := by
    have h1 := keyT ▸ hz (fT n m)
    rw [append_pbT, append_pbU] at h1
    exact h1
  have hY : ∀ i : Fin n, y (fY n m i) - x i * y (fW n m i) = 0 := fun i => by
    have h1 := keyY i ▸ hz (fY n m i)
    rw [append_pbY, append_pbX, append_pbW] at h1
    exact h1
  have hW : ∀ i : Fin n, y (fY n m i) ^ 2 + y (fW n m i) ^ 2 - 1 = 0 := fun i => by
    have h1 := keyW i ▸ hz (fW n m i)
    rw [append_pbY, append_pbW] at h1
    exact h1
  exact ⟨sub_eq_zero.mp hS, fun i => sub_eq_zero.mp (hY i),
    fun i => sub_eq_zero.mp (hW i), sub_eq_zero.mp hT⟩

/-! ## The `ψ`-branch along a solution: `Φ`'s structural coordinates are `ψ`/`psig` of the base

This is the lemma `Work.WilE9.Sharp.pbF_branch` of the tree, proved here without the axiom it
was developed against: the single real-algebra input is `circle_branch` (the uniqueness of the
positive branch on the unit circle), and positivity at `x₀` is upgraded to an eventual statement
by continuity of `Φ`. -/

private theorem pbF_branch_psi {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (Φ : (Fin n → ℝ) → (Fin (qpb n m) → ℝ)) (x₀ : Fin n → ℝ)
    (hcd : ContDiffAt ℝ ⊤ Φ x₀)
    (hs : Work.WilE9.IsSoln (pbChain c) (pbF n m r h) Φ x₀)
    (hw : ∀ i : Fin n, 0 < Φ x₀ (fW n m i))
    (hu : 0 < Φ x₀ (fU n m)) :
    ∀ᶠ x in nhds x₀,
      (∀ i : Fin n, Φ x (fY n m i) = WilkiesDesign.E.psi (x i)) ∧
      (∀ i : Fin n, Φ x (fW n m i) = Work.WilE9.psig (x i)) ∧
      Φ x (fT n m) = WilkiesDesign.E.psi (Φ x (fS n m)) := by
  have hcont : ContinuousAt Φ x₀ := hcd.continuousAt
  have hw_ev : ∀ᶠ x in nhds x₀, ∀ i : Fin n, 0 < Φ x (fW n m i) := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply (fW n m i)).continuousAt.comp hcont).tendsto
      (isOpen_Ioi.mem_nhds (hw i))
  have hu_ev : ∀ᶠ x in nhds x₀, 0 < Φ x (fU n m) :=
    ((continuous_apply (fU n m)).continuousAt.comp hcont).tendsto
      (isOpen_Ioi.mem_nhds hu)
  filter_upwards [hs.1, hw_ev, hu_ev] with x hx hwx hux
  obtain ⟨eS, eY, eW, eT⟩ := pbF_sol_eqs c h x (Φ x) hx
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · exact (circle_branch (hwx i) (eY i) (eW i)).2
  · exact (circle_branch (hwx i) (eY i) (eW i)).1
  · exact (circle_branch hux eS eT).2

/-! ## The solution's `s`-coordinate is `f` near `x₀` -/

private theorem sol_s_eq_f {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : EffStratum n m) (Q : Set (Fin (n + (1 + m)) → ℝ))
    (hπ : ∀ w ∈ Q, stratProj w ∈ Z)
    (Φ : (Fin n → ℝ) → (Fin (qpb n m) → ℝ)) (x₀ : Fin n → ℝ)
    (hstr : ∀ᶠ x in nhds x₀, pbStrat (Fin.append x (Φ x)) ∈ Q)
    (hbr : ∀ᶠ x in nhds x₀,
      (∀ i : Fin n, Φ x (fY n m i) = WilkiesDesign.E.psi (x i)) ∧
      (∀ i : Fin n, Φ x (fW n m i) = Work.WilE9.psig (x i)) ∧
      Φ x (fT n m) = WilkiesDesign.E.psi (Φ x (fS n m))) :
    (fun x : Fin n → ℝ => Φ x (fS n m)) =ᶠ[nhds x₀] f := by
  filter_upwards [hbr, hstr] with x hbrx hstrx
  have hZmem : stratProj (pbStrat (Fin.append x (Φ x))) ∈ Z := hπ _ hstrx
  have hval : stratProj (pbStrat (Fin.append x (Φ x)))
      = Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi (Φ x (fS n m))) := by
    rw [stratProj_pbStrat]
    congr 1
    · funext i
      rw [← natAdd_fY, Fin.append_right, hbrx.1 i]
      rfl
    · rw [← natAdd_fT, Fin.append_right, hbrx.2.2]
  rw [hval] at hZmem
  have hτ : WilkiesDesign.E.psi (Φ x (fS n m)) = WilkiesDesign.E.psi (f x) :=
    graph_rel hZ (abs_psi_lt_one _) hZmem
  have h2 := congrArg psiInv hτ
  rwa [Work.WilE9.Psi.psiInv_psi, Work.WilE9.Psi.psiInv_psi] at h2

/-! ## The main theorem -/

theorem exSemiPf_snd_contDiff_gen {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    (Q : Set (Fin (n + (1 + m)) → ℝ))
    (hQ : ∀ z ∈ Q, ∀ᶠ z' in nhds z,
      (∀ a, WilkiesDesign.E.eaEval E.X.c (E.h a) z' = 0) → z' ∈ Q)
    (hπ : ∀ w ∈ Q, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ)
    (h : ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc y σ ∧ Work.WilE9.Sharp.exStrat z ∈ Q) :
    ContDiffAt ℝ ⊤ f (Work.WilE9.Sharp.psiInvV y) := by
  obtain ⟨z, hzmem, hzout, hzQ⟩ := h
  obtain ⟨hzcube, B, hBmem, hB⟩ := hzmem
  obtain ⟨B0, hB0mem, hB0eq⟩ := List.mem_map.mp hBmem
  rw [← hB0eq] at hB
  obtain ⟨hBeqs, hBpos⟩ := hB
  -- the `y`-coordinates of `z`
  have hy : ∀ i : Fin n, z (exY n m i) = y i := fun i => by
    have h1 := congrFun hzout (Fin.castSucc i)
    rw [Fin.snoc_castSucc] at h1
    change z (Fin.castAdd (n + m + 3) (Fin.castSucc i)) = y i at h1
    rw [exY_eq_castAdd]
    exact h1
  -- the equations of the extended basic condition
  have hBeq : ∀ g ∈ exEqList E.X.c E.h L, eaEval (exChain E.X.c) g z = 0 := fun g hg =>
    hBeqs g (show g ∈ (exBasic E.X.c E.h L B0).eqs from
      List.mem_append.mpr (Or.inl hg))
  have hBpo : ∀ g ∈ exPosList (n := n) (m := m) (r := E.X.r) B0,
      0 < eaEval (exChain E.X.c) g z := fun g hg =>
    hBpos g (show g ∈ (exBasic E.X.c E.h L B0).pos from hg)
  have hyw : ∀ i, z (exY n m i) ^ 2 + z (exW n m i) ^ 2 = 1 := fun i => by
    have h1 := hBeq _ (mem_exEqList_yw E.X.c E.h L i)
    simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one] at h1
    linarith
  have htu : z (exT n m) ^ 2 + z (exU n m) ^ 2 = 1 := by
    have h1 := hBeq _ (mem_exEqList_tu E.X.c E.h L)
    simp only [eaEval_sub, eaEval_add, eaEval_pow, eaEval_X_inl, eaEval_one] at h1
    linarith
  have hstr : ∀ a : Fin (1 + m), eaEval E.X.c (E.h a) (exStrat z) = 0 := fun a => by
    have h1 := hBeq _ (mem_exEqList_h E.X.c E.h L a)
    rwa [eaEval_exRaise] at h1
  have hwpos : ∀ i, 0 < z (exW n m i) := fun i => by
    have h1 := hBpo _ (mem_exPosList_w B0 i)
    simpa only [eaEval_X_inl] using h1
  have hupos : 0 < z (exU n m) := by
    have h1 := hBpo _ (mem_exPosList_u B0)
    simpa only [eaEval_X_inl] using h1
  -- first conclusion: `y ∈ ocube`
  have hy_lt : ∀ i : Fin n, |y i| < 1 := fun i => by
    have h2 : z (exY n m i) ^ 2 < 1 := by linarith [hyw i, pow_pos (hwpos i) 2]
    rw [← hy i]
    exact (sq_lt_one_iff_abs_lt_one _).mp h2
  -- `exStrat z ∈ E.X.set`
  have hXmem : exStrat z ∈ E.X.set := by
    refine ⟨fun i => hzcube (sIdxE n m i), B0, hB0mem, ?_⟩
    refine ⟨?_, ?_⟩
    · intro g hg
      have h1 : eaEval (exChain E.X.c) (exRaise g) z = 0 :=
        hBeqs _ (show exRaise g ∈ (exBasic E.X.c E.h L B0).eqs from
          List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨g, hg, rfl⟩)))
      rwa [eaEval_exRaise] at h1
    · intro g hg
      have h1 : 0 < eaEval (exChain E.X.c) (exRaise g) z :=
        hBpos _ (mem_exPosList_pos B0 hg)
      rwa [eaEval_exRaise] at h1
  obtain ⟨_, hJinv, _⟩ := hgood (exStrat z) hXmem
  have hloc := hQ (exStrat z) hzQ
  -- the reconstructed pulled-back point
  set x₀ : Fin n → ℝ := exBase z with hx₀
  set y₀ : Fin (qpb n m) → ℝ := exFib z with hy₀
  have hexSub : exSub z = Fin.append x₀ y₀ := by
    rw [hx₀, hy₀]; exact exSub_eq_append z
  have hwne : ∀ i, z (exW n m i) ≠ 0 := fun i => ne_of_gt (hwpos i)
  have hune : z (exU n m) ≠ 0 := ne_of_gt hupos
  -- the pulled-back equations hold there
  have hpb0 : ∀ j, eaEval (pbChain E.X.c) (pbF n m E.X.r E.h j) (Fin.append x₀ y₀) = 0 :=
    fun j => by
      rw [← hexSub]
      exact pbF_at_exSub E.X.c E.h z hwne hune hyw htu hstr j
  have hy0 : ∀ i, y₀ (fY n m i) = x₀ i * y₀ (fW n m i) := fun i => by
    rw [hx₀, hy₀, exBase_apply, exFib_fY, exFib_fW]
    exact (div_mul_cancel₀ _ (hwne i)).symm
  have hw0 : ∀ i, y₀ (fW n m i) ≠ 0 := fun i => by rw [hy₀, exFib_fW]; exact hwne i
  have hu0 : y₀ (fU n m) ≠ 0 := by rw [hy₀, exFib_fU]; exact hune
  have hP : (Matrix.of fun (a : Fin (1 + m)) (l : Fin (1 + m)) =>
      eaEval E.X.c (eaD E.X.c (Fin.natAdd n l) (E.h a))
        (pbStrat (Fin.append x₀ y₀))).det ≠ 0 := by
    rw [← hexSub, pbStrat_exSub]
    exact hJinv
  have hpbD : (Matrix.of fun (j : Fin (qpb n m)) (l : Fin (qpb n m)) =>
      eaEval (pbChain E.X.c) (eaD (pbChain E.X.c) (Fin.natAdd n l) (pbF n m E.X.r E.h j))
        (Fin.append x₀ y₀)).det ≠ 0 :=
    pb_det_ne_zero E.X.c E.h x₀ y₀ hy0 hw0 hu0 hP
  obtain ⟨Φ, hΦ0, hΦcd, hΦsoln⟩ :=
    Work.WilE9.Ift.ift_exists (pbChain E.X.c) (pbF n m E.X.r E.h) x₀ y₀ hpb0 hpbD
  -- the stratum's coordinates along the solution converge to those of `z`
  have hpb : Continuous (pbStrat (n := n) (m := m)) := by
    change Continuous (fun z' : Fin (Npb n m) → ℝ => fun i => z' (sIdxPb n m i))
    rw [continuous_pi_iff]
    intro i
    exact continuous_apply (sIdxPb n m i)
  have hcont : Tendsto (fun x => pbStrat (Fin.append x (Φ x))) (nhds x₀) (nhds (exStrat z)) := by
    have h1 : Tendsto (fun x => Fin.append x (Φ x)) (nhds x₀) (nhds (Fin.append x₀ y₀)) := by
      have hΦ : Tendsto Φ (nhds x₀) (nhds y₀) := by rw [← hΦ0]; exact hΦcd.continuousAt
      have hpair : Tendsto (fun x : Fin n → ℝ => (x, Φ x)) (nhds x₀) (nhds (x₀, y₀)) := by
        have hp := tendsto_id.prodMk hΦ
        rwa [← nhds_prod_eq] at hp
      have hclm : Tendsto (fun p : (Fin n → ℝ) × (Fin (qpb n m) → ℝ) => Fin.append p.1 p.2)
          (nhds (x₀, y₀)) (nhds (Fin.append x₀ y₀)) := by
        have hcc := (Work.WilE9.Ift.appendCLM n (qpb n m)).continuous
        rw [Work.WilE9.Ift.coe_appendCLM] at hcc
        exact hcc.tendsto (x₀, y₀)
      simpa only [Function.comp_def] using hclm.comp hpair
    rw [← hexSub] at h1
    have h0 := hpb.tendsto (Fin.append x₀ y₀)
    rw [← hexSub, pbStrat_exSub] at h0
    exact h0.comp h1
  have hStr_loc : ∀ᶠ x in nhds x₀, pbStrat (Fin.append x (Φ x)) ∈ Q := by
    filter_upwards [soln_h_eq E.X.c E.h Φ x₀ hΦsoln, hcont.eventually hloc] with x hxeq hxloc
    exact hxloc hxeq
  -- the `ψ`-branch and the agreement with `f`
  have hbr := pbF_branch_psi E.X.c E.h Φ x₀ hΦcd hΦsoln
    (fun i => by rw [hΦ0, hy₀, exFib_fW]; exact hwpos i)
    (by rw [hΦ0, hy₀, exFib_fU]; exact hupos)
  have hGlEq : (fun x => Φ x (fS n m)) =ᶠ[nhds x₀] f :=
    sol_s_eq_f hZ E Q hπ Φ x₀ hStr_loc hbr
  -- `x ↦ Φ x (fS)` is smooth, so `f =ᶠ Φ · (fS)` is smooth, and `x₀ = psiInvV y`
  have hcosmooth : ContDiffAt ℝ ⊤ (fun x : Fin n → ℝ => Φ x (fS n m)) x₀ := by
    have h1 : ContDiffAt ℝ ⊤ (fun v : Fin (qpb n m) → ℝ => v (fS n m)) (Φ x₀) :=
      (contDiff_apply ℝ ℝ (fS n m)).contDiffAt
    exact h1.comp x₀ hΦcd
  have hfsmooth : ContDiffAt ℝ ⊤ f x₀ := hcosmooth.congr_of_eventuallyEq hGlEq.symm
  have hx0 : x₀ = Work.WilE9.Sharp.psiInvV y := by
    funext i
    have h1 : z (exY n m i) / psig (psiInv (z (exY n m i))) = psiInv (z (exY n m i)) :=
      div_psig_psiInv (by rw [hy i]; exact hy_lt i)
    rw [hx₀, exBase_apply, Work.WilE9.Sharp.psiInvV,
      psig_psiInv_of_sq (hyw i) (hwpos i), ← hy i]
    exact h1
  rw [← hx0]
  exact hfsmooth

/-- The unrestricted statement, the instance `Q = E.X.set` of `exSemiPf_snd_contDiff_gen`. -/
theorem exSemiPf_snd_contDiff {n m : ℕ} {f : (Fin n → ℝ) → ℝ}
    {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    (hπ : ∀ w ∈ E.X.set, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ)
    (h : ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc y σ) :
    ContDiffAt ℝ ⊤ f (Work.WilE9.Sharp.psiInvV y) := by
  obtain ⟨z, hzmem, hzout⟩ := h
  exact exSemiPf_snd_contDiff_gen hZ E hgood E.X.set (fun w hw => (hgood w hw).2.2) hπ L y σ
    ⟨z, hzmem, hzout, exStrat_mem_of_mem_exSemiPf E L hzmem⟩

end Work.WilE9.Sharp
