import Mathlib
import Submission.Work.WilE9.Sharp.Vocab
import Submission.Work.WilE9.Sharp.ExDefs
import Submission.Work.WilE9.Sharp.ExSndAux
import Submission.Work.WilE9.Sharp.clearPb_eval
import Submission.Work.WilE9.Sharp.pbF_branch
import Submission.Work.WilE9.Sharp.pb_det_ne_zero
import Submission.Work.WilE9.Sharp.graph_rel
import Submission.Work.WilE9.Sharp.psig_psiInv_of_sq
import Submission.Work.WilE9.Sharp.eaEval_exRaise
import Submission.Work.WilE9.Sharp.eaEval_pbRaise
import Submission.Work.WilE9.Ift.ift_exists
import Submission.Work.WilE9.Ift.ift_identity
import Submission.Work.WilE9.Ift.AppendCLM
import Submission.Work.WilE9.Psi.psi_psiInv
import Submission.Work.WilE9.Psi.psiInv_psi
import Submission.Work.WilE9.Psi.psi_psig_algebra
import Submission.Work.WilE9.Psi.psig_pos
import Submission.Work.WilE9.Sharp.AE.exStrat_mem

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open WilkiesDesign WilkiesDesign.E Filter
namespace Work.WilE9.Sharp

open Work.WilE9 (psig psiInv)

/-
  **Soundness of the extended set.**  Every point `(y,σ)` of the extended semi-Pfaffian set of an
  effectively smooth stratum `E` and an order `L` satisfies `y ∈ ocube`, `σ ∈ ocube` and
  `σ = ψ (∂_L f (ψ⁻¹ y))`; the extended equations pin `x = ψ⁻¹ y`, `s = f x` and `σ` down.

  Ingredients (all available in the tree):
  * `Work.WilE9.Sharp.psig_psiInv_of_sq` — the branch of the square root;
  * `Work.WilE9.Sharp.pb_det_ne_zero` — the invertibility of the pulled-back Jacobian;
  * `Work.WilE9.Ift.ift_exists`, `Work.WilE9.Ift.ift_identity` — the implicit function and BNZ's
    formula `P_L = (∂_L s)·Q^{2|L|}`;
  * `Work.WilE9.Sharp.graph_rel` — the graph relation of `hZ`;
  * `Work.WilE9.Sharp.clearNumDen_eval` — reading the cleared equation `σ·Q^{2|L|} = υ·P_L`.
-/
/-- **Soundness of the component-restricted extended set.**  Same as `exSemiPf_snd_gen` with
the neighbourhood `Q` of the stratum's component in place of the whole stratum set: the
per-stratum hypothesis "the component projects into `Z`" is only available on `Q`, and every
point of `exComp` has stratum coordinates in `Q` (`exStrat_mem_comp_of_mem_exComp`). -/
theorem exSemiPf_snd_gen {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    (Q : Set (Fin (n + (1 + m)) → ℝ))
    (hQ : ∀ z ∈ Q, ∀ᶠ z' in nhds z,
      (∀ a, WilkiesDesign.E.eaEval E.X.c (E.h a) z' = 0) → z' ∈ Q)
    (hπ : ∀ w ∈ Q, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ)
    (h : ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc y σ ∧ Work.WilE9.Sharp.exStrat z ∈ Q) :
    (∀ i : Fin n, |y i| < 1) ∧ |σ| < 1 ∧
      σ = WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (Work.WilE9.Sharp.psiInvV y)) := by
  obtain ⟨z, hzmem, hzout, hzQ⟩ := h
  obtain ⟨hzcube, B, hBmem, hB⟩ := hzmem
  obtain ⟨B0, hB0mem, hB0eq⟩ := List.mem_map.mp hBmem
  rw [← hB0eq] at hB
  obtain ⟨hBeqs, hBpos⟩ := hB
  -- the `y`- and `σ`-coordinates of `z`
  have hy : ∀ i : Fin n, z (exY n m i) = y i := fun i => by
    have h1 := congrFun hzout (Fin.castSucc i)
    rw [Fin.snoc_castSucc] at h1
    change z (Fin.castAdd (n + m + 3) (Fin.castSucc i)) = y i at h1
    rw [exY_eq_castAdd]
    exact h1
  have hσeq : z (exSig n m) = σ := by
    have h1 := congrFun hzout (Fin.last n)
    rw [Fin.snoc_last] at h1
    change z (Fin.castAdd (n + m + 3) (Fin.last n)) = σ at h1
    rw [exSig_eq_castAdd]
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
  have hsv : z (exSig n m) ^ 2 + z (exV n m) ^ 2 = 1 := by
    have h1 := hBeq _ (mem_exEqList_sv E.X.c E.h L)
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
  have hvpos : 0 < z (exV n m) := by
    have h1 := hBpo _ (mem_exPosList_v B0)
    simpa only [eaEval_X_inl] using h1
  -- first two conclusions
  have hy_lt : ∀ i : Fin n, |y i| < 1 := fun i => by
    have h2 : z (exY n m i) ^ 2 < 1 := by linarith [hyw i, pow_pos (hwpos i) 2]
    rw [← hy i]
    exact (sq_lt_one_iff_abs_lt_one _).mp h2
  have hσ_lt : |σ| < 1 := by
    have h2 : z (exSig n m) ^ 2 < 1 := by linarith [hsv, pow_pos hvpos 2]
    rw [← hσeq]
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
  have hden : ∀ b : Fin (n + 1), z (sDen n m b) ≠ 0 := sDen_ne_zero z hwne hune
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
  -- BNZ's formula for the derivative of the solution
  have hQev : ∀ᶠ x in nhds x₀,
      eaEval (pbChain E.X.c) (jQ (pbChain E.X.c) (pbF n m E.X.r E.h))
        (Fin.append x (Φ x)) ≠ 0 := by
    filter_upwards [hΦsoln.2] with x hx
    have heq : eaEval (pbChain E.X.c) (jQ (pbChain E.X.c) (pbF n m E.X.r E.h))
          (Fin.append x (Φ x))
        = ((jm (pbChain E.X.c) (pbF n m E.X.r E.h)).map
            (fun P => eaEval (pbChain E.X.c) P (Fin.append x (Φ x)))).det := by
      rw [show jQ (pbChain E.X.c) (pbF n m E.X.r E.h)
            = (jm (pbChain E.X.c) (pbF n m E.X.r E.h)).det from rfl]
      exact eaEval_det (pbChain E.X.c) (jm (pbChain E.X.c) (pbF n m E.X.r E.h))
        (Fin.append x (Φ x))
    rwa [heq]
  have hift := Work.WilE9.Ift.ift_identity (pbChain E.X.c) (pbF n m E.X.r E.h) (fS n m)
    Φ x₀ hΦcd hΦsoln hQev L
  -- the cleared equation of the extended system
  have h6 := hBeq _ (mem_exEqList_eq6 E.X.c E.h L)
  simp only [exEq6, eaEval_sub, eaEval_mul, eaEval_X_inl] at h6
  set Cst : ℝ := (∏ b : Fin (n + 1), z (sDen n m b)) ^ (exK E.X.c E.h L) with hCst
  have hKQ : (pbQ E.X.c E.h ^ (2 * L.length)).totalDegree ≤ exK E.X.c E.h L :=
    le_trans (le_max_left _ _) (Nat.le_succ _)
  have hKP : (pbP E.X.c E.h L).totalDegree ≤ exK E.X.c E.h L :=
    le_trans (le_max_right _ _) (Nat.le_succ _)
  have hQcle : eaEval (exChain E.X.c) (exQ E.X.c E.h L) z =
      Cst * eaEval (pbChain E.X.c) (pbQ E.X.c E.h ^ (2 * L.length)) (exSub z) := by
    rw [hCst, exQ]
    exact clearPb_eval E.X.c (exK E.X.c E.h L) (pbQ E.X.c E.h ^ (2 * L.length)) z hKQ hden
  have hPcle : eaEval (exChain E.X.c) (exP E.X.c E.h L) z =
      Cst * eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z) := by
    rw [hCst, exP]
    exact clearPb_eval E.X.c (exK E.X.c E.h L) (pbP E.X.c E.h L) z hKP hden
  have hCst_ne : Cst ≠ 0 := by
    rw [hCst]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun b _ => hden b))
  -- `σ · Q^{2|L|} = υ · P_L` after cancelling the cleared denominator
  have hmain : z (exSig n m)
      * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length)
      = z (exV n m) * eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z) := by
    have h := h6
    rw [hQcle, hPcle, eaEval_pow] at h
    have hfac : Cst * (z (exSig n m)
        * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length)
        - z (exV n m) * eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z)) = 0 := by
      rw [← h]; ring
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd h1 hCst_ne
    · linarith
  -- the numerator at the reconstructed point is the `L`-th derivative of the solution
  have hift' : eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z)
      = Work.WilE9.glDeriv L (fun x => Φ x (fS n m)) x₀
        * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length) := by
    rw [pbP, pbQ, hexSub, ← hΦ0]
    exact hift
  have hQval_ne : eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z) ≠ 0 := by
    rw [hexSub, ← hΦ0]
    exact hQev.self_of_nhds
  -- the `ψ`-coordinates of the output
  have hsv_abs : |z (exSig n m)| < 1 := by rw [hσeq]; exact hσ_lt
  have hυ_psi : z (exV n m) = psig (psiInv (z (exSig n m))) :=
    psig_psiInv_of_sq hsv hvpos
  set r : ℝ := psiInv (z (exSig n m)) with hr
  have hsig_r : z (exSig n m) = r * z (exV n m) := by
    have h1 : WilkiesDesign.E.psi r = z (exSig n m) := by
      rw [hr]; exact Work.WilE9.Psi.psi_psiInv (z (exSig n m)) hsv_abs
    have h2 : z (exV n m) = psig r := hυ_psi
    rw [← h1, h2, (Work.WilE9.Psi.psi_psig_algebra r).1]
  have hr_eq : r * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length)
      = eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z) := by
    have h := hmain
    rw [hsig_r] at h
    have h' : z (exV n m) * (r * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z))
          ^ (2 * L.length))
        = z (exV n m) * eaEval (pbChain E.X.c) (pbP E.X.c E.h L) (exSub z) := by
      rw [← h]; ring
    exact mul_left_cancel₀ (ne_of_gt hvpos) h'
  have hr_deriv : r = Work.WilE9.glDeriv L (fun x => Φ x (fS n m)) x₀ := by
    have h : r * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length)
        = Work.WilE9.glDeriv L (fun x => Φ x (fS n m)) x₀
          * (eaEval (pbChain E.X.c) (pbQ E.X.c E.h) (exSub z)) ^ (2 * L.length) := by
      rw [hr_eq, hift']
    exact mul_right_cancel₀ (pow_ne_zero _ hQval_ne) h
  -- the solution's `s`-coordinate is `f` near `x₀`
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
  have hbr := pbF_branch E.X.c E.h Φ x₀ hΦcd hΦsoln
    (fun i => by rw [hΦ0, hy₀, exFib_fW]; exact hwpos i)
    (by rw [hΦ0, hy₀, exFib_fU]; exact hupos)
  have hGlEq : (fun x => Φ x (fS n m)) =ᶠ[nhds x₀] f := by
    filter_upwards [hbr, hStr_loc] with x hbrx hstrx
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
  have hgl : Work.WilE9.glDeriv L (fun x => Φ x (fS n m)) x₀ = Work.WilE9.glDeriv L f x₀ :=
    glDeriv_congr L hGlEq
  -- `x₀ = psiInvV y`
  have hx0 : x₀ = Work.WilE9.Sharp.psiInvV y := by
    funext i
    have h1 : z (exY n m i) / psig (psiInv (z (exY n m i))) = psiInv (z (exY n m i)) :=
      div_psig_psiInv (by rw [hy i]; exact hy_lt i)
    rw [hx₀, exBase_apply, Work.WilE9.Sharp.psiInvV,
      psig_psiInv_of_sq (hyw i) (hwpos i), ← hy i]
    exact h1
  refine ⟨hy_lt, hσ_lt, ?_⟩
  calc σ = z (exSig n m) := hσeq.symm
    _ = WilkiesDesign.E.psi r := by
        rw [hr]; exact (Work.WilE9.Psi.psi_psiInv (z (exSig n m)) hsv_abs).symm
    _ = WilkiesDesign.E.psi (Work.WilE9.glDeriv L (fun x => Φ x (fS n m)) x₀) := by rw [hr_deriv]
    _ = WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x₀) := by rw [hgl]
    _ = WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (Work.WilE9.Sharp.psiInvV y)) := by rw [hx0]

/-- The unrestricted soundness statement, the instance `Q = E.X.set` of `exSemiPf_snd_gen`
(the third conjunct of `E.Good` is exactly the locality hypothesis `hQ` for `Q = E.X.set`). -/
theorem exSemiPf_snd {n m : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (E : Work.WilE9.Sharp.EffStratum n m) (hgood : E.Good)
    (hπ : ∀ w ∈ E.X.set, Work.WilE9.Sharp.stratProj w ∈ Z)
    (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ)
    (h : ∃ z ∈ (Work.WilE9.Sharp.exSemiPf n m E L).set,
      Work.WilE9.Sharp.exOut z = Fin.snoc y σ) :
    (∀ i : Fin n, |y i| < 1) ∧ |σ| < 1 ∧
      σ = WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (Work.WilE9.Sharp.psiInvV y)) := by
  obtain ⟨z, hzmem, hzout⟩ := h
  exact exSemiPf_snd_gen hZ E hgood E.X.set (fun w hw => (hgood w hw).2.2) hπ L y σ
    ⟨z, hzmem, hzout, exStrat_mem_of_mem_exSemiPf E L hzmem⟩

end Work.WilE9.Sharp
