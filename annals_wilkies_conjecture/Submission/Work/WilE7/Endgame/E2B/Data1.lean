/-
  Area E7 / E2B, node `cellRefine_of_nodesB`, **part 1 of the split**: the constants of the
  bookkeeping (`E2Const`).

  All the producer calls are made at the outer format bound `F`, so that the format bound `F'`, the
  degree polynomial `P` and the cardinality polynomials `Nk, Nl, Ng` are chosen before
  `D k l m m' X Y`; the `Σ`-family and the `X'`-producer are handled uniformly in the fibre
  dimension `m ≤ F` (`E2B.sigmaTotal`).  See `Vocab.lean` for the structure of the data and
  `NOTES_S56_E2S_state.md` §2 for the plan.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Pkg

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-- The constants of the bookkeeping: the producer outputs at the outer format bound `F`, the
degree and cardinality polynomials, and the format/dimension bounds. -/
noncomputable def e2bConst (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6)
    (h0 : FrontierRestrat) (h1 : SigmaVPairs) (n K F : ℕ) : E2Const n K F := by
  classical
  let Ap : ℕ := (E2_pieces_of_family hFC hE5 F).choose
  let Pp : Polynomial ℕ := (E2_pieces_of_family hFC hE5 F).choose_spec.choose
  let Np : MvPolynomial (Fin 2) ℕ :=
    (E2_pieces_of_family hFC hE5 F).choose_spec.choose_spec.choose
  let Ar : ℕ := (E2_rank_strata hE5 Ap).choose
  let Pr : Polynomial ℕ := (E2_rank_strata hE5 Ap).choose_spec.choose
  let Af : ℕ := (E2_frontier_strata h0 Ap).choose
  let Pf : Polynomial ℕ := (E2_frontier_strata h0 Ap).choose_spec.choose
  let As : ℕ := (E2_sheets_of_stratum hE2 (Ap + Ar + Af)).choose
  let Ps : Polynomial ℕ := (E2_sheets_of_stratum hE2 (Ap + Ar + Af)).choose_spec.choose
  let Ac : ℕ := Ap + Ar + Af
  let Fp : ℕ := 2 * Ac
  let Dq : Polynomial ℕ := Pp + Pr.comp Pp + Pf.comp Pp + 1
  have hDq : ∀ D : ℕ, Dq.eval D = Pp.eval D + Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 1 := by
    intro D
    simp only [Dq, Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_one]
  let Qtot : MvPolynomial (Fin 3) ℕ := (E2B.sigmaTotal hE5 hE6 h1 n K Fp F).choose
  let Atot : ℕ := (E2B.sigmaTotal hE5 hE6 h1 n K Fp F).choose_spec.choose
  let Btot : Polynomial ℕ := (E2B.sigmaTotal hE5 hE6 h1 n K Fp F).choose_spec.choose_spec.choose
  let FZ : ℕ := Ac + Atot + pPair n F + 2
  let AZl : ℕ := (Work.CoreStep.fibreProd_sigma_lem FZ).choose
  let BZl : Polynomial ℕ := (Work.CoreStep.fibreProd_sigma_lem FZ).choose_spec.choose
  let M2 : ℕ := F + F + pPair n F + 5
  let Ft : ℕ := max (max Ac Atot) F
  let Fp0 : ℕ := max AZl (Ft + M2)
  let Pe1 : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 Pr Pp).choose
  let Pe2 : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 Pf Pp).choose
  have hPe1 : ∀ D : ℕ, Pr.eval (1 * (D + Pp.eval D)) ≤ Pe1.eval D :=
    (Work.WilE7.Endgame.poly_comp_dominate 1 Pr Pp).choose_spec
  have hPe2 : ∀ D : ℕ, Pf.eval (1 * (D + Pp.eval D)) ≤ Pe2.eval D :=
    (Work.WilE7.Endgame.poly_comp_dominate 1 Pf Pp).choose_spec
  let Dg : Polynomial ℕ :=
    Polynomial.X + Pp + Pe1 + Pe2 + (3 * Dq + 2) + (Btot.comp Dq) + (Ps.comp Dq) + 1
  let Pd1 : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 BZl (Dq + Dg)).choose
  have hPd1 : ∀ D : ℕ, BZl.eval (1 * (D + (Dq + Dg).eval D)) ≤ Pd1.eval D :=
    (Work.WilE7.Endgame.poly_comp_dominate 1 BZl (Dq + Dg)).choose_spec
  let P : Polynomial ℕ := Dg + Pd1
  have hDgeval : ∀ D : ℕ, Dg.eval D = D + Pp.eval D + Pe1.eval D + Pe2.eval D +
      (3 * Dq.eval D + 2) + Btot.eval (Dq.eval D) + Ps.eval (Dq.eval D) + 1 := by
    intro D
    simp only [Dg, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul,
      Polynomial.eval_comp, Polynomial.eval_ofNat, Polynomial.eval_one]
  have hPeval : ∀ D : ℕ, P.eval D = Dg.eval D + Pd1.eval D := by
    intro D; simp only [P, Polynomial.eval_add]
  have hDgP : ∀ D : ℕ, Dg.eval D ≤ P.eval D := fun D => by
    rw [hPeval D, hDgeval D]; omega
  have hPD : ∀ D : ℕ, D ≤ P.eval D := fun D => by rw [hPeval D, hDgeval D]; omega
  have hPPp : ∀ D : ℕ, Pp.eval D ≤ P.eval D := fun D => by rw [hPeval D, hDgeval D]; omega
  have hPPe1 : ∀ D : ℕ, Pe1.eval D ≤ P.eval D := fun D => by rw [hPeval D, hDgeval D]; omega
  have hPPe2 : ∀ D : ℕ, Pe2.eval D ≤ P.eval D := fun D => by rw [hPeval D, hDgeval D]; omega
  have hPDq : ∀ D : ℕ, Dq.eval D ≤ P.eval D := fun D => by rw [hPeval D, hDgeval D]; omega
  have hPB : ∀ D : ℕ, Btot.eval (Dq.eval D) ≤ P.eval D := fun D => by
    rw [hPeval D, hDgeval D]; omega
  have hPPs : ∀ D : ℕ, Ps.eval (Dq.eval D) ≤ P.eval D := fun D => by
    rw [hPeval D, hDgeval D]; omega
  have hP3 : ∀ D : ℕ, 3 * Dq.eval D + 2 ≤ P.eval D := fun D => by
    rw [hPeval D, hDgeval D]; omega
  have hPrP : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ P.eval D := fun D => by
    have h1 : Pr.eval (Pp.eval D) ≤ Pr.eval (1 * (D + Pp.eval D)) :=
      Work.WilE7.coreLT_succ.eval_mono_nat Pr (by omega)
    exact le_trans (le_trans h1 (hPe1 D)) (hPPe1 D)
  have hPfP : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ P.eval D := fun D => by
    have h1 : Pf.eval (Pp.eval D) ≤ Pf.eval (1 * (D + Pp.eval D)) :=
      Work.WilE7.coreLT_succ.eval_mono_nat Pf (by omega)
    exact le_trans (le_trans h1 (hPe2 D)) (hPPe2 D)
  have hDgPr : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ Dg.eval D := fun D => by
    have h1 : Pr.eval (Pp.eval D) ≤ Pr.eval (1 * (D + Pp.eval D)) :=
      Work.WilE7.coreLT_succ.eval_mono_nat Pr (by omega)
    refine le_trans (le_trans h1 (hPe1 D)) ?_
    rw [hDgeval D]; omega
  have hDgPf : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ Dg.eval D := fun D => by
    have h1 : Pf.eval (Pp.eval D) ≤ Pf.eval (1 * (D + Pp.eval D)) :=
      Work.WilE7.coreLT_succ.eval_mono_nat Pf (by omega)
    refine le_trans (le_trans h1 (hPe2 D)) ?_
    rw [hDgeval D]; omega
  have hPdz : ∀ D : ℕ, BZl.eval (Dq.eval D + Dg.eval D) ≤ P.eval D := fun D => by
    have h2 : (Dq + Dg).eval D = Dq.eval D + Dg.eval D := by rw [Polynomial.eval_add]
    have h1 : BZl.eval (Dq.eval D + Dg.eval D) ≤ BZl.eval (1 * (D + (Dq + Dg).eval D)) := by
      refine Work.WilE7.coreLT_succ.eval_mono_nat BZl ?_
      rw [h2, one_mul]; omega
    exact le_trans (le_trans h1 (hPd1 D)) (by rw [hPeval D]; omega)
  -- the length polynomials
  have hAevalZero : ∀ (q : Polynomial ℕ) (D k : ℕ),
      MvPolynomial.eval ![D, k] (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) q) = q.eval D := by
    intro q D k
    rw [Work.WilE7.eval_aeval_X_zero]
    rfl
  let Ncan2 : MvPolynomial (Fin 2) ℕ := Np *
    Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Pr.comp Pp + Pf.comp Pp + Polynomial.C 2)
  have hNcan2 : ∀ D k : ℕ, MvPolynomial.eval ![D, k] Ncan2 =
      MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2) := by
    intro D k
    have h1 := hAevalZero (Pr.comp Pp + Pf.comp Pp + Polynomial.C 2) D k
    simp only [Ncan2, map_mul, h1, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_comp]
  let Nlow2 : MvPolynomial (Fin 2) ℕ := Np *
    Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Pf.comp Pp + Polynomial.C K)
  have hNlow2 : ∀ D k : ℕ, MvPolynomial.eval ![D, k] Nlow2 =
      MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K) := by
    intro D k
    have h1 := hAevalZero (Pf.comp Pp + Polynomial.C K) D k
    simp only [Nlow2, map_mul, h1, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_comp]
  have hCan : PolyShape (fun D k => MvPolynomial.eval ![D, k] Ncan2) :=
    PolyShape.mvpoly Ncan2
  let Nsig2 : MvPolynomial (Fin 2) ℕ := (E2B.poly_dominate3b Qtot Dq
    (fun D k => MvPolynomial.eval ![D, k] Ncan2) (fun D k => MvPolynomial.eval ![D, k] Np)
    hCan (PolyShape.mvpoly Np)).choose +
    Np * (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Polynomial.C (K + 1) + P))
  have hNsig2' : ∀ D k : ℕ, MvPolynomial.eval ![Dq.eval D, MvPolynomial.eval ![D, k] Ncan2,
      MvPolynomial.eval ![D, k] Np] Qtot ≤ MvPolynomial.eval ![D, k] Nsig2 := by
    intro D k
    have h := (E2B.poly_dominate3b Qtot Dq (fun D k => MvPolynomial.eval ![D, k] Ncan2)
      (fun D k => MvPolynomial.eval ![D, k] Np) hCan (PolyShape.mvpoly Np)).choose_spec D k
    simp only [Nsig2, map_add] at h ⊢
    exact le_trans h (Nat.le_add_right _ _)
  have hNsig : ∀ D k : ℕ, MvPolynomial.eval
      ![Dq.eval D, MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2),
        MvPolynomial.eval ![D, k] Np] Qtot ≤ MvPolynomial.eval ![D, k] Nsig2 := by
    intro D k
    refine le_trans ?_ (hNsig2' D k)
    rw [hNcan2]
  let Nk : MvPolynomial (Fin 3) ℕ :=
    MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) (Np * Nsig2)
  have hNk : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Nk =
      MvPolynomial.eval ![D, k] Np * MvPolynomial.eval ![D, k] Nsig2 := by
    intro D k l
    rw [show Nk = MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) (Np * Nsig2) from rfl,
      eval_rename3, map_mul]
  let Nl : MvPolynomial (Fin 3) ℕ :=
    MvPolynomial.X (2 : Fin 3) +
      (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2 +
        MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Nsig2 +
        MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Nlow2) +
      (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2 +
        MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2)
  have hNlE : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Nl =
      l + (MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) +
        (MvPolynomial.eval ![D, k] Nsig2 + MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K)) +
        ((MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) +
         MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) := by
    intro D k l
    have h1 : MvPolynomial.eval ![D, k, l]
        (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2) =
        MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2) := by
      rw [eval_rename3, hNcan2]
    have h2 : MvPolynomial.eval ![D, k, l]
        (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Nlow2) =
        MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K) := by
      rw [eval_rename3, hNlow2]
    have h3 : MvPolynomial.eval ![D, k, l]
        (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Nsig2) =
        MvPolynomial.eval ![D, k] Nsig2 := eval_rename3 Nsig2 D k l
    simp only [Nl, map_add, MvPolynomial.eval_X, h1, h2, h3]
    rw [show (![D, k, l] : Fin 3 → ℕ) 2 = l from rfl]
    ring
  have hNl : ∀ D k l : ℕ, l ≤ MvPolynomial.eval ![D, k, l] Nl := by
    intro D k l
    rw [hNlE D k l]; omega
  let Ng : MvPolynomial (Fin 3) ℕ := 3 + 2 *
    (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2 *
      Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (Ps.comp Dq))
  have hNg : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Ng =
      3 + 2 * ((MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) *
        Ps.eval (Dq.eval D)) := by
    intro D k l
    have h1 : MvPolynomial.eval ![D, k, l]
        (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2) =
        MvPolynomial.eval ![D, k] Ncan2 := eval_rename3 _ D k l
    have hAevalZero3 : ∀ (q : Polynomial ℕ) (v : Fin 3 → ℕ),
        MvPolynomial.eval v (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) q) = q.eval (v 0) := by
      intro q v
      have h := Polynomial.aeval_algHom_apply
        (f := (MvPolynomial.aeval v : MvPolynomial (Fin 3) ℕ →ₐ[ℕ] ℕ))
        (x := MvPolynomial.X (0 : Fin 3)) (p := q)
      simp only [MvPolynomial.aeval_X] at h
      rw [← MvPolynomial.aeval_eq_eval, ← h]
      rfl
    have h2 : MvPolynomial.eval ![D, k, l]
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 3)) (Ps.comp Dq)) = Ps.eval (Dq.eval D) := by
      rw [hAevalZero3, Polynomial.eval_comp]
      rfl
    simp only [Ng, map_add, map_mul, map_ofNat, h1, h2, hNcan2]
  exact ⟨Ap, Pp, Np, Ar, Pr, Af, Pf, As, Ps, Ac, Fp, Dq, Atot, Btot, Qtot, FZ, AZl, BZl,
    Nsig2, M2, Ft, Fp0, Dg, P, Nk, Nl, Ng, hDq, hPD, hPPp, hPrP, hPfP, hPDq, hPB, hPPs, hP3,
    hDgPr, hDgPf, hPdz, rfl, rfl, rfl, rfl, rfl, rfl, hNl, hNlE, hNk, hNg, hNsig⟩

/-- The identification of the constants of `e2bConst` with the producer outputs. -/
theorem e2bEqs (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6)
    (h0 : FrontierRestrat) (h1 : SigmaVPairs) (n K F : ℕ) :
    EqSpec (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) hFC hE2 hE5 hE6 h0 h1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end

end Work.WilE7.Endgame.E2B
