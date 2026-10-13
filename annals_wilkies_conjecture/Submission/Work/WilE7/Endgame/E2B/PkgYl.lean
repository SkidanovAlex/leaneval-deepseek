/-
  Area E7 / E2B, node `cellRefine_of_nodesB`: **the `Y'`-family of the package `E2Pkg`**.

  On top of `SigmaPart` (`PkgSigma.lean`) this module builds the packing `Y'` of the raw list
  (the outer `Y`, the candidates, the pieces, the `Σout`-members, the unpadded `Σlow` members
  and the `±1`-slices), proves `specY`/`specYout` and the length bound `Nl`.  The file-size guard
  forces this to be a module of its own.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.PkgSigma

namespace Work.WilE7.Endgame.E2B

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Classical

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

theorem e2bYlPart (hFC : Work.WilE7.CoreLTSuccPlan.HypFC) (hE2 : Work.WilE7.CoreLTSuccPlan.HypE2)
    (hE5 : Work.WilE7.CoreLTSuccPlan.HypE5) (hE6 : Work.WilE7.CoreLTSuccPlan.HypE6)
    (h0 : Work.WilE7.CoreLTSuccPlan.FrontierRestrat) (h1 : Work.WilE7.CoreLTSuccPlan.SigmaVPairs)
    (n K F : ℕ) (D k l m m' : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m))
    (Y : Fin l → WilkiesDesign.E.SemiPf (n + m'))
    (hX : ∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D)
    (hY : ∀ i, (Y i).fmt ≤ F ∧ (Y i).deg ≤ D)
    (hND : ∀ i, Work.WilE7.MainDesign.NullDimLT
      (Work.WilE7.MainDesign.basePr n m '' (X i).set) (K + 1))
    (hk : 0 < k) (T : SigmaPart (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) D k m X) :
    ∃ Yl : List (WilkiesDesign.E.SemiPf (n + (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2)),
      ((∀ i : Fin Yl.length, (Yl.get i).fmt ≤ (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).Fp0 ∧
          (Yl.get i).deg ≤ (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).P.eval D) ∧
        (∀ Sv ∈ T.base.Cand, ∃ i : Fin Yl.length,
          projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
            projFirst n (m + 1) '' absSet Sv) ∧
        (∀ Z ∈ T.Sig, ∃ i : Fin Yl.length,
          projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
            projFirst n (pPair n m) '' Z.set) ∧
        (∀ (q : Fin T.base.PieceList.length) (r : Fin K), ∃ i : Fin Yl.length,
          projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
            projFirst n (m + 1) '' (T.base.SloR q r).set) ∧
        (∀ (q : Fin T.base.PieceList.length) (Yc : SemiPf (n + (m + 1))), Yc ∈ T.base.Ly q →
          ∃ i : Fin Yl.length,
            projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
              projFirst n (m + 1) '' Yc.set) ∧
        (∀ Sv ∈ T.base.Cand, ∃ i : Fin Yl.length,
          projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
            projFirst n (m + 1) '' (E2.sliceSemiPf Sv 1).set) ∧
        (∀ Sv ∈ T.base.Cand, ∃ i : Fin Yl.length,
          projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
            projFirst n (m + 1) '' (E2.sliceSemiPf Sv (-1)).set) ∧
        (∀ j : Fin l, ∃ i : Fin Yl.length,
          projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
            projFirst n m' '' (Y j).set) ∧
        (∀ U ∈ T.base.PieceList, ∃ i : Fin Yl.length,
          projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
            projFirst n (m + 1) '' absSet U)) ∧
      (Yl.length ≤ MvPolynomial.eval ![D, k, l] (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).Nl ∧
        (∀ i : Fin Yl.length, (Yl.get i).fmt ≤ (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).Fp0 ∧
          (Yl.get i).deg ≤ (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).P.eval D) ∧
        (∀ j : Fin l, ∃ j' : Fin Yl.length,
          projFirst n m' '' (Y j).set =
            projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get j').set)) := by

  classical
  let c : E2Const n K F := e2bConst hFC hE2 hE5 hE6 h0 h1 n K F
  -- ## §0  the constants, chosen exactly as in the definition of `e2bConst`
  let Ap : ℕ := (E2_pieces_of_family hFC hE5 F).choose
  let Pp : Polynomial ℕ := (E2_pieces_of_family hFC hE5 F).choose_spec.choose
  let Np : MvPolynomial (Fin 2) ℕ :=
    (E2_pieces_of_family hFC hE5 F).choose_spec.choose_spec.choose
  let Ar : ℕ := (E2_rank_strata hE5 Ap).choose
  let Pr : Polynomial ℕ := (E2_rank_strata hE5 Ap).choose_spec.choose
  let Af : ℕ := (E2_frontier_strata h0 Ap).choose
  let Pf : Polynomial ℕ := (E2_frontier_strata h0 Ap).choose_spec.choose
  let Ps : Polynomial ℕ := (E2_sheets_of_stratum hE2 (Ap + Ar + Af)).choose_spec.choose
  let Ac : ℕ := Ap + Ar + Af
  let Fp : ℕ := 2 * Ac
  let Dq : Polynomial ℕ := Pp + Pr.comp Pp + Pf.comp Pp + 1
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
  let Dg : Polynomial ℕ :=
    Polynomial.X + Pp + Pe1 + Pe2 + (3 * Dq + 2) + (Btot.comp Dq) + (Ps.comp Dq) + 1
  let Pd1 : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 BZl (Dq + Dg)).choose
  let P : Polynomial ℕ := Dg + Pd1
  let Ncan2 : MvPolynomial (Fin 2) ℕ := Np *
    Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Pr.comp Pp + Pf.comp Pp + Polynomial.C 2)
  let Nlow2 : MvPolynomial (Fin 2) ℕ := Np *
    Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Pf.comp Pp + Polynomial.C K)
  let Nsig2 : MvPolynomial (Fin 2) ℕ := (E2B.poly_dominate3b Qtot Dq
      (fun D k => MvPolynomial.eval ![D, k] Ncan2) (fun D k => MvPolynomial.eval ![D, k] Np)
      (PolyShape.mvpoly Ncan2) (PolyShape.mvpoly Np)).choose
    + Np * (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Polynomial.C (K + 1) + P))
  let Nk : MvPolynomial (Fin 3) ℕ :=
    MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) (Np * Nsig2)
  let Nl : MvPolynomial (Fin 3) ℕ :=
    MvPolynomial.X (2 : Fin 3) +
      (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2 +
        MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Nsig2 +
        MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Nlow2) +
      (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2 +
        MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) Ncan2)
  have hmF : m ≤ F := by
    have h := (hX ⟨0, hk⟩).1
    simp only [WilkiesDesign.E.SemiPf.fmt] at h
    omega
  have hM2_eq' : M2 = (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 := rfl
  have hFp0_eq' : Fp0 = (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).Fp0 := rfl
  have hP_eq' : P = (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).P := rfl
  have hNl_eq' : Nl = (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).Nl := rfl
  -- ## §1  the interface facts in the vocabulary of the producer outputs
  have hDq_l : ∀ D : ℕ, Dq.eval D = Pp.eval D + Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 1 := by
    intro D
    simp only [show Dq = Pp + Pr.comp Pp + Pf.comp Pp + 1 from rfl, Polynomial.eval_add,
      Polynomial.eval_comp, Polynomial.eval_one]
  have hPpDq : ∀ D : ℕ, Pp.eval D ≤ Dq.eval D := by
    intro D
    rw [hDq_l D]
    omega
  have hPPp_l : ∀ D : ℕ, Pp.eval D ≤ P.eval D := c.hPPp
  have hPrP_l : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ P.eval D := c.hPrP
  have hPfP_l : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ P.eval D := c.hPfP
  have hPD_l : ∀ D : ℕ, D ≤ P.eval D := c.hPD
  have hPDq_l : ∀ D : ℕ, Dq.eval D ≤ P.eval D := c.hPDq
  have hPB_l : ∀ D : ℕ, Btot.eval (Dq.eval D) ≤ P.eval D := c.hPB
  have hP3_l : ∀ D : ℕ, 3 * Dq.eval D + 2 ≤ P.eval D := c.hP3
  have hPdz_l : ∀ D : ℕ, BZl.eval (Dq.eval D + Dg.eval D) ≤ P.eval D := c.hPdz
  have hNk_l : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Nk =
      MvPolynomial.eval ![D, k] Np * MvPolynomial.eval ![D, k] Nsig2 := c.hNk
  have hNl_l : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Nl =
      l + (MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) +
        (MvPolynomial.eval ![D, k] Nsig2 +
          MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K)) +
        ((MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) +
         MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) := c.hNlE
  have hPLlen : T.base.PieceList.length ≤ MvPolynomial.eval ![D, k] Np := T.base.specPieceLen
  have hPLmem : ∀ U ∈ T.base.PieceList, U.Good ∧ U.X.fmt ≤ Ap ∧ U.deg ≤ Pp.eval D ∧
      n + (m + 1) - U.j ≤ K + 1 ∧ (∀ z ∈ U.X.set, projRank U z ≤ K) := T.base.specPL
  have hCandLenS : T.base.Cand.length ≤ MvPolynomial.eval ![D, k] Np * Pr.eval (Pp.eval D)
      + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D)
      + MvPolynomial.eval ![D, k] Np := T.base.specCandLenS
  have hCandMem : ∀ Sv ∈ T.base.Cand, Sv.Good ∧ Sv.X.fmt ≤ Ac ∧ Sv.deg ≤ Dq.eval D ∧
      n + (m + 1) - Sv.j ≤ K ∧ (∀ z ∈ Sv.X.set, projRank Sv z = n + (m + 1) - Sv.j) :=
    T.base.specCand
  have hPieFmt : ∀ p ∈ T.base.Pie, (p.2).X.fmt ≤ Ap :=
    fun p hp => (T.base.specPieces.2.2.1 p hp).2.1
  have hPieFZ : ∀ p ∈ T.base.Pie, (p.2).X.fmt ≤ FZ := T.hPieFZ
  have hPieDeg : ∀ p ∈ T.base.Pie, (p.2).deg ≤ Dq.eval D := by
    intro p hp
    exact le_trans (T.base.specPieces.2.2.1 p hp).2.2.1 (hPpDq D)
  have hSigFZ : ∀ Z ∈ T.Sig, Z.fmt ≤ FZ := T.hSigFZ
  have hSigND : ∀ Z ∈ T.Sig, NullDimLT (projFirst n (pPair n m) '' Z.set) K := T.hSigND
  have hSigDegDg : ∀ Z ∈ T.Sig, Z.deg ≤ Dg.eval D := T.hSigDegDg
  have hSigOutFmt : ∀ Z ∈ T.SigOut, Z.fmt ≤ Ft := T.hSigOutFmt
  have hSigOutLen : T.SigOut.length ≤ MvPolynomial.eval ![D, k] Nsig2 := T.hSigOutLen
  have hSloFmt : ∀ (q : Fin T.base.PieceList.length) (r : Fin K),
      (T.base.SloR q r).fmt ≤ Ac := fun q r => le_trans (T.base.specSloR q r).1 (by
        show Ar ≤ Ap + Ar + Af
        omega)
  have hSloDeg : ∀ (q : Fin T.base.PieceList.length) (r : Fin K),
      (T.base.SloR q r).deg ≤ Pr.eval (Pp.eval D) :=
    fun q r => (T.base.specSloR q r).2.1
  have hSloND : ∀ (q : Fin T.base.PieceList.length) (r : Fin K),
      NullDimLT (projFirst n (m + 1) '' (T.base.SloR q r).set) K :=
    fun q r => (T.base.specSloR q r).2.2.2
  have hLyFmt : ∀ (q : Fin T.base.PieceList.length) (Z : SemiPf (n + (m + 1))),
      Z ∈ T.base.Ly q → Z.fmt ≤ Ac := fun q Z hZ => le_trans ((T.base.specLy q).2.1 Z hZ).1 (by
        show Af ≤ Ap + Ar + Af
        omega)
  have hLyDeg : ∀ (q : Fin T.base.PieceList.length) (Z : SemiPf (n + (m + 1))),
      Z ∈ T.base.Ly q → Z.deg ≤ Pf.eval (Pp.eval D) :=
    fun q Z hZ => ((T.base.specLy q).2.1 Z hZ).2.1
  have hLyND : ∀ (q : Fin T.base.PieceList.length) (Z : SemiPf (n + (m + 1))),
      Z ∈ T.base.Ly q → NullDimLT (projFirst n (m + 1) '' Z.set) K :=
    fun q Z hZ => ((T.base.specLy q).2.1 Z hZ).2.2
  have hLylen : ∀ q : Fin T.base.PieceList.length, (T.base.Ly q).length ≤ Pf.eval (Pp.eval D) :=
    fun q => (T.base.specLy q).1
  -- ## §3  the `Y'`-family: the packing of the raw list
  let Slices : List (SemiPf (n + (m + 1))) :=
    T.base.Cand.map (fun Sv => E2.sliceSemiPf Sv 1) ++ T.base.Cand.map (fun Sv => E2.sliceSemiPf Sv (-1))
  let Low : List (SemiPf (n + (m + 1))) :=
    (List.ofFn (fun q : Fin T.base.PieceList.length => List.ofFn (T.base.SloR q))).flatten
      ++ (List.ofFn T.base.Ly).flatten
  let BlkY : List (Σ r : ℕ, SemiPf (n + r)) :=
    (List.ofFn Y).map (fun Z => (⟨m', Z⟩ : Σ r : ℕ, SemiPf (n + r)))
  let BlkC : List (Σ r : ℕ, SemiPf (n + r)) :=
    T.base.Cand.map (fun Sv => (⟨m + 1, E2.stratumSemiPf Sv⟩ : Σ r : ℕ, SemiPf (n + r)))
  let BlkP : List (Σ r : ℕ, SemiPf (n + r)) :=
    T.base.PieceList.map (fun T => (⟨m + 1, E2.stratumSemiPf T⟩ : Σ r : ℕ, SemiPf (n + r)))
  let BlkS : List (Σ r : ℕ, SemiPf (n + r)) :=
    T.SigOut.map (fun Z => (⟨pPair n m, Z⟩ : Σ r : ℕ, SemiPf (n + r)))
  let BlkL : List (Σ r : ℕ, SemiPf (n + r)) :=
    Low.map (fun Z => (⟨m + 1, Z⟩ : Σ r : ℕ, SemiPf (n + r)))
  let BlkX : List (Σ r : ℕ, SemiPf (n + r)) :=
    Slices.map (fun Z => (⟨m + 1, Z⟩ : Σ r : ℕ, SemiPf (n + r)))
  let Raw : List (Σ r : ℕ, SemiPf (n + r)) := BlkY ++ BlkC ++ BlkP ++ BlkS ++ BlkL ++ BlkX
  have hSloLmem : ∀ Z ∈ (List.ofFn (fun q : Fin T.base.PieceList.length =>
      List.ofFn (T.base.SloR q))).flatten,
      ∃ (q : Fin T.base.PieceList.length) (r : Fin K), Z = T.base.SloR q r := by
    intro Z hZ
    rw [List.mem_flatten] at hZ
    obtain ⟨L, hL, hZL⟩ := hZ
    rw [List.mem_ofFn] at hL
    obtain ⟨q, rfl⟩ := hL
    obtain ⟨r, hr⟩ := List.mem_ofFn.mp hZL
    exact ⟨q, r, hr.symm⟩
  have hLyLmem : ∀ Z ∈ (List.ofFn T.base.Ly).flatten,
      ∃ q : Fin T.base.PieceList.length, Z ∈ T.base.Ly q := by
    intro Z hZ
    rw [List.mem_flatten] at hZ
    obtain ⟨L, hL, hZL⟩ := hZ
    rw [List.mem_ofFn] at hL
    obtain ⟨q, rfl⟩ := hL
    exact ⟨q, hZL⟩
  have hLowMem : ∀ Z ∈ Low, Z.fmt ≤ Ac ∧ Z.deg ≤ P.eval D ∧
      NullDimLT (projFirst n (m + 1) '' Z.set) K := by
    intro Z hZ
    dsimp only [Low] at hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · obtain ⟨q, r, rfl⟩ := hSloLmem Z hZ
      exact ⟨hSloFmt q r, le_trans (hSloDeg q r) (hPrP_l D), hSloND q r⟩
    · obtain ⟨q, hq⟩ := hLyLmem Z hZ
      exact ⟨hLyFmt q Z hq, le_trans (hLyDeg q Z hq) (hPfP_l D), hLyND q Z hq⟩
  have hSloL_mem : ∀ (q : Fin T.base.PieceList.length) (r : Fin K),
      T.base.SloR q r ∈ Low := by
    intro q r
    dsimp only [Low]
    rw [List.mem_append]
    left
    exact List.mem_flatten.mpr ⟨List.ofFn (T.base.SloR q), List.mem_ofFn.mpr ⟨q, rfl⟩,
      List.mem_ofFn.mpr ⟨r, rfl⟩⟩
  have hLyL_mem : ∀ (q : Fin T.base.PieceList.length) (Z : SemiPf (n + (m + 1))),
      Z ∈ T.base.Ly q → Z ∈ Low := by
    intro q Z hZ
    dsimp only [Low]
    rw [List.mem_append]
    right
    exact List.mem_flatten.mpr ⟨T.base.Ly q, List.mem_ofFn.mpr ⟨q, rfl⟩, hZ⟩
  have hRawDim : ∀ x ∈ Raw, x.1 ≤ M2 := by
    intro x hx
    dsimp only [Raw] at hx
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
    · dsimp only [BlkY] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      rw [List.mem_ofFn] at hZ
      obtain ⟨j, rfl⟩ := hZ
      have h := (hY j).1
      simp only [WilkiesDesign.E.SemiPf.fmt] at h
      simp only [M2]
      omega
    · dsimp only [BlkC] at hx
      rw [List.mem_map] at hx
      obtain ⟨Sv, -, rfl⟩ := hx
      simp only [M2]
      omega
    · dsimp only [BlkP] at hx
      rw [List.mem_map] at hx
      obtain ⟨T, -, rfl⟩ := hx
      simp only [M2]
      omega
    · dsimp only [BlkS] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, -, rfl⟩ := hx
      simp only [M2, pPair]
      omega
    · dsimp only [BlkL] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, -, rfl⟩ := hx
      simp only [M2]
      omega
    · dsimp only [BlkX] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, -, rfl⟩ := hx
      simp only [M2]
      omega
  have hApAc : Ap ≤ Ac := by
    show Ap ≤ Ap + Ar + Af
    omega
  have hArAc2 : Ar ≤ Ac := by
    show Ar ≤ Ap + Ar + Af
    omega
  have hAfAc2 : Af ≤ Ac := by
    show Af ≤ Ap + Ar + Af
    omega
  have hAcFt : Ac ≤ Ft := by
    show Ac ≤ max (max Ac Atot) F
    exact le_trans (le_max_left Ac Atot) (le_max_left (max Ac Atot) F)
  have hFFt : F ≤ Ft := by
    show F ≤ max (max Ac Atot) F
    exact le_max_right _ _
  have hRawFmt : ∀ x ∈ Raw, x.2.fmt ≤ Ft := by
    intro x hx
    dsimp only [Raw] at hx
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
    · dsimp only [BlkY] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      rw [List.mem_ofFn] at hZ
      obtain ⟨j, rfl⟩ := hZ
      exact le_trans (hY j).1 hFFt
    · dsimp only [BlkC] at hx
      rw [List.mem_map] at hx
      obtain ⟨Sv, hSv, rfl⟩ := hx
      rw [E2.stratumSemiPf_fmt]
      have hfmt : (n + (m + 1)) + Sv.X.r ≤ Ac := by
        simpa only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add] using (hCandMem Sv hSv).2.1
      exact le_trans hfmt hAcFt
    · dsimp only [BlkP] at hx
      rw [List.mem_map] at hx
      obtain ⟨U, hU, rfl⟩ := hx
      rw [E2.stratumSemiPf_fmt]
      have hfmt : (n + (m + 1)) + U.X.r ≤ Ac := by
        simpa only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add] using le_trans (hPLmem U hU).2.1 hApAc
      exact le_trans hfmt hAcFt
    · dsimp only [BlkS] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      exact hSigOutFmt Z hZ
    · dsimp only [BlkL] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      exact le_trans (hLowMem Z hZ).1 hAcFt
    · dsimp only [BlkX] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      rcases List.mem_append.mp hZ with hZ | hZ
      · rw [List.mem_map] at hZ
        obtain ⟨Sv, hSv, rfl⟩ := hZ
        refine le_trans (E2.sliceSemiPf_fmt Sv 1) ?_
        have hfmt : (n + (m + 1)) + Sv.X.r ≤ Ac := by
          simpa only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add] using (hCandMem Sv hSv).2.1
        exact le_trans hfmt hAcFt
      · rw [List.mem_map] at hZ
        obtain ⟨Sv, hSv, rfl⟩ := hZ
        refine le_trans (E2.sliceSemiPf_fmt Sv (-1)) ?_
        have hfmt : (n + (m + 1)) + Sv.X.r ≤ Ac := by
          simpa only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add] using (hCandMem Sv hSv).2.1
        exact le_trans hfmt hAcFt
  have hRawDeg : ∀ x ∈ Raw, x.2.deg ≤ P.eval D := by
    intro x hx
    dsimp only [Raw] at hx
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hx
    rcases hx with ((((hx | hx) | hx) | hx) | hx) | hx
    · dsimp only [BlkY] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      rw [List.mem_ofFn] at hZ
      obtain ⟨j, rfl⟩ := hZ
      exact le_trans (hY j).2 (hPD_l D)
    · dsimp only [BlkC] at hx
      rw [List.mem_map] at hx
      obtain ⟨Sv, hSv, rfl⟩ := hx
      rw [E2.stratumSemiPf_deg]
      exact le_trans (stratum_Xdeg_le_deg Sv) (le_trans (hCandMem Sv hSv).2.2.1 (hPDq_l D))
    · dsimp only [BlkP] at hx
      rw [List.mem_map] at hx
      obtain ⟨U, hU, rfl⟩ := hx
      rw [E2.stratumSemiPf_deg]
      exact le_trans (stratum_Xdeg_le_deg U) (le_trans (hPLmem U hU).2.2.1 (hPPp_l D))
    · dsimp only [BlkS] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      exact T.hSigOutDeg Z hZ
    · dsimp only [BlkL] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      exact (hLowMem Z hZ).2.1
    · dsimp only [BlkX] at hx
      rw [List.mem_map] at hx
      obtain ⟨Z, hZ, rfl⟩ := hx
      rcases List.mem_append.mp hZ with hZ | hZ
      · rw [List.mem_map] at hZ
        obtain ⟨Sv, hSv, rfl⟩ := hZ
        have h1 : Sv.X.deg ≤ Dq.eval D :=
          le_trans (stratum_Xdeg_le_deg Sv) (hCandMem Sv hSv).2.2.1
        have h3 : 3 * Sv.X.deg + 2 ≤ P.eval D := by
          have := hP3_l D
          omega
        exact le_trans (E2.sliceSemiPf_deg Sv 1) h3
      · rw [List.mem_map] at hZ
        obtain ⟨Sv, hSv, rfl⟩ := hZ
        have h1 : Sv.X.deg ≤ Dq.eval D :=
          le_trans (stratum_Xdeg_le_deg Sv) (hCandMem Sv hSv).2.2.1
        have h3 : 3 * Sv.X.deg + 2 ≤ P.eval D := by
          have := hP3_l D
          omega
        exact le_trans (E2.sliceSemiPf_deg Sv (-1)) h3
  obtain ⟨Yl, hYllen, hYlmem, hYlrep⟩ := E2B.packRaw M2 Raw hRawDim Ft hRawFmt D P hRawDeg
  have hYlFmt : ∀ i : Fin Yl.length, (Yl.get i).fmt ≤ Fp0 := by
    intro i
    have h := (hYlmem _ (List.get_mem Yl i)).1
    refine le_trans h ?_
    have h2 : Fp0 = max AZl (Ft + M2) := rfl
    rw [h2]
    exact le_max_right _ _
  have hYlDeg : ∀ i : Fin Yl.length, (Yl.get i).deg ≤ P.eval D :=
    fun i => (hYlmem _ (List.get_mem Yl i)).2
  -- ## §3b  the representatives of the raw blocks in `Yl`
  have hRepY : ∀ j : Fin l, ∃ i : Fin Yl.length,
      projFirst n M2 '' (Yl.get i).set = projFirst n m' '' (Y j).set := by
    intro j
    have hmem : (⟨m', Y j⟩ : Σ r : ℕ, SemiPf (n + r)) ∈ Raw := by
      dsimp only [Raw, BlkY]
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append]
      left; left; left; left; left
      exact List.mem_map.mpr ⟨Y j, List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩
    obtain ⟨i, -, hproj⟩ := hYlrep _ hmem
    exact ⟨i, hproj⟩
  have hRepCand : ∀ Sv ∈ T.base.Cand, ∃ i : Fin Yl.length,
      projFirst n M2 '' (Yl.get i).set = projFirst n (m + 1) '' absSet Sv := by
    intro Sv hSv
    have hmem : (⟨m + 1, E2.stratumSemiPf Sv⟩ : Σ r : ℕ, SemiPf (n + r)) ∈ Raw := by
      dsimp only [Raw, BlkC]
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append]
      left; left; left; left; right
      exact List.mem_map.mpr ⟨Sv, hSv, rfl⟩
    obtain ⟨i, -, hproj⟩ := hYlrep _ hmem
    exact ⟨i, by rw [hproj, E2.stratumSemiPf_set]⟩
  have hRepPiece : ∀ U ∈ T.base.PieceList, ∃ i : Fin Yl.length,
      projFirst n M2 '' (Yl.get i).set = projFirst n (m + 1) '' absSet U := by
    intro U hU
    have hmem : (⟨m + 1, E2.stratumSemiPf U⟩ : Σ r : ℕ, SemiPf (n + r)) ∈ Raw := by
      dsimp only [Raw, BlkP]
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append]
      left; left; left; right
      exact List.mem_map.mpr ⟨U, hU, rfl⟩
    obtain ⟨i, -, hproj⟩ := hYlrep _ hmem
    exact ⟨i, by rw [hproj, E2.stratumSemiPf_set]⟩
  have hRepSigOut : ∀ Z ∈ T.SigOut, ∃ i : Fin Yl.length,
      projFirst n M2 '' (Yl.get i).set = projFirst n (pPair n m) '' Z.set := by
    intro Z hZ
    have hmem : (⟨pPair n m, Z⟩ : Σ r : ℕ, SemiPf (n + r)) ∈ Raw := by
      dsimp only [Raw, BlkS]
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append]
      left; left; right
      exact List.mem_map.mpr ⟨Z, hZ, rfl⟩
    obtain ⟨i, -, hproj⟩ := hYlrep _ hmem
    exact ⟨i, hproj⟩
  have hRepLow : ∀ Z ∈ Low, ∃ i : Fin Yl.length,
      projFirst n M2 '' (Yl.get i).set = projFirst n (m + 1) '' Z.set := by
    intro Z hZ
    have hmem : (⟨m + 1, Z⟩ : Σ r : ℕ, SemiPf (n + r)) ∈ Raw := by
      dsimp only [Raw, BlkL]
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append]
      left; right
      exact List.mem_map.mpr ⟨Z, hZ, rfl⟩
    obtain ⟨i, -, hproj⟩ := hYlrep _ hmem
    exact ⟨i, hproj⟩
  have hRepSlice : ∀ (Sv : Stratum 0 (n + (m + 1))) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      Sv ∈ T.base.Cand →
      ∃ i : Fin Yl.length,
        projFirst n M2 '' (Yl.get i).set = projFirst n (m + 1) '' (E2.sliceSemiPf Sv σ).set := by
    intro Sv σ hσ hSv
    have hmem : (⟨m + 1, E2.sliceSemiPf Sv σ⟩ : Σ r : ℕ, SemiPf (n + r)) ∈ Raw := by
      dsimp only [Raw, BlkX]
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append, List.mem_append]
      right
      refine List.mem_map.mpr ⟨E2.sliceSemiPf Sv σ, ?_, rfl⟩
      dsimp only [Slices]
      rw [List.mem_append]
      rcases hσ with hσ | hσ
      · left
        subst hσ
        exact List.mem_map.mpr ⟨Sv, hSv, rfl⟩
      · right
        subst hσ
        exact List.mem_map.mpr ⟨Sv, hSv, rfl⟩
    obtain ⟨i, -, hproj⟩ := hYlrep _ hmem
    exact ⟨i, hproj⟩
  -- ## §4  the arithmetic bounds
  have hYlLen : Yl.length ≤ MvPolynomial.eval ![D, k, l] Nl := by
    have hSlicesLen : Slices.length = 2 * T.base.Cand.length := by
      dsimp only [Slices]
      rw [List.length_append, List.length_map, List.length_map]
      ring
    have hRawLen : Raw.length = l + T.base.Cand.length + T.base.PieceList.length
        + T.SigOut.length + Low.length + Slices.length := by
      dsimp only [Raw, BlkY, BlkC, BlkP, BlkS, BlkL, BlkX]
      simp only [List.length_append, List.length_map, List.length_ofFn]
    have hLowLen : Low.length ≤ MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K) := by
      have h1 : (List.ofFn (fun q : Fin T.base.PieceList.length =>
          List.ofFn (T.base.SloR q))).flatten.length ≤ T.base.PieceList.length * K := by
        have h := length_flatten_le
          (List.ofFn (fun q : Fin T.base.PieceList.length => List.ofFn (T.base.SloR q))) K
          (fun x hx => by
            rw [List.mem_ofFn] at hx
            obtain ⟨q, rfl⟩ := hx
            simp)
        simpa only [List.length_ofFn] using h
      have h2 : (List.ofFn T.base.Ly).flatten.length ≤
          T.base.PieceList.length * Pf.eval (Pp.eval D) := by
        have h := length_flatten_le (List.ofFn T.base.Ly) (Pf.eval (Pp.eval D)) (fun x hx => by
          rw [List.mem_ofFn] at hx
          obtain ⟨q, rfl⟩ := hx
          exact hLylen q)
        simpa only [List.length_ofFn] using h
      have h3 : Low.length = (List.ofFn (fun q : Fin T.base.PieceList.length =>
          List.ofFn (T.base.SloR q))).flatten.length + (List.ofFn T.base.Ly).flatten.length := by
        dsimp only [Low]
        rw [List.length_append]
      have h4 : T.base.PieceList.length * K + T.base.PieceList.length * Pf.eval (Pp.eval D)
          ≤ MvPolynomial.eval ![D, k] Np * K
            + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hPLlen) (Nat.mul_le_mul_right _ hPLlen)
      have h5 : MvPolynomial.eval ![D, k] Np * K
            + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D)
          = MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K) := by ring
      rw [h3]
      exact h5 ▸ le_trans (Nat.add_le_add h1 h2) h4
    have hCandPiece : T.base.Cand.length + T.base.PieceList.length
        ≤ MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2) := by
      have h : MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)
          = MvPolynomial.eval ![D, k] Np * Pr.eval (Pp.eval D)
            + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D)
            + 2 * MvPolynomial.eval ![D, k] Np := by ring
      rw [h]
      omega
    have hSigPart : T.SigOut.length + Low.length
        ≤ MvPolynomial.eval ![D, k] Nsig2
          + MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K) :=
      Nat.add_le_add hSigOutLen hLowLen
    have hYlLenB : Yl.length = Raw.length := hYllen
    rw [hYlLenB, hRawLen, hSlicesLen, hNl_l D k l]
    omega
  have hRepCand' : ∀ Sv ∈ T.base.Cand, ∃ i : Fin Yl.length,
      projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
        projFirst n (m + 1) '' absSet Sv := hRepCand
  have hRepSigOut' : ∀ Z ∈ T.SigOut, ∃ i : Fin Yl.length,
      projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
        projFirst n (pPair n m) '' Z.set := hRepSigOut
  have hRepLow' : ∀ Z ∈ Low, ∃ i : Fin Yl.length,
      projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
        projFirst n (m + 1) '' Z.set := hRepLow
  have hRepSlice' : ∀ (Sv : Stratum 0 (n + (m + 1))) (σ : ℝ), (σ = 1 ∨ σ = -1) →
      Sv ∈ T.base.Cand → ∃ i : Fin Yl.length,
        projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
          projFirst n (m + 1) '' (E2.sliceSemiPf Sv σ).set := hRepSlice
  have hRepPiece' : ∀ U ∈ T.base.PieceList, ∃ i : Fin Yl.length,
      projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
        projFirst n (m + 1) '' absSet U := hRepPiece
  have hYlFmt' : ∀ i : Fin Yl.length,
      (Yl.get i).fmt ≤ (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).Fp0 ∧
        (Yl.get i).deg ≤ (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).P.eval D :=
    fun i => ⟨hYlFmt i, hYlDeg i⟩
  have hYlLen' : Yl.length ≤
      MvPolynomial.eval ![D, k, l] (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).Nl := hYlLen
  have hRepY' : ∀ j : Fin l, ∃ i : Fin Yl.length,
      projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set =
        projFirst n m' '' (Y j).set := hRepY
  have hRepY'' : ∀ j : Fin l, ∃ i : Fin Yl.length,
      projFirst n m' '' (Y j).set =
        projFirst n (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F).M2 '' (Yl.get i).set :=
    fun j => ⟨(hRepY j).choose, (hRepY j).choose_spec.symm⟩
  exact ⟨Yl,
    ⟨⟨hYlFmt', hRepCand',
      (fun Z hZ => by
        rcases T.hSigSplit Z hZ with hZ | ⟨X, hX, hproj⟩
        · exact hRepSigOut' Z hZ
        · obtain ⟨i, hi⟩ := hRepLow' X hX
          exact ⟨i, hi.trans hproj.symm⟩),
      (fun q r => hRepLow' _ (hSloL_mem q r)),
      (fun q Yc hYc => hRepLow' _ (hLyL_mem q Yc hYc)),
      (fun Sv hSv => hRepSlice' Sv 1 (Or.inl rfl) hSv),
      (fun Sv hSv => hRepSlice' Sv (-1) (Or.inr rfl) hSv),
      hRepY', hRepPiece'⟩,
    ⟨hYlLen', hYlFmt', hRepY''⟩⟩⟩

end

end Work.WilE7.Endgame.E2B
