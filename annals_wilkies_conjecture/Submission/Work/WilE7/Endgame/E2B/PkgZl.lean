/-
  Area E7 / E2B, node `cellRefine_of_nodesB`: **the `X'`-family of the package `E2Pkg`**.

  On top of `SigmaPart` (`PkgSigma.lean`) this module builds the fibre products `Z_{T,S}` of every
  piece with every member of the `Σ`-family, proves `specZ`/`specZout`, and records the resulting
  list `Zl`.  The file-size guard forces this to be a module of its own.
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

/-- The `X'`-family of `E2Pkg`: one fibre product per (piece, `Σ`-member) pair, for the
`Σ`-side data `S` of `SigmaPart`. -/
structure ZlPart {n K F : ℕ} {c : E2Const n K F} {D k l m : ℕ}
    {X : Fin k → SemiPf ((n + 1) + m)} (S : SigmaPart c D k m X) where
  Zl : List (SemiPf ((n + 1) + (m + pPair n m)))
  specZ : (∀ Z ∈ Zl, Z.fmt ≤ c.AZl ∧
      NullDimLT (basePr n (m + pPair n m) '' Z.set) K ∧ Z.deg ≤ c.P.eval D) ∧
    (∀ (i : Fin S.base.Pie.length) (j : Fin S.Sig.length), ∃ i' : Fin Zl.length,
      (Zl.get i').deg ≤ c.BZl.eval ((S.base.Pie.get i).2.deg + (S.Sig.get j).deg) ∧
      projFirst (n + 1) (m + pPair n m) '' (Zl.get i').set =
        (projFirst (n + 1) m '' absSet (S.base.Pie.get i).2) ∩
          {y : Fin (n + 1) → ℝ |
            Fin.init y ∈ projFirst n (pPair n m) '' (S.Sig.get j).set})
  specZout : Zl.length ≤ MvPolynomial.eval ![D, k, l] c.Nk ∧
    (∀ i : Fin Zl.length, (Zl.get i).fmt ≤ c.Fp0 ∧ (Zl.get i).deg ≤ c.P.eval D ∧
      NullDimLT (basePr n (m + pPair n m) '' (Zl.get i).set) K)


theorem e2bZlPart (hFC : Work.WilE7.CoreLTSuccPlan.HypFC) (hE2 : Work.WilE7.CoreLTSuccPlan.HypE2)
    (hE5 : Work.WilE7.CoreLTSuccPlan.HypE5) (hE6 : Work.WilE7.CoreLTSuccPlan.HypE6)
    (h0 : Work.WilE7.CoreLTSuccPlan.FrontierRestrat) (h1 : Work.WilE7.CoreLTSuccPlan.SigmaVPairs)
    (n K F : ℕ) (D k l m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m))
    (hX : ∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D)
    (hND : ∀ i, Work.WilE7.MainDesign.NullDimLT
      (Work.WilE7.MainDesign.basePr n m '' (X i).set) (K + 1))
    (hk : 0 < k) (T : SigmaPart (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) D k m X) :
    ∃ Z : @ZlPart n K F (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) D k l m X T, True := by
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
  -- ## §2  the `X'`-family: one fibre product per (piece, `Σ`-member) pair
  have hZlem := (Work.CoreStep.fibreProd_sigma_lem FZ).choose_spec.choose_spec
  let Zf : (i : Fin T.base.Pie.length) → (j : Fin T.Sig.length) →
      SemiPf ((n + 1) + (m + pPair n m)) := fun i j =>
    (hZlem n m (pPair n m) K (T.base.Pie.get i).2 (T.Sig.get j)
      (hPieFZ _ (List.get_mem T.base.Pie i)) (hSigFZ _ (List.get_mem T.Sig j))
      (hSigND _ (List.get_mem T.Sig j))).choose
  have hZf : ∀ (i : Fin T.base.Pie.length) (j : Fin T.Sig.length),
      (Zf i j).fmt ≤ AZl ∧
      (Zf i j).deg ≤ BZl.eval ((T.base.Pie.get i).2.deg + (T.Sig.get j).deg) ∧
      projFirst (n + 1) (m + pPair n m) '' (Zf i j).set =
        (projFirst (n + 1) m '' absSet (T.base.Pie.get i).2) ∩
          {y : Fin (n + 1) → ℝ | Fin.init y ∈ projFirst n (pPair n m) '' (T.Sig.get j).set} ∧
      NullDimLT (basePr n (m + pPair n m) '' (Zf i j).set) K := fun i j =>
    (hZlem n m (pPair n m) K (T.base.Pie.get i).2 (T.Sig.get j)
      (hPieFZ _ (List.get_mem T.base.Pie i)) (hSigFZ _ (List.get_mem T.Sig j))
      (hSigND _ (List.get_mem T.Sig j))).choose_spec
  let Zl : List (SemiPf ((n + 1) + (m + pPair n m))) :=
    (List.ofFn (fun i : Fin T.base.Pie.length => List.ofFn (Zf i))).flatten
  have hZlget : ∀ (i : Fin T.base.Pie.length) (j : Fin T.Sig.length), Zf i j ∈ Zl := by
    intro i j
    refine List.mem_flatten.mpr ⟨List.ofFn (Zf i), ?_, List.mem_ofFn.mpr ⟨j, rfl⟩⟩
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hZlpair : ∀ (i : Fin T.base.Pie.length) (j : Fin T.Sig.length),
      ∃ i' : Fin Zl.length, Zl.get i' = Zf i j := fun i j =>
    List.mem_iff_get.mp (hZlget i j)
  have hZfDeg : ∀ (i : Fin T.base.Pie.length) (j : Fin T.Sig.length), (Zf i j).deg ≤ P.eval D := by
    intro i j
    refine le_trans (hZf i j).2.1 ?_
    refine le_trans (Work.WilE7.coreLT_succ.eval_mono_nat BZl ?_) (hPdz_l D)
    have h1 : (T.base.Pie.get i).2.deg ≤ Dq.eval D := hPieDeg _ (List.get_mem T.base.Pie i)
    have h2 : (T.Sig.get j).deg ≤ Dg.eval D := hSigDegDg _ (List.get_mem T.Sig j)
    omega
  have hZlmem : ∀ Z ∈ Zl, Z.fmt ≤ AZl ∧
      NullDimLT (basePr n (m + pPair n m) '' Z.set) K ∧ Z.deg ≤ P.eval D := by
    intro Z hZ
    dsimp only [Zl] at hZ
    rw [List.mem_flatten] at hZ
    obtain ⟨L, hL, hZL⟩ := hZ
    rw [List.mem_ofFn] at hL
    obtain ⟨i, rfl⟩ := hL
    rw [List.mem_ofFn] at hZL
    obtain ⟨j, rfl⟩ := hZL
    exact ⟨(hZf i j).1, (hZf i j).2.2.2, hZfDeg i j⟩
  have hZlLen : Zl.length ≤ MvPolynomial.eval ![D, k, l] Nk := by
    have hPieLen : T.base.Pie.length ≤ MvPolynomial.eval ![D, k] Np :=
      T.base.specPieces.1
    have hSigLen : T.Sig.length ≤ MvPolynomial.eval ![D, k] Nsig2 := T.hSigLen
    have hlen : Zl.length ≤ T.base.Pie.length * T.Sig.length := by
      let L : List (List (SemiPf ((n + 1) + (m + pPair n m)))) :=
        List.ofFn (fun i : Fin T.base.Pie.length => List.ofFn (Zf i))
      have h : L.flatten.length ≤ L.length * T.Sig.length :=
        length_flatten_le L (T.Sig.length) (fun x hx => by
          dsimp only [L] at hx
          rw [List.mem_ofFn] at hx
          obtain ⟨i, rfl⟩ := hx
          simp)
      have hL : L.length = T.base.Pie.length := by
        dsimp only [L]
        simp only [List.length_ofFn]
      rw [hL] at h
      dsimp only [Zl, L] at h
      exact h
    rw [hNk_l D k l]
    exact le_trans hlen (Nat.mul_le_mul hPieLen hSigLen)
  refine ⟨{ Zl := Zl, specZ := ?_, specZout := ?_ }, trivial⟩
  · exact ⟨hZlmem, fun i j => by
      obtain ⟨i', hi'⟩ := hZlpair i j
      exact ⟨i', by rw [hi']; exact (hZf i j).2.1, by rw [hi']; exact (hZf i j).2.2.1⟩⟩
  · exact ⟨hZlLen, fun i => by
      obtain ⟨hfmt, hnd, hdeg⟩ := hZlmem _ (List.get_mem Zl i)
      exact ⟨le_trans hfmt (le_max_left c.AZl (c.Ft + c.M2)), hdeg, hnd⟩⟩

end

end Work.WilE7.Endgame.E2B
