/-
  Area E7 / E2B, node `cellRefine_of_nodesB`, **the `Σ`-side of the package `E2Pkg`, part 2**.

  On top of `PiecePart` (`PkgPart.lean`) this module builds the `Σ`-family: the output of
  `E2B.sigmaTotal` together with the `Σlow` members (the rank slices `SloR` and the frontier sets
  `Ly`, padded to the fibre dimension `pPair n m`), and proves the `Σ`-clauses of `E2Pkg`.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.PkgPart

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

/-- The `Σ`-side of the data package `E2Pkg`: the pieces (`PiecePart`) together with the
`Σ`-family and its specifications. -/
structure SigmaPart {n K F : ℕ} (c : E2Const n K F) (D k m : ℕ)
    (X : Fin k → SemiPf ((n + 1) + m)) where
  base : PiecePart c D k m X
  /- `Sig` is the whole `Σ`-family: the output of `E2B.sigmaTotal` *together with* the `Σlow`
  members (the rank slices `SloR` and the frontier sets `Ly`, padded to the fibre dimension
  `pPair n m`), so that the `Σ`-case of the per-base-cell refinement covers the rank-deficient
  loci as well. -/
  Sig : List (SemiPf (n + pPair n m))
  specSig : SigSpec n m K (max (c.Btot.eval (c.Dq.eval D)) (c.P.eval D))
    (max c.Atot (c.Ac + pPair n m)) base.Cand base.Pv Sig
  hSigLen : Sig.length ≤ MvPolynomial.eval ![D, k] c.Nsig2
  hPieFZ : ∀ p ∈ base.Pie, (p.2).X.fmt ≤ c.FZ
  hSigFZ : ∀ Z ∈ Sig, Z.fmt ≤ c.FZ
  hSigND : ∀ Z ∈ Sig, NullDimLT (projFirst n (pPair n m) '' Z.set) K
  hSigDeg : ∀ Z ∈ Sig, Z.deg ≤ c.P.eval D
  hSigDegDg : ∀ Z ∈ Sig, Z.deg ≤ c.Dg.eval D
  /- the `Σout` part of `Sig` (small format) and the description of the padded `Σlow` part,
  for the `Y'`-packing -/
  SigOut : List (SemiPf (n + pPair n m))
  hSigOutFmt : ∀ Z ∈ SigOut, Z.fmt ≤ c.Ft
  hSigOutLen : SigOut.length ≤ MvPolynomial.eval ![D, k] c.Nsig2
  hSigOutDeg : ∀ Z ∈ SigOut, Z.deg ≤ c.P.eval D
  hSigSplit : ∀ Z ∈ Sig, Z ∈ SigOut ∨
    ∃ X ∈ (List.ofFn (fun q : Fin base.PieceList.length => List.ofFn (base.SloR q))).flatten
        ++ (List.ofFn base.Ly).flatten,
      projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' X.set
  hSigSloR : ∀ (q : Fin base.PieceList.length) (r : Fin K), ∃ Z ∈ Sig,
    projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' (base.SloR q r).set
  hSigLy : ∀ (q : Fin base.PieceList.length) (Yc : SemiPf (n + (m + 1))), Yc ∈ base.Ly q →
    ∃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' Yc.set

theorem e2bSigmaPart (hFC : Work.WilE7.CoreLTSuccPlan.HypFC) (hE2 : Work.WilE7.CoreLTSuccPlan.HypE2)
    (hE5 : Work.WilE7.CoreLTSuccPlan.HypE5) (hE6 : Work.WilE7.CoreLTSuccPlan.HypE6)
    (h0 : Work.WilE7.CoreLTSuccPlan.FrontierRestrat) (h1 : Work.WilE7.CoreLTSuccPlan.SigmaVPairs)
    (n K F : ℕ) (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m))
    (hX : ∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D)
    (hND : ∀ i, Work.WilE7.MainDesign.NullDimLT
      (Work.WilE7.MainDesign.basePr n m '' (X i).set) (K + 1))
    (hk : 0 < k) :
    ∃ S : SigmaPart (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) D k m X, True := by
  classical
  set c : E2Const n K F := e2bConst hFC hE2 hE5 hE6 h0 h1 n K F with hc
  -- ## §0  the constants, chosen exactly as in the definition of `e2bConst`
  let Ap : ℕ := (E2_pieces_of_family hFC hE5 F).choose
  let Pp : Polynomial ℕ := (E2_pieces_of_family hFC hE5 F).choose_spec.choose
  let Np : MvPolynomial (Fin 2) ℕ :=
    (E2_pieces_of_family hFC hE5 F).choose_spec.choose_spec.choose
  let Ar : ℕ := (E2_rank_strata hE5 Ap).choose
  let Pr : Polynomial ℕ := (E2_rank_strata hE5 Ap).choose_spec.choose
  let Af : ℕ := (E2_frontier_strata h0 Ap).choose
  let Pf : Polynomial ℕ := (E2_frontier_strata h0 Ap).choose_spec.choose
  let Ac : ℕ := Ap + Ar + Af
  let Fp : ℕ := 2 * Ac
  let Dq : Polynomial ℕ := Pp + Pr.comp Pp + Pf.comp Pp + 1
  let Qtot : MvPolynomial (Fin 3) ℕ := (E2B.sigmaTotal hE5 hE6 h1 n K Fp F).choose
  let Atot : ℕ := (E2B.sigmaTotal hE5 hE6 h1 n K Fp F).choose_spec.choose
  let Btot : Polynomial ℕ := (E2B.sigmaTotal hE5 hE6 h1 n K Fp F).choose_spec.choose_spec.choose
  let Ps : Polynomial ℕ := (E2_sheets_of_stratum hE2 (Ap + Ar + Af)).choose_spec.choose
  let AZl : ℕ := (Work.CoreStep.fibreProd_sigma_lem (Ac + Atot + pPair n F + 2)).choose
  let BZl : Polynomial ℕ :=
    (Work.CoreStep.fibreProd_sigma_lem (Ac + Atot + pPair n F + 2)).choose_spec.choose
  let M2 : ℕ := F + F + pPair n F + 5
  let Ft : ℕ := max (max Ac Atot) F
  let Pe1 : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 Pr Pp).choose
  let Pe2 : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 Pf Pp).choose
  let Dg : Polynomial ℕ :=
    Polynomial.X + Pp + Pe1 + Pe2 + (3 * Dq + 2) + (Btot.comp Dq) + (Ps.comp Dq) + 1
  let Pd1 : Polynomial ℕ := (Work.WilE7.Endgame.poly_comp_dominate 1 BZl (Dq + Dg)).choose
  let P : Polynomial ℕ := Dg + Pd1
  let Ncan2 : MvPolynomial (Fin 2) ℕ := Np *
    Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Pr.comp Pp + Pf.comp Pp + Polynomial.C 2)
  let Nsig2 : MvPolynomial (Fin 2) ℕ := (E2B.poly_dominate3b Qtot Dq
      (fun D k => MvPolynomial.eval ![D, k] Ncan2) (fun D k => MvPolynomial.eval ![D, k] Np)
      (PolyShape.mvpoly Ncan2) (PolyShape.mvpoly Np)).choose
    + Np * (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Polynomial.C (K + 1) + P))
  -- ## §0b  the interface facts in the vocabulary of the producer outputs
  have hAc_eq : Ac = c.Ac := rfl
  have hAtot_eq : Atot = c.Atot := rfl
  have hP_eq : P = c.P := rfl
  have hDg_eq : Dg = c.Dg := rfl
  have hPB_l : ∀ D : ℕ, Btot.eval (Dq.eval D) ≤ P.eval D := c.hPB
  have hPfP_l : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ P.eval D := c.hPfP
  have hPrP_l : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ P.eval D := c.hPrP
  have hDgPr_l : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ Dg.eval D := c.hDgPr
  have hDgPf_l : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ Dg.eval D := c.hDgPf
  have hNsig_l : ∀ D k : ℕ, MvPolynomial.eval
      ![Dq.eval D, MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2),
        MvPolynomial.eval ![D, k] Np] Qtot ≤ MvPolynomial.eval ![D, k] Nsig2 := c.hNsig
  have hDg_ge : ∀ D : ℕ, Btot.eval (Dq.eval D) ≤ Dg.eval D := by
    have hdef : Dg =
        Polynomial.X + Pp + Pe1 + Pe2 + (3 * Dq + 2) + (Btot.comp Dq) + (Ps.comp Dq) + 1 := rfl
    intro D
    rw [hdef]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_ofNat, Polynomial.eval_one]
    omega
  let PDB : MvPolynomial (Fin 2) ℕ := (E2B.poly_dominate3b Qtot Dq
      (fun D k => MvPolynomial.eval ![D, k] Ncan2) (fun D k => MvPolynomial.eval ![D, k] Np)
      (PolyShape.mvpoly Ncan2) (PolyShape.mvpoly Np)).choose
  have hNcan2E : ∀ D k : ℕ, MvPolynomial.eval ![D, k] Ncan2 =
      MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2) := by
    have hdef : Ncan2 = Np * Polynomial.aeval (MvPolynomial.X (0 : Fin 2))
        (Pr.comp Pp + Pf.comp Pp + Polynomial.C 2) := rfl
    intro D k
    rw [hdef, map_mul, Work.WilE7.eval_aeval_X_zero]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_comp,
      Matrix.cons_val_zero]
  have hNsig2def : Nsig2 = PDB +
      Np * (Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Polynomial.C (K + 1) + P)) := rfl
  have hNsig2E : ∀ D k : ℕ, MvPolynomial.eval ![D, k] Nsig2 =
      MvPolynomial.eval ![D, k] PDB + MvPolynomial.eval ![D, k] Np * ((K + 1) + P.eval D) := by
    intro D k
    rw [hNsig2def, map_add, map_mul, Work.WilE7.eval_aeval_X_zero]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Matrix.cons_val_zero]
  have hPDB : ∀ D k : ℕ, MvPolynomial.eval ![Dq.eval D, MvPolynomial.eval ![D, k] Ncan2,
      MvPolynomial.eval ![D, k] Np] Qtot ≤ MvPolynomial.eval ![D, k] PDB :=
    (E2B.poly_dominate3b Qtot Dq (fun D k => MvPolynomial.eval ![D, k] Ncan2)
      (fun D k => MvPolynomial.eval ![D, k] Np) (PolyShape.mvpoly Ncan2)
      (PolyShape.mvpoly Np)).choose_spec
  -- ## §1  the `Σ`-side data of `PiecePart`
  obtain ⟨Pp0, _⟩ := e2bPiecePart hFC hE2 hE5 hE6 h0 h1 n K F D k m X hX hND hk
  have hmF : m ≤ F := by
    have h := (hX ⟨0, hk⟩).1
    simp only [WilkiesDesign.E.SemiPf.fmt] at h
    omega
  have hCandmem : ∀ S ∈ Pp0.Cand, S.Good ∧ S.X.fmt ≤ Ac ∧ S.deg ≤ Dq.eval D ∧
      n + (m + 1) - S.j ≤ K ∧ (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) := Pp0.specCand
  have hCandGood : ∀ S ∈ Pp0.Cand, S.Good := fun S hS => (hCandmem S hS).1
  have hCandFmt : ∀ S ∈ Pp0.Cand, S.X.fmt ≤ Ac := fun S hS => (hCandmem S hS).2.1
  have hCandDeg : ∀ S ∈ Pp0.Cand, S.deg ≤ Dq.eval D := fun S hS => (hCandmem S hS).2.2.1
  have hCandDim : ∀ S ∈ Pp0.Cand, n + (m + 1) - S.j ≤ K := fun S hS => (hCandmem S hS).2.2.2.1
  have hCandFmt' : ∀ S ∈ Pp0.Cand, (n + (m + 1)) + S.X.r ≤ Ac := fun S hS => by
    simpa only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add] using hCandFmt S hS
  have hCandLenB : Pp0.Cand.length ≤ MvPolynomial.eval ![D, k] Np *
      (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2) := Pp0.specCandLen
  have hPLlen : Pp0.PieceList.length ≤ MvPolynomial.eval ![D, k] Np := Pp0.specPieceLen
  have hPLmem : ∀ T ∈ Pp0.PieceList, T.Good ∧ T.X.fmt ≤ Ap ∧ T.deg ≤ Pp.eval D ∧
      n + (m + 1) - T.j ≤ K + 1 ∧ (∀ z ∈ T.X.set, projRank T z ≤ K) := Pp0.specPL
  have hPvmem : ∀ T ∈ Pp0.Pv, T ∈ Pp0.PieceList ∧ n + (m + 1) - T.j = K + 1 := Pp0.specPv
  have hPvLen : Pp0.Pv.length ≤ MvPolynomial.eval ![D, k] Np := Pp0.specPvLen
  have hPvGood : ∀ T ∈ Pp0.Pv, T.Good := fun T hT => (hPLmem T (hPvmem T hT).1).1
  have hArAc : Ar ≤ Ac := by
    show Ar ≤ Ap + Ar + Af
    omega
  have hAfAc : Af ≤ Ac := by
    show Af ≤ Ap + Ar + Af
    omega
  have hPvFmt : ∀ T ∈ Pp0.Pv, T.X.fmt ≤ Ac := fun T hT =>
    le_trans (hPLmem T (hPvmem T hT).1).2.1 (by
      have h := hArAc
      omega)
  have hPvFmt' : ∀ T ∈ Pp0.Pv, (n + (m + 1)) + T.X.r ≤ Ac := fun T hT => by
    simpa only [WilkiesDesign.E.SemiPf.fmt, Nat.zero_add] using hPvFmt T hT
  have hPvDeg : ∀ T ∈ Pp0.Pv, T.deg ≤ Dq.eval D := fun T hT => by
    have h1 : (Pp0.Pv).length ≤ MvPolynomial.eval ![D, k] Np := hPvLen
    have h2 := (hPLmem T (hPvmem T hT).1).2.2.1
    have h3 : Pp.eval D ≤ Dq.eval D := by
      rw [show Dq = Pp + Pr.comp Pp + Pf.comp Pp + 1 from rfl, Polynomial.eval_add,
        Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_one]
      omega
    exact le_trans h2 h3
  -- ## §2  the `Σ`-family of the candidates and of the vertical pairs
  have hAc_le : Ac ≤ Fp := by
    have h : Fp = 2 * Ac := rfl
    rw [h]
    omega
  have hCandFp : ∀ S ∈ Pp0.Cand, S.X.fmt ≤ Fp := fun S hS =>
    le_trans (hCandFmt S hS) hAc_le
  have hPvFp : ∀ T ∈ Pp0.Pv, T.X.fmt ≤ Fp := fun T hT => le_trans (hPvFmt T hT) hAc_le
  have hTotSpec := (E2B.sigmaTotal hE5 hE6 h1 n K Fp F).choose_spec.choose_spec.choose_spec
  obtain ⟨SigOut, hSigOutLen, hSigOutMem, hSigOutLow, hSigOutFront, hSigOutWl, hSigOutVl,
    hSigOutVlV, hSigOutWlV⟩ :=
    hTotSpec m hmF (Dq.eval D) Pp0.Cand Pp0.Pv
      (fun T hT => ⟨hCandGood T hT, hCandFp T hT, hCandDeg T hT⟩)
      (fun T hT => ⟨hPvGood T hT, hPvFp T hT, hPvDeg T hT⟩)
      hCandDim
      (fun S hS => Work.WilE7.Endgame.absPairSet2_fmt_le S S (hCandFmt' S hS) (hCandFmt' S hS))
      (fun S hS T hT => absLevelPairSet_fmt_le S T (hCandFmt' S hS) (hCandFmt' T hT))
      (fun S hS T hT => Work.WilE7.Endgame.absPairSet2_fmt_le S T (hCandFmt' S hS) (hPvFmt' T hT))
      (fun S hS T hT => absLevelPairSet_fmt_le S T (hCandFmt' S hS) (hPvFmt' T hT))
  have hSigOutMemL : ∀ Z ∈ SigOut, Z.fmt ≤ Atot ∧ Z.deg ≤ Btot.eval (Dq.eval D) ∧
      NullDimLT (projFirst n (pPair n m) '' Z.set) K := hSigOutMem
  have hSigOutDeg : ∀ Z ∈ SigOut, Z.deg ≤ Btot.eval (Dq.eval D) :=
    fun Z hZ => (hSigOutMemL Z hZ).2.1
  -- ## §3  the `Σlow` members (the rank slices and the frontier sets, padded)
  let SloL : List (SemiPf (n + (m + 1))) :=
    (List.ofFn (fun q : Fin Pp0.PieceList.length => List.ofFn (Pp0.SloR q))).flatten
  let LyL : List (SemiPf (n + (m + 1))) := (List.ofFn Pp0.Ly).flatten
  have hSloLmem : ∀ Z ∈ SloL,
      ∃ (q : Fin Pp0.PieceList.length) (r : Fin K), Z = Pp0.SloR q r := by
    intro Z hZ
    dsimp only [SloL] at hZ
    rw [List.mem_flatten] at hZ
    obtain ⟨L, hL, hZL⟩ := hZ
    rw [List.mem_ofFn] at hL
    obtain ⟨q, rfl⟩ := hL
    obtain ⟨r, hr⟩ := List.mem_ofFn.mp hZL
    exact ⟨q, r, hr.symm⟩
  have hLyLmem : ∀ Z ∈ LyL, ∃ q : Fin Pp0.PieceList.length, Z ∈ Pp0.Ly q := by
    intro Z hZ
    dsimp only [LyL] at hZ
    rw [List.mem_flatten] at hZ
    obtain ⟨L, hL, hZL⟩ := hZ
    rw [List.mem_ofFn] at hL
    obtain ⟨q, rfl⟩ := hL
    exact ⟨q, hZL⟩
  have hLowmem : ∀ Z ∈ SloL ++ LyL, Z.fmt ≤ Ac ∧ Z.deg ≤ Dg.eval D ∧
      Z.deg ≤ P.eval D ∧ NullDimLT (projFirst n (m + 1) '' Z.set) K := by
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · obtain ⟨q, r, rfl⟩ := hSloLmem Z hZ
      obtain ⟨hf, hd, _hs, hnd⟩ := Pp0.specSloR q r
      exact ⟨le_trans hf hArAc, le_trans hd (hDgPr_l D), le_trans hd (hPrP_l D), hnd⟩
    · obtain ⟨q, hq⟩ := hLyLmem Z hZ
      obtain ⟨hf, hd, hnd⟩ := (Pp0.specLy q).2.1 Z hq
      exact ⟨le_trans hf hAfAc, le_trans hd (hDgPf_l D), le_trans hd (hPfP_l D), hnd⟩
  have hSloL_mem : ∀ (q : Fin Pp0.PieceList.length) (r : Fin K), Pp0.SloR q r ∈ SloL := by
    intro q r
    dsimp only [SloL]
    exact List.mem_flatten.mpr ⟨List.ofFn (Pp0.SloR q), List.mem_ofFn.mpr ⟨q, rfl⟩,
      List.mem_ofFn.mpr ⟨r, rfl⟩⟩
  have hLyL_mem : ∀ (q : Fin Pp0.PieceList.length) (Z : SemiPf (n + (m + 1))),
      Z ∈ Pp0.Ly q → Z ∈ LyL := by
    intro q Z hZ
    dsimp only [LyL]
    exact List.mem_flatten.mpr ⟨Pp0.Ly q, List.mem_ofFn.mpr ⟨q, rfl⟩, hZ⟩
  have hpad_le : m + 1 ≤ pPair n m := by
    simp only [pPair]
    omega
  let SigLow : List (SemiPf (n + pPair n m)) :=
    (SloL ++ LyL).map (fun Z => Work.WilE7.SemiPf.pad (Nat.add_le_add_left hpad_le n) Z)
  have hSigLowLen : SigLow.length ≤ MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K) := by
    have h1 : SloL.length ≤ Pp0.PieceList.length * K := by
      have h := length_flatten_le
        (List.ofFn (fun q : Fin Pp0.PieceList.length => List.ofFn (Pp0.SloR q))) K
        (fun x hx => by
          rw [List.mem_ofFn] at hx
          obtain ⟨q, rfl⟩ := hx
          simp)
      simpa only [List.length_ofFn] using h
    have h2 : LyL.length ≤ Pp0.PieceList.length * Pf.eval (Pp.eval D) := by
      have h := length_flatten_le (List.ofFn Pp0.Ly) (Pf.eval (Pp.eval D)) (fun x hx => by
        rw [List.mem_ofFn] at hx
        obtain ⟨q, rfl⟩ := hx
        exact (Pp0.specLy q).1)
      simpa only [List.length_ofFn] using h
    have h3 : (SloL ++ LyL).length = SloL.length + LyL.length := List.length_append
    have h4 : Pp0.PieceList.length * K + Pp0.PieceList.length * Pf.eval (Pp.eval D)
        ≤ MvPolynomial.eval ![D, k] Np * K + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hPLlen) (Nat.mul_le_mul_right _ hPLlen)
    have h5 : MvPolynomial.eval ![D, k] Np * K + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D)
        = MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K) := by ring
    dsimp only [SigLow]
    rw [List.length_map, h3]
    exact h5 ▸ le_trans (Nat.add_le_add h1 h2) h4
  have hSigLowFmt : ∀ Z ∈ SigLow, Z.fmt ≤ Ac + pPair n m := by
    intro Z hZ
    dsimp only [SigLow] at hZ
    rw [List.mem_map] at hZ
    obtain ⟨W, hW, rfl⟩ := hZ
    have hwf : W.fmt ≤ Ac := (hLowmem W hW).1
    have hpad : (Work.WilE7.SemiPf.pad (Nat.add_le_add_left hpad_le n) W).fmt
        = (n + pPair n m) + W.r := rfl
    have hWfmt : W.fmt = (n + (m + 1)) + W.r := rfl
    have hwf' : (n + (m + 1)) + W.r ≤ Ap + Ar + Af := hwf
    rw [hpad]
    show (n + pPair n m) + W.r ≤ Ac + pPair n m
    show (n + pPair n m) + W.r ≤ Ap + Ar + Af + pPair n m
    omega
  have hSigLowDeg : ∀ Z ∈ SigLow, Z.deg ≤ Dg.eval D := by
    intro Z hZ
    dsimp only [SigLow] at hZ
    rw [List.mem_map] at hZ
    obtain ⟨W, hW, rfl⟩ := hZ
    exact le_trans (semipf_deg_pad_le (Nat.add_le_add_left hpad_le n) W) (hLowmem W hW).2.1
  have hSigLowDegP : ∀ Z ∈ SigLow, Z.deg ≤ P.eval D := by
    intro Z hZ
    dsimp only [SigLow] at hZ
    rw [List.mem_map] at hZ
    obtain ⟨W, hW, rfl⟩ := hZ
    exact le_trans (semipf_deg_pad_le (Nat.add_le_add_left hpad_le n) W) (hLowmem W hW).2.2.1
  have hSigLowND : ∀ Z ∈ SigLow, NullDimLT (projFirst n (pPair n m) '' Z.set) K := by
    intro Z hZ
    dsimp only [SigLow] at hZ
    rw [List.mem_map] at hZ
    obtain ⟨W, hW, rfl⟩ := hZ
    rw [Work.WilE7.pad_proj hpad_le W]
    exact (hLowmem W hW).2.2.2
  -- ## §4  the `Σ`-family and its clauses
  let Sig : List (SemiPf (n + pPair n m)) := SigOut ++ SigLow
  have hSigLen : Sig.length ≤ MvPolynomial.eval ![D, k] Nsig2 := by
    have hOut : SigOut.length ≤ MvPolynomial.eval ![D, k] PDB := by
      have hCanLen : Pp0.Cand.length ≤ MvPolynomial.eval ![D, k] Ncan2 := by
        rw [hNcan2E D k]
        exact hCandLenB
      have hPvLen' : Pp0.Pv.length ≤ MvPolynomial.eval ![D, k] Np := hPvLen
      have hmid : MvPolynomial.eval ![Dq.eval D, MvPolynomial.eval ![D, k] Ncan2,
          MvPolynomial.eval ![D, k] Np] Qtot ≤ MvPolynomial.eval ![D, k] PDB := hPDB D k
      have hmon : MvPolynomial.eval ![Dq.eval D, Pp0.Cand.length, Pp0.Pv.length] Qtot ≤
          MvPolynomial.eval ![Dq.eval D, MvPolynomial.eval ![D, k] Ncan2,
            MvPolynomial.eval ![D, k] Np] Qtot := by
        refine eval_mono_fin3 (b := Qtot) ?_
        intro i
        fin_cases i
        · exact le_rfl
        · simpa using hCanLen
        · simpa using hPvLen'
      exact le_trans hSigOutLen (le_trans hmon hmid)
    have hLowLenB : SigLow.length ≤ MvPolynomial.eval ![D, k] Np * ((K + 1) + P.eval D) := by
      refine le_trans hSigLowLen (Nat.mul_le_mul_left _ ?_)
      have h := hPfP_l D
      omega
    have hslack := hNsig2E D k
    rw [List.length_append, hslack]
    omega
  have hFZ_l : c.FZ = Ac + Atot + pPair n F + 2 := by
    rw [c.hFZ, ← hAc_eq, ← hAtot_eq]
  have hpp : pPair n m ≤ pPair n F := by
    simp only [pPair]
    omega
  have hSigFZ : ∀ Z ∈ Sig, Z.fmt ≤ c.FZ := by
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · refine le_trans (hSigOutMemL Z hZ).1 ?_
      rw [hFZ_l]
      omega
    · refine le_trans (hSigLowFmt Z hZ) ?_
      rw [hFZ_l]
      omega
  have hSigND : ∀ Z ∈ Sig, NullDimLT (projFirst n (pPair n m) '' Z.set) K := by
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact (hSigOutMemL Z hZ).2.2
    · exact hSigLowND Z hZ
  have hSigDeg : ∀ Z ∈ Sig, Z.deg ≤ c.P.eval D := by
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact le_trans (hSigOutDeg Z hZ) (hPB_l D)
    · exact hSigLowDegP Z hZ
  have hSigDegDg : ∀ Z ∈ Sig, Z.deg ≤ c.Dg.eval D := by
    intro Z hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact le_trans (hSigOutDeg Z hZ) (hDg_ge D)
    · exact hSigLowDeg Z hZ
  have hSigMem : ∀ Z ∈ Sig, Z.fmt ≤ max Atot (Ac + pPair n m) ∧
      Z.deg ≤ max (Btot.eval (Dq.eval D)) (c.P.eval D) ∧
      NullDimLT (projFirst n (pPair n m) '' Z.set) K := by
    intro Z hZ
    have h1 : Z.fmt ≤ max Atot (Ac + pPair n m) := by
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact le_trans (hSigOutMemL Z hZ).1 (le_max_left _ _)
      · exact le_trans (hSigLowFmt Z hZ) (le_max_right _ _)
    have h2 : Z.deg ≤ max (Btot.eval (Dq.eval D)) (c.P.eval D) := by
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact le_trans (hSigOutDeg Z hZ) (le_max_left _ _)
      · exact le_trans (hSigLowDegP Z hZ) (le_max_right _ _)
    exact ⟨h1, h2, hSigND Z hZ⟩
  have hSigSloR : ∀ (q : Fin Pp0.PieceList.length) (r : Fin K), ∃ Z ∈ Sig,
      projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' (Pp0.SloR q r).set := by
    intro q r
    refine ⟨Work.WilE7.SemiPf.pad (Nat.add_le_add_left hpad_le n) (Pp0.SloR q r), ?_,
      Work.WilE7.pad_proj hpad_le (Pp0.SloR q r)⟩
    dsimp only [Sig, SigLow]
    rw [List.mem_append]
    right
    exact List.mem_map.mpr ⟨Pp0.SloR q r, List.mem_append.mpr (Or.inl (hSloL_mem q r)), rfl⟩
  have hSigLy : ∀ (q : Fin Pp0.PieceList.length) (Yc : SemiPf (n + (m + 1))), Yc ∈ Pp0.Ly q →
      ∃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' Yc.set := by
    intro q Yc hYc
    refine ⟨Work.WilE7.SemiPf.pad (Nat.add_le_add_left hpad_le n) Yc, ?_,
      Work.WilE7.pad_proj hpad_le Yc⟩
    dsimp only [Sig, SigLow]
    rw [List.mem_append]
    right
    exact List.mem_map.mpr ⟨Yc, List.mem_append.mpr (Or.inr (hLyL_mem q Yc hYc)), rfl⟩
  have hmono : (⋃ Z ∈ SigOut, projFirst n (pPair n m) '' Z.set) ⊆
      (⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) := by
    intro x hx
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨Z, List.mem_append.mpr (Or.inl hZ), hxZ⟩
  have hSigLowC : ∀ T ∈ Pp0.Cand, n + (m + 1) - T.j < K →
      projFirst n (m + 1) '' absSet T ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set :=
    fun T hT hK => subset_trans (hSigOutLow T hT hK) hmono
  have hSigFrontC : ∀ T ∈ Pp0.Cand,
      frontierSet n m T ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set :=
    fun T hT => subset_trans (hSigOutFront T hT) hmono
  have hSigWlC : ∀ T ∈ Pp0.Cand, ∃ Wl : List (Stratum 0 (pPair n m)),
      (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet T).set) ∧
      ((absPairSet T).set = ⋃ W ∈ Wl, W.X.set) ∧
      (∀ W ∈ Wl, pPair n m - W.j < n + (m + 1) - T.j →
        pairSubBaseFst n m W ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) := by
    intro T hT
    obtain ⟨Wl, h1, h2, h3⟩ := hSigOutWl T hT
    exact ⟨Wl, h1, h2, fun W hW hd => subset_trans (h3 W hW hd) hmono⟩
  have hSigVlC : ∀ T ∈ Pp0.Cand, ∀ T' ∈ Pp0.Cand, ∃ Vl : List (Stratum 0 (pPair n m)),
      (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet T T').set) ∧
      ((absLevelPairSet T T').set = ⋃ V ∈ Vl, V.X.set) ∧
      (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - T.j →
        pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
      (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - T.j →
        pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) := by
    intro T hT T' hT'
    obtain ⟨Vl, h1, h2, h3, h4⟩ := hSigOutVl T hT T' hT'
    exact ⟨Vl, h1, h2, (fun V hV hd => subset_trans (h3 V hV hd) hmono),
      (fun V hV hd => subset_trans (h4 V hV hd) hmono)⟩
  have hSigVlVC : ∀ S ∈ Pp0.Cand, ∀ T ∈ Pp0.Pv, ∃ Vl : List (Stratum 0 (pPair n m)),
      (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet S T).set) ∧
      ((absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set) ∧
      (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
        pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
      (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
        pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) := by
    intro S hS T hT
    obtain ⟨Vl, h1, h2, h3, h4⟩ := hSigOutVlV S hS T hT
    exact ⟨Vl, h1, h2, (fun V hV hd => subset_trans (h3 V hV hd) hmono),
      (fun V hV hd => subset_trans (h4 V hV hd) hmono)⟩
  have hSigWlVC : ∀ S ∈ Pp0.Cand, ∀ T ∈ Pp0.Pv, ∃ Wl : List (Stratum 0 (pPair n m)),
      (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet2 S T).set) ∧
      ((absPairSet2 S T).set = ⋃ W ∈ Wl, W.X.set) ∧
      (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - S.j →
        pairBase n m w ∈ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) := by
    intro S hS T hT
    obtain ⟨Wl, h1, h2, h3⟩ := hSigOutWlV S hS T hT
    exact ⟨Wl, h1, h2, fun W hW w hw hd => hmono (h3 W hW w hw hd)⟩
  have hSigOutFmt : ∀ Z ∈ SigOut, Z.fmt ≤ Ft := by
    intro Z hZ
    refine le_trans (hSigOutMemL Z hZ).1 ?_
    show Atot ≤ max (max Ac Atot) F
    omega
  have hSigOutDeg : ∀ Z ∈ SigOut, Z.deg ≤ P.eval D :=
    fun Z hZ => le_trans (hSigOutMemL Z hZ).2.1 (hPB_l D)
  have hSigOutLen : SigOut.length ≤ MvPolynomial.eval ![D, k] Nsig2 := by
    have h : Sig.length = SigOut.length + SigLow.length := List.length_append
    have h2 := hSigLen
    rw [h] at h2
    omega
  have hSigSplit : ∀ Z ∈ Sig, Z ∈ SigOut ∨
      ∃ X ∈ (List.ofFn (fun q : Fin Pp0.PieceList.length => List.ofFn (Pp0.SloR q))).flatten
          ++ (List.ofFn Pp0.Ly).flatten,
        projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' X.set := by
    intro Z hZ
    rw [show Sig = SigOut ++ SigLow from rfl] at hZ
    rcases List.mem_append.mp hZ with hZ | hZ
    · exact Or.inl hZ
    · right
      dsimp only [SigLow] at hZ
      rw [List.mem_map] at hZ
      obtain ⟨X, hX, rfl⟩ := hZ
      exact ⟨X, by simpa only [SloL, LyL] using hX, Work.WilE7.pad_proj hpad_le X⟩
  have hPieFZ : ∀ p ∈ Pp0.Pie, (p.2).X.fmt ≤ c.FZ := by
    intro p hp
    have h : (p.2).X.fmt ≤ Ap := (Pp0.specPieces.2.2.1 p hp).2.1
    rw [hFZ_l]
    refine le_trans h ?_
    show Ap ≤ Ap + Ar + Af + Atot + pPair n F + 2
    omega
  exact ⟨{ base := Pp0, Sig := Sig,
            specSig := ⟨hSigMem, hSigLowC, hSigFrontC, hSigWlC, hSigVlC, hSigVlVC,
              hSigWlVC⟩,
            hSigLen := hSigLen, hPieFZ := hPieFZ, hSigFZ := hSigFZ, hSigND := hSigND,
            hSigDeg := hSigDeg, hSigDegDg := hSigDegDg, SigOut := SigOut,
            hSigOutFmt := hSigOutFmt, hSigOutLen := hSigOutLen, hSigOutDeg := hSigOutDeg,
            hSigSplit := hSigSplit,
            hSigSloR := hSigSloR, hSigLy := hSigLy }, trivial⟩

end

end Work.WilE7.Endgame.E2B
