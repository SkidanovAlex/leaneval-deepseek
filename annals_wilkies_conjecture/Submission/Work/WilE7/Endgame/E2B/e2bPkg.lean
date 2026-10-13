/-
  Area E7 / E2B, node `cellRefine_of_nodesB`: **the package `E2Pkg`**.

  This module assembles the data package `E2Pkg` from the four parts built in the sibling modules
  (`PkgPart`: the pieces and the candidates, `PkgSigma`: the `Σ`-family, `PkgZl`: the fibre products
  `X'`, `PkgYl`: the packing `Y'`), and discharges the two generic `∀`-clauses `hSheet`/`hGcell`
  by the producers `E2_sheets_of_stratum` and `SheetData.gcase_cfs`.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.PkgZl
import Submission.Work.WilE7.Endgame.E2B.PkgYl

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

theorem e2bPkg (hFC : Work.WilE7.CoreLTSuccPlan.HypFC) (hE2 : Work.WilE7.CoreLTSuccPlan.HypE2)
    (hE5 : Work.WilE7.CoreLTSuccPlan.HypE5) (hE6 : Work.WilE7.CoreLTSuccPlan.HypE6)
    (h0 : Work.WilE7.CoreLTSuccPlan.FrontierRestrat) (h1 : Work.WilE7.CoreLTSuccPlan.SigmaVPairs)
    (n K F : ℕ) (Fq : ℕ) (Qq : Polynomial ℕ)
    (c2 : E2Const2 (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) Fq Qq)
    (D k l m m' : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m))
    (Y : Fin l → WilkiesDesign.E.SemiPf (n + m'))
    (hX : ∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D)
    (hY : ∀ i, (Y i).fmt ≤ F ∧ (Y i).deg ≤ D)
    (hND : ∀ i, Work.WilE7.MainDesign.NullDimLT
      (Work.WilE7.MainDesign.basePr n m '' (X i).set) (K + 1))
    (hk : 0 < k) :
    ∃ P : E2Pkg (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) c2 D k l m m' X Y, True := by
  classical
  let c : E2Const n K F := e2bConst hFC hE2 hE5 hE6 h0 h1 n K F
  obtain ⟨S, _⟩ := e2bSigmaPart hFC hE2 hE5 hE6 h0 h1 n K F D k m X hX hND hk
  obtain ⟨Z, _⟩ := e2bZlPart hFC hE2 hE5 hE6 h0 h1 n K F D k l m X hX hND hk S
  obtain ⟨Yl, ⟨hY1, hY2, hY3, hY4, hY5, hY6, hY7, hY8, hY9⟩, hYout1, hYout2, hYout3⟩ :=
    e2bYlPart hFC hE2 hE5 hE6 h0 h1 n K F D k l m m' X Y hX hY hND hk S
  -- ## the two generic clauses, by the producers
  have hSheetData := (E2_sheets_of_stratum hE2 (c.Ap + c.Ar + c.Af)).choose_spec.choose_spec
  have hSheet : ∀ (Sh : Stratum 0 (n + (m + 1))) (b : Set (Fin n → ℝ))
      (Sig' : List (SemiPf (n + pPair n m))) (Wl : List (Stratum 0 (pPair n m))),
      Sh.Good → Sh.X.fmt ≤ c.Ac → Sh.deg ≤ c.Dq.eval D →
      (∀ z ∈ Sh.X.set, projRank Sh z = n + (m + 1) - Sh.j) → IsCell n b → b.Nonempty →
      b ⊆ projFirst n (m + 1) '' absSet Sh →
      (∀ Z ∈ Sig', Disjoint b (projFirst n (pPair n m) '' Z.set)) →
      frontierSet n m Sh ⊆ ⋃ Z ∈ Sig', projFirst n (pPair n m) '' Z.set →
      (∀ W ∈ Wl, W.Good) → (∀ W ∈ Wl, W.X.set ⊆ (absPairSet Sh).set) →
      ((absPairSet Sh).set = ⋃ W ∈ Wl, W.X.set) →
      (∀ W ∈ Wl, pPair n m - W.j < n + (m + 1) - Sh.j →
        pairSubBaseFst n m W ⊆ ⋃ Z ∈ Sig', projFirst n (pPair n m) '' Z.set) →
      ∃ (kk : ℕ) (s : Fin kk → (Fin n → ℝ) → (Fin (m + 1) → ℝ)),
        0 < kk ∧ (∀ j, ContinuousOn (s j) b) ∧
        (∀ x ∈ b, Function.Injective fun j : Fin kk => s j x) ∧
        (∀ (j : Fin kk) (x : Fin n → ℝ), x ∈ b → Fin.append x (s j x) ∈ absSet Sh) ∧
        (∀ x ∈ b, (fiber (absSet Sh) x).ncard = kk) ∧
        (∀ z ∈ absSet Sh, projFirst n (m + 1) z ∈ b →
          ∃ j : Fin kk, s j (projFirst n (m + 1) z) = projSnd n (m + 1) z) ∧
        kk ≤ c.Ps.eval (c.Dq.eval D) :=
    fun Sh b Sig' Wl hGood hfmt hdeg hrank hCell hbne hbsub hdisj hfront hWgood hWsub hWcov
      hWlow =>
      hSheetData n m K (Polynomial.eval D c.Dq) Sh b Sig' Wl hGood hfmt hdeg hrank hCell hbne
        hbsub hdisj hfront hWgood hWsub hWcov hWlow
  have hGcell : ∀ (p₀ mm r : ℕ) (Xc : Fin r → SemiPf (p₀ + (mm + 1)))
      (Zc : SemiPf (p₀ + (mm + 1))) (u₀ : Fin (p₀ + (mm + 1)) → ℝ)
      (hu₀ : u₀ ∈ Zc.set) (Cc : Set (Fin p₀ → ℝ))
      (hC : Cc = Set.image (projFirst p₀ (mm + 1)) (connectedComponentIn Zc.set u₀))
      (hCpf : SubPf p₀ Cc) (hCellc : IsCell p₀ Cc)
      (kc : Fin r → ℕ) (hk' : ∀ t, 0 < kc t)
      (sc : ∀ t : Fin r, Fin (kc t) → (Fin p₀ → ℝ) → (Fin (mm + 1) → ℝ))
      (hcont : ∀ t j, ContinuousOn (sc t j) Cc)
      (hinj : ∀ (t : Fin r) (x : Fin p₀ → ℝ), x ∈ Cc →
        Function.Injective fun j : Fin (kc t) => sc t j x)
      (hsub : ∀ (t : Fin r) (j : Fin (kc t)), ∀ x ∈ Cc,
        Fin.append x (sc t j x) ∈ (Xc t).set)
      (hcov : ∀ (t : Fin r) (z : Fin (p₀ + (mm + 1)) → ℝ), z ∈ (Xc t).set →
        projFirst p₀ (mm + 1) z ∈ Cc →
        ∃ j : Fin (kc t), sc t j (projFirst p₀ (mm + 1) z) = projSnd p₀ (mm + 1) z)
      (hbnd_le : ∀ (t : Fin r) (j : Fin (kc t)), ∀ x ∈ Cc, |(sc t j x) (Fin.last mm)| ≤ 1)
      (hcls : ∀ (t : Fin r) (j : Fin (kc t)),
        (∀ x ∈ Cc, (sc t j x) (Fin.last mm) = 1) ∨
        (∀ x ∈ Cc, (sc t j x) (Fin.last mm) = -1) ∨
        (∀ x ∈ Cc, |(sc t j x) (Fin.last mm)| < 1))
      (hdich : ∀ (t t' : Fin r) (j : Fin (kc t)) (j' : Fin (kc t')),
        (∃ x ∈ Cc, (sc t j x) (Fin.last mm) = (sc t' j' x) (Fin.last mm)) →
        ∀ x ∈ Cc, (sc t j x) (Fin.last mm) = (sc t' j' x) (Fin.last mm))
      (Dc : ℕ) (hS : ∀ t : Fin r, (Xc t).fmt ≤ c2.Fbig ∧ (Xc t).deg ≤ Dc)
      (hZF : Zc.fmt ≤ c2.Fbig) (hZD : Zc.deg ≤ Dc),
      ∃ (Kc : ℕ) (TT : Fin Kc → (Fin p₀ → ℝ) → ℝ),
        (∀ i : Fin Kc, ContinuousOn (TT i) Cc) ∧
        (∀ x ∈ Cc, StrictMono fun i : Fin Kc => TT i x) ∧
        (∀ x ∈ Cc, ∀ i : Fin Kc, |TT i x| < 1) ∧
        (∀ (t : Fin r) (j : Fin (kc t)),
          (∃ i : Fin Kc, ∀ x ∈ Cc, TT i x = (sc t j x) (Fin.last mm)) ∨
          (∀ x ∈ Cc, (sc t j x) (Fin.last mm) = 1) ∨
          (∀ x ∈ Cc, (sc t j x) (Fin.last mm) = -1)) ∧
        (∀ i : Fin Kc, ∃ (t : Fin r) (j : Fin (kc t)),
          ∀ x ∈ Cc, TT i x = (sc t j x) (Fin.last mm)) ∧
        Kc ≤ (∑ t, kc t) ∧
        (∀ κ ∈ Work.WilE7.cfs Cc TT, Fin.init '' κ = Cc) ∧
        IsCylDecompOn (p₀ + 1) (Work.WilE7.cyl Cc) (Work.WilE7.cfs Cc TT) ∧
        (Work.WilE7.cfs Cc TT).card ≤ 2 * (∑ t, kc t) + 3 ∧
        (∀ κ ∈ Work.WilE7.cfs Cc TT, (∃ Pc : StarPiece (p₀ + 1),
            Pc.set = κ ∧ Pc.X.fmt ≤ c2.Ag ∧ Pc.X.deg ≤ c2.Cbg.eval Dc) ∧
          SubPf (p₀ + 1) κ) := by
    intro p₀ mm r Xc Zc u₀ hu₀ Cc hC hCpf hCellc kc hk' sc hcont hinj hsub hcov hbnd_le hcls
      hdich Dc hS hZF hZD
    have h := (Work.WilE7.SheetData.gcase_cfs c2.Fbig).choose_spec.choose_spec p₀ mm r Xc Zc u₀
      hu₀ Cc hC hCpf hCellc kc hk' sc hcont hinj hsub hcov hbnd_le hcls hdich Dc hS hZF hZD
    rw [c2.hEqAg, c2.hEqCbg]
    exact h
  -- ## the package
  exact ⟨{ Pie := S.base.Pie, Cut := S.base.Cut, PieceList := S.base.PieceList, Ld := S.base.Ld,
            Lg := S.base.Lg, Ly := S.base.Ly, SloR := S.base.SloR, Cand := S.base.Cand,
            Pv := S.base.Pv, Sig := S.Sig, Zl := Z.Zl, Yl := Yl,
            hPieceLlen := S.base.hPieceLlen, hPieceLget := S.base.hPieceLget,
            hPieceLmem := S.base.hPieceLmem, specPL := S.base.specPL,
            specPieces := S.base.specPieces, specLd := S.base.specLd,
            specLdcov := S.base.specLdcov, specSloR := S.base.specSloR,
            specLg := S.base.specLg, specLy := S.base.specLy, specCand := S.base.specCand,
            specCandLd := S.base.specCandLd, specCandLg := S.base.specCandLg,
            specCandCut := S.base.specCandCut, specPieceLen := S.base.specPieceLen,
            specCandLen := S.base.specCandLen, specPv := S.base.specPv,
            specPvAll := S.base.specPvAll, specSig := S.specSig,
            specZ := Z.specZ, specY := ⟨hY1, hY2, hY3, hY4, hY5, hY6, hY7, hY8, hY9⟩,
            specZout := Z.specZout,
            specYout := ⟨hYout1, hYout2, hYout3⟩,
            hSheet := hSheet, hGcell := hGcell, hSigLen := S.hSigLen, hPieFZ := S.hPieFZ,
            hSigFZ := S.hSigFZ, hSigND := S.hSigND, hSigDeg := S.hSigDeg,
            hSigSloR := S.hSigSloR, hSigLy := S.hSigLy }, trivial⟩

end

end Work.WilE7.Endgame.E2B
