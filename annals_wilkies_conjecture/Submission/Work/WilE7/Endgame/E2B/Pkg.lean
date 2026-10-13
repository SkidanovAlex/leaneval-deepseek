/-
  Area E7 / E2B: the data package (`E2Const`, `E2Const2`, `E2Pkg`) of the `cellRefine_of_nodesB`
  assembly and the per-base-cell refinement clauses.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Vocab
import Submission.Work.WilE7.pad_stratum

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

/-! ## §3. The constants of the bookkeeping, and the data package -/

section Pkg

open Work.WilE7.CoreLTSuccPlan

/-- The constants of the bookkeeping that do not depend on `(Fq, Qq)`: the producer outputs, the
polynomials and the format/dimension bounds. -/
structure E2Const (n K F : ℕ) where
  Ap : ℕ
  Pp : Polynomial ℕ
  Np : MvPolynomial (Fin 2) ℕ
  Ar : ℕ
  Pr : Polynomial ℕ
  Af : ℕ
  Pf : Polynomial ℕ
  As : ℕ
  Ps : Polynomial ℕ
  Ac : ℕ
  Fp : ℕ
  Dq : Polynomial ℕ
  Atot : ℕ
  Btot : Polynomial ℕ
  Qtot : MvPolynomial (Fin 3) ℕ
  FZ : ℕ
  AZl : ℕ
  BZl : Polynomial ℕ
  Nsig2 : MvPolynomial (Fin 2) ℕ
  M2 : ℕ
  Ft : ℕ
  Fp0 : ℕ
  /- `Dg` bounds the degrees of the `Σlow` members (`Pr.eval (Pp.eval D)` for the rank slices,
  `Pf.eval (Pp.eval D)` for the frontier sets); `hPdz` is the degree bound of the fibre products
  with them. -/
  Dg : Polynomial ℕ
  P : Polynomial ℕ
  Nk : MvPolynomial (Fin 3) ℕ
  Nl : MvPolynomial (Fin 3) ℕ
  Ng : MvPolynomial (Fin 3) ℕ
  hDqP : ∀ D : ℕ, Dq.eval D = Pp.eval D + Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 1
  hPD : ∀ D : ℕ, D ≤ P.eval D
  hPPp : ∀ D : ℕ, Pp.eval D ≤ P.eval D
  hPrP : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ P.eval D
  hPfP : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ P.eval D
  hPDq : ∀ D : ℕ, Dq.eval D ≤ P.eval D
  hPB : ∀ D : ℕ, Btot.eval (Dq.eval D) ≤ P.eval D
  hPPs : ∀ D : ℕ, Ps.eval (Dq.eval D) ≤ P.eval D
  hP3 : ∀ D : ℕ, 3 * Dq.eval D + 2 ≤ P.eval D
  hDgPr : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ Dg.eval D
  hDgPf : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ Dg.eval D
  hPdz : ∀ D : ℕ, BZl.eval (Dq.eval D + Dg.eval D) ≤ P.eval D
  hFp : Fp = 2 * Ac
  hAc : Ac = Ap + Ar + Af
  hFZ : FZ = Ac + Atot + pPair n F + 2
  hM2 : M2 = F + F + pPair n F + 5
  hFt : Ft = max (max Ac Atot) F
  hFp0 : Fp0 = max AZl (Ft + M2)
  hNl : ∀ D k l : ℕ, l ≤ MvPolynomial.eval ![D, k, l] Nl
  hNlE : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Nl =
    l + (MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) +
      (MvPolynomial.eval ![D, k] Nsig2 + MvPolynomial.eval ![D, k] Np * (Pf.eval (Pp.eval D) + K)) +
      ((MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) +
       MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2))
  hNk : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Nk =
    MvPolynomial.eval ![D, k] Np * MvPolynomial.eval ![D, k] Nsig2
  hNg : ∀ D k l : ℕ, MvPolynomial.eval ![D, k, l] Ng =
    3 + 2 * ((MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)) *
      Ps.eval (Dq.eval D))
  hNsig : ∀ D k : ℕ, MvPolynomial.eval
      ![Dq.eval D, MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2),
        MvPolynomial.eval ![D, k] Np] Qtot ≤ MvPolynomial.eval ![D, k] Nsig2
/-- The identification of the constants of an `E2Const` with the producer outputs.  It is what lets
the per-base-cell refinement use the producers (`E2_pieces_of_family`, `E2_rank_strata`,
`E2_frontier_strata`, `E2_sheets_of_stratum`, `E2B.sigmaTotal`, `fibreProd_sigma_lem`) at the
constants carried by the package. -/
def EqSpec {n K F : ℕ} (c : E2Const n K F) (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5)
    (hE6 : HypE6) (h0 : FrontierRestrat) (h1 : SigmaVPairs) : Prop :=
  c.Ap = (E2_pieces_of_family hFC hE5 F).choose ∧
  c.Pp = (E2_pieces_of_family hFC hE5 F).choose_spec.choose ∧
  c.Np = (E2_pieces_of_family hFC hE5 F).choose_spec.choose_spec.choose ∧
  c.Ar = (E2_rank_strata hE5 c.Ap).choose ∧
  c.Pr = (E2_rank_strata hE5 c.Ap).choose_spec.choose ∧
  c.Af = (E2_frontier_strata h0 c.Ap).choose ∧
  c.Pf = (E2_frontier_strata h0 c.Ap).choose_spec.choose ∧
  c.As = (E2_sheets_of_stratum hE2 (c.Ap + c.Ar + c.Af)).choose ∧
  c.Ps = (E2_sheets_of_stratum hE2 (c.Ap + c.Ar + c.Af)).choose_spec.choose ∧
  c.Qtot = (E2B.sigmaTotal hE5 hE6 h1 n K c.Fp F).choose ∧
  c.Atot = (E2B.sigmaTotal hE5 hE6 h1 n K c.Fp F).choose_spec.choose ∧
  c.Btot = (E2B.sigmaTotal hE5 hE6 h1 n K c.Fp F).choose_spec.choose_spec.choose ∧
  c.AZl = (Work.CoreStep.fibreProd_sigma_lem c.FZ).choose ∧
  c.BZl = (Work.CoreStep.fibreProd_sigma_lem c.FZ).choose_spec.choose

/-- The degree budget `Dc` at which the `G`-case producer `SheetData.gcase_cfs` is called.  It must
dominate the degrees of *both* the base presentation and the candidate strata once they have been
carried into the common frame `(n, d + m + 1)`, `d ≤ Fq`:

* the candidates are transferred by a *pinned* middle padding (`Work.WilE7.padStrat`), whose degree is
  `≤ (Work.WilE7.padDegPoly d).eval (c.Dq.eval D) = 2 * d + (1 + 2 * d) * (c.Dq.eval D)`
  (`Work.WilE7.PadAux.padStrat_deg`); `Work.WilE7.pad_stratum` uses the same bound, while the
  composite `Work.WilE7.pad_to_common` doubles the coefficients and also pads the base
  presentation, giving `≤ 2 * d + (2 + 2 * d) * X`;
* the base presentation is the degree-preserving `SemiPf.pad` of `(StarPiece.init P₀).X`
  (`Work.WilE7.pad_component_proj`), of degree `≤ Qq.eval D`.

The displayed bound dominates all of these (each `* X` term at `X = c.Dq.eval D` and at
`X = Qq.eval D`), uniformly in the choice `0 ≤ d ≤ Fq`. -/
def gcaseDeg {n K F : ℕ} (c : E2Const n K F) (Fq : ℕ) (Qq : Polynomial ℕ) (D : ℕ) : ℕ :=
  2 * Fq + 2 * (1 + 2 * Fq) * (c.Dq.eval D + Qq.eval D) + 2

structure E2Const2 {n K F : ℕ} (c : E2Const n K F) (Fq : ℕ) (Qq : Polynomial ℕ) where
  AB : ℕ
  CB : Polynomial ℕ
  Fbig : ℕ
  Ag : ℕ
  Cbg : Polynomial ℕ
  /- `Fbig` must bound the formats of *both* the base presentation and the candidate strata carried
  into the common frame `(n, d + m + 1)` with `d ≤ Fq`: the padded candidates have format
  `≤ max Fq c.Ac + d ≤ 2 * Fq + c.Ac` by `Work.WilE7.pad_stratum` (or `≤ 2 * max Fq c.Ac + d` by
  `Work.WilE7.pad_to_common`), and the padded base has format `≤ Fq + m ≤ Fq + F`. -/
  hBig : Fbig = 2 * c.Ac + c.M2 + 4 * Fq + 4
  hAB : AB = max Ag c.Fp0
  /- `hCB` must dominate the degree of the *padded* strata; see `gcaseDeg` for the bookkeeping. -/
  hCB : ∀ D : ℕ, Cbg.eval (gcaseDeg c Fq Qq D) ≤ CB.eval D
  hEqAg : Ag = (Work.WilE7.SheetData.gcase_cfs Fbig).choose
  hEqCbg : Cbg = (Work.WilE7.SheetData.gcase_cfs Fbig).choose_spec.choose

/-- The data produced by the assembly for one instance `D k l m m' X Y`, together with all the
properties the per-base-cell refinement consumes. -/
structure E2Pkg {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) (D k l m m' : ℕ)
    (X : Fin k → SemiPf ((n + 1) + m)) (Y : Fin l → SemiPf (n + m')) where
  Pie : List (Fin k × Stratum 0 ((n + 1) + m))
  Cut : List (Stratum 0 (n + (m + 1)))
  PieceList : List (Stratum 0 (n + (m + 1)))
  Ld : (q : Fin PieceList.length) → List (Stratum 0 (n + (m + 1)))
  Lg : (q : Fin PieceList.length) → List (Stratum 0 (n + (m + 1)))
  Ly : (q : Fin PieceList.length) → List (SemiPf (n + (m + 1)))
  SloR : (q : Fin PieceList.length) → Fin K → SemiPf (n + (m + 1))
  Cand : List (Stratum 0 (n + (m + 1)))
  Pv : List (Stratum 0 (n + (m + 1)))
  /- ## The correspondence between the two piece lists

  `RefineConcl`'s compatibility clause describes `projFirst (n+1) m '' (X i).set` through the list
  `Pie` of the `π_{n+1}`-cut, while all the data that can make a family of cells compatible with it
  (`Ld`, `Lg`, `Ly`, `SloR`, `Pv`, and the sheets attached to the candidates `Cand`) is indexed by
  the list `PieceList`.  The construction takes `PieceList = Pie.map (fun p => E2.swapStratum p.2)`
  (`E2.swapStratum` only moves the last base coordinate into the fibre, keeping the `π_{n+1}`-image:
  `E2.swapStratum_projTop`); these fields record that link, without which the `G`-case is not
  provable. -/
  hPieceLlen : PieceList.length = Pie.length
  hPieceLget : ∀ p ∈ Pie, ∃ q : Fin PieceList.length, PieceList.get q = E2.swapStratum p.2
  hPieceLmem : ∀ T ∈ PieceList, ∃ p ∈ Pie, E2.swapStratum p.2 = T
  /- the facts about the members of `PieceList` (they are the `π_{n+1}`-cut pieces seen in the
  `(n, m+1)` frame: `Good`, format `≤ c.Ap`, degree `≤ c.Pp.eval D`, dimension `≤ K+1` and
  `π_n`-rank `≤ K`; the `HImm` clause of `PiecesSpec` is the further fact that the `(n+1)`-rank is
  the full dimension, from which `hvert` for the vertical pieces follows, see
  `E2B/projRank_vert_of_hImm`). -/
  specPL : ∀ T ∈ PieceList, T.Good ∧ T.X.fmt ≤ c.Ap ∧ T.deg ≤ c.Pp.eval D ∧
    n + (m + 1) - T.j ≤ K + 1 ∧ (∀ z ∈ T.X.set, projRank T z ≤ K)
  /- `Sig` is the whole `Σ`-family: the output of `E2B.sigmaTotal` *together with* the `Σlow`
  members (the rank slices `SloR` and the frontier sets `Ly`, padded to the fibre dimension
  `pPair n m`), so that the `Σ`-case of the per-base-cell refinement covers the rank-deficient
  loci as well. -/
  Sig : List (SemiPf (n + pPair n m))
  Zl : List (SemiPf ((n + 1) + (m + pPair n m)))
  Yl : List (SemiPf (n + c.M2))
  specPieces : PiecesSpec n m k c.Ap c.Pp c.Np D K X Pie Cut
  specLd : ∀ q : Fin PieceList.length, (Ld q).length ≤ c.Pr.eval (c.Pp.eval D) ∧
    (∀ S ∈ Ld q, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ c.Ar ∧
      S.deg ≤ c.Pr.eval (c.Pp.eval D) ∧
      n + (m + 1) - S.j ≤ K ∧ (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
      S.X.set ⊆ (PieceList.get q).X.set ∧
      S.X.set ⊆ {z | projRank (PieceList.get q) z = n + (m + 1) - (PieceList.get q).j})
  specLdcov : ∀ q : Fin PieceList.length,
    {z | z ∈ (PieceList.get q).X.set ∧
        projRank (PieceList.get q) z = n + (m + 1) - (PieceList.get q).j} =
      ⋃ S ∈ Ld q, S.X.set
  specSloR : ∀ (q : Fin PieceList.length) (r : Fin K), (SloR q r).fmt ≤ c.Ar ∧
    (SloR q r).deg ≤ c.Pr.eval (c.Pp.eval D) ∧
    (SloR q r).set = absPt '' {z | z ∈ (PieceList.get q).X.set ∧
      projRank (PieceList.get q) z = (r : ℕ)} ∧
    NullDimLT (projFirst n (m + 1) '' (SloR q r).set) K
  specLg : ∀ q : Fin PieceList.length, (Lg q).length ≤ c.Pf.eval (c.Pp.eval D) ∧
    (∀ S ∈ Lg q, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ c.Af ∧
      S.deg ≤ c.Pf.eval (c.Pp.eval D) ∧
      n + (m + 1) - S.j ≤ K ∧ (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
      S.X.set ⊆ closure (PieceList.get q).X.set \ (PieceList.get q).X.set)
  specLy : ∀ q : Fin PieceList.length, (Ly q).length ≤ c.Pf.eval (c.Pp.eval D) ∧
    (∀ Yc ∈ Ly q, Yc.fmt ≤ c.Af ∧ Yc.deg ≤ c.Pf.eval (c.Pp.eval D) ∧
      NullDimLT (projFirst n (m + 1) '' Yc.set) K) ∧
    closure (absSet (PieceList.get q)) \ absSet (PieceList.get q) ⊆
      (⋃ S ∈ Lg q, absSet S) ∪ ⋃ Yc ∈ Ly q, Yc.set
  specCand : CandSpec n m K c.Ac c.Dq D Cand
  specCandLd : ∀ (q : Fin PieceList.length) (S : Stratum 0 (n + (m + 1))), S ∈ Ld q → S ∈ Cand
  specCandLg : ∀ (q : Fin PieceList.length) (S : Stratum 0 (n + (m + 1))), S ∈ Lg q → S ∈ Cand
  specCandCut : ∀ S ∈ Cut, S ∈ Cand
  specPieceLen : PieceList.length ≤ MvPolynomial.eval ![D, k] c.Np
  specCandLen : Cand.length ≤ MvPolynomial.eval ![D, k] c.Np *
    (c.Pr.eval (c.Pp.eval D) + c.Pf.eval (c.Pp.eval D) + 2)
  specPv : ∀ T ∈ Pv, T ∈ PieceList ∧ n + (m + 1) - T.j = K + 1
  specPvAll : ∀ T ∈ PieceList, n + (m + 1) - T.j = K + 1 → T ∈ Pv
  specSig : SigSpec n m K (max (c.Btot.eval (c.Dq.eval D)) (c.P.eval D))
    (max c.Atot (c.Ac + pPair n m)) Cand Pv Sig
  specZ : (∀ Z ∈ Zl, Z.fmt ≤ c.AZl ∧
      NullDimLT (basePr n (m + pPair n m) '' Z.set) K ∧ Z.deg ≤ c.P.eval D) ∧
    (∀ (i : Fin Pie.length) (j : Fin Sig.length), ∃ i' : Fin Zl.length,
      (Zl.get i').deg ≤ c.BZl.eval ((Pie.get i).2.deg + (Sig.get j).deg) ∧
      projFirst (n + 1) (m + pPair n m) '' (Zl.get i').set =
        (projFirst (n + 1) m '' absSet (Pie.get i).2) ∩
          {y : Fin (n + 1) → ℝ |
            Fin.init y ∈ projFirst n (pPair n m) '' (Sig.get j).set})
  specY : (∀ i : Fin Yl.length, (Yl.get i).fmt ≤ c.Fp0 ∧ (Yl.get i).deg ≤ c.P.eval D) ∧
    (∀ S ∈ Cand, ∃ i : Fin Yl.length,
      projFirst n c.M2 '' (Yl.get i).set = projFirst n (m + 1) '' absSet S) ∧
    (∀ Z ∈ Sig, ∃ i : Fin Yl.length,
      projFirst n c.M2 '' (Yl.get i).set = projFirst n (pPair n m) '' Z.set) ∧
    (∀ (q : Fin PieceList.length) (r : Fin K), ∃ i : Fin Yl.length,
      projFirst n c.M2 '' (Yl.get i).set = projFirst n (m + 1) '' (SloR q r).set) ∧
    (∀ (q : Fin PieceList.length) (Yc : SemiPf (n + (m + 1))), Yc ∈ Ly q →
      ∃ i : Fin Yl.length,
        projFirst n c.M2 '' (Yl.get i).set = projFirst n (m + 1) '' Yc.set) ∧
    (∀ S ∈ Cand, ∃ i : Fin Yl.length,
      projFirst n c.M2 '' (Yl.get i).set = projFirst n (m + 1) '' (E2.sliceSemiPf S 1).set) ∧
    (∀ S ∈ Cand, ∃ i : Fin Yl.length,
      projFirst n c.M2 '' (Yl.get i).set = projFirst n (m + 1) '' (E2.sliceSemiPf S (-1)).set) ∧
    (∀ j : Fin l, ∃ i : Fin Yl.length,
      projFirst n c.M2 '' (Yl.get i).set = projFirst n m' '' (Y j).set) ∧
    (∀ T ∈ PieceList, ∃ i : Fin Yl.length,
      projFirst n c.M2 '' (Yl.get i).set = projFirst n (m + 1) '' absSet T)
  specZout : Zl.length ≤ MvPolynomial.eval ![D, k, l] c.Nk ∧
    (∀ i : Fin Zl.length, (Zl.get i).fmt ≤ c.Fp0 ∧ (Zl.get i).deg ≤ c.P.eval D ∧
      NullDimLT (basePr n (m + pPair n m) '' (Zl.get i).set) K)
  specYout : Yl.length ≤ MvPolynomial.eval ![D, k, l] c.Nl ∧
    (∀ i : Fin Yl.length, (Yl.get i).fmt ≤ c.Fp0 ∧ (Yl.get i).deg ≤ c.P.eval D) ∧
    (∀ j : Fin l, ∃ j' : Fin Yl.length,
      projFirst n m' '' (Y j).set = projFirst n c.M2 '' (Yl.get j').set)
  hSheet : ∀ (S : Stratum 0 (n + (m + 1))) (b : Set (Fin n → ℝ))
      (Sig' : List (SemiPf (n + pPair n m))) (Wl : List (Stratum 0 (pPair n m))),
      S.Good → S.X.fmt ≤ c.Ac → S.deg ≤ c.Dq.eval D →
      (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) → IsCell n b → b.Nonempty →
      b ⊆ projFirst n (m + 1) '' absSet S →
      (∀ Z ∈ Sig', Disjoint b (projFirst n (pPair n m) '' Z.set)) →
      frontierSet n m S ⊆ ⋃ Z ∈ Sig', projFirst n (pPair n m) '' Z.set →
      (∀ W ∈ Wl, W.Good) → (∀ W ∈ Wl, W.X.set ⊆ (absPairSet S).set) →
      ((absPairSet S).set = ⋃ W ∈ Wl, W.X.set) →
      (∀ W ∈ Wl, pPair n m - W.j < n + (m + 1) - S.j →
        pairSubBaseFst n m W ⊆ ⋃ Z ∈ Sig', projFirst n (pPair n m) '' Z.set) →
      ∃ (kk : ℕ) (s : Fin kk → (Fin n → ℝ) → (Fin (m + 1) → ℝ)),
        0 < kk ∧ (∀ j, ContinuousOn (s j) b) ∧
        (∀ x ∈ b, Function.Injective fun j : Fin kk => s j x) ∧
        (∀ (j : Fin kk) (x : Fin n → ℝ), x ∈ b → Fin.append x (s j x) ∈ absSet S) ∧
        (∀ x ∈ b, (fiber (absSet S) x).ncard = kk) ∧
        (∀ z ∈ absSet S, projFirst n (m + 1) z ∈ b →
          ∃ j : Fin kk, s j (projFirst n (m + 1) z) = projSnd n (m + 1) z) ∧
        kk ≤ c.Ps.eval (c.Dq.eval D)
  hGcell : ∀ (p₀ mm r : ℕ) (Xc : Fin r → SemiPf (p₀ + (mm + 1)))
      (Zc : SemiPf (p₀ + (mm + 1))) (u₀ : Fin (p₀ + (mm + 1)) → ℝ)
      (hu₀ : u₀ ∈ Zc.set) (Cc : Set (Fin p₀ → ℝ))
      (hC : Cc = Set.image (projFirst p₀ (mm + 1)) (connectedComponentIn Zc.set u₀))
      (hCpf : SubPf p₀ Cc) (hCellc : IsCell p₀ Cc)
      (kc : Fin r → ℕ) (hk : ∀ t, 0 < kc t)
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
          SubPf (p₀ + 1) κ)
  hSigLen : Sig.length ≤ MvPolynomial.eval ![D, k] c.Nsig2
  hPieFZ : ∀ p ∈ Pie, (p.2).X.fmt ≤ c.FZ
  hSigFZ : ∀ Z ∈ Sig, Z.fmt ≤ c.FZ
  hSigND : ∀ Z ∈ Sig, NullDimLT (projFirst n (pPair n m) '' Z.set) K
  hSigDeg : ∀ Z ∈ Sig, Z.deg ≤ c.P.eval D
  hSigSloR : ∀ (q : Fin PieceList.length) (r : Fin K), ∃ Z ∈ Sig,
    projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' (SloR q r).set
  hSigLy : ∀ (q : Fin PieceList.length) (Yc : SemiPf (n + (m + 1))), Yc ∈ Ly q → ∃ Z ∈ Sig,
    projFirst n (pPair n m) '' Z.set = projFirst n (m + 1) '' Yc.set

/-- The hypotheses on the decomposition `B` and the base cell `b` in the per-base-cell refinement:
`B` decomposes the cube, is compatible with `X'` and `Y'`, and its cells carry bounded
`StarPiece` presentations. -/
def CompatHyp {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)}
    {Y : Fin l → SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ))) : Prop :=
  IsCylDecompOn (n + 1) (cubeC (n + 1)) B ∧
  (∀ i : Fin P.Zl.length, ∀ κ ∈ B,
    κ ⊆ projFirst (n + 1) (m + pPair n m) '' (P.Zl.get i).set ∨
    Disjoint κ (projFirst (n + 1) (m + pPair n m) '' (P.Zl.get i).set)) ∧
  (∀ i : Fin P.Yl.length, ∀ κ ∈ B,
    Fin.init '' κ ⊆ projFirst n c.M2 '' (P.Yl.get i).set ∨
    Disjoint (Fin.init '' κ) (projFirst n c.M2 '' (P.Yl.get i).set)) ∧
  (∀ κ ∈ B, (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ Fq ∧
      P₀.X.deg ≤ Qq.eval D) ∧ SubPf (n + 1) κ)

/-- The conclusion of the per-base-cell refinement over `b`, for the two branches: either the
cells of `B` over `b` are kept, or a new decomposition into cells with bounded presentations is
produced. -/
def RefineConcl {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ}
    (c2 : E2Const2 c Fq Qq) {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)}
    {Y : Fin l → SemiPf (n + m')} (P : E2Pkg c c2 D k l m m' X Y)
    (B : Finset (Set (Fin (n + 1) → ℝ))) (b : Set (Fin n → ℝ)) : Prop :=
  ∃ B' : Finset (Set (Fin (n + 1) → ℝ)),
    ((∀ κ ∈ B', κ ∈ B) ∨
      ((∀ κ ∈ B', (∃ P₀ : StarPiece (n + 1), P₀.set = κ ∧ P₀.X.fmt ≤ c2.AB ∧
          P₀.X.deg ≤ c2.CB.eval D) ∧ SubPf (n + 1) κ) ∧
        B'.card ≤ MvPolynomial.eval ![D, k, l] c.Ng)) ∧
    IsCylDecompOn (n + 1) (cubeC (n + 1) ∩ {z | Fin.init z ∈ b}) B' ∧
    (∀ κ ∈ B', Fin.init '' κ = b) ∧
    (∀ i, ∀ κ ∈ B', κ ⊆ projFirst (n + 1) m '' (X i).set ∨
      Disjoint κ (projFirst (n + 1) m '' (X i).set))

end Pkg

section Pkg2

open Work.WilE7.CoreLTSuccPlan

/-- The `G`-case hypothesis: the base cell `b` avoids the `π_n`-images of *all* the `Σ`-members
(the vertical-pair family `Sig`, the rank slices `SloR` and the frontier sets `Ly`). -/
def GHyp {n K F : ℕ} (c : E2Const n K F) {Fq : ℕ} {Qq : Polynomial ℕ} (c2 : E2Const2 c Fq Qq)
    {D k l m m' : ℕ} {X : Fin k → SemiPf ((n + 1) + m)} {Y : Fin l → SemiPf (n + m')}
    (P : E2Pkg c c2 D k l m m' X Y) (b : Set (Fin n → ℝ)) : Prop :=
  (∀ Z ∈ P.Sig, Disjoint b (projFirst n (pPair n m) '' Z.set)) ∧
  (∀ (q : Fin P.PieceList.length) (r : Fin K),
    Disjoint b (projFirst n (m + 1) '' (P.SloR q r).set)) ∧
  (∀ (q : Fin P.PieceList.length) (Yc : SemiPf (n + (m + 1))), Yc ∈ P.Ly q →
    Disjoint b (projFirst n (m + 1) '' Yc.set))

end Pkg2


end

end Work.WilE7.Endgame.E2B
