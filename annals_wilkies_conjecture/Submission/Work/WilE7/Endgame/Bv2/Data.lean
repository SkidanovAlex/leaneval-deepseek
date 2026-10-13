/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S** (module `Work.WilE7.Endgame.Bv2.Data`).

  * `E2Env2` — the constants that are chosen *after* `(Fq, Qq)`: the padded format bound `Fbig`, the
    `gcase_cfs` output `(Ag, Cbg)` at `Fbig`, the padding degree polynomial and the produced bounds
    `AB`, `CB`;
  * `E2Data` — the per-instance output of the assembly: the families `X'`, `Y'` and everything the
    per-base-cell argument consumes.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.Bv2.Env
import Submission.Work.WilE7.SheetData.gcase_cfs
import Submission.Work.WilE7.CoreStep.VerticalOpen
import Submission.Work.WilE7.init_set

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7.Endgame.Bv2

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.WilE7.CoreLTSuccPlan (absPairSet2 pairBaseRank)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

theorem le_pPair_of {n m : ℕ} : m + 1 ≤ pPair n m := by
  show m + 1 ≤ (n + (m + 1)) + (n + (m + 1))
  omega

/-- Pad a semi-Pfaffian set in the `(n, m+1)` frame to the pair frame `(n, pPair n m)`. -/
noncomputable def padP {n m : ℕ} (Z : SemiPf (n + (m + 1))) : SemiPf (n + pPair n m) :=
  Work.WilE7.SemiPf.pad (Nat.add_le_add_left (le_pPair_of (n := n) (m := m)) n) Z

theorem semipf_pad_fmt_le {k K : ℕ} (hm : k ≤ K) (X : SemiPf k) :
    (Work.WilE7.SemiPf.pad hm X).fmt ≤ X.fmt + K := by
  show K + X.r ≤ (k + X.r) + K
  omega

theorem padP_proj {n m : ℕ} (Z : SemiPf (n + (m + 1))) :
    projFirst n (pPair n m) '' (padP Z).set = projFirst n (m + 1) '' Z.set :=
  Work.WilE7.pad_proj (le_pPair_of (n := n) (m := m)) Z

theorem padP_deg_le {n m : ℕ} (Z : SemiPf (n + (m + 1))) : (padP Z).deg ≤ Z.deg :=
  Work.WilE7.semipf_deg_pad_le (Nat.add_le_add_left (le_pPair_of (n := n) (m := m)) n) Z

theorem padP_fmt_le {n m : ℕ} (Z : SemiPf (n + (m + 1))) :
    (padP Z).fmt ≤ Z.fmt + pPair n m := by
  show (n + pPair n m) + (padP Z).r ≤ Z.fmt + pPair n m
  have hr : (padP Z).r = Z.r := rfl
  rw [hr]
  show (n + pPair n m) + Z.r ≤ ((n + (m + 1)) + Z.r) + pPair n m
  omega

abbrev LevelFam (p Kc : ℕ) : Type := Fin Kc → (Fin p → ℝ) → ℝ

/-- The specification delivered by the `gcase_cfs` node at the format bound `Fbig`. -/
def GcaseSpec (Fbig Ag : ℕ) (Cbg : Polynomial ℕ) : Prop :=
  ∀ (p m r : ℕ) (X : Fin r → SemiPf (p + (m + 1)))
    (Z : SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (hu₀ : u₀ ∈ Z.set) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : SubPf p C) (hCell : IsCell p C)
    (k : Fin r → ℕ) (hk : ∀ t, 0 < k t)
    (s : ∀ t : Fin r, Fin (k t) → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ (t : Fin r) (j : Fin (k t)), ContinuousOn (s t j) C)
    (hinj : ∀ (t : Fin r) (x : Fin p → ℝ), x ∈ C →
      Function.Injective fun j : Fin (k t) => s t j x)
    (hsub : ∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C, Fin.append x (s t j x) ∈ (X t).set)
    (hcov : ∀ (t : Fin r) (z : Fin (p + (m + 1)) → ℝ), z ∈ (X t).set →
      projFirst p (m + 1) z ∈ C →
      ∃ j : Fin (k t), s t j (projFirst p (m + 1) z) = projSnd p (m + 1) z)
    (hbnd_le : ∀ (t : Fin r) (j : Fin (k t)), ∀ x ∈ C, |(s t j x) (Fin.last m)| ≤ 1)
    (hcls : ∀ (t : Fin r) (j : Fin (k t)),
      (∀ x ∈ C, (s t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ C, (s t j x) (Fin.last m) = -1) ∨
      (∀ x ∈ C, |(s t j x) (Fin.last m)| < 1))
    (hdich : ∀ (t t' : Fin r) (j : Fin (k t)) (j' : Fin (k t')),
      (∃ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m)) →
      ∀ x ∈ C, (s t j x) (Fin.last m) = (s t' j' x) (Fin.last m))
    (D : ℕ)
    (hS : ∀ t : Fin r, (X t).fmt ≤ Fbig ∧ (X t).deg ≤ D)
    (hZF : Z.fmt ≤ Fbig) (hZD : Z.deg ≤ D),
    ∃ (Kc : ℕ) (TT : LevelFam p Kc),
      (∀ i : Fin Kc, ContinuousOn (TT i) C) ∧
      (∀ x ∈ C, StrictMono fun i : Fin Kc => TT i x) ∧
      (∀ x ∈ C, ∀ i : Fin Kc, |TT i x| < 1) ∧
      (∀ (t : Fin r) (j : Fin (k t)),
      (∃ i : Fin Kc, ∀ x ∈ C, TT i x = (s t j x) (Fin.last m)) ∨
      (∀ x ∈ C, (s t j x) (Fin.last m) = 1) ∨
      (∀ x ∈ C, (s t j x) (Fin.last m) = -1)) ∧
      (∀ i : Fin Kc, ∃ (t : Fin r) (j : Fin (k t)),
      ∀ x ∈ C, TT i x = (s t j x) (Fin.last m)) ∧
      Kc ≤ (∑ t, k t) ∧
      (∀ κ ∈ Work.WilE7.cfs C TT, Fin.init '' κ = C) ∧
      IsCylDecompOn (p + 1) (Work.WilE7.cyl C) (Work.WilE7.cfs C TT) ∧
      (Work.WilE7.cfs C TT).card ≤ 2 * (∑ t, k t) + 3 ∧
      (∀ κ ∈ Work.WilE7.cfs C TT, (∃ P : StarPiece (p + 1),
        P.set = κ ∧ P.X.fmt ≤ Ag ∧ P.X.deg ≤ Cbg.eval D) ∧
      SubPf (p + 1) κ)

/-- The constants chosen after `(Fq, Qq)`. -/
structure E2Env2 {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6} {h0 : FrontierRestrat}
    {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) (Fq : ℕ) (Qq : Polynomial ℕ) where
  Fbig : ℕ
  hFbig : Fbig = E.Ac + n + F + 2 * Fq + 4
  Ag : ℕ
  Cbg : Polynomial ℕ
  hGcell : GcaseSpec Fbig Ag Cbg
  padDeg : Polynomial ℕ
  hpadDeg : padDeg = padDegOf Fq
  AB : ℕ
  hAB : AB = Ag
  CB : Polynomial ℕ
  hCB : ∀ D : ℕ, Cbg.eval (Qq.eval D + padDeg.eval (E.Dcand.eval D)) ≤ CB.eval D

/-- The per-instance data produced by the assembly, with all the properties the per-base-cell
argument and the `CellRefineS` conclusion need. -/
structure E2Data {hFC : HypFC} {hE2 : HypE2} {hE5 : HypE5} {hE6 : HypE6} {h0 : FrontierRestrat}
    {h1 : SigmaVPairs} {hV : GCaseVertical} {n K F : ℕ}
    (E : E2Env hFC hE2 hE5 hE6 h0 h1 hV n K F) (Fq : ℕ) (Qq : Polynomial ℕ)
    (D k l m m' : ℕ) (X : Fin k → SemiPf ((n + 1) + m)) (Y : Fin l → SemiPf (n + m')) where
  /- the produced families -/
  k' : ℕ
  l' : ℕ
  m₁ : ℕ
  m₂ : ℕ
  hm₁ : m₁ = m + pPair n m
  X' : Fin k' → SemiPf ((n + 1) + m₁)
  Y' : Fin l' → SemiPf (n + m₂)
  hk' : k' ≤ MvPolynomial.eval ![D, k, l] E.Nk
  hl' : l' ≤ MvPolynomial.eval ![D, k, l] E.Nl
  hX'fmt : ∀ i, (X' i).fmt ≤ E.F'
  hX'deg : ∀ i, (X' i).deg ≤ E.P.eval D
  hX'nd : ∀ i, NullDimLT (basePr n m₁ '' (X' i).set) K
  hY'fmt : ∀ i, (Y' i).fmt ≤ E.F'
  hY'deg : ∀ i, (Y' i).deg ≤ E.P.eval D
  hY'proj : ∀ j : Fin l, ∃ j' : Fin l',
    projFirst n m' '' (Y j).set = projFirst n m₂ '' (Y' j').set
  /- the pieces of the outer family -/
  Pie : List (Fin k × Stratum 0 ((n + 1) + m))
  hPieLen : Pie.length ≤ MvPolynomial.eval ![D, k] E.Np
  hPieMem : ∀ p ∈ Pie, (p.2).Good ∧ (p.2).X.fmt ≤ E.Ap ∧ (p.2).deg ≤ E.Pp.eval D ∧
    (∀ x : Fin (n + 1) → ℝ, (fiber (absSet (p.2)) x).Finite) ∧
    (∀ z ∈ (p.2).X.set, projRank (p.2) z = (n + 1) + m - (p.2).j) ∧
    projFirst (n + 1) m '' absSet (p.2) ⊆ projFirst (n + 1) m '' (X p.1).set
  hPieCov : ∀ i : Fin k, projFirst (n + 1) m '' (X i).set =
    ⋃ p ∈ Pie.filter (fun p => p.1 = i), projFirst (n + 1) m '' absSet (p.2)
  hPieSw : ∀ p ∈ Pie, (E2.swapStratum (p.2)).Good ∧ (E2.swapStratum (p.2)).X.fmt ≤ E.Ap ∧
    (E2.swapStratum (p.2)).deg ≤ E.Pp.eval D ∧
    n + (m + 1) - (E2.swapStratum (p.2)).j ≤ K + 1 ∧
    (∀ z ∈ (E2.swapStratum (p.2)).X.set, projRank (E2.swapStratum (p.2)) z ≤ K) ∧
    (∀ z ∈ (E2.swapStratum (p.2)).X.set, Module.finrank ℝ
      ↥(Submodule.map ((projTopLin n m).comp (absPtLin (n + (m + 1))))
        (jac (E2.swapStratum (p.2)) z).ker) = n + (m + 1) - (E2.swapStratum (p.2)).j) ∧
    projTop n m '' absSet (E2.swapStratum (p.2)) ⊆ projFirst (n + 1) m '' (X p.1).set
  /- the `π_n`-cut -/
  Cut : List (Stratum 0 (n + (m + 1)))
  hCutLen : Cut.length ≤ MvPolynomial.eval ![D, k] E.Np
  hCutMem : ∀ R ∈ Cut, R.Good ∧ R.X.fmt ≤ E.Ap ∧ R.deg ≤ E.Pp.eval D ∧
    (∀ z ∈ R.X.set, projRank R z = n + (m + 1) - R.j) ∧ n + (m + 1) - R.j ≤ K ∧
    (∃ i : Fin k, projFirst n (m + 1) '' absSet R ⊆ basePr n m '' (X i).set)
  hCutCov : (⋃ i : Fin k, basePr n m '' (X i).set) =
    ⋃ R ∈ Cut, projFirst n (m + 1) '' absSet R
  /- the rank strata and rank slices of the pieces -/
  PieceL : List (Stratum 0 (n + (m + 1)))
  hPieceLlen : PieceL.length = Pie.length
  hPieceLget : ∀ p ∈ Pie, ∃ q : Fin PieceL.length, PieceL.get q = E2.swapStratum p.2
  Ld : (q : Fin PieceL.length) → List (Stratum 0 (n + (m + 1)))
  hLd : ∀ q : Fin PieceL.length, (Ld q).length ≤ E.Pr.eval (E.Pp.eval D) ∧
    (∀ S ∈ Ld q, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ E.Ar ∧
      S.deg ≤ E.Pr.eval (E.Pp.eval D) ∧ n + (m + 1) - S.j ≤ K ∧
      (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
      S.X.set ⊆ (PieceL.get q).X.set ∧
      S.X.set ⊆ {z | projRank (PieceL.get q) z = n + (m + 1) - (PieceL.get q).j})
  hLdcov : ∀ q : Fin PieceL.length,
    {z | z ∈ (PieceL.get q).X.set ∧ projRank (PieceL.get q) z = n + (m + 1) - (PieceL.get q).j}
      = ⋃ S ∈ Ld q, S.X.set
  SloR : (q : Fin PieceL.length) → Fin K → SemiPf (n + (m + 1))
  hSloR : ∀ (q : Fin PieceL.length) (r : Fin K), (SloR q r).fmt ≤ E.Ar ∧
    (SloR q r).deg ≤ E.Pr.eval (E.Pp.eval D) ∧
    (SloR q r).set = absPt '' {z | z ∈ (PieceL.get q).X.set ∧
      projRank (PieceL.get q) z = (r : ℕ)} ∧
    NullDimLT (projFirst n (m + 1) '' (SloR q r).set) K
  /- the frontier strata and the `Ly` sets of the pieces -/
  Lg : (q : Fin PieceL.length) → List (Stratum 0 (n + (m + 1)))
  Ly : (q : Fin PieceL.length) → List (SemiPf (n + (m + 1)))
  hLg : ∀ q : Fin PieceL.length, (Lg q).length ≤ E.Pf.eval (E.Pp.eval D) ∧
    (Ly q).length ≤ E.Pf.eval (E.Pp.eval D) ∧
    (∀ S ∈ Lg q, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ E.Af ∧
      S.deg ≤ E.Pf.eval (E.Pp.eval D) ∧ n + (m + 1) - S.j ≤ K ∧
      (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
      S.X.set ⊆ closure (PieceL.get q).X.set \ (PieceL.get q).X.set) ∧
    (∀ Yc ∈ Ly q, Yc.fmt ≤ E.Af ∧ Yc.deg ≤ E.Pf.eval (E.Pp.eval D) ∧
      NullDimLT (projFirst n (m + 1) '' Yc.set) K) ∧
    closure (absSet (PieceL.get q)) \ absSet (PieceL.get q) ⊆
      (⋃ S ∈ Lg q, absSet S) ∪ ⋃ Yc ∈ Ly q, Yc.set
  /- the candidate family and the vertical pieces -/
  Cand : List (Stratum 0 (n + (m + 1)))
  hCandGood : ∀ S ∈ Cand, S.Good
  hCandFmt : ∀ S ∈ Cand, S.X.fmt ≤ E.Ac
  hCandDeg : ∀ S ∈ Cand, S.deg ≤ E.Dcand.eval D
  hCandDim : ∀ S ∈ Cand, n + (m + 1) - S.j ≤ K
  hCandRank : ∀ S ∈ Cand, ∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j
  hLdMem : ∀ (q : Fin PieceL.length) (S : Stratum 0 (n + (m + 1))), S ∈ Ld q → S ∈ Cand
  hLgMem : ∀ (q : Fin PieceL.length) (S : Stratum 0 (n + (m + 1))), S ∈ Lg q → S ∈ Cand
  hCutMem' : ∀ R ∈ Cut, R ∈ Cand
  hPieceLmem : ∀ T ∈ PieceL, ∃ p ∈ Pie, E2.swapStratum (p.2) = T
  hPieceLgood : ∀ T ∈ PieceL, T.Good
  hPieceLfmt : ∀ T ∈ PieceL, T.X.fmt ≤ E.Ap
  hPieceLdeg : ∀ T ∈ PieceL, T.deg ≤ E.Pp.eval D
  hPieceLrank : ∀ T ∈ PieceL, ∀ z ∈ T.X.set, projRank T z ≤ K
  hPieceLdim : ∀ T ∈ PieceL, n + (m + 1) - T.j ≤ K + 1
  Pv : List (Stratum 0 (n + (m + 1)))
  hPvMem : ∀ T ∈ Pv, T ∈ PieceL
  hPvDim : ∀ T ∈ Pv, n + (m + 1) - T.j = K + 1
  /-- Every vertical piece is a member of `Pv` (the converse of `hPvMem`/`hPvDim`; without it the
  `hW1`/`hV1` data of the vertical row is vacuous and the per-base-cell argument cannot handle the
  pieces of dimension `K+1`). -/
  hPvCompl : ∀ T ∈ PieceL, n + (m + 1) - T.j = K + 1 → T ∈ Pv
  /- the Σ- and E1-families and the composite family `SigAll` -/
  SigAll : List (SemiPf (n + pPair n m))
  hSigAllFmt : ∀ S ∈ SigAll, S.fmt ≤ E.Fz
  hSigAllND : ∀ S ∈ SigAll, NullDimLT (projFirst n (pPair n m) '' S.set) K
  Sig : List (SemiPf (n + pPair n m))
  hSigSub : ∀ Z ∈ Sig, Z ∈ SigAll
  hSigMem : ∀ Z ∈ Sig, Z.fmt ≤ E.Asum ∧ Z.deg ≤ E.Dcand.eval D ∧
    NullDimLT (projFirst n (pPair n m) '' Z.set) K
  hSigFront : ∀ T ∈ Cand, frontierSet n m T ⊆
    ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set
  hSigPair : ∀ T ∈ Cand, ∃ Wl : List (Stratum 0 (pPair n m)),
    (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet T).set) ∧
    ((absPairSet T).set = ⋃ W ∈ Wl, W.X.set) ∧
    (∀ W ∈ Wl, pPair n m - W.j < n + (m + 1) - T.j →
      pairSubBaseFst n m W ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set)
  /-- The `Σ`-coverage of the low-dimensional members of `Cand` (clause (2) of the `Σ`-box, at
  `Pi = Cand`).  It is what forces every *active* member of `Cand` to have dimension exactly `K`,
  which the vertical row needs. -/
  hSigLowCand : ∀ T ∈ Cand, n + (m + 1) - T.j < K →
    projFirst n (m + 1) '' absSet T ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set
  /-- The level-agreement pair decomposition for pairs of members of `Cand` (clause (6) of the
  `Σ`-box, at `Pi = Cand`), consumed by `gcase_sheets` for the level dichotomy of the active
  family. -/
  hSigLevCand : ∀ T ∈ Cand, ∀ T' ∈ Cand, ∃ Vl : List (Stratum 0 (pPair n m)),
    (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet T T').set) ∧
    ((absLevelPairSet T T').set = ⋃ V ∈ Vl, V.X.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - T.j →
      pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - T.j →
      pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set)
  Sig1 : List (SemiPf (n + pPair n m))
  hSig1Sub : ∀ Z ∈ Sig1, Z ∈ SigAll
  hSigLow : ∀ p ∈ Pie, n + (m + 1) - (E2.swapStratum (p.2)).j < K →
    projFirst n (m + 1) '' absSet (E2.swapStratum (p.2)) ⊆
      ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set
  hSloSub : ∀ (q : Fin PieceL.length) (r : Fin K), padP (SloR q r) ∈ SigAll
  hLySub : ∀ (q : Fin PieceL.length) (Z : SemiPf (n + (m + 1))), Z ∈ Ly q →
    padP Z ∈ SigAll
  hW1 : ∀ S ∈ Cand, ∀ T ∈ Pv, ∃ Wl : List (Stratum 0 (pPair n m)),
    (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet2 S T).set) ∧
    ((absPairSet2 S T).set = ⋃ W ∈ Wl, W.X.set) ∧
    (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - S.j →
      pairBase n m w ∈ ⋃ Z ∈ Sig1, projFirst n (pPair n m) '' Z.set)
  hV1 : ∀ S ∈ Cand, ∀ T ∈ Pv, ∃ Vl : List (Stratum 0 (pPair n m)),
    (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet S T).set) ∧
    ((absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
      pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig1, projFirst n (pPair n m) '' Z.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
      pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig1, projFirst n (pPair n m) '' Z.set)
  /- the fibre products inside `X'` -/
  hZidx : ∀ (p : Fin k × Stratum 0 ((n + 1) + m)), p ∈ Pie →
    ∀ S ∈ SigAll, ∃ i : Fin k',
      projFirst (n + 1) m₁ '' (X' i).set =
        projFirst (n + 1) m '' absSet p.2 ∩
          {y : Fin (n + 1) → ℝ | Fin.init y ∈ projFirst n (pPair n m) '' S.set} ∧
      NullDimLT (basePr n m₁ '' (X' i).set) K
  /- the correspondence of the `Y'`-family with the data -/
  hYcand : ∀ S ∈ Cand, ∃ j : Fin l',
    projFirst n m₂ '' (Y' j).set = projFirst n (m + 1) '' absSet S
  hYall : ∀ S ∈ SigAll, ∃ j : Fin l',
    projFirst n m₂ '' (Y' j).set = projFirst n (pPair n m) '' S.set
  hYslice1 : ∀ S ∈ Cand, ∃ j : Fin l',
    projFirst n m₂ '' (Y' j).set = projFirst n (m + 1) '' (E2.sliceSemiPf S 1).set
  hYslice2 : ∀ S ∈ Cand, ∃ j : Fin l',
    projFirst n m₂ '' (Y' j).set = projFirst n (m + 1) '' (E2.sliceSemiPf S (-1)).set
  hYpiece : ∀ p ∈ Pie, ∃ j : Fin l',
    projFirst n m₂ '' (Y' j).set = projFirst n (m + 1) '' absSet (E2.swapStratum (p.2))

end Work.WilE7.Endgame.Bv2
