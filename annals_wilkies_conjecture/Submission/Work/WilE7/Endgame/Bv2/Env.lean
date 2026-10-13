/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S** (module `Work.WilE7.Endgame.Bv2.Env`).

  `E2Env` bundles all the constants produced by the node assembly (`hFC`, `hE5`, `h0`, `hE2`, and
  the Σ/E1 boxes) together with their specifications, so that the modules that build the produced
  families and work over a base cell can take a *single* argument.

  The constants live before `(Fq, Qq)`, which is why the `Fq`-dependent ones (`Fbig`, `Ag'`,
  `Cbg'`, `AB`, `CB`) are in `Bv2.Data`'s `E2Env2`.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.Bv2.Defs

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

/-- All the constants of the `cellRefine_of_nodesBv2` endgame that are fixed before `(Fq, Qq)`,
with the specifications of the nodes that produced them. -/
structure E2Env (hFC : HypFC) (hE2 : HypE2) (hE5 : HypE5) (hE6 : HypE6) (h0 : FrontierRestrat)
    (h1 : SigmaVPairs) (hV : GCaseVertical) (n K F : ℕ) where
  Ap : ℕ
  Pp : Polynomial ℕ
  Np : MvPolynomial (Fin 2) ℕ
  Ar : ℕ
  Pr : Polynomial ℕ
  Af : ℕ
  Pf : Polynomial ℕ
  Ps : Polynomial ℕ
  As : ℕ
  Ac : ℕ
  Fp : ℕ
  Qsum : MvPolynomial (Fin 2) ℕ
  Asum : ℕ
  Bsum : Polynomial ℕ
  Q1sum : MvPolynomial (Fin 3) ℕ
  A1sum : ℕ
  B1sum : Polynomial ℕ
  Dq : Polynomial ℕ
  Dcand : Polynomial ℕ
  Psc : Polynomial ℕ
  PX : Polynomial ℕ
  Bz : Polynomial ℕ
  P : Polynomial ℕ
  SC : ℕ
  Fz : ℕ
  Az : ℕ
  F' : ℕ
  Nk : MvPolynomial (Fin 3) ℕ
  Nl : MvPolynomial (Fin 3) ℕ
  Ng : MvPolynomial (Fin 3) ℕ
  /- the defining equations -/
  hAc : Ac = Ap + Ar + Af
  hFp : Fp = 2 * Ac + 1
  hDqdef : Dq = DqOf Pp Pr Pf
  hDq : ∀ D : ℕ, Dq.eval D
    = Pp.eval D + Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + D
  hDcand : ∀ D : ℕ, Dcand.eval D
    = Dq.eval D + 3 * Dq.eval D + 2 + Bsum.eval (Dq.eval D) + B1sum.eval (Dq.eval D)
  hPsc : ∀ D : ℕ, Ps.eval (Dcand.eval D) ≤ Psc.eval D
  hPX : ∀ D : ℕ, Bz.eval (Pp.eval D + Dcand.eval D) ≤ PX.eval D
  hPeval : ∀ D : ℕ, P.eval D = Dcand.eval D + Psc.eval D + PX.eval D + D
  hSC : SC = Ac + Asum + A1sum + Ar + Af + F + pPair n F + n + 2
  hFz : Fz = 2 * SC
  hAzF' : Az ≤ F'
  hSCF' : 2 * SC + 16 ≤ F'
  /- the format budget of the *padding* to a common fibre dimension `≤ SC`: the fibre dimension
  `M2` contributes `M2 ≤ SC` and the padded set keeps its `r`, which is at most `Fz = 2 * SC`. -/
  hF'pad : 4 * SC + 4 ≤ F'
  hNk : ∀ D k l : ℕ, NkL Qsum Q1sum Np Dq Dcand K D k ≤ MvPolynomial.eval ![D, k, l] Nk
  hNl : ∀ D k l : ℕ, BlkL Qsum Q1sum Np Dq Dcand K D k + l ≤ MvPolynomial.eval ![D, k, l] Nl
  hNg : ∀ D k l : ℕ, NgL Psc Np Dcand D k ≤ MvPolynomial.eval ![D, k, l] Ng
  /- the producers -/
  hPieces : ∀ (D k N m K' : ℕ) (X : Fin k → SemiPf ((N + 1) + m)),
    (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
    (∀ i, NullDimLT (basePr N m '' (X i).set) (K' + 1)) →
    ∃ (Pie : List (Fin k × Stratum 0 ((N + 1) + m)))
      (Pie' : List (Fin k × Stratum 0 (N + (m + 1))))
      (Cut : List (Stratum 0 (N + (m + 1)))),
      Pie.length ≤ MvPolynomial.eval ![D, k] Np ∧
      Pie'.length ≤ MvPolynomial.eval ![D, k] Np ∧
      Cut.length ≤ MvPolynomial.eval ![D, k] Np ∧
      (∀ p ∈ Pie, (p.2).Good ∧ (p.2).X.fmt ≤ Ap ∧ (p.2).deg ≤ Pp.eval D ∧
        (∀ x : Fin (N + 1) → ℝ, (fiber (absSet (p.2)) x).Finite) ∧
        (∀ z ∈ (p.2).X.set, projRank (p.2) z = (N + 1) + m - (p.2).j) ∧
        projFirst (N + 1) m '' absSet (p.2) ⊆ projFirst (N + 1) m '' (X p.1).set) ∧
      (∀ i : Fin k, projFirst (N + 1) m '' (X i).set =
        ⋃ p ∈ Pie.filter (fun p => p.1 = i), projFirst (N + 1) m '' absSet (p.2)) ∧
      Pie' = Pie.map (fun p => (p.1, E2.swapStratum p.2)) ∧
      (∀ p ∈ Pie, (E2.swapStratum (p.2)).Good ∧ (E2.swapStratum (p.2)).X.fmt ≤ Ap ∧
        (E2.swapStratum (p.2)).deg ≤ Pp.eval D ∧
        N + (m + 1) - (E2.swapStratum (p.2)).j ≤ K' + 1 ∧
        (∀ z ∈ (E2.swapStratum (p.2)).X.set, projRank (E2.swapStratum (p.2)) z ≤ K') ∧
        (∀ z ∈ (E2.swapStratum (p.2)).X.set, Module.finrank ℝ
          ↥(Submodule.map ((projTopLin N m).comp (absPtLin (N + (m + 1))))
            (jac (E2.swapStratum (p.2)) z).ker) = N + (m + 1) - (E2.swapStratum (p.2)).j) ∧
        projTop N m '' absSet (E2.swapStratum (p.2)) ⊆ projFirst (N + 1) m '' (X p.1).set) ∧
      (∀ R ∈ Cut, R.Good ∧ R.X.fmt ≤ Ap ∧ R.deg ≤ Pp.eval D ∧
        (∀ z ∈ R.X.set, projRank R z = N + (m + 1) - R.j) ∧
        N + (m + 1) - R.j ≤ K' ∧
        (∃ i : Fin k, projFirst N (m + 1) '' absSet R ⊆ basePr N m '' (X i).set)) ∧
      ((⋃ i : Fin k, basePr N m '' (X i).set) =
        ⋃ R ∈ Cut, projFirst N (m + 1) '' absSet R)
  hRank : ∀ (D K' N m : ℕ) (Pie : List (Stratum 0 (N + (m + 1)))),
    (∀ T ∈ Pie, T.Good) → (∀ T ∈ Pie, T.X.fmt ≤ Ap) → (∀ T ∈ Pie, T.deg ≤ D) →
    (∀ T ∈ Pie, ∀ z ∈ T.X.set, projRank T z ≤ K') →
    ∃ (Ld : (Fin Pie.length) → List (Stratum 0 (N + (m + 1))))
      (SloR : (Fin Pie.length) → Fin K' → SemiPf (N + (m + 1))),
      (∀ p : Fin Pie.length, (Ld p).length ≤ Pr.eval D ∧
        (∀ S ∈ Ld p, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ Ar ∧ S.deg ≤ Pr.eval D ∧
          N + (m + 1) - S.j ≤ K' ∧
          (∀ z ∈ S.X.set, projRank S z = N + (m + 1) - S.j) ∧
          S.X.set ⊆ (Pie.get p).X.set ∧
          S.X.set ⊆ {z | projRank (Pie.get p) z = N + (m + 1) - (Pie.get p).j})) ∧
      (∀ p : Fin Pie.length,
        {z | z ∈ (Pie.get p).X.set ∧ projRank (Pie.get p) z = N + (m + 1) - (Pie.get p).j}
          = ⋃ S ∈ Ld p, S.X.set) ∧
      (∀ (p : Fin Pie.length) (r : Fin K'), (SloR p r).fmt ≤ Ar ∧
        (SloR p r).deg ≤ Pr.eval D ∧
        (SloR p r).set = absPt '' {z | z ∈ (Pie.get p).X.set ∧
          projRank (Pie.get p) z = (r : ℕ)} ∧
        NullDimLT (projFirst N (m + 1) '' (SloR p r).set) K')
  hFront : ∀ (D K' N m : ℕ) (Pie : List (Stratum 0 (N + (m + 1)))),
    (∀ T ∈ Pie, T.Good) → (∀ T ∈ Pie, T.X.fmt ≤ Ap) → (∀ T ∈ Pie, T.deg ≤ D) →
    (∀ T ∈ Pie, N + (m + 1) - T.j ≤ K' + 1) →
    ∃ (Lg : (Fin Pie.length) → List (Stratum 0 (N + (m + 1))))
      (Ly : (Fin Pie.length) → List (SemiPf (N + (m + 1)))),
      (∀ p : Fin Pie.length, (Lg p).length ≤ Pf.eval D ∧ (Ly p).length ≤ Pf.eval D ∧
        (∀ S ∈ Lg p, S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ Af ∧ S.deg ≤ Pf.eval D ∧
          N + (m + 1) - S.j ≤ K' ∧
          (∀ z ∈ S.X.set, projRank S z = N + (m + 1) - S.j) ∧
          S.X.set ⊆ closure (Pie.get p).X.set \ (Pie.get p).X.set) ∧
        (∀ Y ∈ Ly p, Y.fmt ≤ Af ∧ Y.deg ≤ Pf.eval D ∧
          NullDimLT (projFirst N (m + 1) '' Y.set) K') ∧
        closure (absSet (Pie.get p)) \ absSet (Pie.get p) ⊆
          (⋃ S ∈ Lg p, absSet S) ∪ ⋃ Y ∈ Ly p, Y.set)
  hSheet : ∀ (N m K' D : ℕ) (S : Stratum 0 (N + (m + 1))) (b : Set (Fin N → ℝ))
      (Sig : List (SemiPf (N + pPair N m))) (Wl : List (Stratum 0 (pPair N m))),
    S.Good → S.X.fmt ≤ Ac → S.deg ≤ D →
    (∀ z ∈ S.X.set, projRank S z = N + (m + 1) - S.j) →
    IsCell N b → b.Nonempty → b ⊆ projFirst N (m + 1) '' absSet S →
    (∀ Z ∈ Sig, Disjoint b (projFirst N (pPair N m) '' Z.set)) →
    frontierSet N m S ⊆ ⋃ Z ∈ Sig, projFirst N (pPair N m) '' Z.set →
    (∀ W ∈ Wl, W.Good) → (∀ W ∈ Wl, W.X.set ⊆ (absPairSet S).set) →
    ((absPairSet S).set = ⋃ W ∈ Wl, W.X.set) →
    (∀ W ∈ Wl, pPair N m - W.j < N + (m + 1) - S.j →
      pairSubBaseFst N m W ⊆ ⋃ Z ∈ Sig, projFirst N (pPair N m) '' Z.set) →
    ∃ (k : ℕ) (s : Fin k → (Fin N → ℝ) → (Fin (m + 1) → ℝ)),
      0 < k ∧ (∀ j, ContinuousOn (s j) b) ∧
      (∀ x ∈ b, Function.Injective fun j : Fin k => s j x) ∧
      (∀ (j : Fin k) (x : Fin N → ℝ), x ∈ b → Fin.append x (s j x) ∈ absSet S) ∧
      (∀ x ∈ b, (fiber (absSet S) x).ncard = k) ∧
      (∀ z ∈ absSet S, projFirst N (m + 1) z ∈ b →
        ∃ j : Fin k, s j (projFirst N (m + 1) z) = projSnd N (m + 1) z) ∧
      k ≤ Ps.eval D
  hSigBox : ∀ (m₀ : ℕ), m₀ ≤ F → ∀ (D : ℕ) (Pi : List (Stratum 0 (n + (m₀ + 1)))),
    (∀ T ∈ Pi, T.Good) → (∀ T ∈ Pi, T.X.fmt ≤ Fp) → (∀ T ∈ Pi, T.deg ≤ D) →
    (∀ T ∈ Pi, n + (m₀ + 1) - T.j ≤ K) →
    (∀ T ∈ Pi, (absPairSet T).fmt ≤ Fp) →
    (∀ T ∈ Pi, ∀ T' ∈ Pi, (absLevelPairSet T T').fmt ≤ Fp) →
    ∃ Sig : List (SemiPf (n + pPair n m₀)),
      Sig.length ≤ MvPolynomial.eval ![D, Pi.length] Qsum ∧
      (∀ Z ∈ Sig, Z.fmt ≤ Asum ∧ Z.deg ≤ Bsum.eval D ∧
        NullDimLT (projFirst n (pPair n m₀) '' Z.set) K) ∧
      (∀ T ∈ Pi, n + (m₀ + 1) - T.j < K →
        projFirst n (m₀ + 1) '' absSet T ⊆
          ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set) ∧
      (∀ T ∈ Pi, frontierSet n m₀ T ⊆
        ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set) ∧
      (∀ T ∈ Pi, ∃ Wl : List (Stratum 0 (pPair n m₀)),
        (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet T).set) ∧
        ((absPairSet T).set = ⋃ W ∈ Wl, W.X.set) ∧
        (∀ W ∈ Wl, pPair n m₀ - W.j < n + (m₀ + 1) - T.j →
          pairSubBaseFst n m₀ W ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set)) ∧
      (∀ T ∈ Pi, ∀ T' ∈ Pi, ∃ Vl : List (Stratum 0 (pPair n m₀)),
        (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet T T').set) ∧
        ((absLevelPairSet T T').set = ⋃ V ∈ Vl, V.X.set) ∧
        (∀ V ∈ Vl, pPair n m₀ - V.j < n + (m₀ + 1) - T.j →
          pairSubBaseFst n m₀ V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set) ∧
        (∀ V ∈ Vl, pPair n m₀ - V.j = n + (m₀ + 1) - T.j →
          pairFrontierBaseFst n m₀ V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set))
  hVBox : ∀ (m₀ : ℕ), m₀ ≤ F → ∀ (D : ℕ) (Pi Pv : List (Stratum 0 (n + (m₀ + 1)))),
    (∀ T ∈ Pi ++ Pv, T.Good ∧ T.X.fmt ≤ Fp ∧ T.deg ≤ D) →
    (∀ S ∈ Pi, n + (m₀ + 1) - S.j ≤ K) →
    (∀ S ∈ Pi, ∀ T ∈ Pv, (absLevelPairSet S T).fmt ≤ Fp ∧ (absPairSet2 S T).fmt ≤ Fp) →
    ∃ Sig : List (SemiPf (n + pPair n m₀)),
      Sig.length ≤ MvPolynomial.eval ![D, Pi.length, Pv.length] Q1sum ∧
      (∀ Z ∈ Sig, Z.fmt ≤ A1sum ∧ Z.deg ≤ B1sum.eval D ∧
        NullDimLT (projFirst n (pPair n m₀) '' Z.set) K) ∧
      (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Vl : List (Stratum 0 (pPair n m₀)),
        (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet S T).set) ∧
        ((absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set) ∧
        (∀ V ∈ Vl, pPair n m₀ - V.j < n + (m₀ + 1) - S.j →
          pairSubBaseFst n m₀ V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set) ∧
        (∀ V ∈ Vl, pPair n m₀ - V.j = n + (m₀ + 1) - S.j →
          pairFrontierBaseFst n m₀ V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set)) ∧
      (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Wl : List (Stratum 0 (pPair n m₀)),
        (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet2 S T).set) ∧
        ((absPairSet2 S T).set = ⋃ W ∈ Wl, W.X.set) ∧
        (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m₀ + 1) - S.j →
          pairBase n m₀ w ∈ ⋃ Z ∈ Sig, projFirst n (pPair n m₀) '' Z.set))
  /- derived consequences, kept here so that the downstream modules do not recompute them -/
  hP_D : ∀ D : ℕ, D ≤ P.eval D
  hP_Dcand : ∀ D : ℕ, Dcand.eval D ≤ P.eval D
  hP_Psc : ∀ D : ℕ, Psc.eval D ≤ P.eval D
  hDq_Dcand : ∀ D : ℕ, Dq.eval D ≤ Dcand.eval D
  hD_Dcand : ∀ D : ℕ, D ≤ Dcand.eval D
  hPp_Dcand : ∀ D : ℕ, Pp.eval D ≤ Dcand.eval D
  hPr_Dcand : ∀ D : ℕ, Pr.eval (Pp.eval D) ≤ Dcand.eval D
  hPf_Dcand : ∀ D : ℕ, Pf.eval (Pp.eval D) ≤ Dcand.eval D
  hApAc : Ap ≤ Ac
  hArAc : Ar ≤ Ac
  hAfAc : Af ≤ Ac
  hAcSC : Ac ≤ SC
  hFSC : F ≤ SC
  hpPairSC : pPair n F ≤ SC
  hAcFz : Ac ≤ Fz
  hApFz : Ap ≤ Fz
  hAsumFz : Asum ≤ Fz
  hA1sumFz : A1sum ≤ Fz
  hArFz : Ar ≤ Fz
  hAfFz : Af ≤ Fz
  hFpAc : Ac ≤ Fp
  hSCFz : SC ≤ Fz
  hZspec : ∀ (N M s K' : ℕ) (T : Stratum 0 ((N + 1) + M)) (S : SemiPf (N + s)),
    T.X.fmt ≤ Fz → S.fmt ≤ Fz → NullDimLT (projFirst N s '' S.set) K' →
    ∃ Z : SemiPf ((N + 1) + (M + s)),
      Z.fmt ≤ Az ∧ Z.deg ≤ Bz.eval (T.deg + S.deg) ∧
      projFirst (N + 1) (M + s) '' Z.set =
        projFirst (N + 1) M '' absSet T ∩ {y | Fin.init y ∈ projFirst N s '' S.set} ∧
      NullDimLT (basePr N (M + s) '' Z.set) K'

end Work.WilE7.Endgame.Bv2
