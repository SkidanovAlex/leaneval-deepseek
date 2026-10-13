/-
  Area E7 / E2B, node `cellRefine_of_nodesB`, **the `Σ`-side of the package `E2Pkg`**.

  The file-size guard forces the construction of `E2Pkg` to be spread over several modules.  This
  one builds the pieces (`E2_pieces_of_family`), the candidate list and the rank/frontier data
  (`E2_rank_strata`, `E2_frontier_strata`), i.e. the fields of the intermediate structure
  `PiecePart`, which is the first half of `E2Pkg`.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.E2B.Data2

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

/-- The padding of the fibre dimension `m + 1` to the pair dimension `pPair n m`. -/
theorem pad_le_pPair (n m : ℕ) : n + (m + 1) ≤ n + pPair n m := by
  simp only [pPair]
  omega

/-- The pieces, the candidates, the vertical pieces and the rank/frontier data of the `E2Pkg`
package, with all the specifications that do not mention the `Σ`-family or the `X'`/`Y'`-families.
The fields are those of `E2Pkg` (in the same order), so that the final package is assembled by
copying them. -/
structure PiecePart {n K F : ℕ} (c : E2Const n K F) (D k m : ℕ)
    (X : Fin k → SemiPf ((n + 1) + m)) where
  Pie : List (Fin k × Stratum 0 ((n + 1) + m))
  Cut : List (Stratum 0 (n + (m + 1)))
  PieceList : List (Stratum 0 (n + (m + 1)))
  Ld : (q : Fin PieceList.length) → List (Stratum 0 (n + (m + 1)))
  Lg : (q : Fin PieceList.length) → List (Stratum 0 (n + (m + 1)))
  Ly : (q : Fin PieceList.length) → List (SemiPf (n + (m + 1)))
  SloR : (q : Fin PieceList.length) → Fin K → SemiPf (n + (m + 1))
  Cand : List (Stratum 0 (n + (m + 1)))
  Pv : List (Stratum 0 (n + (m + 1)))
  /- the correspondence between the two piece lists: `PieceList = Pie.map (fun p => E2.swapStratum
  p.2)` in the construction (`E2.swapStratum` keeps the `π_{n+1}`-image, `E2.swapStratum_projTop`).
  It is what lets the `G`-case apply the `PieceList`-indexed data (`Ld`, `Lg`, `Ly`, `SloR`, `Pv`,
  the sheets of the candidates) to a given `π_{n+1}`-cut piece of `Pie`. -/
  hPieceLlen : PieceList.length = Pie.length
  hPieceLget : ∀ p ∈ Pie, ∃ q : Fin PieceList.length, PieceList.get q = E2.swapStratum p.2
  hPieceLmem : ∀ T ∈ PieceList, ∃ p ∈ Pie, E2.swapStratum p.2 = T
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
  /- the sharp form of `specCandLen`, used to fit the `X'`/`Y'`-families into `Nl` -/
  specCandLenS : Cand.length ≤ MvPolynomial.eval ![D, k] c.Np * c.Pr.eval (c.Pp.eval D)
    + MvPolynomial.eval ![D, k] c.Np * c.Pf.eval (c.Pp.eval D)
    + MvPolynomial.eval ![D, k] c.Np
  specPv : ∀ T ∈ Pv, T ∈ PieceList ∧ n + (m + 1) - T.j = K + 1
  specPvAll : ∀ T ∈ PieceList, n + (m + 1) - T.j = K + 1 → T ∈ Pv
  specPvLen : Pv.length ≤ MvPolynomial.eval ![D, k] c.Np
  /- the members of the piece list are `Good` strata of the outer pieces -/
  specPL : ∀ T ∈ PieceList, T.Good ∧ T.X.fmt ≤ c.Ap ∧ T.deg ≤ c.Pp.eval D ∧
    n + (m + 1) - T.j ≤ K + 1 ∧ (∀ z ∈ T.X.set, projRank T z ≤ K)

theorem e2bPiecePart (hFC : Work.WilE7.CoreLTSuccPlan.HypFC) (hE2 : Work.WilE7.CoreLTSuccPlan.HypE2)
    (hE5 : Work.WilE7.CoreLTSuccPlan.HypE5) (hE6 : Work.WilE7.CoreLTSuccPlan.HypE6)
    (h0 : Work.WilE7.CoreLTSuccPlan.FrontierRestrat) (h1 : Work.WilE7.CoreLTSuccPlan.SigmaVPairs)
    (n K F : ℕ) (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m))
    (hX : ∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D)
    (hND : ∀ i, Work.WilE7.MainDesign.NullDimLT
      (Work.WilE7.MainDesign.basePr n m '' (X i).set) (K + 1))
    (hk : 0 < k) :
    ∃ P : PiecePart (e2bConst hFC hE2 hE5 hE6 h0 h1 n K F) D k m X, True := by
  classical
  set c : E2Const n K F := e2bConst hFC hE2 hE5 hE6 h0 h1 n K F with hc
  -- ## §0  the producers
  let Ap : ℕ := (E2_pieces_of_family hFC hE5 F).choose
  let Pp : Polynomial ℕ := (E2_pieces_of_family hFC hE5 F).choose_spec.choose
  let Np : MvPolynomial (Fin 2) ℕ :=
    (E2_pieces_of_family hFC hE5 F).choose_spec.choose_spec.choose
  have hPieces := (E2_pieces_of_family hFC hE5 F).choose_spec.choose_spec.choose_spec
  let Ar : ℕ := (E2_rank_strata hE5 Ap).choose
  let Pr : Polynomial ℕ := (E2_rank_strata hE5 Ap).choose_spec.choose
  have hRankData := (E2_rank_strata hE5 Ap).choose_spec.choose_spec
  let Af : ℕ := (E2_frontier_strata h0 Ap).choose
  let Pf : Polynomial ℕ := (E2_frontier_strata h0 Ap).choose_spec.choose
  have hFrontData := (E2_frontier_strata h0 Ap).choose_spec.choose_spec
  let Ac : ℕ := Ap + Ar + Af
  let Dq : Polynomial ℕ := Pp + Pr.comp Pp + Pf.comp Pp + 1
  have hDq_l : ∀ D : ℕ, Dq.eval D = Pp.eval D + Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 1 := by
    intro D
    simp only [show Dq = Pp + Pr.comp Pp + Pf.comp Pp + 1 from rfl, Polynomial.eval_add,
      Polynomial.eval_comp, Polynomial.eval_one]
  -- the fibre dimension is bounded by the outer format bound
  have hmF : m ≤ F := by
    have h := (hX ⟨0, hk⟩).1
    simp only [WilkiesDesign.E.SemiPf.fmt] at h
    omega
  -- ## §1  the pieces of the `π_{n+1}`-cut and of the `π_n`-cut
  obtain ⟨Pie, _Pie', Cut, hPielen, _hPie'len, hCutlen, hPiemem, hPiecov, _hPie'eq, hPie'mem,
    hCutmem, hCutcov⟩ := hPieces D k n m K X hX hND
  let PieceList : List (Stratum 0 (n + (m + 1))) := Pie.map (fun p => E2.swapStratum p.2)
  have hPLmem : ∀ T ∈ PieceList, T.Good ∧ T.X.fmt ≤ Ap ∧ T.deg ≤ Pp.eval D ∧
      n + (m + 1) - T.j ≤ K + 1 ∧ (∀ z ∈ T.X.set, projRank T z ≤ K) ∧
      (∀ z ∈ T.X.set, Module.finrank ℝ
        ↥(Submodule.map ((projTopLin n m).comp (absPtLin (n + (m + 1)))) (jac T z).ker)
        = n + (m + 1) - T.j) ∧
      (∃ i : Fin k, projTop n m '' absSet T ⊆ projFirst (n + 1) m '' (X i).set) := by
    intro T hT
    dsimp only [PieceList] at hT
    rw [List.mem_map] at hT
    obtain ⟨p, hp, rfl⟩ := hT
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hPie'mem p hp
    exact ⟨h1, h2, h3, h4, h5, h6, ⟨p.1, h7⟩⟩
  have hPLgood : ∀ T ∈ PieceList, T.Good := fun T hT => (hPLmem T hT).1
  have hPLfmt : ∀ T ∈ PieceList, T.X.fmt ≤ Ap := fun T hT => (hPLmem T hT).2.1
  have hPLdeg : ∀ T ∈ PieceList, T.deg ≤ Pp.eval D := fun T hT => (hPLmem T hT).2.2.1
  have hPLdim : ∀ T ∈ PieceList, n + (m + 1) - T.j ≤ K + 1 :=
    fun T hT => (hPLmem T hT).2.2.2.1
  have hPLrank : ∀ T ∈ PieceList, ∀ z ∈ T.X.set, projRank T z ≤ K :=
    fun T hT => (hPLmem T hT).2.2.2.2.1
  have hPLlen : PieceList.length ≤ MvPolynomial.eval ![D, k] Np := by
    dsimp only [PieceList]
    rw [List.length_map]
    exact hPielen
  -- ## §1b  the rank and frontier data
  obtain ⟨Ld, SloR, hLd, hLdcov, hSlo⟩ :=
    hRankData (Pp.eval D) K n m PieceList hPLgood hPLfmt hPLdeg hPLrank
  obtain ⟨Lg, Ly, hFront⟩ :=
    hFrontData (Pp.eval D) K n m PieceList hPLgood hPLfmt hPLdeg hPLdim
  have hLdlen : ∀ q : Fin PieceList.length, (Ld q).length ≤ Pr.eval (Pp.eval D) :=
    fun q => (hLd q).1
  have hLdmem : ∀ (q : Fin PieceList.length) (S : Stratum 0 (n + (m + 1))), S ∈ Ld q →
      S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ Ar ∧ S.deg ≤ Pr.eval (Pp.eval D) ∧
      n + (m + 1) - S.j ≤ K ∧ (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
      S.X.set ⊆ (PieceList.get q).X.set ∧
      S.X.set ⊆ {z | projRank (PieceList.get q) z = n + (m + 1) - (PieceList.get q).j} :=
    fun q S hS => (hLd q).2 S hS
  have hLglen : ∀ q : Fin PieceList.length, (Lg q).length ≤ Pf.eval (Pp.eval D) :=
    fun q => (hFront q).1
  have hLylen : ∀ q : Fin PieceList.length, (Ly q).length ≤ Pf.eval (Pp.eval D) :=
    fun q => (hFront q).2.1
  have hLgmem : ∀ (q : Fin PieceList.length) (S : Stratum 0 (n + (m + 1))), S ∈ Lg q →
      S.Good ∧ S.X.set.Nonempty ∧ S.X.fmt ≤ Af ∧ S.deg ≤ Pf.eval (Pp.eval D) ∧
      n + (m + 1) - S.j ≤ K ∧ (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) ∧
      S.X.set ⊆ closure (PieceList.get q).X.set \ (PieceList.get q).X.set :=
    fun q S hS => (hFront q).2.2.1 S hS
  have hLymem : ∀ (q : Fin PieceList.length) (Z : SemiPf (n + (m + 1))), Z ∈ Ly q →
      Z.fmt ≤ Af ∧ Z.deg ≤ Pf.eval (Pp.eval D) ∧
      NullDimLT (projFirst n (m + 1) '' Z.set) K :=
    fun q Z hZ => (hFront q).2.2.2.1 Z hZ
  have hCutmem' : ∀ R ∈ Cut, R.Good ∧ R.X.fmt ≤ Ap ∧ R.deg ≤ Pp.eval D ∧
      (∀ z ∈ R.X.set, projRank R z = n + (m + 1) - R.j) ∧ n + (m + 1) - R.j ≤ K ∧
      (∃ i : Fin k, projFirst n (m + 1) '' absSet R ⊆ basePr n m '' (X i).set) := hCutmem
  -- ## §1c  the candidates
  let Cand : List (Stratum 0 (n + (m + 1))) :=
    (List.ofFn Ld).flatten ++ (List.ofFn Lg).flatten ++ Cut
  have hCandmem : ∀ S ∈ Cand, S.Good ∧ S.X.fmt ≤ Ac ∧ S.deg ≤ Dq.eval D ∧
      n + (m + 1) - S.j ≤ K ∧ (∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j) := by
    intro S hS
    dsimp only [Cand] at hS
    rw [List.mem_append, List.mem_append] at hS
    rcases hS with (hS | hS) | hS
    · rw [List.mem_flatten] at hS
      obtain ⟨L, hL, hSL⟩ := hS
      rw [List.mem_ofFn] at hL
      obtain ⟨q, rfl⟩ := hL
      obtain ⟨hg, _hne, hfmt, hdeg, hdim, hrank, _hsub, _hsub2⟩ := hLdmem q S hSL
      exact ⟨hg, le_trans hfmt (by simp only [Ac]; omega),
        le_trans hdeg (by rw [hDq_l D]; omega), hdim, hrank⟩
    · rw [List.mem_flatten] at hS
      obtain ⟨L, hL, hSL⟩ := hS
      rw [List.mem_ofFn] at hL
      obtain ⟨q, rfl⟩ := hL
      obtain ⟨hg, _hne, hfmt, hdeg, hdim, hrank, _hsub⟩ := hLgmem q S hSL
      exact ⟨hg, le_trans hfmt (by simp only [Ac]; omega),
        le_trans hdeg (by rw [hDq_l D]; omega), hdim, hrank⟩
    · obtain ⟨hg, hfmt, hdeg, hRank, hDim, _⟩ := hCutmem' S hS
      exact ⟨hg, le_trans hfmt (by simp only [Ac]; omega),
        le_trans hdeg (by rw [hDq_l D]; omega), hDim, hRank⟩
  have hCandLd : ∀ (q : Fin PieceList.length)
      (S : Stratum 0 (n + (m + 1))), S ∈ Ld q → S ∈ Cand := by
    intro q S hS
    dsimp only [Cand]
    rw [List.mem_append, List.mem_append]
    left; left
    exact List.mem_flatten.mpr ⟨Ld q, List.mem_ofFn.mpr ⟨q, rfl⟩, hS⟩
  have hCandLg : ∀ (q : Fin PieceList.length)
      (S : Stratum 0 (n + (m + 1))), S ∈ Lg q → S ∈ Cand := by
    intro q S hS
    dsimp only [Cand]
    rw [List.mem_append, List.mem_append]
    left; right
    exact List.mem_flatten.mpr ⟨Lg q, List.mem_ofFn.mpr ⟨q, rfl⟩, hS⟩
  have hCandCut : ∀ S ∈ Cut, S ∈ Cand := by
    intro S hS
    dsimp only [Cand]
    rw [List.mem_append, List.mem_append]
    right
    exact hS
  -- ## §1d  the vertical pieces
  let Pv : List (Stratum 0 (n + (m + 1))) :=
    PieceList.filter (fun T => decide (n + (m + 1) - T.j = K + 1))
  have hPvmem : ∀ T ∈ Pv, T ∈ PieceList ∧ n + (m + 1) - T.j = K + 1 := by
    intro T hT
    dsimp only [Pv] at hT
    rw [List.mem_filter] at hT
    exact ⟨hT.1, of_decide_eq_true hT.2⟩
  have hPvAll : ∀ T ∈ PieceList, n + (m + 1) - T.j = K + 1 → T ∈ Pv := by
    intro T hT hj
    dsimp only [Pv]
    rw [List.mem_filter]
    exact ⟨hT, by simp [hj]⟩
  -- ## §1e  the length arithmetic
  have hCandLenS : Cand.length ≤ MvPolynomial.eval ![D, k] Np * Pr.eval (Pp.eval D)
      + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D) + MvPolynomial.eval ![D, k] Np := by
    have hLdFlat : (List.ofFn Ld).flatten.length ≤ PieceList.length * Pr.eval (Pp.eval D) := by
      have h := length_flatten_le (List.ofFn Ld) (Pr.eval (Pp.eval D)) (fun x hx => by
        rw [List.mem_ofFn] at hx
        obtain ⟨q, rfl⟩ := hx
        exact hLdlen q)
      simpa using h
    have hLgFlat : (List.ofFn Lg).flatten.length ≤ PieceList.length * Pf.eval (Pp.eval D) := by
      have h := length_flatten_le (List.ofFn Lg) (Pf.eval (Pp.eval D)) (fun x hx => by
        rw [List.mem_ofFn] at hx
        obtain ⟨q, rfl⟩ := hx
        exact hLglen q)
      simpa using h
    have h1 : PieceList.length * Pr.eval (Pp.eval D)
        ≤ MvPolynomial.eval ![D, k] Np * Pr.eval (Pp.eval D) := Nat.mul_le_mul_right _ hPLlen
    have h2 : PieceList.length * Pf.eval (Pp.eval D)
        ≤ MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D) := Nat.mul_le_mul_right _ hPLlen
    have h3 : Cand.length = (List.ofFn Ld).flatten.length + (List.ofFn Lg).flatten.length
        + Cut.length := by
      simp only [Cand, List.length_append]
    have h4 : Cut.length ≤ MvPolynomial.eval ![D, k] Np := hCutlen
    omega
  have hCandLenB : Cand.length ≤ MvPolynomial.eval ![D, k] Np *
      (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2) := by
    have h : MvPolynomial.eval ![D, k] Np * (Pr.eval (Pp.eval D) + Pf.eval (Pp.eval D) + 2)
        = MvPolynomial.eval ![D, k] Np * Pr.eval (Pp.eval D)
          + MvPolynomial.eval ![D, k] Np * Pf.eval (Pp.eval D)
          + 2 * MvPolynomial.eval ![D, k] Np := by ring
    rw [h]
    omega
  -- ## §2  the part
  exact ⟨{ Pie := Pie, Cut := Cut, PieceList := PieceList, Ld := Ld, Lg := Lg, Ly := Ly,
            SloR := SloR, Cand := Cand, Pv := Pv,
            hPieceLlen := by dsimp only [PieceList]; rw [List.length_map],
            hPieceLget := by
              intro p hp
              exact List.mem_iff_get.mp (by
                dsimp only [PieceList]
                exact List.mem_map.mpr ⟨p, hp, rfl⟩),
            hPieceLmem := by
              intro T hT
              dsimp only [PieceList] at hT
              obtain ⟨p, hp, hpt⟩ := List.mem_map.mp hT
              exact ⟨p, hp, hpt⟩,
            specPieces := ⟨hPielen, hCutlen, hPiemem, hPiecov, hPie'mem, hCutmem, hCutcov⟩,
            specLd := hLd, specLdcov := hLdcov, specSloR := hSlo,
            specLg := fun q => ⟨(hFront q).1, (hFront q).2.2.1⟩,
            specLy := fun q => ⟨(hFront q).2.1, (hFront q).2.2.2.1, (hFront q).2.2.2.2⟩,
            specCand := hCandmem, specCandLd := hCandLd, specCandLg := hCandLg,
            specCandCut := hCandCut, specPieceLen := hPLlen, specCandLen := hCandLenB,
            specCandLenS := hCandLenS,
            specPv := hPvmem, specPvAll := hPvAll,
            specPvLen := le_trans (List.length_filter_le _ _) hPLlen,
            specPL := fun T hT => ⟨hPLgood T hT, hPLfmt T hT, hPLdeg T hT, hPLdim T hT,
              hPLrank T hT⟩ }, trivial⟩

end

end Work.WilE7.Endgame.E2B
