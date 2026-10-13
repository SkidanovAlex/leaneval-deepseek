/-
  E1 of the `CoreLT_succ` plan (`Submission/Work/WilE7/CoreStep/CoreLTSuccNodes.lean`):
  `SigmaVPairs` — the Σ-clauses for the *level pairs* and *base pairs* of a piece `S` of the
  `π_n`-bounded family `Pi` (`dim S ≤ K`) with a *vertical* piece `T` of the family `Pv`
  (`dim T ≤ K + 1`).  A vertical piece cannot be put into `Pi` (its frontier has base dimension
  `K`), so the Σ-family of `Work.CoreStep.sigmaFamily_len` — which only covers pairs inside `Pi` —
  has to be extended by the pairs `(S,T)` with `S ∈ Pi`, `T ∈ Pv`.

  The work is split into the three nodes proved in this directory:

  * `pairRankSlice_data` (from `pairRankSemiPf` + `pairRankSlice_nullDimLE`) — the base-rank-`r`
    locus (`r < K`) of a `Good` stratum of the pair space is the `π_n`-projection of a Σ-member
    (Sard for the pair-space base projection);
  * `levelPairFamily` — for one pair `(S,T)`: the `hE5`-decomposition of the level-pair set
    `absLevelPairSet S T`, whose low strata (`dim V < dim S ≤ K`) enter Σ as `sigPair V` and whose
    top strata (`dim V = dim S`) contribute the `pairFrontierDecomp`-strata of their frontiers
    (`frontierDrop_abs`: `dim U < dim V ≤ K`);
  * `basePairFamily` — for one pair `(S,T)`: the `hE5`-decomposition of the base-pair set
    `absPairSet2 S T` together with the base-rank slices of its strata.

  This file is the *assembly*: it instantiates the three nodes over all pairs of the two lists,
  takes `Sig` to be the concatenation of the Σ-families of all the pairs, and reads off the length
  bound `|Pi| · |Pv| · (B₁ + B₂)(D)` from `length_flatMapLe`.  The base-rank data comes from the
  two nodes `pairRankSemiPf` (the slice `{pairBaseRank = r}` as a `SemiPf`, padded into
  `ℝ^{n + pPair n m}` by `pairRankSlice_data` below) and `pairRankSlice_nullDimLE` (Sard: the base
  projection of the rank-`≤ r` locus is `NullDimLE · r`); their combination is stated in the form
  consumed by `basePairFamily` as `pairRankSlice_data`.
-/
import Mathlib
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.CoreStep.SigmaFamDefs
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif_helpers
import Submission.Work.WilE7.Endgame.pairRankSemiPf
import Submission.Work.WilE7.Endgame.pairRankSlice_nullDimLE
import Submission.Work.WilE7.Endgame.levelPairFamily
import Submission.Work.WilE7.Endgame.basePairFamily

namespace Work.WilE7.Endgame

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreLTSuccPlan
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt)
open Work.CoreStep (pairBase sigPair pairSubBaseFst pairFrontierBaseFst)

/-! ## Helpers -/

/-- The `(S,T)`-pairs of two lists of pieces: `Pi × Pv`, with the membership proofs. -/
abbrev PiecePair (n m : ℕ) (Pi Pv : List (Stratum 0 (n + (m + 1)))) : Type :=
  {S : Stratum 0 (n + (m + 1)) // S ∈ Pi} × {T : Stratum 0 (n + (m + 1)) // T ∈ Pv}

/-- `MvPolynomial.eval` of the substitution of a univariate polynomial into the variable `X 0`
(three variables, the shape of the length polynomial `Q` of `SigmaVPairs`). -/
theorem mv_eval_aeval_X0_fin3 (f : Fin 3 → ℕ) (p : Polynomial ℕ) :
    MvPolynomial.eval f (Polynomial.aeval (MvPolynomial.X 0) p) = p.eval (f 0) := by
  have h := Polynomial.aeval_algHom_apply (MvPolynomial.aeval f) (MvPolynomial.X 0) p
  rw [MvPolynomial.aeval_X] at h
  exact h.symm

/-- The evaluation of the length polynomial `X 1 * X 2 * (B₁ + B₂)(X 0)` at
`![D, l₁, l₂]` is `l₁ * l₂ * ((B₁ + B₂).eval D)`. -/
theorem mv_eval_Q_fin3 (D l₁ l₂ : ℕ) (p : Polynomial ℕ) :
    MvPolynomial.eval ![D, l₁, l₂] (MvPolynomial.X 1 * MvPolynomial.X 2 *
      Polynomial.aeval (MvPolynomial.X 0) p) = l₁ * l₂ * p.eval D := by
  have h0 : (![D, l₁, l₂] : Fin 3 → ℕ) 0 = D := rfl
  have h1 : (![D, l₁, l₂] : Fin 3 → ℕ) 1 = l₁ := rfl
  have h2 : (![D, l₁, l₂] : Fin 3 → ℕ) 2 = l₂ := rfl
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, mv_eval_aeval_X0_fin3, h0, h1, h2]

/-- Monotonicity of a list-indexed union in the index list. -/
theorem list_iUnion_mono {α β : Type*} (f : α → Set β) {L₁ L₂ : List α}
    (h : ∀ a ∈ L₁, a ∈ L₂) : (⋃ a ∈ L₁, f a) ⊆ ⋃ a ∈ L₂, f a := by
  rintro x hx
  obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨a, h a ha, hx⟩

/-- `fstN n` (the first `n` coordinates) is the base projection `pairBase n m` of the pair
space: the two index maps differ only in their proof components. -/
theorem fstN_eq_pairBase {n m : ℕ} (h : n ≤ 0 + pPair n m) (w : Fin (0 + pPair n m) → ℝ) :
    Work.CoreStep.fstN n h w = pairBase n m w := by
  funext i
  exact congrArg w (Fin.ext rfl)

/-- **The Σ-member attached to a base-rank slice of a pair stratum.**  Combining the semi-Pfaffian
realisation of the rank-`r` slice (`Work.WilE7.Endgame.pairRankSemiPf`) with the Sard bound for the
rank-`≤ r` locus (`Work.WilE7.Endgame.pairRankSlice_nullDimLE`) and padding to `ℝ^{n + pPair n m}`
gives, for `r + 1 ≤ K`, a Σ-member whose `π_n`-projection covers the base projection of the
rank-`r` locus of `W`.  This is exactly the `hRank` hypothesis of
`Work.WilE7.Endgame.basePairFamily`. -/
theorem pairRankSlice_data (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m r K : ℕ) (W : Stratum 0 (pPair n m)),
        W.Good → W.X.fmt ≤ F → r + 1 ≤ K →
        ∃ Z : SemiPf (n + pPair n m),
          Z.fmt ≤ A ∧ Z.deg ≤ B.eval W.deg ∧
          NullDimLT (projFirst n (pPair n m) '' Z.set) K ∧
          pairBase n m '' {w : Fin (0 + pPair n m) → ℝ | w ∈ W.X.set ∧
            pairBaseRank W w = r} ⊆ projFirst n (pPair n m) '' Z.set := by
  obtain ⟨A₀, B₀, h₀⟩ := Work.WilE7.Endgame.pairRankSemiPf F
  refine ⟨F + A₀, B₀, fun n m r K W hW hfmt hr => ?_⟩
  obtain ⟨Y, hYset, hYfmt, hYdeg⟩ := h₀ n m r W hfmt
  have hM : 0 + pPair n m ≤ n + pPair n m := by omega
  have hnM : n ≤ 0 + pPair n m := by
    rw [Nat.zero_add]
    exact Work.CoreStep.le_pPair n m
  have hproj : projFirst n (pPair n m) '' (Work.WilE7.SemiPf.pad hM Y).set
      = pairBase n m '' Y.set := by
    rw [Work.CoreStep.pad_proj_fstN hM hnM Y,
      show Work.CoreStep.fstN n hnM = pairBase n m from funext (fstN_eq_pairBase hnM)]
  refine ⟨Work.WilE7.SemiPf.pad hM Y, ?_, ?_, ?_, ?_⟩
  · -- the format
    have hp : pPair n m + W.X.r ≤ F := by
      have h := hfmt
      simp only [SemiPf.fmt] at h
      omega
    have hn : n ≤ pPair n m := Work.CoreStep.le_pPair n m
    have hYr : pPair n m + Y.r ≤ A₀ := by
      have h := hYfmt
      simp only [SemiPf.fmt] at h
      omega
    show (n + pPair n m) + Y.r ≤ F + A₀
    omega
  · -- the degree
    exact le_trans (Work.WilE7.semipf_deg_pad_le hM Y) hYdeg
  · -- the measure
    rw [hproj]
    cases K with
    | zero => exact absurd hr (by omega)
    | succ K' =>
        have hle : r ≤ K' := by omega
        refine Work.WilE7.DimAPI.nullDimLE_mono_dim ?_ hle
        refine Work.WilE7.MainDesign.NullDimLE.mono
          (Work.WilE7.Endgame.pairRankSlice_nullDimLE W hW r) ?_
        rw [hYset]
        exact Set.image_mono (fun w hw => ⟨hw.1, le_of_eq hw.2⟩)
  · -- the covering
    rw [hproj, hYset]

/-! ## The assembly -/

theorem sigmaFamily_vpairs (hE5 : HypE5) (hE6 : HypE6) : SigmaVPairs := by
  classical
  intro n m K Fp
  obtain ⟨Alev, Blev, hLev⟩ := Work.WilE7.Endgame.levelPairFamily hE5 hE6 n m K Fp
  obtain ⟨ABase, BBase, hBase⟩ :=
    Work.WilE7.Endgame.basePairFamily pairRankSlice_data hE5 n m K Fp
  refine ⟨MvPolynomial.X 1 * MvPolynomial.X 2 *
    Polynomial.aeval (MvPolynomial.X 0) (Blev + BBase), max Alev ABase, Blev + BBase, ?_⟩
  intro D Pi Pv hPiece hPiK hPairFmt
  -- ## The hypotheses for the two families of pieces
  have hgoodPi : ∀ S ∈ Pi, S.Good := fun S hS =>
    (hPiece S (List.mem_append.mpr (Or.inl hS))).1
  have hfmtPi : ∀ S ∈ Pi, S.X.fmt ≤ Fp := fun S hS =>
    (hPiece S (List.mem_append.mpr (Or.inl hS))).2.1
  have hdegPi : ∀ S ∈ Pi, S.deg ≤ D := fun S hS =>
    (hPiece S (List.mem_append.mpr (Or.inl hS))).2.2
  have hgoodPv : ∀ T ∈ Pv, T.Good := fun T hT =>
    (hPiece T (List.mem_append.mpr (Or.inr hT))).1
  have hfmtPv : ∀ T ∈ Pv, T.X.fmt ≤ Fp := fun T hT =>
    (hPiece T (List.mem_append.mpr (Or.inr hT))).2.1
  have hdegPv : ∀ T ∈ Pv, T.deg ≤ D := fun T hT =>
    (hPiece T (List.mem_append.mpr (Or.inr hT))).2.2
  -- ## The per-pair data
  have hLevPair : ∀ p : PiecePair n m Pi Pv,
      ∃ (Sig : List (SemiPf (n + pPair n m))),
        Sig.length ≤ Blev.eval D ∧
        (∀ Z ∈ Sig, Z.fmt ≤ Alev ∧ Z.deg ≤ Blev.eval D ∧
          NullDimLT (projFirst n (pPair n m) '' Z.set) K) ∧
        ∃ (Vl : List (Stratum 0 (pPair n m))),
          (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet p.1.1 p.2.1).set) ∧
          (absLevelPairSet p.1.1 p.2.1).set = ⋃ V ∈ Vl, V.X.set ∧
          (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - p.1.1.j →
            pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
          (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - p.1.1.j →
            pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) :=
    fun p => hLev D p.1.1 p.2.1 (hgoodPi p.1.1 p.1.2) (hfmtPi p.1.1 p.1.2)
      (hdegPi p.1.1 p.1.2) (hPiK p.1.1 p.1.2) (hgoodPv p.2.1 p.2.2) (hfmtPv p.2.1 p.2.2)
      (hdegPv p.2.1 p.2.2) (hPairFmt p.1.1 p.1.2 p.2.1 p.2.2).1
  have hBasePair : ∀ p : PiecePair n m Pi Pv,
      ∃ (Sig : List (SemiPf (n + pPair n m))),
        Sig.length ≤ BBase.eval D ∧
        (∀ Z ∈ Sig, Z.fmt ≤ ABase ∧ Z.deg ≤ BBase.eval D ∧
          NullDimLT (projFirst n (pPair n m) '' Z.set) K) ∧
        ∃ (Wl : List (Stratum 0 (pPair n m))),
          (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet2 p.1.1 p.2.1).set) ∧
          (absPairSet2 p.1.1 p.2.1).set = ⋃ W ∈ Wl, W.X.set ∧
          (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - p.1.1.j →
            pairBase n m w ∈ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) :=
    fun p => hBase D p.1.1 p.2.1 (hgoodPi p.1.1 p.1.2) (hfmtPi p.1.1 p.1.2)
      (hdegPi p.1.1 p.1.2) (hPiK p.1.1 p.1.2) (hgoodPv p.2.1 p.2.2) (hfmtPv p.2.1 p.2.2)
      (hdegPv p.2.1 p.2.2) (hPairFmt p.1.1 p.1.2 p.2.1 p.2.2).2
  let levSig : PiecePair n m Pi Pv → List (SemiPf (n + pPair n m)) := fun p => (hLevPair p).choose
  let levVl : PiecePair n m Pi Pv → List (Stratum 0 (pPair n m)) :=
    fun p => (hLevPair p).choose_spec.2.2.choose
  let baseSig : PiecePair n m Pi Pv → List (SemiPf (n + pPair n m)) :=
    fun p => (hBasePair p).choose
  let baseWl : PiecePair n m Pi Pv → List (Stratum 0 (pPair n m)) :=
    fun p => (hBasePair p).choose_spec.2.2.choose
  let PTP : List (PiecePair n m Pi Pv) := Pi.attach.product Pv.attach
  let Sig : List (SemiPf (n + pPair n m)) := PTP.flatMap (fun p => levSig p ++ baseSig p)
  -- ## The specifications of the per-pair data
  have hLevLen : ∀ p : PiecePair n m Pi Pv, (levSig p).length ≤ Blev.eval D := fun p =>
    (hLevPair p).choose_spec.1
  have hBaseLen : ∀ p : PiecePair n m Pi Pv, (baseSig p).length ≤ BBase.eval D := fun p =>
    (hBasePair p).choose_spec.1
  have hLevMem : ∀ (p : PiecePair n m Pi Pv) (Z : SemiPf (n + pPair n m)), Z ∈ levSig p →
      Z.fmt ≤ Alev ∧ Z.deg ≤ Blev.eval D ∧
        NullDimLT (projFirst n (pPair n m) '' Z.set) K := fun p Z hZ =>
    (hLevPair p).choose_spec.2.1 Z hZ
  have hBaseMem : ∀ (p : PiecePair n m Pi Pv) (Z : SemiPf (n + pPair n m)), Z ∈ baseSig p →
      Z.fmt ≤ ABase ∧ Z.deg ≤ BBase.eval D ∧
        NullDimLT (projFirst n (pPair n m) '' Z.set) K := fun p Z hZ =>
    (hBasePair p).choose_spec.2.1 Z hZ
  have hLevGood : ∀ (p : PiecePair n m Pi Pv) (V : Stratum 0 (pPair n m)), V ∈ levVl p →
      V.Good ∧ V.X.set ⊆ (absLevelPairSet p.1.1 p.2.1).set := fun p V hV =>
    (hLevPair p).choose_spec.2.2.choose_spec.1 V hV
  have hLevCov : ∀ p : PiecePair n m Pi Pv,
      (absLevelPairSet p.1.1 p.2.1).set = ⋃ V ∈ levVl p, V.X.set := fun p =>
    (hLevPair p).choose_spec.2.2.choose_spec.2.1
  have hLevLow : ∀ (p : PiecePair n m Pi Pv) (V : Stratum 0 (pPair n m)), V ∈ levVl p →
      pPair n m - V.j < n + (m + 1) - p.1.1.j →
      pairSubBaseFst n m V ⊆ ⋃ Z ∈ levSig p, projFirst n (pPair n m) '' Z.set :=
    fun p V hV h => (hLevPair p).choose_spec.2.2.choose_spec.2.2.1 V hV h
  have hLevTop : ∀ (p : PiecePair n m Pi Pv) (V : Stratum 0 (pPair n m)), V ∈ levVl p →
      pPair n m - V.j = n + (m + 1) - p.1.1.j →
      pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ levSig p, projFirst n (pPair n m) '' Z.set :=
    fun p V hV h => (hLevPair p).choose_spec.2.2.choose_spec.2.2.2 V hV h
  have hBaseGood : ∀ (p : PiecePair n m Pi Pv) (W : Stratum 0 (pPair n m)), W ∈ baseWl p →
      W.Good ∧ W.X.set ⊆ (absPairSet2 p.1.1 p.2.1).set := fun p W hW =>
    (hBasePair p).choose_spec.2.2.choose_spec.1 W hW
  have hBaseCov : ∀ p : PiecePair n m Pi Pv,
      (absPairSet2 p.1.1 p.2.1).set = ⋃ W ∈ baseWl p, W.X.set := fun p =>
    (hBasePair p).choose_spec.2.2.choose_spec.2.1
  have hBaseRank : ∀ (p : PiecePair n m Pi Pv) (W : Stratum 0 (pPair n m)), W ∈ baseWl p →
      ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - p.1.1.j →
      pairBase n m w ∈ ⋃ Z ∈ baseSig p, projFirst n (pPair n m) '' Z.set :=
    fun p W hW w hw h => (hBasePair p).choose_spec.2.2.choose_spec.2.2 W hW w hw h
  -- ## Membership in the two families implies membership in `Sig`
  have hSigOfLev : ∀ (p : PiecePair n m Pi Pv) (Z : SemiPf (n + pPair n m)), Z ∈ levSig p →
      Z ∈ Sig := by
    intro p Z hZ
    simp only [Sig]
    exact List.mem_flatMap.mpr ⟨p, List.mem_product.mpr
      ⟨List.mem_attach _ _, List.mem_attach _ _⟩, List.mem_append.mpr (Or.inl hZ)⟩
  have hSigOfBase : ∀ (p : PiecePair n m Pi Pv) (Z : SemiPf (n + pPair n m)), Z ∈ baseSig p →
      Z ∈ Sig := by
    intro p Z hZ
    simp only [Sig]
    exact List.mem_flatMap.mpr ⟨p, List.mem_product.mpr
      ⟨List.mem_attach _ _, List.mem_attach _ _⟩, List.mem_append.mpr (Or.inr hZ)⟩
  -- ## The length of `Sig`
  have hPTP : PTP.length = Pi.length * Pv.length := by
    rw [show PTP = Pi.attach ×ˢ Pv.attach from rfl, List.length_product, List.length_attach,
      List.length_attach]
  have hSigLen : Sig.length ≤ Pi.length * Pv.length * (Blev.eval D + BBase.eval D) := by
    simp only [Sig]
    refine le_trans (length_flatMap_le PTP _ (Blev.eval D + BBase.eval D) ?_) ?_
    · intro p _
      rw [List.length_append]
      exact Nat.add_le_add (hLevLen p) (hBaseLen p)
    · rw [hPTP]
  refine ⟨Sig, ?_, ?_, ?_, ?_⟩
  · -- (0) the length of `Sig`
    rw [mv_eval_Q_fin3]
    rw [Polynomial.eval_add]
    exact hSigLen
  · -- (1) the members of `Sig`
    intro Z hZ
    have hZ' : Z ∈ PTP.flatMap (fun p => levSig p ++ baseSig p) := hZ
    obtain ⟨p, -, hZp⟩ := List.mem_flatMap.mp hZ'
    rcases List.mem_append.mp hZp with hZp | hZp
    · obtain ⟨h1, h2, h3⟩ := hLevMem p Z hZp
      refine ⟨le_trans h1 (le_max_left _ _), ?_, h3⟩
      rw [Polynomial.eval_add]
      exact le_trans h2 (Nat.le_add_right _ _)
    · obtain ⟨h1, h2, h3⟩ := hBaseMem p Z hZp
      refine ⟨le_trans h1 (le_max_right _ _), ?_, h3⟩
      rw [Polynomial.eval_add]
      exact le_trans h2 (Nat.le_add_left _ _)
  · -- (2) the level-pair clause
    intro S hS T hT
    refine ⟨levVl ⟨⟨S, hS⟩, ⟨T, hT⟩⟩, ?_, ?_, ?_, ?_⟩
    · intro V hV
      exact hLevGood ⟨⟨S, hS⟩, ⟨T, hT⟩⟩ V hV
    · exact hLevCov ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
    · intro V hV hlow
      exact (hLevLow ⟨⟨S, hS⟩, ⟨T, hT⟩⟩ V hV hlow).trans
        (list_iUnion_mono (fun Z : SemiPf (n + pPair n m) =>
          projFirst n (pPair n m) '' Z.set) (hSigOfLev ⟨⟨S, hS⟩, ⟨T, hT⟩⟩))
    · intro V hV htop
      exact (hLevTop ⟨⟨S, hS⟩, ⟨T, hT⟩⟩ V hV htop).trans
        (list_iUnion_mono (fun Z : SemiPf (n + pPair n m) =>
          projFirst n (pPair n m) '' Z.set) (hSigOfLev ⟨⟨S, hS⟩, ⟨T, hT⟩⟩))
  · -- (3) the base-pair clause
    intro S hS T hT
    refine ⟨baseWl ⟨⟨S, hS⟩, ⟨T, hT⟩⟩, ?_, ?_, ?_⟩
    · intro W hW
      exact hBaseGood ⟨⟨S, hS⟩, ⟨T, hT⟩⟩ W hW
    · exact hBaseCov ⟨⟨S, hS⟩, ⟨T, hT⟩⟩
    · intro W hW w hw hrank
      obtain ⟨Z, hZ, hZw⟩ := Set.mem_iUnion₂.mp (hBaseRank ⟨⟨S, hS⟩, ⟨T, hT⟩⟩ W hW w hw hrank)
      exact Set.mem_iUnion₂.mpr ⟨Z, hSigOfBase ⟨⟨S, hS⟩, ⟨T, hT⟩⟩ Z hZ, hZw⟩
