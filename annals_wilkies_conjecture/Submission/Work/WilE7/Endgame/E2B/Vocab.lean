/-
  Area E7 / the `CoreLT_succ` endgame, node **E2B**: the shared vocabulary of the two halves of
  `cellRefine_of_nodesB`.

  The file-size guard of the workspace forces the proof of `cellRefine_of_nodesB` to be split over
  several modules; this module collects

  * the elementary bookkeeping lemmas (`PolyShape` and friends, the format of the level-pair sets,
    the length of a flattened list, the monotonicity of `MvPolynomial.eval`),
  * the *specifications* of the data produced by the assembly (the pieces, the rank and frontier
    data, the candidates, the `Σ`-family, the `X'`- and `Y'`-families),
  * the structure `E2Pkg` bundling that data and its properties, so that the second half of the
    proof (the per-base-cell refinement) can consume it with short field names.

  Everything here is proved; there is no `sorry`.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.CellRefineS
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif
import Submission.Work.WilE7.Endgame.PairSet2Bounds
import Submission.Work.WilE7.Endgame.E2Aux
import Submission.Work.WilE7.Endgame.E2_pieces_of_family
import Submission.Work.WilE7.Endgame.E2_rank_strata
import Submission.Work.WilE7.Endgame.E2_frontier_strata
import Submission.Work.WilE7.Endgame.E2_sheets_of_stratum
import Submission.Work.WilE7.Endgame.E2_cells_compat
import Submission.Work.WilE7.Endgame.E2_union_compat
import Submission.Work.WilE7.Endgame.E2_activeFamily
import Submission.Work.WilE7.Endgame.E2_sigmaCase
import Submission.Work.WilE7.Endgame.E2B.zList
import Submission.Work.WilE7.Endgame.E2B.packRaw
import Submission.Work.WilE7.Endgame.E2B.sigmaTotal
import Submission.Work.WilE7.Endgame.E2B.poly_dominate3b
import Submission.Work.WilE7.init_set
import Submission.Work.WilE7.CoreStep.Basic
import Submission.Work.WilE7.DecompDefs
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.pad_component_proj
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE7.poly_dominate
import Submission.Work.WilE7.poly_dominate3
import Submission.Work.WilE7.poly_embed

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

/-! ## §1. Elementary bookkeeping lemmas -/

/-- The degree of a stratum is at least the degree of its presentation. -/
theorem stratum_Xdeg_le_deg {N : ℕ} (S : Stratum 0 N) : S.X.deg ≤ S.deg := by
  simp only [WilkiesDesign.E.Stratum.deg]; omega

/-- The format of the level-pair set of two candidates. -/
theorem absLevelPairSet_fmt_le {n m F : ℕ} (R T : Stratum 0 (n + (m + 1)))
    (hR : (n + (m + 1)) + R.X.r ≤ F) (hT : (n + (m + 1)) + T.X.r ≤ F) :
    (absLevelPairSet R T).fmt ≤ 2 * F := by
  have h := Work.WilE7.levelGlue_fmt (absReindex R) (absReindex T) hR hT
  have h2 : (absLevelPairSet R T).fmt =
      (Work.WilE7.levelGlue (absReindex R) (absReindex T)).fmt := by
    simp only [WilkiesDesign.E.SemiPf.fmt, absLevelPairSet, Work.WilE7.SemiPf.reindex,
      Work.WilE7.levelGlue, Work.WilE7.CoreStep.pPair, Nat.zero_add]
  rw [h2]
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.levelGlue] at h ⊢
  omega

/-- A sum of list lengths, each bounded, is bounded by the product with the number of lists. -/
theorem length_flatten_le {α : Type*} (l : List (List α)) (B : ℕ)
    (h : ∀ x ∈ l, x.length ≤ B) : l.flatten.length ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.flatten_cons, List.length_append, List.length_cons]
      have ha : a.length ≤ B := h a (by simp)
      have ht : t.flatten.length ≤ t.length * B := ih (fun x hx => h x (by simp [hx]))
      calc a.length + t.flatten.length ≤ B + t.length * B := Nat.add_le_add ha ht
        _ = (t.length + 1) * B := by ring

/-- The polynomial length shape used by the two-variable domination lemmas. -/
def PolyShape (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ M N : ℕ, ∀ D k : ℕ, f D k ≤ M * (1 + D) ^ N * (1 + k) ^ N

theorem PolyShape.const (c : ℕ) : PolyShape (fun _ _ => c) :=
  ⟨c, 0, fun D k => by simp⟩

theorem PolyShape.add {f g : ℕ → ℕ → ℕ} (hf : PolyShape f) (hg : PolyShape g) :
    PolyShape (fun D k => f D k + g D k) := by
  obtain ⟨M, N, hf⟩ := hf
  obtain ⟨M', N', hg⟩ := hg
  refine ⟨M + M', N + N', fun D k => ?_⟩
  have e1 : (1 + D) ^ N ≤ (1 + D) ^ (N + N') :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_right N N')
  have e2 : (1 + k) ^ N ≤ (1 + k) ^ (N + N') :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_right N N')
  have e3 : (1 + D) ^ N' ≤ (1 + D) ^ (N + N') :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_left N' N)
  have e4 : (1 + k) ^ N' ≤ (1 + k) ^ (N + N') :=
    Nat.pow_le_pow_right (by omega) (Nat.le_add_left N' N)
  have h1 : f D k ≤ M * (1 + D) ^ (N + N') * (1 + k) ^ (N + N') :=
    le_trans (hf D k) (Nat.mul_le_mul (Nat.mul_le_mul_left M e1) e2)
  have h2 : g D k ≤ M' * (1 + D) ^ (N + N') * (1 + k) ^ (N + N') :=
    le_trans (hg D k) (Nat.mul_le_mul (Nat.mul_le_mul_left M' e3) e4)
  have hsum := Nat.add_le_add h1 h2
  have heq : M * (1 + D) ^ (N + N') * (1 + k) ^ (N + N') +
      M' * (1 + D) ^ (N + N') * (1 + k) ^ (N + N') =
      (M + M') * (1 + D) ^ (N + N') * (1 + k) ^ (N + N') := by ring
  rwa [heq] at hsum

theorem PolyShape.mul {f g : ℕ → ℕ → ℕ} (hf : PolyShape f) (hg : PolyShape g) :
    PolyShape (fun D k => f D k * g D k) := by
  obtain ⟨M, N, hf⟩ := hf
  obtain ⟨M', N', hg⟩ := hg
  refine ⟨M * M', N + N', fun D k => ?_⟩
  refine le_trans (Nat.mul_le_mul (hf D k) (hg D k)) ?_
  rw [show M * (1 + D) ^ N * (1 + k) ^ N * (M' * (1 + D) ^ N' * (1 + k) ^ N')
      = M * M' * ((1 + D) ^ N * (1 + D) ^ N') * ((1 + k) ^ N * (1 + k) ^ N') from by ring]
  rw [← pow_add, ← pow_add]

theorem PolyShape.poly_eval (p : Polynomial ℕ) : PolyShape (fun D _ => p.eval D) := by
  obtain ⟨C, N, h⟩ := Work.WilE7.poly_eval_le p
  refine ⟨C, N, fun D k => ?_⟩
  have h1 : (1 : ℕ) ≤ (1 + k) ^ N := Nat.one_le_pow N _ (by omega)
  have h2 : (1 + D) ^ N ≤ (1 + D) ^ N * (1 + k) ^ N := by
    calc (1 + D) ^ N = (1 + D) ^ N * 1 := by ring
      _ ≤ (1 + D) ^ N * (1 + k) ^ N := Nat.mul_le_mul_left _ h1
  refine le_trans (h D) ?_
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left C h2

theorem PolyShape.mvpoly (b : MvPolynomial (Fin 2) ℕ) :
    PolyShape (fun D k => MvPolynomial.eval ![D, k] b) := Work.WilE7.poly_le_pow b

theorem eval_mono_fin3 {b : MvPolynomial (Fin 3) ℕ} {v w : Fin 3 → ℕ} (h : ∀ i, v i ≤ w i) :
    MvPolynomial.eval v b ≤ MvPolynomial.eval w b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add]; exact Nat.add_le_add hp hq
  | mul_X p i hp =>
      rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      exact Nat.mul_le_mul hp (h i)

/-- A two-variable polynomial, read in three variables (`l` unused). -/
theorem eval_rename3 : ∀ (q : MvPolynomial (Fin 2) ℕ) (D k l : ℕ),
    MvPolynomial.eval ![D, k, l] (MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) q) =
      MvPolynomial.eval ![D, k] q := by
  intro q D k l
  have hcomp : ((![D, k, l] : Fin 3 → ℕ) ∘ Fin.castLE (by omega : 2 ≤ 3)) = ![D, k] := by
    funext i
    fin_cases i <;> rfl
  rw [MvPolynomial.eval_rename, hcomp]

/-! ## §2. The specification of the data produced by the assembly -/

section Specs

open Work.WilE7.CoreLTSuccPlan

/-- The two cuts of `E2_pieces_of_family`, with all their properties, at the arguments used by the
assembly. -/
def PiecesSpec (n m k : ℕ) (Ap : ℕ) (Pp : Polynomial ℕ) (Np : MvPolynomial (Fin 2) ℕ) (D K : ℕ)
    (X : Fin k → SemiPf ((n + 1) + m))
    (Pie : List (Fin k × Stratum 0 ((n + 1) + m)))
    (Cut : List (Stratum 0 (n + (m + 1)))) : Prop :=
  Pie.length ≤ MvPolynomial.eval ![D, k] Np ∧ Cut.length ≤ MvPolynomial.eval ![D, k] Np ∧
  (∀ p ∈ Pie, (p.2).Good ∧ (p.2).X.fmt ≤ Ap ∧ (p.2).deg ≤ Pp.eval D ∧
    (∀ x : Fin (n + 1) → ℝ, (fiber (absSet (p.2)) x).Finite) ∧
    (∀ z ∈ (p.2).X.set, projRank (p.2) z = (n + 1) + m - (p.2).j) ∧
    projFirst (n + 1) m '' absSet (p.2) ⊆ projFirst (n + 1) m '' (X p.1).set) ∧
  (∀ i : Fin k, projFirst (n + 1) m '' (X i).set =
    ⋃ p ∈ Pie.filter (fun p => p.1 = i), projFirst (n + 1) m '' absSet (p.2)) ∧
  (∀ p ∈ Pie, (E2.swapStratum (p.2)).Good ∧ (E2.swapStratum (p.2)).X.fmt ≤ Ap ∧
    (E2.swapStratum (p.2)).deg ≤ Pp.eval D ∧ n + (m + 1) - (E2.swapStratum (p.2)).j ≤ K + 1 ∧
    (∀ z ∈ (E2.swapStratum (p.2)).X.set, projRank (E2.swapStratum (p.2)) z ≤ K) ∧
    (∀ z ∈ (E2.swapStratum (p.2)).X.set, Module.finrank ℝ
      ↥(Submodule.map ((projTopLin n m).comp (absPtLin (n + (m + 1))))
        (jac (E2.swapStratum (p.2)) z).ker) = n + (m + 1) - (E2.swapStratum (p.2)).j) ∧
    projTop n m '' absSet (E2.swapStratum (p.2)) ⊆ projFirst (n + 1) m '' (X p.1).set) ∧
  (∀ R ∈ Cut, R.Good ∧ R.X.fmt ≤ Ap ∧ R.deg ≤ Pp.eval D ∧
    (∀ z ∈ R.X.set, projRank R z = n + (m + 1) - R.j) ∧ n + (m + 1) - R.j ≤ K ∧
    (∃ i : Fin k, projFirst n (m + 1) '' absSet R ⊆ basePr n m '' (X i).set)) ∧
  (⋃ i : Fin k, basePr n m '' (X i).set) = ⋃ R ∈ Cut, projFirst n (m + 1) '' absSet R

/-- The candidate property: `Good`, rank-full, of dimension `≤ K`, with the format/degree bounds. -/
def CandSpec (n m K : ℕ) (Ac : ℕ) (Dq : Polynomial ℕ) (D : ℕ)
    (Cand : List (Stratum 0 (n + (m + 1)))) : Prop :=
  ∀ S ∈ Cand, S.Good ∧ S.X.fmt ≤ Ac ∧ S.deg ≤ Dq.eval D ∧ n + (m + 1) - S.j ≤ K ∧
    ∀ z ∈ S.X.set, projRank S z = n + (m + 1) - S.j

/-- The `Σ`-clauses consumed by the G-case. -/
def SigSpec (n m K : ℕ) (D : ℕ) (Fp : ℕ) (Pi Pv : List (Stratum 0 (n + (m + 1))))
    (Sig : List (SemiPf (n + pPair n m))) : Prop :=
  (∀ Z ∈ Sig, Z.fmt ≤ Fp ∧ Z.deg ≤ D ∧
    NullDimLT (projFirst n (pPair n m) '' Z.set) K) ∧
  (∀ T ∈ Pi, n + (m + 1) - T.j < K →
    projFirst n (m + 1) '' absSet T ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
  (∀ T ∈ Pi, frontierSet n m T ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
  (∀ T ∈ Pi, ∃ Wl : List (Stratum 0 (pPair n m)),
    (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet T).set) ∧
    ((absPairSet T).set = ⋃ W ∈ Wl, W.X.set) ∧
    (∀ W ∈ Wl, pPair n m - W.j < n + (m + 1) - T.j →
      pairSubBaseFst n m W ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set)) ∧
  (∀ T ∈ Pi, ∀ T' ∈ Pi, ∃ Vl : List (Stratum 0 (pPair n m)),
    (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet T T').set) ∧
    ((absLevelPairSet T T').set = ⋃ V ∈ Vl, V.X.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - T.j →
      pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - T.j →
      pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set)) ∧
  (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Vl : List (Stratum 0 (pPair n m)),
    (∀ V ∈ Vl, V.Good ∧ V.X.set ⊆ (absLevelPairSet S T).set) ∧
    ((absLevelPairSet S T).set = ⋃ V ∈ Vl, V.X.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j < n + (m + 1) - S.j →
      pairSubBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set) ∧
    (∀ V ∈ Vl, pPair n m - V.j = n + (m + 1) - S.j →
      pairFrontierBaseFst n m V ⊆ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set)) ∧
  (∀ S ∈ Pi, ∀ T ∈ Pv, ∃ Wl : List (Stratum 0 (pPair n m)),
    (∀ W ∈ Wl, W.Good ∧ W.X.set ⊆ (absPairSet2 S T).set) ∧
    ((absPairSet2 S T).set = ⋃ W ∈ Wl, W.X.set) ∧
    (∀ W ∈ Wl, ∀ w ∈ W.X.set, pairBaseRank W w < n + (m + 1) - S.j →
      pairBase n m w ∈ ⋃ Z ∈ Sig, projFirst n (pPair n m) '' Z.set))

end Specs

end

end Work.WilE7.Endgame.E2B
