/-
  Area E7 / the `CoreLT_succ` endgame, node **E2S** (`cellRefine_of_nodesS`): auxiliary material.

  This file collects the *plumbing* lemmas that the assembly of `CellRefineS` needs and that are
  independent of the construction itself:

  * `DimLE` monotonicity and the consequence of `not_dimLE_of_projRank` that makes the
    rank classification of the pieces work ("a piece whose `π_n`-image is contained in a set of
    `DimLE · K` has `π_n`-rank `≤ K` everywhere");
  * the "avoidance" bookkeeping: a set covered by the `π_n`-images of a family, every member of
    which is disjoint from a fixed cell `C`, is itself disjoint from `C`;
  * the `SemiPf` presentations of a stratum as a member of the `Y`-family, with the `π_n`-image
    preserved (`stratumSemiPf`), and of its `±1` slices.
-/
import Mathlib
import Submission.Work.WilE7.Endgame.CellRefineS
import Submission.Work.WilE7.coreLT_succ.Pieces
import Submission.Work.WilE7.coreLT_succ.Classification
import Submission.Work.WilE7.coreLT_succ.gcase_strata
import Submission.Work.WilE7.coreLT_succ.frontierFamily
import Submission.Work.WilE7.coreLT_succ.gcase_fiber_finite
import Submission.Work.WilE7.coreLT_succ.SigmaCase
import Submission.Work.WilE7.CoreStep.piFamily
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.SheetData.gcase_cfs
import Submission.Work.WilE7.CoreStep.gcase_sheets
import Submission.Work.WilE7.CoreStep.gcase_compat_strong
import Submission.Work.WilE7.CoreStep.hbound_of_frontier_sheets_C
import Submission.Work.CoreStep.hclosed_of_sigma
import Submission.Work.CoreStep.havoid_of_sigma
import Submission.Work.CoreStep.hdich_of_pieces
import Submission.Work.CoreStep.sigmaFamily_len
import Submission.Work.CoreStep.fibreProd_sigma_lem
import Submission.Work.WilE7.coreLT_succ.semiPf_coord_levelSet
import Submission.Work.WilE7.Endgame.sigmaFamily_len_unif
import Submission.Work.WilE7.fiber_card_bound
import Submission.Work.WilE7.DimAPI.not_dimLE_of_projRank
import Submission.Work.WilE7.DimAPI.cylDecomp_fiber
import Submission.Work.WilE7.DimAPI.cylDecomp_union_restricted
import Submission.Work.WilE7.yFamily_pack_family
import Submission.Work.WilE7.poly_dominate

set_option autoImplicit false
noncomputable section
open Classical Filter Topology

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair pDim absPtUp absPtInv absReindex absLevelPairSet absPairSet
  pairPtUp projTop projTopSet projTopLin absPtLin AttainAt vertCoord)
open Work.CoreStep (frontierSet pairSubBaseFst pairFrontierBaseFst pairBase)

/-! ## 1. `DimLE` monotonicity and the rank bound `projRank ≤ K` -/

theorem dimLE_mono {n μ : ℕ} {X Y : Set (Fin n → ℝ)} (h : DimLE Y μ) (hXY : X ⊆ Y) : DimLE X μ :=
  fun e => by
    have h1 : interior ((fun x => x ∘ e) '' X) ⊆ interior ((fun x => x ∘ e) '' Y) :=
      interior_mono (Set.image_mono hXY)
    rw [h e] at h1
    exact Set.eq_empty_of_subset_empty h1

/-- **The rank bound.**  If the `π_n`-image of a `Good` stratum `S` is contained in a set of
`DimLE · K`, then `projRank S z ≤ K` at every point of `S`. -/
theorem projRank_le_of_dimLE {n m K : ℕ} {S : Stratum 0 (n + m)}
    (hS : S.Good) {Y : Set (Fin n → ℝ)} (hY : DimLE Y K)
    (hsub : projFirst n m '' absSet S ⊆ Y) : ∀ z ∈ S.X.set, projRank S z ≤ K := by
  intro z hz
  by_contra hcon
  rw [not_le] at hcon
  exact Work.WilE7.DimAPI.not_dimLE_of_projRank S hS hz hcon (dimLE_mono hY hsub)

/-! ## 2. Avoidance bookkeeping -/

/-- If every member of a family is disjoint from `C`, then the union of the family is disjoint
from `C`. -/
theorem disjoint_iUnion_of_disjoint {ι α : Type*} {Sig : List ι} {f : ι → Set α}
    {C : Set α} (h : ∀ S ∈ Sig, Disjoint C (f S)) : Disjoint C (⋃ S ∈ Sig, f S) := by
  rw [Set.disjoint_left]
  intro x hx hxS
  obtain ⟨S, hS, hxS'⟩ := Set.mem_iUnion₂.mp hxS
  exact (Set.disjoint_left.mp (h S hS)) hx hxS'

/-- Contrapositive form, used to feed the `pairSubBaseFst` / `pairFrontierBaseFst` avoidance
hypotheses of the pair lemmas: a point covered by the `π_n`-images of a family, every member of
which is disjoint from `C`, cannot lie in `C`. -/
theorem not_mem_of_mem_iUnion_of_disjoint {ι : Type*} {n : ℕ} {Sig : List ι}
    {f : ι → Set (Fin n → ℝ)} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (h : ∀ S ∈ Sig, Disjoint C (f S)) (hx : x ∈ C)
    (hxS : x ∈ ⋃ S ∈ Sig, f S) : False := by
  obtain ⟨S, hS, hxS'⟩ := Set.mem_iUnion₂.mp hxS
  exact (Set.disjoint_left.mp (h S hS)) hx hxS'

/-! ## 3. The `Y`-presentation of a stratum and of its `±1` slices -/

namespace E2

/-- The `SemiPf (n + (m+1))` presentation of the absolute set of a stratum: its set is `absSet S`,
so its `π_n`-image is `projFirst n (m+1) '' absSet S`. -/
def stratumSemiPf {n m : ℕ} (S : Stratum 0 (n + (m + 1))) : SemiPf (n + (m + 1)) :=
  Work.CoreStep.absSub S

theorem stratumSemiPf_set {n m : ℕ} (S : Stratum 0 (n + (m + 1))) :
    (stratumSemiPf S).set = absSet S :=
  Work.CoreStep.absSub_set S

theorem stratumSemiPf_fmt {n m : ℕ} (S : Stratum 0 (n + (m + 1))) :
    (stratumSemiPf S).fmt = (n + (m + 1)) + S.X.r  :=
  Work.CoreStep.absSub_fmt S

theorem stratumSemiPf_deg {n m : ℕ} (S : Stratum 0 (n + (m + 1))) :
    (stratumSemiPf S).deg = S.X.deg :=
  Work.CoreStep.absSub_deg S

/-- The `σ ∈ {±1}` slice of a stratum, as a `SemiPf` set in the `(n, m+1)` frame.  Its set is
`{z ∈ absSet S | vertCoord (projSnd n (m+1) z) = σ}`.  The stratum's presentation is tidied first so
that the degree bound is linear in `S.deg` (a `SemiPf` set always satisfies
`basics.length ≤ 1 + deg` after `tidy`). -/
def sliceSemiPf {n m : ℕ} (S : Stratum 0 (n + (m + 1))) (σ : ℝ) : SemiPf (n + (m + 1)) :=
  (Work.WilE7.coreLT_succ.semiPf_coord_levelSet (Work.WilE7.tidy (Work.CoreStep.absSub S))
    (Fin.last m) σ).choose

theorem sliceSemiPf_set {n m : ℕ} (S : Stratum 0 (n + (m + 1))) (σ : ℝ) :
    (sliceSemiPf S σ).set
      = {z : Fin (n + (m + 1)) → ℝ | z ∈ absSet S ∧ vertCoord (projSnd n (m + 1) z) = σ} := by
  rw [sliceSemiPf,
    (Work.WilE7.coreLT_succ.semiPf_coord_levelSet (Work.WilE7.tidy (Work.CoreStep.absSub S))
      (Fin.last m) σ).choose_spec.1, Work.WilE7.tidy_set, Work.CoreStep.absSub_set]
  rfl

theorem sliceSemiPf_fmt {n m : ℕ} (S : Stratum 0 (n + (m + 1))) (σ : ℝ) :
    (sliceSemiPf S σ).fmt ≤ (n + (m + 1)) + S.X.r := by
  refine le_trans (Work.WilE7.coreLT_succ.semiPf_coord_levelSet
    (Work.WilE7.tidy (Work.CoreStep.absSub S)) (Fin.last m) σ).choose_spec.2.1 ?_
  simp only [WilkiesDesign.E.SemiPf.fmt, Work.WilE7.tidy_r, Work.CoreStep.absSub_r]
  exact le_rfl

theorem sliceSemiPf_deg {n m : ℕ} (S : Stratum 0 (n + (m + 1))) (σ : ℝ) :
    (sliceSemiPf S σ).deg ≤ 3 * S.X.deg + 2 := by
  show ((Work.WilE7.coreLT_succ.semiPf_coord_levelSet
    (Work.WilE7.tidy (Work.CoreStep.absSub S)) (Fin.last m) σ).choose).deg ≤ 3 * S.X.deg + 2
  have h1 := (Work.WilE7.coreLT_succ.semiPf_coord_levelSet
    (Work.WilE7.tidy (Work.CoreStep.absSub S)) (Fin.last m) σ).choose_spec.2.2
  obtain ⟨h2a, h2b⟩ := (Work.WilE7.PadAux.tidy_bounds (n + (m + 1)) (Work.CoreStep.absSub S))
  have h2a' : (Work.WilE7.tidy (Work.CoreStep.absSub S)).deg ≤ S.X.deg :=
    le_trans h2a (le_of_eq (Work.CoreStep.absSub_deg S))
  have h2b' : (Work.WilE7.tidy (Work.CoreStep.absSub S)).basics.length ≤ 1 + S.X.deg :=
    le_trans h2b (by rw [Work.CoreStep.absSub_deg])
  omega

end E2


/-! ## 4. The frame change `((n+1), m) → (n, m+1)` for a single stratum -/

namespace E2

/-- The transport of an absolute stratum of the `((n+1), m)` split to the `(n, m+1)` split used by
the `gcase`/`cfs` machinery of the assembly. -/
def swapStratum {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) : Stratum 0 (n + (m + 1)) :=
  Work.CoreStep.Stratum.reindex (Work.WilE7.coreLT_succ.swapEquiv0 n m) T

theorem swapStratum_j {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) : (swapStratum T).j = T.j := rfl

theorem swapStratum_r {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) :
    (swapStratum T).X.r = T.X.r := rfl

theorem swapStratum_deg {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) :
    (swapStratum T).deg = T.deg :=
  Work.CoreStep.Stratum.reindex_deg _ T

theorem swapStratum_good {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) :
    (swapStratum T).Good ↔ T.Good :=
  ⟨Work.CoreStep.stratReindex_good_fwd _ T, Work.CoreStep.stratReindex_good_bwd _ T⟩

theorem swapStratum_projTop {n m : ℕ} (T : Stratum 0 ((n + 1) + m)) :
    projTop n m '' absSet (swapStratum T) = projFirst (n + 1) m '' absSet T :=
  Work.WilE7.coreLT_succ.projTop_absPt_reindex (n := n) (m := m) T.X

/-- `Fin.init ∘ π_{n+1} = π_n`: the base projection of the `((n+1), m)` frame is the `π_n`-projection
of the `(n, m+1)` frame. -/
theorem init_projFirst {n m : ℕ} (z : Fin ((n + 1) + m) → ℝ) :
    Fin.init (projFirst (n + 1) m z) = basePr n m z := by
  funext i
  rfl

end E2


/-! ## 5. Polynomial domination helpers -/

/-- **Composition domination.**  `q.eval (c * (D + p.eval D))` is dominated by a single
`ℕ`-polynomial in `D`, for any `ℕ`-polynomials `q`, `p` and any constant `c`. -/
theorem poly_comp_dominate (c : ℕ) (q p : Polynomial ℕ) :
    ∃ P : Polynomial ℕ, ∀ D : ℕ, q.eval (c * (D + p.eval D)) ≤ P.eval D := by
  obtain ⟨Cq, Nq, hq⟩ := Work.WilE7.poly_eval_le q
  obtain ⟨Cp, Np, hp⟩ := Work.WilE7.poly_eval_le p
  refine ⟨Polynomial.C (Cq * ((1 + c) * (Cp + 1)) ^ Nq) * (1 + Polynomial.X) ^ ((Np + 1) * Nq),
    fun D => ?_⟩
  have hpD : 1 + p.eval D ≤ (Cp + 1) * (1 + D) ^ Np := by
    have h2 : 1 ≤ (1 + D) ^ Np := Nat.one_le_pow Np (1 + D) (by omega)
    calc 1 + p.eval D ≤ 1 + Cp * (1 + D) ^ Np := Nat.add_le_add_left (hp D) 1
      _ ≤ (1 + D) ^ Np + Cp * (1 + D) ^ Np := Nat.add_le_add_right h2 _
      _ = (Cp + 1) * (1 + D) ^ Np := by ring
  have hX : 1 + c * (D + p.eval D) ≤ ((1 + c) * (Cp + 1)) * (1 + D) ^ (Np + 1) := by
    have h1 : 1 + c * (D + p.eval D) ≤ (1 + c) * (1 + D) * (1 + p.eval D) := by
      have e : (1 + c) * (1 + D) * (1 + p.eval D)
          = 1 + D + p.eval D + D * p.eval D + c + c * D + c * (p.eval D)
            + c * (D * (p.eval D)) := by ring
      rw [e]
      have hDp : c * (D + p.eval D) = c * D + c * (p.eval D) := by ring
      rw [hDp]
      omega
    have h2 : (1 + c) * (1 + D) * (1 + p.eval D)
        ≤ (1 + c) * (1 + D) * ((Cp + 1) * (1 + D) ^ Np) := Nat.mul_le_mul_left _ hpD
    calc 1 + c * (D + p.eval D) ≤ (1 + c) * (1 + D) * (1 + p.eval D) := h1
      _ ≤ (1 + c) * (1 + D) * ((Cp + 1) * (1 + D) ^ Np) := h2
      _ = ((1 + c) * (Cp + 1)) * (1 + D) ^ (Np + 1) := by ring
  have heval : (Polynomial.C (Cq * ((1 + c) * (Cp + 1)) ^ Nq) *
      (1 + Polynomial.X) ^ ((Np + 1) * Nq)).eval D
      = Cq * ((1 + c) * (Cp + 1)) ^ Nq * (1 + D) ^ ((Np + 1) * Nq) := by
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X]
  rw [heval]
  calc q.eval (c * (D + p.eval D)) ≤ Cq * (1 + c * (D + p.eval D)) ^ Nq := hq _
    _ ≤ Cq * (((1 + c) * (Cp + 1)) * (1 + D) ^ (Np + 1)) ^ Nq :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
    _ = Cq * ((1 + c) * (Cp + 1)) ^ Nq * (1 + D) ^ ((Np + 1) * Nq) := by
        rw [mul_pow, ← pow_mul]; ring

/-- A two-variable polynomial bound, read in three variables (`l` unused). -/
theorem mvpoly2_to_3 (b : MvPolynomial (Fin 2) ℕ) :
    ∃ b' : MvPolynomial (Fin 3) ℕ, ∀ D k l : ℕ,
      MvPolynomial.eval ![D, k, l] b' = MvPolynomial.eval ![D, k] b := by
  refine ⟨MvPolynomial.rename (Fin.castLE (by omega : 2 ≤ 3)) b, fun D k l => ?_⟩
  have hcomp : ((![D, k, l] : Fin 3 → ℕ) ∘ Fin.castLE (by omega : 2 ≤ 3)) = ![D, k] := by
    funext i
    fin_cases i <;> rfl
  rw [MvPolynomial.eval_rename, hcomp]

end Work.WilE7.Endgame
