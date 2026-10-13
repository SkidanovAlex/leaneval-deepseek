/-
  CoreStep: the vocabulary of the Σ-family of `Work.CoreStep.sigmaFamily`.

  The Σ-family of the case-B step of `CoreLT_succ` is a list `Sig` of semi-Pfaffian sets in a
  *common* ambient space `ℝ^{n + m''}`, chosen so that the projection `π_n` of each of them is
  `NullDimLT · K`, and so that their `π_n`-projections cover the "forbidden" loci
  (the low-dimensional pieces, the frontiers, the low-dimensional strata of the pair sets and the
  level-agreeing pair sets).

  The natural ambient dimension is `m'' = pPair n m = 2*(n + (m+1))`: the pair space of a piece
  `Stratum 0 (n + (m+1))` is `ℝ^{pPair n m}`, and `π_n` of a point of a pair stratum is the
  "common base point", i.e. exactly the first `n` coordinates of the first block.  Padding at the
  *end* (so that the extra coordinates are `0`) turns any stratum of `ℝ^M`, `M ∈ {n+(m+1), pPair}`,
  into a member of the ambient `ℝ^{n + pPair n m}` whose `π_n`-projection is the image of the
  stratum's set under `fstN n` (the first `n` coordinates).

  This file contains the definitions and the elementary projection/measure bookkeeping;
  the assembly itself is in `Submission/Work/CoreStep/sigmaFamily.lean`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.CoreStep.SigmaAux
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.pad_set
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.pad_deg
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.E6closure
import Submission.Work.WilE7.DimAPI.stratum_nullDimLE
import Submission.Work.WilE7.DimAPI.nullDimLE_mono_dim
import Submission.Work.WilE7.DimAPI.nullDimLT_basics

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign
open Work.WilE7.CoreStep (pPair absPairSet absLevelPairSet absReindex)

/-! ## The base projection `fstN` -/

/-- The first `n` coordinates of a point of `ℝ^M` (`n ≤ M`).  This is the "base projection"
`π_n`; it is `projFirst n (M-n)` up to the `Fin` bookkeeping, and it is `pairBaseFst n m` on the
pair space `ℝ^{pPair n m}`. -/
def fstN (n : ℕ) {M : ℕ} (h : n ≤ M) (u : Fin M → ℝ) : Fin n → ℝ := fun i => u (Fin.castLE h i)

@[simp] theorem fstN_apply (n : ℕ) {M : ℕ} (h : n ≤ M) (u : Fin M → ℝ) (i : Fin n) :
    fstN n h u i = u (Fin.castLE h i) := rfl

/-- `fstN n` on `ℝ^{n + M}` is `projFirst n M`.  (The two differ only by the proof component of
`Fin.castLE`/`Fin.castAdd`.) -/
theorem fstN_eq_projFirst (n M : ℕ) (h : n ≤ n + M) (u : Fin (n + M) → ℝ) :
    fstN n h u = projFirst n M u := by
  funext i
  exact congrArg u (Fin.ext rfl)

/-- `fstN` does not depend on the proof argument. -/
theorem fstN_eq_of_le {n M : ℕ} (h h' : n ≤ M) (u : Fin M → ℝ) : fstN n h u = fstN n h' u := by
  funext i
  exact congrArg u (Fin.ext rfl)

/-- `pairBaseFst` is `fstN n`. -/
theorem pairBaseFst_eq_fstN (n m : ℕ) :
    pairBaseFst n m = fstN n (le_pPair n m) := rfl

/-! ## The stratum piece in unsplit coordinates -/

/-- The semi-Pfaffian set of an absolute stratum, in the *unsplit* coordinates `ℝ^M` (so that its
set is `absSet S`). -/
def absSub {M : ℕ} (S : Stratum 0 M) : SemiPf M :=
  Work.WilE7.SemiPf.reindex (Work.WilE7.finEquiv (Nat.zero_add M)) S.X

/-- The set of `absSub S` is `absSet S`. -/
theorem absSub_set {M : ℕ} (S : Stratum 0 M) : (absSub S).set = absSet S := by
  unfold absSub absSet
  rw [Work.WilE7.sp_reindex_set]
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hu
    refine ⟨(fun i : Fin (0 + M) => u ((Work.WilE7.finEquiv (Nat.zero_add M)) i)), hu, ?_⟩
    funext i
    show u ((Work.WilE7.finEquiv (Nat.zero_add M)) (Fin.cast (Nat.zero_add M).symm i)) = u i
    exact congrArg u (Fin.ext rfl)
  · rintro ⟨z, hz, rfl⟩
    have hz' : (fun i : Fin (0 + M) =>
        absPt z ((Work.WilE7.finEquiv (Nat.zero_add M)) i)) = z := by
      funext i
      show z (Fin.cast (Nat.zero_add M).symm ((Work.WilE7.finEquiv (Nat.zero_add M)) i)) = z i
      exact congrArg z (Fin.ext rfl)
    rw [hz']
    exact hz

@[simp] theorem absSub_r {M : ℕ} (S : Stratum 0 M) : (absSub S).r = S.X.r := rfl

theorem absSub_fmt {M : ℕ} (S : Stratum 0 M) : (absSub S).fmt = M + S.X.r := rfl

theorem absSub_deg {M : ℕ} (S : Stratum 0 M) : (absSub S).deg = S.X.deg :=
  Work.WilE7.sp_reindex_deg _ _

/-! ## The Σ-members -/

/-- The Σ-member attached to an absolute stratum `S : Stratum 0 (n + (m+1))`. -/
def sigAbs (n m : ℕ) (S : Stratum 0 (n + (m + 1))) : SemiPf (n + pPair n m) :=
  Work.WilE7.SemiPf.pad (show n + (m + 1) ≤ n + pPair n m from by
    rw [show pPair n m = (n + (m + 1)) + (n + (m + 1)) from rfl]
    omega) (absSub S)

/-- The Σ-member attached to a stratum of the pair space `ℝ^{pPair n m}`. -/
def sigPair (n m : ℕ) (W : Stratum 0 (pPair n m)) : SemiPf (n + pPair n m) :=
  Work.WilE7.SemiPf.pad (Nat.le_add_left (pPair n m) n) (absSub W)

@[simp] theorem sigAbs_r (n m : ℕ) (S : Stratum 0 (n + (m + 1))) :
    (sigAbs n m S).r = S.X.r := rfl

@[simp] theorem sigPair_r (n m : ℕ) (W : Stratum 0 (pPair n m)) :
    (sigPair n m W).r = W.X.r := rfl

theorem sigAbs_fmt (n m : ℕ) (S : Stratum 0 (n + (m + 1))) :
    (sigAbs n m S).fmt = (n + pPair n m) + S.X.r := rfl

theorem sigPair_fmt (n m : ℕ) (W : Stratum 0 (pPair n m)) :
    (sigPair n m W).fmt = (n + pPair n m) + W.X.r := rfl

theorem sigAbs_deg (n m : ℕ) (S : Stratum 0 (n + (m + 1))) :
    (sigAbs n m S).deg ≤ S.X.deg :=
  le_trans (Work.WilE7.semipf_deg_pad_le _ _) (le_of_eq (absSub_deg S))

theorem sigPair_deg (n m : ℕ) (W : Stratum 0 (pPair n m)) :
    (sigPair n m W).deg ≤ W.X.deg :=
  le_trans (Work.WilE7.semipf_deg_pad_le _ _) (le_of_eq (absSub_deg W))

/-! ## Padding and the base projection -/

/-- **The base projection of a padded semi-Pfaffian set.**  Padding a set in `ℝ^M` to `ℝ^{n+K}`
(`M ≤ n+K`), with the first `n ≤ M` coordinates kept, and projecting to the first `n` coordinates
gives the image of `X.set` under `fstN n`. -/
theorem pad_proj_fstN {n K M : ℕ} (hM : M ≤ n + K) (hnM : n ≤ M) (X : SemiPf M) :
    projFirst n K '' (Work.WilE7.SemiPf.pad hM X).set = fstN n hnM '' X.set := by
  rw [Work.WilE7.pad_set]
  ext z
  constructor
  · rintro ⟨y, ⟨hyc, hy⟩, rfl⟩
    exact ⟨Work.WilE7.takeZ hM y, hy, by
      funext i
      show y (Fin.castAdd K i) = Work.WilE7.takeZ hM y (Fin.castLE hnM i)
      rw [Work.WilE7.takeZ]
      exact congrArg y (Fin.ext rfl)⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨Work.WilE7.padZ (n + K) u, ⟨Work.WilE7.padZ_cube hu.1, ?_⟩, ?_⟩
    · rw [Work.WilE7.takeZ_padZ]
      exact hu
    · funext i
      show Work.WilE7.padZ (n + K) u (Fin.castAdd K i) = fstN n hnM u i
      have hi : (Fin.castAdd K i : Fin (n + K)).val < M := by
        have h1 : (Fin.castAdd K i : Fin (n + K)).val = i.val := Fin.val_castAdd ..
        have h2 : i.val < n := i.isLt
        omega
      rw [Work.WilE7.padZ, dif_pos hi]
      exact congrArg u (Fin.ext rfl)

/-! ## The projections of the Σ-members -/

/-- **The base projection of `sigAbs S`** is `π_{n+(m+1)}` of `absSet S`. -/
theorem sigAbs_proj (n m : ℕ) (S : Stratum 0 (n + (m + 1))) :
    projFirst n (pPair n m) '' (sigAbs n m S).set = projFirst n (m + 1) '' absSet S := by
  unfold sigAbs
  rw [pad_proj_fstN (show n + (m + 1) ≤ n + pPair n m from by
        rw [show pPair n m = (n + (m + 1)) + (n + (m + 1)) from rfl]
        omega)
      (Nat.le_add_right n (m + 1)) (absSub S), absSub_set]
  have hfun : fstN n (by omega : n ≤ n + (m + 1)) = projFirst n (m + 1) := by
    funext u
    exact fstN_eq_projFirst n (m + 1) _ u
  rw [hfun]

/-- **The base projection of `sigPair W`** is the base projection `pairSubBaseFst` of `W`. -/
theorem sigPair_proj (n m : ℕ) (W : Stratum 0 (pPair n m)) :
    projFirst n (pPair n m) '' (sigPair n m W).set = pairSubBaseFst n m W := by
  unfold sigPair
  rw [pad_proj_fstN (Nat.le_add_left (pPair n m) n) (le_pPair n m) (absSub W), absSub_set,
    pairSubBaseFst]
  rfl

/-! ## `absPt` is a coordinate homeomorphism -/

/-- The coordinate homeomorphism `ℝ^{0+N} → ℝ^N` underlying `absPt`. -/
def absHomeo (N : ℕ) : (Fin (0 + N) → ℝ) ≃ₜ (Fin N → ℝ) :=
  (Work.WilE7.pullHomeo (Work.WilE7.finEquiv (Nat.zero_add N))).symm

theorem absHomeo_apply (N : ℕ) (z : Fin (0 + N) → ℝ) : absHomeo N z = absPt z := by
  funext i
  rw [absHomeo, Work.WilE7.pullHomeo_symm_apply]
  exact congrArg z (Fin.ext rfl)

theorem absPt_injective (N : ℕ) : Function.Injective (@absPt N) := by
  intro z z' h
  funext i
  have h2 := congrFun h (Fin.cast (Nat.zero_add N) i)
  have e1 : absPt z (Fin.cast (Nat.zero_add N) i) = z i := by
    show z (Fin.cast (Nat.zero_add N).symm (Fin.cast (Nat.zero_add N) i)) = z i
    exact congrArg z (Fin.ext rfl)
  have e2 : absPt z' (Fin.cast (Nat.zero_add N) i) = z' i := by
    show z' (Fin.cast (Nat.zero_add N).symm (Fin.cast (Nat.zero_add N) i)) = z' i
    exact congrArg z' (Fin.ext rfl)
  rw [e1, e2] at h2
  exact h2

theorem absPt_image_closure {N : ℕ} (A : Set (Fin (0 + N) → ℝ)) :
    absPt '' closure A = closure (absPt '' A) := by
  have hA : absPt '' A = (absHomeo N) '' A := by
    apply Set.image_congr
    intro z _
    exact (absHomeo_apply N z).symm
  have hC : absPt '' closure A = (absHomeo N) '' closure A := by
    apply Set.image_congr
    intro z _
    exact (absHomeo_apply N z).symm
  rw [hC, Homeomorph.image_closure, ← hA]

theorem absPt_image_sdiff {N : ℕ} (A B : Set (Fin (0 + N) → ℝ)) :
    absPt '' (A \ B) = absPt '' A \ absPt '' B :=
  Set.image_sdiff (absPt_injective N) A B

/-- `absSet` unfolds to the `absPt`-image (as an equation lemma, for `rw`). -/
theorem absSet_eq_image {N : ℕ} (S : Stratum 0 N) : absSet S = absPt '' S.X.set := rfl

/-- The closure of `absSet` is the `absPt`-image of the closure. -/
theorem closure_absSet {N : ℕ} (S : Stratum 0 N) :
    closure (absSet S) = absPt '' closure S.X.set := by
  rw [absSet_eq_image, absPt_image_closure]

/-- The frontier of `absSet` is the `absPt`-image of the frontier. -/
theorem frontier_absSet {N : ℕ} (S : Stratum 0 N) :
    closure (absSet S) \ absSet S = absPt '' (closure S.X.set \ S.X.set) := by
  rw [closure_absSet, absSet_eq_image, ← absPt_image_sdiff]

/-- Monotonicity of `Polynomial.eval` for `ℕ`-valued polynomials. -/
theorem pol_eval_mono_nat {p : Polynomial ℕ} {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

/-- Images of `∈`-indexed unions. -/
theorem image_iUnion₂ {ι α β : Type*} (g : α → β) (L : List ι) (f : ι → Set α) :
    g '' (⋃ a ∈ L, f a) = ⋃ a ∈ L, g '' f a := by
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    obtain ⟨a, ha, hya⟩ := Set.mem_iUnion₂.mp hy
    exact Set.mem_iUnion₂.mpr ⟨a, ha, ⟨y, hya, rfl⟩⟩
  · rintro z hz
    obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_iUnion₂.mp hz
    exact ⟨y, Set.mem_iUnion₂.mpr ⟨a, ha, hy⟩, rfl⟩

/-- **The base projection through the pair space.**  The first block of the pair space followed by
`π_n` is `pairBaseFst n m`. -/
theorem pairBaseFst_image_absSet (n m : ℕ) (W : Stratum 0 (pPair n m)) :
    pairBaseFst n m '' absSet W =
      projFirst n (m + 1) '' (projFirst (n + (m + 1)) (n + (m + 1)) '' absSet W) := by
  unfold absSet
  apply Set.Subset.antisymm
  · rintro z ⟨u, hu, rfl⟩
    refine ⟨projFirst (n + (m + 1)) (n + (m + 1)) u, ⟨u, hu, rfl⟩, ?_⟩
    funext i
    show u (Fin.castAdd (n + (m + 1)) (Fin.castAdd (m + 1) i)) =
      u (Fin.castLE (le_pPair n m) i)
    exact congrArg u (Fin.ext rfl)
  · rintro z ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by
      funext i
      show u (Fin.castAdd (n + (m + 1)) (Fin.castAdd (m + 1) i)) =
        u (Fin.castLE (le_pPair n m) i)
      exact congrArg u (Fin.ext rfl)⟩

/-! ## The measure of the Σ-members -/

/-- A `Good` stratum with a nonempty set has at most `N` equations. -/
theorem Stratum.j_le_card_of_good {N : ℕ} (S : Stratum 0 N) (hS : S.Good)
    (hne : S.X.set.Nonempty) : S.j ≤ N := by
  obtain ⟨z, hz⟩ := hne
  have hrank := (hS z hz).2.1
  have hle := Matrix.rank_le_card_width (Matrix.of fun (a : Fin S.j) (l : Fin N) =>
    eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) z)
  rw [hrank] at hle
  simpa using hle

/-- **The measure bound for `sigAbs`.**  If the (nonempty) stratum has dimension `< K`, then the
base projection of `sigAbs S` is `NullDimLT · K`. -/
theorem sigAbs_nullDimLT {n m K : ℕ} (S : Stratum 0 (n + (m + 1))) (hS : S.Good)
    (h : S.X.set.Nonempty → n + (m + 1) - S.j < K) :
    NullDimLT (projFirst n (pPair n m) '' (sigAbs n m S).set) K := by
  rw [sigAbs_proj n m S]
  by_cases hne : S.X.set.Nonempty
  · have hjl : S.j ≤ n + (m + 1) := Stratum.j_le_card_of_good S hS hne
    have hK := h hne
    cases K with
    | zero => exact absurd hK (by omega)
    | succ K' =>
        have hle : n + (m + 1) - S.j ≤ K' := by omega
        exact Work.WilE7.DimAPI.nullDimLE_mono_dim
          (Work.WilE7.DimAPI.stratum_nullDimLE S hS) hle
  · have hempty : S.X.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [absSet, hempty, Set.image_empty, nullDimLT_empty]

/-- **The measure bound for `sigPair`.**  If the (nonempty) pair stratum has dimension `< K`, then
the base projection of `sigPair W` is `NullDimLT · K`. -/
theorem sigPair_nullDimLT {n m K : ℕ} (W : Stratum 0 (pPair n m)) (hW : W.Good)
    (h : W.X.set.Nonempty → pPair n m - W.j < K) :
    NullDimLT (projFirst n (pPair n m) '' (sigPair n m W).set) K := by
  rw [sigPair_proj n m W, pairSubBaseFst]
  by_cases hne : W.X.set.Nonempty
  · have hjl : W.j ≤ pPair n m := Stratum.j_le_card_of_good W hW hne
    have hK := h hne
    cases K with
    | zero => exact absurd hK (by omega)
    | succ K' =>
        have hle : pPair n m - W.j ≤ K' := by omega
        refine Work.WilE7.DimAPI.nullDimLE_mono_dim ?_ hle
        refine Work.WilE7.MainDesign.NullDimLE.mono
          (Y := projFirst n (m + 1) ''
            (projFirst (n + (m + 1)) (n + (m + 1)) '' absSet W)) ?_ ?_
        · exact Work.WilE7.MainDesign.NullDimLE.projFirst (n := n) (m := m + 1)
            (Work.WilE7.DimAPI.stratum_nullDimLE (n := n + (m + 1)) (m := n + (m + 1)) W hW)
        · exact subset_of_eq (pairBaseFst_image_absSet n m W)
  · have hempty : W.X.set = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [absSet, hempty, Set.image_empty, nullDimLT_empty]

/-! ## The degrees of the pair sets -/

theorem absPairSet_deg_le {n m F : ℕ} (T : Stratum 0 (n + (m + 1)))
    (h : (n + (m + 1)) + T.X.r ≤ F) :
    (absPairSet T).deg ≤ 2 * (1 + F) * (1 + (T.X.deg + T.X.deg)) ^ 2 := by
  have hfmt : (absReindex T).fmt ≤ F := h
  have hdeg : (absReindex T).deg = T.X.deg := Work.WilE7.sp_reindex_deg _ _
  have hmain := Work.WilE7.fiberProdZ_deg (absReindex T) (absReindex T) hfmt
  rw [hdeg] at hmain
  have h1 : (absPairSet T).deg
      = (Work.WilE7.fiberProdZ (absReindex T) (absReindex T)).deg :=
    Work.WilE7.sp_reindex_deg _ _
  rw [h1]
  exact hmain

theorem absLevelPairSet_deg_le {n m F : ℕ} (T T' : Stratum 0 (n + (m + 1)))
    (h : (n + (m + 1)) + T.X.r ≤ F) :
    (absLevelPairSet T T').deg ≤ 2 * (F + 2) * (1 + (T.X.deg + T'.X.deg)) ^ 2 := by
  have hfmt : (absReindex T).fmt ≤ F := h
  have hdeg : (absReindex T).deg = T.X.deg := Work.WilE7.sp_reindex_deg _ _
  have hdeg' : (absReindex T').deg = T'.X.deg := Work.WilE7.sp_reindex_deg _ _
  have hmain := Work.WilE7.levelGlue_deg (absReindex T) (absReindex T') hfmt
  rw [hdeg, hdeg'] at hmain
  have h1 : (absLevelPairSet T T').deg
      = (Work.WilE7.levelGlue (absReindex T) (absReindex T')).deg :=
    Work.WilE7.sp_reindex_deg _ _
  rw [h1]
  exact hmain

end Work.CoreStep
