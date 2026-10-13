import Mathlib
import Submission.Work.WilE7.CoreStep.piFamily
import Submission.Work.WilE7.CoreStep.piPiece
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.pieces_of_family
import Submission.Work.WilE7.strata_of_piece
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE7.absGood_locality
import Submission.Work.WilE7.poly_dominate
import Submission.Work.WilE7.CoreStep.polyOuterN

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-!
  `Work.CoreStep.piFamilyTop`: the `(n+1, m)`-split companion of
  `Work.WilE7.CoreStep.piFamily`.

  `Work.WilE7.CoreStep.piFamily` produces, for every family `X : Fin k → SemiPf (n + (m+1))` of
  format `≤ F` and degree `≤ D`, a list of absolute `Good` strata `T : Stratum 0 (n + (m+1))`
  whose `π_n`-images (`projFirst n (m+1)`, base dimension `n`) cover the `π_n`-images of the
  family, with the immersion condition `projRank T z = n + (m+1) - T.j` for the *same* base
  `ℝ^n`.

  The present statement is the corresponding statement for the split `(n+1) + m`: the base is
  the first `n+1` coordinates and the fibre has dimension `m` (which may be `0`, in which case
  `piFamily` does not apply directly, since its fibre dimension is `m'+1 ≥ 1`).  So:

  * for `m ≥ 1` the statement is *literally* `piFamily` at base dimension `n+1` and fibre
    dimension `m` (i.e. at `n ↦ n+1`, `m ↦ m-1`), since `(n+1) + ((m-1)+1) = (n+1) + m`;
  * for `m = 0` the fibre is empty-dimensional; here the fibrewise weak stratification `hE5`
    at `(p,q) = (0, (n+1)+0)` already gives the required absolute strata, and the immersion
    condition `projRank T z = (n+1) + 0 - T.j` reduces to the fact that the base projection
    `basePrLin (n+1) 0` — which is the value-preserving reindexing `absPt` — is injective
    (`basePrLin_zero_injective`), so that it preserves the dimension of the tangent space
    (`projRank_eq_dim_zero`).

  The bounds `A`, `B`, `N` are those of `piFamily` suitably enlarged (`max`, `+`, `+`) so that
  they cover both cases simultaneously.
-/

/-! ## The value-preserving reindexing `Fin N ≃ Fin (0 + N)` -/

/-- The value preserving equivalence `Fin N ≃ Fin (0 + N)`.  This is the equivalence along
which `piPiece`'s `absPt_image_reindex` reindexes a semi-Pfaffian set; naming it here keeps the
reindexing syntactically stable across the proof. -/
def reE (N : ℕ) : Fin N ≃ Fin (0 + N) := (Work.WilE7.finEquiv (Nat.zero_add N)).symm

/-- `absPt` undoes the reindexing `reE`: the `absPt`-image of a `reE`-reindexed semi-Pfaffian
set is the set itself.  Immediate from `Work.WilE7.CoreStep.absPt_image_reindex`. -/
lemma absPt_image_reE {N : ℕ} (X : WilkiesDesign.E.SemiPf N) :
    Work.WilE7.MainDesign.absPt '' (Work.WilE7.SemiPf.reindex (reE N) X).set = X.set :=
  Work.WilE7.CoreStep.absPt_image_reindex X

/-! ## The rank condition in the degenerate fibre dimension `0` -/

/-- For `m = 0` the base projection `basePrLin N 0` is the value preserving reindexing
`absPt`, hence injective. -/
lemma basePrLin_zero_eq_absPt (N : ℕ) (z : Fin (0 + (N + 0)) → ℝ) :
    Work.WilE7.MainDesign.basePrLin N 0 z = Work.WilE7.MainDesign.absPt z := by
  funext i
  show z (Fin.cast (Nat.zero_add (N + 0)).symm (Fin.castAdd 0 i))
      = z (Fin.cast (Nat.zero_add N).symm i)
  congr 1

/-- `basePrLin N 0` is injective (it is the reindexing `absPt`, `basePrLin_zero_eq_absPt`). -/
lemma basePrLin_zero_injective (N : ℕ) :
    Function.Injective (Work.WilE7.MainDesign.basePrLin N 0) := by
  intro v w h
  have h1 : Work.WilE7.MainDesign.absPt v = Work.WilE7.MainDesign.absPt w := by
    rw [← basePrLin_zero_eq_absPt N v, ← basePrLin_zero_eq_absPt N w]
    exact h
  exact Work.WilE7.DimAPI.absPt_injective N h1

/-- **The immersion condition for the degenerate fibre dimension `0`.**  If `T : Stratum 0 (N+0)`
is `Good` and `z ∈ T.X.set`, then the rank of the base projection `π_N` on the tangent space of
`T` at `z` is `(N+0) - T.j = dim T`.

The proof is the dimension count of `projRank_eq_dim_of_sub_fibreGood` with the fibre stratum
replaced by the trivial one: `jac T z` is surjective (`jac_range_eq_top_of_good_aux`), so
`ker (jac T z)` has dimension `(0 + (N+0)) - T.j` (rank–nullity, `finrank_ker_of_surjective`),
and `basePrLin N 0` is injective (`basePrLin_zero_injective`), so it preserves that dimension. -/
theorem projRank_eq_dim_zero {N : ℕ} (T : WilkiesDesign.E.Stratum 0 (N + 0))
    (hT : T.Good) {z : Fin (0 + (N + 0)) → ℝ} (hz : z ∈ T.X.set) :
    Work.WilE7.MainDesign.projRank T z = N + 0 - T.j := by
  have hsurj : (Work.WilE7.MainDesign.jac T z).range = ⊤ :=
    Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux T hT hz
  have hdom : Module.finrank ℝ ↥(Work.WilE7.MainDesign.jac T z).ker = (0 + (N + 0)) - T.j :=
    Work.WilE7.finrank_ker_of_surjective (Work.WilE7.MainDesign.jac T z) hsurj
  have hinj : Function.Injective ((Work.WilE7.MainDesign.basePrLin N 0).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype) := by
    intro a b hab
    exact Subtype.ext (basePrLin_zero_injective N hab)
  have hfin : Module.finrank ℝ ↥(((Work.WilE7.MainDesign.basePrLin N 0).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype).range)
      = Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z)) :=
    LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype
    (Work.WilE7.MainDesign.basePrLin N 0), Submodule.range_subtype] at hfin
  show Module.finrank ℝ ↥((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
    (Work.WilE7.MainDesign.basePrLin N 0)) = N + 0 - T.j
  rw [hfin, hdom]
  omega

/-! ## The branch `m = 0` -/

/-- The `m = 0` branch of `piFamilyTop`: for a family `X : Fin k → SemiPf ((n+1) + 0)` the
fibrewise weak stratification `hE5` at `(p,q) = (0, (n+1)+0)` already provides the required
absolute strata.  The fibres over `ℝ^{n+1}` are finite for trivial reasons (they live in
`Fin 0 → ℝ`), the rank condition is `projRank_eq_dim_zero`, and the two cover identities are
transported across the value preserving reindexing `reE`. -/
theorem piTop_zero_branch
    (a0 F : ℕ) (b0 : Polynomial ℕ)
    (hE5' : ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b0.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a0 ∧ S.deg ≤ b0.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (D k n : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + 0))
    (hX : ∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) :
    ∃ Pi : List (WilkiesDesign.E.Stratum 0 ((n + 1) + 0)),
      Pi.length ≤ k * b0.eval D ∧
      (∀ T ∈ Pi, T.Good ∧ T.X.fmt ≤ a0 ∧ T.deg ≤ b0.eval D ∧
        (∀ x : Fin (n + 1) → ℝ,
          (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite) ∧
        (∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = (n + 1) + 0 - T.j) ∧
        (∃ i : Fin k, WilkiesDesign.E.projFirst (n + 1) 0 ''
            (Work.WilE7.MainDesign.absSet T) ⊆
          WilkiesDesign.E.projFirst (n + 1) 0 '' (X i).set)) ∧
      (⋃ i, WilkiesDesign.E.projFirst (n + 1) 0 '' (X i).set) =
        ⋃ T ∈ Pi, WilkiesDesign.E.projFirst (n + 1) 0 ''
          (Work.WilE7.MainDesign.absSet T) := by
  classical
  have hfmt : ∀ i, (Work.WilE7.SemiPf.reindex (reE ((n + 1) + 0)) (X i)).fmt ≤ F := by
    intro i
    have h : (Work.WilE7.SemiPf.reindex (reE ((n + 1) + 0)) (X i)).fmt = (X i).fmt := by
      simp only [Work.WilE7.SemiPf.reindex, WilkiesDesign.E.SemiPf.fmt]
      omega
    rw [h]; exact (hX i).1
  choose L hLlen hLmem hLcov _hLdisj using fun i : Fin k =>
    hE5' 0 ((n + 1) + 0) (Work.WilE7.SemiPf.reindex (reE ((n + 1) + 0)) (X i)) (hfmt i)
  let Pi : List (WilkiesDesign.E.Stratum 0 ((n + 1) + 0)) := (List.finRange k).flatMap L
  have hdegL : ∀ i, (L i).length ≤ b0.eval D := by
    intro i
    refine le_trans (hLlen i) ?_
    rw [Work.WilE7.sp_reindex_deg]
    exact Work.WilE7.poly_eval_mono_nat b0 (hX i).2
  have hsubX : ∀ (i : Fin k) (S : WilkiesDesign.E.Stratum 0 ((n + 1) + 0)), S ∈ L i →
      Work.WilE7.MainDesign.absSet S ⊆ (X i).set := by
    intro i S hS
    have hsub : S.X.set ⊆ (Work.WilE7.SemiPf.reindex (reE ((n + 1) + 0)) (X i)).set := by
      rw [hLcov i]
      intro w hw
      exact Set.mem_iUnion₂.mpr ⟨S, hS, hw⟩
    calc Work.WilE7.MainDesign.absSet S
        = Work.WilE7.MainDesign.absPt '' S.X.set := rfl
      _ ⊆ Work.WilE7.MainDesign.absPt ''
            (Work.WilE7.SemiPf.reindex (reE ((n + 1) + 0)) (X i)).set := Set.image_mono hsub
      _ = (X i).set := absPt_image_reE (X i)
  have hper_i : ∀ i : Fin k,
      WilkiesDesign.E.projFirst (n + 1) 0 '' (X i).set
        = ⋃ S ∈ L i, WilkiesDesign.E.projFirst (n + 1) 0 ''
            Work.WilE7.MainDesign.absSet S := by
    intro i
    apply Set.Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      rw [← absPt_image_reE (X i)] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hLcov i] at hy
      obtain ⟨S, hS, hyS⟩ := Set.mem_iUnion₂.mp hy
      exact Set.mem_iUnion₂.mpr
        ⟨S, hS, ⟨Work.WilE7.MainDesign.absPt y, ⟨y, hyS, rfl⟩, rfl⟩⟩
    · rintro z hz
      obtain ⟨S, hS, y, hyS, rfl⟩ := Set.mem_iUnion₂.mp hz
      exact ⟨y, hsubX i S hS hyS, rfl⟩
  refine ⟨Pi, ?_, ?_, ?_⟩
  · have h1 := Work.WilE7.CoreStep.length_flatMap_le_mul (List.finRange k) L (b0.eval D)
      (fun i _ => hdegL i)
    rw [List.length_finRange] at h1
    simpa [Pi] using h1
  · intro T hT
    obtain ⟨i, -, hTi⟩ := List.mem_flatMap.mp hT
    obtain ⟨hfmtT, hdegT, hgoodT⟩ := hLmem i T hTi
    have hdegT' : T.deg ≤ b0.eval D := by
      refine le_trans hdegT ?_
      rw [Work.WilE7.sp_reindex_deg]
      exact Work.WilE7.poly_eval_mono_nat b0 (hX i).2
    refine ⟨hgoodT, hfmtT, hdegT', ?_, ?_, ⟨i, Set.image_mono (hsubX i T hTi)⟩⟩
    · intro x
      apply Set.Subsingleton.finite
      intro a _ b _
      exact Subsingleton.elim a b
    · intro z hz
      exact projRank_eq_dim_zero T hgoodT hz
  · rw [show (⋃ i, WilkiesDesign.E.projFirst (n + 1) 0 '' (X i).set)
        = ⋃ i, ⋃ S ∈ L i, WilkiesDesign.E.projFirst (n + 1) 0 ''
            Work.WilE7.MainDesign.absSet S from Set.iUnion_congr fun i => hper_i i]
    apply Set.Subset.antisymm
    · intro z hz
      simp only [Set.mem_iUnion, exists_prop] at hz ⊢
      obtain ⟨i, S, hS, hzS⟩ := hz
      exact ⟨S, List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hS⟩, hzS⟩
    · intro z hz
      simp only [Set.mem_iUnion, exists_prop] at hz ⊢
      obtain ⟨T, hT, hzT⟩ := hz
      obtain ⟨i, -, hTi⟩ := List.mem_flatMap.mp hT
      exact ⟨i, T, hTi, hzT⟩

/-! ## The main statement -/

theorem piFamilyTop
    (hFC : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (n m : ℕ) (X : WilkiesDesign.E.SemiPf (n + m)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
          (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧
            ∀ x, (WilkiesDesign.E.fiber Xh.set x).Finite) ∧
          WilkiesDesign.E.projFirst n m '' X.set =
            ⋃ Xh ∈ L, WilkiesDesign.E.projFirst n m '' Xh.set)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
        ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
          (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
          X.set = (⋃ S ∈ L, S.X.set) ∧
          L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ) (N : MvPolynomial (Fin 2) ℕ),
      ∀ (D k n m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf ((n + 1) + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ Pi : List (WilkiesDesign.E.Stratum 0 ((n + 1) + m)),
          Pi.length ≤ MvPolynomial.eval ![D, k] N ∧
          (∀ T ∈ Pi, T.Good ∧ T.X.fmt ≤ A ∧ T.deg ≤ B.eval D ∧
            (∀ x : Fin (n + 1) → ℝ,
              (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x).Finite) ∧
            (∀ z ∈ T.X.set,
              Work.WilE7.MainDesign.projRank T z = (n + 1) + m - T.j) ∧
            (∃ i : Fin k, WilkiesDesign.E.projFirst (n + 1) m ''
                (Work.WilE7.MainDesign.absSet T) ⊆
              WilkiesDesign.E.projFirst (n + 1) m '' (X i).set)) ∧
          (⋃ i, WilkiesDesign.E.projFirst (n + 1) m '' (X i).set) =
            ⋃ T ∈ Pi, WilkiesDesign.E.projFirst (n + 1) m ''
              (Work.WilE7.MainDesign.absSet T) := by
  classical
  obtain ⟨A1, B1, N1, hmain⟩ := Work.WilE7.CoreStep.piFamily hFC hE5 F
  obtain ⟨a0, b0, hE5'⟩ := hE5 F
  obtain ⟨N0, hN0⟩ := Work.WilE7.CoreStep.polyOuterN b0 (1 : Polynomial ℕ)
  refine ⟨max A1 a0, B1 + b0, N1 + N0, ?_⟩
  intro D k n m X hX
  rcases eq_or_ne m 0 with hm | hm
  · -- degenerate fibre dimension `m = 0`
    subst hm
    obtain ⟨Pi, hlen, hmem, hunion⟩ := piTop_zero_branch a0 F b0 hE5' D k n X hX
    refine ⟨Pi, ?_, ?_, hunion⟩
    · rw [MvPolynomial.eval_add]
      have h2 : MvPolynomial.eval ![D, k] N0 = k * b0.eval D := by
        rw [hN0 D k, Polynomial.eval_one, Nat.mul_one]
      rw [h2]
      exact le_trans hlen (Nat.le_add_left _ _)
    · intro T hT
      obtain ⟨hgood, hfmt, hdeg, hfin, hrank, hprov⟩ := hmem T hT
      refine ⟨hgood, le_trans hfmt (le_max_right _ _), ?_, hfin, hrank, hprov⟩
      rw [Polynomial.eval_add]
      exact le_trans hdeg (Nat.le_add_left _ _)
  · -- fibre dimension `m ≥ 1`: this is `piFamily` at base `n+1` and fibre `m`
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    obtain ⟨Pi, hlen, hmem, hunion⟩ := hmain D k (n + 1) m' X hX
    refine ⟨Pi, ?_, ?_, hunion⟩
    · rw [MvPolynomial.eval_add]
      exact le_trans hlen (Nat.le_add_right _ _)
    · intro T hT
      obtain ⟨hgood, hfmt, hdeg, hfin, hrank, hprov⟩ := hmem T hT
      refine ⟨hgood, le_trans hfmt (le_max_left _ _), ?_, hfin, hrank, hprov⟩
      rw [Polynomial.eval_add]
      exact le_trans hdeg (Nat.le_add_right _ _)

end Work.CoreStep
