import Mathlib
import Submission.Subspace.RealRank.DescentAux
import Submission.Subspace.RealRank.Gap
import Submission.Subspace.RealRank.Realisers
import Submission.Subspace.RealRank.Containment
import Submission.Subspace.RealRank.Exponent
import Submission.Commons.GeometryOfNumbers.Box.prod_successiveMinimum_box_le_real
import Submission.Commons.NumberTheory.DiophantineApproximation.graded_basis_real
import Submission.Commons.Combinatorics.infinite_fiber
import Submission.Commons.Combinatorics.grid_approx_infinite_fintype
import Submission.Commons.Analysis.Normed.finite_bounded_int_vectors
import Submission.Commons.LinearAlgebra.GeneralPosition.not_finite_cover_of_genPos
import Submission.Commons.LinearAlgebra.Matrix.isAlgebraic_det
import Submission.Commons.GeometryOfNumbers.SuccessiveMinima.box_bounds_uniform
import Submission.Commons.Analysis.Log.log_box_bound
import Submission.Commons.LinearAlgebra.Matrix.mem_span_cols_of_mem_span_cols
import Submission.Commons.LinearAlgebra.Matrix.det_unitriangular_comb

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace Submission.Subspace.RealRank

variable {N : ℕ}

/-- **The exponent-sum bound with an arbitrary constant in place of `|det|`.** -/
theorem wedge_exponent_sum_neg_gen {N r k : ℕ} (hrk : r + k = N) (hr : 1 ≤ r)
    (c : Fin N → ℝ) (π : Equiv.Perm (Fin N)) (lam : ℕ → ℝ)
    (hlam0 : ∀ j, j < N → 0 < lam j)
    {Q : ℝ} (hQ : 2 ≤ Q) {D : ℝ} (hD : 0 < D)
    (hprod : ∏ j : Fin N, lam j.val ≤ D * Q ^ (-(∑ i, c i)))
    {gap ε0 : ℝ} (hgap0 : 0 < gap) (hε0 : 0 < ε0)
    (hgap : gap ≤ Q ^ (-ε0)) (K γ : ℝ) (hK : 0 < K) (hγ : 0 ≤ γ)
    (hbig : (Nat.choose N r : ℝ) * Real.log K +
        (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log D ≤ ε0 / 4 * Real.log Q)
    (hgamma : (Nat.choose N r : ℝ) * γ ≤ ε0 / 4) :
    ∑ T : Set.powersetCard (Fin N) r,
      ((∑ t ∈ (T : Finset (Fin N)), c (π t)) +
        ((Real.log (K * ∏ t ∈ (T : Finset (Fin N)), lam t.val) +
          (if (T : Finset (Fin N)) = Finset.univ.filter (fun t => k ≤ t.val)
            then Real.log gap else 0)) / Real.log Q + γ))
      ≤ -ε0 / 2 := by
  have hNpos : 0 < N := by omega
  set M : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.diagonal (fun i => if i = (⟨0, hNpos⟩ : Fin N) then D else 1) with hM
  have hdet : M.det = D := by
    rw [hM, Matrix.det_diagonal]
    rw [Finset.prod_eq_single (⟨0, hNpos⟩ : Fin N)
      (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  refine wedge_exponent_sum_neg hrk hr M (by rw [hdet, abs_of_pos hD]; exact hD) c π lam hlam0 hQ ?_
    hgap0 hε0 hgap K γ hK hγ ?_ hgamma
  · rw [hdet, abs_of_pos hD]; exact hprod
  · rw [hdet, abs_of_pos hD]; exact hbig

/-! ## Per-`x` data -/

/-- The realiser data of the successive minima at scale `‖x‖`. -/
def IsRealiserData (Mr : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ)
    (x : Fin N → ℤ) (xs : Fin N → Fin N → ℤ) : Prop :=
  (∀ j : Fin N, xs j ≠ 0) ∧
  LinearIndependent ℚ (fun j : Fin N => fun k : Fin N => (xs j k : ℚ)) ∧
  (∀ j i : Fin N, ‖∑ k, toC Mr i k * (xs j k : ℂ)‖
      ≤ lamS (toC Mr) c ‖x‖ j.val * ‖x‖ ^ (c i)) ∧
  (∀ j : Fin N, ∀ t : ℝ, 0 < t → t < lamS (toC Mr) c ‖x‖ j.val → ∀ y : Fin N → ℤ,
    (∀ i, ‖∑ k, toC Mr i k * (y k : ℂ)‖ ≤ t * ‖x‖ ^ (c i)) →
    (fun k => (y k : ℚ)) ∈ Submodule.span ℚ (Set.range (fun i : {i : Fin N // i < j} =>
      fun k => (xs i.1 k : ℚ))))

/-- The straightening data (`graded_basis_real`) at scale `‖x‖`. -/
def IsStraightening (Mr : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) (C0 : ℝ)
    (x : Fin N → ℤ) (xs : Fin N → Fin N → ℤ) (ξ : Fin N → Fin N → ℤ)
    (π : Equiv.Perm (Fin N)) : Prop :=
  (∀ i j : Fin N, j ≤ i → ξ i j = 0) ∧
  ∀ t j : Fin N, |∑ k, Mr (π t) k * ((xs j k : ℝ) + ∑ i : Fin N, ((ξ i j : ℤ) : ℝ) * (xs i k : ℝ))|
    ≤ C0 * min (lamS (toC Mr) c ‖x‖ t.val) (lamS (toC Mr) c ‖x‖ j.val) * ‖x‖ ^ (c (π t))

/-- The gap-index data at scale `‖x‖`. -/
def IsGapData (Mr : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) (R : ℕ)
    (x : Fin N → ℤ) (k : Fin N) : Prop :=
  R ≤ k.val ∧ k.val < N ∧
  lamS (toC Mr) c ‖x‖ (k.val - 1) / lamS (toC Mr) c ‖x‖ k.val
    ≤ ‖x‖ ^ (-(-(∑ i, c i) / (2 * (N : ℝ) * ((N : ℝ) - R))))

/-- The complexification of an invertible real matrix is invertible. -/
lemma toC_det_ne_zero {σ : Type*} [Fintype σ] [DecidableEq σ] (Mr : Matrix σ σ ℝ)
    (h : Mr.det ≠ 0) :
    (Matrix.of (toC Mr)).det ≠ 0 := by
  intro h0
  have h1 : (Matrix.of (toC Mr)).det = ((Mr.det : ℝ) : ℂ) := by
    rw [show Matrix.of (toC Mr) = (algebraMap ℝ ℂ).mapMatrix Mr from rfl]
    exact (RingHom.map_det (algebraMap ℝ ℂ) Mr).symm
  exact h (Complex.ofReal_eq_zero.mp (by rw [← h1]; exact h0))


/-! ## Helpers for the compound box -/

/-- The rational cast of a compound entry is the compound entry of the cast matrix. -/
lemma compound_map_intCast_rat {N r : ℕ} (V : Matrix (Fin N) (Fin N) ℤ) (T S : Idx N r) :
    ((Commons.LinearAlgebra.Matrix.compound r V) T S : ℚ)
      = Commons.LinearAlgebra.Matrix.compound r (V.map (Int.castRingHom ℚ)) T S := by
  rw [Commons.LinearAlgebra.Matrix.compound, Commons.LinearAlgebra.Matrix.compound,
    Matrix.of_apply, Matrix.of_apply, Matrix.submatrix_map, ← RingHom.mapMatrix_apply]
  exact RingHom.map_det (Int.castRingHom ℚ) _

/-- **The approximation space of the compound system is the span of the wedge columns.**  -/
theorem approxSpace_compound_eq_span_cols {N r : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M.det ≠ 0) (V : Matrix (Fin N) (Fin N) ℤ) (xbar : Idx N r → ℝ)
    (hxbar : ∑ i, xbar i < 0) (hcard2 : 2 ≤ Fintype.card (Idx N r))
    (hV : V.det ≠ 0)
    (Tstar : Idx N r) (Qcp : ℝ) (hQcp1 : 1 ≤ Qcp)
    (hQcp : ∀ Q' : ℝ, Qcp ≤ Q' → Module.finrank ℚ
      (Submodule.span ℚ (intCastVec '' compBox r M xbar Q')) ≤ Fintype.card (Idx N r) - 1)
    (Q : ℝ) (hQ : Qcp ≤ Q)
    (hmem : ∀ S : Idx N r, S ≠ Tstar →
      (fun S' => (Commons.LinearAlgebra.Matrix.compound r V) S' S) ∈ compBox r M xbar Q) :
    approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M)) xbar Q
        = Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
            (fun T => ((Commons.LinearAlgebra.Matrix.compound r V) T S : ℚ)))) ∧
      Module.finrank ℚ (approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M)) xbar Q)
        = Fintype.card (Idx N r) - 1 := by
  have hVc : (Commons.LinearAlgebra.Matrix.compound r V).det ≠ 0 := by
    have hcompmap : (Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)
        = Commons.LinearAlgebra.Matrix.compound r (V.map (Int.castRingHom ℚ)) := by
      ext T S
      rw [Matrix.map_apply]
      exact compound_map_intCast_rat V T S
    have hVq : (V.map (Int.castRingHom ℚ)).det ≠ 0 := by
      rw [show (V.map (Int.castRingHom ℚ)).det = ((V.det : ℤ) : ℚ) from by
        rw [show V.map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix V from rfl]
        exact (RingHom.map_det (Int.castRingHom ℚ) V).symm]
      exact Int.cast_ne_zero.mpr hV
    have h3 := Commons.LinearAlgebra.Matrix.det_compound_ne_zero (r := r)
      (V.map (Int.castRingHom ℚ)) hVq
    have h4 : ((Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)).det
        = (((Commons.LinearAlgebra.Matrix.compound r V).det : ℤ) : ℚ) := by
      rw [show (Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)
          = (Int.castRingHom ℚ).mapMatrix (Commons.LinearAlgebra.Matrix.compound r V) from rfl]
      exact (RingHom.map_det (Int.castRingHom ℚ) (Commons.LinearAlgebra.Matrix.compound r V)).symm
    have h5 : ((Commons.LinearAlgebra.Matrix.compound r V).det : ℚ) ≠ 0 := by
      rw [← h4, hcompmap]
      exact h3
    exact fun h0 => h5 (by rw [h0]; simp)
  have hspan := span_compBox_eq_wedge M hM V hVc xbar hxbar hcard2 Tstar Qcp hQcp1 hQcp Q hQ hmem
  have hspan' : approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M)) xbar Q
      = Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
          (fun T => ((Commons.LinearAlgebra.Matrix.compound r V) T S : ℚ)))) := by
    rw [approxSpace_toC_compBox_eq, hspan]
  refine ⟨hspan', ?_⟩
  rw [hspan']
  have hVQ : ((Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [show ((Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)).det
        = (((Commons.LinearAlgebra.Matrix.compound r V).det : ℤ) : ℚ) from by
      rw [show (Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)
          = (Int.castRingHom ℚ).mapMatrix (Commons.LinearAlgebra.Matrix.compound r V) from rfl]
      exact (RingHom.map_det (Int.castRingHom ℚ) (Commons.LinearAlgebra.Matrix.compound r V)).symm]
    exact Int.cast_ne_zero.mpr hVc
  have hunit : IsUnit ((Commons.LinearAlgebra.Matrix.compound r V).map (Int.castRingHom ℚ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hVQ)
  have hcols := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
  have hli : LinearIndependent ℚ (fun S : {S : Idx N r // S ≠ Tstar} =>
      (fun T => ((Commons.LinearAlgebra.Matrix.compound r V) T S : ℚ))) := by
    have h1 := hcols.comp (Subtype.val : {S : Idx N r // S ≠ Tstar} → Idx N r)
      Subtype.coe_injective
    exact h1
  rw [finrank_span_eq_card hli]
  have hcard : Fintype.card {S : Idx N r // S ≠ Tstar} = Fintype.card (Idx N r) - 1 := by
    have h := Fintype.card_subtype_compl (fun S : Idx N r => S = Tstar)
    rw [Fintype.card_subtype_eq] at h
    exact h
  rw [hcard]

/-- **Equal compound column spans give equal straightened column spans.** -/
theorem span_straightened_eq_of_compound_span_eq {N r k : ℕ} (hrk : r + k = N) (hr : 1 ≤ r)
    (V V' : Matrix (Fin N) (Fin N) ℤ)
    (hV : V.det ≠ 0)
    (hV' : V'.det ≠ 0)
    (Tstar : Idx N r) (tSet : Set.powersetCard (Fin N) k)
    (ht : ((tSet : Set.powersetCard (Fin N) k) : Finset (Fin N)) = (↑Tstar)ᶜ)
    (heq : Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
              (fun T => ((Commons.LinearAlgebra.Matrix.compound r V) T S : ℚ))))
          = Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
              (fun T => ((Commons.LinearAlgebra.Matrix.compound r V') T S : ℚ))))) :
    Submodule.span ℚ ((fun j i => ((V i j : ℤ) : ℚ)) '' (↑tSet : Set (Fin N)))
      = Submodule.span ℚ ((fun j i => ((V' i j : ℤ) : ℚ)) '' (↑tSet : Set (Fin N))) := by
  have hVQ : (V.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [show (V.map (Int.castRingHom ℚ)).det = ((V.det : ℤ) : ℚ) from by
      rw [show V.map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix V from rfl]
      exact (RingHom.map_det (Int.castRingHom ℚ) V).symm]
    exact Int.cast_ne_zero.mpr hV
  have hVQ' : (V'.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [show (V'.map (Int.castRingHom ℚ)).det = ((V'.det : ℤ) : ℚ) from by
      rw [show V'.map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix V' from rfl]
      exact (RingHom.map_det (Int.castRingHom ℚ) V').symm]
    exact Int.cast_ne_zero.mpr hV'
  have hcol : ∀ W : Matrix (Fin N) (Fin N) ℤ,
      (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
        (fun T => ((Commons.LinearAlgebra.Matrix.compound r W) T S : ℚ))))
      = (Set.range (fun S : {S : Set.powersetCard (Fin N) r // S ≠ (Tstar : Set.powersetCard (Fin N) r)} =>
          compoundCol (W.map (Int.castRingHom ℚ)) S)) := by
    intro W
    ext v
    constructor
    · rintro ⟨S, rfl⟩
      refine ⟨⟨toPC S.1, fun h => S.2 (Subtype.ext
        (congrArg (fun x : Set.powersetCard (Fin N) r => (x : Finset (Fin N))) h))⟩, ?_⟩
      funext T
      exact (compound_map_intCast_rat W T S.1).symm
    · rintro ⟨S, rfl⟩
      refine ⟨⟨ofPC S.1, fun h => S.2 (Subtype.ext
        (congrArg (fun x : Idx N r => (x.1 : Finset (Fin N))) h))⟩, ?_⟩
      funext T
      exact compound_map_intCast_rat W T (ofPC S.1)
  rw [hcol V, hcol V'] at heq
  have h1 : (fun j : Fin N => fun i : Fin N => (V.map (Int.castRingHom ℚ)) i j)
      = fun j i => ((V i j : ℤ) : ℚ) := by
    funext j i
    simp [Matrix.map_apply]
  have h2 : (fun j : Fin N => fun i : Fin N => (V'.map (Int.castRingHom ℚ)) i j)
      = fun j i => ((V' i j : ℤ) : ℚ) := by
    funext j i
    simp [Matrix.map_apply]
  have hres := wedgeSpan_eq_of_compoundSpan_eq hrk (V.map (Int.castRingHom ℚ))
    (V'.map (Int.castRingHom ℚ)) hVQ hVQ' (Tstar : Set.powersetCard (Fin N) r) tSet ht heq
  rw [← h1, ← h2]
  exact hres

/-- **Case B of the real rank descent**: if infinitely many solutions have
`finrank (approxSpace (toC Mr) c ‖x‖) ≤ N - 2`, then general position is violated. -/
theorem lowCase_false (hN : 2 ≤ N) (Mr : Matrix (Fin N) (Fin N) ℝ) (hMr : Mr.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (Mr i j)) (c : Fin N → ℝ) (hc : ∑ i, c i < 0)
    {Y : Set (Fin N → ℤ)} (hgp : GenPos Y)
    (hb : ∀ x ∈ Y, ∀ i, ‖∑ k, toC Mr i k * (x k : ℂ)‖ ≤ ‖x‖ ^ (c i))
    (hlow : {x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) ≤ N - 2}.Infinite) : False := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hεpos : 0 < -(∑ i, c i) := by linarith
  have hdetC := toC_det_ne_zero Mr hMr
  have hind : LinearIndependent ℂ (toC Mr) := by
    have hunit : IsUnit (Matrix.of (toC Mr)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetC)
    have hrow : LinearIndependent ℂ (Matrix.of (toC Mr)).row :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr hunit
    simpa using hrow
  -- ## Step 1: a fixed rank `R ≤ N - 2` occurring infinitely often
  have hRex : ∃ R : ℕ, R ≤ N - 2 ∧
      ({x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = R} : Set (Fin N → ℤ)).Infinite := by
    by_contra hcon
    push_neg at hcon
    have hsub : {x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) ≤ N - 2} ⊆
        ⋃ R : Fin (N - 1), ({x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = R.val}
          : Set (Fin N → ℤ)) := by
      rintro x ⟨hxY, hxr⟩
      have hlt : Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) < N - 1 := by omega
      exact Set.mem_iUnion.mpr ⟨⟨_, hlt⟩, hxY, rfl⟩
    have hfin : (⋃ R : Fin (N - 1), ({x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = R.val}
          : Set (Fin N → ℤ))).Finite := by
      refine Set.finite_iUnion fun R => ?_
      exact hcon R.val (by have := R.2; omega)
    exact hlow (hfin.subset hsub)
  obtain ⟨R, hRle, hZRinf⟩ := hRex
  have hRltN : R < N := by omega
  -- `R ≥ 1` because the box contains the nonzero point `x`
  have hRpos : 1 ≤ R := by
    obtain ⟨x, hxY, hxr⟩ := hZRinf.nonempty
    have hx0 : x ≠ 0 := by
      intro hx0
      have hli := hgp {x} (fun y hy => by
          simp only [Finset.mem_coe, Finset.mem_singleton] at hy
          rw [hy]; exact hxY) (by simp only [Finset.card_singleton, Fintype.card_fin]; omega)
      exact (LinearIndependent.ne_zero ⟨x, Finset.mem_singleton_self x⟩ hli)
        (by rw [hx0]; rfl)
    have hmem : intCastVec x ∈ approxSpace (toC Mr) c ‖x‖ :=
      mem_approxSpace_of_mem_box (mem_approxBox_iff.mpr (hb x hxY))
    have hne : (⟨intCastVec x, hmem⟩ : approxSpace (toC Mr) c ‖x‖) ≠ 0 := by
      intro h
      exact hx0 (intCastVec_injective (congrArg Subtype.val h))
    haveI : Nontrivial ↥(approxSpace (toC Mr) c ‖x‖) := ⟨_, 0, hne⟩
    have h1 : 0 < Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) := Module.finrank_pos
    omega
  -- ## Step 2: the constants and the threshold for the per-`x` data
  obtain ⟨C0, hC0pos, hC0⟩ :=
    Commons.NumberTheory.DiophantineApproximation.graded_basis_real hN1 Mr hMr
  obtain ⟨Qlast, hQlast1, hQlast⟩ := lamS_last_ge hN (toC Mr) hind hdetC c hc
  set Qa : ℝ := max 2 (max Qlast 1) with hQadef
  have hQa2 : 2 ≤ Qa := le_max_left _ _
  have hQa1 : 1 ≤ Qa := by linarith
  have hQaQlast : Qlast ≤ Qa := le_trans (le_max_left _ _) (le_max_right _ _)
  -- ## Step 3: restrict to large norms
  set Z : Set (Fin N → ℤ) :=
    {x | x ∈ Y ∧ Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = R ∧ Qa ≤ ‖x‖} with hZdef
  have hZinf : Z.Infinite := by
    have hsmall : ({x : Fin N → ℤ | ¬ (Qa ≤ ‖x‖)} : Set (Fin N → ℤ)).Finite :=
      (Commons.Analysis.Normed.finite_bounded_int_vectors Qa).subset (fun x hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        exact le_of_lt (not_le.mp hx))
    have hsub : {x ∈ Y | Module.finrank ℚ (approxSpace (toC Mr) c ‖x‖) = R} ⊆
        Z ∪ {x : Fin N → ℤ | ¬ (Qa ≤ ‖x‖)} := by
      rintro x ⟨hxY, hxr⟩
      by_cases h : Qa ≤ ‖x‖
      · exact Or.inl ⟨hxY, hxr, h⟩
      · exact Or.inr h
    by_contra hcon
    rw [Set.not_infinite] at hcon
    exact hZRinf ((hcon.union hsmall).subset hsub)
  -- ## Step 4: the per-`x` data (realisers, straightening, gap index)
  have hXS : ∀ x ∈ Z, ∃ xs : Fin N → Fin N → ℤ, IsRealiserData Mr c x xs := by
    intro x hx
    obtain ⟨hxY, hxr, hxQ⟩ := hx
    have hQ1 : 1 ≤ ‖x‖ := le_trans hQa1 hxQ
    obtain ⟨xs, h1, h2, h3, h4⟩ :=
      Commons.GeometryOfNumbers.SuccessiveMinima.exists_successiveMinima_realisers
        hN1 (toC Mr) hdetC ‖x‖ hQ1 c (lamS (toC Mr) c ‖x‖) (fun j _ => rfl)
    exact ⟨xs, h1, h2, h3, h4⟩
  let xs : (Fin N → ℤ) → Fin N → Fin N → ℤ := fun x =>
    if h : x ∈ Z then Classical.choose (hXS x h) else 0
  have hXS_spec : ∀ (x : Fin N → ℤ) (hx : x ∈ Z), IsRealiserData Mr c x (xs x) := by
    intro x hx
    rw [show xs x = Classical.choose (hXS x hx) from dif_pos hx]
    exact Classical.choose_spec (hXS x hx)
  have hXStr : ∀ (x : Fin N → ℤ) (hx : x ∈ Z),
      ∃ ξ : Fin N → Fin N → ℤ, ∃ π : Equiv.Perm (Fin N),
        IsStraightening Mr c C0 x (xs x) ξ π := by
    intro x hx
    have hX := hXS_spec x hx
    obtain ⟨hxY, hxr, hxQ⟩ := hx
    have hQ1 : 1 ≤ ‖x‖ := le_trans hQa1 hxQ
    have hQpos : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) (le_trans hQa2 hxQ)
    obtain ⟨h1, h2, h3, h4⟩ := hX
    obtain ⟨ξ, π, hξ0, hξb⟩ := hC0 ‖x‖ hQ1 c (fun t : Fin N => lamS (toC Mr) c ‖x‖ t.val) (xs x)
      (fun j => lamS_pos hN1 (toC Mr) hdetC c hQpos j.isLt)
      (fun i j hij => lamS_mono (toC Mr) c hQpos (by exact hij) j.isLt)
      h1 h2 (fun j i => by rw [← norm_toC_apply]; exact h3 j i)
      (fun j t ht htj y hy => h4 j t ht htj y (fun i => by rw [norm_toC_apply]; exact hy i))
    exact ⟨ξ, π, hξ0, hξb⟩
  let xi : (Fin N → ℤ) → Fin N → Fin N → ℤ := fun x =>
    if h : x ∈ Z then Classical.choose (hXStr x h) else 0
  have hxi_spec : ∀ (x : Fin N → ℤ) (hx : x ∈ Z),
      ∃ π : Equiv.Perm (Fin N), IsStraightening Mr c C0 x (xs x) (xi x) π := by
    intro x hx
    rw [show xi x = Classical.choose (hXStr x hx) from dif_pos hx]
    exact Classical.choose_spec (hXStr x hx)
  let pic : (Fin N → ℤ) → Equiv.Perm (Fin N) := fun x =>
    if h : x ∈ Z then Classical.choose (hxi_spec x h) else 1
  have hpic_spec : ∀ (x : Fin N → ℤ) (hx : x ∈ Z),
      IsStraightening Mr c C0 x (xs x) (xi x) (pic x) := by
    intro x hx
    rw [show pic x = Classical.choose (hxi_spec x hx) from dif_pos hx]
    exact Classical.choose_spec (hxi_spec x hx)
  have hXGap : ∀ (x : Fin N → ℤ) (hx : x ∈ Z), ∃ k : Fin N, IsGapData Mr c R x k := by
    intro x hx
    obtain ⟨hxY, hxr, hxQ⟩ := hx
    have hQ1 : 1 ≤ ‖x‖ := le_trans hQa1 hxQ
    have hQgt : 1 < ‖x‖ := lt_of_lt_of_le (by norm_num) (le_trans hQa2 hxQ)
    have hRle1 : lamS (toC Mr) c ‖x‖ (R - 1) ≤ 1 :=
      (lamS_le_one_iff hN1 (toC Mr) hdetC c hQ1 (R := R) hxr.symm (i := R - 1) (by omega)).mpr
        (by omega)
    have hgapN : ‖x‖ ^ (-(∑ i, c i) / (2 * (N : ℝ))) ≤ lamS (toC Mr) c ‖x‖ (N - 1) :=
      hQlast ‖x‖ (le_trans hQaQlast hxQ)
    obtain ⟨k, hkR, hkN, hkgap⟩ :=
      exists_gap_index_lamS hN1 (toC Mr) hdetC c hc hQgt hRltN hRle1 hgapN
    exact ⟨⟨k, hkN⟩, hkR, hkN, hkgap⟩
  let kf : (Fin N → ℤ) → Fin N := fun x =>
    if h : x ∈ Z then Classical.choose (hXGap x h) else ⟨0, hNpos⟩
  have hkf_spec : ∀ (x : Fin N → ℤ) (hx : x ∈ Z), IsGapData Mr c R x (kf x) := by
    intro x hx
    rw [show kf x = Classical.choose (hXGap x hx) from dif_pos hx]
    exact Classical.choose_spec (hXGap x hx)
  -- ## Step 5: pigeonhole the gap index and the permutation
  obtain ⟨b, hbinf⟩ := Commons.Combinatorics.infinite_fiber (s := Z) hZinf
    (fun x : Fin N → ℤ => (kf x, pic x))
  set Z₁ : Set (Fin N → ℤ) := Z ∩ (fun x : Fin N → ℤ => (kf x, pic x)) ⁻¹' {b} with hZ₁def
  have hZ₁inf : Z₁.Infinite := hbinf
  have hZ₁Z : ∀ x ∈ Z₁, x ∈ Z := fun x hx => hx.1
  have hZ₁key : ∀ x ∈ Z₁, (kf x, pic x) = b := fun x hx => hx.2
  set k : ℕ := b.1.val with hkdef
  set π : Equiv.Perm (Fin N) := b.2 with hpidef
  have hklt : k < N := b.1.isLt
  have hkfix : ∀ x ∈ Z₁, (kf x).val = k := by
    intro x hx
    have h : kf x = b.1 := congrArg Prod.fst (hZ₁key x hx)
    rw [h]
  have hpifix : ∀ x ∈ Z₁, pic x = π := by
    intro x hx
    have h : pic x = b.2 := congrArg Prod.snd (hZ₁key x hx)
    rw [h]
  have hRk : R ≤ k := by
    obtain ⟨x, hx⟩ := hZ₁inf.nonempty
    have h := (hkf_spec x (hZ₁Z x hx)).1
    rw [hkfix x hx] at h
    exact h

  -- ## Step 6: the parameters fixed by the pigeonhole
  set r : ℕ := N - k with hrdef
  have hr1 : 1 ≤ r := by omega
  have hrN : r ≤ N := by omega
  have hrk : r + k = N := by omega
  have hrle1 : r ≤ N - 1 := by omega
  set Tstar : Idx N r := ⟨tailSet N k, by rw [tailSet_card (le_of_lt hklt)]⟩ with hTstardef
  set tSet : Set.powersetCard (Fin N) k :=
    ⟨Finset.univ.filter (fun j : Fin N => j.val < k),
      card_filter_val_lt (le_of_lt hklt)⟩ with htSetdef
  have htSet : ((tSet : Set.powersetCard (Fin N) k) : Finset (Fin N)) = (↑Tstar)ᶜ := by
    show (Finset.univ.filter fun j : Fin N => j.val < k) = (↑Tstar)ᶜ
    rw [show (↑Tstar : Finset (Fin N)) = tailSet N k from rfl, tailSet]
    ext j
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  -- the cardinality of the compound index type
  have hcard_eq : Fintype.card (Idx N r) = Nat.choose N r := by
    rw [Fintype.card_eq_nat_card]
    simpa using Set.powersetCard.card (Fin N) r
  have hcard2 : 2 ≤ Fintype.card (Idx N r) := by
    rw [hcard_eq]
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    have hN : (N - 1) + 1 = N := by omega
    calc 2 ≤ (N - 1).choose s + (N - 1).choose (s + 1) := by
          have ha : 0 < Nat.choose (N - 1) s := Nat.choose_pos (by omega)
          have hb : 0 < Nat.choose (N - 1) (s + 1) := Nat.choose_pos (by omega)
          omega
      _ = N.choose r := by
        rw [hs, ← Nat.choose_succ_succ (N - 1) s, show (N - 1).succ = N from by omega]
  -- the exponents and constants
  set ε0 : ℝ := -(∑ i, c i) / (2 * (N : ℝ) * ((N : ℝ) - R)) with hε0def
  have hNR2 : (2 : ℝ) ≤ (N : ℝ) - R := by
    have h1 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ N)]; norm_num
    have h2 : (R : ℝ) ≤ ((N - 2 : ℕ) : ℝ) := Nat.cast_le.mpr hRle
    rw [h1] at h2; linarith
  have hNpos' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hε0pos : 0 < ε0 := by
    rw [hε0def]
    exact div_pos hεpos (by nlinarith)
  have hchoose_pos : (0 : ℝ) < (Nat.choose N r : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hrN)
  set γ : ℝ := ε0 / (4 * (Nat.choose N r : ℝ)) with hγdef
  have hγpos : 0 < γ := by rw [hγdef]; positivity
  have hγnn : 0 ≤ γ := le_of_lt hγpos
  have hgamma : (Nat.choose N r : ℝ) * γ ≤ ε0 / 4 := by
    rw [hγdef]
    have hne : (Nat.choose N r : ℝ) ≠ 0 := ne_of_gt hchoose_pos
    have key : (Nat.choose N r : ℝ) * (ε0 / (4 * (Nat.choose N r : ℝ))) = ε0 / 4 := by
      field_simp
    exact le_of_eq key
  set Kc : ℝ := (Nat.factorial r : ℝ) * C0 ^ r with hKcdef
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  set M' : Matrix (Fin N) (Fin N) ℝ := Mr.submatrix (⇑π) id with hM'def
  have hM'det : M'.det ≠ 0 := by
    have hsign : (((Equiv.Perm.sign π : ℤˣ) : ℤ) : ℝ) ≠ 0 := by
      have h1 : IsUnit (((Equiv.Perm.sign π : ℤˣ) : ℤ)) := (Equiv.Perm.sign π).isUnit
      exact isUnit_iff_ne_zero.mp (h1.map (Int.castRingHom ℝ))
    rw [hM'def, Matrix.det_permute]
    exact mul_ne_zero hsign hMr
  -- the uniform bounds on the successive minima
  obtain ⟨K0, hK0ge1, hK0⟩ :=
    Commons.GeometryOfNumbers.SuccessiveMinima.box_bounds_uniform hN1 (toC Mr) hdetC c
  have hK0pos : 0 < K0 := lt_of_lt_of_le one_pos hK0ge1
  -- the volume constant
  obtain ⟨D, hDpos, hD⟩ :=
    Commons.GeometryOfNumbers.Box.prod_successiveMinimum_box_le_real hN1 (toC Mr) hdetC
      (fun i j => ⟨Mr i j, rfl⟩)
  set Ac : ℝ := Kc + Kc⁻¹ with hAcdef
  have hAc1 : 1 ≤ Ac := by
    rw [hAcdef]
    have h : 0 ≤ (Kc - 1) ^ 2 / Kc := div_nonneg (sq_nonneg _) hKcpos.le
    have h2 : (Kc - 1) ^ 2 / Kc = Kc + Kc⁻¹ - 2 := by
      field_simp
      ring
    linarith
  have hAclog : 0 ≤ Real.log Ac := Real.log_nonneg hAc1
  set B : ℝ := Real.log Ac / Real.log 2 + K0 * r + 2 * K0 + γ with hBdef
  have hBnn : 0 ≤ B := by
    rw [hBdef]
    have h0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h1 : 0 ≤ Real.log Ac / Real.log 2 := div_nonneg hAclog h0.le
    have h2 : 0 ≤ K0 * r := mul_nonneg hK0pos.le (Nat.cast_nonneg r)
    have h3 : 0 ≤ (2 : ℝ) * K0 := by linarith
    linarith
  -- the exponent function
  set d : (Fin N → ℤ) → Set.powersetCard (Fin N) r → ℝ := fun x T =>
    (Real.log (Kc * ∏ t ∈ (T : Finset (Fin N)), lamS (toC Mr) c ‖x‖ t.val) +
      (if (T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)
        then Real.log (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) else 0))
      / Real.log ‖x‖ + γ with hddef
  have hdbound : ∀ (x : Fin N → ℤ), x ∈ Z₁ → ∀ T : Set.powersetCard (Fin N) r,
      |d x T| ≤ B := by
    intro x hx T
    have hxQ : Qa ≤ ‖x‖ := (hZ₁Z x hx).2.2
    have hQ2 : 2 ≤ ‖x‖ := le_trans hQa2 hxQ
    have h : |(Real.log (Kc * ∏ t ∈ (T : Finset (Fin N)), lamS (toC Mr) c ‖x‖ t.val) +
        (if (T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val) then
          Real.log (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) else 0))
        / Real.log ‖x‖ + γ| ≤ B := by
      rw [hBdef, hAcdef]
      exact Commons.Analysis.Log.log_box_bound (N := N) (r := r) (k := k) hklt hK0pos hKcpos hγnn
        hQ2 (fun j => lamS (toC Mr) c ‖x‖ j) (fun j hj => hK0 ‖x‖ hQ2 j hj)
        (T : Finset (Fin N)) T.2
    rw [hddef]
    exact h
  -- ## Step 7: the grid refinement (finitely many exponent vectors)
  obtain ⟨dbar, hdbarB, hβinf⟩ := Commons.Combinatorics.grid_approx_infinite_fintype
    (fun (x : ↥Z₁) (T : Set.powersetCard (Fin N) r) => d x.1 T) B hBnn γ hγpos
    (Set.univ : Set ↥Z₁) (Set.infinite_univ_iff.mpr (Set.infinite_coe_iff.mpr hZ₁inf))
    (fun i _ T => hdbound i.1 i.2 T)
  set β : Set ↥Z₁ := {i | ∀ T : Set.powersetCard (Fin N) r,
      d i.1 T ≤ dbar T ∧ dbar T ≤ d i.1 T + γ} with hβdef
  have hβinf' : β.Infinite := by simpa [hβdef] using hβinf
  set Z₂ : Set (Fin N → ℤ) := Subtype.val '' β with hZ₂def
  have hZ₂inf : Z₂.Infinite := hβinf'.image Subtype.val_injective.injOn
  set xbar : Set.powersetCard (Fin N) r → ℝ := fun T =>
    (∑ t ∈ (T : Finset (Fin N)), c (π t)) + dbar T with hxbardef
  -- ## Step 8: the exponent sum is negative
  have hbigex : ∃ Qb : ℝ, ∀ Q : ℝ, Qb ≤ Q →
      (Nat.choose N r : ℝ) * Real.log Kc + (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log D
        ≤ ε0 / 4 * Real.log Q := by
    have h1 : Filter.Tendsto (fun Q : ℝ => Real.log Q) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop
    have h2 := h1.const_mul_atTop (show (0:ℝ) < ε0 / 4 by linarith)
    exact Filter.eventually_atTop.mp (h2.eventually_ge_atTop _)
  obtain ⟨Qb, hQb⟩ := hbigex
  have hxbarsum : ∑ T : Set.powersetCard (Fin N) r, xbar T < 0 := by
    have hx0ex : ∃ x ∈ Z₂, max Qb Qa ≤ ‖x‖ := by
      by_contra hcon
      push_neg at hcon
      have hsmall : ({x : Fin N → ℤ | ‖x‖ < max Qb Qa} : Set (Fin N → ℤ)).Finite :=
        (Commons.Analysis.Normed.finite_bounded_int_vectors (max Qb Qa)).subset
          (fun x hx => by
            rw [Set.mem_ofPred_eq] at hx ⊢
            exact le_of_lt hx)
      exact hZ₂inf (hsmall.subset fun x hx => hcon x hx)
    obtain ⟨x0, hx0mem, hx0Q⟩ := hx0ex
    obtain ⟨i0, hi0β, hi0val⟩ := hx0mem
    have hx0Z₁ : x0 ∈ Z₁ := hi0val ▸ i0.2
    have hx0Q2 : 2 ≤ ‖x0‖ := le_trans hQa2 (le_trans (le_max_right _ _) hx0Q)
    have hQbbig : (Nat.choose N r : ℝ) * Real.log Kc +
        (Nat.choose (N - 1) (r - 1) : ℝ) * Real.log D ≤ ε0 / 4 * Real.log ‖x0‖ :=
      hQb ‖x0‖ (le_trans (le_max_left _ _) hx0Q)
    have hx0pos : 0 < ‖x0‖ := lt_of_lt_of_le (by norm_num) hx0Q2
    have hprod0 : ∏ j : Fin N, lamS (toC Mr) c ‖x0‖ j.val ≤ D * ‖x0‖ ^ (-(∑ i, c i)) :=
      hD ‖x0‖ (by linarith) c hc (fun j : Fin N => lamS (toC Mr) c ‖x0‖ j.val) (fun j => rfl)
    have hgap0 : 0 < lamS (toC Mr) c ‖x0‖ (k - 1) / lamS (toC Mr) c ‖x0‖ k :=
      div_pos (lamS_pos hN1 (toC Mr) hdetC c hx0pos (by omega))
        (lamS_pos hN1 (toC Mr) hdetC c hx0pos hklt)
    have hgaple : lamS (toC Mr) c ‖x0‖ (k - 1) / lamS (toC Mr) c ‖x0‖ k
        ≤ ‖x0‖ ^ (-ε0) := by
      have h := (hkf_spec x0 (hZ₁Z x0 hx0Z₁)).2.2
      rw [hkfix x0 hx0Z₁] at h
      rwa [hε0def]
    have hkey := wedge_exponent_sum_neg_gen (N := N) (r := r) (k := k) hrk hr1 c π
      (fun j => lamS (toC Mr) c ‖x0‖ j)
      (fun j hj => lamS_pos hN1 (toC Mr) hdetC c hx0pos hj)
      hx0Q2 hDpos hprod0 hgap0 hε0pos hgaple Kc γ hKcpos hγnn hQbbig hgamma
    have hpt : ∀ T : Set.powersetCard (Fin N) r,
        xbar T ≤ (∑ t ∈ (T : Finset (Fin N)), c (π t)) + d x0 T + γ := by
      intro T
      have h1 : dbar T ≤ d i0.1 T + γ := (hi0β T).2
      have h1' : dbar T ≤ d x0 T + γ := by rw [← hi0val]; exact h1
      have h2 : xbar T = (∑ t ∈ (T : Finset (Fin N)), c (π t)) + dbar T := rfl
      rw [h2]; linarith
    calc ∑ T : Set.powersetCard (Fin N) r, xbar T
        ≤ ∑ T : Set.powersetCard (Fin N) r,
            ((∑ t ∈ (T : Finset (Fin N)), c (π t)) + d x0 T + γ) :=
          Finset.sum_le_sum fun T _ => hpt T
      _ = (∑ T : Set.powersetCard (Fin N) r,
            ((∑ t ∈ (T : Finset (Fin N)), c (π t)) + d x0 T))
          + (Fintype.card (Set.powersetCard (Fin N) r) : ℝ) * γ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ ≤ -ε0 / 2 + (Nat.choose N r : ℝ) * γ := by
          have hcard : (Fintype.card (Set.powersetCard (Fin N) r) : ℝ) = (Nat.choose N r : ℝ) := by
            rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]
          rw [hcard]
          linarith
      _ < 0 := by linarith
  have hxbarsumI : ∑ T : Idx N r, xbar T < 0 := by
    rw [← sum_subtype_eq_sum_powersetCard (N := N) (r := r) xbar]
    exact hxbarsum
  -- ## Step 9: the remaining thresholds
  obtain ⟨Qcp, hQcp1, hQcp⟩ := finrank_compBox_le M' hM'det xbar hxbarsumI hcard2
  have hdetCp : (Matrix.of (toC (Commons.LinearAlgebra.Matrix.compound r M'))).det ≠ 0 :=
    toC_det_ne_zero (Commons.LinearAlgebra.Matrix.compound r M')
      (Commons.LinearAlgebra.Matrix.det_compound_ne_zero M' hM'det)
  have halgCp : ∀ i j, IsAlgebraic ℚ ((toC (Commons.LinearAlgebra.Matrix.compound r M')) i j) := by
    intro i j
    have h1 : IsAlgebraic ℚ ((Commons.LinearAlgebra.Matrix.compound r M') i j) :=
      Commons.LinearAlgebra.Matrix.isAlgebraic_det
        (M'.submatrix (i.1.orderEmbOfFin i.2) (j.1.orderEmbOfFin j.2)) (fun a b => halg _ _)
    have h2 : IsAlgebraic ℚ (algebraMap ℝ ℂ ((Commons.LinearAlgebra.Matrix.compound r M') i j)) :=
      IsAlgebraic.algebraMap h1
    exact h2
  obtain ⟨Qs, hQs1, Sset, hSfin, hS⟩ := maximal_rank_finiteness_spaces
    (toC (Commons.LinearAlgebra.Matrix.compound r M')) hdetCp halgCp xbar hxbarsumI
  set Qall : ℝ := max (max Qcp Qs) (max Qb Qa) with hQalldef
  set Z₄ : Set (Fin N → ℤ) := Z₂ ∩ {x | Qall ≤ ‖x‖} with hZ₄def
  have hZ₄inf : Z₄.Infinite := by
    have hsmall : ({x : Fin N → ℤ | ‖x‖ < Qall} : Set (Fin N → ℤ)).Finite :=
      (Commons.Analysis.Normed.finite_bounded_int_vectors Qall).subset
        (fun x hx => by
          rw [Set.mem_ofPred_eq] at hx ⊢
          exact le_of_lt hx)
    have hsub : Z₂ ⊆ Z₄ ∪ {x : Fin N → ℤ | ‖x‖ < Qall} := by
      intro x hx
      by_cases h : Qall ≤ ‖x‖
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
    by_contra hcon
    rw [Set.not_infinite] at hcon
    exact hZ₂inf ((hcon.union hsmall).subset hsub)

  -- ## Step 10: the straightened matrices and the final contradiction
  set Vmat : (Fin N → ℤ) → Matrix (Fin N) (Fin N) ℤ := fun x i j =>
    xs x j i + ∑ p : Fin N, xs x p i * xi x p j with hVmatdef
  have hZ₄Z₁ : ∀ x ∈ Z₄, x ∈ Z₁ := by
    intro x hx
    obtain ⟨i0, hi0β, hi0val⟩ := hx.1
    exact hi0val ▸ i0.2
  have hZ₄Y : ∀ x ∈ Z₄, x ∈ Y := fun x hx => (hZ₁Z x (hZ₄Z₁ x hx)).1
  have hZ₄Qall : ∀ x ∈ Z₄, Qall ≤ ‖x‖ := by
    intro x hx
    have h := hx.2
    rw [Set.mem_ofPred_eq] at h
    exact h
  have hgrid : ∀ x ∈ Z₄, ∀ T : Idx N r, d x T ≤ dbar T ∧ dbar T ≤ d x T + γ := by
    intro x hx T
    obtain ⟨i0, hi0β, hi0val⟩ := hx.1
    have h1 := (hi0β T).1
    have h2 := (hi0β T).2
    rw [hi0val] at h1 h2
    exact ⟨h1, h2⟩
  -- the straightened matrices are invertible
  have hVdet : ∀ x ∈ Z₄, (Vmat x).det ≠ 0 := by
    intro x hx
    obtain ⟨hne, hli, hbnd, hgen⟩ := hXS_spec x (hZ₁Z x (hZ₄Z₁ x hx))
    obtain ⟨hξ0, hξb⟩ := hpic_spec x (hZ₁Z x (hZ₄Z₁ x hx))
    exact Commons.LinearAlgebra.Matrix.det_unitriangular_comb (xs x) (xi x) hξ0 hli
  -- the wedge vectors lie in the compound box
  have hmem : ∀ x ∈ Z₄, ∀ S : Idx N r, S ≠ Tstar →
      (fun S' => (Commons.LinearAlgebra.Matrix.compound r (Vmat x)) S' S) ∈ compBox r M' xbar ‖x‖ := by
    intro x hx S hS
    have hxZ : x ∈ Z := hZ₁Z x (hZ₄Z₁ x hx)
    obtain ⟨hne, hli, hbnd, hgen⟩ := hXS_spec x hxZ
    obtain ⟨hξ0, hξb⟩ := hpic_spec x hxZ
    rw [hpifix x (hZ₄Z₁ x hx)] at hξb
    have hxQ : Qa ≤ ‖x‖ := hxZ.2.2
    have hQ2 : 2 ≤ ‖x‖ := le_trans hQa2 hxQ
    have hQpos : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num) hQ2
    have hQ1 : 1 < ‖x‖ := lt_of_lt_of_le one_lt_two hQ2
    set lamF : Fin N → ℝ := fun s => lamS (toC Mr) c ‖x‖ s.val with hlamFdef
    set cF : Fin N → ℝ := fun s => c (π s) with hcFdef
    have hlamFpos : ∀ s : Fin N, 0 < lamF s := fun s =>
      lamS_pos hN1 (toC Mr) hdetC c hQpos s.isLt
    -- the straightening bound in the `lamF`/`cF` notation
    have hbnd' : ∀ t j : Fin N,
        |∑ i, M' t i * ((Vmat x i j : ℤ) : ℝ)| ≤ C0 * min (lamF t) (lamF j) * ‖x‖ ^ (cF t) := by
      intro t j
      have h1 : (∑ i : Fin N, M' t i * ((Vmat x i j : ℤ) : ℝ))
          = ∑ k, Mr (π t) k * ((xs x j k : ℝ)
              + ∑ i : Fin N, ((xi x i j : ℤ) : ℝ) * (xs x i k : ℝ)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hsum : (∑ p : Fin N, (xs x p i : ℝ) * (xi x p j : ℝ))
            = ∑ p : Fin N, (xi x p j : ℝ) * (xs x p i : ℝ) :=
          Finset.sum_congr rfl fun p _ => by ring
        rw [hM'def, Matrix.submatrix_apply, hVmatdef]
        simp only [id_eq]
        push_cast
        conv_lhs => rw [hsum]
      rw [h1]
      exact hξb t j
    -- the lower bound for the indices of `Tstar`
    have hlowmem : ∀ a : Fin r, k ≤ (Tstar.1.orderEmbOfFin Tstar.2 a).val := by
      intro a
      have hmem' : Tstar.1.orderEmbOfFin Tstar.2 a ∈ tailSet N k :=
        Finset.orderEmbOfFin_mem _ _ _
      exact (Finset.mem_filter.mp hmem').2
    have hTlow : ∀ a : Fin r, lamS (toC Mr) c ‖x‖ k ≤ lamF (Tstar.1.orderEmbOfFin Tstar.2 a) :=
      fun a => lamS_mono (toC Mr) c hQpos (hlowmem a)
        (Tstar.1.orderEmbOfFin Tstar.2 a).isLt
    have hShigh : ∀ S : Idx N r, S ≠ Tstar → ∃ s ∈ S.1,
        lamF s ≤ lamS (toC Mr) c ‖x‖ (k - 1) := by
      intro S hS
      by_contra hcon
      push_neg at hcon
      have hsub : S.1 ⊆ Tstar.1 := by
        intro s hs
        rw [hTstardef]
        simp only [tailSet, Finset.mem_filter, Finset.mem_univ, true_and]
        by_contra hlt
        push_neg at hlt
        exact (not_lt.mpr (lamS_mono (toC Mr) c hQpos (by omega) (by omega))) (hcon s hs)
      exact hS (Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [S.2, Tstar.2])))
    -- the product and sum bookkeeping
    have hprod : ∀ T : Idx N r,
        (∏ t ∈ (T : Finset (Fin N)), lamS (toC Mr) c ‖x‖ t.val)
          = ∏ a : Fin r, lamF (T.1.orderEmbOfFin T.2 a) := by
      intro T
      rw [show (∏ t ∈ (T : Finset (Fin N)), lamS (toC Mr) c ‖x‖ t.val)
          = ∏ t ∈ (T : Finset (Fin N)), lamF t from
        Finset.prod_congr rfl fun t _ => (show lamF t = lamS (toC Mr) c ‖x‖ t.val from rfl)]
      exact (prod_orderEmbOfFin_eq_prod T.1 T.2 lamF).symm
    have hsumid : ∀ T : Idx N r,
        (∑ t ∈ (T : Finset (Fin N)), c (π t)) = ∑ a : Fin r, cF (T.1.orderEmbOfFin T.2 a) := by
      intro T
      rw [show (∑ t ∈ (T : Finset (Fin N)), c (π t))
          = ∑ t ∈ (T : Finset (Fin N)), cF t from
        Finset.sum_congr rfl fun t _ => (show cF t = c (π t) from rfl)]
      exact (sum_orderEmbOfFin_eq_sum T.1 T.2 cF).symm
    have hx1 : ∀ T : Idx N r, T ≠ Tstar →
        (∑ a : Fin r, cF (T.1.orderEmbOfFin T.2 a)) +
          Real.log (Nat.factorial r * C0 ^ r *
            ∏ a : Fin r, lamF (T.1.orderEmbOfFin T.2 a)) / Real.log ‖x‖ ≤ xbar T := by
      intro T hT
      have hdb := (hgrid x hx T).1
      have hif : ¬ ((T : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val)) := by
        intro h
        exact hT (Subtype.ext h)
      have hd : d x T = Real.log (Nat.factorial r * C0 ^ r *
            ∏ a : Fin r, lamF (T.1.orderEmbOfFin T.2 a)) / Real.log ‖x‖ + γ := by
        rw [hddef]
        dsimp only
        rw [if_neg hif, add_zero, hprod T, hKcdef]
      rw [hd] at hdb
      have hxb : xbar T = (∑ t ∈ (T : Finset (Fin N)), c (π t)) + dbar T := rfl
      rw [hxb, hsumid T]
      linarith
    have hx2 : (∑ a : Fin r, cF (Tstar.1.orderEmbOfFin Tstar.2 a)) +
        Real.log (Nat.factorial r * C0 ^ r *
          (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) *
          ∏ a : Fin r, lamF (Tstar.1.orderEmbOfFin Tstar.2 a)) / Real.log ‖x‖ ≤ xbar Tstar := by
      have hdb := (hgrid x hx Tstar).1
      have hif : (Tstar : Finset (Fin N)) = Finset.univ.filter (fun t : Fin N => k ≤ t.val) := rfl
      have hgap0 : 0 < lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k :=
        div_pos (lamS_pos hN1 (toC Mr) hdetC c hQpos (by omega))
          (lamS_pos hN1 (toC Mr) hdetC c hQpos hklt)
      have hPpos : 0 < ∏ a : Fin r, lamF (Tstar.1.orderEmbOfFin Tstar.2 a) :=
        Finset.prod_pos fun a _ => hlamFpos _
      have hlog : Real.log (Nat.factorial r * C0 ^ r *
            (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) *
            ∏ a : Fin r, lamF (Tstar.1.orderEmbOfFin Tstar.2 a))
          = Real.log ((Nat.factorial r : ℝ) * C0 ^ r *
              ∏ a : Fin r, lamF (Tstar.1.orderEmbOfFin Tstar.2 a))
            + Real.log (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) := by
        rw [show Nat.factorial r * C0 ^ r *
            (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) *
            ∏ a : Fin r, lamF (Tstar.1.orderEmbOfFin Tstar.2 a)
            = ((Nat.factorial r : ℝ) * C0 ^ r *
                ∏ a : Fin r, lamF (Tstar.1.orderEmbOfFin Tstar.2 a)) *
              (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) from by ring]
        rw [Real.log_mul (ne_of_gt (mul_pos (mul_pos (by positivity) (pow_pos hC0pos r)) hPpos))
          (ne_of_gt hgap0)]
      have hd : d x Tstar = Real.log (Nat.factorial r * C0 ^ r *
            (lamS (toC Mr) c ‖x‖ (k - 1) / lamS (toC Mr) c ‖x‖ k) *
            ∏ a : Fin r, lamF (Tstar.1.orderEmbOfFin Tstar.2 a)) / Real.log ‖x‖ + γ := by
        rw [hddef]
        dsimp only
        rw [if_pos hif, hprod Tstar, hKcdef, ← hlog]
      rw [hd] at hdb
      have hxb : xbar Tstar = (∑ t ∈ (Tstar : Finset (Fin N)), c (π t)) + dbar Tstar := rfl
      rw [hxb, hsumid Tstar]
      linarith
    exact wedgeVec_mem_box M' (Vmat x) lamF cF hQ1 hC0pos hlamFpos hbnd'
      Tstar (lamS (toC Mr) c ‖x‖ k) (lamS (toC Mr) c ‖x‖ (k - 1))
      (lamS_pos hN1 (toC Mr) hdetC c hQpos hklt)
      (lamS_pos hN1 (toC Mr) hdetC c hQpos (by omega))
      hTlow hShigh xbar hx1 hx2 S hS
  -- ## Step 11: the rank of the compound box
  have hVspan : ∀ x ∈ Z₄,
      approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M')) xbar ‖x‖
        = Submodule.span ℚ (Set.range (fun S : {S : Idx N r // S ≠ Tstar} =>
            (fun T => ((Commons.LinearAlgebra.Matrix.compound r (Vmat x)) T S : ℚ)))) ∧
      Module.finrank ℚ (approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M')) xbar ‖x‖)
        = Fintype.card (Idx N r) - 1 := by
    intro x hx
    exact approxSpace_compound_eq_span_cols M' hM'det (Vmat x) xbar hxbarsumI hcard2 (hVdet x hx)
      Tstar Qcp hQcp1 hQcp ‖x‖
      (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (hZ₄Qall x hx)) (hmem x hx)
  have hVmemS : ∀ x ∈ Z₄,
      approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M')) xbar ‖x‖ ∈ Sset := by
    intro x hx
    refine hS ‖x‖ (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (hZ₄Qall x hx)) ?_
    exact (hVspan x hx).2
  -- ## Step 12: the finiteness of the spaces
  set Wf : (Fin N → ℤ) → Submodule ℚ (Fin N → ℚ) := fun x => Submodule.span ℚ
    ((fun j i => ((Vmat x i j : ℤ) : ℚ)) '' (↑tSet : Set (Fin N))) with hWfdef
  -- `Wf` is the span of the straightened columns
  have hWconv : ∀ x ∈ Z₄, Wf x = Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < k} =>
      fun i => ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
        ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ))) := by
    intro x hx
    have hset : ((fun j i => ((Vmat x i j : ℤ) : ℚ)) '' (↑tSet : Set (Fin N)))
        = Set.range (fun j : {j : Fin N // j.val < k} =>
            fun i => ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
              ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ)) := by
      ext v
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hj' : j.val < k :=
          (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
        refine ⟨⟨j, hj'⟩, ?_⟩
        funext i
        show ((xs x j i : ℤ) : ℚ) + ∑ p : Fin N,
            ((xs x p i : ℤ) : ℚ) * ((xi x p j : ℤ) : ℚ) = ((Vmat x i j : ℤ) : ℚ)
        rw [hVmatdef]
        push_cast
        ring
      · rintro ⟨j, rfl⟩
        refine ⟨j.1, ?_, ?_⟩
        · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩)
        · funext i
          show ((Vmat x i j.1 : ℤ) : ℚ) = ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
              ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ)
          rw [hVmatdef]
          push_cast
          ring
    show Submodule.span ℚ ((fun j i => ((Vmat x i j : ℤ) : ℚ)) '' (↑tSet : Set (Fin N)))
      = Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < k} =>
          fun i => ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
            ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ)))
    rw [hset]
  -- the space of a solution contains the solution
  have hmemW : ∀ x ∈ Z₄, intCastVec x ∈ Wf x := by
    intro x hx
    have hxZ : x ∈ Z := hZ₁Z x (hZ₄Z₁ x hx)
    obtain ⟨hne, hli, hbnd, hgen⟩ := hXS_spec x hxZ
    obtain ⟨hξ0, hξb⟩ := hpic_spec x hxZ
    have hxQ : Qa ≤ ‖x‖ := hxZ.2.2
    have hQ1 : 1 ≤ ‖x‖ := le_trans hQa1 hxQ
    have hspanR := boxT_span_eq_realisers hN1 (toC Mr) hdetC c hQ1 (xs x) hbnd hgen
      hxZ.2.1.symm hRltN
    have h1 : intCastVec x ∈ Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < R} =>
        fun i => ((xs x j.1 i : ℤ) : ℚ))) := by
      have h2 : intCastVec x ∈ approxSpace (toC Mr) c ‖x‖ :=
        mem_approxSpace_of_mem_box (mem_approxBox_iff.mpr (hb x hxZ.1))
      rwa [hspanR] at h2
    have h2 : Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < R} =>
        fun i => ((xs x j.1 i : ℤ) : ℚ)))
        ≤ Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < k} =>
        fun i => ((xs x j.1 i : ℤ) : ℚ))) := by
      rw [Submodule.span_le]
      rintro v ⟨j, rfl⟩
      exact Submodule.subset_span ⟨⟨j.1, lt_of_lt_of_le j.2 hRk⟩, rfl⟩
    have h3 := Commons.LinearAlgebra.Matrix.span_le_span_straightened (m := k) (xs x) (xi x) hξ0
    rw [hWconv x hx]
    exact h3 (h2 h1)
  -- the spaces `Wf x` are proper
  have hWne : ∀ x ∈ Z₄, Wf x ≠ ⊤ := by
    intro x hx
    have hVQ : ((Vmat x).map (Int.castRingHom ℚ)).det ≠ 0 := by
      rw [show ((Vmat x).map (Int.castRingHom ℚ)).det = (((Vmat x).det : ℤ) : ℚ) from by
        rw [show (Vmat x).map (Int.castRingHom ℚ) = (Int.castRingHom ℚ).mapMatrix (Vmat x)
          from rfl]
        exact (RingHom.map_det (Int.castRingHom ℚ) (Vmat x)).symm]
      exact Int.cast_ne_zero.mpr (hVdet x hx)
    have hunit : IsUnit ((Vmat x).map (Int.castRingHom ℚ)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hVQ)
    have hcols := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
    have h4 := hcols.comp (fun j : {j : Fin N // j.val < k} => j.1) Subtype.val_injective
    have h5 : (fun j : {j : Fin N // j.val < k} => fun i : Fin N =>
          (Vmat x).map (Int.castRingHom ℚ) i j.1)
        = (fun j : {j : Fin N // j.val < k} => fun i : Fin N =>
          ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
            ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ)) := by
      funext j i
      change ((Vmat x i j.1 : ℤ) : ℚ) = ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
        ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ)
      rw [hVmatdef]
      push_cast
      ring
    have hliW : LinearIndependent ℚ (fun j : {j : Fin N // j.val < k} =>
        fun i => ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
          ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ)) := by
      rw [← h5]; exact h4
    have hcardk : Fintype.card {j : Fin N // j.val < k} = k := by
      have h := Fintype.card_coe (Finset.univ.filter (fun j : Fin N => j.val < k))
      rw [card_filter_val_lt (le_of_lt hklt)] at h
      simpa using h
    have hfin : Module.finrank ℚ (Submodule.span ℚ (Set.range (fun j : {j : Fin N // j.val < k} =>
        fun i => ((xs x j.1 i : ℤ) : ℚ) + ∑ p : Fin N,
          ((xs x p i : ℤ) : ℚ) * ((xi x p j.1 : ℤ) : ℚ)))) = k := by
      rw [finrank_span_eq_card hliW, hcardk]
    rw [hWconv x hx]
    intro htop
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hfin
    omega
  -- the `Wf` take only finitely many values
  have hWfun : ∀ x ∈ Z₄, ∀ y ∈ Z₄,
      approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M')) xbar ‖x‖
        = approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M')) xbar ‖y‖ →
        Wf x = Wf y := by
    intro x hx y hy heq
    have hcol := span_straightened_eq_of_compound_span_eq hrk hr1 (Vmat x) (Vmat y)
      (hVdet x hx) (hVdet y hy) Tstar tSet htSet
      (by rw [← (hVspan x hx).1, ← (hVspan y hy).1]; exact heq)
    rw [hWfdef]
    exact hcol
  have hWfin : (Set.range (fun x : ↥Z₄ => Wf x)).Finite := by
    refine range_finite_of_key
      (f := fun x : ↥Z₄ => approxSpace (toC (Commons.LinearAlgebra.Matrix.compound r M'))
        xbar ‖(x : Fin N → ℤ)‖) (g := fun x : ↥Z₄ => Wf x) ?_ ?_
    · exact hSfin.subset (by rintro V ⟨x, rfl⟩; exact hVmemS x x.2)
    · intro a b hab
      exact hWfun a.1 a.2 b.1 b.2 hab
  -- ## Step 13: the contradiction
  refine Commons.LinearAlgebra.GeneralPosition.not_finite_cover_of_genPos
    (K := ℚ) (V := Fin N → ℚ)
    (fun T' hT' hcard => Submission.Subspace.genPos_image Y hgp T' ?_ hcard)
    (hZ₄inf.image intCastVec_injective.injOn)
    ⟨(hWfin.toFinset).filter (fun W => W ≠ ⊤), ?_, ?_⟩
  · rintro v hv
    rcases hT' hv with ⟨x, hx, rfl⟩
    exact ⟨x, hZ₄Y x hx, rfl⟩
  · intro W hW
    exact (Finset.mem_filter.mp hW).2
  · rintro v ⟨x, hx, rfl⟩
    refine ⟨Wf x, Finset.mem_filter.mpr ⟨?_, hWne x hx⟩, hmemW x hx⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨⟨x, hx⟩, rfl⟩



/-! ## The real rank descent for `Fin N` and for an arbitrary finite index type -/

/-- **The real rank descent for `Fin N`** (from the maximal-rank and low-rank cases). -/
theorem rankDescentReal_fin {N : ℕ} (hN : 2 ≤ N) (M : Matrix (Fin N) (Fin N) ℝ)
    (hM : M.det ≠ 0) (halg : ∀ i j, IsAlgebraic ℚ (M i j)) : Submission.Subspace.RankDescentReal M := by
  intro c hc hbad
  obtain ⟨Y, hYinf, hYgp, hYnz, hYb⟩ := hbad
  have hdetC := toC_det_ne_zero M hM
  have hind : LinearIndependent ℂ (toC M) := by
    have hunit : IsUnit (Matrix.of (toC M)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetC)
    have hrow : LinearIndependent ℂ (Matrix.of (toC M)).row :=
      Matrix.linearIndependent_rows_iff_isUnit.mpr hunit
    simpa using hrow
  obtain ⟨Q₀, hQ₀1, hQ₀⟩ :=
    finrank_approxSpace_lt (by simpa using hN : 2 ≤ Fintype.card (Fin N)) (toC M) hind c hc
  by_cases hmax : ({x ∈ Y | Module.finrank ℚ (approxSpace (toC M) c ‖x‖) = N - 1}
      : Set (Fin N → ℤ)).Infinite
  · exact maxCase_false hN M hM halg c hc hYgp hYb hmax
  · rw [Set.not_infinite] at hmax
    have hlow : ({x ∈ Y | Module.finrank ℚ (approxSpace (toC M) c ‖x‖) ≤ N - 2}
        : Set (Fin N → ℤ)).Infinite := by
      by_contra hcon
      rw [Set.not_infinite] at hcon
      have hsmall : ({x : Fin N → ℤ | ‖x‖ < Q₀} : Set (Fin N → ℤ)).Finite :=
        (Commons.Analysis.Normed.finite_bounded_int_vectors Q₀).subset (fun x hx => by
          rw [Set.mem_ofPred_eq] at hx ⊢
          exact le_of_lt hx)
      have hsub : Y ⊆ ({x : Fin N → ℤ | ‖x‖ < Q₀}
          ∪ {x ∈ Y | Module.finrank ℚ (approxSpace (toC M) c ‖x‖) = N - 1})
          ∪ {x ∈ Y | Module.finrank ℚ (approxSpace (toC M) c ‖x‖) ≤ N - 2} := by
        intro x hx
        by_cases h1 : ‖x‖ < Q₀
        · exact Or.inl (Or.inl h1)
        · push_neg at h1
          have h2 : Module.finrank ℚ (approxSpace (toC M) c ‖x‖) < N := by
            simpa using hQ₀ ‖x‖ h1
          by_cases h3 : Module.finrank ℚ (approxSpace (toC M) c ‖x‖) = N - 1
          · exact Or.inl (Or.inr ⟨hx, h3⟩)
          · exact Or.inr ⟨hx, by omega⟩
      exact hYinf (((hsmall.union hmax).union hcon).subset hsub)
    exact lowCase_false hN M hM halg c hc hYgp hYb hlow

/-- **The real rank descent is invariant under reindexing the coordinates.** -/
theorem rankDescent_reindex {σ τ : Type*} [Fintype σ] [Fintype τ] (e : σ ≃ τ) (L : τ → τ → ℂ)
    (h : Submission.Subspace.RankDescent (fun i j : σ => L (e i) (e j))) : Submission.Subspace.RankDescent L := by
  classical
  intro c hc hbad
  obtain ⟨Y, hYinf, hYgp, hYnz, hYb⟩ := hbad
  set ψ : (τ → ℤ) → (σ → ℤ) := fun x i => x (e i) with hψ
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    funext t
    have h1 := congrFun hxy (e.symm t)
    simpa [hψ] using h1
  set c' : σ → ℝ := fun i => c (e i) with hc'
  have hc'sum : ∑ i : σ, c' i < 0 := by
    rw [hc', Equiv.sum_comp e c]
    exact hc
  refine h c' hc'sum ⟨ψ '' Y, hYinf.image hψinj.injOn, ?_, ?_, ?_⟩
  · -- general position
    intro T' hT' hcard
    have hpre : ∀ y ∈ T', ∃ x ∈ Y, ψ x = y := by
      intro y hy
      rcases hT' (Finset.mem_coe.mpr hy) with ⟨x, hx, hxy⟩
      exact ⟨x, hx, hxy⟩
    let F : ↥T' → (τ → ℤ) := fun y => Classical.choose (hpre y y.2)
    have hFmem : ∀ y : ↥T', F y ∈ Y := fun y => (Classical.choose_spec (hpre y y.2)).1
    have hFeq : ∀ y : ↥T', ψ (F y) = (y : σ → ℤ) :=
      fun y => (Classical.choose_spec (hpre y y.2)).2
    have hFinj : Function.Injective F := by
      intro a b hab
      apply Subtype.ext
      rw [← hFeq a, ← hFeq b, hab]
    set T : Finset (τ → ℤ) := (Finset.univ : Finset ↥T').image F with hTdef
    have hTsub : (↑T : Set (τ → ℤ)) ⊆ Y := by
      intro x hx
      rw [hTdef, Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with ⟨y, -, rfl⟩
      exact hFmem y
    have hTcard : T.card ≤ Fintype.card τ := by
      rw [hTdef, Finset.card_image_of_injective _ hFinj, Finset.card_univ, Fintype.card_coe,
        ← Fintype.card_congr e]
      exact hcard
    have hli := hYgp T hTsub hTcard
    let g : ↥T' → ↥T := fun y => ⟨F y, by
      rw [hTdef, Finset.mem_image]
      exact ⟨y, Finset.mem_univ y, rfl⟩⟩
    have hg : Function.Injective g := by
      intro a b hab
      exact hFinj (congrArg (fun x : ↥T => (x : τ → ℤ)) hab)
    have hcomp := hli.comp g hg
    have hW : (fun y : ↥T' => fun i : σ => (((y : σ → ℤ)) i : ℚ))
        = (piEquiv e : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) ∘ ((fun x : ↥T => fun t : τ =>
            (((x : τ → ℤ)) t : ℚ)) ∘ g) := by
      funext y i
      have h1 := congrFun (hFeq y) i
      have h2 : (F y) (e i) = (y : σ → ℤ) i := by simpa [hψ] using h1
      show ((y : σ → ℤ) i : ℚ) = (((g y : ↥T) : τ → ℤ) (e i) : ℚ)
      rw [show ((g y : ↥T) : τ → ℤ) = F y from rfl, ← h2]
    rw [hW]
    refine hcomp.map (f := (piEquiv e : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))) ?_
    rw [LinearMap.ker_eq_bot.mpr (piEquiv e).injective]
    exact disjoint_bot_right
  · -- the values do not vanish
    rintro y ⟨x, hxY, rfl⟩ i
    have h1 : (∑ j : σ, L (e i) (e j) * ((ψ x j : ℤ) : ℂ))
        = ∑ t : τ, L (e i) t * ((x t : ℤ) : ℂ) := by
      rw [hψ]
      exact Equiv.sum_comp e (fun t => L (e i) t * ((x t : ℤ) : ℂ))
    rw [h1]
    exact hYnz x hxY (e i)
  · -- the bounds
    rintro y ⟨x, hxY, rfl⟩ i
    have h1 : (∑ j : σ, L (e i) (e j) * ((ψ x j : ℤ) : ℂ))
        = ∑ t : τ, L (e i) t * ((x t : ℤ) : ℂ) := by
      rw [hψ]
      exact Equiv.sum_comp e (fun t => L (e i) t * ((x t : ℤ) : ℂ))
    have h2 : ‖ψ x‖ = ‖x‖ := by
      refine le_antisymm ?_ ?_
      · refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i => ?_
        rw [hψ]
        exact norm_le_pi_norm x (e i)
      · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun t => ?_
        have h3 := norm_le_pi_norm (ψ x) (e.symm t)
        rw [hψ] at h3
        simpa using h3
    rw [h1, h2, hc']
    exact hYb x hxY (e i)

/-- **The real rank descent for an arbitrary finite index type of cardinality at least two.** -/
theorem rankDescentReal_of_card_ge_two {σ : Type*} [Fintype σ] [DecidableEq σ]
    (hσ : 2 ≤ Fintype.card σ)
    (M : σ → σ → ℝ) (hM : (Matrix.of M).det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (M i j)) : Submission.Subspace.RankDescentReal M := by
  classical
  set e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ with he
  have hN : 2 ≤ Fintype.card σ := hσ
  have hsub : Matrix.of (fun i j : Fin (Fintype.card σ) => M (e.symm i) (e.symm j))
      = (Matrix.of M).submatrix (⇑e.symm) (⇑e.symm) := rfl
  have hdet' : (Matrix.of (fun i j : Fin (Fintype.card σ) => M (e.symm i) (e.symm j))).det ≠ 0 := by
    rw [hsub, Matrix.det_submatrix_equiv_self]
    exact hM
  have halg' : ∀ i j : Fin (Fintype.card σ),
      IsAlgebraic ℚ ((fun i j : Fin (Fintype.card σ) => M (e.symm i) (e.symm j)) i j) :=
    fun i j => halg _ _
  have h1 : Submission.Subspace.RankDescentReal (fun i j : Fin (Fintype.card σ) =>
      M (e.symm i) (e.symm j)) :=
    rankDescentReal_fin hN _ hdet' halg'
  refine rankDescent_reindex (e.symm) (fun i j : σ => (M i j : ℂ)) ?_
  show Submission.Subspace.RankDescent
    (fun i j : Fin (Fintype.card σ) => ((M (e.symm i) (e.symm j) : ℝ) : ℂ))
  exact h1

end Submission.Subspace.RealRank
