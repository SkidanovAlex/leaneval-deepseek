/-
  WilE7 / DimAPI — node **N1** of the design (`sources/wilkiesE7main/wilkies_e7_main_design.md`,
  review fix 1): the projection rank of an absolute `Good` stratum `T` contained in a *fibrewise*
  `Good` stratum `Sf` of full fibre codimension `Sf.j = m` equals the dimension `N - T.j` of `T`.

  ## Mathematics

  Let `N = n + m` and `z ∈ T.X.set`.  The fibre of `Sf` over the base `ℝⁿ` is finite near `absPt z`
  (the fibrewise Jacobian of `Sf.h` is a square `m × m` matrix of rank `Sf.j = m`, hence
  invertible).  Since `T.X.set ⊆ Sf.X.set`, the tangent space `ker (jac T z)` of `T` at `z` cannot
  have a nonzero vector with vanishing base component: such a vector would be tangent to a finite
  (hence locally isolated) fibre of `Sf`.

  Formally, with `eqMap T : w ↦ (a ↦ eaEval T.X.c (T.h a) w)` the tuple of defining equations of
  `T` (so that `fderiv ℝ (eqMap T) z` *is* `jac T z`, see `hasFDerivAt_eqMap_aux`):

  * `Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet`, applied to `eqMap T` and to the `b`-th
    defining equation of `Sf` (transported along `absPt`), whose vanishing on the level set of
    `eqMap T` near `z` is the locality clause of `T.Good` followed by the containment
    `absSet T ⊆ Sf.X.set`, shows
    `ker (fderiv (eqMap T) z) ≤ ker (fderiv (Sf.h b ∘ absPt) z)` for every `b`
    (`hkerle` below);
  * `fderiv_eaEval_comp_absPt_aux` evaluates the latter on a vector `v`; the base coordinates of
    `v` vanish (`basePrLin n m v = 0`), so all base terms drop out of the sum, leaving the action
    of the *fibrewise* Jacobian of `Sf`, which is injective (`eq_zero_of_rows_absPt_aux`),
    whence `v = 0`;
  * so `basePrLin n m` is injective on `ker (jac T z)` (`hvert`), and hence
    `projRank T z = finrank (ker (jac T z)) = (0 + (n + m)) - T.j`, the last equality being
    rank–nullity for the surjective differential `jac T z` (`jac_range_eq_top_of_good_aux`).

  The auxiliary lemmas `*_aux` of this file are the local copies of the four interface lemmas of
  this node; the siblings `jac_range_eq_top_of_good`, `hasFDerivAt_eqMap`,
  `fderiv_eaEval_comp_absPt` and `eq_zero_of_rows_absPt` (delegated to colleagues) state the same
  four facts under their canonical names.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet
import Submission.Work.WilE7.exists_ker_equiv

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7.DimAPI
open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-! ## The differential of the defining-equation map of a stratum -/

/-- The Fréchet derivative of the defining-equation map `eqMap S` is the Jacobian
`MainDesign.jac S z` of the defining equations. -/
theorem hasFDerivAt_eqMap_aux {p q : ℕ} (S : Stratum p q) (z : Fin (p + q) → ℝ) :
    HasFDerivAt (eqMap S) ((jac S z).toContinuousLinearMap) z := by
  have hpi : HasFDerivAt (fun w : Fin (p + q) → ℝ => fun a : Fin S.j =>
      eaEval S.X.c (S.h a) w)
      (ContinuousLinearMap.pi fun a : Fin S.j =>
        ∑ i : Fin (p + q), (eaEval S.X.c (eaD S.X.c i (S.h a)) z) •
          (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ)) z :=
    hasFDerivAt_pi.mpr fun a => Work.WilE5.Calc.hasFDerivAt_eaEval S.X.c (S.h a) z
  have hclm : ContinuousLinearMap.pi (fun a : Fin S.j =>
        ∑ i : Fin (p + q), (eaEval S.X.c (eaD S.X.c i (S.h a)) z) •
          (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ))
      = (jac S z).toContinuousLinearMap := by
    ext v a
    simp [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul, jac, Matrix.mulVecLin_apply,
      Matrix.mulVec_apply_eq_sum, Matrix.of_apply]
  rw [hclm] at hpi
  exact hpi

/-! ## The Jacobian of a `Good` stratum has full row rank -/

/-- On a `Good` stratum the full Jacobian `jac S z` (all `p + q` columns) has full row rank
`S.j`, i.e. is surjective: its fibrewise block is a `S.j × q` matrix of rank `S.j`, so its rows are
independent, and the rank is bounded by the number of rows. -/
theorem jac_range_eq_top_of_good_aux {p q : ℕ} (S : Stratum p q) (hS : S.Good)
    {z : Fin (p + q) → ℝ} (hz : z ∈ S.X.set) :
    (jac S z).range = ⊤ := by
  set M : Matrix (Fin S.j) (Fin (p + q)) ℝ :=
    Matrix.of fun (a : Fin S.j) (l : Fin (p + q)) => eaEval S.X.c (eaD S.X.c l (S.h a)) z
    with hM
  have hsub : (M.submatrix id (Fin.natAdd p)).rank ≤ M.rank :=
    Matrix.rank_submatrix_le M id (Fin.natAdd p)
  have hgood : (M.submatrix id (Fin.natAdd p)).rank = S.j := by
    have h := (hS z hz).2.1
    simpa [hM, Matrix.submatrix, Work.WilE5.yDir] using h
  have hle : M.rank ≤ S.j := by
    have h := Matrix.rank_le_height M
    simpa using h
  have hrank : M.rank = S.j := le_antisymm hle (le_trans (le_of_eq hgood.symm) hsub)
  have hrange : (jac S z).range = M.mulVecLin.range := rfl
  rw [hrange]
  apply Submodule.eq_top_of_finrank_eq
  rw [Matrix.rank] at hrank
  rw [hrank]
  simp

/-! ## Vertical vanishing of a tangent vector -/

/-- **Vertical vanishing.**  Let `Sf : Stratum n m` be a `Good` stratum of full fibre codimension
`Sf.j = m`, let `absPt z ∈ Sf.X.set`, and let `v : ℝ^{0+(n+m)}` have no base component
(`basePrLin n m v = 0`) and be annihilated by every row of the transported Jacobian of `Sf` at
`absPt z`.  Then `v = 0`: the fibrewise rows of `Sf` already form an invertible `m × m` matrix, so
the fibre coordinates of `v` vanish as well. -/
theorem eq_zero_of_rows_absPt_aux {n m : ℕ} (Sf : Stratum n m) (hSf : Sf.Good)
    (hj : Sf.j = m) {z v : Fin (0 + (n + m)) → ℝ}
    (hz : absPt z ∈ Sf.X.set)
    (hbase : basePrLin n m v = 0)
    (hsum : ∀ b : Fin Sf.j, ∑ i : Fin (n + m),
        eaEval Sf.X.c (eaD Sf.X.c i (Sf.h b)) (absPt z) * absPt v i = 0) :
    v = 0 := by
  -- the fibrewise Jacobian of `Sf` at `absPt z`, as a matrix
  set M : Matrix (Fin Sf.j) (Fin m) ℝ := Matrix.of fun (b : Fin Sf.j) (l : Fin m) =>
    eaEval Sf.X.c (eaD Sf.X.c (Fin.natAdd n l) (Sf.h b)) (absPt z) with hM
  have hrank : M.rank = Sf.j := by
    have h := Work.WilE5.Stratum.good_rank hSf hz
    simpa [hM, Work.WilE5.yDir] using h
  -- it is surjective, hence injective (equal finite dimensions)
  have hrange : M.mulVecLin.range = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [Matrix.rank] at hrank
    rw [hrank]
    simp
  have hdim : Module.finrank ℝ (Fin m → ℝ) = Module.finrank ℝ (Fin Sf.j → ℝ) := by
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun]
    exact hj.symm
  have hinj : Function.Injective M.mulVecLin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := M.mulVecLin) hdim).mpr
      (LinearMap.range_eq_top.mp hrange)
  -- so the vector of fibre coordinates vanishes
  have hy0 : (fun l : Fin m => absPt v (Fin.natAdd n l)) = 0 := by
    apply hinj
    rw [map_zero]
    funext b
    have hb := hsum b
    rw [Fin.sum_univ_add] at hb
    have hbase0 : (∑ j : Fin n, eaEval Sf.X.c (eaD Sf.X.c (Fin.castAdd m j) (Sf.h b))
        (absPt z) * absPt v (Fin.castAdd m j)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show absPt v (Fin.castAdd m j) = basePrLin n m v j from rfl, hbase]
      simp
    rw [hbase0, zero_add] at hb
    rw [Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum]
    simpa [hM] using hb
  -- hence `absPt v = 0`, and finally `v = 0`
  have habsPt : absPt v = 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun l => ?_) i
    · show absPt v (Fin.castAdd m j) = 0
      rw [show absPt v (Fin.castAdd m j) = basePrLin n m v j from rfl]
      exact congrFun hbase j
    · show absPt v (Fin.natAdd n l) = 0
      exact congrFun hy0 l
  exact eq_zero_of_absPt_eq_zero habsPt

/-! ## The chain rule along the coordinate reindexing `absPt` -/

/-- The transport of a defining equation of a stratum along `MainDesign.absPt` is analytic. -/
lemma analyticAt_eaEval_comp_absPt {n m : ℕ} (Sf : Stratum n m) (b : Fin Sf.j)
    (z : Fin (0 + (n + m)) → ℝ) :
    AnalyticAt ℝ (fun w : Fin (0 + (n + m)) → ℝ => eaEval Sf.X.c (Sf.h b) (absPt w)) z := by
  have h1 : AnalyticAt ℝ (fun w : Fin (n + m) → ℝ => eaEval Sf.X.c (Sf.h b) w) (absPt z) :=
    Work.WilE5.Strat.analyticAt_eaEval Sf.X.c (Sf.h b) (absPt z)
  have h2 : AnalyticAt ℝ (fun w : Fin (0 + (n + m)) → ℝ => (absPtCLM (n + m)) w) z :=
    (absPtCLM (n + m)).analyticAt z
  have heq : (fun w : Fin (0 + (n + m)) → ℝ => (absPtCLM (n + m)) w) = absPt :=
    funext fun w => absPtCLM_apply w
  rw [heq] at h2
  exact h1.comp h2

/-- Chain rule along `MainDesign.absPt`: the derivative of `w ↦ eaEval c (h b) (absPt w)` at `z`,
evaluated at `v`, is the sum of the partial derivatives of `eaEval c (h b)` at `absPt z` against
the coordinates of `absPt v`. -/
theorem fderiv_eaEval_comp_absPt_aux {n m : ℕ} (Sf : Stratum n m) (b : Fin Sf.j)
    (z v : Fin (0 + (n + m)) → ℝ) :
    fderiv ℝ (fun w : Fin (0 + (n + m)) → ℝ =>
        eaEval Sf.X.c (Sf.h b) (absPt w)) z v =
      ∑ i : Fin (n + m),
        eaEval Sf.X.c (eaD Sf.X.c i (Sf.h b)) (absPt z) * absPt v i := by
  have h1 : HasFDerivAt (fun w : Fin (n + m) → ℝ => eaEval Sf.X.c (Sf.h b) w)
      (∑ i : Fin (n + m), (eaEval Sf.X.c (eaD Sf.X.c i (Sf.h b)) (absPt z)) •
        (ContinuousLinearMap.proj i : (Fin (n + m) → ℝ) →L[ℝ] ℝ)) (absPt z) :=
    Work.WilE5.Calc.hasFDerivAt_eaEval Sf.X.c (Sf.h b) (absPt z)
  have h2 := h1.comp z (absPtCLM (n + m)).hasFDerivAt
  have h2' : HasFDerivAt (fun w : Fin (0 + (n + m)) → ℝ =>
      eaEval Sf.X.c (Sf.h b) (absPt w))
      ((∑ i : Fin (n + m), (eaEval Sf.X.c (eaD Sf.X.c i (Sf.h b)) (absPt z)) •
        (ContinuousLinearMap.proj i : (Fin (n + m) → ℝ) →L[ℝ] ℝ)) ∘SL absPtCLM (n + m)) z :=
    h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => rfl)
  rw [h2'.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, absPtCLM_apply]

/-! ## The projection rank of an absolute stratum contained in a full-codimension fibre stratum -/

theorem projRank_eq_dim_of_sub_fibreGood {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + m))
    (hT : T.Good) (Sf : WilkiesDesign.E.Stratum n m) (hSf : Sf.Good) (hj : Sf.j = m)
    (hsub : Work.WilE7.MainDesign.absSet T ⊆ Sf.X.set)
    {z : Fin (0 + (n + m)) → ℝ} (hz : z ∈ T.X.set) :
    Work.WilE7.MainDesign.projRank T z = n + m - T.j := by
  have hzSf : absPt z ∈ Sf.X.set := hsub ⟨z, hz, rfl⟩
  -- (1) the defining-equation map of `T`, its differential, and surjectivity of that differential
  have hfderivT : fderiv ℝ (eqMap T) z = (jac T z).toContinuousLinearMap :=
    (hasFDerivAt_eqMap_aux T z).fderiv
  have hgz : eqMap T z = 0 := eqMap_eq_zero_of_good T hT hz
  have hstrict : HasStrictFDerivAt (eqMap T) (fderiv ℝ (eqMap T) z) z :=
    (analyticAt_eqMap T z).hasStrictFDerivAt
  have hsurj : (fderiv ℝ (eqMap T) z).range = ⊤ := by
    rw [hfderivT]
    exact jac_range_eq_top_of_good_aux T hT hz
  -- (2) the differential of every defining equation of `Sf` kills `ker (fderiv (eqMap T) z)`
  have hkerle : ∀ b : Fin Sf.j, (fderiv ℝ (eqMap T) z).ker ≤
      (fderiv ℝ (fun w : Fin (0 + (n + m)) → ℝ =>
        eaEval Sf.X.c (Sf.h b) (absPt w)) z).ker := by
    intro b
    have hf : HasFDerivAt (fun w : Fin (0 + (n + m)) → ℝ =>
        eaEval Sf.X.c (Sf.h b) (absPt w))
        (fderiv ℝ (fun w : Fin (0 + (n + m)) → ℝ =>
          eaEval Sf.X.c (Sf.h b) (absPt w)) z) z :=
      (analyticAt_eaEval_comp_absPt Sf b z).hasStrictFDerivAt.hasFDerivAt
    refine Work.WilE7.Auxiliary.kerLeKerOfVanishLevelSet (eqMap T)
      (fun w : Fin (0 + (n + m)) → ℝ => eaEval Sf.X.c (Sf.h b) (absPt w)) z
      (fderiv ℝ (eqMap T) z)
      (fderiv ℝ (fun w : Fin (0 + (n + m)) → ℝ =>
        eaEval Sf.X.c (Sf.h b) (absPt w)) z) hstrict hf hsurj hgz ?_
    -- the equations of `Sf` vanish on the level set of the equations of `T`, near `z`
    filter_upwards [(hT z hz).2.2] with w hw hgw
    have hwT : w ∈ T.X.set := hw (by funext i; exact Fin.elim0 i) (fun a => by
      have h := congrFun hgw a
      simpa [eqMap] using h)
    rw [(hSf _ (hsub ⟨w, hwT, rfl⟩)).1 b, (hSf _ hzSf).1 b]
  have hMb : ∀ b : Fin Sf.j, ∀ v ∈ (fderiv ℝ (eqMap T) z).ker,
      (fderiv ℝ (fun w : Fin (0 + (n + m)) → ℝ =>
        eaEval Sf.X.c (Sf.h b) (absPt w)) z) v = 0 :=
    fun b _ hv => hkerle b hv
  -- (3) a tangent vector of `T` with no base component vanishes
  have hvert : ∀ v ∈ (jac T z).ker, basePrLin n m v = 0 → v = 0 := by
    intro v hv hbase
    have hv' : v ∈ (fderiv ℝ (eqMap T) z).ker := by
      rw [hfderivT]
      exact hv
    refine eq_zero_of_rows_absPt_aux Sf hSf hj hzSf hbase (fun b => ?_)
    have h0 := hMb b v hv'
    rwa [fderiv_eaEval_comp_absPt_aux Sf b z v] at h0
  -- (4) hence `basePrLin` is injective on the tangent space of `T`
  have hfin : Module.finrank ℝ (((jac T z).ker).map (basePrLin n m))
      = Module.finrank ℝ (jac T z).ker := by
    set W : Submodule ℝ (Fin (0 + (n + m)) → ℝ) := (jac T z).ker with hW
    have hker : ((basePrLin n m).comp W.subtype).ker = ⊥ := by
      rw [LinearMap.ker_eq_bot]
      intro a b hab
      have hmem : ((a : Fin (0 + (n + m)) → ℝ) - (b : Fin (0 + (n + m)) → ℝ)) ∈ W :=
        W.sub_mem a.2 b.2
      have hab' : basePrLin n m (a : Fin (0 + (n + m)) → ℝ)
          = basePrLin n m (b : Fin (0 + (n + m)) → ℝ) := hab
      have h0 : basePrLin n m
          ((a : Fin (0 + (n + m)) → ℝ) - (b : Fin (0 + (n + m)) → ℝ)) = 0 := by
        rw [map_sub, hab', sub_self]
      have h1 : (a : Fin (0 + (n + m)) → ℝ) - (b : Fin (0 + (n + m)) → ℝ) = 0 :=
        hvert _ hmem h0
      exact Subtype.coe_injective (sub_eq_zero.mp h1)
    have hinj : Function.Injective ((basePrLin n m).comp W.subtype) :=
      LinearMap.ker_eq_bot.mp hker
    have hrange : ((basePrLin n m).comp W.subtype).range = W.map (basePrLin n m) := by
      rw [LinearMap.range_comp W.subtype (basePrLin n m), Submodule.range_subtype]
    have h3 : Module.finrank ℝ ↥(((basePrLin n m).comp W.subtype).range)
        = Module.finrank ℝ ↥W := LinearMap.finrank_range_of_inj hinj
    have h4 : Module.finrank ℝ ↥(((basePrLin n m).comp W.subtype).range)
        = Module.finrank ℝ ↥(W.map (basePrLin n m)) :=
      congrArg (fun X : Submodule ℝ (Fin n → ℝ) => Module.finrank ℝ ↥X) hrange
    exact h4.symm.trans h3
  -- (5) the dimension count
  have hdim : Module.finrank ℝ (jac T z).ker = (0 + (n + m)) - T.j :=
    Work.WilE7.finrank_ker_of_surjective (jac T z) (jac_range_eq_top_of_good_aux T hT hz)
  show Module.finrank ℝ (((jac T z).ker).map (basePrLin n m)) = n + m - T.j
  rw [hfin, hdim]
  omega

end Work.WilE7.DimAPI
