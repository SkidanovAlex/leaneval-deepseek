import Mathlib
import Submission.Work.WilE7.CoreStep.FibreEndDefs
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.Nondrop.FibreCalc
import Submission.Work.WilE7.DimAPI.ProjRankAux
import Submission.Work.WilE7.DimAPI.projRank_eq_dim_of_sub_fibreGood
import Submission.Work.WilE7.CoreStep.submersionReductionOfRank
import Submission.Work.WilE7.CoreStep.analyticLevelSetLocallyConnected
import Submission.Work.WilE7.CoreStep.verticalJacRank
import Submission.Work.WilE7.CoreStep.eaD_reindex
import Submission.Work.WilE7.CoreStep.absSet_locally_singleton_of_fullcodim

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.CoreStep

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.MainDesign

/-! ## 1. The value-preserving reindexing `Fin (0 + N) ≃ Fin N`

`MainDesign.absPt : ℝ^{0+N} → ℝ^N` is a mere reindexing of the coordinates; we record it as an
equivalence `Fin (0 + N) ≃ Fin N`, so that the machinery of `SemiPf.reindex` can be used to move
`T.X` between the "absolute" split `(0, n + (m+1))` and the "fibrewise" split `(n, m+1)`. -/

/-- The value-preserving equivalence `Fin (0 + N) ≃ Fin N` underlying `MainDesign.absPt`. -/
def absFibreEquiv (N : ℕ) : Fin (0 + N) ≃ Fin N := Work.WilE7.finEquiv (Nat.zero_add N)

theorem absFibreEquiv_apply_val (N : ℕ) (i : Fin (0 + N)) :
    ((absFibreEquiv N) i).val = i.val := rfl

theorem absFibreEquiv_symm_apply_val (N : ℕ) (i : Fin N) :
    ((absFibreEquiv N).symm i).val = i.val := rfl

/-- `reindex`ing a function along `absFibreEquiv` is composing with `absPtInv`. -/
theorem absFibreEquiv_coe_eq_absPtInv {N : ℕ} (w : Fin N → ℝ) :
    (fun i : Fin (0 + N) => w (absFibreEquiv N i)) = Work.WilE7.DimAPI.absPtInv N w := by
  funext i
  show w (absFibreEquiv N i) = w (Fin.cast (Nat.zero_add N) i)
  congr 1

/-! ## 2. The fibre point, and the transported stratum in the `(n, m+1)` split -/

/-- The point of the absolute stratum lying over the fibre point `y` of the base point `x`. -/
def fibrePt {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    Fin (0 + (n + (m + 1))) → ℝ :=
  Work.WilE7.DimAPI.absPtInv (n + (m + 1)) (Fin.append x y)

theorem absPt_fibrePt {n m : ℕ} (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    MainDesign.absPt (fibrePt x y) = Fin.append x y :=
  Work.WilE7.DimAPI.absPt_absPtInv (n + (m + 1)) (Fin.append x y)

theorem continuous_append_x {n m : ℕ} (x : Fin n → ℝ) :
    Continuous (fun y : Fin (m + 1) → ℝ => Fin.append x y) := by
  have h1 : (fun y : Fin (m + 1) → ℝ => Fin.append x y)
      = (Work.WilE9.Ift.appendCLM n (m + 1)) ∘ (fun y : Fin (m + 1) → ℝ => (x, y)) := by
    funext y
    rw [Function.comp_apply, Work.WilE9.Ift.appendCLM_apply]
  rw [h1]
  exact (Work.WilE9.Ift.appendCLM n (m + 1)).continuous.comp
    (continuous_const.prodMk continuous_id)

theorem continuous_fibrePt {n m : ℕ} (x : Fin n → ℝ) :
    Continuous (fun y : Fin (m + 1) → ℝ => fibrePt x y) := by
  have h : (fun y : Fin (m + 1) → ℝ => fibrePt x y)
      = (Work.WilE7.DimAPI.absPtInv (n + (m + 1))) ∘
        (fun y : Fin (m + 1) → ℝ => Fin.append x y) := rfl
  rw [h]
  exact Continuous.comp (continuous_pi fun i => continuous_apply _) (continuous_append_x x)

/-- The absolute stratum `T`, reindexed along `absFibreEquiv` into the `(n, m+1)` split.  Its
`X.set` is `MainDesign.absSet T` (see `absTransStratum_X_set`), and its equations are the
transported equations of `T`, so that `Nondrop.fnpFibre` of it is the fibre map of `T`. -/
abbrev absTransStratum {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) :
    WilkiesDesign.E.Stratum n (m + 1) :=
  ⟨Work.WilE7.SemiPf.reindex (absFibreEquiv (n + (m + 1))) T.X, T.j,
    fun a => Work.WilE7.EAPoly.reindex (absFibreEquiv (n + (m + 1))) (T.h a)⟩

theorem absTransStratum_X_set {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) :
    (absTransStratum T).X.set = MainDesign.absSet T := by
  have hset : (absTransStratum T).X.set
      = {y : Fin (n + (m + 1)) → ℝ |
          Work.WilE7.DimAPI.absPtInv (n + (m + 1)) y ∈ T.X.set} := by
    show (Work.WilE7.SemiPf.reindex (absFibreEquiv (n + (m + 1))) T.X).set = _
    rw [Work.WilE7.reindex_set]
    ext y
    simp only [Set.mem_ofPred_eq]
    rw [absFibreEquiv_coe_eq_absPtInv]
  rw [hset, MainDesign.absSet]
  ext y
  constructor
  · intro hy
    exact ⟨Work.WilE7.DimAPI.absPtInv (n + (m + 1)) y, hy,
      Work.WilE7.DimAPI.absPt_absPtInv (n + (m + 1)) y⟩
  · rintro ⟨w, hw, rfl⟩
    show Work.WilE7.DimAPI.absPtInv (n + (m + 1)) (MainDesign.absPt w) ∈ T.X.set
    rwa [Work.WilE7.DimAPI.absPtInv_absPt]

/-- Membership in the `π_n`-fibre, transported to the stratum coordinates. -/
theorem fibrePt_mem_iff {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    y ∈ WilkiesDesign.E.fiber (MainDesign.absSet T) x ↔ fibrePt x y ∈ T.X.set := by
  constructor
  · intro hy
    have hz : Fin.append x y ∈ MainDesign.absSet T := hy
    rw [MainDesign.absSet, Set.mem_image] at hz
    obtain ⟨w, hw, hweq⟩ := hz
    rw [fibrePt, ← hweq, Work.WilE7.DimAPI.absPtInv_absPt]
    exact hw
  · intro hy
    show Fin.append x y ∈ MainDesign.absSet T
    rw [MainDesign.absSet, Set.mem_image]
    exact ⟨fibrePt x y, hy, absPt_fibrePt x y⟩

/-! ## 3. The fibre map of `T` in the `(n, m+1)` split -/

/-- The fibre map of `T` over the base point `x`: in the `(n, m+1)` split this is the map whose
zero set (near a point of the fibre) is the fibre of `absSet T` over `x`. -/
def fibreMap {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (x : Fin n → ℝ) :
    (Fin (m + 1) → ℝ) → (Fin T.j → ℝ) :=
  Work.WilE7.Nondrop.fnpFibre (absTransStratum T) x

theorem fibreMap_apply {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) (a : Fin T.j) :
    fibreMap T x y a = eaEval T.X.c (T.h a) (fibrePt x y) := by
  rw [fibreMap, Work.WilE7.Nondrop.fnpFibre_apply]
  show eaEval (Work.WilE7.EAChain.reindex (absFibreEquiv (n + (m + 1))) T.X.c)
      (Work.WilE7.EAPoly.reindex (absFibreEquiv (n + (m + 1))) (T.h a)) (Fin.append x y) = _
  rw [Work.WilE7.EAChain.reindex_eaEval, absFibreEquiv_coe_eq_absPtInv]
  rfl

theorem fibreMap_analytic {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (x : Fin n → ℝ) (y : Fin (m + 1) → ℝ) :
    AnalyticAt ℝ (fibreMap T x) y :=
  Work.WilE7.Nondrop.fnpFibre_analytic (absTransStratum T) x y

/-! ## 4. The matrix of `fderiv (fibreMap T x) z` and its rank -/

/-- The `finrank` of the range of the linear map given by the rows `a ↦ ∑_j M a j • e_j` is the
rank of `M`. -/
theorem finrank_range_pi_smul_proj {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) :
    Module.finrank ℝ (LinearMap.range
      ((ContinuousLinearMap.pi (fun a : Fin p =>
        ∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ))) :
        (Fin q → ℝ) →ₗ[ℝ] (Fin p → ℝ))) = M.rank := by
  have hcoe : ((ContinuousLinearMap.pi (fun a : Fin p =>
      ∑ j : Fin q, M a j • (ContinuousLinearMap.proj j : (Fin q → ℝ) →L[ℝ] ℝ))) :
      (Fin q → ℝ) →ₗ[ℝ] (Fin p → ℝ)) = M.mulVecLin := by
    ext v a
    simp [ContinuousLinearMap.coe_pi, LinearMap.pi_apply, Matrix.mulVec, dotProduct]
  rw [hcoe, Matrix.rank]

/-- `eaD` commutes with a reindexing, in the form used below (index written as `e ·`). -/
theorem eaD_reindex_apply {k K r : ℕ} (e : Fin k ≃ Fin K) (c : EAChain k r)
    (j : Fin K) (Q : EAPoly k r) :
    eaD (Work.WilE7.EAChain.reindex e c) j (Work.WilE7.EAPoly.reindex e Q) =
      Work.WilE7.EAPoly.reindex e (eaD c (e.symm j) Q) := by
  have h := eaD_reindex e c (e.symm j) Q
  rwa [Equiv.apply_symm_apply] at h

/-- The entrywise identification of the "transported" fibre Jacobian of `T` with the vertical
Jacobian of `T`. -/
theorem fibreMap_eaD_eq {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (x : Fin n → ℝ) (z : Fin (m + 1) → ℝ) (a : Fin T.j) (l : Fin (m + 1)) :
    eaEval (absTransStratum T).X.c
        (eaD (absTransStratum T).X.c (Fin.natAdd n l) ((absTransStratum T).h a))
        (Fin.append x z)
      = eaEval T.X.c (eaD T.X.c (Fin.natAdd 0 (Fin.natAdd n l)) (T.h a)) (fibrePt x z) := by
  have hidx : (absFibreEquiv (n + (m + 1))).symm (Fin.natAdd n l)
      = Fin.natAdd 0 (Fin.natAdd n l) := by
    refine Fin.ext ?_
    rw [absFibreEquiv_symm_apply_val]
    simp [Fin.natAdd]
  show eaEval (Work.WilE7.EAChain.reindex (absFibreEquiv (n + (m + 1))) T.X.c)
      (eaD (Work.WilE7.EAChain.reindex (absFibreEquiv (n + (m + 1))) T.X.c) (Fin.natAdd n l)
        (Work.WilE7.EAPoly.reindex (absFibreEquiv (n + (m + 1))) (T.h a))) (Fin.append x z) = _
  rw [eaD_reindex_apply, Work.WilE7.EAChain.reindex_eaEval, absFibreEquiv_coe_eq_absPtInv, hidx]
  simp only [fibrePt]

/-- The matrix of the derivative of the fibre map is the "vertical Jacobian" of `T`. -/
theorem fderiv_fibreMap_eq {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (x : Fin n → ℝ) (z : Fin (m + 1) → ℝ) :
    fderiv ℝ (fibreMap T x) z =
      ContinuousLinearMap.pi (fun a : Fin T.j =>
        ∑ l : Fin (m + 1),
          (eaEval T.X.c (eaD T.X.c (Fin.natAdd 0 (Fin.natAdd n l)) (T.h a)) (fibrePt x z)) •
            (ContinuousLinearMap.proj l : (Fin (m + 1) → ℝ) →L[ℝ] ℝ)) := by
  rw [fibreMap, Work.WilE7.Nondrop.fnpFibre_fderiv]
  simp only [Work.WilE5.yDir]
  have hfun : (fun a : Fin T.j =>
        ∑ l : Fin (m + 1),
          (eaEval (absTransStratum T).X.c
              (eaD (absTransStratum T).X.c (Fin.natAdd n l) ((absTransStratum T).h a))
              (Fin.append x z)) •
            (ContinuousLinearMap.proj l : (Fin (m + 1) → ℝ) →L[ℝ] ℝ))
      = (fun a : Fin T.j =>
        ∑ l : Fin (m + 1),
          (eaEval T.X.c (eaD T.X.c (Fin.natAdd 0 (Fin.natAdd n l)) (T.h a)) (fibrePt x z)) •
            (ContinuousLinearMap.proj l : (Fin (m + 1) → ℝ) →L[ℝ] ℝ)) := by
    funext a
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [fibreMap_eaD_eq]
  rw [hfun]

/-- The rank of the fibre map at a point of the fibre is `m`, whenever `T.j ≤ n + m`. -/
theorem fibreMap_rank {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, MainDesign.projRank T z = n + m - T.j)
    (hcase : T.j ≤ n + m) (x : Fin n → ℝ) (z : Fin (m + 1) → ℝ)
    (hz : z ∈ WilkiesDesign.E.fiber (MainDesign.absSet T) x) :
    Module.finrank ℝ (fderiv ℝ (fibreMap T x) z).range = m := by
  have hΦmem : fibrePt x z ∈ T.X.set := (fibrePt_mem_iff T x z).mp hz
  let B : Matrix (Fin T.j) (Fin (m + 1)) ℝ := Matrix.of (fun a l =>
    eaEval T.X.c (eaD T.X.c (Fin.natAdd 0 (Fin.natAdd n l)) (T.h a)) (fibrePt x z))
  have hBrank : B.rank = m := by
    have h := verticalJacRank T hT (fibrePt x z) hΦmem
    have hB : B = Matrix.of (fun a l =>
        eaEval T.X.c (eaD T.X.c (Fin.natAdd 0 (Fin.natAdd n l)) (T.h a)) (fibrePt x z)) := rfl
    rw [hB, h, hrank (fibrePt x z) hΦmem]
    omega
  have h' : Module.finrank ℝ (fderiv ℝ (fibreMap T x) z).range = B.rank := by
    rw [fderiv_fibreMap_eq T x z]
    exact finrank_range_pi_smul_proj B
  rw [h', hBrank]

theorem fibre_locallyConnected {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (hT : T.Good)
    (hrank : ∀ z ∈ T.X.set, Work.WilE7.MainDesign.projRank T z = n + m - T.j) :
    ∀ x : Fin n → ℝ, ∀ z ∈ WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x,
      ∃ U ∈ nhds z, ∀ z' ∈ U, z' ∈ WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x →
        z' ∈ connectedComponentIn (WilkiesDesign.E.fiber (Work.WilE7.MainDesign.absSet T) x) z := by
  intro x z hz
  by_cases hcase : T.j ≤ n + m
  · -- Case (a): `T.j ≤ n + m`; the fibre is one-dimensional, and `fibreMap` has rank `m`.
    have hGan : ∀ y : Fin (m + 1) → ℝ, AnalyticAt ℝ (fibreMap T x) y :=
      fun y => fibreMap_analytic T x y
    have hΦmem : fibrePt x z ∈ T.X.set := (fibrePt_mem_iff T x z).mp hz
    have hGz : fibreMap T x z = 0 := by
      funext a
      rw [fibreMap_apply]
      exact Work.WilE5.Stratum.good_eqs hT hΦmem a
    have hZeq : ∀ y ∈ WilkiesDesign.E.fiber (MainDesign.absSet T) x,
        fibreMap T x y = fibreMap T x z := by
      intro y hy
      rw [hGz]
      funext a
      rw [fibreMap_apply]
      exact Work.WilE5.Stratum.good_eqs hT ((fibrePt_mem_iff T x y).mp hy) a
    have hZgerm : ∀ᶠ y in nhds z, fibreMap T x y = fibreMap T x z →
        y ∈ WilkiesDesign.E.fiber (MainDesign.absSet T) x := by
      have hloc := (Work.WilE5.Stratum.good_local hT hΦmem).mono
        (fun w hw h => hw (Subsingleton.elim _ _) h)
      filter_upwards [(continuous_fibrePt x).continuousAt.eventually hloc] with y hy hGy
      exact (fibrePt_mem_iff T x y).mpr (hy (fun a => by
        have h1 : fibreMap T x y a = 0 := by rw [hGy, hGz, Pi.zero_apply]
        rwa [fibreMap_apply] at h1))
    have hrankG : Module.finrank ℝ (fderiv ℝ (fibreMap T x) z).range = m :=
      fibreMap_rank T hT hrank hcase x z hz
    obtain ⟨Ψ, hΨan, hsurj, hcon⟩ := submersionReductionOfRank (fibreMap T x) hGan z hrankG
    exact analyticLevelSetLocallyConnected hGan hΨan hcon hsurj hZeq hZgerm
  · -- Case (b): `T.j = n + (m + 1)`; the fibre is locally a single point.
    have hΦmem : fibrePt x z ∈ T.X.set := (fibrePt_mem_iff T x z).mp hz
    have hjN : T.j = n + (m + 1) := by
      have hsurj : (MainDesign.jac T (fibrePt x z)).range = ⊤ :=
        Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux T hT hΦmem
      have hle : T.j ≤ n + (m + 1) := by
        have h := LinearMap.finrank_le_finrank_of_surjective (LinearMap.range_eq_top.mp hsurj)
        simp only [Module.finrank_fin_fun] at h
        omega
      omega
    have hev : ∀ᶠ w in nhds (Fin.append x z),
        w ∈ MainDesign.absSet T → w = Fin.append x z := by
      have h := absSet_locally_singleton_of_fullcodim T hT hjN (fibrePt x z) hΦmem
      rwa [absPt_fibrePt x z] at h
    obtain ⟨V, hVnhds, hVsub⟩ := Filter.eventually_iff_exists_mem.mp hev
    obtain ⟨V', hV'sub, hV'open, hV'mem⟩ := mem_nhds_iff.mp hVnhds
    refine ⟨(fun y : Fin (m + 1) → ℝ => Fin.append x y) ⁻¹' V', ?_, ?_⟩
    · exact (continuous_append_x x).continuousAt.preimage_mem_nhds (hV'open.mem_nhds hV'mem)
    · intro z' hz'U hz'fib
      have h2 : Fin.append x z' ∈ MainDesign.absSet T := hz'fib
      have h3 : Fin.append x z' = Fin.append x z :=
        hVsub (Fin.append x z') (hV'sub hz'U) h2
      have h4 : z' = z := by
        funext l
        have hh := congrFun h3 (Fin.natAdd n l)
        rwa [Fin.append_right, Fin.append_right] at hh
      rw [h4]
      exact mem_connectedComponentIn hz

end Work.WilE7.CoreStep
