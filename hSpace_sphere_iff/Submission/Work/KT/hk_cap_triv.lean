import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.hk_cap_triv_pre
import Submission.Work.KT.capTplus_contract
import Submission.Work.KT.capTminus_contract
import Submission.Work.KT.homotopy_conj_factors
import Submission.Work.KT.exists_ext_bound
import Submission.Work.KT.mat_inv_of_forall_isUnit

namespace Work.KT

set_option maxHeartbeats 1000000

open Matrix Filter
open scoped Topology

noncomputable section

/-! ## Auxiliary lemmas for the collared-representative argument -/

lemma continuous_tgtHeight (m : ℕ) : Continuous (tgtHeight m) := by
  unfold tgtHeight
  fun_prop

lemma isClosed_capTplus (m : ℕ) : IsClosed (capTplus m) :=
  isClosed_le continuous_const (continuous_tgtHeight m)

lemma isClosed_capTminus (m : ℕ) : IsClosed (capTminus m) :=
  isClosed_le (continuous_tgtHeight m) continuous_const

lemma compactSpace_tgt (m : ℕ) : CompactSpace (Tgt m) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (2 * m + 1))) 1)

lemma compactSpace_of_isClosed {m : ℕ} {cap : Set (Tgt m)} (h : IsClosed cap) : CompactSpace cap := by
  haveI := compactSpace_tgt m
  exact isCompact_iff_compactSpace.mp h.isCompact

/-- Evaluation of a matrix over `C(X, ℂ)` at a point of `X`, as a ring homomorphism. -/
def matEval {X : Type} [TopologicalSpace X] (k : ℕ) (x : X) :
    Matrix (Fin k) (Fin k) C(X, ℂ) →+* Matrix (Fin k) (Fin k) ℂ :=
  RingHom.mapMatrix (evalC x).toRingHom

lemma matEval_apply {X : Type} [TopologicalSpace X] {k : ℕ} (x : X)
    (M : Matrix (Fin k) (Fin k) C(X, ℂ)) :
    matEval k x M = M.map (fun F => evalC x F) := by
  ext i j
  rfl

@[simp] lemma matEval_apply_elem {X : Type} [TopologicalSpace X] {k : ℕ} (x : X)
    (M : Matrix (Fin k) (Fin k) C(X, ℂ)) (a b : Fin k) :
    matEval k x M a b = M a b x := by
  rw [matEval_apply, Matrix.map_apply]
  rfl

/-- Matrices over `C(X, ℂ)` are determined by their pointwise evaluations. -/
lemma matEval_ext {X : Type} [TopologicalSpace X] {k : ℕ}
    {A B : Matrix (Fin k) (Fin k) C(X, ℂ)} (h : ∀ x, matEval k x A = matEval k x B) : A = B := by
  ext i j x
  have hx := congrArg (fun M : Matrix (Fin k) (Fin k) ℂ => M i j) (h x)
  rwa [matEval_apply_elem, matEval_apply_elem] at hx

@[simp] lemma coneProjT_apply_elem' {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) (a b : Fin k) :
    coneProjT m f M a b = (M a b).1.1 := by
  rw [coneProjT_apply, Matrix.map_apply, coneToT_apply]

@[simp] lemma coneProjD_apply_elem' {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) (a b : Fin k) :
    coneProjD m f M a b = (M a b).1.2 := by
  rw [coneProjD_apply, Matrix.map_apply, coneToD_apply]

/-- The image of `List.ofFn` under `List.map`. -/
lemma ofFn_map_eq {α β : Type*} {n : ℕ} (f : Fin n → α) (g : α → β) :
    (List.ofFn f).map g = List.ofFn (fun i => g (f i)) := by
  rw [List.ofFn_eq_map, List.map_map]
  exact (List.ofFn_eq_map (f := g ∘ f)).symm

lemma matEval_list_prod {X : Type} [TopologicalSpace X] {K k : ℕ} (x : X)
    (A : Fin K → Matrix (Fin k) (Fin k) C(X, ℂ)) :
    matEval k x (List.ofFn A).prod = (List.ofFn (fun i => matEval k x (A i))).prod := by
  rw [map_list_prod, ofFn_map_eq]

lemma isUnit_list_prod {k : ℕ} {L : List (Matrix (Fin k) (Fin k) ℂ)}
    (h : ∀ A ∈ L, IsUnit A) : IsUnit L.prod := by
  induction L with
  | nil => exact isUnit_one
  | cons A L ih =>
      rw [List.prod_cons]
      exact (h A (List.mem_cons_self ..)).mul (ih fun B hB => h B (List.mem_cons_of_mem _ hB))

/-- Two matrices over the cone algebra with equal entries are equal. -/
lemma map_ofFn_congr {α β : Type*} {n : ℕ} {f f' : Fin n → α} (h : f = f') (g : α → β) :
    (List.ofFn f).map g = (List.ofFn f').map g := by rw [h]

/-- The base part of a matrix over the cone algebra, as a matrix over `C(Tgt m, ℂ)`. -/
def coneBase {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) : Matrix (Fin k) (Fin k) C(Tgt m, ℂ) :=
  coneProjT m f M

/-- Evaluating the base part of a matrix over the cone algebra. -/
lemma matEval_coneBase {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) (t : Tgt m) :
    matEval k t (coneBase m f M) = M.map (evalT m f t) := by
  rw [coneBase, coneProjT_apply]
  ext i j
  rfl

/-- Evaluating the base projection of a matrix over the cone algebra. -/
lemma matEval_coneProjT {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) (t : Tgt m) :
    matEval k t (coneProjT m f M) = M.map (evalT m f t) := by
  rw [coneProjT_apply]
  ext i j
  rfl

/-- The base projection of a product of elementary factors around `coneMat`. -/
lemma coneProjT_prod_ofFn {k K : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Fin K → Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) :
    coneProjT m f (List.ofFn (fun i => 1 + coneMat m f (A i))).prod
      = (List.ofFn (fun i => 1 + A i)).prod := by
  rw [map_list_prod, ofFn_map_eq]
  have hlist : (List.ofFn (fun i : Fin K => coneProjT m f (1 + coneMat m f (A i))))
      = (List.ofFn (fun i : Fin K => 1 + A i)) := by
    rw [List.ofFn_inj]
    funext i
    rw [map_add, map_one, coneProjT_coneMat]
  rw [hlist]

/-- The cell projection of a product of elementary factors around `coneMat`. -/
lemma coneProjD_prod_ofFn {k K : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Fin K → Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) :
    coneProjD m f (List.ofFn (fun i => 1 + coneMat m f (A i))).prod
      = (List.ofFn (fun i => 1 + coneProjD m f (coneMat m f (A i)))).prod := by
  rw [map_list_prod, ofFn_map_eq]
  have hlist : (List.ofFn (fun i : Fin K => coneProjD m f (1 + coneMat m f (A i))))
      = (List.ofFn (fun i : Fin K => 1 + coneProjD m f (coneMat m f (A i)))) := by
    rw [List.ofFn_inj]
    funext i
    rw [map_add, map_one]
  rw [hlist]

/-- Restriction of functions on `Tgt m` to a subset `cap`. -/
def restrictCap (m : ℕ) (cap : Set (Tgt m)) : C(Tgt m, ℂ) →ₐ[ℂ] C(cap, ℂ) :=
  pullAlg ⟨Subtype.val, continuous_subtype_val⟩

/-- Restriction of matrices over `C(Tgt m, ℂ)` to a subset `cap`. -/
def restrictMat (m : ℕ) (cap : Set (Tgt m)) (k : ℕ) :
    Matrix (Fin k) (Fin k) C(Tgt m, ℂ) →+* Matrix (Fin k) (Fin k) C(cap, ℂ) :=
  RingHom.mapMatrix (restrictCap m cap).toRingHom

lemma matEval_restrictMat {k : ℕ} (m : ℕ) {cap : Set (Tgt m)} (y : cap)
    (M : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) :
    matEval k y (restrictMat m cap k M) = matEval k (y : Tgt m) M := by
  ext i j
  rfl

/-- The constant matrix with values in the functions on a space. -/
private def constMat {k : ℕ} {X : Type} [TopologicalSpace X] (M : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin k) (Fin k) C(X, ℂ) :=
  M.map (fun c => ContinuousMap.const X c)

@[simp] lemma matEval_constMat {k : ℕ} {X : Type} [TopologicalSpace X] (x : X)
    (M : Matrix (Fin k) (Fin k) ℂ) : matEval k x (constMat (X := X) M) = M := by
  ext i j
  rw [matEval_apply, Matrix.map_apply]
  rfl

/-! ## Collaring of cell matrices -/

/-- A matrix over `C(D, ℂ)` is collared when its values only depend on the radial projection. -/
def Collared {m : ℕ} {k : ℕ} (A : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ)) : Prop :=
  ∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
    matEval k z A = matEval k (normPtBall z) A

lemma Collared.one {m : ℕ} {k : ℕ} :
    Collared (1 : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ)) := by
  intro z hz
  rw [map_one, map_one]

lemma Collared.mul {m : ℕ} {k : ℕ} {A B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ)}
    (hA : Collared A) (hB : Collared B) : Collared (A * B) := by
  intro z hz
  rw [map_mul, map_mul, hA z hz, hB z hz]

lemma Collared.add {m : ℕ} {k : ℕ} {A B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ)}
    (hA : Collared A) (hB : Collared B) : Collared (A + B) := by
  intro z hz
  rw [map_add, map_add, hA z hz, hB z hz]

lemma Collared.list_prod {m : ℕ} {k : ℕ}
    {L : List (Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ))}
    (h : ∀ A ∈ L, Collared A) : Collared L.prod := by
  induction L with
  | nil => simpa using Collared.one (m := m) (k := k)
  | cons A L ih =>
      rw [List.prod_cons]
      exact (h A (List.mem_cons_self ..)).mul (ih fun B hB => h B (List.mem_cons_of_mem _ hB))

/-- The pointwise inverse of a collared matrix is collared. -/
lemma Collared.inv {m : ℕ} {k : ℕ} {A B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ)}
    (hA : Collared A) (hB : ∀ z : Ball (Eu m × Eu m), matEval k z B = (matEval k z A)⁻¹) :
    Collared B := by
  intro z hz
  rw [hB z, hB (normPtBall z), hA z hz]

lemma Collared.conj {m : ℕ} {k : ℕ} {A B C : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ)}
    (hA : Collared A) (hB : Collared B) (hC : Collared C) : Collared (A * B * C) :=
  (hA.mul hB).mul hC

/-- The numerical bound used for the elementary factors. -/
lemma num_bound (n : ℕ) : (n : ℝ) * (1 / (2 * ((n : ℝ) + 1))) < 1 := by
  have h : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [mul_one_div, div_lt_one (by positivity)]
  linarith

/-! ## The main step: conjugation on a contractible closed cap -/

theorem hk_cap_triv_of_cap (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (cap : Set (Tgt m))
    (t0 : Tgt m) (ht0 : t0 ∈ cap) (hclosed : IsClosed cap)
    (hcon : ∃ H : C(cap × unitInterval, cap),
      (∀ x, H (x, 0) = x) ∧ ∀ x, H (x, 1) = ⟨t0, ht0⟩)
    (n r : ℕ) (P : Matrix (Fin n) (Fin n) (coneAlg f)) (hP : P * P = P)
    (hPt0 : P.map (evalT m f t0) = diagIdemMat r n)
    (hrad : ∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
      P.map (evalD m f z) = P.map (evalD m f (normPtBall z))) :
    ∃ g ginv : Matrix (Fin n) (Fin n) (coneAlg f), g * ginv = 1 ∧ ginv * g = 1 ∧
      (∀ t, t ∈ cap → (g * P * ginv).map (evalT m f t) = diagIdemMat r n) ∧
      (∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
        (g * P * ginv).map (evalD m f z) =
          (g * P * ginv).map (evalD m f (normPtBall z))) ∧
      (∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
        g.map (evalD m f z) = g.map (evalD m f (normPtBall z))) := by
  haveI hTgt : CompactSpace (Tgt m) := compactSpace_tgt m
  haveI hCap : CompactSpace cap := compactSpace_of_isClosed hclosed
  obtain ⟨H, hH0, hH1⟩ := hcon
  -- The homotopy of idempotents on the cap.
  let Φ : coneAlg f → C(cap × unitInterval, ℂ) := fun x =>
    (coneToT f x).comp ⟨fun z : cap × unitInterval => (H z : Tgt m),
      continuous_subtype_val.comp H.continuous⟩
  let Q : Matrix (Fin n) (Fin n) C(cap × unitInterval, ℂ) := P.map Φ
  have hQab : ∀ (a b : Fin n) (z : cap × unitInterval), (Q a b) z = evalT m f (H z) (P a b) :=
    fun a b z => rfl
  have hQ : Q * Q = Q := by
    refine matEval_ext fun z => ?_
    rw [map_mul]
    have hz : ∀ a b : Fin n, matEval n z Q a b = evalT m f (H z) (P a b) := by
      intro a b
      rw [matEval_apply_elem, hQab]
    ext i j
    have hsum : (∑ k : Fin n, P i k * P k j) = P i j := by
      rw [← Matrix.mul_apply]
      exact congrArg (fun M : Matrix (Fin n) (Fin n) (coneAlg f) => M i j) hP
    rw [Matrix.mul_apply]
    calc (∑ k : Fin n, matEval n z Q i k * matEval n z Q k j)
        = ∑ k : Fin n, evalT m f (H z) (P i k) * evalT m f (H z) (P k j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hz, hz]
      _ = ∑ k : Fin n, evalT m f (H z) (P i k * P k j) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]
      _ = evalT m f (H z) (∑ k : Fin n, P i k * P k j) := by rw [map_sum]
      _ = evalT m f (H z) (P i j) := by rw [hsum]
      _ = matEval n z Q i j := by rw [hz]
  obtain ⟨K, W, hWbd, hWtel⟩ := homotopy_conj_factors n Q hQ
  -- Tietze extension of the entries of the factors to the whole sphere.
  have hex : ∀ (i : Fin K) (a b : Fin n), ∃ G : C(Tgt m, ℂ),
      (∀ x : Tgt m, ‖G x‖ ≤ 1 / (2 * ((n : ℝ) + 1))) ∧ ∀ y : cap, G y = W i a b y := by
    intro i a b
    exact exists_ext_bound cap hclosed (1 / (2 * ((n : ℝ) + 1))) (by positivity) (W i a b)
      (hWbd i a b)
  let Wt : Fin K → Matrix (Fin n) (Fin n) C(Tgt m, ℂ) := fun i a b => (hex i a b).choose
  have hWtbd : ∀ (i : Fin K) (a b : Fin n) (x : Tgt m),
      ‖Wt i a b x‖ ≤ 1 / (2 * ((n : ℝ) + 1)) := fun i a b x => ((hex i a b).choose_spec).1 x
  have hWtres : ∀ (i : Fin K) (a b : Fin n) (y : cap), Wt i a b y = W i a b y :=
    fun i a b y => ((hex i a b).choose_spec).2 y
  -- The base factor product and the glued element.
  let U : Matrix (Fin n) (Fin n) C(Tgt m, ℂ) := (List.ofFn (fun i : Fin K => 1 + Wt i)).prod
  let Ginv : Matrix (Fin n) (Fin n) (coneAlg f) :=
    (List.ofFn (fun i : Fin K => 1 + coneMat m f (Wt i))).prod
  let V : Matrix (Fin n) (Fin n) C(Ball (Eu m × Eu m), ℂ) := coneProjD m f Ginv
  have hUeq : U = (List.ofFn (fun i : Fin K => 1 + Wt i)).prod := rfl
  have hGinveq : Ginv = (List.ofFn (fun i : Fin K => 1 + coneMat m f (Wt i))).prod := rfl
  have hVeq : V = coneProjD m f Ginv := rfl
  have hGinvT : coneProjT m f Ginv = U := by
    rw [hGinveq, hUeq, coneProjT_prod_ofFn]
  -- Pointwise invertibility of the base factors.
  have hUpt : ∀ t : Tgt m, IsUnit (matEval n t U) := by
    intro t
    have h1 : matEval n t U
        = (List.ofFn (fun i : Fin K => 1 + matEval n t (Wt i))).prod := by
      rw [hUeq, matEval_list_prod]
      have hlist : (List.ofFn (fun i : Fin K => matEval n t (1 + Wt i)))
          = (List.ofFn (fun i : Fin K => 1 + matEval n t (Wt i))) := by
        rw [List.ofFn_inj]
        funext i
        rw [map_add, map_one]
      rw [hlist]
    rw [h1]
    refine isUnit_list_prod fun A hA => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    exact isUnit_one_add_of_entry_bound _ (by positivity) (fun a b => hWtbd i a b t) (num_bound n)
  -- Pointwise invertibility of the cell factors.
  have hcellbd : ∀ (i : Fin K) (a b : Fin n) (z : Ball (Eu m × Eu m)),
      ‖matEval n z (coneProjD m f (coneMat m f (Wt i))) a b‖ ≤ 1 / (2 * ((n : ℝ) + 1)) := by
    intro i a b z
    have h1 : matEval n z (coneProjD m f (coneMat m f (Wt i))) a b
        = evalD m f z (coneMat m f (Wt i) a b) := by
      rw [matEval_apply_elem, coneProjD_apply_elem']
      rfl
    rw [h1]
    exact norm_coneMat_evalD_le m f (Wt i) (by positivity)
      (fun a b x => hWtbd i a b x) a b z
  have hVpt : ∀ z : Ball (Eu m × Eu m), IsUnit (matEval n z V) := by
    intro z
    have h1 : matEval n z V = (List.ofFn (fun i : Fin K =>
        1 + matEval n z (coneProjD m f (coneMat m f (Wt i))))).prod := by
      rw [hVeq, hGinveq, coneProjD_prod_ofFn, matEval_list_prod]
      have hlist : (List.ofFn (fun i : Fin K =>
            matEval n z (1 + coneProjD m f (coneMat m f (Wt i)))))
          = (List.ofFn (fun i : Fin K =>
              1 + matEval n z (coneProjD m f (coneMat m f (Wt i))))) := by
        rw [List.ofFn_inj]
        funext i
        rw [map_add, map_one]
      rw [hlist]
    rw [h1]
    refine isUnit_list_prod fun A hA => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    exact isUnit_one_add_of_entry_bound _ (by positivity) (fun a b => hcellbd i a b z) (num_bound n)
  -- The collaring of the cell matrix.
  have hVc : Collared V := by
    have h1 : V = (List.ofFn (fun i : Fin K =>
        1 + coneProjD m f (coneMat m f (Wt i)))).prod := by
      rw [hVeq, hGinveq, coneProjD_prod_ofFn]
    rw [h1]
    refine Collared.list_prod fun A hA => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hA
    refine Collared.add Collared.one ?_
    intro z hz
    rw [matEval_apply, matEval_apply]
    rw [coneProjD_map_evalC m f (coneMat m f (Wt i)) z,
      coneProjD_map_evalC m f (coneMat m f (Wt i)) (normPtBall z)]
    exact coneMat_evalD_collared m f (Wt i) hz
  -- The two inverses.
  obtain ⟨Uinv, hUinv1, hUinv2, hUinv_pt⟩ :=
    mat_inv_of_forall_isUnit U fun t => by
      rw [← matEval_apply]
      exact hUpt t
  obtain ⟨Vinv, hVinv1, hVinv2, hVinv_pt⟩ :=
    mat_inv_of_forall_isUnit V fun z => by
      rw [← matEval_apply]
      exact hVpt z
  -- Compatibility of the two inverses on the boundary sphere.
  have hcompat : ∀ (i j : Fin n) (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1),
      Vinv i j y = Uinv i j (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩) := by
    intro i j y hy
    have hc : V.map (fun F => evalC y F)
        = U.map (fun F => evalC (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩) F) := by
      ext a b
      have hmem := (Ginv a b).2 y hy
      rw [Matrix.map_apply, Matrix.map_apply, hVeq, ← hGinvT,
        coneProjD_apply_elem', coneProjT_apply_elem']
      exact hmem
    have h3 : Vinv.map (fun F => evalC y F)
        = Uinv.map (fun F => evalC (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩) F) := by
      rw [hVinv_pt y, hc, ← hUinv_pt (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)]
    have h4 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h3
    rwa [Matrix.map_apply, Matrix.map_apply] at h4
  -- The glued conjugating matrix.
  let g : Matrix (Fin n) (Fin n) (coneAlg f) :=
    coneGlue m f Uinv Vinv fun i j y hy => hcompat i j y hy
  have hgeq : g = coneGlue m f Uinv Vinv (fun i j y hy => hcompat i j y hy) := rfl
  have hgT : coneProjT m f g = Uinv := by rw [hgeq, coneProjT_coneGlue]
  have hgD : coneProjD m f g = Vinv := by rw [hgeq, coneProjD_coneGlue]
  -- Collaredness of the cell part of `P`.
  have hPc : Collared (coneProjD m f P) := by
    intro z hz
    rw [matEval_apply, matEval_apply]
    rw [coneProjD_map_evalC m f P z, coneProjD_map_evalC m f P (normPtBall z)]
    exact hrad z hz
  have hVinv_c : Collared Vinv := Collared.inv hVc fun z => hVinv_pt z
  refine ⟨g, Ginv, ?_, ?_, ?_, ?_, ?_⟩
  · -- `g * Ginv = 1`
    refine coneProj_ext m f ?_ ?_
    · rw [map_mul, map_one, hgT, hGinvT, hUinv2]
    · rw [map_mul, map_one, hgD]
      exact hVinv2
  · -- `Ginv * g = 1`
    refine coneProj_ext m f ?_ ?_
    · rw [map_mul, map_one, hgT, hGinvT, hUinv1]
    · rw [map_mul, map_one, hgD]
      exact hVinv1
  · -- the cap condition
    intro t ht
    have htelU : matEval n t U * diagIdemMat r n = P.map (evalT m f t) * matEval n t U := by
      have hL : restrictMat m cap n U = (List.ofFn (fun i : Fin K => 1 + W i)).prod := by
        rw [hUeq, map_list_prod, ofFn_map_eq]
        have hlist : (List.ofFn (fun i : Fin K => restrictMat m cap n (1 + Wt i)))
            = (List.ofFn (fun i : Fin K => 1 + W i)) := by
          rw [List.ofFn_inj]
          funext i
          rw [map_add, map_one]
          congr 1
          ext a b y
          exact hWtres i a b y
        rw [hlist]
      have hP0 : Q.map (fun f => sliceAt 0 f) = restrictMat m cap n (coneProjT m f P) := by
        ext a b y
        simp only [Matrix.map_apply]
        rw [sliceAt_apply_pair, hQab, hH0 y]
        rfl
      have hP1 : Q.map (fun f => sliceAt 1 f) = constMat (X := cap) (diagIdemMat r n) := by
        ext a b y
        simp only [Matrix.map_apply, constMat]
        rw [sliceAt_apply_pair, hQab, hH1 y]
        simpa using congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M a b) hPt0
      have htel' := hWtel
      rw [hP1, hP0, ← hL] at htel'
      have h2 := congrArg (matEval n (⟨t, ht⟩ : cap)) htel'
      rw [map_mul, map_mul, matEval_restrictMat, matEval_constMat, matEval_restrictMat,
        matEval_coneProjT] at h2
      exact h2
    have ha : matEval n t Uinv * matEval n t U = 1 := by
      have h := congrArg (matEval n t) hUinv2
      rwa [map_mul, map_one] at h
    have hg : g.map (evalT m f t) = matEval n t Uinv := by
      rw [← coneProjT_map_evalC m f g t, hgT, matEval_apply]
    have hgi : Ginv.map (evalT m f t) = matEval n t U := by
      rw [← coneProjT_map_evalC m f Ginv t, hGinvT, matEval_apply]
    rw [Matrix.map_mul, Matrix.map_mul, hg, hgi]
    calc matEval n t Uinv * P.map (evalT m f t) * matEval n t U
        = matEval n t Uinv * (P.map (evalT m f t) * matEval n t U) := Matrix.mul_assoc _ _ _
      _ = matEval n t Uinv * (matEval n t U * diagIdemMat r n) := by rw [← htelU]
      _ = (matEval n t Uinv * matEval n t U) * diagIdemMat r n := (Matrix.mul_assoc _ _ _).symm
      _ = 1 * diagIdemMat r n := by rw [ha]
      _ = diagIdemMat r n := one_mul _
  · -- the collaring of `g * P * Ginv`
    intro z hz
    have hproj : coneProjD m f (g * P * Ginv) = Vinv * coneProjD m f P * V := by
      rw [map_mul, map_mul, hgD]
    have hconj : Collared (Vinv * coneProjD m f P * V) := hVinv_c.conj hPc hVc
    rw [← coneProjD_map_evalC m f (g * P * Ginv) z,
      ← coneProjD_map_evalC m f (g * P * Ginv) (normPtBall z), hproj]
    exact hconj z hz
  · -- the collaring of `g`
    intro z hz
    rw [← coneProjD_map_evalC m f g z, ← coneProjD_map_evalC m f g (normPtBall z), hgD]
    exact hVinv_c z hz

/-- **Collared representatives.**  Let `P` be an idempotent matrix over the mapping cone `C_f`
whose value at a point `t0` of both closed caps is the diagonal idempotent `diag(1_r,0)`, and whose
cell component is radially collared (constant along rays of norm `≥ 1/2`).  Then `P` is conjugate,
by an invertible matrix over `C_f` whose cell component is itself radially collared, to an
idempotent which is *equal to the constant* `diag(1_r,0)` on the cap `{tgtHeight ≥ -1/2}` and is
still radially collared in the cell; and likewise for the cap `{tgtHeight ≤ 1/2}`.
The radial collaring of `P` is what makes the modification of the base component compatible with
the cell component; the radial collaring of the conjugating matrix is what keeps the conclusion
collared. -/
theorem hk_cap_triv (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m)))
    (f : C(Sph (Eu m × Eu m), Tgt m)) (t0 : Tgt m)
    (ht0p : t0 ∈ capTplus m) (ht0m : t0 ∈ capTminus m)
    (n r : ℕ) (P : Matrix (Fin n) (Fin n) (coneAlg f)) (hP : P * P = P)
    (hPt0 : P.map (evalT m f t0) = diagIdemMat r n)
    (hrad : ∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
      P.map (evalD m f z) = P.map (evalD m f (normPtBall z))) :
    (∃ g ginv : Matrix (Fin n) (Fin n) (coneAlg f), g * ginv = 1 ∧ ginv * g = 1 ∧
        (∀ t, t ∈ capTplus m → (g * P * ginv).map (evalT m f t) = diagIdemMat r n) ∧
        (∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
          (g * P * ginv).map (evalD m f z) =
            (g * P * ginv).map (evalD m f (normPtBall z))) ∧
        (∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
          g.map (evalD m f z) = g.map (evalD m f (normPtBall z)))) ∧
      (∃ g ginv : Matrix (Fin n) (Fin n) (coneAlg f), g * ginv = 1 ∧ ginv * g = 1 ∧
        (∀ t, t ∈ capTminus m → (g * P * ginv).map (evalT m f t) = diagIdemMat r n) ∧
        (∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
          (g * P * ginv).map (evalD m f z) =
            (g * P * ginv).map (evalD m f (normPtBall z))) ∧
        (∀ z : Ball (Eu m × Eu m), (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖ →
          g.map (evalD m f z) = g.map (evalD m f (normPtBall z)))) := by
  constructor
  · exact hk_cap_triv_of_cap m f (capTplus m) t0 ht0p (isClosed_capTplus m)
      (capTplus_contract m t0 ht0p) n r P hP hPt0 hrad
  · exact hk_cap_triv_of_cap m f (capTminus m) t0 ht0m (isClosed_capTminus m)
      (capTminus_contract m t0 ht0m) n r P hP hPt0 hrad

end

end Work.KT
