import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Fund.Basic
import Submission.Work.KT.Basic
import Submission.Work.KT.SphereAux
import Submission.Work.KT.hk_k0_eq_diff
import Submission.Work.KT.homInv_cls_eq_of_conj
import Submission.Work.KT.isUnit_one_sub_of_matNorm_lt_one
import Submission.Work.KT.idem_close_conj_of_isUnit
import Submission.Work.KT.chain_conjugation

/-!
# `Work.KT.SG.kpair_R_vanishing`

`K̃(S¹) = 0` in the `Kpair` model: the augmentation `augPair ℝ y0` is injective on `K₀(Kpair ℝ)`.

This is the statement of `Work.KT.ballK_dim1`, transported into the `Work.KT.SG` namespace so
that the (many) auxiliary declarations it needs do not collide with `ballK_dim1`'s own
declarations.  The whole body below is a copy of `Submission/Work/KT/ballK_dim1.lean`, with the
only change that `import Submission.Work.KT.Fund.Basic` has been added (the file needs
`K0.map_cls` in its `IsIdem`-flavoured form, which lives there).
-/

/-!
# `Work.KT.ballK_dim1`

`K̃(D¹/S⁰) = 0`: on the closed interval `[-1,1]` every idempotent matrix which is constant on the
boundary is stably trivial, i.e. the augmentation `augPair ℝ y0 : Kpair ℝ → ℂ` induces an
injective map `K₀(Kpair ℝ) → K₀(ℂ)`.
-/

namespace Work.KT.SG

open Matrix Polynomial

noncomputable section

/-! ## Evaluation of `Kpair ℝ` at a point -/

/-- Evaluation of an element of `Kpair ℝ` at a point of the closed unit ball of `ℝ`, as a ring
homomorphism. -/
def evY (y : Ball ℝ) : Kpair ℝ →+* ℂ := ((evalC y).comp (Kpair ℝ).val).toRingHom

@[simp] lemma evY_apply (y : Ball ℝ) (f : Kpair ℝ) :
    evY y f = ((f : C(Ball ℝ, ℂ))) y := rfl

/-- The value matrix of a matrix over `Kpair ℝ` at a point of the ball. -/
def valMat (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair ℝ)) (y : Ball ℝ) :
    Matrix (Fin n) (Fin n) ℂ := M.map (evY y)

@[simp] lemma valMat_apply (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair ℝ)) (y : Ball ℝ)
    (i j : Fin n) : valMat n M y i j = ((M i j : Kpair ℝ) : C(Ball ℝ, ℂ)) y := rfl

/-- The constant matrix over `Kpair ℝ` with prescribed value. -/
def constMat (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) (Kpair ℝ) :=
  M.map (algebraMap ℂ (Kpair ℝ))

/-- The point `1` of the closed unit ball of `ℝ`. -/
abbrev ptOne : Ball ℝ := ⟨1, by simp [Metric.mem_closedBall]⟩

/-- The point `-1` of the closed unit ball of `ℝ`. -/
abbrev ptNegOne : Ball ℝ := ⟨-1, by simp [Metric.mem_closedBall]⟩

lemma ptOne_mem_bdry : ptOne ∈ bdry ℝ := by simp [bdry, ptOne]
lemma ptNegOne_mem_bdry : ptNegOne ∈ bdry ℝ := by simp [bdry, ptNegOne]

lemma bdry_eq (y : Ball ℝ) (hy : y ∈ bdry ℝ) : y = ptOne ∨ y = ptNegOne := by
  have h : ‖(y : ℝ)‖ = 1 := hy
  rw [Real.norm_eq_abs] at h
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h with h1 | h1
  · exact Or.inl (Subtype.ext h1)
  · exact Or.inr (Subtype.ext h1)

lemma evY_ptOne_eq_evY_ptNegOne : evY ptOne = evY ptNegOne := by
  refine RingHom.ext fun f => ?_
  exact f.2 ptOne ptOne_mem_bdry ptNegOne ptNegOne_mem_bdry

/-- The value at any boundary point of a matrix over `Kpair ℝ`. -/
lemma valMat_bdry_eq (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair ℝ)) {y : Ball ℝ}
    (hy : y ∈ bdry ℝ) : valMat n M y = valMat n M ptOne := by
  rcases bdry_eq y hy with rfl | rfl
  · rfl
  · simp only [valMat, evY_ptOne_eq_evY_ptNegOne]

lemma valMat_ptOne_eq_ptNegOne (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair ℝ)) :
    valMat n M ptOne = valMat n M ptNegOne := by
  simp only [valMat, evY_ptOne_eq_evY_ptNegOne]

lemma valMat_mul (n : ℕ) (M N : Matrix (Fin n) (Fin n) (Kpair ℝ)) (y : Ball ℝ) :
    valMat n (M * N) y = valMat n M y * valMat n N y := by
  simp only [valMat, Matrix.map_mul]

lemma valMat_idem (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair ℝ)) (hM : M * M = M) (y : Ball ℝ) :
    valMat n M y * valMat n M y = valMat n M y := by
  rw [← valMat_mul, hM]

lemma evY_algebraMap (y : Ball ℝ) (c : ℂ) : evY y (algebraMap ℂ (Kpair ℝ) c) = c := by
  simp [evY_apply]

lemma valMat_constMat (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (y : Ball ℝ) :
    valMat n (constMat n M) y = M := by
  ext i j
  simp only [valMat_apply, constMat, Matrix.map_apply]
  exact evY_algebraMap y (M i j)

lemma continuous_valMat (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair ℝ)) :
    Continuous (valMat n M) := by
  apply continuous_matrix
  intro i j
  simpa only [valMat_apply] using ((M i j : Kpair ℝ) : C(Ball ℝ, ℂ)).continuous

/-- Two matrices over `Kpair ℝ` are equal as soon as all their value matrices are equal. -/
lemma eq_of_forall_valMat_eq {n : ℕ} {M N : Matrix (Fin n) (Fin n) (Kpair ℝ)}
    (h : ∀ y : Ball ℝ, valMat n M y = valMat n N y) : M = N := by
  refine Matrix.ext fun i j => Subtype.ext (ContinuousMap.ext fun y => ?_)
  simpa only [valMat_apply] using congrFun (congrFun (h y) i) j

/-! ## Units of `Kpair ℝ` and of matrices over it -/

/-- An element of `Kpair ℝ` is a unit iff its value at every point of the ball is non-zero. -/
theorem isUnit_iff_forall_evY_ne (h : Kpair ℝ) :
    IsUnit h ↔ ∀ y : Ball ℝ, evY y h ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ y
    have h1 : evY y ((u : Kpair ℝ) * (↑u⁻¹ : Kpair ℝ)) = evY y 1 := by
      rw [Units.mul_inv]
    rw [map_mul, map_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  · intro hne
    have hne' : ∀ y : Ball ℝ, ((h : Kpair ℝ) : C(Ball ℝ, ℂ)) y ≠ 0 := fun y => hne y
    have hcont : Continuous fun y : Ball ℝ => (((h : Kpair ℝ) : C(Ball ℝ, ℂ)) y)⁻¹ :=
      ((h : Kpair ℝ) : C(Ball ℝ, ℂ)).continuous.inv₀ hne'
    have hmem : ∀ a ∈ bdry ℝ, ∀ a' ∈ bdry ℝ,
        (⟨fun y : Ball ℝ => (((h : Kpair ℝ) : C(Ball ℝ, ℂ)) y)⁻¹, hcont⟩ : C(Ball ℝ, ℂ)) a
          = (⟨fun y : Ball ℝ => (((h : Kpair ℝ) : C(Ball ℝ, ℂ)) y)⁻¹, hcont⟩ : C(Ball ℝ, ℂ)) a' := by
      intro a ha a' ha'
      simp only [ContinuousMap.coe_mk]
      rw [h.2 a ha a' ha']
    let h' : Kpair ℝ :=
      ⟨⟨fun y : Ball ℝ => (((h : Kpair ℝ) : C(Ball ℝ, ℂ)) y)⁻¹, hcont⟩, hmem⟩
    have hmul : h * h' = 1 := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro y
      show (((h : Kpair ℝ) : C(Ball ℝ, ℂ)) y) * (((h' : Kpair ℝ) : C(Ball ℝ, ℂ)) y) = 1
      simp only [h', ContinuousMap.coe_mk]
      exact mul_inv_cancel₀ (hne' y)
    have hmul' : h' * h = 1 := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro y
      show (((h' : Kpair ℝ) : C(Ball ℝ, ℂ)) y) * (((h : Kpair ℝ) : C(Ball ℝ, ℂ)) y) = 1
      simp only [h', ContinuousMap.coe_mk]
      exact inv_mul_cancel₀ (hne' y)
    exact ⟨⟨h, h', hmul, hmul'⟩, rfl⟩

/-- A matrix over `Kpair ℝ` is a unit iff all its value matrices are invertible. -/
theorem isUnit_iff_forall_valMat_isUnit (n : ℕ) (M : Matrix (Fin n) (Fin n) (Kpair ℝ)) :
    IsUnit M ↔ ∀ y : Ball ℝ, IsUnit (valMat n M y) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_forall_evY_ne]
  constructor
  · intro h y
    have hmap : (evY y).mapMatrix M = valMat n M y := by ext i j; rfl
    have hdet : (valMat n M y).det = (evY y) M.det := by
      rw [← hmap]; exact (RingHom.map_det (evY y) M).symm
    rw [Matrix.isUnit_iff_isUnit_det, hdet, isUnit_iff_ne_zero]
    exact h y
  · intro h y
    have hmap : (evY y).mapMatrix M = valMat n M y := by ext i j; rfl
    have hdet : (valMat n M y).det = (evY y) M.det := by
      rw [← hmap]; exact (RingHom.map_det (evY y) M).symm
    rw [← hdet]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (h y)).ne_zero

/-! ## Reduction to matrices of functions -/

lemma continuous_matrix_apply {X : Type*} [TopologicalSpace X] {n : ℕ}
    {f : X → Matrix (Fin n) (Fin n) ℂ} (hf : Continuous f) (i j : Fin n) :
    Continuous fun x => f x i j := by
  have h : Continuous (((fun g : Fin n → ℂ => g j) ∘
      (fun M : Fin n → Fin n → ℂ => M i)) ∘ f) :=
    ((continuous_apply j).comp (continuous_apply i)).comp hf
  convert h using 1
  ext x; rfl

/-- Package a function on the ball into `Kpair ℝ`. -/
def mkKp (f : C(Ball ℝ, ℂ))
    (hf : ∀ a ∈ bdry ℝ, ∀ a' ∈ bdry ℝ, f a = f a') : Kpair ℝ := ⟨f, hf⟩

@[simp] lemma mkKp_coe (f : C(Ball ℝ, ℂ)) (hf) :
    ((mkKp f hf : Kpair ℝ) : C(Ball ℝ, ℂ)) = f := rfl

/-- A continuous, boundary-matching family of matrices is a matrix over `Kpair ℝ`. -/
def toKpair (n : ℕ) (X : Ball ℝ → Matrix (Fin n) (Fin n) ℂ) (hcont : Continuous X)
    (hmatch : X ptOne = X ptNegOne) : Matrix (Fin n) (Fin n) (Kpair ℝ) :=
  fun i j => mkKp ⟨fun y => X y i j, continuous_matrix_apply hcont i j⟩ (by
      intro a ha a' ha'
      simp only [ContinuousMap.coe_mk]
      rcases bdry_eq a ha with rfl | rfl <;> rcases bdry_eq a' ha' with rfl | rfl
      · rfl
      · exact congrFun (congrFun hmatch i) j
      · exact (congrFun (congrFun hmatch i) j).symm
      · rfl)

@[simp] lemma valMat_toKpair (n : ℕ) (X : Ball ℝ → Matrix (Fin n) (Fin n) ℂ) (hcont : Continuous X)
    (hmatch : X ptOne = X ptNegOne) (y : Ball ℝ) :
    valMat n (toKpair n X hcont hmatch) y = X y := by
  ext i j; rfl

/-- A continuous family of invertible matrices with matching end points is a unit of the matrix
ring over `Kpair ℝ`. -/
lemma isUnit_toKpair (n : ℕ) (X : Ball ℝ → Matrix (Fin n) (Fin n) ℂ) (hcont : Continuous X)
    (hmatch : X ptOne = X ptNegOne) (hunit : ∀ y, IsUnit (X y)) :
    IsUnit (toKpair n X hcont hmatch) := by
  rw [isUnit_iff_forall_valMat_isUnit]
  intro y
  rw [valMat_toKpair]
  exact hunit y

/-! ## The affine parameter `[-1,1] → [0,1]` -/

/-- The affine parameter `y ↦ (1 - y)/2` from the ball to the unit interval, used to build the
correction at the two ends of the interval. -/
def psi : C(Ball ℝ, unitInterval) where
  toFun y := ⟨(1 - (y : ℝ)) / 2, by
    have hy : |(y : ℝ)| ≤ 1 := by
      have h := Metric.mem_closedBall.mp y.2
      rwa [dist_zero_right, Real.norm_eq_abs] at h
    exact ⟨by linarith [(abs_le.mp hy).2], by linarith [(abs_le.mp hy).1]⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

@[simp] lemma psi_apply (y : Ball ℝ) : ((psi y : unitInterval) : ℝ) = (1 - (y : ℝ)) / 2 := rfl

@[simp] lemma psi_ptOne : psi ptOne = 0 := by
  apply Subtype.ext
  simp [psi, ptOne]

@[simp] lemma psi_ptNegOne : psi ptNegOne = 1 := by
  apply Subtype.ext
  simp [psi, ptNegOne]

/-! ## Paths of units avoiding finitely many parameters -/

/-- A complex polynomial non-vanishing at `0` and `1` has a path from `0` to `1` avoiding its
roots. -/
theorem path_avoid_roots (P : ℂ[X]) (h0 : P.eval 0 ≠ 0) (h1 : P.eval 1 ≠ 0) :
    ∃ σ : unitInterval → ℂ, Continuous σ ∧ σ 0 = 0 ∧ σ 1 = 1 ∧ ∀ t, P.eval (σ t) ≠ 0 := by
  have hPne : P ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hfin : {z : ℂ | P.IsRoot z}.Finite := Polynomial.finite_setOf_isRoot hPne
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank ℝ ℂ, Complex.finrank_real_complex]
    norm_num
  have hconn : IsPathConnected ({z : ℂ | P.IsRoot z}ᶜ) :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hfin.countable
  have h0c : (0:ℂ) ∈ {z : ℂ | P.IsRoot z}ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    exact h0
  have h1c : (1:ℂ) ∈ {z : ℂ | P.IsRoot z}ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
    exact h1
  obtain ⟨γ, hγ⟩ := hconn.joinedIn (0:ℂ) h0c (1:ℂ) h1c
  exact ⟨γ, γ.continuous, γ.source, γ.target, fun t => hγ t⟩

/-- The units of `M_n(ℂ)` commuting with an idempotent `p` form a path connected set. -/
theorem stab_path (n : ℕ) (p u : Matrix (Fin n) (Fin n) ℂ) (hp : p * p = p) (hu : IsUnit u)
    (hup : u * p = p * u) :
    ∃ γ : unitInterval → Matrix (Fin n) (Fin n) ℂ, Continuous γ ∧ γ 0 = u ∧ γ 1 = 1 ∧
      (∀ t, IsUnit (γ t)) ∧ ∀ t, γ t * p = p * γ t := by
  set M : Matrix (Fin n) (Fin n) ℂ[X] :=
    Matrix.of fun i j => Polynomial.C (u i j) + Polynomial.X * Polynomial.C ((1 - u) i j) with hM
  set P : ℂ[X] := M.det with hP
  have heval : ∀ z : ℂ, P.eval z = (u + z • (1 - u)).det := by
    intro z
    have hcoe : (Polynomial.evalRingHom z) (M.det) = P.eval z := by
      rw [hP, Polynomial.coe_evalRingHom]
    have hmap : (Polynomial.evalRingHom z).mapMatrix M = (u + z • (1 - u)) := by
      rw [RingHom.mapMatrix_apply]
      ext i j
      show (Polynomial.evalRingHom z) (Polynomial.C (u i j) + Polynomial.X * Polynomial.C ((1 - u) i j))
        = (u + z • (1 - u)) i j
      rw [Polynomial.coe_evalRingHom]
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      simp [Matrix.add_apply, Matrix.smul_apply]
    calc P.eval z = (Polynomial.evalRingHom z) (M.det) := hcoe.symm
      _ = ((Polynomial.evalRingHom z).mapMatrix M).det := RingHom.map_det _ M
      _ = (u + z • (1 - u)).det := by rw [hmap]
  have h0 : P.eval 0 ≠ 0 := by
    rw [heval 0, zero_smul, add_zero]
    exact ((Matrix.isUnit_iff_isUnit_det u).mp hu).ne_zero
  have h1 : P.eval 1 ≠ 0 := by
    rw [heval 1, one_smul, add_sub_cancel]
    rw [Matrix.det_one]; exact one_ne_zero
  obtain ⟨σ, hσc, hσ0, hσ1, hσ⟩ := path_avoid_roots P h0 h1
  refine ⟨fun t => u + σ t • (1 - u), ?_, ?_, ?_, ?_, ?_⟩
  · apply continuous_matrix
    intro i j
    have h : Continuous fun t : unitInterval =>
        (u i j) + σ t * ((1 - u : Matrix (Fin n) (Fin n) ℂ) i j) :=
      continuous_const.add (hσc.mul continuous_const)
    convert h using 1
    ext t
    simp [Matrix.add_apply, Matrix.smul_apply]
  · simp [hσ0]
  · simp [hσ1]
  · intro t
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← heval (σ t)]
    exact hσ t
  · intro t
    show (u + σ t • (1 - u)) * p = p * (u + σ t • (1 - u))
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, hup]

/-! ## The triviality statement -/

/-- An idempotent matrix over `Kpair ℝ` has the same class as the constant matrix with its value at
any boundary point. -/
theorem cls_eq_const (n : ℕ) (P : Matrix (Fin n) (Fin n) (Kpair ℝ)) (hP : P * P = P)
    (y0 : Ball ℝ) (hy0 : y0 ∈ bdry ℝ) :
    cls (⟨n, P⟩ : Mat (Kpair ℝ)) = cls (⟨n, constMat n (valMat n P y0)⟩ : Mat (Kpair ℝ)) := by
  have hVy0 : valMat n P y0 = valMat n P ptOne := valMat_bdry_eq n P hy0
  rw [hVy0]
  set V : Matrix (Fin n) (Fin n) ℂ := valMat n P ptOne with hV
  have hVidem : V * V = V := valMat_idem n P hP ptOne
  -- the trivialisation over the interval
  obtain ⟨X, hXc, hXone, hXunit, hXconj⟩ :=
    chain_conjugation n (valMat n P) (continuous_valMat n P) (fun y => valMat_idem n P hP y)
  -- the monodromy `X ptNegOne` commutes with `V`
  have hMcomm : X ptNegOne * V = V * X ptNegOne := by
    have h := hXconj ptNegOne
    rw [← valMat_ptOne_eq_ptNegOne n P, ← hV] at h
    exact h
  -- the correction along a path in the commutant of `V`
  obtain ⟨γd, hγdc, hγd0, hγd1, hγdunit, hγdcomm⟩ :=
    stab_path n V (X ptNegOne) hVidem (hXunit ptNegOne) hMcomm
  set X' : Ball ℝ → Matrix (Fin n) (Fin n) ℂ := fun y => γd (psi y) * X y with hX'
  have hX'c : Continuous X' := (hγdc.comp psi.continuous).matrix_mul hXc
  have hX'one : X' ptOne = X ptNegOne := by
    simp only [hX', hγd0, psi_ptOne, hXone, mul_one]
  have hX'neg : X' ptNegOne = X ptNegOne := by
    simp only [hX', hγd1, psi_ptNegOne, one_mul]
  have hX'match : X' ptOne = X' ptNegOne := by rw [hX'one, hX'neg]
  have hX'unit : ∀ y, IsUnit (X' y) := fun y => (hγdunit (psi y)).mul (hXunit y)
  have hX'conj : ∀ y, X' y * valMat n P y = V * X' y := by
    intro y
    simp only [hX']
    show (γd (psi y) * X y) * valMat n P y = V * (γd (psi y) * X y)
    calc (γd (psi y) * X y) * valMat n P y
        = γd (psi y) * (X y * valMat n P y) := by rw [Matrix.mul_assoc]
      _ = γd (psi y) * (V * X y) := by rw [hXconj y, ← hV]
      _ = (γd (psi y) * V) * X y := by rw [Matrix.mul_assoc]
      _ = (V * γd (psi y)) * X y := by rw [hγdcomm (psi y)]
      _ = V * (γd (psi y) * X y) := by rw [Matrix.mul_assoc]
  -- the resulting unit of the matrix ring over `Kpair ℝ`
  have hUunit : IsUnit (toKpair n X' hX'c hX'match) :=
    isUnit_toKpair n X' hX'c hX'match hX'unit
  obtain ⟨UU, hUU⟩ := hUunit
  have hrel : (UU : Matrix (Fin n) (Fin n) (Kpair ℝ)) * P
      = constMat n V * (UU : Matrix (Fin n) (Fin n) (Kpair ℝ)) := by
    rw [hUU]
    apply eq_of_forall_valMat_eq
    intro y
    simp only [valMat_mul, valMat_toKpair, valMat_constMat]
    exact hX'conj y
  have hCidem : (constMat n V) * (constMat n V) = constMat n V := by
    rw [constMat, ← Matrix.map_mul, hVidem]
  exact (homInv_cls_eq_of_conj (constMat n V) P hCidem hP UU hrel).symm

/-- `K̃(D¹/S⁰) = 0`: the augmentation `Kpair ℝ → ℂ` induces an injection on `K₀`. -/
theorem ballK_dim1_SG (y0 : Ball ℝ) (hy0 : y0 ∈ bdry ℝ) :
    ∀ z : K0 (Kpair ℝ), K0.mapA (augPair ℝ y0) z = 0 → z = 0 := by
  intro z hz
  obtain ⟨n, P, Q, hP, hQ, hzPQ⟩ := hk_k0_eq_diff (Kpair ℝ) z
  have hvalP : K0.map (evY y0) (cls (⟨n, P⟩ : Mat (Kpair ℝ)))
      = cls (⟨n, valMat n P y0⟩ : Mat ℂ) := by
    rw [K0.map_cls (evY y0) (show Mat.IsIdem (⟨n, P⟩ : Mat (Kpair ℝ)) from hP)]; rfl
  have hvalQ : K0.map (evY y0) (cls (⟨n, Q⟩ : Mat (Kpair ℝ)))
      = cls (⟨n, valMat n Q y0⟩ : Mat ℂ) := by
    rw [K0.map_cls (evY y0) (show Mat.IsIdem (⟨n, Q⟩ : Mat (Kpair ℝ)) from hQ)]; rfl
  have hconstP : K0.map (algebraMap ℂ (Kpair ℝ)) (cls (⟨n, valMat n P y0⟩ : Mat ℂ))
      = cls (⟨n, P⟩ : Mat (Kpair ℝ)) := by
    rw [K0.map_cls (algebraMap ℂ (Kpair ℝ))
      (show Mat.IsIdem (⟨n, valMat n P y0⟩ : Mat ℂ) from valMat_idem n P hP y0)]
    exact (cls_eq_const n P hP y0 hy0).symm
  have hconstQ : K0.map (algebraMap ℂ (Kpair ℝ)) (cls (⟨n, valMat n Q y0⟩ : Mat ℂ))
      = cls (⟨n, Q⟩ : Mat (Kpair ℝ)) := by
    rw [K0.map_cls (algebraMap ℂ (Kpair ℝ))
      (show Mat.IsIdem (⟨n, valMat n Q y0⟩ : Mat ℂ) from valMat_idem n Q hQ y0)]
    exact (cls_eq_const n Q hQ y0 hy0).symm
  have hz' : K0.map (evY y0) z = 0 := hz
  have key : K0.map (algebraMap ℂ (Kpair ℝ)) (K0.map (evY y0) z) = z := by
    rw [hzPQ]
    simp only [map_sub, hvalP, hvalQ, hconstP, hconstQ]
  rw [← key, hz', map_zero]


/-! ## The target lemma -/

/-- `K̃(S¹) = 0` in the `Kpair` model: the augmentation `augPair ℝ y0` is injective on
`K₀(Kpair ℝ)`. -/
theorem kpair_R_vanishing (y0 : Work.KT.Ball ℝ) (hy0 : y0 ∈ Work.KT.bdry ℝ) :
    ∀ z : Work.KT.K0 (Work.KT.Kpair ℝ), Work.KT.K0.mapA (Work.KT.augPair ℝ y0) z = 0 → z = 0 :=
  ballK_dim1_SG y0 hy0

end

end Work.KT.SG
