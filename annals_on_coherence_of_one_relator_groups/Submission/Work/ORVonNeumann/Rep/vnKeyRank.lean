import Mathlib
import Submission.Work.ORVonNeumann.Rep.vnCore
import Submission.Work.ORVonNeumann.Rep.vnMatOpMul
import Submission.Work.ORVonNeumann.Rep.vnMatOpAdjoint
import Submission.Work.ORVonNeumann.Rep.vnInnerHdelta
import Submission.Work.ORVonNeumann.Rep.vnHdimCompl
import Submission.Work.Rep.tau_tracial
import Submission.Work.ORVonNeumann.Rep.vnMTraceTracial
import Submission.Work.ORVonNeumann.Rep.vnResolventBasic
import Submission.Work.ORVonNeumann.Rep.vnExistsInvAdd
import Submission.Work.ORVonNeumann.Rep.vnDiag
import Submission.Work.ORVonNeumann.Rep.vnCyclicTrace
import Submission.Work.ORVonNeumann.Rep.vnMatOpEquivariant

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped InnerProductSpace

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G]

/-! ### The operator trace on `HSum m` -/

/-- The operator trace on `HSum m`. -/
noncomputable def opTrace {m : ℕ} (A : HSum (G := G) m →L[ℂ] HSum (G := G) m) : ℂ :=
  ∑ i : Fin m, inner ℂ (hdelta (G := G) m i) (A (hdelta (G := G) m i))

theorem opTrace_matOp {m : ℕ} (M : Matrix (Fin m) (Fin m) (↥(groupVonNeumann G))) :
    opTrace (G := G) (matOp (G := G) M) = mTrace (G := G) m M := by
  rw [opTrace, mTrace_apply]
  exact Finset.sum_congr rfl fun i _ => vnInnerHdelta (G := G) M i

theorem opTrace_add {m : ℕ} (A B : HSum (G := G) m →L[ℂ] HSum (G := G) m) :
    opTrace (G := G) (A + B) = opTrace (G := G) A + opTrace (G := G) B := by
  rw [opTrace, opTrace, opTrace, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [add_apply, inner_add_right]

theorem opTrace_neg {m : ℕ} (A : HSum (G := G) m →L[ℂ] HSum (G := G) m) :
    opTrace (G := G) (-A) = -opTrace (G := G) A := by
  rw [opTrace, opTrace, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [neg_apply, inner_neg_right]

theorem opTrace_sub {m : ℕ} (A B : HSum (G := G) m →L[ℂ] HSum (G := G) m) :
    opTrace (G := G) (A - B) = opTrace (G := G) A - opTrace (G := G) B := by
  rw [sub_eq_add_neg, opTrace_add, opTrace_neg, sub_eq_add_neg]

theorem opTrace_one (m : ℕ) :
    opTrace (G := G) (1 : HSum (G := G) m →L[ℂ] HSum (G := G) m) = (m : ℂ) := by
  rw [opTrace,
    Finset.sum_congr rfl (fun i _ => by rw [one_apply_eq_self, vnInnerHdeltaSelf])]
  simp

theorem opTrace_smulC {m : ℕ} (c : ℂ) (A : HSum (G := G) m →L[ℂ] HSum (G := G) m) :
    opTrace (G := G) (c • A) = c * opTrace (G := G) A := by
  rw [opTrace, opTrace, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, inner_smul_right]

theorem opTrace_real_smul (c : ℝ) {m : ℕ} (A : HSum (G := G) m →L[ℂ] HSum (G := G) m) :
    opTrace (G := G) (c • A) = (c : ℂ) * opTrace (G := G) A := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c A]
  exact opTrace_smulC (G := G) (c : ℂ) A

/-- The operator trace is cyclic on equivariant operators. -/
theorem opTrace_cyclic {m n : ℕ} (X : HSum (G := G) m →L[ℂ] HSum (G := G) n)
    (Y : HSum (G := G) n →L[ℂ] HSum (G := G) m)
    (hX : Equivariant (G := G) X) (hY : Equivariant (G := G) Y) :
    opTrace (G := G) (X.comp Y) = opTrace (G := G) (Y.comp X) :=
  vnCyclicTrace (G := G) X Y hX hY

/-! ### Kernel identifications -/

/-- `ker (A† ∘ A) = ker A`. -/
theorem ker_comp_adjoint_self {n m : ℕ} (A : HSum (G := G) m →L[ℂ] HSum (G := G) n) :
    ((ContinuousLinearMap.adjoint A).comp A).ker = A.ker := by
  ext u
  show (((ContinuousLinearMap.adjoint A).comp A) u = 0) ↔ (A u = 0)
  constructor
  · intro hu
    have h : inner ℂ (((ContinuousLinearMap.adjoint A).comp A) u) u = 0 := by
      rw [hu, inner_zero_left]
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left] at h
    exact inner_self_eq_zero.mp h
  · intro hu
    rw [ContinuousLinearMap.comp_apply, hu, map_zero]

theorem matOp_conjTranspose_mul_self {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) :
    matOp (G := G) (Matrix.conjTranspose X * X)
      = (ContinuousLinearMap.adjoint (matOp (G := G) X)).comp (matOp (G := G) X) := by
  rw [vnMatOpMul, vnMatOpAdjoint]

theorem matOp_mul_conjTranspose {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) :
    matOp (G := G) (X * Matrix.conjTranspose X)
      = (matOp (G := G) X).comp (ContinuousLinearMap.adjoint (matOp (G := G) X)) := by
  rw [vnMatOpMul, vnMatOpAdjoint]

/-- The kernel of `matOp X†` is the kernel of `matOp (X X†)`. -/
theorem ker_adjoint_eq {n m : ℕ} (X : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) :
    (ContinuousLinearMap.adjoint (matOp (G := G) X)).ker
      = (matOp (G := G) (X * Matrix.conjTranspose X)).ker := by
  rw [matOp_mul_conjTranspose]
  rw [← ker_comp_adjoint_self (G := G) (ContinuousLinearMap.adjoint (matOp (G := G) X)),
    ContinuousLinearMap.adjoint_adjoint]

theorem ker_matOp_eq {n m : ℕ} (X : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G))) :
    (matOp (G := G) X).ker = (matOp (G := G) (Matrix.conjTranspose X * X)).ker := by
  rw [matOp_conjTranspose_mul_self]
  exact (ker_comp_adjoint_self (G := G) (matOp (G := G) X)).symm

/-- `matOp (Y†Y)` is symmetric. -/
theorem matOp_sq_symm {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G)))
    (x y : HSum (G := G) q) :
    inner ℂ (matOp (G := G) (Matrix.conjTranspose Y * Y) x) y
      = inner ℂ x (matOp (G := G) (Matrix.conjTranspose Y * Y) y) := by
  rw [matOp_conjTranspose_mul_self, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- `matOp (Y†Y)` is positive. -/
theorem matOp_sq_nonneg {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G)))
    (u : HSum (G := G) q) :
    0 ≤ (inner ℂ (matOp (G := G) (Matrix.conjTranspose Y * Y) u) u).re := by
  have h := inner_self_nonneg (𝕜 := ℂ) (x := (matOp (G := G) Y) u)
  rw [matOp_conjTranspose_mul_self, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]
  exact h

theorem matOp_sq_adjoint {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) :
    ContinuousLinearMap.adjoint (matOp (G := G) (Matrix.conjTranspose Y * Y))
      = matOp (G := G) (Matrix.conjTranspose Y * Y) := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  exact matOp_sq_symm (G := G) Y x y

/-! ### The resolvent of `c + matOp (Y† Y)` -/

/-- The operator resolvent `(c + matOp (Y†Y))⁻¹`: for `c > 0` the (two-sided) inverse of
`c + matOp (Y†Y)`, whose existence is `vnExistsInvAdd`. -/
noncomputable def rvOp {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (c : ℝ) :
    HSum (G := G) q →L[ℂ] HSum (G := G) q :=
  if h : 0 < c then Classical.choose (vnExistsInvAdd (G := G) (matOp (G := G) Y) h) else 0

/-- The zero operator is equivariant. -/
theorem Equivariant.zero {m n : ℕ} :
    Equivariant (G := G) (0 : HSum (G := G) m →L[ℂ] HSum (G := G) n) := by
  intro g
  rw [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-- The inverse of an equivariant operator is equivariant, so the resolvent is equivariant. -/
theorem rvOp_equivariant {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (c : ℝ) :
    Equivariant (G := G) (rvOp (G := G) Y c) := by
  rw [rvOp]
  by_cases h : 0 < c
  · rw [dif_pos h]
    set S : HSum (G := G) q →L[ℂ] HSum (G := G) q :=
      Classical.choose (vnExistsInvAdd (G := G) (matOp (G := G) Y) h) with hS
    set A : HSum (G := G) q →L[ℂ] HSum (G := G) q :=
      (ContinuousLinearMap.adjoint (matOp (G := G) Y)).comp (matOp (G := G) Y)
        + (c : ℂ) • 1 with hA
    have hspec := Classical.choose_spec (vnExistsInvAdd (G := G) (matOp (G := G) Y) h)
    have hSA : S.comp A = 1 := by rw [hA]; exact hspec.1
    have hAS : A.comp S = 1 := by rw [hA]; exact hspec.2
    have hT : Equivariant (G := G) (matOp (G := G) Y) := vnMatOpEquivariant (G := G) Y
    have hT' : Equivariant (G := G) (ContinuousLinearMap.adjoint (matOp (G := G) Y)) := by
      rw [vnMatOpAdjoint]
      exact vnMatOpEquivariant (G := G) (Matrix.conjTranspose Y)
    have hAeq : Equivariant (G := G) A := by
      rw [hA]
      exact (hT.comp hT').add (Equivariant.smul (G := G) (c : ℂ) (Equivariant.one (G := G) q))
    intro g
    have hcomm : A.comp (diagOp (G := G) q g) = (diagOp (G := G) q g).comp A := hAeq g
    have hassoc : (diagOp (G := G) q g).comp (A.comp S) = ((diagOp (G := G) q g).comp A).comp S :=
      (ContinuousLinearMap.comp_assoc _ _ _).symm
    calc S.comp (diagOp (G := G) q g)
        = (S.comp (diagOp (G := G) q g)).comp (A.comp S) := by
          rw [hAS]
          simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
      _ = S.comp ((diagOp (G := G) q g).comp (A.comp S)) :=
          ContinuousLinearMap.comp_assoc _ _ _
      _ = S.comp (((diagOp (G := G) q g).comp A).comp S) := by
          rw [hassoc]
      _ = S.comp ((A.comp (diagOp (G := G) q g)).comp S) := by rw [hcomm]
      _ = S.comp (A.comp ((diagOp (G := G) q g).comp S)) := by
          rw [ContinuousLinearMap.comp_assoc]
      _ = (S.comp A).comp ((diagOp (G := G) q g).comp S) :=
          (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = (diagOp (G := G) q g).comp S := by
          rw [hSA]
          simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  · rw [dif_neg h]
    exact Equivariant.zero

/-- The matrix of the resolvent `(c + matOp (Y†Y))⁻¹`; it exists because the resolvent is
equivariant (`rvOp_equivariant`), and every equivariant operator is a matrix operator
(`matOp_matOfEquiv`). -/
noncomputable def rvMat {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) (c : ℝ) :
    Matrix (Fin q) (Fin q) (↥(groupVonNeumann G)) :=
  matOfEquiv (G := G) (rvOp (G := G) Y c) (rvOp_equivariant (G := G) Y c)

theorem rvOp_spec {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) {c : ℝ}
    (hc : 0 < c) :
    rvOp (G := G) Y c = matOp (G := G) (rvMat (G := G) Y c) ∧
    (c • 1 + matOp (G := G) (Matrix.conjTranspose Y * Y)) * rvOp (G := G) Y c = 1 ∧
    rvOp (G := G) Y c * (c • 1 + matOp (G := G) (Matrix.conjTranspose Y * Y)) = 1 := by
  have hmat : (ContinuousLinearMap.adjoint (matOp (G := G) Y)).comp (matOp (G := G) Y)
      = matOp (G := G) (Matrix.conjTranspose Y * Y) :=
    (matOp_conjTranspose_mul_self (G := G) Y).symm
  have hcc : ((c : ℂ) • (1 : HSum (G := G) q →L[ℂ] HSum (G := G) q))
      = c • (1 : HSum (G := G) q →L[ℂ] HSum (G := G) q) :=
    (RCLike.real_smul_eq_coe_smul (K := ℂ) c (1 : HSum (G := G) q →L[ℂ] HSum (G := G) q)).symm
  have heq : (c • (1 : HSum (G := G) q →L[ℂ] HSum (G := G) q)
        + matOp (G := G) (Matrix.conjTranspose Y * Y))
      = ((ContinuousLinearMap.adjoint (matOp (G := G) Y)).comp (matOp (G := G) Y)
          + (c : ℂ) • 1) := by
    rw [hmat, hcc, add_comm]
  have h1 : (rvOp (G := G) Y c).comp (c • (1 : HSum (G := G) q →L[ℂ] HSum (G := G) q)
      + matOp (G := G) (Matrix.conjTranspose Y * Y)) = 1 := by
    rw [rvOp, dif_pos hc, heq]
    exact (Classical.choose_spec (vnExistsInvAdd (G := G) (matOp (G := G) Y) hc)).1
  have h2 : (c • (1 : HSum (G := G) q →L[ℂ] HSum (G := G) q)
      + matOp (G := G) (Matrix.conjTranspose Y * Y)).comp (rvOp (G := G) Y c) = 1 := by
    rw [rvOp, dif_pos hc, heq]
    exact (Classical.choose_spec (vnExistsInvAdd (G := G) (matOp (G := G) Y) hc)).2
  exact ⟨by
      rw [rvMat]
      exact (matOp_matOfEquiv (G := G) (rvOp (G := G) Y c)
        (rvOp_equivariant (G := G) Y c)).symm, h2, h1⟩

/-- The resolvent is symmetric. -/
theorem rvOp_symm {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) {c : ℝ}
    (hc : 0 < c) (x y : HSum (G := G) q) :
    inner ℂ (rvOp (G := G) Y c x) y = inner ℂ x (rvOp (G := G) Y c y) := by
  obtain ⟨hmM, hm1, hm2⟩ := rvOp_spec (G := G) Y hc
  set A : HSum (G := G) q →L[ℂ] HSum (G := G) q :=
    c • 1 + matOp (G := G) (Matrix.conjTranspose Y * Y) with hA
  have hAsymm : ∀ u v : HSum (G := G) q, inner ℂ (A u) v = inner ℂ u (A v) := by
    intro u v
    rw [hA, add_apply, add_apply, inner_add_left, inner_add_right, smul_apply, smul_apply,
      one_apply_eq_self, one_apply_eq_self,
      RCLike.real_smul_eq_coe_smul (K := ℂ) c u,
      RCLike.real_smul_eq_coe_smul (K := ℂ) c v,
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal, matOp_sq_symm (G := G) Y u v]
  have hh : ∀ z : HSum (G := G) q, A (rvOp (G := G) Y c z) = z := by
    intro z
    have h := congrArg (fun (B : HSum (G := G) q →L[ℂ] HSum (G := G) q) => B z) hm1
    rw [show (A * rvOp (G := G) Y c) z = A (rvOp (G := G) Y c z) from rfl] at h
    simpa using h
  calc inner ℂ (rvOp (G := G) Y c x) y
      = inner ℂ (rvOp (G := G) Y c x) (A (rvOp (G := G) Y c y)) := by rw [hh y]
    _ = inner ℂ (A (rvOp (G := G) Y c x)) (rvOp (G := G) Y c y) := (hAsymm _ _).symm
    _ = inner ℂ x (rvOp (G := G) Y c y) := by rw [hh x]

/-! ### The properties of the resolvent as `c → 0` -/

theorem rv_basic {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) :
    (∀ c : ℝ, 0 < c → ∀ u : HSum (G := G) q, ‖(c • rvOp (G := G) Y c) u‖ ≤ ‖u‖) ∧
    (∀ c : ℝ, 0 < c →
      ∀ u ∈ (matOp (G := G) (Matrix.conjTranspose Y * Y)).ker, (c • rvOp (G := G) Y c) u = u) ∧
    (∀ u ∈ (matOp (G := G) (Matrix.conjTranspose Y * Y)).kerᗮ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ c : ℝ, 0 < c → c < δ → ‖(c • rvOp (G := G) Y c) u‖ < ε) :=
  vnResolventBasic (matOp (G := G) (Matrix.conjTranspose Y * Y))
    (matOp_sq_adjoint (G := G) Y) (matOp_sq_nonneg (G := G) Y) (rvOp (G := G) Y)
    (fun _ hc => ⟨(rvOp_spec (G := G) Y hc).2.1, (rvOp_spec (G := G) Y hc).2.2⟩)

/-! ### The trace identity for the resolvent -/

/-- **The trace identity of the resolvent.**  For every `c > 0` the amplified traces of the
resolvents of `X†X` and of `X X†` satisfy
`m - c · τ_m((c + X†X)⁻¹) = n - c · τ_n((c + X X†)⁻¹)`. -/
theorem rv_trace_identity {n m : ℕ} (X : Matrix (Fin n) (Fin m) (↥(groupVonNeumann G)))
    {c : ℝ} (hc : 0 < c) :
    (m : ℂ) - (c : ℂ) * mTrace (G := G) m (rvMat (G := G) X c)
      = (n : ℂ) - (c : ℂ) * mTrace (G := G) n (rvMat (G := G) (Matrix.conjTranspose X) c) := by
  obtain ⟨hmM, hm1, hm2⟩ := rvOp_spec (G := G) X hc
  obtain ⟨hnM, hn1, hn2⟩ := rvOp_spec (G := G) (Matrix.conjTranspose X) hc
  rw [← opTrace_matOp (G := G) (rvMat (G := G) X c), ← hmM,
    ← opTrace_matOp (G := G) (rvMat (G := G) (Matrix.conjTranspose X) c), ← hnM]
  have hTeq : Equivariant (G := G) (matOp (G := G) X) := vnMatOpEquivariant (G := G) X
  have hSeq : Equivariant (G := G) (matOp (G := G) (Matrix.conjTranspose X)) :=
    vnMatOpEquivariant (G := G) (Matrix.conjTranspose X)
  have hheq : Equivariant (G := G) (rvOp (G := G) X c) := rvOp_equivariant (G := G) X c
  have hYeq : Equivariant (G := G)
      ((rvOp (G := G) X c).comp (matOp (G := G) (Matrix.conjTranspose X))) :=
    hSeq.comp hheq
  set T : HSum (G := G) m →L[ℂ] HSum (G := G) n := matOp (G := G) X with hT
  set S : HSum (G := G) n →L[ℂ] HSum (G := G) m := matOp (G := G) (Matrix.conjTranspose X) with hS
  set h : HSum (G := G) m →L[ℂ] HSum (G := G) m := rvOp (G := G) X c with hh
  set h' : HSum (G := G) n →L[ℂ] HSum (G := G) n :=
    rvOp (G := G) (Matrix.conjTranspose X) c with hh'
  set A : HSum (G := G) m →L[ℂ] HSum (G := G) m
    := c • 1 + matOp (G := G) (Matrix.conjTranspose X * X) with hA
  set A' : HSum (G := G) n →L[ℂ] HSum (G := G) n
    := c • 1 + matOp (G := G) (X * Matrix.conjTranspose X) with hA'
  have hSadj : ContinuousLinearMap.adjoint T = S := by
    rw [hT, hS]; exact vnMatOpAdjoint (G := G) X
  have hBT : matOp (G := G) (Matrix.conjTranspose X * X) = S.comp T := by
    rw [matOp_conjTranspose_mul_self, ← hT, hSadj]
  have hBT' : matOp (G := G) (X * Matrix.conjTranspose X) = T.comp S := by
    rw [matOp_mul_conjTranspose, ← hT, hSadj]
  have hA1 : A.comp h = 1 := by rw [← ContinuousLinearMap.mul_def]; exact hm1
  have hA2 : h.comp A = 1 := by rw [← ContinuousLinearMap.mul_def]; exact hm2
  have hB1 : A'.comp h' = 1 := by
    rw [← ContinuousLinearMap.mul_def, hA']
    simpa only [Matrix.conjTranspose_conjTranspose] using hn1
  have hB2 : h'.comp A' = 1 := by
    rw [← ContinuousLinearMap.mul_def, hA']
    simpa only [Matrix.conjTranspose_conjTranspose] using hn2
  have hexpA : h.comp A = c • h + h.comp (S.comp T) := by
    rw [hA, hBT, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  have hexpB : h'.comp A' = c • h' + h'.comp (T.comp S) := by
    rw [hA', hBT', ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  have hcs : c • h = 1 - h.comp (S.comp T) := by
    rw [hexpA] at hA2
    exact eq_sub_of_add_eq hA2
  have hcs' : c • h' = 1 - h'.comp (T.comp S) := by
    rw [hexpB] at hB2
    exact eq_sub_of_add_eq hB2
  have hcm : T.comp (c • (1 : HSum (G := G) m →L[ℂ] HSum (G := G) m)) = c • T := by
    rw [ContinuousLinearMap.comp_smul]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
  have hcn : (c • (1 : HSum (G := G) n →L[ℂ] HSum (G := G) n)).comp T = c • T := by
    rw [ContinuousLinearMap.smul_comp]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  have hkey : T.comp A = A'.comp T := by
    rw [hA, hA', hBT, hBT', ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp, hcm, hcn,
      ContinuousLinearMap.comp_assoc]
  have hTh : h'.comp T = T.comp h := by
    have s1 : T.comp (A.comp h) = (T.comp A).comp h := (ContinuousLinearMap.comp_assoc T A h).symm
    have s2 : (T.comp A).comp h = (A'.comp T).comp h := by rw [hkey]
    have s3 : (A'.comp T).comp h = A'.comp (T.comp h) := ContinuousLinearMap.comp_assoc A' T h
    have s4 : h'.comp (A'.comp (T.comp h)) = (h'.comp A').comp (T.comp h) :=
      (ContinuousLinearMap.comp_assoc h' A' (T.comp h)).symm
    calc h'.comp T
        = (h'.comp T).comp (A.comp h) := by
          rw [hA1]
          simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
      _ = h'.comp (T.comp (A.comp h)) := ContinuousLinearMap.comp_assoc h' T (A.comp h)
      _ = h'.comp ((T.comp A).comp h) := by rw [s1]
      _ = h'.comp ((A'.comp T).comp h) := by rw [s2]
      _ = h'.comp (A'.comp (T.comp h)) := by rw [s3]
      _ = (h'.comp A').comp (T.comp h) := s4
      _ = T.comp h := by
          rw [hB2]
          simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  have hcyc : opTrace (G := G) (h.comp (S.comp T)) = opTrace (G := G) (h'.comp (T.comp S)) := by
    have h1 : h.comp (S.comp T) = (h.comp S).comp T := (ContinuousLinearMap.comp_assoc h S T).symm
    have h2 : (T.comp h).comp S = T.comp (h.comp S) := ContinuousLinearMap.comp_assoc T h S
    have h3 : h'.comp (T.comp S) = (h'.comp T).comp S :=
      (ContinuousLinearMap.comp_assoc h' T S).symm
    rw [h1, (opTrace_cyclic (G := G) T (h.comp S) hTeq hYeq).symm, ← h2, ← hTh, ← h3]
  have e1 : (c : ℂ) * opTrace (G := G) h = (m : ℂ) - opTrace (G := G) (h.comp (S.comp T)) := by
    calc (c : ℂ) * opTrace (G := G) h = opTrace (G := G) (c • h) :=
          (opTrace_real_smul (G := G) c h).symm
      _ = opTrace (G := G) (1 - h.comp (S.comp T)) := by rw [hcs]
      _ = (m : ℂ) - opTrace (G := G) (h.comp (S.comp T)) := by
          rw [opTrace_sub, opTrace_one]
  have e2 : (c : ℂ) * opTrace (G := G) h' = (n : ℂ) - opTrace (G := G) (h'.comp (T.comp S)) := by
    calc (c : ℂ) * opTrace (G := G) h' = opTrace (G := G) (c • h') :=
          (opTrace_real_smul (G := G) c h').symm
      _ = opTrace (G := G) (1 - h'.comp (T.comp S)) := by rw [hcs']
      _ = (n : ℂ) - opTrace (G := G) (h'.comp (T.comp S)) := by
          rw [opTrace_sub, opTrace_one]
  rw [e1, e2, hcyc]
  ring

/-! ### The limit of the trace of the resolvent -/

/-- **The limit identity.**  As `c → 0⁺`, the amplified trace of the resolvent of `Y†Y`
converges to the von Neumann dimension of the kernel of `matOp Y`. -/
theorem rv_limit {p q : ℕ} (Y : Matrix (Fin p) (Fin q) (↥(groupVonNeumann G))) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → c < δ →
      ‖(c : ℂ) * mTrace (G := G) q (rvMat (G := G) Y c)
        - ((hdim (G := G) (matOp (G := G) Y).ker : ℝ) : ℂ)‖ < ε := by
  intro ε hε
  obtain ⟨hb1, hb2, hb3⟩ := rv_basic (G := G) Y
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    refine ⟨1, one_pos, fun c hc _ => ?_⟩
    have h0 : mTrace (G := G) 0 (rvMat (G := G) Y c) = 0 := by simp [mTrace]
    have h1 : hdim (G := G) (matOp (G := G) Y).ker = 0 := by simp [hdim]
    rw [h0, h1]
    simpa using hε
  · have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    have hb2' : ∀ c : ℝ, 0 < c → ∀ u ∈ (matOp (G := G) Y).ker,
        (c • rvOp (G := G) Y c) u = u := by
      intro c hc u hu
      exact hb2 c hc u (by rwa [ker_matOp_eq (G := G) Y] at hu)
    have hb3' : ∀ u ∈ ((matOp (G := G) Y).ker)ᗮ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ c : ℝ, 0 < c → c < δ → ‖(c • rvOp (G := G) Y c) u‖ < ε := by
      intro u hu ε hε
      exact hb3 u (by rwa [ker_matOp_eq (G := G) Y] at hu) ε hε
    have hnorm : ∀ i : Fin q, ‖hdelta (G := G) q i‖ = 1 := fun i => by
      have h := vnNormSqHdelta (G := G) q i
      nlinarith [norm_nonneg (hdelta (G := G) q i)]
    have hper : ∀ i : Fin q, ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → c < δ →
        ‖(c • rvOp (G := G) Y c)
          (hdelta (G := G) q i
            - ((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i))‖ < ε / q := by
      intro i
      refine hb3' _ (Submodule.sub_starProjection_mem_orthogonal _) _ ?_
      positivity
    choose dfun hdfunpos hdfun using hper
    obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin q)) dfun
      Finset.univ_nonempty
    refine ⟨dfun i₀, hdfunpos i₀, fun c hc hcδ => ?_⟩
    have h1 : (c : ℂ) * mTrace (G := G) q (rvMat (G := G) Y c)
        = ∑ i : Fin q, inner ℂ (hdelta (G := G) q i)
            ((c • rvOp (G := G) Y c) (hdelta (G := G) q i)) := by
      rw [← opTrace_matOp (G := G) (rvMat (G := G) Y c), ← (rvOp_spec (G := G) Y hc).1,
        ← opTrace_real_smul (G := G) c (rvOp (G := G) Y c)]
      rfl
    have hprj : ∀ i : Fin q, inner ℂ (hdelta (G := G) q i)
          (((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i))
        = (((‖((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i)‖ : ℝ) : ℂ)) ^ 2 := by
      intro i
      set u := hdelta (G := G) q i with hu
      set P := ((matOp (G := G) Y).ker).starProjection u with hP
      have hPu : P ∈ (matOp (G := G) Y).ker := Submodule.starProjection_apply_mem _ _
      have h0 : inner ℂ (u - P) P = 0 := Submodule.starProjection_inner_eq_zero u P hPu
      have hdec : u = (u - P) + P := by abel
      rw [hdec, inner_add_left, h0, zero_add, inner_self_eq_norm_sq_to_K]
      exact rfl
    have h2 : ((hdim (G := G) (matOp (G := G) Y).ker : ℝ) : ℂ)
        = ∑ i : Fin q, inner ℂ (hdelta (G := G) q i)
            (((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i)) := by
      rw [hdim]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hprj i]
    have h3 : (c : ℂ) * mTrace (G := G) q (rvMat (G := G) Y c)
          - ((hdim (G := G) (matOp (G := G) Y).ker : ℝ) : ℂ)
        = ∑ i : Fin q, inner ℂ (hdelta (G := G) q i)
            ((c • rvOp (G := G) Y c)
              (hdelta (G := G) q i
                - ((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i))) := by
      rw [h1, h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      set u := hdelta (G := G) q i with hu
      set P := ((matOp (G := G) Y).ker).starProjection u with hP
      have hPu : P ∈ (matOp (G := G) Y).ker := Submodule.starProjection_apply_mem _ _
      have hb2i : (c • rvOp (G := G) Y c) P = P := hb2' c hc P hPu
      have hdec : u = (u - P) + P := by abel
      have hsplit : (c • rvOp (G := G) Y c) u = (c • rvOp (G := G) Y c) (u - P) + P := by
        conv_lhs => rw [hdec]
        rw [map_add, hb2i]
      rw [hsplit, inner_add_right, add_sub_cancel_right]
    rw [h3]
    calc ‖∑ i : Fin q, inner ℂ (hdelta (G := G) q i)
            ((c • rvOp (G := G) Y c)
              (hdelta (G := G) q i
                - ((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i)))‖
        ≤ ∑ i : Fin q, ‖inner ℂ (hdelta (G := G) q i)
            ((c • rvOp (G := G) Y c)
              (hdelta (G := G) q i
                - ((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin q, ‖hdelta (G := G) q i‖ *
            ‖(c • rvOp (G := G) Y c)
              (hdelta (G := G) q i
                - ((matOp (G := G) Y).ker).starProjection (hdelta (G := G) q i))‖ :=
          Finset.sum_le_sum fun i _ => norm_inner_le_norm _ _
      _ < ∑ _i : Fin q, 1 * (ε / q) := by
          refine Finset.sum_lt_sum (fun i _ => ?_) ⟨⟨0, hq⟩, Finset.mem_univ _, ?_⟩
          · have hi := hdfun i c hc (lt_of_lt_of_le hcδ (hmin i (Finset.mem_univ i)))
            exact mul_le_mul (le_of_eq (hnorm i)) (le_of_lt hi) (norm_nonneg _) zero_le_one
          · have hi := hdfun ⟨0, hq⟩ c hc (lt_of_lt_of_le hcδ (hmin ⟨0, hq⟩ (Finset.mem_univ _)))
            rw [hnorm ⟨0, hq⟩]
            simpa using hi
      _ = ε := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

/-! ### The key rank identity -/

/-- **The key rank identity**: the von Neumann dimension of the kernel of a matrix operator
and of its adjoint satisfy the Fredholm relation `m - dim ker T = n - dim ker T†`. -/
theorem vnKeyRank {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {n m : ℕ} (X : Matrix (Fin n) (Fin m) (↥(Work.ORVonNeumann.groupVonNeumann G))) : ((m : ℝ) - Work.ORVonNeumann.Rep.hdim ((Work.ORVonNeumann.Rep.matOp (G := G) X).ker)) = ((n : ℝ) - Work.ORVonNeumann.Rep.hdim ((ContinuousLinearMap.adjoint (Work.ORVonNeumann.Rep.matOp (G := G) X)).ker)) := by
  rw [vnMatOpAdjoint]
  set A : ℝ := hdim (G := G) (matOp (G := G) X).ker with hAdef
  set B : ℝ := hdim (G := G) (matOp (G := G) (Matrix.conjTranspose X)).ker with hBdef
  suffices ((m : ℝ) - A) - ((n : ℝ) - B) = 0 by linarith
  by_contra hne
  have hDpos : 0 < |((m : ℝ) - A) - ((n : ℝ) - B)| := abs_pos.mpr hne
  have hε : 0 < |((m : ℝ) - A) - ((n : ℝ) - B)| / 2 := by positivity
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := rv_limit (G := G) X _ hε
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := rv_limit (G := G) (Matrix.conjTranspose X) _ hε
  rw [← hAdef] at hδ₁
  rw [← hBdef] at hδ₂
  set c : ℝ := min δ₁ δ₂ / 2 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hclt₁ : c < δ₁ := by
    rw [hcdef]
    have := min_le_left δ₁ δ₂
    linarith
  have hclt₂ : c < δ₂ := by
    rw [hcdef]
    have := min_le_right δ₁ δ₂
    linarith
  have hp := hδ₁ c hcpos hclt₁
  have hq := hδ₂ c hcpos hclt₂
  have hid := rv_trace_identity (G := G) X hcpos
  have hcast : ((((m : ℝ) - A) - ((n : ℝ) - B) : ℝ) : ℂ)
      = ((c : ℂ) * mTrace (G := G) m (rvMat (G := G) X c) - (A : ℂ))
        - ((c : ℂ) * mTrace (G := G) n (rvMat (G := G) (Matrix.conjTranspose X) c)
            - (B : ℂ)) := by
    push_cast
    linear_combination hid
  have habs : ‖((((m : ℝ) - A) - ((n : ℝ) - B) : ℝ) : ℂ)‖
      = |((m : ℝ) - A) - ((n : ℝ) - B)| :=
    RCLike.norm_ofReal (((m : ℝ) - A) - ((n : ℝ) - B))
  have hlt : ‖((((m : ℝ) - A) - ((n : ℝ) - B) : ℝ) : ℂ)‖
      < |((m : ℝ) - A) - ((n : ℝ) - B)| := by
    calc ‖((((m : ℝ) - A) - ((n : ℝ) - B) : ℝ) : ℂ)‖
        = ‖((c : ℂ) * mTrace (G := G) m (rvMat (G := G) X c) - (A : ℂ))
            - ((c : ℂ) * mTrace (G := G) n (rvMat (G := G) (Matrix.conjTranspose X) c)
                - (B : ℂ))‖ := by rw [hcast]
      _ ≤ ‖(c : ℂ) * mTrace (G := G) m (rvMat (G := G) X c) - (A : ℂ)‖
            + ‖(c : ℂ) * mTrace (G := G) n (rvMat (G := G) (Matrix.conjTranspose X) c)
                - (B : ℂ)‖ := norm_sub_le _ _
      _ < |((m : ℝ) - A) - ((n : ℝ) - B)| / 2 + |((m : ℝ) - A) - ((n : ℝ) - B)| / 2 :=
          add_lt_add hp hq
      _ = |((m : ℝ) - A) - ((n : ℝ) - B)| := by ring
  exact absurd (habs ▸ hlt) (lt_irrefl _)

end Work.ORVonNeumann.Rep
