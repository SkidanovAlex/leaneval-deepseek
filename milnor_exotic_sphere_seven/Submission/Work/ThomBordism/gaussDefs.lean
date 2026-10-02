import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.ThomBordism.orthFrameOrientation
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.PontryaginThom.NormalData
import Submission.Work.ThomBordism.frameSign_fps_cocycle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# The Gauss map of an embedded `8`-manifold into the oriented Grassmannian

For an embedding `E : V ↪ ℝ^{8+k}` of a closed oriented smooth `8`-manifold with normal data `ND`,
`Work.Tubular.exists_euclidean_normalBundle` produces the chartwise orthonormal frames
`orthFrame E ND i x` of the normal plane `ν_x`.  Two such frames differ by an element of `O(k)`, and
the *orientation* of the frames is controlled by the sign cocycle `sigma` of this file: continuous
signs `σ_i : baseSet i → {±1}` with

  `det (frameChange E ND i j x) = σ_i x · σ_j x`   on the overlap

(the transport of the orientability of `ν`, which follows from the fundamental class of `V`; it is
`Work.ThomBordism.framePairSign_cocycle`, valid for every `k`, of which
`Work.ThomBordism.orthFrameOrientation` is the `Odd k` case).

The **gauge** `gauge i x = diag(σ_i x, 1, …, 1)` (an orthogonal matrix of determinant `σ_i x`) then
makes the corrected frames `gframe i x = gauge i x • orthFrame i x` *special*-orthogonally related:

  `gframe i x = frameAct (gchange i j x) (gframe j x)` with `gchange i j x ∈ SO(k)`,

so the point `gauss x = ogMk (ambFrame (gframe i x)) ∈ G̃r_k(ℝ^{k+8})` is independent of the chart `i`
containing `x`.  This is the **Gauss (classifying) map** of the normal bundle.

(The scalar gauge `σ_i • orthFrame i x` of `Work.ThomBordism.orthFrameOrientation` only works for odd
`k`, because `det (σ_i σ_j • M) = (σ_i σ_j)^{k+1}`; the diagonal gauge has determinant `σ_i` for
every `k ≥ 1`, which is exactly what is needed.)
-/

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism.Gauss

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.ThomBordism.Grassmann
open Work.Tubular

noncomputable section

variable {V : Man8}

/-! ## Reindexing the ambient space `ℝ^{8+k} ↔ ℝ^{k+8}` -/

/-- The linear isometry reindexing `ℝ^{8+k}` as `ℝ^{k+8}` (the ambient space of the Stiefel manifold
`Stiefel k 8`). -/
def ambEquiv (k : ℕ) : Work.Tubular.Euc (8 + k) ≃ₗᵢ[ℝ] Amb (k + 8) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (Nat.add_comm 8 k))

theorem ambEquiv_inner (k : ℕ) (u v : Work.Tubular.Euc (8 + k)) :
    inner ℝ (ambEquiv k u) (ambEquiv k v) = inner ℝ u v :=
  LinearIsometryEquiv.inner_map_map (ambEquiv k) u v

/-- The reindexing of a frame of `ℝ^{8+k}` to a frame of `ℝ^{k+8}`. -/
def ambFrame {k : ℕ} (F : Fin k → Work.Tubular.Euc (8 + k)) : Fin k → Amb (k + 8) := fun a => ambEquiv k (F a)

theorem ambFrame_orthonormal {k : ℕ} {F : Fin k → Work.Tubular.Euc (8 + k)} (hF : Orthonormal ℝ F) :
    Orthonormal ℝ (ambFrame F) := by
  rw [orthonormal_iff_ite] at hF ⊢
  intro a b
  show inner ℝ (ambEquiv k (F a)) (ambEquiv k (F b)) = if a = b then 1 else 0
  rw [ambEquiv_inner]
  exact hF a b

theorem orthonormal_of_ambFrame {k : ℕ} {F : Fin k → Work.Tubular.Euc (8 + k)}
    (hF : Orthonormal ℝ (ambFrame F)) : Orthonormal ℝ F := by
  rw [orthonormal_iff_ite] at hF ⊢
  intro a b
  show inner ℝ (F a) (F b) = if a = b then 1 else 0
  rw [← ambEquiv_inner k (F a) (F b)]
  exact hF a b

/-! ## Matrices acting on frames -/

/-- The action of a square matrix on a frame: `(A · F) a = ∑ b, A b a • F b`.  (For the Stiefel
manifold this is `Grassmann.soActFun`; the general-module version is convenient for the frames of
the normal plane, which live in `Euc (8+k)` rather than in the reindexed `Amb (k+8)`.) -/
def frameAct {k : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (A : Matrix (Fin k) (Fin k) ℝ) (F : Fin k → M) : Fin k → M :=
  fun a => ∑ b, A b a • F b

theorem frameAct_soActFun {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (f : Fin k → Amb (k + 8)) :
    frameAct A f = soActFun A f := rfl

theorem frameAct_one {k : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M] (F : Fin k → M) :
    frameAct (1 : Matrix (Fin k) (Fin k) ℝ) F = F := by
  funext a
  rw [frameAct, Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq, one_smul]
  · intro b _ hb; rw [Matrix.one_apply_ne hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ a) h

theorem frameAct_mul {k : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (A B : Matrix (Fin k) (Fin k) ℝ) (F : Fin k → M) :
    frameAct A (frameAct B F) = frameAct (B * A) F := by
  funext a
  simp only [frameAct, Finset.smul_sum, Finset.sum_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, mul_comm]

theorem ambFrame_frameAct {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (F : Fin k → Work.Tubular.Euc (8 + k)) :
    ambFrame (frameAct A F) = frameAct A (ambFrame F) := by
  funext a
  simp only [ambFrame, frameAct, map_sum, map_smul]

/-- The product of two orthogonal matrices (in the `Aᵀ A = 1` form) is orthogonal. -/
theorem transpose_mul_self_of_orthogonal {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.transpose * A = 1) (hB : B.transpose * B = 1) :
    (A * B).transpose * (A * B) = 1 := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc A.transpose A B, hA,
    Matrix.one_mul, hB]

/-! ## The sign cocycle of the normal frames -/

/-- The change-of-frame matrix of the chartwise normal frames has determinant `±1`. -/
theorem frameChange_det_eq_one_or_neg_one {k : ℕ} (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i j : CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    (frameChange E ND i j x).det = 1 ∨ (frameChange E ND i j x).det = -1 := by
  have h1 := congrArg Matrix.det (frameChange_transpose_mul E ND i j hx)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, ← sq] at h1
  exact sq_eq_one_iff.mp h1

/-- **The sign cocycle of the chartwise normal frames, for every `k`.**  There are continuous signs
`σ_i : baseSet i → {±1}` whose product on an overlap is the determinant of the change-of-frame
matrix.  This is the orientation of the normal bundle `ν` (which is orientable because `V` is). -/
theorem exists_signCocycle {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    ∃ σ : CoverIdx V k → V.pt → ℝ,
      (∀ (i : CoverIdx V k) (x : V.pt), σ i x = 1 ∨ σ i x = -1) ∧
      (∀ i, ContinuousOn (σ i) (ND.D.baseSet i)) ∧
      (∀ (i j : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j),
        (frameChange E ND i j x).det = σ i x * σ j x) := by
  classical
  obtain ⟨δ, hval, hcont, -, hcoc⟩ := framePairSign_cocycle E ND
  refine ⟨fun i x => if h : x ∈ ND.D.baseSet i then
    δ i.1 x * framePairSign E ND i x else 1, ?_, ?_, ?_⟩
  · intro i x
    by_cases h : x ∈ ND.D.baseSet i
    · simp only [dif_pos h]
      rcases hval i.1 x with h1 | h1 <;> rcases framePairSign_eq_one_or E ND i h with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
    · simp only [dif_neg h]; norm_num
  · intro i
    refine ContinuousOn.congr (f := fun x => δ i.1 x * framePairSign E ND i x) ?_ ?_
    · exact ((hcont i.1).mono (fun x hx => ND.baseSet_sub i.1 i.2 x hx)).mul
        (continuousOn_framePairSign E ND i)
    · intro x hx; simp only [dif_pos hx]
  · intro i j x hx
    have h := hcoc i j x hx
    simp only [dif_pos hx.1, dif_pos hx.2]
    rw [h]
    exact (sign_eq_self_of_eq_one_or_neg_one
      (frameChange_det_eq_one_or_neg_one E ND i j hx)).symm

/-- **The sign of the normal frame in the chart `i`.**

**This is the *explicit* witness of `exists_signCocycle`** — the sign of the chart tangent frame
against the *given* fundamental class `V.c` (`Work.ThomBordism.FrameSigns.frameSign`), multiplied by
the chart pair sign `framePairSign` — and *not* a `Classical.choose`: the specification (the three
conjuncts of `exists_signCocycle`) is invariant under `σ ↦ ρ · σ` for every locally constant
`ρ : V.pt → {± 1}`, so it does *not* determine the values.  Since `gframe`, `padGaussFunM` (the Gauss
map) and hence the *coorientation of every level set of the source construction* are built from
`sigma`, the value had to be pinned (`Work.ThomBordism.sigmaUpToLocalSign`,
`Submission/Work/ThomBordism/NOTE_SIGMA_TELESCOPE.md` §1).  With this formula,
`Work.ThomBordism.sigmaFS` *is* this function, `Work.ThomBordism.gframeFS` is `Gauss.gframe`,
definitionally (see `Submission/Work/ThomBordism/sigmaGaussTelescope.lean`), and the telescoping
`Work.ThomBordism.sigmaTelescope_gauss` says: the closing-up of `Gauss.gframe` with the
`V.c`-oriented chart tangent frame is the standard orientation of the ambient space — i.e. `gframe`
is the **canonical (intrinsic) coorientation of the normal bundle**, with no orientation choice left
(see also `Work.ThomBordism.padGaussFunM_eq_of_normalData`, which shows the resulting Gauss plane is
independent of the normal datum). -/
def sigma {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    CoverIdx V k → V.pt → ℝ :=
  fun i x => by
    classical
    exact if _ : x ∈ ND.D.baseSet i then
      FrameSigns.frameSign V i.1 x * framePairSign E ND i x
    else 1

/-- The defining formula of `sigma` on a chart set (the explicit witness of `exists_signCocycle`). -/
theorem sigma_eq_mul_of_mem {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (hx : x ∈ ND.D.baseSet i) :
    sigma E ND i x = FrameSigns.frameSign V i.1 x * framePairSign E ND i x := by
  rw [sigma, dif_pos hx]

theorem sigma_eq_one_or {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : sigma E ND i x = 1 ∨ sigma E ND i x = -1 := by
  by_cases h : x ∈ ND.D.baseSet i
  · rw [sigma, dif_pos h]
    rcases FrameSigns.frameSign_eq_one_or_neg_one V i.1 x with h1 | h1 <;>
      rcases framePairSign_eq_one_or E ND i h with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · rw [sigma, dif_neg h]; norm_num

theorem continuousOn_sigma {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) : ContinuousOn (sigma E ND i) (ND.D.baseSet i) := by
  refine ContinuousOn.congr (f := fun x =>
    FrameSigns.frameSign V i.1 x * framePairSign E ND i x) ?_ ?_
  · exact ((FrameSigns.continuousOn_frameSign V i.1).mono
      (fun x hx => ND.baseSet_sub i.1 i.2 x hx)).mul (continuousOn_framePairSign E ND i)
  · intro x hx; rw [sigma, dif_pos hx]

theorem frameChange_det_eq_sigma {k : ℕ} (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i j : CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    (frameChange E ND i j x).det = sigma E ND i x * sigma E ND j x := by
  rw [sigma, sigma, dif_pos hx.1, dif_pos hx.2]
  rw [frameSign_fps_cocycle E ND i j hx,
    sign_eq_self_of_eq_one_or_neg_one (frameChange_det_eq_one_or_neg_one E ND i j hx)]

/-! ## The gauge matrix `diag(σ, 1, …, 1)` -/

/-- The diagonal matrix `diag(s, 1, …, 1)` (the first coordinate carries `s`).  Its determinant is
`s` for `k ≥ 1` — this is the point of the gauge: a *scalar* multiple `s • 1` has determinant
`s^k`, which is `1` for even `k` and so cannot correct the orientation of the frames. -/
def Hmat {k : ℕ} (s : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal fun a : Fin k => if (a : ℕ) = 0 then s else 1

theorem Hmat_transpose {k : ℕ} (s : ℝ) : (Hmat (k := k) s).transpose = Hmat (k := k) s := by
  ext a b
  simp only [Matrix.transpose_apply, Hmat, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem Hmat_mul_self {k : ℕ} {s : ℝ} (hs : s = 1 ∨ s = -1) :
    Hmat (k := k) s * Hmat (k := k) s = 1 := by
  rw [Hmat, Matrix.diagonal_mul_diagonal]
  have hfun : (fun a : Fin k => (if (a:ℕ) = 0 then s else 1) * (if (a:ℕ) = 0 then s else 1))
      = fun _ => (1:ℝ) := by
    funext a
    by_cases h : (a:ℕ) = 0
    · rw [if_pos h]; rcases hs with h1|h1 <;> rw [h1] <;> norm_num
    · rw [if_neg h]; norm_num
  rw [hfun, Matrix.diagonal_one]

theorem Hmat_orthogonal {k : ℕ} {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (Hmat (k := k) s).transpose * Hmat (k := k) s = 1 := by
  rw [Hmat_transpose, Hmat_mul_self hs]

theorem Hmat_det {k : ℕ} (hk : 1 ≤ k) (s : ℝ) : (Hmat (k := k) s).det = s := by
  rw [Hmat, Matrix.det_diagonal]
  rw [Finset.prod_eq_single (⟨0, hk⟩ : Fin k)]
  · rw [if_pos (by simp)]
  · intro b _ hb
    rw [if_neg]
    intro hb0
    exact hb (Fin.ext hb0)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem frameAct_Hmat {k : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M] (s : ℝ)
    (F : Fin k → M) (a : Fin k) :
    frameAct (Hmat (k := k) s) F a = (if (a : ℕ) = 0 then s else 1) • F a := by
  rw [frameAct, Finset.sum_eq_single a]
  · rw [Hmat, Matrix.diagonal_apply_eq]
  · intro b _ hb
    rw [Hmat, Matrix.diagonal_apply, if_neg hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ a) h

/-! ## The corrected frames -/

/-- The gauge matrix of the chart `i` at `x`: `diag(σ_i x, 1, …, 1)`. -/
def gauge {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : Matrix (Fin k) (Fin k) ℝ :=
  Hmat (sigma E ND i x)

theorem gauge_transpose {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : (gauge E ND i x).transpose = gauge E ND i x :=
  Hmat_transpose _

theorem gauge_mul_self {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : gauge E ND i x * gauge E ND i x = 1 :=
  Hmat_mul_self (sigma_eq_one_or E ND i x)

theorem gauge_orthogonal {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : (gauge E ND i x).transpose * gauge E ND i x = 1 :=
  Hmat_orthogonal (sigma_eq_one_or E ND i x)

theorem gauge_det {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (hk : 1 ≤ k)
    (i : CoverIdx V k) (x : V.pt) : (gauge E ND i x).det = sigma E ND i x :=
  Hmat_det hk _

/-- **The corrected normal frame** of the chart `i` at `x`: the orthonormal frame with its first
vector multiplied by the sign `σ_i x`. -/
def gframe {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : Fin k → Work.Tubular.Euc (8 + k) :=
  frameAct (gauge E ND i x) (orthFrame E ND i x)

/-- The corrected normal frame, reindexed into the ambient space `ℝ^{k+8}` of the Stiefel manifold,
so that it is a candidate point of the oriented Grassmannian. -/
def ambGframe {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : Fin k → Amb (k + 8) :=
  ambFrame (gframe E ND i x)

theorem gframe_apply {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (a : Fin k) :
    gframe E ND i x a = (if (a : ℕ) = 0 then sigma E ND i x else 1) • orthFrame E ND i x a :=
  frameAct_Hmat _ _ _

theorem ambGframe_eq_frameAct {k : ℕ} (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    ambGframe E ND i x = frameAct (gauge E ND i x) (ambFrame (orthFrame E ND i x)) := by
  have h : gframe E ND i x = frameAct (gauge E ND i x) (orthFrame E ND i x) := rfl
  rw [ambGframe, h, ambFrame_frameAct]

theorem ambGframe_apply {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) (a : Fin k) :
    ambGframe E ND i x a
      = (if (a : ℕ) = 0 then sigma E ND i x else 1) • ambFrame (orthFrame E ND i x) a := by
  rw [ambGframe_eq_frameAct]
  exact frameAct_Hmat (sigma E ND i x) (ambFrame (orthFrame E ND i x)) a

theorem orthFrame_frameAct_gframe {k : ℕ} (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) (x : V.pt) :
    frameAct (gauge E ND i x) (gframe E ND i x) = orthFrame E ND i x := by
  have h : gframe E ND i x = frameAct (gauge E ND i x) (orthFrame E ND i x) := rfl
  rw [h, frameAct_mul, gauge_mul_self, frameAct_one]

/-- The corrected frame spans the same plane with the same orientation: the change of frame lies in
`SO(k)`.  This is the well-definedness of the Gauss map. -/
theorem isSO_gchange {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    IsSO (gauge E ND j x * frameChange E ND i j x * gauge E ND i x) := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    constructor
    · exact Subsingleton.elim _ _
    · rw [show (gauge E ND j x * frameChange E ND i j x * gauge E ND i x)
          = 1 from Subsingleton.elim _ _, Matrix.det_one]
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    constructor
    · exact transpose_mul_self_of_orthogonal
        (transpose_mul_self_of_orthogonal (gauge_orthogonal E ND j x)
          (frameChange_transpose_mul E ND i j hx))
        (gauge_orthogonal E ND i x)
    · rw [Matrix.det_mul, Matrix.det_mul, gauge_det E ND hk1, gauge_det E ND hk1,
        frameChange_det_eq_sigma E ND i j hx]
      rcases sigma_eq_one_or E ND i x with h | h <;>
        rcases sigma_eq_one_or E ND j x with h' | h' <;>
        rw [h, h'] <;> norm_num

/-- **The expansion of the corrected frame in another corrected frame.** -/
theorem gframe_expand {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    gframe E ND i x
      = frameAct (gauge E ND j x * frameChange E ND i j x * gauge E ND i x) (gframe E ND j x) := by
  have hM : orthFrame E ND i x = frameAct (frameChange E ND i j x) (orthFrame E ND j x) := by
    funext a; exact frameChange_expand E ND i j hx a
  have hjj : frameAct (gauge E ND j x) (gframe E ND j x) = orthFrame E ND j x :=
    orthFrame_frameAct_gframe E ND j x
  calc gframe E ND i x
      = frameAct (gauge E ND i x) (orthFrame E ND i x) := rfl
    _ = frameAct (gauge E ND i x)
          (frameAct (frameChange E ND i j x) (orthFrame E ND j x)) := by rw [hM]
    _ = frameAct (gauge E ND i x) (frameAct (frameChange E ND i j x)
          (frameAct (gauge E ND j x) (gframe E ND j x))) := by rw [← hjj]
    _ = frameAct (frameChange E ND i j x * gauge E ND i x)
          (frameAct (gauge E ND j x) (gframe E ND j x)) := by rw [frameAct_mul]
    _ = frameAct (gauge E ND j x * (frameChange E ND i j x * gauge E ND i x))
          (gframe E ND j x) := by rw [frameAct_mul]
    _ = frameAct (gauge E ND j x * frameChange E ND i j x * gauge E ND i x)
          (gframe E ND j x) := by rw [← Matrix.mul_assoc]

theorem ambGframe_expand {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    ambGframe E ND i x
      = frameAct (gauge E ND j x * frameChange E ND i j x * gauge E ND i x)
          (ambGframe E ND j x) := by
  rw [ambGframe, ambGframe, gframe_expand E ND i j hx, ambFrame_frameAct]

/-- **The corrected frames are orthonormal** (in the reindexed ambient space). -/
theorem orthonormal_ambGframe {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Orthonormal ℝ (ambGframe E ND i x) := by
  have h : ambGframe E ND i x = soActFun (gauge E ND i x) (ambFrame (orthFrame E ND i x)) := by
    rw [ambGframe_eq_frameAct]
    exact frameAct_soActFun _ _
  rw [h]
  exact orthonormal_soActFun (gauge_orthogonal E ND i x)
    (ambFrame_orthonormal (orthFrame_orthonormal E ND i hx))

theorem orthonormal_gframe {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    Orthonormal ℝ (gframe E ND i x) :=
  orthonormal_of_ambFrame (orthonormal_ambGframe E ND i hx)

/-- Continuity of the gauge-corrected frame on the chart. -/
theorem continuousOn_ambGframe {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (fun x => ambGframe E ND i x) (ND.D.baseSet i) := by
  rw [continuousOn_pi]
  intro a
  have hfun : (fun x => ambGframe E ND i x a) = fun x =>
      (if (a : ℕ) = 0 then sigma E ND i x else 1) • ambFrame (orthFrame E ND i x) a :=
    funext fun x => ambGframe_apply E ND i x a
  rw [hfun]
  have hcoef : ContinuousOn
      (fun x => (if (a : ℕ) = 0 then sigma E ND i x else 1)) (ND.D.baseSet i) := by
    by_cases ha : (a : ℕ) = 0
    · rw [show (fun x => (if (a : ℕ) = 0 then sigma E ND i x else 1)) =
        fun x => sigma E ND i x from funext fun x => by rw [if_pos ha]]
      exact continuousOn_sigma E ND i
    · rw [show (fun x => (if (a : ℕ) = 0 then sigma E ND i x else 1)) =
        fun _ => (1 : ℝ) from funext fun x => by rw [if_neg ha]]
      exact continuousOn_const
  exact hcoef.smul ((ambEquiv k).continuous.comp_continuousOn (continuousOn_orthFrame E ND i a))

/-! ## The Gauss map -/

/-- The candidate point of the Grassmannian defined by the chart `i` (junk off the chart). -/
def gaussStiefel {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) (x : V.pt) : Stiefel k 8 := by
  classical
  exact if h : x ∈ ND.D.baseSet i then ⟨ambGframe E ND i x, orthonormal_ambGframe E ND i h⟩
    else Classical.choice (nonempty_stiefel k 8)

theorem gaussStiefel_of_mem {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (h : x ∈ ND.D.baseSet i) :
    gaussStiefel E ND i x = ⟨ambGframe E ND i x, orthonormal_ambGframe E ND i h⟩ := by
  rw [gaussStiefel]
  exact dif_pos h

theorem continuousOn_gaussStiefel {k : ℕ} (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (i : CoverIdx V k) :
    ContinuousOn (gaussStiefel E ND i) (ND.D.baseSet i) := by
  refine continuousOn_subtype_of_eqOn (g := gaussStiefel E ND i)
    (f := fun x => ambGframe E ND i x) (continuousOn_ambGframe E ND i) ?_
  intro x hx
  rw [gaussStiefel_of_mem (E := E) (ND := ND) (i := i) hx]

/-- **The Gauss (classifying) map** of the normal bundle, as a function. -/
def gaussFun {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (x : V.pt) :
    OG k 8 :=
  ogMk k 8 (gaussStiefel E ND (ND.D.indexAt x) x)

/-- **The Gauss map is independent of the chart**: the two corrected frames differ by an element of
`SO(k)`, so they define the same point of the oriented Grassmannian. -/
theorem gaussFun_eq {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    gaussFun E ND x
      = ogMk k 8 (⟨ambGframe E ND i x, orthonormal_ambGframe E ND i hx⟩ : Stiefel k 8) := by
  set j := ND.D.indexAt x with hj
  have hjmem : x ∈ ND.D.baseSet j := ND.D.mem_baseSet_at x
  have hxy : x ∈ ND.D.baseSet j ∩ ND.D.baseSet i := ⟨hjmem, hx⟩
  have hA : IsSO (gauge E ND i x * frameChange E ND j i x * gauge E ND j x) :=
    isSO_gchange E ND j i hxy
  have hsub : gaussStiefel E ND j x
      = SOk.act ⟨gauge E ND i x * frameChange E ND j i x * gauge E ND j x, hA⟩
          (⟨ambGframe E ND i x, orthonormal_ambGframe E ND i hx⟩ : Stiefel k 8) := by
    rw [gaussStiefel_of_mem (E := E) (ND := ND) (i := j) hjmem]
    apply Subtype.ext
    exact ambGframe_expand E ND j i hxy
  calc gaussFun E ND x = ogMk k 8 (gaussStiefel E ND j x) := rfl
    _ = ogMk k 8 (⟨ambGframe E ND i x, orthonormal_ambGframe E ND i hx⟩ : Stiefel k 8) := by
        rw [hsub]
        exact (Quotient.sound (s := grassmannSetoid k 8)
          ⟨⟨_, hA⟩, rfl⟩).symm

theorem continuous_gaussFun {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    Continuous (gaussFun E ND) := by
  rw [continuous_iff_continuousAt]
  intro x
  set i := ND.D.indexAt x with hj
  have hmem : x ∈ ND.D.baseSet i := ND.D.mem_baseSet_at x
  have hopen : IsOpen (ND.D.baseSet i) := ND.D.isOpen_baseSet i
  have hloc : ContinuousOn (fun y => ogMk k 8 (gaussStiefel E ND i y)) (ND.D.baseSet i) :=
    (ogMk k 8).continuous.comp_continuousOn (continuousOn_gaussStiefel E ND i)
  refine (hloc.continuousAt (hopen.mem_nhds hmem)).congr ?_
  filter_upwards [hopen.mem_nhds hmem] with y hy
  rw [gaussStiefel_of_mem (E := E) (ND := ND) (i := i) hy]
  exact (gaussFun_eq E ND i hy).symm

/-- **The Gauss map** of the normal data `ND` of the embedding `E`. -/
def gauss {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) :
    C(V.pt, OG k 8) :=
  ⟨gaussFun E ND, continuous_gaussFun E ND⟩

@[simp] theorem gauss_apply {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (x : V.pt) : gauss E ND x = gaussFun E ND x := rfl

theorem gauss_eq_ogMk {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (t : CoverIdx V k) {x : V.pt} (ht : x ∈ ND.D.baseSet t) :
    gauss E ND x = ogMk k 8
      (⟨ambGframe E ND t x, orthonormal_ambGframe E ND t ht⟩ : Stiefel k 8) :=
  gaussFun_eq E ND t ht

/-! ## The `S`-coordinates of the ambient space -/

/-- The `S`-coordinates of a vector of the ambient space `ℝ^{8+k}`, as a vector of `Amb k`
(reindexing `Fin (8+k)` as `Fin (k+8)`). -/
def sProj {k : ℕ} (S : ChartIdx k 8) (w : Work.Tubular.Euc (8 + k)) : Amb k :=
  WithLp.toLp 2 (fun a : Fin k =>
    WithLp.ofLp w (Fin.cast (Nat.add_comm k 8) ((S.1.equivFinOfCardEq S.2).symm a : Fin (k + 8))))

theorem sProj_apply {k : ℕ} (S : ChartIdx k 8) (w : Work.Tubular.Euc (8 + k)) (a : Fin k) :
    (sProj S w).ofLp a = WithLp.ofLp w
      (Fin.cast (Nat.add_comm k 8) ((S.1.equivFinOfCardEq S.2).symm a : Fin (k + 8))) := rfl

theorem frameMatrix_ambFrame {k : ℕ} (S : ChartIdx k 8) (F : Fin k → Work.Tubular.Euc (8 + k))
    (a b : Fin k) : frameMatrix S (ambFrame F) a b = (sProj S (F b)).ofLp a := rfl

theorem sProj_add {k : ℕ} (S : ChartIdx k 8) (u v : Work.Tubular.Euc (8 + k)) :
    sProj S (u + v) = sProj S u + sProj S v := by
  ext a
  simp [sProj_apply]

theorem sProj_smul {k : ℕ} (S : ChartIdx k 8) (c : ℝ) (u : Work.Tubular.Euc (8 + k)) :
    sProj S (c • u) = c • sProj S u := by
  ext a
  simp [sProj_apply]

/-! ## The matrix of the gauge transformation -/

theorem frameMatrix_ambGframe {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) (x : V.pt) :
    frameMatrix S (ambGframe E ND t x)
      = frameMatrix S (ambFrame (orthFrame E ND t x)) * gauge E ND t x := by
  have h : gframe E ND t x = frameAct (gauge E ND t x) (orthFrame E ND t x) := rfl
  rw [ambGframe, h, ambFrame_frameAct]
  exact frameMatrix_soActFun S (gauge E ND t x) (ambFrame (orthFrame E ND t x))

theorem det_frameMatrix_ambGframe_ne_zero {k : ℕ} (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (S : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt}
    (ht : x ∈ ND.D.baseSet t) (hS : gauss E ND x ∈ baseSet S) :
    (frameMatrix S (ambGframe E ND t x)).det ≠ 0 := by
  have hg := gauss_eq_ogMk E ND t ht
  rw [hg] at hS
  exact (mem_baseSet_iff S ⟨ambGframe E ND t x, orthonormal_ambGframe E ND t ht⟩).mp hS

theorem det_frameMatrix_orthFrame_ne_zero {k : ℕ} (E : EmbeddingData V (8 + k))
    (ND : NormalData V k E.e) (S : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt}
    (ht : x ∈ ND.D.baseSet t) (hS : gauss E ND x ∈ baseSet S) :
    (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0 := by
  have h2 := det_frameMatrix_ambGframe_ne_zero E ND S t ht hS
  rw [frameMatrix_ambGframe E ND S t x, Matrix.det_mul] at h2
  intro h
  exact h2 (by rw [h, zero_mul])

/-- The matrix of the gauge from the tautological `S`-coordinates to the normal `t`-coordinates. -/
def phiMat {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (S : ChartIdx k 8)
    (t : CoverIdx V k) (x : V.pt) : Matrix (Fin k) (Fin k) ℝ :=
  (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹ * orientMat S (gauss E ND x)

/-- The matrix of the inverse gauge. -/
def phiInvMat {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (S : ChartIdx k 8)
    (t : CoverIdx V k) (x : V.pt) : Matrix (Fin k) (Fin k) ℝ :=
  orientMat S (gauss E ND x) * frameMatrix S (ambFrame (orthFrame E ND t x))

/-- The gauge transformation from the tautological `S`-coordinates to the normal `t`-coordinates. -/
def phiCLM {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (S : ChartIdx k 8)
    (t : CoverIdx V k) (x : V.pt) : Amb k →L[ℝ] Amb k :=
  matLin (phiMat E ND S t x)

/-- The inverse gauge transformation. -/
def phiInvCLM {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (S : ChartIdx k 8)
    (t : CoverIdx V k) (x : V.pt) : Amb k →L[ℝ] Amb k :=
  matLin (phiInvMat E ND S t x)

theorem phiCLM_apply {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) (x : V.pt) (v : Amb k) :
    phiCLM E ND S t x v = matLin (phiMat E ND S t x) v := rfl

theorem phiInvCLM_apply {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) (x : V.pt) (v : Amb k) :
    phiInvCLM E ND S t x v = matLin (phiInvMat E ND S t x) v := rfl

/-- The product of the two gauge matrices is the identity (the two factors are mutually inverse on
the overlap). -/
theorem phiInvMat_mul_phiMat {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt} (hS : gauss E ND x ∈ baseSet S)
    (hdet : (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0) :
    phiInvMat E ND S t x * phiMat E ND S t x = 1 := by
  have hunit : IsUnit (frameMatrix S (ambFrame (orthFrame E ND t x))).det :=
    isUnit_iff_ne_zero.mpr hdet
  calc phiInvMat E ND S t x * phiMat E ND S t x
      = orientMat S (gauss E ND x) *
          (frameMatrix S (ambFrame (orthFrame E ND t x)) *
            ((frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹ * orientMat S (gauss E ND x))) :=
        Matrix.mul_assoc _ _ _
    _ = orientMat S (gauss E ND x) *
          ((frameMatrix S (ambFrame (orthFrame E ND t x)) *
            (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹) * orientMat S (gauss E ND x)) := by
        rw [Matrix.mul_assoc]
    _ = orientMat S (gauss E ND x) * (1 * orientMat S (gauss E ND x)) := by
        rw [Matrix.mul_nonsing_inv _ hunit]
    _ = orientMat S (gauss E ND x) * orientMat S (gauss E ND x) := by rw [Matrix.one_mul]
    _ = 1 := orientMat_mul_self (S := S) (gauss E ND x) hS

theorem phiMat_mul_phiInvMat {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt} (hS : gauss E ND x ∈ baseSet S)
    (hdet : (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0) :
    phiMat E ND S t x * phiInvMat E ND S t x = 1 := by
  have hunit : IsUnit (frameMatrix S (ambFrame (orthFrame E ND t x))).det :=
    isUnit_iff_ne_zero.mpr hdet
  calc phiMat E ND S t x * phiInvMat E ND S t x
      = (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹ *
          (orientMat S (gauss E ND x) *
            (orientMat S (gauss E ND x) *
              frameMatrix S (ambFrame (orthFrame E ND t x)))) := Matrix.mul_assoc _ _ _
    _ = (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹ *
          ((orientMat S (gauss E ND x) * orientMat S (gauss E ND x)) *
            frameMatrix S (ambFrame (orthFrame E ND t x))) := by rw [Matrix.mul_assoc]
    _ = (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹ *
          (1 * frameMatrix S (ambFrame (orthFrame E ND t x))) := by
        rw [orientMat_mul_self (S := S) (gauss E ND x) hS]
    _ = (frameMatrix S (ambFrame (orthFrame E ND t x)))⁻¹ *
          frameMatrix S (ambFrame (orthFrame E ND t x)) := by rw [Matrix.one_mul]
    _ = 1 := Matrix.nonsing_inv_mul _ hunit

theorem matLin_mul_apply {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℝ) (v : Amb k) :
    matLin (M * N) v = matLin M (matLin N v) := by
  rw [matLin_mul, ContinuousLinearMap.comp_apply]

theorem matLin_mul_inv_apply {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.det ≠ 0)
    (v : Amb k) : matLin M (matLin M⁻¹ v) = v := by
  rw [← matLin_mul_apply, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM), matLin_one,
    ContinuousLinearMap.one_apply]

theorem matLin_inv_mul_apply {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.det ≠ 0)
    (v : Amb k) : matLin M⁻¹ (matLin M v) = v := by
  rw [← matLin_mul_apply, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM), matLin_one,
    ContinuousLinearMap.one_apply]

theorem matLin_orientMat_self {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) {x : V.pt} (hS : gauss E ND x ∈ baseSet S) (v : Amb k) :
    matLin (orientMat S (gauss E ND x)) (matLin (orientMat S (gauss E ND x)) v) = v := by
  rw [← matLin_mul_apply, orientMat_mul_self (S := S) (gauss E ND x) hS, matLin_one,
    ContinuousLinearMap.one_apply]

/-- The inverse of a product of invertible matrices. -/
theorem inv_mul_eq' {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  calc B⁻¹ * A⁻¹ * (A * B) = B⁻¹ * (A⁻¹ * (A * B)) := Matrix.mul_assoc _ _ _
    _ = B⁻¹ * ((A⁻¹ * A) * B) := by rw [Matrix.mul_assoc]
    _ = B⁻¹ * (1 * B) := by rw [Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA)]
    _ = B⁻¹ * B := by rw [Matrix.one_mul]
    _ = 1 := Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB)

theorem gauge_isUnit_det {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (t : CoverIdx V k) (x : V.pt) : IsUnit (gauge E ND t x).det :=
  Matrix.isUnit_det_of_left_inverse (gauge_mul_self E ND t x)

theorem gauge_det_ne_zero {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (t : CoverIdx V k) (x : V.pt) : (gauge E ND t x).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (gauge_mul_self E ND t x)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact one_ne_zero h1.symm

theorem gauge_inv_mul {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (t : CoverIdx V k) (x : V.pt) : (gauge E ND t x)⁻¹ * gauge E ND t x = 1 :=
  Matrix.nonsing_inv_mul _ (gauge_isUnit_det E ND t x)

theorem phiInvCLM_comp_phiCLM {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt} (hS : gauss E ND x ∈ baseSet S)
    (hdet : (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0) :
    (phiInvCLM E ND S t x).comp (phiCLM E ND S t x) = 1 := by
  rw [phiInvCLM, phiCLM, ← matLin_mul, phiInvMat_mul_phiMat E ND S t hS hdet, matLin_one]

theorem phiCLM_comp_phiInvCLM {k : ℕ} (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (S : ChartIdx k 8) (t : CoverIdx V k) {x : V.pt} (hS : gauss E ND x ∈ baseSet S)
    (hdet : (frameMatrix S (ambFrame (orthFrame E ND t x))).det ≠ 0) :
    (phiCLM E ND S t x).comp (phiInvCLM E ND S t x) = 1 := by
  rw [phiInvCLM, phiCLM, ← matLin_mul, phiMat_mul_phiInvMat E ND S t hS hdet, matLin_one]

end

end Work.ThomBordism.Gauss
