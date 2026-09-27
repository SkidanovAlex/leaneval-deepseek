import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.homotopy_inv

/-!
# Infrastructure for `Work.KT.hk_cap_triv`

Definitions used to build collared representatives of idempotents over the mapping cone `C_f`:

* `collarR` — the collar function on radii (`1` for `r ≥ 1/2`, `min (2r) 1` below);
* `cellExt` — the radial collar extension of a function `F : C(Tgt m, ℂ)` to the closed ball,
  constant along rays of norm `≥ 1/2`;
* `coneElem` — the resulting element of the cone algebra `coneAlg f` (base part `F`, cell part
  `cellExt F`), and `coneMat` — its entrywise matrix version;
* `coneGlue` — the element of the matrix ring over `coneAlg f` with prescribed base and cell parts.

The extension is the device that makes a unit over `C(Tgt m, ℂ)` extend to a unit over the cone
algebra with a controlled pointwise bound, without any smoothing: the cell component is a function
of the radial projection, scaled by the collar function, so it is small wherever the collar is.
-/

namespace Work.KT

open Matrix Filter
open scoped Topology

noncomputable section

/-! ## The collar function -/

/-- The collar function on radii: `1` for `r ≥ 1/2`, `0` for `r ≤ 0`, and `min (2 r) 1` in between,
clamped so as to be nonnegative. -/
def collarR (r : ℝ) : ℝ := max 0 (min (2 * r) 1)

@[simp] lemma collarR_zero : collarR 0 = 0 := by simp [collarR]

lemma collarR_one {r : ℝ} (h : 1 / 2 ≤ r) : collarR r = 1 := by
  rw [collarR, min_eq_right (by linarith), max_eq_right (by norm_num)]

lemma collarR_eq_zero {r : ℝ} (h : r ≤ 0) : collarR r = 0 := by
  rw [collarR, min_eq_left (by linarith), max_eq_left (by linarith)]

lemma collarR_nonneg (r : ℝ) : 0 ≤ collarR r := le_max_left _ _

lemma collarR_le_one (r : ℝ) : collarR r ≤ 1 := by
  rw [collarR]; exact max_le zero_le_one (min_le_right _ _)

lemma continuous_collarR : Continuous collarR := by
  have h : collarR = fun r : ℝ => max 0 (min ((2 : ℝ) * r) 1) := rfl
  rw [h]
  exact continuous_const.max ((continuous_const.mul continuous_id).min continuous_const)

/-- A continuous real function vanishing at `x`, times a map bounded by `M`, is continuous at `x`. -/
lemma ContinuousAt.smul_of_norm_le {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → ℝ} {g : X → E} {x : X} {M : ℝ} (hM : 0 ≤ M)
    (hf : ContinuousAt f x) (hg : ∀ y, ‖g y‖ ≤ M) (hfx : f x = 0) :
    ContinuousAt (fun y => f y • g y) x := by
  change Tendsto (fun y => f y • g y) (𝓝 x) (𝓝 (f x • g x))
  rw [hfx, zero_smul]
  refine squeeze_zero_norm' (a := fun y => M * ‖f y‖) (Eventually.of_forall fun y => ?_) ?_
  · calc ‖f y • g y‖ = ‖f y‖ * ‖g y‖ := norm_smul _ _
      _ ≤ ‖f y‖ * M := by gcongr; exact hg y
      _ = M * ‖f y‖ := by ring
  · have h : Tendsto (fun y => ‖f y‖) (𝓝 x) (𝓝 ‖f x‖) := hf.norm
    simpa only [hfx, norm_zero, mul_zero] using h.const_mul M

/-! ## The sphere point attached to a nonzero point of the ball -/

/-- A point of norm one of the closed unit ball, viewed as a point of the unit sphere. -/
def sphOfBall {V : Type} [NormedAddCommGroup V] (y : Ball V) (h : ‖(y : V)‖ = 1) : Sph V :=
  ⟨(y : V), mem_sphere_zero_iff_norm.mpr h⟩

/-- Radial projection fixes points of the boundary sphere. -/
lemma normPtBall_eq_self {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (w : Ball V)
    (hw : ‖(w : V)‖ = 1) : normPtBall w = w := by
  refine Subtype.ext ?_
  rw [normPtBall_coe, hw]
  simp

/-- The radial projection of a nonzero point of the closed ball, as a point of the unit sphere. -/
def sphNormPtFun {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (z : {z : Ball V // z ≠ 0}) : Sph V :=
  ⟨((normPtBall z.1 : Ball V) : V), mem_sphere_zero_iff_norm.mpr (normPtBall_mem_sphere z.2)⟩

lemma continuous_sphNormPtFun {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Continuous (sphNormPtFun : {z : Ball V // z ≠ 0} → Sph V) := by
  have hc : Continuous fun z : {z : Ball V // z ≠ 0} => ((normPtBall z.1 : Ball V) : V) := by
    rw [show (fun z : {z : Ball V // z ≠ 0} => ((normPtBall z.1 : Ball V) : V))
          = fun z : {z : Ball V // z ≠ 0} =>
              (‖((z.1 : Ball V) : V)‖)⁻¹ • ((z.1 : Ball V) : V) from
        funext fun z => normPtBall_coe z.1]
    have hval : Continuous fun z : {z : Ball V // z ≠ 0} => ((z.1 : Ball V) : V) :=
      continuous_subtype_val.comp continuous_subtype_val
    refine Continuous.smul ?_ hval
    refine Continuous.inv₀ hval.norm ?_
    intro z
    rw [norm_ne_zero_iff]
    exact fun h => z.2 (Subtype.coe_injective h)
  change Continuous fun z : {z : Ball V // z ≠ 0} =>
      (⟨((normPtBall z.1 : Ball V) : V),
        mem_sphere_zero_iff_norm.mpr (normPtBall_mem_sphere z.2)⟩ : Sph V)
  exact hc.subtype_mk fun z => mem_sphere_zero_iff_norm.mpr (normPtBall_mem_sphere z.2)

/-- The radial projection of a nonzero point of the closed ball. -/
def sphNormPt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (z : Ball V) (hz : z ≠ 0) :
    Sph V := sphNormPtFun ⟨z, hz⟩

/-! ## The radial collar extension -/

/-- The value of the collar extension away from the origin (and `0` at the origin). -/
def cellInner (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    (z : Ball (Eu m × Eu m)) : ℂ :=
  if hz : z = 0 then 0 else F (f (sphNormPt z hz))

/-- The radial collar extension of `F : C(Tgt m, ℂ)` to the closed ball: the value at `z` is the
value of `F ∘ f` at the radial projection of `z`, scaled by the collar function.  It is constant
along rays of norm `≥ 1/2` and agrees with `F ∘ f` on the boundary sphere. -/
def cellFun (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    (z : Ball (Eu m × Eu m)) : ℂ :=
  collarR ‖(z : Eu m × Eu m)‖ • cellInner m f F z

lemma cellFun_of_ne (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    {z : Ball (Eu m × Eu m)} (hz : z ≠ 0) :
    cellFun m f F z = collarR ‖(z : Eu m × Eu m)‖ • F (f (sphNormPt z hz)) := by
  simp only [cellFun, cellInner, dif_neg hz]

/-- `F` is bounded on the compact target sphere. -/
lemma exists_bound_of_continuous (m : ℕ) (F : C(Tgt m, ℂ)) :
    ∃ M : ℝ, ∀ x : Tgt m, ‖F x‖ ≤ M := by
  haveI : CompactSpace (Tgt m) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (2 * m + 1))) 1)
  have hb : Bornology.IsBounded (Set.range F) := (isCompact_range F.continuous).isBounded
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  exact ⟨M, fun x => hM (F x) ⟨x, rfl⟩⟩

lemma continuous_cellFun (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ)) :
    Continuous (cellFun m f F) := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuous m F
  have hM' : ∀ x : Tgt m, ‖F x‖ ≤ max M 0 := fun x => le_trans (hM x) (le_max_left _ _)
  have hb : ∀ y : Ball (Eu m × Eu m), ‖cellInner m f F y‖ ≤ max M 0 := by
    intro y
    by_cases hy : y = 0
    · rw [cellInner, dif_pos hy, norm_zero]; exact le_max_right _ _
    · rw [cellInner, dif_neg hy]; exact hM' _
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    show ContinuousAt (fun y : Ball (Eu m × Eu m) =>
      collarR ‖(y : Eu m × Eu m)‖ • cellInner m f F y) 0
    exact ContinuousAt.smul_of_norm_le (le_max_right M 0) (by
        exact (continuous_collarR.comp (continuous_subtype_val.norm)).continuousAt)
      hb (by simp [collarR])
  · have hopen : IsOpen {w : Ball (Eu m × Eu m) | w ≠ 0} := isOpen_ne
    have hOn : ContinuousOn (cellFun m f F) {w : Ball (Eu m × Eu m) | w ≠ 0} := by
      rw [continuousOn_iff_continuous_domRestrict]
      have hfun : {w : Ball (Eu m × Eu m) | w ≠ 0}.domRestrict (cellFun m f F) =
          fun w : {w : Ball (Eu m × Eu m) // w ≠ 0} =>
            collarR ‖(w.1 : Eu m × Eu m)‖ • F (f (sphNormPtFun w)) := by
        funext w
        show collarR ‖(w.1 : Eu m × Eu m)‖ • cellInner m f F w.1 =
          collarR ‖(w.1 : Eu m × Eu m)‖ • F (f (sphNormPtFun w))
        rw [cellInner, dif_neg w.2]
        try rfl
      rw [hfun]
      exact (continuous_collarR.comp
          ((continuous_subtype_val.comp continuous_subtype_val).norm)).smul
        (F.continuous.comp (f.continuous.comp continuous_sphNormPtFun))
    exact hOn.continuousAt (hopen.mem_nhds hz)

/-- The radial collar extension, as a bundled continuous map. -/
def cellExt (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ)) :
    C(Ball (Eu m × Eu m), ℂ) :=
  ⟨cellFun m f F, continuous_cellFun m f F⟩

@[simp] lemma cellExt_apply (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    (z : Ball (Eu m × Eu m)) : cellExt m f F z = cellFun m f F z := rfl

/-- The radial collar extension agrees with `F ∘ f` on the boundary sphere. -/
lemma cellFun_sphere (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1) :
    cellFun m f F y = F (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩) := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at hy; simp at hy
  have hval : ((normPtBall y : Ball (Eu m × Eu m)) : Eu m × Eu m) = (y : Eu m × Eu m) := by
    rw [normPtBall_coe, hy]; simp
  have hpt : sphNormPt y hy0 = ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩ :=
    Subtype.ext hval
  rw [cellFun_of_ne m f F hy0, collarR_one (r := ‖(y : Eu m × Eu m)‖) (by rw [hy]; norm_num), hpt]
  simp

/-- The collar extension is constant along rays of norm `≥ 1/2`. -/
lemma cellFun_collared (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    {z : Ball (Eu m × Eu m)} (hz : (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖) :
    cellFun m f F z = cellFun m f F (normPtBall z) := by
  have hz0 : z ≠ 0 := by
    intro h; rw [h] at hz; simp at hz; linarith
  have hnorm : ‖((normPtBall z : Ball (Eu m × Eu m)) : Eu m × Eu m)‖ = 1 :=
    normPtBall_mem_sphere hz0
  have hz1 : normPtBall z ≠ 0 := by
    intro h; rw [h] at hnorm; simp at hnorm
  have hval : ((normPtBall (normPtBall z) : Ball (Eu m × Eu m)) : Eu m × Eu m) =
      ((normPtBall z : Ball (Eu m × Eu m)) : Eu m × Eu m) :=
    congrArg (fun w : Ball (Eu m × Eu m) => (w : Eu m × Eu m))
      (normPtBall_eq_self (normPtBall z) hnorm)
  have hpt : sphNormPt (normPtBall z) hz1 = sphNormPt z hz0 := Subtype.ext hval
  rw [cellFun_of_ne m f F hz0, cellFun_of_ne m f F hz1, hpt,
    collarR_one (r := ‖(z : Eu m × Eu m)‖) hz,
    collarR_one (r := ‖((normPtBall z : Ball (Eu m × Eu m)) : Eu m × Eu m)‖)
      (by rw [hnorm]; norm_num)]

lemma cellFun_zero' (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ)) :
    cellFun m f F 0 = 0 := by
  simp [cellFun, cellInner, collarR]

/-- Pointwise bound for the collar extension. -/
lemma norm_cellFun_le (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ)) {c : ℝ}
    (hc : 0 ≤ c) (hF : ∀ x : Tgt m, ‖F x‖ ≤ c) (z : Ball (Eu m × Eu m)) :
    ‖cellFun m f F z‖ ≤ c := by
  by_cases hz : z = 0
  · rw [hz, cellFun_zero']; simpa using hc
  · rw [cellFun_of_ne m f F hz, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (collarR_nonneg _)]
    calc collarR ‖(z : Eu m × Eu m)‖ * ‖F (f (sphNormPt z hz))‖
        ≤ 1 * c := mul_le_mul (collarR_le_one _) (hF _) (norm_nonneg _) (by linarith)
      _ = c := one_mul c

/-! ## The collar extension as an element of the cone algebra -/

/-- The element of the mapping cone algebra `C(C_f)` with base part `F ∈ C(Tgt m)` and cell part the
collar extension `cellExt F`. -/
def coneElem (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ)) : coneAlg f :=
  ⟨(F, cellExt m f F), by
    intro y hy
    exact cellFun_sphere m f F y hy⟩

@[simp] lemma coneElem_val (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ)) :
    ((coneElem m f F : coneAlg f) : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)) =
      (F, cellExt m f F) := rfl

@[simp] lemma evalT_coneElem (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    (t : Tgt m) : evalT m f t (coneElem m f F) = F t := rfl

@[simp] lemma evalD_coneElem (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (F : C(Tgt m, ℂ))
    (z : Ball (Eu m × Eu m)) : evalD m f z (coneElem m f F) = cellFun m f F z := rfl

@[simp] lemma evalT_coneElem' (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (t : Tgt m)
    (x : coneAlg f) : evalT m f t x = (coneToT f x) t := rfl

@[simp] lemma evalD_coneElem'' (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (z : Ball (Eu m × Eu m)) (x : coneAlg f) : evalD m f z x = x.1.2 z := rfl

/-- The cell projection `C(C_f) → C(D)` to the second factor. -/
def coneToD (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) :
    coneAlg f →ₐ[ℂ] C(Ball (Eu m × Eu m), ℂ) :=
  (AlgHom.snd ℂ C(Tgt m, ℂ) C(Ball (Eu m × Eu m), ℂ)).comp (coneAlg f).val

@[simp] lemma coneToD_apply (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (x : coneAlg f) :
    coneToD m f x = x.1.2 := rfl

@[simp] lemma coneToT_apply (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) (x : coneAlg f) :
    coneToT f x = x.1.1 := rfl

/-- Entrywise matrix version of `coneElem`: the matrix over `C(C_f)` with base entries `A i j` and
cell entries `cellExt (A i j)`. -/
def coneMat {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) : Matrix (Fin k) (Fin k) (coneAlg f) :=
  fun i j => coneElem m f (A i j)

@[simp] lemma evalT_coneMat (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) {k : ℕ}
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) (t : Tgt m) :
    (coneMat m f A).map (evalT m f t) = A.map (evalC t) := by
  ext i j; rfl

/-- The matrix over `C(C_f)` with prescribed base part `A` and cell part `B`, compatible on the
boundary sphere of the ball. -/
def coneGlue {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) (B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ))
    (h : ∀ (i j : Fin k) (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1),
      B i j y = A i j (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)) :
    Matrix (Fin k) (Fin k) (coneAlg f) :=
  fun i j => ⟨(A i j, B i j), by
    intro y hy
    exact h i j y hy⟩

@[simp] lemma evalT_coneGlue {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) (B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ))
    (h : ∀ (i j : Fin k) (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1),
      B i j y = A i j (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩))
    (t : Tgt m) : (coneGlue m f A B h).map (evalT m f t) = A.map (evalC t) := by
  ext i j; rfl

@[simp] lemma evalD_coneGlue {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) (B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ))
    (h : ∀ (i j : Fin k) (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1),
      B i j y = A i j (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩))
    (z : Ball (Eu m × Eu m)) : (coneGlue m f A B h).map (evalD m f z) = B.map (evalC z) := by
  ext i j; rfl

/-- The base projection of matrices over the cone algebra. -/
def coneProjT {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) :
    Matrix (Fin k) (Fin k) (coneAlg f) →+* Matrix (Fin k) (Fin k) C(Tgt m, ℂ) :=
  RingHom.mapMatrix (coneToT f).toRingHom

/-- The cell projection of matrices over the cone algebra. -/
def coneProjD {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m)) :
    Matrix (Fin k) (Fin k) (coneAlg f) →+* Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ) :=
  RingHom.mapMatrix (coneToD m f).toRingHom

lemma coneProjT_apply {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) :
    coneProjT m f M = M.map (fun x => coneToT f x) := by
  ext i j
  rfl

lemma coneProjD_apply {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) :
    coneProjD m f M = M.map (fun x => coneToD m f x) := by
  ext i j
  rfl

/-! ## The glueing construction: projections, extensionality, and the collar matrix -/

@[simp] lemma coneProjT_coneGlue {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) (B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ))
    (h : ∀ (i j : Fin k) (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1),
      B i j y = A i j (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)) :
    coneProjT m f (coneGlue m f A B h) = A := by
  rw [coneProjT_apply]
  ext i j
  rfl

@[simp] lemma coneProjD_coneGlue {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) (B : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ))
    (h : ∀ (i j : Fin k) (y : Ball (Eu m × Eu m)) (hy : ‖(y : Eu m × Eu m)‖ = 1),
      B i j y = A i j (f ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)) :
    coneProjD m f (coneGlue m f A B h) = B := by
  rw [coneProjD_apply]
  ext i j
  rfl

@[simp] lemma coneProjT_coneMat {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) : coneProjT m f (coneMat m f A) = A := by
  rw [coneProjT_apply]
  ext i j
  rfl

/-- The base projection, evaluated at a point, is the evaluation of the matrix over the base. -/
@[simp] lemma coneProjT_map_evalC {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) (t : Tgt m) :
    (coneProjT m f M).map (fun F => evalC t F) = M.map (evalT m f t) := by
  ext i j
  rfl

/-- The cell projection, evaluated at a point, is the evaluation of the matrix over the ball. -/
@[simp] lemma coneProjD_map_evalC {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (M : Matrix (Fin k) (Fin k) (coneAlg f)) (z : Ball (Eu m × Eu m)) :
    (coneProjD m f M).map (fun F => evalC z F) = M.map (evalD m f z) := by
  ext i j
  rfl

/-- Two elements of the cone algebra with equal projections are equal. -/
lemma coneElem_ext {m : ℕ} {f : C(Sph (Eu m × Eu m), Tgt m)} {x y : coneAlg f}
    (h1 : coneToT f x = coneToT f y) (h2 : coneToD m f x = coneToD m f y) : x = y := by
  refine Subtype.val_injective (Prod.ext ?_ ?_)
  · simpa only [coneToT_apply] using h1
  · simpa only [coneToD_apply] using h2

/-- Two matrices over the cone algebra with the same base and cell projections are equal. -/
lemma coneProj_ext {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    {M N : Matrix (Fin k) (Fin k) (coneAlg f)}
    (h1 : coneProjT m f M = coneProjT m f N) (h2 : coneProjD m f M = coneProjD m f N) : M = N := by
  have h1' : M.map (fun x => coneToT f x) = N.map (fun x => coneToT f x) := by
    rw [← coneProjT_apply m f M, ← coneProjT_apply m f N]; exact h1
  have h2' : M.map (fun x => coneToD m f x) = N.map (fun x => coneToD m f x) := by
    rw [← coneProjD_apply m f M, ← coneProjD_apply m f N]; exact h2
  funext i j
  exact coneElem_ext
    (congrArg (fun X : Matrix (Fin k) (Fin k) C(Tgt m, ℂ) => X i j) h1')
    (congrArg (fun X : Matrix (Fin k) (Fin k) C(Ball (Eu m × Eu m), ℂ) => X i j) h2')

/-- The `coneMat` construction is collared in the cell. -/
lemma coneMat_evalD_collared {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) {z : Ball (Eu m × Eu m)}
    (hz : (1 : ℝ) / 2 ≤ ‖(z : Eu m × Eu m)‖) :
    (coneMat m f A).map (evalD m f z) = (coneMat m f A).map (evalD m f (normPtBall z)) := by
  ext i j
  simp only [Matrix.map_apply, coneMat, evalD_coneElem]
  exact cellFun_collared m f (A i j) hz

/-- Entrywise bound for the cell part of `coneMat`. -/
lemma norm_coneMat_evalD_le {k : ℕ} (m : ℕ) (f : C(Sph (Eu m × Eu m), Tgt m))
    (A : Matrix (Fin k) (Fin k) C(Tgt m, ℂ)) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ (i j : Fin k) (x : Tgt m), ‖A i j x‖ ≤ c) (i j : Fin k)
    (z : Ball (Eu m × Eu m)) : ‖evalD m f z (coneMat m f A i j)‖ ≤ c := by
  rw [show evalD m f z (coneMat m f A i j) = cellFun m f (A i j) z from rfl]
  exact norm_cellFun_le m f (A i j) hc (hA i j) z

/-- Small entries make `1 + W` a unit in `M_k(ℂ)`. -/
lemma isUnit_one_add_of_entry_bound {k : ℕ} (W : Matrix (Fin k) (Fin k) ℂ) {c : ℝ}
    (hc0 : 0 ≤ c) (h : ∀ i j, ‖W i j‖ ≤ c) (hc : (k : ℝ) * c < 1) : IsUnit (1 + W) := by
  have hb : homInvMatNorm (-W) < 1 := by
    rw [homInvMatNorm_neg]
    refine lt_of_le_of_lt (homInvMatNorm_le_card_mul W (c := Real.toNNReal c) ?_) ?_
    · intro i j
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal c hc0]
      exact h i j
    · have h' : ((k : NNReal) * Real.toNNReal c : NNReal) < 1 := by
        rw [← NNReal.coe_lt_coe, NNReal.coe_one]
        have h2 : (((k : NNReal) * Real.toNNReal c : NNReal) : ℝ) = (k : ℝ) * c := by
          push_cast
          rw [Real.coe_toNNReal c hc0]
        rw [h2]
        exact hc
      simpa using h'
  simpa using isUnit_one_sub_of_matNorm_lt_one (-W) hb

end

end Work.KT
