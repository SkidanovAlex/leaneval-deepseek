import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.dissection_additivity
import Submission.Commons.Geometry.Convex.Hadwiger.simple_valuation_binary_union
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_inclusionExclusion
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_dense
import Submission.Commons.Geometry.Convex.Hadwiger.exists_fullDim_polytope_close
import Submission.Commons.Geometry.Convex.Hadwiger.klain333_fin1
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_smear_dissection
import Submission.Commons.Geometry.Convex.Hadwiger.oblique_prism_zero
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_smear_dissection_normal
import Submission.Commons.Geometry.Convex.Hadwiger.exists_lie_unit_to_unit
import Submission.Commons.Geometry.Convex.Hadwiger.continuous_bodyAdd_left
import Submission.Commons.Geometry.Convex.Hadwiger.simplex_parallelotope_dissection
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_triangulation
import Submission.Commons.Geometry.Convex.Hadwiger.centred_zonoidDiff_seq
/-!
# `klain333_from_cylinders`

Statement (as requested by the `klain333_step` development; the in-dimension
part of Klain, *A short proof of Hadwiger's characterization theorem*,
Mathematika 42 (1995) 329–339, Theorem 3.3, steps 4–7):

> Let `μ` be a continuous, quadruple-additive, translation-invariant, *simple*
> (empty interior ⇒ 0) and *even* (`μ(−K) = μ K`) valuation on
> `EuclideanSpace ℝ (Fin (m+1))`.  If `μ` vanishes on **every right cylinder**
> `ρ (K × [0,h])` over every convex body `K` of `EuclideanSpace ℝ (Fin m)`,
> at every height `h ≥ 0`, in every orthonormal frame `ρ`, then `μ` is
> identically zero.

## Mathematical content and proof route

This is exactly the *in-dimension chain* of Klain's Thm 3.3 (steps 4–7); with
right cylinders over every hyperplane-base already available, the remaining
steps of that theorem are:

1. **Oblique prisms vanish** (Klain Fig. 2, p. 335): an oblique prism
   `B + [0,1]·v` over an `(n−1)`-body `B` in a hyperplane is scissors-congruent
   (in the dissection sense, using the Groemer polyconvex extension of a simple
   valuation — `dissection_additivity`) to a right cylinder over (a translate
   of) `B`; fat bases are first cut into "skinny" convex pieces.
2. **Polytopes** (`P + σ = P ∪ ⋃_{⟨uᵢ,v⟩>0} (Pᵢ + σ)`): with `Pᵢ` the facets of
   a polytope `P` with outward normals `uᵢ` and `σ = [0,v]` a segment, this is a
   dissection (overlaps of dimension ≤ n−1), hence `μ(P+σ) = μ(P)`; iterating
   Minkowski sums of segments: `μ(Z) = 0` for zonotopes `Z` and
   `μ(P+Z) = μ(P)` for polytopes `P` and zonotopes `Z`.
3. **Zonoids** (Hausdorff limits of zonotopes): `μ(Y) = 0` and
   `μ(K+Y) = μ(K)` for every body `K` and zonoid `Y` (continuity + density).
4. **Centred bodies** (Klain Prop 3.1, p. 333 — the single analytic input,
   spherical harmonics / Funk–Hecke / cosine transform): every centred convex
   body with a `C∞` support function `K` satisfies `K + Y₂ = Y₁` for zonoids
   `Y₁,Y₂`, so `μ(K) = μ(K+Y₂) = μ(Y₁) = 0`; every centred body is a Hausdorff
   limit of smooth centred bodies, so all centred bodies vanish.
5. **Simplices**: for a simplex `Δ = conv{0,u₁,…,u_n}` with parallelotope
   `P = Σᵢ[0,uᵢ]` and `v = Σᵢ uᵢ`, `P = Δ ∪ Q ∪ (−Δ+v)` is a dissection with
   `P` (a zonotope) and `Q = P ∩ {1 ≤ Σtᵢ ≤ n−1}` (a centred polytope) of value
   0, so `0 = μ(Δ) + μ(Q) + μ(−Δ) = 2μ(Δ)`; then triangulate polytopes into
   simplices (`dissection_additivity`), apply `polytope_dense` + continuity
   ⇒ `μ ≡ 0` on every convex body.

Note the statement is **true** (it is exactly Klain Thm 3.3 for the even simple
case, in the cylinder formulation) but is a deep theorem: it is equivalent
(by plugging a nondegenerate cylinder into Klain's volume-characterization
Thm 3.4) to "every continuous translation-invariant simple *even* valuation is
a multiple of volume", whose proof genuinely requires step 4 above or the
equally heavy classical alternatives.

## (historical development notes between this point and "UPDATE 2" below have been superseded; see UPDATE 2)

## Development status — UPDATE 2 (authoritative)

**The whole theorem is FORMALISED and compiles** (`lake build` rc = 0); the
target `klain333_from_cylinders` has a *real* proof, via:

* steps 1–3 (oblique prisms, polytope smearing, zonotopes/zonoids): commons
  `oblique_prism_zero` (L81), `polytope_smear_dissection_normal` (L82),
  `exists_lie_unit_to_unit` (L89), `continuous_bodyAdd_left` (L90) assembled
  with in-file geometry into `poly_smear` / `smear_invariance` /
  `zonotope_zero` / `zonoid_zero` / `zonoid_bodyAdd` (`IsZonoid` = Hausdorff
  limit of `foldSmear (pointBody ·)` over lists of segments);
* steps 5–7: `simplex_zero_of_centred` (dissection
  `P = Δ ∪ Q ∪ (−Δ+v)`, commons `simplex_parallelotope_dissection` L91),
  `polytope_zero_of_centred` (commons `polytope_triangulation` L92 +
  `dissection_additivity`), `body_zero_of_centred` (full-dim polytope density
  `exists_fullDim_polytope_close` + continuity), and the `m = 0` base case
  (`klain333_fin1`; cube-of-`En 1` = height-1 cylinder over the `En 0` point);
* step 4 (the analytic core, Klain Prop. 3.1 + smooth-centre density) is the
  shared commons lemma `Commons.Geometry.Convex.Hadwiger.centred_zonoidDiff_seq`
  (agent L104, with its cosine-transform/Funk–Hecke and smooth-centre-density
  subtree): in body-language, every centred body is a Hausdorff limit of
  bodies each of which is a difference of two zonoids (`∃ Kⱼ → K`, per `j`:
  zonoids `Y₁,Y₂` with `Kⱼ + Y₂ = Y₁`).  `centred_zonoidDiff_seq_scaffold` is
  the instantiation of that lemma at `V = En (m+1)`, bridging its
  Mathlib-only zonoid spelling (Hausdorff limits of `parSetV`-zonotopes) into
  this module's `IsZonoid m` via `zonoid_of_parLimit` (carriers match by
  `simpa [parSetV]`); `centred_zero_of_zonoidSeq` and `centred_zero` close by
  continuity + the two zonoid facts (`zonoid_zero`, `zonoid_bodyAdd`).

**The file is complete (no unproved gaps).**  The analytic core is proved and
published in the shared commons (see above), and the whole chain --- oblique
prisms, smearing, zonotopes/zonooids, the analytic core, the simplex
dissection, polytope triangulation/density and the `m = 0` base case --- is
real.  (Note for the record: the analytic core cannot be replaced by an
elementary polytope argument, since not even every centrally symmetric
*polytope* is an exact difference of zonoids --- octahedron-type polytopes are
only limits --- which is why smooth-centre density is an essential part.)
-/


open Set Filter
open scoped Pointwise Topology BigOperators Classical

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

abbrev En (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-! ## Coordinate plumbing between `En n` and `En (n+1)` -/

/-- Drop the last coordinate. -/
def dropLast (n : ℕ) (y : En (n + 1)) : En n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j : Fin n => y (Fin.castSucc j))

/-- The last coordinate. -/
def lastCoord (n : ℕ) (y : En (n + 1)) : ℝ := y (Fin.last n)

/-- Embed by putting `0` in the last coordinate. -/
def emb (n : ℕ) (x : En n) : En (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (fun i : Fin (n + 1) =>
      if h : i = Fin.last n then 0 else x (Fin.castLT i (Fin.val_lt_last h)))

/-- The last-coordinate unit vector. -/
def eLast (n : ℕ) : En (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (fun i : Fin (n + 1) => if i = Fin.last n then 1 else 0)

@[simp] theorem emb_zero (n : ℕ) : emb n (0 : En n) = 0 := by ext i; simp [emb]

@[simp] theorem emb_add (n : ℕ) (x y : En n) : emb n (x + y) = emb n x + emb n y := by
  ext i
  dsimp [emb]
  by_cases h : i = Fin.last n
  · simp [h]
  · simp [h]

@[simp] theorem emb_smul (n : ℕ) (a : ℝ) (x : En n) : emb n (a • x) = a • emb n x := by
  ext i
  dsimp [emb]
  by_cases h : i = Fin.last n
  · simp [h]
  · simp [h]

@[simp] theorem dropLast_emb (n : ℕ) (x : En n) : dropLast n (emb n x) = x := by
  ext j; simp [dropLast, emb]

@[simp] theorem lastCoord_emb (n : ℕ) (x : En n) : lastCoord n (emb n x) = 0 := by
  simp [lastCoord, emb]

@[simp] theorem dropLast_eLast (n : ℕ) : dropLast n (eLast n) = 0 := by
  ext j; simp [dropLast, eLast]

@[simp] theorem lastCoord_eLast (n : ℕ) : lastCoord n (eLast n) = 1 := by
  simp [lastCoord, eLast]

/-- Any point decomposes as its first-coordinate part plus last-coordinate part. -/
theorem emb_dropLast_add_last (n : ℕ) (y : En (n + 1)) :
    emb n (dropLast n y) + lastCoord n y • eLast n = y := by
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  funext i
  by_cases h : i = Fin.last n
  · simp [emb, eLast, lastCoord, h]
  · have hlt := Fin.val_lt_last h
    have hi : Fin.castSucc (Fin.castLT i hlt) = i := by ext; simp [Fin.castLT]
    simp [emb, eLast, lastCoord, dropLast, h, hi]

@[simp] theorem dropLast_add (n : ℕ) (x y : En (n + 1)) : dropLast n (x + y) = dropLast n x + dropLast n y := by ext j; rfl
@[simp] theorem dropLast_smul (n : ℕ) (a : ℝ) (x : En (n + 1)) : dropLast n (a • x) = a • dropLast n x := by ext j; rfl
@[simp] theorem lastCoord_add (n : ℕ) (x y : En (n + 1)) : lastCoord n (x + y) = lastCoord n x + lastCoord n y := by rfl
@[simp] theorem lastCoord_smul (n : ℕ) (a : ℝ) (x : En (n + 1)) : lastCoord n (a • x) = a * lastCoord n x := by rfl
@[simp] theorem dropLast_neg (n : ℕ) (y : En (n + 1)) : dropLast n (-y) = - dropLast n y := by ext j; rfl
@[simp] theorem lastCoord_neg (n : ℕ) (y : En (n + 1)) : lastCoord n (-y) = - lastCoord n y := by rfl

/-! ## Norm bounds for the coordinate maps -/

@[simp] theorem norm_emb (n : ℕ) (x : En n) : ‖emb n x‖ = ‖x‖ := by
  have hsq : ‖emb n x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    simp [emb]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
    |>.elim (fun h => h) (fun h => by linarith [norm_nonneg (emb n x), norm_nonneg x])

theorem norm_dropLast_le (n : ℕ) (y : En (n + 1)) : ‖dropLast n y‖ ≤ ‖y‖ := by
  have hsq : ‖dropLast n y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    simp [dropLast]
    exact sq_nonneg (y (Fin.last n))
  have habs := sq_le_sq.mp hsq
  have h1 : |‖dropLast n y‖| = ‖dropLast n y‖ := abs_of_nonneg (norm_nonneg _)
  have h2 : |‖y‖| = ‖y‖ := abs_of_nonneg (norm_nonneg _)
  linarith

theorem abs_lastCoord_le_norm (n : ℕ) (y : En (n + 1)) : |lastCoord n y| ≤ ‖y‖ := by
  have h := PiLp.norm_apply_le (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) => ℝ) y (Fin.last n)
  simpa [lastCoord] using h

@[simp] theorem norm_eLast (n : ℕ) : ‖eLast n‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [Fin.sum_univ_castSucc]
  simp [eLast]

/-! ## The standard right cylinder over a base in the coordinate hyperplane -/

/-- The standard right-cylinder set over `K` (base in the coordinate hyperplane,
height `[0,h]` along the last coordinate axis). -/
def cylSetStd (m : ℕ) (K : ConvexBody (En m)) (h : ℝ) : Set (En (m + 1)) :=
  {y : En (m + 1) | dropLast m y ∈ (K : Set (En m)) ∧ lastCoord m y ∈ Set.Icc (0 : ℝ) h}

theorem cylSetStd_convex (m : ℕ) (K : ConvexBody (En m)) (h : ℝ) : Convex ℝ (cylSetStd m K h) := by
  rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ a b ha hb hab
  constructor
  · simpa using (K.convex hx1 hy1 ha hb hab)
  · simpa using ((convex_Icc (0 : ℝ) h) hx2 hy2 ha hb hab)

theorem cylSetStd_closed (m : ℕ) (K : ConvexBody (En m)) (h : ℝ) : IsClosed (cylSetStd m K h) := by
  rw [show cylSetStd m K h =
      (dropLast m ⁻¹' (K : Set (En m))) ∩ (lastCoord m ⁻¹' (Set.Icc (0 : ℝ) h)) by
    ext y; simp [cylSetStd]]
  exact (IsClosed.preimage (LinearMap.continuous_of_finiteDimensional
      { toFun := dropLast m, map_add' := dropLast_add m, map_smul' := dropLast_smul m })
      (IsCompact.isClosed K.isCompact)).inter
    (IsClosed.preimage (LinearMap.continuous_of_finiteDimensional
      { toFun := lastCoord m, map_add' := lastCoord_add m, map_smul' := lastCoord_smul m })
      (isClosed_Icc))

theorem cylSetStd_nonempty (m : ℕ) (K : ConvexBody (En m)) (h : ℝ) (hh : 0 ≤ h) :
    (cylSetStd m K h).Nonempty := by
  rcases K.nonempty with ⟨x, hx⟩
  refine ⟨emb m x, ?_⟩
  constructor
  · simpa using hx
  · simp [hh]

theorem cylSetStd_bounded (m : ℕ) (K : ConvexBody (En m)) (h : ℝ) (hh : 0 ≤ h) :
    Bornology.IsBounded (cylSetStd m K h) := by
  rcases (Metric.isBounded_iff_subset_closedBall (0 : En m)).mp K.isCompact.isBounded with ⟨C, hKC⟩
  refine (Metric.isBounded_iff_subset_closedBall (0 : En (m + 1))).mpr ⟨C + h, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall]
  have hC1 : ‖dropLast m y‖ ≤ C := by
    have := hKC hy.1
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hC2 : |lastCoord m y| ≤ h := by
    have hlo : 0 ≤ lastCoord m y := hy.2.1
    rw [abs_of_nonneg hlo]
    exact hy.2.2
  have hnorm : ‖y‖ ≤ ‖dropLast m y‖ + |lastCoord m y| := by
    calc
      ‖y‖ = ‖emb m (dropLast m y) + lastCoord m y • eLast m‖ := by
        rw [emb_dropLast_add_last m y]
      _ ≤ ‖emb m (dropLast m y)‖ + ‖lastCoord m y • eLast m‖ := norm_add_le _ _
      _ ≤ ‖dropLast m y‖ + |lastCoord m y| := by
        have h : ‖emb m (dropLast m y)‖ = ‖dropLast m y‖ := norm_emb m (dropLast m y)
        have h' : ‖lastCoord m y • eLast m‖ = |lastCoord m y| := by
          rw [norm_smul, Real.norm_eq_abs, norm_eLast, mul_one]
        rw [h, h']
  have : ‖y‖ ≤ C + h := by
    calc
      ‖y‖ ≤ ‖dropLast m y‖ + |lastCoord m y| := hnorm
      _ ≤ C + h := by linarith
  simpa [dist_eq_norm] using this

/-- The standard cylinder as a convex body. -/
def cylStdBody (m : ℕ) (K : ConvexBody (En m)) (h : ℝ) (hh : 0 ≤ h) : ConvexBody (En (m + 1)) :=
  ⟨cylSetStd m K h, cylSetStd_convex m K h,
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨cylSetStd_closed m K h, cylSetStd_bounded m K h hh⟩,
    cylSetStd_nonempty m K h hh⟩

@[simp] theorem cylStdBody_coe (m : ℕ) (K : ConvexBody (En m)) (h : ℝ) (hh : 0 ≤ h) :
    (cylStdBody m K h hh : Set (En (m + 1))) = cylSetStd m K h := rfl

/-- The set in the cylinder hypothesis of `klain333_from_cylinders` is exactly the
image under `ρ` of the standard cylinder set. -/
theorem hypSet_eq_image (m : ℕ) (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1))
    (K : ConvexBody (En m)) (h : ℝ) :
    {y : En (m + 1) |
        dropLast m (ρ.symm y) ∈ (K : Set (En m)) ∧
        lastCoord m (ρ.symm y) ∈ Set.Icc (0 : ℝ) h} =
      (fun x : En (m + 1) => ρ x) '' cylSetStd m K h := by
  ext y
  constructor
  · rintro ⟨hK, ht⟩
    refine ⟨ρ.symm y, ?_, ?_⟩
    · simpa [cylSetStd] using ⟨hK, ht⟩
    · simp
  · rintro ⟨z, hz, hyz⟩
    subst y
    simpa [cylSetStd] using hz

/-- Image of a convex body under a linear isometry (still a convex body). -/
def bodyImage {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (ρ : V ≃ₗᵢ[ℝ] V)
    (K : ConvexBody V) : ConvexBody V :=
  ⟨(fun x : V => ρ x) '' (K : Set V),
   K.convex.linear_image (ρ : V →ₗ[ℝ] V),
   by simpa using K.isCompact.image (by fun_prop : Continuous (fun x : V => ρ x)),
   by simpa using K.nonempty.image (fun x : V => ρ x)⟩

@[simp] theorem bodyImage_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : V ≃ₗᵢ[ℝ] V) (K : ConvexBody V) :
    (bodyImage ρ K : Set V) = (fun x : V => ρ x) '' (K : Set V) := rfl

/-- The set appearing in the cylinder hypothesis of `klain333_from_cylinders`
(in the explicit coordinate form used there). -/
def cylHypSet (m : ℕ) (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ) :
    Set (En (m + 1)) :=
  {y : En (m + 1) |
    (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => (ρ.symm y) (Fin.castSucc i)) ∈
      (K : Set (En m)) ∧
    (ρ.symm y) (Fin.last m) ∈ Set.Icc (0 : ℝ) h}

/-- The hypothesis set is the image under `ρ` of the standard cylinder set
(in the exact coordinate form of the statement). -/
theorem cylHypSet_eq_image (m : ℕ) (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1))
    (K : ConvexBody (En m)) (h : ℝ) :
    cylHypSet m ρ K h = (fun x : En (m + 1) => ρ x) '' cylSetStd m K h := by
  -- the coordinate forms are definitionally the `dropLast`/`lastCoord` forms
  simpa [cylHypSet, dropLast, lastCoord] using (hypSet_eq_image m ρ K h)


/-- Composing the frame: `τ '' (cylHypSet σ K h) = cylHypSet (σ.trans τ) K h`. -/
theorem cylHypSet_frame_comp (m : ℕ) (σ τ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1))
    (K : ConvexBody (En m)) (h : ℝ) :
    (fun x : En (m + 1) => τ x) '' cylHypSet m σ K h = cylHypSet m (σ.trans τ) K h := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [cylHypSet_eq_image m σ K h] at hz
    rcases hz with ⟨c, hc, rfl⟩
    rw [cylHypSet_eq_image m (σ.trans τ) K h]
    refine ⟨c, hc, ?_⟩
    rfl
  · intro hy
    rw [cylHypSet_eq_image m (σ.trans τ) K h] at hy
    rcases hy with ⟨c, hc, hyc⟩
    refine ⟨σ c, ?_, hyc⟩
    rw [cylHypSet_eq_image m σ K h]
    exact ⟨c, hc, rfl⟩

/-- First interop lemma: the cylinder hypothesis (set form) forces `μ` to vanish
on the *body* `ρ (K × [0,h])` obtained as the image of the standard cylinder
body under `ρ`.  This is the entry point through which the hypothesis of
`klain333_from_cylinders` is used in body form. -/
theorem cylHyp_body_zero (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ) (hh : 0 ≤ h),
      μ (bodyImage ρ (cylStdBody m K h hh)) = 0 := by
  intro ρ K h hh
  refine hcyl ρ K h hh (bodyImage ρ (cylStdBody m K h hh)) ?_
  rw [bodyImage_coe, cylStdBody_coe]
  exact (cylHypSet_eq_image m ρ K h).symm
/-! ## Frame conjugation of a valuation (needed: extend oblique-prism zero
from coordinate-hyperplane bases to arbitrary hyperplane bases) -/

/-- Conjugate a valuation by the linear isometry `ρ`: `μ_ρ(K) = μ(ρ K)`.
(Using Mathlib's `ConvexBody.imageLIE` transport.) -/
def conjVal {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ρ : V ≃ₗᵢ[ℝ] W) (μ : ConvexBody W → ℝ) : ConvexBody V → ℝ :=
  fun K => μ (ConvexBody.imageLIE ρ K)

theorem conjVal_cont {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ρ : V ≃ₗᵢ[ℝ] W) {μ : ConvexBody W → ℝ} (hμ : Continuous μ) :
    Continuous (conjVal ρ μ) := by
  unfold conjVal
  exact hμ.comp (Commons.Geometry.Convex.Hadwiger.imageLIE_isometry ρ).continuous

theorem conjVal_hadd {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ρ : V ≃ₗᵢ[ℝ] W) {μ : ConvexBody W → ℝ}
    (hμ : ∀ A B C D : ConvexBody W,
        (A : Set W) = (C : Set W) ∪ (D : Set W) →
        (B : Set W) = (C : Set W) ∩ (D : Set W) → μ A + μ B = μ C + μ D) :
    ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) →
        conjVal ρ μ A + conjVal ρ μ B = conjVal ρ μ C + conjVal ρ μ D := by
  intro A B C D hU hI
  unfold conjVal
  apply hμ
  · -- ρ '' A = ρ '' C ∪ ρ '' D  (A = C ∪ D)
    rw [imageLIE_apply, imageLIE_apply, imageLIE_apply]
    rw [hU]
    rw [image_union]
  · rw [imageLIE_apply, imageLIE_apply, imageLIE_apply]
    rw [hI]
    rw [image_inter (LinearIsometryEquiv.injective ρ)]

theorem conjVal_htrans {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ρ : V ≃ₗᵢ[ℝ] W) {μ : ConvexBody W → ℝ}
    (hμ : ∀ A B : ConvexBody W, ∀ t : W,
        (B : Set W) = (fun x : W => x + t) '' (A : Set W) → μ A = μ B) :
    ∀ A B : ConvexBody V, ∀ t : V,
        (B : Set V) = (fun x : V => x + t) '' (A : Set V) →
        conjVal ρ μ A = conjVal ρ μ B := by
  intro A B t hB
  unfold conjVal
  apply hμ (ConvexBody.imageLIE ρ A) (ConvexBody.imageLIE ρ B) (ρ t)
  -- show ρ '' B = (y ↦ y + ρ t) '' (ρ '' A), using B = (x ↦ x+t)''A and lie_image_translate
  rw [imageLIE_apply, imageLIE_apply]
  rw [hB]
  exact (Commons.Geometry.Convex.Hadwiger.lie_image_translate ρ A t)

theorem conjVal_hsimple {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (ρ : V ≃ₗᵢ[ℝ] W) {μ : ConvexBody W → ℝ}
    (hμ : ∀ K : ConvexBody W, interior (K : Set W) = ∅ → μ K = 0) :
    ∀ K : ConvexBody V, interior (K : Set V) = ∅ → conjVal ρ μ K = 0 := by
  intro K hK
  unfold conjVal
  apply hμ
  rw [imageLIE_apply]
  rw [Commons.Geometry.Convex.Hadwiger.lie_image_interior ρ (K : Set V)]
  rw [hK]
  simp

/-- The cylinder hypothesis is preserved by frame conjugation: if `μ` vanishes
on every right cylinder (in every frame), then so does `μ ∘ imageLIE τ`.  This
is the hinge that will let `oblique_prism_zero` (coordinate-hyperplane bases)
be conjugated to arbitrary hyperplane bases (needed for facet smearing). -/
theorem conjVal_hcyl (m : ℕ) (τ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1))
    (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcyl : ∀ (σ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m σ K h → μ Q = 0) :
    ∀ (σ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m σ K h →
        conjVal τ μ Q = 0 := by
  intro σ K h hh Q hQ
  unfold conjVal
  -- apply hcyl at the composed frame σ.trans τ
  refine hcyl (σ.trans τ) K h hh (ConvexBody.imageLIE τ Q) ?_
  -- τ '' (Q : Set) = τ '' (cylHypSet σ K h) = cylHypSet (σ.trans τ) K h
  rw [imageLIE_apply]
  rw [hQ]
  exact cylHypSet_frame_comp m σ τ K h

/-! ## Oblique prisms (step 1 of the chain: next piece) -/

/-- `emb` as a linear map. -/
def embL (n : ℕ) : En n →ₗ[ℝ] En (n + 1) where
  toFun := emb n
  map_add' := by intro x y; exact emb_add n x y
  map_smul' := by intro a x; exact emb_smul n a x

theorem continuous_emb (n : ℕ) : Continuous (emb n) := by
  exact LinearMap.continuous_of_finiteDimensional (embL n)

/-- The oblique prism over the base `K` (a body of the coordinate hyperplane)
with direction `w`: `{emb x + t • w | x ∈ K, t ∈ [0,1]}`. -/
def obliquePrismSet (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) : Set (En (m + 1)) :=
  {y : En (m + 1) | ∃ x : En m, x ∈ (K : Set (En m)) ∧ ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ y = emb m x + t • w}

theorem obliquePrismSet_convex (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) :
    Convex ℝ (obliquePrismSet m K w) := by
  rintro y ⟨x1, hx1, t1, ht1, rfl⟩ z ⟨x2, hx2, t2, ht2, rfl⟩ a b ha hb hab
  refine ⟨a • x1 + b • x2, ?_, a • t1 + b • t2, ?_, ?_⟩
  · exact K.convex hx1 hx2 ha hb hab
  · exact (convex_Icc (0 : ℝ) 1) ht1 ht2 ha hb hab
  · calc
      a • (emb m x1 + t1 • w) + b • (emb m x2 + t2 • w)
          = (a • emb m x1 + a • (t1 • w)) + (b • emb m x2 + b • (t2 • w)) := by simp [smul_add]
      _ = (a • emb m x1 + b • emb m x2) + (a • (t1 • w) + b • (t2 • w)) := by abel
      _ = emb m (a • x1 + b • x2) + ((a • t1 + b • t2) • w) := by
            rw [← emb_smul m, ← emb_smul m, ← emb_add m]
            rw [smul_smul, smul_smul]
            simp only [smul_eq_mul]
            rw [← add_smul]

theorem obliquePrismSet_nonempty (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) :
    (obliquePrismSet m K w).Nonempty := by
  rcases K.nonempty with ⟨x, hx⟩
  refine ⟨emb m x + (0 : ℝ) • w, ⟨x, hx, (0 : ℝ), ?_, by simp⟩⟩
  exact left_mem_Icc.mpr zero_le_one

theorem obliquePrismSet_compact (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) :
    IsCompact (obliquePrismSet m K w) := by
  let f : En m × ℝ → En (m + 1) := fun p => emb m p.1 + p.2 • w
  have hf : Continuous f := by
    have h1 : Continuous (fun p : En m × ℝ => emb m p.1) := (continuous_emb m).comp continuous_fst
    have h2 : Continuous (fun p : En m × ℝ => p.2 • w) := Continuous.smul continuous_snd continuous_const
    exact h1.add h2
  have himage : obliquePrismSet m K w = f '' ((K : Set (En m)) ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext y
    constructor
    · rintro ⟨x, hx, t, ht, rfl⟩
      refine ⟨(x, t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
  rw [himage]
  exact IsCompact.image (K.isCompact.prod isCompact_Icc) hf

theorem obliquePrismSet_closed (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) :
    IsClosed (obliquePrismSet m K w) :=
  (obliquePrismSet_compact m K w).isClosed

theorem obliquePrismSet_bounded (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) :
    Bornology.IsBounded (obliquePrismSet m K w) :=
  (obliquePrismSet_compact m K w).isBounded

/-- The oblique prism over `K` in direction `w` as a convex body. -/
def obliquePrismBody (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) : ConvexBody (En (m + 1)) :=
  ⟨obliquePrismSet m K w, obliquePrismSet_convex m K w,
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨obliquePrismSet_closed m K w, obliquePrismSet_bounded m K w⟩,
    obliquePrismSet_nonempty m K w⟩

@[simp] theorem obliquePrismBody_coe (m : ℕ) (K : ConvexBody (En m)) (w : En (m + 1)) :
    (obliquePrismBody m K w : Set (En (m + 1))) = obliquePrismSet m K w := rfl

/-- Step 1 of the chain (Klain Fig. 2): an oblique prism over a base in a
hyperplane, in a direction with nonzero perpendicular component, vanishes.
Klain's argument: cut the prism into two pieces by a hyperplane, slide the
pieces (translations only) and re-paste them into a right cylinder over (a
translate of) the same base; fat bases are subdivided into skinny convex pieces
first.  Requires the full valuation bundle: continuity, quadruple additivity,
translation invariance, simplicity, and vanishing on every right cylinder
(in body form, `hcyl_body`). -/
theorem oblique_prism_zero_body (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
      (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
      (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
      μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
      (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ (K : ConvexBody (En m)) (w : En (m + 1)), lastCoord m w ≠ 0 →
      μ (obliquePrismBody m K w) = 0 := by
  intro K w hw
  -- convert the short (cylHypSet) hypothesis to L81's inline set form (definitionally equal)
  have hcyl' : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) =
        {y : En (m + 1) |
          (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => (ρ.symm y) (Fin.castSucc i)) ∈
            (K : Set (En m)) ∧
          (ρ.symm y) (Fin.last m) ∈ Set.Icc (0 : ℝ) h} →
        μ Q = 0 := by
    intro ρ K0 h hh Q hQ
    exact hcyl ρ K0 h hh Q (by simpa [cylHypSet] using hQ)
  have hqeq : (obliquePrismBody m K w : Set (En (m + 1))) =
      {y : En (m + 1) | ∃ x : En m, x ∈ (K : Set (En m)) ∧ ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
        y = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
              (fun j : Fin (m + 1) => if h : j = Fin.last m then (0 : ℝ) else x (Fin.castLT j (Fin.val_lt_last h))) + t • w} := by
    rw [obliquePrismBody_coe, obliquePrismSet]
    rfl
  exact Commons.Geometry.Convex.Hadwiger.oblique_prism_zero m μ hcont hadd htrans hsimple hcyl'
    K w (by simpa [lastCoord] using hw) (obliquePrismBody m K w) hqeq


/-- `bodyImage` agrees with Mathlib's `ConvexBody.imageLIE` on equal carriers. -/
theorem bodyImage_eq_imageLIE {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ : V ≃ₗᵢ[ℝ] V) (X : ConvexBody V) :
    bodyImage ρ X = ConvexBody.imageLIE ρ X := by
  apply ConvexBody.ext
  rfl

/-- Composing images: `ρ '' (σ '' X) = (σ.trans ρ) '' X` at the body level. -/
theorem imageLIE_bodyImage_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ σ : V ≃ₗᵢ[ℝ] V) (X : ConvexBody V) :
    ConvexBody.imageLIE ρ (bodyImage σ X) = bodyImage (σ.trans ρ) X := by
  apply ConvexBody.ext
  rw [imageLIE_apply, bodyImage_coe, bodyImage_coe]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨x0, hx0, rfl⟩
    refine ⟨x0, hx0, ?_⟩
    exact (LinearIsometryEquiv.trans_apply σ ρ x0).symm
  · rintro ⟨x0, hx0, rfl⟩
    refine ⟨σ x0, ?_, ?_⟩
    · exact ⟨x0, hx0, rfl⟩
    · exact LinearIsometryEquiv.trans_apply σ ρ x0

/-- All-frames version of `oblique_prism_zero`: an oblique prism over a base in
*any* hyperplane (the `ρ`-image of the coordinate hyperplane), in a direction
with nonzero component along that hyperplane's normal, vanishes.  Proof:
conjugate `μ` by `ρ` (the bundle and the cylinder hypothesis are preserved),
apply `oblique_prism_zero` to the conjugate, and translate back.  The single
remaining seam is the call to `oblique_prism_zero` (delegated: L81). -/
theorem oblique_prism_zero_frame (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
      (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
      (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
      μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
      (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (w : En (m + 1)),
      lastCoord m w ≠ 0 → μ (bodyImage ρ (obliquePrismBody m K w)) = 0 := by
  intro ρ K w hw
  -- conjugate μ by ρ; the bundle and cylinder hypothesis pass to the conjugate
  have hμρ := oblique_prism_zero_body m (conjVal ρ μ)
    (conjVal_cont ρ hcont) (conjVal_hadd ρ hadd) (conjVal_htrans ρ htrans)
    (conjVal_hsimple ρ hsimple) (conjVal_hcyl m ρ μ hcyl) K w hw
  -- hμρ : conjVal ρ μ (obliquePrismBody m K w) = 0, i.e. μ (imageLIE ρ prism) = 0
  change μ (ConvexBody.imageLIE ρ (obliquePrismBody m K w)) = 0 at hμρ
  rw [bodyImage_eq_imageLIE]
  exact hμρ


/-! ## Minkowski sum with a segment ("smearing") and the facet-smearing reduction -/

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The Minkowski sum `P + [0,1]·v` ("smearing" `P` by the segment `[0,v]`). -/
def smearBodySet (P : ConvexBody S) (v : S) : Set S :=
  {x : S | ∃ p : S, p ∈ (P : Set S) ∧ ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = p + t • v}

theorem smearBodySet_convex (P : ConvexBody S) (v : S) : Convex ℝ (smearBodySet P v) := by
  rintro x ⟨p1, hp1, t1, ht1, rfl⟩ y ⟨p2, hp2, t2, ht2, rfl⟩ a b ha hb hab
  refine ⟨a • p1 + b • p2, ?_, a • t1 + b • t2, ?_, ?_⟩
  · simpa using (P.convex hp1 hp2 ha hb hab)
  · exact (convex_Icc (0 : ℝ) 1) ht1 ht2 ha hb hab
  · calc
      a • (p1 + t1 • v) + b • (p2 + t2 • v)
          = (a • p1 + a • (t1 • v)) + (b • p2 + b • (t2 • v)) := by simp [smul_add]
      _ = (a • p1 + b • p2) + (a • (t1 • v) + b • (t2 • v)) := by abel
      _ = (a • p1 + b • p2) + ((a • t1 + b • t2) • v) := by
            rw [smul_smul, smul_smul]
            simp only [smul_eq_mul]
            rw [← add_smul]

theorem smearBodySet_nonempty (P : ConvexBody S) (v : S) : (smearBodySet P v).Nonempty := by
  rcases P.nonempty with ⟨p, hp⟩
  refine ⟨p + (0 : ℝ) • v, ⟨p, hp, (0 : ℝ), ?_, by simp⟩⟩
  exact left_mem_Icc.mpr zero_le_one

theorem smearBodySet_compact (P : ConvexBody S) (v : S) : IsCompact (smearBodySet P v) := by
  let f : S × ℝ → S := fun q => q.1 + q.2 • v
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have himage : smearBodySet P v = f '' ((P : Set S) ×ˢ Set.Icc (0 : ℝ) 1) := by
    ext x
    constructor
    · rintro ⟨p, hp, t, ht, rfl⟩
      refine ⟨(p, t), ?_, rfl⟩
      exact ⟨hp, ht⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1, hq.1, q.2, hq.2, rfl⟩
  rw [himage]
  exact IsCompact.image (P.isCompact.prod isCompact_Icc) hf

/-- The Minkowski sum `P + [0,v]` as a convex body. -/
def smearBody (P : ConvexBody S) (v : S) : ConvexBody S :=
  ⟨smearBodySet P v, smearBodySet_convex P v, smearBodySet_compact P v, smearBodySet_nonempty P v⟩

@[simp] theorem smearBody_coe (P : ConvexBody S) (v : S) : (smearBody P v : Set S) = smearBodySet P v := rfl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- Dissection glue: if the convex body `S` is the dissection
`S = P ∪ ⋃ᵢ Qᵢ` (pairwise empty-interior intersections) and every `Qᵢ` has
`μ`-value 0, then `μ S = μ P`.  (This is where the facet-smearing dissection
and `oblique_prism_zero_frame` will be combined.) -/
theorem smear_val_of_dissection
    (μ : ConvexBody V → ℝ) (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → μ K = 0)
    (S P : ConvexBody V) {ι : Type*} [Fintype ι] (Q : ι → ConvexBody V)
    (hcover : (S : Set V) = (P : Set V) ∪ ⋃ i : ι, (Q i : Set V))
    (hpairP : ∀ i : ι, interior (((P : Set V) ∩ (Q i : Set V))) = ∅)
    (hpairQ : ∀ i j : ι, i ≠ j → interior ((Q i : Set V) ∩ (Q j : Set V)) = ∅)
    (hQ : ∀ i : ι, μ (Q i) = 0) : μ S = μ P := by
  let F : Option ι → ConvexBody V := fun a => match a with
    | none => P | some i => Q i
  have hFcover : (S : Set V) = ⋃ a : Option ι, (F a : Set V) := by
    rw [hcover]
    simpa [F] using (Set.iUnion_option (s := fun a : Option ι => (F a : Set V))).symm
  have hFpair : ∀ a b : Option ι, a ≠ b → interior ((F a : Set V) ∩ (F b : Set V)) = ∅ := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exfalso; exact hab rfl
        | some j => simpa [F] using hpairP j
    | some i =>
        cases b with
        | none => simpa [F, inter_comm] using hpairP i
        | some j => exact hpairQ i j (by intro h; exact hab (by simp [h]))
  have hmain := dissection_additivity (ι := Option ι) μ hcont hadd hsimple (P := S) (A := F) hFcover hFpair
  rw [hmain]
  simp [F, hQ]

/-- First reduction of the facet-smearing lemma `μ(P + σ) = μ(P)`: if the
smearing body `smearBody P v` admits the dissection `P ∪ ⋃ᵢ Qᵢ` (pairwise
empty-interior intersections, supplied by the geometric smearing lemma) and
each prism piece `Qᵢ` vanishes (supplied by `oblique_prism_zero_frame`), then
`μ (smearBody P v) = μ P`. -/
theorem poly_smear_of_dissection
    (μ : ConvexBody V → ℝ) (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → μ K = 0)
    (P : ConvexBody V) (v : V) {ι : Type*} [Fintype ι] (Q : ι → ConvexBody V)
    (hcover : (smearBody P v : Set V) = (P : Set V) ∪ ⋃ i : ι, (Q i : Set V))
    (hpairP : ∀ i : ι, interior (((P : Set V) ∩ (Q i : Set V))) = ∅)
    (hpairQ : ∀ i j : ι, i ≠ j → interior ((Q i : Set V) ∩ (Q j : Set V)) = ∅)
    (hQ : ∀ i : ι, μ (Q i) = 0) : μ (smearBody P v) = μ P := by
  exact smear_val_of_dissection μ hcont hadd hsimple (smearBody P v) P Q hcover hpairP hpairQ hQ

lemma inner_eLast_eq_lastCoord (m : ℕ) (x : En (m + 1)) : inner ℝ x (eLast m) = lastCoord m x := by
  simp [eLast, lastCoord, PiLp.inner_apply]

lemma mem_emb_iff_inner_eLast (m : ℕ) (x : En (m + 1)) :
    (∃ y : En m, emb m y = x) ↔ inner ℝ x (eLast m) = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [inner_eLast_eq_lastCoord]
    simp
  · intro hx
    refine ⟨dropLast m x, ?_⟩
    have h := emb_dropLast_add_last m x
    have hlc : lastCoord m x = 0 := by
      rw [← inner_eLast_eq_lastCoord]
      exact hx
    calc
      emb m (dropLast m x) = emb m (dropLast m x) + 0 := by simp
      _ = emb m (dropLast m x) + lastCoord m x • eLast m := by simp [hlc]
      _ = x := h

lemma inner_symm_smul {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b : V) (c : ℝ) : inner ℝ (c • a) b = c * inner ℝ a b := by
  simp [inner_smul_left, real_inner_comm]

/-- carrier set of a translate body -/
def transSet {S : Type*} [NormedAddCommGroup S] (t : S) (A : Set S) : Set S :=
  (fun x : S => x + t) '' A

@[simp] theorem mem_transSet_iff {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (t : S) (A : Set S) (x : S) : x ∈ transSet t A ↔ ∃ a ∈ A, a + t = x := by
  constructor <;> intro h <;> exact h

theorem transSet_convex {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (t : S) {A : Set S} (hA : Convex ℝ A) : Convex ℝ (transSet t A) := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ s u hs hu hsu
  refine ⟨s • a + u • b, hA ha hb hs hu hsu, ?_⟩
  calc
    (s • a + u • b) + t = (s • a + u • b) + (s + u) • t := by rw [hsu]; simp
    _ = (s • a + u • b) + (s • t + u • t) := by rw [add_smul]
    _ = (s • a + s • t) + (u • b + u • t) := by abel
    _ = s • (a + t) + u • (b + t) := by rw [smul_add, smul_add]

theorem transSet_compact {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (t : S) {A : Set S} (hA : IsCompact A) : IsCompact (transSet t A) := by
  have hc : Continuous (fun x : S => x + t) := by fun_prop
  simpa [transSet] using hA.image hc

theorem transSet_nonempty {S : Type*} [NormedAddCommGroup S] (t : S) {A : Set S}
    (hA : A.Nonempty) : (transSet t A).Nonempty := by
  simpa [transSet] using hA.image (fun x : S => x + t)

def transBody {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (t : S) (A : ConvexBody S) : ConvexBody S :=
  ⟨transSet t (A : Set S), transSet_convex t A.convex, transSet_compact t A.isCompact,
    transSet_nonempty t A.nonempty⟩

@[simp] theorem transBody_coe {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (t : S) (A : ConvexBody S) : (transBody t A : Set S) = transSet t (A : Set S) := rfl

theorem inner_lie_symm {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (ρ : V ≃ₗᵢ[ℝ] W) (u : W) (v : V) :
    inner ℝ (ρ.symm u) v = inner ℝ u (ρ v) := by
  rw [← LinearIsometryEquiv.inner_map_map ρ (ρ.symm u) v]
  simp

theorem mem_image_lie_emb_iff {m : ℕ} (w : En (m + 1)) (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1))
    (hρ : ρ (eLast m) = ‖w‖⁻¹ • w) (hw : w ≠ 0) (z : En (m + 1)) :
    z ∈ (fun y : En (m + 1) => ρ y) '' ((emb m) '' (Set.univ : Set (En m))) ↔ inner ℝ w z = 0 := by
  have hc : ‖w‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hw)
  constructor
  · rintro ⟨y, hy, hz⟩
    rcases hy with ⟨x, _, rfl⟩
    have hmain : inner ℝ (ρ (emb m x)) w = 0 := by
      have h1 : inner ℝ (ρ (emb m x)) (ρ (eLast m)) = 0 := by
        rw [LinearIsometryEquiv.inner_map_map]
        rw [inner_eLast_eq_lastCoord]
        simp
      rw [hρ] at h1
      have hsmul : inner ℝ (ρ (emb m x)) (‖w‖⁻¹ • w) = ‖w‖⁻¹ * inner ℝ (ρ (emb m x)) w := by
        rw [inner_smul_right]
      rw [hsmul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hc
    rw [← hz]
    simpa [real_inner_comm] using hmain
  · intro hz0
    have hpre : ∃ x : En m, emb m x = ρ.symm z := by
      apply (mem_emb_iff_inner_eLast m (ρ.symm z)).mpr
      rw [inner_lie_symm, hρ]
      have hsmul : inner ℝ z (‖w‖⁻¹ • w) = ‖w‖⁻¹ * inner ℝ z w := by
        rw [inner_smul_right]
      rw [hsmul]
      have hzw : inner ℝ z w = 0 := by simpa [real_inner_comm] using hz0
      simp [hzw]
    rcases hpre with ⟨x, hx⟩
    refine ⟨emb m x, ⟨x, by simp, rfl⟩, ?_⟩
    rw [hx]
    simp

theorem lastCoord_symm_ne_zero_iff {m : ℕ} (w v : En (m + 1))
    (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1))
    (hρ : ρ (eLast m) = ‖w‖⁻¹ • w) (hw : w ≠ 0) :
    lastCoord m (ρ.symm v) ≠ 0 ↔ inner ℝ w v ≠ 0 := by
  have hc : ‖w‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hw)
  have hiff : lastCoord m (ρ.symm v) = 0 ↔ inner ℝ w v = 0 := by
    constructor
    · intro hlc
      have hmem : ∃ x : En m, emb m x = ρ.symm v :=
        (mem_emb_iff_inner_eLast m (ρ.symm v)).mpr (by simpa [inner_eLast_eq_lastCoord] using hlc)
      rcases hmem with ⟨x, hx⟩
      have hz : ρ (emb m x) = v := by
        calc
          ρ (emb m x) = ρ (ρ.symm v) := by rw [hx]
          _ = v := by simp
      have hmemv : v ∈ (fun y : En (m + 1) => ρ y) '' ((emb m) '' (Set.univ : Set (En m))) := by
        refine ⟨emb m x, ?_, ?_⟩
        · exact ⟨x, by simp, rfl⟩
        · exact hz
      exact (mem_image_lie_emb_iff w ρ hρ hw v).mp hmemv
    · intro hwv0
      rw [← inner_eLast_eq_lastCoord]
      rw [inner_lie_symm, hρ]
      have hsmul : inner ℝ v (‖w‖⁻¹ • w) = ‖w‖⁻¹ * inner ℝ w v := by
        rw [inner_smul_right]
        simp [real_inner_comm]
      rw [hsmul, hwv0]
      simp
  constructor
  · intro hn hz
    exact hn (hiff.mpr hz)
  · intro hz hn
    exact hz (hiff.mp hn)


/-- Convex body of `En m` whose `emb`-image is the set `A ⊆ emb(En m)`. -/
def baseOfImage (m : ℕ) (A : Set (En (m + 1)))
    (hA_sub : A ⊆ (emb m) '' (Set.univ : Set (En m)))
    (hAcvx : Convex ℝ A) (hAcpt : IsCompact A) (hAne : A.Nonempty) : ConvexBody (En m) :=
  ⟨{x : En m | emb m x ∈ A}, by
    rintro x hx y hy a b ha hb hab
    have hxy : emb m (a • x + b • y) = a • emb m x + b • emb m y := by
      rw [← emb_smul m a x, ← emb_smul m b y, ← emb_add m]
    change emb m (a • x + b • y) ∈ A
    rw [hxy]
    exact hAcvx hx hy ha hb hab, by
    have hdrop_cont : Continuous (dropLast m) := by
      exact LinearMap.continuous_of_finiteDimensional
        { toFun := dropLast m, map_add' := dropLast_add m, map_smul' := dropLast_smul m }
    have hcar : {x : En m | emb m x ∈ A} = dropLast m '' A := by
      ext x
      constructor
      · intro hx
        refine ⟨emb m x, hx, ?_⟩
        rw [dropLast_emb]
      · rintro ⟨a, ha, hxa⟩
        have haemb : a ∈ (emb m) '' (Set.univ : Set (En m)) := hA_sub ha
        rcases haemb with ⟨y, _, hay⟩
        have hdl : emb m (dropLast m a) = a := by
          rw [← hay, dropLast_emb]
        change emb m x ∈ A
        rw [← hxa, hdl]
        exact ha
    rw [hcar]
    exact IsCompact.image hAcpt hdrop_cont, by
    rcases hAne with ⟨a, ha⟩
    rcases hA_sub ha with ⟨y, _, hay⟩
    refine ⟨y, ?_⟩
    change emb m y ∈ A
    rw [hay]
    exact ha⟩

@[simp] theorem baseOfImage_coe (m : ℕ) (A : Set (En (m + 1)))
    (hA_sub : A ⊆ (emb m) '' (Set.univ : Set (En m)))
    (hAcvx : Convex ℝ A) (hAcpt : IsCompact A) (hAne : A.Nonempty) :
    ((baseOfImage m A hA_sub hAcvx hAcpt hAne : ConvexBody (En m)) : Set (En m)) =
      {x : En m | emb m x ∈ A} := rfl

theorem emb_baseOfImage (m : ℕ) (A : Set (En (m + 1)))
    (hA_sub : A ⊆ (emb m) '' (Set.univ : Set (En m)))
    (hAcvx : Convex ℝ A) (hAcpt : IsCompact A) (hAne : A.Nonempty) :
    (emb m) '' ((baseOfImage m A hA_sub hAcvx hAcpt hAne : ConvexBody (En m)) : Set (En m)) = A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hz
    have hm : z ∈ (emb m) '' (Set.univ : Set (En m)) := hA_sub hz
    rcases hm with ⟨x, _, hxz⟩
    refine ⟨x, ?_, hxz⟩
    rw [baseOfImage_coe]
    change emb m x ∈ A
    rw [hxz]
    exact hz


/-- Per-piece zero, full-dimensional case: prism over a convex compact set `F` contained in a
level hyperplane `{inner w = c}` (`w ≠ 0`), with nonempty interior, vanishes. -/
theorem prismFace_full_zero (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
      (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
      (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
      μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
      (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0)
    (a0 w v : En (m + 1)) (F : Set (En (m + 1)))
    (hw : w ≠ 0) (ha0 : a0 ∈ F)
    (hFcvx : Convex ℝ F) (hFcpt : IsCompact F)
    (hFlev : F ⊆ {x : En (m + 1) | inner ℝ w x = inner ℝ w a0})
    (Q : ConvexBody (En (m + 1)))
    (hQ : (Q : Set (En (m + 1))) =
      {x : En (m + 1) | ∃ f : En (m + 1), f ∈ F ∧ ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v})
    (hfull : (interior (Q : Set (En (m + 1)))).Nonempty) :
    μ Q = 0 := by
  classical
  -- 1. inner w v ≠ 0
  have hwv : inner ℝ w v ≠ 0 := by
    intro hwv0
    have hsub : {x : En (m + 1) | ∃ f : En (m + 1), f ∈ F ∧
          ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v}
        ⊆ {x : En (m + 1) | inner ℝ w x = inner ℝ w a0} := by
      intro x hx
      rcases hx with ⟨f, hf, t, ht, rfl⟩
      have hfc : inner ℝ w f = inner ℝ w a0 := hFlev hf
      change inner ℝ w (f + t • v) = inner ℝ w a0
      rw [inner_add_right, inner_smul_right]
      simp [hfc, hwv0]
    have hL : interior {x : En (m + 1) | inner ℝ w x = inner ℝ w a0} = ∅ :=
      interior_level_const_empty hw (inner ℝ w a0)
    have hmono : interior {x : En (m + 1) | ∃ f : En (m + 1), f ∈ F ∧
          ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = f + t • v}
        ⊆ interior {x : En (m + 1) | inner ℝ w x = inner ℝ w a0} := interior_mono hsub
    have hint : interior (Q : Set (En (m + 1))) = ∅ := by
      rw [hQ]
      rw [hL] at hmono
      exact eq_empty_of_subset_empty hmono
    have : ¬ (interior (Q : Set (En (m + 1)))).Nonempty := by
      rw [hint]
      exact not_nonempty_empty
    exact (this hfull)
  -- 2. frame ρ with ρ (eLast m) = ‖w‖⁻¹ • w
  rcases exists_lie_unit_to_unit (eLast m) (by simp) w hw with ⟨ρ, hρ⟩
  let w0 : En (m + 1) := ρ.symm v
  have hw0 : lastCoord m w0 ≠ 0 := (lastCoord_symm_ne_zero_iff w v ρ hρ hw).mpr hwv
  -- 3. F0 := F - a0
  let F0 : Set (En (m + 1)) := {x : En (m + 1) | a0 + x ∈ F}
  have hF0_cvx : Convex ℝ F0 := by
    rintro x hx y hy a b ha hb hab
    have hmain : a0 + (a • x + b • y) = a • (a0 + x) + b • (a0 + y) := by
      calc
        a0 + (a • x + b • y) = (a + b) • a0 + (a • x + b • y) := by rw [hab]; simp
        _ = (a • a0 + a • x) + (b • a0 + b • y) := by rw [add_smul]; abel
        _ = a • (a0 + x) + b • (a0 + y) := by rw [smul_add, smul_add]
    change a0 + (a • x + b • y) ∈ F
    rw [hmain]
    exact hFcvx hx hy ha hb hab
  have hF0_cpt : IsCompact F0 := by
    have hc : Continuous (fun y : En (m + 1) => y - a0) := by fun_prop
    have him : F0 = (fun y : En (m + 1) => y - a0) '' F := by
      ext x
      constructor
      · intro hx
        refine ⟨a0 + x, hx, ?_⟩
        change a0 + x - a0 = x
        abel
      · rintro ⟨y, hy, hxy⟩
        change a0 + x ∈ F
        rw [← hxy]
        change a0 + (y - a0) ∈ F
        have : a0 + (y - a0) = y := by abel
        rw [this]
        exact hy
    rw [him]
    exact IsCompact.image hFcpt hc
  have hF0_ne : F0.Nonempty := by
    refine ⟨0, ?_⟩
    change a0 + (0 : En (m + 1)) ∈ F
    simpa using ha0
  have hF0_ker : F0 ⊆ {x : En (m + 1) | inner ℝ w x = 0} := by
    intro x hx
    have hfc' : inner ℝ w x = 0 := by
      have := hFlev hx
      change inner ℝ w (a0 + x) = inner ℝ w a0 at this
      have hplus : inner ℝ w (a0 + x) = inner ℝ w a0 + inner ℝ w x := by simp [inner_add_right]
      rw [hplus] at this
      linarith
    exact hfc' 
  -- 4. A0 := ρ.symm '' F0 (lies in the coordinate hyperplane); base body
  let A0 : Set (En (m + 1)) := ρ.symm '' F0
  have hA0_sub : A0 ⊆ (emb m) '' (Set.univ : Set (En m)) := by
    intro y hy
    rcases hy with ⟨x, hx, hyx⟩
    have hxker : inner ℝ w x = 0 := hF0_ker hx
    have hinner : inner ℝ y (eLast m) = 0 := by
      rw [← hyx]
      have h1 : inner ℝ (ρ.symm x) (eLast m) = inner ℝ x (ρ (eLast m)) := inner_lie_symm ρ x (eLast m)
      rw [h1, hρ]
      have hsmul : inner ℝ x (‖w‖⁻¹ • w) = ‖w‖⁻¹ * inner ℝ w x := by
        rw [inner_smul_right]
        simp [real_inner_comm]
      rw [hsmul, hxker]
      simp
    rcases (mem_emb_iff_inner_eLast m y).mpr hinner with ⟨z, hz⟩
    exact ⟨z, by simp, hz⟩
  have hA0_cvx : Convex ℝ A0 := by
    simpa [A0] using hF0_cvx.linear_image (ρ.symm : En (m + 1) →ₗ[ℝ] En (m + 1))
  have hA0_cpt : IsCompact A0 := by
    simpa [A0] using IsCompact.image hF0_cpt (by fun_prop : Continuous (fun x : En (m + 1) => ρ.symm x))
  have hA0_ne : A0.Nonempty := by
    simpa [A0] using hF0_ne.image (fun x : En (m + 1) => ρ.symm x)
  let K : ConvexBody (En m) := baseOfImage m A0 hA0_sub hA0_cvx hA0_cpt hA0_ne
  -- 5. ρ emb K = F0
  have hρembK : (fun y : En (m + 1) => ρ y) '' (emb m '' (K : Set (En m))) = F0 := by
    have h1 : (emb m) '' (K : Set (En m)) = A0 := by
      dsimp [K]
      exact emb_baseOfImage m A0 hA0_sub hA0_cvx hA0_cpt hA0_ne
    calc
      (fun y : En (m + 1) => ρ y) '' (emb m '' (K : Set (En m))) = ρ '' (emb m '' (K : Set (En m))) := rfl
      _ = ρ '' A0 := by rw [h1]
      _ = F0 := by
        change ρ '' (ρ.symm '' F0) = F0
        rw [Set.image_image]
        have hid : (fun y : En (m + 1) => ρ (ρ.symm y)) = id := by
          funext y
          simp
        rw [hid]
        simp
  -- 6. vanishing of the frame-prism body
  have hzero : μ (bodyImage ρ (obliquePrismBody m K w0)) = 0 :=
    oblique_prism_zero_frame m μ hcont hadd htrans hsimple hcyl ρ K w0 hw0
  -- 7. set identity: Q-set = a0 + bodyImage-set
  have hset : (Q : Set (En (m + 1))) =
      transSet a0 (bodyImage ρ (obliquePrismBody m K w0) : Set (En (m + 1))) := by
    rw [hQ]
    ext x
    constructor
    · intro hx
      rcases hx with ⟨f, hf, t, ht, rfl⟩
      have hf0 : f - a0 ∈ F0 := by
        change a0 + (f - a0) ∈ F
        have : a0 + (f - a0) = f := by abel
        rw [this]
        exact hf
      have hf0rk : f - a0 ∈ (fun y : En (m + 1) => ρ y) '' (emb m '' (K : Set (En m))) := by
        rw [hρembK]
        exact hf0
      rcases hf0rk with ⟨g, hg, hfg⟩
      have hfgρ : ρ g = f - a0 := by simpa using hfg
      rcases hg with ⟨z, hz, hgz⟩
      have hρz : ρ (emb m z) = f - a0 := by
        rw [hgz]
        exact hfgρ
      have hlin : ρ (emb m z + t • w0) = ρ (emb m z) + t • ρ w0 := by
        rw [map_add, map_smul]
      have hρw0 : ρ w0 = v := by
        dsimp [w0]
        simp
      have hb : ρ (emb m z + t • w0) ∈ bodyImage ρ (obliquePrismBody m K w0) := by
        change ρ (emb m z + t • w0) ∈
          ((bodyImage ρ (obliquePrismBody m K w0) : ConvexBody (En (m + 1))) : Set (En (m + 1)))
        rw [bodyImage_coe]
        refine ⟨emb m z + t • w0, ?_, rfl⟩
        rw [obliquePrismBody_coe]
        exact ⟨z, hz, t, ht, rfl⟩
      rw [mem_transSet_iff]
      refine ⟨ρ (emb m z + t • w0), hb, ?_⟩
      calc
        ρ (emb m z + t • w0) + a0 = (ρ (emb m z) + t • ρ w0) + a0 := by rw [hlin]
        _ = (ρ (emb m z) + t • v) + a0 := by rw [hρw0]
        _ = (f - a0 + t • v) + a0 := by rw [hρz]
        _ = f + t • v := by abel
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have hxy' : y + a0 = x := by simpa using hxy
      change y ∈ ((bodyImage ρ (obliquePrismBody m K w0) : ConvexBody (En (m + 1))) : Set (En (m + 1))) at hy
      rw [bodyImage_coe] at hy
      rcases hy with ⟨s, hs, hys⟩
      have hysρ : ρ s = y := by simpa using hys
      rw [obliquePrismBody_coe] at hs
      rcases hs with ⟨z, hz, t, ht, hsz⟩
      have hlin : ρ (emb m z + t • w0) = ρ (emb m z) + t • ρ w0 := by
        rw [map_add, map_smul]
      have hρw0 : ρ w0 = v := by
        dsimp [w0]
        simp
      have hρzF0 : ρ (emb m z) ∈ F0 := by
        rw [← hρembK]
        exact ⟨emb m z, ⟨z, hz, rfl⟩, rfl⟩
      let f : En (m + 1) := a0 + ρ (emb m z)
      have hfF : f ∈ F := hρzF0
      refine ⟨f, hfF, t, ht, ?_⟩
      have hyval : y = ρ (emb m z + t • w0) := by
        calc
          y = ρ s := by rw [hysρ]
          _ = ρ (emb m z + t • w0) := by rw [hsz]
      calc
        x = y + a0 := by rw [hxy']
        _ = ρ (emb m z + t • w0) + a0 := by rw [hyval]
        _ = (ρ (emb m z) + t • ρ w0) + a0 := by rw [hlin]
        _ = (ρ (emb m z) + t • v) + a0 := by rw [hρw0]
        _ = (a0 + ρ (emb m z)) + t • v := by abel
        _ = f + t • v := rfl
  -- conclusion
  have htr : μ Q = μ (bodyImage ρ (obliquePrismBody m K w0)) := by
    exact (htrans (bodyImage ρ (obliquePrismBody m K w0)) Q a0 (by
      rw [hset]
      rfl)).symm
  rw [htr]
  exact hzero

/-- `topFace w P` is compact when `P` is a nonempty compact convex set (extreme value). -/
theorem topFace_compact_of_compact {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (w : V) {P : Set V} (hPcpt : IsCompact P) (hPne : P.Nonempty) :
    IsCompact (topFace w P) := by
  classical
  have hcont : Continuous (fun x : V => inner ℝ w x) := by fun_prop
  rcases hPcpt.exists_isMaxOn hPne hcont.continuousOn with ⟨x0, hx0, hx0max⟩
  have hlev : topFace w P = {x ∈ P | inner ℝ w x = inner ℝ w x0} :=
    topFace_eq_level (n := w) (q := x0) hx0 (by intro y hy; simpa using hx0max hy)
  rw [hlev]
  -- closed subset of compact
  have hclP : IsClosed P := hPcpt.isClosed
  have hcllev : IsClosed {x : V | inner ℝ w x = inner ℝ w x0} := by
    exact isClosed_eq (by fun_prop : Continuous (fun x : V => inner ℝ w x)) continuous_const
  have hcl : IsClosed ({x | x ∈ P ∧ inner ℝ w x = inner ℝ w x0}) := by
    have heq : {x | x ∈ P ∧ inner ℝ w x = inner ℝ w x0} =
        P ∩ {x : V | inner ℝ w x = inner ℝ w x0} := by
      ext x
      rfl
    rw [heq]
    exact hclP.inter hcllev
  refine IsCompact.of_isClosed_subset hPcpt hcl ?_
  intro x hx
  exact hx.1

/-- `poly_smear` (step 2 of the chain): adding a segment to a full-dimensional polytope
does not change the value. -/
theorem poly_smear
    (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ) (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
      (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
      (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
      μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
      (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0)
    (u : Finset (En (m + 1))) (P : ConvexBody (En (m + 1)))
    (hP : (P : Set (En (m + 1))) = convexHull ℝ (u : Set (En (m + 1))))
    (hint : (interior (P : Set (En (m + 1)))).Nonempty)
    (v : En (m + 1)) :
    μ (smearBody P v) = μ P := by
  classical
  have hPcvx : Convex ℝ (P : Set (En (m + 1))) := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set (En (m + 1)))
  have hPcpt : IsCompact (P : Set (En (m + 1))) := by
    rw [hP]
    exact (Finset.finite_toSet u).isCompact_convexHull ℝ
  have hPne : (P : Set (En (m + 1))).Nonempty := by
    rcases hint with ⟨x, hx⟩
    exact ⟨x, interior_subset hx⟩
  rcases polytope_smear_dissection_normal (n := m + 1) (u := u)
      (P := (P : Set (En (m + 1)))) hP hint v with ⟨ι, inst, Q, hQw, hcover, hpairP, hpairQ⟩
  -- per-piece zero
  have hQ0 : ∀ i : ι, μ (Q i) = 0 := by
    intro i
    rcases hQw i with ⟨w, hw, hwv, hQi⟩
    by_cases hfull : (interior (Q i : Set (En (m + 1)))).Nonempty
    · -- full-dimensional case: prism over a face in a level hyperplane
      have hFne : (topFace w (P : Set (En (m + 1)))).Nonempty := by
        have hQne : ((Q i : ConvexBody (En (m + 1))) : Set (En (m + 1))).Nonempty := (Q i).nonempty
        rw [hQi] at hQne
        rcases hQne with ⟨z, hz⟩
        rcases hz with ⟨a0, ha0, t, ht, hz⟩
        exact ⟨a0, ha0⟩
      rcases hFne with ⟨a0, ha0⟩
      have hFcvx : Convex ℝ (topFace w (P : Set (En (m + 1)))) :=
        topFace_convex (n := w) hPcvx
      have hFcpt : IsCompact (topFace w (P : Set (En (m + 1)))) :=
        topFace_compact_of_compact w hPcpt hPne
      have hFlev : topFace w (P : Set (En (m + 1))) ⊆
          {x : En (m + 1) | inner ℝ w x = inner ℝ w a0} := by
        intro f hf
        exact topFace_eq_of_mem hf ha0
      exact prismFace_full_zero m μ hcont hadd htrans hsimple hcyl a0 w v
        (topFace w (P : Set (En (m + 1)))) hw ha0 hFcvx hFcpt hFlev (Q i) hQi hfull
    · -- degenerate: interior empty
      have hQiE : interior (Q i : Set (En (m + 1))) = ∅ := (Set.not_nonempty_iff_eq_empty).mp hfull
      exact hsimple (Q i) hQiE
  -- glue
  have hcover' : (smearBody P v : Set (En (m + 1))) =
      (P : Set (En (m + 1))) ∪ ⋃ i : ι, (Q i : Set (En (m + 1))) := by
    rw [smearBody_coe]
    unfold smearBodySet
    exact hcover
  exact poly_smear_of_dissection μ hcont hadd hsimple P v Q hcover' hpairP hpairQ hQ0

/-! ## Zonotopes and zonoids (next layer; does not wait on L81/L82 for its API)

A *zonotope* is a finite Minkowski sum of segments; here we represent a finite
family of segments by a `List V` of their endpoint vectors and form the
zonotope by repeatedly smearing (`smearBody · u`), i.e.

`foldSmear P us := us.foldr (fun u B => smearBody B u) P`

so `foldSmear P us` is `P + [0,u₁] + … + [0,uₖ]` (the Minkowski sum of `P`
with the segments of `us`); `foldSmear {0} us` is the zonotope `Z(us)`.

Chain (Klain Thm 3.3 steps 2–3), decomposed:
* `foldSmear_value_eq` (proved below): if `μ` is invariant under adding a
  single segment to *any* body (`hseg`), then `μ (foldSmear P us) = μ P`;
  in particular, for `P = {0}` (a body with `μ = 0` by simplicity) every
  zonotope vanishes.  The invariance `hseg` is supplied later by `poly_smear`
  (full-dim polytopes `P`) extended by density to all bodies — both are
  behind the L81/L82 seams; this lemma is the mechanical iteration on top.
* Zonoids: a zonoid is a Hausdorff limit of zonotopes; then `μ(Y)=0` and
  `μ(K+Y)=μ(K)` follow from the zonotope results by continuity and
  continuity of `(K,L) ↦ K+L` (Hausdorff), plus `polytope_dense` to go from
  polytopes to all bodies.
-/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Iterated smearing of `P` by a list of segments (the Minkowski sum of `P`
with the segments of `us`). -/
def foldSmear (P : ConvexBody W) (us : List W) : ConvexBody W :=
  us.foldr (fun u B => smearBody B u) P

@[simp] theorem foldSmear_nil (P : ConvexBody W) : foldSmear P [] = P := rfl

theorem foldSmear_cons (P : ConvexBody W) (u : W) (us : List W) :
    foldSmear P (u :: us) = smearBody (foldSmear P us) u := rfl

/-- Adding segments one at a time does not change the `μ`-value, provided `μ` is
invariant under adding a single segment to every body.  (The invariance is
exactly what `poly_smear` + polytope density will supply.) -/
theorem foldSmear_value_eq (μ : ConvexBody W → ℝ)
    (hseg : ∀ (B : ConvexBody W) (u : W), μ (smearBody B u) = μ B) :
    ∀ (P : ConvexBody W) (us : List W), μ (foldSmear P us) = μ P := by
  intro P us
  induction us with
  | nil => simp
  | cons u us ih =>
      rw [foldSmear_cons]
      rw [hseg (foldSmear P us) u]
      exact ih

/-- The degenerate singleton body `{0}` (explicit type parameter so the
`ConvexBody` → `Set` coercion elaborates). -/
def pointBody (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : ConvexBody V :=
  ⟨({0} : Set V), convex_singleton (0 : V), isCompact_singleton, ⟨0, rfl⟩⟩

@[simp] theorem pointBody_coe (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ((pointBody V : ConvexBody V) : Set V) = ({0} : Set V) := rfl

/-- Standalone conditional zonotope vanishing: if `μ` is invariant under
adding a single segment to any body (`hseg`) and vanishes on the point
(`h0`), then every zonotope `foldSmear (pointBody W) us` (finite Minkowski
sum of segments from `0`) vanishes.  This is the precise interface that
`poly_smear` (+ density + simplicity at `{0}`) will later satisfy; nothing
here needs additivity or continuity. -/
theorem zonotope_zero_of_hseg (μ : ConvexBody W → ℝ)
    (hseg : ∀ (B : ConvexBody W) (u : W), μ (smearBody B u) = μ B)
    (h0 : μ (pointBody W) = 0) :
    ∀ us : List W, μ (foldSmear (pointBody W) us) = 0 := by
  intro us
  rw [foldSmear_value_eq μ hseg (pointBody W) us, h0]

/-- Generic Minkowski sum of two convex bodies. -/
def bodyAdd (P L : ConvexBody W) : ConvexBody W :=
  ⟨{x : W | ∃ p : W, p ∈ (P : Set W) ∧ ∃ ℓ : W, ℓ ∈ (L : Set W) ∧ x = p + ℓ},
   by
     rintro x ⟨p1,hp1,ℓ1,hℓ1,rfl⟩ y ⟨p2,hp2,ℓ2,hℓ2,rfl⟩ a b ha hb hab
     refine ⟨a • p1 + b • p2, ?_, a • ℓ1 + b • ℓ2, ?_, ?_⟩
     · simpa using (P.convex hp1 hp2 ha hb hab)
     · simpa using (L.convex hℓ1 hℓ2 ha hb hab)
     · rw [smul_add, smul_add]; abel,
   by
     let f : W × W → W := fun q => q.1 + q.2
     have hf : Continuous f := by dsimp [f]; fun_prop
     have him : {x : W | ∃ p, p ∈ (P : Set W) ∧ ∃ ℓ, ℓ ∈ (L : Set W) ∧ x = p + ℓ} =
         f '' ((P : Set W) ×ˢ (L : Set W)) := by
       ext x; constructor
       · rintro ⟨p,hp,ℓ,hℓ,rfl⟩; refine ⟨(p,ℓ), ⟨hp,hℓ⟩, rfl⟩
       · rintro ⟨q,hq,rfl⟩; exact ⟨q.1,hq.1,q.2,hq.2,rfl⟩
     rw [him]
     exact IsCompact.image (P.isCompact.prod L.isCompact) hf,
   by
     rcases P.nonempty with ⟨p,hp⟩; rcases L.nonempty with ⟨ℓ,hℓ⟩
     refine ⟨p + ℓ, ⟨p,hp,ℓ,hℓ,rfl⟩⟩⟩

@[simp] theorem bodyAdd_coe (P L : ConvexBody W) :
    (bodyAdd P L : Set W) =
      {x : W | ∃ p : W, p ∈ (P : Set W) ∧ ∃ ℓ : W, ℓ ∈ (L : Set W) ∧ x = p + ℓ} := rfl

theorem bodyAdd_pointBody (P : ConvexBody W) : bodyAdd P (pointBody W) = P := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨p,hp,ℓ,hℓ,rfl⟩
    have hℓ0 : ℓ = 0 := by
      change ℓ ∈ ({0} : Set W) at hℓ
      simpa using hℓ
    simpa [hℓ0] using hp
  · intro hx
    refine ⟨x, hx, (0 : W), ?_, by simp⟩
    change (0 : W) ∈ ({0} : Set W)
    simp

theorem bodyAdd_smearBody (P Z : ConvexBody W) (u : W) :
    bodyAdd P (smearBody Z u) = smearBody (bodyAdd P Z) u := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨p,hp,z,hz,rfl⟩
    rcases hz with ⟨z0,hz0,t,ht,rfl⟩
    refine ⟨p + z0, ?_, t, ht, ?_⟩
    · exact ⟨p, hp, z0, hz0, rfl⟩
    · rw [add_assoc]
  · rintro ⟨y,hy,t,ht,rfl⟩
    rcases hy with ⟨p,hp,z,hz,rfl⟩
    refine ⟨p, hp, z + t • u, ?_, ?_⟩
    · refine ⟨z, hz, t, ht, rfl⟩
    · rw [add_assoc]

/-- Set-extensionality bridge: `P + Z(us) = foldSmear P us`, where
`Z(us) = foldSmear (pointBody W) us` is the zonotope (Minkowski sum of the
segments `[0,u]`, `u ∈ us`) and `P + Z` is the body-level Minkowski sum. -/
theorem bodyAdd_foldSmear (P : ConvexBody W) (us : List W) :
    bodyAdd P (foldSmear (pointBody W) us) = foldSmear P us := by
  induction us with
  | nil => simp [foldSmear, bodyAdd_pointBody]
  | cons u us ih =>
      rw [foldSmear_cons, foldSmear_cons]
      rw [bodyAdd_smearBody]
      rw [ih]

/-- Companion of `zonotope_zero_of_hseg`: `μ (P + Z) = μ P` for every
zonotope `Z`, again as a pure consequence of one-segment invariance. -/
theorem bodyAdd_foldSmear_value_eq (μ : ConvexBody W → ℝ)
    (hseg : ∀ (B : ConvexBody W) (u : W), μ (smearBody B u) = μ B) :
    ∀ (P : ConvexBody W) (us : List W), μ (bodyAdd P (foldSmear (pointBody W) us)) = μ P := by
  intro P us
  rw [bodyAdd_foldSmear]
  exact foldSmear_value_eq μ hseg P us

/-- The segment `{t • v | 0 ≤ t ≤ 1}` as a convex body. -/
def segBodyK {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] (v : S) : ConvexBody S :=
  ⟨{x : S | ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = t • v},
   by
     rintro x ⟨t, ht, rfl⟩ y ⟨s, hs, rfl⟩ a b ha hb hab
     refine ⟨a * t + b * s, ?_, ?_⟩
     · exact (convex_Icc (0 : ℝ) 1) ht hs ha hb hab
     · rw [smul_smul, smul_smul]
       rw [add_smul],
   by
     have hc : Continuous (fun t : ℝ => t • v) := by fun_prop
     have him : {x : S | ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = t • v} =
         (fun t : ℝ => t • v) '' (Set.Icc (0 : ℝ) 1) := by
       ext x
       constructor <;> rintro ⟨t, ht, rfl⟩ <;> refine ⟨t, ht, rfl⟩
     rw [him]
     exact IsCompact.image isCompact_Icc hc,
   by
     refine ⟨(0 : S), ?_⟩
     refine ⟨(0 : ℝ), ?_, ?_⟩
     · exact left_mem_Icc.mpr zero_le_one
     · simp⟩

@[simp] theorem segBodyK_coe {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (v : S) : (segBodyK v : Set S) = {x : S | ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x = t • v} := rfl

/-- Smearing by `v` is the same as Minkowski addition of the segment `segBodyK v`. -/
theorem smearBody_eq_add_segBody {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (K : ConvexBody S) (v : S) : smearBody K v = K + segBodyK v := by
  apply ConvexBody.ext
  ext x
  constructor
  · rintro ⟨p, hp, t, ht, rfl⟩
    refine ⟨p, hp, t • v, ?_, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨p, hp, y, hy, hxy⟩
    rcases hy with ⟨t, ht, hyt⟩
    refine ⟨p, hp, t, ht, ?_⟩
    calc
      x = p + y := hxy.symm
      _ = p + t • v := by rw [← hyt]

/-- WIRING: from the full valuation bundle + raw cylinder hypothesis, `μ` is invariant
under adding a single segment `[0,u]` to *any* body (`poly_smear` for full-dimensional
polytopes + polytope density + continuity of `μ` and of `B ↦ smearBody B u`). -/
theorem smear_invariance (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ (B : ConvexBody (En (m + 1))) (u : En (m + 1)), μ (smearBody B u) = μ B := by
  classical
  intro B u
  have hpoly : ∀ (P : ConvexBody (En (m + 1))) (w : Finset (En (m + 1))),
      (P : Set (En (m + 1))) = convexHull ℝ (w : Set (En (m + 1))) →
      (interior (P : Set (En (m + 1)))).Nonempty →
      μ (smearBody P u) = μ P := by
    intro P w hPw hintw
    exact poly_smear m μ hcont hadd htrans hsimple hcyl w P hPw hintw u
  have hcontS : Continuous (fun X : ConvexBody (En (m + 1)) => smearBody X u) := by
    have hfuneq : (fun X : ConvexBody (En (m + 1)) => smearBody X u) =
        fun X : ConvexBody (En (m + 1)) => X + segBodyK u := by
      funext X
      exact smearBody_eq_add_segBody X u
    rw [hfuneq]
    exact continuous_bodyAdd_left (segBodyK u)
  have hμS : Continuous (fun X : ConvexBody (En (m + 1)) => μ (smearBody X u)) :=
    hcont.comp hcontS
  -- prove the equality by showing |μ (smearBody B u) - μ B| < ε for all ε > 0
  have hmain : ∀ ε : ℝ, 0 < ε → |μ (smearBody B u) - μ B| < ε := by
    intro ε hε
    have hε2 : 0 < ε / 2 := by positivity
    rcases Metric.continuousAt_iff.mp (hcont.continuousAt (x := B)) (ε / 2) hε2 with ⟨δμ, hδμ0, hδμ⟩
    rcases Metric.continuousAt_iff.mp (hμS.continuousAt (x := B)) (ε / 2) hε2 with ⟨δS, hδS0, hδS⟩
    let δ : ℝ := min δμ δS
    have hδ0 : 0 < δ := lt_min hδμ0 hδS0
    rcases exists_fullDim_polytope_close (m + 1) B (δ := δ) hδ0 with ⟨P, w, hP, hintP, hdist⟩
    have hPBμ : dist P B < δμ := lt_of_lt_of_le hdist (min_le_left δμ δS)
    have hPBS : dist P B < δS := lt_of_lt_of_le hdist (min_le_right δμ δS)
    have hmid : μ (smearBody P u) = μ P := hpoly P w hP hintP
    have h1 : |μ (smearBody B u) - μ (smearBody P u)| < ε / 2 := by
      have ht := hδS hPBS
      -- ht : dist (μ (smearBody P u)) (μ (smearBody B u)) < ε/2
      rw [abs_sub_comm]
      simpa [dist_eq_norm, Real.norm_eq_abs] using ht
    have h2 : |μ (smearBody P u) - μ B| < ε / 2 := by
      rw [hmid]
      have ht := hδμ hPBμ
      simpa [dist_eq_norm, Real.norm_eq_abs] using ht
    have hsplit : |μ (smearBody B u) - μ B| ≤
        |μ (smearBody B u) - μ (smearBody P u)| + |μ (smearBody P u) - μ B| := by
      have hte : (μ (smearBody B u) - μ (smearBody P u)) +
          (μ (smearBody P u) - μ B) = μ (smearBody B u) - μ B := by ring
      rw [← hte]
      exact abs_add_le _ _
    linarith
  -- all ε > 0 ⇒ values equal
  apply sub_eq_zero.mp
  by_contra hz
  have hp : 0 < |μ (smearBody B u) - μ B| := abs_pos.mpr hz
  have hsmall : |μ (smearBody B u) - μ B| < |μ (smearBody B u) - μ B| / 2 :=
    hmain (|μ (smearBody B u) - μ B| / 2) (by positivity)
  linarith


/-- The point `{0}` of `En (m+1)` has empty interior (the space has dimension
`m + 1 ≥ 1`; equivalently: a nonzero normed space has no isolated points). -/
theorem interior_pointBody_empty (m : ℕ) :
    interior (((pointBody (En (m + 1)) : ConvexBody (En (m + 1))) : Set (En (m + 1)))) = ∅ := by
  change interior ({0} : Set (En (m + 1))) = ∅
  exact interior_singleton (0 : En (m + 1))

/-- WIRING: `μ` vanishes on the point `{0}` (simplicity). -/
theorem pointBody_zero (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0) :
    μ (pointBody (En (m + 1))) = 0 := by
  exact hsimple (pointBody (En (m + 1))) (interior_pointBody_empty m)

/-- WIRING: every zonotope (Minkowski sum of the segments `[0,u]`, `u ∈ us`)
vanishes, for the full bundle + cylinder hypothesis.  Instantiation of
`zonotope_zero_of_hseg` via `smear_invariance` and `pointBody_zero`. -/
theorem zonotope_zero (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ us : List (En (m + 1)),
      μ (foldSmear (pointBody (En (m + 1))) us) = 0 := by
  exact zonotope_zero_of_hseg μ (smear_invariance m μ hcont hadd htrans hsimple hcyl)
    (pointBody_zero m μ hsimple)

/-- WIRING: `μ (P + Z) = μ P` for every body `P` and zonotope `Z`. -/
theorem bodyAdd_zonotope_value_eq (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ (P : ConvexBody (En (m + 1))) (us : List (En (m + 1))),
      μ (bodyAdd P (foldSmear (pointBody (En (m + 1))) us)) = μ P := by
  exact bodyAdd_foldSmear_value_eq μ (smear_invariance m μ hcont hadd htrans hsimple hcyl)

/-- A zonoid: a Hausdorff limit of zonotopes (finite Minkowski sums of segments). -/
def IsZonoid (m : ℕ) (Y : ConvexBody (En (m + 1))) : Prop :=
  ∃ Z : ℕ → List (En (m + 1)),
    Tendsto (fun n : ℕ => foldSmear (pointBody (En (m + 1))) (Z n)) atTop (𝓝 Y)

/-- `bodyAdd` agrees with Mathlib's Minkowski addition of bodies. -/
theorem bodyAdd_eq_add (P L : ConvexBody W) : bodyAdd P L = P + L := by
  apply ConvexBody.ext
  rw [bodyAdd_coe, ConvexBody.coe_add]
  ext x
  constructor
  · rintro ⟨p, hp, ℓ, hℓ, hx⟩
    exact ⟨p, hp, ℓ, hℓ, hx.symm⟩
  · rintro ⟨p, hp, ℓ, hℓ, hx⟩
    exact ⟨p, hp, ℓ, hℓ, hx.symm⟩

/-- Zonoids vanish. -/
theorem zonoid_zero (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ Y : ConvexBody (En (m + 1)), IsZonoid m Y → μ Y = 0 := by
  intro Y hY
  rcases hY with ⟨Z, hZ⟩
  have h1 : Tendsto (fun n : ℕ => μ (foldSmear (pointBody (En (m + 1))) (Z n)))
      atTop (𝓝 (μ Y)) :=
    (hcont.continuousAt (x := Y)).tendsto.comp hZ
  have hsame : (fun n : ℕ => μ (foldSmear (pointBody (En (m + 1))) (Z n))) = fun _ : ℕ => 0 := by
    funext n
    exact zonotope_zero m μ hcont hadd htrans hsimple hcyl (Z n)
  rw [hsame] at h1
  exact tendsto_nhds_unique h1 (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Adding a zonoid to a body does not change its value. -/
theorem zonoid_bodyAdd (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ (K Y : ConvexBody (En (m + 1))), IsZonoid m Y → μ (bodyAdd K Y) = μ K := by
  intro K Y hY
  rcases hY with ⟨Z, hZ⟩
  have hgoal : (fun X : ConvexBody (En (m + 1)) => K + X) =
      fun X : ConvexBody (En (m + 1)) => X + K := by
    funext X
    exact add_comm K X
  have hmap : Continuous (fun X : ConvexBody (En (m + 1)) => K + X) := by
    rw [hgoal]
    exact continuous_bodyAdd_left (L := K)
  have hcontKA : Continuous (fun X : ConvexBody (En (m + 1)) => bodyAdd K X) := by
    have hfuneq : (fun X : ConvexBody (En (m + 1)) => bodyAdd K X) =
        fun X : ConvexBody (En (m + 1)) => K + X := by
      funext X
      exact bodyAdd_eq_add K X
    rw [hfuneq]
    exact hmap
  have h2 : Tendsto (fun n : ℕ => μ (bodyAdd K (foldSmear (pointBody (En (m + 1))) (Z n))))
      atTop (𝓝 (μ (bodyAdd K Y))) :=
    (hcont.comp hcontKA).continuousAt (x := Y) |>.tendsto.comp hZ
  have hsame : (fun n : ℕ => μ (bodyAdd K (foldSmear (pointBody (En (m + 1))) (Z n)))) =
      fun _ : ℕ => μ K := by
    funext n
    exact bodyAdd_zonotope_value_eq m μ hcont hadd htrans hsimple hcyl K (Z n)
  rw [hsame] at h2
  exact tendsto_nhds_unique h2 (tendsto_const_nhds : Tendsto (fun _ : ℕ => μ K) atTop (𝓝 (μ K)))

/-! ## Step 5-7 assembly: centredness, parallelotope bodies -/

/-- A set is *centred* (symmetric about some point): `A = v - A`. -/
def CentredSet {S : Type*} [AddCommGroup S] (A : Set S) : Prop :=
  ∃ v : S, A = (fun x : S => -x + v) '' A

/-- The negation `-K` of a convex body. -/
def negBody {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (K : ConvexBody S) : ConvexBody S :=
  ⟨-(K : Set S), Convex.neg K.convex, IsCompact.neg K.isCompact,
    by
      rcases K.nonempty with ⟨x, hx⟩
      refine ⟨-x, ?_⟩
      exact Set.neg_mem_neg.mpr hx⟩

@[simp] theorem negBody_coe {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    (K : ConvexBody S) : (negBody K : Set S) = -(K : Set S) := rfl

/-- The parallelotope `{∑ tᵢ uᵢ | tᵢ ∈ [0,1]}` (Minkowski sum of the segments) in `V`. -/
def parSetV {V : Type*} [AddCommMonoid V] [Module ℝ V] (n : ℕ) (u : Fin n → V) : Set V :=
  {x : V | ∃ t : Fin n → ℝ, (∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1) ∧
    x = ∑ i : Fin n, t i • u i}

theorem parSetV_convex {V : Type*} [AddCommGroup V] [Module ℝ V] (n : ℕ) (u : Fin n → V) :
    Convex ℝ (parSetV n u) := by
  rintro x ⟨t, ht, rfl⟩ y ⟨s, hs, rfl⟩ a b ha hb hab
  refine ⟨fun i => a * t i + b * s i, ?_, ?_⟩
  · intro i
    exact (convex_Icc (0 : ℝ) 1) (ht i) (hs i) ha hb hab
  · calc
      a • (∑ i : Fin n, t i • u i) + b • (∑ i : Fin n, s i • u i)
          = ∑ i : Fin n, (a * t i + b * s i) • u i := by
              rw [Finset.smul_sum, Finset.smul_sum]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [smul_smul, smul_smul]
              rw [add_smul]

theorem parSetV_compact {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (u : Fin n → V) : IsCompact (parSetV n u) := by
  let f : (Fin n → ℝ) → V := fun t => ∑ i : Fin n, t i • u i
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have him : parSetV n u = f '' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, by intro i hi; exact ht i, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, fun i => ht i (Set.mem_univ i), rfl⟩
  rw [him]
  exact IsCompact.image (isCompact_univ_pi (fun i => isCompact_Icc)) hf

theorem parSetV_nonempty {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (n : ℕ) (u : Fin n → V) : (parSetV n u).Nonempty := by
  refine ⟨0, ⟨(fun _ : Fin n => 0), ?_, ?_⟩⟩
  · intro i
    exact left_mem_Icc.mpr zero_le_one
  · simp

/-- The parallelotope spanned by `u : Fin n → V` as a convex body. -/
def parBodyV {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (u : Fin n → V) : ConvexBody V :=
  ⟨parSetV n u, parSetV_convex n u, parSetV_compact n u, parSetV_nonempty n u⟩

@[simp] theorem parBodyV_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (u : Fin n → V) : (parBodyV n u : Set V) = parSetV n u := rfl

/-- The carrier of the iterated segment-sum over the list `u 0, …, u (n-1)` is the
parallelotope `{∑ tᵢ uᵢ | tᵢ ∈ [0,1]}`. -/
theorem foldSmear_ofFn_carrier {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (u : Fin n → V) :
    (foldSmear (pointBody V) (List.ofFn u) : Set V) = parSetV n u := by
  classical
  induction n with
  | zero =>
      ext x
      constructor
      · intro hx
        have hx0 : x = 0 := by simpa using hx
        subst x
        exact ⟨(fun _ : Fin 0 => 0), fun i => False.elim (Fin.elim0 i), by simp⟩
      · rintro ⟨t, ht, hx⟩
        have hx0 : x = 0 := by simpa using hx
        rw [hx0]
        simp
  | succ n ih =>
      let urest : Fin n → V := fun i => u i.succ
      have hfold : foldSmear (pointBody V) (List.ofFn u) =
          smearBody (foldSmear (pointBody V) (List.ofFn urest)) (u 0) := by
        rw [List.ofFn_succ]
        rfl
      rw [hfold]
      ext x
      constructor
      · rintro ⟨p, hp, s, hs, rfl⟩
        rw [ih urest] at hp
        rcases hp with ⟨t, ht, rfl⟩
        refine ⟨Fin.cons s t, ?hcons, ?hsum⟩
        · intro j
          by_cases hj : j = 0
          · subst j
            simp
            exact hs
          · have hpred : (Fin.pred j hj).succ = j :=
              Fin.succ_pred j hj
            rw [← hpred, Fin.cons_succ]
            exact ht (Fin.pred j hj)
        · rw [Fin.sum_univ_succ]
          simp [Fin.cons_zero, Fin.cons_succ]
          abel
      · rintro ⟨t, ht, rfl⟩
        have hmain : (∑ i : Fin (n + 1), t i • u i) =
            t 0 • u 0 + ∑ i : Fin n, t i.succ • u i.succ := by
          rw [Fin.sum_univ_succ]
        refine ⟨∑ i : Fin n, t i.succ • u i.succ, ?hp, t 0, ht 0, ?hx⟩
        · rw [ih urest]
          exact ⟨(fun i : Fin n => t i.succ), (fun i => ht i.succ), rfl⟩
        · rw [hmain]
          abel

theorem parBodyV_eq_foldSmear {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (u : Fin n → V) :
    parBodyV n u = foldSmear (pointBody V) (List.ofFn u) := by
  apply ConvexBody.ext
  rw [foldSmear_ofFn_carrier]
  rfl



/-! ## Bridging to the analytic-core lemma (`centred_zonoidDiff_seq`)

The analytic core is delegated (commons path
`Geometry/Convex/Hadwiger/centred_zonoidDiff_seq`, agent L104) and is stated in
pure Mathlib terms, with "zonoid" spelled out as the Hausdorff limit of
zonotopes whose carriers are `parSetV`-shaped sets.  The following lemma
translates that shape into this module's `IsZonoid m` (Hausdorff limit of
`foldSmear (pointBody (En (m + 1)))` over lists). -/

/-- If `Y` is the Hausdorff limit of bodies `Z n` whose carriers are the
parallelotopes `parSetV (k n) (w n)` (finite Minkowski sums of the segments
`[0, w n i]`), then `Y` is a zonoid in the sense of this module. -/
theorem zonoid_of_parLimit (m : ℕ) {Y : ConvexBody (En (m + 1))}
    {Z : ℕ → ConvexBody (En (m + 1))} {k : ℕ → ℕ} {w : ∀ n : ℕ, Fin (k n) → En (m + 1)}
    (hZ : ∀ n : ℕ, (Z n : Set (En (m + 1))) = parSetV (k n) (w n))
    (hT : Tendsto Z atTop (𝓝 Y)) : IsZonoid m Y := by
  classical
  let Z' : ℕ → List (En (m + 1)) := fun n => List.ofFn (w n)
  refine ⟨Z', ?_⟩
  have hEq : (fun n : ℕ => foldSmear (pointBody (En (m + 1))) (Z' n)) = Z := by
    funext n
    apply ConvexBody.ext
    rw [foldSmear_ofFn_carrier (k n) (w n)]
    exact (Eq.symm (hZ n))
  rw [hEq]
  exact hT

/-! ## three-piece dissection additivity (mechanical) -/

theorem val_eq_sum_three {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    (μ : ConvexBody V → ℝ) (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody V,
        (A : Set V) = (C : Set V) ∪ (D : Set V) →
        (B : Set V) = (C : Set V) ∩ (D : Set V) → μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody V, interior (K : Set V) = ∅ → μ K = 0)
    (P A B C : ConvexBody V)
    (hcover : (P : Set V) = (A : Set V) ∪ (B : Set V) ∪ (C : Set V))
    (hAB : interior ((A : Set V) ∩ (B : Set V)) = ∅)
    (hAC : interior ((A : Set V) ∩ (C : Set V)) = ∅)
    (hBC : interior ((B : Set V) ∩ (C : Set V)) = ∅) :
    μ P = μ A + μ B + μ C := by
  let F : Fin 3 → ConvexBody V := fun i =>
    match i.1 with | 0 => A | 1 => B | _ => C
  have hcovF : (P : Set V) = ⋃ i : Fin 3, (F i : Set V) := by
    rw [hcover]
    ext x
    constructor
    · intro h
      rcases h with hAB | hC
      · rcases hAB with hA | hB
        · rw [Set.mem_iUnion]
          exact ⟨0, by simpa [F] using hA⟩
        · rw [Set.mem_iUnion]
          exact ⟨1, by simpa [F] using hB⟩
      · rw [Set.mem_iUnion]
        exact ⟨2, by simpa [F] using hC⟩
    · intro hx
      rw [Set.mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      rcases i with ⟨n, hn⟩
      interval_cases n
      · left
        left
        simp [F] at hi
        exact hi
      · left
        right
        simp [F] at hi
        exact hi
      · right
        simp [F] at hi
        exact hi
  have hpairF : ∀ i j : Fin 3, i ≠ j → interior ((F i : Set V) ∩ (F j : Set V)) = ∅ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exfalso; exact hij (Fin.ext rfl)
      | simpa [F, inter_comm] using hAB
      | simpa [F, inter_comm] using hAC
      | simpa [F, inter_comm] using hBC
  have hmain := dissection_additivity (ι := Fin 3) μ hcont hadd hsimple (P := P) (A := F) hcovF hpairF
  rw [hmain]
  norm_num [Fin.sum_univ_succ, F]
  ring_nf

/-! ## step 5: simplices vanish (given centred bodies vanish) -/

theorem simplex_zero_of_centred (m : ℕ) (hm : 0 < m)
    (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (heven : ∀ A B : ConvexBody (En (m + 1)),
        (B : Set (En (m + 1))) = -(A : Set (En (m + 1))) → μ A = μ B)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0)
    (hcentred : ∀ C : ConvexBody (En (m + 1)), CentredSet (C : Set (En (m + 1))) → μ C = 0) :
    ∀ (u : Fin (m + 1) → En (m + 1)) (hu : LinearIndependent ℝ u)
      (Δ : ConvexBody (En (m + 1))),
      (Δ : Set (En (m + 1))) = convexHull ℝ (({0} ∪ Set.range u) : Set (En (m + 1))) → μ Δ = 0 := by
  classical
  intro u hu Δ hΔ
  have hn2 : 2 ≤ m + 1 := by omega
  rcases simplex_parallelotope_dissection (m + 1) hn2 u hu with
    ⟨P, Δ0, Q, R, v, hv, hP, hΔ0, hQ, hQR_, hQcent, hcov, hDQ, hQRint, hDR⟩
  have hPz : μ P = 0 := by
    have hPe : P = parBodyV (m + 1) u := by
      apply ConvexBody.ext
      rw [hP]
      rfl
    have hfold : parBodyV (m + 1) u = foldSmear (pointBody (En (m + 1))) (List.ofFn u) :=
      parBodyV_eq_foldSmear (m + 1) u
    have hz : μ (foldSmear (pointBody (En (m + 1))) (List.ofFn u)) = 0 :=
      zonotope_zero m μ hcont hadd htrans hsimple hcyl (List.ofFn u)
    rw [hPe, hfold]
    exact hz
  have hQ0 : μ Q = 0 := hcentred Q ⟨v, hQcent⟩
  have hDe : Δ0 = Δ := by
    apply ConvexBody.ext
    rw [hΔ0, hΔ]
  have hDμ : μ Δ0 = μ Δ := by rw [hDe]
  have hRμ : μ R = μ Δ0 := by
    have hRn : (R : Set (En (m + 1))) =
        (fun x : En (m + 1) => x + v) '' (negBody Δ0 : Set (En (m + 1))) := by
      rw [hQR_]
      ext x
      constructor
      · intro hx
        rw [Set.mem_image] at hx
        rcases hx with ⟨y, hy, hx⟩
        rw [Set.mem_image]
        refine ⟨-y, ⟨?_, ?_⟩⟩
        · rw [negBody_coe]
          rw [Set.mem_neg]
          simpa using hy
        · simp [hx]
      · intro hx
        rw [Set.mem_image] at hx
        rcases hx with ⟨z, hz, hx⟩
        rw [Set.mem_image]
        refine ⟨-z, ⟨?_, ?_⟩⟩
        · rw [negBody_coe] at hz
          exact Set.mem_neg.mp hz
        · simp [hx]
    have hneg : μ Δ0 = μ (negBody Δ0) := by
      exact heven Δ0 (negBody Δ0) (by simp)
    have htransR : μ (negBody Δ0) = μ R := htrans (negBody Δ0) R v hRn
    calc
      μ R = μ (negBody Δ0) := htransR.symm
      _ = μ Δ0 := hneg.symm
  have hcov3 : (P : Set (En (m + 1))) =
      (Δ0 : Set (En (m + 1))) ∪ (Q : Set (En (m + 1))) ∪ (R : Set (En (m + 1))) := by
    exact hcov
  have hsum : μ P = μ Δ0 + μ Q + μ R :=
    val_eq_sum_three μ hcont hadd hsimple P Δ0 Q R hcov3 hDQ hDR hQRint
  have hgoal : μ Δ = 0 := by
    have hlin : μ Δ0 + μ Δ0 = 0 := by
      have h1 : μ Δ0 + μ Q + μ R = 0 := hsum.symm.trans hPz
      rw [hQ0, hRμ] at h1
      simpa using h1
    have hlin' : μ Δ + μ Δ = 0 := by
      simpa [hDμ] using hlin
    linarith
  exact hgoal


/-! ## translate of a simplex convex hull -/

lemma convHull_translate_neg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (w : Fin (n + 1) → V) :
    (fun x : V => x + (-w 0)) '' (convexHull ℝ (Set.range w)) =
      convexHull ℝ (({0} ∪ Set.range (fun k : Fin n => w (Fin.succ k) + (-w 0))) : Set V) := by
  classical
  let f : V →ᵃ[ℝ] V :=
    { toFun := fun x => x + (-w 0)
      linear := LinearMap.id
      map_vadd' := by intro x y; simp [vadd_eq_add]; abel }
  have hf : (fun x : V => x + (-w 0)) = f := by
    funext x
    rfl
  have hset : (fun x : V => x + (-w 0)) '' (Set.range w) =
      ({0} ∪ Set.range (fun k : Fin n => w (Fin.succ k) + (-w 0))) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨j, rfl⟩
      rcases Fin.eq_zero_or_eq_succ j with h0 | ⟨k, hk⟩
      · subst j
        left
        simp
      · subst j
        right
        refine ⟨k, ?_⟩
        simp
    · intro hz
      rcases hz with h0 | ⟨k, rfl⟩
      · refine ⟨w 0, ⟨0, rfl⟩, ?_⟩
        simpa using h0.symm
      · refine ⟨w (Fin.succ k), ⟨Fin.succ k, rfl⟩, ?_⟩
        simp
  calc
    (fun x : V => x + (-w 0)) '' (convexHull ℝ (Set.range w))
        = convexHull ℝ ((fun x : V => x + (-w 0)) '' Set.range w) := by
            rw [hf]
            exact f.image_convexHull (Set.range w)
    _ = convexHull ℝ (({0} ∪ Set.range (fun k : Fin n => w (Fin.succ k) + (-w 0))) : Set V) := by
            rw [hset]

theorem linearIndependent_of_affineIndependent_succ {V : Type*} [AddCommGroup V] [Module ℝ V]
    {n : ℕ} (w : Fin (n + 1) → V) (hw : AffineIndependent ℝ w) :
    LinearIndependent ℝ (fun k : Fin n => w (Fin.succ k) - w 0) := by
  have hvs : LinearIndependent ℝ (fun i : {j : Fin (n + 1) // j ≠ 0} =>
      w (i : Fin (n + 1)) - w 0) := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ w (0 : Fin (n + 1))).mp hw
    simpa [vsub_eq_sub] using h
  let e : Fin n → {j : Fin (n + 1) // j ≠ 0} := fun k => ⟨Fin.succ k, by simp⟩
  have heinj : Function.Injective e := by
    intro k k' h
    apply Fin.succ_injective n
    exact congrArg (fun s : {j : Fin (n + 1) // j ≠ 0} => (s : Fin (n + 1))) h
  have h1 := LinearIndependent.comp hvs e heinj
  exact h1

/-! ## step 6: polytopes vanish (given centred bodies vanish + triangulation) -/

theorem polytope_zero_of_centred (m : ℕ) (hm : 0 < m)
    (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (heven : ∀ A B : ConvexBody (En (m + 1)),
        (B : Set (En (m + 1))) = -(A : Set (En (m + 1))) → μ A = μ B)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0)
    (hcentred : ∀ C : ConvexBody (En (m + 1)), CentredSet (C : Set (En (m + 1))) → μ C = 0) :
    ∀ (P : ConvexBody (En (m + 1))) (S : Finset (En (m + 1))),
      (P : Set (En (m + 1))) = convexHull ℝ (S : Set (En (m + 1))) → μ P = 0 := by
  classical
  intro P S hP
  by_cases hfull : (interior (P : Set (En (m + 1)))).Nonempty
  · have hfullS : (interior (convexHull ℝ (S : Set (En (m + 1))))).Nonempty := by
      rw [← hP]
      exact hfull
    rcases polytope_triangulation (m + 1) S hfullS with ⟨ι, hι, A, w, hcov, hcar, hind, hpair⟩
    have hAi0 : ∀ i : ι, μ (A i) = 0 := by
      intro i
      let a0 : En (m + 1) := w i 0
      let u : Fin (m + 1) → En (m + 1) := fun k => w i (Fin.succ k) + (-a0)
      let B : ConvexBody (En (m + 1)) := transBody (-a0) (A i)
      have hBcar : (B : Set (En (m + 1))) =
          convexHull ℝ (({0} ∪ Set.range u) : Set (En (m + 1))) := by
        have hB : (B : Set (En (m + 1))) =
            (fun x : En (m + 1) => x + (-a0)) '' (A i : Set (En (m + 1))) := by
          dsimp [B]
          rfl
        rw [hB]
        rw [hcar i]
        have hconv := convHull_translate_neg (m + 1) (w i)
        dsimp [u, a0] at hconv ⊢
        exact hconv
      have hLI : LinearIndependent ℝ u := by
        have hLI0 := linearIndependent_of_affineIndependent_succ (w i) (hind i)
        -- hLI0 : LI (fun k => w i (Fin.succ k) - w i 0): transfer to u (uses + (-a0))
        have hEq : (fun k : Fin (m + 1) => w i (Fin.succ k) - w i 0) = u := by
          funext k
          dsimp [u, a0]
          rw [sub_eq_add_neg]
        rw [← hEq]
        exact hLI0
      have hB0 : μ B = 0 :=
        simplex_zero_of_centred m hm μ hcont hadd htrans hsimple heven hcyl hcentred u hLI B hBcar
      have hAeq : μ (A i) = μ B := by
        have hB : (B : Set (En (m + 1))) =
            (fun x : En (m + 1) => x + (-a0)) '' (A i : Set (En (m + 1))) := by
          dsimp [B]
          rfl
        have htr : (A i : Set (En (m + 1))) =
            (fun x : En (m + 1) => x + a0) '' (B : Set (En (m + 1))) := by
          rw [hB]
          ext x
          constructor
          · intro hx
            rw [Set.mem_image]
            refine ⟨x + (-a0), ⟨?_, ?_⟩⟩
            · rw [Set.mem_image]
              refine ⟨x, ⟨hx, rfl⟩⟩
            · abel
          · intro hx
            rw [Set.mem_image] at hx
            rcases hx with ⟨y, hy, hx⟩
            rw [Set.mem_image] at hy
            rcases hy with ⟨z, hz, hy'⟩
            have hxz : x = z := by
              calc
                x = y + a0 := hx.symm
                _ = (z + (-a0)) + a0 := by rw [hy']
                _ = z := by abel
            simpa [hxz] using hz
        exact (htrans B (A i) a0 htr).symm
      rw [hAeq]
      exact hB0
    have hcov' : (P : Set (En (m + 1))) = ⋃ i : ι, (A i : Set (En (m + 1))) := by
      rw [hP]
      exact hcov.symm
    have hsum := dissection_additivity (ι := ι) μ hcont hadd hsimple (P := P) (A := A) hcov' hpair
    rw [hsum]
    simp [hAi0]
  · have hint : interior (P : Set (En (m + 1))) = ∅ := (Set.not_nonempty_iff_eq_empty).mp hfull
    exact hsimple P hint


/-! ## step 7: every body vanishes (given centred bodies vanish) -/

theorem body_zero_of_centred (m : ℕ) (hm : 0 < m)
    (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (heven : ∀ A B : ConvexBody (En (m + 1)),
        (B : Set (En (m + 1))) = -(A : Set (En (m + 1))) → μ A = μ B)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0)
    (hcentred : ∀ C : ConvexBody (En (m + 1)), CentredSet (C : Set (En (m + 1))) → μ C = 0) :
    ∀ K : ConvexBody (En (m + 1)), μ K = 0 := by
  classical
  intro K
  let P : ℕ → ConvexBody (En (m + 1)) := fun j => Classical.choose
      (exists_fullDim_polytope_close (m + 1) K (δ := ((1 : ℝ) / (j + 1))) (by positivity))
  have hPj : ∀ j : ℕ,
      ∃ u : Finset (En (m + 1)),
        (P j : Set (En (m + 1))) = convexHull ℝ (u : Set (En (m + 1))) ∧
        (interior (P j : Set (En (m + 1)))).Nonempty ∧ dist (P j) K < (1 : ℝ) / (j + 1) := by
    intro j
    exact Classical.choose_spec (exists_fullDim_polytope_close (m + 1) K (δ := ((1 : ℝ) / (j + 1))) (by positivity))
  have hdist0 : Tendsto (fun j : ℕ => dist (P j) K) atTop (𝓝 0) := by
    have hg0 : Tendsto (fun j : ℕ => (1 : ℝ) / (j + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact squeeze_zero (f := fun j : ℕ => dist (P j) K) (g := fun j : ℕ => (1 : ℝ) / (j + 1))
      (fun j => dist_nonneg) (fun j => by
        rcases hPj j with ⟨u, hcar, hint, hd⟩
        exact le_of_lt hd) hg0
  have hPcon : Tendsto (fun j : ℕ => P j) atTop (𝓝 K) :=
    (tendsto_iff_dist_tendsto_zero).mpr hdist0
  have hμ : Tendsto (fun j : ℕ => μ (P j)) atTop (𝓝 (μ K)) :=
    (hcont.continuousAt (x := K)).tendsto.comp hPcon
  have hzero : (fun j : ℕ => μ (P j)) = fun _ : ℕ => 0 := by
    funext j
    rcases hPj j with ⟨u, hcar, hint, hd⟩
    exact polytope_zero_of_centred m hm μ hcont hadd htrans hsimple heven hcyl hcentred (P j) u hcar
  rw [hzero] at hμ
  exact tendsto_nhds_unique hμ (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-! ## base case m = 0: dimension one -/

lemma e0_val_zero0 (y : En 1) :
    (EuclideanSpace.equiv (Fin 0) ℝ).symm (fun i : Fin 0 => y (Fin.castSucc i)) = (0 : En 0) := by
  apply PiLp.ext
  intro i
  exact Fin.elim0 i

lemma mem_pointBody0 (K : ConvexBody (En 0)) (y : En 1) :
    (EuclideanSpace.equiv (Fin 0) ℝ).symm (fun i : Fin 0 => y (Fin.castSucc i)) ∈ (K : Set (En 0)) := by
  rw [e0_val_zero0 y]
  rcases K.nonempty with ⟨z, hz⟩
  have hz0 : z = (0 : En 0) := by
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  simpa [hz0] using hz

lemma cubeSet1_eq :
    {y : En 1 | y 0 ∈ Set.Icc (0 : ℝ) 1} =
      (EuclideanSpace.equiv (Fin 1) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (0 : ℝ) 1)) := by
  ext y
  constructor
  · intro hy
    refine ⟨(fun _ : Fin 1 => y 0), ?_, ?_⟩
    · intro i hi
      exact hy
    · ext i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst i
      simp
  · rintro ⟨f, hf, rfl⟩
    exact hf 0 (Set.mem_univ 0)

lemma cylHypSet0_point :
    cylHypSet 0 (LinearIsometryEquiv.refl ℝ (En 1)) (pointBody (En 0)) 1 =
      {y : En 1 | y 0 ∈ Set.Icc (0 : ℝ) 1} := by
  ext y
  constructor
  · intro hy
    unfold cylHypSet at hy
    rcases hy with ⟨h1, h2⟩
    have hid : ((LinearIsometryEquiv.refl ℝ (En 1)).symm y) = y := rfl
    simpa [hid] using h2
  · intro hy
    unfold cylHypSet
    constructor
    · exact mem_pointBody0 (pointBody (En 0)) y
    · have hid : ((LinearIsometryEquiv.refl ℝ (En 1)).symm y) = y := rfl
      simpa [hid] using hy

/-! ## the analytic core: centred bodies vanish (imported from the commons)

The only non-elementary input of the whole proof — Klain's Prop. 3.1
(Mathematika 42 (1995), p. 333) together with the classical density of smooth
centred bodies among all centred bodies (the cosine transform / Funk–Hecke
theory on the sphere) — is now a shared commons lemma:

`Commons.Geometry.Convex.Hadwiger.centred_zonoidDiff_seq` (agent L104, built on
its support-function and cosine-transform subtree under
`Geometry/Convex/Hadwiger/`).  In body-language: every centred convex body is
a Hausdorff limit of bodies each of which is a difference of two zonoids
(`∃ Kⱼ → K`, and for each `j` zonoids `Y₁,Y₂` with `Kⱼ + Y₂ = Y₁`).
`centred_zonoidDiff_seq_scaffold` below instantiates it at `V = En (m+1)` and
bridges its Mathlib-only zonoid spelling into this module's `IsZonoid m` via
`zonoid_of_parLimit`; the remaining steps (`centred_zero_of_zonoidSeq`,
`centred_zero`) are pure continuity once the two zonoid facts
(`zonoid_zero`, `zonoid_bodyAdd`) are in hand. -/

/-- **Analytic core (instantiation).**  Every centred body is the Hausdorff
limit of centred bodies each of which is a difference of two zonoids:
`∃ Kⱼ → K` with, for every `j`, zonoids `Y₁,Y₂` and `Kⱼ + Y₂ = Y₁`.  This is
the instantiation of the shared commons lemma
`Commons.Geometry.Convex.Hadwiger.centred_zonoidDiff_seq` at `V = En (m+1)`,
bridging its Mathlib-only zonoid spelling into this module's `IsZonoid m` via
`zonoid_of_parLimit` (carriers match by unfolding `parSetV`). -/
theorem centred_zonoidDiff_seq_scaffold (m : ℕ) (K : ConvexBody (En (m + 1)))
    (hK : CentredSet (K : Set (En (m + 1)))) :
    ∃ Kj : ℕ → ConvexBody (En (m + 1)),
      Tendsto Kj atTop (𝓝 K) ∧
      ∀ j : ℕ, ∃ Y₁ Y₂ : ConvexBody (En (m + 1)),
        IsZonoid m Y₁ ∧ IsZonoid m Y₂ ∧ Kj j + Y₂ = Y₁ := by
  classical
  rcases centred_zonoidDiff_seq (En (m + 1)) K hK with ⟨Kj, hconv, hpieces⟩
  refine ⟨Kj, hconv, ?_⟩
  intro j
  rcases hpieces j with ⟨Y₁, Y₂, Z₁, Z₂, k₁, k₂, w₁, w₂, hT1, hT2, hc1, hc2, heq⟩
  refine ⟨Y₁, Y₂, ?_, ?_, heq⟩
  · exact zonoid_of_parLimit m (fun n => by simpa [parSetV] using hc1 n) hT1
  · exact zonoid_of_parLimit m (fun n => by simpa [parSetV] using hc2 n) hT2

/-- Closing argument: with the analytic core available, every centred body
vanishes.  Uses only continuity of `μ` and the two zonoid facts
(`μ Y = 0` for zonoids, `μ (K+Y) = μ K` for zonoids `Y`); no uniformity
issue arises because the approximating bodies `Kⱼ` themselves converge to
`K`. -/
theorem centred_zero_of_zonoidSeq (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (heven : ∀ A B : ConvexBody (En (m + 1)),
        (B : Set (En (m + 1))) = -(A : Set (En (m + 1))) → μ A = μ B)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0)
    (hseq : ∀ K : ConvexBody (En (m + 1)), CentredSet (K : Set (En (m + 1))) →
      ∃ Kj : ℕ → ConvexBody (En (m + 1)),
        Tendsto Kj atTop (𝓝 K) ∧
        ∀ j : ℕ, ∃ Y₁ Y₂ : ConvexBody (En (m + 1)),
          IsZonoid m Y₁ ∧ IsZonoid m Y₂ ∧ Kj j + Y₂ = Y₁) :
    ∀ K : ConvexBody (En (m + 1)), CentredSet (K : Set (En (m + 1))) → μ K = 0 := by
  classical
  intro K hK
  rcases hseq K hK with ⟨Kj, hconv, hpieces⟩
  have hμ0 : (fun j : ℕ => μ (Kj j)) = fun _ : ℕ => 0 := by
    funext j
    rcases hpieces j with ⟨Y₁, Y₂, hz1, hz2, heq⟩
    have hzY1 : μ Y₁ = 0 := zonoid_zero m μ hcont hadd htrans hsimple hcyl Y₁ hz1
    have hval : μ (Kj j + Y₂) = μ (Kj j) := by
      have hb := zonoid_bodyAdd m μ hcont hadd htrans hsimple hcyl (Kj j) Y₂ hz2
      -- hb : μ (bodyAdd (Kj j) Y₂) = μ (Kj j)
      rw [bodyAdd_eq_add (Kj j) Y₂] at hb
      exact hb
    have hEqVal : μ (Kj j) = μ Y₁ := by
      calc
        μ (Kj j) = μ (Kj j + Y₂) := hval.symm
        _ = μ Y₁ := by rw [heq]
    rw [hEqVal, hzY1]
  have hconvμ : Tendsto (fun j : ℕ => μ (Kj j)) atTop (𝓝 (μ K)) :=
    (hcont.continuousAt (x := K)).tendsto.comp hconv
  rw [hμ0] at hconvμ
  exact tendsto_nhds_unique hconvμ
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Centred bodies vanish (Klain Prop. 3.1 + smooth-centre density, wired
through `centred_zonoidDiff_seq`). -/
theorem centred_zero (m : ℕ) (μ : ConvexBody (En (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (En (m + 1)),
        (A : Set (En (m + 1))) = (C : Set (En (m + 1))) ∪ (D : Set (En (m + 1))) →
        (B : Set (En (m + 1))) = (C : Set (En (m + 1))) ∩ (D : Set (En (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (En (m + 1)), ∀ t : En (m + 1),
        (B : Set (En (m + 1))) = (fun x : En (m + 1) => x + t) '' (A : Set (En (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (En (m + 1)), interior (K : Set (En (m + 1))) = ∅ → μ K = 0)
    (heven : ∀ A B : ConvexBody (En (m + 1)),
        (B : Set (En (m + 1))) = -(A : Set (En (m + 1))) → μ A = μ B)
    (hcyl : ∀ (ρ : En (m + 1) ≃ₗᵢ[ℝ] En (m + 1)) (K : ConvexBody (En m)) (h : ℝ), 0 ≤ h →
      ∀ Q : ConvexBody (En (m + 1)), (Q : Set (En (m + 1))) = cylHypSet m ρ K h → μ Q = 0) :
    ∀ K : ConvexBody (En (m + 1)), CentredSet (K : Set (En (m + 1))) → μ K = 0 := by
  exact centred_zero_of_zonoidSeq m μ hcont hadd htrans hsimple heven hcyl
    (fun K hK => centred_zonoidDiff_seq_scaffold m K hK)




/-! ## the target theorem (test copy, name differs from the imported module's) -/

theorem klain333_from_cylinders (m : ℕ) :
    ∀ (μ : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))) → ℝ),
      Continuous μ →
      (∀ A B C D : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
          (A : Set (EuclideanSpace ℝ (Fin (m + 1)))) = (C : Set (EuclideanSpace ℝ (Fin (m + 1)))) ∪ (D : Set (EuclideanSpace ℝ (Fin (m + 1)))) →
          (B : Set (EuclideanSpace ℝ (Fin (m + 1)))) = (C : Set (EuclideanSpace ℝ (Fin (m + 1)))) ∩ (D : Set (EuclideanSpace ℝ (Fin (m + 1)))) →
          μ A + μ B = μ C + μ D) →
      (∀ A B : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))), ∀ t : EuclideanSpace ℝ (Fin (m + 1)),
          (B : Set (EuclideanSpace ℝ (Fin (m + 1)))) = (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x + t) '' (A : Set (EuclideanSpace ℝ (Fin (m + 1)))) → μ A = μ B) →
      (∀ K : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))), interior (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) = ∅ → μ K = 0) →
      (∀ A B : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))), (B : Set (EuclideanSpace ℝ (Fin (m + 1)))) = -(A : Set (EuclideanSpace ℝ (Fin (m + 1)))) → μ A = μ B) →
      (∀ ρ : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
        ∀ K : ConvexBody (EuclideanSpace ℝ (Fin m)),
        ∀ h : ℝ, 0 ≤ h →
        ∀ Q : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
          (Q : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
            {y : EuclideanSpace ℝ (Fin (m + 1)) |
              (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => (ρ.symm y) (Fin.castSucc i)) ∈
                (K : Set (EuclideanSpace ℝ (Fin m))) ∧
              (ρ.symm y) (Fin.last m) ∈ Set.Icc (0 : ℝ) h} →
          μ Q = 0) →
      ∀ K : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))), μ K = 0 := by
  classical
  intro μ hcont hadd htrans hsimple heven hcyl K
  by_cases hm0 : m = 0
  · subst m
    have hcube0 : ∀ Q : ConvexBody (En 1),
        (Q : Set (En 1)) = (EuclideanSpace.equiv (Fin 1) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin 1 => Set.Icc (0 : ℝ) 1)) →
        μ Q = 0 := by
      intro Q hQ
      have hcar : (Q : Set (En 1)) =
          cylHypSet 0 (LinearIsometryEquiv.refl ℝ (En 1)) (pointBody (En 0)) 1 := by
        rw [hQ]
        rw [← cubeSet1_eq]
        exact cylHypSet0_point.symm
      exact hcyl (LinearIsometryEquiv.refl ℝ (En 1)) (pointBody (En 0)) 1 zero_le_one Q hcar
    have hfin : ∀ K : ConvexBody (En 1), μ K = 0 :=
      klain333_fin1 μ hcont hadd htrans hsimple heven hcube0
    exact hfin K
  · have hm : 0 < m := Nat.pos_of_ne_zero hm0
    exact body_zero_of_centred m hm μ hcont hadd htrans hsimple heven hcyl
      (centred_zero m μ hcont hadd htrans hsimple heven hcyl) K


end
end Commons.Geometry.Convex.Hadwiger
