import Mathlib
import Submission.Work.Noncompact.CompressionTube.Defs
import Submission.Work.Noncompact.CompressionTube.exists_smooth_squash
import Submission.Work.Noncompact.CompressionTube.injective_fderiv_shear
import Submission.Work.Noncompact.CompressionTube.isOpenMap_shear
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion

/-!
# The compression of the domain from the tube datum: the sheared self-map

This file sets up the construction of
`Work.Noncompact.CompressionTube.fromTube`: from the tube datum
`T : Work.Noncompact.CompressionTube n M B` (a locally finite family of pairwise disjoint tubes
to infinity, one through each point of `B`) we build a self-map `tubePhi T : M → M` which is the
identity outside the tubes and which, inside the tube `i`, is the conjugate
`tube i ∘ F ∘ (tube i)⁻¹` of the *shear*

`F (u, s) = (u, (1 - χ u) * s + χ u * g s)`

of the parameter space.  Here

* `tubeChi` is a smooth cut-off which is `1` on `‖u‖ ≤ 1/2` and `0` for `‖u‖ ≥ 1`, so that `F` is
  the identity on the "collar" `‖u‖ ≥ 1` of the tube — this is what makes the gluing (and hence
  the smoothness of `tubePhi`) true, using that the frontier of a tube is only approached with
  `‖u‖ > 1` (a consequence of `escapes` and `T2Space M`);
* `tubeG = sigmoid - 1/2` is smooth, strictly increasing, with image in `(-1/2, 1/2)`: it pushes
  the core `u = 0` of the tube into the region `|s| < 1/2`, so that the points of `B` (which lie
  on the cores at height `|s| ≥ 1`) are missing from the closure of the image of `tubePhi`.

The main structural statement proved here is `tubePhi_apply_tube`: for every tube index `i` and
every parameter `p`, `tubePhi T (T.tube i p) = T.tube i (tubeF n p)`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

noncomputable section

variable {n : ℕ}

/-! ### The transverse cut-off `χ` -/

/-- The bump function underlying the transverse cut-off: a smooth bump centred at `0` with
`rIn = 1/2` and `rOut = 1`. -/
def tubeChiBump (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin (n - 1))) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The transverse cut-off of the compression: a smooth function which is `1` on the closed ball
`‖u‖ ≤ 1/2` and `0` for `‖u‖ ≥ 1`, with values in `[0,1]`. -/
def tubeChi (n : ℕ) : EuclideanSpace ℝ (Fin (n - 1)) → ℝ := tubeChiBump n

lemma tubeChi_contDiff (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeChi n) :=
  ContDiffBump.contDiff (tubeChiBump n)

lemma tubeChi_nonneg (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) : 0 ≤ tubeChi n u :=
  ContDiffBump.nonneg (tubeChiBump n)

lemma tubeChi_le_one (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) : tubeChi n u ≤ 1 :=
  ContDiffBump.le_one (tubeChiBump n)

lemma tubeChi_eq_one (n : ℕ) {u : EuclideanSpace ℝ (Fin (n - 1))} (h : ‖u‖ ≤ 1 / 2) :
    tubeChi n u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall (f := tubeChiBump n)
  simpa [tubeChiBump, Metric.mem_closedBall, dist_eq_norm] using h

lemma tubeChi_eq_zero (n : ℕ) {u : EuclideanSpace ℝ (Fin (n - 1))} (h : 1 ≤ ‖u‖) :
    tubeChi n u = 0 := by
  apply ContDiffBump.zero_of_le_dist (f := tubeChiBump n)
  simpa [tubeChiBump, dist_eq_norm] using h

/-! ### The longitudinal squash `g` -/

/-- The longitudinal squash of the compression: smooth, strictly increasing, with image in
`(-1/2, 1/2)`. -/
def tubeG : ℝ → ℝ := fun s => Real.sigmoid s - 1 / 2

lemma tubeG_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) tubeG := by
  have h : ContDiff ℝ (⊤ : WithTop ℕ∞) (fun s : ℝ => Real.sigmoid s - 1 / 2) :=
    ContDiff.sub contDiff_sigmoid contDiff_const
  exact h.of_le le_top

lemma tubeG_strictMono : StrictMono tubeG := fun a b hab => by
  have h := Real.sigmoid_strictMono hab
  simp only [tubeG]
  linarith

lemma tubeG_deriv_pos (s : ℝ) : 0 < deriv tubeG s := by
  have hfun : tubeG = fun s : ℝ => Real.sigmoid s - 1 / 2 := rfl
  rw [hfun, deriv_sub_const, Real.deriv_sigmoid]
  have h1 := Real.sigmoid_pos s
  have h2 := Real.sigmoid_lt_one s
  nlinarith

lemma tubeG_abs_lt (s : ℝ) : |tubeG s| < 1 / 2 := by
  have h1 := Real.sigmoid_pos s
  have h2 := Real.sigmoid_lt_one s
  have hs : tubeG s = Real.sigmoid s - 1 / 2 := rfl
  rw [hs, abs_lt]
  constructor <;> linarith

/-! ### The shear `F` -/

/-- **The shear** `F (u,s) = (u, (1 - χ u) * s + χ u * g s)` of the parameter space of a tube.
It preserves the transverse coordinate, is the identity for `‖u‖ ≥ 1`, and on `‖u‖ ≤ 1/2` it is
`(u, s) ↦ (u, g s)`. -/
def tubeF (n : ℕ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
  (p.1, (1 - tubeChi n p.1) * p.2 + tubeChi n p.1 * tubeG p.2)

lemma tubeF_fst (n : ℕ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) : (tubeF n p).1 = p.1 := rfl

lemma tubeF_eq_self (n : ℕ) {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ} (h : 1 ≤ ‖p.1‖) :
    tubeF n p = p := by
  have hχ : tubeChi n p.1 = 0 := tubeChi_eq_zero n h
  simp [tubeF, hχ]

lemma tubeF_eq_small (n : ℕ) {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ} (h : ‖p.1‖ ≤ 1 / 2) :
    tubeF n p = (p.1, tubeG p.2) := by
  have hχ : tubeChi n p.1 = 1 := tubeChi_eq_one n h
  simp [tubeF, hχ]

lemma tubeF_snd_abs_lt_of_small (n : ℕ) {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ}
    (h : ‖p.1‖ ≤ 1 / 2) : |(tubeF n p).2| < 1 / 2 := by
  rw [tubeF_eq_small n h]
  exact tubeG_abs_lt _

/-- The "fiber" of the shear, `s ↦ (1 - χ u) * s + χ u * g s`, is strictly monotone. -/
lemma tubeF_fiber_strictMono (n : ℕ) (u : EuclideanSpace ℝ (Fin (n - 1))) :
    StrictMono fun s : ℝ => (1 - tubeChi n u) * s + tubeChi n u * tubeG s := by
  intro a b hab
  rcases lt_or_eq_of_le (tubeChi_le_one n u) with h1 | h1
  · have hlt : 0 < 1 - tubeChi n u := by linarith
    have h2 : tubeChi n u * tubeG a ≤ tubeChi n u * tubeG b :=
      mul_le_mul_of_nonneg_left (le_of_lt (tubeG_strictMono hab)) (tubeChi_nonneg n u)
    have h3 := mul_lt_mul_of_pos_left hab hlt
    linarith
  · rw [h1]
    simp only [sub_self, zero_mul, one_mul, zero_add]
    exact tubeG_strictMono hab

lemma tubeF_injective (n : ℕ) : Function.Injective (tubeF n) := by
  intro p q hpq
  have h1 : p.1 = q.1 := by
    have := congrArg Prod.fst hpq
    simpa [tubeF_fst] using this
  have h2 : p.2 = q.2 := by
    have h := congrArg Prod.snd hpq
    simp only [tubeF] at h
    rw [h1] at h
    exact (tubeF_fiber_strictMono n q.1).injective h
  exact Prod.ext h1 h2

/-- Smoothness of the shear, in the self-model form of the parameter space. -/
lemma tubeF_contMDiff_self (n : ℕ) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeF n) := by
  rw [contMDiff_iff_contDiff]
  apply ContDiff.prodMk
  · exact contDiff_fst
  · apply ContDiff.add
    · exact (contDiff_const.sub ((tubeChi_contDiff n).comp contDiff_fst)).mul contDiff_snd
    · exact ((tubeChi_contDiff n).comp contDiff_fst).mul (tubeG_contDiff.comp contDiff_snd)

lemma tubeF_contMDiff (n : ℕ) :
    ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeF n) := by
  have h1 : (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
      (modelWithCornersSelf ℝ ℝ) = 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    rw [modelWithCornersSelf_prod]
  rw [h1]
  rw [show prodChartedSpace (EuclideanSpace ℝ (Fin (n - 1)))
        (EuclideanSpace ℝ (Fin (n - 1))) ℝ ℝ =
      chartedSpaceSelf (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) from chartedSpaceSelf_prod]
  exact tubeF_contMDiff_self n

lemma tubeF_mfderiv_injective (n : ℕ) (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    Function.Injective (mfderiv ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      (tubeF n) p) := by
  have h1 : (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
      (modelWithCornersSelf ℝ ℝ) = 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    rw [modelWithCornersSelf_prod]
  rw [h1]
  rw [show prodChartedSpace (EuclideanSpace ℝ (Fin (n - 1)))
        (EuclideanSpace ℝ (Fin (n - 1))) ℝ ℝ =
      chartedSpaceSelf (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) from chartedSpaceSelf_prod]
  rw [mfderiv_eq_fderiv]
  exact injective_fderiv_shear (tubeChi n) tubeG (tubeChi_contDiff n) tubeG_contDiff
    (tubeChi_nonneg n) (tubeChi_le_one n) tubeG_deriv_pos p

lemma tubeF_isLocalDiffeomorph (n : ℕ) :
    IsLocalDiffeomorph ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (tubeF n) := by
  have h1 : (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
      (modelWithCornersSelf ℝ ℝ) = 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
    rw [modelWithCornersSelf_prod]
  rw [h1]
  rw [show prodChartedSpace (EuclideanSpace ℝ (Fin (n - 1)))
        (EuclideanSpace ℝ (Fin (n - 1))) ℝ ℝ =
      chartedSpaceSelf (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) from chartedSpaceSelf_prod]
  refine isLocalDiffeomorph_of_mfderiv_injective rfl ?_ ?_
  · exact tubeF_contMDiff_self n
  · intro p
    rw [mfderiv_eq_fderiv]
    exact injective_fderiv_shear (tubeChi n) tubeG (tubeChi_contDiff n) tubeG_contDiff
      (tubeChi_nonneg n) (tubeChi_le_one n) tubeG_deriv_pos p

/-! ### The compression `tubePhi` -/

/-- The "thin part" of the tube `i`: the part of its image where the shear need not be the
identity. -/
def tubeThin {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : CompressionTube n M B) (i : T.ι) : Set M :=
  T.tube i '' {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ ≤ 1}

/-- **The compression map.**  It is `tube i ∘ F ∘ (tube i)⁻¹` on the image of the tube `i` and the
identity outside the union of the tubes.  (The tubes are pairwise disjoint, so this is
well defined.) -/
def tubePhi {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : CompressionTube n M B) (x : M) : M := by
  classical
  exact if h : ∃ i : T.ι, x ∈ Set.range (T.tube i) then
    T.tube (Classical.choose h) (tubeF n (Classical.choose (Classical.choose_spec h)))
  else x

/-- Well-definedness of `tubePhi`: two parametrisations of the same point of a tube give the
same image. -/
lemma tubeF_eq_of_tube_eq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : CompressionTube n M B) {i j : T.ι}
    {p q : EuclideanSpace ℝ (Fin (n - 1)) × ℝ} (h : T.tube i p = T.tube j q) :
    T.tube i (tubeF n p) = T.tube j (tubeF n q) := by
  rcases eq_or_ne i j with hij | hij
  · subst hij
    rw [(T.isEmbedding_tube i).injective h]
  · exact ((Set.disjoint_left.mp (T.disjoint i j hij)) ⟨p, rfl⟩ ⟨q, h.symm⟩).elim

/-- **The key structural property of the compression**: on the tube `i` it is the conjugate of the
shear `F` by the tube. -/
theorem tubePhi_apply_tube {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : CompressionTube n M B) (i : T.ι)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    tubePhi T (T.tube i p) = T.tube i (tubeF n p) := by
  classical
  have h : ∃ j : T.ι, T.tube i p ∈ Set.range (T.tube j) := ⟨i, p, rfl⟩
  rw [tubePhi, dif_pos h]
  exact tubeF_eq_of_tube_eq T (Classical.choose_spec (Classical.choose_spec h))

/-- Outside the union of the tubes, the compression is the identity. -/
lemma tubePhi_eq_self_of_notMem_range {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : CompressionTube n M B) {x : M}
    (h : ∀ i : T.ι, x ∉ Set.range (T.tube i)) : tubePhi T x = x := by
  classical
  rw [tubePhi, dif_neg (not_exists.mpr h)]


/-! ### The local form of the compression, and its behaviour off the thin parts -/

/-- Every tube of the datum is a local diffeomorphism (it is a smooth equidimensional
immersion). -/
theorem tube_isLocalDiffeomorph {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : CompressionTube n M B) (hn : 1 ≤ n) (i : T.ι) :
    IsLocalDiffeomorph ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
        (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) (T.tube i) :=
  isLocalDiffeomorph_of_immersion hn (T.contMDiff_tube i) (T.immersion_tube i)

/-- **The local form of the compression.**  Near a point `tube i p` of a tube, the compression is
the conjugate `tube i ∘ F ∘ Ψ` of the shear `F` by the tube: there is a local inverse `Ψ` of the
tube `i` at `p`, defined and smooth on an open set `Ψ.source` containing `tube i p`, and on that
open set `tubePhi T y = tube i (tubeF n (Ψ y))` for every `y`. -/
theorem tubePhi_exists_localInverse {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : CompressionTube n M B) (hn : 1 ≤ n) (i : T.ι)
    (p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ) :
    ∃ Ψ : PartialDiffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n - 1)))).prod
          (modelWithCornersSelf ℝ ℝ)) M (EuclideanSpace ℝ (Fin (n - 1)) × ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞),
      T.tube i p ∈ Ψ.source ∧
      ∀ y ∈ Ψ.source, tubePhi T y = T.tube i (tubeF n (Ψ y)) := by
  have h1 := tube_isLocalDiffeomorph T hn i p
  refine ⟨h1.localInverse, h1.localInverse_mem_source, ?_⟩
  intro y hy
  have hy' : T.tube i (h1.localInverse y) = y := h1.localInverse_right_inv hy
  have h1' : tubePhi T (T.tube i (h1.localInverse y)) = T.tube i (tubeF n (h1.localInverse y)) :=
    tubePhi_apply_tube T i (h1.localInverse y)
  rwa [hy'] at h1'

/-- The thin part of a single tube is closed.  This uses `escapes` (the tube is proper on the thin
part) and `T2Space M`. -/
theorem isClosed_tubeThin {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] {B : Set M} (T : CompressionTube n M B) (i : T.ι) :
    IsClosed (tubeThin T i) := by
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  -- a compact neighbourhood `K` of `x`, and a height bound `S` for the tube over `K`
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨S, hS⟩ := T.escapes i K hKc
  -- the compact piece of the thin part above `K`
  set L : Set (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := {p | ‖p.1‖ ≤ 1 ∧ |p.2| ≤ S} with hL
  have hLc : IsCompact L := by
    have hEq : L = Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n - 1))) 1 ×ˢ Set.Icc (-S) S := by
      rw [hL]
      ext p
      simp [Metric.mem_closedBall, dist_eq_norm, abs_le]
    rw [hEq]
    exact (isCompact_closedBall _ _).prod isCompact_Icc
  have hclosed : IsClosed (T.tube i '' L) :=
    (hLc.image (T.contMDiff_tube i).continuous).isClosed
  have hLthin : T.tube i '' L ⊆ tubeThin T i := Set.image_mono (fun p hp => hp.1)
  have hsub : tubeThin T i ∩ K ⊆ T.tube i '' L ∩ K := by
    rintro z ⟨⟨p, hp, rfl⟩, hzK⟩
    have hp2 : |p.2| ≤ S := by
      by_contra hcon
      exact hS p hp (le_of_lt (not_le.mp hcon)) hzK
    exact ⟨⟨p, ⟨hp, hp2⟩, rfl⟩, hzK⟩
  have heq : tubeThin T i ∩ K = T.tube i '' L ∩ K :=
    Set.Subset.antisymm hsub (fun z hz => ⟨hLthin hz.1, hz.2⟩)
  have hnotmem : x ∉ T.tube i '' L ∩ K := fun hmem => hx (heq ▸ hmem).1
  refine Filter.mem_of_superset
    (((hclosed.inter hKc.isClosed).isOpen_compl.inter isOpen_interior).mem_nhds
      ⟨hnotmem, mem_interior_iff_mem_nhds.mpr hKn⟩) ?_
  intro z hz
  rw [Set.mem_compl_iff]
  intro hzthin
  exact hz.1 (heq ▸ ⟨hzthin, interior_subset hz.2⟩)

/-- If `x` lies on no thin part of the tubes, then the compression is the identity near `x`.
Here the local finiteness of the family of tubes and the closedness of the thin parts are used:
only finitely many thin parts meet a compact neighbourhood of `x`, and a neighbourhood of `x`
avoiding those (and contained in the compact set) avoids all of them. -/
theorem tubePhi_eventuallyEq_id_of_notMem_thin {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] {B : Set M} (T : CompressionTube n M B) {x : M}
    (hx : x ∉ ⋃ i, tubeThin T i) :
    ∀ᶠ y in 𝓝 x, tubePhi T y = y := by
  classical
  haveI : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  have hxK : x ∈ interior K := mem_interior_iff_mem_nhds.mpr hKn
  -- only finitely many thin parts meet `K`
  have hfin : {i : T.ι | (tubeThin T i ∩ K).Nonempty}.Finite := by
    refine (T.locallyFinite K hKc).subset ?_
    rintro i ⟨z, hzthin, hzK⟩
    rcases hzthin with ⟨p, hp, rfl⟩
    exact ⟨p, hp, hzK⟩
  have hIclosed : IsClosed (⋃ i ∈ {i : T.ι | (tubeThin T i ∩ K).Nonempty}, tubeThin T i) :=
    hfin.isClosed_biUnion (fun i _ => isClosed_tubeThin T i)
  have hIthin : ∀ i : T.ι, (tubeThin T i ∩ K).Nonempty → False → True := fun _ _ _ => trivial
  set V : Set M := interior K \ (⋃ i ∈ {i : T.ι | (tubeThin T i ∩ K).Nonempty}, tubeThin T i)
    with hV
  have hVopen : IsOpen V := isOpen_interior.sdiff hIclosed
  have hxV : x ∈ V := by
    refine ⟨hxK, ?_⟩
    intro hmem
    rcases Set.mem_iUnion.mp hmem with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hi with ⟨hiS, hithin⟩
    exact hx (Set.mem_iUnion.mpr ⟨i, hithin⟩)
  have hVsub : ∀ y ∈ V, tubePhi T y = y := by
    intro y hy
    obtain ⟨hyK, hyU⟩ := hy
    have hythin : y ∉ ⋃ i, tubeThin T i := by
      intro hmem
      rcases Set.mem_iUnion.mp hmem with ⟨i, hi⟩
      by_cases hiS : (tubeThin T i ∩ K).Nonempty
      · exact hyU (Set.mem_biUnion hiS hi)
      · have hyt : y ∈ tubeThin T i ∩ K := ⟨hi, interior_subset hyK⟩
        rw [Set.not_nonempty_iff_eq_empty.mp hiS] at hyt
        exact hyt
    by_cases hr : ∃ i, y ∈ Set.range (T.tube i)
    · obtain ⟨i, p, rfl⟩ := hr
      have hp1 : 1 ≤ ‖p.1‖ := by
        by_contra hlt
        exact hythin (Set.mem_iUnion.mpr ⟨i, ⟨p, le_of_lt (not_le.mp hlt), rfl⟩⟩)
      rw [tubePhi_apply_tube T i p, tubeF_eq_self n hp1]
    · exact tubePhi_eq_self_of_notMem_range T (fun i h => hr ⟨i, h⟩)
  exact Filter.eventuallyEq_of_mem (hVopen.mem_nhds hxV) hVsub

end

end Work.Noncompact.CompressionTube
