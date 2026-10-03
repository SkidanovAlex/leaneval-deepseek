import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_homotopyEquiv_subgraph_oneDimCW_of_union_dyadicCells
import Submission.Lib.Unif2.Commons.Topology.Plane.polyomino_deformationRetract_oneDim

/-!
# A finite union of dyadic cells strongly deformation retracts onto a 1-dimensional spine

For `n : ℕ` and a finite set `S` of indices, the finite union
`K = ⋃ p ∈ S, dyadicCell n p` of closed dyadic squares of level `n` in `ℂ` is a finite subcomplex of
the standard dyadic square complex.  The classical "spine" theorem for polyominoes then says that
`K` strongly deformation retracts onto a 1-dimensional CW subcomplex `G ⊆ K` (no cells in dimension
`≥ 2`).

The commons theorem `Commons.Topology.Plane.exists_homotopyEquiv_subgraph_oneDimCW_of_union_dyadicCells`
gives such a `G` together with a *homotopy equivalence*.  Here we upgrade this to an honest strong
deformation retraction, by scaling the *unit* polyomino theorem
`Commons.Topology.Plane.polyomino_deformationRetract_oneDim` (which already yields a strong
deformation retraction) by the factor `2^{-n}`.
-/

open Set
open scoped Topology

noncomputable section

namespace Commons.Topology.Plane

/-! ## Scaling the plane -/

/-- Scaling of `ℂ` by the factor `2^{-n}`. -/
def dsc (n : ℕ) : ℂ → ℂ := fun z => ⟨z.re / 2 ^ n, z.im / 2 ^ n⟩

/-- Scaling of `ℂ` by the factor `2^{n}`; the inverse of `dsc n`. -/
def dscI (n : ℕ) : ℂ → ℂ := fun z => ⟨z.re * 2 ^ n, z.im * 2 ^ n⟩

lemma dsc_re (n : ℕ) (z : ℂ) : (dsc n z).re = z.re / 2 ^ n := rfl
lemma dsc_im (n : ℕ) (z : ℂ) : (dsc n z).im = z.im / 2 ^ n := rfl
lemma dscI_re (n : ℕ) (z : ℂ) : (dscI n z).re = z.re * 2 ^ n := rfl
lemma dscI_im (n : ℕ) (z : ℂ) : (dscI n z).im = z.im * 2 ^ n := rfl

lemma dsc_two_pow_pos (n : ℕ) : (0 : ℝ) < 2 ^ n := by positivity
lemma dsc_two_pow_ne (n : ℕ) : (2 : ℝ) ^ n ≠ 0 := ne_of_gt (dsc_two_pow_pos n)

lemma dscI_dsc (n : ℕ) (z : ℂ) : dscI n (dsc n z) = z := by
  apply Complex.ext <;> simp only [dscI_re, dsc_re, dscI_im, dsc_im]
  · exact div_mul_cancel₀ _ (dsc_two_pow_ne n)
  · exact div_mul_cancel₀ _ (dsc_two_pow_ne n)

lemma dsc_dscI (n : ℕ) (z : ℂ) : dsc n (dscI n z) = z := by
  apply Complex.ext <;> simp only [dsc_re, dscI_re, dsc_im, dscI_im]
  · exact mul_div_cancel_right₀ _ (dsc_two_pow_ne n)
  · exact mul_div_cancel_right₀ _ (dsc_two_pow_ne n)

lemma continuous_dsc (n : ℕ) : Continuous (dsc n) := by
  change Continuous (fun z : ℂ => (⟨z.re / 2 ^ n, z.im / 2 ^ n⟩ : ℂ))
  rw [show (fun z : ℂ => (⟨z.re / 2 ^ n, z.im / 2 ^ n⟩ : ℂ)) = (dAff 0 0 (1 / 2 ^ n)) from by
    funext z; apply Complex.ext
    · simp only [dAff]; rw [zero_add, div_eq_mul_inv]; ring
    · simp only [dAff]; rw [zero_add, div_eq_mul_inv]; ring]
  exact continuous_dAff _ _ _

lemma continuous_dscI (n : ℕ) : Continuous (dscI n) := by
  change Continuous (fun z : ℂ => (⟨z.re * 2 ^ n, z.im * 2 ^ n⟩ : ℂ))
  rw [show (fun z : ℂ => (⟨z.re * 2 ^ n, z.im * 2 ^ n⟩ : ℂ)) = (dInv 0 0 (1 / 2 ^ n)) from by
    funext z; apply Complex.ext
    · simp only [dInv]; rw [sub_zero, one_div, div_eq_mul_inv, inv_inv]
    · simp only [dInv]; rw [sub_zero, one_div, div_eq_mul_inv, inv_inv]]
  exact continuous_dInv _ _ _

lemma dsc_injective (n : ℕ) : Function.Injective (dsc n) := by
  intro a b h
  have := congrArg (dscI n) h
  rwa [dscI_dsc, dscI_dsc] at this

/-! ## The scaling identifies the unit polyomino with the dyadic one -/

lemma dsc_mem_dSq {n : ℕ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ dSq n p ↔ (p.1 : ℝ) / 2 ^ n ≤ z.re ∧ z.re ≤ ((p.1 : ℝ) + 1) / 2 ^ n ∧
      (p.2 : ℝ) / 2 ^ n ≤ z.im ∧ z.im ≤ ((p.2 : ℝ) + 1) / 2 ^ n := Iff.rfl

lemma dsc_mem_dInt {n : ℕ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ dInt n p ↔ (p.1 : ℝ) / 2 ^ n < z.re ∧ z.re < ((p.1 : ℝ) + 1) / 2 ^ n ∧
      (p.2 : ℝ) / 2 ^ n < z.im ∧ z.im < ((p.2 : ℝ) + 1) / 2 ^ n := Iff.rfl

lemma dsc_mem_dOpenTop {n : ℕ} {p : ℤ × ℤ} {z : ℂ} :
    z ∈ dOpenTop n p ↔ (p.1 : ℝ) / 2 ^ n < z.re ∧ z.re < ((p.1 : ℝ) + 1) / 2 ^ n ∧
      z.im = ((p.2 : ℝ) + 1) / 2 ^ n := Iff.rfl

lemma image_dsc_unitSqAt (n : ℕ) (p : ℤ × ℤ) : dsc n '' unitSqAt p = dSq n p := by
  ext w; constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_unitSqAt] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [dsc_mem_dSq]
    exact ⟨div_le_div_of_nonneg_right h1 (le_of_lt (dsc_two_pow_pos n)),
           div_le_div_of_nonneg_right h2 (le_of_lt (dsc_two_pow_pos n)),
           div_le_div_of_nonneg_right h3 (le_of_lt (dsc_two_pow_pos n)),
           div_le_div_of_nonneg_right h4 (le_of_lt (dsc_two_pow_pos n))⟩
  · intro hw
    rw [dsc_mem_dSq] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨dscI n w, ?_, dsc_dscI n w⟩
    rw [mem_unitSqAt]
    exact ⟨(div_le_iff₀ (dsc_two_pow_pos n)).mp h1, (le_div_iff₀ (dsc_two_pow_pos n)).mp h2,
           (div_le_iff₀ (dsc_two_pow_pos n)).mp h3, (le_div_iff₀ (dsc_two_pow_pos n)).mp h4⟩

lemma image_dsc_openSqAt (n : ℕ) (p : ℤ × ℤ) : dsc n '' openSqAt p = dInt n p := by
  ext w; constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_openSqAt] at hz
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [dsc_mem_dInt]
    exact ⟨div_lt_div_of_pos_right h1 (dsc_two_pow_pos n),
           div_lt_div_of_pos_right h2 (dsc_two_pow_pos n),
           div_lt_div_of_pos_right h3 (dsc_two_pow_pos n),
           div_lt_div_of_pos_right h4 (dsc_two_pow_pos n)⟩
  · intro hw
    rw [dsc_mem_dInt] at hw
    obtain ⟨h1, h2, h3, h4⟩ := hw
    refine ⟨dscI n w, ?_, dsc_dscI n w⟩
    rw [mem_openSqAt]
    exact ⟨(div_lt_iff₀ (dsc_two_pow_pos n)).mp h1, (lt_div_iff₀ (dsc_two_pow_pos n)).mp h2,
           (div_lt_iff₀ (dsc_two_pow_pos n)).mp h3, (lt_div_iff₀ (dsc_two_pow_pos n)).mp h4⟩

lemma image_dsc_openTopAt (n : ℕ) (p : ℤ × ℤ) : dsc n '' openTopAt p = dOpenTop n p := by
  ext w; constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_openTopAt] at hz
    obtain ⟨h1, h2, h3⟩ := hz
    rw [dsc_mem_dOpenTop, dsc_im, h3]
    exact ⟨div_lt_div_of_pos_right h1 (dsc_two_pow_pos n),
           div_lt_div_of_pos_right h2 (dsc_two_pow_pos n), rfl⟩
  · intro hw
    rw [dsc_mem_dOpenTop] at hw
    obtain ⟨h1, h2, h3⟩ := hw
    refine ⟨dscI n w, ?_, dsc_dscI n w⟩
    rw [mem_openTopAt]
    refine ⟨(div_lt_iff₀ (dsc_two_pow_pos n)).mp h1, (lt_div_iff₀ (dsc_two_pow_pos n)).mp h2, ?_⟩
    rw [dscI_im, h3]
    exact div_mul_cancel₀ _ (dsc_two_pow_ne n)

lemma image_dsc_badSet (n : ℕ) (p : ℤ × ℤ) : dsc n '' badSet p = dRemoved n p := by
  rw [badSet, dRemoved, Set.image_union, image_dsc_openSqAt, image_dsc_openTopAt]

lemma image_dsc_polyK (n : ℕ) (S : Finset (ℤ × ℤ)) : dsc n '' polyK S = YSet n S ∅ := by
  rw [YSet_empty]
  show dsc n '' (⋃ p ∈ S, unitSqAt p) = ⋃ p ∈ S, dSq n p
  simp only [Set.image_iUnion, image_dsc_unitSqAt]

lemma image_dsc_spineSet (n : ℕ) (S A : Finset (ℤ × ℤ)) : dsc n '' spineSet S A = YSet n S A := by
  rw [spineSet, YSet, image_sdiff_of_injective (dsc_injective n)]
  rw [image_dsc_polyK, YSet_empty]
  congr 1
  rw [show (⋃ p ∈ A, badSet p) = ⋃ p, ⋃ (_ : p ∈ A), badSet p from rfl]
  simp only [Set.image_iUnion, image_dsc_badSet]

/-! ## Transfer of the unit-square deformation retraction -/

/-- The unit-square spine retraction, scaled by `2^{-n}`, is a strong deformation retraction of
`YSet n S ∅` onto `YSet n S S`. -/
theorem dyadic_spine_retraction (n : ℕ) (S : Finset (ℤ × ℤ)) :
    ∃ H : ↥(YSet n S ∅) × ↥(Set.Icc (0:ℝ) 1) → ↥(YSet n S ∅),
      Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x, ((H (x, 1) : ↥(YSet n S ∅)) : ℂ) ∈ YSet n S S) ∧
      (∀ x, ((x : ↥(YSet n S ∅)) : ℂ) ∈ YSet n S S → ∀ t, H (x, t) = x) := by
  obtain ⟨Φ, hΦ0, hΦ1, hΦfix⟩ := exists_spine_retraction S
  have hmap_unit : MapsTo (dsc n) (polyK S) (YSet n S ∅) := by
    intro z hz
    rw [← image_dsc_polyK n S]
    exact ⟨z, hz, rfl⟩
  have hmap_dy : MapsTo (dscI n) (YSet n S ∅) (polyK S) := by
    intro z hz
    have hz' : z ∈ dsc n '' polyK S := by rw [image_dsc_polyK]; exact hz
    obtain ⟨y, hy, hyz⟩ := hz'
    rw [show dscI n z = y from by rw [← hyz, dscI_dsc]]
    exact hy
  have hmap_spine : MapsTo (dscI n) (YSet n S S) (spineSet S S) := by
    intro z hz
    have hz' : z ∈ dsc n '' spineSet S S := by rw [image_dsc_spineSet]; exact hz
    obtain ⟨y, hy, hyz⟩ := hz'
    rw [show dscI n z = y from by rw [← hyz, dscI_dsc]]
    exact hy
  let φp : ↥(YSet n S ∅) → ↥(polyK S) := fun x => ⟨dscI n (x : ℂ), hmap_dy x.2⟩
  have hφpc : Continuous φp :=
    Continuous.subtype_mk ((continuous_dscI n).comp continuous_subtype_val)
      (fun x => hmap_dy x.2)
  have hHcontfun : Continuous (fun q : ↥(YSet n S ∅) × ↥(Set.Icc (0:ℝ) 1) =>
      dsc n ((Φ (φp q.1, q.2) : ↥(polyK S)) : ℂ)) := by
    have h1 : Continuous (fun q : ↥(YSet n S ∅) × ↥(Set.Icc (0:ℝ) 1) => (φp q.1, q.2)) :=
      (hφpc.comp continuous_fst).prodMk continuous_snd
    exact (continuous_dsc n).comp (continuous_subtype_val.comp (Φ.continuous.comp h1))
  refine ⟨fun q => ⟨dsc n ((Φ (φp q.1, q.2) : ↥(polyK S)) : ℂ),
      hmap_unit (Φ (φp q.1, q.2)).2⟩, ?_, ?_, ?_, ?_⟩
  · exact hHcontfun.subtype_mk (fun q => hmap_unit (Φ (φp q.1, q.2)).2)
  · intro x
    apply Subtype.ext
    have h := hΦ0 (φp x)
    show dsc n ((Φ (φp x, (0 : ↥(Set.Icc (0:ℝ) 1))) : ↥(polyK S)) : ℂ) = (x : ℂ)
    rw [h]
    show dsc n (dscI n (x : ℂ)) = (x : ℂ)
    exact dsc_dscI n (x : ℂ)
  · intro x
    have h := hΦ1 (φp x)
    show dsc n ((Φ (φp x, (1 : ↥(Set.Icc (0:ℝ) 1))) : ↥(polyK S)) : ℂ) ∈ YSet n S S
    rw [← image_dsc_spineSet n S S]
    exact ⟨_, h, rfl⟩
  · intro x hx t
    have hx' : ((φp x : ↥(polyK S)) : ℂ) ∈ spineSet S S := hmap_spine hx
    have h := hΦfix (φp x) hx' t
    apply Subtype.ext
    show dsc n ((Φ (φp x, t) : ↥(polyK S)) : ℂ) = (x : ℂ)
    rw [h]
    show dsc n (dscI n (x : ℂ)) = (x : ℂ)
    exact dsc_dscI n (x : ℂ)

/-! ## Assembly: CW structure and deformation retraction -/

theorem dyadic_aux (n : ℕ) (S : Finset (ℤ × ℤ)) :
    ∃ (G : Set ↥(⋃ p ∈ S, dSq n p))
      (hC : @Topology.CWComplex ↥(⋃ p ∈ S, dSq n p) _ G)
      (H : ↥(⋃ p ∈ S, dSq n p) × ↥(Set.Icc (0:ℝ) 1) → ↥(⋃ p ∈ S, dSq n p)),
      (∀ m : ℕ, 2 ≤ m →
        IsEmpty (@Topology.CWComplex.cell ↥(⋃ p ∈ S, dSq n p) _ G hC m)) ∧
      Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x, H (x, 1) ∈ G) ∧ (∀ x, x ∈ G → ∀ t, H (x, t) = x) := by
  rw [← YSet_empty n S]
  obtain ⟨hCseg, hcellseg⟩ := exists_cwComplex_of_finset_segments (gVerts n S) (gEdges n S)
    (fun _ he => gEdges_endpoints_mem_gVerts he) (fun _ he => gEdges_ne he)
    (fun _ he _ he' hne' => gEdges_disjoint_segments he he' hne')
  have hKclosed : IsClosed (YSet n S ∅) := by
    rw [YSet_empty]
    exact isClosed_biUnion_finset (fun p _ => isClosed_dSq n p)
  have hsub : ((gVerts n S : Set ℂ) ∪ ⋃ e ∈ gEdges n S, segment ℝ e.1 e.2) ⊆ YSet n S ∅ := by
    rw [← YSet_eq_segments n S]
    exact YSet_antitone n S (Finset.empty_subset S)
  obtain ⟨hC', hcell'⟩ := exists_cwComplex_subtype_of_subset hsub hKclosed hCseg
  obtain ⟨H, hHcont, hH0, hH1, hHfix⟩ := dyadic_spine_retraction n S
  refine ⟨{z : ↥(YSet n S ∅) |
      (z : ℂ) ∈ (gVerts n S : Set ℂ) ∪ ⋃ e ∈ gEdges n S, segment ℝ e.1 e.2},
    hC', H, ?_, hHcont, hH0, ?_, ?_⟩
  · intro m hm
    exact hcell' m (hcellseg m hm)
  · intro x
    rw [← YSet_eq_segments n S]
    exact hH1 x
  · intro x hx t
    rw [← YSet_eq_segments n S] at hx
    exact hHfix x hx t

theorem dyadicPolyomino_deformationRetract (n : ℕ) (S : Finset (ℤ × ℤ)) :
    ∃ (G : Set ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p))
      (hC : @Topology.CWComplex ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p) _ G)
      (H : ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p) × ↥(Set.Icc (0:ℝ) 1) →
           ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p)),
      (∀ m : ℕ, 2 ≤ m →
        IsEmpty (@Topology.CWComplex.cell ↥(⋃ p ∈ S, Commons.Topology.Plane.dyadicCell n p) _ G hC m)) ∧
      Continuous H ∧ (∀ x, H (x, 0) = x) ∧
      (∀ x, H (x, 1) ∈ G) ∧ (∀ x, x ∈ G → ∀ t, H (x, t) = x) := by
  exact dyadic_aux n S

end Commons.Topology.Plane
