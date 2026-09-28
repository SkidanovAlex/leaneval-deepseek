import Mathlib
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.DetLOrth.Defs
import Submission.Work.HP.DetLOrth.exists_adapted_basis
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.det_inv_compl_block

/-!
# Reciprocal covolume: `detL (orthLat Λ) = detL Λ` for saturated `Λ ⊆ ℤ^ι`

For a saturated (pure, primitive) integral lattice `Λ ⊆ ℤ^ι`, the lattice of integer vectors
orthogonal to `Λ` has the same covolume-in-its-real-span as `Λ`.

The proof follows the route laid out in `Work.HP.DetLOrth`:

* `exists_adapted_basis` writes `Λ = span {b i : i ∈ p}` for a `ℤ`-basis `b` of `ℤ^ι` and a
  subset `p` of the index set (saturation means `Λ` is a direct summand);
* the covolume of `Λ` is the square root of the Gram determinant of `{b i : i ∈ p}`;
* the orthogonal lattice is spanned by the dual vectors `dualVec b i` with `i ∉ p`, whose Gram
  matrix is the complementary block of `(gramR b)⁻¹`;
* Jacobi's complementary minor identity (`Lat.det_inv_compl_block`) together with `det (gramR b) = 1`
  identifies that determinant with the Gram determinant of `{b i : i ∈ p}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

open Matrix

namespace Work.HP.EElow

open Work.HP.DetLOrth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Building a basis of `span {w i : i ∈ q}` from a linearly independent family -/

/-- The map `i ↦ w i` seen as a family of elements of `L = span {w i : i ∈ q}`. -/
def spanVec (w : ι → (ι → ℤ)) (q : ι → Prop) (L : Submodule ℤ (ι → ℤ))
    (hL : L = Submodule.span ℤ (Set.range fun i : {i // q i} => w i.1)) : {i // q i} → L :=
  fun i => ⟨w i.1, by rw [hL]; exact Submodule.subset_span ⟨i, rfl⟩⟩

lemma spanVec_apply (w : ι → (ι → ℤ)) (q : ι → Prop) (L : Submodule ℤ (ι → ℤ))
    (hL : L = Submodule.span ℤ (Set.range fun i : {i // q i} => w i.1)) (i : {i // q i}) :
    ((spanVec w q L hL i : L) : ι → ℤ) = w i.1 := rfl

lemma spanVec_linearIndependent (w : ι → (ι → ℤ)) (hw : LinearIndependent ℤ w) (q : ι → Prop)
    (L : Submodule ℤ (ι → ℤ))
    (hL : L = Submodule.span ℤ (Set.range fun i : {i // q i} => w i.1)) :
    LinearIndependent ℤ (spanVec w q L hL) := by
  refine LinearIndependent.of_comp L.subtype ?_
  have hcomp : (L.subtype ∘ spanVec w q L hL) = w ∘ (Subtype.val : {i // q i} → ι) := by
    funext i; rfl
  rw [hcomp]
  exact hw.comp _ Subtype.val_injective

lemma spanVec_span (w : ι → (ι → ℤ)) (q : ι → Prop) (L : Submodule ℤ (ι → ℤ))
    (hL : L = Submodule.span ℤ (Set.range fun i : {i // q i} => w i.1)) :
    ⊤ ≤ Submodule.span ℤ (Set.range (spanVec w q L hL)) := by
  intro x _
  have hmap : Submodule.map L.subtype (Submodule.span ℤ (Set.range (spanVec w q L hL))) = L := by
    rw [Submodule.map_span]
    have himg : L.subtype '' Set.range (spanVec w q L hL) =
        Set.range fun i : {i // q i} => w i.1 := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨i, rfl⟩ := hz
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨spanVec w q L hL i, ⟨i, rfl⟩, rfl⟩
    rw [himg, ← hL]
  have hx : (x : ι → ℤ) ∈
      Submodule.map L.subtype (Submodule.span ℤ (Set.range (spanVec w q L hL))) := by
    rw [hmap]; exact x.2
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
  have hyx' : x = y := (Subtype.ext hyx).symm
  rw [hyx']; exact hy

/-- A `ℤ`-basis of `L = span {w i : i ∈ q}`, indexed by `{i // q i}`, for a linearly
independent family `w`. -/
def spanBasis (w : ι → (ι → ℤ)) (hw : LinearIndependent ℤ w) (q : ι → Prop)
    (L : Submodule ℤ (ι → ℤ))
    (hL : L = Submodule.span ℤ (Set.range fun i : {i // q i} => w i.1)) :
    Module.Basis {i // q i} ℤ L :=
  Module.Basis.mk (spanVec_linearIndependent w hw q L hL) (spanVec_span w q L hL)

lemma spanBasis_apply (w : ι → (ι → ℤ)) (hw : LinearIndependent ℤ w) (q : ι → Prop)
    (L : Submodule ℤ (ι → ℤ))
    (hL : L = Submodule.span ℤ (Set.range fun i : {i // q i} => w i.1)) (i : {i // q i}) :
    ((spanBasis w hw q L hL i : L) : ι → ℤ) = w i.1 := by
  rw [spanBasis, Module.Basis.mk_apply, spanVec_apply]

/-! ## The three ingredients -/

/-- The covolume of `K = span {b i : i ∈ p}` is the square root of the Gram determinant of the
selected basis vectors. -/
theorem detL_eq_sqrt_gramR_block (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop)
    [DecidablePred p] (K : Submodule ℤ (ι → ℤ))
    (h : K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ))) :
    detL K = Real.sqrt ((gramR b).toSquareBlockProp p).det := by
  classical
  set B : Module.Basis {i // p i} ℤ K :=
    spanBasis (fun i => (b i : ι → ℤ)) b.linearIndependent p K h with hB
  have hmat : (Matrix.of fun i j : {i // p i} =>
      ∑ x, (((B i : ι → ℤ) x : ℝ) * ((B j : ι → ℤ) x : ℝ)))
      = (gramR b).toSquareBlockProp p := by
    ext i j
    rw [Matrix.toSquareBlockProp, Matrix.toBlock_apply, Matrix.of_apply]
    rw [hB, spanBasis_apply, spanBasis_apply]
    rfl
  rw [Work.HP.Lat.detL_basis_gram K B, hmat]

/-- The orthogonal lattice of `K = span {b i : i ∈ p}` is spanned by the dual basis vectors
with index outside `p`. -/
theorem orthLat_eq_span_dualVec (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop)
    [DecidablePred p] (K : Submodule ℤ (ι → ℤ))
    (h : K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ))) :
    orthLat K = Submodule.span ℤ (Set.range fun i : {i // ¬ p i} => dualVec b i.1) := by
  classical
  apply le_antisymm
  · intro a ha
    rw [← sum_dualVec_smul b a]
    refine Submodule.sum_mem _ ?_
    intro i _
    by_cases hp : p i
    · have hz : (∑ x, a x * b i x) = 0 := by
        have h1 : dotI a (b i) = 0 :=
          (mem_orthLat.mp ha) (b i)
            (by rw [h]; exact Submodule.subset_span ⟨⟨i, hp⟩, rfl⟩)
        simpa [dotI] using h1
      simp [hz]
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hp⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    simp only [mem_orthLat]
    intro y hy
    rw [h] at hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · rintro z ⟨j, rfl⟩
      rw [dotI, dualVec_pairing]
      have hne : ¬ (i.1 = j.1) := fun hij => i.2 (hij ▸ j.2)
      simp [hne]
    · simp [dotI]
    · intro u v hu hv ihu ihv
      rw [dotI_add_right, ihu, ihv, add_zero]
    · intro c u hu ihu
      rw [dotI_smul_right, ihu, mul_zero]

/-- The covolume of `orthLat K` in terms of the inverse Gram matrix, given that the dual vectors
with index outside `p` span it. -/
theorem detL_orthLat_eq_sqrt_gramR_inv_block (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop)
    [DecidablePred p] (K : Submodule ℤ (ι → ℤ))
    (hsp : orthLat K = Submodule.span ℤ (Set.range fun i : {i // ¬ p i} => dualVec b i.1)) :
    detL (orthLat K) =
      Real.sqrt (((gramR b)⁻¹).toSquareBlockProp (fun i => ¬ p i)).det := by
  classical
  set B : Module.Basis {i // ¬ p i} ℤ (orthLat K) :=
    spanBasis (dualVec b) (dualVec_linearIndependent b) (fun i => ¬ p i) (orthLat K) hsp with hB
  have hmat : (Matrix.of fun i j : {i // ¬ p i} =>
      ∑ x, (((B i : ι → ℤ) x : ℝ) * ((B j : ι → ℤ) x : ℝ)))
      = (((gramR b)⁻¹).toSquareBlockProp (fun i => ¬ p i)) := by
    ext i j
    rw [Matrix.toSquareBlockProp, Matrix.toBlock_apply, Matrix.of_apply]
    rw [hB, spanBasis_apply, spanBasis_apply]
    rw [gramR_inv_apply]
  rw [Work.HP.Lat.detL_basis_gram (orthLat K) B, hmat]

/-! ## The main statement -/

theorem detL_orthLat {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : Submodule ℤ (ι → ℤ))
    (h : Work.HP.IsPrimLat Λ) : Work.HP.detL (Work.HP.orthLat Λ) = Work.HP.detL Λ := by
  classical
  obtain ⟨b, p, hp⟩ := exists_adapted_basis Λ h
  have h1 : detL Λ = Real.sqrt ((gramR b).toSquareBlockProp p).det :=
    detL_eq_sqrt_gramR_block b p Λ hp
  have h2 : detL (orthLat Λ) =
      Real.sqrt (((gramR b)⁻¹).toSquareBlockProp (fun i => ¬ p i)).det :=
    detL_orthLat_eq_sqrt_gramR_inv_block b p Λ (orthLat_eq_span_dualVec b p Λ hp)
  rw [h1, h2]
  have hMdet : (gramR b).det = 1 := gramR_det b
  have hMne : (gramR b).det ≠ 0 := by rw [hMdet]; norm_num
  have hAne : ((gramR b).toSquareBlockProp p).det ≠ 0 := gramR_block_det_ne_zero b p
  have hjac := Work.HP.Lat.det_inv_compl_block (gramR b) hMne p hAne
  rw [hMdet, div_one] at hjac
  rw [hjac]

end Work.HP.EElow
