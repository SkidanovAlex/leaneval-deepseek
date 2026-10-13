import Mathlib
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilkiesH.Norm.normMap_mem_cube01_and_injOn

/-!
# Normalisation preserves the dimension bound `DimLE`

`WilkiesDesign.DimLE X μ` means (o-minimally) that `dim X ≤ μ`, i.e. that every
projection of `X` to `μ + 1` coordinates has empty interior.  This file shows that
the coordinatewise normalisation `normSet σ X = normMap σ '' (X ∩ normPiece σ)`
does not raise the dimension: `DimLE X μ → DimLE (normSet σ X) μ`.

The mathematical content is entirely local.  Fix an embedding
`e : Fin (μ+1) ↪ Fin n` and let `π` be the projection onto the coordinates in the
range of `e`.  Writing `s j = σ (e j)` we have

  `π '' normSet σ X = Φ '' A`,  where `Φ z = fun j => shapeMap (s j) (z j)`
  and `A = π '' (X ∩ normPiece σ) ⊆ π '' X`.

Here `Φ` is a *coordinatewise* map, each of whose coordinates
(`shapeMap s : t ↦ t`, `t ↦ -t`, `t ↦ t⁻¹`, `t ↦ -t⁻¹`) is continuous and
injective on the corresponding region `shapeSet s`, and those regions are
intervals with dense interior.  The general topological fact proved below
(`cwImage_interior`) is that such a coordinatewise map cannot manufacture
interior: if `Φ '' A` has nonempty interior then so does `A`.  Hence
`interior (π '' normSet σ X) ≠ ∅` forces `interior (π '' X) ≠ ∅`, contradicting
`DimLE X μ`.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture

/-- A coordinatewise map never creates interior.

Let `J : Fin m → Set ℝ`, let `f : Fin m → ℝ → ℝ` be continuous and injective on
each `J j`, and suppose every `J j` is contained in the closure of its interior
(in particular `J j` has nonempty interior).  Write
`Φ z = fun j => f j (z j)`.  If `A` is contained in the box `∏ j, J j` and
`Φ '' A` has nonempty interior in `ℝ^m`, then `A` itself has nonempty interior;
more precisely it contains a nonempty open set.

Indeed, `z ∈ int (Φ '' A)` together with injectivity of `Φ` on the box shows
that `Φ ⁻¹' (int (Φ '' A)) ∩ ∏ J j ⊆ A` is a relatively open subset of the box;
intersecting it with the (dense) interior `∏ int (J j)` yields the required open
subset of `A`. -/
theorem cwImage_interior {m : ℕ} {J : Fin m → Set ℝ} {f : Fin m → ℝ → ℝ}
    {A : Set (Fin m → ℝ)}
    (hA : A ⊆ Set.pi Set.univ J)
    (hcont : ∀ j, ContinuousOn (f j) (J j))
    (hinj : ∀ j, Set.InjOn (f j) (J j))
    (hdense : ∀ j, J j ⊆ closure (interior (J j)))
    (hint : (interior ((fun z : Fin m → ℝ => fun j => f j (z j)) '' A)).Nonempty) :
    ∃ U : Set (Fin m → ℝ), IsOpen U ∧ U.Nonempty ∧ U ⊆ A := by
  set φ : (Fin m → ℝ) → (Fin m → ℝ) := fun z => fun j => f j (z j)
  have hinjφ : Set.InjOn φ (Set.pi Set.univ J) := by
    intro z hz w hw hzw
    funext j
    exact hinj j (hz j (Set.mem_univ j)) (hw j (Set.mem_univ j)) (congrFun hzw j)
  obtain ⟨u₀, hu₀⟩ := hint
  obtain ⟨ub, hIsub, hub⟩ := (isOpen_pi_iff'.1 isOpen_interior) u₀ hu₀
  have hsub : Set.pi Set.univ ub ⊆ φ '' A := fun x hx => interior_subset (hub hx)
  have hu₀ub : u₀ ∈ Set.pi Set.univ ub := fun j _ => (hIsub j).2
  obtain ⟨a₀, ha₀A, ha₀⟩ := hsub hu₀ub
  have ha₀D : a₀ ∈ Set.pi Set.univ J := hA ha₀A
  have ha₀ub : ∀ j, f j (a₀ j) ∈ ub j := fun j => by
    have h : f j (a₀ j) = u₀ j := congrFun ha₀ j
    rw [h]; exact (hIsub j).2
  have hch : ∀ j, ∃ u : Set ℝ, IsOpen u ∧ (f j) ⁻¹' (ub j) ∩ J j = u ∩ J j :=
    fun j => (continuousOn_iff'.1 (hcont j)) (ub j) ((hIsub j).1)
  choose v hv using hch
  have hvopen : ∀ j, IsOpen (v j) := fun j => (hv j).1
  have hveq : ∀ j, (f j) ⁻¹' (ub j) ∩ J j = v j ∩ J j := fun j => (hv j).2
  have hUopen : IsOpen (Set.pi Set.univ v) :=
    isOpen_set_pi Set.finite_univ (fun j _ => hvopen j)
  have hDcopen : IsOpen (Set.pi Set.univ (fun j => interior (J j))) :=
    isOpen_set_pi Set.finite_univ (fun j _ => isOpen_interior)
  have hdenseD : Set.pi Set.univ J ⊆ closure (Set.pi Set.univ (fun j => interior (J j))) := by
    intro z hz
    rw [mem_closure_pi]
    intro j _
    exact hdense j (hz j (Set.mem_univ j))
  have ha₀U : a₀ ∈ Set.pi Set.univ v := by
    intro j _
    have h2 : a₀ j ∈ J j := ha₀D j (Set.mem_univ j)
    have h3 : a₀ j ∈ (f j) ⁻¹' (ub j) ∩ J j := ⟨ha₀ub j, h2⟩
    rw [hveq j] at h3
    exact h3.1
  have hne : (Set.pi Set.univ v ∩ Set.pi Set.univ (fun j => interior (J j))).Nonempty :=
    mem_closure_iff.1 (hdenseD ha₀D) _ hUopen ha₀U
  refine ⟨Set.pi Set.univ v ∩ Set.pi Set.univ (fun j => interior (J j)),
    hUopen.inter hDcopen, hne, ?_⟩
  intro z hz
  have hzV : z ∈ Set.pi Set.univ v := hz.1
  have hzJ : ∀ j, z j ∈ J j := fun j => interior_subset (hz.2 j (Set.mem_univ j))
  have hzφub : φ z ∈ Set.pi Set.univ ub := by
    intro j _
    have h1 : z j ∈ v j := hzV j (Set.mem_univ j)
    have h3 : z j ∈ v j ∩ J j := ⟨h1, hzJ j⟩
    rw [← hveq j] at h3
    exact h3.1
  have hzD : z ∈ Set.pi Set.univ J := fun j _ => hzJ j
  obtain ⟨a, haA, ha⟩ := hsub hzφub
  have hza : z = a := hinjφ hzD (hA haA) ha.symm
  rw [hza]; exact haA

/-- Every shape map is continuous on its region. -/
lemma shapeMap_continuousOn (s : NormShape) : ContinuousOn (shapeMap s) (shapeSet s) := by
  cases s
  · exact continuous_id.continuousOn
  · exact continuous_neg.continuousOn
  · have hsub : Set.Ioi (1 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := by
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      simp only [Set.mem_Ioi] at ht
      exact ne_of_gt (by linarith)
    exact continuousOn_inv₀.mono hsub
  · have hsub : Set.Iio (-1 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := by
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      simp only [Set.mem_Iio] at ht
      exact ne_of_lt (by linarith)
    exact (continuousOn_inv₀.mono hsub).neg

/-- Every shape region is contained in the closure of its interior. -/
lemma shapeSet_subset_closure_interior (s : NormShape) :
    shapeSet s ⊆ closure (interior (shapeSet s)) := by
  cases s
  · intro t ht
    simp only [shapeSet] at ht ⊢
    rw [interior_Icc, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ht
  · intro t ht
    simp only [shapeSet] at ht ⊢
    rw [interior_Icc, closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
    exact ht
  · intro t ht
    simp only [shapeSet] at ht ⊢
    rw [interior_Ioi]
    exact subset_closure ht
  · intro t ht
    simp only [shapeSet] at ht ⊢
    rw [interior_Iio]
    exact subset_closure ht

theorem dimLE_normSet {n μ : ℕ} (σ : Fin n → Work.WilkiesH.Norm.NormShape) (X : Set (Fin n → ℝ))
    (h : WilkiesDesign.DimLE X μ) : WilkiesDesign.DimLE (Work.WilkiesH.Norm.normSet σ X) μ := by
  intro e
  set A : Set (Fin (μ + 1) → ℝ) :=
    (fun y : Fin n → ℝ => y ∘ e) '' (X ∩ normPiece σ) with hAdef
  set Φ : (Fin (μ + 1) → ℝ) → (Fin (μ + 1) → ℝ) :=
    fun z => fun j => shapeMap (σ (e j)) (z j) with hΦdef
  have hA_sub : A ⊆ Set.pi Set.univ (fun j : Fin (μ + 1) => shapeSet (σ (e j))) := by
    rintro z ⟨y, ⟨-, hypiece⟩, rfl⟩
    exact fun j _ => hypiece (e j)
  have hA_proj : A ⊆ (fun x : Fin n → ℝ => x ∘ e) '' X := by
    rintro z ⟨y, ⟨hyX, -⟩, rfl⟩
    exact ⟨y, hyX, rfl⟩
  have himg : (fun x : Fin n → ℝ => x ∘ e) '' normSet σ X = Φ '' A := by
    show (fun x : Fin n → ℝ => x ∘ e) '' (normMap σ '' (X ∩ normPiece σ)) = Φ '' A
    rw [Set.image_image, hAdef, Set.image_image]
    rfl
  rw [himg, ← Set.not_nonempty_iff_eq_empty]
  rintro ⟨u, hu⟩
  obtain ⟨U, hUopen, hUne, hUA⟩ :=
    cwImage_interior (m := μ + 1) (J := fun j => shapeSet (σ (e j)))
      (f := fun j => shapeMap (σ (e j))) (A := A) hA_sub
      (fun j => shapeMap_continuousOn _) (fun j => shapeMap_injOn _)
      (fun j => shapeSet_subset_closure_interior _) ⟨u, hu⟩
  obtain ⟨z, hzU⟩ := hUne
  have hz : z ∈ interior ((fun x : Fin n → ℝ => x ∘ e) '' X) :=
    interior_maximal (hUA.trans hA_proj) hUopen hzU
  rw [h e] at hz
  exact hz

end Work.WilkiesH.Norm
