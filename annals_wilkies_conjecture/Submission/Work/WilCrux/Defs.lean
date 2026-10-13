/-
  Work.WilCrux — vocabulary for the G4c crux `BadProjThin` (T0 of the reviewed proof map
  `sources/wilkiesG4/wilkies_g4c_crux_map.md`, 2026-10-11).

  A *cell* `κ` of a sharp cell decomposition of `ℝ^{m+N}` which lies over an open base cell and
  whose fibre type sequence has `n₁` band levels and `n₂` graph levels is the graph of a
  continuous map `φ : ℝ^{m+n₁} → ℝ^{n₂}` over an open set of "band coordinates".  A coordinate
  permutation `e : Fin N ≃ Fin (n₁ + n₂)` splits the fibre coordinates into the `n₁` band
  coordinates (`v (Fin.natAdd m k)`) followed by the `n₂` graph coordinates (given by `φ v`).
  `sheetPt e v u` is the point of `ℝ^{m+N}` with parameters `v ∘ castAdd` and fibre coordinates
  `Fin.append (band part of v) u` reindexed by `e`.

  This file only sets up that vocabulary and its basic coordinate API.  The nodes of the map
  live in the sibling files, all in the `Work.WilCrux` namespace.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The point of `ℝ^{m+N}` over a parameter with prescribed fibre coordinates -/

/-- The point of `ℝ^{m+N}` lying over `v = (w, y_A) ∈ ℝ^{m+n₁}` with fibre coordinates
`Fin.append y_A u` reindexed by `e`.  Here `y_A` is the band part of `v` (dropping the first
`m` coordinates) and `u : Fin n₂ → ℝ` is the graph part. -/
def sheetPt {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) (v : Fin (m + n1) → ℝ)
    (u : Fin n2 → ℝ) : Fin (m + N) → ℝ :=
  Fin.append (fun i : Fin m => v (Fin.castAdd n1 i))
    (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) u) (e j))

/-- The parameter coordinates of `sheetPt` are those of `v`. -/
@[simp] theorem sheetPt_castAdd {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) (i : Fin m) :
    sheetPt e v u (Fin.castAdd N i) = v (Fin.castAdd n1 i) := by
  simp only [sheetPt, Fin.append_left]

/-- The `j`-th fibre coordinate of `sheetPt` is the `(e j)`-th entry of `(band part of v, u)`. -/
@[simp] theorem sheetPt_natAdd {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) (j : Fin N) :
    sheetPt e v u (Fin.natAdd m j) =
      (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) u) (e j) := by
  simp only [sheetPt, Fin.append_right]

/-- `sheetPt` is continuous in `(v, u)`. -/
theorem continuous_sheetPt {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) :
    Continuous (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPt e p.1 p.2) := by
  have hA : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      (fun i : Fin m => p.1 (Fin.castAdd n1 i)) :=
    continuous_pi fun i => (continuous_apply (Fin.castAdd n1 i)).comp continuous_fst
  have hC : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      ((fun k : Fin n1 => p.1 (Fin.natAdd m k)), p.2) :=
    (continuous_pi fun k =>
      (continuous_apply (Fin.natAdd m k)).comp continuous_fst).prodMk continuous_snd
  have hD : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      Fin.append (fun k : Fin n1 => p.1 (Fin.natAdd m k)) p.2 :=
    (Fin.continuous_append n1 n2).comp hC
  have hB : Continuous fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) =>
      (fun j : Fin N => (Fin.append (fun k : Fin n1 => p.1 (Fin.natAdd m k)) p.2) (e j)) :=
    continuous_pi fun j => (continuous_apply (e j)).comp hD
  exact (Fin.continuous_append m N).comp (hA.prodMk hB)

/-- **`sheetPt` is injective**: the pair `(v, u)` can be read back off the point. -/
theorem sheetPt_injective {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2)) :
    Function.Injective (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPt e p.1 p.2) := by
  rintro ⟨v, u⟩ ⟨v', u'⟩ h
  have h' : sheetPt e v u = sheetPt e v' u' := h
  have hv : v = v' := by
    funext i
    refine Fin.addCases (m := m) (n := n1) (motive := fun i => v i = v' i) ?_ ?_ i
    · intro i'
      have h1 := congrFun h' (Fin.castAdd N i')
      simpa only [sheetPt_castAdd] using h1
    · intro k'
      have h1 := congrFun h' (Fin.natAdd m (e.symm (Fin.castAdd n2 k')))
      simpa only [sheetPt_natAdd, Equiv.apply_symm_apply, Fin.append_left] using h1
  subst hv
  have hu : u = u' := by
    funext k
    have h1 := congrFun h' (Fin.natAdd m (e.symm (Fin.natAdd n1 k)))
    simpa only [sheetPt_natAdd, Equiv.apply_symm_apply, Fin.append_right] using h1
  subst hu
  rfl

/-! ## 2. The shear family -/

/-- The sheared family: parameters `v = (w, y_A)` and fibre variable `u = y_B - φ v`. -/
def shearFam {m n1 n2 N : ℕ} (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ) (e : Fin N ≃ Fin (n1 + n2))
    (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)) : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ) → ℝ :=
  fun v u => g (fun i : Fin m => v (Fin.castAdd n1 i))
    (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) (φ v + u)) (e j))

/-- The joint function of the sheared family at `(v, u)` is the joint function of `g` at the
point of the sheet with fibre coordinates `φ v + u`. -/
theorem famFun_shearFam {m n1 n2 N : ℕ} (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) :
    Work.WilG4c.famFun (shearFam g e φ) (Fin.append v u)
      = Work.WilG4c.famFun g (sheetPt e v (φ v + u)) := by
  simp only [Work.WilG4c.famFun, shearFam, sheetPt, Fin.append_left, Fin.append_right]

/-- The joint function of the sheared family at `u = 0` is the joint function of `g` at the
graph point `(v, φ v)`. -/
theorem famFun_shearFam_zero {m n1 n2 N : ℕ} (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (e : Fin N ≃ Fin (n1 + n2)) (φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ))
    (v : Fin (m + n1) → ℝ) :
    Work.WilG4c.famFun (shearFam g e φ) (Fin.append v (0 : Fin n2 → ℝ))
      = Work.WilG4c.famFun g (sheetPt e v (φ v)) := by
  rw [famFun_shearFam, add_zero]

/-! ## 3. The fibre part of a point of `ℝ^{m+N}` and the sheet parametrisation -/

/-- The fibre coordinates of a point of `ℝ^{m+N}`. -/
def sheetFib {m N : ℕ} (z : Fin (m + N) → ℝ) : Fin N → ℝ := fun j => z (Fin.natAdd m j)

/-- The fibre coordinates of `sheetPt e v u` are `(band part of v, u)` reindexed by `e`. -/
@[simp] theorem sheetFib_sheetPt {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u : Fin n2 → ℝ) :
    sheetFib (sheetPt e v u) =
      (fun j : Fin N => (Fin.append (fun k : Fin n1 => v (Fin.natAdd m k)) u) (e j)) := by
  funext j
  simp only [sheetFib, sheetPt_natAdd]

/-- Two sheet points with the same parameter differ only in the fibre block, so their distance is
bounded by the distance of the fibre values. -/
theorem dist_sheetPt_le {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    (v : Fin (m + n1) → ℝ) (u u' : Fin n2 → ℝ) :
    dist (sheetPt e v u) (sheetPt e v u') ≤ dist u u' := by
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  refine Fin.addCases (m := m) (n := N)
    (motive := fun j => dist (sheetPt e v u j) (sheetPt e v u' j) ≤ dist u u') ?_ ?_ j
  · intro i
    rw [sheetPt_castAdd, sheetPt_castAdd, dist_self]
    exact dist_nonneg
  · intro k
    rw [sheetPt_natAdd, sheetPt_natAdd]
    refine Fin.addCases (m := n1) (n := n2)
      (motive := fun x => dist
        ((Fin.append (fun k' : Fin n1 => v (Fin.natAdd m k')) u) x)
        ((Fin.append (fun k' : Fin n1 => v (Fin.natAdd m k')) u') x) ≤ dist u u') ?_ ?_ (e k)
    · intro i
      rw [Fin.append_left, Fin.append_left, dist_self]
      exact dist_nonneg
    · intro i
      rw [Fin.append_right, Fin.append_right]
      simpa only [dist_eq_norm, Pi.sub_apply] using norm_le_pi_norm (u - u') i

/-- The sheet parametrisation `v ↦ sheetPt e v (φ v)` is continuous wherever `φ` is. -/
theorem continuousAt_sheetPt_comp {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    {φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)} {V : Set (Fin (m + n1) → ℝ)}
    (hV : IsOpen V) (hφ : ContinuousOn φ V) {v₀ : Fin (m + n1) → ℝ} (hv₀ : v₀ ∈ V) :
    ContinuousAt (fun v => sheetPt e v (φ v)) v₀ := by
  change ContinuousAt ((fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPt e p.1 p.2) ∘
    fun v : Fin (m + n1) → ℝ => (v, φ v)) v₀
  exact (continuous_sheetPt e).continuousAt.comp
    (ContinuousAt.prodMk continuousAt_id (hφ.continuousAt (hV.mem_nhds hv₀)))

/-- The *shifted* sheet parametrisation `(v,u) ↦ sheetPt e v (φ v + u)` is continuous at
`(v₀, 0)`. -/
theorem continuousAt_sheetPt_shift {m n1 n2 N : ℕ} (e : Fin N ≃ Fin (n1 + n2))
    {φ : (Fin (m + n1) → ℝ) → (Fin n2 → ℝ)} {V : Set (Fin (m + n1) → ℝ)}
    (hV : IsOpen V) (hφ : ContinuousOn φ V) {v₀ : Fin (m + n1) → ℝ} (hv₀ : v₀ ∈ V) :
    ContinuousAt (fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPt e p.1 (φ p.1 + p.2))
      (v₀, 0) := by
  change ContinuousAt ((fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => sheetPt e p.1 p.2) ∘
    fun p : (Fin (m + n1) → ℝ) × (Fin n2 → ℝ) => (p.1, φ p.1 + p.2)) (v₀, 0)
  exact (continuous_sheetPt e).continuousAt.comp
    (ContinuousAt.prodMk continuous_fst.continuousAt
      (((hφ.continuousAt (hV.mem_nhds hv₀)).comp continuous_fst.continuousAt).add
        continuous_snd.continuousAt))

end Work.WilCrux
