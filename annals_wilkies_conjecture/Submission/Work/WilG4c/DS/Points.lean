/-
  `Work.WilG4c.DS.Points`: elementary point-level helpers for the coordinate splitting
  `ℝ^{m+N} = ℝ^m × ℝ^N` used by `Work.WilG4c.DefinableSection`.

  A point of `ℝ^{m+N}` is written as `Fin.append w y` with `w : Fin m → ℝ` the *parameter*
  and `y : Fin N → ℝ` the *fibre* point.  The projection onto the first `m` coordinates is
  `projFirst m N` and the complementary projection is `fibTail m N`.
-/
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c.DS

/-! ## `Fin.init` and `Fin.append` -/

/-- `Fin.init`, unfolded: dropping the last coordinate. -/
lemma init_apply {n : ℕ} (z : Fin (n + 1) → ℝ) (i : Fin n) : Fin.init z i = z i.castSucc :=
  rfl

/-- Dropping the last coordinate commutes with `Fin.append`. -/
lemma init_append (m N : ℕ) (w : Fin m → ℝ) (y : Fin (N + 1) → ℝ) :
    Fin.init (Fin.append (n := N + 1) w y) = Fin.append (n := N) w (Fin.init y) := by
  funext i
  change Fin.append w y i.castSucc = Fin.append w (Fin.init y) i
  cases i using Fin.addCases with
  | left j => rw [Fin.castSucc_castAdd, Fin.append_left, Fin.append_left]
  | right j => rw [← Fin.natAdd_castSucc, Fin.append_right, Fin.append_right, init_apply]

/-- Dropping the last coordinate of `Fin.append w (Fin.snoc p t)`. -/
lemma init_append_snoc (m N : ℕ) (w : Fin m → ℝ) (p : Fin N → ℝ) (t : ℝ) :
    Fin.init (Fin.append (n := N + 1) w (Fin.snoc p t)) = Fin.append (n := N) w p := by
  funext i
  change Fin.append w (Fin.snoc p t) i.castSucc = Fin.append w p i
  cases i using Fin.addCases with
  | left j => rw [Fin.castSucc_castAdd, Fin.append_left, Fin.append_left]
  | right j =>
      rw [← Fin.natAdd_castSucc, Fin.append_right, Fin.snoc_castSucc, Fin.append_right]

/-- The last coordinate of `Fin.append w (Fin.snoc p t)`. -/
lemma append_snoc_last (m N : ℕ) (w : Fin m → ℝ) (p : Fin N → ℝ) (t : ℝ) :
    Fin.append (n := N + 1) w (Fin.snoc p t) (Fin.last (m + N)) = t := by
  have h : Fin.last (m + N) = Fin.natAdd m (Fin.last N) :=
    (Fin.natAdd_last (m := N) (n := m)).symm
  rw [h, Fin.append_right, Fin.snoc_last]

/-- `Fin.append` with an empty fibre is the parameter itself (the two types are identified
by the definitional equality `m + 0 = m`). -/
lemma append_fin_zero (m : ℕ) (w : Fin m → ℝ) (y : Fin 0 → ℝ) :
    Fin.append (n := 0) w y = w := by
  funext i
  exact Fin.append_left w y i

/-! ## The two projections -/

/-- The projection of `ℝ^{m+N}` onto its first `m` coordinates. -/
def projFirst (m N : ℕ) (z : Fin (m + N) → ℝ) : Fin m → ℝ := fun i => z (Fin.castAdd N i)

/-- The projection of `ℝ^{m+N}` onto its last `N` coordinates. -/
def fibTail (m N : ℕ) (z : Fin (m + N) → ℝ) : Fin N → ℝ := fun j => z (Fin.natAdd m j)

lemma projFirst_append (m N : ℕ) (w : Fin m → ℝ) (y : Fin N → ℝ) :
    projFirst m N (Fin.append w y) = w := by
  funext i
  exact Fin.append_left w y i

lemma fibTail_append (m N : ℕ) (w : Fin m → ℝ) (y : Fin N → ℝ) :
    fibTail m N (Fin.append w y) = y := by
  funext j
  exact Fin.append_right w y j

/-- Every point is the gluing of its two projections. -/
lemma append_projFirst_fibTail (m N : ℕ) (z : Fin (m + N) → ℝ) :
    Fin.append (projFirst m N z) (fibTail m N z) = z := by
  funext i
  cases i using Fin.addCases with
  | left j => rw [Fin.append_left]; rfl
  | right j => rw [Fin.append_right]; rfl

/-- Membership in a projection, unfolded: the fibre over `w` is nonempty. -/
lemma mem_projFirst_image {m N : ℕ} (κ : Set (Fin (m + N) → ℝ)) (w : Fin m → ℝ) :
    w ∈ projFirst m N '' κ ↔ ∃ y : Fin N → ℝ, Fin.append w y ∈ κ := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨fibTail m N z, by rw [append_projFirst_fibTail m N z]; exact hz⟩
  · rintro ⟨y, hy⟩
    exact ⟨Fin.append w y, hy, projFirst_append m N w y⟩

/-- Dropping the last coordinate followed by the projection to the first `m` coordinates. -/
lemma projFirst_init (m N : ℕ) (z : Fin (m + (N + 1)) → ℝ) :
    projFirst m (N + 1) z = projFirst m N (Fin.init z) := by
  funext i
  show z (Fin.castAdd (N + 1) i) = (Fin.init z) (Fin.castAdd N i)
  rw [init_apply, Fin.castSucc_castAdd]

/-- The projection to the first `m` coordinates with no fibre coordinate is the identity. -/
lemma projFirst_zero (m : ℕ) (z : Fin (m + 0) → ℝ) : projFirst m 0 z = z := by
  funext i
  exact congrArg z (Fin.ext rfl)

lemma projFirst_zero_image (m : ℕ) (s : Set (Fin (m + 0) → ℝ)) :
    projFirst m 0 '' s = s := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [projFirst_zero m z]
  · intro hw
    exact ⟨w, hw, projFirst_zero m w⟩

lemma projFirst_zero_image_finset (m : ℕ) (C : Finset (Set (Fin (m + 0) → ℝ))) :
    C.image (fun c => projFirst m 0 '' c) = C := by
  rw [Finset.image_congr (f := fun c => projFirst m 0 '' c) (g := fun c => c)
    (fun c _ => projFirst_zero_image m c)]
  exact Finset.image_id

/-- The projection of a set commutes with dropping the last coordinate. -/
lemma projFirst_image_init {m N : ℕ} (κ : Set (Fin (m + (N + 1)) → ℝ)) :
    projFirst m (N + 1) '' κ = projFirst m N '' (Fin.init '' κ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨Fin.init z, ⟨z, hz, rfl⟩, (projFirst_init m N z).symm⟩
  · rintro ⟨z', ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, projFirst_init m N z⟩

end Work.WilG4c.DS
