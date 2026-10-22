import Submission.Work.ANALYTIC.CechPt.LevelAux

/-!
# Plumbing for the acyclicity of the level-`n` dyadic nerve

Elementary lemmas used in the induction proving `Work.ANALYTIC.CechPt.level_acyclic`:
linearity of `diff`, naturality of `diff` under the coordinatewise inclusion `inclS` and
retraction `retrS` (and their round-trip identities), the description of vertices, and the
alternating-sum computation used in the base case `M = 1`.
-/

namespace Work.ANALYTIC.CechPt.Level

/-- The assertion of `level_acyclic` at a fixed level `M`. -/
def level_acyclic_prop (M : ℕ) : Prop :=
  (∀ (p : ℕ) (f : lev M (p + 1) → ℤ), diff f = 0 → ∃ g : lev M p → ℤ, diff g = f) ∧
  (∀ f : lev M 0 → ℤ, diff f = 0 → ∃ c : ℤ, f = fun _ => c)

theorem diff_sub {M p : ℕ} (f g : lev M p → ℤ) :
    diff (fun x => f x - g x) = fun x => diff f x - diff g x := by
  funext x
  simp only [diff]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diff_add {M p : ℕ} (f g : lev M p → ℤ) :
    diff (fun x => f x + g x) = fun x => diff f x + diff g x := by
  funext x
  simp only [diff]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem diff_zero {M p : ℕ} : diff (fun _ : lev M p => (0 : ℤ)) = 0 := by
  funext x
  simp only [diff]
  simp

/-! ## Naturality of `diff` under the coordinatewise maps -/

theorem face_inclS {M p : ℕ} (x : lev (M + 1) (p + 1)) (i : Fin (p + 2)) :
    face i (inclS x) = inclS (face i x) := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  show ((inclS x).1 (Fin.succAbove i j) : ℕ) = ((inclS (face i x)).1 j : ℕ)
  rw [inclS_val, inclS_val]
  rfl

theorem face_retrS {M p : ℕ} (x : lev (M + 2) (p + 1)) (i : Fin (p + 2)) :
    face i (retrS x) = retrS (face i x) := by
  apply Subtype.ext
  funext j
  apply Fin.ext
  show ((retrS x).1 (Fin.succAbove i j) : ℕ) = ((retrS (face i x)).1 j : ℕ)
  rw [retrS_val, retrS_val]
  rfl

theorem diff_inclS {M p : ℕ} (F : lev (M + 2) p → ℤ) :
    diff (fun x => F (inclS x)) = fun x => diff F (inclS x) := by
  funext y
  simp only [diff]
  apply Finset.sum_congr rfl
  intro i _
  rw [face_inclS]

theorem diff_retrS {M p : ℕ} (F : lev (M + 1) p → ℤ) :
    diff (fun x => F (retrS x)) = fun x => diff F (retrS x) := by
  funext y
  simp only [diff]
  apply Finset.sum_congr rfl
  intro i _
  rw [face_retrS]

theorem retrS_inclS {M p : ℕ} (x : lev (M + 1) p) : retrS (inclS x) = x := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  have hle : ((x.1 i : Fin (M + 1)) : ℕ) ≤ M := by have := (x.1 i).isLt; omega
  simp only [retrS_val, inclS_val, Nat.min_eq_left hle]

theorem inclS_retrS {M p : ℕ} (z : lev (M + 2) p) : inclS (retrS z) = rhoS z := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  simp only [inclS_val, retrS_val, rhoS_val, rhoV]
  omega

/-! ## Vertices -/

/-- The vertex with value `k`. -/
def vtx (M : ℕ) (k : Fin M) : lev M 0 :=
  ⟨fun _ => k, by intro i j; simp only [Fin.le_def]; omega⟩

@[simp] theorem vtx_val (M : ℕ) (k : Fin M) (i : Fin 1) : ((vtx M k).1 i : ℕ) = (k : ℕ) := rfl

theorem rhoS_vtx {M : ℕ} (k : Fin M) : rhoS (vtx M k) = vtx M (rhoV M k) := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  show ((rhoS (vtx M k)).1 i : ℕ) = ((vtx M (rhoV M k)).1 i : ℕ)
  rw [rhoS_val]
  rfl

theorem vtx_eta {M : ℕ} (v : lev M 0) : v = vtx M (v.1 0) := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  show ((v.1 i : Fin M) : ℕ) = ((v.1 0 : Fin M) : ℕ)
  have hi : i = (0 : Fin 1) := Fin.ext (by have := i.isLt; omega)
  rw [hi]

end Work.ANALYTIC.CechPt.Level
