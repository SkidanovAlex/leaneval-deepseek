import Mathlib
import Submission.Work.LT.Defs

/-! **Vertex cover for the quadripartite left–right Cayley complex.**

The code `lrCode A B CA CB` asks that the local view of the word at *every* vertex of the
quadripartite complex lie in the tensor code `tensorCode CA CB`.  The type-`00` vertices and the
type-`11` vertices already form a vertex cover of the complex: every edge of the complex (an
`A`-edge or a `B`-edge) has at least one endpoint of type `00` or `11`.  Consequently the views at
the type-`10` vertices and at the type-`01` vertices are *forced*:

* the row `i` of the type-`10` view at `g` is the row `i` of the type-`00` view at `(A i)⁻¹ g`
  (the two endpoints of the `A`-edge of label `i` agree on row `i`), and its column `j` is the
  column `j` of the type-`11` view at `g B j` (the two endpoints of the `B`-edge of label `j`
  agree on column `j`);
* symmetrically, the row `i` of the type-`01` view at `g` is the row `i` of the type-`11` view at
  `A i * g`, and its column `j` is the column `j` of the type-`00` view at `g (B j)⁻¹`.

This is the "vertex cover" step (DELLM Lemma 4.3, bipartite case) used to compute the rate of the
code: `lrCode A B CA CB = (⨅ g, comap (lrView 0 0 g)) ⊓ (⨅ g, comap (lrView 1 1 g))`.
-/

namespace Work.LT

open Classical

namespace CoverLe

/-- Membership in the tensor code `CA ⊗ CB`, unfolded into its row and column conditions: every
row (fixed first index) lies in `CB` and every column (fixed second index) lies in `CA`. -/
lemma mem_tensorCode {Δ : ℕ} {CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)}
    {w : Fin Δ × Fin Δ → ZMod 2} :
    w ∈ tensorCode CA CB ↔
      (∀ i, (fun j => w (i, j)) ∈ CB) ∧ (∀ j, (fun i => w (i, j)) ∈ CA) := by
  have hrow : ∀ i : Fin Δ,
      (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun j : Fin Δ => (i, j))) w = fun j => w (i, j) :=
    fun i => by funext j; simp [LinearMap.funLeft_apply]
  have hcol : ∀ j : Fin Δ,
      (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin Δ => (i, j))) w = fun i => w (i, j) :=
    fun j => by funext i; simp [LinearMap.funLeft_apply]
  simp only [tensorCode, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_inf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by rw [← hrow i]; exact h1 i, fun j => by rw [← hcol j]; exact h2 j⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => by rw [hrow i]; exact h1 i, fun j => by rw [hcol j]; exact h2 j⟩

/-- Row `i` of the type-`10` view at `g` is row `i` of the type-`00` view at `(A i)⁻¹ * g`:
both are computed on the `A`-edge of label `i` through `(A i)⁻¹ * g`. -/
lemma row_one_zero {G : Type} [Group G] {Δ : ℕ} (A B : Fin Δ → G) (g : G) (i : Fin Δ)
    (f : G × Fin Δ × Fin Δ → ZMod 2) :
    (fun j => lrView A B 1 0 g f (i, j)) = (fun j => lrView A B 0 0 ((A i)⁻¹ * g) f (i, j)) := by
  funext j; simp only [lrView, LinearMap.funLeft_apply, lrSq]; simp

/-- Row `i` of the type-`01` view at `g` is row `i` of the type-`11` view at `A i * g`. -/
lemma row_zero_one {G : Type} [Group G] {Δ : ℕ} (A B : Fin Δ → G) (g : G) (i : Fin Δ)
    (f : G × Fin Δ × Fin Δ → ZMod 2) :
    (fun j => lrView A B 0 1 g f (i, j)) = (fun j => lrView A B 1 1 (A i * g) f (i, j)) := by
  funext j; simp only [lrView, LinearMap.funLeft_apply, lrSq]; simp

/-- Column `j` of the type-`10` view at `g` is column `j` of the type-`11` view at `g * B j`. -/
lemma col_one_zero {G : Type} [Group G] {Δ : ℕ} (A B : Fin Δ → G) (g : G) (j : Fin Δ)
    (f : G × Fin Δ × Fin Δ → ZMod 2) :
    (fun i => lrView A B 1 0 g f (i, j)) = (fun i => lrView A B 1 1 (g * B j) f (i, j)) := by
  funext i; simp only [lrView, LinearMap.funLeft_apply, lrSq]; simp [mul_assoc]

/-- Column `j` of the type-`01` view at `g` is column `j` of the type-`00` view at `g * (B j)⁻¹`. -/
lemma col_zero_one {G : Type} [Group G] {Δ : ℕ} (A B : Fin Δ → G) (g : G) (j : Fin Δ)
    (f : G × Fin Δ × Fin Δ → ZMod 2) :
    (fun i => lrView A B 0 1 g f (i, j)) = (fun i => lrView A B 0 0 (g * (B j)⁻¹) f (i, j)) := by
  funext i; simp only [lrView, LinearMap.funLeft_apply, lrSq]; simp

end CoverLe

/-- **Vertex cover**. The constraints at the type-00 vertices and at the type-11 vertices of the
quadripartite complex imply the constraints at all vertices: sitting in the intersection over `g`
of the type-00 constraints and over `g` of the type-11 constraints forces every view (also of
types 10 and 01) into `tensorCode CA CB`. -/
lemma cover_le_lrCode {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) :
    ((⨅ g : G, (tensorCode CA CB).comap (lrView A B 0 0 g)) ⊓
      (⨅ g : G, (tensorCode CA CB).comap (lrView A B 1 1 g)) :
        Submodule (ZMod 2) (G × Fin Δ × Fin Δ → ZMod 2)) ≤ lrCode A B CA CB := by
  intro f hf
  -- Unpack the two families of constraints at the type-`00` and type-`11` vertices.
  rw [Submodule.mem_inf] at hf
  obtain ⟨h00, h11⟩ := hf
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at h00 h11
  -- It suffices to check every view.
  simp only [lrCode, Submodule.mem_iInf, Submodule.mem_comap]
  intro α β g
  rw [CoverLe.mem_tensorCode]
  refine ⟨fun i => ?_, fun j => ?_⟩
  · -- row `i` of the view, according to the type of the view in the `B`-direction
    by_cases hβ : β = 1
    · subst hβ
      by_cases hα : α = 1
      · subst hα
        exact (CoverLe.mem_tensorCode.mp (h11 g)).1 i
      · have hα0 : α = 0 := by fin_cases α <;> simp_all
        subst hα0
        rw [CoverLe.row_zero_one A B g i f]
        exact (CoverLe.mem_tensorCode.mp (h11 (A i * g))).1 i
    · have hβ0 : β = 0 := by fin_cases β <;> simp_all
      subst hβ0
      by_cases hα : α = 1
      · subst hα
        rw [CoverLe.row_one_zero A B g i f]
        exact (CoverLe.mem_tensorCode.mp (h00 ((A i)⁻¹ * g))).1 i
      · have hα0 : α = 0 := by fin_cases α <;> simp_all
        subst hα0
        exact (CoverLe.mem_tensorCode.mp (h00 g)).1 i
  · -- column `j` of the view, according to the type of the view in the `A`-direction
    by_cases hα : α = 1
    · subst hα
      by_cases hβ : β = 1
      · subst hβ
        exact (CoverLe.mem_tensorCode.mp (h11 g)).2 j
      · have hβ0 : β = 0 := by fin_cases β <;> simp_all
        subst hβ0
        rw [CoverLe.col_one_zero A B g j f]
        exact (CoverLe.mem_tensorCode.mp (h11 (g * B j))).2 j
    · have hα0 : α = 0 := by fin_cases α <;> simp_all
      subst hα0
      by_cases hβ : β = 1
      · subst hβ
        rw [CoverLe.col_zero_one A B g j f]
        exact (CoverLe.mem_tensorCode.mp (h00 (g * (B j)⁻¹))).2 j
      · have hβ0 : β = 0 := by fin_cases β <;> simp_all
        subst hβ0
        exact (CoverLe.mem_tensorCode.mp (h00 g)).2 j

end Work.LT
