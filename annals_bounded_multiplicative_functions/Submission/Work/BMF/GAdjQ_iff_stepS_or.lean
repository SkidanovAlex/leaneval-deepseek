import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-! ## Auxiliary lemmas for `GAdjQ_iff_stepS_or`

The `q`-adjacency `GAdjQ D q x y` says that some edge of `D.edges` carries the prime `q` and has
`x`, `y` as endpoints (in either order).  The prime set `stepS D x y` of the step `x → y` is the
prime set of the *chosen* witnessing edge `stepWit D x y`.  The two descriptions agree because
(i) distinct edges of `D.edges` with the same ordered arc coincide (`edge_ext`), so the chosen
witness is the unique edge with that arc, and (ii) the junk witness `⟨0,0,0,0⟩` arising when no
arc exists is never in `D.edges`, since it carries `p₁ = 0`, which is not prime. -/

/-- `edgeS` is empty on edges outside `D.edges`. -/
lemma edgeS_eq_empty (D : QuadData k f c C X L P₁ P₂) {e : Edge} (h : e ∉ D.edges) :
    edgeS D e = ∅ := by
  classical
  unfold edgeS
  exact dif_neg h

/-- If `q` lies in the prime set of a step then the witnessing edge belongs to `D.edges`. -/
lemma stepWit_mem_of_mem_stepS (D : QuadData k f c C X L P₁ P₂) {q : ℕ} {x y : GVert D}
    (h : q ∈ stepS D x y) : stepWit D x y ∈ D.edges := by
  by_contra hnot
  rw [stepS_eq, edgeS_eq_empty D hnot] at h
  exact Finset.notMem_empty q h

/-- The chosen arc-witness of `(a, b)` has endpoints `a`, `b` whenever it is a genuine edge of
`D.edges`.  (When the arc does not exist the witness is the junk edge `⟨0,0,0,0⟩`, whose first
prime `0` violates `EdgeGeom`, so it is not in `D.edges`.) -/
lemma arcWit_spec_self (D : QuadData k f c C X L P₁ P₂) {a b : ℝ}
    (h : arcWit D a b ∈ D.edges) : (arcWit D a b).x₁ = a ∧ (arcWit D a b).x₂ = b := by
  classical
  by_cases hh : ∃ e ∈ D.edges, e.x₁ = a ∧ e.x₂ = b
  · rw [arcWit, dif_pos hh]
    exact (Classical.choose_spec hh).2
  · rw [arcWit, dif_neg hh] at h
    exact absurd (D.geom _ h).2.2.2.2.1.1 Nat.not_prime_zero

/-- Membership in the prime set of a step yields the corresponding `q`-adjacency. -/
lemma GAdjQ_of_mem_stepS (D : QuadData k f c C X L P₁ P₂) {q : ℕ} {x y : GVert D}
    (h : q ∈ stepS D x y) : GAdjQ D q x y := by
  classical
  have he : stepWit D x y ∈ D.edges := stepWit_mem_of_mem_stepS D h
  by_cases hf : stepFwd D x y
  · have he' : arcWit D x.1 y.1 ∈ D.edges := by rwa [stepWit_fwd D hf] at he
    obtain ⟨h1, h2⟩ := arcWit_spec_self D he'
    exact ⟨stepWit D x y, he, h, Or.inl ⟨by rw [stepWit_fwd D hf]; exact h1,
      by rw [stepWit_fwd D hf]; exact h2⟩⟩
  · have he' : arcWit D y.1 x.1 ∈ D.edges := by rwa [stepWit_rev D hf] at he
    obtain ⟨h1, h2⟩ := arcWit_spec_self D he'
    exact ⟨stepWit D x y, he, h, Or.inr ⟨by rw [stepWit_rev D hf]; exact h1,
      by rw [stepWit_rev D hf]; exact h2⟩⟩

theorem GAdjQ_iff_stepS_or {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂)
    (hP : 0 < P₁) (hL : 0 < L) (hbig : 8000 * P₁ ^ 2 < X / L)
    (x y : Work.BMF.GVert D) (q : ℕ) :
    Work.BMF.GAdjQ D q x y ↔ q ∈ Work.BMF.stepS D x y ∨ q ∈ Work.BMF.stepS D y x := by
  constructor
  · rintro ⟨e, he, hq, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · -- `e` runs forward `x → y`
      have hsf : stepFwd D x y := ⟨e, he, h1, h2⟩
      have hs := arcWit_spec D hsf
      have heq : arcWit D x.1 y.1 = e :=
        edge_ext D hP hL hbig hs.1 he (by rw [hs.2.1, h1]) (by rw [hs.2.2, h2])
      left
      rw [stepS_eq, stepWit_fwd D hsf, heq]
      exact hq
    · -- `e` runs forward `y → x`
      have hsf : stepFwd D y x := ⟨e, he, h1, h2⟩
      have hs := arcWit_spec D hsf
      have heq : arcWit D y.1 x.1 = e :=
        edge_ext D hP hL hbig hs.1 he (by rw [hs.2.1, h1]) (by rw [hs.2.2, h2])
      right
      rw [stepS_eq, stepWit_fwd D hsf, heq]
      exact hq
  · rintro (h | h)
    · exact GAdjQ_of_mem_stepS D h
    · exact (GAdjQ_symm D q y x).mp (GAdjQ_of_mem_stepS D h)

end Work.BMF
