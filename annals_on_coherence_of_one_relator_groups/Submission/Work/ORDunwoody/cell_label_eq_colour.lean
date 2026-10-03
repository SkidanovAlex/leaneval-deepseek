import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Pattern

universe u

namespace Work.ORDunwoody

open scoped Sym2

namespace Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
variable {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}

/-- **The colour of a position along a generator edge.**  The colour `φ` of the `i`-th vertex of
the subdivided generator edge `(j,true)` based at `c` is the `i`-th vertex of the geodesic of that
generator, translated by `c`.  (Only positions `0 ≤ i ≤ L (j,true)` are meaningful; there the
`i`-th vertex of `Λ''` is an old vertex and not the collapsed endpoint.) -/
private theorem colour_pos (D : GeoData T t₀ P) (c : G) (j : Fin P.n) {i : ℕ}
    (h : i ≤ D.L (j, true)) :
    colour D (pos D c j i) = c • D.geo (j, true) ⟨i, by omega⟩ := by
  rcases i with _ | m
  · rw [pos_zero, colour_base]
    congr 1
    rw [show (⟨0, by omega⟩ : Fin (D.L (j, true) + 1)) = 0 from Fin.ext rfl, D.geo_zero]
  · rcases lt_or_eq_of_le h with hlt | heq
    · rw [pos_succ_of_lt D c j hlt, colour_inner]
    · rw [pos_succ_of_not_lt D c j (by omega), colour_base, mul_smul]
      congr 1
      rw [show (⟨m + 1, by omega⟩ : Fin (D.L (j, true) + 1)) = Fin.last (D.L (j, true))
        from Fin.ext heq, D.geo_last]

end Dunwoody

theorem cell_label_eq_colour {G : Type u} [Group G] {V : Type u} [MulAction G V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (e : Work.ORDunwoody.Dunwoody.Cell D) : e.label = s(Work.ORDunwoody.Dunwoody.colour D e.src, Work.ORDunwoody.Dunwoody.colour D e.tgt) := by
  have h1 := Dunwoody.colour_pos D e.c e.j (le_of_lt e.k.isLt)
  have h2 := Dunwoody.colour_pos D e.c e.j (show (e.k : ℕ) + 1 ≤ D.L (e.j, true) by
    have := e.k.isLt; omega)
  simp only [Dunwoody.Cell.label, Dunwoody.Cell.src, Dunwoody.Cell.tgt, h1, h2]

end Work.ORDunwoody
