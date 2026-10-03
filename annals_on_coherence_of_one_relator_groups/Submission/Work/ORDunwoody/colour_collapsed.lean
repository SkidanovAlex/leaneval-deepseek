import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Pattern

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley

/-- If the geodesic of a generator-with-sign `x` has length `0`, then the geodesic from `t₀` to
`genE P x • t₀` is trivial, so `genE P x` fixes the basepoint `t₀`. -/
theorem genE_smul_eq_self_of_L_eq_zero {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (x : Fin P.n × Bool) (h : D.L x = 0) :
    CayV.genE P x • t₀ = t₀ := by
  have hidx : (Fin.last (D.L x) : Fin (D.L x + 1)) = 0 := by
    apply Fin.ext
    simp only [Fin.val_last, Fin.val_zero]
    exact h
  exact (D.geo_last x).symm.trans ((congrArg (D.geo x) hidx).trans (D.geo_zero x))

/-- **A collapse of a generator edge does not move the colour.**  If the generator edge
`(j, true)` of the presentation is collapsed by the map `φ` (its geodesic in `T` has length `0`),
then the generator `genE P (j, true)` fixes `t₀`, hence multiplying a group element `a` on the
right by it does not change the colour of the old vertex `(a, ∗)`. -/
theorem colour_collapsed {G : Type u} [Group G] {V : Type u} [MulAction G V] {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G} {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n) (h : D.L (j, true) = 0) : Work.ORDunwoody.Dunwoody.colour D (a, Sum.inl ()) = Work.ORDunwoody.Dunwoody.colour D (a * Work.ORDunwoody.Cayley.CayV.genE P (j, true), Sum.inl ()) := by
  have hfix : CayV.genE P (j, true) • t₀ = t₀ :=
    genE_smul_eq_self_of_L_eq_zero (D := D) (j, true) h
  rw [Work.ORDunwoody.Dunwoody.colour_base, Work.ORDunwoody.Dunwoody.colour_base, mul_smul, hfix]

end Work.ORDunwoody
