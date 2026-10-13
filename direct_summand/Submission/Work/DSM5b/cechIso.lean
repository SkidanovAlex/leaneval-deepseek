import Mathlib
import Submission.Work.DSM5b.PerfComplexDefs
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.Basic
import Submission.Work.DSF1.Cech.CechComponents
import Submission.Work.DSM5b.CechIsoDefs

namespace Work.DSM5b

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
universe a

namespace Work.DSM5b

/-- **The perfected chart Čech complex in coordinates.**

`K = (cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)` is the (non-normalised,
alternating coface) Čech complex of the perfected blowup charts of `Spec R` along `J = (t_i)`
(`R` perfect of characteristic `p`, `t : ι → R` finite).  Its terms are
`K.X m = ∏ᶜ (fun τ : Fin (m+1) → ι => P (op (∏ᶜ_a (op {τ a}))))`, the product over all
`(m+1)`-tuples of the value of `P = perfChartPresheaf p t` at the product (in the thin category
`(Finset ι)ᵒᵖ`) of the objects `op {τ a}`.

The conclusion identifies `K`, degree by degree, with the explicit complex
`PCX p t m = ∀ τ : Fin (m+1) → ι, perfChartRing p t (tupRng τ)`
(`tupRng τ = Finset.univ.image τ`, the set of values of the tuple), and identifies `K.d m (m+1)`
with `PCd p t m`, whose `τ`-component is
`∑ i : Fin (m+2), (-1)^i • rho (z (tupDel i τ))`,  `tupDel i τ = τ ∘ Fin.succAbove i`
(the tuple with the `i`-th entry deleted), where
`rho p t h : perfChartRing p t S →ₐ[R] perfChartRing p t T` is the localisation map `locRes t h` of
perfected chart rings, for `h : S ⊆ T`.

Useful already-proven input: `Work.DSF1.Cech.cechComplexFunctor_d_π` (in
`Submission/Work/DSF1/Cech/CechComponents.lean`) computes the components of the differential of
Mathlib's `cechComplexFunctor` as `∑ a, (-1)^a • (Pi.π ≫ P.map ((cech.map (δ a).op).φ x).op)`.

Proof route: unfold `cechComplexFunctor` (`FormalCoproduct.cochainComplexFunctor`,
`cosimplicialObjectFunctor`, `FormalCoproduct.evalOp`, `FormalCoproduct.cech`,
`AlternatingCofaceMapComplex.obj`/`objD`); identify the product in `(Finset ι)ᵒᵖ` of the `op {τ a}`
with `op (tupRng τ)` (in a thin category, two objects with maps both ways are isomorphic; one map
comes from `Pi.π`, the other from the universal property of the product using `{τ a} ⊆ tupRng τ`);
identify `evalOp`'s `map` on `mapPower`-morphisms with the presheaf map `rho`; use
`CosimplicialObject.δ i = X.map (SimplexCategory.δ i)` with `SimplexCategory.δ i = Fin.succAbove i`
and `objD X n = ∑ i, (-1)^i • X.δ i`.

Do NOT use the frozen sorried declaration `DSMap.Mix2.area_M5b`. -/
theorem cechIso (p : ℕ) [Fact p.Prime] {R : Type a} [CommRing R] [CharP R p] [PerfectRing R p]
    {ι : Type a} [Finite ι] [DecidableEq ι] (t : ι → R) :
    ∃ e : ∀ m, ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).X m ≅
        ModuleCat.of R (PCX p t m),
      ∀ (m : ℕ) (z : ((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).X m),
        (e (m + 1)).hom
            (((cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)).d m (m + 1) z)
          = ModuleCat.ofHom (PCd p t m) ((e m).hom z) := by
  refine ⟨fun m => coordIso p t m, ?_⟩
  intro m z
  exact coordIso_comm p t m z

end Work.DSM5b

/-- The same statement under the (single-namespace) name of this module, so that it can be used as
`Work.DSM5b.cechIso`. -/
alias cechIso := _root_.Work.DSM5b.Work.DSM5b.cechIso
