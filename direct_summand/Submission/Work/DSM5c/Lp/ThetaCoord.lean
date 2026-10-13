import Mathlib
import Submission.Work.DSM5c.Lp.ChartCmpMap
import Submission.Work.DSM5c.Lp.almostAcyc_chartLpR
import Submission.Work.DSM5b.CechIsoDefs

/-!
# DSM5c/Lp — coordinates of the chart Čech complexes and the transport map `Θ`

The transport of the characteristic-`p` input from the tilt `W♭ = PreTilt W p` to `W`
(`Submission/Work/DSM5c/Lp/NOTES_transport.md`, step (A)) compares the two "mod-`p`" chart
complexes

* `KQ = Č(chartLQ …)`, the Čech complex of `S ↦ D_S ⧸ (p) · ⊤` over `W`, and
* `Kp = Č(chartLpR …)`, the Čech complex of `S ↦ R_S ⧸ (φ_S(ϖ♭)^p)` over the tilt `W♭`,

whose terms have *different rings of scalars* but the *same* underlying sets: the comparison
`Work.DSM5c.Lp.chartCmpMap S` is the `0`-th Witt coordinate `D_S ⧸ (p) → R_S ⧸ (φ_S(ϖ♭)^p)` (PB2).
Hence the transport is an *elementwise* operation, not a map of complexes.

This file fixes the clockwork:

* `Work.DSM5c.Lp.cechFam` — the family whose product is the degree-`q` term of the Čech complex;
* `Work.DSM5c.Lp.cechComplex_d_π_apply` — the component formula for the Čech differential at the
  level of elements (from `Work.DSM5b.cech_d_comp_π_gen`);
* `Work.DSM5c.Lp.cech_map_π_apply` — the component formula for the chain map of a natural
  transformation (from `Work.DSM5c.Lp.cech_map_f`);
* `Work.DSM5c.Lp.Theta` — the degree-`q` component `Θ_q : KQ.X q → Kp.X q`, defined through the
  componentwise comparison, together with its component formula `Theta_π`, its values on `0`, and
  its injectivity and surjectivity.

The differential compatibility, the vector match and the coaugmentation identity are proved in
companion modules; the assembly is `Submission/Work/DSM5c/Lp/almostAcyc_chartLQ.lean`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option allowUnsafeReducibility true
set_option backward.isDefEq.respectTransparency false

attribute [local reducible] Work.DSM5c.chartTiltGen Work.DSM5c.tiltChart
  Work.DSM5c.Lp.chartLpRObj Work.DSM5c.Lp.chartLpROfHom
  DSMap.Mix2.perfChartRing DSMap.Mix2.perfChartPresheaf DSMap.Mix2.locPresheaf
  Work.DSM5c.Lp.chartLQObj Work.DSM5c.Lp.chartLQOfHom Work.DSM5c.Lp.chartLQEta
  Work.DSM5c.Lp.chartCmpLinear Work.DSM5c.Lp.chartDpTop

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite
open scoped Simplicial

universe a

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [Finite ι] [DecidableEq ι]

/-! ## The coordinates of the Čech complex -/

/-- The family of presheaf values whose product is the degree-`q` term of the Čech complex. -/
noncomputable abbrev cechFam (P : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (q : ℕ) :
    (Fin (q + 1) → ι) → ModuleCat.{a} W :=
  fun y => P.obj (cechIdx (ι := ι) q y)

/-- **Component formula for the Čech differential**, at the level of elements: the `y`-component of
`d q (q+1) z` is the alternating sum of the restrictions of the components of `z` at the faces of
`y` (`Work.DSM5b.cech_d_comp_π_gen`). -/
theorem cechComplex_d_π_apply (P : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (q : ℕ)
    (z : ↥(((cechComplexFunctor (chartIdx ι)).obj P).X q)) (y : Fin (q + 2) → ι) :
    (Pi.π (cechFam (ι := ι) P (q + 1)) y).hom
        ((((cechComplexFunctor (chartIdx ι)).obj P).d q (q + 1)).hom z) =
      ∑ b : Fin (q + 2), (-1 : ℤ) ^ (b : ℕ) •
        (P.map (((FormalCoproduct.mk ι (chartIdx ι)).cech.map
            (SimplexCategory.δ b).op).φ y).op).hom
          ((Pi.π (cechFam (ι := ι) P q)
            (((FormalCoproduct.mk ι (chartIdx ι)).cech.map
              (SimplexCategory.δ b).op).f y)).hom z) := by
  have h := Work.DSM5b.cech_d_comp_π_gen (chartIdx ι) P q y
  have h2 := congrArg (fun (m : ((cechComplexFunctor (chartIdx ι)).obj P).X q ⟶
      cechFam (ι := ι) P (q + 1) y) => m.hom z) h
  refine h2.trans ?_
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul]
  rfl

/-- **Component formula for the Čech chain map of a natural transformation**: the `y`-component of
`(Č φ).f q v` is the `y`-component of `φ` applied to the `y`-component of `v`. -/
theorem cech_map_π_apply {F G : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W} (φ : F ⟶ G) (q : ℕ)
    (v : ↥(((cechComplexFunctor (chartIdx ι)).obj F).X q)) (y : Fin (q + 1) → ι) :
    (Pi.π (cechFam (ι := ι) G q) y).hom
        ((((cechComplexFunctor (chartIdx ι)).map φ).f q).hom v) =
      (φ.app (cechIdx (ι := ι) q y)).hom ((Pi.π (cechFam (ι := ι) F q) y).hom v) := by
  rw [cech_map_f F G φ q]
  have h2 := congrArg (fun (m : (∏ᶜ cechFam (ι := ι) F q) ⟶
      G.obj (cechIdx (ι := ι) q y)) => m.hom v)
    (Pi.map_π (fun i : (Fin (q + 1) → ι) =>
      φ.app (op ((FormalCoproduct.power (FormalCoproduct.mk ι (chartIdx ι))
        (Fin (q + 1))).obj i))) y)
  rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at h2
  exact h2

/-- The product identification `ModuleCat.piIsoPi` is injective. -/
theorem ModuleCat_piIsoPi_injective {β : Type a} (Z : β → ModuleCat.{a} W) :
    Function.Injective (ModuleCat.piIsoPi Z).hom.hom :=
  (CategoryTheory.ConcreteCategory.bijective_of_isIso (ModuleCat.piIsoPi Z).hom).injective

/-- **Extensionality of a Čech term in terms of its components**, in the `cechFam` normal form used
by the component formulas. -/
theorem cech_pi_eq_iff {P : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W} {q : ℕ}
    {x y : ↥(((cechComplexFunctor (chartIdx ι)).obj P).X q)} :
    x = y ↔ ∀ j : Fin (q + 1) → ι,
      (Pi.π (cechFam (ι := ι) P q) j).hom x =
        (Pi.π (cechFam (ι := ι) P q) j).hom y := by
  constructor
  · intro h j
    rw [h]
  · intro h
    apply ModuleCat_piIsoPi_injective
    funext j
    rw [ModuleCat.piIsoPi_hom_ker_subtype_apply, ModuleCat.piIsoPi_hom_ker_subtype_apply]
    change (Pi.π (cechFam (ι := ι) P q) j).hom x =
      (Pi.π (cechFam (ι := ι) P q) j).hom y
    exact h j

/-! ## The transport `Θ` -/

section Main

variable (Q : DSMap.PerfectoidData p W)
  (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
  (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
  (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)

/-- **The degree-`q` component of the transport `Θ`**: the componentwise comparison
`chartCmpMap` read through the product identifications `ModuleCat.piIsoPi` of the two Čech terms. -/
noncomputable def Theta (q : ℕ)
    (z : ↥(((cechComplexFunctor (chartIdx ι)).obj
      (chartLQ Q hθ t tr htr0 htr j₀ e)).X q)) :
    ↥(((cechComplexFunctor (chartIdx ι)).obj
      (chartLpR Q t tr htr0 htr j₀ e)).X q) :=
  (ModuleCat.piIsoPi (cechFam (ι := ι) (chartLpR Q t tr htr0 htr j₀ e) q)).inv
    (fun y => chartCmpMap Q hθ t tr htr0 htr j₀ e ((cechIdx (ι := ι) q y).unop.unop)
      ((Pi.π (cechFam (ι := ι) (chartLQ Q hθ t tr htr0 htr j₀ e) q) y).hom z))

/-- The component formula for `Theta`: the `y`-component of `Θ_q z` is the comparison of the
`y`-component of `z`. -/
theorem Theta_π (q : ℕ)
    (z : ↥(((cechComplexFunctor (chartIdx ι)).obj
      (chartLQ Q hθ t tr htr0 htr j₀ e)).X q)) (y : Fin (q + 1) → ι) :
    (Pi.π (cechFam (ι := ι) (chartLpR Q t tr htr0 htr j₀ e) q) y).hom
        (Theta Q hθ t tr htr0 htr j₀ e q z) =
      chartCmpMap Q hθ t tr htr0 htr j₀ e ((cechIdx (ι := ι) q y).unop.unop)
        ((Pi.π (cechFam (ι := ι) (chartLQ Q hθ t tr htr0 htr j₀ e) q) y).hom z) := by
  rw [Theta]
  rw [ModuleCat.piIsoPi_inv_kernel_ι_apply]

/-- `Θ_q 0 = 0`. -/
theorem Theta_zero (q : ℕ) :
    Theta Q hθ t tr htr0 htr j₀ e q
      (0 : ↥(((cechComplexFunctor (chartIdx ι)).obj
        (chartLQ Q hθ t tr htr0 htr j₀ e)).X q)) = 0 := by
  refine (cech_pi_eq_iff).mpr fun y => ?_
  rw [Theta_π]
  simp only [map_zero]

/-- `Θ_q` is injective. -/
theorem Theta_injective (q : ℕ) : Function.Injective (Theta Q hθ t tr htr0 htr j₀ e q) := by
  intro a b hab
  refine (cech_pi_eq_iff).mpr fun y => ?_
  have h1 := congrArg (fun u =>
    (Pi.π (cechFam (ι := ι) (chartLpR Q t tr htr0 htr j₀ e) q) y).hom u) hab
  rw [Theta_π, Theta_π] at h1
  exact chartCmpMap_injective Q hθ t tr htr0 htr j₀ e ((cechIdx (ι := ι) q y).unop.unop) h1

/-- `Θ_q` is surjective. -/
theorem Theta_surjective (q : ℕ) : Function.Surjective (Theta Q hθ t tr htr0 htr j₀ e q) := by
  intro w
  choose x hx using fun y : Fin (q + 1) → ι =>
    chartCmpMap_surjective Q hθ t tr htr0 htr j₀ e ((cechIdx (ι := ι) q y).unop.unop)
      ((Pi.π (cechFam (ι := ι) (chartLpR Q t tr htr0 htr j₀ e) q) y).hom w)
  refine ⟨(ModuleCat.piIsoPi (cechFam (ι := ι)
    (chartLQ Q hθ t tr htr0 htr j₀ e) q)).inv x, ?_⟩
  refine (cech_pi_eq_iff).mpr fun y => ?_
  rw [Theta_π, ModuleCat.piIsoPi_inv_kernel_ι_apply, hx]

end Main

end Work.DSM5c.Lp
