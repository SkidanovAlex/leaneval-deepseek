import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5c.Basic
import Submission.Work.DSM5c.Untilt.Basic

/-!
# DSM5c — the perfectoid charts `D_S` as untilts of the completed perfected tilted charts

This file fixes the **vocabulary** of the chart layer of the M5c node
(`DSMap.Mix2.area_M5c`), following the design of
`sources/dsmap/direct_summand_mix_design.md` (M5c, PB3) and the corrections recorded in
`Submission/Work/DSM5c/NOTES.md` §§4, 9.

Let `W` be perfectoid (`Q : DSMap.PerfectoidData p W`), `t : ι → W` a finite family with a
compatible system of `p`-power roots `tr` (`tr i 0 = t i`, `tr i (k+1) ^ p = tr i k`), and
`t j₀ = Q.ϖ 0 ^ e`.

## The tilted charts

The characteristic-`p` input `area_M5b` lives on the tilt `W♭ = PreTilt W p`.  Two normalisations
matter:

* the tilted generator at `j₀` is taken to be the **`♯`-element** `(ϖ♭) ^ e` rather than the tilt
  of the given tower `tr j₀`: this is legitimate because `♯ ((ϖ♭) ^ e) = ϖ₀ ^ e = t j₀`
  (`DSMap.Mix.perfectoid_varpiFlat_proved`), so the tilted chart still tilts the honest chart, and
  it removes the "arbitrary root tower" obstruction of `NOTES.md` §4: with `t♭ j₀ = (ϖ♭) ^ e`
  `area_M5b` applies with `T := ϖ♭`, so the almost-vector is transported to the frozen
  statement's vector `Q.ϖ` **exactly** (no change of almost-vector is needed);
* for `i ≠ j₀` the tilted generator is the tilt `Work.DSM5c.tiltGens … i` of the given tower
  (`♯ (t♭ i) = t i`).

`chartTiltGen` is the resulting family; `tiltChart` is its perfection
(`DSMap.Mix2.perfChartRing`) inside the localisation `(W♭)_{t_S}`, and `tiltChartHat` is its
`ϖ♭`-adic completion — the "completed perfected tilted chart" of the design.

## The untilt functor

The design's untilt functor is

`untilt (R) := 𝕎(R) ⊗_{𝕎(W♭)} W = 𝕎(R) / (image of ker θ_W)`

(`sources/dsmap/direct_summand_mix_design.md`: *"Use untilt(R) := W(R) ⊗_{W(C♭)} C = W(R)/ξ"*),
where `θ_W : 𝕎 W♭ → W` is Mathlib's `WittVector.fontaineTheta`.  Writing the charts this way — with
the **ideal** `ker θ_W` in place of a chosen generator `ξ` — makes

* the `W`-algebra structure `W = 𝕎W♭ ⧸ ker θ_W ⟶ 𝕎R ⧸ (image of ker θ_W)` *tautological*, and
* the mod-`p` comparison `D_S ⧸ (p) ≅ R̂_S ⧸ (ϖ♭) ^ p` depend only on the **mod-`p`** description of
  `ker θ_W`, i.e. on `PB2` (`DSMap.Mix.perfectoid_modp_tilt_proved`, proved in
  `Submission/Work/DSPB2`), rather than on the principality of `ker θ_W`.

This is why `NOTES.md` §9's `ξ_W` does not have to be produced by hand: the *ideal* is what is
used, and everything about it that the chart construction needs is the mod-`p` statement.

## Contents

* `Work.DSM5c.chartTiltGen` — the tilted chart generators (with the `j₀`-normalisation);
* `Work.DSM5c.tiltChart`, `Work.DSM5c.tiltChartHat`, `Work.DSM5c.varpiHat` — the perfected
  tilted chart, its `ϖ♭`-adic completion, and the element `ϖ♭` in it;
* `Work.DSM5c.untiltOf` — the untilt functor `R ↦ 𝕎(R) ⊗_{𝕎(W♭)} W` on `W♭`-algebras;
* (planned, see `NOTES.md` §12 items 1a–1d) the presheaf `S ↦ untiltOf (R̂_S)` (`untiltOf.map`
  already gives the naturality) and the chart maps `η : chartPresheaf t ⟶ Dp`.

The *theorems* about these objects (perfection/char-`p`/torsion-freeness of the completed charts,
the mod-`p` comparison, the chart maps `η`) are stated in the companion modules; see
`Submission/Work/DSM5c/NOTES.md` §10 for the dependency list.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.DSM5c

universe a

open CategoryTheory
open DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W]

/-! ## The tilted chart generators -/

section TiltChart

variable [Fact ¬IsUnit (p : W)] {ι : Type a} [DecidableEq ι]

/-- **The tilted chart generators** attached to the M5c data.

At the distinguished index `j₀` the generator is the `♯`-element `(ϖ♭) ^ e` (so that
`♯ (chartTiltGen … j₀) = ϖ₀ ^ e = t j₀` by `DSMap.Mix.perfectoid_varpiFlat_proved`, and so that
`area_M5b` applies with `T := ϖ♭` and exponent `e`), and at every other index it is the tilt
`Work.DSM5c.tiltGens … i` of the given compatible tower (so that `♯ (chartTiltGen … i) = t i`).

The design's generator condition `t j₀ = T ^ e` of `area_M5b` is thus met with `T := ϖ♭`
(`chartTiltGen … j₀ = (tiltVarpi Q) ^ e`) *for every compatible tower* `tr`, not only for the
canonical one; this is the normalisation that removes the change-of-almost-vector problem of
`NOTES.md` §4. -/
noncomputable def chartTiltGen (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    ι → PreTilt W p :=
  fun i => if i = j₀ then tiltVarpi Q ^ e else tiltGens t tr htr0 htr i

@[simp] theorem chartTiltGen_j₀ (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    chartTiltGen Q t tr htr0 htr j₀ e j₀ = tiltVarpi Q ^ e :=
  if_pos rfl

theorem chartTiltGen_of_ne (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {i : ι} (hi : i ≠ j₀) :
    chartTiltGen Q t tr htr0 htr j₀ e i = tiltGens t tr htr0 htr i :=
  if_neg hi

/-- **The perfected tilted chart** `R_S` of the M5c design: the perfection
(`DSMap.Mix2.perfChartRing`) of the honest tilted chart of `Bl_{(t♭ i)}(W♭)` inside the localisation
`(W♭)_{t_S}`. -/
noncomputable def tiltChart (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) :
    Subalgebra (PreTilt W p) (Localization.Away (tS (chartTiltGen Q t tr htr0 htr j₀ e) S)) :=
  perfChartRing p (chartTiltGen Q t tr htr0 htr j₀ e) S

/-- The element `ϖ♭` of the perfected tilted chart `R_S` (`ϖ♭ = Work.DSM5c.tiltVarpi Q`): the
pseudo-uniformizer at which the chart is completed. -/
noncomputable def varpiHat (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) : tiltChart Q t tr htr0 htr j₀ e S :=
  ⟨algebraMap (PreTilt W p) _ (tiltVarpi Q), (tiltChart Q t tr htr0 htr j₀ e S).algebraMap_mem _⟩

/-- **The completed perfected tilted chart** `R̂_S`: the `ϖ♭`-adic completion of `R_S`.  This is the
input of the untilt functor; its properties (perfect, characteristic `p`, `ϖ♭`-torsion-free,
`ϖ♭`-adically complete, and `R̂_S ⧸ ϖ♭^n ≅ R_S ⧸ ϖ♭^n`) are proved in the companion modules. -/
noncomputable def tiltChartHat (Q : PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) : Type a :=
  AdicCompletion (Ideal.span {varpiHat Q t tr htr0 htr j₀ e S}) (tiltChart Q t tr htr0 htr j₀ e S)

end TiltChart

/-! ## The untilt functor -/

section WittFunctor

variable (p : ℕ) [Fact p.Prime] {A B C : Type a} [CommRing A] [CommRing B] [CommRing C]

/-- `𝕎` is a functor: `𝕎(g ∘ f) = 𝕎(g) ∘ 𝕎(f)`.  (Mathlib has `WittVector.map_id` but not this
composition law.) -/
theorem wittVector_map_comp (f : A →+* B) (g : B →+* C) :
    (WittVector.map (p := p) g).comp (WittVector.map (p := p) f) =
      WittVector.map (p := p) (g.comp f) := by
  refine RingHom.ext (fun x => WittVector.ext (fun n => ?_))
  simp only [RingHom.comp_apply, WittVector.map_coeff]

end WittFunctor

section Untilt

variable [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]

/-- **The untilt functor of the M5c design**, in the "ideal" form of
`sources/dsmap/direct_summand_mix_design.md`:

`untilt (R) := 𝕎(R) ⊗_{𝕎(W♭)} W = 𝕎(R) / (image of ker (θ_W))`,

where `θ_W = WittVector.fontaineTheta W p : 𝕎 W♭ →+* W` is Fontaine's theta map and
`φ : W♭ →+* R` makes `R` a `W♭`-algebra.  The quotient is naturally a `W`-algebra (the map
`W = 𝕎W♭ ⧸ ker θ_W ⟶ 𝕎R ⧸ (image of ker θ_W)`), hence in particular a `W`-module, which is what
the frozen statement needs of the charts.

Using the *ideal* rather than a chosen generator is what lets the mod-`p` comparison
(`D_S ⧸ p ≅ R̂_S ⧸ (ϖ♭) ^ p`) be proved from `PB2` alone. -/
noncomputable abbrev untiltOf (R : Type a) [CommRing R] (φ : PreTilt W p →+* R) : Type a :=
  WittVector p R ⧸
    Ideal.span ((WittVector.map φ) ''
      ((RingHom.ker (WittVector.fontaineTheta (p := p) (R := W)) :
        Set (WittVector p (PreTilt W p)))))

/-- The quotient map `𝕎 R → untiltOf R φ` defining the untilt. -/
noncomputable def untiltOf.mk {R : Type a} [CommRing R] (φ : PreTilt W p →+* R) :
    WittVector p R →+* untiltOf (p := p) (W := W) R φ :=
  Ideal.Quotient.mk _

/-- The data defining the `W`-algebra structure of the untilt: the ring homomorphism
`𝕎W♭ →+* untiltOf R φ` induced by `𝕎(φ)` on the nose, together with the verification that
`ker θ_W` is carried into the ideal defining the untilt. -/
noncomputable def untiltOf.algebraMapData {R : Type a} [CommRing R] (φ : PreTilt W p →+* R) :
    { g : WittVector p (PreTilt W p) →+* untiltOf (p := p) (W := W) R φ //
      RingHom.ker (WittVector.fontaineTheta (p := p) (R := W)) ≤ RingHom.ker g } :=
  ⟨(untiltOf.mk (p := p) (W := W) φ).comp (WittVector.map φ), fun x hx =>
    RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_image_of_mem (WittVector.map φ) hx)))⟩

/-- **The `W`-algebra structure of the untilt**: `W` is a quotient of `𝕎W♭` along the surjective
theta map, and `𝕎(φ)` carries `ker θ_W` into the ideal defining `untiltOf R φ`; hence `W` maps to
the untilt.  (The map is produced by `RingHom.liftOfSurjective`, so it carries `θ_W x` to the class
of `𝕎(φ) x`.) -/
noncomputable def untiltOf.algebraMap
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    {R : Type a} [CommRing R] (φ : PreTilt W p →+* R) :
    W →+* untiltOf (p := p) (W := W) R φ :=
  RingHom.liftOfSurjective _ hθ (untiltOf.algebraMapData (p := p) (W := W) φ)

/-- The defining property of the `W`-algebra structure of the untilt: `θ_W x` maps to the class of
`𝕎(φ) x`. -/
theorem untiltOf.algebraMap_fontaineTheta
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    {R : Type a} [CommRing R] (φ : PreTilt W p →+* R) (x : WittVector p (PreTilt W p)) :
    untiltOf.algebraMap (p := p) (W := W) hθ φ (WittVector.fontaineTheta (p := p) (R := W) x) =
      untiltOf.mk (p := p) (W := W) φ (WittVector.map φ x) :=
  RingHom.liftOfSurjective_comp_apply _ hθ
    (untiltOf.algebraMapData (p := p) (W := W) φ) x

/-! ### Naturality of the untilt in `R` -/

/-- The data defining functoriality of the untilt in `R`. -/
noncomputable def untiltOf.mapData {R R' : Type a} [CommRing R] [CommRing R']
    (φ : PreTilt W p →+* R) (φ' : PreTilt W p →+* R') (ψ : R →+* R') (h : ψ.comp φ = φ') :
    { g : WittVector p R →+* untiltOf (p := p) (W := W) R' φ' //
      Ideal.span ((WittVector.map φ) ''
        ((RingHom.ker (WittVector.fontaineTheta (p := p) (R := W)) :
          Set (WittVector p (PreTilt W p))))) ≤ RingHom.ker g } :=
  ⟨(untiltOf.mk (p := p) (W := W) φ').comp (WittVector.map ψ),
    Ideal.span_le.mpr (by
      rintro _ ⟨y, hy, rfl⟩
      refine RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr ?_)
      have hcomp : WittVector.map ψ (WittVector.map φ y) = WittVector.map φ' y := by
        rw [← RingHom.comp_apply, wittVector_map_comp p φ ψ, h]
      rw [hcomp]
      exact Ideal.subset_span (Set.mem_image_of_mem (WittVector.map φ') hy))⟩

/-- **Functoriality of the untilt in `R`**: a `W♭`-algebra map `ψ : R →+* R'` compatible with the
structure maps induces a `W`-algebra map of untilts. -/
noncomputable def untiltOf.map {R R' : Type a} [CommRing R] [CommRing R']
    (φ : PreTilt W p →+* R) (φ' : PreTilt W p →+* R') (ψ : R →+* R') (h : ψ.comp φ = φ') :
    untiltOf (p := p) (W := W) R φ →+* untiltOf (p := p) (W := W) R' φ' :=
  Ideal.Quotient.lift _ (untiltOf.mapData (p := p) (W := W) φ φ' ψ h).1
    fun x hx => (untiltOf.mapData (p := p) (W := W) φ φ' ψ h).2 hx

theorem untiltOf.map_apply {R R' : Type a} [CommRing R] [CommRing R']
    (φ : PreTilt W p →+* R) (φ' : PreTilt W p →+* R') (ψ : R →+* R') (h : ψ.comp φ = φ')
    (x : WittVector p R) :
    untiltOf.map (p := p) (W := W) (R := R) (R' := R') φ φ' ψ h
        (untiltOf.mk (p := p) (W := W) φ x) =
      untiltOf.mk (p := p) (W := W) φ' (WittVector.map ψ x) :=
  Ideal.Quotient.lift_mk _ _ _

end Untilt

end Work.DSM5c
