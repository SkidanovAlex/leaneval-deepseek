import Mathlib
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.ChartComparison
import Submission.Work.DSM5c.ChartLpFunctor
import Submission.Work.DSM5c.Charts.perfChartRing_perfect
import Submission.Work.DSM5c.Lp.LpDefs
import Submission.Work.DSM5c.Lp.PiHelpers
import Submission.Work.DSM5c.Lp.ker_Pi_map_span
import Submission.Work.DSM5c.Lp.surjective_Pi_map
import Submission.Work.DSM5c.Lp.chartCmpRingHom_algebraMap
import Submission.Work.DSM5c.Lp.chartCmpRingHom_eq_zero_iff

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option allowUnsafeReducibility true

-- See `LpDefs.lean`: the locally `reducible` attributes let the quotient API rewrite under the
-- bundled chart objects (which are `def`s in other modules).
attribute [local reducible] Work.DSM5c.chartDObj Work.DSM5c.chartD Work.DSM5c.chartDOfHom
  Work.DSM5c.Lp.chartLQObj Work.DSM5c.Lp.chartLQOfHom Work.DSM5c.Lp.chartLQEta
  Work.DSM5c.Lp.chartLQ Work.DSM5c.Lp.chartUntiltIdeal

namespace Work.DSM5c.Lp

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2 Opposite

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]

/-! ## The comparison `D_S → L_S`: surjectivity and `W`-linearity -/

/-- The comparison `D_S →+* L_S` is surjective: `constantCoeff` is split by the Teichmüller lift. -/
theorem chartCmpRingHom_surjective (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    Function.Surjective (chartCmpRingHom Q hθ t tr htr0 htr j₀ e S) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨(Ideal.Quotient.mk (chartUntiltIdeal Q hθ t tr htr0 htr j₀ e S))
    (WittVector.teichmuller p x), ?_⟩
  rw [chartCmpRingHom_mk, constantCoeff_teichmuller']

/-- The `W`-linearity of the comparison map, in `algebraMap` form (the domain algebra structure is
`Work.DSM5c.chartDAlg`, the codomain one `Work.DSM5c.chartLAlg`). -/
theorem chartCmpRingHom_algebraMap' (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) (w : W) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    chartCmpRingHom Q hθ t tr htr0 htr j₀ e S (algebraMap W _ w) =
      chartLRingHom Q t tr htr0 htr j₀ e S w := by
  exact chartCmpRingHom_algebraMap Q hθ t tr htr0 htr j₀ e S w

/-- **The comparison map as a `W`-linear map** `D_S →ₗ[W] L_S`. -/
noncomputable def chartCmpLinear (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartLAlg Q t tr htr0 htr j₀ e S
    untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S) →ₗ[W]
      (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartLAlg Q t tr htr0 htr j₀ e S
  exact { toFun := chartCmpRingHom Q hθ t tr htr0 htr j₀ e S
          map_add' := map_add _
          map_smul' := fun w x => by
            rw [Algebra.smul_def, Algebra.smul_def, map_mul, chartCmpRingHom_algebraMap']
            rfl }

attribute [local reducible] chartCmpLinear

/-- The comparison map is surjective. -/
theorem chartCmpLinear_surjective (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    Function.Surjective ⇑(chartCmpLinear Q hθ t tr htr0 htr j₀ e S) := by
  intro y
  obtain ⟨x, hx⟩ := chartCmpRingHom_surjective Q hθ t tr htr0 htr j₀ e S y
  exact ⟨x, hx⟩

/-- **The kernel of the comparison map is `(p) · ⊤`.** -/
theorem chartCmpLinear_ker (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι)
    [CharP (tiltChart Q t tr htr0 htr j₀ e S) p]
    [PerfectRing (tiltChart Q t tr htr0 htr j₀ e S) p] :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartLAlg Q t tr htr0 htr j₀ e S
    LinearMap.ker (chartCmpLinear Q hθ t tr htr0 htr j₀ e S) =
      chartDpTop Q hθ t tr htr0 htr j₀ e S := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartLAlg Q t tr htr0 htr j₀ e S
  ext x
  rw [LinearMap.mem_ker]
  exact chartCmpRingHom_eq_zero_iff Q hθ t tr htr0 htr j₀ e S x

/-! ## The characteristic of the tilted chart -/

/-- `p = 0` in the tilted chart `R_S`, which is a `PreTilt W p`-algebra. -/
theorem chart_p_eq_zero (Q : DSMap.PerfectoidData p W) (t : ι → W) (tr : ι → ℕ → W)
    (htr0 : ∀ i, tr i 0 = t i) (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : Finset ι) : (p : tiltChart Q t tr htr0 htr j₀ e S) = 0 := by
  rw [← map_natCast (algebraMap (PreTilt W p) (tiltChart Q t tr htr0 htr j₀ e S)) p,
    CharP.cast_eq_zero, map_zero]

/-! ## The comparison isomorphism `D_S ⧸ (p) ≅ L_S` -/

/-- **Degenerate case**: if the tilted chart `R_S` is the zero ring, so are `D_S ⧸ (p)` and `L_S`,
and the (zero) comparison is an isomorphism. -/
theorem chartLQObj_iso_of_subsingleton (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ)
    (hsub : Subsingleton (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)) :
    Nonempty (chartLQObj Q hθ t tr htr0 htr j₀ e S ≅
      chartLpObj (p := p) (W := W) Q t tr htr0 htr j₀ e S) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  letI := chartLAlg Q t tr htr0 htr j₀ e S.unop.unop
  haveI hW : Subsingleton (WittVector p (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)) :=
    ⟨fun x y => WittVector.ext fun n => Subsingleton.elim _ _⟩
  haveI hD : Subsingleton (untiltOf (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
      (chartPhi Q t tr htr0 htr j₀ e S.unop.unop)) :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Subsingleton.elim a b]⟩
  haveI hQ : Subsingleton (untiltOf (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
      (chartPhi Q t tr htr0 htr j₀ e S.unop.unop) ⧸
      chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop) :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [Subsingleton.elim a b]⟩
  haveI hL : Subsingleton (tiltChart Q t tr htr0 htr j₀ e S.unop.unop ⧸
      chartLIdeal Q t tr htr0 htr j₀ e S.unop.unop) :=
    ⟨fun x y => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Subsingleton.elim a b]⟩
  exact ⟨LinearEquiv.toModuleIso
    { toFun := fun _ => 0
      invFun := fun _ => 0
      map_add' := fun x y => (add_zero (0 : tiltChart Q t tr htr0 htr j₀ e S.unop.unop ⧸
        chartLIdeal Q t tr htr0 htr j₀ e S.unop.unop)).symm
      map_smul' := fun c x => (smul_zero c).symm
      left_inv := fun x => Subsingleton.elim _ _
      right_inv := fun x => Subsingleton.elim _ _ }⟩

/-- **The comparison isomorphism `D_S ⧸ (p) ≅ L_S`.** -/
theorem chartLQObj_iso (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ) :
    Nonempty (chartLQObj Q hθ t tr htr0 htr j₀ e S ≅
      chartLpObj (p := p) (W := W) Q t tr htr0 htr j₀ e S) := by
  by_cases hsub : Subsingleton (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
  · exact chartLQObj_iso_of_subsingleton Q hθ t tr htr0 htr j₀ e S hsub
  · letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    letI := chartLAlg Q t tr htr0 htr j₀ e S.unop.unop
    haveI hchar : CharP (tiltChart Q t tr htr0 htr j₀ e S.unop.unop) p := by
      have hdvd : ringChar (tiltChart Q t tr htr0 htr j₀ e S.unop.unop) ∣ p :=
        ringChar.dvd (chart_p_eq_zero Q t tr htr0 htr j₀ e S.unop.unop)
      rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp
      · exact absurd (ringChar.ringChar_eq_one.mp h1) hsub
      · exact ringChar.of_eq hp
    haveI hperf : PerfectRing (tiltChart Q t tr htr0 htr j₀ e S.unop.unop) p :=
      Work.DSM5c.Charts.perfChartRing_perfect p (chartTiltGen Q t tr htr0 htr j₀ e)
        S.unop.unop
    have hsurj : Function.Surjective ⇑(chartCmpLinear Q hθ t tr htr0 htr j₀ e S.unop.unop) :=
      chartCmpLinear_surjective Q hθ t tr htr0 htr j₀ e S.unop.unop
    have hker : LinearMap.ker (chartCmpLinear Q hθ t tr htr0 htr j₀ e S.unop.unop) =
        chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop :=
      chartCmpLinear_ker Q hθ t tr htr0 htr j₀ e S.unop.unop
    have hle : chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop ≤
        LinearMap.ker (chartCmpLinear Q hθ t tr htr0 htr j₀ e S.unop.unop) := hker.ge
    refine ⟨LinearEquiv.toModuleIso (LinearEquiv.ofBijective
      ((chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop).liftQ
        (chartCmpLinear Q hθ t tr htr0 htr j₀ e S.unop.unop) hle) ⟨?_, ?_⟩)⟩
    · intro a b hab
      obtain ⟨x, rfl⟩ :=
        Submodule.Quotient.mk_surjective
          (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop) a
      obtain ⟨y, rfl⟩ :=
        Submodule.Quotient.mk_surjective
          (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop) b
      rw [Submodule.liftQ_apply, Submodule.liftQ_apply] at hab
      refine (Submodule.Quotient.eq (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop)).mpr ?_
      rw [← hker, LinearMap.mem_ker, map_sub, hab, sub_self]
    · intro y
      obtain ⟨a, ha⟩ := hsurj y
      exact ⟨Submodule.Quotient.mk a, by
        rw [Submodule.liftQ_apply]
        exact ha⟩

/-! ## The terms of the Čech complex of a presheaf of modules -/

/-- The component at degree `q` of the chain map induced by a natural transformation `η` between
presheaves of `W`-modules is the product of the components of `η` at the chart intersections. -/
theorem cech_map_f (F G : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (η : F ⟶ G) (q : ℕ) :
    ((cechComplexFunctor (chartIdx ι)).map η).f q =
      CategoryTheory.Limits.Pi.map (fun i : (Fin (q + 1) → ι) =>
        η.app (op ((CategoryTheory.Limits.FormalCoproduct.power
          (CategoryTheory.Limits.FormalCoproduct.mk ι (chartIdx ι))
          (Fin (q + 1))).obj i))) :=
  rfl

/-- The objects indexing the degree-`q` term of the Čech complex. -/
noncomputable abbrev cechIdx (q : ℕ) : (Fin (q + 1) → ι) → (Finset ι)ᵒᵖᵒᵖ :=
  fun i => op ((CategoryTheory.Limits.FormalCoproduct.power
    (CategoryTheory.Limits.FormalCoproduct.mk ι (chartIdx ι)) (Fin (q + 1))).obj i)

/-- **The mod-`p` comparison presheaf `Lp` and the termwise surjection `Dp ⟶ Lp`** (transport step 5
of `NOTES.md` §20.2): there are a presheaf `Lp` of `W`-modules on `(Finset ι)ᵒᵖᵒᵖ` whose values are
the mod-`p` charts `L_S = R_S ⧸ (φ_S (ϖ♭)^p)` (`Work.DSM5c.chartLpObj`, i.e. the perfect tilted chart
modulo `(ϖ♭)^p`), and a chain map `f` between the Čech complexes of `Work.DSM5c.chartD` and of `Lp`
which is *termwise surjective with kernel exactly `(p) · ⊤`*.

The kernel computation is exactly `Work.DSM5c.mem_span_p_sup_map_ker_fontaineTheta`
(`Submission/Work/DSM5c/ChartComparison.lean`): `x ∈ (p) ⊔ 𝕎(φ_S)(ker θ_W) ↔ constantCoeff x ∈
(φ_S (ϖ♭))^p`; hence `D_S ⧸ (p) ≅ L_S` by the third isomorphism, and the components of `f` are the
composites `D_S ↠ D_S ⧸ (p) ≅ L_S`.

Available ingredients: the elementwise laws `Work.DSM5c.chartLMap_self`,
`Work.DSM5c.chartLMap_comp` and the `W`-linearity `Work.DSM5c.Lp.chartLMap_algebraMap`, plus the
objects `Work.DSM5c.chartLpObj`.  Packaging them into the functor `Lp` is currently blocked by an
elaboration issue (the `W`-module structure on `L_S` comes from the non-global instance
`chartLAlg`, so `ModuleCat.ofHom`-based bundling times out in `whnf` / instance synthesis); the fix
that worked for `Work.DSM5c.chartD` (`Submission/Work/DSM5c/ChartFunctor.lean`) is to state the
`W`-linearity of `chartLMap` as a *closed* declaration and hand it to `ModuleCat.ofHom` as a term. -/
theorem chartDToLp_exists {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    ∃ (Lp : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat W)
      (f : (cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e) ⟶
        (cechComplexFunctor (chartIdx ι)).obj Lp),
      (∀ (S : (Finset ι)ᵒᵖᵒᵖ), Nonempty (Lp.obj S ≅
        Work.DSM5c.chartLpObj (p := p) (W := W) Q t tr htr0 htr j₀ e S)) ∧
      (∀ q, Function.Surjective (f.f q).hom) ∧
      (∀ (q : ℕ) (x : ((cechComplexFunctor (chartIdx ι)).obj
          (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X q),
        (f.f q).hom x = 0 ↔ x ∈ Ideal.span {(p : W)} •
          (⊤ : Submodule W (((cechComplexFunctor (chartIdx ι)).obj
            (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).X q))) := by
  refine ⟨chartLQ Q hθ t tr htr0 htr j₀ e,
    (cechComplexFunctor (chartIdx ι)).map (chartLQEta Q hθ t tr htr0 htr j₀ e), ?_, ?_, ?_⟩
  · intro S
    exact chartLQObj_iso Q hθ t tr htr0 htr j₀ e S
  · intro q
    have hq : ((cechComplexFunctor (chartIdx ι)).map
        (chartLQEta Q hθ t tr htr0 htr j₀ e)).f q =
        CategoryTheory.Limits.Pi.map (fun i : (Fin (q + 1) → ι) =>
          (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i)) :=
      cech_map_f (chartD Q hθ t tr htr0 htr j₀ e) (chartLQ Q hθ t tr htr0 htr j₀ e)
        (chartLQEta Q hθ t tr htr0 htr j₀ e) q
    rw [hq]
    exact surjective_Pi_map _ _ _ (fun i => chartLQEta_app_surjective Q hθ t tr htr0 htr j₀ e _)
  · intro q x
    have hq : ((cechComplexFunctor (chartIdx ι)).map
        (chartLQEta Q hθ t tr htr0 htr j₀ e)).f q =
        CategoryTheory.Limits.Pi.map (fun i : (Fin (q + 1) → ι) =>
          (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i)) :=
      cech_map_f (chartD Q hθ t tr htr0 htr j₀ e) (chartLQ Q hθ t tr htr0 htr j₀ e)
        (chartLQEta Q hθ t tr htr0 htr j₀ e) q
    rw [hq]
    have key : ∀ y : ↥(∏ᶜ fun i : (Fin (q + 1) → ι) =>
        (chartD Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i)),
        (CategoryTheory.Limits.Pi.map fun i : (Fin (q + 1) → ι) =>
          (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i)).hom y = 0 ↔
        y ∈ Ideal.span {(p : W)} • (⊤ : Submodule W ↥(∏ᶜ fun i : (Fin (q + 1) → ι) =>
          (chartD Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i))) := by
      intro y
      rw [← LinearMap.mem_ker,
        ker_Pi_map_span (fun i : (Fin (q + 1) → ι) =>
            (chartD Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i))
          (fun i => (chartLQ Q hθ t tr htr0 htr j₀ e).obj (cechIdx (q := q) i))
          (fun i => (chartLQEta Q hθ t tr htr0 htr j₀ e).app (cechIdx (q := q) i))
          (p : W)
          (fun i => by
            letI := chartDAlg Q hθ t tr htr0 htr j₀ e (cechIdx (q := q) i).unop.unop
            exact Submodule.ker_mkQ (chartDpTop Q hθ t tr htr0 htr j₀ e
              (cechIdx (q := q) i).unop.unop))]
    exact key x

end Work.DSM5c.Lp
