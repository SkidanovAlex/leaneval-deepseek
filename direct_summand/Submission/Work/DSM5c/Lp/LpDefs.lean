import Mathlib
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.ChartLpFunctor
import Submission.Work.DSM5c.ChartComparison
import Submission.Work.DSM5c.Lp.PiHelpers

/-!
# DSM5c — the mod-`p` comparison presheaf `Lp` (definitions)

This file fixes the vocabulary of transport step 5 of `NOTES.md` §20.2: the presheaf of
`W`-modules

  `L_S := D_S ⧸ (p) · ⊤`,   `D_S = untiltOf R_S φ_S`,

together with the natural surjection `chartD ⟶ chartLQ` (`chartLQEta`) and the *comparison ring
homomorphism* `chartCmpRingHom : D_S →+* L_S` given by the `0`-th Witt coordinate
(`WittVector.constantCoeff`).  Its kernel is `(p) · ⊤` by
`Work.DSM5c.mem_span_p_sup_map_ker_fontaineTheta`, and it is `W`-linear, hence it induces the
isomorphism `D_S ⧸ (p) ≅ L_S = R_S ⧸ (φ_S (ϖ♭)^p)` identifying `Lp` with the presheaf of mod-`p`
charts `Work.DSM5c.chartLpObj`.

## Contents

* `Work.DSM5c.Lp.chartDpTop` — the submodule `(p) · ⊤ ⊆ D_S`;
* `Work.DSM5c.Lp.chartUntiltIdeal` — the ideal of `𝕎 R_S` defining `D_S`;
* `Work.DSM5c.Lp.chartLQObj`, `chartLQOfHom`, `chartLQ` — the presheaf `S ↦ D_S ⧸ (p) · ⊤`;
* `Work.DSM5c.Lp.chartLQEta` — the natural surjection `chartD ⟶ chartLQ`;
* `Work.DSM5c.Lp.chartCmpRingHom`, `chartCmpRingHom_mk` — the comparison `D_S →+* L_S`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option allowUnsafeReducibility true

-- The local `reducible` attribute below is needed because `ModuleCat` morphisms stated in terms of
-- the bundled chart objects `chartDObj`/`chartLQObj` (which are `def`s in other modules) must be
-- seen as living on the underlying quotient types when rewriting by the quotient API.
attribute [local reducible] Work.DSM5c.chartDObj Work.DSM5c.chartD Work.DSM5c.chartDOfHom

namespace Work.DSM5c.Lp

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]

/-! ## The submodule `(p) · ⊤` and the presheaf `Lp` -/

/-- **The `W`-submodule `(p) · ⊤` of the chart untilt `D_S`**: the kernel of the mod-`p` comparison
`D_S → L_S`. -/
noncomputable abbrev chartDpTop (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    Submodule W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
      (chartPhi Q t tr htr0 htr j₀ e S)) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  exact Ideal.span {(p : W)} •
    (⊤ : Submodule W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
      (chartPhi Q t tr htr0 htr j₀ e S)))

/-- Membership in `chartDpTop`: it is `(p) · ⊤`. -/
theorem mem_chartDpTop (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι)
    (x : untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S)) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    (x ∈ chartDpTop Q hθ t tr htr0 htr j₀ e S ↔
      x ∈ Ideal.span {(p : W)} • (⊤ : Submodule W
        (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
          (chartPhi Q t tr htr0 htr j₀ e S)))) :=
  Iff.rfl

/-- The ideal of `𝕎 R_S` defining the chart untilt `D_S = 𝕎 R_S ⧸ 𝕎(φ_S)(ker θ_W)`. -/
noncomputable def chartUntiltIdeal (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    Ideal (WittVector p (tiltChart Q t tr htr0 htr j₀ e S)) :=
  Ideal.span ((WittVector.map (chartPhi Q t tr htr0 htr j₀ e S)) ''
    ((RingHom.ker (WittVector.fontaineTheta (p := p) (R := W)) :
      Set (WittVector p (PreTilt W p)))))

attribute [local reducible] chartUntiltIdeal

/-- The object of the presheaf `Lp` at `S`: the quotient `D_S ⧸ (p) · ⊤`. -/
noncomputable def chartLQObj (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ) : ModuleCat.{a} W := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  exact ModuleCat.of W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
    (chartPhi Q t tr htr0 htr j₀ e S.unop.unop) ⧸
    chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop)

attribute [local reducible] chartLQObj

/-- The morphism data of `Lp`: the map `D_S ⧸ (p)·⊤ → D_T ⧸ (p)·⊤` induced by `chartDMap`. -/
noncomputable def chartLQOfHom (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T) :
    chartLQObj Q hθ t tr htr0 htr j₀ e S ⟶ chartLQObj Q hθ t tr htr0 htr j₀ e T := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e T.unop.unop
  refine ModuleCat.ofHom (Submodule.mapQ (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop)
    (chartDpTop Q hθ t tr htr0 htr j₀ e T.unop.unop)
    (chartDMap Q hθ t tr htr0 htr j₀ e (leOfHom f.unop.unop)) ?_)
  intro x hx
  exact map_smul_top_le (chartDMap Q hθ t tr htr0 htr j₀ e (leOfHom f.unop.unop))
    (Ideal.span {(p : W)}) ⟨x, hx, rfl⟩

attribute [local reducible] chartLQOfHom

/-- The defining property of `chartLQOfHom` on representatives. -/
theorem chartLQOfHom_mk (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    {S T : (Finset ι)ᵒᵖᵒᵖ} (f : S ⟶ T)
    (x : untiltOf (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
      (chartPhi Q t tr htr0 htr j₀ e S.unop.unop)) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e T.unop.unop
    (chartLQOfHom Q hθ t tr htr0 htr j₀ e f).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (chartDMap Q hθ t tr htr0 htr j₀ e (leOfHom f.unop.unop) x) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e T.unop.unop
  rw [ModuleCat.hom_ofHom, Submodule.mapQ_apply]

/-- **The presheaf `Lp = Dp ⧸ (p)·⊤`**: the codomain of the mod-`p` comparison chain map. -/
noncomputable def chartLQ (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W where
  obj := chartLQObj Q hθ t tr htr0 htr j₀ e
  map f := chartLQOfHom Q hθ t tr htr0 htr j₀ e f
  map_id S := by
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_id]
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop) x
    rw [chartLQOfHom_mk]
    have h : leOfHom (𝟙 S).unop.unop = subset_refl S.unop.unop := Subsingleton.elim _ _
    rw [show chartDMap Q hθ t tr htr0 htr j₀ e (leOfHom (𝟙 S).unop.unop) y =
      chartDMap Q hθ t tr htr0 htr j₀ e (subset_refl S.unop.unop) y from by rw [h],
      chartDMap_self]
    rfl
  map_comp {S T V} f g := by
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e T.unop.unop
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e V.unop.unop
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ :=
      Submodule.Quotient.mk_surjective (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop) x
    rw [chartLQOfHom_mk, ModuleCat.hom_comp, LinearMap.comp_apply, chartLQOfHom_mk,
      chartLQOfHom_mk]
    have h : leOfHom (f ≫ g).unop.unop =
        (leOfHom f.unop.unop).trans (leOfHom g.unop.unop) := Subsingleton.elim _ _
    rw [show chartDMap Q hθ t tr htr0 htr j₀ e (leOfHom (f ≫ g).unop.unop) y =
      chartDMap Q hθ t tr htr0 htr j₀ e
        ((leOfHom f.unop.unop).trans (leOfHom g.unop.unop)) y from by rw [h],
      chartDMap_trans]

attribute [local reducible] chartLQ

/-- **The natural surjection `chartD ⟶ Lp`**: termwise the quotient map `D_S ↠ D_S ⧸ (p) · ⊤`. -/
noncomputable def chartLQEta (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) :
    chartD Q hθ t tr htr0 htr j₀ e ⟶ chartLQ Q hθ t tr htr0 htr j₀ e where
  app S := by
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    exact ModuleCat.ofHom (chartDpTop Q hθ t tr htr0 htr j₀ e S.unop.unop).mkQ
  naturality {S T} f := by
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e T.unop.unop
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [ModuleCat.hom_ofHom, Submodule.mkQ_apply]
    rw [Submodule.mapQ_apply]

attribute [local reducible] chartLQEta

/-- The component of `chartLQEta` is the quotient map, on elements. -/
theorem chartLQEta_app_eq (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ)
    (x : untiltOf (tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
      (chartPhi Q t tr htr0 htr j₀ e S.unop.unop)) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
    ((chartLQEta Q hθ t tr htr0 htr j₀ e).app S).hom x = Submodule.Quotient.mk x := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  exact Submodule.mkQ_apply _ x

/-- The component of `chartLQEta` is surjective. -/
theorem chartLQEta_app_surjective (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (S : (Finset ι)ᵒᵖᵒᵖ) :
    Function.Surjective ((chartLQEta Q hθ t tr htr0 htr j₀ e).app S).hom := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S.unop.unop
  exact Submodule.mkQ_surjective _

/-! ## The comparison ring homomorphism `D_S →+* L_S` -/

/-- **The comparison ring homomorphism `D_S →+* L_S`**: the `0`-th Witt coordinate
(`WittVector.constantCoeff`), which kills `𝕎(φ_S)(ker θ_W)` because an element of `ker θ_W` has its
`constantCoeff` in `(ϖ♭)^p` (PB2 at the base level,
`Work.DSM5c.mem_span_p_sup_ker_fontaineTheta`). -/
noncomputable def chartCmpRingHom (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S) →+*
      (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) :=
  Ideal.Quotient.lift (chartUntiltIdeal Q hθ t tr htr0 htr j₀ e S)
    ((Ideal.Quotient.mk (chartLIdeal Q t tr htr0 htr j₀ e S)).comp
      (WittVector.constantCoeff (p := p) (R := tiltChart Q t tr htr0 htr j₀ e S)))
    (fun x hx => by
      have hle : chartUntiltIdeal Q hθ t tr htr0 htr j₀ e S ≤
          RingHom.ker ((Ideal.Quotient.mk (chartLIdeal Q t tr htr0 htr j₀ e S)).comp
            (WittVector.constantCoeff (p := p)
              (R := tiltChart Q t tr htr0 htr j₀ e S))) := by
        rw [chartUntiltIdeal]
        refine Ideal.span_le.mpr ?_
        rintro y ⟨k, hk, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, wittVector_constantCoeff_map,
          Ideal.Quotient.eq_zero_iff_mem, chartLIdeal_def]
        have hk' : k ∈ Ideal.span {(p : WittVector p (PreTilt W p))} ⊔
            RingHom.ker (WittVector.fontaineTheta (p := p) (R := W)) :=
          Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, k, hk, by simp⟩
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
          ((mem_span_p_sup_ker_fontaineTheta (W := W) Q hθ k).mp hk')
        rw [← hc, map_mul, map_pow]
        exact Ideal.mul_mem_left _ _
          (Ideal.mem_span_singleton_self ((chartPhi Q t tr htr0 htr j₀ e S) (tiltVarpi Q) ^ p))
      exact RingHom.mem_ker.mp (hle hx))

/-- The defining property of the comparison map: on the class of `y : 𝕎 R_S` it is the class of
`constantCoeff y`. -/
theorem chartCmpRingHom_mk (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι)
    (y : WittVector p (tiltChart Q t tr htr0 htr j₀ e S)) :
    chartCmpRingHom Q hθ t tr htr0 htr j₀ e S
        ((Ideal.Quotient.mk (chartUntiltIdeal Q hθ t tr htr0 htr j₀ e S)) y) =
      (Ideal.Quotient.mk (chartLIdeal Q t tr htr0 htr j₀ e S))
        (WittVector.constantCoeff y) :=
  Ideal.Quotient.lift_mk _ _ _

end Work.DSM5c.Lp
