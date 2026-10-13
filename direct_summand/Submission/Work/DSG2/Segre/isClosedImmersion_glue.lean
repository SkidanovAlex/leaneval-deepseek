import Mathlib
import Submission.Work.DSG2.Segre.Basic
import Submission.Work.DSG2.Segre.Triangle
import Submission.Work.DSG4c.ChartPushout.chartToPoly_surjective

/-!
# The glued Segre map `ℙ^a_A ×_A ℙ^b_A ⟶ ℙ^N_A` is a closed immersion (area DSG2)

The chartwise maps `sigma k` agree on the overlaps `V k ∩ V k'` (the hypothesis `hcompat`), hence
glue to a morphism `f : ℙ^a_A ×_{Spec A} ℙ^b_A ⟶ ℙ^N_A` (`Scheme.Cover.glueMorphisms`), the Segre
embedding.  This file proves `IsClosedImmersion f`.

The argument is:

* `awayι_preimage_chartCoord`: the preimage of the `k`-th standard chart of `ℙ^N_A` under the chart
  inclusion `chartι` is the basic open of the coordinate `X k / X i`.
* `specBasicOpen_tmul`: the basic open of a tensor product `x ⊗ₜ y` is the intersection of the
  basic opens of `x ⊗ₜ 1` and `1 ⊗ₜ y` (in the product of the two spectra).
* `sigma_preimage_chartOpen`: consequently, the preimage of the `m`-th chart of `ℙ^N_A` under the
  chartwise Segre map `sigma k` is the intersection of the source charts `V k` and
  `V (toIdx.symm m)`.
* Summing this over the open cover `V k` of the source yields that the preimage of a chart of
  `ℙ^N_A` under the glued map is a single source chart.
* `IsClosedImmersion` is local at the target, so it suffices to test `f` on the charts of `ℙ^N_A`;
  on the `k`-th chart the restriction of `f` becomes the closed immersion `sigmaChart k`, which is
  `Spec` of the surjective chart ring map `segreChart k` (`segreChart_surjective_dsg2`).
-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

namespace Work.DSG2.Segre

universe u

/-! ## Auxiliary chart computations -/

/-- Preimages under an isomorphism are injective on opens. -/
lemma preimage_inj_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] {U V : Y.Opens}
    (h : f ⁻¹ᵁ U = f ⁻¹ᵁ V) : U = V := by
  have h2 := congrArg (fun W => f ''ᵁ W) h
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso,
    top_inf_eq, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso,
    top_inf_eq] at h2

/-- The preimage of the `k`-th standard chart of `ℙⁿ_A` under the `i`-th chart inclusion is the
basic open of the coordinate `X k / X i`. -/
lemma awayι_preimage_chartCoord (A : Type u) [CommRing A] (n : ℕ) (i k : Fin (n+1)) :
    (Work.DSG4c.chartι A n i) ⁻¹ᵁ
        (Proj.basicOpen (DSMap.PGr A n) (MvPolynomial.X k)) =
      PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A n i k) := by
  have h := Proj.awayι_preimage_basicOpen (𝒜 := DSMap.PGr A n)
    (f_deg := Work.DSG4c.X_mem A n i) (hm := one_pos)
    (g := MvPolynomial.X k) (g_deg := Work.DSG4c.X_mem A n k) one_pos
  rw [Work.DSG4c.chartι, h]
  congr 1
  simp [HomogeneousLocalization.Away.isLocalizationElem, Work.DSG4c.ChartPushout.chartElemAll,
    pow_one]

/-- The basic open of a tensor product `x ⊗ₜ y` in `Spec (S ⊗[R] T)` is the intersection of the
basic opens of `x ⊗ₜ 1` and `1 ⊗ₜ y`. -/
lemma specBasicOpen_tmul {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (x : S) (y : T) :
    (PrimeSpectrum.basicOpen ((algebraMap S (S ⊗[R] T)) x) : (Spec ↧(S ⊗[R] T)).Opens) ⊓
      (PrimeSpectrum.basicOpen
        ((Algebra.TensorProduct.includeRight (R := R) (A := S) (B := T)) y)
        : (Spec ↧(S ⊗[R] T)).Opens)
    = (PrimeSpectrum.basicOpen (x ⊗ₜ[R] y) : (Spec ↧(S ⊗[R] T)).Opens) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.includeRight_apply,
    ← PrimeSpectrum.basicOpen_mul, Algebra.TensorProduct.tmul_mul_tmul,
    Algebra.algebraMap_self, RingHom.id_apply, mul_one, one_mul]

/-- `(p * q) ⊗ₜ 1 = (p ⊗ₜ 1) * (q ⊗ₜ 1)`. -/
lemma tmul_one_mul {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (p q : S) :
    ((p * q) ⊗ₜ[R] (1 : T)) = (p ⊗ₜ[R] (1 : T)) * (q ⊗ₜ[R] (1 : T)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

/-- `1 ⊗ₜ (p * q) = (1 ⊗ₜ p) * (1 ⊗ₜ q)`. -/
lemma one_tmul_mul {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (p q : T) :
    ((1 : S) ⊗ₜ[R] (p * q)) = ((1 : S) ⊗ₜ[R] p) * ((1 : S) ⊗ₜ[R] q) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

variable (A : Type u) [CommRing A] (a b : ℕ)

/-- The family of chart-ring elements `x_{p}/x_{k.1} ⊗ y_{q}/y_{k.2}` indexing the coordinates of
the `k`-th chart of `ℙ^N_A`, i.e. the coordinate functions of the Segre chart map. -/
noncomputable def segreCoord (k : Fin (a+1) × Fin (b+1)) :
    Work.DSG4c.ChartPushout.chartIdx (segreN a b) (toIdx a b k) → chartRing A a b k :=
  fun j => Work.DSG4c.ChartPushout.chartElemAll A a k.1 ((toIdx a b).symm j.1).1 ⊗ₜ[A]
    Work.DSG4c.ChartPushout.chartElemAll A b k.2 ((toIdx a b).symm j.1).2

/-- The second projection of the product chart inclusion is the structure map of the chart rings. -/
lemma chartIncl_snd_ring (k : Fin (a+1) × Fin (b+1)) :
    chartIncl A a b k.1 k.2 ≫ pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A)
        (A := chartRingA A a k.1) (B := chartRingB A b k.2))) ≫
        Work.DSG4c.chartι A b k.2 := by
  simp only [chartIncl]
  rw [Category.assoc, pullback.map, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd]

/-- The first projection of the product chart inclusion, spelled with `awayChart`. -/
lemma chartIncl_fst_away (k : Fin (a+1) × Fin (b+1)) :
    chartIncl A a b k.1 k.2 ≫ pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) =
      Spec.map (CommRingCat.ofHom (algebraMap (Work.DSG4c.awayChart A a k.1)
        (Work.DSG4c.awayChart A a k.1 ⊗[A] Work.DSG4c.awayChart A b k.2))) ≫
        Work.DSG4c.chartι A a k.1 := by
  simpa only [chartRingA, chartRingB, chartRing] using chartIncl_fst A a b k

/-- The second projection of the product chart inclusion, spelled with `awayChart`. -/
lemma chartIncl_snd_away (k : Fin (a+1) × Fin (b+1)) :
    chartIncl A a b k.1 k.2 ≫ pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A)
        (A := Work.DSG4c.awayChart A a k.1) (B := Work.DSG4c.awayChart A b k.2))) ≫
        Work.DSG4c.chartι A b k.2 := by
  simpa only [chartRingA, chartRingB, chartRing] using chartIncl_snd_ring A a b k

/-! ## The chartwise Segre map -/

/-- The chart coordinate `X_m / X_{toIdx k}` of the `(toIdx k)`-th chart of `ℙ^N_A` is sent by
`segreChart k` to `x_p/x_{k.1} ⊗ y_q/y_{k.2}`, where `(p,q) = (toIdx a b).symm m`. -/
theorem segreChart_chartElemAll_dsg2 (k : Fin (a+1) × Fin (b+1)) (m : Fin (segreN a b + 1)) :
    segreChart A a b k (Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) m) =
      Work.DSG4c.ChartPushout.chartElemAll A a k.1 ((toIdx a b).symm m).1 ⊗ₜ[A]
        Work.DSG4c.ChartPushout.chartElemAll A b k.2 ((toIdx a b).symm m).2 := by
  by_cases hm : m = toIdx a b k
  · subst hm
    rw [Work.DSG4c.ChartPushout.chartElemAll_self, map_one, Equiv.symm_apply_apply,
      Work.DSG4c.ChartPushout.chartElemAll_self, Work.DSG4c.ChartPushout.chartElemAll_self]
    exact Algebra.TensorProduct.one_def
  · rw [segreChart, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      show Work.DSG4c.ChartPushout.chartElemAll A (segreN a b) (toIdx a b k) m =
          Work.DSG4c.ChartPushout.chartElem A (segreN a b) (toIdx a b k) ⟨m, hm⟩ from rfl,
      Work.DSG4c.ChartPushout.polyToChart_chartElem, MvPolynomial.aeval_X]

/-- The dehomogenized Segre chart map `segreChart k` is surjective. -/
theorem segreChart_surjective_dsg2 (k : Fin (a+1) × Fin (b+1)) :
    Function.Surjective (segreChart A a b k) := by
  -- the `aeval` part is surjective because the `x_p ⊗ y_q` generate the chart ring
  have keyA : ∀ x : chartRingA A a k.1,
      (x ⊗ₜ[A] (1 : chartRingB A b k.2)) ∈ Algebra.adjoin A (Set.range (segreCoord A a b k)) := by
    intro x
    obtain ⟨P, rfl⟩ := Work.DSG4c.ChartPushout.chartToPoly_surjective A a k.1 x
    induction P using MvPolynomial.induction_on with
    | C c =>
        rw [Work.DSG4c.ChartPushout.chartToPoly_C, ← awayChart_algebraMap A a k.1,
          ← Algebra.TensorProduct.algebraMap_apply]
        exact Subalgebra.algebraMap_mem _ c
    | add p q hp hq =>
        rw [map_add, TensorProduct.add_tmul]
        exact Subalgebra.add_mem _ hp hq
    | mul_X p j hp =>
        rw [map_mul, Work.DSG4c.ChartPushout.chartToPoly_X, tmul_one_mul]
        refine Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ?_)
        refine ⟨⟨toIdx a b (j.1, k.2), ?_⟩, ?_⟩
        · intro h
          exact j.2 (Prod.ext_iff.mp ((toIdx a b).injective h)).1
        · simp only [segreCoord, Equiv.symm_apply_apply,
            Work.DSG4c.ChartPushout.chartElemAll_self]
          rfl
  have keyB : ∀ y : chartRingB A b k.2,
      ((1 : chartRingA A a k.1) ⊗ₜ[A] y) ∈ Algebra.adjoin A (Set.range (segreCoord A a b k)) := by
    intro y
    obtain ⟨P, rfl⟩ := Work.DSG4c.ChartPushout.chartToPoly_surjective A b k.2 y
    induction P using MvPolynomial.induction_on with
    | C c =>
        rw [Work.DSG4c.ChartPushout.chartToPoly_C, ← awayChart_algebraMap A b k.2,
          ← Algebra.TensorProduct.algebraMap_apply']
        exact Subalgebra.algebraMap_mem _ c
    | add p q hp hq =>
        rw [map_add, TensorProduct.tmul_add]
        exact Subalgebra.add_mem _ hp hq
    | mul_X p j hp =>
        rw [map_mul, Work.DSG4c.ChartPushout.chartToPoly_X, one_tmul_mul]
        refine Subalgebra.mul_mem _ hp (Algebra.subset_adjoin ?_)
        refine ⟨⟨toIdx a b (k.1, j.1), ?_⟩, ?_⟩
        · intro h
          exact j.2 (Prod.ext_iff.mp ((toIdx a b).injective h)).2
        · simp only [segreCoord, Equiv.symm_apply_apply,
            Work.DSG4c.ChartPushout.chartElemAll_self]
          rfl
  have hT : Algebra.adjoin A (Set.range (segreCoord A a b k)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    refine TensorProduct.inductionOn z ?_ ?_
    · intro x y
      have hxy : x ⊗ₜ[A] y =
          (x ⊗ₜ[A] (1 : chartRingB A b k.2)) * ((1 : chartRingA A a k.1) ⊗ₜ[A] y) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hxy]
      exact Subalgebra.mul_mem _ (keyA x) (keyB y)
    · intro x y hx hy
      exact Subalgebra.add_mem _ hx hy
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := A) (segreCoord A a b k)) := by
    rw [← AlgHom.range_eq_top, MvPolynomial.aeval_range]
    exact hT
  have hp : Function.Surjective
      (Work.DSG4c.ChartPushout.polyToChart A (segreN a b) (toIdx a b k)) := by
    intro z
    refine ⟨Work.DSG4c.ChartPushout.chartToPoly A (segreN a b) (toIdx a b k) z, ?_⟩
    have h := congrArg (fun (f : MvPolynomial
        (Work.DSG4c.ChartPushout.chartIdx (segreN a b) (toIdx a b k)) A →+*
        MvPolynomial (Work.DSG4c.ChartPushout.chartIdx (segreN a b) (toIdx a b k)) A) => f z)
      (Work.DSG4c.ChartPushout.polyToChart_comp_chartToPoly A (segreN a b) (toIdx a b k))
    simpa using h
  exact hsurj.comp hp

/-- The preimage of the `m`-th standard chart of `ℙ^N_A` under the chartwise Segre map `sigma k` is
the intersection of the `k`-th and `(toIdx.symm m)`-th product charts. -/
theorem sigma_preimage_chartOpen (k : Fin (a+1) × Fin (b+1)) (m : Fin (segreN a b + 1)) :
    (sigma A a b k) ⁻¹ᵁ (chartOpenA A (segreN a b) m) =
      (V A a b k).ι ⁻¹ᵁ (V A a b ((toIdx a b).symm m)) := by
  apply preimage_inj_of_isIso (chartIso A a b k).hom
  have hL : (chartIso A a b k).hom ⁻¹ᵁ ((sigma A a b k) ⁻¹ᵁ (chartOpenA A (segreN a b) m))
      = (PrimeSpectrum.basicOpen
            (Work.DSG4c.ChartPushout.chartElemAll A a k.1 ((toIdx a b).symm m).1 ⊗ₜ[A]
              Work.DSG4c.ChartPushout.chartElemAll A b k.2 ((toIdx a b).symm m).2)
          : (Spec (CommRingCat.of
              (Work.DSG4c.awayChart A a k.1 ⊗[A] Work.DSG4c.awayChart A b k.2))).Opens) := by
    rw [← Scheme.Hom.comp_preimage]
    rw [sigma, chartIso_hom_sigmaChart_assoc, Scheme.Hom.comp_preimage, chartOpenA,
        awayι_preimage_chartCoord, SpecMap_preimage_basicOpen]
    simp only [CommRingCat.hom_ofHom]
    rw [segreChart_chartElemAll_dsg2 A a b k m]
  have hR : (chartIso A a b k).hom ⁻¹ᵁ ((V A a b k).ι ⁻¹ᵁ (V A a b ((toIdx a b).symm m)))
      = (PrimeSpectrum.basicOpen
            (Work.DSG4c.ChartPushout.chartElemAll A a k.1 ((toIdx a b).symm m).1 ⊗ₜ[A]
              Work.DSG4c.ChartPushout.chartElemAll A b k.2 ((toIdx a b).symm m).2)
          : (Spec (CommRingCat.of
              (Work.DSG4c.awayChart A a k.1 ⊗[A] Work.DSG4c.awayChart A b k.2))).Opens) := by
    rw [← Scheme.Hom.comp_preimage, chartIso_hom_ι]
    rw [V, Scheme.Hom.preimage_inf]
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
    rw [chartIncl_fst_away, chartIncl_snd_away, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    rw [chartOpenA, chartOpenB, awayι_preimage_chartCoord, awayι_preimage_chartCoord,
        SpecMap_preimage_basicOpen, SpecMap_preimage_basicOpen]
    simp only [CommRingCat.hom_ofHom]
    rw [← specBasicOpen_tmul]
    rfl
  rw [hL, hR]

set_option linter.style.haveILetI false in
/-- The Segre chart map `sigmaChart k` is a closed immersion (it is `Spec` of the surjective ring
map `segreChart k`, precomposed with the chart isomorphism). -/
theorem sigmaChart_isClosedImmersion (k : Fin (a+1) × Fin (b+1)) :
    IsClosedImmersion (sigmaChart A a b k) := by
  rw [sigmaChart]
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (segreChart A a b k))) :=
    IsClosedImmersion.spec_of_surjective _ (by simpa using segreChart_surjective_dsg2 A a b k)
  infer_instance

/-! ## The glued Segre map -/

/-- **The glued Segre map is a closed immersion.** -/
theorem isClosedImmersion_glue (A : Type u) [CommRing A] (a b : ℕ)
    (hcompat : ∀ k k' : Fin (a+1) × Fin (b+1),
      CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.pullback.fst (Work.DSG2.Segre.V A a b k).ι
            (Work.DSG2.Segre.V A a b k').ι) (Work.DSG2.Segre.sigma A a b k) =
        CategoryTheory.CategoryStruct.comp
          (CategoryTheory.Limits.pullback.snd (Work.DSG2.Segre.V A a b k).ι
            (Work.DSG2.Segre.V A a b k').ι) (Work.DSG2.Segre.sigma A a b k')) :
    AlgebraicGeometry.IsClosedImmersion
      ((Work.DSG2.Segre.cover A a b).glueMorphisms (Work.DSG2.Segre.sigma A a b) hcompat) := by
  set f : Xab A a b ⟶ DSMap.PSpace A (segreN a b) :=
    (cover A a b).glueMorphisms (sigma A a b) hcompat with hf
  have hι (k : Fin (a+1) × Fin (b+1)) : (V A a b k).ι ≫ f = sigma A a b k := by
    rw [hf]
    exact Scheme.Cover.ι_glueMorphisms (cover A a b) (sigma A a b) hcompat k
  -- the preimage of the `toIdx k`-th chart of `ℙ^N_A` is the product chart `V k`
  have hpre (k : Fin (a+1) × Fin (b+1)) :
      f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k) = V A a b k := by
    have hstep : ∀ l, (V A a b l).ι ⁻¹ᵁ (f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k)) =
        (V A a b l).ι ⁻¹ᵁ V A a b k := by
      intro l
      rw [← Scheme.Hom.comp_preimage, hι l]
      simpa using sigma_preimage_chartOpen A a b l (toIdx a b k)
    have hinf : ∀ l, V A a b l ⊓ (f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k)) =
        V A a b l ⊓ V A a b k := by
      intro l
      have h := congrArg (fun W => (V A a b l).ι ''ᵁ W) (hstep l)
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h
      exact h
    calc f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k)
        = ⊤ ⊓ (f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k)) := (top_inf_eq _).symm
      _ = (⨆ l, V A a b l) ⊓ (f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k)) := by
            rw [iSup_V_eq_top]
      _ = ⨆ l, (V A a b l ⊓ f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k)) := iSup_inf_eq _ _
      _ = ⨆ l, (V A a b l ⊓ V A a b k) := by simp only [hinf]
      _ = (⨆ l, V A a b l) ⊓ V A a b k := (iSup_inf_eq _ _).symm
      _ = ⊤ ⊓ V A a b k := by rw [iSup_V_eq_top]
      _ = V A a b k := top_inf_eq _
  -- `IsClosedImmersion` is local at the target, and the charts of `ℙ^N_A` cover the target
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun k : Fin (a+1) × Fin (b+1) => chartOpenA A (segreN a b) (toIdx a b k)) ?_ ?_
  · rw [Equiv.iSup_comp (toIdx a b)]
    exact iSup_chartOpenA A (segreN a b)
  · intro k
    have hU : f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k) = V A a b k := hpre k
    let e : (V A a b k).toScheme ≅ (f ⁻¹ᵁ chartOpenA A (segreN a b) (toIdx a b k)).toScheme :=
      (Scheme.isoOfEq (Xab A a b) hU).symm
    let e2 : Spec (CommRingCat.of (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))) ≅
        (chartOpenA A (segreN a b) (toIdx a b k)).toScheme :=
      IsOpenImmersion.isoOfRangeEq (Work.DSG4c.chartι A (segreN a b) (toIdx a b k))
        (chartOpenA A (segreN a b) (toIdx a b k)).ι (by
          rw [← Scheme.Hom.coe_opensRange (Work.DSG4c.chartι A (segreN a b) (toIdx a b k)),
            ← Scheme.Hom.coe_opensRange (chartOpenA A (segreN a b) (toIdx a b k)).ι,
            Proj.opensRange_awayι, Scheme.Opens.opensRange_ι])
    -- the restriction of `f` to the chart is (up to isomorphism) the chartwise Segre map
    have hkey : e.hom ≫ (f ∣_ chartOpenA A (segreN a b) (toIdx a b k)) ≫ e2.inv =
        sigmaChart A a b k := by
      refine (cancel_mono (Work.DSG4c.chartι A (segreN a b) (toIdx a b k))).mp ?_
      simp only [e, e2, Iso.symm_hom, Category.assoc]
      rw [IsOpenImmersion.isoOfRangeEq_inv_fac, morphismRestrict_ι]
      rw [← Category.assoc, Scheme.isoOfEq_inv_ι, hι k, sigma]
    have hcl : IsClosedImmersion
        (e.hom ≫ (f ∣_ chartOpenA A (segreN a b) (toIdx a b k)) ≫ e2.inv) := by
      rw [hkey]
      exact sigmaChart_isClosedImmersion A a b k
    exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ e2.inv).mp
      ((MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) e.hom _).mp hcl)

end Work.DSG2.Segre
