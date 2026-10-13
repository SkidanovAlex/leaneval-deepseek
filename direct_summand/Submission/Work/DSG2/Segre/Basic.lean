import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSG4c.Basic
import Submission.Work.DSG4c.ChartPushout.Defs
import Submission.Work.DSG4c.ProjBaseChange.isPullback_baseChangeMap_of_chartPushout

/-!
# The Segre embedding `ℙ^a_A ×_A ℙ^b_A ↪ ℙ^{(a+1)(b+1)-1}_A` (area DSG2)

This file sets up the vocabulary for the Segre embedding.  The source is the fibre product
`X = ℙ^a_A ×_{Spec A} ℙ^b_A`, and for `k : Fin (a+1) × Fin (b+1)` we have

* `V k` — the product chart `D₊(x_{k.1}) ×_{Spec A} D₊(y_{k.2}) ⊆ X`, i.e. the locus where the
  section `z_k` of `O(1,1)` is invertible;
* `chartIncl k : Spec (A[x/x_{k.1}] ⊗_A A[y/y_{k.2}]) ⟶ X` — the (open immersion) chart
  inclusion, obtained as the product of the two standard charts of `ℙ^a` and `ℙ^b`;
* `chartIso k` — the induced isomorphism onto the chart.

The target is `ℙ^N_A` with `N = (a+1)(b+1)-1`; the variables of `ℙ^N_A` are indexed by
`Fin (N+1)`, and we fix the identification `toIdx : Fin (a+1) × Fin (b+1) ≃ Fin (N+1)`.

-/

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Work.DSG2.Segre

universe u

variable (A : Type u) [CommRing A] (a b : ℕ)

noncomputable instance instAlgebraAwayChart (n : ℕ) (i : Fin (n+1)) :
    Algebra A (Work.DSG4c.awayChart A n i) :=
  (Work.DSG4c.chartMap A n i).toAlgebra

lemma awayChart_algebraMap (n : ℕ) (i : Fin (n+1)) :
    algebraMap A (Work.DSG4c.awayChart A n i) = Work.DSG4c.chartMap A n i := rfl

/-- The target index of the Segre embedding. -/
def segreN (a b : ℕ) : ℕ := (a + 1) * (b + 1) - 1

lemma segreN_add_one : segreN a b + 1 = (a + 1) * (b + 1) := by
  rw [segreN]
  exact Nat.succ_pred_eq_of_pos (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))

/-- The identification of the coordinates of `ℙ^N_A` with pairs of coordinates of `ℙ^a_A` and
`ℙ^b_A`. -/
noncomputable def toIdx : Fin (a + 1) × Fin (b + 1) ≃ Fin (segreN a b + 1) :=
  (finProdFinEquiv (m := a + 1) (n := b + 1)).trans (finCongr (segreN_add_one a b).symm)

/-- The source of the Segre embedding: `ℙ^a_A ×_{Spec A} ℙ^b_A`. -/
noncomputable abbrev Xab : Scheme.{u} :=
  Limits.pullback (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)

/-- The `i`-th standard chart of `ℙ^a_A`. -/
noncomputable abbrev chartOpenA (i : Fin (a+1)) : (DSMap.PSpace A a).Opens :=
  Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X i)

/-- The `j`-th standard chart of `ℙ^b_A`. -/
noncomputable abbrev chartOpenB (j : Fin (b+1)) : (DSMap.PSpace A b).Opens :=
  Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X j)

/-- The product chart of `ℙ^a_A ×_{Spec A} ℙ^b_A` indexed by `k = (i,j)`:
the locus where `x_i ≠ 0` and `y_j ≠ 0`. -/
noncomputable def V (k : Fin (a+1) × Fin (b+1)) : (Xab A a b).Opens :=
  (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ chartOpenA A a k.1 ⊓
    (pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ chartOpenB A b k.2

/-- The composite map of the two structure maps of the standard charts. -/
lemma chartι_comp_toSpec_A (i : Fin (a+1)) :
    Work.DSG4c.chartι A a i ≫ DSMap.PSpace.toSpec A a =
      Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A a i)) :=
  Work.DSG4c.chartι_comp_toSpec A a i

lemma chartι_comp_toSpec_B (j : Fin (b+1)) :
    Work.DSG4c.chartι A b j ≫ DSMap.PSpace.toSpec A b =
      Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A b j)) :=
  Work.DSG4c.chartι_comp_toSpec A b j

namespace chartIncl

variable {A a b}

lemma comm_fst (i : Fin (a+1)) :
    Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A a i)) ≫
        (𝟙 (Spec (CommRingCat.of A))) = Work.DSG4c.chartι A a i ≫ DSMap.PSpace.toSpec A a := by
  rw [Category.comp_id, chartι_comp_toSpec_A]

lemma comm_snd (j : Fin (b+1)) :
    Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A b j)) ≫
        (𝟙 (Spec (CommRingCat.of A))) = Work.DSG4c.chartι A b j ≫ DSMap.PSpace.toSpec A b := by
  rw [Category.comp_id, chartι_comp_toSpec_B]

end chartIncl

/-- The product chart inclusion `Spec (A[x/x_i] ⊗_A A[y/y_j]) ⟶ ℙ^a_A ×_{Spec A} ℙ^b_A`. -/
noncomputable def chartIncl (i : Fin (a+1)) (j : Fin (b+1)) :
    Spec (CommRingCat.of (Work.DSG4c.awayChart A a i ⊗[A] Work.DSG4c.awayChart A b j)) ⟶
      Xab A a b :=
  (pullbackSpecIso A (Work.DSG4c.awayChart A a i) (Work.DSG4c.awayChart A b j)).inv ≫
    pullback.map (Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A a i)))
      (Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A b j)))
      (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)
      (Work.DSG4c.chartι A a i) (Work.DSG4c.chartι A b j) (𝟙 (Spec (CommRingCat.of A)))
      (chartIncl.comm_fst i) (chartIncl.comm_snd j)

instance chartIncl_isOpenImmersion (i : Fin (a+1)) (j : Fin (b+1)) :
    IsOpenImmersion (chartIncl A a b i j) := by
  unfold chartIncl
  exact IsOpenImmersion.comp _ _

lemma chartIncl_opensRange (i : Fin (a+1)) (j : Fin (b+1)) :
    (chartIncl A a b i j).opensRange = V A a b (i, j) := by
  have h2 : (chartIncl A a b i j).opensRange =
      (pullback.map (Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A a i)))
        (Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A b j)))
        (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)
        (Work.DSG4c.chartι A a i) (Work.DSG4c.chartι A b j) (𝟙 (Spec (CommRingCat.of A)))
        (chartIncl.comm_fst i) (chartIncl.comm_snd j)).opensRange := by
    unfold chartIncl
    rw [Scheme.Hom.opensRange_comp_of_isIso]
  rw [h2]
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_opensRange]
  rw [AlgebraicGeometry.Scheme.Pullback.range_map
      (f := Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A a i)))
      (g := Spec.map (CommRingCat.ofHom (Work.DSG4c.chartMap A b j)))
      (f' := DSMap.PSpace.toSpec A a) (g' := DSMap.PSpace.toSpec A b)
      (i₁ := Work.DSG4c.chartι A a i) (i₂ := Work.DSG4c.chartι A b j)
      (i₃ := 𝟙 (Spec (CommRingCat.of A)))
      (e₁ := chartIncl.comm_fst i) (e₂ := chartIncl.comm_snd j)]
  rw [← Scheme.Hom.coe_opensRange (Work.DSG4c.chartι A a i),
    ← Scheme.Hom.coe_opensRange (Work.DSG4c.chartι A b j)]
  rw [Proj.opensRange_awayι, Proj.opensRange_awayι]
  rw [V]
  rfl

/-- The canonical isomorphism of the product chart with the spectrum of the tensor product of
the two chart rings. -/
noncomputable def chartIso (k : Fin (a+1) × Fin (b+1)) :
    Spec (CommRingCat.of (Work.DSG4c.awayChart A a k.1 ⊗[A] Work.DSG4c.awayChart A b k.2)) ≅
      (V A a b k).toScheme :=
  IsOpenImmersion.isoOfRangeEq (chartIncl A a b k.1 k.2) (V A a b k).ι
    (by
      rw [← Scheme.Hom.coe_opensRange (chartIncl A a b k.1 k.2), chartIncl_opensRange,
        ← Scheme.Hom.coe_opensRange (V A a b k).ι, Scheme.Opens.opensRange_ι])

@[reassoc (attr := simp)]
lemma chartIso_hom_ι (k : Fin (a+1) × Fin (b+1)) :
    (chartIso A a b k).hom ≫ (V A a b k).ι = chartIncl A a b k.1 k.2 :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end Work.DSG2.Segre

namespace Work.DSG2.Segre

universe u

variable (A : Type u) [CommRing A] (a b : ℕ)

open scoped TensorProduct

/-- The coordinate ring of the `i`-th chart of `ℙ^a_A`. -/
noncomputable abbrev chartRingA (i : Fin (a+1)) : Type u := Work.DSG4c.awayChart A a i

/-- The coordinate ring of the `j`-th chart of `ℙ^b_A`. -/
noncomputable abbrev chartRingB (j : Fin (b+1)) : Type u := Work.DSG4c.awayChart A b j

/-- The product-chart coordinate ring. -/
noncomputable abbrev chartRing (k : Fin (a+1) × Fin (b+1)) : Type u :=
  chartRingA A a k.1 ⊗[A] chartRingB A b k.2

/-- The ring of functions on the product chart `V k`, identified with the tensor product of the
two chart rings via the chart isomorphism. -/
noncomputable def chartΓ (k : Fin (a+1) × Fin (b+1)) :
    chartRing A a b k →+* Γ((V A a b k).toScheme, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (chartRing A a b k))).inv ≫
    (chartIso A a b k).inv.appTop).hom

/-- The `p`-th `x`-coordinate of the `i`-th chart of `ℙ^a_A`. -/
noncomputable abbrev segreElemA (i : Fin (a+1)) (p : Fin (a+1)) : chartRingA A a i :=
  Work.DSG4c.ChartPushout.chartElemAll A a i p

/-- The `q`-th `y`-coordinate of the `j`-th chart of `ℙ^b_A`. -/
noncomputable abbrev segreElemB (j : Fin (b+1)) (q : Fin (b+1)) : chartRingB A b j :=
  Work.DSG4c.ChartPushout.chartElemAll A b j q

/-- The (dehomogenized) Segre map from the `k`-th chart ring of `ℙ^N_A` onto the product chart
ring.  It sends the coordinate `z_m/z_k` to `x_p/x_{k.1} ⊗ y_q/y_{k.2}` where `m = (p,q)`. -/
noncomputable def segreChart (k : Fin (a+1) × Fin (b+1)) :
    Work.DSG4c.awayChart A (segreN a b) (toIdx a b k) →+* chartRing A a b k :=
  (MvPolynomial.aeval (R := A)
      (fun j : Work.DSG4c.ChartPushout.chartIdx (segreN a b) (toIdx a b k) =>
        segreElemA A a k.1 ((toIdx a b).symm j.1).1 ⊗ₜ[A]
          segreElemB A b k.2 ((toIdx a b).symm j.1).2)).toRingHom.comp
    (Work.DSG4c.ChartPushout.polyToChart A (segreN a b) (toIdx a b k))

/-- The `k`-th chart of `X` mapped to the `k`-th chart of `ℙ^N_A`. -/
noncomputable def sigmaChart (k : Fin (a+1) × Fin (b+1)) :
    (V A a b k).toScheme ⟶
      Spec (CommRingCat.of (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))) :=
  (chartIso A a b k).inv ≫ Spec.map (CommRingCat.ofHom (segreChart A a b k))

/-- The `k`-th chart of `X` mapped into `ℙ^N_A` (the Segre embedding restricted to the chart,
a closed immersion onto the part of the Segre locus lying in the `k`-th chart). -/
noncomputable def sigma (k : Fin (a+1) × Fin (b+1)) :
    (V A a b k).toScheme ⟶ DSMap.PSpace A (segreN a b) :=
  sigmaChart A a b k ≫ Work.DSG4c.chartι A (segreN a b) (toIdx a b k)

end Work.DSG2.Segre

namespace Work.DSG2.Segre

universe u

variable (A : Type u) [CommRing A] (a b : ℕ)

/-- The irrelevant ideal of the polynomial ring is spanned by the coordinates. -/
lemma irrelevant_le_span_X (n : ℕ) :
    (HomogeneousIdeal.irrelevant (DSMap.PGr A n)).toIdeal ≤
      Ideal.span (Set.range (fun i : Fin (n+1) => (MvPolynomial.X i : MvPolynomial (Fin (n+1)) A))) :=
  Work.DSG4c.ProjBaseChange.irrelevant_toIdeal_le_span_X A n

lemma iSup_chartOpenA : ⨆ i : Fin (a+1), chartOpenA A a i = ⊤ :=
  Proj.iSup_basicOpen_eq_top (DSMap.PGr A a) (fun i : Fin (a+1) => (MvPolynomial.X i))
    (irrelevant_le_span_X A a)

lemma iSup_chartOpenB : ⨆ j : Fin (b+1), chartOpenB A b j = ⊤ :=
  Proj.iSup_basicOpen_eq_top (DSMap.PGr A b) (fun j : Fin (b+1) => (MvPolynomial.X j))
    (irrelevant_le_span_X A b)

/-- The product charts cover `ℙ^a_A ×_{Spec A} ℙ^b_A`. -/
theorem iSup_V_eq_top :
    ⨆ k : Fin (a+1) × Fin (b+1), V A a b k = ⊤ := by
  have hA : (⨆ i : Fin (a+1),
      (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ
        chartOpenA A a i) = ⊤ := by
    change iSup ((TopologicalSpace.Opens.map
      (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)).base).obj ∘
        chartOpenA A a) = ⊤
    rw [← TopologicalSpace.Opens.map_iSup
        (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)).base
        (chartOpenA A a),
      iSup_chartOpenA A a]
    simp
  have hB : (⨆ j : Fin (b+1),
      (pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ
        chartOpenB A b j) = ⊤ := by
    change iSup ((TopologicalSpace.Opens.map
      (pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)).base).obj ∘
        chartOpenB A b) = ⊤
    rw [← TopologicalSpace.Opens.map_iSup
        (pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)).base
        (chartOpenB A b),
      iSup_chartOpenB A b]
    simp
  refine le_antisymm le_top ?_
  show ⊤ ≤ ⨆ k : Fin (a+1) × Fin (b+1),
      (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ
          chartOpenA A a k.1 ⊓
        (pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ
          chartOpenB A b k.2
  rw [← iSup_inf_iSup
    (f := fun i : Fin (a+1) =>
      (pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ chartOpenA A a i)
    (g := fun j : Fin (b+1) =>
      (pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b)) ⁻¹ᵁ chartOpenB A b j),
    hA, hB]
  simp

/-- The open cover of `ℙ^a_A ×_{Spec A} ℙ^b_A` by the product charts. -/
noncomputable def cover : (Xab A a b).OpenCover :=
  Scheme.openCoverOfIsOpenCover (Xab A a b) (V A a b) (iSup_V_eq_top A a b)

end Work.DSG2.Segre
