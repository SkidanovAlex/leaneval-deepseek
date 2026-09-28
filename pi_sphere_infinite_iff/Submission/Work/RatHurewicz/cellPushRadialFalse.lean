import Mathlib
import Submission.Work.RatHurewicz.cellDefs
import Submission.Work.RatHurewicz.cycleModelDefs

/-!
# `Work.RatHurewicz.cellPushRadial` is **false**: a machine-checked refutation

The statement `Work.RatHurewicz.cellPushRadial` (equivalently `Work.RatHurewicz.modelCellPush`),
as written, is false; the counterexample below is checked by the kernel (no `sorry` anywhere in
this file).  The requested statement itself is kept, unchanged, at the end of the file (with the
`sorry` it had).

## The counterexample

Take

* `X := Δ³ = stdSimplex ℝ (Fin 4)`, `x₀ :=` the vertex `0`, `n := 2`, and the `MData` `cntD` with a
  *single* index (`D.Idx = PUnit`) whose simplex map is the **identity** `Δ³ → Δ³` (a nondegenerate
  top cell) and whose arc is the constant arc at `x₀`;
* `S := cntS = {0,1,2} ⊂ Fin 4`, a facet of the top cell; here `2 < S.card` holds.

The model `Model cntD` is then the quotient of `Δ³ ⊔ I` identifying only the vertex `0` of `Δ³`
with the point `0` of the arc; it embeds into the Hausdorff space `Δ³ × I` (`cntPhi_injective`),
so limits in it are unique (`cnt_tendsto_unique`).

Let `x` be any point of the *relative interior* of the face `S` (`ptSupport x = S`, all coordinates
in `S` positive: `xA`, `xB`), and `z := cntMk x ∈ openCell cntD PUnit.unit cntS`.  Let `y n` be the
points of the *interior of the top cell* converging to `x` — the convex combinations
`(1-ε) x + ε • v₃` with `ε = 1/(n+2)` (`seqPt`).  Then

* `ptSupport (y n)` has cardinality `4 ≠ 3 = S.card`, and the cardinality of the support is
  invariant along the gluing relation (`rawWeight_eqvGen`, `modelWeight`); hence
  `cntMk (y n) ∉ openCell cntD PUnit.unit cntS` (`not_mem_openCell_of_card_ne`);
* `cntMk (y n) → z` (continuity of the inclusion of the top cell, `tendsto_seqPt`).

If the conclusion of `cellPushRadial` held, the second clause would force
`Φ (1, cntMk (y n)) = cntMk (y n) → z`, while continuity of `Φ` gives
`Φ (1, cntMk (y n)) → Φ (1, z)`; uniqueness of limits yields `Φ (1, z) = z ∈ openCell …`, which
contradicts the third clause (`Φ (1, z) ∉ openCell …`).  This is `cnt_contradiction_at`, and
`not_cellPushRadial_instance` is the resulting refutation of the instantiated statement.

## Why the statement is misframed, and what the true statement is

`openCell D i S` is the image of the *relative interior* of a face, and such an image is **not
open** in `Model D` as soon as the face is a proper face of a top cell: points in the interior of
the top cell (of *larger* support) accumulate at each of its points, and the second clause
requires those points to be fixed.  So a continuous `Φ` with the required properties can exist
only when nothing accumulates: the statement is true for the top cells (`S.card = n+2`) but false
for proper faces.

The repair used by the plan (`COMPRESS_NOTES.md`: "the path's image lies in the `k`-skeleton") is
to restrict the domain of the homotopy to the skeleton.  With `S.card = k+1`, the points of
`skel D (S.card - 1)` near `cntMk x` are either in `openCell D i S` or lie on the boundary of the
face `S`, where the radial push is the identity, so continuity holds.  Suggested statement:

```
∃ (o : Model D) (Φ : C(unitInterval × {z : Model D // z ∈ skel D (S.card - 1) ∧ z ≠ o}, Model D)),
  o ∈ openCell D i S ∧ (∀ z, Φ (0, z) = z) ∧
  (∀ z, (z : Model D) ∉ openCell D i S → ∀ s, Φ (s, z) = z) ∧
  (∀ z, (z : Model D) ∈ openCell D i S →
      Φ (1, z) ∈ closedCell D i S ∧ Φ (1, z) ∉ openCell D i S)
```
-/

open scoped Topology Simplicial unitInterval
open Filter

namespace Work.RatHurewicz

noncomputable section

/-! ## The support of a point of a standard simplex (any arity) -/

/-- The support of a point of a standard simplex: the vertices with a nonzero coordinate.  This is
`ptSupport` without the arity restriction `Fin (n+2)`. -/
def supp {m : ℕ} (x : stdSimplex ℝ (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter (fun k => (x : Fin m → ℝ) k ≠ 0)

theorem ptSupport_eq_supp {n : ℕ} (x : stdSimplex ℝ (Fin (n+2))) : ptSupport x = supp x := rfl

theorem mem_supp {m : ℕ} {x : stdSimplex ℝ (Fin m)} {k : Fin m} :
    k ∈ supp x ↔ (x : Fin m → ℝ) k ≠ 0 := by simp [supp]

/-- The support of `stdSimplex.map f x` is contained in the image of the support. -/
theorem supp_map_subset {m m' : ℕ} (f : Fin m → Fin m') (x : stdSimplex ℝ (Fin m)) :
    supp (stdSimplex.map f x) ⊆ (supp x).image f := by
  intro j hj
  rw [mem_supp] at hj
  rw [Finset.mem_image]
  by_contra hcon
  push Not at hcon
  apply hj
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  by_contra hxi
  exact hcon i (by rwa [mem_supp]) hi.2

/-- For an injective `f`, the support of `stdSimplex.map f x` is the image of the support. -/
theorem supp_map_of_injective {m m' : ℕ} {f : Fin m → Fin m'} (hf : Function.Injective f)
    (x : stdSimplex ℝ (Fin m)) : supp (stdSimplex.map f x) = (supp x).image f := by
  refine Finset.Subset.antisymm (supp_map_subset f x) ?_
  intro j hj
  rw [Finset.mem_image] at hj
  obtain ⟨i₀, hi₀, rfl⟩ := hj
  rw [mem_supp]
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  have : (Finset.univ.filter (fun i => f i = f i₀)) = {i₀} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hf h, fun h => by rw [h]⟩
  rw [this, Finset.sum_singleton]
  rwa [mem_supp] at hi₀

/-- A face of `stdSimplex.map` preserves the cardinality of the support. -/
theorem card_supp_facept {n : ℕ} (p : Fin (n+2)) (x : stdSimplex ℝ (Fin (n+1))) :
    (supp (facept (n+1) p x)).card = (supp x).card := by
  have hf : Function.Injective (p.succAbove : Fin (n+1) → Fin (n+2)) :=
    Fin.succAbove_right_injective
  rw [show (facept (n+1) p) x = stdSimplex.map p.succAbove x from rfl,
    supp_map_of_injective hf]
  exact Finset.card_image_of_injective _ hf

/-- The support of a vertex is a singleton. -/
theorem card_ptSupport_vertex {n : ℕ} (k : Fin (n+2)) :
    (ptSupport (stdSimplex.vertex k)).card = 1 := by
  have h : ∀ j : Fin (n+2),
      ((stdSimplex.vertex (S := ℝ) k : stdSimplex ℝ (Fin (n+2))) : Fin (n+2) → ℝ) j ≠ 0 ↔
        j = k := by
    intro j
    rw [stdSimplex.vertex_coe]
    constructor
    · intro hj
      by_contra hjk
      rw [Pi.single_eq_of_ne hjk] at hj
      exact hj rfl
    · intro hjk; subst hjk; rw [Pi.single_eq_same]; exact one_ne_zero
  rw [ptSupport, Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact h j

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-- `rawWeight` is invariant under a single generating relation of the model. -/
theorem rawWeight_modelRel (D : MData X n x₀) {a b : Raw D} (h : modelRel D a b) :
    rawWeight D a = rawWeight D b := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, hmaps⟩ | ⟨i, ha, hb⟩ | ⟨i, j, ha, hb⟩
  · rw [rawWeight_inl, rawWeight_inl, ptSupport_eq_supp, ptSupport_eq_supp,
      card_supp_facept, card_supp_facept]
  · subst ha; subst hb
    rw [rawWeight_inl, rawWeight_inr, card_ptSupport_vertex]
  · subst ha; subst hb; rfl

/-- **`rawWeight` is invariant along the gluing relation**: two representatives of the same model
point carry supports of the same cardinality. -/
theorem rawWeight_eqvGen (D : MData X n x₀) :
    ∀ a b : Raw D, Relation.EqvGen (modelRel D) a b → rawWeight D a = rawWeight D b := by
  intro a b h
  induction h with
  | rel x y hr => exact rawWeight_modelRel D hr
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- The weight of a model point: the cardinality of the support of any representative. -/
noncomputable def modelWeight (D : MData X n x₀) (z : Model D) : ℕ :=
  Quotient.lift (rawWeight D) (rawWeight_eqvGen D) z

theorem modelWeight_mk_inl (D : MData X n x₀) (i : D.Idx) (x : stdSimplex ℝ (Fin (n+2))) :
    modelWeight D (Quotient.mk'' (Sum.inl (⟨i, x⟩ :
      Σ _ : D.Idx, stdSimplex ℝ (Fin (n+2))))) = (ptSupport x).card := rfl

theorem modelWeight_mk_inr (D : MData X n x₀) (i : D.Idx) (t : unitInterval) :
    modelWeight D (Quotient.mk'' (Sum.inr (⟨i, t⟩ : Σ _ : D.Idx, unitInterval))) = 1 := rfl

/-- **Two points of the same copy of a simplex with supports of different cardinality represent
different model points.** -/
theorem mk_inl_ne_of_card_ne (D : MData X n x₀) {i j : D.Idx}
    {x y : stdSimplex ℝ (Fin (n+2))} (hxy : (ptSupport x).card ≠ (ptSupport y).card) :
    (Quotient.mk'' (Sum.inl (⟨i, x⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n+2)))) : Model D) ≠
      Quotient.mk'' (Sum.inl (⟨j, y⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n+2)))) := by
  intro h
  have hw : (ptSupport x).card = (ptSupport y).card := by
    have := congrArg (modelWeight D) h
    rwa [modelWeight_mk_inl, modelWeight_mk_inl] at this
  exact hxy hw

/-- **A point of a simplex whose support does not have the cardinality of `S` is not in the open
cell `openCell D i S`.** -/
theorem not_mem_openCell_of_card_ne (D : MData X n x₀) (i : D.Idx)
    (S : Finset (Fin (n+2))) {y : stdSimplex ℝ (Fin (n+2))}
    (hy : (ptSupport y).card ≠ S.card) :
    (Quotient.mk'' (Sum.inl (⟨i, y⟩ : Σ _ : D.Idx,
      stdSimplex ℝ (Fin (n+2)))) : Model D) ∉ openCell D i S := by
  rintro ⟨x, hx, hxy⟩
  exact mk_inl_ne_of_card_ne D (by rw [hx]; exact hy) hxy.symm

/-! ## The counterexample instance -/

/-- The space of the counterexample: the standard `3`-simplex. -/
abbrev cntX : Type := stdSimplex ℝ (Fin 4)

/-- The `MData` of the counterexample: a single *nondegenerate* `3`-simplex (the identity map),
with its connecting arc collapsed at the vertex `0`. -/
def cntD : MData cntX 2 (stdSimplex.vertex (0 : Fin 4)) where
  Idx := PUnit
  finIdx := inferInstance
  simplexMap := fun _ => ContinuousMap.id _
  arcPath := fun _ => ContinuousMap.const _ (stdSimplex.vertex (0 : Fin 4))
  arc_zero := fun _ => rfl
  arc_one := fun _ => rfl

theorem cntD_simplexMap_apply (i : cntD.Idx) (y : cntX) : cntD.simplexMap i y = y := rfl

theorem continuous_sigma_snd {ι X : Type*} [TopologicalSpace X] :
    Continuous (fun p : Sigma (fun _ : ι => X) => p.2) :=
  continuous_sigma fun _ => continuous_id

/-! ## The separating map -/

/-- First coordinate of the model: the simplex coordinate, the arc collapsed to the vertex `0`. -/
def cntPsi1Fun : Raw cntD → cntX :=
  Sum.elim (fun p => p.2) (fun _ => stdSimplex.vertex (0 : Fin 4))

/-- Second coordinate of the model: `0` on the simplex, the arc coordinate on the arc. -/
def cntPsi2Fun : Raw cntD → unitInterval :=
  Sum.elim (fun _ => 0) (fun p => p.2)

theorem cntPsi1Fun_rel : ∀ a b, modelRel cntD a b → cntPsi1Fun a = cntPsi1Fun b := by
  intro a b h
  rcases h with ⟨i, j, p, q, x, rfl, rfl, hmaps⟩ | ⟨i, ha, hb⟩ | ⟨i, j, ha, hb⟩
  · have h2 : facept (2+1) p x = facept (2+1) q x := by
      have h' := congrFun (congrArg DFunLike.coe hmaps) x
      simp only [ContinuousMap.comp_apply, cntD_simplexMap_apply] at h'
      exact h'
    simpa [cntPsi1Fun] using h2
  · subst ha; subst hb; rfl
  · subst ha; subst hb; rfl

theorem cntPsi2Fun_rel : ∀ a b, modelRel cntD a b → cntPsi2Fun a = cntPsi2Fun b := by
  intro a b h
  rcases h with ⟨i, j, p, q, x, rfl, rfl, hmaps⟩ | ⟨i, ha, hb⟩ | ⟨i, j, ha, hb⟩
  · rfl
  · subst ha; subst hb; rfl
  · subst ha; subst hb; rfl

theorem cntPsi1Fun_eqv : ∀ a b, Relation.EqvGen (modelRel cntD) a b →
    cntPsi1Fun a = cntPsi1Fun b := by
  intro a b h
  induction h with
  | rel x y hr => exact cntPsi1Fun_rel x y hr
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

theorem cntPsi2Fun_eqv : ∀ a b, Relation.EqvGen (modelRel cntD) a b →
    cntPsi2Fun a = cntPsi2Fun b := by
  intro a b h
  induction h with
  | rel x y hr => exact cntPsi2Fun_rel x y hr
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- The first coordinate of the model. -/
def cntPsi1 : Model cntD → cntX := Quotient.lift cntPsi1Fun cntPsi1Fun_eqv

/-- The second coordinate of the model. -/
def cntPsi2 : Model cntD → unitInterval := Quotient.lift cntPsi2Fun cntPsi2Fun_eqv

theorem continuous_cntPsi1Fun : Continuous cntPsi1Fun := by
  refine Continuous.sumElim ?_ ?_
  · exact continuous_sigma_snd
  · exact continuous_const

theorem continuous_cntPsi2Fun : Continuous cntPsi2Fun := by
  refine Continuous.sumElim ?_ ?_
  · exact continuous_const
  · exact continuous_sigma_snd

theorem continuous_cntPsi1 : Continuous cntPsi1 :=
  continuous_cntPsi1Fun.quotient_lift (s := Relation.EqvGen.setoid (modelRel cntD)) cntPsi1Fun_eqv

theorem continuous_cntPsi2 : Continuous cntPsi2 :=
  continuous_cntPsi2Fun.quotient_lift (s := Relation.EqvGen.setoid (modelRel cntD)) cntPsi2Fun_eqv

/-- The separating map of the model into a Hausdorff space. -/
def cntPhi : Model cntD → cntX × unitInterval := fun z => (cntPsi1 z, cntPsi2 z)

theorem continuous_cntPhi : Continuous cntPhi := continuous_cntPsi1.prodMk continuous_cntPsi2

theorem cntPhi_mk_inl_fst (p : Σ _ : cntD.Idx, stdSimplex ℝ (Fin 4)) :
    (cntPhi (Quotient.mk'' (Sum.inl p))).1 = p.2 := rfl

theorem cntPhi_mk_inl_snd (p : Σ _ : cntD.Idx, stdSimplex ℝ (Fin 4)) :
    (cntPhi (Quotient.mk'' (Sum.inl p))).2 = 0 := rfl

theorem cntPhi_mk_inr_fst (p : Σ _ : cntD.Idx, unitInterval) :
    (cntPhi (Quotient.mk'' (Sum.inr p))).1 = stdSimplex.vertex (0 : Fin 4) := rfl

theorem cntPhi_mk_inr_snd (p : Σ _ : cntD.Idx, unitInterval) :
    (cntPhi (Quotient.mk'' (Sum.inr p))).2 = p.2 := rfl

/-- **The separating map is injective**: this instance of the model embeds in `Δ³ × I`. -/
theorem cntPhi_injective : Function.Injective cntPhi := by
  intro z w h
  induction z using Quotient.inductionOn with
  | _ a =>
    induction w using Quotient.inductionOn with
    | _ b =>
      rcases a with ⟨i, x⟩ | ⟨i, t⟩ <;> rcases b with ⟨j, y⟩ | ⟨j, t'⟩
      · have hxy : x = y := by
          have h' := congrArg Prod.fst h
          simpa only [cntPhi_mk_inl_fst] using h'
        rw [hxy]
        have hij : i = j := by cases i; cases j; rfl
        rw [hij]
      · have hx : x = stdSimplex.vertex (0 : Fin 4) := by
          have h' := congrArg Prod.fst h
          simpa only [cntPhi_mk_inl_fst, cntPhi_mk_inr_fst] using h'
        have ht : t' = 0 := by
          have h' := congrArg Prod.snd h
          simpa only [cntPhi_mk_inl_snd, cntPhi_mk_inr_snd] using h'.symm
        subst hx; subst ht
        have hij : i = j := by cases i; cases j; rfl
        rw [hij]
        have hrel : modelRel cntD
            (Sum.inl (⟨i, stdSimplex.vertex (0 : Fin 4)⟩ :
              Σ _ : cntD.Idx, stdSimplex ℝ (Fin 4)))
            (Sum.inr (⟨i, (0 : unitInterval)⟩ : Σ _ : cntD.Idx, unitInterval)) :=
          Or.inr (Or.inl ⟨i, rfl, rfl⟩)
        exact Quotient.sound (Relation.EqvGen.rel _ _ hrel)
      · have hy : y = stdSimplex.vertex (0 : Fin 4) := by
          have h' := congrArg Prod.fst h
          simpa only [cntPhi_mk_inl_fst, cntPhi_mk_inr_fst] using h'.symm
        have ht : t = 0 := by
          have h' := congrArg Prod.snd h
          simpa only [cntPhi_mk_inl_snd, cntPhi_mk_inr_snd] using h'
        subst hy; subst ht
        have hij : i = j := by cases i; cases j; rfl
        rw [hij]
        have hrel : modelRel cntD
            (Sum.inl (⟨i, stdSimplex.vertex (0 : Fin 4)⟩ :
              Σ _ : cntD.Idx, stdSimplex ℝ (Fin 4)))
            (Sum.inr (⟨i, (0 : unitInterval)⟩ : Σ _ : cntD.Idx, unitInterval)) :=
          Or.inr (Or.inl ⟨i, rfl, rfl⟩)
        exact (Quotient.sound (Relation.EqvGen.rel _ _ hrel)).symm
      · have htt : t = t' := by
          have h' := congrArg Prod.snd h
          simpa only [cntPhi_mk_inr_snd] using h'
        rw [htt]
        have hij : i = j := by cases i; cases j; rfl
        rw [hij]

/-- **Limits in this instance of the model are unique** (through the injective map `cntPhi`). -/
theorem cnt_tendsto_unique {α : Type*} {l : Filter α} [l.NeBot] {u : α → Model cntD}
    {a b : Model cntD} (ha : Tendsto u l (𝓝 a)) (hb : Tendsto u l (𝓝 b)) : a = b := by
  have h1 : Tendsto (fun n => cntPhi (u n)) l (𝓝 (cntPhi a)) :=
    (continuous_cntPhi.tendsto a).comp ha
  have h2 : Tendsto (fun n => cntPhi (u n)) l (𝓝 (cntPhi b)) :=
    (continuous_cntPhi.tendsto b).comp hb
  exact cntPhi_injective (tendsto_nhds_unique h1 h2)

/-! ## Convex combinations of points of a standard simplex -/

/-- The convex combination `a • x + b • y` of two points of a standard simplex. -/
def combo {m : ℕ} (a b : ℝ) (x y : stdSimplex ℝ (Fin m)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : stdSimplex ℝ (Fin m) :=
  ⟨a • (x : Fin m → ℝ) + b • (y : Fin m → ℝ),
    (convex_stdSimplex ℝ (Fin m)) x.2 y.2 ha hb hab⟩

theorem combo_coe {m : ℕ} (a b : ℝ) (x y : stdSimplex ℝ (Fin m)) (ha hb hab) :
    (combo a b x y ha hb hab : Fin m → ℝ) = a • (x : Fin m → ℝ) + b • (y : Fin m → ℝ) := rfl

theorem combo_apply {m : ℕ} (a b : ℝ) (x y : stdSimplex ℝ (Fin m)) (ha hb hab) (k : Fin m) :
    (combo a b x y ha hb hab : Fin m → ℝ) k = a * x k + b * y k := by
  rw [combo_coe]
  simp [smul_eq_mul]

/-! ## The face `{0,1,2}` of `Δ³` and the fourth vertex -/

/-- The face of `Δ³` spanned by the vertices `0`, `1`, `2`. -/
def cntS : Finset (Fin 4) := {0, 1, 2}

theorem cntS_card : cntS.card = 3 := by decide

theorem two_lt_cntS_card : 2 < cntS.card := by rw [cntS_card]; norm_num

theorem mem_cntS_of_ne_three {k : Fin 4} (h : k ≠ 3) : k ∈ cntS := by
  fin_cases k <;> simp_all [cntS]

theorem not_mem_cntS_three : (3 : Fin 4) ∉ cntS := by decide

/-- The fourth vertex of `Δ³`, off the face `cntS`. -/
def cntV : stdSimplex ℝ (Fin 4) := stdSimplex.vertex (3 : Fin 4)

theorem cntV_apply (k : Fin 4) : (cntV : Fin 4 → ℝ) k = if k = 3 then 1 else 0 := by
  rw [cntV, stdSimplex.vertex_coe]
  by_cases h : k = 3
  · subst h; rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne h, if_neg h]

theorem cntV_apply_of_ne {k : Fin 4} (h : k ≠ 3) : (cntV : Fin 4 → ℝ) k = 0 := by
  rw [cntV_apply, if_neg h]

theorem cntV_apply_three : (cntV : Fin 4 → ℝ) 3 = 1 := by rw [cntV_apply, if_pos rfl]

/-! ## The sequence of points tending to a point of the relative interior -/

/-- The parameter `1/(n+2)`. -/
def eps (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem eps_pos (n : ℕ) : 0 < eps n := by rw [eps]; positivity

theorem eps_le_one (n : ℕ) : eps n ≤ 1 := by
  rw [eps, div_le_one (by positivity)]
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem eps_lt_one (n : ℕ) : eps n < 1 := by
  rw [eps, div_lt_one (by positivity)]
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem tendsto_eps : Tendsto eps atTop (𝓝 0) := by
  have hcomp := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 1)
  refine Tendsto.congr (f₁ := fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) + 1)) (fun n => ?_) hcomp
  rw [eps]
  push_cast
  ring

theorem one_sub_eps_pos (n : ℕ) : 0 < 1 - eps n := by linarith [eps_lt_one n]

theorem one_sub_eps_nonneg (n : ℕ) : 0 ≤ 1 - eps n := (one_sub_eps_pos n).le

theorem eps_nonneg (n : ℕ) : 0 ≤ eps n := (eps_pos n).le

theorem one_sub_eps_add_eps (n : ℕ) : (1 - eps n) + eps n = 1 := by ring

/-- The sequence point `(1-ε) x + ε · v` approaching `x` from off the face. -/
def seqPt (x : stdSimplex ℝ (Fin 4)) (n : ℕ) : stdSimplex ℝ (Fin 4) :=
  combo (1 - eps n) (eps n) x cntV (one_sub_eps_nonneg n) (eps_nonneg n)
    (one_sub_eps_add_eps n)

theorem seqPt_apply (x : stdSimplex ℝ (Fin 4)) (n : ℕ) (k : Fin 4) :
    (seqPt x n : Fin 4 → ℝ) k = (1 - eps n) * x k + eps n * (cntV : Fin 4 → ℝ) k :=
  combo_apply _ _ _ _ _ _ _ _

/-- **Off the face**: the sequence point has full support. -/
theorem supp_seqPt (x : stdSimplex ℝ (Fin 4)) (hx3 : (x : Fin 4 → ℝ) 3 = 0)
    (hpos : ∀ k, k ∈ cntS → 0 < (x : Fin 4 → ℝ) k) (n : ℕ) :
    supp (seqPt x n) = Finset.univ := by
  refine Finset.eq_univ_of_forall (fun k => ?_)
  rw [mem_supp, seqPt_apply]
  by_cases hk : k = 3
  · subst hk
    rw [cntV_apply_three, mul_one, hx3, mul_zero, zero_add]
    exact ne_of_gt (eps_pos n)
  · rw [cntV_apply_of_ne hk, mul_zero, add_zero]
    exact mul_ne_zero (ne_of_gt (one_sub_eps_pos n))
      (ne_of_gt (hpos k (mem_cntS_of_ne_three hk)))

theorem card_supp_seqPt (x : stdSimplex ℝ (Fin 4)) (hx3 : (x : Fin 4 → ℝ) 3 = 0)
    (hpos : ∀ k, k ∈ cntS → 0 < (x : Fin 4 → ℝ) k) (n : ℕ) :
    (ptSupport (seqPt x n)).card ≠ cntS.card := by
  rw [ptSupport_eq_supp, supp_seqPt x hx3 hpos n, cntS_card]
  simp

/-- **Convergence**: the sequence points tend to `x`. -/
theorem tendsto_seqPt (x : stdSimplex ℝ (Fin 4)) :
    Tendsto (fun n => seqPt x n) atTop (𝓝 x) := by
  refine tendsto_subtype_rng.mpr ?_
  refine tendsto_pi_nhds.mpr (fun k => ?_)
  have h1 : Tendsto (fun n : ℕ => 1 - eps n) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub tendsto_eps
  have h2 : Tendsto (fun n : ℕ => eps n) atTop (𝓝 0) := tendsto_eps
  have h3 : Tendsto (fun n : ℕ => (1 - eps n) * x k + eps n * (cntV : Fin 4 → ℝ) k)
      atTop (𝓝 ((1 - 0) * x k + 0 * (cntV : Fin 4 → ℝ) k)) :=
    (h1.mul tendsto_const_nhds).add (h2.mul tendsto_const_nhds)
  have h4 : Tendsto (fun n : ℕ => (1 - eps n) * x k + eps n * (cntV : Fin 4 → ℝ) k)
      atTop (𝓝 (x k)) := by simpa using h3
  refine Tendsto.congr (fun n => ?_) h4
  exact (seqPt_apply x n k).symm

/-- The model point of a point of the top simplex. -/
def cntMk (x : stdSimplex ℝ (Fin 4)) : Model cntD :=
  Quotient.mk'' (Sum.inl (⟨PUnit.unit, x⟩ : Σ _ : cntD.Idx, stdSimplex ℝ (Fin 4)))

theorem cntMk_injective : Function.Injective cntMk := by
  intro x y h
  have h' : cntPhi (cntMk x) = cntPhi (cntMk y) := by rw [h]
  have h'' := congrArg Prod.fst h'
  simpa only [cntMk, cntPhi_mk_inl_fst] using h''

/-- **The contradiction**: a hypothetical push at a point of the relative interior of the face
`{0,1,2}` is impossible, because points of the *interior* of the top cell converge to it and are
fixed by the push. -/
theorem cnt_contradiction_at (x : stdSimplex ℝ (Fin 4)) (hx : ptSupport x = cntS)
    (hx3 : (x : Fin 4 → ℝ) 3 = 0)
    (hpos : ∀ k, k ∈ cntS → 0 < (x : Fin 4 → ℝ) k)
    (o : Model cntD) (Φ : C(unitInterval × {z : Model cntD // z ≠ o}, Model cntD))
    (hfix : ∀ (z : {z : Model cntD // z ≠ o}),
      (z : Model cntD) ∉ openCell cntD PUnit.unit cntS → ∀ s : unitInterval, Φ (s, z) = z)
    (hpush : ∀ (z : {z : Model cntD // z ≠ o}),
      (z : Model cntD) ∈ openCell cntD PUnit.unit cntS →
        Φ (1, z) ∉ openCell cntD PUnit.unit cntS)
    (ho : o ∈ openCell cntD PUnit.unit cntS)
    (hne : cntMk x ≠ o) : False := by
  have hzC : cntMk x ∈ openCell cntD PUnit.unit cntS := ⟨x, hx, rfl⟩
  let u0 : {z : Model cntD // z ≠ o} := ⟨cntMk x, hne⟩
  have hnotC : ∀ n, cntMk (seqPt x n) ∉ openCell cntD PUnit.unit cntS :=
    fun n => not_mem_openCell_of_card_ne cntD PUnit.unit cntS
      (card_supp_seqPt x hx3 hpos n)
  have hne' : ∀ n, cntMk (seqPt x n) ≠ o := by
    intro n hcon
    have h' := ho
    rw [← hcon] at h'
    exact hnotC n h'
  let u : ℕ → {z : Model cntD // z ≠ o} := fun n => ⟨cntMk (seqPt x n), hne' n⟩
  have htend_mk : Tendsto (fun n => cntMk (seqPt x n)) atTop (𝓝 (cntMk x)) := by
    have h := ((topMap cntD PUnit.unit).continuous.tendsto x).comp (tendsto_seqPt x)
    simpa [Function.comp_def, cntMk, topMap] using h
  have htend_u : Tendsto u atTop (𝓝 u0) := by
    refine tendsto_subtype_rng.mpr ?_
    refine Tendsto.congr (f₁ := fun n => cntMk (seqPt x n)) (fun n => ?_) htend_mk
    rfl
  have hpair : Tendsto (fun n => ((1 : unitInterval), u n)) atTop
      (𝓝 ((1 : unitInterval), u0)) :=
    ((continuous_const.prodMk continuous_id).tendsto u0).comp htend_u
  have hΦ : Tendsto (fun n => Φ (1, u n)) atTop (𝓝 (Φ (1, u0))) :=
    (Φ.continuous.tendsto (1, u0)).comp hpair
  have hid : ∀ n, Φ (1, u n) = (u n : Model cntD) := fun n => hfix (u n) (hnotC n) 1
  have hlim : Tendsto (fun n => (u n : Model cntD)) atTop (𝓝 (Φ (1, u0))) :=
    hΦ.congr' (Eventually.of_forall hid)
  have hlim2 : Tendsto (fun n => (u n : Model cntD)) atTop (𝓝 (cntMk x)) := by
    have h := (continuous_subtype_val.tendsto u0).comp htend_u
    simpa [Function.comp_def, u0] using h
  have hEq : Φ (1, u0) = cntMk x := cnt_tendsto_unique hlim hlim2
  exact (hpush u0 hzC) (by rw [hEq]; exact hzC)

/-! ## Two explicit points of the relative interior -/

def xAf : Fin 4 → ℝ :=
  fun k => if k = 0 then 1/2 else if k = 1 then 1/4 else if k = 2 then 1/4 else 0

def xBf : Fin 4 → ℝ :=
  fun k => if k = 0 then 1/4 else if k = 1 then 1/2 else if k = 2 then 1/4 else 0

theorem xAf_nonneg : ∀ k, 0 ≤ xAf k := by intro k; fin_cases k <;> simp [xAf]
theorem xBf_nonneg : ∀ k, 0 ≤ xBf k := by intro k; fin_cases k <;> simp [xBf]

theorem xAf_sum : ∑ k, xAf k = 1 := by
  rw [Fin.sum_univ_four]; simp [xAf]; norm_num
theorem xBf_sum : ∑ k, xBf k = 1 := by
  rw [Fin.sum_univ_four]; simp [xBf]; norm_num

def xA : stdSimplex ℝ (Fin 4) := ⟨xAf, xAf_nonneg, xAf_sum⟩
def xB : stdSimplex ℝ (Fin 4) := ⟨xBf, xBf_nonneg, xBf_sum⟩

theorem xA_coe : (xA : Fin 4 → ℝ) = xAf := rfl
theorem xB_coe : (xB : Fin 4 → ℝ) = xBf := rfl

theorem xA_supp : ptSupport xA = cntS := by
  rw [ptSupport_eq_supp]
  ext k
  rw [mem_supp, xA_coe]
  fin_cases k <;> simp [xAf, cntS]

theorem xB_supp : ptSupport xB = cntS := by
  rw [ptSupport_eq_supp]
  ext k
  rw [mem_supp, xB_coe]
  fin_cases k <;> simp [xBf, cntS]

theorem xA_three : (xA : Fin 4 → ℝ) 3 = 0 := by rw [xA_coe]; simp [xAf]
theorem xB_three : (xB : Fin 4 → ℝ) 3 = 0 := by rw [xB_coe]; simp [xBf]

theorem xA_pos {k : Fin 4} (hk : k ∈ cntS) : 0 < (xA : Fin 4 → ℝ) k := by
  rw [xA_coe]
  fin_cases k <;> simp_all [xAf, cntS]

theorem xB_pos {k : Fin 4} (hk : k ∈ cntS) : 0 < (xB : Fin 4 → ℝ) k := by
  rw [xB_coe]
  fin_cases k <;> simp_all [xBf, cntS]

theorem cntMk_xA_ne_xB : cntMk xA ≠ cntMk xB := by
  intro h
  have h2 : xA = xB := cntMk_injective h
  have h3 : (xA : Fin 4 → ℝ) 0 = (xB : Fin 4 → ℝ) 0 := by rw [h2]
  rw [xA_coe, xB_coe] at h3
  simp [xAf, xBf] at h3

/-- **The statement `cellPushRadial` fails at the counterexample instance.** -/
theorem not_cellPushRadial_instance :
    ¬ (∃ (o : Model cntD)
        (Φ : C(unitInterval × {z : Model cntD // z ≠ o}, Model cntD)),
        o ∈ openCell cntD PUnit.unit cntS ∧
        (∀ z, Φ (0, z) = z) ∧
        (∀ (z : {z : Model cntD // z ≠ o}),
          (z : Model cntD) ∉ openCell cntD PUnit.unit cntS → ∀ s : unitInterval,
          Φ (s, z) = z) ∧
        (∀ (z : {z : Model cntD // z ≠ o}),
          (z : Model cntD) ∈ openCell cntD PUnit.unit cntS →
          Φ (1, z) ∈ closedCell cntD PUnit.unit cntS ∧
            Φ (1, z) ∉ openCell cntD PUnit.unit cntS)) := by
  rintro ⟨o, Φ, ho, h0, hfix, hpush⟩
  rcases em (cntMk xA = o) with hAo | hAo
  · refine cnt_contradiction_at xB xB_supp xB_three (fun k hk => xB_pos hk) o Φ hfix
      (fun z hz => (hpush z hz).2) ho ?_
    intro h
    exact cntMk_xA_ne_xB (hAo.trans h.symm)
  · exact cnt_contradiction_at xA xA_supp xA_three (fun k hk => xA_pos hk) o Φ hfix
      (fun z hz => (hpush z hz).2) ho hAo

end

end Work.RatHurewicz
