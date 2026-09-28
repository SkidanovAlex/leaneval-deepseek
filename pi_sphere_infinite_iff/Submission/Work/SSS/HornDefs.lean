import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.exists_lift_rel

/-!
# The topological horn, the cone parametrization of the simplex, and the relative HLP

This file sets up the vocabulary for `Work.SSS.singularFibration` (a Serre fibration induces a
Kan fibration of singular simplicial sets).

* `Work.SSS.TopHorn k i` — the **topological horn** `Λ[k,i]`: the union of the faces of the
  standard simplex `Δ^k = stdSimplex ℝ (Fin (k+1))` other than the `i`-th one.
* `Work.SSS.RelHLP p X A` — the **relative homotopy lifting property** of `p` for the pair
  `(X, A)`: lifts of a map `X → B` prescribed on `A` extend to `X`.
* `Work.SSS.cubeToSimplexFun n : I^n → Δ^n` — the standard parametrization of the simplex by the
  cube, defined by iterating the cone description `Δ^{n+1} = C(Δ^n)` (the last coordinate of the
  cube is the cone coordinate).  It is continuous, surjective, maps the interior of the cube into
  the interior of the simplex, and is injective off the boundary of the cube.
* `Work.SSS.coneMapFun n i : I^n × I → Δ^{n+1}` — the cone map with cone point the `i`-th vertex;
  the preimage of the horn `Λ[n+1,i]` is the "cup" `I^n × {0} ∪ ∂I^n × I` of
  `Work.StemsB.LSet n`, so the cube pair `(I^n × I, LSet n)`, for which a Serre fibration has the
  relative homotopy lifting property (`Work.StemsB.HasHLPRel`), maps onto the simplex pair
  `(Δ^{n+1}, Λ[n+1,i])`.
-/

set_option autoImplicit false

namespace Work.SSS

open scoped Topology unitInterval
open CategoryTheory

noncomputable section

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

/-- The **topological horn** `Λ[k, i]`: the union of the faces of the standard simplex
`Δ^k = stdSimplex ℝ (Fin (k+1))` other than the `i`-th one. -/
def TopHorn (k : ℕ) (i : Fin (k + 1)) : Set (stdSimplex ℝ (Fin (k + 1))) :=
  {q | ∃ j : Fin (k + 1), j ≠ i ∧ (q : Fin (k + 1) → ℝ) j = 0}

/-- The **relative homotopy lifting property for the pair `(X, A)`**: every map `v : X → B`
together with a lift `u : A → E` of `v|_A` extends to a lift of `v` on `X`. -/
def RelHLP (p : C(E, B)) (X : Type*) [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (v : C(X, B)) (u : C(↥A, E)),
    p.comp u = v.comp ⟨Subtype.val, continuous_subtype_val⟩ →
    ∃ F : C(X, E), p.comp F = v ∧ F.comp ⟨Subtype.val, continuous_subtype_val⟩ = u

/-! ## The standard parametrization of the simplex by the cube

`Δ^n = stdSimplex ℝ (Fin (n+1))` is the cone on `Δ^{n-1}` with cone point its last vertex, and
`I^n = I^{n-1} × I`; iterating gives the parametrization below: writing `θ_n := cubeToSimplexFun n`
and splitting a cube point `x : I^{n+1}` as `(Fin.init x, t)`,

* `θ_{n+1}(x)` has last coordinate `1 - t` and `i`-th coordinate `t * θ_n (Fin.init x) i`.
-/

/-- The standard parametrization `θ_n : I^n → Δ^n` of the `n`-simplex by the `n`-cube, defined by
iterating the cone description `Δ^{n+1} = C(Δ^n)`. -/
def cubeToSimplexFun : (n : ℕ) → (Fin n → I) → stdSimplex ℝ (Fin (n + 1))
  | 0 => fun _ => ⟨fun _ => 1, ⟨fun _ => zero_le_one, by simp⟩⟩
  | n + 1 => fun x =>
      ⟨Fin.insertNth (Fin.last (n + 1)) (1 - (x (Fin.last n) : ℝ))
          (fun l => (x (Fin.last n) : ℝ) *
            (cubeToSimplexFun n (Fin.init x) : Fin (n + 1) → ℝ) l),
        ⟨(fun j => by
          rcases Fin.eq_self_or_eq_succAbove (Fin.last (n + 1)) j with h | ⟨l, hl⟩
          · rw [h, Fin.insertNth_apply_same]
            exact sub_nonneg.mpr (Set.mem_Icc.mp (x (Fin.last n)).2).2
          · rw [hl, Fin.insertNth_apply_succAbove]
            exact mul_nonneg (Set.mem_Icc.mp (x (Fin.last n)).2).1
              ((cubeToSimplexFun n (Fin.init x)).2.1 l)),
          by
            rw [Fin.sum_univ_succAbove _ (Fin.last (n + 1)), Fin.insertNth_apply_same]
            simp only [Fin.insertNth_apply_succAbove]
            rw [← Finset.mul_sum]
            rw [show (∑ i : Fin (n + 1),
                (cubeToSimplexFun n (Fin.init x) : Fin (n + 1) → ℝ) i) = 1 from
              (cubeToSimplexFun n (Fin.init x)).2.2]
            ring⟩⟩

/-- The explicit formula for one unfolding step of `θ_n`. -/
theorem cubeToSimplexFun_succ (n : ℕ) (x : Fin (n + 1) → I) :
    (cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) =
      Fin.insertNth (Fin.last (n + 1)) (1 - (x (Fin.last n) : ℝ))
        (fun l => (x (Fin.last n) : ℝ) *
          (cubeToSimplexFun n (Fin.init x) : Fin (n + 1) → ℝ) l) :=
  rfl

@[simp]
theorem cubeToSimplexFun_last (n : ℕ) (x : Fin (n + 1) → I) :
    (cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) (Fin.last (n + 1)) =
      1 - (x (Fin.last n) : ℝ) := by
  rw [cubeToSimplexFun_succ, Fin.insertNth_apply_same]

@[simp]
theorem cubeToSimplexFun_succAbove (n : ℕ) (x : Fin (n + 1) → I) (l : Fin (n + 1)) :
    (cubeToSimplexFun (n + 1) x : Fin (n + 2) → ℝ) ((Fin.last (n + 1)).succAbove l) =
      (x (Fin.last n) : ℝ) * (cubeToSimplexFun n (Fin.init x) : Fin (n + 1) → ℝ) l := by
  rw [cubeToSimplexFun_succ, Fin.insertNth_apply_succAbove]

/-- **The parametrization `θ_n` is continuous.** -/
theorem continuous_cubeToSimplexFun : ∀ n : ℕ, Continuous (cubeToSimplexFun n) := by
  intro n
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
    rcases Fin.eq_self_or_eq_succAbove (Fin.last (n + 1)) j with h | ⟨l, hl⟩
    · rw [h]
      simp only [Fin.insertNth_apply_same]
      exact continuous_const.sub (continuous_subtype_val.comp (continuous_apply (Fin.last n)))
    · rw [hl]
      simp only [Fin.insertNth_apply_succAbove]
      have hinit : Continuous fun a : Fin (n + 1) → I => Fin.init a :=
        continuous_pi fun i : Fin n => continuous_apply i.castSucc
      have hθn : Continuous fun a : Fin n → I =>
          (cubeToSimplexFun n a : Fin (n + 1) → ℝ) :=
        (continuous_subtype_val (p := fun z : Fin (n + 1) → ℝ =>
          z ∈ stdSimplex ℝ (Fin (n + 1)))).comp ih
      exact Continuous.mul (continuous_subtype_val.comp (continuous_apply (Fin.last n)))
        ((continuous_apply l).comp (hθn.comp hinit))

/-- **The parametrization `θ_n` as a continuous map.** -/
def cubeToSimplex (n : ℕ) : C(Fin n → I, stdSimplex ℝ (Fin (n + 1))) :=
  ⟨cubeToSimplexFun n, continuous_cubeToSimplexFun n⟩

@[simp]
theorem cubeToSimplex_apply (n : ℕ) (x : Fin n → I) :
    cubeToSimplex n x = cubeToSimplexFun n x := rfl

/-! ## The cone map -/

/-- The **cone map** `I^n × I → Δ^{n+1}` with cone point the `i`-th vertex of `Δ^{n+1}`: for
`w = (x, t)` the `i`-th coordinate is `1 - t` and the `(i.succAbove l)`-th coordinate is
`t * θ_n(x)_l`. -/
def coneMapFun (n : ℕ) (i : Fin (n + 2)) (w : (Fin n → I) × I) : stdSimplex ℝ (Fin (n + 2)) :=
  ⟨Fin.insertNth i (1 - (w.2 : ℝ))
      (fun l => (w.2 : ℝ) * (cubeToSimplexFun n w.1 : Fin (n + 1) → ℝ) l),
    ⟨(fun j => by
      rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨l, hl⟩
      · rw [h, Fin.insertNth_apply_same]
        exact sub_nonneg.mpr (Set.mem_Icc.mp (w.2).2).2
      · rw [hl, Fin.insertNth_apply_succAbove]
        exact mul_nonneg (Set.mem_Icc.mp (w.2).2).1 ((cubeToSimplexFun n w.1).2.1 l)),
      by
        rw [Fin.sum_univ_succAbove _ i, Fin.insertNth_apply_same]
        simp only [Fin.insertNth_apply_succAbove]
        rw [← Finset.mul_sum]
        rw [show (∑ l : Fin (n + 1), (cubeToSimplexFun n w.1 : Fin (n + 1) → ℝ) l) = 1 from
          (cubeToSimplexFun n w.1).2.2]
        ring⟩⟩

/-- The explicit formula for `coneMapFun`. -/
theorem coneMapFun_eq (n : ℕ) (i : Fin (n + 2)) (w : (Fin n → I) × I) :
    (coneMapFun n i w : Fin (n + 2) → ℝ) =
      Fin.insertNth i (1 - (w.2 : ℝ))
        (fun l => (w.2 : ℝ) * (cubeToSimplexFun n w.1 : Fin (n + 1) → ℝ) l) :=
  rfl

@[simp]
theorem coneMapFun_self (n : ℕ) (i : Fin (n + 2)) (w : (Fin n → I) × I) :
    (coneMapFun n i w : Fin (n + 2) → ℝ) i = 1 - (w.2 : ℝ) := by
  rw [coneMapFun_eq, Fin.insertNth_apply_same]

@[simp]
theorem coneMapFun_succAbove (n : ℕ) (i : Fin (n + 2)) (w : (Fin n → I) × I) (l : Fin (n + 1)) :
    (coneMapFun n i w : Fin (n + 2) → ℝ) (i.succAbove l) =
      (w.2 : ℝ) * (cubeToSimplexFun n w.1 : Fin (n + 1) → ℝ) l := by
  rw [coneMapFun_eq, Fin.insertNth_apply_succAbove]

/-- **The cone map is continuous.** -/
theorem continuous_coneMapFun (n : ℕ) (i : Fin (n + 2)) : Continuous (coneMapFun n i) := by
  refine Continuous.subtype_mk (continuous_pi fun j => ?_) _
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨l, hl⟩
  · rw [h]
    simp only [Fin.insertNth_apply_same]
    exact continuous_const.sub (continuous_subtype_val.comp continuous_snd)
  · rw [hl]
    simp only [Fin.insertNth_apply_succAbove]
    have hθ : Continuous fun a : (Fin n → I) × I =>
        (cubeToSimplexFun n a.1 : Fin (n + 1) → ℝ) :=
      (continuous_subtype_val (p := fun z : Fin (n + 1) → ℝ =>
          z ∈ stdSimplex ℝ (Fin (n + 1)))).comp
        ((continuous_cubeToSimplexFun n).comp continuous_fst)
    exact Continuous.mul (continuous_subtype_val.comp continuous_snd)
      ((continuous_apply l).comp hθ)

/-- **The cone map as a continuous map.** -/
def coneMap (n : ℕ) (i : Fin (n + 2)) : C((Fin n → I) × I, stdSimplex ℝ (Fin (n + 2))) :=
  ⟨coneMapFun n i, continuous_coneMapFun n i⟩

@[simp]
theorem coneMap_apply (n : ℕ) (i : Fin (n + 2)) (w : (Fin n → I) × I) :
    coneMap n i w = coneMapFun n i w := rfl

/-! ## The faces of the horn -/

/-- The inclusion of the `j`-th face into the horn `Λ[m, i]`, for `j ≠ i`. -/
def faceIncl (m : ℕ) (i : Fin (m + 1)) (j : Fin (m + 1)) (hj : j ≠ i) :
    C(stdSimplex ℝ (Fin m), ↥(TopHorn m i)) where
  toFun q := ⟨stdSimplex.map (Fin.succAbove j) q, j, hj, by
    rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
      Finset.filter_eq_empty_iff.mpr (fun y _ hy => Fin.succAbove_ne j y hy), Finset.sum_empty]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (stdSimplex.continuous_map (S := ℝ) (Fin.succAbove j)) _

@[simp]
theorem faceIncl_coe (m : ℕ) (i : Fin (m + 1)) (j : Fin (m + 1)) (hj : j ≠ i)
    (q : stdSimplex ℝ (Fin m)) :
    ((faceIncl m i j hj q : ↥(TopHorn m i)) : stdSimplex ℝ (Fin (m + 1))) =
      stdSimplex.map (Fin.succAbove j) q := rfl

/-! ## The bridge between the singular simplices of a space and continuous maps from the simplex -/

/-- The identification between the `n`-simplices of the singular simplicial set of `X` and the
continuous maps `Δ^n → X`. -/
def simplexEquiv (n : ℕ) (X : Type) [TopologicalSpace X] :
    (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n)) ≃
      C(stdSimplex ℝ (Fin (n + 1)), X) :=
  (TopCat.of X).toSSetObjEquivT (Opposite.op (SimplexCategory.mk n))

/-- The identification between the morphisms `Δ[n] ⟶ sSing X` and the continuous maps
`Δ^n → X`. -/
def morphSimplex (n : ℕ) (X : Type) [TopologicalSpace X] :
    (SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ TopCat.toSSet.obj (TopCat.of X)) ≃
      C(stdSimplex ℝ (Fin (n + 1)), X) :=
  SSet.yonedaEquiv.trans (simplexEquiv n X)

/-- The `j`-th face of a morphism from the horn `Λ[n+1, i]`: the continuous map `Δ^n → X`
carried by `horn.ι i j hj ≫ f`. -/
def faceSimplex {X : Type} [TopologicalSpace X] {n : ℕ} {i : Fin (n + 2)}
    (f : (SSet.horn (n + 1) i).toSSet ⟶ TopCat.toSSet.obj (TopCat.of X))
    (j : Fin (n + 2)) (hj : j ≠ i) : C(stdSimplex ℝ (Fin (n + 1)), X) :=
  morphSimplex n X (SSet.horn.ι i j hj ≫ f)

/-! ## The cofaces, the inclusion of the horn and the deletion of a coordinate -/

/-- The `j`-th coface `δ_j : Δ^n → Δ^{n+1}`, inserting a zero in the `j`-th coordinate. -/
def coface (n : ℕ) (j : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map (Fin.succAbove j), stdSimplex.continuous_map (S := ℝ) (Fin.succAbove j)⟩

@[simp]
theorem coface_apply (n : ℕ) (j : Fin (n + 2)) (q : stdSimplex ℝ (Fin (n + 1))) :
    coface n j q = stdSimplex.map (Fin.succAbove j) q := rfl

/-- The inclusion of the horn `Λ[m, i]` into the simplex `Δ^m`. -/
def hornIncl (m : ℕ) (i : Fin (m + 1)) :
    C(↥(TopHorn m i), stdSimplex ℝ (Fin (m + 1))) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp]
theorem hornIncl_apply (m : ℕ) (i : Fin (m + 1)) (q : ↥(TopHorn m i)) :
    hornIncl m i q = q.1 := rfl

/-- The `j`-th face of the horn, followed by the inclusion of the horn, is the `j`-th coface. -/
theorem hornIncl_comp_faceIncl (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 2)) (hj : j ≠ i) :
    (hornIncl (n + 1) i).comp (faceIncl (n + 1) i j hj) = coface n j :=
  rfl

/-- Delete a vanishing coordinate of a point of the standard simplex. -/
def stdSimplexDel {k : ℕ} (j : Fin (k + 1)) (q : stdSimplex ℝ (Fin (k + 1)))
    (hq : (q : Fin (k + 1) → ℝ) j = 0) : stdSimplex ℝ (Fin k) :=
  ⟨fun l => (q : Fin (k + 1) → ℝ) (j.succAbove l), ⟨fun l => q.2.1 _, by
    have h := Fin.sum_univ_succAbove (fun l : Fin (k + 1) => (q : Fin (k + 1) → ℝ) l) j
    have h1 : ∑ i : Fin (k + 1), (q : Fin (k + 1) → ℝ) i = 1 := q.2.2
    rw [h1, hq, zero_add] at h
    exact h.symm⟩⟩

@[simp]
theorem stdSimplexDel_apply {k : ℕ} (j : Fin (k + 1)) (q : stdSimplex ℝ (Fin (k + 1)))
    (hq : (q : Fin (k + 1) → ℝ) j = 0) (l : Fin k) :
    (stdSimplexDel j q hq : Fin k → ℝ) l = (q : Fin (k + 1) → ℝ) (j.succAbove l) := rfl

/-- The `j`-th coface of the point obtained from `q` by deleting the vanishing `j`-th
coordinate is `q`. -/
theorem coface_stdSimplexDel {n : ℕ} (j : Fin (n + 2)) (q : stdSimplex ℝ (Fin (n + 2)))
    (hq : (q : Fin (n + 2) → ℝ) j = 0) :
    coface n j (stdSimplexDel (k := n + 1) j q hq) = q := by
  ext k
  show (stdSimplex.map (Fin.succAbove j) (stdSimplexDel (k := n + 1) j q hq) :
      Fin (n + 2) → ℝ) k = (q : Fin (n + 2) → ℝ) k
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = j
  · rw [hk, Finset.filter_eq_empty_iff.mpr (fun x _ hx => Fin.succAbove_ne j x hx),
      Finset.sum_empty, hq]
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    have hfil : Finset.univ.filter (fun x : Fin (n + 1) => j.succAbove x = k) = {l} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
      · intro b hb
        exact Fin.succAbove_right_injective ((Finset.mem_filter.mp hb).2.trans hl.symm)
    rw [hfil, Finset.sum_singleton, stdSimplexDel_apply, hl]

end

end Work.SSS
