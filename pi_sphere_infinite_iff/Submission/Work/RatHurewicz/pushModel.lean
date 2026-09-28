import Mathlib
import Submission.Work.RatHurewicz.pushMap

/-!
# The push of the cycle model off its `k`-cells

The push `pushPt` of `pushMap.lean` is compatible with the face maps, hence extends to the disjoint
union `Raw D` (`pushRaw`) in a way that preserves the generating relations of `modelRel D`, and
therefore descends to a self-map `pushModel` of the model `Model D`.  The push fixes the arcs, is
the identity on points of weight different from `k+1`, and lowers the weight of every point of an
open `(k+1)`-cell to `≤ k` at `u = 1`.
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## The support of a vertex -/

theorem supp_vertex {m : ℕ} (k : Fin m) : supp (stdSimplex.vertex k : stdSimplex ℝ (Fin m)) = {k} := by
  ext j
  rw [mem_supp, Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hjk
    rw [stdSimplex.vertex_coe, Pi.single_eq_of_ne hjk] at hj
    exact hj rfl
  · intro hjk
    subst hjk
    rw [stdSimplex.vertex_coe, Pi.single_eq_same]
    exact one_ne_zero

/-! ## The raw push -/

/-- **The raw push**: in each copy of `Δ^{n+1}` the collapse homotopy of the `(k+1)`-cells, and the
identity on the arcs. -/
def pushRaw (D : MData X n x₀) (k : ℕ) (u : I) (a : Raw D) : Raw D :=
  match a with
  | Sum.inl p =>
      Sum.inl ⟨p.1, if h : (supp p.2).card = k + 1 ∧ (1 - ((k : ℝ) + 1) * suppMin p.2) ≠ 0
        then pushPt k u p.2 h.1 h.2 else p.2⟩
  | Sum.inr p => Sum.inr p

@[simp] theorem pushRaw_inr (D : MData X n x₀) (k : ℕ) (u : I)
    (p : Σ _ : D.Idx, unitInterval) : pushRaw D k u (Sum.inr p) = Sum.inr p := rfl

/-- The raw push is the identity on points whose support does not have `k+1` elements. -/
theorem pushRaw_inl_eq_self (D : MData X n x₀) (k : ℕ) (u : I) (i : D.Idx)
    (x : stdSimplex ℝ (Fin (n + 2))) (h : ¬ ((supp x).card = k + 1 ∧
      1 - ((k : ℝ) + 1) * suppMin x ≠ 0)) :
    pushRaw D k u (Sum.inl ⟨i, x⟩) = Sum.inl ⟨i, x⟩ := by
  simp only [pushRaw]
  rw [dif_neg h]

/-- The raw push on a point of an open `(k+1)`-cell. -/
theorem pushRaw_inl_push (D : MData X n x₀) (k : ℕ) (u : I) (i : D.Idx)
    (x : stdSimplex ℝ (Fin (n + 2))) (hcard : (supp x).card = k + 1)
    (hden : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0) :
    pushRaw D k u (Sum.inl ⟨i, x⟩)
      = Sum.inl ⟨i, pushPt k u x hcard hden⟩ := by
  simp only [pushRaw]
  rw [dif_pos ⟨hcard, hden⟩]

/-! ## The push preserves the generating relations -/

/-- The push preserves a generating relation of the model in the first case (a face
identification). -/
theorem pushRaw_rel_face (D : MData X n x₀) (k : ℕ) (u : I) {i j : D.Idx} {p q : Fin (n + 2)}
    {x : stdSimplex ℝ (Fin (n + 1))}
    (hmap : (D.simplexMap i).comp (facept (n + 1) p)
      = (D.simplexMap j).comp (facept (n + 1) q)) :
    modelRel D (pushRaw D k u (Sum.inl ⟨i, facept (n + 1) p x⟩))
      (pushRaw D k u (Sum.inl ⟨j, facept (n + 1) q x⟩)) := by
  by_cases hc : (supp x).card = k + 1
  · by_cases hd : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0
    · have hd' : 1 - ((k : ℝ) + 1) * suppMin (facept (n + 1) p x) ≠ 0 := by
        rw [suppMin_facept]; exact hd
      have hd'' : 1 - ((k : ℝ) + 1) * suppMin (facept (n + 1) q x) ≠ 0 := by
        rw [suppMin_facept]; exact hd
      have hcardp : (supp (facept (n + 1) p x)).card = k + 1 :=
        (card_supp_facept p x).trans hc
      have hcardq : (supp (facept (n + 1) q x)).card = k + 1 :=
        (card_supp_facept q x).trans hc
      rw [pushRaw_inl_push D k u i _ hcardp hd', pushRaw_inl_push D k u j _ hcardq hd'']
      rw [pushPt_facept k u p x hcardp hd' hc hd, pushPt_facept k u q x hcardq hd'' hc hd]
      exact Or.inl ⟨i, j, p, q, pushPt k u x hc hd, rfl, rfl, hmap⟩
    · have hgardp : ¬ ((supp (facept (n + 1) p x)).card = k + 1 ∧
          1 - ((k : ℝ) + 1) * suppMin (facept (n + 1) p x) ≠ 0) := by
        intro hcon
        exact hd (by rw [← suppMin_facept p x]; exact hcon.2)
      have hgardq : ¬ ((supp (facept (n + 1) q x)).card = k + 1 ∧
          1 - ((k : ℝ) + 1) * suppMin (facept (n + 1) q x) ≠ 0) := by
        intro hcon
        exact hd (by rw [← suppMin_facept q x]; exact hcon.2)
      rw [pushRaw_inl_eq_self D k u i _ hgardp, pushRaw_inl_eq_self D k u j _ hgardq]
      exact Or.inl ⟨i, j, p, q, x, rfl, rfl, hmap⟩
  · have hgardp : ¬ ((supp (facept (n + 1) p x)).card = k + 1 ∧
        1 - ((k : ℝ) + 1) * suppMin (facept (n + 1) p x) ≠ 0) := by
      intro hcon
      exact hc ((card_supp_facept p x).symm.trans hcon.1)
    have hgardq : ¬ ((supp (facept (n + 1) q x)).card = k + 1 ∧
        1 - ((k : ℝ) + 1) * suppMin (facept (n + 1) q x) ≠ 0) := by
      intro hcon
      exact hc ((card_supp_facept q x).symm.trans hcon.1)
    rw [pushRaw_inl_eq_self D k u i _ hgardp, pushRaw_inl_eq_self D k u j _ hgardq]
    exact Or.inl ⟨i, j, p, q, x, rfl, rfl, hmap⟩

/-- **The raw push preserves the generating relations of the model.** -/
theorem pushRaw_modelRel (D : MData X n x₀) (k : ℕ) (u : I) {a b : Raw D}
    (h : modelRel D a b) : modelRel D (pushRaw D k u a) (pushRaw D k u b) := by
  rcases h with ⟨i, j, p, q, x, rfl, rfl, hmap⟩ | ⟨i, ha, hb⟩ | ⟨i, j, ha, hb⟩
  · exact pushRaw_rel_face D k u hmap
  · subst ha; subst hb
    -- the vertex `0` and the base point of the arc
    have hc : ¬ ((supp (stdSimplex.vertex (0 : Fin (n + 2)))).card = k + 1 ∧
        1 - ((k : ℝ) + 1) * suppMin (stdSimplex.vertex (0 : Fin (n + 2))) ≠ 0) := by
      intro hcon
      rw [supp_vertex] at hcon
      have hcard : (({0} : Finset (Fin (n + 2))).card) = 1 := by simp
      rw [hcard] at hcon
      have hk0 : k = 0 := by omega
      have h1 : (stdSimplex.vertex (0 : Fin (n + 2)) : Fin (n + 2) → ℝ) 0 = 1 := by
        rw [stdSimplex.vertex_coe, Pi.single_eq_same]
      have hmin : suppMin (stdSimplex.vertex (0 : Fin (n + 2))) = 1 := by
        rw [suppMin_eq_of_min (i := 0)
          (by rw [supp_vertex]; exact Finset.mem_singleton_self 0)
          (by intro j hj
              rw [supp_vertex] at hj
              obtain rfl := Finset.mem_singleton.mp hj
              exact le_of_eq h1)]
        exact h1
      rw [hmin] at hcon
      exact hcon.2 (by rw [hk0]; norm_num)
    rw [pushRaw_inl_eq_self D k u i _ hc]
    exact Or.inr (Or.inl ⟨i, rfl, rfl⟩)
  · subst ha; subst hb
    exact Or.inr (Or.inr ⟨i, j, rfl, rfl⟩)

/-- **The raw push preserves the gluing relation.** -/
theorem pushRaw_eqvGen (D : MData X n x₀) (k : ℕ) (u : I) {a b : Raw D}
    (h : Relation.EqvGen (modelRel D) a b) :
    Relation.EqvGen (modelRel D) (pushRaw D k u a) (pushRaw D k u b) := by
  induction h with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ (pushRaw_modelRel D k u hxy)
  | refl x => exact Relation.EqvGen.refl _
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz =>
      exact Relation.EqvGen.trans (pushRaw D k u x) (pushRaw D k u y) (pushRaw D k u z)
        ihxy ihyz

/-! ## The descent to the model -/

/-- **The push of the model**, as a function: the descent of the raw push along the quotient
map. -/
noncomputable def pushModel (D : MData X n x₀) (k : ℕ) (u : I) (z : Model D) : Model D :=
  Quotient.lift (fun a => Quotient.mk'' (pushRaw D k u a))
    (fun _ _ hab => Quotient.sound (pushRaw_eqvGen D k u hab)) z

theorem pushModel_mk (D : MData X n x₀) (k : ℕ) (u : I) (a : Raw D) :
    pushModel D k u (Quotient.mk'' a) = Quotient.mk'' (pushRaw D k u a) := rfl

end

end Work.RatHurewicz
