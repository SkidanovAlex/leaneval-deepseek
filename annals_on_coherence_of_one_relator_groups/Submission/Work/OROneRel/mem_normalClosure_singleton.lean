import Mathlib

/-!
# Describing the normal closure of a singleton by products of conjugates

For an element `u` of a group `G`, an element of the normal closure of `{u}` is a product of
conjugates of powers of `u`.  This file makes that description explicit: we build the subgroup
`conjProdSubgroup u` consisting of all products

`∏ i, g i * u ^ (ε i) * (g i)⁻¹`

of conjugates of integral powers of `u`, show that it is a normal subgroup containing `u`, and
hence contains `normalClosure {u}`.  Finally we rewrite a product indexed by a list as a product
indexed by `Fin n`, which yields the stated `List.ofFn` normal form.
-/

namespace Work.OROneRel

variable {G : Type*} [Group G]

/-- A single conjugate of a power of `u`, indexed by the conjugating element together with the
exponent: the pair `(g, ε)` encodes `g * u ^ ε * g⁻¹`. -/
def conjTerm (u : G) (p : G × ℤ) : G := p.1 * u ^ p.2 * p.1⁻¹

/-- The inverse of `g * u ^ ε * g⁻¹` is again of the same shape, with exponent `-ε`. -/
lemma conjTerm_inv (u : G) (p : G × ℤ) : (conjTerm u p)⁻¹ = conjTerm u (p.1, -p.2) := by
  simp only [conjTerm, zpow_neg]
  group

/-- Conjugating a term `g * u ^ ε * g⁻¹` by `h` again gives a term of the same shape. -/
lemma conjTerm_conj (u : G) (h : G) (p : G × ℤ) :
    h * conjTerm u p * h⁻¹ = conjTerm u (h * p.1, p.2) := by
  simp only [conjTerm]
  group

/-- Conjugation distributes over a product of a list: `g * ∏ l * g⁻¹ = ∏ (g * a * g⁻¹)`. -/
lemma conj_prod (g : G) (L : List G) :
    g * L.prod * g⁻¹ = (L.map fun a => g * a * g⁻¹).prod := by
  induction L with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      show g * (a * l.prod) * g⁻¹ = (g * a * g⁻¹) * (g * l.prod * g⁻¹) by group, ih]

/-- The set of products of conjugates of powers of `u`. -/
def conjProdSet (u : G) : Set G :=
  {y | ∃ L : List (G × ℤ), y = (L.map (conjTerm u)).prod}

lemma one_mem_conjProdSet (u : G) : (1 : G) ∈ conjProdSet u :=
  ⟨[], by simp⟩

lemma mul_mem_conjProdSet (u : G) {x y : G} (hx : x ∈ conjProdSet u)
    (hy : y ∈ conjProdSet u) : x * y ∈ conjProdSet u := by
  rcases hx with ⟨L, rfl⟩
  rcases hy with ⟨M, rfl⟩
  exact ⟨L ++ M, by rw [List.map_append, List.prod_append]⟩

lemma inv_mem_conjProdSet (u : G) {x : G} (hx : x ∈ conjProdSet u) :
    x⁻¹ ∈ conjProdSet u := by
  rcases hx with ⟨L, rfl⟩
  refine ⟨(L.map fun p : G × ℤ => (p.1, -p.2)).reverse, ?_⟩
  have hlist : List.map (fun x : G => x⁻¹) (L.map (conjTerm u))
      = (L.map fun p : G × ℤ => (p.1, -p.2)).map (conjTerm u) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun p _ => conjTerm_inv u p)
  rw [List.prod_inv_reverse, hlist, List.map_reverse]

lemma conj_mem_conjProdSet (u : G) (h : G) {x : G} (hx : x ∈ conjProdSet u) :
    h * x * h⁻¹ ∈ conjProdSet u := by
  rcases hx with ⟨L, rfl⟩
  refine ⟨L.map fun p : G × ℤ => (h * p.1, p.2), ?_⟩
  have hlist : List.map (fun a : G => h * a * h⁻¹) (L.map (conjTerm u))
      = (L.map fun p : G × ℤ => (h * p.1, p.2)).map (conjTerm u) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun p _ => conjTerm_conj u h p)
  rw [conj_prod, hlist]

/-- The products of conjugates of powers of `u` form a subgroup. -/
def conjProdSubgroup (u : G) : Subgroup G where
  carrier := conjProdSet u
  mul_mem' := mul_mem_conjProdSet u
  one_mem' := one_mem_conjProdSet u
  inv_mem' := inv_mem_conjProdSet u

instance conjProdSubgroup_normal (u : G) : (conjProdSubgroup u).Normal where
  conj_mem := fun n hn h => conj_mem_conjProdSet u h hn

/-- **Normal form for elements of the normal closure of a singleton.** Any element of the normal
closure of `{u}` is a product of conjugates of integral powers of `u`. -/
theorem exists_conjProd_of_mem_normalClosure {u y : G}
    (hy : y ∈ Subgroup.normalClosure ({u} : Set G)) :
    ∃ (n : ℕ) (g : Fin n → G) (ε : Fin n → ℤ),
      y = (List.ofFn fun i : Fin n => g i * u ^ (ε i) * (g i)⁻¹).prod := by
  have hle : Subgroup.normalClosure ({u} : Set G) ≤ conjProdSubgroup u := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨[(1, 1)], by simp [conjTerm]⟩
  obtain ⟨L, hL⟩ := hle hy
  have key : (List.map (conjTerm u) L).prod
      = (List.ofFn fun i : Fin L.length =>
          (L.get i).1 * u ^ ((L.get i).2) * ((L.get i).1)⁻¹).prod := by
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn]
    congr 1
  exact ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, by rw [hL, key]⟩

theorem mem_normalClosure_singleton {α : Type*} {u y : FreeGroup α}
    (hy : y ∈ Subgroup.normalClosure ({u} : Set (FreeGroup α))) :
    ∃ (n : ℕ) (g : Fin n → FreeGroup α) (ε : Fin n → ℤ),
      y = (List.ofFn fun i : Fin n => g i * u ^ (ε i) * (g i)⁻¹).prod :=
  exists_conjProd_of_mem_normalClosure hy

end Work.OROneRel
