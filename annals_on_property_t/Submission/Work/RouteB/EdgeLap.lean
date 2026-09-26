import Submission.Work.RouteB.SimplexCount
import Submission.Work.RouteB.TransvectionEquiv
import Submission.Work.RouteB.FreeGroupAutDecEq
import Submission.Work.RouteB.Symmetrisation
import Submission.Commons.Algebra.MonoidAlgebra.laplacian_biUnion
import Submission.PropertyT

open OnPropertyT Submission.FreeGroupAut
open scoped BigOperators

set_option autoImplicit false

/-!
# The edge Laplacians `Δ_e` of the symmetrisation argument

For an edge `e = {i,j}` of the standard `(m-1)`-simplex, `SEdge e` is the set of
the eight Nielsen transvections carried by `e`:

    `ρᵢⱼ^{±1}, λᵢⱼ^{±1}, ρⱼᵢ^{±1}, λⱼᵢ^{±1}`,

and `edgeLap e = Laplacian (SEdge e) ∈ ℝ[Aut(F_m)]` is its Laplacian.  These
`Δ_e` are the building blocks of the paper's `Δ_n = ∑_{e ∈ E_n} Δ_e`
(Kaluba–Kielak–Nowak, Lemma `delta using edges`), of

    `Δ_n² = Sq_n + Adj_n + Op_n`   (`sum of sq adj op`),

and of the symmetrisation step (`Method I` / `Method II`).

The main technical content of this file is the **pairwise disjointness** of the
families `SEdge e` (`e ∈ E_m`), which is what `laplacian_biUnion` needs in order
to conclude `Laplacian (⨆_e SEdge e) = ∑_e Laplacian (SEdge e)`.  It is proved
through the abelianisation invariant `matPair`: for a Nielsen transvection `g`
the "matrix" `transMat g` of exponent sums has exactly one nonzero row and one
nonzero column, and `matPair g` (the union of these two sets) is the underlying
(ordered) pair of indices.  Hence `g ∈ SEdge p ⟹ matPair g = p.toFinset`.
-/

namespace Submission.RouteB

namespace Edge

variable {m : ℕ}

/-! ## The eight transvections of an edge -/

/-- The four Nielsen transvections `ρᵢⱼ^{±1}, λᵢⱼ^{±1}` attached to the *ordered*
pair `(i,j)` (`i ≠ j`). -/
noncomputable def dirEdge (i j : Fin m) (hij : i ≠ j) : Finset (MulAut (FreeGroup (Fin m))) :=
  {rho i j hij, rhoNeg i j hij, lam i j hij, lamNeg i j hij}

@[simp] lemma mem_dirEdge {i j : Fin m} (hij : i ≠ j) {x : MulAut (FreeGroup (Fin m))} :
    x ∈ dirEdge i j hij ↔ x = rho i j hij ∨ x = rhoNeg i j hij
      ∨ x = lam i j hij ∨ x = lamNeg i j hij := by
  simp [dirEdge]

/-- The eight Nielsen transvections attached to the *unordered* pair `{i,j}`. -/
noncomputable def sEdgeOf (i j : Fin m) (hij : i ≠ j) : Finset (MulAut (FreeGroup (Fin m))) :=
  dirEdge i j hij ∪ dirEdge j i hij.symm

lemma mem_sEdgeOf {i j : Fin m} (hij : i ≠ j) {x : MulAut (FreeGroup (Fin m))} :
    x ∈ sEdgeOf i j hij ↔ x ∈ dirEdge i j hij ∨ x ∈ dirEdge j i hij.symm := by
  simp [sEdgeOf]

lemma dirEdge_proof_irrel {i j : Fin m} (h1 h2 : i ≠ j) :
    dirEdge i j h1 = dirEdge i j h2 := by
  rw [Subsingleton.elim h1 h2]

lemma sEdgeOf_comm {i j : Fin m} (hij : i ≠ j) :
    sEdgeOf i j hij = sEdgeOf j i hij.symm := by
  rw [sEdgeOf, sEdgeOf, dirEdge_proof_irrel ((hij.symm).symm) hij, Finset.union_comm]

/-- The set of the eight Nielsen transvections of an edge `p`. -/
noncomputable def SEdge (p : Edge m) : Finset (MulAut (FreeGroup (Fin m))) :=
  sEdgeOf p.1.1 p.1.2 (ne_of_lt p.2)

lemma SEdge_def (p : Edge m) : SEdge p = sEdgeOf p.1.1 p.1.2 (ne_of_lt p.2) := rfl

lemma mem_SEdge {p : Edge m} {x : MulAut (FreeGroup (Fin m))} :
    x ∈ SEdge p ↔ x ∈ sEdgeOf p.1.1 p.1.2 (ne_of_lt p.2) := Iff.rfl

/-- Two edges with the same vertex set have the same transvection set. -/
lemma sEdgeOf_proof_irrel {i j : Fin m} (h1 h2 : i ≠ j) : sEdgeOf i j h1 = sEdgeOf i j h2 := by
  simp only [sEdgeOf, dirEdge_proof_irrel h1 h2, dirEdge_proof_irrel h1.symm h2.symm]

lemma sEdgeOf_eq_of_pair {i j i' j' : Fin m} (hij : i ≠ j) (hij' : i' ≠ j')
    (h : ({i, j} : Finset (Fin m)) = {i', j'}) : sEdgeOf i j hij = sEdgeOf i' j' hij' := by
  have hi : i' = i ∨ i' = j := by
    have h1 : i' ∈ ({i, j} : Finset (Fin m)) := by rw [h]; simp
    simpa using h1
  have hj : j' = i ∨ j' = j := by
    have h1 : j' ∈ ({i, j} : Finset (Fin m)) := by rw [h]; simp
    simpa using h1
  rcases hi with h1 | h1 <;> rcases hj with h2 | h2
  · exact absurd (h1.trans h2.symm) hij'
  · subst h1; subst h2; exact sEdgeOf_proof_irrel hij hij'
  · subst h1; subst h2; simpa using sEdgeOf_comm hij
  · exact absurd (h1.trans h2.symm) hij'

lemma SEdge_eq_of_toFinset {p q : Edge m} (h : p.toFinset = q.toFinset) :
    SEdge p = SEdge q := by
  have h' : ({p.1.1, p.1.2} : Finset (Fin m)) = ({q.1.1, q.1.2} : Finset (Fin m)) := by
    simpa [toFinset] using h
  exact sEdgeOf_eq_of_pair (ne_of_lt p.2) (ne_of_lt q.2) h'

/-- Two edges with the same vertices (in either order) have the same transvection set. -/
lemma sEdgeOf_eq_of_vertices {i j i' j' : Fin m} (hij : i ≠ j) (hij' : i' ≠ j')
    (h1 : i' = i ∨ i' = j) (h2 : j' = i ∨ j' = j) :
    sEdgeOf i j hij = sEdgeOf i' j' hij' := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hij'
  · subst h1; subst h2; exact sEdgeOf_proof_irrel hij hij'
  · subst h1; subst h2; simpa using sEdgeOf_comm hij
  · exact absurd (h1.trans h2.symm) hij'

/-- The transvection set of an edge is closed under inversion. -/
lemma dirEdge_inv_mem {i j : Fin m} (hij : i ≠ j) {x : MulAut (FreeGroup (Fin m))}
    (hx : x ∈ dirEdge i j hij) : x⁻¹ ∈ dirEdge i j hij := by
  rw [mem_dirEdge] at hx ⊢
  rcases hx with h | h | h | h <;> rw [h]
  · exact Or.inr (Or.inl (rho_inv_eq i j hij).symm)
  · exact Or.inl (rhoNeg_inv_eq i j hij).symm
  · exact Or.inr (Or.inr (Or.inr (lam_inv_eq i j hij).symm))
  · exact Or.inr (Or.inr (Or.inl (lamNeg_inv_eq i j hij).symm))

lemma sEdgeOf_inv_mem {i j : Fin m} (hij : i ≠ j) {x : MulAut (FreeGroup (Fin m))}
    (hx : x ∈ sEdgeOf i j hij) : x⁻¹ ∈ sEdgeOf i j hij := by
  rw [mem_sEdgeOf] at hx ⊢
  rcases hx with h | h
  · exact Or.inl (dirEdge_inv_mem hij h)
  · exact Or.inr (dirEdge_inv_mem hij.symm h)

lemma sEdgeOf_symm (i j : Fin m) (hij : i ≠ j) :
    ((sEdgeOf i j hij : Finset (MulAut (FreeGroup (Fin m)))) : Set _)⁻¹
      = (sEdgeOf i j hij : Set (MulAut (FreeGroup (Fin m)))) := by
  ext x
  rw [Set.mem_inv]
  constructor
  · intro h; simpa using sEdgeOf_inv_mem hij h
  · intro h; exact sEdgeOf_inv_mem hij h

lemma SEdge_symm (p : Edge m) :
    ((SEdge p : Finset (MulAut (FreeGroup (Fin m)))) : Set _)⁻¹
      = (SEdge p : Set (MulAut (FreeGroup (Fin m)))) :=
  sEdgeOf_symm _ _ _

/-! ## The abelianisation invariant distinguishing the transvections -/

/-- The exponent-sum character `F_m →* Multiplicative (Fin m → ℤ)`: the
`k`-th coordinate of the image is the exponent sum of `a_k`. -/
noncomputable def expSum (m : ℕ) : FreeGroup (Fin m) →* Multiplicative (Fin m → ℤ) :=
  FreeGroup.lift (fun k : Fin m => Multiplicative.ofAdd (Pi.single k (1 : ℤ)))

lemma expSum_of (k : Fin m) :
    expSum m (FreeGroup.of k) = Multiplicative.ofAdd (Pi.single k (1 : ℤ)) :=
  FreeGroup.lift_apply_of

@[simp] lemma expSum_toAdd_of (k l : Fin m) :
    (expSum m (FreeGroup.of l)).toAdd k = if k = l then 1 else 0 := by
  rw [expSum_of]
  simp [Pi.single_apply]

/-- The matrix of exponent sums of an automorphism, relative to the identity:
`transMat g k l = χ_k (g a_l) - χ_k (a_l)`. -/
noncomputable def transMat (g : MulAut (FreeGroup (Fin m))) (k l : Fin m) : ℤ :=
  (expSum m (g (FreeGroup.of l))).toAdd k - (expSum m (FreeGroup.of l)).toAdd k

lemma transMat_rho (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (rho i j hij) k l = if l = i then (if k = j then (1 : ℤ) else 0) else 0 := by
  unfold transMat
  by_cases hl : l = i
  · subst hl
    simp only [rho_apply_self, map_mul, toAdd_mul, Pi.add_apply, expSum_toAdd_of]
    split_ifs <;> ring
  · rw [rho_apply_other hij hl]
    simp only [expSum_toAdd_of, if_neg hl]
    ring

lemma transMat_rhoNeg (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (rhoNeg i j hij) k l = if l = i then (if k = j then (-1 : ℤ) else 0) else 0 := by
  unfold transMat
  by_cases hl : l = i
  · subst hl
    simp only [rhoNeg_apply_self, map_mul, toAdd_mul, Pi.add_apply, (expSum m).map_inv,
      toAdd_inv, Pi.neg_apply, expSum_toAdd_of]
    split_ifs <;> ring
  · rw [rhoNeg_apply_other hij hl]
    simp only [expSum_toAdd_of, if_neg hl]
    ring

lemma transMat_lam (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (lam i j hij) k l = if l = i then (if k = j then (1 : ℤ) else 0) else 0 := by
  unfold transMat
  by_cases hl : l = i
  · subst hl
    simp only [lam_apply_self, map_mul, toAdd_mul, Pi.add_apply, expSum_toAdd_of]
    split_ifs <;> ring
  · rw [lam_apply_other hij hl]
    simp only [expSum_toAdd_of, if_neg hl]
    ring

lemma transMat_lamNeg (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (lamNeg i j hij) k l = if l = i then (if k = j then (-1 : ℤ) else 0) else 0 := by
  unfold transMat
  by_cases hl : l = i
  · subst hl
    simp only [lamNeg_apply_self, map_mul, toAdd_mul, Pi.add_apply, (expSum m).map_inv,
      toAdd_inv, Pi.neg_apply, expSum_toAdd_of]
    split_ifs <;> ring
  · rw [lamNeg_apply_other hij hl]
    simp only [expSum_toAdd_of, if_neg hl]
    ring

lemma transMat_rho_ne_zero (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (rho i j hij) k l ≠ 0 ↔ k = j ∧ l = i := by
  rw [transMat_rho]
  constructor
  · intro h
    by_cases hl : l = i
    · rw [if_pos hl] at h
      by_cases hk : k = j
      · exact ⟨hk, hl⟩
      · rw [if_neg hk] at h; exact absurd rfl h
    · rw [if_neg hl] at h; exact absurd rfl h
  · rintro ⟨rfl, rfl⟩
    simp

lemma transMat_rhoNeg_ne_zero (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (rhoNeg i j hij) k l ≠ 0 ↔ k = j ∧ l = i := by
  rw [transMat_rhoNeg]
  constructor
  · intro h
    by_cases hl : l = i
    · rw [if_pos hl] at h
      by_cases hk : k = j
      · exact ⟨hk, hl⟩
      · rw [if_neg hk] at h; exact absurd rfl h
    · rw [if_neg hl] at h; exact absurd rfl h
  · rintro ⟨rfl, rfl⟩
    simp

lemma transMat_lam_ne_zero (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (lam i j hij) k l ≠ 0 ↔ k = j ∧ l = i := by
  rw [transMat_lam]
  constructor
  · intro h
    by_cases hl : l = i
    · rw [if_pos hl] at h
      by_cases hk : k = j
      · exact ⟨hk, hl⟩
      · rw [if_neg hk] at h; exact absurd rfl h
    · rw [if_neg hl] at h; exact absurd rfl h
  · rintro ⟨rfl, rfl⟩
    simp

lemma transMat_lamNeg_ne_zero (i j : Fin m) (hij : i ≠ j) (k l : Fin m) :
    transMat (lamNeg i j hij) k l ≠ 0 ↔ k = j ∧ l = i := by
  rw [transMat_lamNeg]
  constructor
  · intro h
    by_cases hl : l = i
    · rw [if_pos hl] at h
      by_cases hk : k = j
      · exact ⟨hk, hl⟩
      · rw [if_neg hk] at h; exact absurd rfl h
    · rw [if_neg hl] at h; exact absurd rfl h
  · rintro ⟨rfl, rfl⟩
    simp

/-- The "index pair" of an automorphism: the union of the nonzero rows and the
nonzero columns of the exponent-sum matrix `transMat`. -/
noncomputable def matPair (g : MulAut (FreeGroup (Fin m))) : Finset (Fin m) :=
  (Finset.univ.filter (fun k => ∃ l, transMat g k l ≠ 0)) ∪
    (Finset.univ.filter (fun l => ∃ k, transMat g k l ≠ 0))

lemma matPair_eq_of_iff {g : MulAut (FreeGroup (Fin m))} {i j : Fin m} (hij : i ≠ j)
    (h : ∀ k l, transMat g k l ≠ 0 ↔ k = j ∧ l = i) :
    matPair g = ({i, j} : Finset (Fin m)) := by
  have hrows : (Finset.univ.filter (fun k : Fin m => ∃ l, transMat g k l ≠ 0))
      = ({j} : Finset (Fin m)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨l, hl⟩
      exact (h k l).mp hl |>.1
    · intro hk
      exact ⟨i, (h k i).mpr ⟨hk, rfl⟩⟩
  have hcols : (Finset.univ.filter (fun l : Fin m => ∃ k, transMat g k l ≠ 0))
      = ({i} : Finset (Fin m)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨k, hk⟩
      exact (h k l).mp hk |>.2
    · intro hl
      exact ⟨j, (h j l).mpr ⟨rfl, hl⟩⟩
  rw [matPair, hrows, hcols]
  ext k
  simp [Finset.mem_insert, Finset.mem_singleton, or_comm, or_assoc, or_left_comm]

lemma matPair_rho (i j : Fin m) (hij : i ≠ j) :
    matPair (rho i j hij) = ({i, j} : Finset (Fin m)) :=
  matPair_eq_of_iff hij (transMat_rho_ne_zero i j hij)

lemma matPair_rhoNeg (i j : Fin m) (hij : i ≠ j) :
    matPair (rhoNeg i j hij) = ({i, j} : Finset (Fin m)) :=
  matPair_eq_of_iff hij (transMat_rhoNeg_ne_zero i j hij)

lemma matPair_lam (i j : Fin m) (hij : i ≠ j) :
    matPair (lam i j hij) = ({i, j} : Finset (Fin m)) :=
  matPair_eq_of_iff hij (transMat_lam_ne_zero i j hij)

lemma matPair_lamNeg (i j : Fin m) (hij : i ≠ j) :
    matPair (lamNeg i j hij) = ({i, j} : Finset (Fin m)) :=
  matPair_eq_of_iff hij (transMat_lamNeg_ne_zero i j hij)

lemma matPair_sEdgeOf {i j : Fin m} (hij : i ≠ j) {x : MulAut (FreeGroup (Fin m))}
    (hx : x ∈ sEdgeOf i j hij) : matPair x = ({i, j} : Finset (Fin m)) := by
  rw [mem_sEdgeOf] at hx
  rcases hx with hx | hx
  · rw [mem_dirEdge] at hx
    rcases hx with h | h | h | h
    · rw [h]; exact matPair_rho i j hij
    · rw [h]; exact matPair_rhoNeg i j hij
    · rw [h]; exact matPair_lam i j hij
    · rw [h]; exact matPair_lamNeg i j hij
  · rw [mem_dirEdge] at hx
    rcases hx with h | h | h | h
    · rw [h, matPair_rho j i hij.symm, Finset.pair_comm]
    · rw [h, matPair_rhoNeg j i hij.symm, Finset.pair_comm]
    · rw [h, matPair_lam j i hij.symm, Finset.pair_comm]
    · rw [h, matPair_lamNeg j i hij.symm, Finset.pair_comm]

lemma matPair_SEdge {p : Edge m} {x : MulAut (FreeGroup (Fin m))} (hx : x ∈ SEdge p) :
    matPair x = p.toFinset := by
  have h := matPair_sEdgeOf (ne_of_lt p.2) hx
  rw [h]
  simp [toFinset]

/-- **The transvection sets of distinct edges are disjoint.** -/
theorem SEdge_disjoint {p q : Edge m} (hpq : p ≠ q) : Disjoint (SEdge p) (SEdge q) := by
  rw [Finset.disjoint_left]
  intro x hxp hxq
  have h1 := matPair_SEdge hxp
  have h2 := matPair_SEdge hxq
  exact hpq (toFinset_injective (by rw [← h1, h2]))

/-! ## The edge Laplacians and their equivariance -/

/-- The Laplacian `Δ_e ∈ ℝ[Aut(F_m)]` of the transvections carried by the edge `e`. -/
noncomputable def edgeLap (p : Edge m) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  OnPropertyT.Laplacian (SEdge p)

/-- `Δ_e` is self-adjoint (the transvection set of an edge is symmetric). -/
theorem edgeLap_star (p : Edge m) : star (edgeLap p) = edgeLap p :=
  Submission.PropertyT.star_laplacian (SEdge p) (SEdge_symm p)

/-- Conjugation by the permutation automorphism `permAut σ`. -/
def conjFun (σ : Equiv.Perm (Fin m)) (g : MulAut (FreeGroup (Fin m))) :
    MulAut (FreeGroup (Fin m)) :=
  permAut σ * g * (permAut σ)⁻¹

lemma dirEdge_image_conj (σ : Equiv.Perm (Fin m)) {i j : Fin m} (hij : i ≠ j) :
    (dirEdge i j hij).image (conjFun σ) = dirEdge (σ i) (σ j) (fun h => hij (σ.injective h)) := by
  ext x
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_dirEdge] at hg ⊢
    rcases hg with h | h | h | h
    · exact Or.inl (h ▸ permAut_conj_rho σ i j hij)
    · exact Or.inr (Or.inl (h ▸ permAut_conj_rhoNeg σ i j hij))
    · exact Or.inr (Or.inr (Or.inl (h ▸ permAut_conj_lam σ i j hij)))
    · exact Or.inr (Or.inr (Or.inr (h ▸ permAut_conj_lamNeg σ i j hij)))
  · intro hx
    rw [mem_dirEdge] at hx
    rcases hx with h | h | h | h
    · exact ⟨rho i j hij, by rw [mem_dirEdge]; exact Or.inl rfl,
        by rw [h]; simp only [conjFun]; exact permAut_conj_rho σ i j hij⟩
    · exact ⟨rhoNeg i j hij, by rw [mem_dirEdge]; exact Or.inr (Or.inl rfl),
        by rw [h]; simp only [conjFun]; exact permAut_conj_rhoNeg σ i j hij⟩
    · exact ⟨lam i j hij, by rw [mem_dirEdge]; exact Or.inr (Or.inr (Or.inl rfl)),
        by rw [h]; simp only [conjFun]; exact permAut_conj_lam σ i j hij⟩
    · exact ⟨lamNeg i j hij, by rw [mem_dirEdge]; exact Or.inr (Or.inr (Or.inr rfl)),
        by rw [h]; simp only [conjFun]; exact permAut_conj_lamNeg σ i j hij⟩

lemma sEdgeOf_image_conj (σ : Equiv.Perm (Fin m)) {i j : Fin m} (hij : i ≠ j) :
    (sEdgeOf i j hij).image (conjFun σ)
      = sEdgeOf (σ i) (σ j) (fun h => hij (σ.injective h)) := by
  rw [sEdgeOf, sEdgeOf, Finset.image_union, dirEdge_image_conj, dirEdge_image_conj]

lemma SEdge_eq_sEdgeOf_edgeOf (i j : Fin m) (hij : i ≠ j) :
    SEdge (edgeOf i j hij) = sEdgeOf i j hij := by
  have hmem := toFinset_edgeOf hij
  have h1 : i = (edgeOf i j hij).1.1 ∨ i = (edgeOf i j hij).1.2 := by
    have h : i ∈ (edgeOf i j hij).toFinset := by rw [hmem]; simp
    rw [toFinset] at h
    simpa using h
  have h2 : j = (edgeOf i j hij).1.1 ∨ j = (edgeOf i j hij).1.2 := by
    have h : j ∈ (edgeOf i j hij).toFinset := by rw [hmem]; simp
    rw [toFinset] at h
    simpa using h
  have := sEdgeOf_eq_of_vertices (ne_of_lt (edgeOf i j hij).2) hij h1 h2
  rw [SEdge_def]
  exact this

lemma SEdge_image_conj (σ : Equiv.Perm (Fin m)) (p : Edge m) :
    (SEdge p).image (conjFun σ) = SEdge (σ • p) := by
  rw [SEdge_def, SEdge_def, sEdgeOf_image_conj σ (ne_of_lt p.2)]
  have ht : (σ • p).toFinset = ({σ p.1.1, σ p.1.2} : Finset (Fin m)) := by
    rw [toFinset_smul]
    simp [toFinset]
  have hpair : ({σ p.1.1, σ p.1.2} : Finset (Fin m)) = (σ • p).toFinset := ht.symm
  exact sEdgeOf_eq_of_pair (fun h => ne_of_lt p.2 (σ.injective h)) (ne_of_lt (σ • p).2) hpair

/-- Conjugation by `permAut σ` on the group ring, in the `mapDomain`-image form. -/
lemma permRingHom_laplacian_image (σ : Equiv.Perm (Fin m))
    (S : Finset (MulAut (FreeGroup (Fin m)))) :
    permRingHom σ (OnPropertyT.Laplacian S) = OnPropertyT.Laplacian (S.image (conjFun σ)) := by
  rw [permRingHom_eq_conj]
  exact Commons.Algebra.MonoidAlgebra.conj_laplacian S (permAut σ)

/-- **Equivariance of the edge Laplacians** under the permutation action:
`permRingHom σ (Δ_e) = Δ_{σ • e}`. -/
theorem permRingHom_edgeLap (σ : Equiv.Perm (Fin m)) (p : Edge m) :
    permRingHom σ (edgeLap p) = edgeLap (σ • p) := by
  rw [edgeLap, permRingHom_laplacian_image, SEdge_image_conj, edgeLap]

/-- `permRingHom σ` commutes with `star`. -/
theorem permRingHom_star (σ : Equiv.Perm (Fin m))
    (x : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m)))) :
    permRingHom σ (star x) = star (permRingHom σ x) := by
  rw [permRingHom, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.mapDomainRingHom_apply]
  exact (Submission.Helpers.mapDomain_hom_star _ x).symm

/-! ## The decomposition `SAutGen m = ⨆_{e} SEdge e` and the elements `Δ_n`, `Sq_n`, `Adj_n`, `Op_n` -/

/-- Membership of the four transvections of an ordered pair in `SAutGen`. -/
lemma rho_mem_SAutGen' {i j : Fin m} (hij : i ≠ j) :
    rho i j hij ∈ (SAutGen m : Set (MulAut (FreeGroup (Fin m)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (true, true)), hij⟩, Finset.mem_univ _,
    by simp [sAutAut]⟩

lemma rhoNeg_mem_SAutGen' {i j : Fin m} (hij : i ≠ j) :
    rhoNeg i j hij ∈ (SAutGen m : Set (MulAut (FreeGroup (Fin m)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (true, false)), hij⟩, Finset.mem_univ _,
    by simp [sAutAut]⟩

lemma lam_mem_SAutGen' {i j : Fin m} (hij : i ≠ j) :
    lam i j hij ∈ (SAutGen m : Set (MulAut (FreeGroup (Fin m)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (false, true)), hij⟩, Finset.mem_univ _,
    by simp [sAutAut]⟩

lemma lamNeg_mem_SAutGen' {i j : Fin m} (hij : i ≠ j) :
    lamNeg i j hij ∈ (SAutGen m : Set (MulAut (FreeGroup (Fin m)))) := by
  classical
  rw [SAutGen]
  exact Finset.mem_image.mpr ⟨⟨((i, j), (false, false)), hij⟩, Finset.mem_univ _,
    by simp [sAutAut]⟩

lemma SEdge_subset_SAutGen (p : Edge m) {x : MulAut (FreeGroup (Fin m))} (hx : x ∈ SEdge p) :
    x ∈ SAutGen m := by
  rw [SEdge_def, mem_sEdgeOf] at hx
  rcases hx with hx | hx <;> rw [mem_dirEdge] at hx
  · rcases hx with h | h | h | h
    · rw [h]; exact rho_mem_SAutGen' (ne_of_lt p.2)
    · rw [h]; exact rhoNeg_mem_SAutGen' (ne_of_lt p.2)
    · rw [h]; exact lam_mem_SAutGen' (ne_of_lt p.2)
    · rw [h]; exact lamNeg_mem_SAutGen' (ne_of_lt p.2)
  · rcases hx with h | h | h | h
    · rw [h]; exact rho_mem_SAutGen' (ne_of_lt p.2).symm
    · rw [h]; exact rhoNeg_mem_SAutGen' (ne_of_lt p.2).symm
    · rw [h]; exact lam_mem_SAutGen' (ne_of_lt p.2).symm
    · rw [h]; exact lamNeg_mem_SAutGen' (ne_of_lt p.2).symm

/-- The sub-simplex on all vertices is everything. -/
lemma Esub_self (m : ℕ) : Esub m m = Finset.univ := by
  rw [Esub, Finset.filter_true_of_mem]
  intro p _
  exact ⟨p.1.1.isLt, p.1.2.isLt⟩

/-- The generating set of the transvections carried by the edges of a sub-simplex. -/
noncomputable def genSub (m r : ℕ) : Finset (MulAut (FreeGroup (Fin m))) :=
  (Esub m r).biUnion SEdge

/-- The Laplacian `Δ_r` of the sub-simplex, i.e. the sum of the edge-Laplacians. -/
noncomputable def deltaSub (m r : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  OnPropertyT.Laplacian (genSub m r)

set_option maxHeartbeats 800000 in
/-- Every Nielsen transvection index gives an element of the transvection set of an edge. -/
lemma sAutAut_mem_SEdge {i j : Fin m} (hij : i ≠ j) (b e : Bool) :
    sAutAut (⟨((i, j), (b, e)), hij⟩ : SAutIdx m) ∈ SEdge (edgeOf i j hij) := by
  rw [SEdge_eq_sEdgeOf_edgeOf, mem_sEdgeOf, mem_dirEdge, mem_dirEdge]
  cases b <;> cases e <;> simp [sAutAut]

set_option maxHeartbeats 800000 in
lemma SAutGen_subset_genSub {x : MulAut (FreeGroup (Fin m))} (hx : x ∈ SAutGen m) :
    x ∈ genSub m m := by
  rw [SAutGen] at hx
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨⟨⟨i, j⟩, ⟨b, e⟩⟩, hij⟩ := q
  refine Finset.mem_biUnion.mpr ⟨edgeOf i j hij, ?_, ?_⟩
  · rw [Esub_self]; exact Finset.mem_univ _
  · exact sAutAut_mem_SEdge hij b e

/-- **`SAutGen m` is the union of the transvection sets of the edges.** -/
theorem genSub_top (m : ℕ) : genSub m m = SAutGen m := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [genSub, Esub_self, Finset.mem_biUnion] at hx
    obtain ⟨p, -, hp⟩ := hx
    exact SEdge_subset_SAutGen p hp
  · intro x hx
    exact SAutGen_subset_genSub hx

/-- **The paper's `Delta using edges`.**  The Laplacian of the transvection
generating set is the sum of the edge-Laplacians. -/
theorem deltaSub_eq_sum (m r : ℕ) :
    deltaSub m r = ∑ p ∈ Esub m r, edgeLap p :=
  Commons.Algebra.MonoidAlgebra.laplacian_biUnion (Esub m r) SEdge
    (fun e _ f _ h => SEdge_disjoint h)

theorem deltaSub_top (m : ℕ) : deltaSub m m = OnPropertyT.Laplacian (SAutGen m) := by
  rw [deltaSub, genSub_top]

/-! ### The elements `Sq_n`, `Adj_n`, `Op_n` -/

lemma mem_Dsub_self {x : Edge m × Edge m} : x ∈ Dsub m m ↔ x.1 = x.2 := by
  rw [mem_Dsub, Esub_self]
  simp

lemma mem_Psub_self {x : Edge m × Edge m} : x ∈ Psub m m ↔ Adj x.1 x.2 := by
  rw [mem_Psub, Esub_self]
  simp

lemma mem_Qsub_self {x : Edge m × Edge m} : x ∈ Qsub m m ↔ Op x.1 x.2 := by
  rw [mem_Qsub, Esub_self]
  simp

/-- `Sq_n = ∑_{e} Δ_e²`, as a sum over the diagonal pairs of edges. -/
noncomputable def SqLap (m : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  ∑ x ∈ Dsub m m, edgeLap x.1 * edgeLap x.2

/-- `Adj_n = ∑_{e} Δ_e ∑_{f adjacent e} Δ_f`. -/
noncomputable def AdjLap (m : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  ∑ x ∈ Psub m m, edgeLap x.1 * edgeLap x.2

/-- `Op_n = ∑_{e} Δ_e ∑_{f opposite e} Δ_f`. -/
noncomputable def OpLap (m : ℕ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  ∑ x ∈ Qsub m m, edgeLap x.1 * edgeLap x.2

lemma product_eq_Dsub_Psub_Qsub (m : ℕ) :
    (Esub m m) ×ˢ (Esub m m) = Dsub m m ∪ (Psub m m ∪ Qsub m m) := by
  ext x
  rw [Finset.mem_product, Esub_self, Finset.mem_union, Finset.mem_union, mem_Dsub_self,
    mem_Psub_self, mem_Qsub_self]
  constructor
  · intro _
    by_cases h : x.1 = x.2
    · exact Or.inl h
    · rcases Edge.trichotomy h with h1 | h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
  · intro _
    exact ⟨Finset.mem_univ _, Finset.mem_univ _⟩

lemma disjoint_Dsub_Psub_union_Qsub (m : ℕ) :
    Disjoint (Dsub m m) (Psub m m ∪ Qsub m m) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_Dsub_self] at hx
  rw [Finset.mem_union, mem_Psub_self, mem_Qsub_self] at hx'
  rcases hx' with h | h
  · exact h.1 hx
  · exact Edge.op_irrefl x.1 (hx ▸ h)

lemma disjoint_Psub_Qsub (m : ℕ) : Disjoint (Psub m m) (Qsub m m) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_Psub_self] at hx
  rw [mem_Qsub_self] at hx'
  exact hx.2 hx'

/-- **The paper's `sum of sq adj op`**: `Δ_n² = Sq_n + Adj_n + Op_n`. -/
theorem deltaSub_sq_eq (m : ℕ) : deltaSub m m ^ 2 = SqLap m + AdjLap m + OpLap m := by
  have hprod : deltaSub m m ^ 2
      = ∑ x ∈ (Esub m m) ×ˢ (Esub m m), edgeLap x.1 * edgeLap x.2 := by
    rw [deltaSub_eq_sum, sq, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun p _ => Finset.mul_sum _ _ _)]
    exact (Finset.sum_product' (Esub m m) (Esub m m)
      (fun a b => edgeLap a * edgeLap b)).symm
  rw [hprod, product_eq_Dsub_Psub_Qsub, Finset.sum_union (disjoint_Dsub_Psub_union_Qsub m),
    Finset.sum_union (disjoint_Psub_Qsub m), SqLap, AdjLap, OpLap, add_assoc]

/-- `Sq_n ∈ Σ²` (the paper's `sq op sos`, first half). -/
theorem isSOS_SqLap (m : ℕ) : IsSOS (SqLap m) := by
  classical
  have h : SqLap m = ∑ x ∈ Dsub m m, star (edgeLap x.1) * edgeLap x.1 := by
    rw [SqLap]
    exact Finset.sum_congr rfl (fun x hx => by
      rw [mem_Dsub_self] at hx
      rw [hx, edgeLap_star])
  rw [h, ← Finset.sum_coe_sort (Dsub m m)
    (fun x : Edge m × Edge m => star (edgeLap x.1) * edgeLap x.1)]
  exact isSOS_of_fintype (fun x : (Dsub m m) => edgeLap x.1.1)

end Edge

end Submission.RouteB
