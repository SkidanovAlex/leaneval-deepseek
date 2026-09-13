import Submission.Grassmann.BSAvg
import Submission.Commons.LinearAlgebra.Matrix.rank_sub_eq
import Submission.Commons.LinearAlgebra.Matrix.mem_range_mul_mul_iff
import Submission.Commons.LinearAlgebra.Submodule.card_cell_good_ge_quarter
import Submission.Commons.LinearAlgebra.LinearMap.card_preimage_add_mul_card_range
import Submission.Grassmann.BKSNice
import Submission.Grassmann.HypHyperUC
import Submission.Grassmann.IHypStep
import Submission.Grassmann.Transfer

/-!
# The endgame of the BKS reduction (`arXiv:1804.08662` §3 ⟹ `theorem_1_12`)

This file finishes route (B): it converts the Inverse Shortcode Hypothesis (`HypSSE`, which is
unconditional via `HypHyperUC`) into the Grassmann Expansion Hypothesis (`ExpStmt`).

Given `S ⊆ Gr k ℓ` with `Φ(S) ≤ α` we

* choose (by `BSAvg.exists_good_basis`) a linear isomorphism `e : 𝔽₂^k ≃ₗ 𝔽₂^k` such that the
  good part `S ∩ G_e` of `S` (goodness = `grMap e` of the vertex lies in `V_ℓ(B₀)`) has no more
  external good edges than `Φ(S)·N₁·#(S ∩ G_e)`, where `N₁` is the number of rank-one matrices;
* transport `S ∩ G_e` to the set `T_e := φ(grMap e (S ∩ G_e))` of `ℓ × (k-ℓ)` matrices by BKS's
  homomorphism `φ = phiFin`;
* `φ` is a graph isomorphism from `G_e` endowed with Grassmann adjacency to its image with
  *rank-one* adjacency (`BKSHom.adj_iff_rank_one_fin`), and every good vertex has exactly `N₁`
  good neighbours, so the rank-one return probability of `T_e` is exactly
  `1 - Xnum/(N₁·Ynum) ≥ 1 - Φ(S) ≥ 1 - α`;
* hence `T_e` is not `(r+1, 2^{-C₀ r²})`-restriction global (contraposition of `HypSSE`), and
  `GlobalBS`-failure produces `Q, ι, T₀` and the "nice" set
  `Nice = T₀ + range (A ↦ ι A Q) = {M : ker Q ≤ ker(M - T₀) ∧ range(M - T₀) ≤ range ι}`, which
  meets `T_e` in a positive proportion of its elements;
* the pullback (`BKSNice.exists_subGr_of_nice`) of `Nice` is a cell `Gr[A,B]` with
  `dim A + codim B ≤ hybridOrder Q ι ≤ r+1`, and a quarter of `Gr[A,B]` is good
  (`Commons.LinearAlgebra.Submodule.card_cell_good_ge_quarter`), so `S` has density at least a
  constant in `Gr[A,B]`.

Everything is `Fin`-indexed so that it can be fed to `HypSSE`.
-/

open Finset BigOperators Matrix Filter
open Classical
open PseudorandomGrassmann
open Module

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {k ℓ : ℕ}

/-! ## The `VGood` structure of a good vertex -/

/-- The `VGood` structure carried by a good vertex. -/
def toVGood (L : GrVertex k ℓ) (h : IsGood L) : VGood k ℓ :=
  ⟨L.1, L.2, h⟩

@[simp] lemma toVGood_carrier (L : GrVertex k ℓ) (h : IsGood L) :
    (toVGood L h).carrier = L.1 := rfl

@[simp] lemma toVGood_toVertex (L : GrVertex k ℓ) (h : IsGood L) :
    VGood.toVertex (toVGood L h) = L := rfl

lemma eq_of_toVGood_eq {L L' : GrVertex k ℓ} {h : IsGood L} {h' : IsGood L'}
    (hh : toVGood L h = toVGood L' h') : L = L' := by
  have := congrArg VGood.toVertex hh
  simpa using this

/-! ## `phiFin` is a bijection -/

@[simp] lemma phiFin_apply' (h : ℓ ≤ k) (L : VGood k ℓ) :
    phiFin h L = Matrix.reindex (subLtEquiv h) (subGeEquiv h) (phi L) := rfl

lemma phiFin_injective (h : ℓ ≤ k) : Function.Injective (phiFin (k := k) (ℓ := ℓ) h) :=
  (Matrix.reindex (subLtEquiv h) (subGeEquiv h)).injective.comp (phi_injective h)

lemma phiFin_surjective (h : ℓ ≤ k) : Function.Surjective (phiFin (k := k) (ℓ := ℓ) h) :=
  (Matrix.reindex (subLtEquiv h) (subGeEquiv h)).surjective.comp (phi_surjective h)

/-- BKS's homomorphism, as an equivalence between good `ℓ`-subspaces and matrices. -/
noncomputable def phiEquiv (h : ℓ ≤ k) :
    VGood k ℓ ≃ Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂ :=
  Equiv.ofBijective (phiFin h) ⟨phiFin_injective h, phiFin_surjective h⟩

@[simp] lemma phiEquiv_apply (h : ℓ ≤ k) (L : VGood k ℓ) : phiEquiv h L = phiFin h L := rfl

lemma phiFin_apply_congr {h : ℓ ≤ k} {L L' : VGood k ℓ} (hh : L = L') : phiFin h L = phiFin h L' :=
  congrArg _ hh

/-! ## The transport of `S` to a set of matrices -/

/-- The good part of `S` in the basis `e`. -/
def Sgood (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) :
    Finset (GrVertex k ℓ) :=
  S.filter fun L => IsGood (F2.grMap e L)

lemma mem_Sgood {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)} {S : Finset (GrVertex k ℓ)}
    {L : GrVertex k ℓ} : L ∈ Sgood e S ↔ L ∈ S ∧ IsGood (F2.grMap e L) :=
  Finset.mem_filter

lemma card_Sgood (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) :
    (Sgood e S).card = Ynum S e := by
  rw [Sgood, Ynum, Finset.card_filter]

/-- The `φ`-image of a vertex, extended by `0` off the good set. -/
def psiGood (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂ :=
  if hL : IsGood (F2.grMap e L) then phiFin h (toVGood (F2.grMap e L) hL) else 0

lemma psiGood_of (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ)
    (hL : IsGood (F2.grMap e L)) :
    psiGood h e L = phiFin h (toVGood (F2.grMap e L) hL) := dif_pos hL

lemma psiGood_injOn (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :
    Set.InjOn (psiGood (ℓ := ℓ) (k := k) h e)
      {L : GrVertex k ℓ | IsGood (F2.grMap e L)} := by
  intro L hL L' hL' hh
  rw [psiGood_of h e L hL, psiGood_of h e L' hL'] at hh
  exact F2.grMap_injective e (eq_of_toVGood_eq (phiFin_injective h hh))

/-- **The BKS transport of `S`**: the set of matrices `φ(grMap e L)` for `L ∈ S` good in the
basis `e`. -/
def Te (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) :
    Finset (Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) :=
  (Sgood e S).image (psiGood h e)

lemma card_Te (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (S : Finset (GrVertex k ℓ)) : (Te h e S).card = Ynum S e := by
  rw [Te, Finset.card_image_of_injOn
      (Set.InjOn.mono (fun x hx => (mem_Sgood.mp hx).2) (psiGood_injOn h e)),
    card_Sgood]

lemma mem_Te {h : ℓ ≤ k} {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)} {S : Finset (GrVertex k ℓ)}
    {M : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂} :
    M ∈ Te h e S ↔ ∃ L ∈ S, ∃ _hL : IsGood (F2.grMap e L), psiGood h e L = M := by
  rw [Te, Finset.mem_image]
  constructor
  · rintro ⟨L, hL, rfl⟩
    exact ⟨L, (mem_Sgood.mp hL).1, (mem_Sgood.mp hL).2, rfl⟩
  · rintro ⟨L, hLS, hgood, rfl⟩
    exact ⟨L, mem_Sgood.mpr ⟨hLS, hgood⟩, rfl⟩


lemma toVGood_eq_of_same {L : GrVertex k ℓ} (h1 h2 : IsGood L) : toVGood L h1 = toVGood L h2 := by
  obtain rfl : h1 = h2 := Subsingleton.elim h1 h2
  rfl

lemma toVGood_toVertex_self {J : VGood k ℓ} (h : IsGood J.toVertex) :
    toVGood J.toVertex h = J := by
  cases J with
  | mk c f m =>
    have hh : h = m := Subsingleton.elim h m
    rw [hh]
    rfl

lemma toVGood_eq_of_val {L L' : GrVertex k ℓ} (h : L = L') (hL : IsGood L) (hL' : IsGood L') :
    toVGood L hL = toVGood L' hL' := by
  subst h
  obtain rfl : hL = hL' := Subsingleton.elim hL hL'
  rfl

/-! ## Adjacency is rank-one difference -/

/-- **The graph homomorphism, vertex form.** -/
lemma adj_toVertex_iff (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ) (L L' : VGood k ℓ) :
    (Gr k ℓ).Adj L.toVertex L'.toVertex ↔ (phiFin h L - phiFin h L').rank = 1 := by
  rw [Gr, SimpleGraph.fromRel]
  constructor
  · rintro ⟨-, hh | hh⟩
    · exact (adj_iff_rank_one_fin h L L' hℓ).mp hh
    · rw [inf_comm] at hh
      exact (adj_iff_rank_one_fin h L L' hℓ).mp hh
  · intro h1
    refine ⟨fun heq => ?_, Or.inl ((adj_iff_rank_one_fin h L L' hℓ).mpr h1)⟩
    have h2 := (adj_iff_rank_one_fin h L L' hℓ).mpr h1
    have hc : L'.carrier = L.carrier := (congrArg Subtype.val heq).symm
    rw [hc, inf_idem, L.finrank_eq] at h2
    omega

/-- **Adjacency in terms of `psiGood`.** -/
lemma adj_iff_rank_one_vertex (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L L' : GrVertex k ℓ)
    (hL : IsGood (F2.grMap e L)) (hL' : IsGood (F2.grMap e L')) :
    (Gr k ℓ).Adj L L' ↔ (psiGood h e L' - psiGood h e L).rank = 1 := by
  have key : (Gr k ℓ).Adj L L' ↔ (psiGood h e L - psiGood h e L').rank = 1 := by
    rw [← F2.grMap_adj_iff e L L', psiGood_of h e L hL, psiGood_of h e L' hL']
    exact adj_toVertex_iff h hℓ (toVGood (F2.grMap e L) hL) (toVGood (F2.grMap e L') hL')
  rw [key]
  refine ⟨?_, ?_⟩
  · intro h1
    rwa [Commons.LinearAlgebra.Matrix.rank_sub_eq (psiGood h e L) (psiGood h e L')] at h1
  · intro h1
    rwa [Commons.LinearAlgebra.Matrix.rank_sub_eq (psiGood h e L') (psiGood h e L)] at h1

/-! ## Counting the good neighbours -/

/-- The vertex whose `φ`-image is the matrix `M`. -/
def preVGood (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (M : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) : GrVertex k ℓ :=
  F2.grMap e.symm ((phiEquiv h).symm M).toVertex

lemma grMap_preVGood (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (M : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) :
    F2.grMap e (preVGood h e M) = ((phiEquiv h).symm M).toVertex := by
  rw [preVGood, F2.grMap_grMap_symm]

lemma isGood_preVGood (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (M : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) : IsGood (F2.grMap e (preVGood h e M)) := by
  rw [grMap_preVGood]
  exact ((phiEquiv h).symm M).map_eq_top

lemma psiGood_preVGood (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (M : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) : psiGood h e (preVGood h e M) = M := by
  rw [psiGood_of h e _ (isGood_preVGood h e M)]
  have h1 : toVGood (F2.grMap e (preVGood h e M)) (isGood_preVGood h e M)
      = (phiEquiv h).symm M := by
    rw [toVGood_eq_of_val (grMap_preVGood h e M) (isGood_preVGood h e M)
      (((phiEquiv h).symm M).map_eq_top)]
    exact toVGood_toVertex_self (((phiEquiv h).symm M).map_eq_top)
  rw [h1, ← phiEquiv_apply h ((phiEquiv h).symm M), Equiv.apply_symm_apply]

lemma psiGood_inj (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) {L L' : GrVertex k ℓ}
    (hL : IsGood (F2.grMap e L)) (hL' : IsGood (F2.grMap e L'))
    (hh : psiGood h e L = psiGood h e L') : L = L' :=
  psiGood_injOn h e hL hL' hh

/-- **The bijection between rank-one matrices and the good neighbours of a good vertex.** -/
noncomputable def nbrEquiv (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ)
    (hL : IsGood (F2.grMap e L)) :
    {B : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂ // B.rank = 1} ≃
      {L' : GrVertex k ℓ // IsGood (F2.grMap e L') ∧ (Gr k ℓ).Adj L L'} where
  toFun B :=
    ⟨preVGood h e (psiGood h e L + B.1), isGood_preVGood h e _,
      (adj_iff_rank_one_vertex h hℓ e L _ hL (isGood_preVGood h e _)).mpr (by
        rw [psiGood_preVGood, add_sub_cancel_left]
        exact B.2)⟩
  invFun L' :=
    ⟨psiGood h e L'.1 - psiGood h e L,
      ((adj_iff_rank_one_vertex h hℓ e L L'.1 hL L'.2.1).mp L'.2.2)⟩
  left_inv B := by
    refine Subtype.ext ?_
    show psiGood h e (preVGood h e (psiGood h e L + B.1)) - psiGood h e L = B.1
    rw [psiGood_preVGood, add_sub_cancel_left]
  right_inv L' := by
    refine Subtype.ext ?_
    show preVGood h e (psiGood h e L + (psiGood h e L'.1 - psiGood h e L)) = L'.1
    have hsum : psiGood h e L + (psiGood h e L'.1 - psiGood h e L) = psiGood h e L'.1 := by
      abel
    rw [hsum]
    exact psiGood_inj h e (isGood_preVGood h e _) L'.2.1 (by rw [psiGood_preVGood])

/-- **Every good vertex has exactly `N₁` good neighbours.** -/
lemma card_good_nbrs (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ)
    (hL : IsGood (F2.grMap e L)) :
    (Finset.univ.filter (fun L' : GrVertex k ℓ =>
        IsGood (F2.grMap e L') ∧ (Gr k ℓ).Adj L L')).card = (rankOneSet ℓ (k - ℓ)).card := by
  have hB : Nat.card {B : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂ // B.rank = 1}
      = (rankOneSet ℓ (k - ℓ)).card := by
    simp only [rankOneSet, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hL' : Nat.card {L' : GrVertex k ℓ //
        IsGood (F2.grMap e L') ∧ (Gr k ℓ).Adj L L'}
      = (Finset.univ.filter (fun L' : GrVertex k ℓ =>
          IsGood (F2.grMap e L') ∧ (Gr k ℓ).Adj L L')).card := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← hL', ← hB]
  exact (Nat.card_congr (nbrEquiv h hℓ e L hL)).symm

/-! ## The rank-one return probability of `T_e` -/

-- We resolve decidability through the classical instances so that terms such as `Sᶜ`
-- are elaborated exactly as in `Xnum` (whose `DecidableEq` came from `Classical.propDecidable`).
attribute [-instance] Subtype.instDecidableEq

/-- `sseRow` as a cardinality of rank-one shifts that stay inside. -/
lemma sseRow_eq_card {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂))
    (A : Matrix (Fin m) (Fin n) 𝔽₂) :
    sseRow S A = (((rankOneSet m n).filter fun B => A + B ∈ S).card : ℝ) := by
  rw [sseRow, Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun B _ => by
    by_cases h : A + B ∈ S <;> simp [h]

/-- `sseNum` as a sum of cardinalities. -/
lemma sseNum_eq_sum_card {m n : ℕ} (S : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    sseNum S = ∑ A ∈ S, (((rankOneSet m n).filter fun B => A + B ∈ S).card : ℝ) := by
  rw [sseNum]
  exact Finset.sum_congr rfl fun A _ => sseRow_eq_card S A

lemma mem_rankOneSet {m n : ℕ} {B : Matrix (Fin m) (Fin n) 𝔽₂} :
    B ∈ rankOneSet m n ↔ B.rank = 1 := by
  simp only [rankOneSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The rank-one neighbours of `psiGood h e L` inside `Te` are exactly the good neighbours of
`L` inside `S`. -/
lemma filter_rankOne_eq_image (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ)
    (hL : IsGood (F2.grMap e L)) :
    ((rankOneSet ℓ (k - ℓ)).filter (fun B => psiGood h e L + B ∈ Te h e S))
      = ((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).image
          (fun L' => psiGood h e L' - psiGood h e L) := by
  refine Finset.ext fun B => ?_
  rw [Finset.mem_filter, mem_rankOneSet, Finset.mem_image]
  constructor
  · rintro ⟨hrank, hmem⟩
    rw [mem_Te] at hmem
    obtain ⟨L', hLS, hL', heq⟩ := hmem
    have hBL : psiGood h e L' - psiGood h e L = B := by
      rw [heq]; abel
    refine ⟨L', ?_, hBL⟩
    rw [Finset.mem_filter, mem_Sgood]
    exact ⟨⟨hLS, hL'⟩, (adj_iff_rank_one_vertex h hℓ e L L' hL hL').mpr (by rw [hBL]; exact hrank)⟩
  · rintro ⟨L', hL'mem, hB⟩
    rw [Finset.mem_filter, mem_Sgood] at hL'mem
    obtain ⟨⟨hLS, hL'⟩, hadj⟩ := hL'mem
    have hrank : (psiGood h e L' - psiGood h e L).rank = 1 :=
      (adj_iff_rank_one_vertex h hℓ e L L' hL hL').mp hadj
    refine ⟨?_, ?_⟩
    · rw [← hB]; exact hrank
    · rw [mem_Te]
      refine ⟨L', hLS, hL', ?_⟩
      rw [← hB]; abel

lemma card_filter_rankOne (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ)
    (hL : IsGood (F2.grMap e L)) :
    (((rankOneSet ℓ (k - ℓ)).filter (fun B => psiGood h e L + B ∈ Te h e S)).card)
      = (((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card) := by
  rw [filter_rankOne_eq_image h hℓ e S L hL, Finset.card_image_of_injOn]
  intro L₁ h₁ L₂ h₂ hh
  have hg₁ : IsGood (F2.grMap e L₁) := (mem_Sgood.mp (Finset.mem_filter.mp h₁).1).2
  have hg₂ : IsGood (F2.grMap e L₂) := (mem_Sgood.mp (Finset.mem_filter.mp h₂).1).2
  refine psiGood_inj h e hg₁ hg₂ ?_
  have hh' := congrArg (· + psiGood h e L) hh
  simpa [sub_add_cancel] using hh'

/-- **The rank-one return count of `T_e`.** -/
lemma sseNum_image (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) :
    sseNum ((Sgood e S).image (psiGood h e))
      = ∑ L ∈ Sgood e S, (((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card : ℝ) := by
  rw [sseNum_eq_sum_card]
  rw [Finset.sum_image
    (Set.InjOn.mono (fun x hx => (mem_Sgood.mp hx).2) (psiGood_injOn h e))]
  exact Finset.sum_congr rfl fun L hL => by
    show (((rankOneSet ℓ (k - ℓ)).filter (fun B => psiGood h e L + B ∈ Te h e S)).card : ℝ)
      = (((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card : ℝ)
    rw [card_filter_rankOne h hℓ e S L (mem_Sgood.mp hL).2]

lemma sseNum_Te (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) :
    sseNum (Te h e S)
      = ∑ L ∈ Sgood e S, (((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card : ℝ) :=
  sseNum_image h hℓ e S

/-! ## The number of good neighbours is `N₁`, split by side -/

/-- The set of vertices that are good in the basis `e`. -/
def Ggood (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) : Finset (GrVertex k ℓ) :=
  Finset.univ.filter fun L => IsGood (F2.grMap e L)

lemma mem_Ggood {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)} {L : GrVertex k ℓ} :
    L ∈ Ggood e ↔ IsGood (F2.grMap e L) := by
  simp only [Ggood, Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_Ggood_sdiff {e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)}
    {S : Finset (GrVertex k ℓ)} {L : GrVertex k ℓ} :
    L ∈ Ggood e \ Sgood e S ↔ IsGood (F2.grMap e L) ∧ L ∉ S := by
  rw [Finset.mem_sdiff, mem_Ggood, mem_Sgood]
  constructor
  · rintro ⟨hg, hn⟩
    exact ⟨hg, fun hS => hn ⟨hS, hg⟩⟩
  · rintro ⟨hg, hS⟩
    exact ⟨hg, fun hc => hS hc.1⟩

lemma Sgood_subset_Ggood (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (S : Finset (GrVertex k ℓ)) : Sgood e S ⊆ Ggood e := fun L hL => by
  rw [mem_Ggood, mem_Sgood] at *
  exact hL.2

lemma Ggood_filter_eq (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ) :
    (Ggood e).filter (fun L' => (Gr k ℓ).Adj L L')
      = Finset.univ.filter (fun L' : GrVertex k ℓ =>
          IsGood (F2.grMap e L') ∧ (Gr k ℓ).Adj L L') := by
  ext L'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_Ggood]

/-- The good neighbours of `L` split into those in `S` and those outside. -/
lemma card_Ggood_filter (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (S : Finset (GrVertex k ℓ)) (L : GrVertex k ℓ) :
    ((Ggood e).filter (fun L' => (Gr k ℓ).Adj L L')).card
      = ((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card
        + ((Ggood e \ Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card := by
  have h1 : ((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L'))
      ∪ ((Ggood e \ Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L'))
      = (Ggood e).filter (fun L' => (Gr k ℓ).Adj L L') := by
    rw [← Finset.filter_union, Finset.union_sdiff_of_subset (Sgood_subset_Ggood e S)]
  rw [← h1, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr fun x hx1 hx2 =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx2).1).2 (Finset.mem_filter.mp hx1).1

/-- **Every good vertex has exactly `N₁` good neighbours.** -/
lemma card_Ggood_nbrs (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (L : GrVertex k ℓ)
    (hL : IsGood (F2.grMap e L)) :
    ((Ggood e).filter (fun L' => (Gr k ℓ).Adj L L')).card = (rankOneSet ℓ (k - ℓ)).card := by
  rw [Ggood_filter_eq]
  exact card_good_nbrs h hℓ e L hL

/-- **`Xnum` is the number of good external edges, written as a sum over `Sgood`.** -/
lemma Xnum_eq_sum_sdiff (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (S : Finset (GrVertex k ℓ)) :
    Xnum S e = ∑ L ∈ Sgood e S,
      (((Ggood e \ Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card) := by
  rw [Xnum]
  have hstep : ∀ L : GrVertex k ℓ,
      (∑ L' ∈ Sᶜ, if (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L)
        ∧ IsGood (F2.grMap e L') then 1 else 0)
      = if IsGood (F2.grMap e L) then
          (((Ggood e \ Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card) else 0 := by
    intro L
    by_cases hL : IsGood (F2.grMap e L)
    · rw [if_pos hL]
      have h1 : (∑ L' ∈ Sᶜ, if (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L)
            ∧ IsGood (F2.grMap e L') then 1 else 0)
          = ∑ L' ∈ Sᶜ, if (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L') then 1 else 0 := by
        refine Finset.sum_congr rfl fun L' _ => ?_
        by_cases hh : (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L')
        · rw [if_pos ⟨hh.1, hL, hh.2⟩, if_pos hh]
        · rw [if_neg (fun hc => hh ⟨hc.1, hc.2.2⟩), if_neg hh]
      rw [h1, Finset.sum_boole]
      refine congrArg Finset.card ?_
      ext L'
      simp only [Finset.mem_filter, Finset.mem_sdiff, mem_Ggood, mem_Sgood,
        Finset.mem_compl]
      tauto
    · rw [if_neg hL]
      refine Finset.sum_eq_zero fun L' _ => ?_
      rw [if_neg]
      intro hc
      exact hL hc.2.1
  have h1 : (∑ L ∈ S, ∑ L' ∈ Sᶜ, if (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L)
        ∧ IsGood (F2.grMap e L') then 1 else 0)
      = ∑ L ∈ Sgood e S, ∑ L' ∈ Sᶜ, if (Gr k ℓ).Adj L L' ∧ IsGood (F2.grMap e L)
        ∧ IsGood (F2.grMap e L') then 1 else 0 := by
    refine (Finset.sum_subset (fun L hL => (mem_Sgood.mp hL).1) ?_).symm
    intro L hLS hLnot
    refine Finset.sum_eq_zero fun L' _ => ?_
    rw [if_neg]
    intro hc
    exact hLnot (mem_Sgood.mpr ⟨hLS, hc.2.1⟩)
  rw [h1]
  exact Finset.sum_congr rfl fun L hL => by
    rw [hstep L, if_pos (mem_Sgood.mp hL).2]

/-- **The rank-one return count of `T_e`, added to the external count.** -/
lemma Xnum_add_sseNum_Te_ge (h : ℓ ≤ k) (hℓ : 2 ≤ ℓ)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) :
    (Xnum S e : ℝ) + sseNum (Te h e S)
      ≥ (Ynum S e : ℝ) * ((rankOneSet ℓ (k - ℓ)).card : ℝ) := by
  set c : GrVertex k ℓ → ℕ := fun L => ((Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card
    with hc
  set d : GrVertex k ℓ → ℕ :=
    fun L => ((Ggood e \ Sgood e S).filter (fun L' => (Gr k ℓ).Adj L L')).card with hd
  have hcd : ∀ L ∈ Sgood e S, c L + d L = (rankOneSet ℓ (k - ℓ)).card := by
    intro L hL
    rw [hc, hd]
    rw [← card_Ggood_filter e S L, card_Ggood_nbrs h hℓ e L (mem_Sgood.mp hL).2]
  have hdsum : (∑ L ∈ Sgood e S, d L) = Xnum S e := by
    rw [hd]
    exact (Xnum_eq_sum_sdiff e S).symm
  have htot : (∑ L ∈ Sgood e S, c L) + Xnum S e
      = (Sgood e S).card * (rankOneSet ℓ (k - ℓ)).card := by
    rw [← hdsum, ← Finset.sum_add_distrib, Finset.sum_congr rfl hcd, Finset.sum_const]
    simp
  have hsse : sseNum (Te h e S) = ((∑ L ∈ Sgood e S, c L : ℕ) : ℝ) := by
    rw [sseNum_Te h hℓ e S]
    simp only [hc, Nat.cast_sum]
  rw [hsse, ← Nat.cast_add, add_comm, htot, card_Sgood e S, Nat.cast_mul]

/-! ## The density bridge: `GlobalBS`-failure is a density statement -/

/-- The linear map `A ↦ ι * A * Q`. -/
def sandwich {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) :
    Matrix (Fin m') (Fin n') 𝔽₂ →ₗ[𝔽₂] Matrix (Fin m) (Fin n) 𝔽₂ where
  toFun A := ι * A * Q
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] lemma sandwich_apply {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (A : Matrix (Fin m') (Fin n') 𝔽₂) :
    sandwich Q ι A = ι * A * Q := rfl

/-- The "nice" set of matrices: the coset `T₀ + range (A ↦ ι A Q)`. -/
def NiceF {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
    (T₀ : Matrix (Fin m) (Fin n) 𝔽₂) : Finset (Matrix (Fin m) (Fin n) 𝔽₂) :=
  Finset.univ.filter fun M => M - T₀ ∈ LinearMap.range (sandwich Q ι)

lemma mem_NiceF {m n m' n' : ℕ} {Q : Matrix (Fin n') (Fin n) 𝔽₂}
    {ι : Matrix (Fin m) (Fin m') 𝔽₂} {T₀ : Matrix (Fin m) (Fin n) 𝔽₂}
    {M : Matrix (Fin m) (Fin n) 𝔽₂} :
    M ∈ NiceF Q ι T₀ ↔ M - T₀ ∈ LinearMap.range (sandwich Q ι) := by
  simp only [NiceF, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The "nice" constraint is the pair of BKS conditions.** -/
lemma mem_NiceF_iff {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T₀ : Matrix (Fin m) (Fin n) 𝔽₂)
    (M : Matrix (Fin m) (Fin n) 𝔽₂) :
    M ∈ NiceF Q ι T₀ ↔ (LinearMap.ker Q.mulVecLin ≤ LinearMap.ker (M - T₀).mulVecLin ∧
      LinearMap.range (M - T₀).mulVecLin ≤ LinearMap.range ι.mulVecLin) := by
  rw [mem_NiceF, LinearMap.mem_range]
  exact Commons.LinearAlgebra.Matrix.mem_range_mul_mul_iff Q ι (M - T₀)

/-- Translation by `T₀` is a bijection onto the range of `sandwich Q ι`. -/
noncomputable def niceEquiv {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T₀ : Matrix (Fin m) (Fin n) 𝔽₂) :
    {M : Matrix (Fin m) (Fin n) 𝔽₂ // M - T₀ ∈ LinearMap.range (sandwich Q ι)} ≃
      ↥(LinearMap.range (sandwich Q ι)) where
  toFun M := ⟨M.1 - T₀, M.2⟩
  invFun Y := ⟨Y.1 + T₀, by rw [add_sub_cancel_right]; exact Y.2⟩
  left_inv M := by ext; simp
  right_inv Y := by ext; simp

lemma card_NiceF {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T₀ : Matrix (Fin m) (Fin n) 𝔽₂) :
    (NiceF Q ι T₀).card = Nat.card ↥(LinearMap.range (sandwich Q ι)) := by
  rw [NiceF, ← Fintype.card_subtype (p := fun M : Matrix (Fin m) (Fin n) 𝔽₂ =>
    M - T₀ ∈ LinearMap.range (sandwich Q ι)), ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (niceEquiv Q ι T₀)

/-! ## The pullback of the nice set -/

/-- **`phiFin`-pullback of the nice set.** -/
lemma phiFin_mem_NiceF_iff {n' m' : ℕ} (h : ℓ ≤ k) (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂)
    (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂) (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂)
    (L : VGood k ℓ) :
    phiFin h L ∈ NiceF Q ι T₀ ↔
      (LinearMap.ker Q.mulVecLin ≤ LinearMap.ker ((phiFin h L - T₀).mulVecLin) ∧
        LinearMap.range ((phiFin h L - T₀).mulVecLin) ≤ LinearMap.range ι.mulVecLin) :=
  mem_NiceF_iff Q ι T₀ (phiFin h L)

/-- **The pullback, in terms of the cell `[A,B]`.** -/
lemma phiFin_mem_NiceF_iff_cell {n' m' : ℕ} (h : ℓ ≤ k)
    (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂) (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hAB : ∀ L : VGood k ℓ,
      (LinearMap.ker Q.mulVecLin ≤ LinearMap.ker ((phiFin h L - T₀).mulVecLin) ∧
        LinearMap.range ((phiFin h L - T₀).mulVecLin) ≤ LinearMap.range ι.mulVecLin) ↔
      (A ≤ L.carrier ∧ L.carrier ≤ B)) (L : VGood k ℓ) :
    phiFin h L ∈ NiceF Q ι T₀ ↔ (A ≤ L.carrier ∧ L.carrier ≤ B) :=
  (phiFin_mem_NiceF_iff h Q ι T₀ L).trans (hAB L)

/-- The number of nice matrices, as the number of good subspaces in the cell. -/
lemma card_NiceF_eq_vgood {n' m' : ℕ} (h : ℓ ≤ k)
    (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂) (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hAB : ∀ L : VGood k ℓ, phiFin h L ∈ NiceF Q ι T₀ ↔ (A ≤ L.carrier ∧ L.carrier ≤ B)) :
    (NiceF Q ι T₀).card = Nat.card {J : VGood k ℓ // A ≤ J.carrier ∧ J.carrier ≤ B} := by
  have h1 : Nat.card ↥(NiceF Q ι T₀) = (NiceF Q ι T₀).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have h2 : Nat.card ↥(NiceF Q ι T₀)
      = Nat.card {J : VGood k ℓ // A ≤ J.carrier ∧ J.carrier ≤ B} :=
    (Nat.card_congr (Equiv.subtypeEquiv (phiEquiv h) (fun L => (hAB L).symm))).symm
  rw [← h1]
  exact h2


/-! ## Cells, bijections and the relative count -/

/-- `A ≤ L.map e` if and only if `comap e A ≤ L`. -/
lemma map_le_iff_comap_le (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (A L : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    (A ≤ L.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))) ↔
      (Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A ≤ L) := by
  constructor
  · intro h
    calc Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A
        ≤ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
            (L.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))) := Submodule.comap_mono h
      _ = L := by
        rw [Submodule.comap_map_eq, LinearEquiv.ker, sup_bot_eq]
  · intro h
    calc A = Submodule.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂))
            (Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A) := by
          rw [Submodule.map_comap_eq, LinearMap.range_eq_top.mpr e.surjective, top_inf_eq]
      _ ≤ Submodule.map (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) L := Submodule.map_mono h

/-- The bijection between good vertices and `VGood` structures. -/
noncomputable def vgEquiv (k ℓ : ℕ) : {L : GrVertex k ℓ // IsGood L} ≃ VGood k ℓ where
  toFun L := ⟨L.1.1, L.1.2, L.2⟩
  invFun J := ⟨⟨J.1, J.2⟩, J.3⟩
  left_inv _ := Subtype.ext rfl
  right_inv J := by cases J with | mk c f m => rfl

/-- The bijection between good subspaces in a cell and good *vertices* in the same cell. -/
noncomputable def vgoodCellEquiv (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    {J : VGood k ℓ // A ≤ J.carrier ∧ J.carrier ≤ B} ≃
      {L : GrVertex k ℓ // IsGood L ∧ A ≤ L.1 ∧ L.1 ≤ B} where
  toFun J := ⟨J.1.toVertex, J.1.map_eq_top, J.2.1, J.2.2⟩
  invFun L := ⟨⟨L.1.1, L.1.2, L.2.1⟩, L.2.2.1, L.2.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

lemma card_vgoodCell_eq (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Nat.card {J : VGood k ℓ // A ≤ J.carrier ∧ J.carrier ≤ B}
      = Nat.card {L : GrVertex k ℓ // IsGood L ∧ A ≤ L.1 ∧ L.1 ≤ B} :=
  Nat.card_congr (vgoodCellEquiv A B)

/-- The permutation of the Grassmannian induced by a linear equivalence, as an `Equiv`. -/
noncomputable def grMapEquiv (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :
    GrVertex k ℓ ≃ GrVertex k ℓ where
  toFun := F2.grMap e
  invFun := F2.grMap e.symm
  left_inv := F2.grMap_symm_grMap e
  right_inv := F2.grMap_grMap_symm e

/-- **The cell count is invariant under `grMap`.** -/
lemma card_grCell_eq (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Nat.card {L : GrVertex k ℓ // IsGood (F2.grMap e L) ∧
        Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A ≤ L.1 ∧
        L.1 ≤ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) B}
      = Nat.card {L : GrVertex k ℓ // IsGood L ∧ A ≤ L.1 ∧ L.1 ≤ B} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (grMapEquiv e) (fun L => ?_))
  show (IsGood (F2.grMap e L) ∧ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A ≤ L.1 ∧
      L.1 ≤ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) B) ↔
    (IsGood (F2.grMap e L) ∧ A ≤ (F2.grMap e L).1 ∧ (F2.grMap e L).1 ≤ B)
  rw [F2.grMap_val]
  exact and_congr Iff.rfl
    ⟨fun h => ⟨(map_le_iff_comap_le e A L.1).mpr h.1,
        Submodule.map_le_iff_le_comap.mpr h.2⟩,
      fun h => ⟨(map_le_iff_comap_le e A L.1).mp h.1,
        Submodule.map_le_iff_le_comap.mp h.2⟩⟩


/-! ## The `l2sq` of a restriction of an indicator -/

lemma l2sq_restr_shift_ind {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T₀ : Matrix (Fin m) (Fin n) 𝔽₂)
    (U : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    l2sq (restr Q ι (shift T₀ (ind U)))
      = ((2 : ℝ) ^ (m' * n'))⁻¹ * (Nat.card {A : Matrix (Fin m') (Fin n') 𝔽₂ //
          ι * A * Q + T₀ ∈ U} : ℝ) := by
  rw [l2sq]
  congr 1
  have h1 : ∀ A : Matrix (Fin m') (Fin n') 𝔽₂,
      ‖restr Q ι (shift T₀ (ind U)) A‖ ^ 2
        = if ι * A * Q + T₀ ∈ U then (1 : ℝ) else 0 := by
    intro A
    rw [show restr Q ι (shift T₀ (ind U)) A = ind U (ι * A * Q + T₀) from rfl,
      ind_eq_ofReal]
    by_cases h : ι * A * Q + T₀ ∈ U <;> simp [h]
  rw [Finset.sum_congr rfl (fun A _ => h1 A), Finset.sum_boole,
    ← Fintype.card_subtype (p := fun A : Matrix (Fin m') (Fin n') 𝔽₂ =>
      ι * A * Q + T₀ ∈ U), ← Nat.card_eq_fintype_card]

/-! ## The transfer of the density statement -/

/-- The number of `T_e`-elements inside the nice set. -/
lemma card_Te_inter_NiceF {n' m' : ℕ} (h : ℓ ≤ k)
    (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂) (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hAB : ∀ L : VGood k ℓ, phiFin h L ∈ NiceF Q ι T₀ ↔ (A ≤ L.carrier ∧ L.carrier ≤ B))
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (S : Finset (GrVertex k ℓ)) :
    ((Te h e S).filter (fun M => M ∈ NiceF Q ι T₀)).card
      = ((Sgood e S).filter (fun L =>
          A ≤ (F2.grMap e L).1 ∧ (F2.grMap e L).1 ≤ B)).card := by
  have hset : (Te h e S).filter (fun M => M ∈ NiceF Q ι T₀)
      = ((Sgood e S).filter (fun L => psiGood h e L ∈ NiceF Q ι T₀)).image
          (psiGood h e) := by
    rw [Te, Finset.filter_image]
  have hset2 : (Sgood e S).filter (fun L => psiGood h e L ∈ NiceF Q ι T₀)
      = (Sgood e S).filter (fun L =>
          A ≤ (F2.grMap e L).1 ∧ (F2.grMap e L).1 ≤ B) := by
    refine Finset.filter_congr fun L hL => ?_
    rw [psiGood_of h e L (mem_Sgood.mp hL).2, hAB (toVGood (F2.grMap e L) (mem_Sgood.mp hL).2)]
    rfl
  rw [hset, hset2, Finset.card_image_of_injOn
    (Set.InjOn.mono (fun x hx => (mem_Sgood.mp (Finset.mem_filter.mp hx).1).2)
      (psiGood_injOn h e))]

/-- The number of nice matrices equals the number of good vertices in the cell. -/
lemma card_NiceF_eq_grCell {n' m' : ℕ} (h : ℓ ≤ k)
    (Q : Matrix (Fin n') (Fin (k - ℓ)) 𝔽₂) (ι : Matrix (Fin ℓ) (Fin m') 𝔽₂)
    (T₀ : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hAB : ∀ L : VGood k ℓ, phiFin h L ∈ NiceF Q ι T₀ ↔ (A ≤ L.carrier ∧ L.carrier ≤ B))
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) :
    (NiceF Q ι T₀).card
      = Nat.card {L : GrVertex k ℓ // IsGood (F2.grMap e L) ∧
          Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A ≤ L.1 ∧
          L.1 ≤ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) B} := by
  rw [card_NiceF_eq_vgood h Q ι T₀ A B hAB, card_vgoodCell_eq A B]
  exact (card_grCell_eq e A B).symm

/-! ## The relative count -/

/-- Vertices in a cell, as subspaces in the same cell. -/
noncomputable def cellSubEquiv (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    {L : GrVertex k ℓ // A ≤ L.1 ∧ L.1 ≤ B} ≃
      {U : Submodule 𝔽₂ (Fin k → 𝔽₂) //
        Module.finrank 𝔽₂ U = ℓ ∧ A ≤ U ∧ U ≤ B} where
  toFun L := ⟨L.1.1, L.1.2, L.2.1, L.2.2⟩
  invFun U := ⟨⟨U, U.2.1⟩, U.2.2.1, U.2.2.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Good vertices in a cell, as subspaces in the same cell meeting `K` trivially. -/
noncomputable def cellGoodEquiv (h : ℓ ≤ k) (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    {L : GrVertex k ℓ // IsGood (F2.grMap e L) ∧ A ≤ L.1 ∧ L.1 ≤ B} ≃
      {U : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ U = ℓ ∧ A ≤ U ∧ U ≤ B ∧
        U ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k) = ⊥} where
  toFun L := ⟨L.1.1, L.1.2, L.2.2.1, L.2.2.2, (IsGood_grMap_iff h e L.1).mp L.2.1⟩
  invFun U := ⟨⟨U, U.2.1⟩, (IsGood_grMap_iff h e ⟨U, U.2.1⟩).mpr U.2.2.2.2,
    U.2.2.1, U.2.2.2.1⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- **A quarter of a cell is good.** -/
theorem card_good_cell_ge_quarter (h : ℓ ≤ k)
    (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂)) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hne : ∃ L : GrVertex k ℓ, IsGood (F2.grMap e L) ∧ A ≤ L.1 ∧ L.1 ≤ B) :
    4 * Nat.card {L : GrVertex k ℓ // IsGood (F2.grMap e L) ∧ A ≤ L.1 ∧ L.1 ≤ B}
      ≥ Nat.card {L : GrVertex k ℓ // A ≤ L.1 ∧ L.1 ≤ B} := by
  have hne' : ∃ U : Submodule 𝔽₂ (Fin k → 𝔽₂), Module.finrank 𝔽₂ U = ℓ ∧ A ≤ U ∧ U ≤ B ∧
      U ⊓ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k) = ⊥ := by
    obtain ⟨L, hg, hA, hB⟩ := hne
    exact ⟨L.1, L.2, hA, hB, (IsGood_grMap_iff h e L).mp hg⟩
  have hAB : A ≤ B := by
    obtain ⟨U, -, hA, hB, -⟩ := hne'
    exact le_trans hA hB
  have hq := Commons.LinearAlgebra.Submodule.card_cell_good_ge_quarter
    (Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) (kernFirst ℓ k)) A B
    (finrank_comap_grMap h e) hAB hne'
  rw [← Nat.card_congr (cellGoodEquiv h e A B), ← Nat.card_congr (cellSubEquiv A B)] at hq
  exact hq


/-! ## Assembly -/

-- Re-enable the `Subtype` decidability instance so that the statement below is elaborated
-- exactly as in `F2.ExpStmt`.
attribute [instance] Subtype.instDecidableEq

/-- `GlobalBS`-failure produces a restriction with large `l2sq`. -/
lemma exists_of_not_globalBS {m n : ℕ} {d : ℕ} {ε : ℝ}
    {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (h : ¬ GlobalBS d ε f) :
    ∃ (m' n' : ℕ) (Q : Matrix (Fin n') (Fin n) 𝔽₂) (ι : Matrix (Fin m) (Fin m') 𝔽₂)
      (T : Matrix (Fin m) (Fin n) 𝔽₂),
      hybridOrder Q ι ≤ d ∧ ε < l2sq (restr Q ι (shift T f)) := by
  rw [GlobalBS] at h
  push_neg at h
  obtain ⟨m', n', Q, ι, h1, T, h2⟩ := h
  exact ⟨m', n', Q, ι, T, h1, h2⟩

lemma natCard_matrix (m' n' : ℕ) : Nat.card (Matrix (Fin m') (Fin n') 𝔽₂) = 2 ^ (m' * n') := by
  rw [Nat.card_eq_fintype_card]
  show Fintype.card (Fin m' → Fin n' → 𝔽₂) = 2 ^ (m' * n')
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
  rw [← pow_mul, Nat.mul_comm]

lemma card_filter_NiceF {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (T₀ : Matrix (Fin m) (Fin n) 𝔽₂)
    (U : Finset (Matrix (Fin m) (Fin n) 𝔽₂)) :
    (U.filter (fun M => M ∈ NiceF Q ι T₀)).card
      = Nat.card {M : Matrix (Fin m) (Fin n) 𝔽₂ //
          M ∈ U ∧ M - T₀ ∈ LinearMap.range (sandwich Q ι)} := by
  have h1 : ((Finset.univ : Finset (Matrix (Fin m) (Fin n) 𝔽₂)).filter
      (fun M => M ∈ U ∧ M - T₀ ∈ LinearMap.range (sandwich Q ι)))
      = U.filter (fun M => M ∈ NiceF Q ι T₀) := by
    ext M
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_NiceF]
  rw [← h1, ← Fintype.card_subtype (p := fun M : Matrix (Fin m) (Fin n) 𝔽₂ =>
    M ∈ U ∧ M - T₀ ∈ LinearMap.range (sandwich Q ι)), Nat.card_eq_fintype_card]

/-- The cell membership is transported along `grMap`. -/
lemma filter_cell_transport (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (S : Finset (GrVertex k ℓ)) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    (S.filter (fun L => A ≤ (F2.grMap e L).1 ∧ (F2.grMap e L).1 ≤ B))
      = (S.filter (fun L => Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A ≤ L.1 ∧
          L.1 ≤ Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) B)) := by
  refine Finset.filter_congr fun L _ => ?_
  rw [F2.grMap_val]
  exact ⟨fun h => ⟨(map_le_iff_comap_le e A L.1).mp h.1,
      Submodule.map_le_iff_le_comap.mp h.2⟩,
    fun h => ⟨(map_le_iff_comap_le e A L.1).mpr h.1,
      Submodule.map_le_iff_le_comap.mpr h.2⟩⟩

lemma inter_SubGr_eq_filter (S : Finset (GrVertex k ℓ)) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    S ∩ SubGr k ℓ A B = S.filter (fun L : GrVertex k ℓ => A ≤ L.1 ∧ L.1 ≤ B) := by
  ext L
  simp only [Finset.mem_inter, Finset.mem_filter, SubGr, Finset.mem_univ, true_and]

lemma card_SubGr (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    (SubGr k ℓ A B).card = Nat.card {L : GrVertex k ℓ // A ≤ L.1 ∧ L.1 ≤ B} := by
  have h : SubGr k ℓ A B
      = Finset.univ.filter (fun L : GrVertex k ℓ => A ≤ L.1 ∧ L.1 ≤ B) := by
    ext L
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SubGr]
  rw [h, ← Fintype.card_subtype (p := fun L : GrVertex k ℓ => A ≤ L.1 ∧ L.1 ≤ B),
    ← Nat.card_eq_fintype_card]

lemma finrank_comap_linearEquiv (e : (Fin k → 𝔽₂) ≃ₗ[𝔽₂] (Fin k → 𝔽₂))
    (A : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    Module.finrank 𝔽₂ (Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A)
      = Module.finrank 𝔽₂ A := by
  have h : Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A
      = A.map (e.symm : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) := by
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_map]
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [h]
  exact (LinearEquiv.finrank_eq ((e.symm).submoduleMap A)).symm

/-- **The `2ℓ ≤ k` case of the expansion statement.** -/
theorem exists_cell_density (hℓk : ℓ ≤ k) (hℓ2 : 2 ≤ ℓ) (h2 : 2 * ℓ ≤ k) (C₀ : ℝ)
    (hSSE : ∀ (m n : ℕ) (r : ℕ), 1 ≤ r → ∀ T : Finset (Matrix (Fin m) (Fin n) 𝔽₂),
      GlobalBS (r + 1) ((2 : ℝ) ^ (-(C₀ * r ^ 2))) (fun A => if A ∈ T then 1 else 0) →
        (∑ A ∈ T, ∑ B : Matrix (Fin m) (Fin n) 𝔽₂,
          if B.rank = 1 then (if A + B ∈ T then (1 : ℝ) else 0) else 0) /
        ((T.card : ℝ) * (∑ B : Matrix (Fin m) (Fin n) 𝔽₂,
          if B.rank = 1 then (1 : ℝ) else 0)) < ((2 : ℝ) ^ r)⁻¹)
    {α : ℝ} (r₀ : ℕ) (hr₀ : 1 ≤ r₀) (hr₀α : ((2 : ℝ) ^ r₀)⁻¹ ≤ 1 - α)
    (S : Finset (GrVertex k ℓ)) (hS : S.Nonempty) (hΦ : Φ (Gr k ℓ) S hS ≤ α) :
    ∃ A' B' : Submodule 𝔽₂ (Fin k → 𝔽₂), A' ≤ B' ∧
      Module.finrank 𝔽₂ A' + (k - Module.finrank 𝔽₂ B') ≤ r₀ + 1 ∧
      ((S ∩ SubGr k ℓ A' B').card : ℝ) / ((SubGr k ℓ A' B').card : ℝ)
        ≥ (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) / 4 := by
  have hℓ1 : 1 ≤ ℓ := by omega
  obtain ⟨e, hY, hX⟩ := exists_good_basis hℓk hℓ1 h2 S hS
  have hcardN : (rankOneSet ℓ (k - ℓ)).card = (2 ^ ℓ - 1) * (2 ^ (k - ℓ) - 1) := by
    have h := rankOneCount_eq_card (m := ℓ) (n := k - ℓ)
    rw [rankOneCount] at h
    exact_mod_cast h
  have hN₁pos : 0 < (rankOneSet ℓ (k - ℓ)).card := by
    rw [hcardN]
    exact Nat.mul_pos
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by norm_num)))
      (Nat.sub_pos_of_lt (Nat.one_lt_pow (by omega) (by norm_num)))
  have hYposR : (0 : ℝ) < (Ynum S e : ℝ) := by exact_mod_cast hY
  have hN₁posR : (0 : ℝ) < ((rankOneSet ℓ (k - ℓ)).card : ℝ) := by exact_mod_cast hN₁pos
  have hΦR : ((Φ (Gr k ℓ) S hS : ℚ) : ℝ) ≤ α := by exact_mod_cast hΦ
  have hratio : ((2 : ℝ) ^ r₀)⁻¹
      ≤ (∑ A ∈ Te hℓk e S, ∑ B : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂,
          if B.rank = 1 then (if A + B ∈ Te hℓk e S then (1 : ℝ) else 0) else 0) /
        ((Te hℓk e S).card *
          (∑ B : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂, if B.rank = 1 then (1 : ℝ) else 0)) := by
    rw [← sseNum_eq_sum]
    have hden : ((Te hℓk e S).card : ℝ) *
        (∑ B : Matrix (Fin ℓ) (Fin (k - ℓ)) 𝔽₂, if B.rank = 1 then (1 : ℝ) else 0)
        = (Ynum S e : ℝ) * ((rankOneSet ℓ (k - ℓ)).card : ℝ) := by
      rw [card_Te hℓk e S, ← rankOneCount_eq_sum, rankOneCount]
    rw [hden]
    rw [le_div_iff₀ (by positivity :
      (0 : ℝ) < (Ynum S e : ℝ) * ((rankOneSet ℓ (k - ℓ)).card : ℝ))]
    have hX' : (Xnum S e : ℝ) ≤ ((Φ (Gr k ℓ) S hS : ℚ) : ℝ) *
        ((rankOneSet ℓ (k - ℓ)).card : ℝ) * (Ynum S e : ℝ) := by
      simpa only [rankOneCount] using hX
    have hge := Xnum_add_sseNum_Te_ge hℓk hℓ2 e S
    have h1 : ((2 : ℝ) ^ r₀)⁻¹ ≤ 1 - ((Φ (Gr k ℓ) S hS : ℚ) : ℝ) := by linarith
    have hmain : (1 - ((Φ (Gr k ℓ) S hS : ℚ) : ℝ)) *
        ((Ynum S e : ℝ) * ((rankOneSet ℓ (k - ℓ)).card : ℝ)) ≤ sseNum (Te hℓk e S) := by
      nlinarith [hX', hge]
    have hΦY := mul_le_mul_of_nonneg_right h1 (le_of_lt (mul_pos hYposR hN₁posR))
    linarith [hΦY, hmain]
  have hnotglob : ¬ GlobalBS (r₀ + 1) ((2 : ℝ) ^ (-(C₀ * r₀ ^ 2))) (ind (Te hℓk e S)) := by
    intro hg
    have hh := hSSE ℓ (k - ℓ) r₀ hr₀ (Te hℓk e S) hg
    exact absurd hh (not_lt.mpr hratio)
  obtain ⟨m', n', Q, ι, T₀, hord, hl2⟩ := exists_of_not_globalBS hnotglob
  obtain ⟨A, B, hdim, hAB₀⟩ := exists_subGr_of_nice hℓk Q ι T₀
  have hAB : ∀ L : VGood k ℓ, phiFin hℓk L ∈ NiceF Q ι T₀ ↔ (A ≤ L.carrier ∧ L.carrier ≤ B) :=
    fun L => phiFin_mem_NiceF_iff_cell hℓk Q ι T₀ A B hAB₀ L
  set NA : ℕ := Nat.card {A₀ : Matrix (Fin m') (Fin n') 𝔽₂ //
      sandwich Q ι A₀ + T₀ ∈ Te hℓk e S} with hNA
  have hNAeq : Nat.card {A₀ : Matrix (Fin m') (Fin n') 𝔽₂ //
      ι * A₀ * Q + T₀ ∈ Te hℓk e S} = NA := by
    rw [hNA]
    rfl
  set NR : ℕ := Nat.card ↥(LinearMap.range (sandwich Q ι)) with hNR
  set NT : ℕ := ((Te hℓk e S).filter (fun M => M ∈ NiceF Q ι T₀)).card with hNT
  have hkey' : NA * NR = NT * 2 ^ (m' * n') := by
    rw [hNA, hNR, Commons.LinearAlgebra.LinearMap.card_preimage_add_mul_card_range,
      ← card_filter_NiceF Q ι T₀ (Te hℓk e S), hNT, natCard_matrix]
  have hNRpos : 0 < NR := by
    rw [hNR]
    exact Nat.card_pos_iff.mpr ⟨⟨0, Submodule.zero_mem _⟩, inferInstance⟩
  have hNRposR : (0 : ℝ) < (NR : ℝ) := by exact_mod_cast hNRpos
  have hcast : (NA : ℝ) * (NR : ℝ) = (NT : ℝ) * (2 : ℝ) ^ (m' * n') := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hkey'
    push_cast at h
    simpa using h
  rw [l2sq_restr_shift_ind Q ι T₀ (Te hℓk e S), hNAeq] at hl2
  have hl2' : (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) < (NT : ℝ) / (NR : ℝ) := by
    have hsimpl : ((2 : ℝ) ^ (m' * n'))⁻¹ * (NA : ℝ) = (NT : ℝ) / (NR : ℝ) := by
      have h2e : (2 : ℝ) ^ (m' * n') ≠ 0 := by positivity
      have hne : (NR : ℝ) ≠ 0 := ne_of_gt hNRposR
      field_simp
      linarith [hcast]
    rwa [hsimpl] at hl2
  have hNTge : (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) * (NR : ℝ) ≤ (NT : ℝ) := by
    have hh := (lt_div_iff₀ hNRposR).mp hl2'
    linarith
  have hNTpos : 0 < NT := by
    have hposExp : (0 : ℝ) < (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) := by positivity
    have hpos : (0 : ℝ) < (NT : ℝ) := by
      have := mul_pos hposExp hNRposR
      linarith
    exact_mod_cast hpos
  set A' : Submodule 𝔽₂ (Fin k → 𝔽₂) :=
    Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) A with hA'
  set B' : Submodule 𝔽₂ (Fin k → 𝔽₂) :=
    Submodule.comap (e : (Fin k → 𝔽₂) →ₗ[𝔽₂] (Fin k → 𝔽₂)) B with hB'
  have hcell_eq : NT = ((Sgood e S).filter (fun L => A' ≤ L.1 ∧ L.1 ≤ B')).card := by
    rw [hNT, card_Te_inter_NiceF hℓk Q ι T₀ A B hAB e S, hA', hB']
    exact congrArg Finset.card (filter_cell_transport e (Sgood e S) A B)
  have hne : ∃ L : GrVertex k ℓ, IsGood (F2.grMap e L) ∧ A' ≤ L.1 ∧ L.1 ≤ B' := by
    have hp : 0 < ((Sgood e S).filter (fun L => A' ≤ L.1 ∧ L.1 ≤ B')).card := by
      rwa [← hcell_eq]
    obtain ⟨L, hL⟩ := Finset.card_pos.mp hp
    rw [Finset.mem_filter] at hL
    exact ⟨L, ⟨(mem_Sgood.mp hL.1).2, hL.2.1, hL.2.2⟩⟩
  have hAB' : A' ≤ B' := by
    obtain ⟨L, -, hA, hB⟩ := hne
    exact le_trans hA hB
  have hNRcell : (NR : ℝ) = (Nat.card {L : GrVertex k ℓ //
      IsGood (F2.grMap e L) ∧ A' ≤ L.1 ∧ L.1 ≤ B'} : ℝ) := by
    have h1 : NR = (NiceF Q ι T₀).card := hNR.trans (card_NiceF Q ι T₀).symm
    rw [h1, card_NiceF_eq_grCell hℓk Q ι T₀ A B hAB e, hA', hB']
  have hquarter := card_good_cell_ge_quarter hℓk e A' B' hne
  have hSge : NT ≤ (S ∩ SubGr k ℓ A' B').card := by
    rw [hcell_eq, inter_SubGr_eq_filter]
    exact Finset.card_le_card (Finset.filter_subset_filter
      (p := fun L : GrVertex k ℓ => A' ≤ L.1 ∧ L.1 ≤ B')
      (fun L hL => (mem_Sgood.mp hL).1))
  refine ⟨A', B', hAB', ?_, ?_⟩
  · rw [finrank_comap_linearEquiv e A, finrank_comap_linearEquiv e B]
    exact le_trans hdim hord
  · have hlam : (0 : ℝ) < (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) := by positivity
    rw [hNRcell] at hNTge
    have hquarterR : (4 : ℝ) * (NR : ℝ) ≥ ((SubGr k ℓ A' B').card : ℝ) := by
      have hq : (4 : ℝ) * (Nat.card {L : GrVertex k ℓ //
          IsGood (F2.grMap e L) ∧ A' ≤ L.1 ∧ L.1 ≤ B'} : ℝ)
          ≥ (Nat.card {L : GrVertex k ℓ // A' ≤ L.1 ∧ L.1 ≤ B'} : ℝ) := by
        exact_mod_cast hquarter
      rw [← card_SubGr A' B'] at hq
      rw [hNRcell]
      exact hq
    have hfinal : (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) / 4 * ((SubGr k ℓ A' B').card : ℝ)
        ≤ (NT : ℝ) := by
      have hh1 : ((SubGr k ℓ A' B').card : ℝ) ≤ 4 * (NR : ℝ) := by linarith [hquarterR]
      calc (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) / 4 * ((SubGr k ℓ A' B').card : ℝ)
          ≤ (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) / 4 * (4 * (NR : ℝ)) :=
            mul_le_mul_of_nonneg_left hh1 (by positivity)
        _ = (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) * (NR : ℝ) := by ring
        _ ≤ (NT : ℝ) := by rw [hNRcell]; exact hNTge
    have hle : (2 : ℝ) ^ (-(C₀ * r₀ ^ 2)) / 4 * ((SubGr k ℓ A' B').card : ℝ)
        ≤ ((S ∩ SubGr k ℓ A' B').card : ℝ) :=
      le_trans hfinal (by exact_mod_cast hSge)
    obtain ⟨L₀, -, hA₀, hB₀⟩ := hne
    have hcellpos : (0 : ℝ) < ((SubGr k ℓ A' B').card : ℝ) := by
      have hpos : 0 < (SubGr k ℓ A' B').card := by
        rw [card_SubGr A' B']
        exact Nat.card_pos_iff.mpr ⟨⟨L₀, hA₀, hB₀⟩, inferInstance⟩
      exact_mod_cast hpos
    exact (le_div_iff₀ hcellpos).mpr hle


/-- **The BKS reduction**: the Inverse Shortcode Hypothesis implies the Grassmann expansion
statement. -/
theorem main_exp (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    ∃ ε > 0, ∃ r, ∀ᶠ (ℓ : ℕ) (k : ℕ) in atTop, 2 * ℓ ≤ k → F2.ExpStmt α ε r k ℓ := by
  obtain ⟨C₀, _hC₀pos, hSSE⟩ := HypSSE_of_HypHyperUC HypHyperUC_of_step
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < 1 - α by linarith [hα.2])
    (by norm_num : (1 : ℝ) / 2 < 1)
  refine ⟨(2 : ℝ) ^ (-(C₀ * (max n 1) ^ 2)) / 4, by positivity, max n 1 + 1, ?_⟩
  refine Filter.eventually_atTop.mpr ⟨2, fun ℓ hℓ => ?_⟩
  refine Filter.eventually_atTop.mpr ⟨2 * ℓ, fun k _ h2 => ?_⟩
  have hr₀ : 1 ≤ max n 1 := le_max_right _ _
  have hr₀α : ((2 : ℝ) ^ max n 1)⁻¹ ≤ 1 - α := by
    have hk : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ max n 1 :=
      pow_le_pow_right₀ (by norm_num) (le_max_left n 1)
    have h1 : ((2 : ℝ) ^ max n 1)⁻¹ ≤ ((2 : ℝ) ^ n)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).mpr hk
    have h2 : ((2 : ℝ) ^ n)⁻¹ = (1 / 2 : ℝ) ^ n := by
      rw [one_div, inv_pow]
    rw [h2] at h1
    linarith [h1, hn.le]
  intro S hS hcard hΦ
  exact exists_cell_density (by omega) hℓ h2 C₀ hSSE (max n 1) hr₀ hr₀α S hS hΦ


end

end Submission.Grassmann
