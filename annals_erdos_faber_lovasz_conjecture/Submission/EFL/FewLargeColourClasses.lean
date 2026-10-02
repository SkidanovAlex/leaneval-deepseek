import Submission.EFL.Counting
import Submission.EFL.Matching
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Few large colour classes (Proposition `few-large-colour-classes` of §7)

The first layer of the proof of the large-edge theorem.  We formalise the
elementary counting behind Proposition `few-large-colour-classes` of §7 of
the paper:

> Let `α > 0` and let `𝓗` be an `n`-vertex linear hypergraph whose edges all
> have size at least `r+1`.  If `M₁,…,M_t` are pairwise edge-disjoint
> matchings of `𝓗` each covering at least `αn` vertices, then
> `t ≤ n/(αr)`.

The proof is the double counting through *volume*: for a family `s` of edges
whose sizes are at least `r+1` and whose sizes sum to at least `αn`
(which is automatic when the family is a matching covering at least `αn`
vertices), the volume `(∑_e |e|(|e|−1)) / (n(n−1))` is at least
`αr/(n−1) ≥ αr/n`; the volumes of pairwise edge-disjoint matchings add, and
the volume of any subfamily of a linear hypergraph is at most `1`.

Families of edges are represented here as `Finset (Set (Fin n))` (a finite
set of vertex sets); `sumEdgeSizes`, `familyNatVolume` and `familyVolume`
are the three quantities used in the estimate.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The sum of the sizes of the edges of a finite family `s`. -/
def sumEdgeSizes (s : Finset (Set (Fin n))) : ℕ :=
  s.sum fun e : Set (Fin n) => edgeSize e

/-- `∑_{e ∈ s} |e|·(|e|−1)` for a finite family `s` of edges (the numerator
of the volume). -/
def familyNatVolume (s : Finset (Set (Fin n))) : ℕ :=
  s.sum fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)

/-- The volume of a finite family `s` of edges on `Fin n`:
`(∑_e |e|(|e|−1)) / (n(n−1))`. -/
def familyVolume (n : ℕ) (s : Finset (Set (Fin n))) : ℝ :=
  (((familyNatVolume s : ℕ) : ℝ)) / (((n : ℝ) * ((n - 1 : ℕ) : ℝ)))

/-- A finite family is a *matching* if its edges are pairwise vertex-disjoint. -/
def IsMatchingFamily (s : Finset (Set (Fin n))) : Prop :=
  ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ s → e₂ ∈ s → e₁ ≠ e₂ → Disjoint e₁ e₂

/-- A finite family lies inside the hypergraph `𝓗`. -/
def FamilyInHypergraph (𝓗 : Hypergraph (Fin n)) (s : Finset (Set (Fin n))) : Prop :=
  ∀ ⦃e : Set (Fin n)⦄, e ∈ s → e ∈ 𝓗

/-- The vertices covered by a finite family of edges. -/
def FamilyVertices (s : Finset (Set (Fin n))) : Set (Fin n) :=
  {v : Fin n | ∃ e : Set (Fin n), e ∈ s ∧ v ∈ e}

/-- The number of vertices covered by a finite family of edges. -/
def FamilyVertexCount (s : Finset (Set (Fin n))) : ℕ :=
  (FamilyVertices s).ncard

/-- The number of distinct vertices covered by a family is at most the sum of
the sizes of its edges. -/
theorem FamilyVertexCount_le_sumEdgeSizes (s : Finset (Set (Fin n))) :
    FamilyVertexCount s ≤ sumEdgeSizes s := by
  classical
  let U : Finset (Fin n) := s.biUnion fun e : Set (Fin n) => verts e
  have hsub : FamilyVertices s ⊆ (U : Set (Fin n)) := by
    intro v hv
    rcases hv with ⟨e, he, hv⟩
    exact Finset.mem_biUnion.mpr ⟨e, he, (mem_verts e v).2 hv⟩
  have hle : FamilyVertexCount s ≤ U.card := by
    dsimp [FamilyVertexCount]
    have h1 : (FamilyVertices s).ncard ≤ (U : Set (Fin n)).ncard := Set.ncard_le_ncard hsub
    simpa using h1
  calc
    FamilyVertexCount s ≤ U.card := hle
    _ ≤ (s.sum fun e : Set (Fin n) => (verts e).card) := Finset.card_biUnion_le
    _ = sumEdgeSizes s := by
      simp [sumEdgeSizes, edgeSize]

/-- If every edge of the family has size at least `r+1`, then
`r · (sum of the sizes) ≤ ∑ |e|(|e|−1)`. -/
theorem familyNatVolume_ge_mul_sum {r : ℕ} (s : Finset (Set (Fin n)))
    (hsizes : ∀ e : Set (Fin n), e ∈ s → r + 1 ≤ edgeSize e) :
    r * sumEdgeSizes s ≤ familyNatVolume s := by
  classical
  have hper : ∀ e : Set (Fin n), e ∈ s → r * edgeSize e ≤ edgeSize e * (edgeSize e - 1) := by
    intro e he
    have hsz : r + 1 ≤ edgeSize e := hsizes e he
    have hge : r ≤ edgeSize e - 1 := by omega
    have hmul : edgeSize e * r ≤ edgeSize e * (edgeSize e - 1) :=
      Nat.mul_le_mul_left (edgeSize e) hge
    -- r * edgeSize e = edgeSize e * r
    rw [Nat.mul_comm r]
    exact hmul
  have hsum : s.sum (fun e : Set (Fin n) => r * edgeSize e) ≤ familyNatVolume s := by
    unfold familyNatVolume
    exact Finset.sum_le_sum hper
  calc
    r * sumEdgeSizes s = s.sum (fun e : Set (Fin n) => r * edgeSize e) := by
      unfold sumEdgeSizes
      rw [Finset.mul_sum]
    _ ≤ familyNatVolume s := hsum

/-- For a linear hypergraph, the volume of any finite family of edges is at
most `1`. -/
theorem familyVolume_le_one {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (s : Finset (Set (Fin n))) (hs : FamilyInHypergraph 𝓗 s) (hn : 2 ≤ n) :
    familyVolume n s ≤ 1 := by
  classical
  have hsub : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ s → e₂ ∈ s → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton := by
    intro e₁ e₂ he₁ he₂ hne
    exact hlin (hs he₁) (hs he₂) hne
  have hnat : familyNatVolume s ≤ n * (n - 1) := by
    simpa [familyNatVolume] using sum_edgeSize_mul_sub_le_on s hsub
  have hdenpos : 0 < ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
    have hn1 : 1 ≤ (n - 1 : ℕ) := by omega
    positivity
  unfold familyVolume
  rw [div_le_one₀ hdenpos]
  exact_mod_cast hnat

/-- For any finite family of sets whose pairwise intersections are
subsingleton, `∑_e |e|(|e|−1) ≤ n(n−1)`. -/
lemma familyNatVolume_le_n_mul_sub {n : ℕ} {s : Finset (Set (Fin n))}
    (hlin : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ s → e₂ ∈ s → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton) :
    familyNatVolume s ≤ n * (n - 1) := by
  simpa [familyNatVolume] using sum_edgeSize_mul_sub_le_on s hlin

/-- `familyNatVolume` is additive over disjoint unions. -/
lemma familyNatVolume_disjiUnion {t : ℕ} {M : Fin t → Finset (Set (Fin n))}
    (hpd : ((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint M) :
    familyNatVolume ((Finset.univ : Finset (Fin t)).disjiUnion M hpd) =
      (Finset.univ : Finset (Fin t)).sum (fun i : Fin t => familyNatVolume (M i)) := by
  classical
  unfold familyNatVolume
  simpa using (Finset.sum_disjiUnion (s := (Finset.univ : Finset (Fin t))) M hpd
    (f := fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)))

/-- *Few large colour classes* (bound part): if `M₁,…,M_t` are pairwise
edge-disjoint families of edges (e.g. matchings) on `Fin n`, all edges of
size at least `r+1`, whose edge-size sums are at least `αn`, then
`t·αr ≤ n−1` (in particular `t ≤ n/(αr)`).  This is the counting behind
Proposition `few-large-colour-classes`(i) of the paper. -/
theorem fewLargeColourClasses_bound {n t r : ℕ} {α : ℝ} (h2n : 2 ≤ n)
    {M : Fin t → Finset (Set (Fin n))}
    (hlinfam : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, (∃ i : Fin t, e₁ ∈ M i) →
      (∃ i : Fin t, e₂ ∈ M i) → e₁ ≠ e₂ → (e₁ ∩ e₂ : Set (Fin n)).Subsingleton)
    (hsizes : ∀ (i : Fin t) (e : Set (Fin n)), e ∈ M i → r + 1 ≤ edgeSize e)
    (hcover : ∀ i : Fin t, (α : ℝ) * (n : ℝ) ≤ (sumEdgeSizes (M i) : ℝ))
    (hdisj : ∀ (i j : Fin t), i ≠ j → Disjoint (M i) (M j)) :
    (t : ℝ) * (α * (r : ℝ)) ≤ ((n - 1 : ℕ) : ℝ) := by
  classical
  let hpd : ((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint M := by
    intro i _he₁ j _he₂ hij
    exact hdisj i j hij
  let U : Finset (Set (Fin n)) := (Finset.univ : Finset (Fin t)).disjiUnion M hpd
  -- the union U inherits the subsingleton-intersection property
  have hlinU : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, e₁ ∈ U → e₂ ∈ U → e₁ ≠ e₂ →
      (e₁ ∩ e₂ : Set (Fin n)).Subsingleton := by
    intro e₁ e₂ he₁ he₂ hne
    rw [Finset.mem_disjiUnion] at he₁ he₂
    rcases he₁ with ⟨i, _hi, hi⟩
    rcases he₂ with ⟨j, _hj, hj⟩
    exact hlinfam ⟨i, hi⟩ ⟨j, hj⟩ hne
  -- 1. per-family real lower bound: α·r·n ≤ familyNatVolume (M i)
  have hlow : ∀ i : Fin t, (α : ℝ) * (r : ℝ) * (n : ℝ) ≤ (familyNatVolume (M i) : ℝ) := by
    intro i
    have hnat_i := familyNatVolume_ge_mul_sum (s := M i) (r := r) (by
      intro e he
      exact hsizes i e he)
    have hcast : (r : ℝ) * (sumEdgeSizes (M i) : ℝ) ≤ (familyNatVolume (M i) : ℝ) := by
      exact_mod_cast hnat_i
    have hmul : (r : ℝ) * ((α : ℝ) * (n : ℝ)) ≤ (r : ℝ) * (sumEdgeSizes (M i) : ℝ) :=
      mul_le_mul_of_nonneg_left (hcover i) (by positivity)
    calc
      (α : ℝ) * (r : ℝ) * (n : ℝ) = (r : ℝ) * ((α : ℝ) * (n : ℝ)) := by ring
      _ ≤ (r : ℝ) * (sumEdgeSizes (M i) : ℝ) := hmul
      _ ≤ (familyNatVolume (M i) : ℝ) := hcast
  -- 2. the total of the per-family volumes is at most n(n-1)
  have hnatU : familyNatVolume U ≤ n * (n - 1) := familyNatVolume_le_n_mul_sub hlinU
  have hsumEq : (Finset.univ : Finset (Fin t)).sum
      (fun i : Fin t => (familyNatVolume (M i) : ℝ)) ≤ (n * (n - 1) : ℕ) := by
    have hcast2 : ((familyNatVolume U : ℕ) : ℝ) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
      exact_mod_cast hnatU
    have hsumNat : familyNatVolume U =
        (Finset.univ : Finset (Fin t)).sum (fun i : Fin t => familyNatVolume (M i)) :=
      familyNatVolume_disjiUnion (M := M) hpd
    rw [hsumNat] at hcast2
    simpa using hcast2
  -- 3. summing the per-family lower bounds
  have hsumLow : (Finset.univ : Finset (Fin t)).sum
      (fun _ : Fin t => (α : ℝ) * (r : ℝ) * (n : ℝ)) ≤
      (Finset.univ : Finset (Fin t)).sum
      (fun i : Fin t => (familyNatVolume (M i) : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    exact hlow i
  have hconst : (Finset.univ : Finset (Fin t)).sum
      (fun _ : Fin t => (α : ℝ) * (r : ℝ) * (n : ℝ)) =
      (t : ℝ) * ((α : ℝ) * (r : ℝ) * (n : ℝ)) := by
    rw [Finset.sum_const]
    simp
  have htotal : (t : ℝ) * ((α : ℝ) * (r : ℝ) * (n : ℝ)) ≤ ((n * (n - 1) : ℕ) : ℝ) := by
    calc
      (t : ℝ) * ((α : ℝ) * (r : ℝ) * (n : ℝ)) = (Finset.univ : Finset (Fin t)).sum
          (fun _ : Fin t => (α : ℝ) * (r : ℝ) * (n : ℝ)) := hconst.symm
      _ ≤ (Finset.univ : Finset (Fin t)).sum
          (fun i : Fin t => (familyNatVolume (M i) : ℝ)) := hsumLow
      _ ≤ ((n * (n - 1) : ℕ) : ℝ) := hsumEq
  -- 4. divide by n (which is ≥ 2 > 0)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have htotal' : (t : ℝ) * ((α : ℝ) * (r : ℝ) * (n : ℝ)) ≤
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
    simpa [Nat.cast_mul] using htotal
  have hmul2 : (t : ℝ) * (α * (r : ℝ)) * (n : ℝ) ≤ ((n - 1 : ℕ) : ℝ) * (n : ℝ) := by
    nlinarith [htotal']
  exact (mul_le_mul_iff_of_pos_right hnpos).1 hmul2

/-- *Few large colour classes* in the paper's form: with the hypotheses of
`fewLargeColourClasses_bound` and `α > 0`, `r ≥ 1`, the number `t` of
pairwise edge-disjoint matchings satisfies `t ≤ n / (αr)`. -/
theorem fewLargeColourClasses_le {n t r : ℕ} {α : ℝ} (h2n : 2 ≤ n) (hα : 0 < α) (hr : 1 ≤ r)
    {M : Fin t → Finset (Set (Fin n))}
    (hlinfam : ∀ ⦃e₁ e₂ : Set (Fin n)⦄, (∃ i : Fin t, e₁ ∈ M i) →
      (∃ i : Fin t, e₂ ∈ M i) → e₁ ≠ e₂ → (e₁ ∩ e₂ : Set (Fin n)).Subsingleton)
    (hsizes : ∀ (i : Fin t) (e : Set (Fin n)), e ∈ M i → r + 1 ≤ edgeSize e)
    (hcover : ∀ i : Fin t, (α : ℝ) * (n : ℝ) ≤ (sumEdgeSizes (M i) : ℝ))
    (hdisj : ∀ (i j : Fin t), i ≠ j → Disjoint (M i) (M j)) :
    (t : ℝ) ≤ (n : ℝ) / (α * (r : ℝ)) := by
  classical
  have hb := fewLargeColourClasses_bound (h2n := h2n) hlinfam hsizes hcover hdisj
  have hden : 0 < α * (r : ℝ) := by
    positivity
  have hb' : (t : ℝ) * (α * (r : ℝ)) ≤ (n : ℝ) := by
    have hle1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (by omega : n - 1 ≤ n)
    exact hb.trans hle1
  exact (le_div_iff₀ hden).2 hb'
