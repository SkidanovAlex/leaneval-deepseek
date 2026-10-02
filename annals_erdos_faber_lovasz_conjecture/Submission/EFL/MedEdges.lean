import Submission.EFL.DeepInputs
import Submission.EFL.Basic
import Submission.EFL.Counting
import Submission.EFL.FewLargeColourClasses
import Submission.EFL.AlphaBoundedColouring
import Submission.EFL.LargeEdge

/-!
# The maximum degree of a linear hypergraph, and the medium edges

The paper's Proposition 6.10 (`prop:med-edges`) colours the edges of
*prescribed size* (`r₁ ≤ |e| ≤ r₀`) with `γn` colours, each colour class
covering at most `γn` vertices.  Its proof rests on the observation that in a
linear hypergraph all of whose edges have size at least `r`, the maximum
degree satisfies `Δ(𝓗) ≤ n/(r−1)`: the sets `e ∖ {v}` for the edges `e`
through a fixed vertex `v` are pairwise disjoint subsets of `Fin n ∖ {v}`.

This module proves that degree bound (`degree_mul_le`, `degree_le_div`,
`maxDegree_le_div`) and then Proposition 6.10 from

* Kahn's theorem (`KahnStatement`) for `χ'(𝓗) ≤ 2n/r₁`, and
* Proposition 6.8(ii) (`alpha_bounded_recolour`) for the `γ`-bounded
  recolouring at the cost of `O(n/(γ²r₁))` colours.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The vertices of the edge `e` other than `v`. -/
def otherVerts {n : ℕ} (e : Set (Fin n)) (v : Fin n) : Finset (Fin n) :=
  (verts e).erase v

lemma otherVerts_subset_erase {n : ℕ} (e : Set (Fin n)) (v : Fin n) :
    otherVerts e v ⊆ (Finset.univ : Finset (Fin n)).erase v := by
  intro w hw
  exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_univ w⟩

lemma otherVerts_card {n : ℕ} {e : Set (Fin n)} {v : Fin n} (hv : v ∈ e) :
    (otherVerts e v).card = edgeSize e - 1 := by
  simp only [otherVerts, edgeSize]
  exact Finset.card_erase_of_mem (by simpa [mem_verts] using hv)

/-- **The paper's `Δ(𝓗) ≤ n/(r−1)`**: in a linear hypergraph all of whose
edges have size at least `r`, the edges through a fixed vertex `v` have
pairwise disjoint "other vertex" sets, whence
`d_𝓗(v)·(r−1) ≤ n−1`. -/
theorem degree_mul_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) {r : ℕ}
    (hsize : ∀ e ∈ 𝓗, r ≤ edgeSize e) (v : Fin n) :
    hypergraphDegree 𝓗 v * (r - 1) ≤ n - 1 := by
  classical
  haveI : Fintype 𝓗 := Fintype.ofFinite 𝓗
  let S := {e : 𝓗 // v ∈ (e : Set (Fin n))}
  letI : Fintype S := Fintype.ofFinite S
  let f : S → Finset (Fin n) := fun e => otherVerts (e.1 : Set (Fin n)) v
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset S)) f := by
    intro e _ e' _ hne
    change Disjoint (f e) (f e')
    rw [Finset.disjoint_left]
    intro w hw hw'
    have hw1 : w ≠ v ∧ w ∈ verts (e.1 : Set (Fin n)) := by
      simpa only [f, otherVerts] using (Finset.mem_erase.mp hw)
    have hw2 : w ≠ v ∧ w ∈ verts (e'.1 : Set (Fin n)) := by
      simpa only [f, otherVerts] using (Finset.mem_erase.mp hw')
    have hsub : ((e.1 : Set (Fin n)) ∩ (e'.1 : Set (Fin n))).Subsingleton := by
      refine hlin e.1.2 e'.1.2 ?_
      intro hEq
      exact hne (Subtype.ext (Subtype.ext hEq))
    have h1 : v ∈ ((e.1 : Set (Fin n)) ∩ (e'.1 : Set (Fin n))) := ⟨e.2, e'.2⟩
    have h2 : w ∈ ((e.1 : Set (Fin n)) ∩ (e'.1 : Set (Fin n))) :=
      ⟨by simpa [mem_verts] using hw1.2, by simpa [mem_verts] using hw2.2⟩
    exact hw1.1 (hsub h1 h2).symm
  have hcard_le : ∀ e : S, r - 1 ≤ (f e).card := by
    intro e
    have h1 : (f e).card = edgeSize (e.1 : Set (Fin n)) - 1 := by
      simpa only [f] using otherVerts_card e.2
    have h2 : r ≤ edgeSize (e.1 : Set (Fin n)) := hsize _ e.1.2
    omega
  have hsum : Fintype.card S * (r - 1) ≤ ∑ e : S, (f e).card := by
    have h := Finset.card_nsmul_le_sum (Finset.univ : Finset S) (fun e : S => (f e).card)
      (r - 1) (fun x _ => hcard_le x)
    simpa [nsmul_eq_mul] using h
  have hbUnion : ((Finset.univ : Finset S).biUnion f).card = ∑ e : S, (f e).card := by
    rw [Finset.card_biUnion hdisj]
  have hsub_erase : (Finset.univ.biUnion f) ⊆ (Finset.univ : Finset (Fin n)).erase v := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨e, _, hwe⟩
    exact otherVerts_subset_erase _ v hwe
  have hcardfin : (Finset.univ.biUnion f).card ≤ n - 1 := by
    have h := Finset.card_le_card hsub_erase
    simpa using h
  have hfin : Fintype.card S * (r - 1) ≤ n - 1 := by
    calc Fintype.card S * (r - 1) ≤ ∑ e : S, (f e).card := hsum
      _ = (Finset.univ.biUnion f).card := hbUnion.symm
      _ ≤ n - 1 := hcardfin
  have hdeg : hypergraphDegree 𝓗 v = Fintype.card S := by
    rw [hypergraphDegree, Nat.card_eq_fintype_card]
  rw [hdeg]
  exact hfin

/-- `d_𝓗(v) ≤ n/(r−1)` in the reals. -/
theorem degree_le_div {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) {r : ℕ} (hr : 2 ≤ r)
    (hsize : ∀ e ∈ 𝓗, r ≤ edgeSize e) (v : Fin n) :
    (hypergraphDegree 𝓗 v : ℝ) ≤ (n : ℝ) / ((r : ℝ) - 1) := by
  have h := degree_mul_le hlin hsize v
  have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have h1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n - 1 ≤ n)
  have hmul : ((hypergraphDegree 𝓗 v : ℕ) : ℝ) * ((r : ℝ) - 1) ≤ (n : ℝ) := by
    have h' : ((hypergraphDegree 𝓗 v * (r - 1) : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) :=
      by exact_mod_cast h
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at h'
    linarith [h', h1]
  rw [le_div_iff₀ hr1]
  linarith [hmul]

/-- `Δ(𝓗) ≤ n/(r−1)` in the reals. -/
theorem maxDegree_le_div {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) {r : ℕ} (hr : 2 ≤ r)
    (hsize : ∀ e ∈ 𝓗, r ≤ edgeSize e) :
    (hypergraphMaxDegree 𝓗 : ℝ) ≤ (n : ℝ) / ((r : ℝ) - 1) := by
  have hr1 : 0 < r - 1 := by omega
  have hsup : hypergraphMaxDegree 𝓗 ≤ n / (r - 1) := by
    rw [hypergraphMaxDegree]
    refine Finset.sup_le (fun v _ => ?_)
    rw [Nat.le_div_iff_mul_le hr1]
    exact le_trans (degree_mul_le hlin hsize v) (Nat.sub_le n 1)
  calc (hypergraphMaxDegree 𝓗 : ℝ) ≤ ((n / (r - 1) : ℕ) : ℝ) := by exact_mod_cast hsup
    _ ≤ (n : ℝ) / ((r - 1 : ℕ) : ℝ) := Nat.cast_div_le
    _ = (n : ℝ) / ((r : ℝ) - 1) := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]

/-- `α`-boundedness is preserved by casting a colouring into a larger colour
type along an injection: the classes are only relabelled, and the colours
outside the image get empty classes. -/
lemma AlphaBounded_ofLeColors {m : ℕ} {hmn : m ≤ n} {𝓗 : Hypergraph (Fin n)} {γ : ℝ}
    {ψ : 𝓗.Coloring (Fin m)} (h : ψ.AlphaBounded γ) :
    (ψ.ofLeColors hmn).AlphaBounded γ := by
  classical
  intro c
  by_cases hc : ∃ c' : Fin m, Fin.castLE hmn c' = c
  · obtain ⟨c', rfl⟩ := hc
    have hcl : (ψ.ofLeColors hmn).colorClass (Fin.castLE hmn c') = ψ.colorClass c' := by
      ext e
      simp only [mem_colorClass, Hypergraph.Coloring.ofLeColors]
      constructor
      · intro hh
        exact Fin.castLE_injective hmn hh
      · intro hh
        rw [hh]
    rw [hcl]
    exact h c'
  · left
    have hempty : (ψ.ofLeColors hmn).colorClass c = ∅ := by
      ext e
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro hh
      exact hc ⟨ψ.labels e, hh⟩
    rw [hempty]
    simp

/-- **Proposition 6.10** (`prop:med-edges`), conditional on the
chromatic-index bound `χ'(𝓗) ≤ 4n/r₁ + 1` that Kahn's theorem supplies for
size-bounded linear hypergraphs: a linear hypergraph with all edges of size
at least `r₁` has a `γ`-bounded proper edge-colouring using at most `γn`
colours. -/
theorem medEdges_colouring_of_chi {n r₁ : ℕ} {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2)
    (h2n : 2 ≤ n) (hr₁ : 2 ≤ r₁)
    (hr₁big : 32 / γ ^ 3 + 8 / γ ^ 2 + 8 / γ ≤ (r₁ : ℝ))
    (hγn : 2 ≤ γ * (n : ℝ))
    {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hsize₁ : ∀ e ∈ 𝓗, r₁ ≤ edgeSize e)
    (hχ : ∃ c : ℕ, (c : ℝ) ≤ 4 * (n : ℝ) / (r₁ : ℝ) + 1 ∧ 𝓗.Colorable c) :
    ∃ (C : Finset (Fin n)) (φ : 𝓗.Coloring (Fin n)),
      φ.UsesColourSet C ∧ (C.card : ℝ) ≤ γ * (n : ℝ) ∧ φ.AlphaBounded γ := by
  classical
  obtain ⟨c, hc, ⟨φ'⟩⟩ := hχ
  have hr₁pos : (0 : ℝ) < (r₁ : ℝ) := by positivity
  have h4g : 4 / γ ≤ (r₁ : ℝ) := by
    have h2 : (0 : ℝ) ≤ 32 / γ ^ 3 + 8 / γ ^ 2 := by positivity
    have h3 : 8 / γ ≤ 32 / γ ^ 3 + 8 / γ ^ 2 + 8 / γ := by linarith
    have h6 : 4 / γ ≤ 8 / γ := by
      rw [div_le_div_iff₀ hγ0 hγ0]; linarith
    linarith [hr₁big, h2, h3, h6]
  have hgn : (0 : ℝ) < γ * (n : ℝ) := by linarith
  -- the number of colours of `χ'` is at most `n`
  have hcn : c ≤ n := by
    have h1 : (c : ℝ) ≤ γ * (n : ℝ) + 1 := by
      calc (c : ℝ) ≤ 4 * (n : ℝ) / (r₁ : ℝ) + 1 := hc
        _ ≤ 4 * (n : ℝ) / (4 / γ) + 1 := by
            have h := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ))
              (by positivity : (0 : ℝ) < 4 / γ) h4g
            linarith [h]
        _ = γ * (n : ℝ) + 1 := by field_simp
    have h2 : (1 : ℝ) ≤ γ * (n : ℝ) / 2 := by linarith
    have h3 : γ * (n : ℝ) ≤ (n : ℝ) / 2 := by nlinarith [hγ1, hgn]
    exact_mod_cast (by linarith [h1, h2, h3] : (c : ℝ) ≤ (n : ℝ))
  let C : Finset (Fin n) := (Finset.univ : Finset (Fin c)).image (Fin.castLE hcn)
  have hCcard : (C.card : ℝ) ≤ (c : ℝ) := by
    have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin c))) (f := Fin.castLE hcn)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  let φ : 𝓗.Coloring (Fin n) := φ'.ofLeColors hcn
  have hφC : φ.UsesColourSet C := by
    intro e
    exact Finset.mem_image.mpr ⟨φ'.labels e, Finset.mem_univ _, rfl⟩
  -- Proposition 6.8(ii) at `β = γ`, `r = r₁ − 1`
  obtain ⟨m, ψ, hψbdd, hψcard⟩ := alpha_bounded_recolour (r := r₁ - 1) hγ0 (by linarith) h2n
    (by omega) hlin (fun e => by have := hsize₁ _ e.2; omega) φ hφC
  have hr1m1 : ((r₁ - 1 : ℕ) : ℝ) = (r₁ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r₁), Nat.cast_one]
  have hcoef : (2 : ℝ) / (γ / 2) + 1 = 4 / γ + 1 := by
    field_simp
    ring
  rw [hcoef] at hψcard
  have hfrac : (n : ℝ) / ((γ / 2) * ((r₁ - 1 : ℕ) : ℝ)) ≤ 4 * (n : ℝ) / (γ * (r₁ : ℝ)) := by
    have hdenpos : (0 : ℝ) < (γ / 2) * ((r₁ - 1 : ℕ) : ℝ) := by
      have h1 : (0 : ℝ) < γ / 2 := by linarith
      have h2 : (0 : ℝ) < ((r₁ - 1 : ℕ) : ℝ) := by
        have h3 : 0 < r₁ - 1 := by omega
        exact_mod_cast h3
      exact mul_pos h1 h2
    rw [div_le_div_iff₀ hdenpos (by positivity : (0 : ℝ) < γ * (r₁ : ℝ))]
    have hden : γ * (r₁ : ℝ) / 4 ≤ (γ / 2) * ((r₁ - 1 : ℕ) : ℝ) := by
      rw [hr1m1]
      have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁
      nlinarith [h2, hγ0]
    nlinarith [hden, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hkey : (4 + 16 / γ ^ 2 + 4 / γ : ℝ) ≤ γ * (r₁ : ℝ) / 2 := by
    have h := mul_le_mul_of_nonneg_left hr₁big (le_of_lt hγ0)
    have hL : γ * (32 / γ ^ 3 + 8 / γ ^ 2 + 8 / γ) = 32 / γ ^ 2 + 8 / γ + 8 := by
      field_simp
    rw [hL] at h
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hX : (4 + 16 / γ ^ 2 + 4 / γ) * 2 = 32 / γ ^ 2 + 8 / γ + 8 := by ring
    rw [hX]
    exact h
  have hnum : 4 * (n : ℝ) / (r₁ : ℝ) + (4 / γ + 1) * (4 * (n : ℝ) / (γ * (r₁ : ℝ))) + 1 ≤
      γ * (n : ℝ) := by
    have hL : 4 * (n : ℝ) / (r₁ : ℝ) + (4 / γ + 1) * (4 * (n : ℝ) / (γ * (r₁ : ℝ))) =
        (4 + 16 / γ ^ 2 + 4 / γ) * ((n : ℝ) / (r₁ : ℝ)) := by
      field_simp
      ring
    rw [hL]
    have h := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ (n : ℝ) / (r₁ : ℝ))
    have h2 : γ * (r₁ : ℝ) / 2 * ((n : ℝ) / (r₁ : ℝ)) = γ * (n : ℝ) / 2 := by field_simp
    have h3 : (1 : ℝ) ≤ γ * (n : ℝ) / 2 := by linarith
    linarith [h, h2.le, h2.ge, h3]
  have hm_bound : (m : ℝ) ≤ γ * (n : ℝ) := by
    have hA : (0 : ℝ) ≤ 4 / γ + 1 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hfrac hA
    have h3 : (C.card : ℝ) ≤ 4 * (n : ℝ) / (r₁ : ℝ) + 1 := le_trans hCcard hc
    linarith [hψcard, h2, h3, hnum]
  have hmn : m ≤ n := by
    have h3 : γ * (n : ℝ) ≤ (n : ℝ) := by nlinarith [hγ1, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    exact_mod_cast (by linarith [hm_bound, h3] : (m : ℝ) ≤ (n : ℝ))
  refine ⟨(Finset.univ : Finset (Fin m)).image (Fin.castLE hmn),
    ψ.ofLeColors hmn, ?_, ?_, AlphaBounded_ofLeColors hψbdd⟩
  · intro e
    exact Finset.mem_image.mpr ⟨ψ.labels e, Finset.mem_univ _, rfl⟩
  · have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := Fin.castLE hmn)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact le_trans (by exact_mod_cast h : _ ≤ (m : ℝ)) hm_bound

/-- The chromatic-index input of Proposition 6.10 from Kahn's theorem: for a
linear `n`-vertex hypergraph all of whose edges have size in `[r₁, r]`, the
bound `Δ(𝓗) ≤ n/(r₁−1)` turns Kahn's theorem into
`χ'(𝓗) ≤ 4n/r₁ + 1`. -/
theorem colorable_of_kahn_sizes {n : ℕ} {r r₁ : ℕ} {D₀ : ℝ}
    (hKahn : ∀ D : ℝ, D₀ ≤ D → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓗, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, (1 + 1) * D ≤ (c : ℝ) → 𝓗.Colorable c)
    {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (hr₁ : 2 ≤ r₁)
    (hsize₁ : ∀ e ∈ 𝓗, r₁ ≤ edgeSize e)
    (hsize₀ : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ r)
    (hD : D₀ ≤ (n : ℝ) / ((r₁ : ℝ) - 1)) :
    ∃ c : ℕ, (c : ℝ) ≤ 4 * (n : ℝ) / (r₁ : ℝ) + 1 ∧ 𝓗.Colorable c := by
  have hr₁pos : (0 : ℝ) < (r₁ : ℝ) := by positivity
  refine ⟨⌈2 * (n : ℝ) / ((r₁ : ℝ) - 1)⌉₊, ?_, ?_⟩
  · have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁
    have hpos : (0 : ℝ) ≤ 2 * (n : ℝ) / ((r₁ : ℝ) - 1) := by
      have h3 : (0 : ℝ) < (r₁ : ℝ) - 1 := by linarith
      positivity
    have hceil : (⌈2 * (n : ℝ) / ((r₁ : ℝ) - 1)⌉₊ : ℝ) < 2 * (n : ℝ) / ((r₁ : ℝ) - 1) + 1 :=
      Nat.ceil_lt_add_one hpos
    have h3 : 2 * (n : ℝ) / ((r₁ : ℝ) - 1) ≤ 4 * (n : ℝ) / (r₁ : ℝ) := by
      rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < (r₁ : ℝ) - 1)
        (by linarith : (0 : ℝ) < (r₁ : ℝ))]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), h2]
    linarith [hceil, h3]
  · refine hKahn ((n : ℝ) / ((r₁ : ℝ) - 1)) hD n 𝓗 hlin ?_ (fun e => ?_)
      ⌈2 * (n : ℝ) / ((r₁ : ℝ) - 1)⌉₊ ?_
    · exact maxDegree_le_div hlin hr₁ hsize₁
    · exact_mod_cast hsize₀ e
    · rw [show (1 + 1 : ℝ) * ((n : ℝ) / ((r₁ : ℝ) - 1)) =
          2 * (n : ℝ) / ((r₁ : ℝ) - 1) by ring]
      exact Nat.le_ceil _

end

end ErdosFaberLovaszConjecture
