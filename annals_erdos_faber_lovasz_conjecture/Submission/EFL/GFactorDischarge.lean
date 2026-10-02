import Submission.EFL.Comm.LovaszGfFactor
import Submission.EFL.Comm.InternalMatchingConnect

/-!
# Discharging `GFactorStatement` from the ported Lovász `(g,f)`-factor theorem

`Submission/EFL/GFactor.lean` records the paper's Theorem `thm:gf_factor`
(Lovász's `(g,f)`-factor theorem) as an input statement `GFactorStatement`.
The shared commons contains a complete proof of the theorem
(`Commons.Combinatorics.LovaszGFactor.lovasz_gf_factor`, proved on top of
Tutte's `f`-factor theorem); this module ports that proof into the
`Submission` cone (modules `Submission.EFL.Comm.*`) and transports it to the
precise form `GFactorStatement`:

* the graph of `GFactorStatement` is the induced graph `graphOf G W` on the
  vertex set `W` (from `Submission/EFL/Comm/InternalMatchingConnect.lean`);
* the functions `f, g` live on `Fin n` but only their values on `W` matter, so
  they are restricted to `↥W`;
* the hypothesis and the conclusion are transported across the identification
  of finsets of `↥W` with their images in `W`.

The main result is `gfactorStatement : GFactorStatement`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## `Nat.card` versions of the degrees -/

/-- The `Nat.card` of the `graphOf`-neighbourhood of `x` is `degIn`. -/
theorem natCard_graphOf_adj (G : Hypergraph (Fin n)) (W : Set (Fin n))
    (hG2 : ∀ e ∈ G, edgeSize e = 2) (x : ↥W) :
    Nat.card {y : ↥W // (graphOf G W hG2).Adj x y} = degIn G W x.1 := by
  rw [degIn_eq_ncard]
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }

/-- Transport of finset sums along `Subtype.val`. -/
theorem sum_image_val {M : Type*} [AddCommMonoid M] {W : Set (Fin n)}
    (S : Finset ↥W) (h : Fin n → M) :
    ∑ s ∈ S, h s.1 = ∑ t ∈ S.image Subtype.val, h t := by
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact Subtype.ext hab

/-! ## The edge family of a subgraph of `graphOf G W` -/

/-- The family of 2-element subsets of `W` corresponding to the edges of a
subgraph `M` of `graphOf G W`. -/
def edgesOf (G : Hypergraph (Fin n)) (W : Set (Fin n)) (hG2 : ∀ e ∈ G, edgeSize e = 2)
    (M : (graphOf G W hG2).Subgraph) : Hypergraph (Fin n) :=
  {e | e ⊆ W ∧ ∃ p : ↥W × ↥W, M.Adj p.1 p.2 ∧ e = ({p.1.1, p.2.1} : Set (Fin n))}

/-- Membership of a pair in `edgesOf`. -/
theorem mem_edgesOf (G : Hypergraph (Fin n)) (W : Set (Fin n))
    (hG2 : ∀ e ∈ G, edgeSize e = 2) (M : (graphOf G W hG2).Subgraph) (x y : ↥W) :
    ({x.1, y.1} : Set (Fin n)) ∈ edgesOf G W hG2 M ↔ M.Adj x y := by
  constructor
  · rintro ⟨-, p, hp, heq⟩
    rcases Set.pair_eq_pair_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hx : x = p.1 := Subtype.ext h1
      have hy : y = p.2 := Subtype.ext h2
      rwa [hx, hy]
    · have hx : x = p.2 := Subtype.ext h1
      have hy : y = p.1 := Subtype.ext h2
      rw [hx, hy]
      exact M.adj_symm hp
  · intro h
    exact ⟨Set.pair_subset x.2 y.2, ⟨(x, y), h, rfl⟩⟩

/-- `edgesOf` is a subfamily of `G`. -/
theorem edgesOf_subset (G : Hypergraph (Fin n)) (W : Set (Fin n))
    (hG2 : ∀ e ∈ G, edgeSize e = 2) (M : (graphOf G W hG2).Subgraph) :
    edgesOf G W hG2 M ⊆ G := by
  rintro e ⟨-, p, hp, rfl⟩
  exact M.adj_sub hp

/-- Every edge of `edgesOf` has size two. -/
theorem edgeSize_of_mem_edgesOf (G : Hypergraph (Fin n)) (W : Set (Fin n))
    (hG2 : ∀ e ∈ G, edgeSize e = 2) (M : (graphOf G W hG2).Subgraph)
    (e : Set (Fin n)) (he : e ∈ edgesOf G W hG2 M) : edgeSize e = 2 := by
  obtain ⟨-, p, hp, rfl⟩ := he
  have hne : p.1.1 ≠ p.2.1 := by
    intro h
    have hp' : (graphOf G W hG2).Adj p.1 p.2 := M.adj_sub hp
    rw [Subtype.ext h] at hp'
    exact (graphOf G W hG2).irrefl hp'
  rw [edgeSize_eq_ncard, Set.ncard_pair hne]

/-- The degree of `x` inside `W` in `edgesOf G W hG2 M` is the number of
`M`-neighbours of `x`. -/
theorem degIn_edgesOf (G : Hypergraph (Fin n)) (W : Set (Fin n))
    (hG2 : ∀ e ∈ G, edgeSize e = 2) (M : (graphOf G W hG2).Subgraph) (x : ↥W) :
    degIn (edgesOf G W hG2 M) W x.1 = Nat.card {y : ↥W // M.Adj x y} := by
  rw [← natCard_graphOf_adj (edgesOf G W hG2 M) W
        (edgeSize_of_mem_edgesOf G W hG2 M) x]
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun y => ?_))
  exact mem_edgesOf G W hG2 M x y

/-! ## The main statement -/

/-- **Lovász's `(g,f)`-factor theorem** in the form `GFactorStatement`. -/
theorem gfactorStatement : GFactorStatement := by
  intro n G W f g hG2 hg0 hgf hfd hlov
  haveI : Fintype ↥W := Fintype.ofFinite _
  haveI : DecidableEq ↥W := Classical.decEq _
  set f' : ↥W → ℤ := fun x => f x.1 with hf'def
  set g' : ↥W → ℤ := fun x => g x.1 with hg'def
  have hg0' : ∀ x, 0 ≤ g' x := fun x => hg0 x.1 x.2
  have hgf' : ∀ x, g' x < f' x := fun x => hgf x.1 x.2
  have hfd' : ∀ x, f' x ≤ (Nat.card {y : ↥W // (graphOf G W hG2).Adj x y} : ℤ) := by
    intro x
    show f x.1 ≤ _
    rw [natCard_graphOf_adj G W hG2 x]
    exact hfd x.1 x.2
  have hlov' : ∀ S T : Finset ↥W, Disjoint S T →
      (((S.product T).filter (fun p => (graphOf G W hG2).Adj p.1 p.2)).card : ℤ) ≤
        (∑ s ∈ S, f' s)
          + ∑ t ∈ T, ((Nat.card {y : ↥W // (graphOf G W hG2).Adj t y} : ℤ) - g' t) := by
    intro S T hST
    rw [card_filter_adj_eq_edgeCount hG2 S T]
    have hSW : ∀ x ∈ S.image Subtype.val, x ∈ W := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact y.2
    have hTW : ∀ x ∈ T.image Subtype.val, x ∈ W := by
      intro x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
      exact y.2
    have hdisj : Disjoint (S.image Subtype.val) (T.image Subtype.val) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb, hb'⟩ := Finset.mem_image.mp hx'
      exact (Finset.disjoint_left.mp hST) ha (Subtype.ext hb' ▸ hb)
    have hmain := hlov (S.image Subtype.val) (T.image Subtype.val) hSW hTW hdisj
    have hSsum : (∑ s ∈ S.image Subtype.val, f s) = ∑ s ∈ S, f' s := by
      simp only [hf'def]
      rw [sum_image_val S f]
    have hTsum : (∑ t ∈ T.image Subtype.val, ((degIn G W t : ℤ) - g t))
        = ∑ t ∈ T, ((Nat.card {y : ↥W // (graphOf G W hG2).Adj t y} : ℤ) - g' t) := by
      simp only [hg'def]
      rw [← sum_image_val T (fun t => ((degIn G W t : ℤ) - g t))]
      exact Finset.sum_congr rfl (fun t _ => by rw [natCard_graphOf_adj G W hG2 t])
    rw [hSsum, hTsum] at hmain
    exact hmain
  obtain ⟨M, hM⟩ :=
    Commons.Combinatorics.LovaszGFactor.lovasz_gf_factor (graphOf G W hG2) f' g'
      hg0' hgf' hfd' hlov'
  refine ⟨edgesOf G W hG2 M, edgesOf_subset G W hG2 M, ?_, ?_⟩
  · intro e he
    exact he.1
  · intro x hx
    rw [degIn_edgesOf G W hG2 M ⟨x, hx⟩]
    exact ⟨by simpa [hg'def] using (hM ⟨x, hx⟩).1,
      by simpa [hf'def] using (hM ⟨x, hx⟩).2⟩

end

end ErdosFaberLovaszConjecture
