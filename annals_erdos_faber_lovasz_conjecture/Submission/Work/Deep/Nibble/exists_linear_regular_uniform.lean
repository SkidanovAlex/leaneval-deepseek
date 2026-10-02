import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.EFL.DeepInputs

/-!
# The auxiliary design of `lem:embed` (`exists_linear_regular_uniform`)

For `r ≥ 2`, `p` prime with `r ≤ p` and `d ≤ p`, there is an `r`-uniform linear
hypergraph on `Fin (r * p)` in which every vertex has degree exactly `d`.

The construction is the cyclic one: identify `Fin (r * p)` with
`Fin r × ZMod p`, let `B := {0, …, d-1} ⊆ ZMod p` (a `d`-subset, as `d ≤ p`) and
take the family of the `d * p` edges

`E(a,x) = {(i, x + a·i) : i < r}`   (`a ∈ B`, `x : ZMod p`).

Each `E(a,x)` has exactly `r` points (as `Fin r ↪ ZMod p` is injective, which is
where `r ≤ p` is used), each vertex `(i,y)` lies in the unique edge
`E(a, y - a·i)` for each of the `d` multipliers `a ∈ B` (giving degree exactly
`d`), and two distinct edges meet in at most one point: if their multipliers
differ, `x + a·i = x' + a'·i` has at most one solution in the field `ZMod p`; if
the multipliers agree, the edges are equal or disjoint (and equal edges would
have `r ≥ 2` common points, contradicting the preceding case).

The construction is carried out on the product type `Fin r × ZMod p` — where
`Set.ncard` and the general-type degree `degAt` are the natural notions — and
then transported to `Fin (r * p)` along a bijection.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

namespace Cyc

/-! ## The cyclic design on `Fin r × ZMod p` -/

/-- The cast `Fin r → ZMod p`, `i ↦ i`.  It is injective when `r ≤ p`. -/
def finCast (r p : ℕ) (i : Fin r) : ZMod p := ((i : ℕ) : ZMod p)

/-- The cast `Fin r → ZMod p` is injective as soon as `r ≤ p`. -/
theorem finCast_injective {r p : ℕ} (hrp : r ≤ p) : Function.Injective (finCast r p) := by
  intro i j h
  apply Fin.ext
  have hmod := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp h
  rwa [Nat.mod_eq_of_lt (i.isLt.trans_le hrp), Nat.mod_eq_of_lt (j.isLt.trans_le hrp)] at hmod

/-- The cyclic edge `E(a,x) = {(i, x + a·i) : i < r}` of the design. -/
def cycEdge (r p : ℕ) (a x : ZMod p) : Set (Fin r × ZMod p) :=
  Set.range (fun i : Fin r => (i, x + a * finCast r p i))

/-- Membership in a cyclic edge. -/
theorem mem_cycEdge {r p : ℕ} (a x : ZMod p) (j : Fin r) (y : ZMod p) :
    (j, y) ∈ cycEdge r p a x ↔ y = x + a * finCast r p j := by
  constructor
  · rintro ⟨i, hi⟩
    have h1 : i = j := congrArg Prod.fst hi
    have h2 : x + a * finCast r p i = y := congrArg Prod.snd hi
    rw [h1] at h2
    exact h2.symm
  · intro hy
    exact ⟨j, by rw [hy]⟩

/-- A cyclic edge has exactly `r` points. -/
theorem cycEdge_ncard (r p : ℕ) (a x : ZMod p) : (cycEdge r p a x).ncard = r := by
  have hinj : Function.Injective (fun i : Fin r => (i, x + a * finCast r p i)) :=
    fun _ _ h => congrArg Prod.fst h
  rw [cycEdge, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Two cyclic edges with **distinct** multipliers meet in at most one point:
their two common points `(i,y)`, `(j,z)` satisfy `(a - a') * (i - j) = 0` in the
field `ZMod p`. -/
theorem cycEdge_inter_subsingleton {r p : ℕ} [Fact p.Prime] (hrp : r ≤ p)
    {a a' x x' : ZMod p} (ha : a ≠ a') :
    (cycEdge r p a x ∩ cycEdge r p a' x').Subsingleton := by
  rintro ⟨i, y⟩ hu ⟨j, z⟩ hv
  have huy : y = x + a * finCast r p i := (mem_cycEdge a x i y).mp hu.1
  have huy' : y = x' + a' * finCast r p i := (mem_cycEdge a' x' i y).mp hu.2
  have hvy : z = x + a * finCast r p j := (mem_cycEdge a x j z).mp hv.1
  have hvy' : z = x' + a' * finCast r p j := (mem_cycEdge a' x' j z).mp hv.2
  have hia : x + a * finCast r p i = x' + a' * finCast r p i := huy.symm.trans huy'
  have hja : x + a * finCast r p j = x' + a' * finCast r p j := hvy.symm.trans hvy'
  have hne : a - a' ≠ 0 := sub_ne_zero.mpr ha
  have hic : finCast r p i = (x' - x) / (a - a') := by
    rw [eq_div_iff_mul_eq hne]
    linear_combination hia
  have hjc : finCast r p j = (x' - x) / (a - a') := by
    rw [eq_div_iff_mul_eq hne]
    linear_combination hja
  have hij : i = j := finCast_injective hrp (hic.trans hjc.symm)
  subst hij
  rw [huy, hvy]

/-- A cyclic edge determines its parameters (here `r ≥ 2` is needed: the two
points `(0,x)`, `(1,x+a)` of `E(a,x)` must be distinct). -/
theorem cycEdge_eq_iff {r p : ℕ} [Fact p.Prime] (hr : 2 ≤ r) (hrp : r ≤ p)
    {a a' x x' : ZMod p} :
    cycEdge r p a x = cycEdge r p a' x' ↔ a = a' ∧ x = x' := by
  have hr0 : 0 < r := by omega
  have hr1 : 1 < r := by omega
  constructor
  · intro h
    have haa : a = a' := by
      by_contra ha
      have hsub : (cycEdge r p a x).Subsingleton := by
        have h' := cycEdge_inter_subsingleton (r := r) (p := p) (x := x) (x' := x') hrp ha
        rwa [← h, Set.inter_self] at h'
      have hm0 : ((⟨0, hr0⟩ : Fin r), x) ∈ cycEdge r p a x :=
        (mem_cycEdge a x ⟨0, hr0⟩ x).mpr (by simp [finCast])
      have hm1 : ((⟨1, hr1⟩ : Fin r), x + a) ∈ cycEdge r p a x :=
        (mem_cycEdge a x ⟨1, hr1⟩ (x + a)).mpr (by simp [finCast])
      have h01 := hsub hm0 hm1
      have hval : (⟨0, hr0⟩ : Fin r).val = (⟨1, hr1⟩ : Fin r).val :=
        congrArg (fun u : Fin r × ZMod p => u.1.val) h01
      simp at hval
    have h' : cycEdge r p a' x = cycEdge r p a' x' := by
      rw [haa] at h
      exact h
    have hmem : ((⟨0, hr0⟩ : Fin r), x) ∈ cycEdge r p a' x :=
      (mem_cycEdge a' x ⟨0, hr0⟩ x).mpr (by simp [finCast])
    rw [h'] at hmem
    have hx := (mem_cycEdge a' x' ⟨0, hr0⟩ x).mp hmem
    exact ⟨haa, by simpa [finCast] using hx⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## The family of cyclic edges -/

/-- The `d * p` cyclic edges `E(ζ k, x)`, `k : Fin d`, `x : ZMod p`. -/
def cycFam (r p d : ℕ) (ζ : Fin d → ZMod p) : Set (Set (Fin r × ZMod p)) :=
  (fun t : Fin d × ZMod p => cycEdge r p (ζ t.1) t.2) '' Set.univ

/-- Membership in the cyclic family. -/
theorem mem_cycFam {r p d : ℕ} {ζ : Fin d → ZMod p} {E : Set (Fin r × ZMod p)} :
    E ∈ cycFam r p d ζ ↔ ∃ (k : Fin d) (x : ZMod p), E = cycEdge r p (ζ k) x := by
  constructor
  · rintro ⟨⟨k, x⟩, -, rfl⟩
    exact ⟨k, x, rfl⟩
  · rintro ⟨k, x, rfl⟩
    exact ⟨(k, x), Set.mem_univ _, rfl⟩

/-- Every edge of the cyclic family has `r` points. -/
theorem cycFam_ncard {r p d : ℕ} {ζ : Fin d → ZMod p} :
    ∀ E ∈ cycFam r p d ζ, E.ncard = r := by
  rintro E ⟨⟨k, x⟩, -, rfl⟩
  exact cycEdge_ncard r p (ζ k) x

/-- The cyclic family is linear. -/
theorem cycFam_linear {r p d : ℕ} [Fact p.Prime] (hrp : r ≤ p) {ζ : Fin d → ZMod p} :
    ErdosFaberLovaszConjecture.Hypergraph.IsLinear (cycFam r p d ζ) := by
  rintro E₁ hE₁ E₂ hE₂ hne
  rw [mem_cycFam] at hE₁ hE₂
  obtain ⟨k₁, x₁, rfl⟩ := hE₁
  obtain ⟨k₂, x₂, rfl⟩ := hE₂
  by_cases hk : ζ k₁ = ζ k₂
  · rw [hk] at hne ⊢
    have hx : x₁ ≠ x₂ := by rintro rfl; exact hne rfl
    rintro ⟨i, y⟩ ⟨h1, h2⟩ ⟨j, z⟩ ⟨h3, h4⟩
    have hy1 : y = x₁ + ζ k₂ * finCast r p i := (mem_cycEdge (ζ k₂) x₁ i y).mp h1
    have hy2 : y = x₂ + ζ k₂ * finCast r p i := (mem_cycEdge (ζ k₂) x₂ i y).mp h2
    exact absurd (add_right_cancel (hy1.symm.trans hy2)) hx
  · exact cycEdge_inter_subsingleton hrp hk

/-- The degree of a vertex of a hypergraph on an arbitrary type: the number of
edges through it. -/
def degAt {α : Type*} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph α) (y : α) : ℕ :=
  Nat.card {A : Set α // A ∈ 𝓗 ∧ y ∈ A}

/-- `degAt` agrees with the `Nat.card` of the subtype of edges through `y`. -/
theorem degAt_eq {α : Type*} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph α) (y : α) :
    degAt 𝓗 y = Nat.card {e : 𝓗 // y ∈ (e : Set α)} := by
  rw [degAt, Nat.card_congr]
  refine Equiv.ofBijective
    (fun x : {A : Set α // A ∈ 𝓗 ∧ y ∈ A} =>
      (⟨⟨x.1, x.2.1⟩, x.2.2⟩ : {e : 𝓗 // y ∈ (e : Set α)})) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (congrArg (fun z : {e : 𝓗 // y ∈ (e : Set α)} => (z.1.1 : Set α)) h)
  · rintro ⟨⟨A, hA⟩, hy⟩
    exact ⟨⟨A, hA, hy⟩, rfl⟩

/-- Exactly `d` edges of the cyclic family pass through each vertex `(j, y)`:
the edges `E(ζ k, y - ζ k · j)`, `k : Fin d`. -/
theorem cycFam_degree {r p d : ℕ} [Fact p.Prime] (hr : 2 ≤ r) (hrp : r ≤ p)
    {ζ : Fin d → ZMod p} (hζ : Function.Injective ζ) (j : Fin r) (y : ZMod p) :
    degAt (cycFam r p d ζ) (j, y) = d := by
  classical
  rw [degAt_eq]
  have hset : Nat.card {E : ↥(cycFam r p d ζ) // (j, y) ∈ (E : Set (Fin r × ZMod p))}
      = ({E : ↥(cycFam r p d ζ) | (j, y) ∈ (E : Set (Fin r × ZMod p))} :
          Set ↥(cycFam r p d ζ)).ncard :=
    Nat.card_coe_set_eq _
  rw [hset]
  have huniv : (Set.univ : Set (Fin d)).ncard = d := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have key : (Set.univ : Set (Fin d)).ncard
      = ({E : ↥(cycFam r p d ζ) | (j, y) ∈ (E : Set (Fin r × ZMod p))} :
          Set ↥(cycFam r p d ζ)).ncard := by
    refine Set.ncard_congr (s := (Set.univ : Set (Fin d)))
      (t := ({E : ↥(cycFam r p d ζ) | (j, y) ∈ (E : Set (Fin r × ZMod p))} :
        Set ↥(cycFam r p d ζ)))
      (fun k _ => ⟨cycEdge r p (ζ k) (y - ζ k * finCast r p j),
        ⟨(k, y - ζ k * finCast r p j), Set.mem_univ _, rfl⟩⟩) ?_ ?_ ?_
    · intro k _
      exact (mem_cycEdge (ζ k) (y - ζ k * finCast r p j) j y).mpr (by ring)
    · intro k k' _ _ heq
      exact hζ ((cycEdge_eq_iff hr hrp).mp (congrArg Subtype.val heq)).1
    · intro E hE
      obtain ⟨k, x, hkx⟩ := mem_cycFam.mp E.2
      have hE' : (j, y) ∈ (E : Set (Fin r × ZMod p)) := hE
      have hmem : (j, y) ∈ cycEdge r p (ζ k) x := by rw [hkx] at hE'; exact hE'
      have hxy : y = x + ζ k * finCast r p j := (mem_cycEdge (ζ k) x j y).mp hmem
      have hx : x = y - ζ k * finCast r p j := by rw [hxy]; ring
      refine ⟨k, Set.mem_univ k, Subtype.ext ?_⟩
      rw [hx] at hkx
      exact hkx.symm
  rw [← key]
  exact huniv

/-! ## Transport along a bijection of vertex types -/

/-- **Degree is preserved by transporting a hypergraph along an injective map.**
The degree of `a` in `𝓗` equals the degree of `f a` in the pushed-forward
hypergraph `(Set.image f) '' 𝓗`. -/
theorem natCard_deg_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph α) (a : α) :
    Nat.card {e : (Set.image f) '' 𝓗 // f a ∈ (e : Set β)}
      = Nat.card {e : 𝓗 // a ∈ (e : Set α)} := by
  classical
  have h₁ : Nat.card {e : ↥𝓗 // a ∈ (e : Set α)}
      = ({e : ↥𝓗 | a ∈ (e : Set α)} : Set ↥𝓗).ncard := Nat.card_coe_set_eq _
  have h₂ : Nat.card {e' : ↥((Set.image f) '' 𝓗) // f a ∈ (e' : Set β)}
      = ({e' : ↥((Set.image f) '' 𝓗) | f a ∈ (e' : Set β)} : Set ↥((Set.image f) '' 𝓗)).ncard
      := Nat.card_coe_set_eq _
  rw [h₁, h₂]
  symm
  refine Set.ncard_congr
    (fun (e : ↥𝓗) (_ : e ∈ ({e : ↥𝓗 | a ∈ (e : Set α)} : Set ↥𝓗)) =>
      (⟨Set.image f (e : Set α), ⟨(e : Set α), e.2, rfl⟩⟩ : ↥((Set.image f) '' 𝓗))) ?_ ?_ ?_
  · intro e he
    exact Set.mem_image_of_mem f he
  · intro e₁ _ e₂ _ heq
    apply Subtype.ext
    exact (Set.image_eq_image hf).mp (congrArg Subtype.val heq)
  · intro e' he'
    obtain ⟨x, hx, hxe⟩ := e'.2
    have hfa : f a ∈ (e' : Set β) := he'
    rw [← hxe] at hfa
    obtain ⟨y, hy, hfy⟩ := hfa
    have hya : y = a := hf hfy
    have hax : a ∈ x := by rw [← hya]; exact hy
    refine ⟨⟨x, hx⟩, hax, ?_⟩
    apply Subtype.ext
    exact hxe

/-- Degrees are preserved by transporting a hypergraph along an injective map. -/
theorem degAt_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (𝓗 : ErdosFaberLovaszConjecture.Hypergraph α) (a : α) :
    degAt ((Set.image f) '' 𝓗) (f a) = degAt 𝓗 a := by
  rw [degAt_eq, degAt_eq]
  exact natCard_deg_image f hf 𝓗 a

end Cyc

open Cyc

/-- **The auxiliary design of `lem:embed`.**

For `r ≥ 2`, `p` prime with `r ≤ p`, and `d ≤ p`, there is an `r`-uniform linear
family on `Fin (r*p)` in which every vertex has degree exactly `d`.

(The hypothesis `r ≤ p` is needed: for `r = 4`, `p = 2`, `d = 2` the
incidence/pair count `r(d-1) ≤ pd - 1` fails, so no such hypergraph exists; and
the cyclic construction below also needs `Fin r ↪ ZMod p` to be injective.  In
the application of `lem:embed` one takes `p` prime with
`max (D, r) ≤ p ≤ 2 max (D, r)`, so the hypothesis is available.)

Construction (the cyclic one recorded in `Submission/EFL/Roadmap.lean`):
identify `Fin (r*p)` with `Fin r × ZMod p` (via `finProdFinEquiv` and
`Fin p ≃ ZMod p`), let `B := {a : ZMod p | a.val < d}` (a `d`-subset, so
`#B = d` as `d ≤ p`), and take the family of the `d * p` edges
`E(a,x) := {(i, x + a*i) : i < r}` for `a ∈ B`, `x : ZMod p`.
Each `E(a,x)` has exactly `r` points (as `Fin r ↪ ZMod p` is injective), each
vertex `(i,y)` lies in the unique edge `E(a, y - a*i)` for each of the `d`
multipliers `a ∈ B` (so the degree is exactly `d`), and two distinct edges
`E(a,x) ≠ E(a',x')` meet in at most one point: if `a ≠ a'` then
`x + a*i = x' + a'*i` has at most one solution in the field `ZMod p`, and if
`a = a'` the edges are equal or disjoint. -/
theorem exists_linear_regular_uniform (r p d : ℕ) (hr : 2 ≤ r) (hp : p.Prime) (hrp : r ≤ p)
    (hd : d ≤ p) :
    ∃ 𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin (r * p)),
      (∀ e ∈ 𝓗, ErdosFaberLovaszConjecture.edgeSize e = r) ∧
      𝓗.IsLinear ∧
      ∀ v : Fin (r * p), ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v = d := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hζ : Function.Injective (finCast d p) := finCast_injective hd
  have hcard : Fintype.card (Fin r × ZMod p) = r * p := by
    rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]
  let f : Fin r × ZMod p ≃ Fin (r * p) := Fintype.equivFinOfCardEq hcard
  refine ⟨(Set.image (f : Fin r × ZMod p → Fin (r * p))) '' cycFam r p d (finCast d p),
    ?_, ?_, ?_⟩
  · -- every edge has size `r`
    rintro e ⟨E, hE, rfl⟩
    rw [edgeSize_eq_ncard, Set.ncard_image_of_injective E (f.injective)]
    exact cycFam_ncard E hE
  · -- linearity
    rintro e₁ ⟨E₁, hE₁, rfl⟩ e₂ ⟨E₂, hE₂, rfl⟩ hne
    have hne' : E₁ ≠ E₂ := fun h => hne (by rw [h])
    have him : (Set.image (f : Fin r × ZMod p → Fin (r * p)) (E₁ ∩ E₂)).Subsingleton :=
      (cycFam_linear (ζ := finCast d p) hrp hE₁ hE₂ hne').image _
    rwa [Set.image_inter (f.injective)] at him
  · -- degree `d`
    intro v
    have hdeg : hypergraphDegree
          ((Set.image (f : Fin r × ZMod p → Fin (r * p))) '' cycFam r p d (finCast d p)) v
        = degAt ((Set.image (f : Fin r × ZMod p → Fin (r * p))) '' cycFam r p d (finCast d p)) v :=
      (degAt_eq _ v).symm
    rw [hdeg, ← f.apply_symm_apply v]
    rw [degAt_image (f : Fin r × ZMod p → Fin (r * p)) f.injective
      (cycFam r p d (finCast d p)) (f.symm v)]
    obtain ⟨j, y⟩ := f.symm v
    exact cycFam_degree hr hrp hζ j y

end

end Work.Deep.Nibble
