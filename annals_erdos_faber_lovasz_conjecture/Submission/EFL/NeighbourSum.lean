import Submission.EFL.Counting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The neighbour-sum bound of a linear hypergraph

The first ingredient of the paper's §6.2 forward-degree machinery
(Proposition `fwdnbr` and the reordering lemma) is the following counting
statement, the first line of the proof of Prop `fwdnbr`:

> **Neighbour-sum bound.**  In a linear hypergraph on `n` vertices, for an
> edge `e` of size `r` and with `N(e)` the set of its *neighbours* (the
> distinct edges intersecting `e`),
> ```
>     ∑_{f ∈ N(e)} (|f| − 1)  ≤  r · (n − r) .
> ```
> Indeed every neighbour `f` shares exactly one vertex with `e`, so it
> contributes `|f| − 1` pairs `{v, u}` with `v ∈ e` and `u ∉ e`; different
> neighbours contribute disjoint pairs (two distinct edges cannot share two
> vertices) and there are exactly `r(n−r)` such pairs.

The proof formalises this: `crossPairs e` is the set of ordered pairs
`(v, u)` with `v ∈ e`, `u ∉ e` (`|crossPairs e| = |e|·(n−|e|)`); for a
neighbour `f` the set `neighbourCrossPairs e f` of cross pairs with both
endpoints inside `f` has exactly `|f| − 1` elements (the common vertex is
unique by linearity), and these sets are pairwise disjoint as `f` ranges
over `N(e)`.  Summing the cardinalities (`neighbourCrossPairs_card`) over
the neighbours (`sum_neighbour_size_sub_le`) gives the bound; its real
cast (`sum_neighbour_real_le`) is the form the real-valued `fwdnbr`
inequalities of §6.2 consume.

Downstream uses: every estimate in §6.2 that bounds the number of
neighbours of a fixed edge by size.  The full statement is

> **Prop `fwdnbr`, inequality (i) (`fwddeg-inequality`), proved as
> `fwdnbr_inequality1`.**  For a linear hypergraph, an edge `e` of real size
> `r := (edgeSize e : ℝ)`, disjoint subfamilies `F₁`, `F₂ ⊆ N(e)` with
> `(1+α₁)r ≤ |f|` on `F₁` and `r/(1+α₂) ≤ |f|` on `F₂`, and `1+α₂ < r`
> (`α₁, α₂ ≥ 0`), `(1+α₁)m₁ + m₂/(1+α₂) ≤ n + (1+α₂)n/(r−1−α₂)` with
> `mᵢ := (Fᵢ.card : ℝ)`.

Its proof is assembled from: the lower bound `fwdnbr_sum_alpha` (step (α)):
`∑_{F₁∪F₂}((|f|:ℝ) − 1) ≥ m₁·((1+α₁)r − 1) + m₂·(r/(1+α₂) − 1)`; the upper
bound `fwdnbr_union_upper` (both halves of the paper's
`fwddeg-inequality1`); the divided form `fwdnbr_beta` (step (β));
the `m₁+m₂` bound `fwdnbr_gamma` (the paper's `fwddeg-inequality2`, divided
by `r`); and the substitution into `n − r + (m₁+m₂)/r ≤ n + (1+α₂)n/(r−1−α₂)`.

> **Prop `fwdnbr`, inequality (ii) (`fwddeg-far-bound`), proved as
> `fwdnbr_inequality2`.**  Under the additional hypotheses `m₁ + m₂ ≥
> (1−τ)n` and `α₁ > 0`, `m₁ ≤ (τ + (1+α₂)(1+α₂r)/(r−1−α₂))·n/α₁`.  Proof
> (paper §6.2): write (i)'s left side as
> `(m₁+m₂) + α₁m₁ − (1 − 1/(1+α₂))m₂`, drop `m₁+m₂ ≥ (1−τ)n`, use
> `1 − 1/(1+α₂) ≤ α₂` (`one_sub_inv_le`), bound `α₂m₂` by
> `α₂·(1+α₂)·r·n/(r−1−α₂)` from `fwdnbr_gamma`, and divide by `α₁ > 0`.

Also used: the maximum-degree bounds on the line graph used by the
locally-sparse corollaries.  Prop `fwdnbr` is thereby complete.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- The vertices *outside* a set `e ⊆ Fin n`, as a finset. -/
def outsideVerts {n : ℕ} (e : Set (Fin n)) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter (fun x : Fin n => x ∉ e)

/-- Membership in `outsideVerts e` is non-membership in `e`. -/
lemma mem_outsideVerts {n : ℕ} (e : Set (Fin n)) (x : Fin n) : x ∈ outsideVerts e ↔ x ∉ e := by
  classical
  simp [outsideVerts]

/-- The number of vertices outside a set of size `edgeSize e` is `n − edgeSize e`. -/
lemma card_outsideVerts {n : ℕ} (e : Set (Fin n)) : (outsideVerts e).card = n - edgeSize e := by
  classical
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun x : Fin n => x ∈ e)
  have h1 : ((Finset.univ : Finset (Fin n)).filter (fun x : Fin n => x ∈ e)).card = edgeSize e := by
    have : (Finset.univ : Finset (Fin n)).filter (fun x : Fin n => x ∈ e) = verts e := by
      ext x
      simp [verts]
    rw [this]
    rfl
  have h2 : (Finset.univ : Finset (Fin n)).filter (fun x : Fin n => ¬ x ∈ e) = outsideVerts e := by
    ext x
    simp [outsideVerts]
  rw [h1, h2, Finset.card_univ] at hsum
  simp at hsum
  omega

/-- The ordered cross pairs `(v, u)` with `v ∈ e` and `u ∉ e`. -/
def crossPairs {n : ℕ} (e : Set (Fin n)) : Finset (Fin n × Fin n) :=
  (verts e) ×ˢ (outsideVerts e)

/-- The number of cross pairs of an edge of size `edgeSize e` is
`edgeSize e · (n − edgeSize e)`. -/
lemma card_crossPairs {n : ℕ} (e : Set (Fin n)) : (crossPairs e).card = edgeSize e * (n - edgeSize e) := by
  classical
  unfold crossPairs
  rw [Finset.card_product]
  rw [card_outsideVerts]
  rfl

/-- The *neighbours* of an edge `e`: the distinct edges of `𝓗` intersecting `e`. -/
def neighbourEdges {n : ℕ} (𝓗 : Hypergraph (Fin n)) (e : 𝓗) : Finset 𝓗 := by
  classical
  exact (Finset.univ : Finset 𝓗).filter (fun f : 𝓗 =>
    f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty)

/-- Membership in `neighbourEdges`. -/
lemma mem_neighbourEdges {n : ℕ} (𝓗 : Hypergraph (Fin n)) (e f : 𝓗) :
    f ∈ neighbourEdges 𝓗 e ↔ f ≠ e ∧ ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty := by
  classical
  simp [neighbourEdges]

/-- A chosen common vertex of two intersecting vertex sets. -/
def commonVertex {n : ℕ} {a b : Set (Fin n)} (hint : (a ∩ b).Nonempty) : Fin n :=
  Classical.choose hint

/-- The chosen common vertex lies in the first set. -/
lemma commonVertex_mem_left {n : ℕ} {a b : Set (Fin n)} (hint : (a ∩ b).Nonempty) :
    commonVertex hint ∈ a :=
  (Classical.choose_spec hint).1

/-- The chosen common vertex lies in the second set. -/
lemma commonVertex_mem_right {n : ℕ} {a b : Set (Fin n)} (hint : (a ∩ b).Nonempty) :
    commonVertex hint ∈ b :=
  (Classical.choose_spec hint).2

/-- The cross pairs inside a neighbour `f` of `e`: pairs `(v, u)` with
`v ∈ f ∩ e`, `u ∈ f`, `u ∉ e`. -/
noncomputable def neighbourCrossPairs {n : ℕ} {𝓗 : Hypergraph (Fin n)} (e f : 𝓗) :
    Finset (Fin n × Fin n) := by
  classical
  exact (crossPairs (e : Set (Fin n))).filter (fun p : Fin n × Fin n =>
    p.1 ∈ (f : Set (Fin n)) ∧ p.2 ∈ (f : Set (Fin n)))

/-- The cross pairs inside a neighbour `f` of `e` are exactly `|f| − 1`
(the common vertex of `f` and `e` is unique, by linearity). -/
lemma neighbourCrossPairs_card {n : ℕ} {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {e f : 𝓗} (hfe : f ≠ e) (hint : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty) :
    (neighbourCrossPairs e f).card = edgeSize (f : Set (Fin n)) - 1 := by
  classical
  let v : Fin n := commonVertex (a := (f : Set (Fin n))) (b := (e : Set (Fin n))) hint
  let S : Finset (Fin n) := (verts (f : Set (Fin n))).filter (fun u : Fin n => u ∉ (e : Set (Fin n)))
  have hv1 : v ∈ (f : Set (Fin n)) := commonVertex_mem_left (a := (f : Set (Fin n))) (b := (e : Set (Fin n))) hint
  have hv2 : v ∈ (e : Set (Fin n)) := commonVertex_mem_right (a := (f : Set (Fin n))) (b := (e : Set (Fin n))) hint
  have hfeS : (f : Set (Fin n)) ≠ (e : Set (Fin n)) := by
    intro hEq
    exact hfe (Subtype.ext hEq)
  have hsubS : ((f : Set (Fin n)) ∩ (e : Set (Fin n))).Subsingleton := hlin f.2 e.2 hfeS
  have hEq : neighbourCrossPairs e f = S.image (fun u : Fin n => (v, u)) := by
    ext p
    constructor
    · intro hp
      rw [neighbourCrossPairs, Finset.mem_filter] at hp
      rcases hp with ⟨hpC, hpf⟩
      rcases (Finset.mem_product.mp hpC) with ⟨hp1e, hp2out⟩
      have hp1f : p.1 ∈ (f : Set (Fin n)) := hpf.1
      have hp1 : p.1 ∈ (e : Set (Fin n)) := by simpa using hp1e
      have hp1eq : p.1 = v := hsubS ⟨hp1f, hp1⟩ ⟨hv1, hv2⟩
      have hp2f : p.2 ∈ (f : Set (Fin n)) := hpf.2
      have hp2S : p.2 ∈ S := by
        dsimp [S]
        rw [Finset.mem_filter]
        exact ⟨by simpa using hp2f, (mem_outsideVerts (e : Set (Fin n)) p.2).mp hp2out⟩
      refine (Finset.mem_image).mpr ⟨p.2, hp2S, ?_⟩
      cases p with
      | mk a b =>
        rw [← hp1eq]
    · intro hp
      rcases (Finset.mem_image.mp hp) with ⟨u, huS, hEqp⟩
      rw [neighbourCrossPairs, Finset.mem_filter]
      constructor
      · rw [← hEqp]
        rw [crossPairs, Finset.mem_product]
        constructor
        · simpa using hv2
        · rw [mem_outsideVerts]
          have hu2 : u ∉ (e : Set (Fin n)) := by
            dsimp [S] at huS
            rw [Finset.mem_filter] at huS
            exact huS.2
          exact hu2
      · rw [← hEqp]
        constructor
        · simpa using hv1
        · dsimp [S] at huS
          rw [Finset.mem_filter] at huS
          simpa using huS.1
  have hS : S.card = edgeSize (f : Set (Fin n)) - 1 := by
    have hEq2 : S = (verts (f : Set (Fin n))).erase v := by
      ext u
      constructor
      · intro hu
        dsimp [S] at hu
        rw [Finset.mem_filter] at hu
        rw [Finset.mem_erase]
        constructor
        · intro hEqv
          exact hu.2 (by simpa [hEqv] using hv2)
        · simpa using hu.1
      · intro hu
        rw [Finset.mem_erase] at hu
        dsimp [S]
        rw [Finset.mem_filter]
        constructor
        · simpa using hu.2
        · intro hue
          have hu1 : u ∈ (f : Set (Fin n)) := by simpa using hu.2
          have hEq : u = v := hsubS ⟨hu1, hue⟩ ⟨hv1, hv2⟩
          exact hu.1 hEq
    have hvc : v ∈ (verts (f : Set (Fin n))) := by simp [hv1]
    rw [hEq2]
    rw [Finset.card_erase_of_mem hvc]
    rfl
  have hinj : Function.Injective (fun u : Fin n => (v, u)) := by
    intro a b h
    exact congrArg Prod.snd h
  rw [hEq]
  rw [Finset.card_image_of_injective (s := S) (f := fun u : Fin n => (v, u)) hinj]
  exact hS

/-- **Neighbour-sum lemma** (paper §6.2, Prop `fwdnbr`, first line of its
proof): in a linear hypergraph on `n` vertices, for an edge `e` the sum of
`|f| − 1` over all neighbours `f ∈ N(e)` is at most
`|e| · (n − |e|)`. -/
theorem sum_neighbour_size_sub_le {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) :
    ((neighbourEdges 𝓗 e).sum (fun f : 𝓗 => edgeSize (f : Set (Fin n)) - 1)) ≤
      edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n))) := by
  classical
  let fp : 𝓗 → Finset (Fin n × Fin n) := fun f => neighbourCrossPairs e f
  have hpd : ((neighbourEdges 𝓗 e : Finset 𝓗) : Set 𝓗).PairwiseDisjoint fp := by
    intro f₁ hf₁ f₂ hf₂ hne
    change Disjoint (fp f₁) (fp f₂)
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    dsimp [fp] at hp₁ hp₂
    rw [neighbourCrossPairs, Finset.mem_filter] at hp₁ hp₂
    rcases hp₁ with ⟨hp₁C, hp₁f⟩
    rcases hp₂ with ⟨hp₂C, hp₂f⟩
    rcases (Finset.mem_product.mp hp₁C) with ⟨hp₁v, hp₁out⟩
    have hp₁e : p.1 ∈ (e : Set (Fin n)) := by simpa using hp₁v
    have hp₂not : p.2 ∉ (e : Set (Fin n)) := (mem_outsideVerts (e : Set (Fin n)) p.2).mp hp₁out
    have hxy : p.1 ≠ p.2 := by
      intro hEq
      exact hp₂not (by simpa [hEq] using hp₁e)
    have hEqS : (f₁ : Set (Fin n)) = (f₂ : Set (Fin n)) :=
      IsLinear.eq_of_mem_pair hlin f₁.2 f₂.2 hxy hp₁f.1 hp₁f.2 hp₂f.1 hp₂f.2
    exact hne (Subtype.ext hEqS)
  let D : Finset (Fin n × Fin n) := (neighbourEdges 𝓗 e).disjiUnion fp hpd
  have hDcard : D.card = (neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (fp f).card) :=
    Finset.card_disjiUnion (neighbourEdges 𝓗 e) fp hpd
  have hDsub : D ⊆ crossPairs (e : Set (Fin n)) := by
    intro p hp
    rw [Finset.mem_disjiUnion] at hp
    rcases hp with ⟨f, _hf, hp⟩
    dsimp [fp] at hp
    rw [neighbourCrossPairs, Finset.mem_filter] at hp
    exact hp.1
  have hle : D.card ≤ (crossPairs (e : Set (Fin n))).card := Finset.card_le_card hDsub
  calc
    (neighbourEdges 𝓗 e).sum (fun f : 𝓗 => edgeSize (f : Set (Fin n)) - 1)
        = (neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (fp f).card) := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          dsimp [fp]
          have hfN := (mem_neighbourEdges 𝓗 e f).mp hf
          exact (neighbourCrossPairs_card (𝓗 := 𝓗) hlin hfN.1 hfN.2).symm
    _ = D.card := hDcard.symm
    _ ≤ (crossPairs (e : Set (Fin n))).card := hle
    _ = edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n))) := card_crossPairs (e : Set (Fin n))


/-- A subfamily `F` of the neighbours of `e`, all of whose members have size
at least `ℓ`, satisfies `|F|·(ℓ−1) ≤ |e|·(n − |e|)` — the natural form of
the paper's `fwddeg-inequality2` (`m₁ + m₂ ≤ r(n−r)/(r/(1+α₂) − 1)`):
each `f ∈ F` contributes at least `ℓ − 1` to the neighbour-sum. -/
theorem card_neighbour_family_mul_le {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) (F : Finset 𝓗)
    (hF : ∀ f ∈ F, f ∈ neighbourEdges 𝓗 e)
    (ℓ : ℕ) (hℓ : ∀ f ∈ F, ℓ ≤ edgeSize (f : Set (Fin n))) :
    F.card * (ℓ - 1) ≤ edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n))) := by
  classical
  have hFsub : F ⊆ neighbourEdges 𝓗 e := by
    intro f hf
    exact hF f hf
  have hterm : ∀ f ∈ F, ℓ - 1 ≤ edgeSize (f : Set (Fin n)) - 1 := by
    intro f hf
    have hs := hℓ f hf
    omega
  have hsum_le : (F.sum (fun f : 𝓗 => edgeSize (f : Set (Fin n)) - 1)) ≥
      F.card * (ℓ - 1) := by
    have hsumc : (F.sum fun _ : 𝓗 => ℓ - 1) = F.card * (ℓ - 1) := by
      rw [Finset.sum_const]
      simp
    calc
      F.card * (ℓ - 1) = F.sum (fun _ : 𝓗 => ℓ - 1) := hsumc.symm
      _ ≤ F.sum (fun f : 𝓗 => edgeSize (f : Set (Fin n)) - 1) := by
        exact Finset.sum_le_sum hterm
  have hle_sum : (F.sum (fun f : 𝓗 => edgeSize (f : Set (Fin n)) - 1)) ≤
      ((neighbourEdges 𝓗 e).sum (fun f : 𝓗 => edgeSize (f : Set (Fin n)) - 1)) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hFsub (by simp)
  exact (hsum_le.trans hle_sum).trans (sum_neighbour_size_sub_le (𝓗 := 𝓗) hlin e)

/-- A subfamily `F` of the neighbours of `e` with all members of size at
least `ℓ ≥ 2` has size at most `|e|·(n−|e|) / (ℓ−1)`. -/
theorem card_neighbour_family_le {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) (F : Finset 𝓗)
    (hF : ∀ f ∈ F, f ∈ neighbourEdges 𝓗 e)
    (ℓ : ℕ) (h2ℓ : 2 ≤ ℓ) (hℓ : ∀ f ∈ F, ℓ ≤ edgeSize (f : Set (Fin n))) :
    F.card ≤ (edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n)))) / (ℓ - 1) := by
  classical
  have hmul := card_neighbour_family_mul_le (𝓗 := 𝓗) hlin e F hF ℓ hℓ
  have hpos : 0 < ℓ - 1 := by omega
  exact (Nat.le_div_iff_mul_le hpos).2 hmul


/-- **Real-valued neighbour-sum bound**: the real form of
`sum_neighbour_size_sub_le` used by the real-valued `fwdnbr` inequalities of
§6.2 (Prop `fwdnbr`). -/
theorem sum_neighbour_real_le {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) :
    (((neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1)) ≤
      (edgeSize (e : Set (Fin n)) : ℝ) * ((n : ℝ) - (edgeSize (e : Set (Fin n)) : ℝ))) := by
  classical
  have hnat := sum_neighbour_size_sub_le (𝓗 := 𝓗) hlin e
  have hterm : ∀ f : 𝓗, f ∈ neighbourEdges 𝓗 e →
      (((edgeSize (f : Set (Fin n)) - 1 : ℕ) : ℝ) = (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
    intro f hf
    have hfN := (mem_neighbourEdges 𝓗 e f).mp hf
    have hge : 1 ≤ edgeSize (f : Set (Fin n)) := by
      rcases hfN.2 with ⟨x, hx⟩
      have : (verts (f : Set (Fin n))).Nonempty := ⟨x, by simp [hx.1]⟩
      simpa [edgeSize] using (Finset.card_pos.mpr this)
    rw [Nat.cast_sub hge]
    norm_num
  have hsumL : ((neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) - 1 : ℕ)) : ℝ)
      = (neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
    calc
      ((neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) - 1 : ℕ)) : ℝ)
          = (neighbourEdges 𝓗 e).sum (fun f : 𝓗 => ((edgeSize (f : Set (Fin n)) - 1 : ℕ) : ℝ)) := by
            simp
      _ = (neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
            refine Finset.sum_congr rfl ?_
            intro f hf
            exact hterm f hf
  have hre : edgeSize (e : Set (Fin n)) ≤ n := by
    have hsub : verts (e : Set (Fin n)) ⊆ (Finset.univ : Finset (Fin n)) := by
      intro x _hx
      simp
    have hle : (verts (e : Set (Fin n))).card ≤ (Finset.univ : Finset (Fin n)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    simpa [edgeSize] using hle
  have hsumR : ((edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n))) : ℕ) : ℝ) =
      (edgeSize (e : Set (Fin n)) : ℝ) * ((n : ℝ) - (edgeSize (e : Set (Fin n)) : ℝ)) := by
    rw [Nat.cast_mul]
    rw [Nat.cast_sub hre]
  have hcast : ((neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) - 1 : ℕ)) : ℝ) ≤
      ((edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n))) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  rw [← hsumL, ← hsumR]
  exact hcast


/-- **Step (α) of Prop `fwdnbr` (paper §6.2)**: for disjoint subfamilies
`F₁`, `F₂` of edges whose sizes satisfy the real lower bounds
`(1+α₁)·r ≤ |f|` (for `f ∈ F₁`) and `r/(1+α₂) ≤ |f|` (for `f ∈ F₂`),
where `r := (edgeSize e : ℝ)`, the sum over `F₁ ∪ F₂` of `(|f| : ℝ) − 1`
is at least `m₁·((1+α₁)r − 1) + m₂·(r/(1+α₂) − 1)`, with
`mᵢ := (Fᵢ.card : ℝ)`.  (This is the lower-bound half of the paper's
`fwddeg-inequality1`; the upper half comes from
`sum_neighbour_real_le`.) -/
theorem fwdnbr_sum_alpha {n : ℕ} {𝓗 : Hypergraph (Fin n)} (e : 𝓗)
    (α₁ α₂ : ℝ) (F₁ F₂ : Finset 𝓗)
    (hdisj : Disjoint F₁ F₂)
    (hbig : ∀ f ∈ F₁, ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ))
    (hmed : ∀ f ∈ F₂, ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ)) :
    (F₁.card : ℝ) * ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ) - 1) +
      (F₂.card : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂) - 1) ≤
      (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
  classical
  have h₁ : (F₁.card : ℝ) * ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ) - 1) ≤
      F₁.sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
    have hle : F₁.card • ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ) - 1) ≤
        F₁.sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
      exact Finset.card_nsmul_le_sum F₁
        (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1)
        ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ) - 1) (by
          intro f hf
          have hb := hbig f hf
          nlinarith)
    simpa using hle
  have h₂ : (F₂.card : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂) - 1) ≤
      F₂.sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
    have hle : F₂.card • ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂) - 1) ≤
        F₂.sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
      exact Finset.card_nsmul_le_sum F₂
        (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1)
        ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂) - 1) (by
          intro f hf
          have hb := hmed f hf
          nlinarith)
    simpa using hle
  rw [Finset.sum_union hdisj]
  exact add_le_add h₁ h₂


/-- union of two neighbour subfamilies: its real-minus-one sum is at most r(n−r) -/
lemma fwdnbr_union_upper {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) (F₁ F₂ : Finset 𝓗)
    (hF₁ : ∀ f ∈ F₁, f ∈ neighbourEdges 𝓗 e)
    (hF₂ : ∀ f ∈ F₂, f ∈ neighbourEdges 𝓗 e) :
    (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) ≤
      (edgeSize (e : Set (Fin n)) : ℝ) * ((n : ℝ) - (edgeSize (e : Set (Fin n)) : ℝ)) := by
  classical
  have hUsub : F₁ ∪ F₂ ⊆ neighbourEdges 𝓗 e := by
    intro f hf
    rcases (Finset.mem_union.mp hf) with hf₁ | hf₂
    · exact hF₁ f hf₁
    · exact hF₂ f hf₂
  have hnonneg : ∀ f ∈ neighbourEdges 𝓗 e,
      (0 : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) - 1 := by
    intro f hf
    have hfN := (mem_neighbourEdges 𝓗 e f).mp hf
    rcases hfN.2 with ⟨x, hx⟩
    have hnon : (verts (f : Set (Fin n))).Nonempty := ⟨x, by simp [hx.1]⟩
    have hge : 1 ≤ (verts (f : Set (Fin n))).card := Finset.card_pos.mpr hnon
    have hge' : 1 ≤ edgeSize (f : Set (Fin n)) := by simpa [edgeSize] using hge
    have hgeR : (1 : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by exact_mod_cast hge'
    nlinarith
  have hle1 : (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) ≤
      (neighbourEdges 𝓗 e).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hUsub (by
      intro f hfN _hfnot
      exact hnonneg f hfN)
  exact hle1.trans (sum_neighbour_real_le (𝓗 := 𝓗) hlin e)

/-- (β): the divided form -/
lemma fwdnbr_beta {𝓗 : Hypergraph (Fin n)} (e : 𝓗) (α₁ α₂ : ℝ) (F₁ F₂ : Finset 𝓗)
    (hr : 0 < (edgeSize (e : Set (Fin n)) : ℝ))
    (h₁α₂ : 0 < 1 + α₂)
    (hstar : (F₁.card : ℝ) * ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ) - 1) +
        (F₂.card : ℝ) * ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂) - 1) ≤
      (edgeSize (e : Set (Fin n)) : ℝ) *
        ((n : ℝ) - (edgeSize (e : Set (Fin n)) : ℝ))) :
    (1 + α₁) * (F₁.card : ℝ) + (F₂.card : ℝ) / (1 + α₂) ≤
      (n : ℝ) - (edgeSize (e : Set (Fin n)) : ℝ) +
        ((F₁.card : ℝ) + (F₂.card : ℝ)) / (edgeSize (e : Set (Fin n)) : ℝ) := by
  classical
  let r : ℝ := (edgeSize (e : Set (Fin n)) : ℝ)
  let m₁ : ℝ := (F₁.card : ℝ)
  let m₂ : ℝ := (F₂.card : ℝ)
  let X : ℝ := (1 + α₁) * m₁ + m₂ / (1 + α₂)
  let Y : ℝ := (n : ℝ) - r
  have hstarR : m₁ * ((1 + α₁) * r - 1) + m₂ * (r / (1 + α₂) - 1) ≤ r * ((n : ℝ) - r) := by
    dsimp [r, m₁, m₂]
    exact hstar
  have hEqL : m₁ * ((1 + α₁) * r - 1) + m₂ * (r / (1 + α₂) - 1) = r * X - (m₁ + m₂) := by
    dsimp [X]
    field_simp [h₁α₂.ne']
    ring
  have h1 : r * X ≤ r * Y + (m₁ + m₂) := by
    have hh : r * X - (m₁ + m₂) ≤ r * Y := by
      dsimp [Y]
      rwa [hEqL] at hstarR
    nlinarith
  apply le_of_mul_le_mul_right _ hr
  calc
    X * r = r * X := by ring
    _ ≤ r * Y + (m₁ + m₂) := h1
    _ = (Y + (m₁ + m₂) / r) * r := by
      rw [add_mul, div_mul_cancel₀ (m₁ + m₂) hr.ne']
      ring

/-- (γ): the divided m₁+m₂ bound -/
lemma fwdnbr_gamma {n : ℕ} {𝓗 : Hypergraph (Fin n)} (e : 𝓗) (α₂ : ℝ) (F₁ F₂ : Finset 𝓗)
    (h1α₂ : 0 < 1 + α₂)
    (hr1α2 : 0 < (edgeSize (e : Set (Fin n)) : ℝ) - 1 - α₂)
    (hr : 0 < (edgeSize (e : Set (Fin n)) : ℝ))
    (hdisj : Disjoint F₁ F₂)
    (hc : ∀ f ∈ F₁ ∪ F₂, ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ))
    (hupper : (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) ≤
      (edgeSize (e : Set (Fin n)) : ℝ) * (n : ℝ)) :
    ((F₁.card : ℝ) + (F₂.card : ℝ)) / (edgeSize (e : Set (Fin n)) : ℝ) ≤
      (1 + α₂) * (n : ℝ) / ((edgeSize (e : Set (Fin n)) : ℝ) - 1 - α₂) := by
  classical
  let r : ℝ := (edgeSize (e : Set (Fin n)) : ℝ)
  let c : ℝ := r / (1 + α₂) - 1
  have hcpos : 0 < c := by
    have hEq : c = (r - 1 - α₂) / (1 + α₂) := by
      dsimp [c]
      field_simp [h1α₂.ne']
      ring
    rw [hEq]
    exact div_pos hr1α2 h1α₂
  have hlower : c * ((F₁.card : ℝ) + (F₂.card : ℝ)) ≤
      (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
    have hcard : (F₁ ∪ F₂).card = F₁.card + F₂.card := Finset.card_union_of_disjoint hdisj
    have hns : (F₁ ∪ F₂).card • c ≤
        (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
      exact Finset.card_nsmul_le_sum (F₁ ∪ F₂)
        (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) c (by
          intro f hf
          have hc' := hc f hf
          dsimp [c]
          nlinarith)
    -- (card:ℝ)·c = c·(m1+m2):
    have hcR : ((F₁ ∪ F₂).card : ℝ) * c = c * ((F₁.card : ℝ) + (F₂.card : ℝ)) := by
      rw [hcard]
      norm_cast
      ring
    calc
      c * ((F₁.card : ℝ) + (F₂.card : ℝ)) = ((F₁ ∪ F₂).card : ℝ) * c := by rw [hcR]
      _ ≤ (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) := by
        simpa using hns
  -- hupper with r
  have hupR : (F₁ ∪ F₂).sum (fun f : 𝓗 => (edgeSize (f : Set (Fin n)) : ℝ) - 1) ≤ r * (n : ℝ) := by
    dsimp [r]
    exact hupper
  -- divide by r:
  apply le_of_mul_le_mul_right _ hr
  -- goal: (m1+m2)/r * r ≤ ((1+α2)*n/(r−1−α2)) * r; LHS = m1+m2:
  calc
    (((F₁.card : ℝ) + (F₂.card : ℝ)) / r) * r = (F₁.card : ℝ) + (F₂.card : ℝ) := by
      rw [div_mul_cancel₀ _ hr.ne']
    _ ≤ ((1 + α₂) * (n : ℝ) / (r - 1 - α₂)) * r := by
      -- from hlower & hupper: c·(m1+m2) ≤ r·n; c = (r−1−α2)/(1+α2):
      have hcEq : c = (r - 1 - α₂) / (1 + α₂) := by
        dsimp [c]
        field_simp [h1α₂.ne']
        ring
      have hmain : c * ((F₁.card : ℝ) + (F₂.card : ℝ)) ≤ r * (n : ℝ) := hlower.trans hupR
      -- multiply by (1+α2), divide by (r−1−α2): target (m1+m2) ≤ ((1+α2)n/(r−1−α2))·r
      -- equivalently: (m1+m2) ≤ ((1+α2)·r·n)/(r−1−α2): from hmain: (r−1−α2)/(1+α2)·(m1+m2) ≤ rn
      -- multiply hmain by (1+α2) and substitute hcEq:
      have hcL : (1 + α₂) * (c * ((F₁.card : ℝ) + (F₂.card : ℝ))) =
            (r - 1 - α₂) * ((F₁.card : ℝ) + (F₂.card : ℝ)) := by
        rw [hcEq]
        field_simp [h1α₂.ne']
      have hmain' : (r - 1 - α₂) * ((F₁.card : ℝ) + (F₂.card : ℝ)) ≤ (1 + α₂) * r * (n : ℝ) := by
        have h0 := mul_le_mul_of_nonneg_left hmain (le_of_lt h1α₂)
        rw [hcL] at h0
        simpa [← mul_assoc] using h0
      -- now divide by (r−1−α2) > 0:
      have hmain2 : (F₁.card : ℝ) + (F₂.card : ℝ) ≤ (1 + α₂) * r * (n : ℝ) / (r - 1 - α₂) := by
        apply le_of_mul_le_mul_right _ hr1α2
        calc
          (((F₁.card : ℝ) + (F₂.card : ℝ)) * (r - 1 - α₂)) = (r - 1 - α₂) * ((F₁.card : ℝ) + (F₂.card : ℝ)) := by ring
          _ ≤ (1 + α₂) * r * (n : ℝ) := hmain'
          _ = ((1 + α₂) * r * (n : ℝ) / (r - 1 - α₂)) * (r - 1 - α₂) := by
            rw [div_mul_cancel₀ _ hr1α2.ne']
      -- goal: (m1+m2) ≤ ((1+α2)n/(r−1−α2))·r; RHS = (1+α2)·r·n/(r−1−α2): ring-normalize
      have hrhs : ((1 + α₂) * (n : ℝ) / (r - 1 - α₂)) * r = (1 + α₂) * r * (n : ℝ) / (r - 1 - α₂) := by
        field_simp [hr1α2.ne']
      rwa [hrhs]

/-- **Prop `fwdnbr` inequality (i)** (paper §6.2, `fwddeg-inequality`):
for a linear hypergraph, an edge `e` of real size `r := (edgeSize e : ℝ)`,
disjoint subfamilies `F₁`, `F₂ ⊆ N(e)` with `(1+α₁)r ≤ |f|` on `F₁` and
`r/(1+α₂) ≤ |f|` on `F₂`, and `1 + α₂ < r` (with `α₁, α₂ ≥ 0`),
`(1+α₁)·m₁ + m₂/(1+α₂) ≤ n + (1+α₂)·n/(r−1−α₂)` where `mᵢ := (Fᵢ.card : ℝ)`. -/
theorem fwdnbr_inequality1 {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) (α₁ α₂ : ℝ)
    (hα₁ : 0 ≤ α₁) (hα₂ : 0 ≤ α₂)
    (F₁ F₂ : Finset 𝓗)
    (hF₁ : ∀ f ∈ F₁, f ∈ neighbourEdges 𝓗 e)
    (hF₂ : ∀ f ∈ F₂, f ∈ neighbourEdges 𝓗 e)
    (hdisj : Disjoint F₁ F₂)
    (hbig : ∀ f ∈ F₁, ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ))
    (hmed : ∀ f ∈ F₂, ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ))
    (hcond : (1 + α₂) < (edgeSize (e : Set (Fin n)) : ℝ)) :
    (1 + α₁) * (F₁.card : ℝ) + (F₂.card : ℝ) / (1 + α₂) ≤
      (n : ℝ) + (1 + α₂) * (n : ℝ) / ((edgeSize (e : Set (Fin n)) : ℝ) - 1 - α₂) := by
  classical
  let r : ℝ := (edgeSize (e : Set (Fin n)) : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    have h01 : (0 : ℝ) ≤ 1 + α₂ := by nlinarith
    exact lt_of_le_of_lt h01 hcond
  have h₁α₂ : 0 < 1 + α₂ := by nlinarith
  have hr1α2 : 0 < r - 1 - α₂ := by
    dsimp [r]
    nlinarith
  -- (α)
  have halpha := fwdnbr_sum_alpha (n := n) e α₁ α₂ F₁ F₂ hdisj hbig hmed
  -- upper
  have hupper := fwdnbr_union_upper (n := n) hlin e F₁ F₂ hF₁ hF₂
  have hstar : (F₁.card : ℝ) * ((1 + α₁) * r - 1) + (F₂.card : ℝ) * (r / (1 + α₂) - 1) ≤
      r * ((n : ℝ) - r) := by
    dsimp [r]
    exact halpha.trans hupper
  -- (β)
  have hbeta := fwdnbr_beta e α₁ α₂ F₁ F₂ hr h₁α₂ (by simpa [r] using hstar)
  -- (γ): per-member lower bound over the union
  have hc : ∀ f ∈ F₁ ∪ F₂, (r / (1 + α₂) ≤ (edgeSize (f : Set (Fin n)) : ℝ)) := by
    intro f hf
    rcases (Finset.mem_union.mp hf) with hf₁ | hf₂
    · have hb := hbig f hf₁
      have hdiv : r / (1 + α₂) ≤ r := div_le_self (le_of_lt hr) (by nlinarith)
      have hmono : r ≤ (1 + α₁) * r := by
        have hαr : 0 ≤ α₁ * r := mul_nonneg hα₁ (le_of_lt hr)
        nlinarith
      exact (hdiv.trans hmono).trans hb
    · have hmed' := hmed f hf₂
      dsimp [r] at hmed' ⊢
      exact hmed'
  have hgamma := fwdnbr_gamma (n := n) e α₂ F₁ F₂ h₁α₂ (by simpa [r] using hr1α2) hr hdisj hc
    (by
      have hle1 := hupper
      have hle2 : r * ((n : ℝ) - r) ≤ r * (n : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hr)
        nlinarith
      -- union sum ≤ r((n:ℝ)−r) ≤ r·(n:ℝ): hc-type: (fun f => |f|−1) sum ≤ r·n:
      exact hle1.trans (by
        -- (edgeSize)·((n:ℝ) − edgeSize) ≤ (edgeSize)·(n:ℝ)
        have hle2 : (edgeSize (e : Set (Fin n)) : ℝ) * ((n : ℝ) - (edgeSize (e : Set (Fin n)) : ℝ)) ≤
            (edgeSize (e : Set (Fin n)) : ℝ) * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        simpa [r] using hle2))
  -- gamma conclusion: (m1+m2)/r ≤ (1+α2)n/(r−1−α2)  [with r := edgeSize]: expressed via edgeSize cast inside gamma. Combine with beta:
  have hbetar : (1 + α₁) * (F₁.card : ℝ) + (F₂.card : ℝ) / (1 + α₂) ≤
      (n : ℝ) - r + ((F₁.card : ℝ) + (F₂.card : ℝ)) / r := by
    simpa [r] using hbeta
  have hgammar : ((F₁.card : ℝ) + (F₂.card : ℝ)) / r ≤
      (1 + α₂) * (n : ℝ) / (r - 1 - α₂) := by
    simpa [r] using hgamma
  have hfinal : (1 + α₁) * (F₁.card : ℝ) + (F₂.card : ℝ) / (1 + α₂) ≤
      (n : ℝ) + (1 + α₂) * (n : ℝ) / (r - 1 - α₂) := by
    nlinarith [hbetar, hgammar]
  simpa [r] using hfinal


/-- helper: 1 − 1/(1+α₂) ≤ α₂ -/
lemma one_sub_inv_le {α₂ : ℝ} (hα₂ : 0 ≤ α₂) (h1α2 : 0 < 1 + α₂) :
    1 - 1 / (1 + α₂) ≤ α₂ := by
  apply le_of_mul_le_mul_right _ h1α2
  calc
    (1 - 1 / (1 + α₂)) * (1 + α₂) = α₂ := by
      field_simp [h1α2.ne']
      ring
    _ ≤ α₂ * (1 + α₂) := by
      have hsq : 0 ≤ α₂ * α₂ := mul_self_nonneg α₂
      nlinarith


/-- **Prop `fwdnbr` inequality (ii)** (paper §6.2, `fwddeg-far-bound`):
if in addition `m₁ + m₂ ≥ (1−τ)n` and `α₁ > 0`, then
`m₁ ≤ (τ + (1+α₂)(1+α₂r)/(r−1−α₂))·n/α₁`. -/
theorem fwdnbr_inequality2 {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) (α₁ α₂ τ : ℝ)
    (hα₁ : 0 < α₁) (hα₂ : 0 ≤ α₂)
    (F₁ F₂ : Finset 𝓗)
    (hF₁ : ∀ f ∈ F₁, f ∈ neighbourEdges 𝓗 e)
    (hF₂ : ∀ f ∈ F₂, f ∈ neighbourEdges 𝓗 e)
    (hdisj : Disjoint F₁ F₂)
    (hbig : ∀ f ∈ F₁, ((1 + α₁) * (edgeSize (e : Set (Fin n)) : ℝ)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ))
    (hmed : ∀ f ∈ F₂, ((edgeSize (e : Set (Fin n)) : ℝ) / (1 + α₂)) ≤
      (edgeSize (f : Set (Fin n)) : ℝ))
    (hcond : (1 + α₂) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hbigsum : (1 - τ) * (n : ℝ) ≤ (F₁.card : ℝ) + (F₂.card : ℝ)) :
    (F₁.card : ℝ) ≤
      (τ + (1 + α₂) * (1 + α₂ * (edgeSize (e : Set (Fin n)) : ℝ)) /
        ((edgeSize (e : Set (Fin n)) : ℝ) - 1 - α₂)) * (n : ℝ) / α₁ := by
  classical
  let r : ℝ := (edgeSize (e : Set (Fin n)) : ℝ)
  let m₁ : ℝ := (F₁.card : ℝ)
  let m₂ : ℝ := (F₂.card : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    have h01 : (0 : ℝ) ≤ 1 + α₂ := by nlinarith
    exact lt_of_le_of_lt h01 hcond
  have h₁α₂ : 0 < 1 + α₂ := by nlinarith
  have hr1α2 : 0 < r - 1 - α₂ := by
    dsimp [r]
    nlinarith
  have hm1 : 0 ≤ m₁ := by dsimp [m₁]; positivity
  have hm2 : 0 ≤ m₂ := by dsimp [m₂]; positivity
  -- inequality (i) in r/m/T form
  have hi' : (1 + α₁) * m₁ + m₂ / (1 + α₂) ≤
      (n : ℝ) + (1 + α₂) * (n : ℝ) / (r - 1 - α₂) := by
    have h := fwdnbr_inequality1 (n := n) hlin e α₁ α₂ (le_of_lt hα₁) hα₂ F₁ F₂ hF₁ hF₂ hdisj hbig hmed hcond
    simpa [r, m₁, m₂] using h
  -- γ: (m₁+m₂)/r ≤ T
  have hc : ∀ f ∈ F₁ ∪ F₂, (r / (1 + α₂) ≤ (edgeSize (f : Set (Fin n)) : ℝ)) := by
    intro f hf
    rcases (Finset.mem_union.mp hf) with hf₁ | hf₂
    · have hb := hbig f hf₁
      have hdiv : r / (1 + α₂) ≤ r := div_le_self (le_of_lt hr) (by nlinarith)
      have hmono : r ≤ (1 + α₁) * r := by
        have hαr : 0 ≤ α₁ * r := mul_nonneg (le_of_lt hα₁) (le_of_lt hr)
        nlinarith
      exact (hdiv.trans hmono).trans hb
    · have hmed' := hmed f hf₂
      dsimp [r] at hmed' ⊢
      exact hmed'
  have hgamma := fwdnbr_gamma (n := n) e α₂ F₁ F₂ h₁α₂ (by simpa [r] using hr1α2) hr hdisj hc
    (by
      have hu := fwdnbr_union_upper (n := n) hlin e F₁ F₂ hF₁ hF₂
      exact hu.trans (by
        have hle2 : (edgeSize (e : Set (Fin n)) : ℝ) * ((n : ℝ) - (edgeSize (e : Set (Fin n)) : ℝ)) ≤
            (edgeSize (e : Set (Fin n)) : ℝ) * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith
        simpa [r] using hle2))
  -- algebra: subtract (m₁+m₂), use 1−1/(1+α₂) ≤ α₂ and the m₂ bound from γ
  let T : ℝ := (1 + α₂) * (n : ℝ) / (r - 1 - α₂)
  let Q : ℝ := (1 + α₂) * (1 + α₂ * r) / (r - 1 - α₂)
  let c : ℝ := 1 - 1 / (1 + α₂)
  -- hi' with RHS n + T
  have hiT : (1 + α₁) * m₁ + m₂ / (1 + α₂) ≤ (n : ℝ) + T := by
    simpa [T] using hi'
  -- X = (m₁+m₂) + α₁m₁ − c·m₂
  have hXeq : (1 + α₁) * m₁ + m₂ / (1 + α₂) = (m₁ + m₂) + α₁ * m₁ - c * m₂ := by
    dsimp [c]
    ring
  have hlow : (1 - τ) * (n : ℝ) + α₁ * m₁ - c * m₂ ≤ (n : ℝ) + T := by
    have hsubst : (1 - τ) * (n : ℝ) + α₁ * m₁ - c * m₂ ≤ (m₁ + m₂) + α₁ * m₁ - c * m₂ := by
      dsimp [m₁, m₂]
      nlinarith [hbigsum]
    have hX : (m₁ + m₂) + α₁ * m₁ - c * m₂ ≤ (n : ℝ) + T := by
      rw [← hXeq]
      exact hiT
    exact hsubst.trans hX
  have hA : α₁ * m₁ ≤ τ * (n : ℝ) + T + c * m₂ := by
    nlinarith [hlow]
  have hcα : c ≤ α₂ := one_sub_inv_le (hα₂ := hα₂) (h1α2 := h₁α₂)
  have hcαm : c * m₂ ≤ α₂ * m₂ := mul_le_mul_of_nonneg_right hcα hm2
  have hA2 : α₁ * m₁ ≤ τ * (n : ℝ) + T + α₂ * m₂ := by
    nlinarith [hA, hcαm]
  -- γ-based m₂ bound: m₂ ≤ T·r
  have hgr : (m₁ + m₂) / r ≤ T := by
    dsimp [T, r, m₁, m₂]
    exact hgamma
  have hM : m₁ + m₂ ≤ T * r := by
    have h' := mul_le_mul_of_nonneg_right hgr (le_of_lt hr)
    calc
      m₁ + m₂ = ((m₁ + m₂) / r) * r := (div_mul_cancel₀ (m₁ + m₂) hr.ne').symm
      _ ≤ T * r := h'
  have hm2le : m₂ ≤ T * r := by
    have : m₂ ≤ m₁ + m₂ := by nlinarith [hm1]
    exact this.trans hM
  have hα2m2 : α₂ * m₂ ≤ α₂ * (T * r) := mul_le_mul_of_nonneg_left hm2le hα₂
  have hA3 : α₁ * m₁ ≤ τ * (n : ℝ) + T + α₂ * (T * r) := by
    nlinarith [hA2, hα2m2]
  -- T + α₂·(T·r) = n·Q
  have hTQ : T + α₂ * (T * r) = (n : ℝ) * Q := by
    dsimp [T, Q]
    field_simp [hr1α2.ne']
  have hA4 : α₁ * m₁ ≤ τ * (n : ℝ) + (n : ℝ) * Q := by
    nlinarith [hA3, hTQ]
  have hA5 : α₁ * m₁ ≤ (n : ℝ) * (τ + Q) := by
    nlinarith [hA4]
  have hfin1 : m₁ ≤ ((n : ℝ) * (τ + Q)) / α₁ := by
    apply le_of_mul_le_mul_right _ hα₁
    calc
      m₁ * α₁ = α₁ * m₁ := by ring
      _ ≤ (n : ℝ) * (τ + Q) := hA5
      _ = (((n : ℝ) * (τ + Q)) / α₁) * α₁ := by rw [div_mul_cancel₀ _ hα₁.ne']
  have hEqR : ((n : ℝ) * (τ + Q)) / α₁ = (τ + Q) * (n : ℝ) / α₁ := by ring
  have hfin : m₁ ≤ (τ + Q) * (n : ℝ) / α₁ := by
    rwa [← hEqR]
  simpa [r, Q, m₁] using hfin
