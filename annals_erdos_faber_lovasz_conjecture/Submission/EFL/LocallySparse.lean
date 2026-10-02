import Submission.EFL.LineGraph
import Submission.EFL.NeighbourSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Colouring locally sparse line graphs (paper §6.2)

This module isolates the part of Theorem 6.7's proof that reduces the two
deep colouring results for *locally sparse graphs* to concrete counting
statements about linear hypergraphs.

The two deep inputs are the paper's

* Theorem 6.4 (Molloy and Reed [45]): a graph of maximum degree `Δ` all of
  whose neighbourhoods span at most `(1−ζ)Δ²/2` edges has chromatic number
  at most `(1−ζ/e⁶)Δ` (for `1/Δ ≪ ζ`),
* Theorem 6.6 (Alon, Krivelevich and Sudakov [4]): a graph of maximum degree
  at most `Δ` all of whose neighbourhoods span at most `ζΔ²` edges has
  chromatic number at most `KΔ/log(1/ζ)` (for `1/K ≪ 1`).

They are stated here as the propositions `MolloyReedStatement` and
`AKSStatement` on `SimpleGraph`; `Corollary 6.5`/`Corollary 6.7` of the
paper are then *proved* from them using only elementary counting in the
line graph of a linear hypergraph (`card_neighbourEdges_le`,
`card_commonNeighbours_le` below).

## Main definitions / results

* `nbrEdges G v` — the number of edges of `G` spanned by the neighbourhood
  of `v` (the `e(G[N(v)])` of the local sparsity hypotheses).
* `MolloyReedStatement`, `AKSStatement` — the two deep inputs.
* `card_neighbourEdges_le` — the maximum degree of the line graph of a
  linear hypergraph (`|N(e)| ≤ |e|(n−|e|)/(r−1)`); with all edge sizes in
  `[r, (1+α)r]` this is the paper's `Δ(L) ≤ (1+α)r(n−r)/(r−1)`.
* `card_commonNeighbours_le` — the codegree bound
  `|N(e) ∩ N(f)| ≤ n/(r−1) + |e||f|` for intersecting `e ≠ f` of size `≥ r`
  (the paper's `n/(r−1) + (1+α)²r²` when sizes are at most `(1+α)r`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

/-! ## The two deep inputs (paper Theorems 6.4 and 6.6) -/

/-- The number of edges of the graph `G` spanned by the neighbourhood of `v`,
i.e. the paper's `e(G[N(v)])`. -/
def nbrEdges {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  (G.induce (G.neighborSet v)).edgeFinset.card

/-- **Molloy–Reed** (paper Theorem 6.4), as an input statement: there is a
threshold function `Δ₀` such that for `0 < ζ ≤ 1` and a graph `G` of maximum
degree at least `Δ₀ ζ` all of whose neighbourhoods span at most
`(1−ζ)·Δ(G)²/2` edges, `G` is colourable with at most `(1−ζ/e⁶)·Δ(G)`
colours.

The statement also records that the threshold `Δ₀ ζ` is bounded by a
polynomial in `1/ζ` (the content of the literature's `0 < 1/Δ ≪ ζ ≤ 1`
convention): there are `C > 0` and `m : ℕ` with `Δ₀ ζ ≤ C/ζ^m`.  This is the
form in which the threshold is actually consumed (see
`case21_margin_Δthr`), where `ζ` is the instance-dependent
`1 − r₃/√n ≥ δ` and `n` has to dominate the threshold. -/
def MolloyReedStatement : Prop :=
  ∃ Δ₀ : ℝ → ℝ, (∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → 0 < Δ₀ ζ) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ m : ℕ, ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → Δ₀ ζ ≤ C / ζ ^ m) ∧
    (∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 →
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ),
      Δ₀ ζ ≤ Δ →
      (G.maxDegree : ℝ) ≤ Δ →
      (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ) * Δ ^ 2 / 2) →
      ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ / Real.exp 6) * Δ ∧ G.Colorable k)

/-- **Alon–Krivelevich–Sudakov** (paper Theorem 6.6), as an input statement:
there are a constant `K` and a `ζ₀ > 0` such that for `0 < ζ ≤ ζ₀` and a
graph `G` of maximum degree at least `Δ₀` all of whose neighbourhoods span
at most `ζ·Δ(G)²` edges, `G` is colourable with at most
`K·Δ(G)/log(1/ζ)` colours. -/
def AKSStatement : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∃ ζ₀ : ℝ, 0 < ζ₀ ∧ ∀ ζ : ℝ, 0 < ζ → ζ ≤ ζ₀ →
    ∃ Δ₀ : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
      (Δ : ℝ), Δ₀ ≤ Δ →
      (G.maxDegree : ℝ) ≤ Δ →
      (∀ v : V, (nbrEdges G v : ℝ) ≤ ζ * Δ ^ 2) →
      ∃ k : ℕ, (k : ℝ) ≤ K * Δ / Real.log (1 / ζ) ∧ G.Colorable k

/-! ## Counting the degree of the line graph

`|N(e)| ≤ |e|(n−|e|)/(r−1)` when all edges meeting `e` have size at least
`r ≥ 2`: this is the paper's `Δ(L) ≤ (1+α)r(n−r)/(r−1)` (there `|e| ≤
(1+α)r` and `|e| ≥ r`, so `|e|(n−|e|) ≤ (1+α)r(n−r)`). -/

/-- **Degree bound for the line graph**: if every neighbour of the edge `e`
in the linear hypergraph `𝓗` has size at least `r ≥ 2`, then `e` has at
most `|e|(n−|e|)/(r−1)` neighbours. -/
theorem card_neighbourEdges_le {n r : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (e : 𝓗) (hr : 2 ≤ r)
    (hsize : ∀ f : 𝓗, f ∈ neighbourEdges 𝓗 e → r ≤ edgeSize (f : Set (Fin n))) :
    (neighbourEdges 𝓗 e).card ≤
      (edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n)))) / (r - 1) := by
  exact card_neighbour_family_le hlin e (neighbourEdges 𝓗 e) (fun f hf => hf) r hr hsize


/-! ## The codegree bound of the line graph

For two intersecting edges `e ≠ f` of a linear hypergraph all of whose
edges have size at least `r`, the common neighbours of `e` and `f` split
into

* `N₁ = {g ∈ N(e)∩N(f) : g∩e = g∩f}` — these `g` all pass through the
  common vertex `v` of `e` and `f`, and their leftovers `g∖{v}` are
  pairwise disjoint subsets of size `≥ r−1`, so `|N₁| ≤ n/(r−1)`;
* `N₂` — the rest, each `g` determined by the unordered pair of the vertex
  of `g∩e` and the vertex of `g∩f` (distinct, else `g ∈ N₁`), so
  `|N₂| ≤ |e|·|f|`.

This is the estimate `|N(e)∩N(f)| ≤ n/(r−1) + (1+α)²r²` used in the proofs
of Corollaries 6.5 and 6.7 to check local sparsity of the line graph. -/

/-- **Codegree bound for the line graph**: two intersecting edges `e ≠ f`
of a linear hypergraph whose edges all have size at least `r ≥ 2` have at
most `n/(r−1) + |e|·|f|` common neighbours. -/
theorem card_commonNeighbours_le {n r : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (hr : 2 ≤ r) (hsize : ∀ g : 𝓗, r ≤ edgeSize (g : Set (Fin n)))
    (e f : 𝓗) (hne : e ≠ f)
    (hint : ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty) :
    (neighbourEdges 𝓗 e ∩ neighbourEdges 𝓗 f).card ≤
      n / (r - 1) + edgeSize (e : Set (Fin n)) * edgeSize (f : Set (Fin n)) := by
  classical
  have hn2 : 2 ≤ n := by
    have h1 : r ≤ edgeSize (e : Set (Fin n)) := hsize e
    have h2 : edgeSize (e : Set (Fin n)) ≤ n := by
      have := Finset.card_le_univ (verts (e : Set (Fin n)))
      simpa [edgeSize, Fintype.card_fin] using this
    omega
  haveI : NeZero n := ⟨by omega⟩
  have hneSet : (e : Set (Fin n)) ≠ (f : Set (Fin n)) := by
    intro hEq
    exact hne (Subtype.ext hEq)
  have hsubEF : ((e : Set (Fin n)) ∩ (f : Set (Fin n))).Subsingleton :=
    hlin e.2 f.2 hneSet
  let v : Fin n := commonVertex (a := (e : Set (Fin n))) (b := (f : Set (Fin n))) hint
  have hv_e : v ∈ (e : Set (Fin n)) :=
    commonVertex_mem_left (a := (e : Set (Fin n))) (b := (f : Set (Fin n))) hint
  have hv_f : v ∈ (f : Set (Fin n)) :=
    commonVertex_mem_right (a := (e : Set (Fin n))) (b := (f : Set (Fin n))) hint
  have hinter_eq : (e : Set (Fin n)) ∩ (f : Set (Fin n)) = ({v} : Set (Fin n)) := by
    ext x
    constructor
    · intro hx
      have hxv : x = v := hsubEF hx ⟨hv_e, hv_f⟩
      rw [Set.mem_singleton_iff]
      exact hxv
    · intro hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact ⟨hv_e, hv_f⟩
  let S : Finset 𝓗 := neighbourEdges 𝓗 e ∩ neighbourEdges 𝓗 f
  let P : 𝓗 → Prop := fun g =>
    ((g : Set (Fin n)) ∩ (e : Set (Fin n))) = ((g : Set (Fin n)) ∩ (f : Set (Fin n)))
  let N₁ : Finset 𝓗 := S.filter P
  let N₂ : Finset 𝓗 := S.filter (fun g => ¬ P g)
  have memS : ∀ g : 𝓗, g ∈ S ↔ g ∈ neighbourEdges 𝓗 e ∧ g ∈ neighbourEdges 𝓗 f := by
    intro g; simp [S]
  have memN₁ : ∀ g : 𝓗, g ∈ N₁ ↔ g ∈ S ∧ P g := by intro g; simp [N₁]
  have memN₂ : ∀ g : 𝓗, g ∈ N₂ ↔ g ∈ S ∧ ¬ P g := by intro g; simp [N₂]
  have hsplit : S.card = N₁.card + N₂.card := by
    have h := Finset.card_filter_add_card_filter_not (s := S) P
    dsimp [N₁, N₂]
    exact h.symm
  -- N₁: every member contains `v`
  have hv_in : ∀ g ∈ N₁, v ∈ (g : Set (Fin n)) := by
    intro g hg
    obtain ⟨hgS, hP⟩ := (memN₁ g).mp hg
    obtain ⟨hge, hgf⟩ := (memS g).mp hgS
    have hintE : (((g : Set (Fin n))) ∩ (e : Set (Fin n))).Nonempty :=
      (mem_neighbourEdges 𝓗 e g).mp hge |>.2
    let uu : Fin n := commonVertex (a := (g : Set (Fin n))) (b := (e : Set (Fin n))) hintE
    have huu_g : uu ∈ (g : Set (Fin n)) :=
      commonVertex_mem_left (a := (g : Set (Fin n))) (b := (e : Set (Fin n))) hintE
    have huu_e : uu ∈ (e : Set (Fin n)) :=
      commonVertex_mem_right (a := (g : Set (Fin n))) (b := (e : Set (Fin n))) hintE
    have huu_gf : uu ∈ (g : Set (Fin n)) ∩ (f : Set (Fin n)) := by
      rw [← hP]
      exact ⟨huu_g, huu_e⟩
    have huu_ef : uu ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)) := ⟨huu_e, huu_gf.2⟩
    rw [hinter_eq] at huu_ef
    have huv : uu = v := Set.mem_singleton_iff.mp huu_ef
    rw [← huv]
    exact huu_g
  let L : 𝓗 → Finset (Fin n) := fun g => (verts (g : Set (Fin n))).erase v
  have hpd : (N₁ : Set 𝓗).PairwiseDisjoint L := by
    intro g₁ hg₁ g₂ hg₂ hne'
    change Disjoint (L g₁) (L g₂)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hx₁' := Finset.mem_erase.mp hx₁
    have hx₂' := Finset.mem_erase.mp hx₂
    have hxg₁ : x ∈ (g₁ : Set (Fin n)) := (mem_verts _ x).mp hx₁'.2
    have hxg₂ : x ∈ (g₂ : Set (Fin n)) := (mem_verts _ x).mp hx₂'.2
    have hv₁ : v ∈ (g₁ : Set (Fin n)) := hv_in g₁ hg₁
    have hv₂ : v ∈ (g₂ : Set (Fin n)) := hv_in g₂ hg₂
    have hneSet' : (g₁ : Set (Fin n)) ≠ (g₂ : Set (Fin n)) := by
      intro hEq
      exact hne' (Subtype.ext hEq)
    exact hne' (Subtype.ext (IsLinear.eq_of_mem_pair (𝓗 := 𝓗) hlin g₁.2 g₂.2 hx₁'.1
      hxg₁ hv₁ hxg₂ hv₂))
  let D : Finset (Fin n) := N₁.disjiUnion L hpd
  have hDcard : D.card = N₁.sum (fun g : 𝓗 => (L g).card) :=
    Finset.card_disjiUnion N₁ L hpd
  have hDsub : D ⊆ (Finset.univ : Finset (Fin n)).erase v := by
    intro x hxD
    rw [Finset.mem_disjiUnion] at hxD
    obtain ⟨g, _hg, hxL⟩ := hxD
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hxL).1, Finset.mem_univ x⟩
  have hDle : D.card ≤ n - 1 := by
    have hle := Finset.card_le_card hDsub
    have hc : ((Finset.univ : Finset (Fin n)).erase v).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    rwa [hc] at hle
  have hterm : ∀ g ∈ N₁, r - 1 ≤ (L g).card := by
    intro g hg
    have h1 : v ∈ verts (g : Set (Fin n)) := by
      rw [mem_verts]
      exact hv_in g hg
    have hcard : (L g).card = edgeSize (g : Set (Fin n)) - 1 := by
      dsimp [L, edgeSize]
      rw [Finset.card_erase_of_mem h1]
    rw [hcard]
    have := hsize g
    omega
  have hsum_le : N₁.card * (r - 1) ≤ D.card := by
    rw [hDcard]
    calc N₁.card * (r - 1) = N₁.sum (fun _ : 𝓗 => r - 1) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ N₁.sum (fun g : 𝓗 => (L g).card) := Finset.sum_le_sum hterm
  have hN₁ : N₁.card ≤ n / (r - 1) := by
    have hpos : 0 < r - 1 := by omega
    refine (Nat.le_div_iff_mul_le hpos).mpr ?_
    exact hsum_le.trans (hDle.trans (Nat.sub_le n 1))
  -- N₂: inject into `e × f`
  let u : 𝓗 → Fin n := fun g =>
    if h : ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty then
      commonVertex (a := (g : Set (Fin n))) (b := (e : Set (Fin n))) h else 0
  let w : 𝓗 → Fin n := fun g =>
    if h : ((g : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty then
      commonVertex (a := (g : Set (Fin n))) (b := (f : Set (Fin n))) h else 0
  let φ : 𝓗 → Fin n × Fin n := fun g => (u g, w g)
  let T : Finset (Fin n × Fin n) := (verts (e : Set (Fin n))) ×ˢ (verts (f : Set (Fin n)))
  have hφinj : Set.InjOn φ (N₂ : Set 𝓗) := by
    intro g₁ hg₁ g₂ hg₂ hEq
    obtain ⟨hg₁S, hP₁⟩ := (memN₂ g₁).mp hg₁
    obtain ⟨hg₂S, hP₂⟩ := (memN₂ g₂).mp hg₂
    obtain ⟨hg₁e, hg₁f⟩ := (memS g₁).mp hg₁S
    obtain ⟨hg₂e, hg₂f⟩ := (memS g₂).mp hg₂S
    have hne₁e : g₁ ≠ e := (mem_neighbourEdges 𝓗 e g₁).mp hg₁e |>.1
    have hne₁f : g₁ ≠ f := (mem_neighbourEdges 𝓗 f g₁).mp hg₁f |>.1
    have hintE₁ : ((g₁ : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty :=
      (mem_neighbourEdges 𝓗 e g₁).mp hg₁e |>.2
    have hintF₁ : ((g₁ : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty :=
      (mem_neighbourEdges 𝓗 f g₁).mp hg₁f |>.2
    have hintE₂ : ((g₂ : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty :=
      (mem_neighbourEdges 𝓗 e g₂).mp hg₂e |>.2
    have hintF₂ : ((g₂ : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty :=
      (mem_neighbourEdges 𝓗 f g₂).mp hg₂f |>.2
    have hu₁ : u g₁ = commonVertex (a := (g₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₁ := by
      simp [u, hintE₁]
    have hu₂ : u g₂ = commonVertex (a := (g₂ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₂ := by
      simp [u, hintE₂]
    have hw₁ : w g₁ = commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁ := by
      simp [w, hintF₁]
    have hw₂ : w g₂ = commonVertex (a := (g₂ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₂ := by
      simp [w, hintF₂]
    have hufst : commonVertex (a := (g₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₁ =
        commonVertex (a := (g₂ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₂ := by
      rw [← hu₁, ← hu₂]
      exact congrArg Prod.fst hEq
    have hwsnd : commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁ =
        commonVertex (a := (g₂ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₂ := by
      rw [← hw₁, ← hw₂]
      exact congrArg Prod.snd hEq
    have hu₁g : commonVertex (a := (g₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₁
        ∈ (g₁ : Set (Fin n)) := commonVertex_mem_left hintE₁
    have hu₁e : commonVertex (a := (g₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₁
        ∈ (e : Set (Fin n)) := commonVertex_mem_right hintE₁
    have hw₁g : commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁
        ∈ (g₁ : Set (Fin n)) := commonVertex_mem_left hintF₁
    have hw₁f : commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁
        ∈ (f : Set (Fin n)) := commonVertex_mem_right hintF₁
    have huw_ne : commonVertex (a := (g₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₁ ≠
        commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁ := by
      intro hEqv
      have hmem : commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁
          ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)) := by
        refine ⟨?_, hw₁f⟩
        rw [← hEqv]
        exact hu₁e
      have hxv : commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁ = v := by
        rw [hinter_eq] at hmem
        exact Set.mem_singleton_iff.mp hmem
      have hve : v ∈ (g₁ : Set (Fin n)) ∩ (e : Set (Fin n)) := by
        refine ⟨?_, hv_e⟩
        rw [← hxv]
        exact hw₁g
      have hvf : v ∈ (g₁ : Set (Fin n)) ∩ (f : Set (Fin n)) := by
        refine ⟨?_, hv_f⟩
        rw [← hxv]
        exact hw₁g
      have hsub₁e : ((g₁ : Set (Fin n)) ∩ (e : Set (Fin n))).Subsingleton :=
        hlin g₁.2 e.2 (by intro hE; exact hne₁e (Subtype.ext hE))
      have hsub₁f : ((g₁ : Set (Fin n)) ∩ (f : Set (Fin n))).Subsingleton :=
        hlin g₁.2 f.2 (by intro hE; exact hne₁f (Subtype.ext hE))
      have heq₁ : (g₁ : Set (Fin n)) ∩ (e : Set (Fin n)) = ({v} : Set (Fin n)) := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_singleton_iff]
          exact hsub₁e hx hve
        · intro hx
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact hve
      have heq₂ : (g₁ : Set (Fin n)) ∩ (f : Set (Fin n)) = ({v} : Set (Fin n)) := by
        ext x
        constructor
        · intro hx
          rw [Set.mem_singleton_iff]
          exact hsub₁f hx hvf
        · intro hx
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact hvf
      exact hP₁ (by show (g₁ : Set (Fin n)) ∩ (e : Set (Fin n)) =
          (g₁ : Set (Fin n)) ∩ (f : Set (Fin n)); rw [heq₁, heq₂])
    have hg₂u : commonVertex (a := (g₁ : Set (Fin n))) (b := (e : Set (Fin n))) hintE₁
        ∈ (g₂ : Set (Fin n)) := by
      rw [hufst]
      exact commonVertex_mem_left hintE₂
    have hg₂w : commonVertex (a := (g₁ : Set (Fin n))) (b := (f : Set (Fin n))) hintF₁
        ∈ (g₂ : Set (Fin n)) := by
      rw [hwsnd]
      exact commonVertex_mem_left hintF₂
    exact Subtype.ext (IsLinear.eq_of_mem_pair (𝓗 := 𝓗) hlin g₁.2 g₂.2 huw_ne hu₁g hw₁g hg₂u hg₂w)
  have hφsub : N₂.image φ ⊆ T := by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hgS, _⟩ := (memN₂ g).mp hg
    obtain ⟨hge, hgf⟩ := (memS g).mp hgS
    have hintE : ((g : Set (Fin n)) ∩ (e : Set (Fin n))).Nonempty :=
      (mem_neighbourEdges 𝓗 e g).mp hge |>.2
    have hintF : ((g : Set (Fin n)) ∩ (f : Set (Fin n))).Nonempty :=
      (mem_neighbourEdges 𝓗 f g).mp hgf |>.2
    have hu : u g = commonVertex (a := (g : Set (Fin n))) (b := (e : Set (Fin n))) hintE := by
      simp [u, hintE]
    have hw : w g = commonVertex (a := (g : Set (Fin n))) (b := (f : Set (Fin n))) hintF := by
      simp [w, hintF]
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · show u g ∈ verts (e : Set (Fin n))
      rw [hu, mem_verts]
      exact commonVertex_mem_right hintE
    · show w g ∈ verts (f : Set (Fin n))
      rw [hw, mem_verts]
      exact commonVertex_mem_right hintF
  have hN₂ : N₂.card ≤ edgeSize (e : Set (Fin n)) * edgeSize (f : Set (Fin n)) := by
    have h1 : N₂.card = (N₂.image φ).card := (Finset.card_image_of_injOn hφinj).symm
    have h2 : (N₂.image φ).card ≤ T.card := Finset.card_le_card hφsub
    have h3 : T.card = edgeSize (e : Set (Fin n)) * edgeSize (f : Set (Fin n)) := by
      dsimp [T, edgeSize]
      rw [Finset.card_product]
    calc N₂.card = (N₂.image φ).card := h1
      _ ≤ T.card := h2
      _ = edgeSize (e : Set (Fin n)) * edgeSize (f : Set (Fin n)) := h3
  rw [hsplit]
  exact Nat.add_le_add hN₁ hN₂


/-! ## Bridging the counting to the line graph

The two counting statements above are converted into the graph-theoretic
form consumed by `MolloyReedStatement`/`AKSStatement`: the degree of the
line graph, and the number of edges spanned by the neighbourhood of a
vertex of the line graph.

`sum_degree_lineGraph_le` is the degree-sum identity for the subgraph of
the line graph induced by the neighbourhood of an edge `e` together with
the per-vertex codegree bound: the `2·e(L[N(e)]) ≤ Δ(L)·codeg` step of the
proofs of Corollaries 6.5 and 6.7. -/

variable {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]

local instance instLineGraphAdj : DecidableRel (𝓗.lineGraph).Adj := Classical.decRel _

/-- The neighbourhood of a vertex of the line graph is exactly the family of
edges of `𝓗` meeting the corresponding edge. -/
lemma lineGraph_neighborFinset (u : 𝓗) :
    (𝓗.lineGraph).neighborFinset u = neighbourEdges 𝓗 u := by
  ext f
  rw [SimpleGraph.mem_neighborFinset]
  simp only [neighbourEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  show (𝓗.lineGraph).Adj u f ↔ f ≠ u ∧ (((f : Set (Fin n))) ∩ ((u : Set (Fin n)))).Nonempty
  constructor
  · intro h
    change u ≠ f ∧ (((u : Set (Fin n))) ∩ ((f : Set (Fin n)))).Nonempty at h
    exact ⟨h.1.symm, by simpa [Set.inter_comm] using h.2⟩
  · intro h
    change u ≠ f ∧ (((u : Set (Fin n))) ∩ ((f : Set (Fin n)))).Nonempty
    exact ⟨h.1.symm, by simpa [Set.inter_comm] using h.2⟩

/-- the number of vertices of the line graph in the neighbourhood of `e` is
the degree of `e` in `𝓗` -/
lemma card_neighborSet_lineGraph (e : 𝓗) :
    Fintype.card ↥((𝓗.lineGraph).neighborSet e) = (neighbourEdges 𝓗 e).card := by
  rw [Set.fintypeCard_eq_ncard, Set.ncard_eq_toFinset_card', ← SimpleGraph.neighborFinset_def,
    lineGraph_neighborFinset]

/-- degree in the induced subgraph of the neighbour set -/
lemma induced_degree_eq (G : SimpleGraph 𝓗) [DecidableRel G.Adj] (v : 𝓗)
    (u : ↥(G.neighborSet v)) :
    (G.induce (G.neighborSet v)).degree u
      = (G.neighborFinset (u : 𝓗) ∩ (G.neighborSet v).toFinset).card := by
  rw [SimpleGraph.degree]
  rw [← Finset.card_map (f := Function.Embedding.subtype (· ∈ G.neighborSet v))]
  rw [G.map_neighborFinset_induce (s := G.neighborSet v) u]

/-- **Degree-sum bound**: if every edge `f` meeting `e` shares at most `C`
common neighbours with `e`, then the sum of the degrees of the neighbours of
`e` in the induced subgraph on `N_L(e)` is at most `|N(e)|·C`.  Doubling via
the handshaking lemma bounds `2·e(L[N(e)])`. -/
theorem sum_degree_lineGraph_le (e : 𝓗) (C : ℕ)
    (hC : ∀ f : 𝓗, f ∈ neighbourEdges 𝓗 e →
      (((𝓗.lineGraph).neighborFinset f) ∩ ((𝓗.lineGraph).neighborFinset e)).card ≤ C) :
    (∑ u : ↥((𝓗.lineGraph).neighborSet e),
        (((𝓗.lineGraph).induce ((𝓗.lineGraph).neighborSet e)).degree u))
      ≤ (neighbourEdges 𝓗 e).card * C := by
  classical
  have hdeg : ∀ u : ↥((𝓗.lineGraph).neighborSet e),
      (((𝓗.lineGraph).induce ((𝓗.lineGraph).neighborSet e)).degree u)
        = (((𝓗.lineGraph).neighborFinset (u : 𝓗))
          ∩ ((𝓗.lineGraph).neighborSet e).toFinset).card :=
    fun u => induced_degree_eq _ _ u
  have hbound : ∀ u : ↥((𝓗.lineGraph).neighborSet e),
      (((𝓗.lineGraph).neighborFinset (u : 𝓗))
        ∩ ((𝓗.lineGraph).neighborSet e).toFinset).card ≤ C := by
    intro u
    have hu : (u : 𝓗) ∈ neighbourEdges 𝓗 e := by
      have hmem : (u : 𝓗) ∈ (𝓗.lineGraph).neighborSet e := u.2
      change (𝓗.lineGraph).Adj e (u : 𝓗) at hmem
      rw [← SimpleGraph.mem_neighborFinset] at hmem
      rwa [lineGraph_neighborFinset] at hmem
    have h := hC (u : 𝓗) hu
    simp only [lineGraph_neighborFinset, ← SimpleGraph.neighborFinset_def] at h ⊢
    exact h
  calc (∑ u : ↥((𝓗.lineGraph).neighborSet e),
        (((𝓗.lineGraph).induce ((𝓗.lineGraph).neighborSet e)).degree u))
      = ∑ u : ↥((𝓗.lineGraph).neighborSet e),
        (((𝓗.lineGraph).neighborFinset (u : 𝓗))
          ∩ ((𝓗.lineGraph).neighborSet e).toFinset).card :=
          Finset.sum_congr rfl (fun u _ => hdeg u)
    _ ≤ ∑ _u : ↥((𝓗.lineGraph).neighborSet e), C :=
          Finset.sum_le_sum (fun u _ => hbound u)
    _ = Fintype.card ↥((𝓗.lineGraph).neighborSet e) * C := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    _ = (neighbourEdges 𝓗 e).card * C := by rw [card_neighborSet_lineGraph]

/-- **Local sparsity of the line graph**: if every edge of `𝓗` has size at
least `r ≥ 2` and at most `B`, and every neighbour of `e` shares at most `C`
common neighbours with `e`, then the neighbourhood of `e` in the line graph
spans at most `|N(e)|·C/2` edges — the paper's
`e(L[N(e)]) ≤ Δ(L)·(1+α)²r²/2` (with `C := n/(r−1) + B²`). -/
theorem nbrEdges_lineGraph_le_sum (e : 𝓗) (C : ℕ)
    (hC : ∀ f : 𝓗, f ∈ neighbourEdges 𝓗 e →
      (((𝓗.lineGraph).neighborFinset f) ∩ ((𝓗.lineGraph).neighborFinset e)).card ≤ C) :
    (nbrEdges (𝓗.lineGraph) e : ℝ)
      ≤ ((neighbourEdges 𝓗 e).card : ℝ) * (C : ℝ) / 2 := by
  classical
  have hsum := sum_degree_lineGraph_le (𝓗 := 𝓗) e C hC
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at hsum
  have hle : 2 * nbrEdges (𝓗.lineGraph) e ≤ (neighbourEdges 𝓗 e).card * C := hsum
  have hle' : (2 : ℝ) * (nbrEdges (𝓗.lineGraph) e : ℝ)
      ≤ ((neighbourEdges 𝓗 e).card : ℝ) * (C : ℝ) := by exact_mod_cast hle
  linarith

/-- **Local sparsity of the line graph, explicit form**: for a linear
hypergraph all of whose edges have size in `[r, B]`, the neighbourhood of
any edge `e` of the line graph spans at most
`|N(e)|·(n/(r−1) + B²)/2` edges. -/
theorem nbrEdges_lineGraph_le {r B : ℕ} (e : 𝓗)
    (hlin : 𝓗.IsLinear) (hr : 2 ≤ r)
    (hsize_ge : ∀ g : 𝓗, r ≤ edgeSize (g : Set (Fin n)))
    (hsize_le : ∀ g : 𝓗, edgeSize (g : Set (Fin n)) ≤ B) :
    (nbrEdges (𝓗.lineGraph) e : ℝ)
      ≤ ((neighbourEdges 𝓗 e).card : ℝ)
        * ((n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2) / 2 := by
  classical
  have hC : ∀ f : 𝓗, f ∈ neighbourEdges 𝓗 e →
      (((𝓗.lineGraph).neighborFinset f) ∩ ((𝓗.lineGraph).neighborFinset e)).card
        ≤ n / (r - 1) + B * B := by
    intro f hf
    have hfe := (mem_neighbourEdges 𝓗 e f).mp hf
    have h := card_commonNeighbours_le (𝓗 := 𝓗) hlin hr hsize_ge f e hfe.1 hfe.2
    rw [lineGraph_neighborFinset, lineGraph_neighborFinset]
    refine h.trans ?_
    exact Nat.add_le_add_left (Nat.mul_le_mul (hsize_le f) (hsize_le e)) (n / (r - 1))
  have hmain := nbrEdges_lineGraph_le_sum (𝓗 := 𝓗) e (n / (r - 1) + B * B) hC
  have hCbound : (((n / (r - 1) + B * B : ℕ)) : ℝ)
      ≤ (n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2 := by
    have h1 : (((n / (r - 1) : ℕ)) : ℝ) ≤ (n : ℝ) / (((r - 1 : ℕ)) : ℝ) := Nat.cast_div_le
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one] at h1
    have h2 : (((n / (r - 1) + B * B : ℕ)) : ℝ)
        = ((n / (r - 1) : ℕ) : ℝ) + (B : ℝ) * (B : ℝ) := by push_cast; ring
    have h3 : ((B : ℝ) * (B : ℝ)) = (B : ℝ) ^ 2 := by ring
    rw [h2, h3]
    linarith
  calc (nbrEdges (𝓗.lineGraph) e : ℝ)
      ≤ ((neighbourEdges 𝓗 e).card : ℝ) * (((n / (r - 1) + B * B : ℕ)) : ℝ) / 2 := hmain
    _ ≤ ((neighbourEdges 𝓗 e).card : ℝ)
        * ((n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2) / 2 := by
        refine div_le_div_of_nonneg_right ?_ (by norm_num)
        exact mul_le_mul_of_nonneg_left hCbound (by positivity)

/-- **Maximum degree of the line graph**: for a linear hypergraph whose edges
all have size in `[r, B]` with `r ≤ n`, the maximum degree of the line graph
is at most `B·(n − r)/(r − 1)` (the paper's
`Δ(L) ≤ (1+α)r(n−r)/(r−1)`). -/
theorem lineGraph_maxDegree_le {r B : ℕ} (hrn : r ≤ n)
    (hlin : 𝓗.IsLinear) (hr : 2 ≤ r)
    (hsize_ge : ∀ g : 𝓗, r ≤ edgeSize (g : Set (Fin n)))
    (hsize_le : ∀ g : 𝓗, edgeSize (g : Set (Fin n)) ≤ B) :
    (((𝓗.lineGraph).maxDegree : ℕ) : ℝ)
      ≤ (B : ℝ) * ((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1) := by
  classical
  have hdeg : ∀ u : 𝓗, (𝓗.lineGraph).degree u ≤ B * (n - r) / (r - 1) := by
    intro u
    have h1 : (𝓗.lineGraph).degree u ≤
        edgeSize (u : Set (Fin n)) * (n - edgeSize (u : Set (Fin n))) / (r - 1) := by
      rw [SimpleGraph.degree, lineGraph_neighborFinset]
      exact card_neighbourEdges_le (𝓗 := 𝓗) hlin u hr (fun f _ => hsize_ge f)
    have hle1 : edgeSize (u : Set (Fin n)) ≤ B := hsize_le u
    have hle2 : n - edgeSize (u : Set (Fin n)) ≤ n - r := Nat.sub_le_sub_left (hsize_ge u) n
    have hmul : edgeSize (u : Set (Fin n)) * (n - edgeSize (u : Set (Fin n)))
        ≤ B * (n - r) := Nat.mul_le_mul hle1 hle2
    exact h1.trans (Nat.div_le_div_right hmul)
  have hmax : (𝓗.lineGraph).maxDegree ≤ B * (n - r) / (r - 1) :=
    SimpleGraph.maxDegree_le_of_forall_degree_le (G := 𝓗.lineGraph) (B * (n - r) / (r - 1)) hdeg
  have hcast : (((B * (n - r) / (r - 1) : ℕ)) : ℝ)
      ≤ (B : ℝ) * ((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1) := by
    have h1 : (((B * (n - r) / (r - 1) : ℕ)) : ℝ)
        ≤ (((B * (n - r) : ℕ)) : ℝ) / ((((r - 1 : ℕ))) : ℝ) := Nat.cast_div_le
    have h2 : (((B * (n - r) : ℕ)) : ℝ) = (B : ℝ) * ((n : ℝ) - (r : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_sub hrn]
    have h3 : (((r - 1 : ℕ)) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
    rwa [h2, h3] at h1
  exact (Nat.cast_le.mpr hmax).trans hcast


/-! ## Corollary 6.5 (reduction to Molloy–Reed)

The paper's Corollary 6.5: for a linear hypergraph on `n` vertices all of
whose edges have size in `[r, (1+α)r]` with `r ≤ (1−ζ)√n`, the chromatic
index is at most `(1 − ζ/500)n`.  Its proof is the counting of
`nbrEdges_lineGraph_le`/`lineGraph_maxDegree_le` (which check the two
hypotheses of the Molloy–Reed theorem for the *line graph* of the
hypergraph for the parameter `Δ := (1+α)r(n−r)/(r−1)`) followed by the
arithmetic `(1 − 5ζ/(6e⁶))Δ ≤ (1 − ζ/500)n`.

Below, the numerical content (the hierarchy `0 < 1/n₀, 1/r ≪ α ≪ ζ < 1`
together with `r ≤ (1−ζ)√n`, which the paper leaves to the reader) is
isolated in the structure `Corollary65Margins`; the colouring conclusion
`χ′ ≤ (1−ζ/500)n` is then *proved* from Molloy–Reed. -/

/-- The numerical hypotheses of Corollary 6.5 for the (abstract) parameter
`Δ`, the size bounds `r ≤ |e| ≤ B` and `n` vertices.  `Δ` is the paper's
`(1+α)r(n−r)/(r−1)`; the conjuncts are exactly the inequalities used in the
proof. -/
structure Corollary65Margins (Δ₀ : ℝ → ℝ) (ζ : ℝ) (r B n : ℕ) (Δ : ℝ) : Prop where
  hζ0 : 0 < ζ
  hζ1 : ζ ≤ 1
  hr2 : 2 ≤ r
  hrn : r ≤ n
  /-- the maximum degree of the line graph fits under `Δ` -/
  hΔge : (B : ℝ) * ((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1) ≤ Δ
  /-- the Molloy–Reed threshold for the parameter `5ζ/6` is below `Δ` -/
  hΔthr : Δ₀ (5 * ζ / 6) ≤ Δ
  /-- the codegree bound `n/(r−1) + B²` is below `(1−5ζ/6)Δ` -/
  hcodeg : (n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2 ≤ (1 - 5 * ζ / 6) * Δ
  /-- the final arithmetic `(1 − 5ζ/(6e⁶))Δ ≤ (1 − ζ/500)n` -/
  hfinal : (1 - 5 * ζ / (6 * Real.exp 6)) * Δ ≤ (1 - ζ / 500) * (n : ℝ)

/-- **Corollary 6.5** (paper §6.2), reduced to Molloy–Reed: for a linear
hypergraph on `n` vertices whose edges all have size in `[r, B]` with
`B = (1+α)r`, and for the parameter `Δ := (1+α)r(n−r)/(r−1)` satisfying
the numerical hypotheses `Corollary65Margins`, the number of colours
needed is at most `(1 − ζ/500)n`. -/
theorem corollary_6_5 {Δ₀ : ℝ → ℝ}
    (hMR : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {ζ : ℝ} {r B n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] {Δ : ℝ}
    (hm : Corollary65Margins Δ₀ ζ r B n Δ)
    (hlin : 𝓗.IsLinear)
    (hsize_ge : ∀ e : 𝓗, r ≤ edgeSize (e : Set (Fin n)))
    (hsize_le : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ B) :
    ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ / 500) * (n : ℝ) ∧ 𝓗.Colorable k := by
  classical
  have hζ'0 : 0 < 5 * ζ / 6 := by linarith [hm.hζ0]
  have hζ'1 : 5 * ζ / 6 ≤ 1 := by linarith [hm.hζ1]
  have hpos : 0 < 1 - 5 * ζ / 6 := by linarith [hm.hζ1]
  -- the maximum degree of the line graph is at most `Δ`
  have hmax : (((𝓗.lineGraph).maxDegree : ℕ) : ℝ) ≤ Δ :=
    (lineGraph_maxDegree_le (𝓗 := 𝓗) hm.hrn hlin hm.hr2 hsize_ge hsize_le).trans hm.hΔge
  -- the local sparsity hypothesis of Molloy–Reed, for `ζ' = 5ζ/6`
  have hlsp : ∀ v : 𝓗, (nbrEdges (𝓗.lineGraph) v : ℝ)
      ≤ (1 - 5 * ζ / 6) * Δ ^ 2 / 2 := by
    intro e
    have hdeg : (((neighbourEdges 𝓗 e).card : ℕ) : ℝ) ≤ Δ := by
      have h1 : (((𝓗.lineGraph).degree e : ℕ) : ℝ) ≤ ((𝓗.lineGraph).maxDegree : ℕ) := by
        exact_mod_cast SimpleGraph.degree_le_maxDegree (G := 𝓗.lineGraph) e
      have h2 : (((𝓗.lineGraph).degree e : ℕ) : ℝ) ≤ Δ := h1.trans hmax
      simpa [SimpleGraph.degree, lineGraph_neighborFinset] using h2
    have hcodegnonneg : 0 ≤ (n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2 := by
      have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by
        have hr1' : (1 : ℕ) < r := lt_of_lt_of_le (by norm_num) hm.hr2
        have h : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr1'
        linarith
      have h1 : 0 ≤ (n : ℝ) / ((r : ℝ) - 1) := div_nonneg (Nat.cast_nonneg n) (le_of_lt hr1)
      have h2 : 0 ≤ (B : ℝ) ^ 2 := sq_nonneg _
      linarith
    have hΔnonneg : 0 ≤ Δ := by
      have h1 : 0 ≤ (1 - 5 * ζ / 6) * Δ := le_trans hcodegnonneg hm.hcodeg
      nlinarith [h1, hpos]
    have h := nbrEdges_lineGraph_le (𝓗 := 𝓗) (r := r) (B := B) e hlin hm.hr2 hsize_ge hsize_le
    have hstep : ((neighbourEdges 𝓗 e).card : ℝ) * ((n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2)
        ≤ Δ * ((1 - 5 * ζ / 6) * Δ) :=
      mul_le_mul hdeg hm.hcodeg hcodegnonneg hΔnonneg
    calc (nbrEdges (𝓗.lineGraph) e : ℝ)
        ≤ ((neighbourEdges 𝓗 e).card : ℝ) * ((n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2) / 2 := h
      _ ≤ Δ * ((1 - 5 * ζ / 6) * Δ) / 2 := by linarith [hstep]
      _ = (1 - 5 * ζ / 6) * Δ ^ 2 / 2 := by ring
  obtain ⟨k, hk, hcol⟩ := hMR (5 * ζ / 6) hζ'0 hζ'1 𝓗 (𝓗.lineGraph) Δ hm.hΔthr hmax hlsp
  refine ⟨k, ?_, ?_⟩
  · calc (k : ℝ) ≤ (1 - (5 * ζ / 6) / Real.exp 6) * Δ := hk
      _ = (1 - 5 * ζ / (6 * Real.exp 6)) * Δ := by ring
      _ ≤ (1 - ζ / 500) * (n : ℝ) := hm.hfinal
  · exact (Hypergraph.colorable_iff_lineGraph_colorable k 𝓗).mpr hcol


/-! ## Corollary 6.7 (reduction to Alon–Krivelevich–Sudakov)

The paper's Corollary 6.7: an `n`-vertex linear hypergraph whose edge sizes
all lie in `[1/η, η√n]` and are within a factor `1/α` of each other has
chromatic index at most `εn`.  Its proof is the same counting as for
Corollary 6.5 (with `Δ := (r/α)n/(r−1)` and the codegree bound
`n/(1/η−1) + η²n ≤ 2ηn`), followed by the Alon–Krivelevich–Sudakov
theorem with parameter `ζ := ηα` and the arithmetic
`KΔ/log(1/(ηα)) ≤ εn`. -/

/-- The numerical hypotheses of Corollary 6.7 for the (abstract) parameter
`Δ`, the size bounds `r ≤ |e| ≤ B` and `n` vertices. -/
structure Corollary67Margins (Δ₀ : ℝ → ℝ) (K η α ε ζ₀ : ℝ) (r B n : ℕ) (Δ : ℝ) : Prop where
  hη0 : 0 < η
  hα0 : 0 < α
  hε0 : 0 < ε
  hζ₀0 : 0 < ζ₀
  hζζ₀ : η * α ≤ ζ₀
  hr2 : 2 ≤ r
  hrn : r ≤ n
  hΔge : (B : ℝ) * ((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1) ≤ Δ
  hΔthr : Δ₀ (η * α) ≤ Δ
  hcodeg : (n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2 ≤ η * α * Δ
  hfinal : K * Δ / Real.log (1 / (η * α)) ≤ ε * (n : ℝ)

/-- **Corollary 6.7** (paper §6.2), reduced to Alon–Krivelevich–Sudakov: for
a linear hypergraph on `n` vertices whose edges all have size in `[r, B]`
(with `B = r/α`, the paper's `min_e |e| ≥ α max_e |e|`), and for a
parameter `Δ` satisfying the numerical hypotheses `Corollary67Margins`, the
chromatic index is at most `εn`. -/
theorem corollary_6_7 {K : ℝ} {Δ₀ : ℝ → ℝ} {ζ₀ : ℝ}
    (hAKS : ∀ (ζ : ℝ), 0 < ζ → ζ ≤ ζ₀ → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ ζ * Δ ^ 2) →
        ∃ k : ℕ, (k : ℝ) ≤ K * Δ / Real.log (1 / ζ) ∧ G.Colorable k)
    {η α ε : ℝ} {r B n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] {Δ : ℝ}
    (hm : Corollary67Margins Δ₀ K η α ε ζ₀ r B n Δ)
    (hlin : 𝓗.IsLinear)
    (hsize_ge : ∀ e : 𝓗, r ≤ edgeSize (e : Set (Fin n)))
    (hsize_le : ∀ e : 𝓗, edgeSize (e : Set (Fin n)) ≤ B) :
    ∃ k : ℕ, (k : ℝ) ≤ ε * (n : ℝ) ∧ 𝓗.Colorable k := by
  classical
  have hζ0 : 0 < η * α := mul_pos hm.hη0 hm.hα0
  have hζ : η * α ≤ ζ₀ := hm.hζζ₀
  have hcodegnonneg : 0 ≤ (n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2 := by
    have hr1' : (1 : ℕ) < r := lt_of_lt_of_le (by norm_num) hm.hr2
    have h : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr1'
    have hr1 : (0 : ℝ) < (r : ℝ) - 1 := by linarith
    have h1 : 0 ≤ (n : ℝ) / ((r : ℝ) - 1) := div_nonneg (Nat.cast_nonneg n) (le_of_lt hr1)
    have h2 : 0 ≤ (B : ℝ) ^ 2 := sq_nonneg _
    linarith
  have hΔnonneg : 0 ≤ Δ := by
    have h1 : 0 ≤ η * α * Δ := le_trans hcodegnonneg hm.hcodeg
    nlinarith [h1, hζ0]
  have hmax : (((𝓗.lineGraph).maxDegree : ℕ) : ℝ) ≤ Δ :=
    (lineGraph_maxDegree_le (𝓗 := 𝓗) hm.hrn hlin hm.hr2 hsize_ge hsize_le).trans hm.hΔge
  have hlsp : ∀ v : 𝓗, (nbrEdges (𝓗.lineGraph) v : ℝ) ≤ (η * α) * Δ ^ 2 := by
    intro e
    have hdeg : (((neighbourEdges 𝓗 e).card : ℕ) : ℝ) ≤ Δ := by
      have h1 : (((𝓗.lineGraph).degree e : ℕ) : ℝ) ≤ ((𝓗.lineGraph).maxDegree : ℕ) := by
        exact_mod_cast SimpleGraph.degree_le_maxDegree (G := 𝓗.lineGraph) e
      have h2 : (((𝓗.lineGraph).degree e : ℕ) : ℝ) ≤ Δ := h1.trans hmax
      simpa [SimpleGraph.degree, lineGraph_neighborFinset] using h2
    have h := nbrEdges_lineGraph_le (𝓗 := 𝓗) (r := r) (B := B) e hlin hm.hr2 hsize_ge hsize_le
    have hstep : ((neighbourEdges 𝓗 e).card : ℝ) * ((n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2)
        ≤ Δ * (η * α * Δ) :=
      mul_le_mul hdeg hm.hcodeg hcodegnonneg hΔnonneg
    calc (nbrEdges (𝓗.lineGraph) e : ℝ)
        ≤ ((neighbourEdges 𝓗 e).card : ℝ) * ((n : ℝ) / ((r : ℝ) - 1) + (B : ℝ) ^ 2) / 2 := h
      _ ≤ Δ * (η * α * Δ) / 2 := by linarith [hstep]
      _ ≤ (η * α) * Δ ^ 2 := by nlinarith [hΔnonneg, hζ0]
  obtain ⟨k, hk, hcol⟩ := hAKS (η * α) hζ0 hζ 𝓗 (𝓗.lineGraph) Δ hm.hΔthr hmax hlsp
  exact ⟨k, hk.trans hm.hfinal, (Hypergraph.colorable_iff_lineGraph_colorable k 𝓗).mpr hcol⟩

end

end ErdosFaberLovaszConjecture
