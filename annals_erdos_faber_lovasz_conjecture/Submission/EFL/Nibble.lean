import Submission.EFL.Regularising
import Submission.EFL.Absorption
import Submission.EFL.CrossingAbsorption

/-!
# The deep inputs of §8/§9: the Nibble Lemma and the Leftover Lemma

This module records, as `Prop`-valued input statements (in the style of
`KahnStatement`, `EGJStatement`, …), the two results of the paper that §12
consumes but which are themselves proved from the Rödl-nibble machinery of
§8/§9:

* **`NibbleStatement`** — Lemma `lem:nibble2` of the paper, §7 (the "Main
  colouring lemma"): given a `(ρ,γ,ξ,ε)`-absorber `R`, a linear
  multi-hypergraph `𝓗'` with `d_{𝓗'}(w) = (1 ± β)D`, and `D` edge-disjoint
  matchings `M_c` of few vertices and small overlap with `𝓗'`, there are
  matchings `N_c ⊇ M_c` with `N_c ∖ M_c ⊆ 𝓗' ∪ R` and small "colour degree"
  overlap with `R` and `𝓗'`, whose coverage of `U` is perfect or nearly
  perfect.  The paper's asymptotic hypotheses
  (`0 < 1/n₀ ≪ 1/r, ξ, β ≪ γ ≪ ε, ρ ≪ 1`, `n ≥ n₀`, `D ∈ [n^{2/3}, n]`) are
  recorded in the margin bundle `NibbleMargins` below.

* **`LeftoverStatement`** — Lemma `lem:leftover` (§7): the analogous statement
  for the "buffer" colour set, where the leftover hypergraph `𝓗_rem` is
  coloured by Kahn's theorem instead of the nibble.  **Superseded**: as stated
  here it omits the asymptotic hypotheses that the proof needs; the honest
  version is `leftover_colouring_lemma` in
  `Submission/EFL/LeftoverLemma.lean` (with the margin bundle
  `LeftoverMargins` of `Submission/EFL/LeftoverMargins.lean`), which the §12
  chain uses instead.

Both are stated for a *linear multi-hypergraph* `𝓗` (the paper's ambient
object, obtained from `𝓗` by adding singleton edges): a matching is a family of
pairwise disjoint vertex sets each of which is an edge of the multi-hypergraph
(singleton edges being counted with multiplicity, hence at most once each).

The paper proves `NibbleStatement` from `SparseEGJStatement`/`EGJStatement`
(`Submission/EFL/EGJ.lean`) together with the embedding lemma `lem:embed` and
the pseudorandom-matching lemma `lem:pseudorandom_matching`; this reduction is
*not* formalised here (it needs the multi-hypergraph embedding theory of §8).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

namespace MultiHypergraph

/-- The full edge family of a multi-hypergraph: the proper edges together with
the singleton edge `{v}` at every vertex whose singleton multiplicity is
positive. -/
def edgeSet (𝓜 : MultiHypergraph n) : Set (Set (Fin n)) :=
  𝓜.edges ∪ {e | ∃ v : Fin n, e = {v} ∧ 1 ≤ 𝓜.singles v}

theorem mem_edgeSet {𝓜 : MultiHypergraph n} {e : Set (Fin n)} :
    e ∈ 𝓜.edgeSet ↔ e ∈ 𝓜.edges ∨ ∃ v : Fin n, e = {v} ∧ 1 ≤ 𝓜.singles v :=
  Iff.rfl

theorem edges_subset_edgeSet (𝓜 : MultiHypergraph n) : 𝓜.edges ⊆ 𝓜.edgeSet :=
  fun _ he => Or.inl he

/-- A *matching* in a multi-hypergraph: a family of pairwise disjoint vertex
sets, each of which is an edge of the multi-hypergraph (the singleton edges
being available once each). -/
def IsMatching (𝓜 : MultiHypergraph n) (N : Set (Set (Fin n))) : Prop :=
  N ⊆ 𝓜.edgeSet ∧ N.Pairwise fun e₁ e₂ => Disjoint e₁ e₂

/-- The 2-uniform part `𝓗^{(2)}` of a multi-hypergraph. -/
def pow2 (𝓜 : MultiHypergraph n) : Hypergraph (Fin n) :=
  {e | e ∈ 𝓜.edges ∧ edgeSize e = 2}

theorem mem_pow2 {𝓜 : MultiHypergraph n} {e : Set (Fin n)} :
    e ∈ 𝓜.pow2 ↔ e ∈ 𝓜.edges ∧ edgeSize e = 2 := Iff.rfl

end MultiHypergraph

/-- `V_+^{(x)}(G)` for a 2-uniform family `G` of pairs. -/
def VplusTwo (G : Hypergraph (Fin n)) (x : ℝ) : Set (Fin n) :=
  {v | x * (n : ℝ) ≤ (degAt G v : ℝ)}

/-- Two families of vertex sets are *edge-disjoint* in a multi-hypergraph
sense if their proper (non-singleton) parts are disjoint: the singleton edges
of a multi-hypergraph are available in several copies, so two matchings may
each use a `{v}`. -/
def EdgeDisjointFam (N N' : Set (Set (Fin n))) : Prop :=
  Disjoint {e ∈ N | 2 ≤ e.ncard} {e ∈ N' | 2 ≤ e.ncard}

/-- The proper part of a family of vertex sets. -/
def nonsing (N : Set (Set (Fin n))) : Set (Set (Fin n)) := {e ∈ N | 2 ≤ e.ncard}

/-- The vertex set of a family of vertex sets. -/
def famVert (N : Set (Set (Fin n))) : Set (Fin n) := ⋃₀ N

theorem mem_famVert {N : Set (Set (Fin n))} {v : Fin n} :
    v ∈ famVert N ↔ ∃ e ∈ N, v ∈ e := by
  simp [famVert]

/-- `N` covers `X` (as a family of vertex sets). -/
def CoversFamMulti (N : Set (Set (Fin n))) (X : Set (Fin n)) : Prop :=
  X ⊆ famVert N

/-- Nearly-perfect coverage for a family of vertex-set families. -/
def NearlyPerfectCoverageFam {ι : Type*} [Fintype ι] (N : ι → Set (Set (Fin n)))
    (U S : Set (Fin n)) : Prop :=
  (∀ u ∈ U, ({i | u ∈ famVert (N i)}.ncard : ℝ) + 1 ≥ (Fintype.card ι : ℝ)) ∧
  (∀ i, U \ famVert (N i) ⊆ S) ∧
  ∀ i, (U \ famVert (N i)).ncard ≤ 1

namespace MultiHypergraph

/-! ## Degrees after deleting a family of edges -/

theorem hdeg_sdiff_add {𝓜 : MultiHypergraph n} {𝓕 : Hypergraph (Fin n)}
    (h : 𝓕 ⊆ 𝓜.edges) (w : Fin n) :
    hdeg (𝓜.edges \ 𝓕) w + hdeg 𝓕 w = hdeg 𝓜.edges w := by
  have h1 : {e ∈ 𝓜.edges | w ∈ e} = {e ∈ 𝓜.edges \ 𝓕 | w ∈ e} ∪ {e ∈ 𝓕 | w ∈ e} := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union]
    tauto
  have h2 : Disjoint {e ∈ 𝓜.edges \ 𝓕 | w ∈ e} {e ∈ 𝓕 | w ∈ e} := by
    rw [Set.disjoint_left]
    intro e he₁ he₂
    exact he₁.1.2 he₂.1
  rw [hdeg, hdeg, hdeg, h1]
  exact (Set.ncard_union_eq h2 (Set.toFinite _) (Set.toFinite _)).symm

theorem deg_sdiff_le {𝓜 : MultiHypergraph n} {𝓕 : Hypergraph (Fin n)}
    (h : 𝓕 ⊆ 𝓜.edges) (w : Fin n) : (𝓜.sdiff 𝓕).deg w ≤ 𝓜.deg w := by
  have h1 : hdeg (𝓜.edges \ 𝓕) w ≤ hdeg 𝓜.edges w := by
    have := hdeg_sdiff_add h w
    omega
  simp only [deg_def, edges_sdiff, singles_sdiff]
  omega

theorem deg_sdiff_ge {𝓜 : MultiHypergraph n} {𝓕 : Hypergraph (Fin n)}
    (h : 𝓕 ⊆ 𝓜.edges) (w : Fin n) (hm : hdeg 𝓕 w ≤ 1) :
    𝓜.deg w - 1 ≤ (𝓜.sdiff 𝓕).deg w := by
  have h1 : hdeg (𝓜.edges \ 𝓕) w + hdeg 𝓕 w = hdeg 𝓜.edges w := hdeg_sdiff_add h w
  have h2 : hdeg 𝓜.edges w - 1 ≤ hdeg (𝓜.edges \ 𝓕) w := by omega
  simp only [deg_def, edges_sdiff, singles_sdiff]
  omega

/-- A pairwise disjoint family contains at most one edge through `w`. -/
theorem hdeg_le_one_of_pairwise_disjoint {𝓕 : Hypergraph (Fin n)}
    (h : 𝓕.Pairwise fun e₁ e₂ => Disjoint e₁ e₂) (w : Fin n) : hdeg 𝓕 w ≤ 1 := by
  rw [hdeg, Set.ncard_le_one (s := {e ∈ 𝓕 | w ∈ e})]
  intro e₁ h₁ e₂ h₂
  by_contra hne
  exact (Set.disjoint_left.mp (h h₁.1 h₂.1 hne) h₁.2) h₂.2

/-- A single matching has degree at most one at every vertex. -/
theorem hdeg_famOf_le_one {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗}
    (hM : ErdosFaberLovaszConjecture.IsMatching 𝓗 M) (w : Fin n) :
    hdeg (famOf M) w ≤ 1 := by
  rw [hdeg, Set.ncard_le_one (s := {e ∈ famOf M | w ∈ e})]
  intro e₁ h₁ e₂ h₂
  have hf₁ : e₁ ∈ famOf M := h₁.1
  have hf₂ : e₂ ∈ famOf M := h₂.1
  rw [mem_famOf] at hf₁ hf₂
  obtain ⟨e₁', he₁', hv₁⟩ := hf₁
  obtain ⟨e₂', he₂', hv₂⟩ := hf₂
  have hw₁ : w ∈ (e₁' : Set (Fin n)) := by rw [hv₁]; exact h₁.2
  have hw₂ : w ∈ (e₂' : Set (Fin n)) := by rw [hv₂]; exact h₂.2
  have heq : e₁' = e₂' := by
    by_contra hne
    exact (Set.disjoint_left.mp (hM he₁' he₂' hne) hw₁) hw₂
  rw [← hv₁, ← hv₂, heq]

/-- Deleting a subfamily of degree at most one at every vertex shifts all
degrees by at most one. -/
theorem abs_deg_sdiff_sub_le {𝓜 : MultiHypergraph n} {𝓕 : Hypergraph (Fin n)}
    (h : 𝓕 ⊆ 𝓜.edges) (hm : ∀ w, hdeg 𝓕 w ≤ 1)
    {ρ D C : ℝ} (hC : ∀ w, |((𝓜.deg w : ℝ)) - (1 - ρ) * ((n : ℝ) - 1)| ≤ C)
    (w : Fin n) :
    |(((𝓜.sdiff 𝓕).deg w : ℝ)) - D| ≤ C + 1 + |(1 - ρ) * ((n : ℝ) - 1) - D| := by
  have h1 : (𝓜.sdiff 𝓕).deg w ≤ 𝓜.deg w := deg_sdiff_le h w
  have h2 : 𝓜.deg w ≤ (𝓜.sdiff 𝓕).deg w + 1 := by
    have := deg_sdiff_ge h w (hm w)
    omega
  have h1' : (((𝓜.sdiff 𝓕).deg w : ℝ)) ≤ (𝓜.deg w : ℝ) := by exact_mod_cast h1
  have h2' : ((𝓜.deg w : ℝ)) ≤ (((𝓜.sdiff 𝓕).deg w : ℝ)) + 1 := by exact_mod_cast h2
  have hCw := hC w
  rw [abs_le] at hCw
  have habs1 : (1 - ρ) * ((n : ℝ) - 1) ≤ D + |(1 - ρ) * ((n : ℝ) - 1) - D| := by
    have := le_abs_self ((1 - ρ) * ((n : ℝ) - 1) - D); linarith
  have habs2 : D - |(1 - ρ) * ((n : ℝ) - 1) - D| ≤ (1 - ρ) * ((n : ℝ) - 1) := by
    have := neg_abs_le ((1 - ρ) * ((n : ℝ) - 1) - D); linarith
  rw [abs_le]
  constructor <;> linarith

end MultiHypergraph

/-! ## Converting between families of vertex sets and families of edges -/

/-- The family of edges of `𝓗` corresponding to a family `N` of vertex sets
(all of whose proper members must be edges of `𝓗`). -/
def toFam {𝓗 : Hypergraph (Fin n)} (N : Set (Set (Fin n))) : Set 𝓗 :=
  {e : 𝓗 | (e : Set (Fin n)) ∈ nonsing N}

theorem mem_toFam {𝓗 : Hypergraph (Fin n)} {N : Set (Set (Fin n))} {e : 𝓗} :
    e ∈ toFam N ↔ (e : Set (Fin n)) ∈ nonsing N := Iff.rfl

/-- A pairwise disjoint family of vertex sets yields a matching of `𝓗` after
deleting the singletons. -/
theorem isMatching_toFam {𝓗 : Hypergraph (Fin n)} {N : Set (Set (Fin n))}
    (hN : N.Pairwise fun e₁ e₂ => Disjoint e₁ e₂) : IsMatching 𝓗 (toFam N) := by
  intro e₁ h₁ e₂ h₂ hne
  exact hN h₁.1 h₂.1 (fun heq => hne (Subtype.ext heq))

/-- A matching of a multi-hypergraph whose proper edges lie in `𝓗` is, after
deleting its singleton edges, a matching of `𝓗`. -/
theorem MultiHypergraph.IsMatching.toFam {𝓜 : MultiHypergraph n} {𝓗 : Hypergraph (Fin n)}
    {N : Set (Set (Fin n))} (hN : MultiHypergraph.IsMatching 𝓜 N)
    (hedges : 𝓜.edges ⊆ 𝓗) : ErdosFaberLovaszConjecture.IsMatching 𝓗 (toFam N) :=
  isMatching_toFam (𝓗 := 𝓗) hN.2

theorem MultiHypergraph.edgeSet_ofHypergraph (𝓗 : Hypergraph (Fin n)) :
    (MultiHypergraph.ofHypergraph 𝓗).edgeSet = 𝓗 := by
  ext e
  simp only [MultiHypergraph.mem_edgeSet, MultiHypergraph.edges_ofHypergraph,
    MultiHypergraph.singles_ofHypergraph, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨v, rfl, h⟩)
    · exact h
    · exact absurd h (by norm_num)
  · exact Or.inl

/-- The underlying family of vertex sets of a matching of a hypergraph. -/
theorem MultiHypergraph.isMatching_famOf {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗}
    (hM : ErdosFaberLovaszConjecture.IsMatching 𝓗 M) :
    MultiHypergraph.IsMatching (MultiHypergraph.ofHypergraph 𝓗) (famOf M) := by
  constructor
  · rintro e ⟨e', he', rfl⟩
    rw [MultiHypergraph.edgeSet_ofHypergraph]
    exact e'.2
  · intro e₁ h₁ e₂ h₂ hne
    obtain ⟨e₁', he₁', rfl⟩ := h₁
    obtain ⟨e₂', he₂', heq⟩ := h₂
    rw [← heq] at hne ⊢
    exact hM he₁' he₂' (fun heq' => hne (by rw [heq']))

theorem famVert_famOf {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) :
    famVert (famOf M) = matchVert M := by
  ext v
  rw [mem_famVert, mem_matchVert]
  constructor
  · rintro ⟨e, ⟨e', he', rfl⟩, hve⟩
    exact ⟨e', he', hve⟩
  · rintro ⟨e, he, hve⟩
    exact ⟨(e : Set (Fin n)), ⟨e, he, rfl⟩, hve⟩

theorem coversFamMulti_famOf {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) (X : Set (Fin n)) :
    CoversFamMulti (famOf M) X ↔ Covers M X := by
  rw [CoversFamMulti, Covers, famVert_famOf]

/-! ## `lem:nibble2` (the Nibble Lemma) -/

/-- **The asymptotic side conditions of the Nibble Lemma.**

The paper's Lemma `lem:nibble2` assumes
`0 < 1/n₀ ≪ 1/r, ξ, β ≪ γ ≪ ε, ρ ≪ 1`, `n ≥ n₀` and `D ∈ [n^{2/3}, n]`,
where the `≪`'s are between *constants* (independent of `n`) and `n` is then
taken sufficiently large.  As in `HugeMargins`/`LeftoverMargins` we record this
hierarchy in explicit constant form; every field is a consequence of the
paper's hypotheses for suitable choices of `n₀`, and is what the proof of
`lem:nibble2` actually uses (`κ` is chosen with `1/r, ξ, β ≪ κ ≪ γ`, and
`D ≥ n^{2/3}` is what makes the Chernoff bound and the union bound in the
partition step work).

**KNOWN DEFECT (2026-09-22, found by the subproject
`Submission/Work/Deep/Nibble/`).**  The constant factors `4`/`16` below are
*not* enough for the paper's proof of `lem:nibble2`: the proof chooses a
constant `κ` with `1/r, ξ, β^{1/2} ≪ κ ≪ γ` and then applies the formalised
§7.2 absorption (`Submission/EFL/InternalAbsorption.lean`,
`InternalMargins.hκγ`) with pseudorandomness parameter `γ/4`, which requires
`1500·κ ≤ γ/4`;  with `κ = γ/6000` this forces `1/r, ξ, β^{1/2} ≤ γ/6000`,
whereas the bundle below only gives `≤ γ/4` (a gap of the factor `1500`).
Moreover the boundary term `γ·|V(M_c)|/n` of `lem:pseudorandom_matching`
together with `|V(M_c)| ≤ β·D` forces `1500·β·D ≤ n`, and the `K`-partition
step needs `n` to dominate the constants (a Chernoff bound and a lower bound on
`K`).  See `Work/Deep/Nibble/Defs.lean` for the full derivation and for the
structure `NibbleMarginsStrong` (the bundle their proof uses).  Whether
`NibbleStatement` *as stated below* is true is open — no counterexample is
known, but the paper's route does not go through with these constants.

**The fix is not a mere constant bump.**  The pseudorandomness error `κ` of the
matchings produced by `lem:pseudorandom_matching` also has to satisfy the other
fields of `InternalMargins` (see `Submission/EFL/InternalAbsorption.lean`:
`8κ ≤ γ ρ ε`, `4000κ ≤ γρ`, `100κ ≤ γ²`, `20000γ ≤ ρ`, …), and the application
takes `γ_abs = γ/4`;  in particular `8κ ≤ (γ/4)·ρ·ε` forces `κ ≪ γρε`, so the
Nibble bundle must encode `β^{1/2}, ξ, 1/r ≪ γρε` — relations between `β, ξ, r`
and the *product* `γρε`, not just small constants.  Weakening the absorption is
not an option either: the shapes above are what the formalised §7.2 absorption
actually uses, and the `1500` in `hκγ` is likewise substantive.  So fixing the
bundle means (i) restating it with the `γρε`-relative conditions, and (ii)
choosing the §12 constants (`s12_step1`'s `β, r₁`, `exists_S12ANum`'s `ξ`) small
enough relative to `σ` — feasible, since `ρ = σ/2` and `ε = σ³/10⁴²` are
functions of `σ`, which `s12_step1` already produces, and `β`/`ξ`/`r₁` are
chosen there by `min`/`max`.  That is a research-level reworking of §12's
numeric layer, **not** the mechanical constant bump attempted (and reverted) in
this session; it is left for a future session.  (The *constant* strengthenings
and the corresponding constant strengthenings in the §12 chain that supplies them
(`Submission/EFL/S12Params.lean` `S12Margins_of`/`exists_S12Margins`,
`S12ANum.lean` `exists_S12ANum`, and ultimately the constant hierarchy chosen
by `s12_step1` in `S12Step1Full.lean`, where `β := min β₀ (min (γ₁/2)
(γ₁²/16))` and `r₁ := max R₁ (max 10 ⌈32/β⌉₊)` show that the constants are
free to be chosen smaller/larger).  This was *not* done in this session because
it reaches the core of the §12 chain; it is recorded here so that a future
session can carry it out. -/
structure NibbleMargins (n : ℕ) (D : ℝ) (r : ℕ) (β γ ε ρ ξ : ℝ) : Prop where
  /-- `n ≥ n₀` -/
  hn : 8 ≤ n
  /-- `r ≥ 2` -/
  hr : 2 ≤ r
  hβ0 : 0 < β
  hγ0 : 0 < γ
  hε0 : 0 < ε
  hρ0 : 0 < ρ
  hξ0 : 0 < ξ
  /-- `ρ ≪ 1` -/
  hρ1 : ρ ≤ 1
  /-- `D ∈ [n^{2/3}, n]`: the lower bound `D ≥ n^{2/3}` -/
  hDlow : Real.rpow (n : ℝ) (2 / 3) ≤ D
  /-- `D ∈ [n^{2/3}, n]`: the upper bound `D ≤ n` -/
  hDhigh : D ≤ (n : ℝ)
  /-- `1/n ≪ 1/r` -/
  hnr : 4 * (r : ℝ) ≤ (n : ℝ)
  /-- `1/n ≪ ξ` -/
  hnξ : 1 ≤ ξ * (n : ℝ)
  /-- `1/n ≪ β` -/
  hnβ : 1 ≤ β * (n : ℝ)
  /-- `1/r ≪ γ` -/
  hrγ : 4 ≤ γ * (r : ℝ)
  /-- `ξ ≪ γ` -/
  hξγ : 4 * ξ ≤ γ
  /-- `β ≪ γ`: more precisely `β ≪ γ²`, which is exactly what the proof uses
  (the pseudorandom-matching lemma is applied on each part with `β^{1/2}` and
  `γ/4`, so one needs `β^{1/2} ≪ γ`). -/
  hβγ : 16 * β ≤ γ ^ 2
  /-- `γ ≪ ε` -/
  hγε : 4 * γ ≤ ε
  /-- `γ ≪ ρ` -/
  hγρ : 4 * γ ≤ ρ

/-- **The strengthened asymptotic side conditions of the Nibble Lemma**
(`γρε`-relative form, matching `Work.Deep.Nibble.NibbleMarginsStrong`).

The paper's proof of `lem:nibble2` chooses a *constant* `κ` with
`1/r, ξ, β^{1/2} ≪ κ ≪ γ` and then applies the pseudorandom-matching lemma on
each of the `K = ⌈κ⁻¹⌉` parts and the §7.2 absorption at pseudorandomness
parameter `γ_p ≈ γ/4`.  The formalised absorption
(`Submission/EFL/InternalAbsorption.lean`) imposes `8κ ≤ γ_p ρ ε` and
`1500κ ≤ γ_p`, so `κ ≪ γρε` and hence `1/r, ξ, β^{1/2} ≪ γρε` — relations
between `β, ξ, r` and the *product* `γρε`, which the seeded bundle
`NibbleMargins` does not encode (it only has `β^{1/2}, ξ, 1/r ≪ γ`).

The fields below are the paper's hierarchy in exactly the form that makes the
choice of `κ` (and of the other assembly parameters `γ_p, δ, β_p, K`) possible;
they are the hypotheses that the §12 numeric layer supplies
(`Submission/EFL/S12Params.lean`, session 4: `S12Margins_of` constructs this bundle, and
`S12ANum`/`S12BNum` supply the constant-level facts). -/
structure NibbleMarginsStrong (n : ℕ) (D : ℝ) (r : ℕ) (β γ ε ρ ξ : ℝ) : Prop where
  base : NibbleMargins n D r β γ ε ρ ξ
  /-- `β^{1/2} ≤ γρε/10^6`, i.e. `10^{12} β ≤ (γρε)²` -/
  hβ : 10 ^ 12 * β ≤ (γ * ρ * ε) ^ 2
  /-- `β` is even smaller than `γ⁴`: this is what makes the §7 assembly parameter
  `κ := γ²/2400` dominate `β^{1/2}` (needed for `AssemblyParams.hβpκ`), while
  `AssemblyParams.hκγ2` keeps `κ ≤ γ²` -/
  hβ4 : β ≤ γ ^ 4 / 10 ^ 12
  /-- `ξ ≤ γρε/10^{12}` -/
  hξ : 10 ^ 12 * ξ ≤ γ * ρ * ε
  /-- `ξ ≤ γ²/10^8` -/
  hξ2 : ξ ≤ γ ^ 2 / 10 ^ 8
  /-- `1/r ≤ γρε/10^{12}` -/
  hr : 10 ^ 12 ≤ γ * ρ * ε * (r : ℝ)
  /-- `1/r ≤ γ²/10^8` -/
  hr2 : 10 ^ 8 ≤ γ ^ 2 * (r : ℝ)
  /-- `γ ≤ ρ/10^6` -/
  hγρ : 10 ^ 6 * γ ≤ ρ
  /-- `10 γ ≤ ρ ε`: with the paper's choice `γ_p = γ/2` this is exactly
  `AssemblyParams.hκγε` for `κ = γ²/2400` -/
  hγρε : 10 * γ ≤ ρ * ε
  /-- `β D ≤ γρε n/8`, the boundary term of `lem:pseudorandom_matching` -/
  hβD : 8 * β * D ≤ γ * ρ * ε * (n : ℝ)
  /-- `n` dominates all the constants -/
  hn : 10 ^ 100 ≤ γ * ρ * ε * (n : ℝ)
  /-- `ε` is small -/
  hε : 4000 * ε ≤ 1
  /-- the *gap* `n - D ≥ ρ n` left over by the `D` colour classes: in §12
  `D = Dparam n ρ ≤ (1-ρ)(n-1)`, so this is what makes the chunking parameter
  `K = ⌈κ⁻¹⌉` satisfy `1 ≤ κ (n - D)` -/
  hDgap : D ≤ (1 - ρ) * (n : ℝ)
  /-- `D` is a positive proportion of `n`: `n/2 ≤ D`.

  **This field is a repair (session 4) of a machine-checked defect of the
  bundle.**  The §7 assembly's `AssemblyParams` forces `1502 * (√n + 1) ≤ γ * D`
  (combine `hκγ` with `hγpγup` and `hKfloor`), which the fields above do *not*
  imply: with `D = n^{2/3}` (allowed by `NibbleMargins.hDlow`) the family
  `n = 10^{12t}`, `D = 10^{8t}`, `γ = 10^{-(2t+1)}`, `ρ = 10^{-100}`,
  `ε = 10^{-5}`, `β = 10^{-(8t+20)}`, `ξ = 10^{-6t}` satisfies every other
  field, while `γ D = 10^{6t-1}` is far below `1502·10^{6t} ≈ 1502 √n`, so no
  `κ` can satisfy both `1500 κ ≤ γ_p ≤ γ` and `√n + 1 ≤ κ D`.  In §12 the bundle
  is applied with `D = Dparam n ρ` and `n ≤ 2 * Dparam n ρ`
  (`S12Setup.n_le_two_Dparam`), so this field is exactly what the §12 supply
  provides. -/
  hDlin : (n : ℝ) / 2 ≤ D
  /-- `n` also dominates the reciprocal constants, which is what lets the §7
  assembly choose `K = ⌈κ⁻¹⌉` together with `K ≤ D/√n` and the Chernoff bound of
  the partition step (`AssemblyParams.hKfloor`, `hKceil`, `hKround`, `hCher`).
  Every instance of §12 satisfies this, since there `n` is unbounded while
  `β, γ, ρ, ε, ξ, r` are fixed constants (functions of `σ`), and the thresholds
  of `Submission/EFL/S12Params.lean` are built from exactly these expressions.
  NOTE.  `n ≠ 10^110 ≤ n`-style *upper* bounds must never be added here: the
  theorem is a `∀ᶠ n` statement and the §12 branches apply the Nibble statement
  at every `n ≥ N₀` with `N₀` fixed (a bundle containing an upper bound on `n`
  is inconsistent with this field, as machine-checked in
  `Work.Deep.Nibble.exists_assemblyData`). -/
  hnbig : 10 ^ 400 * ((ρ⁻¹) ^ 6 + (γ⁻¹) ^ 16 + (γ * ρ * ε)⁻¹ + ((γ * ρ * ε)⁻¹) ^ 2
      + (r : ℝ)) ≤ (n : ℝ)

/-- **Lemma `lem:nibble2`** (the Nibble Lemma), as an input statement.

**THIS IS THE SEEDED STATEMENT, AND IT IS FALSE.**  It is kept only as documentation of the
defect (the refutation `Work.Deep.Nibble.not_nibbleStatement` is a theorem about it); *nothing*
in the cone uses it any more.  The corrected statement is `NibbleStatementFixed`, and the §12
chain was switched to it in session 4 (see `HANDOFF.md`): `s12_step6` takes a
`NibbleStatementFixed` and a `NibbleMarginsStrong`, and `S12Margins.hnib` has type
`NibbleMarginsStrong` (supplied by `S12Params.S12Margins_of` /
`Work.Nib.strong_of_margins`).

* **The `M i` must be pairwise edge-disjoint (the paper's C4).**  The paper's C4 reads "let
  `𝓜 = {M_1, …, M_D}` be a set of *edge-disjoint matchings* in `𝓗 ∖ (𝓗' ∪ R)`".  The seeded
  statement below keeps only `∀ i, IsMatching 𝓗 (M i)` and never relates `M i` to `M j`, while
  the conclusion requires `∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)` with `M i ⊆ N i`; so two
  equal `M i = {e₀}` (with `e₀.ncard = 2`) make the conclusion unsatisfiable while every
  hypothesis holds.  A machine-checked refutation is
  `Work.Deep.Nibble.not_nibbleStatement` (`Submission/Work/Deep/Nibble/not_nibbleStatement.lean`).
* **The margins are too weak.**  `NibbleMargins` records `β ≪ γ` as `β^{1/2} ≤ γ/4`, but the
  paper's proof chooses a constant `κ` with `1/r, ξ, β^{1/2} ≪ κ ≪ γ`, applies
  `lem:pseudorandom_matching` on each of the `K = ⌈κ⁻¹⌉` parts and runs the §7.2 absorption
  (`Submission/EFL/InternalAbsorption.lean`) at pseudorandomness parameter `γ_p ≈ γ/2`, whose
  fields (`8κ ≤ γ_p ρ ε`, `1500 κ ≤ γ_p`, …) force `κ ≪ γρε` — relations between `β, ξ, r` and
  the *product* `γρε` that `NibbleMargins` does not encode.  The corrected bundle is
  `NibbleMarginsStrong` above; the §12 numeric layer must be reworked to supply it (it can: its
  `ρ ε = (σ/2)·(σ³/10⁴²) ≥ 10γ` and it chooses `β, ξ, r₁` from `σ`).

The seeded statement is kept only as the object of that machine-checked refutation; nothing
in the cone uses it any more (§12 instantiates `NibbleStatementFixed`,
`Submission/EFL/NibbleFixed.lean`), and nothing should be built on it. -/
def NibbleStatement : Prop :=
  ∀ {n : ℕ} (𝓗 𝓗' : MultiHypergraph n) (R : Hypergraph (Fin n))
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {ρ γ β ξ ε : ℝ} {D r : ℕ}
    (M : Fin D → Set (Set (Fin n))),
    -- the asymptotic side conditions of the paper
    NibbleMargins n (D : ℝ) r β γ ε ρ ξ →
    -- `U = V_+^{(1-ε)}(G)` where `G = 𝓗^{(2)}`
    U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε) →
    -- **C1**
    S ⊆ U →
    ((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ)) →
    -- **C2**
    U ∈ 𝓥 → (Set.univ : Set (Fin n)) ∈ 𝓥 →
    IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ →
    -- **C3**
    𝓗' ≤ 𝓗 →
    -- `𝓗' ⊆ 𝓗 ∖ R` (the paper's C3)
    (∀ e ∈ 𝓗'.edges, e ∉ R) →
    𝓗'.IsLinear →
    (∀ e ∈ 𝓗'.edges, edgeSize e ≤ r) →
    (∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ)) →
    -- **C4**
    (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
    (∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet) →
    (∀ i, ∀ e ∈ M i, e ∉ R) →
    (∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ)) →
    (∀ e ∈ 𝓗'.edges, (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) →
    ∃ N : Fin D → Set (Set (Fin n)),
      (∀ i, M i ⊆ N i) ∧
      (∀ i, MultiHypergraph.IsMatching 𝓗 (N i)) ∧
      (∀ i, ∀ e ∈ N i, e ∉ M i → e ∈ 𝓗'.edgeSet ∪ R) ∧
      (∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)) ∧
      (∀ w : Fin n, ((({e ∈ R | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i : Fin D, N i)).ncard : ℝ) ≤
        γ * (D : ℝ)) ∧
      (∀ w : Fin n, ((({e ∈ 𝓗'.edgeSet | w ∈ e} : Set (Set (Fin n))) \ (⋃ i : Fin D, N i)).ncard : ℝ) ≤
        γ * (D : ℝ)) ∧
      (((U.ncard : ℝ) ≤ (1 - 2 * ε) * (n : ℝ)) → ∀ i, CoversFamMulti (N i) U) ∧
      (((1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverageFam N U S) ∧
      -- NB1, singleton bookkeeping: the matchings use *distinct copies* of each
      -- singleton edge of `𝓗'`, so a singleton `{w}` of `𝓗'` occurs in at most
      -- `𝓗'.singles w` of the matchings `N i` (outside of `M i`).
      (∀ w : Fin n, (({i : Fin D | ({w} : Set (Fin n)) ∈ N i ∧
          ({w} : Set (Fin n)) ∉ M i} : Set (Fin D)).ncard) ≤ 𝓗'.singles w)

/- **The corrected Nibble Lemma (`lem:nibble2`)** — MOVED.  The statement lives in
`Submission/EFL/NibbleFixed.lean` (`ErdosFaberLovaszConjecture.NibbleStatementFixed`), in the
paper's *asymptotic* form: the constants `r, β, γ, ε, ρ, ξ` are fixed first (subject to the
`n`-free conditions of `Work.Deep.Nibble.MarginsConst`) and only then is a threshold `N₀`
chosen (`∀ n ≥ N₀`).  That is the form in which the lemma is proved
(`Work.Deep.Nibble.nibbleStatementFixed`, from `Work.Deep.Nibble.nibbleStatementFixed_weak`)
and the form the §12 chain consumes: it carries, for each `n`, the *pointwise* statement
`ErdosFaberLovaszConjecture.NibblePointwise r β γ ε ρ ξ n` above the threshold
`ErdosFaberLovaszConjecture.nibbleThr r β γ ε ρ ξ`.  The `NibbleStatementFixed` that used to
live here was the pointwise-in-`n` form with no threshold, which is *stronger* than the
paper's lemma (`Work/Deep/Nibble/NOTES_SESSION7.md`, defect D7) and is not what the chapter
proves. -/

/-! ## `lem:leftover` (the Leftover Lemma) -/

/-- The conclusion of the Leftover Lemma: the matchings `N i` extend the given
`M i`, use only the leftover edges and the absorber `R`, remain pairwise
edge-disjoint, cover `𝓗_rem`, and cover `U` perfectly (or nearly perfectly with
defects in `S`). -/
def LeftoverConcl {n : ℕ} (𝓗 : MultiHypergraph n) (𝓗rem R : Hypergraph (Fin n))
    (U S : Set (Fin n)) (ε : ℝ) {k : ℕ} (M N : Fin k → Set (Set (Fin n))) : Prop :=
  (∀ i, M i ⊆ N i) ∧
  (∀ i, MultiHypergraph.IsMatching 𝓗 (N i)) ∧
  (∀ i, ∀ e ∈ N i, e ∉ M i → e ∈ 𝓗rem ∪ R) ∧
  (∀ i j, i ≠ j → EdgeDisjointFam (N i) (N j)) ∧
  (∀ e ∈ 𝓗rem, ∃ j : Fin k, e ∈ N j) ∧
  (((U.ncard : ℝ) ≤ (1 - 10 * ε) * (n : ℝ)) → ∀ i, CoversFamMulti (N i) U) ∧
  (((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ)) → NearlyPerfectCoverageFam N U S)

/-- **Lemma `lem:leftover`** (the Leftover Lemma), as an input statement: the
remaining edges of `𝓗_rem` are coloured by Kahn's theorem, the buffer colour
classes being extended using the absorber `R`. -/
def LeftoverStatement : Prop :=
  ∀ {n : ℕ} (𝓗 : MultiHypergraph n) (R : Hypergraph (Fin n)) (𝓗rem : Hypergraph (Fin n))
    {U S : Set (Fin n)} {ρ γ ξ ε : ℝ} {D r k : ℕ} (M : Fin k → Set (Set (Fin n))),
    -- **linearity of the ambient multi-hypergraph** (the paper's hypothesis; it
    -- is what lets Kahn's list-edge-colouring theorem apply to `𝓗rem`)
    𝓗.IsLinear →
    -- `U = V_+^{(1-ε)}(G)` where `G = 𝓗^{(2)}`
    U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε) →
    -- **L1**
    γ * (D : ℝ) / 2 ≤ (k : ℝ) →
    (k : ℝ) ≤ γ * (D : ℝ) →
    -- **L2**
    -- no singleton edge occurs in the given matchings or in the leftover (in
    -- the application all these edges have size at least two, since the
    -- ambient `𝓗` has no singleton edge)
    (∀ i, ∀ e ∈ M i, 2 ≤ e.ncard) →
    (∀ i, MultiHypergraph.IsMatching 𝓗 (M i)) →
    (∀ i j, i ≠ j → Disjoint (M i) (M j)) →
    (∀ i, ((famVert (M i)).ncard : ℝ) ≤ γ * (n : ℝ) / 2) →
    -- **L3**
    R ⊆ (MultiHypergraph.pow2 𝓗) →
    (∀ i, ∀ e ∈ M i, e ∉ R) →
    IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R
      ({(Set.univ : Set (Fin n)), U} : Set (Set (Fin n))) ρ (10 * γ) ξ →
    -- **L4**
    (∀ e ∈ 𝓗rem, 2 ≤ e.ncard) →
    (𝓗rem ⊆ 𝓗.edges) →
    (∀ e ∈ 𝓗rem, e ∉ R) →
    (∀ e ∈ 𝓗rem, ∀ i, e ∉ M i) →
    (∀ v : Fin n, (MultiHypergraph.hdeg 𝓗rem v : ℝ) ≤ γ ^ 2 * (D : ℝ) / 20) →
    (∀ e ∈ 𝓗rem, edgeSize e ≤ r) →
    (∀ e ∈ 𝓗rem, (({i : Fin k | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤
      γ ^ 2 * (D : ℝ) / 100) →
    -- **L5**
    S ⊆ U →
    ((1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) → (γ + ε) * (n : ℝ) < (S.ncard : ℝ)) →
    ∃ N : Fin k → Set (Set (Fin n)), LeftoverConcl 𝓗 𝓗rem R U S ε M N


theorem mem_toFam_iff {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))} {e : 𝓗} :
    e ∈ toFam (𝓗 := 𝓗) G ↔ (e : Set (Fin n)) ∈ G ∧ 2 ≤ (e : Set (Fin n)).ncard := by
  rw [mem_toFam, nonsing, Set.mem_ofPred_eq]

/-- A matching of `ofHypergraph 𝓗` (i.e. a pairwise disjoint subfamily of `𝓗`)
has the same vertex set after deleting its singletons. -/
theorem matchVert_toFam {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))}
    (hG : G ⊆ 𝓗) (hns : ∀ e ∈ G, 2 ≤ e.ncard) :
    matchVert (toFam (𝓗 := 𝓗) G) = famVert G := by
  ext v
  rw [mem_matchVert, mem_famVert]
  constructor
  · rintro ⟨e, he, hve⟩
    exact ⟨(e : Set (Fin n)), (mem_toFam_iff.mp he).1, hve⟩
  · rintro ⟨e, he, hve⟩
    exact ⟨⟨e, hG he⟩, mem_toFam_iff.mpr ⟨he, hns e he⟩, hve⟩

/-! ## Glue between families of vertex sets and families of edges of `𝓗` -/

theorem nonsing_eq_self {G : Set (Set (Fin n))} (h : ∀ e ∈ G, 2 ≤ e.ncard) :
    nonsing G = G := by
  ext e
  constructor
  · intro he
    rw [nonsing, Set.mem_ofPred_eq] at he
    exact he.1
  · intro he
    rw [nonsing, Set.mem_ofPred_eq]
    exact ⟨he, h e he⟩

/-- `toFam` does not delete anything when `G` consists of edges of `𝓗` of size
at least `2`. -/
theorem toFam_eq_self {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))}
    (hG : G ⊆ 𝓗) (h : ∀ e ∈ G, 2 ≤ e.ncard) :
    toFam (𝓗 := 𝓗) G = {e : 𝓗 | (e : Set (Fin n)) ∈ G} := by
  ext e
  rw [mem_toFam]
  constructor
  · intro he
    exact (show (e : Set (Fin n)) ∈ nonsing G from he) |> fun hh =>
      (by rwa [nonsing_eq_self h] at hh)
  · intro he
    exact (nonsing_eq_self h).symm ▸ he

theorem famOf_toFam_eq {𝓗 : Hypergraph (Fin n)} {G : Set (Set (Fin n))}
    (hG : G ⊆ 𝓗) (h : ∀ e ∈ G, 2 ≤ e.ncard) : famOf (toFam (𝓗 := 𝓗) G) = G := by
  ext e
  rw [mem_famOf]
  constructor
  · rintro ⟨e', he', rfl⟩
    have h2 : (e' : Set (Fin n)) ∈ G := by
      rwa [toFam_eq_self hG h] at he'
    exact h2
  · intro he
    exact ⟨⟨e, hG he⟩, by rw [toFam_eq_self hG h]; exact he, rfl⟩

end

end ErdosFaberLovaszConjecture
