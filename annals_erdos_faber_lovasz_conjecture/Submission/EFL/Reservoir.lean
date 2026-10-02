import Submission.EFL.LargeEdge
import Submission.EFL.StabilityLoop
import Submission.EFL.DeepInputs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Reservoirs, absorbers and the types of §12 (Definitions 3.x, 7.1–7.5, 11.1–11.3)

This module sets up the definitions of the paper that Sections 7–12 of the
proof of Theorem 1.1 use.  Everything is phrased on the 2-uniform part
`𝓗^{(2)}` of a hypergraph, represented as a *family of pairs* (rather than as
a `SimpleGraph`): a set `R ⊆ 𝓗^{(2)}` of 2-edges is a graph on `Fin n` in the
usual way, with `N_R(v) = {w : {v,w} ∈ R}`.

* `𝓗^{(i)}` (`Hypergraph.powFam`), the graph part `G = 𝓗^{(2)}`
  (`Hypergraph.pow2`), the neighbourhood `nbrs R v` and degree `degAt R v`;
* `Vplus 𝓗 x` — the paper's `V_+^{(x)}(G)` (`= {v : d_G(v) ≥ xn}`), and
  `VexactNat`;
* matchings and coverage (`IsMatching`, `vertSet`, `Covers`,
  `PerfectCoverage`, `NearlyPerfectCoverage`);
* the quasirandomness vocabulary of Definition 7.1: `Typical` and
  `UpperRegular`/`LowerRegular`, and Definition 7.3's `IsAbsorber`;
* Definitions 11.1–11.2's reservoirs: `IsPseudoReservoir`, `IsRegularising`;
* the `(ρ,ε)`-full condition of Definition 2.x and the Type-A/Type-B
  colourings of Definition 12.1 (`IsFull`, `IsTypeA`, `IsTypeB`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## `𝓗^{(i)}`, the 2-graph, neighbourhoods -/

/-- `𝓗^{(i)}`: the edges of `𝓗` of size exactly `i`. -/
def Hypergraph.powFam (𝓗 : Hypergraph (Fin n)) (i : ℕ) : Hypergraph (Fin n) :=
  {e | e ∈ 𝓗 ∧ edgeSize e = i}

@[simp]
theorem mem_powFam {𝓗 : Hypergraph (Fin n)} {i : ℕ} {e : Set (Fin n)} :
    e ∈ 𝓗.powFam i ↔ e ∈ 𝓗 ∧ edgeSize e = i := Iff.rfl

theorem powFam_subset (𝓗 : Hypergraph (Fin n)) (i : ℕ) : 𝓗.powFam i ⊆ 𝓗 :=
  fun _ h => h.1

/-- `G = 𝓗^{(2)}`: the 2-uniform part of `𝓗`. -/
abbrev Hypergraph.pow2 (𝓗 : Hypergraph (Fin n)) : Hypergraph (Fin n) := 𝓗.powFam 2

@[simp]
theorem mem_pow2 {𝓗 : Hypergraph (Fin n)} {e : Set (Fin n)} :
    e ∈ 𝓗.pow2 ↔ e ∈ 𝓗 ∧ edgeSize e = 2 := Iff.rfl

/-- `N_R(v)`: the vertices joined to `v` by a 2-edge of `R`. -/
def nbrs (R : Hypergraph (Fin n)) (v : Fin n) : Set (Fin n) :=
  {w | ({v, w} : Set (Fin n)) ∈ R}

/-- The degree of `v` in the 2-graph `R`. -/
def degAt (R : Hypergraph (Fin n)) (v : Fin n) : ℕ := (nbrs R v).ncard

/-- `V_+^{(x)}(G) = {v : d_G(v) ≥ x n}`, where `G = 𝓗^{(2)}`. -/
def Vplus (𝓗 : Hypergraph (Fin n)) (x : ℝ) : Set (Fin n) :=
  {v | x * (n : ℝ) ≤ (degAt 𝓗.pow2 v : ℝ)}

/-- `{v : d_G(v) ≥ m}` for an integer `m`. -/
def VgeNat (𝓗 : Hypergraph (Fin n)) (m : ℕ) : Set (Fin n) :=
  {v | m ≤ degAt 𝓗.pow2 v}

/-- `{v : d_G(v) = d}`. -/
def VeqNat (𝓗 : Hypergraph (Fin n)) (d : ℕ) : Set (Fin n) :=
  {v | degAt 𝓗.pow2 v = d}

/-! ## Matchings and coverage -/

/-- The vertex set of a matching `M` (a family of edges of `𝓗`). -/
def matchVert {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) : Set (Fin n) :=
  ⋃ e ∈ M, (e : Set (Fin n))

/-- `M` covers `X`. -/
def Covers {𝓗 : Hypergraph (Fin n)} (M : Set 𝓗) (X : Set (Fin n)) : Prop :=
  X ⊆ matchVert M

/-- A family of matchings has *perfect coverage* of `U`. -/
def PerfectCoverage {ι : Type*} {𝓗 : Hypergraph (Fin n)} (𝓝 : ι → Set 𝓗)
    (U : Set (Fin n)) : Prop :=
  ∀ i, Covers (𝓝 i) U

/-- **Nearly-perfect coverage of `U` with defects in `S`** (paper
Definition 3.x): each vertex of `U` is covered by all but one of the
matchings, and each matching misses at most one vertex of `U`, the missed
vertices lying in `S`. -/
def NearlyPerfectCoverage {ι : Type*} [Fintype ι] {𝓗 : Hypergraph (Fin n)}
    (𝓝 : ι → Set 𝓗) (U S : Set (Fin n)) : Prop :=
  (∀ u ∈ U, ({i | u ∈ matchVert (𝓝 i)}.ncard : ℝ) + 1 ≥ (Fintype.card ι : ℝ)) ∧
  (∀ i, U \ matchVert (𝓝 i) ⊆ S) ∧
  ∀ i, (U \ matchVert (𝓝 i)).ncard ≤ 1

/-! ## The quasirandomness vocabulary of §7 -/

/-- **Definition 7.1 (`def:typicality`), typicality.**  `R` is
`(ρ, γ, G')`-typical with respect to `𝓥` if for every `X ∈ 𝓥` and every vertex
`v` the `R`-degree of `v` inside `X` (resp. outside `X`) is the
`ρ`-fraction of its `G'`-degree inside `X` (resp. outside `X`), up to `γn`. -/
def Typical (G' R : Hypergraph (Fin n)) (ρ γ : ℝ) (𝓥 : Set (Set (Fin n))) : Prop :=
  ∀ X ∈ 𝓥, ∀ v : Fin n,
    |(((X ∩ nbrs R v).ncard : ℝ) - ρ * ((X ∩ nbrs G' v).ncard : ℝ))| ≤ γ * (n : ℝ) ∧
    |(((Xᶜ ∩ nbrs R v).ncard : ℝ) - ρ * ((Xᶜ ∩ nbrs G' v).ncard : ℝ))| ≤ γ * (n : ℝ)

/-- The number of `R`-edges between the disjoint vertex sets `S` and `T`. -/
def edgeCount (R : Hypergraph (Fin n)) (S T : Finset (Fin n)) : ℕ := by
  classical
  exact ((S.product T).filter (fun p : Fin n × Fin n => ({p.1, p.2} : Set (Fin n)) ∈ R)).card

/-- **Definition 7.1 (`def:typicality`), upper regularity.** -/
def UpperRegular (G' R : Hypergraph (Fin n)) (ρ ξ : ℝ) : Prop :=
  ∀ S T : Finset (Fin n), Disjoint S T → ξ * (n : ℝ) ≤ (S.card : ℝ) →
    ξ * (n : ℝ) ≤ (T.card : ℝ) →
    (edgeCount R S T : ℝ) ≤ ρ * (edgeCount G' S T : ℝ) + ξ * (S.card : ℝ) * (T.card : ℝ)

/-- **Definition 7.1**, lower regularity (used for Type-`A₂` reservoirs). -/
def LowerRegular (G' R : Hypergraph (Fin n)) (ρ ξ : ℝ) : Prop :=
  ∀ S T : Finset (Fin n), Disjoint S T → ξ * (n : ℝ) ≤ (S.card : ℝ) →
    ξ * (n : ℝ) ≤ (T.card : ℝ) →
    ρ * (edgeCount G' S T : ℝ) - ξ * (S.card : ℝ) * (T.card : ℝ) ≤ (edgeCount R S T : ℝ)

/-- **Definition 7.3 (`def:absorber`), absorbers.**  `R` is a
`(ρ, γ, ξ)`-absorber for `𝓥` inside the 2-graph `G'`: it consists of edges of
`G'`, is `(ρ,γ,G')`-typical w.r.t. `𝓥` and is upper `(ρ,ξ,G')`-regular. -/
def IsAbsorber (G' R : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n))) (ρ γ ξ : ℝ) : Prop :=
  R ⊆ G' ∧ Typical G' R ρ γ 𝓥 ∧ UpperRegular G' R ρ ξ

/-- The 2-edges of `𝓗` incident to a vertex of `U`: the paper's `G'`. -/
def incidentTwo (𝓗 : Hypergraph (Fin n)) (U : Set (Fin n)) : Hypergraph (Fin n) :=
  {e | e ∈ 𝓗.pow2 ∧ ∃ u ∈ e, u ∈ U}

@[simp]
theorem mem_incidentTwo {𝓗 : Hypergraph (Fin n)} {U : Set (Fin n)} {e : Set (Fin n)} :
    e ∈ incidentTwo 𝓗 U ↔ e ∈ 𝓗.pow2 ∧ ∃ u ∈ e, u ∈ U := Iff.rfl

/-- **Definition 11.1 (`def:pseudoreg`), pseudorandom reservoirs.** -/
def IsPseudoReservoir (𝓗 : Hypergraph (Fin n)) (G' R : Hypergraph (Fin n))
    (𝓥 : Set (Set (Fin n))) (ρ ξ : ℝ) : Prop :=
  (∀ v : Fin n, |((degAt R v : ℝ) - ρ * (degAt 𝓗.pow2 v : ℝ))| ≤ ξ * (n : ℝ)) ∧
  IsAbsorber G' (R ∩ G') 𝓥 ρ ξ ξ

/-- **Definition 11.1 (`def:pseudoreg`), regularising reservoirs.**  Relative
to an absorber `Rabs` of density `ρ/2`, `Rreg` augments it to density `ρ` at
the vertices of `U = V_+^{(1-ε)}(G)` and to a lower bound `(ρ-20ε)n` at the
vertices outside `U`. -/
def IsRegularising (𝓗 : Hypergraph (Fin n)) (Rabs Rreg : Hypergraph (Fin n))
    (ρ ξ ε : ℝ) : Prop :=
  (∀ v ∈ Vplus 𝓗 (1 - ε),
      |((degAt (Rabs ∪ Rreg) v : ℝ) - ρ * (degAt 𝓗.pow2 v : ℝ))| ≤ ξ * (n : ℝ)) ∧
  (∀ w : Fin n, w ∉ Vplus 𝓗 (1 - ε) →
      max (ρ * (degAt 𝓗.pow2 w : ℝ)) ((ρ - 20 * ε) * (n : ℝ)) ≤
        (degAt (Rabs ∪ Rreg) w : ℝ) ∧
      (degAt (Rabs ∪ Rreg) w : ℝ) ≤ ρ * (1 - ε) * (n : ℝ) + ξ * (n : ℝ))

/-! ## The `(ρ,ε)`-full condition and the types of §12 -/

/-- **Definition 2.x (`def:full`), `(ρ,ε)`-fullness.** -/
def IsFull (𝓗 : Hypergraph (Fin n)) (ρ ε : ℝ) : Prop :=
  (1 - 10 * ε) * (n : ℝ) ≤ ((Vplus 𝓗 (1 - ε)).ncard : ℝ) ∧
  (ρ - 15 * ε) * (n : ℝ) ≤ ((VeqNat 𝓗 (n - 1)).ncard : ℝ)

/-- `𝓗_med ∪ 𝓗_large = {e ∈ 𝓗 : |e| > r₁}`, the domain of the colouring of
Theorem 6.7. -/
def medLarge (𝓗 : Hypergraph (Fin n)) (r₁ : ℝ) : Hypergraph (Fin n) :=
  {e | e ∈ 𝓗 ∧ (r₁ : ℝ) < (edgeSize e : ℝ)}

@[simp]
theorem mem_medLarge {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ} {e : Set (Fin n)} :
    e ∈ medLarge 𝓗 r₁ ↔ e ∈ 𝓗 ∧ (r₁ : ℝ) < (edgeSize e : ℝ) := Iff.rfl

theorem medLarge_subset (𝓗 : Hypergraph (Fin n)) (r₁ : ℝ) : medLarge 𝓗 r₁ ⊆ 𝓗 :=
  fun _ h => h.1

/-- A colouring of `𝓗_large ∪ 𝓗_med` is of **Type A** (it satisfies the
non-extremal alternative (6.7:a) of `large-edge-thm` for the given
parameters; `𝓗_large ∪ 𝓗_med = medLarge 𝓗 r₁`). -/
def IsTypeA (σ γ₁ β r₁ r₀ : ℝ) (𝓗 : Hypergraph (Fin n))
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) : Prop :=
  ∃ C₁ Cmed : Finset (Fin n),
    φ.UsesColourSet C₁ ∧ (C₁.card : ℝ) ≤ (1 - σ) * (n : ℝ) ∧ Cmed ⊆ C₁ ∧
    (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ) ∧
    (∀ e : medLarge 𝓗 r₁, edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ Cmed) ∧
    (∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) ∧
    φ.SingletonClassesForHuge β ∧
    (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))

/-- A colouring of `𝓗_large ∪ 𝓗_med` is of **Type B** (it satisfies the
extremal alternative (6.7:b) of `large-edge-thm`). -/
def IsTypeB (δ γ₂ γ₁ β r₁ r₀ : ℝ) (𝓗 : Hypergraph (Fin n))
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) : Prop :=
  (∃ W : Hypergraph (Fin n), W ⊆ 𝓗 ∧ (∀ e : Set (Fin n), e ∈ W → edgeExtremal δ n e) ∧
      1 - δ ≤ volume n W) ∧
  ∃ Cmed : Finset (Fin n), (Cmed.card : ℝ) ≤ γ₂ * (n : ℝ) ∧
    (∀ e : medLarge 𝓗 r₁, edgeMedium r₁ r₀ (e : Set (Fin n)) → φ.labels e ∈ Cmed) ∧
    (∀ c ∈ Cmed, (φ.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ)) ∧
    (∀ c : Fin n, φ.AssignedToHuge β c → (φ.classVertexCount c : ℝ) ≤ δ * (n : ℝ)) ∧
    (∀ c : Fin n, c ∉ Cmed → ¬ φ.AssignedToHuge β c →
        (φ.classVertexCount c : ℝ) ≤ β * (n : ℝ))

/-! ## Elementary consequences -/

/-- Subfamilies of a linear hypergraph are linear. -/
theorem IsLinear.mono' {𝓖 𝓗 : Hypergraph (Fin n)} (hsub : 𝓖 ⊆ 𝓗) (hlin : 𝓗.IsLinear) :
    𝓖.IsLinear :=
  Set.Pairwise.mono hsub hlin

theorem IsLinear.powFam {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (i : ℕ) :
    (𝓗.powFam i).IsLinear :=
  IsLinear.mono' (powFam_subset 𝓗 i) hlin

theorem IsLinear.medLarge {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ} (hlin : 𝓗.IsLinear) :
    (medLarge 𝓗 r₁).IsLinear :=
  IsLinear.mono' (medLarge_subset 𝓗 r₁) hlin

/-- **Volume upper bound**: if every edge of `𝓕` has size at most `M`, then
`vol(𝓕) ≤ (number of edges)·M(M-1)/(n(n-1))`. -/
theorem volume_le_canon_card_mul {𝓕 : Hypergraph (Fin n)} {M : ℕ} (hM1 : 1 ≤ M)
    (hM : ∀ e ∈ 𝓕, edgeSize e ≤ M) :
    volume n 𝓕 ≤ ((canonFinset 𝓕).card : ℝ) * ((M : ℝ) * ((M : ℝ) - 1)) /
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  classical
  by_cases hn : n ≤ 1
  · have hden : ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) = 0 := by
      have h : n = 0 ∨ n = 1 := by omega
      rcases h with h | h <;> subst h <;> norm_num
    rw [volume_eq_canon, hden, div_zero, div_zero]
  · have hden : (0 : ℝ) < (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
      have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
      have h2 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
        have : 0 < n - 1 := by omega
        exact_mod_cast this
      exact mul_pos (by linarith) h2
    rw [volume_eq_canon, div_le_div_iff_of_pos_right hden]
    have hnat : (canonFinset 𝓕).sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) ≤
        (canonFinset 𝓕).card * (M * (M - 1)) := by
      calc (canonFinset 𝓕).sum (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1))
          ≤ (canonFinset 𝓕).sum (fun _ => M * (M - 1)) := by
            apply Finset.sum_le_sum
            intro e he
            have he𝓕 : e ∈ 𝓕 := by
              simpa only [canonFinset, Finset.mem_filter, Finset.mem_univ, true_and] using he
            exact Nat.mul_le_mul (hM e he𝓕) (Nat.sub_le_sub_right (hM e he𝓕) 1)
        _ = (canonFinset 𝓕).card * (M * (M - 1)) := by
            rw [Finset.sum_const, smul_eq_mul]
    have hcast : ((M * (M - 1) : ℕ) : ℝ) = (M : ℝ) * ((M : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hM1, Nat.cast_one]
    calc (((canonFinset 𝓕).sum
          (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ)
        ≤ (((canonFinset 𝓕).card * (M * (M - 1)) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((canonFinset 𝓕).card : ℝ) * ((M : ℝ) * ((M : ℝ) - 1)) := by
          rw [Nat.cast_mul, hcast]

/-! ## Robustness of absorbers (Observation 7.4, `obs:del_absorber`) -/

/-- The number of `R`-neighbours of `v` outside `R'` is at most `αn`
(the maximum degree bound of `R \ R'`). -/
theorem nbrs_diff_card_le {R R' : Hypergraph (Fin n)} {α : ℝ}
    (hdeg : ∀ v : Fin n, ((nbrs R v \ nbrs R' v).ncard : ℝ) ≤ α * (n : ℝ)) (v : Fin n) :
    ((nbrs R v \ nbrs R' v).ncard : ℝ) ≤ α * (n : ℝ) := hdeg v

/-- **Observation 7.4 (typicality part).**  Removing a sub-2-graph of maximum
degree at most `αn` from a `(ρ,γ,G')`-typical family costs `αn` in the
typicality parameter. -/
theorem Typical.mono_del {G' R R' : Hypergraph (Fin n)} (hR' : R' ⊆ R)
    (𝓥 : Set (Set (Fin n))) {ρ γ α : ℝ} (hα : 0 ≤ α)
    (hdeg : ∀ v : Fin n, ((nbrs R v \ nbrs R' v).ncard : ℝ) ≤ α * (n : ℝ))
    (h : Typical G' R ρ γ 𝓥) : Typical G' R' ρ (γ + α) 𝓥 := by
  intro X hX v
  obtain ⟨h1, h2⟩ := h X hX v
  have hdiff : ∀ Y : Set (Fin n),
      (Y ∩ nbrs R v).ncard ≤ (Y ∩ nbrs R' v).ncard + (nbrs R v \ nbrs R' v).ncard := by
    intro Y
    have hcover : Y ∩ nbrs R v ⊆ (Y ∩ nbrs R' v) ∪ (nbrs R v \ nbrs R' v) := by
      rintro w ⟨hwY, hwR⟩
      by_cases h : w ∈ nbrs R' v
      · exact Or.inl ⟨hwY, h⟩
      · exact Or.inr ⟨hwR, h⟩
    calc (Y ∩ nbrs R v).ncard ≤ ((Y ∩ nbrs R' v) ∪ (nbrs R v \ nbrs R' v)).ncard :=
          Set.ncard_mono hcover
      _ ≤ (Y ∩ nbrs R' v).ncard + (nbrs R v \ nbrs R' v).ncard := Set.ncard_union_le _ _
  have hmono : ∀ Y : Set (Fin n), (Y ∩ nbrs R' v).ncard ≤ (Y ∩ nbrs R v).ncard := by
    intro Y
    exact Set.ncard_mono (Set.inter_subset_inter_right _ (fun w hw => hR' hw))
  have hαn : (0 : ℝ) ≤ α * (n : ℝ) := mul_nonneg hα (Nat.cast_nonneg n)
  constructor
  · refine abs_le.mpr ⟨?_, ?_⟩
    · have hlow := (abs_le.mp h1).1
      have hup : ((X ∩ nbrs R v).ncard : ℝ) ≤
          ((X ∩ nbrs R' v).ncard : ℝ) + ((nbrs R v \ nbrs R' v).ncard : ℝ) := by
        exact_mod_cast hdiff X
      have hcc := hdeg v
      linarith [hcc, hαn]
    · have hup := (abs_le.mp h1).2
      have hcc : ((X ∩ nbrs R' v).ncard : ℝ) ≤ ((X ∩ nbrs R v).ncard : ℝ) := by
        exact_mod_cast hmono X
      linarith [hcc, hαn]
  · refine abs_le.mpr ⟨?_, ?_⟩
    · have hlow := (abs_le.mp h2).1
      have hup : (((Xᶜ) ∩ nbrs R v).ncard : ℝ) ≤
          (((Xᶜ) ∩ nbrs R' v).ncard : ℝ) + ((nbrs R v \ nbrs R' v).ncard : ℝ) := by
        exact_mod_cast hdiff Xᶜ
      have hcc := hdeg v
      linarith [hcc, hαn]
    · have hup := (abs_le.mp h2).2
      have hcc : (((Xᶜ) ∩ nbrs R' v).ncard : ℝ) ≤ (((Xᶜ) ∩ nbrs R v).ncard : ℝ) := by
        exact_mod_cast hmono Xᶜ
      linarith [hcc, hαn]

/-- **Observation 7.4.**  A subfamily of an absorber obtained by deleting a
2-graph of maximum degree at most `αn` is again an absorber (with typicality
parameter increased by `α`). -/
theorem IsAbsorber.mono_del {G' R R' : Hypergraph (Fin n)} (hR' : R' ⊆ R)
    (𝓥 : Set (Set (Fin n))) {ρ γ ξ α : ℝ} (hγ0 : 0 ≤ γ) (hα : 0 ≤ α)
    (hdeg : ∀ v : Fin n, ((nbrs R v \ nbrs R' v).ncard : ℝ) ≤ α * (n : ℝ))
    (h : IsAbsorber G' R 𝓥 ρ γ ξ) : IsAbsorber G' R' 𝓥 ρ (γ + α) ξ := by
  classical
  obtain ⟨hsub, htyp, hup⟩ := h
  refine ⟨fun e he => hsub (hR' he), htyp.mono_del hR' 𝓥 hα hdeg, ?_⟩
  intro S T hdisj hS hT
  have hmono : edgeCount R' S T ≤ edgeCount R S T := by
    rw [edgeCount, edgeCount]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hR' hp.2⟩
  have := hup S T hdisj hS hT
  have : (edgeCount R' S T : ℝ) ≤ (edgeCount R S T : ℝ) := by exact_mod_cast hmono
  linarith

/-- **Volume upper bound (real form)**: if every edge of `𝓕` has
`(edgeSize e : ℝ) ≤ x` with `1 ≤ x`, then
`vol(𝓕) ≤ (number of edges)·x(x-1)/(n(n-1))`. -/
theorem volume_le_canon_card_mul_real {𝓕 : Hypergraph (Fin n)} {x : ℝ} (hx1 : 1 ≤ x)
    (hM : ∀ e ∈ 𝓕, (edgeSize e : ℝ) ≤ x) :
    volume n 𝓕 ≤ ((canonFinset 𝓕).card : ℝ) * (x * (x - 1)) /
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  classical
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  by_cases hn : n ≤ 1
  · have hden : ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) = 0 := by
      have h : n = 0 ∨ n = 1 := by omega
      rcases h with h | h <;> subst h <;> norm_num
    rw [volume_eq_canon, hden, div_zero, div_zero]
  · have hn2 : 2 ≤ n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hdenpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
      have : 0 < n - 1 := by omega
      exact_mod_cast this
    have hdenpos2 : (0 : ℝ) < (n : ℝ) * ((n - 1 : ℕ) : ℝ) := mul_pos hnR hdenpos
    rw [volume_eq_canon, div_le_div_iff_of_pos_right hdenpos2]
    have hterm : ∀ e ∈ canonFinset 𝓕,
        (((edgeSize e * (edgeSize e - 1) : ℕ)) : ℝ) ≤ x * (x - 1) := by
      intro e he
      have he𝓕 : e ∈ 𝓕 := by
        simpa only [canonFinset, Finset.mem_filter, Finset.mem_univ, true_and] using he
      have h1 : (edgeSize e : ℝ) ≤ x := hM e he𝓕
      rcases Nat.eq_zero_or_pos (edgeSize e) with hz | hp
      · rw [hz]
        norm_num
        nlinarith [hx1]
      · have hcast : ((edgeSize e * (edgeSize e - 1) : ℕ) : ℝ) =
            (edgeSize e : ℝ) * ((edgeSize e : ℝ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ edgeSize e), Nat.cast_one]
        rw [hcast]
        have h2 : (1 : ℝ) ≤ (edgeSize e : ℝ) := by exact_mod_cast hp
        have h3 : (edgeSize e : ℝ) - 1 ≤ x - 1 := by linarith
        have h4 : (0 : ℝ) ≤ (edgeSize e : ℝ) - 1 := by linarith
        have h5 : (0 : ℝ) ≤ x - 1 := by linarith
        exact mul_le_mul h1 h3 h4 (le_of_lt hx0)
    have hsumR : (((canonFinset 𝓕).sum
        (fun e : Set (Fin n) => edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ) ≤
        ((canonFinset 𝓕).card : ℝ) * (x * (x - 1)) := by
      rw [Nat.cast_sum]
      calc (canonFinset 𝓕).sum
            (fun e : Set (Fin n) => (((edgeSize e * (edgeSize e - 1) : ℕ)) : ℝ))
          ≤ (canonFinset 𝓕).sum (fun _ => x * (x - 1)) := Finset.sum_le_sum hterm
        _ = ((canonFinset 𝓕).card : ℝ) * (x * (x - 1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    exact hsumR

end

end ErdosFaberLovaszConjecture
