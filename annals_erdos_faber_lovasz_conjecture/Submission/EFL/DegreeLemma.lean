import Submission.EFL.DegreeBounds
import Submission.EFL.ReservoirType
import Submission.EFL.RegReservoir

/-!
# The Regularising Lemma (Lemma 11.3, `lem:degree-lemma`)

Let `𝓗` be an `n`-vertex linear hypergraph without singleton edges, `G = 𝓗^{(2)}`
and `U = V_+^{(1-ε)}(G)`.  If `R_res` is a `(ρ,ξ,ε,𝓥)`-reservoir of Type `A₁`
or `A₂` for a family `𝓥` containing `V(𝓗)`, then (assuming the parameter
hierarchy) there is a linear multi-hypergraph `𝓗'`

* obtained from `𝓗_small ∖ R_res` by adding singleton edges,
* contained in `𝓗_reg` (i.e. no more than `max 0 (n - 3 - d_𝓗(w))` singletons
  are added at `w`), and
* with `d_{𝓗'}(w) = (1-ρ)(n-1 ± βn)` at every vertex;

the same holds for a reservoir of Type `B` under the additional numerical
assumption `2ρ(n-1) + 1 ≤ εn` (the paper's `3ρ ≤ ε`).

The proof follows the paper: with

`d_{𝓗 ∖ E(G)}(w) ≤ (n - 1 - d_G(w))/2`

one shows `d_{𝓗 ∖ R_res}(w) ≤ (1-ρ)(n-1) + ξn` for all `w` (three cases, one
for each reservoir type; the estimates are the contents of
`hdeg_sdiff_le_A` and `hdeg_sdiff_le_B`), and then takes
`k := ⌊(1-ρ)(n-1) - βn/2⌋` and adds `k - d(w)` singletons at every vertex `w`
with `d(w) < k`.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

theorem hdeg_mono {𝓕 𝓗 : Hypergraph (Fin n)} (h : 𝓕 ⊆ 𝓗) (w : Fin n) :
    MultiHypergraph.hdeg 𝓕 w ≤ MultiHypergraph.hdeg 𝓗 w :=
  Set.ncard_le_ncard (fun e he => ⟨h he.1, he.2⟩) (Set.toFinite _)

/-- For a family of 2-element edges, the degree of `w` is its degree in `G`. -/
theorem hdeg_pow2_eq_degAt (𝓗 : Hypergraph (Fin n)) (w : Fin n) :
    MultiHypergraph.hdeg 𝓗.pow2 w = degAt 𝓗.pow2 w :=
  hdeg_eq_degAt _ (fun e he => by rw [← edgeSize_eq_ncard]; exact (mem_pow2.mp he).2) w

/-- The two-sided degree estimate given by `Typical` at `V(𝓗)`. -/
theorem absorber_degAt_abs {G' Rabs : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {ρ ξ : ℝ} (hVuniv : (Set.univ : Set (Fin n)) ∈ 𝓥) (htyp : Typical G' Rabs ρ ξ 𝓥)
    (v : Fin n) :
    |((degAt Rabs v : ℝ)) - ρ * (degAt G' v : ℝ)| ≤ ξ * (n : ℝ) := by
  have h1 := (htyp Set.univ hVuniv v).1
  simp only [Set.univ_inter] at h1
  rwa [degAt, degAt]

/-- The parameter hierarchy used by the Regularising Lemma. -/
structure DegreeMargins (n : ℕ) (ρ ξ ε β : ℝ) (r₁ : ℕ) : Prop where
  hρ0 : 0 < ρ
  hρhalf : ρ ≤ 1 / 2
  hε0 : 0 < ε
  hξ0 : 0 ≤ ξ
  hβ0 : 0 < β
  hr1 : 2 ≤ r₁
  hξβ : 8 * ξ ≤ β
  hβr1 : 16 ≤ β * (r₁ : ℝ)
  hβn : 24 ≤ β * (n : ℝ)
  hβhalf : β * (n : ℝ) / 2 ≤ (1 - ρ) * ((n : ℝ) - 1)

/-- The degree estimate `d_{𝓗∖R_res}(w) ≤ (1-ρ)(n-1) + ξn` for a reservoir of
Type `A₁` or `A₂` (equation `eqn:estimate_hsmall` of the paper). -/
theorem hdeg_sdiff_le_A (𝓗 Rres : Hypergraph (Fin n)) {ρ ξ : ℝ}
    (hn1 : 1 ≤ n) (hρhalf : ρ ≤ 1 / 2) (hRsub : Rres ⊆ 𝓗.pow2)
    (hE1 : ∀ w : Fin n, (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) ≤
      (((n : ℝ) - 1) - (degAt 𝓗.pow2 w : ℝ)) / 2)
    (w : Fin n) (hlow : ρ * (degAt 𝓗.pow2 w : ℝ) - ξ * (n : ℝ) ≤ (degAt Rres w : ℝ)) :
    (MultiHypergraph.hdeg (𝓗 \ Rres) w : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) + ξ * (n : ℝ) := by
  have hR2 : ∀ e ∈ 𝓗.pow2, e.ncard = 2 :=
    fun e he => by rw [← edgeSize_eq_ncard]; exact (mem_pow2.mp he).2
  have hdG : (degAt 𝓗.pow2 w : ℝ) ≤ (n : ℝ) - 1 := by
    have h := degAt_le_pred 𝓗.pow2 hR2 w
    have h' : (degAt 𝓗.pow2 w : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rwa [Nat.cast_sub hn1, Nat.cast_one] at h'
  have hdec : 𝓗 \ Rres = (𝓗.pow2 \ Rres) ∪ (𝓗 \ 𝓗.pow2) := by
    ext e
    constructor
    · intro he
      by_cases h : e ∈ 𝓗.pow2
      · exact Or.inl ⟨h, he.2⟩
      · exact Or.inr ⟨he.1, h⟩
    · intro he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨powFam_subset 𝓗 2 h1, h2⟩
      · exact ⟨h1, fun h => h2 (hRsub h)⟩
  have hdisj : Disjoint (𝓗.pow2 \ Rres) (𝓗 \ 𝓗.pow2) := by
    rw [Set.disjoint_left]
    exact fun e h1 h2 => h2.2 h1.1
  have hcast : (MultiHypergraph.hdeg (𝓗.pow2 \ Rres) w : ℝ) =
      (degAt 𝓗.pow2 w : ℝ) - (degAt Rres w : ℝ) := by
    have h1 := hdeg_sdiff hRsub w
    have h2 : MultiHypergraph.hdeg Rres w ≤ MultiHypergraph.hdeg 𝓗.pow2 w :=
      hdeg_mono hRsub w
    have h3 : (MultiHypergraph.hdeg (𝓗.pow2 \ Rres) w : ℝ) =
        (MultiHypergraph.hdeg 𝓗.pow2 w : ℝ) - (MultiHypergraph.hdeg Rres w : ℝ) := by
      rw [h1, Nat.cast_sub h2]
    have h4 : MultiHypergraph.hdeg Rres w = degAt Rres w :=
      hdeg_eq_degAt Rres (fun e he => hR2 e (hRsub he)) w
    rw [h3, hdeg_pow2_eq_degAt, h4]
  have hE1w := hE1 w
  have hmain : (1 / 2 - ρ) * (degAt 𝓗.pow2 w : ℝ) + ((n : ℝ) - 1) / 2 + ξ * (n : ℝ) ≤
      (1 - ρ) * ((n : ℝ) - 1) + ξ * (n : ℝ) := by
    nlinarith [hdG, hρhalf]
  calc (MultiHypergraph.hdeg (𝓗 \ Rres) w : ℝ)
      = (MultiHypergraph.hdeg (𝓗.pow2 \ Rres) w : ℝ) +
        (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) := by
        rw [hdec, hdeg_union hdisj, Nat.cast_add]
    _ = ((degAt 𝓗.pow2 w : ℝ) - (degAt Rres w : ℝ)) +
        (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) := by rw [hcast]
    _ ≤ (1 / 2 - ρ) * (degAt 𝓗.pow2 w : ℝ) + ((n : ℝ) - 1) / 2 + ξ * (n : ℝ) := by
        linarith
    _ ≤ (1 - ρ) * ((n : ℝ) - 1) + ξ * (n : ℝ) := hmain

/-- The degree estimate `d_{𝓗∖R_res}(w) ≤ (1-ρ)(n-1) + ξn` for a reservoir of
Type `B` (an absorber for `G'`), under the numerical assumption
`2ρ(n-1) + 1 ≤ εn` (the paper's `3ρ ≤ ε`). -/
theorem hdeg_sdiff_le_B (𝓗 Rres : Hypergraph (Fin n)) {ρ ξ ε : ℝ}
    (hn1 : 1 ≤ n) (hρ0 : 0 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (hmargB : 2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ))
    (hRsub : Rres ⊆ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)))
    (hE1 : ∀ w : Fin n, (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) ≤
      (((n : ℝ) - 1) - (degAt 𝓗.pow2 w : ℝ)) / 2)
    (w : Fin n)
    (hlow : ρ * (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) - ξ * (n : ℝ) ≤
      (degAt Rres w : ℝ)) :
    (MultiHypergraph.hdeg (𝓗 \ Rres) w : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) + ξ * (n : ℝ) := by
  have hR2 : ∀ e ∈ 𝓗.pow2, e.ncard = 2 :=
    fun e he => by rw [← edgeSize_eq_ncard]; exact (mem_pow2.mp he).2
  have hG'sub : incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) ⊆ 𝓗.pow2 :=
    incidentTwo_subset_pow2 𝓗 _
  have hG2 : ∀ e ∈ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)), e.ncard = 2 :=
    fun e he => hR2 e (hG'sub he)
  have hpow2G' : 𝓗.pow2 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) ⊆ 𝓗.pow2 :=
    Set.sdiff_subset
  -- degrees
  have h1 : (MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) \ Rres) w : ℝ) =
      (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) - (degAt Rres w : ℝ) := by
    have hs := hdeg_sdiff hRsub w
    have hmono : MultiHypergraph.hdeg Rres w ≤
        MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w := hdeg_mono hRsub w
    have h3 : (MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) \ Rres) w : ℝ) =
        (MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) -
          (MultiHypergraph.hdeg Rres w : ℝ) := by
      rw [hs, Nat.cast_sub hmono]
    have h4 : MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w =
        degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w := hdeg_eq_degAt _ hG2 w
    have h5 : MultiHypergraph.hdeg Rres w = degAt Rres w :=
      hdeg_eq_degAt Rres (fun e he => hR2 e (hG'sub (hRsub he))) w
    rw [h3, h4, h5]
  have h2 : (MultiHypergraph.hdeg (𝓗.pow2 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) =
      (degAt 𝓗.pow2 w : ℝ) - (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) := by
    have hs := hdeg_sdiff hG'sub w
    have hmono : MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w ≤
        MultiHypergraph.hdeg 𝓗.pow2 w := hdeg_mono hG'sub w
    have h3 : (MultiHypergraph.hdeg (𝓗.pow2 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) =
        (MultiHypergraph.hdeg 𝓗.pow2 w : ℝ) -
          (MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) := by
      rw [hs, Nat.cast_sub hmono]
    rw [h3, hdeg_pow2_eq_degAt, hdeg_eq_degAt _ hG2 w]
  -- decomposition
  have hdec1 : 𝓗 \ Rres = (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) \ Rres) ∪
      (𝓗 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) := by
    ext e
    constructor
    · intro he
      by_cases h : e ∈ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))
      · exact Or.inl ⟨h, he.2⟩
      · exact Or.inr ⟨he.1, h⟩
    · intro he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(hG'sub h1).1, h2⟩
      · exact ⟨h1, fun h => h2 (hRsub h)⟩
  have hdisj1 : Disjoint (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) \ Rres)
      (𝓗 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) := by
    rw [Set.disjoint_left]
    exact fun e h1 h2 => h2.2 h1.1
  have hdec2 : 𝓗 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) =
      (𝓗.pow2 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) ∪ (𝓗 \ 𝓗.pow2) := by
    ext e
    constructor
    · intro he
      by_cases h : e ∈ 𝓗.pow2
      · exact Or.inl ⟨h, he.2⟩
      · exact Or.inr ⟨he.1, h⟩
    · intro he
      rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.1, h2⟩
      · exact ⟨h1, fun h => h2 (hG'sub h)⟩
  have hdisj2 : Disjoint (𝓗.pow2 \ incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) (𝓗 \ 𝓗.pow2) := by
    rw [Set.disjoint_left]
    exact fun e h1 h2 => h2.2 h1.1
  have hsplit : (MultiHypergraph.hdeg (𝓗 \ Rres) w : ℝ) =
      (MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) \ Rres) w : ℝ) +
      ((degAt 𝓗.pow2 w : ℝ) - (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ)) +
      (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) := by
    rw [hdec1, hdeg_union hdisj1, Nat.cast_add, hdec2, hdeg_union hdisj2, Nat.cast_add, h2, h1]
    ring
  rw [hsplit]
  by_cases hw : w ∈ Vplus 𝓗 (1 - ε)
  · have hdegEq : degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w = degAt 𝓗.pow2 w :=
      degAt_incidentTwo_eq 𝓗 hw
    have hdG : (degAt 𝓗.pow2 w : ℝ) ≤ (n : ℝ) - 1 := by
      have h := degAt_le_pred 𝓗.pow2 hR2 w
      have h' : (degAt 𝓗.pow2 w : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_sub hn1, Nat.cast_one] at h'
    rw [hdegEq] at hlow ⊢
    nlinarith [hlow, hE1 w, hdG, hρhalf]
  · have hb : (degAt 𝓗.pow2 w : ℝ) < (1 - ε) * (n : ℝ) := not_le.mp hw
    have ha : 0 ≤ (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) := Nat.cast_nonneg _
    have hstep1 : (MultiHypergraph.hdeg (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε)) \ Rres) w : ℝ) ≤
        (1 - ρ) * (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) + ξ * (n : ℝ) := by
      rw [h1]
      linarith [hlow]
    have hmain : (1 - ρ) * (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) + ξ * (n : ℝ) +
        ((degAt 𝓗.pow2 w : ℝ) - (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ)) +
        (((n : ℝ) - 1) - (degAt 𝓗.pow2 w : ℝ)) / 2 ≤
        (1 - ρ) * ((n : ℝ) - 1) + ξ * (n : ℝ) := by
      nlinarith [hb.le, ha, hmargB, hρ0]
    linarith [hstep1, hE1 w, hmain]

/-- **Lemma 11.3 (`lem:degree-lemma`), core form.**  Given the two numerical
bounds `hE1` (`d_{𝓗∖E(G)}(w) ≤ (n-1-d_G(w))/2`) and `hsmall`
(`d_𝓗(w) - d_{𝓗_small}(w) ≤ 2n/r₁`), a reservoir `R_res` of Type `A₁`, `A₂` or
`B` can be extended to a multi-hypergraph `𝓗'` obtained from
`𝓗_small ∖ R_res` by adding singleton edges, contained in `𝓗_reg`, with
`d_{𝓗'}(w) = (1-ρ)(n-1 ± βn)`. -/
theorem regularising_lemma_core (𝓗 Rres : Hypergraph (Fin n)) (𝓥 : Set (Set (Fin n)))
    {ρ ξ ε β : ℝ} {r₁ : ℕ} (hm : DegreeMargins n ρ ξ ε β r₁)
    (hlin : 𝓗.IsLinear) (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e)
    (hV : (Set.univ : Set (Fin n)) ∈ 𝓥)
    (hres : IsReservoirTypeA1 𝓗 Rres 𝓥 ρ ξ ε ∨ IsReservoirTypeA2 𝓗 Rres 𝓥 ρ ξ ε ∨
            (IsReservoirTypeB 𝓗 Rres 𝓥 ρ ξ ε ∧ 2 * ρ * ((n : ℝ) - 1) + 1 ≤ ε * (n : ℝ)))
    (hE1 : ∀ w : Fin n, (MultiHypergraph.hdeg (𝓗 \ 𝓗.pow2) w : ℝ) ≤
      (((n : ℝ) - 1) - (degAt 𝓗.pow2 w : ℝ)) / 2)
    (hsmall : ∀ w : Fin n, (MultiHypergraph.hdeg 𝓗 w : ℝ) -
      (MultiHypergraph.hdeg (𝓗.smallEdges r₁) w : ℝ) ≤ 2 * (n : ℝ) / (r₁ : ℝ)) :
    ∃ 𝓗' : MultiHypergraph n,
      𝓗'.edges = 𝓗.smallEdges r₁ \ Rres ∧
      𝓗' ≤ MultiHypergraph.regHypergraph 𝓗 ∧
      𝓗'.IsLinear ∧
      ∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (1 - ρ) * ((n : ℝ) - 1)| ≤ 2 / 3 * β * (n : ℝ) := by
  classical
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hh := hm.hβhalf
    rw [hn0] at hh
    norm_num at hh
    linarith [hm.hρ0, hm.hρhalf]
  -- the reservoir is contained in the 2-graph
  have hRpow : Rres ⊆ 𝓗.pow2 := by
    rcases hres with h | h | h
    · exact h.1
    · exact h.1
    · exact fun e he => (h.1.1 he).1
  -- ## Step 1: `d_{𝓗 ∖ R_res}(w) ≤ (1-ρ)(n-1) + ξn`
  have hstep : ∀ w : Fin n, (MultiHypergraph.hdeg (𝓗 \ Rres) w : ℝ) ≤
      (1 - ρ) * ((n : ℝ) - 1) + ξ * (n : ℝ) := by
    intro w
    rcases hres with h | h | h
    · refine hdeg_sdiff_le_A 𝓗 Rres hn1 hm.hρhalf h.1 hE1 w ?_
      have h1 := (abs_le.mp (h.2.1 w)).1
      linarith
    · obtain ⟨Rabs, Rreg, hEq, habs, hlowreg, hreg⟩ := h.2
      refine hdeg_sdiff_le_A 𝓗 Rres hn1 hm.hρhalf h.1 hE1 w ?_
      rw [hEq]
      by_cases hw : w ∈ Vplus 𝓗 (1 - ε)
      · have h1 := (abs_le.mp (hreg.1 w hw)).1
        linarith
      · have h1 := (hreg.2 w hw).1
        have h2 : ρ * (degAt 𝓗.pow2 w : ℝ) ≤ (degAt (Rabs ∪ Rreg) w : ℝ) :=
          le_trans (le_max_left _ _) h1
        have h3 : 0 ≤ ξ * (n : ℝ) := mul_nonneg hm.hξ0 (Nat.cast_nonneg (α := ℝ) n)
        linarith
    · refine hdeg_sdiff_le_B 𝓗 Rres hn1 (le_of_lt hm.hρ0) hm.hρhalf h.2
        h.1.1 hE1 w ?_
      have h1 := (abs_le.mp (absorber_degAt_abs hV h.1.2.1 w)).1
      linarith
  -- ## Step 2: `d_{R_res}(w) ≤ (ρ+ξ)n`
  have hRup : ∀ w : Fin n, (degAt Rres w : ℝ) ≤ (ρ + ξ) * (n : ℝ) := by
    intro w
    rcases hres with h | h | h
    · have h1 := (abs_le.mp (h.2.1 w)).2
      have h2 : (degAt 𝓗.pow2 w : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast degAt_le_n 𝓗.pow2 w
      nlinarith [h1, h2, le_of_lt hm.hρ0]
    · obtain ⟨Rabs, Rreg, hEq, habs, hlowreg, hreg⟩ := h.2
      rw [hEq]
      by_cases hw : w ∈ Vplus 𝓗 (1 - ε)
      · have h1 := (abs_le.mp (hreg.1 w hw)).2
        have h2 : (degAt 𝓗.pow2 w : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast degAt_le_n 𝓗.pow2 w
        nlinarith [h1, h2, le_of_lt hm.hρ0]
      · have h1 := (hreg.2 w hw).2
        have h3 : 0 ≤ ρ * ε * (n : ℝ) :=
          mul_nonneg (mul_nonneg (le_of_lt hm.hρ0) (le_of_lt hm.hε0))
            (Nat.cast_nonneg (α := ℝ) n)
        nlinarith [h1, h3]
    · have h1 := (abs_le.mp (absorber_degAt_abs hV h.1.2.1 w)).2
      have h2 : (degAt (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast degAt_le_n (incidentTwo 𝓗 (Vplus 𝓗 (1 - ε))) w
      nlinarith [h1, h2, le_of_lt hm.hρ0]
  -- ## Step 3: the number `k` of singleton edges added at each vertex
  set k : ℕ := ⌊(1 - ρ) * ((n : ℝ) - 1) - β * (n : ℝ) / 2⌋₊ with hk
  have hkub : (k : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) - β * (n : ℝ) / 2 := by
    rw [hk]
    exact Nat.floor_le (by linarith [hm.hβhalf])
  have hklb : (1 - ρ) * ((n : ℝ) - 1) - 2 / 3 * β * (n : ℝ) ≤ (k : ℝ) := by
    rw [hk]
    have h1 := Nat.lt_floor_add_one ((1 - ρ) * ((n : ℝ) - 1) - β * (n : ℝ) / 2)
    nlinarith [h1, hm.hβn]
  -- ## Step 4: the identification of `𝓗_small`
  have hpowsmall : Rres ⊆ 𝓗.smallEdges r₁ := by
    intro e he
    refine (mem_smallEdges 𝓗 r₁ e).mpr ⟨(mem_pow2.mp (hRpow he)).1, ?_⟩
    rw [edgeSize_eq_ncard]
    have h2 := (mem_pow2.mp (hRpow he)).2
    rw [edgeSize_eq_ncard] at h2
    exact le_trans (le_of_eq h2) hm.hr1
  refine ⟨MultiHypergraph.addSingletons (𝓗.smallEdges r₁ \ Rres) k, ?_, ?_, ?_, ?_⟩
  · rw [MultiHypergraph.edges_addSingletons]
  · refine ⟨?_, ?_⟩
    · intro e he
      exact ((mem_smallEdges 𝓗 r₁ e).mp he.1).1
    · intro w
      rw [MultiHypergraph.singles_addSingletons, MultiHypergraph.singles_regHypergraph]
      have hFsub : 𝓗.smallEdges r₁ \ Rres ⊆ 𝓗 \ Rres := by
        intro e he
        exact ⟨(mem_smallEdges 𝓗 r₁ e).mp he.1 |>.1, he.2⟩
      have hdegF : MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w =
          MultiHypergraph.hdeg (𝓗.smallEdges r₁) w - MultiHypergraph.hdeg Rres w :=
        hdeg_sdiff hpowsmall w
      have hRdeg : MultiHypergraph.hdeg Rres w = degAt Rres w :=
        hdeg_eq_degAt Rres (fun e he => by
          rw [← edgeSize_eq_ncard]; exact (mem_pow2.mp (hRpow he)).2) w
      by_cases hk' : MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w < k
      · have hbound : (k : ℝ) - (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w : ℝ) ≤
            (n : ℝ) - 3 - (MultiHypergraph.hdeg 𝓗 w : ℝ) := by
          have hB : (MultiHypergraph.hdeg 𝓗 w : ℝ) -
              (MultiHypergraph.hdeg (𝓗.smallEdges r₁) w : ℝ) ≤ 2 * (n : ℝ) / (r₁ : ℝ) :=
            hsmall w
          have hρξ : (MultiHypergraph.hdeg Rres w : ℝ) ≤ (ρ + ξ) * (n : ℝ) := by
            rw [hRdeg]; exact hRup w
          have hsub : MultiHypergraph.hdeg Rres w ≤ MultiHypergraph.hdeg (𝓗.smallEdges r₁) w :=
            hdeg_mono hpowsmall w
          have hr1pos : (0 : ℝ) < (r₁ : ℝ) := by
            have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hm.hr1
            linarith
          have h2n : 2 * (n : ℝ) / (r₁ : ℝ) ≤ β * (n : ℝ) / 8 := by
            rw [div_le_iff₀ hr1pos]
            nlinarith [hm.hβr1, hm.hβ0, Nat.cast_nonneg (α := ℝ) n]
          have hξn : ξ * (n : ℝ) ≤ β * (n : ℝ) / 8 := by
            nlinarith [hm.hξβ, hm.hξ0, Nat.cast_nonneg (α := ℝ) n]
          have hcast : (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w : ℝ) =
              (MultiHypergraph.hdeg (𝓗.smallEdges r₁) w : ℝ) -
                (MultiHypergraph.hdeg Rres w : ℝ) := by
            rw [hdegF, Nat.cast_sub hsub]
          rw [hcast]
          nlinarith [hkub, hB, hρξ, h2n, hξn, hm.hβn, hm.hρ0, hm.hρhalf]
        have hℝ : (((k - MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w) +
            MultiHypergraph.hdeg 𝓗 w + 3 : ℕ) : ℝ) ≤ (n : ℝ) := by
          rw [Nat.cast_add, Nat.cast_add, Nat.cast_ofNat, Nat.cast_sub (le_of_lt hk')]
          linarith [hbound]
        have hℕ : (k - MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w) +
            MultiHypergraph.hdeg 𝓗 w + 3 ≤ n := Nat.cast_le.mp hℝ
        omega
      · have hz : k - MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w = 0 :=
          Nat.sub_eq_zero_of_le (not_lt.mp hk')
        rw [hz]
        exact Nat.zero_le _
  · rw [MultiHypergraph.IsLinear, MultiHypergraph.edges_addSingletons]
    exact ⟨fun e he => hbig e ((mem_smallEdges 𝓗 r₁ e).mp he.1).1,
      Set.Pairwise.mono (fun e he => ((mem_smallEdges 𝓗 r₁ e).mp he.1).1) hlin⟩
  · intro w
    have hFsub : 𝓗.smallEdges r₁ \ Rres ⊆ 𝓗 \ Rres :=
      fun e he => ⟨((mem_smallEdges 𝓗 r₁ e).mp he.1).1, he.2⟩
    have h1 : (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w : ℝ) ≤
        (1 - ρ) * ((n : ℝ) - 1) + ξ * (n : ℝ) := by
      have h2 : (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w : ℝ) ≤
          (MultiHypergraph.hdeg (𝓗 \ Rres) w : ℝ) := by
        exact_mod_cast hdeg_mono hFsub w
      linarith [h2, hstep w]
    have hξn : ξ * (n : ℝ) ≤ 2 / 3 * β * (n : ℝ) := by
      nlinarith [hm.hξβ, hm.hξ0, Nat.cast_nonneg (α := ℝ) n]
    have h2 : (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w : ℝ) ≤
        (1 - ρ) * ((n : ℝ) - 1) + 2 / 3 * β * (n : ℝ) := by linarith
    have h3 : (k : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) + 2 / 3 * β * (n : ℝ) := by
      nlinarith [hkub, le_of_lt hm.hβ0, Nat.cast_nonneg (α := ℝ) n]
    rw [MultiHypergraph.deg_addSingletons, Nat.cast_max, abs_le]
    constructor
    · have h4 := le_max_right (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w : ℝ) (k : ℝ)
      linarith [hklb, h4]
    · have h4 : max (MultiHypergraph.hdeg (𝓗.smallEdges r₁ \ Rres) w : ℝ) (k : ℝ) ≤
          (1 - ρ) * ((n : ℝ) - 1) + 2 / 3 * β * (n : ℝ) := max_le h2 h3
      linarith [h4]

end

end ErdosFaberLovaszConjecture
