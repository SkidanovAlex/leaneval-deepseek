import Submission.EFL.S12Step1
import Submission.EFL.Comm.NcardEqTwo
import Submission.EFL.S12Final

/-!
# §12, Step 1: the constant hierarchy and the Type A/B alternative

The paper's first step applies Theorem 6.7 (`large-edge-thm`) to the medium and
large edges of `𝓗`, i.e. to `medLarge 𝓗 r₁` (all of whose edges satisfy
`r₁ < |e|` by construction), and then splits into the non-extremal (Type A) and
extremal (Type B) cases.

This module formalises:

* `isTypeA_of_nonExtremal_medLarge` / `isTypeB_of_extremal_medLarge`: the
  alternatives of Theorem 6.7, applied to `medLarge 𝓗 r₁`, are *literally* the
  hypotheses `IsTypeA`/`IsTypeB` of §12 (up to reordering the existential
  quantifiers), because `LargeEdgeNonExtremal n σ γ₁ β r₁ r₀ 𝓖` asks for a
  colouring of `𝓖` while `IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ` asks for a colouring of
  `medLarge 𝓗 r₁`; taking `𝓖 = medLarge 𝓗 r₁` makes the two coincide.  (No
  restriction/transport is needed!)
* `s12_step1`: the parameter hierarchy.  The constants are chosen in the order
  forced by `LargeEdgeThmStatement`, namely
  `γ₂ ⊳ δ₀ ⊳ δ ⊳ σ₀ ⊳ σ ⊳ γ₁₀ ⊳ γ₁ ⊳ β₀ ⊳ β ⊳ R₁ ⊳ r₁ ⊳ R₀ ⊳ r₀ ⊳ N₀ ⊳ n`,
  and the result is a colouring `φ` of `medLarge 𝓗 r₁` of Type A or of Type B.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-! ## The alternatives of Theorem 6.7 are the hypotheses `IsTypeA`/`IsTypeB` -/

/-- **Theorem 6.7(a) applied to `medLarge 𝓗 r₁` is (literally) `IsTypeA`.** -/
theorem isTypeA_of_nonExtremal_medLarge {𝓗 : Hypergraph (Fin n)}
    {r₁ r₀ σ γ₁ β : ℝ}
    (h : LargeEdgeNonExtremal n σ γ₁ β r₁ r₀ (medLarge 𝓗 r₁)) :
    ∃ φ : (medLarge 𝓗 r₁).Coloring (Fin n), IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ := by
  obtain ⟨φ, C₁, Cmed, huse, hcard, hsub, hcmc, hmed, hcv, hsing, hvert⟩ := h
  exact ⟨φ, C₁, Cmed, huse, hcard, hsub, hcmc, hmed, hcv, hsing, hvert⟩

/-- **Theorem 6.7(b) applied to `medLarge 𝓗 r₁` is (literally) `IsTypeB`.** -/
theorem isTypeB_of_extremal_medLarge {𝓗 : Hypergraph (Fin n)}
    {r₁ r₀ δ γ₂ γ₁ β : ℝ}
    (h : LargeEdgeExtremal n δ γ₂ γ₁ β r₁ r₀ (medLarge 𝓗 r₁)) :
    ∃ φ : (medLarge 𝓗 r₁).Coloring (Fin n), IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ := by
  obtain ⟨⟨W, hWsub, hWex, hWvol⟩, φ, Cmed, hcmc, hmed, hcv, hass, hvert⟩ := h
  exact ⟨φ, ⟨W, hWsub.trans (medLarge_subset 𝓗 r₁), hWex, hWvol⟩, Cmed, hcmc, hmed, hcv,
    hass, hvert⟩


/-! ## The parameter hierarchy -/

/-- **§12, Step 1.**  From the deep inputs Molloy–Reed and Kahn (through
Theorem 6.7, `largeEdgeThmStatement_of_deep`) we obtain the whole constant
hierarchy of the paper's proof:

`γ₂ ⊳ δ ⊳ σ ⊳ γ₁ ⊳ β ⊳ r₁ ⊳ r₀ ⊳ N₀`

with `γ₂` an explicit tiny constant, together with, for every `n ≥ N₀` and every
linear `𝓗` on `n` vertices, a colouring `φ` of `medLarge 𝓗 r₁` that is either of
Type A or of Type B (the two alternatives of Theorem 6.7, applied to
`medLarge 𝓗 r₁`).

The smallness of `γ₂` and the ratios `δ/γ₂`, `σ/δ`, `γ₁/σ`, `β/γ₁` are the
concrete form of the paper's `≪`-hierarchy; the remaining parameters
`ε, ρ, ρ_abs, ξ, κ` are chosen *after* the Type A/Type B split (their admissible
ranges differ between the types: Type A uses `γ := γ₁`, Type B uses
`γ := γ₂`). -/
theorem s12_step1 (hMR : MolloyReedStatement) (hK : KahnStatement) :
    ∃ (γ₂ δ σ γ₁ β : ℝ) (r₁ r₀ N₀ : ℕ),
      (0 < γ₂ ∧ γ₂ ≤ (10 : ℝ) ^ (-30 : ℤ)) ∧
      (0 < δ ∧ δ ≤ γ₂) ∧ (0 < σ ∧ σ ≤ δ) ∧
      (0 < γ₁ ∧ γ₁ ≤ σ ^ 10 / 10 ^ 250) ∧
      (0 < β ∧ β ≤ γ₁ ∧ β ≤ γ₁ ^ 2 / 16 ∧ β ≤ γ₁ ^ 4 / 10 ^ 12) ∧
      10 ≤ r₁ ∧ 2 ≤ r₀ ∧ r₁ < r₀ ∧
      (32 ≤ β * (r₁ : ℝ)) ∧ (r₁ : ℝ) < β * ((r₀ : ℝ) - 1) ∧
      r₁ < γ₁ / 4 * ((r₀ : ℝ) - 1) ∧
      ∀ n ≥ N₀, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → (∀ e ∈ 𝓗, 2 ≤ edgeSize e) →
        ∃ φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin n),
          IsTypeA σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ ∨
          IsTypeB δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 φ := by
  classical
  have hγ₂0 : (0 : ℝ) < (10 : ℝ) ^ (-30 : ℤ) := by positivity
  have hγ₂1 : (10 : ℝ) ^ (-30 : ℤ) ≤ 1 := by norm_num
  obtain ⟨δ₀, hδ₀0, hδ₀γ₂, Hδ⟩ := largeEdgeThmStatement_of_deep hMR hK _ hγ₂0 hγ₂1
  set γ₂ : ℝ := (10 : ℝ) ^ (-30 : ℤ) with hγ₂def
  set δ : ℝ := min δ₀ (γ₂ / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hδ₀0 (by positivity)
  have hδγ₂ : δ ≤ γ₂ := le_trans (min_le_right _ _) (by nlinarith [hγ₂0])
  obtain ⟨σ₀, hσ₀0, hσ₀δ, Hσ⟩ := Hδ δ hδ0 (min_le_left _ _)
  set σ : ℝ := min σ₀ (δ / 2) with hσdef
  have hσ0 : 0 < σ := lt_min hσ₀0 (by linarith)
  have hσδ : σ ≤ δ := le_trans (min_le_right _ _) (by nlinarith [hδ0])
  obtain ⟨γ₁₀, hγ₁₀0, hγ₁₀σ, Hγ₁⟩ := Hσ σ hσ0 (min_le_left _ _)
  have hσle1 : σ ≤ 1 := by linarith only [hσδ, hδγ₂, hγ₂1]
  set γ₁ : ℝ := min γ₁₀ (σ ^ 10 / 10 ^ 250) with hγ₁def
  have hγ₁0 : 0 < γ₁ := lt_min hγ₁₀0 (by positivity)
  have hγ₁sq : γ₁ ≤ σ ^ 10 / 10 ^ 250 := min_le_right _ _
  obtain ⟨β₀, hβ₀0, hβ₀γ₁, Hβ⟩ := Hγ₁ γ₁ hγ₁0 (min_le_left _ _)
  set β : ℝ := min β₀ (min (γ₁ / 2) (min (γ₁ ^ 2 / 16) (γ₁ ^ 4 / 10 ^ 12)))
    with hβdef
  have hβ0 : 0 < β :=
    lt_min hβ₀0 (lt_min (by linarith) (lt_min (by positivity) (by positivity)))
  have hβγ₁ : β ≤ γ₁ := by
    refine le_trans (min_le_right _ _) ?_
    exact le_trans (min_le_left _ _) (by linarith only [hγ₁0])
  -- `β ≪ γ₁²`: the separation used by the Nibble Lemma of §7
  have hβsq : β ≤ γ₁ ^ 2 / 16 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  -- `β ≪ γ₁⁴`: the extra separation the *corrected* Nibble margins need (the §7
  -- assembly chooses `K = ⌈κ⁻¹⌉` with `κ ≲ γ²`, so it needs `β ≲ γ⁴`)
  have hβ4 : β ≤ γ₁ ^ 4 / 10 ^ 12 := by
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨R₁, _hR₁0, HR₁⟩ := Hβ β hβ0 (min_le_left _ _)
  -- `r₁` is chosen large enough that `βr₁ ≥ 32`
  set r₁ : ℕ := max R₁ (max 10 ⌈32 / β⌉₊) with hr₁def
  have hr₁ : R₁ ≤ r₁ := le_max_left _ _
  have h10r₁ : 10 ≤ r₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hceil₁ : (⌈32 / β⌉₊ : ℝ) ≤ (r₁ : ℝ) := by
    exact_mod_cast (le_trans (le_max_right _ _) (le_max_right _ _))
  have hβr₁ : 32 ≤ β * (r₁ : ℝ) := by
    have h1 : 32 / β ≤ (⌈32 / β⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (32 : ℝ) ≤ β * (⌈32 / β⌉₊ : ℝ) := by
      rw [div_le_iff₀ hβ0] at h1
      linarith
    nlinarith [hβ0, hceil₁, Nat.cast_nonneg (α := ℝ) ⌈32 / β⌉₊]
  obtain ⟨R₀, _hR₀0, HR₀⟩ := HR₁ r₁ hr₁
  -- `r₀` is chosen large enough that `2r₁ ≤ γ₁(r₀-1)` and `r₁ < β(r₀-1)`
  set M : ℕ := max 2 (⌈max (4 * (r₁ : ℝ) / γ₁) ((r₁ : ℝ) / β)⌉₊ + 2) with hMdef
  set r₀ : ℕ := max R₀ M with hr₀def
  have hr₀ : R₀ ≤ r₀ := le_max_left _ _
  have hMr₀ : M ≤ r₀ := le_max_right _ _
  have hr₀2 : 2 ≤ r₀ := le_trans (le_max_left _ _) hMr₀
  have hceil₂ : (⌈max (4 * (r₁ : ℝ) / γ₁) ((r₁ : ℝ) / β)⌉₊ : ℝ) + 2 ≤ (r₀ : ℝ) := by
    have h1 : ⌈max (4 * (r₁ : ℝ) / γ₁) ((r₁ : ℝ) / β)⌉₊ + 2 ≤ M := le_max_right _ _
    have h2 : M ≤ r₀ := hMr₀
    exact_mod_cast (le_trans h1 h2)
  have hγ₁1 : γ₁ ≤ 1 := by
    have h1 : σ ^ 10 ≤ 1 := pow_le_one₀ (le_of_lt hσ0) hσle1 (n := 10)
    have h2 : σ ^ 10 / 10 ^ 250 ≤ 1 := by linarith only [h1]
    linarith only [hγ₁sq, h2]
  have hr₁γ₁ : (r₁ : ℝ) < γ₁ / 4 * ((r₀ : ℝ) - 1) := by
    set C : ℝ := (⌈max (4 * (r₁ : ℝ) / γ₁) ((r₁ : ℝ) / β)⌉₊ : ℝ) with hC
    have hC2 : C + 2 ≤ (r₀ : ℝ) := by rw [hC]; exact hceil₂
    have h1 : 4 * (r₁ : ℝ) / γ₁ ≤ C := by
      rw [hC]
      exact le_trans (le_max_left _ _) (Nat.le_ceil _)
    have h2 : 4 * (r₁ : ℝ) / γ₁ ≤ (r₀ : ℝ) - 2 := by linarith
    have h3 : 4 * (r₁ : ℝ) ≤ ((r₀ : ℝ) - 2) * γ₁ := by
      rw [div_le_iff₀ hγ₁0] at h2
      linarith
    have h4 : ((r₀ : ℝ) - 2) * γ₁ < ((r₀ : ℝ) - 1) * γ₁ := by nlinarith [hγ₁0]
    nlinarith
  have hr₁β' : (r₁ : ℝ) < β * ((r₀ : ℝ) - 1) := by
    set C : ℝ := (⌈max (4 * (r₁ : ℝ) / γ₁) ((r₁ : ℝ) / β)⌉₊ : ℝ) with hC
    have hC2 : C + 2 ≤ (r₀ : ℝ) := by rw [hC]; exact hceil₂
    have h1 : (r₁ : ℝ) / β ≤ C := by
      rw [hC]
      exact le_trans (le_max_right _ _) (Nat.le_ceil _)
    have h2 : (r₁ : ℝ) / β ≤ (r₀ : ℝ) - 2 := by linarith
    have h3 : (r₁ : ℝ) ≤ ((r₀ : ℝ) - 2) * β := by
      rw [div_le_iff₀ hβ0] at h2
      linarith
    have h4 : ((r₀ : ℝ) - 2) * β < ((r₀ : ℝ) - 1) * β := by nlinarith [hβ0]
    linarith
  have hr₁r₀ : r₁ < r₀ := by
    have h1 : (r₁ : ℝ) < γ₁ / 4 * ((r₀ : ℝ) - 1) := hr₁γ₁
    have h2 : γ₁ / 4 * ((r₀ : ℝ) - 1) ≤ (r₀ : ℝ) := by nlinarith [hγ₁0, hγ₁1, hr₀2]
    have h3 : ((r₁ : ℕ) : ℝ) < (r₀ : ℝ) := lt_of_lt_of_le h1 h2
    exact_mod_cast h3
  obtain ⟨N₀, _hN₀0, HN₀⟩ := HR₀ r₀ hr₀
  refine ⟨γ₂, δ, σ, γ₁, β, r₁, r₀, N₀, ⟨hγ₂0, le_rfl⟩, ⟨hδ0, hδγ₂⟩, ⟨hσ0, hσδ⟩,
    ⟨hγ₁0, hγ₁sq⟩, ⟨hβ0, hβγ₁, hβsq, hβ4⟩, h10r₁, hr₀2, hr₁r₀, ?_, hr₁β', hr₁γ₁, ?_⟩
  · exact_mod_cast hβr₁
  · intro n hn 𝓗 hlin _
    have hlin' : (medLarge 𝓗 (r₁ : ℝ)).IsLinear := IsLinear.medLarge hlin
    have hbig' : ∀ e : ↥(medLarge 𝓗 (r₁ : ℝ)), (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ) :=
      fun e => e.2.2
    rcases HN₀ n hn (medLarge 𝓗 (r₁ : ℝ)) hbig' hlin' with h | h
    · exact (isTypeA_of_nonExtremal_medLarge h).imp (fun _ hφ => Or.inl hφ)
    · exact (isTypeB_of_extremal_medLarge h).imp (fun _ hφ => Or.inr hφ)

/-! ## `V^{(n-1)}(𝓗) ⊆ {v : d_G(v) = n-1}`

The paper's `(eqn:rs)` for Type A₁ bounds the size of the defect set
`S = U ∖ V^{(n-1)}(𝓗)`, and `¬ IsFull 𝓗 ρ ε` bounds
`VeqNat 𝓗 (n-1) = {v : d_G(v) = n-1}`.  The bridge is the elementary fact that
a vertex of degree `n-1` in a linear hypergraph lies only in 2-edges (recorded
by the hypothesis `hcount` below, whose proof is pure counting:
`Submission.Commons.Combinatorics.Hypergraph.ncard_eq_two_of_mem_ncard_pred`):

if `d_𝓗(v) = n-1` then every edge through `v` has exactly two vertices,
otherwise the `n-1` pairwise disjoint non-empty sets `e ∖ {v}` would cover more
than the `n-1` vertices of `V ∖ {v}`. -/

/-- **`V^{(n-1)}(𝓗) ⊆ VeqNat 𝓗 (n-1)`** given the counting fact `hcount`. -/
theorem Vdeg_pred_subset_VeqNat_of {𝓗 : Hypergraph (Fin n)}
    (hcount : ∀ v : Fin n, MultiHypergraph.hdeg 𝓗 v = n - 1 →
      ∀ e ∈ 𝓗, v ∈ e → e.ncard = 2) :
    Vdeg 𝓗 (n - 1) ⊆ VeqNat 𝓗 (n - 1) := by
  classical
  intro v hv
  rw [mem_Vdeg_iff] at hv
  have h2 : ∀ e ∈ 𝓗, v ∈ e → e.ncard = 2 := fun e he hve => hcount v hv e he hve
  have hEq : ({e ∈ 𝓗.pow2 | v ∈ e} : Set (Set (Fin n))) =
      ({e ∈ 𝓗 | v ∈ e} : Set (Set (Fin n))) := by
    ext e
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨he, -⟩, hve⟩
      exact ⟨he, hve⟩
    · rintro ⟨he, hve⟩
      exact ⟨⟨he, by rw [edgeSize_eq_ncard]; exact h2 e he hve⟩, hve⟩
  have hdeg : MultiHypergraph.hdeg 𝓗.pow2 v = MultiHypergraph.hdeg 𝓗 v := by
    rw [MultiHypergraph.hdeg, MultiHypergraph.hdeg, hEq]
  rw [VeqNat, Set.mem_setOf_eq]
  rw [← hdeg_eq_degAt 𝓗.pow2 (fun e he => by
    rw [← edgeSize_eq_ncard]; exact (mem_pow2.mp he).2) v]
  rw [hdeg, hv]

/-- **`V^{(n-1)}(𝓗) ⊆ VeqNat 𝓗 (n-1)`** for a linear hypergraph all of whose
edges have at least two vertices (via the counting lemma
`Commons.Combinatorics.Hypergraph.ncard_eq_two_of_mem_ncard_pred`). -/
theorem Vdeg_pred_subset_VeqNat {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) :
    Vdeg 𝓗 (n - 1) ⊆ VeqNat 𝓗 (n - 1) :=
  Vdeg_pred_subset_VeqNat_of (fun v hv e he hve =>
    Commons.Combinatorics.Hypergraph.ncard_eq_two_of_mem_ncard_pred hlin
      (fun e he => by have h := hbig e he; rwa [edgeSize_eq_ncard] at h)
      (show ({e ∈ 𝓗 | v ∈ e} : Set (Set (Fin n))).ncard = n - 1 from hv) he hve)

/-! ## `(eqn:rs)`: the size of the defect set `S` for the three types -/

/-- **`(eqn:rs)`, Type A₁.**  Here `S = U ∖ V^{(n-1)}(𝓗)`: since `¬ IsFull` (and
`|U| > (1-10ε)n`, so `IsFull`'s first conjunct holds) gives
`|V^{(n-1)}(𝓗)| < (ρ-15ε)n` -- via `Vdeg_pred_subset_VeqNat` -- we get
`|S| ≥ |U| - |V^{(n-1)}(𝓗)| > (1-ρ+5ε)n`. -/
theorem S_big_typeA1 {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hbig : ∀ e ∈ 𝓗, 2 ≤ edgeSize e) {ρ ε : ℝ} {U : Set (Fin n)}
    (hU : U = Vplus 𝓗 (1 - ε)) (hnfull : ¬ IsFull 𝓗 ρ ε) (hVn1U : Vn1set 𝓗 ⊆ U) :
    (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ ((U \ Vn1set 𝓗).ncard : ℝ) := by
  intro hUbig
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  -- `IsFull`'s first conjunct holds, so `¬ IsFull` bounds `VeqNat`
  have hA : (1 - 10 * ε) * (n : ℝ) ≤ ((Vplus 𝓗 (1 - ε)).ncard : ℝ) := by
    rw [← hU]; exact le_of_lt hUbig
  have hB : ¬ ((ρ - 15 * ε) * (n : ℝ) ≤ ((VeqNat 𝓗 (n - 1)).ncard : ℝ)) :=
    fun h => hnfull ⟨hA, h⟩
  have hVn1le : ((Vn1set 𝓗).ncard : ℝ) < (ρ - 15 * ε) * (n : ℝ) := by
    have hsub : Vn1set 𝓗 ⊆ VeqNat 𝓗 (n - 1) := Vdeg_pred_subset_VeqNat hlin hbig
    have h1 : ((Vn1set 𝓗).ncard : ℝ) ≤ ((VeqNat 𝓗 (n - 1)).ncard : ℝ) := by
      exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    exact lt_of_le_of_lt h1 (not_le.mp hB)
  -- `|U| = |S| + |Vn1|` (since `Vn1 ⊆ U`)
  have hsdiff : (U \ Vn1set 𝓗).ncard + (Vn1set 𝓗).ncard = U.ncard :=
    Set.ncard_sdiff_add_ncard_of_subset hVn1U
  have hcast : ((U \ Vn1set 𝓗).ncard : ℝ) =
      (U.ncard : ℝ) - ((Vn1set 𝓗).ncard : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hsdiff
    push_cast at h
    linarith
  linarith

/-- **`(eqn:rs)`, Types A₂ and B.**  Here `S = U`, so the estimate is the pure
inequality `15ε ≤ ρ`. -/
theorem S_big_typeA2 {ρ ε : ℝ} {U : Set (Fin n)} (h : 15 * ε ≤ ρ) :
    (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ (U.ncard : ℝ) := by
  intro hUbig
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [hUbig, h, hn0]

/-- **`(eqn:rs)`, Type B.**  Vacuous: `EP3` gives `|U| ≤ 2δn < (1-10ε)n`. -/
theorem S_big_typeB {δ ρ ε : ℝ} {U : Set (Fin n)} (hU : (U.ncard : ℝ) ≤ 2 * δ * (n : ℝ))
    (h : 2 * δ < 1 - 10 * ε) :
    (1 - 10 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) ≤ (U.ncard : ℝ) := by
  intro hUbig
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exfalso
  nlinarith [hUbig, hU, h, hn0]

end

end ErdosFaberLovaszConjecture
