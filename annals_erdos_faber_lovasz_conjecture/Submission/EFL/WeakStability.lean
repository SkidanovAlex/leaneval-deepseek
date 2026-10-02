import Submission.EFL.StabilityLoop
import Submission.EFL.LocallySparse
import Submission.EFL.DeepInputs
import Submission.EFL.ColourCombine
import Submission.EFL.Counting
import Submission.EFL.SubfamilyConcat

/-!
# Theorem 1.3 of the paper: weak stability

The paper's Theorem 1.3 (`weak-stability-thm`): for every `ε > 0` there are
`n₀` and `η > 0` such that every `n`-vertex linear hypergraph (`n ≥ n₀`)
with maximum degree at most `ηn` and *no edge of size in `(η√n, √n/η)`*
has chromatic index at most `εn`.

The proof (paper §6.1) splits `𝓗` into

* `𝓗₁ = {1/η < |e| < η√n}` — coloured by the *loop* of the reordering lemma
  (`exists_volumeDecomposition`), each volume block by the locally-sparse
  corollary `corollary_6_7` (Alon–Krivelevich–Sudakov) and the good part by
  Proposition 6.9;
* `𝓗₂ = {|e| ≤ 1/η}` — coloured with `3ηn/2` colours by Kahn's theorem;
* `𝓗₃ = {|e| ≥ √n/η}` — at most `2η²n` edges (pair double counting), so
  `2η²n` colours suffice (one per edge).

This module sets up the size-class vocabulary (with *real* thresholds, unlike
`EdgeSize.lean`'s integer classes), proves the colourings of `𝓗₂` and `𝓗₃`,
and then attacks `𝓗₁` with the loop.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Edge classes with real thresholds -/

/-- The edges of `𝓗` of size at least `a`. -/
def Hypergraph.sizeGE (𝓗 : Hypergraph (Fin n)) (a : ℝ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ a ≤ (edgeSize e : ℝ)}

/-- The edges of `𝓗` of size at most `a`. -/
def Hypergraph.sizeLE (𝓗 : Hypergraph (Fin n)) (a : ℝ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ (edgeSize e : ℝ) ≤ a}

/-- The edges of `𝓗` of size strictly greater than `a` and at most `b`.  This
is the paper's class `𝓗₁ = {1/η < |e| < η√n}` with the upper end closed, so
that the three classes of Theorem 1.3 cover `𝓗`. -/
def Hypergraph.sizeBetween (𝓗 : Hypergraph (Fin n)) (a b : ℝ) : Hypergraph (Fin n) :=
  {e : Set (Fin n) | e ∈ 𝓗 ∧ a < (edgeSize e : ℝ) ∧ (edgeSize e : ℝ) ≤ b}

@[simp] theorem mem_sizeGE (𝓗 : Hypergraph (Fin n)) (a : ℝ) (e : Set (Fin n)) :
    e ∈ 𝓗.sizeGE a ↔ e ∈ 𝓗 ∧ a ≤ (edgeSize e : ℝ) := Iff.rfl

@[simp] theorem mem_sizeLE (𝓗 : Hypergraph (Fin n)) (a : ℝ) (e : Set (Fin n)) :
    e ∈ 𝓗.sizeLE a ↔ e ∈ 𝓗 ∧ (edgeSize e : ℝ) ≤ a := Iff.rfl

@[simp] theorem mem_sizeBetween (𝓗 : Hypergraph (Fin n)) (a b : ℝ) (e : Set (Fin n)) :
    e ∈ 𝓗.sizeBetween a b ↔ e ∈ 𝓗 ∧ a < (edgeSize e : ℝ) ∧ (edgeSize e : ℝ) ≤ b :=
  Iff.rfl

theorem sizeGE_subset (𝓗 : Hypergraph (Fin n)) (a : ℝ) : 𝓗.sizeGE a ⊆ 𝓗 :=
  fun _ h => h.1

theorem sizeLE_subset (𝓗 : Hypergraph (Fin n)) (a : ℝ) : 𝓗.sizeLE a ⊆ 𝓗 :=
  fun _ h => h.1

theorem sizeBetween_subset (𝓗 : Hypergraph (Fin n)) (a b : ℝ) : 𝓗.sizeBetween a b ⊆ 𝓗 :=
  fun _ h => h.1

theorem IsLinear.sizeGE {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (a : ℝ) :
    (𝓗.sizeGE a).IsLinear := hlin.mono (sizeGE_subset 𝓗 a)

theorem IsLinear.sizeLE {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (a : ℝ) :
    (𝓗.sizeLE a).IsLinear := hlin.mono (sizeLE_subset 𝓗 a)

theorem IsLinear.sizeBetween {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) (a b : ℝ) :
    (𝓗.sizeBetween a b).IsLinear := hlin.mono (sizeBetween_subset 𝓗 a b)

/-- **The cover of Theorem 1.3's decomposition**: if no edge of `𝓗` has size
strictly between `η√n` and `√n/η`, then every edge is in one of the three
classes. -/
theorem cover_size_classes {𝓗 : Hypergraph (Fin n)} {η : ℝ}
    (hno : ∀ e ∈ 𝓗, ¬(η * Real.sqrt n < (edgeSize e : ℝ) ∧
      (edgeSize e : ℝ) < Real.sqrt n / η)) (e : Set (Fin n)) (he : e ∈ 𝓗) :
    e ∈ 𝓗.sizeLE (1 / η) ∨ e ∈ 𝓗.sizeBetween (1 / η) (η * Real.sqrt n) ∨
      e ∈ 𝓗.sizeGE (Real.sqrt n / η) := by
  by_cases h1 : (edgeSize e : ℝ) ≤ 1 / η
  · exact Or.inl ((mem_sizeLE 𝓗 (1 / η) e).mpr ⟨he, h1⟩)
  · have h1' : 1 / η < (edgeSize e : ℝ) := lt_of_not_ge h1
    rcases not_and_or.mp (hno e he) with h | h
    · have h2 : (edgeSize e : ℝ) ≤ η * Real.sqrt n := not_lt.mp h
      exact Or.inr (Or.inl ((mem_sizeBetween 𝓗 (1 / η) (η * Real.sqrt n) e).mpr
        ⟨he, h1', h2⟩))
    · have h2 : Real.sqrt n / η ≤ (edgeSize e : ℝ) := not_lt.mp h
      exact Or.inr (Or.inr ((mem_sizeGE 𝓗 (Real.sqrt n / η) e).mpr ⟨he, h2⟩))

/-! ## Colouring by one colour per edge

A hypergraph with at most `C` edges is `C`-colourable (distinct colours on
distinct edges are always proper). -/

/-- **One colour per edge**: a hypergraph with at most `C` edges is
`C`-colourable. -/
theorem colorable_of_card_le {V : Type*} {𝓖 : Hypergraph V} [Finite 𝓖] {C : ℕ}
    (h : Nat.card 𝓖 ≤ C) : 𝓖.Colorable C := by
  classical
  haveI : Fintype 𝓖 := Fintype.ofFinite 𝓖
  have hcard : Fintype.card 𝓖 ≤ C := by simpa [Nat.card_eq_fintype_card] using h
  refine ⟨{ labels := ?_, isColoring := ?_ }⟩
  · intro e
    exact Fin.castLE hcard (Fintype.equivFin 𝓖 e)
  · intro e₁ e₂ he _
    intro hcol
    exact he ((Fintype.equivFin 𝓖).injective (Fin.castLE_injective hcard hcol))

/-! ## Counting the edges of a linear hypergraph by size -/

/-- The number of edges of size at least `s` (`s ≥ 2`) in a linear hypergraph
on `n` vertices is at most `n(n−1)/(s(s−1))` (pair double counting). -/
theorem card_edgesSizeGE_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) {s : ℕ}
    (hs : 2 ≤ s) :
    Nat.card {e : 𝓗 // s ≤ edgeSize (e : Set (Fin n))} ≤
      n * (n - 1) / (s * (s - 1)) := by
  classical
  haveI : Fintype 𝓗 := Fintype.ofFinite 𝓗
  have h := card_edges_size_ge_le (𝓗 := 𝓗) hlin hs
  rw [card_filter_eq_natCard (α := 𝓗) (p := fun e : 𝓗 =>
    s ≤ edgeSize (e : Set (Fin n)))] at h
  exact h

/-- **Few huge edges**: if every edge of `𝓗` has size at least `a`, then
`𝓗` has at most `n(n−1)/(s(s−1))` edges, for any `s` with `s ≤ ⌈a⌉`. -/
theorem card_sizeGE_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) {a : ℝ} {s : ℕ}
    (hs : 2 ≤ s) (has : (s : ℝ) ≤ (⌈a⌉₊ : ℝ)) :
    Nat.card (𝓗.sizeGE a) ≤ n * (n - 1) / (s * (s - 1)) := by
  classical
  have key : ∀ e : 𝓗.sizeGE a, s ≤ edgeSize (e : Set (Fin n)) := by
    intro e
    have hge : a ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
      ((mem_sizeGE 𝓗 a (e : Set (Fin n))).mp e.2).2
    have hceil : ⌈a⌉₊ ≤ edgeSize (e : Set (Fin n)) := Nat.ceil_le.mpr hge
    have h1 : (⌈a⌉₊ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by exact_mod_cast hceil
    have h3 : (s : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := has.trans h1
    exact_mod_cast h3
  refine (Nat.card_le_card_of_injective (fun e : 𝓗.sizeGE a =>
    (⟨⟨(e : Set (Fin n)), ((mem_sizeGE 𝓗 a (e : Set (Fin n))).mp e.2).1⟩, key e⟩ :
      {f : 𝓗 // s ≤ edgeSize (f : Set (Fin n))})) ?_).trans
    (card_edgesSizeGE_le hlin hs)
  intro x y hxy
  exact Subtype.ext (congrArg (fun t : {f : 𝓗 // s ≤ edgeSize (f : Set (Fin n))} =>
    ((t.1 : 𝓗) : Set (Fin n))) hxy)

/-- **The `𝓗₃` colouring**: at most `n(n−1)/(s(s−1))` colours suffice for the
edges of size at least `a`. -/
theorem colorable_sizeGE {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear) {a : ℝ} {s : ℕ}
    (hs : 2 ≤ s) (has : (s : ℝ) ≤ (⌈a⌉₊ : ℝ)) :
    (𝓗.sizeGE a).Colorable (n * (n - 1) / (s * (s - 1))) := by
  classical
  haveI : Fintype (Set (Fin n)) := Fintype.ofFinite (Set (Fin n))
  exact colorable_of_card_le (card_sizeGE_le (𝓗 := 𝓗) hlin hs has)

/-! ## The `𝓗₂` colouring via Kahn's theorem -/

/-- **Kahn for the small edges**: if `Δ(𝓗) ≤ D` and `1/η ≤ r` with `r ≥ 2`,
then the edges of size at most `1/η` are colourable with `⌈(1+α)D⌉` colours. -/
theorem colorable_sizeLE_of_kahn {α : ℝ} (hα : 0 < α) {r : ℕ} (hr2 : 2 ≤ r) {D₀ : ℝ}
    (hD₀ : 0 < D₀)
    (hKahn : ∀ D : ℝ, D₀ ≤ D → ∀ n : ℕ, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
      ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓗, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r : ℝ)) →
      ∀ c : ℕ, (1 + α) * D ≤ (c : ℝ) → 𝓗.Colorable c)
    {η D : ℝ} (hη0 : 0 < η) (hrη : 1 / η ≤ (r : ℝ)) (hD : D₀ ≤ D)
    {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hΔ : (hypergraphMaxDegree 𝓗 : ℝ) ≤ D) :
    (𝓗.sizeLE (1 / η)).Colorable ⌈(1 + α) * D⌉₊ := by
  refine hKahn D hD n (𝓗.sizeLE (1 / η)) (IsLinear.sizeLE hlin (1 / η)) ?_ ?_
    ⌈(1 + α) * D⌉₊ (Nat.le_ceil _)
  · calc (((hypergraphMaxDegree (𝓗.sizeLE (1 / η)) : ℕ) : ℝ))
        ≤ ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) := by
          exact_mod_cast hypergraphMaxDegree_mono (sizeLE_subset 𝓗 (1 / η))
      _ ≤ D := hΔ
  · intro e
    exact le_trans ((mem_sizeLE 𝓗 (1 / η) (e.1 : Set (Fin n))).mp e.2).2 hrη

/-! ## Colouring a volume block (the AKS input of Theorem 1.3)

A block of the loop is a linear subfamily of `𝓗₁` whose edges have sizes in
`[r, B]` with `r ≥ 1/η` and `B ≤ C·r`: the block's edge sizes are within a
constant factor of each other, which is exactly the hypothesis of the
locally-sparse corollary `corollary_6_7` (Alon–Krivelevich–Sudakov applied
to the line graph).  This lemma discharges the numeric margins of
`Corollary67Margins` for the concrete choice `Δ := 4ε^{-10}n`. -/

theorem colorable_block_of_aks {ε : ℝ} (hε0 : 0 < ε) {K_AKS : ℝ} {Δ₀ : ℝ → ℝ}
    {ζ₀ η Csf εb : ℝ} {n r B : ℕ}
    (hAKS : ∀ (ζ : ℝ), 0 < ζ → ζ ≤ ζ₀ → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ ≤ Δ →
      (G.maxDegree : ℝ) ≤ Δ →
      (∀ v : V, (nbrEdges G v : ℝ) ≤ ζ * Δ ^ 2) →
      ∃ k : ℕ, (k : ℝ) ≤ K_AKS * Δ / Real.log (1 / ζ) ∧ G.Colorable k)
    (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) (hεb0 : 0 < εb)
    (hζ0 : η * ε ^ 10 ≤ ζ₀) (hr2 : 2 ≤ r) (hrn : r ≤ n)
    (hrη : 1 / η ≤ (r : ℝ)) (hCsf : (B : ℝ) ≤ Csf * (r : ℝ))
    (hCsf2 : 2 * (Csf + 1) ≤ 4 / ε ^ 10)
    (hrsqrt : (r : ℝ) ≤ η * Real.sqrt n)
    (hCsf3 : (Csf + 1) ^ 2 * η ≤ 2)
    (hΔthr : Δ₀ (η * ε ^ 10) ≤ 4 / ε ^ 10 * (n : ℝ))
    (hfinal : K_AKS * (4 / ε ^ 10 * (n : ℝ)) / Real.log (1 / (η * ε ^ 10)) ≤ εb * (n : ℝ))
    {𝓦 : Hypergraph (Fin n)} [Fintype 𝓦] (hlin : 𝓦.IsLinear)
    (hge : ∀ e : 𝓦, r ≤ edgeSize (e : Set (Fin n)))
    (hle : ∀ e : 𝓦, edgeSize (e : Set (Fin n)) ≤ B) :
    ∃ k : ℕ, (k : ℝ) ≤ εb * (n : ℝ) ∧ 𝓦.Colorable k := by
  classical
  have hε10 : (0 : ℝ) < ε ^ 10 := by positivity
  have hζ₀0 : 0 < ζ₀ := lt_of_lt_of_le (mul_pos hη0 hε10) hζ0
  have hr1 : (1 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 1 < r)
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hr1pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have h2r : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrn' : (r : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrn
  have hCsf0 : 0 ≤ Csf := by
    have h : 0 ≤ (r : ℝ) * Csf := by
      have h2 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
      linarith [h2, hCsf]
    exact nonneg_of_mul_nonneg_right h hrpos
  refine corollary_6_7 (K := K_AKS) (Δ₀ := Δ₀) (ζ₀ := ζ₀) hAKS
    (η := η) (α := ε ^ 10) (ε := εb) (r := r) (B := B) (n := n) (𝓗 := 𝓦)
    (Δ := 4 / ε ^ 10 * (n : ℝ))
    ⟨hη0, hε10, hεb0, hζ₀0, hζ0, hr2, hrn, ?_, hΔthr, ?_, hfinal⟩ hlin hge hle
  · -- hΔge : B(n−r)/(r−1) ≤ 4ε^{-10} n
    have hnr : ((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1) ≤ 2 * (n : ℝ) / (r : ℝ) := by
      rw [div_le_div_iff₀ hr1pos hrpos]
      nlinarith [h2r, hrpos, hn0]
    have hstep : (B : ℝ) * (((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1)) ≤
        (Csf * (r : ℝ)) * (2 * (n : ℝ) / (r : ℝ)) := by
      refine mul_le_mul hCsf hnr ?_ ?_
      · exact div_nonneg (by linarith) (le_of_lt hr1pos)
      · exact mul_nonneg hCsf0 (le_of_lt hrpos)
    have hEq : (Csf * (r : ℝ)) * (2 * (n : ℝ) / (r : ℝ)) = 2 * Csf * (n : ℝ) := by
      field_simp
    calc (B : ℝ) * ((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1)
        = (B : ℝ) * (((n : ℝ) - (r : ℝ)) / ((r : ℝ) - 1)) := by ring
      _ ≤ (Csf * (r : ℝ)) * (2 * (n : ℝ) / (r : ℝ)) := hstep
      _ = 2 * Csf * (n : ℝ) := hEq
      _ ≤ 4 / ε ^ 10 * (n : ℝ) := by nlinarith [hCsf2, hn0]
  · -- hcodeg : n/(r−1) + B² ≤ η·ε¹⁰·(4ε^{-10}n) = 4ηn
    have h1 : (1 : ℝ) ≤ 2 * η * ((r : ℝ) - 1) := by
      have h2 : (2 : ℝ) ≤ 2 * η * (r : ℝ) := by
        have h3 : 2 * η * (1 / η) = (2 : ℝ) := by field_simp
        calc (2 : ℝ) = 2 * η * (1 / η) := h3.symm
          _ ≤ 2 * η * (r : ℝ) := by
              exact mul_le_mul_of_nonneg_left hrη (by positivity)
      nlinarith [h2, hηhalf]
    have hratio : (n : ℝ) / ((r : ℝ) - 1) ≤ 2 * η * (n : ℝ) := by
      rw [div_le_iff₀ hr1pos]
      have := mul_le_mul_of_nonneg_left h1 hn0
      linarith [this]
    have hBsq : (B : ℝ) ^ 2 ≤ (Csf + 1) ^ 2 * η ^ 2 * (n : ℝ) := by
      have hBr : (B : ℝ) ≤ (Csf + 1) * (r : ℝ) := by linarith [hCsf, hrpos]
      have h1 : (B : ℝ) ^ 2 ≤ ((Csf + 1) * (r : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg B) hBr 2
      have h2 : (r : ℝ) ^ 2 ≤ η ^ 2 * (n : ℝ) := by
        have h3 : (r : ℝ) ≤ η * Real.sqrt (n : ℝ) := hrsqrt
        have h4 : (η * Real.sqrt (n : ℝ)) ^ 2 = η ^ 2 * (n : ℝ) := by
          rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        calc (r : ℝ) ^ 2 ≤ (η * Real.sqrt (n : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (le_of_lt hrpos) h3 2
          _ = η ^ 2 * (n : ℝ) := h4
      nlinarith [h1, h2, hCsf0, hη0, hn0]
    have hBsq' : (B : ℝ) ^ 2 ≤ 2 * η * (n : ℝ) := by
      have h5 : η * ((Csf + 1) ^ 2) ≤ 2 := by linarith [hCsf3]
      have h6 : (Csf + 1) ^ 2 * η ^ 2 * (n : ℝ) ≤ 2 * η * (n : ℝ) := by
        have h7 : η * ((Csf + 1) ^ 2) * (η * (n : ℝ)) ≤ 2 * (η * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right h5 (by positivity)
        calc (Csf + 1) ^ 2 * η ^ 2 * (n : ℝ) = η * ((Csf + 1) ^ 2) * (η * (n : ℝ)) := by
              ring
          _ ≤ 2 * (η * (n : ℝ)) := h7
          _ = 2 * η * (n : ℝ) := by ring
      linarith [hBsq, h6]
    rw [show η * ε ^ 10 * (4 / ε ^ 10 * (n : ℝ)) = 4 * η * (n : ℝ) by field_simp]
    linarith [hratio, hBsq']

/-! ## Combining the colourings of the volume blocks

The blocks of the loop are pairwise disjoint subfamilies, so their colourings
combine into one colouring of their union, and the total number of colours is
the sum of the blocks' colour counts.  The volume additivity of
`volume_subfamily_union` over a list gives the block count bound
`length · volBound ≤ 1`. -/

/-- The union of a list of subfamilies. -/
def famUnion {V : Type*} (l : List (Hypergraph V)) : Hypergraph V :=
  {e : Set V | ∃ W ∈ l, e ∈ W}

lemma famUnion_nil {V : Type*} : famUnion ([] : List (Hypergraph V)) = ∅ := by
  ext e; simp [famUnion]

lemma famUnion_cons {V : Type*} (W : Hypergraph V) (l : List (Hypergraph V)) :
    famUnion (W :: l) = W ∪ famUnion l := by
  ext e
  simp only [famUnion, List.mem_cons, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, rfl | hC, he⟩
    · exact Or.inl he
    · exact Or.inr ⟨C, hC, he⟩
  · rintro (he | ⟨C, hC, he⟩)
    · exact ⟨W, Or.inl rfl, he⟩
    · exact ⟨C, Or.inr hC, he⟩

/-- The first member of a pairwise-disjoint list is disjoint from the union of
the rest. -/
lemma disjoint_famUnion_of_pairwise (W : Hypergraph (Fin n))
    {l : List (Hypergraph (Fin n))} (h : (W :: l).Pairwise (fun A B => Disjoint A B)) :
    Disjoint W (famUnion l) := by
  rw [Set.disjoint_left]
  intro e heW heU
  obtain ⟨C, hC, heC⟩ := heU
  exact (Set.disjoint_left.mp ((List.pairwise_cons.mp h).1 C hC) heW) heC

/-- **Volume is additive over a pairwise disjoint list of subfamilies.** -/
theorem volume_famUnion {l : List (Hypergraph (Fin n))}
    (hdisj : l.Pairwise (fun A B => Disjoint A B)) :
    volume n (famUnion l) = (l.map (fun W => volume n W)).sum := by
  induction l with
  | nil => simp [famUnion_nil, volume_eq_canon, canonFinset]
  | cons W l ih =>
      rw [famUnion_cons, List.map_cons, List.sum_cons,
        volume_subfamily_union (disjoint_famUnion_of_pairwise W hdisj),
        ih (List.Pairwise.tail hdisj)]

/-- **The total volume of the blocks is at most `1`** (they are disjoint
subfamilies of the linear hypergraph `𝓖`). -/
theorem volume_sum_le_one {l : List (Hypergraph (Fin n))} {𝓖 : Hypergraph (Fin n)}
    (hdisj : l.Pairwise (fun A B => Disjoint A B)) (hsub : ∀ W ∈ l, W ⊆ 𝓖)
    (hlin : 𝓖.IsLinear) :
    (l.map (fun W => volume n W)).sum ≤ 1 := by
  rw [← volume_famUnion hdisj]
  refine (volume_subfamily_mono ?_).trans (volume_le_one_of_linear hlin)
  intro e he
  obtain ⟨W, hW, heW⟩ := he
  exact hsub W hW heW

/-- **Colourings of a pairwise disjoint list of subfamilies combine**: if each
member is `c`-colourable, the union is `length · c`-colourable. -/
theorem famUnion_colorable {V : Type*} {l : List (Hypergraph V)} {c : ℕ}
    (h : ∀ W ∈ l, W.Colorable c) : (famUnion l).Colorable (l.length * c) := by
  induction l with
  | nil =>
      rw [famUnion_nil]
      exact ⟨{ labels := fun e => e.2.elim, isColoring := fun e => e.2.elim }⟩
  | cons W l ih =>
      have hW : W.Colorable c := h W List.mem_cons_self
      have hl : ∀ W' ∈ l, W'.Colorable c := fun W' hW' => h W' (List.mem_cons_of_mem _ hW')
      have hunion : (W ∪ famUnion l).Colorable (c + l.length * c) :=
        Hypergraph.Colorable.union (fun e he => Or.inl he) (fun e he => Or.inr he)
          (fun e he => he) hW (ih hl)
      have hlen : (W :: l).length * c = c + l.length * c := by
        rw [List.length_cons]; ring
      rw [famUnion_cons, hlen]
      exact hunion

/-- The size of an edge is at most `n`. -/
lemma edgeSize_le {n : ℕ} (e : Set (Fin n)) : edgeSize e ≤ n := by
  simpa [edgeSize, Fintype.card_fin] using Finset.card_le_univ (verts e)

/-- **The good part of the decomposition is colourable with `⌈εn/3⌉` colours**
(Proposition 6.9, with all lists the full colour set, and the `(1−τ)n = εn/6`
good-ordering hypothesis). -/
theorem colorable_good_of_ordering {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {n r₁ : ℕ}
    {𝓖 : Hypergraph (Fin n)}
    (h2n : 2 ≤ n) (h2r : 2 ≤ r₁) (hlin : 𝓖.IsLinear)
    (hsize : ∀ e : 𝓖, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))
    {k : ℕ} (ord : 𝓖 ≃ Fin k)
    (hgood : ∀ e : 𝓖, (precedingDegree 𝓖 ord e : ℝ) ≤ (ε / 6) * (n : ℝ))
    (hm1 : 4 * (n : ℝ) / ((r₁ : ℝ) - 1) < (ε / 6) * (n : ℝ) / 4)
    (hbig : (((bigFinset (1 / 2) 𝓖).card : ℕ) : ℝ) < (ε / 6) * (n : ℝ) / 2) :
    𝓖.Colorable ⌈ε * (n : ℝ) / 3⌉₊ := by
  classical
  set k' : ℕ := ⌈ε * (n : ℝ) / 3⌉₊ with hk'
  have hle : k' ≤ n := by
    rw [hk']
    exact Nat.ceil_le.mpr (by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h : ε / 3 ≤ 1 := by linarith
      nlinarith [hn0, hε0, h])
  have hm1' : (2 : ℝ) * (n : ℝ) / ((1 / 2 : ℝ) * ((r₁ : ℝ) - 1)) <
      (ε / 6) * (n : ℝ) / 4 := by
    have h : (2 : ℝ) * (n : ℝ) / ((1 / 2 : ℝ) * ((r₁ : ℝ) - 1)) =
        4 * (n : ℝ) / ((r₁ : ℝ) - 1) := by
      field_simp
      ring
    rw [h]; exact hm1
  have hlists : ∀ e : 𝓖, ((precedingDegree 𝓖 ord e : ℝ) + (ε / 6) * (n : ℝ)) ≤
      (((Finset.univ : Finset (Fin k')).image (Fin.castLE hle)).card : ℝ) := by
    intro e
    have hcard : (((Finset.univ : Finset (Fin k')).image (Fin.castLE hle)).card : ℝ) =
        (k' : ℝ) := by
      rw [Finset.card_image_of_injective (f := Fin.castLE hle) (Finset.univ)
        (Fin.castLE_injective hle)]
      simp
    rw [hcard, hk']
    have h1 := hgood e
    have h2 : ε * (n : ℝ) / 3 ≤ (⌈ε * (n : ℝ) / 3⌉₊ : ℝ) := Nat.le_ceil _
    linarith
  obtain ⟨φ, -, hφ⟩ := prop69Instance (n := n) (r := r₁) (α₁ := ε / 6) (α₂ := 1 / 2)
    (𝓗 := 𝓖) ⟨h2n, h2r, by positivity, by norm_num, hm1', hbig⟩ ord hlin hsize
    (fun _ => (Finset.univ : Finset (Fin k')).image (Fin.castLE hle)) hlists
  refine ⟨{ labels := fun e => (Finset.mem_image.mp (hφ e)).choose, isColoring := ?_ }⟩
  intro e₁ e₂ he hnon hcol
  have h1 : Fin.castLE hle ((Finset.mem_image.mp (hφ e₁)).choose) = φ.labels e₁ :=
    (Finset.mem_image.mp (hφ e₁)).choose_spec.2
  have h2 : Fin.castLE hle ((Finset.mem_image.mp (hφ e₂)).choose) = φ.labels e₂ :=
    (Finset.mem_image.mp (hφ e₂)).choose_spec.2
  exact φ.isColoring e₁ e₂ he hnon (by rw [← h1, ← h2, hcol])

/-- **Every volume block of the decomposition is colourable with `⌈εb·n⌉`
colours** (the AKS input, via `colorable_block_of_aks` at the size factor
`sizeFactor τ K + 1`). -/
theorem colorable_block_of_decomposition {ε : ℝ} (hε0 : 0 < ε) {K_AKS : ℝ} {Δ₀ : ℝ → ℝ}
    {ζ₀ η εb : ℝ} {n : ℕ} {τ : ℝ} {K : ℕ}
    (hAKS : ∀ (ζ : ℝ), 0 < ζ → ζ ≤ ζ₀ → ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ ≤ Δ →
      (G.maxDegree : ℝ) ≤ Δ →
      (∀ v : V, (nbrEdges G v : ℝ) ≤ ζ * Δ ^ 2) →
      ∃ k : ℕ, (k : ℝ) ≤ K_AKS * Δ / Real.log (1 / ζ) ∧ G.Colorable k)
    (hη0 : 0 < η) (hηhalf : η ≤ 1 / 2) (hεb0 : 0 < εb) (hζ0 : η * ε ^ 10 ≤ ζ₀)
    (hCsf2 : 2 * (sizeFactor τ K + 1 + 1) ≤ 4 / ε ^ 10)
    (hCsf3 : (sizeFactor τ K + 1 + 1) ^ 2 * η ≤ 2)
    (hΔthr : Δ₀ (η * ε ^ 10) ≤ 4 / ε ^ 10 * (n : ℝ))
    (hfinal : K_AKS * (4 / ε ^ 10 * (n : ℝ)) / Real.log (1 / (η * ε ^ 10)) ≤ εb * (n : ℝ))
    {𝓖 : Hypergraph (Fin n)} (D : VolumeDecomposition 𝓖 τ K) (hlin : 𝓖.IsLinear)
    (hsmin : ∀ B ∈ D.blocks, 1 / η ≤ (edgeSize (B.2 : Set (Fin n)) : ℝ))
    (hsmax : ∀ B ∈ D.blocks, (edgeSize (B.2 : Set (Fin n)) : ℝ) ≤ η * Real.sqrt n) :
    (famUnion (D.blocks.map (fun B => B.1))).Colorable (D.blocks.length * ⌈εb * (n : ℝ)⌉₊) := by
  classical
  have h2η : (2 : ℝ) ≤ 1 / η := by
    rw [le_div_iff₀ hη0]
    linarith
  have hper : ∀ W ∈ D.blocks.map (fun B => B.1), W.Colorable ⌈εb * (n : ℝ)⌉₊ := by
    intro W hW
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hW
    haveI : Fintype (B.1 : Hypergraph (Fin n)) := Fintype.ofFinite _
    have hrmin : 1 / η ≤ ((edgeSize (B.2 : Set (Fin n))) : ℝ) := hsmin B hB
    have hr2' : (2 : ℝ) ≤ ((edgeSize (B.2 : Set (Fin n))) : ℝ) := h2η.trans hrmin
    have hr2 : 2 ≤ edgeSize (B.2 : Set (Fin n)) := by exact_mod_cast hr2'
    have hrsqrt : ((edgeSize (B.2 : Set (Fin n))) : ℝ) ≤ η * Real.sqrt n := hsmax B hB
    have hrn : edgeSize (B.2 : Set (Fin n)) ≤ n := edgeSize_le _
    set r : ℕ := edgeSize (B.2 : Set (Fin n)) with hrdef
    have hrcast : (r : ℝ) = ((edgeSize (B.2 : Set (Fin n))) : ℝ) := rfl
    have hge : ∀ e : (B.1 : Hypergraph (Fin n)), r ≤ edgeSize (e : Set (Fin n)) := by
      intro e
      have h1 : (r : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := D.hBlockMin B hB _ e.2
      exact_mod_cast h1
    have hle : ∀ e : (B.1 : Hypergraph (Fin n)),
        edgeSize (e : Set (Fin n)) ≤ ⌈sizeFactor τ K * (r : ℝ)⌉₊ := by
      intro e
      have h1 : (edgeSize (e : Set (Fin n)) : ℝ) ≤ sizeFactor τ K * (r : ℝ) :=
        D.hBlockMax B hB _ e.2
      exact_mod_cast h1.trans (Nat.le_ceil (sizeFactor τ K * (r : ℝ)))
    have hCsf : ((⌈sizeFactor τ K * (r : ℝ)⌉₊ : ℕ) : ℝ) ≤
        (sizeFactor τ K + 1) * (r : ℝ) := by
      have hrpos : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le (by norm_num) hr2'
      have hsf0 : (0 : ℝ) ≤ sizeFactor τ K := le_of_lt (sizeFactor_pos τ K)
      have hceil : ((⌈sizeFactor τ K * (r : ℝ)⌉₊ : ℕ) : ℝ) ≤
          sizeFactor τ K * (r : ℝ) + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (a := sizeFactor τ K * (r : ℝ))
          (mul_nonneg hsf0 (le_of_lt hrpos)))
      nlinarith [hceil, hrpos]
    obtain ⟨k, hk, hcol⟩ := colorable_block_of_aks (ε := ε) hε0 (K_AKS := K_AKS) (Δ₀ := Δ₀)
      (ζ₀ := ζ₀) (η := η) (Csf := sizeFactor τ K + 1) (εb := εb) (n := n)
      (r := r) (B := ⌈sizeFactor τ K * (r : ℝ)⌉₊)
      (𝓦 := (B.1 : Hypergraph (Fin n))) hAKS hη0 hηhalf hεb0 hζ0 hr2 hrn
      (by rw [hrcast]; exact hrmin) hCsf hCsf2 (by rw [hrcast]; exact hrsqrt) hCsf3
      hΔthr hfinal (hlin.mono (D.hBlockSub B hB)) hge hle
    have hk' : (k : ℝ) ≤ ((⌈εb * (n : ℝ)⌉₊ : ℕ) : ℝ) := le_trans hk (Nat.le_ceil _)
    exact ⟨(hcol.some).ofLeColors (by exact_mod_cast hk')⟩
  have key := famUnion_colorable hper
  rwa [List.length_map] at key

/-! ## Theorem 1.3: the assembly

We now put the pieces together.  The complete statement is

`WeakStabilityInstance ε : ∃ η > 0, ∃ n₀, ∀ n ≥ n₀, ∀ 𝓗 : Hypergraph (Fin n)`,
linear with `Δ(𝓗) ≤ ηn` and no edge of size in `(η√n, √n/η)`,
`∃ k ≤ εn, 𝓗.Colorable k`.

The constants are chosen so that every margin of the loop, of the AKS
corollary and of Proposition 6.9 is satisfied:

* `τ := 1 − ε/6`, `K := ⌈ε^{-2}⌉`, `r₁ := ⌊1/η⌋ + 1` for the loop
  (`ReorderingMargins r₁ τ K` holds because `r₁ ≥ 1/η ≥ 4ε^{-20}`),
* `M := ⌈1/volBound τ K⌉ + 1` bounds the number of volume blocks
  (each block has volume `≥ volBound τ K ≥ ε^{10}/14400`),
* `εb := ε/(10M)` is the per-block colour budget,
* `η := ζ ε^{-10}` with `ζ := (1/4)·min(ζ₀,1)·min(e^{-C₁},1)·ε^{30}` and
  `C₁ := 10⁹·K_AKS·ε^{-21} + 1`, which makes `log(1/ζ) ≥ C₁` dominate the
  AKS error term (`η ≤ ε^{20}/4` gives `1/η ≥ 4ε^{-20}`). -/

/-- The statement of Theorem 1.3 (weak stability) as a per-`ε`
proposition. -/
def WeakStabilityInstance (ε : ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ 𝓗 : Hypergraph (Fin n),
    𝓗.IsLinear →
    ((hypergraphMaxDegree 𝓗 : ℕ) : ℝ) ≤ η * (n : ℝ) →
    (∀ e ∈ 𝓗, ¬(η * Real.sqrt n < (edgeSize e : ℝ) ∧
      (edgeSize e : ℝ) < Real.sqrt n / η)) →
    ∃ k : ℕ, (k : ℝ) ≤ ε * (n : ℝ) ∧ 𝓗.Colorable k

/-- Auxiliary: the blocks of a decomposition, as a list of hypergraphs and a
list of their volumes, have the same `Pairwise`/membership structure. -/
lemma pairwise_map_sub {n : ℕ}
    {l : List (Σ W : Hypergraph (Fin n), {e : Set (Fin n) // e ∈ W})}
    (h : l.Pairwise (fun A B => Disjoint A.1 B.1)) :
    (l.map (fun B => B.1)).Pairwise Disjoint := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons A l ih =>
      rw [List.map_cons]
      refine List.pairwise_cons.mpr ⟨?_, ih (List.Pairwise.tail h)⟩
      intro W hW
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hW
      exact (List.pairwise_cons.mp h).1 C hC

/-- `1 ≤ (1/ε)^n` for `0 < ε ≤ 1`. -/
lemma one_le_inv_pow {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (n : ℕ) : (1 : ℝ) ≤ (1 / ε) ^ n := by
  calc (1 : ℝ) = 1 ^ n := (one_pow n).symm
    _ ≤ (1 / ε) ^ n := pow_le_pow_left₀ (by norm_num) (by rw [le_div_iff₀ h0]; linarith) n

/-- `(1/ε)^a ≤ (1/ε)^b` for `a ≤ b`, `0 < ε ≤ 1`. -/
lemma inv_pow_le_inv_pow {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    (1 / ε) ^ a ≤ (1 / ε) ^ b :=
  pow_le_pow_right₀ (by rw [le_div_iff₀ h0]; linarith) hab

/-- `1000 ≤ 1/ε` for `0 < ε ≤ 1/1000`. -/
lemma inv_ge_1000 {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 1000) : (1000 : ℝ) ≤ 1 / ε := by
  rw [le_div_iff₀ h0]; linarith

/-- `2 * (1 + 4x²) ≤ 4x^{20}` for `x ≥ 1000`. -/
lemma two_mul_le_pow {x : ℝ} (hx : (1000 : ℝ) ≤ x) : 2 * (1 + 4 * x ^ 2) ≤ 4 * x ^ 20 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
  have h18 : (3 : ℝ) ≤ x ^ 18 := by
    have h3 : (1000 : ℝ) ^ 18 ≤ x ^ 18 := pow_le_pow_left₀ (by norm_num) hx 18
    nlinarith [h3]
  have hsplit : x ^ 20 = x ^ 18 * x ^ 2 := by ring
  nlinarith [hx2, h18, hsplit, sq_nonneg (x ^ 2)]

/-- `2 * (1 + 4x²) ≤ x^{20}` for `x ≥ 1000`. -/
lemma two_mul_one_add_le_pow {x : ℝ} (hx : (1000 : ℝ) ≤ x) : 2 * (1 + 4 * x ^ 2) ≤ x ^ 20 := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hx2 : (2 : ℝ) ≤ x ^ 2 := by nlinarith
  have h18 : (9 : ℝ) ≤ x ^ 18 := by
    have h3 : (1000 : ℝ) ^ 18 ≤ x ^ 18 := pow_le_pow_left₀ (by norm_num) hx 18
    nlinarith [h3]
  have hsplit : x ^ 20 = x ^ 18 * x ^ 2 := by ring
  nlinarith [hx2, h18, hsplit, sq_nonneg (x ^ 2)]

/-- `1 + 4x² ≤ 4x^{20}` for `x ≥ 1000`. -/
lemma one_add_four_mul_sq_le_pow {x : ℝ} (hx : (1000 : ℝ) ≤ x) : 1 + 4 * x ^ 2 ≤ 4 * x ^ 20 := by
  have h1 := two_mul_le_pow hx
  have h2 : (0 : ℝ) < 1 + 4 * x ^ 2 := by nlinarith
  linarith [h1, h2]

/-- `c / ε^n = c (1/ε)^n`, the normal form used for the constant estimates. -/
lemma div_pow_eq_mul (c ε : ℝ) (n : ℕ) : c / ε ^ n = c * (1 / ε) ^ n := by
  rw [one_div_pow, div_eq_mul_inv, one_div]

end

end ErdosFaberLovaszConjecture
