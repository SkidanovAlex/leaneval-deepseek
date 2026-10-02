import Submission.EFL.LargeEdgeThm
import Submission.EFL.Reservoir
import Submission.EFL.EdgeSize
import Submission.EFL.ColourCombine
import Submission.Commons.Data.Real.exvol_arith

/-!
# Theorem 1.2 (`main-thm-2`) of the paper: the volume reduction

The paper's Theorem 1.2 (a stability version of Theorem 1.1) states: for
every `δ > 0` there are `n₀` and `σ > 0` such that every `n`-vertex linear
hypergraph (`n ≥ n₀`) with maximum degree at most `(1-δ)n` and with at most
`(1-3δ)n` edges of size `(1±δ)√n` has chromatic index at most `(1-σ)n`.

Its proof (Kang–Kelly–Kühn–Methuku–Osthus, §6.3) has three steps:

1. **The FPP-extremal edges have small volume.**  `e(𝓗_ex) ≤ (1-3δ)n` and
   `|e| ≤ (1+δ)√n` for `e ∈ 𝓗_ex` give
   `vol(𝓗_ex) ≤ (1-3δ)n·x(x-1)/(n(n-1))` with `x := (1+δ)√n`, which is
   `< 1-δ` for `n ≥ 1000/δ²` (`volume_exEdges_lt_of`, from
   `volume_le_canon_card_mul_real` and the arithmetic lemma
   `Commons.Data.Real.exvol_arith`).  Hence the *extremal* alternative of
   Theorem 6.7 is impossible when Theorem 6.7 is applied to
   `𝓗_med ∪ 𝓗_large` with extremality parameter `δ' ≤ δ` (because
   `𝓗_ex^{δ'} ⊆ 𝓗_ex^δ` and `1-δ ≤ 1-δ'`).

2. **Apply Theorem 6.7** (`largeEdgeThmStatement_of_deep`) to
   `medLarge 𝓗 r₁ = 𝓗_med ∪ 𝓗_large`: this yields a proper colouring of the
   medium and large edges with at most `(1-σ')n` colours, with the medium
   colours inside a set `Cmed` of size at most `γ₁n`.

3. **Extend to the small edges** with Kahn's list-colouring theorem
   (`KahnStatement`): for each small edge `e`, forbid the colours of the
   *large* edges meeting `e` (at most `r₁n/r₀` of them, by the degree bound
   `degree_mul_le`) and all of `Cmed`; the lists have size `≤ αD/2` with
   `α := 3β`, `D := ⌊(1-δ)n⌋`, and `(1+α)D ≤ K - |Cmed|` with
   `K := ⌊(1-σ')n⌋`, so Kahn yields a colouring of the small edges into
   `Fin K` avoiding all lists.  The two colourings combine into a proper
   colouring of `𝓗` with `K` colours.

This module currently contains the statement (`MainThm2Statement`) and step 1
(`volume_exEdges_lt_of`); the remaining steps are in progress.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **Theorem 1.2 of the paper** (`main-thm-2`): for every `δ > 0` there are
`n₀` and `σ > 0` such that every `n`-vertex linear hypergraph (`n ≥ n₀`)
with maximum degree at most `(1-δ)n` and at most `(1-3δ)n` edges of size
`(1±δ)√n` has a proper edge-colouring with at most `(1-σ)n` colours. -/
def MainThm2Statement : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ n₀ : ℕ, ∃ σ : ℝ, 0 < σ ∧
      ∀ n : ℕ, n₀ ≤ n → ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear →
        (hypergraphMaxDegree 𝓗 : ℝ) ≤ (1 - δ) * (n : ℝ) →
        ((𝓗.exEdges δ).ncard : ℝ) ≤ (1 - 3 * δ) * (n : ℝ) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - σ) * (n : ℝ) ∧ 𝓗.Colorable k

/-! ## Step 1: the FPP-extremal edges have volume less than `1 - δ` -/

/-- **Step 1 of Theorem 1.2**, with the arithmetic isolated: if the number of
FPP-extremal edges is at most `(1-3δ)n` and
`(1-3δ)·x(x-1) < (1-δ)(n-1)` for `x = (1+δ)√n`, then `vol(𝓗_ex) < 1 - δ`. -/
theorem volume_exEdges_lt_of {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) {𝓗 : Hypergraph (Fin n)}
    (hn2 : 2 ≤ n)
    (hcard : ((canonFinset (𝓗.exEdges δ)).card : ℝ) ≤ (1 - 3 * δ) * (n : ℝ))
    (harith : (1 - 3 * δ) * (((1 + δ) * Real.sqrt (n : ℝ)) *
        (((1 + δ) * Real.sqrt (n : ℝ)) - 1)) < (1 - δ) * ((n : ℝ) - 1)) :
    volume n (𝓗.exEdges δ) < 1 - δ := by
  classical
  set x : ℝ := (1 + δ) * Real.sqrt (n : ℝ) with hx
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    refine (Real.le_sqrt (by norm_num) (by linarith)).mpr ?_
    simpa using hn1R
  have hx1 : 1 ≤ x := by
    rw [hx]
    have h1 : (1 : ℝ) < 1 + δ := by linarith
    nlinarith
  have hxnn : (0 : ℝ) ≤ x * (x - 1) := by
    have h0 : (0 : ℝ) ≤ x := by linarith
    have h1 : (0 : ℝ) ≤ x - 1 := by linarith
    exact mul_nonneg h0 h1
  have hsize : ∀ e ∈ 𝓗.exEdges δ, (edgeSize e : ℝ) ≤ x := by
    intro e he
    have h := (mem_exEdges 𝓗 δ e).mp he
    rw [hx]
    exact h.2.2
  have hdenpos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    have h2 : 0 < n - 1 := by omega
    exact_mod_cast h2
  have hdenpos2 : (0 : ℝ) < (n : ℝ) * ((n - 1 : ℕ) : ℝ) := mul_pos hnR hdenpos
  have hnm1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1, Nat.cast_one]
  have hvol := volume_le_canon_card_mul_real (𝓕 := 𝓗.exEdges δ) hx1 hsize
  have hcard' : ((canonFinset (𝓗.exEdges δ)).card : ℝ) * (x * (x - 1)) ≤
      (1 - 3 * δ) * (n : ℝ) * (x * (x - 1)) :=
    mul_le_mul_of_nonneg_right hcard hxnn
  have h1 : volume n (𝓗.exEdges δ) ≤
      (1 - 3 * δ) * (n : ℝ) * (x * (x - 1)) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
    le_trans hvol (by rw [div_le_div_iff_of_pos_right hdenpos2]; exact hcard')
  have h2 : (1 - 3 * δ) * (n : ℝ) * (x * (x - 1)) /
      ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) = (1 - 3 * δ) * (x * (x - 1)) / ((n : ℝ) - 1) := by
    rw [hnm1]
    field_simp
  have h3 : (1 - 3 * δ) * (x * (x - 1)) / ((n : ℝ) - 1) < 1 - δ := by
    have hpos' : (0 : ℝ) < (n : ℝ) - 1 := by rw [← hnm1]; exact hdenpos
    rw [div_lt_iff₀ hpos']
    rw [hx] at harith
    exact harith
  linarith [h1, h2.symm.le, h2.le, h3]

/-- The arithmetic of Step 1: `(1-3δ)·x(x-1) < (1-δ)(n-1)` for
`x = (1+δ)√n`, `n ≥ 1000/δ²` and `δ ≤ 1/4`. -/
theorem exvol_arith_local {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) {n : ℕ}
    (hn : 1000 / δ ^ 2 ≤ (n : ℝ)) :
    (1 - 3 * δ) * (((1 + δ) * Real.sqrt (n : ℝ)) *
        (((1 + δ) * Real.sqrt (n : ℝ)) - 1)) < (1 - δ) * ((n : ℝ) - 1) := by
  set x : ℝ := (1 + δ) * Real.sqrt (n : ℝ) with hx
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h1 : (0 : ℝ) < 1000 / δ ^ 2 := by positivity
    linarith
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn0)
  have hδsq : (1000 : ℝ) ≤ δ ^ 2 * (n : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)] at hn
    linarith
  have hx0 : (0 : ℝ) < x := by
    rw [hx]
    have : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
    nlinarith
  have h13 : (0 : ℝ) ≤ 1 - 3 * δ := by linarith
  have hstep1 : (1 - 3 * δ) * (x * (x - 1)) ≤ (1 - 3 * δ) * x ^ 2 := by nlinarith
  have hx2 : x ^ 2 = (1 + δ) ^ 2 * (n : ℝ) := by
    rw [hx, mul_pow, hsq]
  have hstep2 : (1 - 3 * δ) * x ^ 2 = (1 - 3 * δ) * (1 + δ) ^ 2 * (n : ℝ) := by
    rw [hx2]; ring
  have hkey : (0 : ℝ) < δ ^ 2 * (5 + 3 * δ) * (n : ℝ) - (1 - δ) := by
    have h5 : (0 : ℝ) < 5 + 3 * δ := by linarith
    nlinarith [hδsq, h5, hδ0, hδ4]
  have hdiff : (1 - δ) * ((n : ℝ) - 1) - (1 - 3 * δ) * (1 + δ) ^ 2 * (n : ℝ) =
      δ ^ 2 * (5 + 3 * δ) * (n : ℝ) - (1 - δ) := by ring
  linarith [hstep1, hstep2.le, hstep2.ge, hdiff.le, hdiff.ge, hkey]

/-- **Step 1 of Theorem 1.2.**  For `0 < δ ≤ 1/4` and `n ≥ 1000/δ²`, at most
`(1-3δ)n` FPP-extremal edges force `vol(𝓗_ex) < 1 - δ`. -/
theorem volume_exEdges_lt {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) {𝓗 : Hypergraph (Fin n)}
    (hn : 1000 / δ ^ 2 ≤ (n : ℝ))
    (hcard : ((canonFinset (𝓗.exEdges δ)).card : ℝ) ≤ (1 - 3 * δ) * (n : ℝ)) :
    volume n (𝓗.exEdges δ) < 1 - δ := by
  have hn2 : 2 ≤ n := by
    have h1 : (16000 : ℝ) ≤ 1000 / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)]
      nlinarith only [hδ0, hδ4]
    have : (2 : ℝ) ≤ (n : ℝ) := by linarith [hn]
    exact_mod_cast this
  exact volume_exEdges_lt_of hδ0 hδ4 hn2 hcard (Commons.Data.Real.exvol_arith hδ0 hδ4 n hn)
  -- (the `16000` is a safe lower bound: `1000/δ² ≥ 16000` for `δ ≤ 1/4`)

/-! ## Relabelling a colouring into a smaller colour type -/

/-- The canonical injection `C → Fin K` (for `C.card ≤ K`), extended by `0`
off `C`; it is injective on `C`. -/
noncomputable def colourCast (C : Finset (Fin n)) {K : ℕ} (h : C.card ≤ K) (hK : 0 < K) :
    Fin n → Fin K :=
  fun a => if ha : a ∈ C then Fin.castLE h ((Finset.equivFin C) ⟨a, ha⟩) else ⟨0, hK⟩

theorem colourCast_of_mem (C : Finset (Fin n)) {K : ℕ} (h : C.card ≤ K) (hK : 0 < K)
    {a : Fin n} (ha : a ∈ C) :
    colourCast C h hK a = Fin.castLE h ((Finset.equivFin C) ⟨a, ha⟩) := by
  rw [colourCast]
  exact dif_pos ha

/-- `colourCast` is injective on `C`. -/
theorem colourCast_injOn (C : Finset (Fin n)) {K : ℕ} (h : C.card ≤ K) (hK : 0 < K) :
    ∀ a ∈ C, ∀ b ∈ C, colourCast C h hK a = colourCast C h hK b → a = b := by
  intro a ha b hb hab
  rw [colourCast_of_mem C h hK ha, colourCast_of_mem C h hK hb] at hab
  have h1 : (Finset.equivFin C) ⟨a, ha⟩ = (Finset.equivFin C) ⟨b, hb⟩ :=
    Fin.castLE_injective h hab
  have h2 : (⟨a, ha⟩ : C) = ⟨b, hb⟩ := (Finset.equivFin C).injective h1
  exact congrArg (fun x : C => (x : Fin n)) h2

/-- **Relabelling a colouring into a smaller colour set.**  If `φ` uses only
the colours of `C` and `C.card ≤ K`, then `φ ∘ colourCast C h` is a proper
colouring with `K` colours. -/
theorem Coloring.relabel {𝓖 : Hypergraph (Fin n)} (φ : 𝓖.Coloring (Fin n))
    {C : Finset (Fin n)} (hφ : φ.UsesColourSet C) {K : ℕ} (hK : C.card ≤ K)
    (hK0 : 0 < K) :
    ∃ ψ : 𝓖.Coloring (Fin K),
      (∀ e : 𝓖, ψ.labels e = colourCast C hK hK0 (φ.labels e)) ∧
      (∀ (e : 𝓖) (cmed : Fin n), cmed ∈ C → φ.labels e = cmed →
        ψ.labels e = colourCast C hK hK0 cmed) := by
  refine ⟨⟨fun e => colourCast C hK hK0 (φ.labels e), ?_⟩, fun e => rfl, ?_⟩
  · intro e₁ e₂ hne hnon hab
    exact φ.isColoring e₁ e₂ hne hnon
      (colourCast_injOn C hK hK0 _ (hφ e₁) _ (hφ e₂) hab)
  · intro e cmed _ hc
    show colourCast C hK hK0 (φ.labels e) = colourCast C hK hK0 cmed
    rw [hc]

/-- Colour classes of the relabelled colouring: for a colour `c` hit by
`colourCast C hK`, the class is that of `c`. -/
theorem Coloring.colorClass_relabel {𝓖 : Hypergraph (Fin n)} (φ : 𝓖.Coloring (Fin n))
    {C : Finset (Fin n)} (hφ : φ.UsesColourSet C) {K : ℕ} (hK : C.card ≤ K) (hK0 : 0 < K)
    (ψ : 𝓖.Coloring (Fin K))
    (hψ : ∀ e : 𝓖, ψ.labels e = colourCast C hK hK0 (φ.labels e))
    {c : Fin n} (hc : c ∈ C) :
    ψ.colorClass (colourCast C hK hK0 c) = φ.colorClass c := by
  ext e
  rw [Hypergraph.Coloring.colorClass, Set.mem_setOf_eq, Hypergraph.Coloring.colorClass,
    Set.mem_setOf_eq, hψ e]
  constructor
  · intro h
    exact colourCast_injOn C hK hK0 _ (hφ e) c hc h
  · intro h
    rw [h]

/-! ## The crossing count for Theorem 1.2 (and Claim 12.1's `EP2`) -/

/-- **The crossing count.**  In a linear hypergraph, a small edge `e`
(`|e| ≤ r₁`) meets at most `r₁·n/(r₀−1)` edges of size `> r₀`. -/
theorem card_largeEdges_meeting_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {r₁ r₀ : ℕ} (hr₀ : 2 ≤ r₀) (hn : 0 < n) {e : Set (Fin n)} (he : e ∈ 𝓗)
    (hsize : edgeSize e ≤ r₁) :
    (Nat.card {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} : ℝ) ≤
      (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := by
  classical
  haveI : Fintype 𝓗 := Fintype.ofFinite 𝓗
  have hlinL : (𝓗.largeEdges r₀).IsLinear := IsLinear.mono' (largeEdges_subset 𝓗 r₀) hlin
  have hszL : ∀ f ∈ 𝓗.largeEdges r₀, r₀ ≤ edgeSize f := fun f hf =>
    le_of_lt ((mem_largeEdges 𝓗 r₀ f).mp hf).2
  have hr₀1 : 0 < r₀ - 1 := by omega
  set S : Finset (𝓗.largeEdges r₀) :=
    (Finset.univ : Finset (𝓗.largeEdges r₀)).filter
      (fun f : 𝓗.largeEdges r₀ => ((f : Set (Fin n)) ∩ e).Nonempty) with hS
  have hcardS : Nat.card {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hdegv : ∀ v : Fin n,
      ((Finset.univ : Finset (𝓗.largeEdges r₀)).filter
        (fun f : 𝓗.largeEdges r₀ => v ∈ (f : Set (Fin n)))).card ≤ n / (r₀ - 1) := by
    intro v
    have h1 : hypergraphDegree (𝓗.largeEdges r₀) v * (r₀ - 1) ≤ n - 1 :=
      degree_mul_le hlinL hszL v
    have h1' : ((Finset.univ : Finset (𝓗.largeEdges r₀)).filter
        (fun f : 𝓗.largeEdges r₀ => v ∈ (f : Set (Fin n)))).card * (r₀ - 1) ≤ n - 1 := by
      rw [hypergraphDegree] at h1
      rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    rw [Nat.le_div_iff_mul_le hr₀1]
    exact le_trans h1' (Nat.sub_le n 1)
  have hsub : S ⊆ (verts e).biUnion (fun v =>
      (Finset.univ : Finset (𝓗.largeEdges r₀)).filter
        (fun f : 𝓗.largeEdges r₀ => v ∈ (f : Set (Fin n)))) := by
    intro f hf
    rw [hS, Finset.mem_filter] at hf
    obtain ⟨v, hvf, hve⟩ := hf.2
    rw [Finset.mem_biUnion]
    exact ⟨v, by rw [mem_verts]; exact hve, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hvf⟩
  have hnat : Nat.card {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} ≤
      edgeSize e * (n / (r₀ - 1)) := by
    rw [hcardS]
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc (verts e).sum (fun v => ((Finset.univ : Finset (𝓗.largeEdges r₀)).filter
            (fun f : 𝓗.largeEdges r₀ => v ∈ (f : Set (Fin n)))).card)
        ≤ (verts e).sum (fun _ => n / (r₀ - 1)) := Finset.sum_le_sum (fun v _ => hdegv v)
      _ = (verts e).card * (n / (r₀ - 1)) := by rw [Finset.sum_const, smul_eq_mul]
      _ = edgeSize e * (n / (r₀ - 1)) := rfl
  have hr₀1R : (0 : ℝ) < (r₀ : ℝ) - 1 := by
    have h1' : (1 : ℝ) < (r₀ : ℝ) := by exact_mod_cast (by omega : 1 < r₀)
    linarith
  have hdiv : (((n / (r₀ - 1) : ℕ)) : ℝ) ≤ (n : ℝ) / ((r₀ : ℝ) - 1) := by
    have h := Nat.cast_div_le (α := ℝ) (m := n) (n := r₀ - 1)
    rwa [show (((r₀ - 1 : ℕ)) : ℝ) = (r₀ : ℝ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ r₀), Nat.cast_one]] at h
  have hnn : (0 : ℝ) ≤ (n : ℝ) / ((r₀ : ℝ) - 1) :=
    le_of_lt (div_pos (by exact_mod_cast hn) hr₀1R)
  calc (Nat.card {f : 𝓗.largeEdges r₀ // ((f : Set (Fin n)) ∩ e).Nonempty} : ℝ)
      ≤ (edgeSize e : ℝ) * (((n / (r₀ - 1) : ℕ)) : ℝ) := by exact_mod_cast hnat
    _ ≤ (r₁ : ℝ) * ((n : ℝ) / ((r₀ : ℝ) - 1)) := by
        have h2 : (edgeSize e : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hsize
        exact mul_le_mul h2 hdiv (by positivity) (by positivity)
    _ = (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := by ring

/-! ## The medium/large colouring of Theorem 1.2 (step 2)

Auxiliary: the canonical finset of a family has card equal to its `ncard`. -/

theorem canonFinset_card_eq_ncard (S : Set (Set (Fin n))) :
    (canonFinset S).card = S.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext e
  simp only [canonFinset, Finset.mem_filter, Finset.mem_univ, true_and,
    Set.Finite.mem_toFinset]

/-- Sub-hypergraph relation for extrema: `𝓗.exEdges δ'' ⊆ 𝓗.exEdges δ` when
`δ'' ≤ δ`. -/
theorem exEdges_mono {𝓗 : Hypergraph (Fin n)} {δ δ' : ℝ} (h : δ' ≤ δ) :
    𝓗.exEdges δ' ⊆ 𝓗.exEdges δ := by
  intro e he
  have h1 := (mem_exEdges 𝓗 δ' e).mp he
  refine (mem_exEdges 𝓗 δ e).mpr ⟨h1.1, ?_, ?_⟩
  · have := h1.2.1
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  · have := h1.2.2
    nlinarith [Real.sqrt_nonneg (n : ℝ)]

theorem exEdges_ncard_mono {𝓗 : Hypergraph (Fin n)} {δ δ' : ℝ} (h : δ' ≤ δ) :
    (𝓗.exEdges δ').ncard ≤ (𝓗.exEdges δ).ncard :=
  Set.ncard_mono (exEdges_mono h)

/-! ## Combining two colourings of a disjoint cover (arbitrary colour type) -/

/-- The combined labelling of a disjoint cover (arbitrary colour type). -/
def unionLabelCrossGen {α : Type*} {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂)
    (φ₁ : 𝓖₁.Coloring α) (φ₂ : 𝓖₂.Coloring α) (e : 𝓗) : α := by
  classical
  exact if he : (e : Set (Fin n)) ∈ 𝓖₁ then φ₁.labels ⟨(e : Set (Fin n)), he⟩
    else φ₂.labels ⟨(e : Set (Fin n)), (hcover (e : Set (Fin n)) e.2).resolve_left he⟩

/-- **Combining two colourings of a cover with a cross-condition** (arbitrary
colour type): if `φ₁` and `φ₂` colour a disjoint cover and never agree on
intersecting edges across the two parts, they combine into a proper
colouring of the whole. -/
def coloringUnionCrossGen {α : Type*} {𝓖₁ 𝓖₂ 𝓗 : Hypergraph (Fin n)}
    (hcover : ∀ e ∈ 𝓗, e ∈ 𝓖₁ ∨ e ∈ 𝓖₂) (hdisjG : Disjoint 𝓖₁ 𝓖₂)
    (φ₁ : 𝓖₁.Coloring α) (φ₂ : 𝓖₂.Coloring α)
    (hcross : ∀ (e₁ : 𝓖₁) (e₂ : 𝓖₂),
      (((e₁ : Set (Fin n)) ∩ (e₂ : Set (Fin n))).Nonempty) → φ₁.labels e₁ ≠ φ₂.labels e₂) :
    𝓗.Coloring α where
  labels := unionLabelCrossGen hcover φ₁ φ₂
  isColoring := by
    intro e₁ e₂ hne hnon hcol
    by_cases h1 : (e₁ : Set (Fin n)) ∈ 𝓖₁
    · by_cases h2 : (e₂ : Set (Fin n)) ∈ 𝓖₁
      · have hcol1 : φ₁.labels ⟨(e₁ : Set (Fin n)), h1⟩ = φ₁.labels ⟨(e₂ : Set (Fin n)), h2⟩ := by
          simpa only [unionLabelCrossGen, dif_pos h1, dif_pos h2] using hcol
        exact φ₁.isColoring ⟨_, h1⟩ ⟨_, h2⟩
          (fun hEq => hne (Subtype.ext (by simpa using congrArg Subtype.val hEq)))
          (by simpa using hnon) hcol1
      · have hcol1 : φ₁.labels ⟨(e₁ : Set (Fin n)), h1⟩ =
            φ₂.labels ⟨(e₂ : Set (Fin n)), (hcover (e₂ : Set (Fin n)) e₂.2).resolve_left h2⟩ := by
          simpa only [unionLabelCrossGen, dif_pos h1, dif_neg h2] using hcol
        exact hcross ⟨(e₁ : Set (Fin n)), h1⟩
          ⟨(e₂ : Set (Fin n)), (hcover (e₂ : Set (Fin n)) e₂.2).resolve_left h2⟩
          (by simpa using hnon) hcol1
    · by_cases h2 : (e₂ : Set (Fin n)) ∈ 𝓖₁
      · have hcol1 : φ₂.labels ⟨(e₁ : Set (Fin n)), (hcover (e₁ : Set (Fin n)) e₁.2).resolve_left h1⟩ =
            φ₁.labels ⟨(e₂ : Set (Fin n)), h2⟩ := by
          simpa only [unionLabelCrossGen, dif_neg h1, dif_pos h2] using hcol
        exact hcross ⟨(e₂ : Set (Fin n)), h2⟩
          ⟨(e₁ : Set (Fin n)), (hcover (e₁ : Set (Fin n)) e₁.2).resolve_left h1⟩
          (by simpa [Set.inter_comm] using hnon) hcol1.symm
      · have hcol1 : φ₂.labels ⟨(e₁ : Set (Fin n)), (hcover (e₁ : Set (Fin n)) e₁.2).resolve_left h1⟩ =
            φ₂.labels ⟨(e₂ : Set (Fin n)), (hcover (e₂ : Set (Fin n)) e₂.2).resolve_left h2⟩ := by
          simpa only [unionLabelCrossGen, dif_neg h1, dif_neg h2] using hcol
        exact φ₂.isColoring ⟨_, _⟩ ⟨_, _⟩
          (fun hEq => hne (Subtype.ext (by simpa using congrArg Subtype.val hEq)))
          (by simpa using hnon) hcol1


/-- **Extremality is impossible** when the FPP-extremal edges have volume
`< 1 - δ`. -/
theorem not_largeEdgeExtremal_of_volume {δ γ₂ γ₁ β : ℝ} {r₁ r₀ : ℕ}
    {𝓗 : Hypergraph (Fin n)} (hvol : volume n (𝓗.exEdges δ) < 1 - δ)
    (h : LargeEdgeExtremal n δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) (medLarge 𝓗 (r₁ : ℝ))) :
    False := by
  obtain ⟨⟨W, hWsub, hWex, hWvol⟩, _⟩ := h
  have hW' : W ⊆ 𝓗.exEdges δ := by
    intro e he
    exact (mem_exEdges 𝓗 δ e).mpr
      ⟨medLarge_subset 𝓗 (r₁ : ℝ) (hWsub he), hWex e he⟩
  have := volume_subfamily_mono hW'
  linarith

/-- The colours, in a colouring `φ` of the medium/large edges, of the edges of
size `> r₀` meeting a set `e`. -/
noncomputable def largeColours (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℝ) {K : ℕ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin K)) (e : Set (Fin n)) : Finset (Fin K) := by
  classical
  exact ((Finset.univ : Finset (medLarge 𝓗 r₁)).filter
    (fun f : medLarge 𝓗 r₁ => r₀ < (edgeSize (f : Set (Fin n)) : ℝ) ∧
      (((f : Set (Fin n)) ∩ e).Nonempty))).image φ.labels

/-- The list of colours forbidden for a small edge `e` in Theorem 1.2: the
colours of the large edges meeting `e`, together with the medium colour set. -/
noncomputable def smallLists (𝓗 : Hypergraph (Fin n)) (r₁ r₀ : ℝ) {K : ℕ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin K)) (CC : Finset (Fin K)) (e : Set (Fin n)) :
    Finset (Fin K) :=
  largeColours 𝓗 r₁ r₀ φ e ∪ CC

/-- **The counting bound for the lists of Theorem 1.2**: a small edge `e` meets
at most `r₁·n/(r₀−1)` edges of size `> r₀`. -/
theorem card_mediumLarge_meeting_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {r₁ r₀ : ℕ} (hr₀ : 2 ≤ r₀) (hn : 0 < n) {e : Set (Fin n)} (he : e ∈ 𝓗)
    (hsize : edgeSize e ≤ r₁) :
    (Nat.card {f : medLarge 𝓗 (r₁ : ℝ) //
        (r₀ : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) ∧
        (((f : Set (Fin n)) ∩ e).Nonempty)} : ℝ) ≤
      (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := by
  classical
  haveI : Fintype (𝓗.largeEdges r₀) := Fintype.ofFinite _
  have hinj : Function.Injective
      (fun f : {f : medLarge 𝓗 (r₁ : ℝ) //
          (r₀ : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) ∧ (((f : Set (Fin n)) ∩ e).Nonempty)} =>
        (⟨⟨(f.1 : Set (Fin n)), ⟨medLarge_subset 𝓗 (r₁ : ℝ) f.1.2,
            by exact_mod_cast f.2.1⟩⟩, f.2.2⟩ :
          {f : 𝓗.largeEdges r₀ // (((f : Set (Fin n)) ∩ e).Nonempty)})) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x => (x.1.1 : Set (Fin n))) hab
  refine le_trans (Nat.cast_le.mpr (Nat.card_le_card_of_injective _ hinj)) ?_
  exact card_largeEdges_meeting_le hlin hr₀ hn he hsize

/-- **The list size of Theorem 1.2.** -/
theorem card_largeColours_le {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {r₁ r₀ : ℕ} (hr₀ : 2 ≤ r₀) (hn : 0 < n) {K : ℕ}
    (φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin K)) {e : Set (Fin n)} (he : e ∈ 𝓗)
    (hsize : edgeSize e ≤ r₁) :
    ((largeColours 𝓗 (r₁ : ℝ) (r₀ : ℝ) φ e).card : ℝ) ≤
      (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) := by
  classical
  have hconv : (((Finset.univ : Finset (medLarge 𝓗 (r₁ : ℝ))).filter
      (fun f : medLarge 𝓗 (r₁ : ℝ) => (r₀ : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) ∧
        (((f : Set (Fin n)) ∩ e).Nonempty))).card : ℝ) =
      (Nat.card {f : medLarge 𝓗 (r₁ : ℝ) //
        (r₀ : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) ∧
        (((f : Set (Fin n)) ∩ e).Nonempty)} : ℝ) := by
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1 : ((largeColours 𝓗 (r₁ : ℝ) (r₀ : ℝ) φ e).card : ℝ) ≤
      (((Finset.univ : Finset (medLarge 𝓗 (r₁ : ℝ))).filter
        (fun f : medLarge 𝓗 (r₁ : ℝ) => (r₀ : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) ∧
          (((f : Set (Fin n)) ∩ e).Nonempty))).card : ℝ) := by
    rw [largeColours]
    exact_mod_cast Finset.card_image_le
  have h2 := card_mediumLarge_meeting_le hlin hr₀ hn he hsize
  linarith [h1, hconv.le, h2]

/-- **Gluing the small-edge colouring to the medium/large colouring.** -/
theorem colorable_of_mediumLarge_colouring {𝓗 : Hypergraph (Fin n)} {r₁ r₀ : ℕ} {K : ℕ}
    (φ : (medLarge 𝓗 (r₁ : ℝ)).Coloring (Fin K))
    (CC : Finset (Fin K))
    (hmedium : ∀ f : medLarge 𝓗 (r₁ : ℝ), (edgeSize (f : Set (Fin n)) : ℝ) ≤ (r₀ : ℝ) →
        φ.labels f ∈ CC)
    (ψ : (𝓗.smallEdges r₁).Coloring (Fin K))
    (hψ : ∀ e : 𝓗.smallEdges r₁, ψ.labels e ∉ CC ∧
        ∀ f : medLarge 𝓗 (r₁ : ℝ), (r₀ : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) →
          (((f : Set (Fin n)) ∩ (e.1 : Set (Fin n))).Nonempty) → ψ.labels e ≠ φ.labels f) :
    𝓗.Colorable K := by
  classical
  have hcover : ∀ e ∈ 𝓗, e ∈ 𝓗.smallEdges r₁ ∨ e ∈ medLarge 𝓗 (r₁ : ℝ) := by
    intro e he
    by_cases h : edgeSize e ≤ r₁
    · exact Or.inl ((mem_smallEdges 𝓗 r₁ e).mpr ⟨he, h⟩)
    · exact Or.inr ((mem_medLarge).mpr ⟨he, by exact_mod_cast (by omega : r₁ < edgeSize e)⟩)
  have hdisj : Disjoint (𝓗.smallEdges r₁) (medLarge 𝓗 (r₁ : ℝ)) := by
    rw [Set.disjoint_left]
    intro e he hs
    rw [mem_smallEdges] at he
    rw [mem_medLarge] at hs
    exact absurd hs.2 (not_lt.mpr (by exact_mod_cast he.2 : ((edgeSize e : ℝ) ≤ (r₁ : ℝ))))
  exact ⟨coloringUnionCrossGen hcover hdisj ψ φ (by
    intro e₁ e₂ hnon heq
    by_cases hbig : (r₀ : ℝ) < (edgeSize (e₂ : Set (Fin n)) : ℝ)
    · exact (hψ e₁).2 e₂ hbig (by simpa [Set.inter_comm] using hnon) heq
    · exact (hψ e₁).1 (heq ▸ hmedium e₂ (le_of_not_gt hbig)))⟩

/-- `α = 8(γ₁+β)` is at most `(5/2)σ` in the Theorem-1.2 hierarchy. -/
theorem alpha_le_five_halves {σ γ₁ β α : ℝ} (hγ₁ : γ₁ ≤ σ / 4) (hβ : β ≤ γ₁ / 4)
    (hα : α = 8 * (γ₁ + β)) : α ≤ 5 / 2 * σ := by
  rw [hα]; nlinarith

theorem one_add_alpha_mul_le {α σ δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hσ0 : 0 < σ)
    (hα : α ≤ 5 / 2 * σ)
    (hσ : σ ≤ δ / 14) : (1 + α) * (1 - δ) ≤ 1 - σ - δ / 2 := by
  have hδ0' : (0 : ℝ) ≤ 1 - δ := by linarith
  have hstep1 : (1 + α) * (1 - δ) ≤ (1 + 5 / 2 * σ) * (1 - δ) :=
    mul_le_mul_of_nonneg_right (by linarith) hδ0'
  have hstep2 : (1 + 5 / 2 * σ) * (1 - δ) ≤ 1 + 5 / 2 * σ := by
    nlinarith [mul_nonneg hσ0.le (le_of_lt hδ0), hδ0, hσ0]
  nlinarith [hstep1, hstep2, hσ, hσ0, hδ0]

theorem kahn_bound_of_floor {α σ δ : ℝ} {K : ℕ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ0 : 0 < σ) (hα : α ≤ 5 / 2 * σ) (hσ : σ ≤ δ / 14)
    (hn : 2 / δ ≤ (n : ℝ))
    (hK : (K : ℝ) = ((⌊(1 - σ) * (n : ℝ)⌋₊ : ℕ) : ℝ)) :
    (1 + α) * ((1 - δ) * (n : ℝ)) ≤ (K : ℝ) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hmain : (1 + α) * ((1 - δ) * (n : ℝ)) ≤ (1 - σ) * (n : ℝ) - 1 := by
    have h := one_add_alpha_mul_le hδ0 hδ1 hσ0 hα hσ
    have h2 : (1 + α) * ((1 - δ) * (n : ℝ)) ≤ (1 - σ - δ / 2) * (n : ℝ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right h hn0
    have h3 : (1 - σ - δ / 2) * (n : ℝ) = (1 - σ) * (n : ℝ) - δ / 2 * (n : ℝ) := by ring
    have h4 : (1 : ℝ) ≤ δ / 2 * (n : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_left hn (by linarith : (0 : ℝ) ≤ δ / 2)
      have h5 : δ / 2 * (2 / δ) = 1 := by field_simp
      linarith [hmul, h5.ge]
    linarith [h3.ge, h3.le]
  have hlt : (1 - σ) * (n : ℝ) < ((⌊(1 - σ) * (n : ℝ)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [hK]; linarith

/-- The ratio `r₁/(r₀-1)` bound used for the lists of Theorem 1.2. -/
theorem ratio_le_of_r₀ {r₁ r₀ : ℕ} {β X : ℝ} (hβ : 0 < β) (hX : 0 ≤ X) (hr₁ : 1 ≤ r₁)
    (h : ⌈4 * (r₁ : ℝ) / β⌉₊ + 2 ≤ r₀) :
    (r₁ : ℝ) * X / ((r₀ : ℝ) - 1) ≤ β / 4 * X := by
  have h2 : (⌈4 * (r₁ : ℝ) / β⌉₊ : ℝ) + 2 ≤ (r₀ : ℝ) := by exact_mod_cast h
  have hlt : 4 * (r₁ : ℝ) / β < (r₀ : ℝ) - 1 := by
    have h3 := Nat.le_ceil (4 * (r₁ : ℝ) / β)
    linarith
  have hpos : (0 : ℝ) < (r₀ : ℝ) - 1 := by
    have h4 : (0 : ℝ) < 4 * (r₁ : ℝ) / β := by
      have : (0 : ℝ) < 4 * (r₁ : ℝ) := by
        have : (1 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁
        linarith
      exact div_pos this hβ
    linarith
  have h5 : (r₁ : ℝ) ≤ β / 4 * ((r₀ : ℝ) - 1) := by
    rw [div_lt_iff₀ hβ] at hlt
    linarith
  rw [div_le_iff₀ hpos]
  nlinarith [h5, hX]

/-- **Theorem 1.2, nonextremal case.**  From the non-extremal colouring of the
medium/large edges (Theorem 6.7), Kahn's theorem colours the small edges, and
the two colourings glue along the cover `𝓗_small ∪ (𝓗_med ∪ 𝓗_large)`. -/
theorem colorable_of_nonextremal_kahn {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    {r₁ r₀ : ℕ} {δ σ γ₁ β α : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hδ13 : δ ≤ 1 / 3) (hσ0 : 0 < σ) (hσ14 : σ ≤ δ / 14)
    (hα : α ≤ 5 / 2 * σ) (hαdef : α = 8 * (γ₁ + β)) (hβ0 : 0 < β) (hγ₁0 : 0 < γ₁)
    (hβγ₁ : β ≤ γ₁ / 4) (hγ₁σ : γ₁ ≤ σ / 4)
    (hn2 : 2 ≤ n) (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀)
    (hr₀ratio : ⌈4 * (r₁ : ℝ) / β⌉₊ + 2 ≤ r₀) (hσ256 : σ ≤ 1 / 256)
    (hnslack : 2 / δ ≤ (n : ℝ))
    (hNE : LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) (medLarge 𝓗 (r₁ : ℝ)))
    (hΔsmall : ((hypergraphMaxDegree (𝓗.smallEdges r₁) : ℕ) : ℝ) ≤ (1 - δ) * (n : ℝ))
    (hKahn : ∀ c : ℕ, (1 + α) * ((1 - δ) * (n : ℝ)) ≤ (c : ℝ) →
        ∀ Λ : (𝓗.smallEdges r₁) → Finset (Fin c),
        (∀ e : 𝓗.smallEdges r₁, ((Λ e).card : ℝ) ≤ α * ((1 - δ) * (n : ℝ)) / 2) →
        ∃ φ : (𝓗.smallEdges r₁).Coloring (Fin c), ∀ e, φ.labels e ∉ Λ e) :
    ∃ k : ℕ, (k : ℝ) ≤ (1 - σ) * (n : ℝ) ∧ 𝓗.Colorable k := by
  classical
  obtain ⟨φ, C₁, Cmed, hφuse, hC₁card, hCmedsub, hCmedcard, hmed, hCmedclass, hsgl,
    hsmallcls⟩ := hNE
  have hn0 : 0 < n := by omega
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  set K : ℕ := ⌊(1 - σ) * (n : ℝ)⌋₊ with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    refine Nat.le_floor ?_
    simp only [Nat.cast_one]
    have hσn : σ * (n : ℝ) ≤ (1 / 256) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hσ256 (Nat.cast_nonneg n)
    have h4 : (255 / 256) * (n : ℝ) ≤ (n : ℝ) - σ * (n : ℝ) := by linarith [hσn]
    have h5 : (1 : ℝ) ≤ (255 / 256) * (n : ℝ) := by linarith [hn2R]
    have h6 : (1 - σ) * (n : ℝ) = (n : ℝ) - σ * (n : ℝ) := by ring
    linarith [h4, h5, h6]
  have hK0 : 0 < K := hK1
  have hC₁K : C₁.card ≤ K := by rw [hK]; exact Nat.le_floor hC₁card
  obtain ⟨ψ', hψ'eq, hψ'med⟩ := Coloring.relabel φ hφuse hC₁K hK0
  set CC : Finset (Fin K) := Cmed.image (colourCast C₁ hC₁K hK0) with hCC
  have hCCmed : ∀ f : medLarge 𝓗 (r₁ : ℝ),
      (edgeSize (f : Set (Fin n)) : ℝ) ≤ (r₀ : ℝ) → ψ'.labels f ∈ CC := by
    intro f hf
    have h2 : φ.labels f ∈ Cmed := hmed f ⟨f.2.2, hf⟩
    rw [hψ'eq f]
    exact Finset.mem_image.mpr ⟨φ.labels f, h2, rfl⟩
  set Λ : (𝓗.smallEdges r₁) → Finset (Fin K) :=
    (fun e => smallLists 𝓗 (r₁ : ℝ) (r₀ : ℝ) ψ' CC (e : Set (Fin n))) with hΛdef
  have hΛ : ∀ e : 𝓗.smallEdges r₁, ((Λ e).card : ℝ) ≤ α * ((1 - δ) * (n : ℝ)) / 2 := by
    intro e
    have he𝓗 : ((e : Set (Fin n))) ∈ 𝓗 := smallEdges_subset 𝓗 r₁ e.2
    have hes : edgeSize (e : Set (Fin n)) ≤ r₁ :=
      ((mem_smallEdges 𝓗 r₁ (e : Set (Fin n))).mp e.2).2
    have h1 := card_largeColours_le hlin hr₀2 hn0 ψ' he𝓗 hes
    have hratio := ratio_le_of_r₀ hβ0 (Nat.cast_nonneg n) (by omega : 1 ≤ r₁) hr₀ratio
    have h2 : (CC.card : ℝ) ≤ γ₁ * (n : ℝ) := by
      rw [hCC]
      exact le_trans (Nat.cast_le.mpr Finset.card_image_le) hCmedcard
    have h3 : ((Λ e).card : ℝ) ≤
        ((largeColours 𝓗 (r₁ : ℝ) (r₀ : ℝ) ψ' (e : Set (Fin n))).card : ℝ) +
          (CC.card : ℝ) := by
      rw [hΛdef]
      simp only [smallLists]
      exact_mod_cast Finset.card_union_le _ _
    have h4 : β / 4 * (n : ℝ) + γ₁ * (n : ℝ) ≤ α * ((1 - δ) * (n : ℝ)) / 2 := by
      have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hδ' : (8 : ℝ) / 3 ≤ 4 * (1 - δ) := by linarith
      have hsum : (0 : ℝ) ≤ γ₁ + β := by linarith
      have h2 : β / 4 + γ₁ ≤ (8 / 3) * (γ₁ + β) := by linarith [hβ0, hγ₁0]
      have h3 : (8 / 3) * (γ₁ + β) ≤ 4 * (1 - δ) * (γ₁ + β) := by
        nlinarith [hδ', hsum]
      calc β / 4 * (n : ℝ) + γ₁ * (n : ℝ) = (β / 4 + γ₁) * (n : ℝ) := by ring
        _ ≤ (8 / 3) * (γ₁ + β) * (n : ℝ) := mul_le_mul_of_nonneg_right h2 hn'
        _ ≤ 4 * (1 - δ) * (γ₁ + β) * (n : ℝ) := mul_le_mul_of_nonneg_right h3 hn'
        _ = α * ((1 - δ) * (n : ℝ)) / 2 := by rw [hαdef]; ring
    linarith [h1, h2, h3, hratio, h4]
  have hKbound : (1 + α) * ((1 - δ) * (n : ℝ)) ≤ (K : ℝ) :=
    kahn_bound_of_floor hδ0 hδ1 hσ0 hα hσ14 hnslack (by rw [hK])
  obtain ⟨ψ'', hψ''⟩ := hKahn K hKbound Λ hΛ
  have hψ''2 : ∀ e : 𝓗.smallEdges r₁, ψ''.labels e ∉ CC ∧
      ∀ f : medLarge 𝓗 (r₁ : ℝ), (r₀ : ℝ) < (edgeSize (f : Set (Fin n)) : ℝ) →
        (((f : Set (Fin n)) ∩ (e.1 : Set (Fin n))).Nonempty) →
          ψ''.labels e ≠ ψ'.labels f := by
    intro e
    have hnot := hψ'' e
    constructor
    · intro hc
      exact hnot (by
        rw [hΛdef]
        simp only [smallLists]
        exact Finset.mem_union_right _ hc)
    · intro f hf hnon heq
      exact hnot (by
        rw [hΛdef]
        simp only [smallLists]
        refine Finset.mem_union_left _ ?_
        rw [largeColours]
        refine Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hf, hnon⟩, ?_⟩
        exact heq.symm)
  refine ⟨K, ?_, colorable_of_mediumLarge_colouring ψ' CC hCCmed ψ'' hψ''2⟩
  rw [hK]
  exact Nat.floor_le (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - σ) (Nat.cast_nonneg n))

/-- **Theorem 1.2 of the paper** (`main-thm-2`), from the deep inputs
Molloy–Reed and Kahn. -/
theorem mainThm2_of_deep (hMR : MolloyReedStatement) (hK : KahnStatement) :
    MainThm2Statement := by
  intro δ hδ
  by_cases hvac : 1 - 3 * δ < 0
  · refine ⟨1, 1 / 2, by norm_num, ?_⟩
    intro n hn 𝓗 _ _ hcard
    exfalso
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnn : (0 : ℝ) ≤ ((𝓗.exEdges δ).ncard : ℝ) := Nat.cast_nonneg _
    nlinarith
  · push_neg at hvac
    have hLETS : LargeEdgeThmStatement := largeEdgeThmStatement_of_deep hMR hK
    set δ₁ : ℝ := min δ (1 / 4) with hδ₁
    have hδ₁pos : 0 < δ₁ := by rw [hδ₁]; exact lt_min hδ (by norm_num)
    have hδ₁1 : δ₁ ≤ 1 := by rw [hδ₁]; exact le_trans (min_le_right _ _) (by norm_num)
    obtain ⟨δ₀, hδ₀pos, hδ₀le, Hδ⟩ := hLETS δ₁ hδ₁pos hδ₁1
    set δ₂ : ℝ := min δ₁ δ₀ with hδ₂
    have hδ₂pos : 0 < δ₂ := by rw [hδ₂]; exact lt_min hδ₁pos hδ₀pos
    have hδ₂δ₀ : δ₂ ≤ δ₀ := by rw [hδ₂]; exact min_le_right _ _
    have hδ₂δ₁ : δ₂ ≤ δ₁ := by rw [hδ₂]; exact min_le_left _ _
    have hδ₁δ : δ₁ ≤ δ := by rw [hδ₁]; exact min_le_left _ _
    have hδ₁4 : δ₁ ≤ 1 / 4 := by rw [hδ₁]; exact min_le_right _ _
    have hδ₂δ : δ₂ ≤ δ := le_trans hδ₂δ₁ hδ₁δ
    have hδ₂4 : δ₂ ≤ 1 / 4 := le_trans hδ₂δ₁ hδ₁4
    obtain ⟨σ₀, hσ₀pos, hσ₀le, Hσ⟩ := Hδ δ₂ hδ₂pos hδ₂δ₀
    set σ : ℝ := min σ₀ (δ₂ / 64) with hσ
    have hσpos : 0 < σ := by rw [hσ]; exact lt_min hσ₀pos (by positivity)
    have hσ64 : σ ≤ δ₂ / 64 := by rw [hσ]; exact min_le_right _ _
    have hσσ₀ : σ ≤ σ₀ := by rw [hσ]; exact min_le_left _ _
    obtain ⟨γ₁₀, hγ₁₀pos, hγ₁₀le, Hγ⟩ := Hσ σ hσpos hσσ₀
    set γ₁ : ℝ := min γ₁₀ (σ / 4) with hγ₁
    have hγ₁pos : 0 < γ₁ := by rw [hγ₁]; exact lt_min hγ₁₀pos (by positivity)
    have hγ₁σ : γ₁ ≤ σ / 4 := by rw [hγ₁]; exact min_le_right _ _
    have hγ₁γ₁₀ : γ₁ ≤ γ₁₀ := by rw [hγ₁]; exact min_le_left _ _
    obtain ⟨β₀, hβ₀pos, hβ₀le, Hβ⟩ := Hγ γ₁ hγ₁pos hγ₁γ₁₀
    set β : ℝ := min β₀ (γ₁ / 4) with hβ
    have hβpos : 0 < β := by rw [hβ]; exact lt_min hβ₀pos (by positivity)
    have hβγ₁ : β ≤ γ₁ / 4 := by rw [hβ]; exact min_le_right _ _
    have hββ₀ : β ≤ β₀ := by rw [hβ]; exact min_le_left _ _
    obtain ⟨R₁, hR₁pos, HR₁⟩ := Hβ β hβpos hββ₀
    set r₁ : ℕ := max R₁ 2 with hr₁
    have hr₁2 : 2 ≤ r₁ := by rw [hr₁]; exact le_max_right _ _
    have hR₁r₁ : R₁ ≤ r₁ := by rw [hr₁]; exact le_max_left _ _
    obtain ⟨R₀, hR₀pos, HR₀⟩ := HR₁ r₁ hR₁r₁
    set r₀ : ℕ := max R₀ (max (r₁ + 1) (⌈4 * (r₁ : ℝ) / β⌉₊ + 2)) with hr₀
    have hR₀r₀ : R₀ ≤ r₀ := by rw [hr₀]; exact le_max_left _ _
    have hr₀ratio : ⌈4 * (r₁ : ℝ) / β⌉₊ + 2 ≤ r₀ := by
      rw [hr₀]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hr₁r₀ : r₁ < r₀ := by
      have h : r₁ + 1 ≤ r₀ := by
        rw [hr₀]; exact le_trans (le_max_left _ _) (le_max_right _ _)
      omega
    obtain ⟨N₀, hN₀pos, HN₀⟩ := HR₀ r₀ hR₀r₀
    set α : ℝ := 8 * (γ₁ + β) with hα
    have hαpos : 0 < α := by rw [hα]; positivity
    obtain ⟨D₀, hD₀pos, hKahn0⟩ := hK α hαpos r₁ hr₁2
    set n₀ : ℕ := max N₀ (max (⌈1000 / δ₂ ^ 2⌉₊ + 2)
      (max (⌈2 / δ⌉₊ + 2) (⌈D₀ / (1 - δ)⌉₊ + 1))) with hn₀
    refine ⟨n₀, σ, hσpos, ?_⟩
    intro n hn 𝓗 hlin hΔm hcard
    rw [hn₀] at hn
    have hnN₀ : N₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hnA : ⌈1000 / δ₂ ^ 2⌉₊ + 2 ≤ n :=
      le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn
    have hnB : ⌈2 / δ⌉₊ + 2 ≤ n :=
      le_trans (le_trans (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)) hn
    have hnC : ⌈D₀ / (1 - δ)⌉₊ + 1 ≤ n :=
      le_trans (le_trans (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
        (Nat.le_max_right _ _)) hn
    have hn2 : 2 ≤ n := by omega
    have hn0 : 0 < n := by omega
    have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hδ13 : δ ≤ 1 / 3 := by linarith
    have hδ1 : δ ≤ 1 := by linarith
    have hn1000 : 1000 / δ₂ ^ 2 ≤ (n : ℝ) := by
      have h : ⌈1000 / δ₂ ^ 2⌉₊ ≤ n := by omega
      calc 1000 / δ₂ ^ 2 ≤ (⌈1000 / δ₂ ^ 2⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := Nat.cast_le.mpr h
    have hnslack : 2 / δ ≤ (n : ℝ) := by
      have h : ⌈2 / δ⌉₊ ≤ n := by omega
      calc 2 / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (n : ℝ) := Nat.cast_le.mpr h
    have hD₀le : D₀ ≤ (1 - δ) * (n : ℝ) := by
      have h : ⌈D₀ / (1 - δ)⌉₊ ≤ n := by omega
      have h1 : D₀ / (1 - δ) ≤ (⌈D₀ / (1 - δ)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (0 : ℝ) < 1 - δ := by linarith
      have h3 : D₀ / (1 - δ) ≤ (n : ℝ) := le_trans h1 (Nat.cast_le.mpr h)
      rw [div_le_iff₀ h2] at h3
      linarith [h3]
    have hσ256 : σ ≤ 1 / 256 := by linarith [hσ64, hδ₂4]
    have hσδ : σ ≤ δ / 64 := by linarith [hσ64, hδ₂δ]
    have hσδ14 : σ ≤ δ / 14 := by linarith
    have hα5 : α ≤ 5 / 2 * σ := by
      rw [hα]; exact alpha_le_five_halves hγ₁σ hβγ₁ rfl
    have hr₀2 : 2 ≤ r₀ := by omega
    have hcard₂ : ((canonFinset (𝓗.exEdges δ₂)).card : ℝ) ≤ (1 - 3 * δ₂) * (n : ℝ) := by
      rw [canonFinset_card_eq_ncard]
      have h1 : ((𝓗.exEdges δ₂).ncard : ℝ) ≤ ((𝓗.exEdges δ).ncard : ℝ) :=
        Nat.cast_le.mpr (exEdges_ncard_mono hδ₂δ)
      have h3 : (1 - 3 * δ) * (n : ℝ) ≤ (1 - 3 * δ₂) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
      linarith
    have hvol : volume n (𝓗.exEdges δ₂) < 1 - δ₂ :=
      volume_exEdges_lt hδ₂pos hδ₂4 hn1000 hcard₂
    have hinst := HN₀ n hnN₀ (medLarge 𝓗 (r₁ : ℝ)) (fun e => e.2.2) (IsLinear.medLarge hlin)
    rcases hinst with hNE | hEx
    · have hsizeSmall : ∀ e : 𝓗.smallEdges r₁,
          (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r₁ : ℝ) :=
        fun e => by
          have h := ((mem_smallEdges 𝓗 r₁ (e : Set (Fin n))).mp e.2).2
          exact_mod_cast h
      have hΔsmall : ((hypergraphMaxDegree (𝓗.smallEdges r₁) : ℕ) : ℝ) ≤ (1 - δ) * (n : ℝ) :=
        le_trans (Nat.cast_le.mpr (hypergraphMaxDegree_mono (smallEdges_subset 𝓗 r₁))) hΔm
      have hKahn : ∀ c : ℕ, (1 + α) * ((1 - δ) * (n : ℝ)) ≤ (c : ℝ) →
          ∀ Λ : (𝓗.smallEdges r₁) → Finset (Fin c),
          (∀ e : 𝓗.smallEdges r₁, ((Λ e).card : ℝ) ≤ α * ((1 - δ) * (n : ℝ)) / 2) →
          ∃ φ : (𝓗.smallEdges r₁).Coloring (Fin c), ∀ e, φ.labels e ∉ Λ e := by
        intro c hc Λ hΛ
        exact hKahn0 ((1 - δ) * (n : ℝ)) hD₀le n (𝓗.smallEdges r₁) (IsLinear.smallEdges hlin r₁)
          hΔsmall hsizeSmall c hc Λ hΛ
      exact colorable_of_nonextremal_kahn hlin hδ hδ1 hδ13 hσpos hσδ14 hα5 rfl hβpos
        hγ₁pos hβγ₁ hγ₁σ hn2 hr₁2 hr₀2 hr₀ratio hσ256 hnslack hNE hΔsmall hKahn
    · exact (not_largeEdgeExtremal_of_volume hvol hEx).elim

end

end ErdosFaberLovaszConjecture
