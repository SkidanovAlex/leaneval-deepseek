import Submission.EFL.Reordering
import Submission.EFL.GreedyListColouring
import Submission.Commons.Data.Finset.exists_not_mem_of_card_lt_univ

/-!
# The classical chromatic-index bounds for linear hypergraphs

This module proves, unconditionally, the classical bounds stated after
Proposition 6.3 of the paper:

* `colorable_two_mul_add_one` / `chromaticIndex_le_two_mul_add_one`: every
  linear hypergraph on `n` vertices has `χ′ ≤ 2n + 1`;
* `colorable_of_min_edgeSize`: if moreover every edge has size at least
  `r₁ ≥ 2` then `χ′ ≤ (1 + 1/(r₁−1))n + 1`.

Both are proved by greedily colouring the edges along the *size-non-increasing*
ordering `sizeOrder` of `Reordering.lean`:

* `colorable_of_precedingDegree_le` — the greedy lemma: if every edge has at
  most `k-1` preceding neighbours, then `k` colours suffice (the colour of a
  new edge is chosen outside the colours of its preceding neighbours; the
  non-membership comes from the shared commons lemma
  `Commons.Data.Finset.exists_not_mem_of_card_lt_univ`);
* `precedingDegree_sizeOrder_le` — for an edge of size at least `2`, the
  forward degree is at most `n + n/(|e|−1)` (Proposition 6.3(i) with
  `α₁ = α₂ = 0`, applied to the family of preceding neighbours, which all have
  size `≥ |e|` by the ordering's monotonicity);
* `precedingDegree_sizeOrder_le_le_one` — for an edge of size at most `1`, the
  forward degree is at most `|e|·(n − |e|)`: all its preceding neighbours have
  size at least `2`, so the neighbour-family bound applies with `ℓ = 2`.

This is the "warm-up" bound of the paper; the conjecture itself needs
`χ′ ≤ n`, which is proved by the much deeper arguments of §6–§12.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ} {𝓗 : Hypergraph (Fin n)}

/-- **Greedy colouring along an ordering**: if every edge has at most `k-1`
preceding neighbours in the ordering `ord`, then `k` colours suffice. -/
theorem colorable_of_precedingDegree_le {k k' : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (ord : 𝓗 ≃ Fin k') (hk0 : 0 < k)
    (hk : ∀ e : 𝓗, precedingDegree 𝓗 ord e + 1 ≤ k) :
    𝓗.Colorable k := by
  classical
  have key : ∀ m : ℕ, m ≤ k' → ∃ φ : 𝓗 → Fin k,
      ∀ e f : 𝓗, (ord e : ℕ) < m → (ord f : ℕ) < m → e ≠ f →
        (((e : Set (Fin n))) ∩ ((f : Set (Fin n)))).Nonempty → φ e ≠ φ f := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨fun _ => ⟨0, hk0⟩, by intro e f he _ _ _; exact absurd he (by omega)⟩
    | succ m ih =>
      intro hm
      obtain ⟨φ, hφ⟩ := ih (by omega)
      have hlt : m < k' := by omega
      let e₀ : 𝓗 := ord.symm ⟨m, hlt⟩
      have hrank₀ : (ord e₀ : ℕ) = m := by simp [e₀]
      let T : Finset (Fin k) := (precedingNeighbours 𝓗 ord e₀).image φ
      have hTcard : T.card < k := by
        calc T.card ≤ (precedingNeighbours 𝓗 ord e₀).card := Finset.card_image_le
          _ = precedingDegree 𝓗 ord e₀ := rfl
          _ < k := by have h := hk e₀; omega
      obtain ⟨c, hc⟩ :=
        Commons.Data.Finset.exists_not_mem_of_card_lt_univ T
          (by simpa [Fintype.card_fin] using hTcard)
      refine ⟨fun e => if e = e₀ then c else φ e, ?_⟩
      have hmemT : ∀ g : 𝓗, g ≠ e₀ → (ord g : ℕ) < m →
          ((((g : Set (Fin n))) ∩ ((e₀ : Set (Fin n)))).Nonempty) → φ g ∈ T := by
        intro g hg hgr hint'
        have hgle : ord g ≤ ord e₀ := by
          rw [Fin.le_iff_val_le_val, hrank₀]
          omega
        have hmem : g ∈ precedingNeighbours 𝓗 ord e₀ := by
          rw [mem_precedingNeighbours]
          exact ⟨hg, hgle, hint'⟩
        exact Finset.mem_image.mpr ⟨g, hmem, rfl⟩
      have hrank_lt : ∀ g : 𝓗, (ord g : ℕ) < m + 1 → g ≠ e₀ → (ord g : ℕ) < m := by
        intro g hg hgne
        have h2 : (ord g : ℕ) ≠ m := by
          intro hcon
          exact hgne (ord.injective (Fin.ext (by rw [hrank₀]; exact hcon)))
        omega
      intro e f he hf hne hint
      by_cases he₀ : e = e₀
      · have hfne : f ≠ e₀ := by rintro rfl; exact hne he₀
        have hfr : (ord f : ℕ) < m := hrank_lt f hf hfne
        have hint' : (((f : Set (Fin n))) ∩ ((e₀ : Set (Fin n)))).Nonempty := by
          simpa [he₀, Set.inter_comm] using hint
        have hmem := hmemT f hfne hfr hint'
        have hcne : φ f ≠ c := fun hcon => hc (hcon ▸ hmem)
        simp only [he₀, hfne, reduceIte]
        exact fun hcon => hcne hcon.symm
      · by_cases hf₀ : f = e₀
        · have her : (ord e : ℕ) < m := hrank_lt e he he₀
          have hint' : (((e : Set (Fin n))) ∩ ((e₀ : Set (Fin n)))).Nonempty := by
            simpa [hf₀] using hint
          have hmem := hmemT e he₀ her hint'
          have hcne : φ e ≠ c := fun hcon => hc (hcon ▸ hmem)
          simp only [he₀, hf₀, reduceIte]
          exact hcne
        · simp only [he₀, if_neg, hf₀, if_neg]
          exact hφ e f (hrank_lt e he he₀) (hrank_lt f hf hf₀) hne hint
  obtain ⟨φ, hφ⟩ := key k' le_rfl
  exact ⟨⟨φ, fun e f hne hint => hφ e f (ord e).isLt (ord f).isLt hne hint⟩⟩


/-- An edge of size `0` has no neighbours. -/
lemma eq_empty_of_edgeSize_eq_zero {e : Set (Fin n)} (h : edgeSize e = 0) : e = ∅ := by
  have hv : verts e = ∅ := by
    have := Finset.card_eq_zero.mp h
    simpa [edgeSize] using this
  ext x
  constructor
  · intro hx
    have : x ∈ verts e := by rwa [mem_verts]
    rw [hv] at this
    exact absurd this (by simp)
  · intro hx
    simp at hx

/-- An edge of size `1` is a singleton. -/
lemma eq_singleton_of_edgeSize_eq_one {e : Set (Fin n)} {x : Fin n} (hx : x ∈ e)
    (h : edgeSize e = 1) : e = {x} := by
  have hv : (verts e).card = 1 := h
  have hx' : x ∈ verts e := by rwa [mem_verts]
  have hsub : verts e ⊆ {x} := by
    intro y hy
    rw [Finset.mem_singleton]
    by_contra hne
    have h2 : 2 ≤ (verts e).card := by
      have hsub' : ({x, y} : Finset (Fin n)) ⊆ verts e := by
        intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hx'
        · exact hy
      calc (2 : ℕ) = ({x, y} : Finset (Fin n)).card := by
            rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using hne), Finset.card_singleton]
        _ ≤ (verts e).card := Finset.card_le_card hsub'
    omega
  have hsingle : verts e = {x} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hx', fun y hy => by simpa using hsub hy⟩
  ext y
  rw [← mem_verts, hsingle, Finset.mem_singleton]
  exact Iff.rfl

/-- For the size-non-increasing ordering, the preceding degree of an edge of
size at least `2` is at most `n + n/(|e|−1)` (paper §6.2, Prop 6.3(i) with
`α₁ = α₂ = 0`). -/
lemma precedingDegree_sizeOrder_le {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] (hlin : 𝓗.IsLinear)
    (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) {e : 𝓗} (h2 : 2 ≤ edgeSize (e : Set (Fin n))) :
    (precedingDegree 𝓗 (sizeOrder ord₀) e : ℝ) ≤
      (n : ℝ) + (n : ℝ) / ((edgeSize (e : Set (Fin n)) : ℝ) - 1) := by
  classical
  have hF₁ : ∀ f ∈ precedingNeighbours 𝓗 (sizeOrder ord₀) e, f ∈ neighbourEdges 𝓗 e := by
    intro f hf
    rw [mem_neighbourEdges]
    exact ⟨((mem_precedingNeighbours 𝓗 (sizeOrder ord₀) e f).mp hf).1,
      ((mem_precedingNeighbours 𝓗 (sizeOrder ord₀) e f).mp hf).2.2⟩
  have hbig : ∀ f ∈ precedingNeighbours 𝓗 (sizeOrder ord₀) e,
      (1 + 0) * (edgeSize (e : Set (Fin n)) : ℝ) ≤ (edgeSize (f : Set (Fin n)) : ℝ) := by
    intro f hf
    have h := ((mem_precedingNeighbours 𝓗 (sizeOrder ord₀) e f).mp hf).2.1
    have hnat : (sizeOrder ord₀ f : ℕ) ≤ (sizeOrder ord₀ e : ℕ) := Fin.le_iff_val_le_val.mp h
    simpa using sizeOrder_ge_size ord₀ hnat
  have hcond : (1 + (0 : ℝ)) < (edgeSize (e : Set (Fin n)) : ℝ) := by
    have : (2 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by exact_mod_cast h2
    linarith
  have h := fwdnbr_inequality1 (𝓗 := 𝓗) hlin e 0 0 (le_refl 0) (le_refl 0)
    (precedingNeighbours 𝓗 (sizeOrder ord₀) e) ∅ hF₁ (by simp) (by simp) hbig (by simp) hcond
  simpa [precedingDegree] using h

/-- For the size-non-increasing ordering and an edge of size at most `1`, the
preceding degree is at most `|e|·(n−|e|)`: the preceding neighbours all have
size at least `2`, so `card_neighbour_family_le` applies with `ℓ = 2`. -/
lemma precedingDegree_sizeOrder_le_le_one {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) (ord₀ : 𝓗 ≃ Fin (Fintype.card 𝓗)) {e : 𝓗}
    (h1 : edgeSize (e : Set (Fin n)) ≤ 1) :
    precedingDegree 𝓗 (sizeOrder ord₀) e ≤
      edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n))) := by
  classical
  have hF₁ : ∀ f ∈ precedingNeighbours 𝓗 (sizeOrder ord₀) e, f ∈ neighbourEdges 𝓗 e := by
    intro f hf
    rw [mem_neighbourEdges]
    exact ⟨((mem_precedingNeighbours 𝓗 (sizeOrder ord₀) e f).mp hf).1,
      ((mem_precedingNeighbours 𝓗 (sizeOrder ord₀) e f).mp hf).2.2⟩
  have hsize2 : ∀ f ∈ precedingNeighbours 𝓗 (sizeOrder ord₀) e, 2 ≤ edgeSize (f : Set (Fin n)) := by
    intro f hf
    have hmem := (mem_precedingNeighbours 𝓗 (sizeOrder ord₀) e f).mp hf
    have hint : ((((f : Set (Fin n))) ∩ ((e : Set (Fin n))))).Nonempty := hmem.2.2
    obtain ⟨x, hx⟩ := hint
    have hx_f : x ∈ (f : Set (Fin n)) := hx.1
    have hx_e : x ∈ (e : Set (Fin n)) := hx.2
    rcases Nat.lt_or_ge (edgeSize (f : Set (Fin n))) 2 with hlt | hge
    · exfalso
      have hf1 : edgeSize (f : Set (Fin n)) ≤ 1 := by omega
      have hfe : (f : Set (Fin n)) = e := by
        rcases Nat.eq_zero_or_pos (edgeSize (f : Set (Fin n))) with h0 | hpos
        · rw [eq_empty_of_edgeSize_eq_zero h0] at hx_f
          exact absurd hx_f (by simp)
        · have hepos : 1 ≤ edgeSize (e : Set (Fin n)) := by
            have hpos' : 0 < (verts (e : Set (Fin n))).card :=
              Finset.card_pos.mpr ⟨x, by rwa [mem_verts]⟩
            simpa [edgeSize] using hpos'
          have hf1' : edgeSize (f : Set (Fin n)) = 1 := by omega
          have he1 : edgeSize (e : Set (Fin n)) = 1 := by omega
          rw [eq_singleton_of_edgeSize_eq_one hx_f hf1', eq_singleton_of_edgeSize_eq_one hx_e he1]
      exact hmem.1 (Subtype.ext hfe)
    · exact hge
  have h := card_neighbour_family_le (𝓗 := 𝓗) hlin e (precedingNeighbours 𝓗 (sizeOrder ord₀) e)
    hF₁ 2 (by norm_num) hsize2
  simpa [precedingDegree] using h

/-- **Classical bound**: every linear hypergraph on `n` vertices has chromatic
index at most `2n + 1`.  (Paper, after Prop 6.3: the size-decreasing ordering
gives `d⪯(e) ≤ n + n/(|e|−1)` for `|e| ≥ 2` and `d⪯(e) ≤ |e|(n−|e|) ≤ n`
for `|e| ≤ 1`, so the greedy colouring along the ordering uses at most
`2n + 1` colours.) -/
theorem colorable_two_mul_add_one {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) : 𝓗.Colorable (2 * n + 1) := by
  classical
  refine colorable_of_precedingDegree_le (sizeOrder (Fintype.equivFin 𝓗)) (by omega) ?_
  intro e
  by_cases h2 : 2 ≤ edgeSize (e : Set (Fin n))
  · have hbound := precedingDegree_sizeOrder_le (𝓗 := 𝓗) hlin (Fintype.equivFin 𝓗) h2
    have hden : (0 : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by exact_mod_cast h2
      linarith
    have hden1 : (1 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by exact_mod_cast h2
      linarith
    have hle : (n : ℝ) / ((edgeSize (e : Set (Fin n)) : ℝ) - 1) ≤ (n : ℝ) := by
      rw [div_le_iff₀ hden]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have : (precedingDegree 𝓗 (sizeOrder (Fintype.equivFin 𝓗)) e : ℝ) ≤ 2 * (n : ℝ) := by
      linarith
    have : precedingDegree 𝓗 (sizeOrder (Fintype.equivFin 𝓗)) e ≤ 2 * n := by exact_mod_cast this
    omega
  · have h1 : edgeSize (e : Set (Fin n)) ≤ 1 := by omega
    have hbound := precedingDegree_sizeOrder_le_le_one (𝓗 := 𝓗) hlin (Fintype.equivFin 𝓗) h1
    have hmul : edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n))) ≤ n := by
      calc edgeSize (e : Set (Fin n)) * (n - edgeSize (e : Set (Fin n)))
          ≤ 1 * n := Nat.mul_le_mul h1 (Nat.sub_le n _)
        _ = n := one_mul n
    omega

/-- **Classical bound, chromatic index form**: every linear hypergraph on `n`
vertices has `χ′ ≤ 2n + 1`. -/
theorem chromaticIndex_le_two_mul_add_one {n : ℕ} {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗]
    (hlin : 𝓗.IsLinear) : 𝓗.chromaticIndex ≤ 2 * n + 1 :=
  Hypergraph.chromaticIndex_le_of_colorable 𝓗 (colorable_two_mul_add_one hlin)

/-- Sharper form of the classical bound: if every edge has size at least
`r₁ ≥ 2` then `χ′ ≤ n + n/(r₁−1) + 1`, i.e. `(1 + 1/(r₁−1))n + 1`. -/
theorem colorable_of_min_edgeSize {𝓗 : Hypergraph (Fin n)} [Fintype 𝓗] (hlin : 𝓗.IsLinear)
    {r₁ k : ℕ} (hr : 2 ≤ r₁) (hsize : ∀ e : 𝓗, r₁ ≤ edgeSize (e : Set (Fin n)))
    (hk : (n : ℝ) + (n : ℝ) / ((r₁ : ℝ) - 1) + 1 ≤ (k : ℝ)) : 𝓗.Colorable k := by
  classical
  have hkpos : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := by
      have h1 : (0 : ℝ) ≤ (n : ℝ) + (n : ℝ) / ((r₁ : ℝ) - 1) := by
        have hr1 : (0 : ℝ) < (r₁ : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr
          linarith
        have h2 : (0 : ℝ) ≤ (n : ℝ) / ((r₁ : ℝ) - 1) :=
          div_nonneg (Nat.cast_nonneg n) (le_of_lt hr1)
        linarith
      linarith
    exact_mod_cast this
  refine colorable_of_precedingDegree_le (sizeOrder (Fintype.equivFin 𝓗)) hkpos ?_
  intro e
  have h2 : 2 ≤ edgeSize (e : Set (Fin n)) := le_trans hr (hsize e)
  have hbound := precedingDegree_sizeOrder_le (𝓗 := 𝓗) hlin (Fintype.equivFin 𝓗) h2
  have hden : (0 : ℝ) < (r₁ : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr
    linarith
  have hden' : (0 : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by exact_mod_cast h2
    linarith
  have hle : (n : ℝ) / ((edgeSize (e : Set (Fin n)) : ℝ) - 1) ≤ (n : ℝ) / ((r₁ : ℝ) - 1) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg (α := ℝ) n) hden
    have : (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) := by exact_mod_cast hsize e
    linarith
  have hreal : (precedingDegree 𝓗 (sizeOrder (Fintype.equivFin 𝓗)) e : ℝ) + 1 ≤ (k : ℝ) := by
    linarith
  have hnat : precedingDegree 𝓗 (sizeOrder (Fintype.equivFin 𝓗)) e + 1 ≤ k := by
    exact_mod_cast hreal
  exact hnat

end

end ErdosFaberLovaszConjecture
