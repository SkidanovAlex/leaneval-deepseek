import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.AuxDefs

/-!
# The vertex count of the auxiliary hypergraph `𝓗_aux` (§8)

The auxiliary hypergraph `𝓗_aux` of the paper's proof of
`lem:pseudorandom_matching` has two kinds of vertices: the edges `e*` of `𝓖`,
and the copies `w^i` of the vertices `w ∈ V(𝓖)` that avoid `ι '' V(M_i)`
(see `Work.Deep.Nibble.AuxVertex`).  This file proves the paper's cardinality
bounds `n ≤ v(𝓗_aux) ≤ n^7`.

The upper bound is obtained by decomposing the vertex type into the two pieces
(a sum of subtypes) and bounding each piece: the number of edges of the
`r`-uniform `𝓖` is at most `(∑_w d_{𝓖}(w))/1 ≤ 2 D M` (every edge has at
least one vertex, so `𝓖` injects into the set of incidences, whose size is the
sum of the degrees), and the copies contribute at most `D M`.

The lower bound only uses the `w^i`-vertices: for each `i` there are at least
`M - β D ≥ M - D/2` vertices `w` with `w ∉ ι '' V(M_i)`, whence the vertex set
has at least `D (M - β D) ≥ n` elements.
-/

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

attribute [local instance] Classical.propDecidable

noncomputable section

/-- In a hypergraph all of whose edges are nonempty, the number of edges is at
most the sum of the degrees: every edge is counted by the degree of each of its
vertices. -/
theorem ncard_le_sum_hdeg {M : ℕ} (𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M))
    (hne : ∀ f ∈ 𝓖, f.Nonempty) :
    𝓖.ncard ≤ ∑ w : Fin M, MultiHypergraph.hdeg 𝓖 w := by
  have hunion : (⋃ w : Fin M, {e ∈ 𝓖 | w ∈ e}) = 𝓖 := by
    ext e
    constructor
    · intro h
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
      exact hw.1
    · intro he
      obtain ⟨w, hw⟩ := hne e he
      exact Set.mem_iUnion.mpr ⟨w, he, hw⟩
  calc 𝓖.ncard = (⋃ w : Fin M, {e ∈ 𝓖 | w ∈ e}).ncard := by rw [hunion]
    _ ≤ ∑ w : Fin M, ({e ∈ 𝓖 | w ∈ e} : Set (Set (Fin M))).ncard :=
        Set.ncard_iUnion_le_of_fintype _
    _ = ∑ w : Fin M, MultiHypergraph.hdeg 𝓖 w := rfl

/-- The number of vertices of `Fin M` outside a set `S`. -/
theorem card_compl_ncard {M : ℕ} (S : Set (Fin M)) :
    Fintype.card {w : Fin M // w ∉ S} = M - S.ncard := by
  have h := Fintype.card_congr (Equiv.sumCompl (p := fun w : Fin M => w ∈ S)).symm
  rw [Fintype.card_sum, Set.fintypeCard_eq_ncard] at h
  rw [Fintype.card_fin] at h
  omega

/-- The real form of `card_compl_ncard`. -/
theorem card_compl_cast {M : ℕ} (S : Set (Fin M)) :
    (Fintype.card {w : Fin M // w ∉ S} : ℝ) = (M : ℝ) - (S.ncard : ℝ) := by
  have hle : S.ncard ≤ M := by
    have h1 : S.ncard ≤ (Set.univ : Set (Fin M)).ncard := Set.ncard_le_ncard (Set.subset_univ S)
    simpa [Set.ncard_univ] using h1
  rw [card_compl_ncard S, Nat.cast_sub hle]

/-- Cardinality bounds `n ≤ v(𝓗_aux) ≤ n^7` for the vertex type of the auxiliary
hypergraph `𝓗_aux` of the paper's proof of `lem:pseudorandom_matching`. -/
theorem aux_card {n M D r : ℕ} {𝓖 : ErdosFaberLovaszConjecture.Hypergraph (Fin M)}
    {ι : Fin n ↪ Fin M} {Mfam : Fin D → Set (Set (Fin n))} {β : ℝ}
    (hr : 1 ≤ r) (huni : ∀ f ∈ 𝓖, f.ncard = r)
    (hdeg : ∀ w : Fin M, (ErdosFaberLovaszConjecture.MultiHypergraph.hdeg 𝓖 w : ℝ) ≤ 2 * D)
    (hβ : β ≤ 1 / 2)
    (hMsize : ∀ i, ((ErdosFaberLovaszConjecture.famVert (Mfam i)).ncard : ℝ) ≤ β * D)
    (hMn : (M : ℝ) ≤ (n : ℝ) ^ 5) (hDn : (D : ℝ) ≤ (n : ℝ)) (hD2 : (2 : ℝ) ≤ D)
    (hn : (3 : ℝ) ≤ (n : ℝ)) :
    (n : ℝ) ≤ (Fintype.card (Work.Deep.Nibble.AuxVertex n M D 𝓖 ι Mfam) : ℝ) ∧
      (Fintype.card (Work.Deep.Nibble.AuxVertex n M D 𝓖 ι Mfam) : ℝ) ≤ (n : ℝ) ^ 7 := by
  classical
  have hn0 : (0:ℝ) < n := by linarith
  -- the embedding already forces `n ≤ M`
  have hnM : n ≤ M := by
    have h := Fintype.card_le_of_injective ι ι.injective
    simpa using h
  have hnM' : (n:ℝ) ≤ (M:ℝ) := by exact_mod_cast hnM
  -- ## The vertex type splits into the `e*`-vertices and the `w^i`-vertices
  have hcard1 : Fintype.card (AuxVertex n M D 𝓖 ι Mfam) =
      𝓖.ncard + Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} := by
    have hcard : Fintype.card (AuxVertex n M D 𝓖 ι Mfam) =
        Fintype.card (Sum {f : Set (Fin M) // f ∈ 𝓖}
          {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)}) :=
      Fintype.card_congr (Equiv.subtypeSum
        (p := fun y : Set (Fin M) ⊕ (Fin D × Fin M) =>
          y.elim (fun f => f ∈ 𝓖) (fun p => p.2 ∉ ι '' famVert (Mfam p.1))))
    rw [hcard, Fintype.card_sum, Set.fintypeCard_eq_ncard]
  have hcard2 : Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} =
      ∑ i : Fin D, Fintype.card {w : Fin M // w ∉ ι '' famVert (Mfam i)} := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
          (fun (i : Fin D) (w : Fin M) => w ∉ ι '' famVert (Mfam i)))]
    rw [Fintype.card_sigma]
  -- ## Upper bound for the `e*`-vertices
  have hedge_ne : ∀ f ∈ 𝓖, f.Nonempty := by
    intro f hf
    have h1 : 0 < f.ncard := by rw [huni f hf]; omega
    exact (Set.ncard_pos).mp h1
  have hG1 : 𝓖.ncard ≤ ∑ w : Fin M, MultiHypergraph.hdeg 𝓖 w := ncard_le_sum_hdeg 𝓖 hedge_ne
  have hG : (𝓖.ncard : ℝ) ≤ 2 * (D : ℝ) * (M : ℝ) := by
    have h2 : (∑ w : Fin M, ((MultiHypergraph.hdeg 𝓖 w : ℕ) : ℝ)) ≤
        ∑ w : Fin M, (2 * (D : ℝ)) := by
      apply Finset.sum_le_sum
      intro w _
      exact hdeg w
    have h3 : (∑ w : Fin M, (2 * (D : ℝ))) = 2 * (D : ℝ) * (M : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    calc (𝓖.ncard : ℝ) ≤ (∑ w : Fin M, ((MultiHypergraph.hdeg 𝓖 w : ℕ) : ℝ)) := by
          exact_mod_cast hG1
      _ ≤ ∑ w : Fin M, (2 * (D : ℝ)) := h2
      _ = 2 * (D : ℝ) * (M : ℝ) := h3
  -- ## Upper bound for the `w^i`-vertices (there are at most `D M` pairs)
  have hPup : (Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} : ℝ) ≤
      (D : ℝ) * (M : ℝ) := by
    have h := Fintype.card_le_of_injective
      (fun p : {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} => p.1)
      (fun a b hab => Subtype.ext hab)
    have h' : Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} ≤ D * M := by
      simpa [Fintype.card_prod, Fintype.card_fin] using h
    exact_mod_cast h'
  -- ## Lower bound for the `w^i`-vertices
  have himg : ∀ i : Fin D, ((ι '' famVert (Mfam i)).ncard : ℝ) ≤ β * (D : ℝ) := by
    intro i
    have h1 : ((ι '' famVert (Mfam i)).ncard : ℝ) ≤ ((famVert (Mfam i)).ncard : ℝ) := by
      have h2 := Set.ncard_image_le (f := (ι : Fin n → Fin M)) (s := famVert (Mfam i))
      exact_mod_cast h2
    linarith [hMsize i]
  have hPlow : (n : ℝ) ≤
      (Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} : ℝ) := by
    have hper : ∀ i : Fin D, (Fintype.card {w : Fin M // w ∉ ι '' famVert (Mfam i)} : ℝ)
        = (M : ℝ) - ((ι '' famVert (Mfam i)).ncard : ℝ) := fun i => card_compl_cast _
    have hstep : ∀ i : Fin D, (M : ℝ) - β * (D : ℝ) ≤
        (Fintype.card {w : Fin M // w ∉ ι '' famVert (Mfam i)} : ℝ) := by
      intro i; rw [hper i]; linarith [himg i]
    have hsum : (∑ i : Fin D, ((M:ℝ) - β * (D:ℝ))) ≤
        ∑ i : Fin D, (Fintype.card {w : Fin M // w ∉ ι '' famVert (Mfam i)} : ℝ) :=
      Finset.sum_le_sum (fun i _ => hstep i)
    have hsumval : (∑ i : Fin D, ((M:ℝ) - β * (D:ℝ))) = (D:ℝ) * ((M:ℝ) - β * (D:ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hD0 : (0:ℝ) ≤ (D:ℝ) := by linarith
    -- `M - βD ≥ n/2`, both signs of `β`
    have hMD : (n:ℝ)/2 ≤ (M:ℝ) - β * (D:ℝ) := by
      rcases lt_or_ge β 0 with hβ0 | hβ0
      · have hbD : β * (D:ℝ) ≤ 0 := by nlinarith [hβ0, hD0]
        linarith [hnM', hn]
      · have hbD : β * (D:ℝ) ≤ (1/2) * (n:ℝ) := by
          have h1 : β * (D:ℝ) ≤ (1/2) * (D:ℝ) := by nlinarith [hβ, hD0]
          have h2 : (1/2) * (D:ℝ) ≤ (1/2) * (n:ℝ) := by nlinarith [hDn]
          linarith
        linarith [hnM']
    have hnum : (n:ℝ) ≤ (D:ℝ) * ((M:ℝ) - β * (D:ℝ)) := by
      have h2 : (2:ℝ) * ((n:ℝ)/2) ≤ (D:ℝ) * ((M:ℝ) - β * (D:ℝ)) :=
        mul_le_mul hD2 hMD (by linarith) hD0
      linarith
    calc (n : ℝ) ≤ (D:ℝ) * ((M:ℝ) - β * (D:ℝ)) := hnum
      _ = ∑ i : Fin D, ((M:ℝ) - β * (D:ℝ)) := hsumval.symm
      _ ≤ ∑ i : Fin D, (Fintype.card {w : Fin M // w ∉ ι '' famVert (Mfam i)} : ℝ) := hsum
      _ = (Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} : ℝ) := by
            rw [hcard2, Nat.cast_sum]
  constructor
  · calc (n : ℝ) ≤ (Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} : ℝ) :=
          hPlow
      _ ≤ (Fintype.card (AuxVertex n M D 𝓖 ι Mfam) : ℝ) := by
            rw [hcard1, Nat.cast_add]
            exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  · have hDM6 : (D:ℝ) * (M:ℝ) ≤ (n:ℝ)^6 := by
      have hM0 : (0:ℝ) ≤ (M:ℝ) := by positivity
      calc (D:ℝ) * (M:ℝ) ≤ (n:ℝ) * (n:ℝ)^5 := mul_le_mul hDn hMn hM0 (by positivity)
        _ = (n:ℝ)^6 := by ring
    calc (Fintype.card (AuxVertex n M D 𝓖 ι Mfam) : ℝ)
        = (𝓖.ncard : ℝ) +
            (Fintype.card {p : Fin D × Fin M // p.2 ∉ ι '' famVert (Mfam p.1)} : ℝ) := by
            rw [hcard1, Nat.cast_add]
      _ ≤ 2 * (D : ℝ) * (M : ℝ) + (D : ℝ) * (M : ℝ) := add_le_add hG hPup
      _ = 3 * (D : ℝ) * (M : ℝ) := by ring
      _ ≤ 3 * (n:ℝ)^6 := by nlinarith [hDM6]
      _ ≤ (n:ℝ)^7 := by nlinarith [hn, pow_pos hn0 6]

end

end Work.Deep.Nibble
