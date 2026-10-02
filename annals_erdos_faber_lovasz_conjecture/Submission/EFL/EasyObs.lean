import Submission.EFL.Reservoir
import Submission.EFL.HugeAbsorption
import Submission.EFL.VplusBound

/-!
# Claim 12.1 (`claim:easyobs`), observation (EP4)

If `φ` is a colouring of the medium and large edges of `𝓗` of Type A
(`LargeEdgeNonExtremal`, Definition 12.2), then at most one colour class that
contains a huge edge is *difficult* (Definition 7.4: it covers at least
`3/4` of the vertices outside `U = V_+^{(1-ε)}(G)`, and `|V(𝓗) ∖ U| ≥ 2`).

Two distinct such colour classes would consist of single huge edges `e₀ ≠ e₁`
(Type A colour classes containing a huge edge are singletons), and each of
`e₀, e₁` contains at least `3|V∖U|/4` vertices of `V ∖ U`; hence
`e₀ ∩ e₁` has at least two vertices, contradicting the linearity of `𝓗`.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- A colour class of a colouring of the medium and large edges of `𝓗`,
viewed as a family of edges of `𝓗`. -/
def colorClassFam (𝓗 : Hypergraph (Fin n)) (r₁ : ℝ)
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) (c : Fin n) : Hypergraph (Fin n) :=
  {e | ∃ he : e ∈ medLarge 𝓗 r₁, φ.labels ⟨e, he⟩ = c}

/-- If a colour class consists of a single edge `e₀`, the vertices it covers
are exactly the vertices of `e₀`. -/
theorem classVertices_eq_of_colorClass_singleton {𝓗 : Hypergraph (Fin n)} {r₁ : ℝ}
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {c : Fin n}
    {e₀ : ↥(medLarge 𝓗 r₁)} (h : φ.colorClass c = {e₀}) :
    φ.classVertices c = (e₀ : Set (Fin n)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, hve⟩ := hv
    have hmem : e ∈ φ.colorClass c := he
    rw [h] at hmem
    rw [Set.mem_singleton_iff] at hmem
    rw [← hmem]
    exact hve
  · intro hv
    refine ⟨e₀, ?_, hv⟩
    rw [h]
    exact Set.mem_singleton _

/-- **Claim 12.1 (EP4).**  In a Type A colouring of the medium and large edges
of a linear hypergraph `𝓗`, there is at most one colour class that contains a
huge edge and is difficult with respect to `U`. -/
theorem easyObs_EP4 (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear) {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) {σ γ₁ β r₀ : ℝ} (U : Set (Fin n))
    (hA : IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ) :
    ({c : Fin n | φ.AssignedToHuge β c ∧ 2 ≤ (Uᶜ).ncard ∧
        3 * (Uᶜ).ncard ≤ 4 * ((φ.classVertices c) ∩ Uᶜ).ncard}).ncard ≤ 1 := by
  obtain ⟨C₁, Cmed, huse, hC₁, hCmedC₁, hCmed, hmed, hCmedvert, hsing, hlast⟩ := hA
  refine (Set.ncard_le_one (s := {c : Fin n | φ.AssignedToHuge β c ∧ 2 ≤ (Uᶜ).ncard ∧
      3 * (Uᶜ).ncard ≤ 4 * ((φ.classVertices c) ∩ Uᶜ).ncard}) (Set.toFinite _)).mpr ?_
  intro c hc c' hc'
  by_contra hne
  obtain ⟨e₀, he₀⟩ := hsing c hc.1
  obtain ⟨e₁, he₁⟩ := hsing c' hc'.1
  have hv₀ : φ.classVertices c = (e₀ : Set (Fin n)) := classVertices_eq_of_colorClass_singleton he₀
  have hv₁ : φ.classVertices c' = (e₁ : Set (Fin n)) :=
    classVertices_eq_of_colorClass_singleton he₁
  have hd₀ : 3 * (Uᶜ).ncard ≤ 4 * (((e₀ : Set (Fin n)) ∩ Uᶜ).ncard) := by
    rw [← hv₀]; exact hc.2.2
  have hd₁ : 3 * (Uᶜ).ncard ≤ 4 * (((e₁ : Set (Fin n)) ∩ Uᶜ).ncard) := by
    rw [← hv₁]; exact hc'.2.2
  have hN : 2 ≤ (Uᶜ).ncard := hc.2.1
  -- the two huge edges are distinct
  have hne' : (e₀ : Set (Fin n)) ≠ (e₁ : Set (Fin n)) := by
    intro h
    have hsub : e₀ = e₁ := Subtype.ext h
    have hm₀ : e₀ ∈ φ.colorClass c := by rw [he₀]; exact Set.mem_singleton _
    have hm₁ : e₀ ∈ φ.colorClass c' := by rw [hsub, he₁]; exact Set.mem_singleton _
    exact hne (hm₀.symm.trans hm₁)
  -- the intersection has at least two vertices
  have hinter : 2 ≤ (((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n)) : Set (Fin n))).ncard := by
    have hA₀ : ((e₀ : Set (Fin n)) ∩ Uᶜ).ncard ≤ (Uᶜ).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
    have hA₁ : ((e₁ : Set (Fin n)) ∩ Uᶜ).ncard ≤ (Uᶜ).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)
    -- `(↑e₀ ∩ Uᶜ) + (↑e₁ ∩ Uᶜ) ≥ N + 2`
    have hkey : (Uᶜ).ncard + 2 ≤ ((e₀ : Set (Fin n)) ∩ Uᶜ).ncard +
        ((e₁ : Set (Fin n)) ∩ Uᶜ).ncard := by
      rcases Nat.lt_or_ge (Uᶜ).ncard 4 with hN3 | hN4
      · have ha : ((e₀ : Set (Fin n)) ∩ Uᶜ).ncard = (Uᶜ).ncard := by omega
        have hb : ((e₁ : Set (Fin n)) ∩ Uᶜ).ncard = (Uᶜ).ncard := by omega
        omega
      · omega
    have key : ((((e₀ : Set (Fin n)) ∩ Uᶜ) ∩ ((e₁ : Set (Fin n)) ∩ Uᶜ)).ncard : ℝ) +
        ((((e₀ : Set (Fin n)) ∩ Uᶜ) ∪ ((e₁ : Set (Fin n)) ∩ Uᶜ)).ncard : ℝ) =
        (((e₀ : Set (Fin n)) ∩ Uᶜ).ncard : ℝ) +
        (((e₁ : Set (Fin n)) ∩ Uᶜ).ncard : ℝ) := by
      exact_mod_cast Set.ncard_inter_add_ncard_union
        ((e₀ : Set (Fin n)) ∩ Uᶜ) ((e₁ : Set (Fin n)) ∩ Uᶜ) (Set.toFinite _)
    have hub : ((((e₀ : Set (Fin n)) ∩ Uᶜ) ∪ ((e₁ : Set (Fin n)) ∩ Uᶜ)).ncard : ℝ) ≤
        ((Uᶜ).ncard : ℝ) := by
      have h₁ : ((e₀ : Set (Fin n)) ∩ Uᶜ : Set (Fin n)) ⊆ Uᶜ := Set.inter_subset_right
      have h₂ : ((e₁ : Set (Fin n)) ∩ Uᶜ : Set (Fin n)) ⊆ Uᶜ := Set.inter_subset_right
      have h := Set.ncard_le_ncard (Set.union_subset h₁ h₂) (Set.toFinite _)
      exact_mod_cast h
    have heq : (((e₀ : Set (Fin n)) ∩ Uᶜ) ∩ ((e₁ : Set (Fin n)) ∩ Uᶜ)) =
        (((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n))) ∩ Uᶜ) := by
      ext v
      simp only [Set.mem_inter_iff]
      tauto
    rw [heq] at key
    have hkeyR : ((Uᶜ).ncard : ℝ) + 2 ≤ (((e₀ : Set (Fin n)) ∩ Uᶜ).ncard : ℝ) +
        (((e₁ : Set (Fin n)) ∩ Uᶜ).ncard : ℝ) := by exact_mod_cast hkey
    have hmain : ((((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n))) ∩ Uᶜ).ncard : ℝ) ≥ 2 := by
      linarith [key, hub, hkeyR]
    have hle : ((((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n))) ∩ Uᶜ : Set (Fin n))).ncard ≤
        ((((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n))))).ncard :=
      Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
    have h3 : (2 : ℝ) ≤ ((((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n))))).ncard :=
      le_trans hmain (by exact_mod_cast hle)
    exact_mod_cast h3
  -- contradict linearity
  have hsub : (((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n))) : Set (Fin n)).Subsingleton :=
    hlin (medLarge_subset 𝓗 r₁ e₀.2) (medLarge_subset 𝓗 r₁ e₁.2) hne'
  have hone : (((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n))) : Set (Fin n)).ncard ≤ 1 :=
    (Set.ncard_le_one (s := ((e₀ : Set (Fin n)) ∩ (e₁ : Set (Fin n)) : Set (Fin n)))
      (Set.toFinite _)).mpr (fun a ha b hb => hsub ha hb)
  omega

/-- **Claim 12.1 (EP3), second part.**  In a Type B colouring of the medium
and large edges of a linear hypergraph, no colour class is difficult
(provided `|V ∖ U| ≥ (1 - 2δ)n`, which is the first part of (EP3) and the
parameter hierarchy `γ₁, β ≤ δ`). -/
theorem easyObs_EP3_no_difficult (𝓗 : Hypergraph (Fin n)) {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) {δ γ₂ γ₁ β r₀ : ℝ} (U : Set (Fin n))
    (hB : IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ)
    (hγδ : γ₁ ≤ δ) (hβδ : β ≤ δ) (hδ : δ < 3 / 10)
    (hU : (1 - 2 * δ) * (n : ℝ) ≤ ((Uᶜ).ncard : ℝ)) :
    ∀ c : Fin n, ¬ (2 ≤ (Uᶜ).ncard ∧
      3 * (Uᶜ).ncard ≤ 4 * ((φ.classVertices c) ∩ Uᶜ).ncard) := by
  obtain ⟨hex, Cmed, hCmed, hmed, hCmedvert, hhuge, hlast⟩ := hB
  intro c hc
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hbound : (φ.classVertexCount c : ℝ) ≤ δ * (n : ℝ) := by
    by_cases hmem : c ∈ Cmed
    · have h1 := hCmedvert c hmem
      nlinarith [h1, hγδ, hn]
    · by_cases hhg : φ.AssignedToHuge β c
      · exact hhuge c hhg
      · have h1 := hlast c hmem hhg
        nlinarith [h1, hβδ, hn]
  have h1 : 3 * ((Uᶜ).ncard : ℝ) ≤ 4 * (φ.classVertexCount c : ℝ) := by
    have hle : (((φ.classVertices c) ∩ Uᶜ).ncard : ℝ) ≤ (φ.classVertexCount c : ℝ) := by
      have h := Set.ncard_le_ncard (Set.inter_subset_left : (φ.classVertices c) ∩ Uᶜ ⊆
        φ.classVertices c) (Set.toFinite _)
      exact_mod_cast h
    have h2 : (3 * ((Uᶜ).ncard : ℝ)) ≤ 4 * (((φ.classVertices c) ∩ Uᶜ).ncard : ℝ) := by
      exact_mod_cast hc.2
    linarith
  have hUn : ((Uᶜ).ncard : ℝ) ≤ (n : ℝ) := by
    have h := Set.ncard_le_ncard (Set.subset_univ Uᶜ) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_fin] at h
    exact_mod_cast h
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := le_trans (by exact_mod_cast hc.1) hUn
  nlinarith [h1, hbound, hU, hδ, hn2]

/-- **Claim 12.1 (EP3), first part, in the form used in §12**: if the
extremal family of a Type B colouring has volume at least `1-δ` and every
extremal edge has at least three vertices, then `|U| ≤ 2δn` for
`U = V_+^{(1-ε)}(G)`. -/
theorem easyObs_EP3_card_Vplus (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear) {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) {δ γ₂ γ₁ β r₀ ε : ℝ}
    (hB : IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (h3 : 3 ≤ (1 - δ) * Real.sqrt (n : ℝ)) (hn1 : 1 ≤ n) :
    ((Vplus 𝓗 (1 - ε)).ncard : ℝ) ≤ 2 * δ * (n : ℝ) := by
  obtain ⟨⟨W, hWsub, hWext, hWvol⟩, hrest⟩ := hB
  have hWd : ∀ e ∈ W, 3 ≤ e.ncard := by
    intro e he
    have h1 := (hWext e he).1
    have h2 : (3 : ℝ) ≤ (edgeSize e : ℝ) := le_trans h3 h1
    have h4 : 3 ≤ edgeSize e := Nat.cast_le.mp h2
    rwa [edgeSize_eq_ncard] at h4
  have hvol : (1 - δ) * ((n : ℝ) * ((n : ℝ) - 1)) ≤
      (canonFinset W).sum (fun e => (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)) := by
    have hn2 : 2 ≤ n := by
      by_contra h
      push_neg at h
      have hn1' : n = 1 := by omega
      subst hn1'
      rw [volume_eq_canon] at hWvol
      norm_num at hWvol
      linarith
    have hDpos : 0 < (n : ℝ) * ((n - 1 : ℕ) : ℝ) := by
      have h1 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have h2 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
        exact_mod_cast (by omega : 0 < n - 1)
      positivity
    rw [volume_eq_canon] at hWvol
    rw [le_div_iff₀ hDpos] at hWvol
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    rw [hcast] at hWvol
    have hsum : (((canonFinset W).sum (fun e => edgeSize e * (edgeSize e - 1)) : ℕ) : ℝ) =
        (canonFinset W).sum (fun e => (e.ncard : ℝ) * ((e.ncard : ℝ) - 1)) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl (fun e he => ?_)
      have h4 : 1 ≤ e.ncard := by
        have h5 := hWd e (Finset.mem_filter.mp he).2
        omega
      rw [edgeSize_eq_ncard, Nat.cast_mul, Nat.cast_sub h4, Nat.cast_one]
    rwa [hsum] at hWvol
  exact card_Vplus_le_of_extremal 𝓗 W (Vplus 𝓗 (1 - ε)) hlin hWsub hWd hvol
    (fun w hw => hw) hδ0 hε0 hε1

/-- **Claim 12.1 (EP3).**  In the Type B case, `|U| ≤ 2δn` and no colour class
is difficult. -/
theorem easyObs_EP3 (𝓗 : Hypergraph (Fin n)) (hlin : 𝓗.IsLinear) {r₁ : ℝ}
    (φ : (medLarge 𝓗 r₁).Coloring (Fin n)) {δ γ₂ γ₁ β r₀ ε : ℝ}
    (hB : IsTypeB δ γ₂ γ₁ β r₁ r₀ 𝓗 φ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    (h3 : 3 ≤ (1 - δ) * Real.sqrt (n : ℝ)) (hδ3 : δ < 3 / 10)
    (hγδ : γ₁ ≤ δ) (hβδ : β ≤ δ) (hn1 : 1 ≤ n) :
    ((Vplus 𝓗 (1 - ε)).ncard : ℝ) ≤ 2 * δ * (n : ℝ) ∧
      ∀ c : Fin n, ¬ (2 ≤ ((Vplus 𝓗 (1 - ε))ᶜ).ncard ∧
        3 * ((Vplus 𝓗 (1 - ε))ᶜ).ncard ≤
          4 * ((φ.classVertices c) ∩ ((Vplus 𝓗 (1 - ε))ᶜ)).ncard) := by
  have hcard := easyObs_EP3_card_Vplus 𝓗 hlin φ hB hδ0 hδ1 hε0 hε1 h3 hn1
  refine ⟨hcard, ?_⟩
  -- `|Uᶜ| ≥ (1-2δ)n`
  have hUc : (1 - 2 * δ) * (n : ℝ) ≤ (((Vplus 𝓗 (1 - ε))ᶜ).ncard : ℝ) := by
    have hle : (Vplus 𝓗 (1 - ε)).ncard ≤ n := by
      have h := Set.ncard_le_ncard (Set.subset_univ (Vplus 𝓗 (1 - ε))) (Set.toFinite _)
      rwa [Set.ncard_univ, Nat.card_fin] at h
    have h1 : (((Vplus 𝓗 (1 - ε))ᶜ).ncard : ℝ) =
        (n : ℝ) - ((Vplus 𝓗 (1 - ε)).ncard : ℝ) := by
      rw [Set.ncard_compl (Vplus 𝓗 (1 - ε)), Nat.card_fin, Nat.cast_sub hle]
    rw [h1]
    linarith [hcard]
  exact easyObs_EP3_no_difficult 𝓗 φ (Vplus 𝓗 (1 - ε)) hB hγδ hβδ hδ3 hUc

end

end ErdosFaberLovaszConjecture
