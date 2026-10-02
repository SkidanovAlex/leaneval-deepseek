import Submission.EFL.S12Setup
import Submission.EFL.DiffAbs2
import Submission.EFL.AbsorberDeletion

/-!
# §12, Step 4 (`step:diff`): extending the difficult colour classes

This module formalises **Step 4** of the proof of Theorem 1.1 (the paper's
`step:diff`).  For the (at most one) colour `c ∈ C_diff` we apply the
difficult-edge absorption Lemma 7.12 (`difficult_edge_absorption`) to the huge
edge `e` with `φ⁻¹(c) = {e}`, obtaining either `χ'(𝓗) ≤ n` directly, or a
matching `M_c` with

* **(D1)** `M_c ⊇ φ⁻¹(c)`, `M_c ∖ φ⁻¹(c) ⊆ E(G) = 𝓗^{(2)}`,
  `M_c` covers `V^{(n-1)}(𝓗)`, and
  `|V^{(n-2)}(𝓗) ∖ V(M_c)| ≤ 5`.

We then define

* `R₁ = R_abs ∖ ⋃_{c ∈ C_diff} M_c` and
* `S₁ = S ∖ ⋃_{c ∈ C_diff} (V^{(n-2)}(𝓗) ∖ V(M_c))`,

and prove `(eq:R1abs)` (`R₁` is a `(ρ_abs, 3γ/2, ξ, ε)`-absorber for `𝓥`,
using the robustness Observation `obs:del_absorber`) and `(eq:boundS1)`
(`|S₁| ≥ |S| - 5`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Coercing a subfamily of a subhypergraph -/

/-- The family of edges of `𝓗` whose underlying set is an edge lying in the
family `S` of the subhypergraph `𝓖`. -/
def subFam {𝓖 𝓗 : Hypergraph (Fin n)} (S : Set 𝓖) : Set 𝓗 :=
  {e : 𝓗 | ∃ (he : (e : Set (Fin n)) ∈ 𝓖), (⟨(e : Set (Fin n)), he⟩ : 𝓖) ∈ S}

theorem mem_subFam {𝓖 𝓗 : Hypergraph (Fin n)} {S : Set 𝓖} {e : 𝓗} :
    e ∈ subFam (𝓖 := 𝓖) S ↔ ∃ (he : (e : Set (Fin n)) ∈ 𝓖),
      (⟨(e : Set (Fin n)), he⟩ : 𝓖) ∈ S := Iff.rfl

/-- The image of a matching under the coercion from a subhypergraph is a
matching. -/
theorem IsMatching.subFam {𝓖 𝓗 : Hypergraph (Fin n)} {S : Set 𝓖}
    (hS : IsMatching 𝓖 S) : IsMatching 𝓗 (subFam (𝓗 := 𝓗) S) := by
  intro e₁ h₁ e₂ h₂ hne
  obtain ⟨he₁, h₁'⟩ := h₁
  obtain ⟨he₂, h₂'⟩ := h₂
  exact hS h₁' h₂' (fun heq =>
    hne (Subtype.ext (congrArg (fun x : 𝓖 => (x : Set (Fin n))) heq)))

/-- A singleton family of a subhypergraph maps to a singleton family. -/
theorem subFam_singleton {𝓖 𝓗 : Hypergraph (Fin n)} (h : 𝓖 ⊆ 𝓗) {e : 𝓖} :
    subFam (𝓗 := 𝓗) ({e} : Set 𝓖) = {(⟨(e : Set (Fin n)), h e.2⟩ : 𝓗)} := by
  ext f
  constructor
  · rintro ⟨he, hfe⟩
    rw [Set.mem_singleton_iff] at hfe
    exact Subtype.ext (congrArg (fun x : 𝓖 => (x : Set (Fin n))) hfe)
  · intro hf
    subst hf
    refine ⟨e.2, ?_⟩
    rw [Set.mem_singleton_iff]

/-! ## The `R`-neighbourhood degree of a matching is at most one -/

/-- If `M` is a matching then at most one 2-edge of `M` contains `v`, so
`degAt (famOf M) v ≤ 1`. -/
theorem ncard_nbrs_famOf_le_one {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} (hM : IsMatching 𝓗 M)
    (v : Fin n) : (nbrs (famOf M) v).ncard ≤ 1 := by
  rw [Set.ncard_le_one (s := nbrs (famOf M) v)]
  intro a ha b hb
  have ha₀ : ({v, a} : Set (Fin n)) ∈ famOf M := ha
  have hb₀ : ({v, b} : Set (Fin n)) ∈ famOf M := hb
  rw [mem_famOf] at ha₀ hb₀
  obtain ⟨e₁, he₁, ha₁⟩ := ha₀
  obtain ⟨e₂, he₂, hb₂⟩ := hb₀
  have hv₁ : v ∈ (e₁ : Set (Fin n)) := by rw [ha₁]; simp
  have hv₂ : v ∈ (e₂ : Set (Fin n)) := by rw [hb₂]; simp
  have heq : e₁ = e₂ := by
    by_contra hne
    exact (Set.disjoint_left.mp (hM he₁ he₂ hne) hv₁) hv₂
  have hset : ({v, a} : Set (Fin n)) = ({v, b} : Set (Fin n)) := by rw [← ha₁, ← hb₂, heq]
  have ha' : a ∈ ({v, b} : Set (Fin n)) := by rw [← hset]; simp
  have hb' : b ∈ ({v, a} : Set (Fin n)) := by rw [hset]; simp
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha' hb'
  rcases ha' with h | h
  · rcases hb' with h2 | h2
    · exact h.trans h2.symm
    · exact h2.symm
  · exact h

/-- Deleting a matching from an absorber keeps it an absorber, at the cost of
increasing `γ` by `1/n` (the deleted part has maximum degree at most `1`). -/
theorem IsAbsorber.delete_famOf {G' R : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    {𝓗 : Hypergraph (Fin n)} {ρ γ γ' ξ : ℝ} (h : IsAbsorber G' R 𝓥 ρ γ ξ)
    {M : Set 𝓗} (hM : IsMatching 𝓗 M) (hγ : γ + 1 / (n : ℝ) ≤ γ') (hn : 1 ≤ n) :
    IsAbsorber G' (R \ famOf M) 𝓥 ρ γ' ξ := by
  have hsub : R \ famOf M ⊆ R := Set.sdiff_subset
  have hdel : ∀ v : Fin n, (degAt (R \ (R \ famOf M)) v : ℝ) ≤ (1 / (n : ℝ)) * (n : ℝ) := by
    intro v
    have hEq : R \ (R \ famOf M) = R ∩ famOf M := by
      ext e
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [hEq]
    have h1 : degAt (R ∩ famOf M) v ≤ degAt (famOf M) v := by
      unfold degAt
      refine Set.ncard_le_ncard (fun x hx => ?_) (Set.toFinite _)
      simp only [nbrs, Set.mem_ofPred_eq] at hx ⊢
      exact hx.2
    have h2 : degAt (famOf M) v ≤ 1 := ncard_nbrs_famOf_le_one hM v
    have h3 : ((1 / (n : ℝ)) * (n : ℝ)) = 1 := by
      have hn0 : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [h3]
    exact_mod_cast le_trans h1 h2
  have h' := IsAbsorber.delete h hsub hdel
  exact IsAbsorber.mono_gamma h' (by linarith)

/-- The union of a family of matchings indexed by a colour set containing `c₀`. -/
theorem famUnionIdx_if_le_one {𝓗 : Hypergraph (Fin n)} {M : Set 𝓗} {C : Finset (Fin n)}
    {c₀ : Fin n} (hc₀ : c₀ ∈ C) :
    famUnionIdx (fun c : Fin n => if c ∈ C then M else (∅ : Set 𝓗)) = famOf M := by
  ext e
  rw [mem_famUnionIdx]
  constructor
  · rintro ⟨c, hc⟩
    by_cases hcC : c ∈ C
    · rwa [if_pos hcC] at hc
    · rw [if_neg hcC, mem_famOf] at hc
      obtain ⟨e', he', -⟩ := hc
      exact absurd he' (by simp)
  · intro he
    rw [mem_famOf] at he
    obtain ⟨e', he', hfe⟩ := he
    refine ⟨c₀, ?_⟩
    rw [if_pos hc₀, mem_famOf]
    exact ⟨e', he', hfe⟩

/-- The `⋃` of the defect sets of a family indexed by a subsingleton colour set
has at most five elements. -/
theorem ncard_biUnion_defect_le_five {𝓗 : Hypergraph (Fin n)} {C : Finset (Fin n)}
    (hcard : C.card ≤ 1) {Mdiff : Fin n → Set 𝓗}
    (hsmall : ∀ c ∈ C, (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c)).ncard ≤ 5) :
    (⋃ c ∈ (C : Set (Fin n)), (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c))).ncard ≤ 5 := by
  classical
  rcases C.eq_empty_or_nonempty with h | ⟨c₀, hc₀⟩
  · simp [h]
  · have hC : C = {c₀} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hc₀, fun b hb => Finset.card_le_one.mp hcard b hb c₀ hc₀⟩
    have hset : (⋃ c ∈ (C : Set (Fin n)), (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c))) =
        (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c₀)) := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_sdiff]
      constructor
      · rintro ⟨c, hcC, hx⟩
        rw [hC, Finset.mem_coe, Finset.mem_singleton] at hcC
        rwa [hcC] at hx
      · intro hx
        exact ⟨c₀, by rw [hC, Finset.mem_coe]; exact Finset.mem_singleton_self c₀, hx⟩
    rw [hset]
    exact hsmall c₀ hc₀

/-! ## Step 4 -/

/-- **§12, Step 4 (`step:diff`).**  Applying Lemma 7.12 to the (at most one)
difficult colour of `C_diff` either colours `𝓗` with `n` colours, or produces
the family `𝓜_diff = {M_c}` of D1 and the sets `R₁`, `S₁` of `(def:r1s1)`,
together with `(eq:R1abs)` and `(eq:boundS1)`. -/
theorem s12_step4 {n : ℕ} {𝓗 : Hypergraph (Fin n)} {r₁ r₀ σ γ₁ β γ ρ ρ_abs ξ ε : ℝ}
    (hlin : 𝓗.IsLinear) (hno : ∀ f ∈ 𝓗, 2 ≤ f.ncard) (hm : DiffMargins n β)
    {φ : (medLarge 𝓗 r₁).Coloring (Fin n)} {U : Set (Fin n)} {S : Set (Fin n)}
    {Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal : Finset (Fin n)}
    (hS12 : IsS12Colours n 𝓗 r₁ φ U r₀ β γ ρ Cmed Cdiff Chuge Clarge Cmain Cbuff Cfinal)
    (hA : IsTypeA σ γ₁ β r₁ r₀ 𝓗 φ)
    {R_abs : Hypergraph (Fin n)} {𝓥 : Set (Set (Fin n))}
    (hRabs : IsAbsorber (incidentTwo 𝓗 U) R_abs 𝓥 ρ_abs (10 * ξ) ξ)
    (hξγ : 10 * ξ + 1 / (n : ℝ) ≤ 3 * γ / 2) (hn : 1 ≤ n) :
    𝓗.chromaticIndex ≤ n ∨
      ∃ (Mdiff : Fin n → Set 𝓗) (R₁ : Hypergraph (Fin n)) (S₁ : Set (Fin n)),
        (∀ c ∉ Cdiff, Mdiff c = ∅) ∧
        (∀ c ∈ Cdiff, subFam (φ.colorClass c) ⊆ Mdiff c) ∧
        (∀ c ∈ Cdiff, ∀ e ∈ Mdiff c, e ∉ subFam (𝓖 := medLarge 𝓗 r₁) (φ.colorClass c) →
            (e : Set (Fin n)) ∈ 𝓗.pow2) ∧
        (∀ c, IsMatching 𝓗 (Mdiff c)) ∧
        (∀ c ∈ Cdiff, Covers (Mdiff c) (Vdeg 𝓗 (n - 1))) ∧
        (∀ c ∈ Cdiff, (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c)).ncard ≤ 5) ∧
        R₁ = R_abs \ famUnionIdx Mdiff ∧
        S₁ = S \ (⋃ c ∈ (Cdiff : Set (Fin n)),
          (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c))) ∧
        S₁ ⊆ S ∧
        IsAbsorber (incidentTwo 𝓗 U) R₁ 𝓥 ρ_abs (3 * γ / 2) ξ ∧
        (S.ncard : ℝ) - 5 ≤ (S₁.ncard : ℝ) := by
  classical
  have hγ0 : 10 * ξ ≤ 3 * γ / 2 := by
    have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    linarith
  by_cases hCempty : Cdiff = ∅
  · -- `C_diff = ∅`: nothing is deleted
    have hfam : famUnionIdx (fun _ : Fin n => (∅ : Set 𝓗)) = ∅ := by
      ext e
      rw [mem_famUnionIdx]
      constructor
      · rintro ⟨i, hi⟩
        rw [mem_famOf] at hi
        obtain ⟨e', he', -⟩ := hi
        exact he'
      · intro he
        exact absurd he (by simp)
    have hX : (⋃ c ∈ (Cdiff : Set (Fin n)),
        (Vdeg 𝓗 (n - 2) \ matchVert ((fun _ => (∅ : Set 𝓗)) c))) = ∅ := by
      rw [hCempty]
      simp
    refine Or.inr ⟨(fun _ => ∅), R_abs \ famUnionIdx (fun _ : Fin n => (∅ : Set 𝓗)),
      S \ (⋃ c ∈ (Cdiff : Set (Fin n)),
        (Vdeg 𝓗 (n - 2) \ matchVert ((fun _ => (∅ : Set 𝓗)) c))),
      ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
    · intro c hc; rfl
    · intro c hc; rw [hCempty] at hc; exact absurd hc (Finset.notMem_empty c)
    · intro c hc; rw [hCempty] at hc; exact absurd hc (Finset.notMem_empty c)
    · intro c; exact isMatching_empty 𝓗
    · intro c hc; rw [hCempty] at hc; exact absurd hc (Finset.notMem_empty c)
    · intro c hc; rw [hCempty] at hc; exact absurd hc (Finset.notMem_empty c)
    · exact Set.sdiff_subset
    · rw [hfam, Set.sdiff_empty]
      exact IsAbsorber.mono_gamma hRabs hγ0
    · rw [hX, Set.sdiff_empty]
      linarith
  · -- `C_diff = {c₀}`
    obtain ⟨c₀, hc₀⟩ := Finset.nonempty_iff_ne_empty.mpr hCempty
    have hcard : Cdiff.card ≤ 1 := hS12.hCdiff_card
    have hCiff : Cdiff = {c₀} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hc₀, fun b hb => Finset.card_le_one.mp hcard b hb c₀ hc₀⟩
    obtain ⟨C₁, Cmed', huse, hC₁, hC₁s, hCmedsz, hmed, hCmedvert, hsing, hlast⟩ := hA
    have hc₀huge : c₀ ∈ φ.hugeColourSet β := hS12.hCdiff_sub hc₀
    obtain ⟨e₀, he₀⟩ := hsing c₀ (Hypergraph.Coloring.mem_hugeColourSet.mp hc₀huge)
    obtain ⟨e', he', hhuge'⟩ := Hypergraph.Coloring.mem_hugeColourSet.mp hc₀huge
    rw [he₀, Set.mem_singleton_iff] at he'
    have hv : (e' : Set (Fin n)) = (e₀ : Set (Fin n)) := congrArg Subtype.val he'
    have hhn : β * (n : ℝ) / 4 ≤ (((e₀ : Set (Fin n))).ncard : ℝ) := by
      rw [← hv]
      simpa only [edgeHuge, edgeSize_eq_ncard] using hhuge'
    rcases difficult_edge_absorption (𝓗 := 𝓗) (e := (e₀ : Set (Fin n))) hm hlin hno
        e₀.2.1 hhn with ⟨M', hsub, hmat, hpow, hcov, hsmall⟩ | hchrom
    · set Mdiff : Fin n → Set 𝓗 := fun c => if c ∈ Cdiff then M' else ∅ with hMdiff
      have hsing' : ∀ c ∈ Cdiff, subFam (φ.colorClass c) =
          {(⟨(e₀ : Set (Fin n)), (medLarge_subset 𝓗 r₁) e₀.2⟩ : 𝓗)} := by
        intro c hc
        have hc' : c = c₀ := by
          rw [hCiff] at hc
          rwa [Finset.mem_singleton] at hc
        subst hc'
        rw [he₀]
        exact subFam_singleton (medLarge_subset 𝓗 r₁)
      have hv' : (⟨(e₀ : Set (Fin n)), (medLarge_subset 𝓗 r₁) e₀.2⟩ : 𝓗) =
          ⟨(e₀ : Set (Fin n)), e₀.2.1⟩ := rfl
      refine Or.inr ⟨Mdiff, R_abs \ famUnionIdx Mdiff,
        S \ (⋃ c ∈ (Cdiff : Set (Fin n)),
          (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c))),
        ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
      · intro c hc
        rw [hMdiff]
        simp only [hc, if_false]
      · intro c hc
        rw [hMdiff]
        simp only [hc, ↓reduceIte]
        rw [hsing' c hc, hv']
        intro e he
        rw [Set.mem_singleton_iff] at he
        rw [he]
        exact hsub (Set.mem_singleton _)
      · intro c hc e he hne
        rw [hMdiff] at he
        simp only [hc, ↓reduceIte] at he
        have hne' : e ≠ ⟨(e₀ : Set (Fin n)), e₀.2.1⟩ := by
          intro heq
          apply hne
          rw [hsing' c hc, hv', heq]
          exact Set.mem_singleton _
        exact hpow e he hne'
      · intro c
        rw [hMdiff]
        by_cases hc : c ∈ Cdiff
        · simp only [hc, ↓reduceIte]; exact hmat
        · simp only [hc, if_false]; exact isMatching_empty 𝓗
      · intro c hc
        rw [hMdiff]
        simp only [hc, ↓reduceIte]
        exact hcov
      · intro c hc
        rw [hMdiff]
        simp only [hc, ↓reduceIte]
        exact hsmall
      · exact Set.sdiff_subset
      · have hfam : famUnionIdx Mdiff = famOf M' := by
          rw [hMdiff]
          exact famUnionIdx_if_le_one hc₀
        rw [hfam]
        exact IsAbsorber.delete_famOf hRabs hmat hξγ hn
      · set X : Set (Fin n) := ⋃ c ∈ (Cdiff : Set (Fin n)),
          (Vdeg 𝓗 (n - 2) \ matchVert (Mdiff c)) with hXdef
        have hX : X.ncard ≤ 5 := by
          rw [hXdef]
          exact ncard_biUnion_defect_le_five hcard (fun c hc => by
            rw [hMdiff]; simp only [hc, ↓reduceIte]; exact hsmall)
        have hsplit : S = (S \ X) ∪ (S ∩ X) := by
          ext x
          simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union]
          tauto
        have h1 : S.ncard ≤ (S \ X).ncard + X.ncard := by
          have h := Set.ncard_union_le (S \ X) (S ∩ X)
          rw [← hsplit] at h
          exact le_trans h (Nat.add_le_add_left
            (Set.ncard_le_ncard Set.inter_subset_right (Set.toFinite _)) _)
        have h2 : (S.ncard : ℝ) - 5 ≤ ((S \ X).ncard : ℝ) := by
          have hh1 : ((S.ncard : ℝ)) ≤ ((S \ X).ncard : ℝ) + (X.ncard : ℝ) := by
            exact_mod_cast h1
          have hh2 : (X.ncard : ℝ) ≤ 5 := by exact_mod_cast hX
          linarith
        rw [hXdef] at h2 ⊢
        exact h2
    · exact Or.inl hchrom

end

end ErdosFaberLovaszConjecture
