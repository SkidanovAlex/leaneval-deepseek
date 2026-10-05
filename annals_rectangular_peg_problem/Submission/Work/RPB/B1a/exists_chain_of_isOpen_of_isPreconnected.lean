import Mathlib
import Submission.Work.RPB.B1a.SegChain

namespace Work.RPB.B1a

open Set Filter
open scoped Topology

noncomputable section

/-! ## The reverse of a polygonal chain -/

/-- Reverse a polygonal chain: reverse the order of the segments and swap the endpoints of each
segment. -/
def chainRev : List (ℂ × ℂ) → List (ℂ × ℂ)
  | [] => []
  | s :: L => chainRev L ++ [(s.2, s.1)]

lemma chainRev_cons (s : ℂ × ℂ) (L : List (ℂ × ℂ)) :
    chainRev (s :: L) = chainRev L ++ [(s.2, s.1)] := rfl

/-! ## Concatenation and reversal preserve being a chain and lying in `U` -/

/-- Concatenation of two chains. -/
lemma IsChainFrom.append {p q r : ℂ} {L₁ L₂ : List (ℂ × ℂ)}
    (h₁ : IsChainFrom p q L₁) (h₂ : IsChainFrom q r L₂) :
    IsChainFrom p r (L₁ ++ L₂) := by
  induction L₁ generalizing p with
  | nil =>
    simp only [List.nil_append]
    have hpq : p = q := h₁
    rw [hpq]
    exact h₂
  | cons s _ ih =>
    have h₁' : s.1 = p ∧ IsChainFrom s.2 q _ := h₁
    obtain ⟨h1, h2⟩ := h₁'
    exact ⟨h1, ih h2⟩

lemma ChainIn.append {U : Set ℂ} {L₁ L₂ : List (ℂ × ℂ)}
    (h₁ : ChainIn U L₁) (h₂ : ChainIn U L₂) : ChainIn U (L₁ ++ L₂) := by
  intro s hs
  rw [List.mem_append] at hs
  rcases hs with hs | hs
  · exact h₁ s hs
  · exact h₂ s hs

lemma IsChainFrom.reverse {p q : ℂ} {L : List (ℂ × ℂ)} (h : IsChainFrom p q L) :
    IsChainFrom q p (chainRev L) := by
  induction L generalizing p with
  | nil =>
    have hpq : p = q := h
    exact hpq.symm
  | cons s _ ih =>
    have h' : s.1 = p ∧ IsChainFrom s.2 q _ := h
    obtain ⟨h1, h2⟩ := h'
    rw [chainRev_cons]
    exact IsChainFrom.append (ih h2) ⟨rfl, h1⟩

lemma ChainIn.reverse {U : Set ℂ} {L : List (ℂ × ℂ)} (h : ChainIn U L) :
    ChainIn U (chainRev L) := by
  induction L with
  | nil => simp [ChainIn, chainRev]
  | cons s _ ih =>
    intro t ht
    rw [chainRev_cons, List.mem_append] at ht
    rcases ht with ht | ht
    · exact ih (fun u hu => h u (List.mem_cons_of_mem s hu)) t ht
    · obtain rfl := List.mem_singleton.mp ht
      obtain ⟨h1, h2, h3⟩ := h s List.mem_cons_self
      exact ⟨h2, h1, by rwa [segment_symm]⟩

/-! ## The local step: near any point of an open set, the chain can be extended -/

/-- In an open set `U`, from a point `x ∈ U` one can reach every nearby point `y ∈ U` by a single
segment lying in `U`. -/
lemma eventually_exists_chain (U : Set ℂ) (hUo : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[U] x, ∃ L : List (ℂ × ℂ), IsChainFrom x y L ∧ ChainIn U L := by
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hUo) x hx
  refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
  refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
  intro y hy
  refine ⟨[(x, y)], by simp [IsChainFrom], ?_⟩
  intro s hs
  obtain rfl := List.mem_singleton.mp hs
  exact ⟨hx, hball hy,
    Subset.trans (Convex.segment_subset (convex_ball x ε) (Metric.mem_ball_self hε) hy) hball⟩

/-! ## The main result -/

theorem exists_chain_of_isOpen_of_isPreconnected (U : Set ℂ) (hUo : IsOpen U) (hUc : IsConnected U)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    ∃ L : List (ℂ × ℂ), IsChainFrom a b L ∧ ChainIn U L := by
  have htrans : ∀ x y z : ℂ, x ∈ U → y ∈ U → z ∈ U →
      (∃ L : List (ℂ × ℂ), IsChainFrom x y L ∧ ChainIn U L) →
      (∃ L : List (ℂ × ℂ), IsChainFrom y z L ∧ ChainIn U L) →
      (∃ L : List (ℂ × ℂ), IsChainFrom x z L ∧ ChainIn U L) := by
    rintro x y z - - - ⟨L₁, h1, h2⟩ ⟨L₃, h3, h4⟩
    exact ⟨L₁ ++ L₃, IsChainFrom.append h1 h3, ChainIn.append h2 h4⟩
  have hsym : ∀ x y : ℂ, x ∈ U → y ∈ U →
      (∃ L : List (ℂ × ℂ), IsChainFrom x y L ∧ ChainIn U L) →
      (∃ L : List (ℂ × ℂ), IsChainFrom y x L ∧ ChainIn U L) := by
    rintro x y - - ⟨L, h1, h2⟩
    exact ⟨chainRev L, IsChainFrom.reverse h1, ChainIn.reverse h2⟩
  exact hUc.isPreconnected.induction₂ _ (fun x hx => eventually_exists_chain U hUo hx)
    htrans hsym ha hb

end

end Work.RPB.B1a
