import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs

/-!
# The `R`-edges through a vertex used by an absorbed batch

Every `R`-edge through `w` lying in the absorbed family `⋃ i, Nabs i` is charged
to a colour `i` whose *input* matching `Nin i` does **not** cover `w`: an `R`-edge
must come from the absorption, which is vertex-disjoint from the input matching.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

theorem ncard_Redges_le_missing {n : ℕ} {ι : Type*} [Fintype ι]
    {𝓜 : ErdosFaberLovaszConjecture.MultiHypergraph n}
    (R : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    (Nin : ι → Set (Set (Fin n))) (Nabs : ι → Set (Set (Fin n))) (w : Fin n)
    (hmat : ∀ i, ErdosFaberLovaszConjecture.MultiHypergraph.IsMatching 𝓜 (Nabs i))
    (hsub : ∀ i, Nin i ⊆ Nabs i)
    (hNout : ∀ i, ∀ e ∈ Nin i, e ∉ R) :
    ((({e ∈ R | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i, Nabs i)).ncard : ℝ) ≤
      (({i : ι | w ∉ ErdosFaberLovaszConjecture.famVert (Nin i)} : Set ι).ncard : ℝ) := by
  classical
  set S : Set (Set (Fin n)) := ({e ∈ R | w ∈ e} : Set (Set (Fin n))) ∩ (⋃ i, Nabs i) with hS
  set T : Set ι := {i : ι | w ∉ famVert (Nin i)} with hT
  have hchoice : ∀ (e : Set (Fin n)) (he : e ∈ S), ∃ i, e ∈ Nabs i :=
    fun e he => Set.mem_iUnion.mp he.2
  choose f hf using hchoice
  have hfT : ∀ (e : Set (Fin n)) (he : e ∈ S), f e he ∈ T := by
    intro e he
    obtain ⟨heR, hew⟩ := he.1
    intro hw
    rw [mem_famVert] at hw
    obtain ⟨e', he'nin, he'w⟩ := hw
    have he'abs : e' ∈ Nabs (f e he) := hsub _ he'nin
    by_cases h : e = e'
    · exact hNout (f e he) e' he'nin (by rw [← h]; exact heR)
    · exact ((hmat (f e he)).2 (hf e he) he'abs h).notMem_of_mem_left hew he'w
  have hinjf : ∀ (e₁ : Set (Fin n)) (h₁ : e₁ ∈ S) (e₂ : Set (Fin n)) (h₂ : e₂ ∈ S),
      f e₁ h₁ = f e₂ h₂ → e₁ = e₂ := by
    intro e₁ h₁ e₂ h₂ hfe
    by_contra hne
    obtain ⟨-, hw₁⟩ := h₁.1
    obtain ⟨-, hw₂⟩ := h₂.1
    have h1 := hf e₁ h₁
    have h2 := hf e₂ h₂
    rw [hfe] at h1
    exact ((hmat (f e₂ h₂)).2 h1 h2 hne).notMem_of_mem_left hw₁ hw₂
  rcases isEmpty_or_nonempty ι with hemp | hne
  · have hiu : (⋃ i, Nabs i) = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun e he => by
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
        exact isEmptyElim i
    have h0 : S.ncard = 0 := by rw [hS, hiu, Set.inter_empty, Set.ncard_empty]
    simp [h0]
  · obtain ⟨i₀⟩ := hne
    have hfTg : ∀ a ∈ S, (if h : a ∈ S then f a h else i₀) ∈ T := by
      intro a ha
      rw [dif_pos ha]
      exact hfT a ha
    have hinjg : Set.InjOn (fun a => if h : a ∈ S then f a h else i₀) S := by
      intro a₁ ha₁ a₂ ha₂ hg
      dsimp only at hg
      rw [dif_pos ha₁, dif_pos ha₂] at hg
      exact hinjf a₁ ha₁ a₂ ha₂ hg
    exact mod_cast Set.ncard_le_ncard_of_injOn (fun a => if h : a ∈ S then f a h else i₀) hfTg hinjg

end Work.Deep.Nibble
