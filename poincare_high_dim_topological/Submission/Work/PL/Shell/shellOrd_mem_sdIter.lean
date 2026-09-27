import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic
import Submission.Work.PL.Shell.sd_iter_shelling_strong
import Submission.Work.PL.Subdiv.SdBasic
import Submission.Work.PL.Shell.cover_bary
import Submission.Work.PL.Shell.subList_spec
import Submission.Work.PL.Shell.flagEnum_mem

/-!
# `Work.PL.Shell.shellOrd_mem_sdIter`

Bridge between the abstract shelling order `shellOrd r Δ τ₁` of `Submission.Work.PL.Shell`
and the complex-level iterated barycentric subdivision `Work.PL.Subdiv.sdIter r K hK`:
if `Δ` is a face of `K`, every simplex of the shelling order of `Δ` is a face of the
`r`-fold subdivision of `K`.
-/

namespace Work.PL.Shell

noncomputable section

variable {N : ℕ}

/-- The prefix sets `prefAt l k` of a list are nested (they are the prefixes of `l`). -/
private lemma prefAt_subset_of_le (l : List (PL.E N)) {k k' : ℕ} (h : k ≤ k') :
    prefAt l k ⊆ prefAt l k' := by
  intro x hx
  simp only [prefAt, List.mem_toFinset] at hx ⊢
  have h1 : List.Sublist ((List.take (k' + 1) l).take (k + 1)) (List.take (k' + 1) l) :=
    List.take_sublist (k + 1) (List.take (k' + 1) l)
  rw [List.take_take, Nat.min_eq_left (Nat.succ_le_succ h)] at h1
  exact h1.subset hx

/-- `prefixes l` is a chain: any two prefix sets are comparable by inclusion. -/
private lemma soms_prefixes_chain (l : List (PL.E N)) :
    ∀ A ∈ prefixes l, ∀ B ∈ prefixes l, A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  obtain ⟨k, -, rfl⟩ := mem_prefixes_iff.mp hA
  obtain ⟨k', -, rfl⟩ := mem_prefixes_iff.mp hB
  rcases le_total k k' with h | h
  · exact Or.inl (prefAt_subset_of_le l h)
  · exact Or.inr (prefAt_subset_of_le l h)

/-- **The one-step bridge.**  If `σ` is a face of the complex `L`, then every simplex of
the barycentric subdivision data `sd1Data σ T` is a face of `sd L`. -/
theorem sd1Data_mem_sd (L : PL.Cx N) (σ T : Finset (PL.E N)) (hσ : σ ∈ L.faces) :
    ∀ p ∈ Work.PL.Shell.sd1Data σ T, p.1 ∈ (Work.PL.Subdiv.sd L).faces := by
  intro p hp
  simp only [Work.PL.Shell.sd1Data, List.mem_map] at hp
  obtain ⟨l, hl, rfl⟩ := hp
  have hlperm : l.Perm (subList σ T) := flagEnum_mem.mp hl
  have hto : l.toFinset = σ := by
    rw [List.toFinset_eq_of_perm _ _ hlperm, (subList_spec (σ := σ) (T := T)).2.1]
  have hσne : σ.Nonempty := L.nonempty_of_mem_faces hσ
  have hlne : l ≠ [] := by
    intro hnil
    have : σ = ∅ := by rw [← hto, hnil]; simp
    exact hσne.ne_empty this
  show (prefixes l).image Work.PL.Subdiv.bary ∈ (Work.PL.Subdiv.sd L).faces
  refine Work.PL.Subdiv.mem_sd_faces_of_chain ?_ ?_
  · refine ⟨?_, ?_⟩
    · intro ρ hρ
      refine L.down_closed hσ ?_ (prefixes_nonempty hρ)
      intro x hx
      have h := prefixes_subset_toFinset hρ hx
      rwa [hto] at h
    · exact soms_prefixes_chain l
  · exact ⟨l.toFinset, top_mem_prefixes l hlne⟩

/-- **The iterated bridge.**  If `Δ` is a face of `K`, then the first components of
`sdIter r Δ τ₁` are faces of the `r`-fold subdivision of `K`. -/
theorem sdIter_mem_sd_faces (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite)
    (Δ τ₁ : Finset (PL.E N)) (hΔK : Δ ∈ K.faces) :
    ∀ p ∈ Work.PL.Shell.sdIter r Δ τ₁, p.1 ∈ (Work.PL.Subdiv.sdIter r K hK).faces := by
  induction r with
  | zero =>
      intro p hp
      rw [show Work.PL.Shell.sdIter 0 Δ τ₁ = [(Δ, τ₁)] from rfl] at hp
      rw [Work.PL.Subdiv.sdIter_zero]
      simp only [List.mem_singleton] at hp
      subst hp
      exact hΔK
  | succ r ih =>
      intro p hp
      rw [show Work.PL.Shell.sdIter (r + 1) Δ τ₁ =
        (Work.PL.Shell.sdIter r Δ τ₁).flatMap
          (fun q => Work.PL.Shell.sd1Data q.1 q.2) from rfl] at hp
      rw [Work.PL.Subdiv.sdIter_succ]
      simp only [List.mem_flatMap] at hp
      obtain ⟨q, hq, hpq⟩ := hp
      exact sd1Data_mem_sd (Work.PL.Subdiv.sdIter r K hK) q.1 q.2 (ih q hq) p hpq

theorem shellOrd_mem_sdIter {N : ℕ} (r : ℕ) (K : PL.Cx N) (hK : K.faces.Finite)
    (Δ τ₁ : Finset (PL.E N)) (hΔK : Δ ∈ K.faces) (h₁ : τ₁.Nonempty) (h₂ : τ₁ ⊂ Δ) :
    ∀ τ ∈ Work.PL.Shell.shellOrd r Δ τ₁, τ ∈ (Work.PL.Subdiv.sdIter r K hK).faces := by
  intro τ hτ
  rw [Work.PL.Shell.shellOrd, List.mem_map] at hτ
  obtain ⟨p, hp, rfl⟩ := hτ
  exact sdIter_mem_sd_faces r K hK Δ τ₁ hΔK p hp

end

end Work.PL.Shell
