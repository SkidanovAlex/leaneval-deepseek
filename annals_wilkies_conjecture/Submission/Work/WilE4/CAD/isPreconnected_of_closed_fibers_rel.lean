/-
  WilE4 / CAD — preconnectedness of a *relative* closed family with preconnected, locally bounded
  fibres.

  Let `C ⊆ ℝ^k` be preconnected and let `D ⊆ ℝ^k × ℝ` be closed; put
  `X = {p | p.1 ∈ C} ∩ D` (so `X` need not be closed itself — only its position relative to
  `C × ℝ` and to the closed set `D` is used).  If every fibre `{t | (x,t) ∈ X}` over `x ∈ C` is
  nonempty and preconnected, and every fibre is bounded on a neighbourhood of every `x ∈ C`, then
  `X` is preconnected.

  The proof is the usual "closed map with connected fibres over a connected base" argument, in the
  relative form needed here:

  * for a closed `S` the projection `Prod.fst '' (X ∩ S)` is closed in the subspace `C`: a limit
    point `x ∈ C` of the projection can be lifted because the second coordinates stay in a fixed
    compact interval (`exists_snd_of_mem_closure_fst_rel`), and the lifted point lies in `D ∩ S`;
  * every fibre over `C` lies entirely in one of the two parts of any closed 2-cover of `X`
    (`isPreconnected_iff_subset_of_disjoint_closed` applied in the fibre).

  Then both parts project onto relatively closed, disjoint subsets of `C` covering `C`, so
  preconnectedness of `C` forces one of them to be empty, and the corresponding `X ∩ Tᵢ` is empty
  as well.
-/
import Mathlib
import Submission.Work.WilE4.CAD.isPreconnected_of_closed_fibers
import Submission.Work.WilE4.CAD.exists_snd_of_mem_closure_fst_rel

open Filter Topology
open scoped Topology

namespace Work.WilE4.CAD

theorem isPreconnected_of_closed_fibers_rel {k : ℕ} {C : Set (Fin k → ℝ)} (hC : IsPreconnected C)
    {X D : Set ((Fin k → ℝ) × ℝ)} (hD : IsClosed D)
    (hX : X = {p : (Fin k → ℝ) × ℝ | p.1 ∈ C} ∩ D)
    (hint : ∀ x ∈ C, IsPreconnected {t : ℝ | (x, t) ∈ X})
    (hne : ∀ x ∈ C, ∃ t : ℝ, (x, t) ∈ X)
    (hbd : ∀ x ∈ C, ∃ B : ℝ,
      Filter.Eventually (fun x' => ∀ t : ℝ, (x', t) ∈ X → |t| ≤ B) (nhds x)) :
    IsPreconnected X := by
  classical
  have hsub : ∀ p ∈ X, p.1 ∈ C := by
    intro p hp
    rw [hX] at hp
    exact hp.1
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro T₁ T₂ hT₁ hT₂ hcover hdisj
  -- Every fibre over `C` lies entirely in `T₁` or entirely in `T₂`: the two parts are closed and
  -- disjoint in the (preconnected, nonempty) fibre.
  have hfiber : ∀ x ∈ C,
      (∀ t, (x, t) ∈ X → (x, t) ∈ T₁) ∨ (∀ t, (x, t) ∈ X → (x, t) ∈ T₂) := by
    intro x hxC
    have h1 : IsClosed {t : ℝ | (x, t) ∈ T₁} :=
      hT₁.preimage (continuous_const.prodMk continuous_id)
    have h2 : IsClosed {t : ℝ | (x, t) ∈ T₂} :=
      hT₂.preimage (continuous_const.prodMk continuous_id)
    have hcov' : {t : ℝ | (x, t) ∈ X} ⊆ {t | (x, t) ∈ T₁} ∪ {t | (x, t) ∈ T₂} := by
      intro t ht; simpa using hcover ht
    have hdisj' : {t : ℝ | (x, t) ∈ X} ∩ ({t | (x, t) ∈ T₁} ∩ {t | (x, t) ∈ T₂}) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro t ⟨htX, ht1, ht2⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj) (x, t) ⟨htX, ht1, ht2⟩
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp (hint x hxC))
        {t : ℝ | (x, t) ∈ T₁} {t : ℝ | (x, t) ∈ T₂} h1 h2 hcov' hdisj' with h | h
    · exact Or.inl fun t ht => h ht
    · exact Or.inr fun t ht => h ht
  -- For closed `S`, the projection of `X ∩ S` is closed in the subspace `C`.
  have hkey : ∀ (S : Set ((Fin k → ℝ) × ℝ)), IsClosed S →
      C ∩ closure (Prod.fst '' (X ∩ S)) = Prod.fst '' (X ∩ S) := by
    intro S hS
    apply Set.Subset.antisymm
    · rintro x ⟨hxC, hxcl⟩
      obtain ⟨B, hB⟩ := hbd x hxC
      have hB' : ∀ᶠ x' in nhds x, ∀ t : ℝ, (x', t) ∈ X ∩ S → |t| ≤ B :=
        hB.mono (fun x' hx' t ht => hx' t ht.1)
      have hsubD : X ∩ S ⊆ D := by
        rw [hX]; exact Set.inter_subset_left.trans Set.inter_subset_right
      obtain ⟨t, ht⟩ :=
        exists_snd_of_mem_closure_fst_rel hD hS hsubD Set.inter_subset_right hB' hxcl
      refine ⟨(x, t), ⟨?_, ht.2⟩, rfl⟩
      rw [hX]
      exact ⟨hxC, ht.1⟩
    · rintro x ⟨p, hp, rfl⟩
      exact ⟨hsub p hp.1, subset_closure ⟨p, hp, rfl⟩⟩
  have hkey₁ := hkey T₁ hT₁
  have hkey₂ := hkey T₂ hT₂
  have hC₁sub : Prod.fst '' (X ∩ T₁) ⊆ C := by
    rintro x ⟨p, hp, rfl⟩; exact hsub p hp.1
  have hC₂sub : Prod.fst '' (X ∩ T₂) ⊆ C := by
    rintro x ⟨p, hp, rfl⟩; exact hsub p hp.1
  -- the two projections cover `C` ...
  have hcover12 : C ⊆ Prod.fst '' (X ∩ T₁) ∪ Prod.fst '' (X ∩ T₂) := by
    intro x hxC
    rcases hfiber x hxC with h | h
    · obtain ⟨t, ht⟩ := hne x hxC
      exact Or.inl ⟨(x, t), ⟨ht, h t ht⟩, rfl⟩
    · obtain ⟨t, ht⟩ := hne x hxC
      exact Or.inr ⟨(x, t), ⟨ht, h t ht⟩, rfl⟩
  -- ... and they are disjoint.
  have hdisj12 : C ∩ (Prod.fst '' (X ∩ T₁) ∩ Prod.fst '' (X ∩ T₂)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxC, ⟨p, hp, hp1⟩, ⟨q, hq, hq1⟩⟩
    have hpe : (x, p.2) = p := by rw [← hp1]
    have hqe : (x, q.2) = q := by rw [← hq1]
    rcases hfiber x hxC with h | h
    · refine (Set.eq_empty_iff_forall_notMem.mp hdisj) q ⟨hq.1, ?_, hq.2⟩
      have hmem : (x, q.2) ∈ X := by rw [hqe]; exact hq.1
      have hT : (x, q.2) ∈ T₁ := h q.2 hmem
      rwa [hqe] at hT
    · refine (Set.eq_empty_iff_forall_notMem.mp hdisj) p ⟨hp.1, hp.2, ?_⟩
      have hmem : (x, p.2) ∈ X := by rw [hpe]; exact hp.1
      have hT : (x, p.2) ∈ T₂ := h p.2 hmem
      rwa [hpe] at hT
  have hcov2 : C ⊆ closure (Prod.fst '' (X ∩ T₁)) ∪ closure (Prod.fst '' (X ∩ T₂)) := by
    intro x hx
    rcases hcover12 hx with h | h
    · exact Or.inl (subset_closure h)
    · exact Or.inr (subset_closure h)
  have hdisj2 :
      C ∩ (closure (Prod.fst '' (X ∩ T₁)) ∩ closure (Prod.fst '' (X ∩ T₂))) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxC, hx1, hx2⟩
    have e1 : x ∈ Prod.fst '' (X ∩ T₁) := by rw [← hkey₁]; exact ⟨hxC, hx1⟩
    have e2 : x ∈ Prod.fst '' (X ∩ T₂) := by rw [← hkey₂]; exact ⟨hxC, hx2⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj12) x ⟨hxC, e1, e2⟩
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hC)
      (closure (Prod.fst '' (X ∩ T₁))) (closure (Prod.fst '' (X ∩ T₂)))
      isClosed_closure isClosed_closure hcov2 hdisj2 with h | h
  · -- `C ⊆ closure (fst '' (X ∩ T₁))`, hence `X ∩ T₂ = ∅`
    have hC2empty : Prod.fst '' (X ∩ T₂) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx1 : x ∈ Prod.fst '' (X ∩ T₁) := by
        rw [← hkey₁]; exact ⟨hC₂sub hx, h (hC₂sub hx)⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj12) x ⟨hC₂sub hx, hx1, hx⟩
    have hBempty : X ∩ T₂ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      exact (Set.eq_empty_iff_forall_notMem.mp hC2empty) p.1 ⟨p, hp, rfl⟩
    left
    intro p hp
    rcases hcover hp with hh | hh
    · exact hh
    · exact absurd ⟨hp, hh⟩ (Set.eq_empty_iff_forall_notMem.mp hBempty p)
  · -- `C ⊆ closure (fst '' (X ∩ T₂))`, hence `X ∩ T₁ = ∅`
    have hC1empty : Prod.fst '' (X ∩ T₁) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hx1 : x ∈ Prod.fst '' (X ∩ T₂) := by
        rw [← hkey₂]; exact ⟨hC₁sub hx, h (hC₁sub hx)⟩
      exact (Set.eq_empty_iff_forall_notMem.mp hdisj12) x ⟨hC₁sub hx, hx, hx1⟩
    have hAempty : X ∩ T₁ = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro p hp
      exact (Set.eq_empty_iff_forall_notMem.mp hC1empty) p.1 ⟨p, hp, rfl⟩
    right
    intro p hp
    rcases hcover hp with hh | hh
    · exact absurd ⟨hp, hh⟩ (Set.eq_empty_iff_forall_notMem.mp hAempty p)
    · exact hh

end Work.WilE4.CAD
