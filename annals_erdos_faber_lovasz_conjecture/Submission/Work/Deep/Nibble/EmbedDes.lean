import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.EmbedAux
import Submission.Work.Deep.Nibble.exists_linear_regular_uniform

/-!
# The designs glued at the clones of a vertex
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {N r : ℕ} {𝓗 : MultiHypergraph N}

/-- The bridge between `hypergraphDegree` and the `ncard` of the set of edges
through a vertex. -/
theorem hypergraphDegree_eq_ncard {n : ℕ} (𝓗 : Set (Set (Fin n))) (v : Fin n) :
    hypergraphDegree 𝓗 v = ({e ∈ 𝓗 | v ∈ e} : Set (Set (Fin n))).ncard := by
  rw [hypergraphDegree, ← Nat.card_coe_set_eq]
  refine Nat.card_congr (Equiv.ofBijective
    (fun e : {e : 𝓗 // v ∈ (e : Set (Fin n))} => (⟨(e.1 : Set (Fin n)), e.1.2, e.2⟩ :
      {e : Set (Fin n) // e ∈ 𝓗 ∧ v ∈ e})) ⟨?_, ?_⟩)
  · intro a b h
    have h1 : (a.1 : Set (Fin n)) = b.1 := congrArg (fun x : {e : Set (Fin n) // e ∈ 𝓗 ∧ v ∈ e} =>
      (x.1 : Set (Fin n))) h
    exact Subtype.ext (Subtype.ext h1)
  · rintro ⟨e, he, hv⟩
    exact ⟨⟨⟨e, he⟩, hv⟩, Subtype.ext rfl⟩

/-- Membership in the image of a set under an equivalence. -/
theorem mem_image_equiv {α β : Type*} (e : α ≃ β) (F : Set α) (i : β) :
    i ∈ e '' F ↔ e.symm i ∈ F := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [Equiv.symm_apply_apply]
  · intro hi
    exact ⟨e.symm i, hi, e.apply_symm_apply i⟩

/-- The defining properties of the chosen design `designOn`. -/
theorem designOn_spec (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) :
    (∀ e ∈ designOn hr D C U u, edgeSize e = r) ∧
      (designOn hr D C U u).Pairwise (fun e₁ e₂ => (e₁ ∩ e₂).Subsingleton) ∧
      (∀ v : Fin (r * designPrime hr D C U), hypergraphDegree (designOn hr D C U u) v
        = dprime D C U u) := by
  exact Classical.choose_spec (exists_linear_regular_uniform r (designPrime hr D C U)
    (dprime D C U u) (by omega) (designPrime_prime hr D C U) (le_of_lt (r_lt_designPrime hr D C U))
    (le_of_lt (lt_of_le_of_lt (dprime_le_dmax D C U u) (dmax_lt_designPrime hr D C U))))

theorem des_ncard (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) :
    ∀ E ∈ des hr D C U u, E.ncard = r := by
  intro E hE
  rw [des] at hE
  split_ifs at hE with h
  · simp at hE
  · obtain ⟨F, hF, rfl⟩ := hE
    rw [Set.ncard_image_of_injective F (finCongr _).injective, ← edgeSize_eq_ncard]
    exact (designOn_spec hr D C U u).1 F hF

theorem des_linear (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) :
    ∀ ⦃E⦄, E ∈ des hr D C U u → ∀ ⦃E'⦄, E' ∈ des hr D C U u → E ≠ E' →
      (E ∩ E').Subsingleton := by
  intro E hE E' hE' hne
  rw [des] at hE hE'
  split_ifs at hE hE' with h
  · simp at hE
  · obtain ⟨F, hF, rfl⟩ := hE
    obtain ⟨F', hF', rfl⟩ := hE'
    have hFF : F ≠ F' := fun hh => hne (by rw [hh])
    rw [← Set.image_inter (finCongr _).injective]
    exact ((designOn_spec hr D C U u).2.1 hF hF' hFF).image _

theorem des_deg (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) (i : Fin (T hr D C U)) :
    ({E ∈ des hr D C U u | i ∈ E} : Set (Set (Fin (T hr D C U)))).ncard
      = dprime D C U u := by
  rw [des]
  split_ifs with h
  · rw [(dmax_eq_zero_iff D C U).mp h u]
    simp
  · have hset : ({E ∈ Set.image (fun E : Set (Fin (r * designPrime hr D C U)) =>
          (finCongr (T_eq_of_ne hr D C U h).symm) '' E) (designOn hr D C U u) | i ∈ E}
        : Set (Set (Fin (T hr D C U))))
        = (fun E : Set (Fin (r * designPrime hr D C U)) =>
            (finCongr (T_eq_of_ne hr D C U h).symm) '' E) ''
          {F ∈ designOn hr D C U u | (finCongr (T_eq_of_ne hr D C U h).symm).symm i ∈ F} := by
      ext E; constructor
      · rintro ⟨⟨F, hF, rfl⟩, hiF⟩
        exact ⟨F, ⟨hF, (mem_image_equiv _ F i).mp hiF⟩, rfl⟩
      · rintro ⟨F, ⟨hF, hiF⟩, rfl⟩
        exact ⟨⟨F, hF, rfl⟩, (mem_image_equiv _ F i).mpr hiF⟩
    rw [hset, Set.ncard_image_of_injective _ (Set.image_injective.mpr (finCongr _).injective),
      ← hypergraphDegree_eq_ncard]
    exact (designOn_spec hr D C U u).2.2 _

theorem des_empty_of_dprime_zero (hr : 3 ≤ r) (D C : ℝ) (U : UnifData N r 𝓗)
    (u : Vstar 𝓗 r U.M) (h0 : dprime D C U u = 0) : des hr D C U u = ∅ := by
  rw [des]
  split_ifs with h
  · rfl
  · have hS : ¬ (designOn hr D C U u).Nonempty := by
      rintro ⟨F, hF⟩
      have hdeg := (designOn_spec hr D C U u).2.2
      have h2 : edgeSize (F : Set (Fin (r * designPrime hr D C U))) = r :=
        (designOn_spec hr D C U u).1 F hF
      rw [edgeSize_eq_ncard] at h2
      have hFne : F.Nonempty := by
        by_contra hcon
        rw [Set.not_nonempty_iff_eq_empty] at hcon
        rw [hcon] at h2
        simp at h2
        omega
      obtain ⟨y, hy⟩ := hFne
      have h1 : 1 ≤ hypergraphDegree (designOn hr D C U u) y := by
        rw [hypergraphDegree_eq_ncard]
        have hsub : ({F} : Set (Set (Fin (r * designPrime hr D C U)))) ⊆
            {e ∈ designOn hr D C U u | y ∈ e} := by
          intro e he
          rw [Set.mem_singleton_iff] at he
          subst he
          exact ⟨hF, hy⟩
        have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
        simpa using h3
      rw [hdeg y, h0] at h1
      omega
    rw [Set.not_nonempty_iff_eq_empty.mp hS, Set.image_empty]

end

end Work.Deep.Nibble
