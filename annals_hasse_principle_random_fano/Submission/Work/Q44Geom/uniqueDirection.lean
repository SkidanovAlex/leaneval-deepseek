import Mathlib
import Submission.Work.Q44Geom.pairs

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Q44Geom

/-- The range of the parametrisation `toV w` is the span of the vectors `w a`. -/
lemma toV_range (w : Fin 3 → Fin 5 → ℚ) :
    LinearMap.range (toV w) = Submodule.span ℚ (Set.range w) := by
  apply le_antisymm
  · rintro x ⟨p, rfl⟩
    rw [toV_apply]
    exact Submodule.sum_mem _
      (fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self a)))
  · rw [Submodule.span_le]
    rintro x ⟨a, rfl⟩
    refine ⟨Pi.single a (1 : ℚ), ?_⟩
    rw [toV_apply, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h

/-- `toV w` is injective as soon as the `w a` are linearly independent. -/
lemma toV_injective {w : Fin 3 → Fin 5 → ℚ} (hw : LinearIndependent ℚ w) :
    Function.Injective (toV w) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro p hp
  funext a
  have h0 : (toV w) p = 0 := LinearMap.mem_ker.mp hp
  rw [toV_apply] at h0
  exact Fintype.linearIndependent_iff.mp hw p h0 a

theorem uniqueDirection (b₁ b₂ : Fin 5 → ℚ) (w : Fin 3 → Fin 5 → ℚ)
    (hb : LinearIndependent ℚ (Fin.append w ![b₁, b₂]))
    (hsp : Submodule.span ℚ (Set.range (Fin.append w ![b₁, b₂])) = ⊤)
    (P : Submodule ℚ (Fin 5 → ℚ)) (hb1 : b₁ ∈ P) (hb2 : b₂ ∈ P)
    (hr : Module.finrank ℚ P = 3) :
    ∃! L : Submodule ℚ (Fin 3 → ℚ), Module.finrank ℚ L = 1 ∧
      P = Submodule.span ℚ ({b₁, b₂} ∪ Set.range (fun p : L => Work.Q44Geom.toV w (p : Fin 3 → ℚ))) := by
  classical
  have hw : LinearIndependent ℚ w := by
    have h := hb.comp (Fin.castAdd 2) (Fin.castAdd_injective 3 2)
    convert h using 1
    funext i
    simp
  set W : Submodule ℚ (Fin 5 → ℚ) := Submodule.span ℚ (Set.range w) with hW
  set ℓ : Submodule ℚ (Fin 5 → ℚ) := Submodule.span ℚ ({b₁, b₂} : Set (Fin 5 → ℚ)) with hℓ
  have hfinW : Module.finrank ℚ W = 3 := by
    rw [hW, finrank_span_eq_card hw, Fintype.card_fin]
  have hrange : LinearMap.range (toV w) = W := by
    rw [hW]; exact toV_range w
  have hinj : Function.Injective (toV w) := toV_injective hw
  have hsup : ℓ ⊔ W = ⊤ := by
    rw [← hsp]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rw [hℓ, Submodule.span_le]
        rintro x (rfl | rfl)
        · exact Submodule.subset_span ⟨Fin.natAdd 3 0, by rw [Fin.append_right]; simp⟩
        · exact Submodule.subset_span ⟨Fin.natAdd 3 1, by rw [Fin.append_right]; simp⟩
      · rw [hW, Submodule.span_le]
        rintro x ⟨j, rfl⟩
        exact Submodule.subset_span ⟨Fin.castAdd 2 j, by rw [Fin.append_left]⟩
    · rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      refine Fin.addCases (m := 3) (n := 2) (fun j => ?_) (fun k => ?_) i
      · rw [Fin.append_left]
        exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_range_self j))
      · rw [Fin.append_right]
        refine Submodule.mem_sup_left (Submodule.subset_span ?_)
        fin_cases k <;> simp
  have hℓP : ℓ ≤ P := by
    rw [hℓ, Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hb1
    · exact hb2
  have hPW : P ⊔ W = ⊤ := le_antisymm le_top (hsup ▸ sup_le_sup_right hℓP W)
  have hrank : Module.finrank ℚ ↥(P ⊓ W) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq P W
    rw [hPW, finrank_top, hr, hfinW, Module.finrank_fin_fun] at h
    omega
  have hP_eq : P = ℓ ⊔ (P ⊓ W) := by
    refine le_antisymm ?_ (sup_le hℓP inf_le_left)
    intro p hp
    have hp' : p ∈ W ⊔ ℓ := by rw [sup_comm, hsup]; exact Submodule.mem_top
    obtain ⟨y, hyW, z, hzℓ, hyz⟩ := Submodule.mem_sup.mp hp'
    refine Submodule.mem_sup.mpr ⟨z, hzℓ, y, ⟨?_, hyW⟩, ?_⟩
    · have hy : p - z = y := by rw [← hyz]; abel
      rw [← hy]
      exact P.sub_mem hp (hℓP hzℓ)
    · rw [add_comm]; exact hyz
  set L : Submodule ℚ (Fin 3 → ℚ) := Submodule.comap (toV w) (P ⊓ W) with hL
  have hmapL : Submodule.map (toV w) L = P ⊓ W := by
    rw [hL, Submodule.map_comap_eq, hrange, inf_eq_right.mpr inf_le_right]
  have hfinL : Module.finrank ℚ L = 1 := by
    have e := (Submodule.equivMapOfInjective (toV w) hinj L).finrank_eq
    rw [hmapL, hrank] at e
    exact e
  have hspanL : Submodule.span ℚ ({b₁, b₂} ∪ Set.range (fun p : L => (toV w) (p : Fin 3 → ℚ)))
      = ℓ ⊔ Submodule.map (toV w) L := by
    have h1 : (fun p : L => (toV w) (p : Fin 3 → ℚ))
        = (toV w) ∘ (Subtype.val : L → (Fin 3 → ℚ)) := rfl
    rw [h1, Set.range_comp, Subtype.range_coe]
    rw [Submodule.span_union, ← hℓ, ← Submodule.map_coe, Submodule.span_eq]
  have hPeq : P = Submodule.span ℚ ({b₁, b₂} ∪ Set.range (fun p : L => (toV w) (p : Fin 3 → ℚ))) := by
    rw [hspanL, hmapL]; exact hP_eq
  refine ⟨L, ⟨hfinL, hPeq⟩, ?_⟩
  rintro L' ⟨hfinL', hPeq'⟩
  have hspanL' : Submodule.span ℚ ({b₁, b₂} ∪ Set.range (fun p : L' => (toV w) (p : Fin 3 → ℚ)))
      = ℓ ⊔ Submodule.map (toV w) L' := by
    have h1 : (fun p : L' => (toV w) (p : Fin 3 → ℚ))
        = (toV w) ∘ (Subtype.val : L' → (Fin 3 → ℚ)) := rfl
    rw [h1, Set.range_comp, Subtype.range_coe]
    rw [Submodule.span_union, ← hℓ, ← Submodule.map_coe, Submodule.span_eq]
  have hmapL'_le : Submodule.map (toV w) L' ≤ P ⊓ W := by
    refine le_inf ?_ ?_
    · rw [hPeq', hspanL']
      exact le_sup_right
    · exact le_trans LinearMap.map_le_range hrange.le
  have hmapL'_fin : Module.finrank ℚ ↥(Submodule.map (toV w) L') = 1 := by
    have e := (Submodule.equivMapOfInjective (toV w) hinj L').finrank_eq
    rw [hfinL'] at e
    exact e.symm
  have hmapL' : Submodule.map (toV w) L' = P ⊓ W :=
    Submodule.eq_of_le_of_finrank_eq hmapL'_le (by rw [hmapL'_fin, hrank])
  have hle : L' ≤ L := by
    have h := Submodule.map_le_iff_le_comap.mp hmapL'.le
    rw [← hL] at h
    exact h
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinL', hfinL])

end Work.Q44Geom
