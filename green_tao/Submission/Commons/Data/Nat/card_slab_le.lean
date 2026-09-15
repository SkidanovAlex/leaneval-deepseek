import Mathlib
import Submission.Commons.Data.Fintype.card_subtype_ne

namespace Commons.Data.Nat

/-- Fiber bound: for a nonzero integer linear form `∑ k, L k * u k` on the box
`Fin t → Fin Q`, every level set has at most `Q ^ (t - 1)` elements. -/
theorem fiber_card_le {t : ℕ} (L : Fin t → ℤ) (j : Fin t) (hj : L j ≠ 0) (Q : ℕ) (n : ℤ) :
    ((Finset.univ : Finset (Fin t → Fin Q)).filter
      (fun u => ∑ k, L k * ((u k).val : ℤ) = n)).card ≤ Q ^ (t - 1) := by
  classical
  set r : (Fin t → Fin Q) → ({i : Fin t // i ≠ j} → Fin Q) := fun u i => u i.1 with hr
  have hinj : Set.InjOn r
      ↑((Finset.univ : Finset (Fin t → Fin Q)).filter
          (fun u => ∑ k, L k * ((u k).val : ℤ) = n)) := by
    intro u hu v hv huv
    have hu' : (∑ k, L k * ((u k).val : ℤ)) = n :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    have hv' : (∑ k, L k * ((v k).val : ℤ)) = n :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have hru : ∀ i : {i : Fin t // i ≠ j}, u i.1 = v i.1 := by
      intro i
      have h := congrFun huv i
      simpa only [hr] using h
    have hφ : (∑ k, L k * ((u k).val : ℤ)) = (∑ k, L k * ((v k).val : ℤ)) := by rw [hu', hv']
    funext k
    by_cases hk : k = j
    · have er : (∑ x ∈ Finset.univ.erase j, L x * ((u x).val : ℤ))
              = (∑ x ∈ Finset.univ.erase j, L x * ((v x).val : ℤ)) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxj : x ≠ j := Finset.ne_of_mem_erase hx
        have h : u x = v x := hru ⟨x, hxj⟩
        rw [h]
      have h1 := Finset.add_sum_erase (Finset.univ)
        (fun x => L x * ((u x).val : ℤ)) (Finset.mem_univ j)
      have h2 := Finset.add_sum_erase (Finset.univ)
        (fun x => L x * ((v x).val : ℤ)) (Finset.mem_univ j)
      rw [← h1, ← h2, er] at hφ
      have hcancel : L j * ((u j).val : ℤ) = L j * ((v j).val : ℤ) := add_right_cancel hφ
      have hval : (u j).val = (v j).val := Int.ofNat_inj.mp (mul_left_cancel₀ hj hcancel)
      rw [hk]
      exact Fin.ext hval
    · exact hru ⟨k, hk⟩
  calc ((Finset.univ : Finset (Fin t → Fin Q)).filter
          (fun u => ∑ k, L k * ((u k).val : ℤ) = n)).card
      = (((Finset.univ : Finset (Fin t → Fin Q)).filter
          (fun u => ∑ k, L k * ((u k).val : ℤ) = n)).image r).card :=
          (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.univ : Finset ({i : Fin t // i ≠ j} → Fin Q)).card :=
          Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card ({i : Fin t // i ≠ j} → Fin Q) := Finset.card_univ
    _ = Q ^ (t - 1) := by
          rw [Fintype.card_fun, Fintype.card_fin,
              Commons.Data.Fintype.card_subtype_ne, Fintype.card_fin]

/-- Slab bound: the number of `u : Fin t → Fin Q` with `|∑ j, L j * u j - c| ≤ K`
is at most `Q ^ (t - 1) * (2 * K + 1)`, for any nonzero integer coefficient vector `L`. -/
theorem card_slab_le {t : ℕ} (L : Fin t → ℤ) (hL : ∃ j, L j ≠ 0) (Q : ℕ) (c : ℤ) (K : ℕ) :
    ((Finset.univ : Finset (Fin t → Fin Q)).filter
        (fun u => |(∑ j, L j * ((u j).val : ℤ)) - c| ≤ (K : ℤ))).card
      ≤ Q ^ (t - 1) * (2 * K + 1) := by
  classical
  obtain ⟨j, hj⟩ := hL
  set T : Finset (Fin t → Fin Q) := (Finset.univ : Finset (Fin t → Fin Q)).filter
      (fun u => |(∑ j, L j * ((u j).val : ℤ)) - c| ≤ (K : ℤ)) with hT
  have hfib : ∀ b ∈ Finset.image (fun u => ∑ k, L k * ((u k).val : ℤ)) T,
      {a ∈ T | (∑ k, L k * ((a k).val : ℤ)) = b}.card ≤ Q ^ (t - 1) := by
    intro b hb
    refine le_trans (Finset.card_le_card ?_) (fiber_card_le L j hj Q b)
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ a, ha.2⟩
  have himg : (Finset.image (fun u => ∑ k, L k * ((u k).val : ℤ)) T).card ≤ 2 * K + 1 := by
    have hsub : Finset.image (fun u => ∑ k, L k * ((u k).val : ℤ)) T
        ⊆ Finset.Icc (c - (K : ℤ)) (c + (K : ℤ)) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨a, haT, rfl⟩ := hx
      rw [Finset.mem_Icc]
      rw [hT] at haT
      have haT' : |(∑ k, L k * ((a k).val : ℤ)) - c| ≤ (K : ℤ) :=
        (Finset.mem_filter.mp haT).2
      have habs := abs_le.mp haT'

      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    calc (Finset.image (fun u => ∑ k, L k * ((u k).val : ℤ)) T).card
        ≤ (Finset.Icc (c - (K : ℤ)) (c + (K : ℤ))).card := Finset.card_le_card hsub
      _ = 2 * K + 1 := by
            rw [Int.card_Icc]
            have hz : c + (K : ℤ) + 1 - (c - (K : ℤ)) = ((2 * K + 1 : ℕ) : ℤ) := by
              push_cast; ring
            rw [hz, Int.toNat_natCast]
  refine le_trans (Finset.card_le_mul_card_image
    (f := fun u => ∑ k, L k * ((u k).val : ℤ)) T (Q ^ (t - 1)) hfib) ?_
  exact Nat.mul_le_mul_left _ himg

end Commons.Data.Nat
