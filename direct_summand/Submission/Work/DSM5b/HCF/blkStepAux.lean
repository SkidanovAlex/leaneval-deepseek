import Mathlib
import Submission.Work.DSM5b.HCF.BlkDefs

/-!
# The step relation on a block of the honest tuple complex

This file contains a self-contained proof of the "alternating in the positions" relation
`Work.DSM5b.HCF.blkVal_step_fb` for cocycles of the honest tuple complex on the block of a finset
`S₀` of size `k'+1`, together with the two combinatorial tuple identities it uses:
`tupDel_insertNth_self_aux` and `tupDel_insertNth_swap_aux`.

They are the transcription, to an arbitrary index type `ι`, of the computation carried out inside
`Work.DSM5b.HCF.surjD_step_of_cocycle` (the surjection complex of a `Finset (Fin n)`); the point of
the proofs here is that all the values are moved into the *single* module `ℰ.M S₀` by the
restriction maps, so no `Eq.rec` bookkeeping is needed (`Work.DSM5b.HCF.blkVal`,
`Work.DSM5b.HCF.blkVal_eq_res`, `Work.DSM5b.HCF.res_apply_congr`).
-/


namespace Work.DSM5b.HCF

open Work.DSM5b

universe u

variable {R : Type u} [CommRing R] {ι : Type u} [DecidableEq ι]

/-- Deleting the inserted entry returns the original tuple. -/
lemma tupDel_insertNth_self_aux {m : ℕ} (f : Fin (m + 1) → ι) (i : Fin m) :
    tupDel (i.castSucc.castSucc : Fin (m + 2))
      (Fin.insertNth (α := fun _ => ι) i.castSucc.castSucc (f i.succ) f) = f := by
  funext x
  rw [tupDel_apply]
  exact congrFun (Fin.insertNth_comp_succAbove (i.castSucc.castSucc) (f i.succ) f) x

/-- Deleting the position holding the second copy of the repeated entry. -/
lemma tupDel_insertNth_swap_aux {m : ℕ} (f : Fin (m + 1) → ι) (i : Fin m) :
    tupDel (i.succ.succ : Fin (m + 2))
        (Fin.insertNth (α := fun _ => ι) i.castSucc.castSucc (f i.succ) f)
      = f ∘ Equiv.swap i.castSucc i.succ := by
  funext x
  rw [tupDel_apply, Function.comp_apply]
  rcases lt_trichotomy (x : ℕ) (i : ℕ) with hlt | heq | hgt
  · have hxa : x ≠ i.castSucc := by
      intro h; rw [h] at hlt; simp only [Fin.val_castSucc] at hlt; omega
    have hxb : x ≠ i.succ := by
      intro h; rw [h] at hlt; simp only [Fin.val_succ] at hlt; omega
    rw [Equiv.swap_apply_def, if_neg hxa, if_neg hxb]
    have hs : (i.succ.succ : Fin (m + 2)).succAbove x = x.castSucc :=
      Fin.succAbove_succ_of_le i.succ x (by rw [Fin.le_def]; simp only [Fin.val_succ]; omega)
    have hs2 : (i.castSucc.castSucc : Fin (m + 2)).succAbove x = x.castSucc :=
      Fin.succAbove_castSucc_of_lt (i.castSucc) x (by rw [Fin.lt_def, Fin.val_castSucc]; exact hlt)
    rw [hs, ← hs2]
    exact congrFun (Fin.insertNth_comp_succAbove (i.castSucc.castSucc) (f i.succ) f) x
  · have hxa : x = i.castSucc := Fin.ext heq
    rw [hxa, Equiv.swap_apply_left]
    have hs : (i.succ.succ : Fin (m + 2)).succAbove (i.castSucc) = i.castSucc.castSucc :=
      Fin.succAbove_succ_of_le i.succ (i.castSucc)
        (by rw [Fin.le_def]; simp only [Fin.val_succ]; omega)
    rw [hs, Fin.insertNth_apply_same]
  · by_cases hxb : x = i.succ
    · rw [hxb, Equiv.swap_apply_right]
      have hs : (i.succ.succ : Fin (m + 2)).succAbove (i.succ) = (i.castSucc).succ := by
        rw [Fin.succAbove_succ_of_le (i.succ) (i.succ) le_rfl]
        exact Fin.ext rfl
      have hs2 : (i.castSucc.castSucc : Fin (m + 2)).succAbove (i.castSucc) = (i.castSucc).succ :=
        Fin.succAbove_castSucc_of_le (i.castSucc) (i.castSucc) le_rfl
      rw [hs, ← hs2]
      exact congrFun (Fin.insertNth_comp_succAbove (i.castSucc.castSucc) (f i.succ) f) (i.castSucc)
    · have hxne : (x : ℕ) ≠ (i : ℕ) + 1 := by
        intro h
        exact hxb (Fin.ext (by simp only [Fin.val_succ]; exact h))
      have hxlt : (i.succ : Fin (m + 1)) < x := by
        rw [Fin.lt_def]; simp only [Fin.val_succ]; omega
      have hxa : x ≠ i.castSucc := by
        intro h; rw [h] at hgt; exact absurd hgt (lt_irrefl _)
      rw [Equiv.swap_apply_def, if_neg hxa, if_neg hxb]
      have hs : (i.succ.succ : Fin (m + 2)).succAbove x = x.succ :=
        Fin.succAbove_succ_of_lt i.succ x hxlt
      have hs2 : (i.castSucc.castSucc : Fin (m + 2)).succAbove x = x.succ :=
        Fin.succAbove_castSucc_of_le (i.castSucc) x
          (by rw [Fin.le_def]; simp only [Fin.val_castSucc]; omega)
      rw [hs, ← hs2]
      exact congrFun (Fin.insertNth_comp_succAbove (i.castSucc.castSucc) (f i.succ) f) x

/-- **The basic step relation of a cocycle of the honest tuple complex on a block.** -/
theorem blkVal_step_fb (ℰ : CoeffSys R ι) (k' : ℕ) (S₀ : Finset ι) (hcard : S₀.card = k' + 1)
    (hsub : ∀ S : Finset ι, S.card ≠ k' + 1 → Subsingleton (ℰ.M S))
    (z : ℰ.Htc k') (hz : ℰ.htcD k' z = 0)
    (σ : BlkIdx S₀ k') (i : Fin k') :
    blkVal ℰ S₀ k' z σ + blkVal ℰ S₀ k' z (swapBlk σ i) = 0 := by
  classical
  have hinj : Function.Injective σ.1 := by
    have h1 : (Finset.univ.image σ.1).card = (Finset.univ : Finset (Fin (k' + 1))).card := by
      rw [Finset.card_univ, Fintype.card_fin, ← tupRng, σ.2, hcard]
    have h2 : Set.InjOn σ.1 ↑(Finset.univ : Finset (Fin (k' + 1))) := Finset.card_image_iff.mp h1
    intro x y hxy
    exact h2 (Finset.mem_univ x) (Finset.mem_univ y) hxy
  set u : Fin (k' + 2) → ι :=
    Fin.insertNth (α := fun _ => ι) i.castSucc.castSucc (σ.1 i.succ) σ.1 with hu
  have huc : u ∘ (i.castSucc.castSucc).succAbove = σ.1 := by
    rw [hu]; exact Fin.insertNth_comp_succAbove _ _ _
  have hup : u (i.castSucc.castSucc) = σ.1 i.succ := by
    rw [hu]; exact Fin.insertNth_apply_same _ _ _
  have hpred : ∀ j : Fin (k' + 2), j ≠ i.castSucc.castSucc →
      u j = σ.1 ((i.castSucc).predAbove j) := by
    intro j hj
    have hh := congrFun huc ((i.castSucc).predAbove j)
    simp only [Function.comp_apply] at hh
    rwa [Fin.succAbove_predAbove hj] at hh
  have hurn : tupRng u = S₀ := by
    have hsub1 : tupRng σ.1 ⊆ tupRng u := by
      intro x hx
      rw [tupRng, Finset.mem_image] at hx ⊢
      obtain ⟨y, -, rfl⟩ := hx
      exact ⟨(i.castSucc.castSucc).succAbove y, Finset.mem_univ _, congrFun huc y⟩
    have hsub2 : tupRng u ⊆ tupRng σ.1 := by
      intro x hx
      rw [tupRng, Finset.mem_image] at hx ⊢
      obtain ⟨j, -, rfl⟩ := hx
      by_cases hj : j = i.castSucc.castSucc
      · exact ⟨i.succ, Finset.mem_univ _, by rw [hj, hup]⟩
      · exact ⟨(i.castSucc).predAbove j, Finset.mem_univ _, by rw [hpred j hj]⟩
    exact (Finset.Subset.antisymm hsub2 hsub1).trans σ.2
  have hdel1 : tupDel (i.castSucc.castSucc) u = σ.1 := by
    funext x
    rw [tupDel_apply]
    exact congrFun huc x
  have hdel2 : tupDel (i.succ.succ) u = σ.1 ∘ Equiv.swap i.castSucc i.succ := by
    rw [hu]
    exact tupDel_insertNth_swap_aux σ.1 i
  have hsurj : ∀ j : Fin (k' + 2), tupRng (tupDel j u) = S₀ →
      j = i.castSucc.castSucc ∨ j = i.succ.succ := by
    intro j hj
    have hmem : u j ∈ tupRng (tupDel j u) := by
      rw [hj, ← hurn, tupRng, Finset.mem_image]
      exact ⟨j, Finset.mem_univ _, rfl⟩
    rw [tupRng, Finset.mem_image] at hmem
    obtain ⟨b, -, hb⟩ := hmem
    have hb' : u (j.succAbove b) = u j := hb
    have hnj : j.succAbove b ≠ j := Fin.succAbove_ne j b
    by_cases hj1 : j = i.castSucc.castSucc
    · exact Or.inl hj1
    · right
      by_cases hm1 : j.succAbove b = i.castSucc.castSucc
      · have hum : u (j.succAbove b) = σ.1 i.succ := by rw [hm1, hup]
        have huj : u j = σ.1 ((i.castSucc).predAbove j) := hpred j hj1
        rw [hum, huj] at hb'
        have hpe : (i.castSucc).predAbove j = i.succ := (hinj hb').symm
        have hjj : j = (i.castSucc.castSucc).succAbove ((i.castSucc).predAbove j) :=
          (Fin.succAbove_predAbove hj1).symm
        rw [hjj, hpe]
        exact Fin.succAbove_castSucc_of_le (i.castSucc) (i.succ) (Fin.castSucc_le_succ i)
      · exfalso
        have hum : u (j.succAbove b) = σ.1 ((i.castSucc).predAbove (j.succAbove b)) :=
          hpred (j.succAbove b) hm1
        have huj : u j = σ.1 ((i.castSucc).predAbove j) := hpred j hj1
        rw [hum, huj] at hb'
        have hpe : (i.castSucc).predAbove (j.succAbove b) = (i.castSucc).predAbove j :=
          hinj hb'
        have h1 : (i.castSucc.castSucc).succAbove ((i.castSucc).predAbove j) = j :=
          Fin.succAbove_predAbove hj1
        have h2 : (i.castSucc.castSucc).succAbove ((i.castSucc).predAbove (j.succAbove b)) =
            j.succAbove b := Fin.succAbove_predAbove hm1
        exact hnj (by rw [← h2, hpe, h1])
  have hu' : tupRng u ⊆ S₀ := fun x hx => hurn ▸ hx
  have h0 : ℰ.htcD k' z u = 0 := congrFun hz u
  rw [CoeffSys.htcD_apply] at h0
  have h3 : ∑ j : Fin (k' + 2), ((-1 : R) ^ (j : ℕ)) •
      ℰ.res ((tupRng_del_subset j u).trans hu') (z (tupDel j u)) = 0 := by
    have h1 : ℰ.res hu' (∑ j : Fin (k' + 2), ((-1 : R) ^ (j : ℕ)) •
        ℰ.res (tupRng_del_subset j u) (z (tupDel j u))) = 0 := by
      rw [h0, map_zero]
    simpa only [map_sum, map_smul, map_zero, CoeffSys.res_comp_apply] using h1
  have h4 : ∑ j ∈ ({i.castSucc.castSucc, i.succ.succ} : Finset (Fin (k' + 2))),
      ((-1 : R) ^ (j : ℕ)) • ℰ.res ((tupRng_del_subset j u).trans hu') (z (tupDel j u)) = 0 := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).trans h3
    intro j _ hj
    have hcardj : (tupRng (tupDel j u)).card ≠ k' + 1 := by
      intro hc
      have hset : tupRng (tupDel j u) = S₀ :=
        Finset.eq_of_subset_of_card_le ((tupRng_del_subset j u).trans hu') (by rw [hc, hcard])
      rcases hsurj j hset with h | h
      · subst h; simp at hj
      · subst h; simp at hj
    have hz0 : z (tupDel j u) = 0 := by
      haveI := hsub (tupRng (tupDel j u)) hcardj
      exact Subsingleton.elim _ _
    rw [hz0, map_zero, smul_zero]
  have hpq : (i.castSucc.castSucc : Fin (k' + 2)) ≠ (i.succ.succ : Fin (k' + 2)) := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hh
    omega
  have h5 : ∑ j ∈ ({i.castSucc.castSucc, i.succ.succ} : Finset (Fin (k' + 2))),
      ((-1 : R) ^ (j : ℕ)) • ℰ.res ((tupRng_del_subset j u).trans hu') (z (tupDel j u))
      = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))) • blkVal ℰ S₀ k' z σ
        + ((-1 : R) ^ (((i.succ.succ : Fin (k' + 2)) : ℕ))) •
            blkVal ℰ S₀ k' z (swapBlk σ i) := by
    have e₁ : ℰ.res ((tupRng_del_subset (i.castSucc.castSucc) u).trans hu')
        (z (tupDel (i.castSucc.castSucc) u)) = blkVal ℰ S₀ k' z σ :=
      res_apply_congr (ℰ := ℰ) (z := z) (T := S₀) hdel1 _ (fun x hx => σ.2 ▸ hx)
    have e₂ : ℰ.res ((tupRng_del_subset (i.succ.succ) u).trans hu')
        (z (tupDel (i.succ.succ) u)) = blkVal ℰ S₀ k' z (swapBlk σ i) :=
      res_apply_congr (ℰ := ℰ) (z := z) (T := S₀) hdel2 _ (fun x hx => (swapBlk σ i).2 ▸ hx)
    rw [Finset.sum_pair hpq, e₁, e₂]
  have h6 : ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))) • blkVal ℰ S₀ k' z σ
      + ((-1 : R) ^ (((i.succ.succ : Fin (k' + 2)) : ℕ))) • blkVal ℰ S₀ k' z (swapBlk σ i) = 0 :=
    h5.symm.trans h4
  have hsign : ((-1 : R) ^ (((i.succ.succ : Fin (k' + 2)) : ℕ)))
      = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))) := by
    have hv : (((i.succ.succ : Fin (k' + 2)) : ℕ))
        = (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ)) + 2 := by
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.add_assoc]
    rw [hv, pow_add, show (-1 : R) ^ 2 = 1 by norm_num, mul_one]
  have hfinal : ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))) •
      (blkVal ℰ S₀ k' z σ + blkVal ℰ S₀ k' z (swapBlk σ i)) = 0 := by
    rw [hsign] at h6
    rwa [← smul_add] at h6
  have hcc : ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ)))
      * ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))) = 1 := by
    rw [← pow_add]
    rw [show (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))
        + (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))
        = 2 * (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ)) from by omega]
    rw [pow_mul, show (-1 : R) ^ 2 = 1 by norm_num, one_pow]
  calc blkVal ℰ S₀ k' z σ + blkVal ℰ S₀ k' z (swapBlk σ i)
      = (1 : R) • (blkVal ℰ S₀ k' z σ + blkVal ℰ S₀ k' z (swapBlk σ i)) :=
        (one_smul _ _).symm
    _ = (((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ)))
          * ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))))
          • (blkVal ℰ S₀ k' z σ + blkVal ℰ S₀ k' z (swapBlk σ i)) := by rw [hcc]
    _ = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ)))
          • (((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ)))
          • (blkVal ℰ S₀ k' z σ + blkVal ℰ S₀ k' z (swapBlk σ i))) := by rw [mul_smul]
    _ = ((-1 : R) ^ (((i.castSucc.castSucc : Fin (k' + 2)) : ℕ))) • 0 := by rw [hfinal]
    _ = 0 := smul_zero _

end Work.DSM5b.HCF
