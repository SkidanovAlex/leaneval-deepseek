import Mathlib
import Submission.Work.EKLC6Core.BiGenAux

set_option linter.unusedVariables false

namespace Work.EKLC6Core.BiGenSup

open Work.EKLContract

/-- Composing an iterate of `T` with an iterate of a left inverse `Tinv` of `T` through `comap`:
for `b ≤ n` the composite `Tinv^[b] ∘ T^[n]` is `T^[n-b]`. -/
theorem comap_iterate_comp_le {X : Type*} [mX : MeasurableSpace X] {T Tinv : X → X}
    (hinv : Function.LeftInverse Tinv T) (m : MeasurableSpace X) {b n : ℕ} (h : b ≤ n) :
    MeasurableSpace.comap (T^[n]) (MeasurableSpace.comap (Tinv^[b]) m)
      = MeasurableSpace.comap (T^[n - b]) m := by
  rw [MeasurableSpace.comap_comp, BiGenAux.iterate_comp_of_leftInverse_le hinv h]

/-- The companion of `comap_iterate_comp_le`: for `n ≤ b` the composite `Tinv^[b] ∘ T^[n]`
is `Tinv^[b-n]`. -/
theorem comap_iterate_comp_ge {X : Type*} [mX : MeasurableSpace X] {T Tinv : X → X}
    (hinv : Function.LeftInverse Tinv T) (m : MeasurableSpace X) {b n : ℕ} (h : n ≤ b) :
    MeasurableSpace.comap (T^[n]) (MeasurableSpace.comap (Tinv^[b]) m)
      = MeasurableSpace.comap (Tinv^[b - n]) m := by
  rw [MeasurableSpace.comap_comp, BiGenAux.iterate_comp_of_leftInverse_ge hinv h]

/-- **Pull-back of a window σ-algebra.**  For the window partition
`winPart Tinv hTinv P l = ⋁_{1 ≤ b ≤ l} Tinv^{-b} P`,
`comap (T^[n]) (partSigma (winPart …))` is the join over `b ∈ {1,…,l}` of the pull-backs
`comap (Tinv^[b] ∘ T^[n]) (partSigma P)`. -/
theorem comap_partSigma_winPart {X : Type*} [mX : MeasurableSpace X]
    (T Tinv : X → X) (hTinv : Measurable Tinv) (P : @Work.EKLContract.FinPart X mX) (l n : ℕ) :
    MeasurableSpace.comap (T^[n])
        (@Work.EKLContract.partSigma X mX
          (@Work.EKLC6Core.BiGenAux.winPart X mX Tinv hTinv P l))
      = ⨆ i : Fin l, MeasurableSpace.comap (Tinv^[(i : ℕ) + 1] ∘ T^[n])
          (@Work.EKLContract.partSigma X mX P) := by
  rw [Work.EKLC6Core.BiGenAux.partSigma_winPart, MeasurableSpace.comap_iSup]
  refine iSup_congr fun i => ?_
  rw [MeasurableSpace.comap_comp]

theorem iSup_comap_winPart_eq {X : Type*} [mX : MeasurableSpace X]
    (T Tinv : X → X) (hinv : Function.LeftInverse Tinv T) (hTinv : Measurable Tinv)
    (𝒮 : MeasurableSpace X) (G : ℕ → @Work.EKLContract.FinPart X mX)
    (hGmono : ∀ l, @Work.EKLContract.partSigma X mX (G l) ≤
      @Work.EKLContract.partSigma X mX (G (l + 1)))
    (hGgen : (⨆ l, @Work.EKLContract.partSigma X mX (G l)) = 𝒮)
    (hbil : (⨆ n : ℕ, MeasurableSpace.comap (T^[n]) 𝒮 ⊔
      MeasurableSpace.comap (Tinv^[n]) 𝒮) = mX) :
    (⨆ l : ℕ, ⨆ n : ℕ, MeasurableSpace.comap (T^[n])
      (@Work.EKLContract.partSigma X mX
        (@Work.EKLC6Core.BiGenAux.winPart X mX Tinv hTinv (G l) l))) = mX := by
  refine le_antisymm ?_ ?_
  · -- upper bound: every term of the join lies below `mX`
    have hT_le : ∀ k : ℕ, MeasurableSpace.comap (T^[k]) 𝒮 ≤ mX := fun k =>
      le_trans (le_sup_left :
          MeasurableSpace.comap (T^[k]) 𝒮 ≤ MeasurableSpace.comap (T^[k]) 𝒮 ⊔
            MeasurableSpace.comap (Tinv^[k]) 𝒮)
        (le_trans (le_iSup (fun n : ℕ => MeasurableSpace.comap (T^[n]) 𝒮 ⊔
            MeasurableSpace.comap (Tinv^[n]) 𝒮) k) (le_of_eq hbil))
    have hTinv_le : ∀ k : ℕ, MeasurableSpace.comap (Tinv^[k]) 𝒮 ≤ mX := fun k =>
      le_trans (le_sup_right :
          MeasurableSpace.comap (Tinv^[k]) 𝒮 ≤ MeasurableSpace.comap (T^[k]) 𝒮 ⊔
            MeasurableSpace.comap (Tinv^[k]) 𝒮)
        (le_trans (le_iSup (fun n : ℕ => MeasurableSpace.comap (T^[n]) 𝒮 ⊔
            MeasurableSpace.comap (Tinv^[n]) 𝒮) k) (le_of_eq hbil))
    have hGl : ∀ l, @Work.EKLContract.partSigma X mX (G l) ≤ 𝒮 := fun l =>
      le_trans (le_iSup (fun l => @Work.EKLContract.partSigma X mX (G l)) l) (le_of_eq hGgen)
    refine iSup_le fun l => iSup_le fun n => ?_
    rw [@comap_partSigma_winPart X mX T Tinv hTinv (G l) l n]
    refine iSup_le fun i => ?_
    by_cases hle : (i : ℕ) + 1 ≤ n
    · rw [BiGenAux.iterate_comp_of_leftInverse_le hinv hle]
      exact le_trans (MeasurableSpace.comap_mono (hGl l)) (hT_le (n - ((i : ℕ) + 1)))
    · rw [BiGenAux.iterate_comp_of_leftInverse_ge hinv (le_of_lt (not_le.mp hle))]
      exact le_trans (MeasurableSpace.comap_mono (hGl l)) (hTinv_le (((i : ℕ) + 1) - n))
  · -- lower bound: the join dominates the full two-sided orbit of `𝒮`
    set LHS : MeasurableSpace X := (⨆ l : ℕ, ⨆ n : ℕ, MeasurableSpace.comap (T^[n])
        (@Work.EKLContract.partSigma X mX
          (@Work.EKLC6Core.BiGenAux.winPart X mX Tinv hTinv (G l) l))) with hLHS
    have hGmono' : ∀ a b : ℕ, a ≤ b →
        @Work.EKLContract.partSigma X mX (G a) ≤ @Work.EKLContract.partSigma X mX (G b) := by
      intro a b hab
      induction b, hab using Nat.le_induction with
      | base => exact le_rfl
      | succ c _ ih => exact le_trans ih (hGmono c)
    -- a forward iterate of `partSigma (G N)` is dominated by the `(k+1, N)`-term
    have step : ∀ k N : ℕ, 1 ≤ N → MeasurableSpace.comap (T^[k])
          (@Work.EKLContract.partSigma X mX (G N))
        ≤ MeasurableSpace.comap (T^[k+1]) (⨆ i : Fin N, MeasurableSpace.comap (Tinv^[(i:ℕ)+1])
            (@Work.EKLContract.partSigma X mX (G N))) := by
      intro k N hN
      have hkey : MeasurableSpace.comap (T^[k]) (@Work.EKLContract.partSigma X mX (G N))
          = MeasurableSpace.comap (T^[k+1]) (MeasurableSpace.comap (Tinv^[1])
            (@Work.EKLContract.partSigma X mX (G N))) := by
        rw [MeasurableSpace.comap_comp,
          BiGenAux.iterate_comp_of_leftInverse_le hinv (b := 1) (j := k+1) (by omega),
          Nat.add_sub_cancel]
      rw [hkey]
      exact MeasurableSpace.comap_mono (le_iSup (fun i : Fin N =>
          MeasurableSpace.comap (Tinv^[(i:ℕ)+1])
            (@Work.EKLContract.partSigma X mX (G N))) ⟨0, hN⟩)
    -- a backward iterate `Tinv^[k]` (`k ≥ 1`) is dominated by the `(0, N)`-term
    have stepk : ∀ k N : ℕ, 1 ≤ k → k ≤ N →
        MeasurableSpace.comap (Tinv^[k]) (@Work.EKLContract.partSigma X mX (G N))
        ≤ MeasurableSpace.comap (T^[0]) (⨆ i : Fin N, MeasurableSpace.comap (Tinv^[(i:ℕ)+1])
            (@Work.EKLContract.partSigma X mX (G N))) := by
      intro k N hk1 hkN
      have hkey : MeasurableSpace.comap (Tinv^[k]) (@Work.EKLContract.partSigma X mX (G N))
          = MeasurableSpace.comap (T^[0]) (MeasurableSpace.comap (Tinv^[k])
            (@Work.EKLContract.partSigma X mX (G N))) := by
        rw [Function.iterate_zero, MeasurableSpace.comap_id]
      rw [hkey]
      refine MeasurableSpace.comap_mono ?_
      have hidx : k - 1 < N := by omega
      have hle0 := le_iSup (fun i : Fin N => MeasurableSpace.comap (Tinv^[(i:ℕ)+1])
            (@Work.EKLContract.partSigma X mX (G N))) ⟨k-1, hidx⟩
      rwa [Nat.sub_add_cancel hk1] at hle0
    -- the `N`-th window term lies in the join
    have toLHS : ∀ m N : ℕ, 1 ≤ N → MeasurableSpace.comap (T^[m])
          (⨆ i : Fin N, MeasurableSpace.comap (Tinv^[(i:ℕ)+1])
            (@Work.EKLContract.partSigma X mX (G N))) ≤ LHS := by
      intro m N hN
      rw [← @Work.EKLC6Core.BiGenAux.partSigma_winPart X mX Tinv hTinv (G N) N]
      exact le_trans (le_iSup (fun n : ℕ => MeasurableSpace.comap (T^[n])
          (@Work.EKLContract.partSigma X mX
            (@Work.EKLC6Core.BiGenAux.winPart X mX Tinv hTinv (G N) N))) m)
        (le_iSup (fun l : ℕ => ⨆ n : ℕ, MeasurableSpace.comap (T^[n])
          (@Work.EKLContract.partSigma X mX
            (@Work.EKLC6Core.BiGenAux.winPart X mX Tinv hTinv (G l) l))) N)
    refine le_trans (le_of_eq hbil.symm) ?_
    refine iSup_le fun k => sup_le ?_ ?_
    · rw [← hGgen, MeasurableSpace.comap_iSup]
      refine iSup_le fun l => ?_
      have hN : 1 ≤ max l (k + 1) := Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) (le_max_right _ _)
      exact le_trans (MeasurableSpace.comap_mono (hGmono' l (max l (k+1)) (le_max_left _ _)))
        (le_trans (step k (max l (k+1)) hN) (toLHS (k+1) (max l (k+1)) hN))
    · by_cases hk : k = 0
      · subst hk
        rw [show MeasurableSpace.comap (Tinv^[0]) 𝒮 = MeasurableSpace.comap (T^[0]) 𝒮 from by
          rw [Function.iterate_zero, Function.iterate_zero, MeasurableSpace.comap_id]]
        rw [← hGgen, MeasurableSpace.comap_iSup]
        refine iSup_le fun l => ?_
        have hN : 1 ≤ max l (0 + 1) :=
          Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (le_max_right _ _)
        exact le_trans (MeasurableSpace.comap_mono (hGmono' l (max l (0+1)) (le_max_left _ _)))
          (le_trans (step 0 (max l (0+1)) hN) (toLHS 1 (max l (0+1)) hN))
      · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
        rw [← hGgen, MeasurableSpace.comap_iSup]
        refine iSup_le fun l => ?_
        have hkN : k ≤ max l k := le_max_right _ _
        exact le_trans (MeasurableSpace.comap_mono (hGmono' l (max l k) (le_max_left _ _)))
          (le_trans (stepk k (max l k) hk1 hkN) (toLHS 0 (max l k) (by omega)))

end Work.EKLC6Core.BiGenSup
