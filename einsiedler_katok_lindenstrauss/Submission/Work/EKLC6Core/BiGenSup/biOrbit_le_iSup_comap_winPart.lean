import Mathlib
import Submission.Work.EKLC6Core.BiGenAux
import Submission.Work.EKLC6Core.BiGenSup.iSup_comap_winPart_eq

set_option linter.unusedVariables false

namespace Work.EKLC6Core.BiGenSup

open Work.EKLContract

/-- **Lower bound for the bilateral orbit σ-algebra.**  The full two-sided orbit of `𝒮 = ⨆ l,
partSigma (G l)` is dominated by the join, over `l` and `n`, of the pull-backs `comap (T^[n])` of
the window σ-algebras `partSigma (winPart Tinv hTinv (G l) l) = ⨆_{1 ≤ b ≤ l} comap (Tinv^[b])
(partSigma (G l))`.

The proof follows the lower-bound half of `iSup_comap_winPart_eq`: a positive iterate `comap
(T^[k]) (partSigma (G N))` is reached from the pull-back at time `k+1` of the `b = 1` window term
(using `Tinv ∘ T = id` on the nose), while a negative iterate `comap (Tinv^[k]) (partSigma (G N))`
is one of the window terms directly.  Monotonicity of `G` lets us first pass to a sufficiently
large index `N`. -/
theorem biOrbit_le_iSup_comap_winPart {X : Type*} [mX : MeasurableSpace X]
    (T Tinv : X → X) (hinv : Function.LeftInverse Tinv T) (hTinv : Measurable Tinv)
    (𝒮 : MeasurableSpace X) (G : ℕ → @Work.EKLContract.FinPart X mX)
    (hGmono : ∀ l, @Work.EKLContract.partSigma X mX (G l) ≤
      @Work.EKLContract.partSigma X mX (G (l + 1)))
    (hGgen : (⨆ l, @Work.EKLContract.partSigma X mX (G l)) = 𝒮) :
    (⨆ n : ℕ, MeasurableSpace.comap (T^[n]) 𝒮 ⊔
        MeasurableSpace.comap (Tinv^[n]) 𝒮)
      ≤ ⨆ l : ℕ, ⨆ n : ℕ, MeasurableSpace.comap (T^[n])
          (@Work.EKLContract.partSigma X mX
            (@Work.EKLC6Core.BiGenAux.winPart X mX Tinv hTinv (G l) l)) := by
  set LHS : MeasurableSpace X := (⨆ l : ℕ, ⨆ n : ℕ, MeasurableSpace.comap (T^[n])
      (@Work.EKLContract.partSigma X mX
        (@Work.EKLC6Core.BiGenAux.winPart X mX Tinv hTinv (G l) l))) with hLHS
  -- monotonicity of `G` at the level of σ-algebras
  have hGmono' : ∀ a b : ℕ, a ≤ b →
      @Work.EKLContract.partSigma X mX (G a) ≤ @Work.EKLContract.partSigma X mX (G b) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ c _ ih => exact le_trans ih (hGmono c)
  -- a forward iterate is dominated by the pull-back at time `k+1` of the `b = 1` window term
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
  -- a backward iterate `Tinv^[k]` (`k ≥ 1`) is dominated by the `n = 0` pull-back of the window
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
  -- the `N`-th window term lies in the join defining `LHS`
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
  refine iSup_le fun k => sup_le ?_ ?_
  · -- forward direction: `comap (T^[k]) 𝒮 ≤ LHS`
    rw [← hGgen, MeasurableSpace.comap_iSup]
    refine iSup_le fun l => ?_
    have hN : 1 ≤ max l (k + 1) := Nat.lt_of_lt_of_le (Nat.zero_lt_succ k) (le_max_right _ _)
    exact le_trans (MeasurableSpace.comap_mono (hGmono' l (max l (k+1)) (le_max_left _ _)))
      (le_trans (step k (max l (k+1)) hN) (toLHS (k+1) (max l (k+1)) hN))
  · -- backward direction: `comap (Tinv^[k]) 𝒮 ≤ LHS`
    by_cases hk : k = 0
    · subst hk
      rw [show MeasurableSpace.comap (Tinv^[0]) 𝒮 = MeasurableSpace.comap (T^[0]) 𝒮 from by
        rw [Function.iterate_zero, Function.iterate_zero, MeasurableSpace.comap_id]]
      rw [← hGgen, MeasurableSpace.comap_iSup]
      refine iSup_le fun l => ?_
      have hN : 1 ≤ max l (0 + 1) := Nat.lt_of_lt_of_le (Nat.zero_lt_succ 0) (le_max_right _ _)
      exact le_trans (MeasurableSpace.comap_mono (hGmono' l (max l (0+1)) (le_max_left _ _)))
        (le_trans (step 0 (max l (0+1)) hN) (toLHS 1 (max l (0+1)) hN))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      rw [← hGgen, MeasurableSpace.comap_iSup]
      refine iSup_le fun l => ?_
      have hkN : k ≤ max l k := le_max_right _ _
      exact le_trans (MeasurableSpace.comap_mono (hGmono' l (max l k) (le_max_left _ _)))
        (le_trans (stepk k (max l k) hk1 hkN) (toLHS 0 (max l k) (by omega)))

end Work.EKLC6Core.BiGenSup
