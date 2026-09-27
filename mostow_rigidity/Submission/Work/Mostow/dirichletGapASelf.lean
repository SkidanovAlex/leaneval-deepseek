import Mathlib
import Submission.Work.Mostow.dirichletScrew
import Submission.Work.Mostow.geodGapClause
import Submission.Work.Mostow.margRegionInvariant
import Submission.Work.Mostow.geodRegionTube
import Submission.Work.Mostow.geodStratumOddAux
import Submission.Work.Mostow.gapA_oddCore
import Submission.Work.Mostow.gapA_three
import Submission.Work.Mostow.gapA_even
import Submission.Work.Mostow.gapA_all_aux

/-!
# GAP-A, self-contained, with the geodesic-stratum screw proved locally

`Submission/Work/Mostow/dirichletScrew.lean` (namespace `Work.Mostow.DirichletScrew`) contains a
complete `sorry`-free proof of the element step of the geodesic stratum (the statement of
`Work.Mostow.geodScrewW`), so the geodesic stratum and GAP-A can be assembled without the foreign
stub.  This file replays that (short) assembly in our own module, so that
`Work.Mostow.dirichletNotDeepBounded` rests on no foreign `sorry`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

theorem geodStepSelf (m : ℕ) (hm : 4 ≤ m) (hev : Even m)
    (hA : ∀ k, 1 ≤ k → POActionProp k) (hI : ∀ k, 1 ≤ k → HypIsometryProp k) :
    GeodStep m := by
  have hA1 : POActionProp 1 := hA 1 (by norm_num)
  have hI1 : HypIsometryProp 1 := hI 1 (by norm_num)
  have hAn : POActionProp (1 + m) := hA (1 + m) (by omega)
  have hIn : HypIsometryProp (1 + m) := hI (1 + m) (by omega)
  obtain ⟨θG, hθG, hgapC⟩ := geodGapClause m hm hev hAn hIn hA1 hI1
  obtain ⟨η1m, hη1m, hmarg⟩ := margRegionInvariant m hm hev hAn hIn hA1 hI1
  obtain ⟨Cn, hCn, η1t, hη1t, htube⟩ := geodRegionTube m hm hev hAn hIn hA1 hI1
  -- the `V`-dependent gap scale
  set ηg : ℝ → ℝ := fun V => if h : 0 < V then (Classical.choose (hgapC V h)) else 1 with hηgdef
  have hηgpos : ∀ V : ℝ, 0 < V → 0 < ηg V := by
    intro V hV
    rw [hηgdef]
    simp only [dif_pos hV]
    exact (Classical.choose_spec (hgapC V hV)).1
  have hηg_spec : ∀ V : ℝ, (hV : 0 < V) → ∀ (Λ : Subgroup (PO (1 + m) 1)) (D : Set (E (1 + m)))
      (a : PO (1 + m) 1) (u : E (1 + m)),
      IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (1 + m)) →
      volH (1 + m) D ≤ ENNReal.ofReal V → a ∈ Λ → a ∈ SetStabStd 1 m → resStd 1 m a = 1 →
      a ≠ 1 → NearIdAt a u (ηg V) → fixSet a = stdTG 1 m := by
    intro V hV
    rw [hηgdef]
    simp only [dif_pos hV]
    exact (Classical.choose_spec (hgapC V hV)).2.2
  set η1 : ℝ → ℝ := fun V => min (min (ηg V) η1m) η1t with hη1def
  have hη1pos : ∀ V : ℝ, 0 < V → 0 < η1 V := by
    intro V hV
    rw [hη1def]
    exact lt_min (lt_min (hηgpos V hV) hη1m) hη1t
  obtain ⟨C, hCpos, hscrew⟩ := DirichletScrew.dirichletScrew m hm hev hAn hIn hA1 hI1 η1 hη1pos Cn hCn
  refine ⟨C, hCpos, fun V hV => ?_⟩
  obtain ⟨η₀, hη₀pos, hη₀le, hη₀rest⟩ := hscrew V hV
  refine ⟨η₀, hη₀pos, fun η hη hηle Λ D R z hdisc hD hvol hb hRfree hnear => ?_⟩
  refine hη₀rest Λ D R z η hdisc hD hvol hb hRfree hnear hη hηle ?_
  -- the tube inequality at the scale `η1 V`
  have hpos : 0 < η1 V := hη1pos V hV
  have hle_t : η1 V ≤ η1t := by rw [hη1def]; exact min_le_right _ _
  have hle_m : η1 V ≤ η1m := by
    rw [hη1def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hle_g : η1 V ≤ ηg V := by
    rw [hη1def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hgapV : ∀ (a : PO (1 + m) 1) (u : E (1 + m)), a ∈ Λ → a ∈ SetStabStd 1 m →
      resStd 1 m a = 1 → a ≠ 1 → NearIdAt a u (η1 V) → fixSet a = stdTG 1 m :=
    fun a u ha hs hr hn hna =>
      hηg_spec V hV Λ D a u hdisc hD hvol ha hs hr hn
        (fun v hv => lt_of_lt_of_le (hna v hv) hle_g)
  have hmul := hmarg (η1 V) hpos hle_m Λ hdisc hgapV
  intro DY hDY
  calc volH 1 DY * (volume : Measure (E m)) (nrmC 1 m '' margRegion m Λ (η1 V))
      ≤ ENNReal.ofReal Cn * (geodPtCard m Λ : ENNReal) * volH (1 + m) D :=
        htube (η1 V) hpos hle_t Λ D R hdisc hD hb hRfree hgapV hmul DY hDY
    _ ≤ ENNReal.ofReal Cn * (geodPtCard m Λ : ENNReal) * ENNReal.ofReal V :=
        mul_le_mul_of_nonneg_left hvol zero_le
    _ = ENNReal.ofReal (Cn * V) * (geodPtCard m Λ : ENNReal) := by
        rw [mul_assoc, mul_comm (geodPtCard m Λ : ENNReal) (ENNReal.ofReal V), ← mul_assoc,
          ← ENNReal.ofReal_mul hCn.le]

/-- **The geodesic stratum (`k = 1`) from the locally proved element step.** -/
theorem geodStratumSelf (m : ℕ) (hm : 4 ≤ m) (hev : Even m)
    (hA : ∀ k, 1 ≤ k → POActionProp k) (hI : ∀ k, 1 ≤ k → HypIsometryProp k)
    (hCov : ∀ j, 2 ≤ j → j < 1 + m → CovolLB j) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (Λ : Subgroup (PO (1 + m) 1)) (D : Set (E (1 + m))) (z : E (1 + m)),
        IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (1 + m)) → volH (1 + m) D ≤ ENNReal.ofReal V →
        nearGrp Λ z η ≠ ⊥ → Finite (nearGrp Λ z η) →
        ∃ γ ∈ Λ, orderOf γ = 0 ∧ hdist z (γ • z) ≤ C * η :=
  geodStratum_of_block m hm hev hA hI hCov (geodStepSelf m hm hev hA hI)

theorem gapA_oddSelf (n : ℕ) (hn : 5 ≤ n) (hodd : Odd n)
    (hA : ∀ k, 1 ≤ k → POActionProp k) (hI : ∀ k, 1 ≤ k → HypIsometryProp k)
    (hCov : ∀ k, 2 ≤ k → k < n → CovolLB k)
    (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) (hmult : MultThickProp Γ) : GapAProp Γ := by
  obtain ⟨k, hk⟩ := hodd
  have hk2 : n = 1 + 2 * k := by omega
  subst hk2
  have hCov' : ∀ j, 2 ≤ j → j < 1 + 2 * k → CovolLB j := fun j hj hjlt => hCov j hj hjlt
  have H : ∃ C : ℝ, 0 < C ∧ ∀ V : ℝ, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ (Λ : Subgroup (PO (1 + 2 * k) 1)) (D : Set (E (1 + 2 * k))) (z : E (1 + 2 * k)),
        IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (1 + 2 * k)) →
        volH (1 + 2 * k) D ≤ ENNReal.ofReal V → nearGrp Λ z η ≠ ⊥ →
        Finite ↥(nearGrp Λ z η) →
        ∃ γ ∈ Λ, orderOf γ = 0 ∧ hdist z (γ • z) ≤ C * η :=
    geodStratumSelf (2 * k) (by omega) (even_two_mul k) hA hI hCov'
  exact gapA_odd_geod k (by omega) hA hI hCov' H Γ hΓ hmult

/-- **GAP-A for every `n ≥ 3`**, with the odd case routed through the locally proved geodesic
stratum. -/
theorem gapA_allSelf (n : ℕ) (hn : 3 ≤ n) (Γ : Subgroup (PO n 1)) (hΓ : HypLattice Γ) :
    GapAProp Γ := by
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · obtain rfl : n = 3 := by omega
    exact gapA_three (poAction_all 3 (by norm_num)) (hypIsometry_all 3 (by norm_num))
      (margulisCusp_all 3 (by norm_num)) (pairStab_all 3 (by norm_num)) Γ hΓ
      (multThick_all 3 (by norm_num) Γ hΓ)
  · rcases Nat.even_or_odd n with hev | hodd
    · exact gapA_even n hge hev poAction_all hypIsometry_all (fun k hk _ => covolLB_all k hk)
        Γ hΓ (multThick_all n (by omega) Γ hΓ)
    · have h5 : 5 ≤ n := by
        obtain ⟨m, hm⟩ := hodd
        omega
      exact gapA_oddSelf n h5 hodd (fun k hk => poAction_ge1 k hk)
        (fun k hk => hypIsometryAll k (poAction_ge1 k hk)) (fun k hk _ => covolLB_all k hk)
        Γ hΓ (multThick_all n (by omega) Γ hΓ)

end

end Work.Mostow
