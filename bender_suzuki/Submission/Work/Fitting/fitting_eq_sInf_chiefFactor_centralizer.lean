import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.exists_chiefSeries

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical
open scoped commutatorElement

namespace Work.Fitting

/-- The Fitting subgroup of a group is normal. -/
theorem fitting_normal' (G : Type*) [Group G] : (Work.Fitting.fitting G).Normal :=
  Work.Fitting.normal_sSup fun _ hN => hN.1

/-- **A normal nilpotent subgroup centralizes every chief factor.**
If `N ⊴ G` is nilpotent and `H < K` is a chief factor of `G` (`H ⊴ K`), then
`[N, K] ≤ H`, i.e. `N ≤ C_G(K/H)`. -/
theorem nilpotent_le_sectionCentralizer {G : Type*} [Group G] [Finite G]
    {N H K : Subgroup G} [H.Normal] [N.Normal] [Group.IsNilpotent ↥N]
    (h : Work.Fitting.IsChiefFactor H K) :
    N ≤ Work.Fitting.sectionCentralizer H K := by
  haveI hKnorm : K.Normal := h.2.1
  suffices hcomm : ⁅N, K⁆ ≤ H by
    intro x hx
    rw [Work.Fitting.mem_sectionCentralizer_iff_commutator]
    intro k hk
    rw [← commutatorElement_def]
    exact hcomm (Subgroup.commutator_mem_commutator hx hk)
  by_contra hcon
  have hMnorm : (⁅N, K⁆ ⊔ H).Normal := Subgroup.sup_normal _ _
  have hHleM : H ≤ ⁅N, K⁆ ⊔ H := le_sup_right
  have hMleK : ⁅N, K⁆ ⊔ H ≤ K :=
    sup_le (Subgroup.commutator_le_right N K) (le_of_lt h.2.2.1)
  have hMeqK : ⁅N, K⁆ ⊔ H = K := by
    rcases h.2.2.2 (⁅N, K⁆ ⊔ H) hMnorm hHleM hMleK with hMH | hMK
    · exact absurd (hMH ▸ le_sup_left) hcon
    · exact hMK
  have hKle : K ≤ ⁅N, K⁆ ⊔ H := hMeqK.ge
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries N).mp inferInstance
  have hiter : ∀ k : ℕ, K ≤ N.lowerCentralSeries k ⊔ H := by
    intro k
    induction k with
    | zero =>
      rw [Subgroup.lowerCentralSeries_zero]
      exact hKle.trans (sup_le_sup (Subgroup.commutator_le_left N K) le_rfl)
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      have h1 : ⁅N, K⁆ ≤ ⁅N.lowerCentralSeries k, N⁆ ⊔ H := by
        have hmono : ⁅N, K⁆ ≤ ⁅N, N.lowerCentralSeries k ⊔ H⁆ :=
          Subgroup.commutator_mono_right ih
        rw [Subgroup.commutator_sup_left N (N.lowerCentralSeries k) H,
            Subgroup.commutator_comm N (N.lowerCentralSeries k)] at hmono
        exact hmono.trans
          (sup_le le_sup_left ((Subgroup.commutator_le_right N H).trans le_sup_right))
      calc K ≤ ⁅N, K⁆ ⊔ H := hKle
        _ ≤ ⁅N.lowerCentralSeries k, N⁆ ⊔ H := sup_le h1 le_sup_right
  have hKleH : K ≤ H := by
    have hh := hiter c
    rw [hc, bot_sup_eq] at hh
    exact hh
  exact absurd hKleH (not_le_of_gt h.2.2.1)

theorem fitting_eq_sInf_chiefFactor_centralizer (G : Type*) [Group G] [Finite G] :
    Work.Fitting.fitting G = sInf {C : Subgroup G | ∃ (H K : Subgroup G) (hH : H.Normal),
      Work.Fitting.IsChiefFactor H K ∧
        C = @Work.Fitting.sectionCentralizer G _ H K hH} := by
  set S : Set (Subgroup G) :=
    {C : Subgroup G | ∃ (H K : Subgroup G) (hH : H.Normal),
      Work.Fitting.IsChiefFactor H K ∧
        C = @Work.Fitting.sectionCentralizer G _ H K hH} with hS
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    rintro C ⟨H, K, hH, hcf, rfl⟩
    haveI : H.Normal := hH
    haveI : (Work.Fitting.fitting G).Normal := Work.Fitting.fitting_normal' G
    haveI : Group.IsNilpotent ↥(Work.Fitting.fitting G) := Work.Fitting.fitting_isNilpotent G
    exact nilpotent_le_sectionCentralizer hcf
  · let C₀ : Subgroup G := sInf S
    have hCnorm : C₀.Normal := by
      have h : (sInf S).Normal := by
        rw [sInf_eq_iInf]
        refine Subgroup.normal_iInf_normal (fun a => Subgroup.normal_iInf_normal (fun ha => ?_))
        obtain ⟨H, K, hH, hcf, rfl⟩ := ha
        haveI : K.Normal := hcf.2.1
        exact sectionCentralizer_normal
      exact h
    haveI : C₀.Normal := hCnorm
    have hCnil : Group.IsNilpotent ↥C₀ := by
      obtain ⟨cs⟩ := exists_chiefSeries G
      haveI hnormcs : ∀ i : Fin (cs.n + 1), (cs.G_ i).Normal := cs.normal
      let m : ℕ := cs.n
      have hcf : ∀ i : Fin m, IsChiefFactor (cs.G_ i.succ) (cs.G_ i.castSucc) :=
        fun i => ⟨cs.normal _, cs.normal _, cs.lt_prev i, cs.minimal i⟩
      have hle : ∀ i : Fin m, C₀ ≤ sectionCentralizer (cs.G_ i.succ) (cs.G_ i.castSucc) := by
        intro i
        have : (sectionCentralizer (cs.G_ i.succ) (cs.G_ i.castSucc)) ∈ S :=
          ⟨cs.G_ i.succ, cs.G_ i.castSucc, cs.normal i.succ, hcf i, rfl⟩
        exact sInf_le this
      have hcomm_i : ∀ i : Fin m, ⁅C₀, cs.G_ i.castSucc⁆ ≤ cs.G_ i.succ := by
        intro i
        rw [Subgroup.commutator_le]
        intro x hx y hy
        have hmem := (Work.Fitting.mem_sectionCentralizer_iff_commutator.mp (hle i hx)) y hy
        rwa [← commutatorElement_def] at hmem
      have hidx : ∀ j : ℕ, C₀.lowerCentralSeries j ≤
          C₀ ⊓ cs.G_ (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1)) := by
        intro j
        induction j with
        | zero =>
          have h0 : (⟨min 0 m, Nat.lt_succ_of_le (Nat.min_le_right 0 m)⟩ : Fin (m+1)) = 0 := by
            ext; simp
          rw [Subgroup.lowerCentralSeries_zero, h0, cs.top_eq, inf_top_eq]
        | succ j ih =>
          rw [Subgroup.lowerCentralSeries_succ]
          by_cases hj : j < m
          · have hidxj : (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1)) =
                ⟨j, Nat.lt_trans hj (Nat.lt_succ_self m)⟩ := by
              ext; simp [Nat.min_eq_left (le_of_lt hj)]
            have hidxj1 : (⟨min (j+1) m, Nat.lt_succ_of_le (Nat.min_le_right (j+1) m)⟩ : Fin (m+1)) =
                ⟨j+1, Nat.succ_lt_succ hj⟩ := by
              ext; simp [Nat.min_eq_left (Nat.succ_le_of_lt hj)]
            have hstep : ⁅C₀, cs.G_ (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1))⁆
                ≤ cs.G_ (⟨min (j+1) m, Nat.lt_succ_of_le (Nat.min_le_right (j+1) m)⟩ : Fin (m+1)) := by
              rw [hidxj, hidxj1]
              exact hcomm_i ⟨j, hj⟩
            refine le_inf ?_ ?_
            · exact (Subgroup.commutator_mono_left ih).trans (Subgroup.commutator_le_right _ C₀)
            · calc ⁅C₀.lowerCentralSeries j, C₀⁆
                  ≤ ⁅C₀ ⊓ cs.G_ (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1)), C₀⁆ :=
                    Subgroup.commutator_mono_left ih
                _ ≤ ⁅cs.G_ (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1)), C₀⁆ :=
                    Subgroup.commutator_mono_left inf_le_right
                _ = ⁅C₀, cs.G_ (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1))⁆ :=
                    Subgroup.commutator_comm _ _
                _ ≤ cs.G_ (⟨min (j+1) m, Nat.lt_succ_of_le (Nat.min_le_right (j+1) m)⟩ : Fin (m+1)) :=
                    hstep
          · have hidxj : (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1)) =
                Fin.last m := by
              ext; simp; omega
            have hEm : C₀ ⊓ cs.G_ (⟨min j m, Nat.lt_succ_of_le (Nat.min_le_right j m)⟩ : Fin (m+1)) = ⊥ := by
              rw [hidxj, cs.bot_eq, inf_bot_eq]
            have hbot : C₀.lowerCentralSeries j = ⊥ := le_bot_iff.mp (hEm ▸ ih)
            rw [hbot, Subgroup.commutator_comm, Subgroup.commutator_bot_right]
            exact bot_le
      have hbot : C₀.lowerCentralSeries m = ⊥ := by
        have hh := hidx m
        have hidxm : (⟨min m m, Nat.lt_succ_of_le (Nat.min_le_right m m)⟩ : Fin (m+1)) = Fin.last m := by
          ext; simp
        have hEm : C₀ ⊓ cs.G_ (⟨min m m, Nat.lt_succ_of_le (Nat.min_le_right m m)⟩ : Fin (m+1)) = ⊥ := by
          rw [hidxm, cs.bot_eq, inf_bot_eq]
        rw [hEm] at hh
        exact le_bot_iff.mp hh
      exact (Subgroup.isNilpotent_iff_lowerCentralSeries C₀).mpr ⟨m, hbot⟩
    exact le_fitting hCnorm hCnil

end Work.Fitting
