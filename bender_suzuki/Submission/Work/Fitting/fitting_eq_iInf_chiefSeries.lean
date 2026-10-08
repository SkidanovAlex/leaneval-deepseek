import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.fitting_le_sectionCentralizer
import Submission.Work.Fitting.mem_sectionCentralizer_iff_commutator

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Fitting subgroup is the intersection of the centralizers of a chief series

For a finite group `G`, `F(G)` is the intersection of the centralizers `C_G(K/H)` of the
chief factors `K/H` of `G`.  Since a chief series `⊤ = G₀ > G₁ > ⋯ > Gₙ = ⊥` provides a
list of chief factors `Gᵢ/Gᵢ₊₁` containing (up to `G`-isomorphism) every chief factor, this
reads

  `F(G) = ⋂_{i<n} C_G(Gᵢ/Gᵢ₊₁)`

for any chief series `s` of `G` — the statement proved here.

## The argument

* `≤`:  `F(G)` is normal and nilpotent, and a normal nilpotent subgroup centralizes every
  chief factor (`Work.Fitting.fitting_le_sectionCentralizer`), in particular each
  `C_G(Gᵢ/Gᵢ₊₁)`.
* `≥`:  Let `C = ⋂_i C_G(Gᵢ/Gᵢ₊₁)`, a normal subgroup.  It suffices to see that `C` is
  nilpotent, and this is shown by driving the lower central series of `C` down the chief
  series: from `C ≤ C_G(Gᵢ/Gᵢ₊₁)` we get `⁅C, Gᵢ⁆ ≤ Gᵢ₊₁`, whence by induction
  `γ_j(C) ≤ G_j`.  At `j = n` this gives `γ_n(C) ≤ G_n = ⊥`, so `C` is nilpotent.
  (The case `n = 0` forces `⊤ = ⊥`, i.e. `G` trivial, where the claim reads `F(G) = ⊤`.)
-/

noncomputable section

open Classical
open scoped commutatorElement

namespace Work.Fitting

/-- The Fitting subgroup of a subsingleton group is the whole group. -/
theorem fitting_eq_top_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    Work.Fitting.fitting G = ⊤ :=
  le_antisymm le_top (le_fitting Subgroup.normal_top (Group.isNilpotent_of_subsingleton))

theorem fitting_eq_iInf_chiefSeries (G : Type*) [Group G] [Finite G] (s : Work.Fitting.ChiefSeries G) :
    Work.Fitting.fitting G = ⨅ i : Fin s.n,
      @Work.Fitting.sectionCentralizer G _ (s.G_ i.succ) (s.G_ i.castSucc) (s.normal i.succ) := by
  classical
  let f : Fin s.n → Subgroup G := fun i =>
    @Work.Fitting.sectionCentralizer G _ (s.G_ i.succ) (s.G_ i.castSucc) (s.normal i.succ)
  change Work.Fitting.fitting G = ⨅ i : Fin s.n, f i
  refine le_antisymm ?_ ?_
  · refine le_iInf fun i => ?_
    exact @fitting_le_sectionCentralizer G _ _ (s.G_ i.succ) (s.G_ i.castSucc)
      (s.normal i.succ) ⟨s.normal _, s.normal _, s.lt_prev i, s.minimal i⟩
  · rcases Nat.eq_zero_or_pos s.n with hn | hn
    · have h0 : (0 : Fin (s.n + 1)) = Fin.last s.n := Fin.ext hn.symm
      have htop : (⊤ : Subgroup G) = ⊥ := by rw [← s.top_eq, ← s.bot_eq, h0]
      haveI : Subsingleton G := ⟨fun a b => by
        have ha : a = 1 := Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top a)
        have hb : b = 1 := Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top b)
        rw [ha, hb]⟩
      rw [fitting_eq_top_of_subsingleton G]
      exact le_top
    · let C : Subgroup G := ⨅ i : Fin s.n, f i
      change C ≤ Work.Fitting.fitting G
      have hCnorm : C.Normal := by
        refine Subgroup.normal_iInf_normal (a := f) fun i => ?_
        exact @sectionCentralizer_normal G _ (s.G_ i.succ) (s.G_ i.castSucc)
          (s.normal i.succ) (s.normal i.castSucc)
      have hcomm : ∀ i : Fin s.n, ⁅C, s.G_ i.castSucc⁆ ≤ s.G_ i.succ := by
        intro i
        rw [Subgroup.commutator_le]
        intro x hx y hy
        have hmem := (@mem_sectionCentralizer_iff_commutator G _ (s.G_ i.succ) (s.G_ i.castSucc)
          (s.normal i.succ) x).mp (iInf_le f i hx) y hy
        rwa [← commutatorElement_def] at hmem
      let idx : ℕ → Fin (s.n + 1) :=
        fun j => ⟨min j s.n, Nat.lt_succ_of_le (Nat.min_le_right j s.n)⟩
      have hidx : ∀ j : ℕ, C.lowerCentralSeries j ≤ s.G_ (idx j) := by
        intro j
        induction j with
        | zero =>
          rw [Subgroup.lowerCentralSeries_zero]
          have h0 : idx 0 = 0 := by ext; simp [idx]
          rw [h0, s.top_eq]
          exact le_top
        | succ j ih =>
          rw [Subgroup.lowerCentralSeries_succ]
          by_cases hj : j < s.n
          · have hidxj : idx j = (⟨j, hj⟩ : Fin s.n).castSucc := by
              ext; simp [idx, Nat.min_eq_left (le_of_lt hj)]
            have hidxj1 : idx (j + 1) = (⟨j, hj⟩ : Fin s.n).succ := by
              ext; simp [idx, Nat.min_eq_left (Nat.succ_le_of_lt hj)]
            rw [hidxj] at ih
            rw [hidxj1]
            calc ⁅C.lowerCentralSeries j, C⁆
                ≤ ⁅s.G_ (⟨j, hj⟩ : Fin s.n).castSucc, C⁆ :=
                  Subgroup.commutator_mono_left ih
              _ = ⁅C, s.G_ (⟨j, hj⟩ : Fin s.n).castSucc⁆ := Subgroup.commutator_comm _ _
              _ ≤ s.G_ (⟨j, hj⟩ : Fin s.n).succ := hcomm ⟨j, hj⟩
          · push_neg at hj
            have hidxj : idx j = Fin.last s.n := by
              ext; simp [idx, Nat.min_eq_right hj]
            have hbot : C.lowerCentralSeries j = ⊥ := by
              have h := ih
              rw [hidxj, s.bot_eq] at h
              exact le_bot_iff.mp h
            rw [hbot, Subgroup.commutator_bot_left]
            exact bot_le
      have hlast := hidx s.n
      have hidxlast : idx s.n = Fin.last s.n := by ext; simp [idx]
      rw [hidxlast, s.bot_eq] at hlast
      have hCnil : Group.IsNilpotent ↥C :=
        (Subgroup.isNilpotent_iff_lowerCentralSeries C).mpr ⟨s.n, le_bot_iff.mp hlast⟩
      exact le_fitting hCnorm hCnil

end Work.Fitting
