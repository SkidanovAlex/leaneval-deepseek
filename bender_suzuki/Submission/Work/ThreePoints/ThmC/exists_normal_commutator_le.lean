import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

variable {F : Type} [Group F]

/-- The `n`-th term of the derived series of the subgroup `M ≤ F`, computed inside `F`
(so that its `F`-normality and its commutator are visible in the ambient group). -/
def derivSeriesIn (M : Subgroup F) (n : ℕ) : Subgroup F :=
  (derivedSeries ↥M n).map M.subtype

@[simp]
theorem derivSeriesIn_zero (M : Subgroup F) : derivSeriesIn M 0 = M := by
  unfold derivSeriesIn
  rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem derivSeriesIn_succ (M : Subgroup F) (n : ℕ) :
    derivSeriesIn M (n + 1) = ⁅derivSeriesIn M n, derivSeriesIn M n⁆ := by
  unfold derivSeriesIn
  rw [derivedSeries_succ, Subgroup.map_commutator]

theorem derivSeriesIn_le (M : Subgroup F) (n : ℕ) : derivSeriesIn M n ≤ M := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem derivSeriesIn_normal (M : Subgroup F) (hM : M.Normal) (n : ℕ) :
    (derivSeriesIn M n).Normal :=
  @ConjAct.normal_of_characteristic_of_normal F _ M hM (derivedSeries ↥M n) _

theorem derivSeriesIn_bot_of_solvable (M : Subgroup F) (h : Group.IsSolvable ↥M) :
    ∃ N : ℕ, derivSeriesIn M N = ⊥ := by
  obtain ⟨N, hN⟩ := h.solvable
  refine ⟨N, ?_⟩
  unfold derivSeriesIn
  rw [hN, Subgroup.map_bot]

theorem derivSeriesIn_card (M : Subgroup F) (n : ℕ) :
    Nat.card ↥(derivSeriesIn M n) = Nat.card ↥(derivedSeries ↥M n) :=
  Subgroup.card_subtype M (derivedSeries ↥M n)

/-- Let `F` be a finite group, `M ⊴ F` a solvable subgroup of odd order and `H ≤ F` a subgroup with `M ⊄ H`.  Then there is a normal subgroup `Q ⊴ F` with `Q ≤ M`, `Q ⊄ H` and `⁅Q,Q⁆ ≤ H` — namely the last term of the derived series of `M` (computed inside `F`) that is not contained in `H`. -/
theorem exists_normal_commutator_le {F : Type} [Group F] [Finite F] (M H : Subgroup F)
    (hMnorm : M.Normal) (hMsolv : Group.IsSolvable ↥M) (hModd : Odd (Nat.card ↥M))
    (hMH : ¬ M ≤ H) :
    ∃ Q : Subgroup F, Q.Normal ∧ Q ≤ M ∧ ¬ Q ≤ H ∧ ⁅Q,Q⁆ ≤ H ∧ Odd (Nat.card ↥Q) := by
  classical
  obtain ⟨N, hN⟩ := derivSeriesIn_bot_of_solvable M hMsolv
  have hex : ∃ n : ℕ, derivSeriesIn M n ≤ H := ⟨N, by rw [hN]; exact bot_le⟩
  let k := Nat.find hex
  have hkspec : derivSeriesIn M k ≤ H := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, derivSeriesIn_zero] at hkspec
    exact hMH hkspec
  refine ⟨derivSeriesIn M (k - 1), derivSeriesIn_normal M hMnorm (k - 1),
    derivSeriesIn_le M (k - 1), ?_, ?_, ?_⟩
  · exact fun hle => Nat.find_min hex (Nat.pred_lt hk0) hle
  · rw [← derivSeriesIn_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
    exact hkspec
  · rw [derivSeriesIn_card]
    exact Odd.of_dvd_nat hModd
      ⟨_, (Subgroup.card_mul_index (H := derivedSeries ↥M (k - 1))).symm⟩

end Work.ThreePoints.ThmC
