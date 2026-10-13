import Mathlib
import Submission.Work.WilE2.Ebc.Defs
import Submission.Work.WilE2.Ebc.tube_separation
import Submission.Work.WilE2.Ebc.component_locally_level
import Submission.Work.WilE2.exists_multiplier_of_isCompact_component
import Submission.Work.WilE2.Ebc.exists_zero_in_component

namespace Work.WilE2.Ebc

open Work.WilE2

-- Please declare any auxiliary lemmas in this file as `private` (or with a `_`-prefix) so that
-- they cannot clash with helper names used elsewhere under Submission/Work/WilE2.
--
-- Useful existing facts (imported above):
--  * `Work.WilE2.Ebc.continuous_tubeFun`, `Work.WilE2.Ebc.isClosed_tubeSet`,
--    `Work.WilE2.Ebc.tubeSet_subset_eball` (from `Ebc/tube_separation`), `Work.WilE2.isCompact_eball`,
--    `Work.WilE2.Ebc.isClosed_connectedComponentIn_of_isClosed`;
--  * `Work.WilE2.Ebc.component_locally_level` turns "regular level set" into the local condition
--    required by `Work.WilE2.exists_multiplier_of_isCompact_component`;
--  * `Work.WilE2.exists_multiplier_of_isCompact_component F u hF Γ hne hcomp hsub hopen hgrad`
--    yields `∃ z ∈ Γ, ∃ c, ∀ v, dotProduct u v = c * fderiv ℝ F z v`.

/-- `dotProduct u` evaluated at the `i`-th standard basis vector `Pi.single i 1`. -/
private lemma _dotProduct_single {k : ℕ} (u : Fin k → ℝ) (i : Fin k) :
    dotProduct u (Pi.single i (1 : ℝ)) = u i := by
  simp [dotProduct, Pi.single_apply]

/-- **The main general statement.**  For a `C¹` function `F : ℝᵏ → ℝ` which is regular on its zero
set, whose sublevel set `{F ≤ 0}` is bounded, and for any prescribed slope vector `sl`, the
connected component of `y` in `{F ≤ 0}` contains a point `z` at which `F` vanishes and its gradient
is proportional to the direction `(sl, 1)` with non-zero `i₀`-component.

`Γ := K ∩ {F = 0}`, where `K` is the component of `y`, is a nonempty compact union of connected
components of the regular level set `{F = 0}` (nonemptiness: `exists_zero_in_component`;
the "locally level" property: `component_locally_level`).  Maximising the linear functional
`x ↦ ⟨u, x⟩` on `Γ`, where `u i₀ = 1` and `u j = sl j` for `j ≠ i₀`, Lagrange multipliers give a
point `z ∈ Γ` with `∇F z ∥ u`; reading off the components of this proportionality on the standard
basis vectors yields the claim. -/
private lemma _good_point_general {k : ℕ} (hk : 0 < k) {F : (Fin k → ℝ) → ℝ}
    (hFc : Continuous F) (hF : ContDiff ℝ 1 F)
    (hreg : ∀ z, F z = 0 → fderiv ℝ F z ≠ 0)
    {S : Set (Fin k → ℝ)} (hS : S = {x | F x ≤ 0})
    (hbdd : ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Fin k → ℝ, F x ≤ 0 → ∑ i, (x i) ^ 2 ≤ R)
    {y : Fin k → ℝ} (hy : y ∈ S) (i₀ : Fin k) (sl : Fin k → ℝ) :
    ∃ z ∈ connectedComponentIn S y, F z = 0 ∧
      (∀ j : Fin k, j ≠ i₀ → fderiv ℝ F z (Pi.single j 1)
        = sl j * fderiv ℝ F z (Pi.single i₀ 1)) ∧
      fderiv ℝ F z (Pi.single i₀ 1) ≠ 0 := by
  have hSclosed : IsClosed S := by rw [hS]; exact isClosed_Iic.preimage hFc
  have hy0 : F y ≤ 0 := by rw [hS] at hy; exact hy
  obtain ⟨R, hRnn, hRbdd⟩ := hbdd
  have hSeball : S ⊆ eball k (Real.sqrt R) := by
    intro x hx
    rw [hS] at hx
    rw [mem_eball, Real.sq_sqrt hRnn]
    exact hRbdd x hx
  set K : Set (Fin k → ℝ) := connectedComponentIn S y with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]; exact isClosed_connectedComponentIn_of_isClosed hSclosed y
  have hKcomp : IsCompact K :=
    (isCompact_eball k (Real.sqrt R)).of_isClosed_subset hKclosed
      (subset_trans (by rw [hKdef]; exact connectedComponentIn_subset S y) hSeball)
  set Γ : Set (Fin k → ℝ) := K ∩ {x | F x = 0} with hΓdef
  have hΓsub : Γ ⊆ {x | F x = 0} := by rw [hΓdef]; exact Set.inter_subset_right
  have hZeroClosed : IsClosed {x : Fin k → ℝ | F x = 0} := isClosed_eq hFc continuous_const
  have hΓcomp : IsCompact Γ := by
    rw [hΓdef]; exact hKcomp.inter_right hZeroClosed
  have hΓne : Γ.Nonempty := by
    obtain ⟨z, hzK', hzF⟩ := exists_zero_in_component hk hFc hy0 ⟨R, hRbdd⟩
    refine ⟨z, ?_, hzF⟩
    rw [hKdef, hS]
    exact hzK'
  have hopen : ∀ z ∈ Γ, ∃ ε : ℝ, 0 < ε ∧ ∀ w : Fin k → ℝ, dist w z < ε → F w = 0 → w ∈ Γ := by
    intro z hzΓ
    have hzK : z ∈ K := hzΓ.1
    have hzF : F z = 0 := hzΓ.2
    obtain ⟨e, he, hprop⟩ := component_locally_level F hF hreg z z (mem_connectedComponentIn hzF)
    refine ⟨e, he, fun w hw hwF => ?_⟩
    have hwcomp : w ∈ connectedComponentIn {x : Fin k → ℝ | F x = 0} z := hprop w hw hwF
    have hsub1 : connectedComponentIn {x : Fin k → ℝ | F x = 0} z ⊆ connectedComponentIn S z :=
      (isPreconnected_connectedComponentIn (x := z) (F := {x : Fin k → ℝ | F x = 0})).subset_connectedComponentIn
        (mem_connectedComponentIn hzF)
        (by intro t ht; rw [hS]; exact le_of_eq (connectedComponentIn_subset {x | F x = 0} z ht))
    have hKz : connectedComponentIn S z = K := by
      rw [hKdef]; exact (connectedComponentIn_eq (F := S) hzK).symm
    exact ⟨hKz ▸ hsub1 hwcomp, hwF⟩
  set u : Fin k → ℝ := fun j => if j = i₀ then 1 else sl j with hudef
  have hu_i : dotProduct u (Pi.single i₀ (1 : ℝ)) = 1 := by
    rw [_dotProduct_single]; simp [hudef]
  have hu_j : ∀ j, j ≠ i₀ → dotProduct u (Pi.single j (1 : ℝ)) = sl j := by
    intro j hj; rw [_dotProduct_single]; simp [hudef, hj]
  obtain ⟨z, hzΓ, c, hc⟩ :=
    exists_multiplier_of_isCompact_component F u hF Γ hΓne hΓcomp hΓsub hopen hreg
  have hzK : z ∈ K := hzΓ.1
  have hzF : F z = 0 := hzΓ.2
  have hci : c * fderiv ℝ F z (Pi.single i₀ 1) = 1 := by
    have hh := hc (Pi.single i₀ (1 : ℝ)); rw [hu_i] at hh; exact hh.symm
  have hcne : c ≠ 0 := by intro h; rw [h, zero_mul] at hci; norm_num at hci
  have hderiv_i : fderiv ℝ F z (Pi.single i₀ 1) = c⁻¹ := eq_inv_of_mul_eq_one_right hci
  have hne_i : fderiv ℝ F z (Pi.single i₀ 1) ≠ 0 := by rw [hderiv_i]; exact inv_ne_zero hcne
  have hprop2 : ∀ j, j ≠ i₀ →
      fderiv ℝ F z (Pi.single j 1) = sl j * fderiv ℝ F z (Pi.single i₀ 1) := by
    intro j hj
    have hcj : c * fderiv ℝ F z (Pi.single j 1) = sl j := by
      have hh := hc (Pi.single j (1 : ℝ)); rw [hu_j j hj] at hh; exact hh.symm
    have hX : fderiv ℝ F z (Pi.single j 1) = c⁻¹ * sl j := by
      calc fderiv ℝ F z (Pi.single j 1)
          = c⁻¹ * (c * fderiv ℝ F z (Pi.single j 1)) := by rw [inv_mul_cancel_left₀ hcne]
        _ = c⁻¹ * sl j := by rw [hcj]
    rw [hX, hderiv_i, mul_comm]
  exact ⟨z, hKdef ▸ hzK, hzF, hprop2, hne_i⟩

theorem exists_good_point {k : ℕ} (hk : 0 < k) (φ : (Fin k → ℝ) → ℝ) (hφc : Continuous φ)
    (hφnn : ∀ x, 0 ≤ φ x) {ρ ε : ℝ} (hε : 0 < ε)
    (hreg : ∀ z : Fin k → ℝ,
      Work.WilE2.tubeFun φ ρ ε z = 0 → fderiv ℝ (Work.WilE2.tubeFun φ ρ ε) z ≠ 0)
    (hF : ContDiff ℝ 1 (Work.WilE2.tubeFun φ ρ ε)) (i₀ : Fin k) (sl : Fin k → ℝ)
    {y : Fin k → ℝ} (hy : y ∈ Work.WilE2.tubeSet φ ρ ε) :
    ∃ z ∈ connectedComponentIn (Work.WilE2.tubeSet φ ρ ε) y,
      Work.WilE2.tubeFun φ ρ ε z = 0 ∧
      (∀ j : Fin k, j ≠ i₀ → fderiv ℝ (Work.WilE2.tubeFun φ ρ ε) z (Pi.single j 1)
        = sl j * fderiv ℝ (Work.WilE2.tubeFun φ ρ ε) z (Pi.single i₀ 1)) ∧
      fderiv ℝ (Work.WilE2.tubeFun φ ρ ε) z (Pi.single i₀ 1) ≠ 0 := by
  exact _good_point_general hk (continuous_tubeFun φ hφc ρ ε) hF hreg rfl
    ⟨ρ ^ 2, sq_nonneg ρ, fun x hx => tubeSet_subset_eball hε hφnn hx⟩ hy i₀ sl

end Work.WilE2.Ebc
