import Mathlib
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.Reductions.stronglyEmbedded_normalizer_eq
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The hypothesis bundle without `Situation`

`Work.ZassenhausSuzuki.SzHyp` bundles the hypotheses of Suzuki 1962 §8 in the special case
`σ = ρ`: besides the split rank-one Zassenhaus datum `H = Q ⋊ D` with `Q` a `2`-group it
carries `HasFourGroup G` and a distinguished involution `s ∈ Q` with `(s * t) ^ 3 = 1`.

The results needed for the class count (Suzuki 1962 Prop. 13 and its preparatory lemmas) do
not use those two extra items; this file records the weaker bundle they *do* use, with the
same field names (`split`, `zass`, `two`) as `SzHyp`, so that the proofs transfer verbatim.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- The hypotheses used by the class count: split rank-one data `H = Q ⋊ D` with `H` a
Zassenhaus subgroup and `Q` a `2`-group. -/
structure GenHyp (H Q : Subgroup G) (t : G) : Prop where
  split : IsSplitRankOne H Q t
  zass : IsZassenhaus H
  two : IsPGroup 2 Q

/-- An element of order two is an involution. -/
private lemma sq_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [hx] at h
  simpa [pow_two] using h

/-- **`H ⊓ C_G(t) = 1`.**  An element of `H` commuting with `t` lies in `twoPoint H t` (it is
fixed by `t`), and `centD H t = twoPoint H t ⊓ C_G(t) = 1` by the Zassenhaus condition. -/
theorem H_inf_centralizer_t_eq_bot_general (h : GenHyp H Q t) :
    H ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  have hV : centD H t = ⊥ :=
    Work.ZassenhausPSL2.ZData.centD_eq_bot_aux H Q t h.split h.zass
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hcomm : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hmem : x ∈ centD H t := by
    rw [Work.ThreePoints.mem_centD]
    refine ⟨hxH, ?_, hcomm⟩
    have hxt : t * x * t = x := by
      rw [← hcomm]
      calc x * t * t = x * (t * t) := by rw [mul_assoc]
        _ = x := by rw [htt, mul_one]
    rw [htinv, hxt]
    exact hxH
  rw [hV] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- **`(u * t)² ≠ 1` for an involution `u ∈ H`.**  If `(u t)² = 1` then `u` commutes with `t`,
so `u ∈ H ⊓ H^t = twoPoint H t` is an involution in a group of odd order. -/
theorem mul_t_sq_ne_one_general (h : GenHyp H Q t) {u : G}
    (hu : u ∈ Submission.Blueprint.involutions (H : Set G)) :
    (u * t) * (u * t) ≠ 1 := by
  intro hsq
  obtain ⟨huH, hu2⟩ := hu
  have huu : u * u = 1 := sq_eq_one_of_orderOf_eq_two hu2
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have hcomm : u * t = t * u := by
    have h1 : (u * t)⁻¹ = u * t := inv_eq_of_mul_eq_one_right hsq
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right huu, inv_eq_of_mul_eq_one_right htt] at h1
    exact h1.symm
  have hu_eq : u = t * u * t := by
    calc u = u * (t * t) := by rw [htt, mul_one]
      _ = (u * t) * t := by group
      _ = (t * u) * t := by rw [hcomm]
  have hmem : u ∈ Submission.Blueprint.conj t H := by
    rw [Work.ThreePoints.mem_conj_iff']
    exact ⟨u, huH, by rw [inv_eq_of_mul_eq_one_right htt]; exact hu_eq⟩
  have hodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) :=
    h.split.stronglyEmbedded.2.2 t h.split.not_mem
  have hmem2 : u ∈ Submission.Blueprint.twoPoint H t :=
    Subgroup.mem_inf.mpr ⟨huH, hmem⟩
  have hdvd : 2 ∣ Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have h2 := Subgroup.orderOf_dvd_natCard _ hmem2
    rwa [hu2] at h2
  exact Nat.not_even_iff_odd.mpr hodd (even_iff_two_dvd.mpr hdvd)

/-- **`C_G(u * t)` is abelian of odd order and inverted by `t`.**  Since `t` inverts `u * t`
and `(u * t)² ≠ 1`, the involution `t` acts on the odd-order group `C_G(u * t)`; the action is
fixed-point-free (a fixed point commutes with `u`, hence lies in `H ⊓ C_G(t) = 1`), so it is
inversion (Burnside). -/
theorem centralizer_mul_t_inv_general (h : GenHyp H Q t) {u : G}
    (hu : u ∈ Submission.Blueprint.involutions (H : Set G)) :
    (∀ x ∈ Subgroup.centralizer ({u * t} : Set G), t * x * t⁻¹ = x⁻¹) ∧
      IsMulCommutative ↥(Subgroup.centralizer ({u * t} : Set G)) ∧
      Odd (Nat.card ↥(Subgroup.centralizer ({u * t} : Set G))) := by
  obtain ⟨huH, hu2⟩ := hu
  have htt : t * t = 1 := sq_eq_one_of_orderOf_eq_two h.split.invol
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hu_inv : u * u = 1 := sq_eq_one_of_orderOf_eq_two hu2
  have htα : t * (u * t) * t⁻¹ = (u * t)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right htt]
    calc t * (u * t) * t = t * u * (t * t) := by group
      _ = t * u := by rw [htt, mul_one]
      _ = (u * t)⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu_inv,
              inv_eq_of_mul_eq_one_right htt]
  have hfpf : ∀ y : G, y ∈ Subgroup.centralizer ({u * t} : Set G) →
      t * y * t⁻¹ = y → y = 1 := by
    intro y hy hfix
    have hycomm : y * (u * t) = (u * t) * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hyt : y * t = t * y := by
      have h' : t * y = y * t := by
        have hfix' : t * y * t = y := by
          rw [htinv] at hfix
          exact hfix
        calc t * y = (t * y) * (t * t) := by rw [htt, mul_one]
          _ = (t * y * t) * t := by group
          _ = y * t := by rw [hfix']
      exact h'.symm
    have hyu : y * u = u * y := by
      have h1 : (u * t) * t = u := by rw [mul_assoc, htt, mul_one]
      have s1 : y * ((u * t) * t) = (y * (u * t)) * t := by group
      have s2 : (y * (u * t)) * t = ((u * t) * y) * t := by rw [hycomm]
      have s3 : ((u * t) * y) * t = (u * t) * (y * t) := by group
      have s4 : (u * t) * (y * t) = (u * t) * (t * y) := by rw [hyt]
      have s5 : (u * t) * (t * y) = ((u * t) * t) * y := by group
      have s6 : ((u * t) * t) * y = u * y := by rw [h1]
      calc y * u = y * ((u * t) * t) := by rw [h1]
        _ = (y * (u * t)) * t := s1
        _ = ((u * t) * y) * t := s2
        _ = (u * t) * (y * t) := s3
        _ = (u * t) * (t * y) := s4
        _ = ((u * t) * t) * y := s5
        _ = u * y := s6
    have hyH : y ∈ H :=
      Work.ThmF.centralizer_involution_le h.split.stronglyEmbedded huH hu2
        (Subgroup.mem_centralizer_singleton_iff.mpr hyu)
    have hybot : y ∈ H ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hyH, Subgroup.mem_centralizer_singleton_iff.mpr hyt⟩
    rw [H_inf_centralizer_t_eq_bot_general h] at hybot
    exact Subgroup.mem_bot.mp hybot
  have hα2 : (u * t) * (u * t) ≠ 1 := mul_t_sq_ne_one_general h ⟨huH, hu2⟩
  refine ⟨(Work.ZassenhausSuzuki.inv_of_involution_of_fpf htt htα hfpf).1,
    (Work.ZassenhausSuzuki.inv_of_involution_of_fpf htt htα hfpf).2, ?_⟩
  exact (centralizer_abelian_of_strongly_real h.split h.zass h.two hα2
    ⟨u, t, hu_inv, htt, rfl⟩).2.1

end Work.ZassenhausSuzuki
