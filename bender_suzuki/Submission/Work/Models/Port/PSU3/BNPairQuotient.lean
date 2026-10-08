/-
**The rank-one `(B,N)`-pair of `PSU(3,2^n)` at the quotient level.**

Collects the standard rank-one `(B,N)`-pair data for the group being classified: the Borel
`B̄ = psu3B n`, the unipotent radical `Ū = psu3U n`, the maximal torus `T̄ = psu3T n` and the Weyl
element `w̄ = psu3W n`, with

* `B̄ = Ū ⊔ T̄` and `Ū ⊓ T̄ = ⊥`,
* `T̄ ≤ N(Ū)` and `C_Ū(T̄) = 1`,
* `w̄ ∉ B̄` and `w̄ ∈ N(T̄)`,
* the Suzuki condition `[PSU(3,2^n) : B̄] = |Ū| + 1` and the regularity of `Ū` off the base point.

These feed the abstract rank-one `(B,N)`-pair theorem
`Commons.GroupTheory.BNPair.normalizer_eq_sup_zpowers`, which we use to give a second proof of
`N(T̄) = T̄ ⊔ ⟨w̄⟩` (`normalizer_psu3T_eq_sup_zpowers_via_bnpair`).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.Models.Port.PSU3.Simple
import Submission.Work.Models.Port.PSU3.WeylQuotient
import Submission.Work.Models.Port.SuzukiSetup
import Submission.Work.Models.Port.Commons.GroupTheory.BNPair.normalizer_eq_sup_zpowers
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_mulAut_conj
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.map_inf_eq_map_inf_map_of_ker_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Matrix LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.PSU3

/-! ## The `(B,N)`-pair identities -/

/-- The Weyl element of `PSU(3,2^n)` defined in `Simple.lean` is the image of `suSgM`. -/
lemma psu3W_eq (n : ℕ) : psu3W n = psu3Hom n (suSgM n) := rfl

lemma psu3W_eq_weyl (n : ℕ) : psu3W n = psu3Weyl n := rfl

/-- `B̄ = Ū ⊔ T̄`. -/
theorem psu3B_eq_sup_psu3T (n : ℕ) : psu3B n = psu3U n ⊔ psu3T n := by
  change (suBS n).map (psu3Hom n) =
    (suUS n).map (psu3Hom n) ⊔ (suTS n).map (psu3Hom n)
  rw [suBS_eq_sup, Subgroup.map_sup]

/-- `Ū ⊓ T̄ = ⊥`. -/
theorem psu3U_inf_psu3T (n : ℕ) : psu3U n ⊓ psu3T n = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxU, hxT⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxU
  obtain ⟨t, ht, hxt⟩ := Subgroup.mem_map.mp hxT
  have hker : u * t⁻¹ ∈ (psu3Hom n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxt, mul_inv_cancel]
  have huT : u ∈ suTS n := by
    have h1 : u * t⁻¹ ∈ suTS n := psu3Hom_ker_le_suTS n hker
    have h2 : u = (u * t⁻¹) * t := by group
    rw [h2]
    exact (suTS n).mul_mem h1 ht
  have hu1 : u = 1 := by
    have hmem : u ∈ suUS n ⊓ suTS n := Subgroup.mem_inf.mpr ⟨hu, huT⟩
    rwa [suTS_inf_suUS n, Subgroup.mem_bot] at hmem
  rw [hu1, map_one]

/-- `T̄ ≤ N(Ū)`. -/
theorem psu3T_le_normalizer_psu3U (n : ℕ) :
    psu3T n ≤ Subgroup.normalizer (psu3U n : Set (PSU3Model n)) := by
  intro t ht
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht
  refine Subgroup.le_normalizer_map (psu3Hom n)
    (Subgroup.mem_map.mpr ⟨t₀, suTS_le_normalizer_suUS n ht₀, rfl⟩)

/-- `C_Ū(T̄) = 1`: the only element of `Ū` centralising `T̄` is the identity. -/
theorem centralizer_psu3U_psu3T (n : ℕ) (hn : 2 ≤ n) {u : PSU3Model n} (hu : u ∈ psu3U n)
    (hcent : ∀ t ∈ psu3T n, u * t = t * u) : u = 1 := by
  have hn1 : 1 ≤ n := by omega
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerU : (psu3Hom n).ker ⊓ suUS n = ⊥ := by
    rw [inf_comm]
    exact Commons.GroupTheory.IsPGroup.inf_eq_bot_of_not_dvd_card (p := 2)
      (suUS_isPGroup n hn1)
      (by
        intro h
        exact Nat.not_even_iff_odd.mpr (odd_card_psu3Hom_ker n hn1) (even_iff_two_dvd.mpr h))
  have hcent₀ : ∀ t ∈ suTS n, u₀ * t = t * u₀ := by
    intro t ht
    have htT : psu3Hom n t ∈ psu3T n := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have hcomm := hcent (psu3Hom n t) htT
    have h1 : u₀ * t * u₀⁻¹ * t⁻¹ ∈ (psu3Hom n).ker := by
      rw [MonoidHom.mem_ker]
      have hm : psu3Hom n (u₀ * t * u₀⁻¹ * t⁻¹) = (psu3Hom n) u₀ * (psu3Hom n) t *
          ((psu3Hom n) u₀)⁻¹ * ((psu3Hom n) t)⁻¹ := by
        simp only [map_mul, map_inv]
      rw [hm, hcomm]
      group
    have h2 : u₀ * t * u₀⁻¹ * t⁻¹ ∈ suUS n := by
      have h3 : t * u₀⁻¹ * t⁻¹ ∈ suUS n := by
        have h4 : t * u₀ * t⁻¹ ∈ suUS n :=
          (Subgroup.le_normalizer_iff.mp (suTS_le_normalizer_suUS n)) t ht u₀ hu₀
        have h5 : (t * u₀ * t⁻¹)⁻¹ ∈ suUS n := (suUS n).inv_mem h4
        rwa [show (t * u₀ * t⁻¹)⁻¹ = t * u₀⁻¹ * t⁻¹ by group] at h5
      have h4 : u₀ * (t * u₀⁻¹ * t⁻¹) ∈ suUS n := (suUS n).mul_mem hu₀ h3
      simpa only [mul_assoc] using h4
    have h4 : u₀ * t * u₀⁻¹ * t⁻¹ ∈ (psu3Hom n).ker ⊓ suUS n :=
      Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hkerU, Subgroup.mem_bot] at h4
    have h5 : u₀ * t * u₀⁻¹ = t := by
      calc u₀ * t * u₀⁻¹ = u₀ * t * u₀⁻¹ * t⁻¹ * t := by group
        _ = 1 * t := by rw [h4]
        _ = t := one_mul t
    calc u₀ * t = (u₀ * t * u₀⁻¹) * u₀ := by group
      _ = t * u₀ := by rw [h5]
  have hu1 : u₀ = 1 :=
    eq_one_of_mem_suUS_of_centralizes_suTS (n := n) (hn := hn) (u := u₀) hu₀ hcent₀
  rw [hu1, map_one]

/-- `w̄ ∉ B̄`. -/
theorem psu3W_notMem_psu3B (n : ℕ) : psu3W n ∉ psu3B n := by
  intro h
  obtain ⟨b, hb, hbw⟩ := Subgroup.mem_map.mp h
  have hbw' : psu3Hom n b = psu3Hom n (suSgM n) := hbw
  have hker : suSgM n * b⁻¹ ∈ (psu3Hom n).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hbw', mul_inv_cancel]
  have h1 : suSgM n * b⁻¹ ∈ suTS n := psu3Hom_ker_le_suTS n hker
  have h2 : suSgM n = (suSgM n * b⁻¹) * b := by group
  exact suSgM_notMem_suBS n (h2 ▸ (suBS n).mul_mem (suTS_le_suBS n h1) hb)

/-- **`B̄ ⊓ B̄^w̄ = T̄`.** -/
theorem psu3B_inf_map_conj_psu3W_eq_psu3T (n : ℕ) :
    psu3B n ⊓ (psu3B n).map (MulAut.conj (psu3W n)).toMonoidHom = psu3T n := by
  have hmap : (psu3B n).map (MulAut.conj (psu3W n)).toMonoidHom
      = ((suBS n).map (MulAut.conj (suSgM n)).toMonoidHom).map (psu3Hom n) := by
    rw [show psu3B n = (suBS n).map (psu3Hom n) from rfl, psu3W_eq]
    exact (Commons.GroupTheory.Subgroup.map_mulAut_conj (psu3Hom n) (suBS n) (suSgM n)).symm
  rw [hmap, show psu3B n = (suBS n).map (psu3Hom n) from rfl,
    ← Commons.GroupTheory.Subgroup.map_inf_eq_map_inf_map_of_ker_le (psu3Hom n)
      (psu3Hom_ker_le_borel n), suBS_inf_map_conj_eq n]
  rfl

/-- `w̄ ∈ N(T̄)`. -/
theorem psu3W_mem_normalizer_psu3T (n : ℕ) :
    psu3W n ∈ Subgroup.normalizer (psu3T n : Set (PSU3Model n)) := by
  change psu3Hom n (suSgM n) ∈ _
  refine Subgroup.le_normalizer_map (psu3Hom n)
    (Subgroup.mem_map.mpr ⟨suSgM n, suSgM_mem_normalizer_suTS n, rfl⟩)

/-! ## A second proof of the Weyl theorem, via the abstract rank-one `(B,N)`-pair theorem -/

/-- **The rank-one `(B,N)`-pair relation `N(T̄) = T̄ ⋊ ⟨w̄⟩`**, obtained from the abstract commons
theorem `Commons.GroupTheory.BNPair.normalizer_eq_sup_zpowers` applied to the `(B,N)`-pair data of
`PSU(3,2^n)`. -/
theorem normalizer_psu3T_eq_sup_zpowers_via_bnpair (n : ℕ) (hn : 2 ≤ n) :
    Subgroup.normalizer (psu3T n : Set (PSU3Model n)) =
      psu3T n ⊔ Subgroup.zpowers (psu3W n) := by
  have hn1 : 1 ≤ n := by omega
  refine Commons.GroupTheory.BNPair.normalizer_eq_sup_zpowers (psu3B n) (psu3U n) (psu3T n)
    (psu3W n) (psu3B_eq_sup_psu3T n) (psu3U_inf_psu3T n)
    (psu3T_le_normalizer_psu3U n) (psu3W_notMem_psu3B n)
    (psu3W_mem_normalizer_psu3T n) ?_ ?_ ?_
  · intro u hu hcent
    exact centralizer_psu3U_psu3T n hn hu hcent
  · rw [psu3B_index_eq_one_add_card_psu3U n hn, card_psu3U n hn, Nat.add_comm]
  · intro u hu x hx
    exact Submission.psu3U_fixedPoint_eq_one n hn u hu hx

end Submission.PSU3
