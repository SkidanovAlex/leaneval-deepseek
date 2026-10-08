import Mathlib
import Submission.Work.Frobenius.ThetaIrr
import Submission.Work.Frobenius.Main
import Submission.Work.Frobenius.Induced.ConjChar
import Submission.Work.Frobenius.Induced.conjChar_ne_self_of_fpf
import Submission.Work.Frobenius.Induced.resFun_indFun_eq_sum_conjChar

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `frobenius_induced_irr`

For a Frobenius complement `H ≤ G` with kernel `K` (`Work.Frobenius.frobeniusKernel H`) and a
non-trivial irreducible character `θ ∈ Irr K`, the induced class function `indFun K θ` is an
irreducible character of `G` (Feit–Thompson (3.16)(iii) / Isaacs, Theorem 6.34).

The proof computes `⟨θ^G, θ^G⟩_G = ⟨θ, (θ^G)|_K⟩_K = ∑_{h ∈ H} ⟨θ, θ^h⟩_K = 1`:

* `(θ^G)|_K = ∑_{h ∈ H} θ^h` (`resFun_indFun_eq_sum_conjChar`);
* `⟨θ, θ^h⟩_K` is `1` for `h = 1` and `0` otherwise, because a fixed-point-free automorphism
  of `K` fixes no non-trivial irreducible character (`conjChar_ne_self_of_fpf`);
* `indFun K θ` is a virtual character of norm one (`isVChar_indFun`), hence `±` an irreducible
  character (`vchar_norm_one`), and the negative sign is excluded by positivity of the degree.
-/

@[expose] public section

noncomputable section

open Classical

namespace Work.Frobenius.Induced

variable {G : Type*} [Group G] [Fintype G]

local instance instFintypeSubgroupInduced (H : Subgroup G) : Fintype H := Fintype.ofFinite H

/-- The degree of an induced class function at the identity: `Ind_K^G θ 1 = [G : K] * θ 1`. -/
theorem indFun_apply_one_eq (K : Subgroup G) (θ : K → ℂ) :
    indFun K θ 1 = (K.index : ℂ) * θ 1 := by
  have h1 : ∀ x : G, (if hx : x * 1 * x⁻¹ ∈ K then θ ⟨x * 1 * x⁻¹, hx⟩ else 0) = θ 1 := by
    intro x
    have hx : x * 1 * x⁻¹ ∈ K := by simpa using K.one_mem
    rw [dite_eq_left hx]
    congr 1
    exact Subtype.ext (by simp)
  simp only [indFun, h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  have hcard : (Nat.card K : ℂ) ≠ 0 := by
    simp [Nat.card_eq_fintype_card]
  have hidx : (Nat.card G : ℂ) = (Nat.card K : ℂ) * (K.index : ℂ) := by
    rw [← Subgroup.card_mul_index K, Nat.cast_mul]
  rw [hidx, mul_assoc, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem frobenius_induced_irr {G : Type*} [Group G] [Fintype G] {H K : Subgroup G} (hH : IsFrobeniusComplement H) (hK : (K : Set G) = frobeniusKernel H) {θ : K → ℂ} (hθ : θ ∈ Irr K) (hθ1 : θ ≠ 1) : indFun K θ ∈ Irr G := by
  classical
  haveI hKn : K.Normal := frobenius_normal hH hK
  have hfpf : IsFixedPointFreeOn K H :=
    (frobenius_fpf_iff (frobenius_normal hH hK) (frobenius_inf_eq_bot hH hK)
      (frobenius_sup_eq_top hH hK) hH.ne_bot (kernel_ne_bot hH hK)).mp hH
  have hcomp : Subgroup.IsComplement' K H :=
    (isComplement'_iff K H).mp (frobenius_isComplement' hH hK)
  -- the two inputs: the fixed-point-free action and the restriction formula
  have hkey : ∀ h : H, h ≠ 1 → conjChar K (h : G) θ ≠ θ := by
    intro h hh1
    exact conjChar_ne_self_of_fpf hθ hθ1
      (fun k hk hkeq => hfpf h.2 (fun hc => hh1 (Subtype.ext hc)) hk hkeq)
  have hres : resFun K (indFun K θ) = ∑ h : H, conjChar K h θ :=
    resFun_indFun_eq_sum_conjChar hcomp (irr_isClassFun hθ)
  -- the norm of `indFun K θ` is one
  have hnorm : charPair (indFun K θ) (indFun K θ) = 1 := by
    rw [Induction.charPair_indFun_resFun (φ := θ) (ψ := indFun K θ)
      (Induction.isClassFun_indFun θ)]
    rw [hres, charPair_sum_right]
    trans ∑ h : H, (if conjChar K (h : G) θ = θ then 1 else 0)
    · exact Finset.sum_congr rfl fun h _ => by
        rw [Irr.charPair_irr_eq_ite hθ (conjChar_mem_Irr (h : G) hθ)]
        by_cases hc : conjChar K (h : G) θ = θ
        · simp [hc]
        · have hc' : ¬ (θ = conjChar K (h : G) θ) := fun h' => hc h'.symm
          simp [hc, hc']
    · rw [Finset.sum_eq_single (1 : H)]
      · simp
      · intro h _ hne
        exact if_neg (hkey h hne)
      · intro hnot
        exact absurd (Finset.mem_univ (1 : H)) hnot
  -- `indFun K θ` is a virtual character of norm one, hence `±` irreducible
  have hV : IsVChar (indFun K θ) := isVChar_indFun (AddSubgroup.subset_closure hθ)
  obtain ⟨χ, hχ, hcase⟩ := VChar.vchar_norm_one hV hnorm
  rcases hcase with h | h
  · rw [h]; exact hχ
  · -- the negative case is excluded by positivity of the degree
    exfalso
    obtain ⟨m, hmpos, hm⟩ := character_one_eq_natCast hχ
    obtain ⟨n, hnpos, hn⟩ := character_one_eq_natCast hθ
    have h1 := congrFun h 1
    rw [indFun_apply_one_eq K θ, hn, Pi.neg_apply, hm] at h1
    have hnat : K.index * n + m = 0 := by
      have hcast : ((K.index * n + m : ℕ) : ℂ) = 0 := by
        push_cast
        rw [h1]; ring
      exact_mod_cast hcast
    omega

end Work.Frobenius.Induced
