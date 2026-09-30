import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic
import Submission.Work.BW.InSub_of_subIdeal
import Submission.Work.BW.hset_zero_cosets_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Every element of `I(G') = subIdeal N ρ ε M` vanishes at the cone point over a point of `G'`. -/
theorem eval_conePt_eq_zero_of_mem_subIdeal {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ)
    {y : Fin (N + 1) → ℂ} (hy : InSub N ρ ε M y) {F : MR N}
    (hF : F ∈ subIdeal N ρ ε M) :
    MvPolynomial.eval (conePt N y) F = 0 := by
  have hle : subIdeal N ρ ε M ≤ RingHom.ker (MvPolynomial.eval (conePt N y)) := by
    rw [subIdeal]
    refine Ideal.span_le.mpr ?_
    rintro Q ⟨-, hQ⟩
    exact RingHom.mem_ker.mpr (hQ y hy)
  exact RingHom.mem_ker.mp (hle hF)

/-- The `G`-points of the zero set of the coset ideal `τ_{f⁻¹}(I(G'))` are exactly the coset
`f · G'`. -/
theorem coset_ZG_cosetIdeal {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ)
    (f : Fin (N + 1) → ℂ) (hf : InG f) :
    ZG (cosetIdeal f ε M) = gmul f '' subSet N ρ ε M := by
  ext v
  constructor
  · intro hv
    rw [ZG] at hv
    obtain ⟨hvG, hv0⟩ := hv
    refine ⟨gmul (ginv f) v, ?_, ?_⟩
    · refine InSub_of_subIdeal ε M (gmul (ginv f) v)
        (hsc_inG_gmul (hsc_inG_ginv hf) hvG) ?_
      intro F hF
      have hF' : transl (ginv f) F ∈ cosetIdeal f ε M := by
        rw [cosetIdeal]
        exact Ideal.mem_map_of_mem _ hF
      have h0 := hv0 _ hF'
      rw [hsc_eval_transl, hsc_coneAct_conePt] at h0
      exact h0
    · rw [← hsc_gmul_assoc, hsc_gmul_ginv_right f hf, hsc_gmul_gone_left]
  · rintro ⟨y, hy, hgy⟩
    rw [← hgy]
    rw [subSet] at hy
    rw [ZG]
    refine ⟨hsc_inG_gmul hf hy.2.1, ?_⟩
    have hle : cosetIdeal f ε M ≤
        RingHom.ker (MvPolynomial.eval (conePt N (gmul f y))) := by
      rw [cosetIdeal, Ideal.map_le_iff_le_comap]
      intro F hF
      show MvPolynomial.eval (conePt N (gmul f y)) (transl (ginv f) F) = 0
      rw [hsc_eval_transl, hsc_coneAct_conePt]
      have hgy' : gmul (ginv f) (gmul f y) = y := by
        rw [← hsc_gmul_assoc, hsc_gmul_ginv_left f hf, hsc_gmul_gone_left]
      rw [hgy']
      exact eval_conePt_eq_zero_of_mem_subIdeal ε M hy hF
    intro F hF
    exact RingHom.mem_ker.mp (hle hF)

end Work.BW
