import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.cuspThinRegionDefs
import Submission.Work.Mostow.margulisCuspV2
import Submission.Work.Mostow.parabolicCommuteFix

/-!
# Basic invariance and separation of Margulis thin regions

The `G`-action on the thin regions (`cuspThinRegion_smul`, from `smul_mem_cuspThinRegion`) and the
disjointness of the thin regions of two *distinct* parabolic fixed points for a level below the
Margulis threshold (`cuspThinRegion_separation`).  These three lemmas are needed both by the
packing theorem `cuspHoroballsPairwise` and by the proof that a thin region contains a horoball
(`cuspThinRegion_horoball`), so they live in their own module to keep the two independent.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-- Membership form of the `Γ`-action on the thin regions. -/
theorem smul_mem_cuspThinRegion (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (γ : Γ) {ξ : E n} (hξ : ξ ∈ Sph n) (ε : ℝ) (u : E n) :
    (γ : PO n 1) • u ∈ cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε ↔ u ∈ cuspThinRegion Γ ξ ε := by
  have hAk : POBasic n := POBasic.ofProp hA
  have hIk : HypIsoData n := HypIsoData.ofProp hI
  have hinv : bd ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = ξ := by
    have h := hAk.bd_mul ((γ : PO n 1)⁻¹) (γ : PO n 1) ξ hξ
    rw [inv_mul_cancel, hAk.bd_one ξ hξ] at h
    exact h.symm
  have hsmul : ∀ w : E n, (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) = w := by
    intro w
    rw [← hAk.mul_smul, mul_inv_cancel, hAk.one_smul]
  have hsmul' : ∀ w : E n, (γ : PO n 1)⁻¹ • ((γ : PO n 1) • w) = w := by
    intro w
    rw [← hAk.mul_smul, inv_mul_cancel, hAk.one_smul]
  constructor
  · rintro ⟨q, hqpar, hqfix, hqd⟩
    have hmem : (γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1) ∈ Γ :=
      mul_mem (mul_mem (inv_mem γ.2) q.2) γ.2
    refine ⟨⟨(γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1), hmem⟩, ?_, ?_, ?_⟩
    · simpa only [inv_inv] using isParabolic_conj hA hI (γ : PO n 1)⁻¹ (q : PO n 1) hqpar
    · show bd ((γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1)) ξ = ξ
      rw [hAk.bd_mul ((γ : PO n 1)⁻¹ * (q : PO n 1)) (γ : PO n 1) ξ hξ,
        hAk.bd_mul ((γ : PO n 1)⁻¹) (q : PO n 1) (bd (γ : PO n 1) ξ)
          (hAk.bd_mem (γ : PO n 1) ξ hξ), hqfix]
      exact hinv
    · have hconj : ((⟨(γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1), hmem⟩ : Γ) : PO n 1) • u
          = (γ : PO n 1)⁻¹ • ((q : PO n 1) • ((γ : PO n 1) • u)) := by
        calc ((⟨(γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1), hmem⟩ : Γ) : PO n 1) • u
            = ((γ : PO n 1)⁻¹ * (q : PO n 1) * (γ : PO n 1)) • u := rfl
          _ = ((γ : PO n 1)⁻¹ * (q : PO n 1)) • ((γ : PO n 1) • u) := hAk.mul_smul _ _ _
          _ = (γ : PO n 1)⁻¹ • ((q : PO n 1) • ((γ : PO n 1) • u)) := hAk.mul_smul _ _ _
      have hkey : hdist u ((γ : PO n 1)⁻¹ • ((q : PO n 1) • ((γ : PO n 1) • u)))
          = hdist ((γ : PO n 1) • u) ((q : PO n 1) • ((γ : PO n 1) • u)) := by
        rw [← hIk.isom_smul (γ : PO n 1) u
          ((γ : PO n 1)⁻¹ • ((q : PO n 1) • ((γ : PO n 1) • u)))]
        rw [hsmul]
      rw [hconj, hkey]
      exact hqd
  · rintro ⟨q, hqpar, hqfix, hqd⟩
    have hmem : (γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹ ∈ Γ :=
      mul_mem (mul_mem γ.2 q.2) (inv_mem γ.2)
    refine ⟨⟨(γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹, hmem⟩, ?_, ?_, ?_⟩
    · exact isParabolic_conj hA hI (γ : PO n 1) (q : PO n 1) hqpar
    · show bd ((γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ) = bd (γ : PO n 1) ξ
      rw [hAk.bd_mul ((γ : PO n 1) * (q : PO n 1)) ((γ : PO n 1)⁻¹) (bd (γ : PO n 1) ξ)
            (hAk.bd_mem (γ : PO n 1) ξ hξ),
          hinv, hAk.bd_mul (γ : PO n 1) (q : PO n 1) ξ hξ, hqfix]
    · have hconj : ((⟨(γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹, hmem⟩ : Γ) : PO n 1)
            • ((γ : PO n 1) • u) = (γ : PO n 1) • ((q : PO n 1) • u) := by
        calc ((⟨(γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹, hmem⟩ : Γ) : PO n 1) • ((γ : PO n 1) • u)
            = ((γ : PO n 1) * (q : PO n 1) * (γ : PO n 1)⁻¹) • ((γ : PO n 1) • u) := rfl
          _ = ((γ : PO n 1) * (q : PO n 1)) • ((γ : PO n 1)⁻¹ • ((γ : PO n 1) • u)) :=
                hAk.mul_smul _ _ _
          _ = (γ : PO n 1) • ((q : PO n 1) • ((γ : PO n 1)⁻¹ • ((γ : PO n 1) • u))) :=
                hAk.mul_smul _ _ _
          _ = (γ : PO n 1) • ((q : PO n 1) • u) := by rw [hsmul']
      rw [hconj, hIk.isom_smul]
      exact hqd

theorem cuspThinRegion_smul (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (γ : Γ) {ξ : E n} (hξ : ξ ∈ Sph n) (ε : ℝ) :
    (fun u : E n => (γ : PO n 1) • u) '' cuspThinRegion Γ ξ ε
      = cuspThinRegion Γ (bd (γ : PO n 1) ξ) ε := by
  have hAk : POBasic n := POBasic.ofProp hA
  have hsmul : ∀ w : E n, (γ : PO n 1) • ((γ : PO n 1)⁻¹ • w) = w := by
    intro w
    rw [← hAk.mul_smul, mul_inv_cancel, hAk.one_smul]
  apply Set.Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact (smul_mem_cuspThinRegion hA hI Γ γ hξ ε u).mpr hu
  · intro v hv
    refine ⟨(γ : PO n 1)⁻¹ • v, (smul_mem_cuspThinRegion hA hI Γ γ hξ ε ((γ : PO n 1)⁻¹ • v)).mp ?_, ?_⟩
    · rwa [hsmul v]
    · exact hsmul v

/-! ## 2. Separation of distinct thin regions -/

theorem cuspThinRegion_separation (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ξ ∈ parFixed Γ, ∀ η ∈ parFixed Γ, ξ ≠ η →
      Disjoint (cuspThinRegion Γ ξ ε) (cuspThinRegion Γ η ε) := by
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := margulisCuspV2 n hn hA hI 1
  refine ⟨min ε₁ 1, lt_min hε₁pos one_pos, ?_⟩
  intro ξ hξ η hη hne
  rw [Set.disjoint_left]
  intro u hu hu'
  obtain ⟨q, hqpar, hqfix, hqd⟩ := hu
  obtain ⟨q', hq'par, hq'fix, hq'd⟩ := hu'
  have hlt : hdist u ((q : PO n 1) • u) < ε₁ := lt_of_lt_of_le hqd (min_le_left _ _)
  have hle : hdist u ((q' : PO n 1) • u) ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hq'd (min_le_right _ _))
  have hfix : bd (q' : PO n 1) ξ = ξ := hε₁ Γ hdisc u ξ q q' hqpar hξ.1 hqfix hlt hle
  exact hne (pcf_parabolic_fixed_unique hA hI (q' : PO n 1) hq'par ξ η hξ.1 hη.1 hfix hq'fix)

end

end Work.Mostow
