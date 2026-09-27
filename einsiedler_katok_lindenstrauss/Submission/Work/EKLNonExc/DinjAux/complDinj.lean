import Mathlib
import Submission.Work.EKLNonExc.DinjAux.WSets

namespace Work.EKLNonExc
namespace DinjAux

open Work.EKLContract Filter Topology

noncomputable section

theorem complDinj (δ : ℝ) :
    (Work.EKLNonExc.Dinj δ)ᶜ = Work.EKLContract.mkX '' Work.EKLNonExc.DinjAux.Lbad δ := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_compl_iff, Work.EKLNonExc.mem_Dinj] at hx
    push Not at hx
    obtain ⟨g, h, hg, hh, heq, hne⟩ := hx
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective x
    have hkx : mkX k = x := hk
    refine ⟨k, ?_, hkx⟩
    rw [mem_Lbad]
    have hΓ : k⁻¹ * g⁻¹ * h * k ∈ Γ3 := by
      rw [← smul_mkX_eq_iff g h k, hkx]
      exact heq
    refine ⟨⟨k⁻¹ * g⁻¹ * h * k, hΓ⟩, ?_, ?_⟩
    · intro hγ
      have h1 : (k⁻¹ * g⁻¹ * h * k : SL3) = 1 := by
        have := congrArg (Subtype.val : Γ3 → SL3) hγ
        simpa using this
      have h2 : g⁻¹ * h = 1 := by
        calc g⁻¹ * h = k * (k⁻¹ * g⁻¹ * h * k) * k⁻¹ := by group
          _ = k * 1 * k⁻¹ := by rw [h1]
          _ = 1 := by group
      have hgh : h = g := by
        have := congrArg (fun y : SL3 => g * y) h2
        simpa using this
      exact hne hgh.symm
    · have hsimp : k * (↑(⟨k⁻¹ * g⁻¹ * h * k, hΓ⟩ : Γ3)) * k⁻¹ = g⁻¹ * h := by
        group
      rw [hsimp, Wset]
      exact Set.mul_mem_mul (Set.mem_inv.mpr (by simpa using hg)) hh
  · intro hx
    rw [Set.mem_image] at hx
    obtain ⟨k, hkLbad, hkx⟩ := hx
    rw [mem_Lbad] at hkLbad
    obtain ⟨γ, hγne, hγW⟩ := hkLbad
    rw [Wset, Set.mem_mul] at hγW
    obtain ⟨a, ha, b, hb, hab⟩ := hγW
    rw [Set.mem_compl_iff, Work.EKLNonExc.mem_Dinj]
    push Not
    refine ⟨a⁻¹, b, Set.mem_inv.mp ha, hb, ?_, ?_⟩
    · have hΓ : k⁻¹ * (a⁻¹)⁻¹ * b * k ∈ Γ3 := by
        have hval : k⁻¹ * (a⁻¹)⁻¹ * b * k = (γ : SL3) := by
          calc k⁻¹ * (a⁻¹)⁻¹ * b * k = k⁻¹ * (a * b) * k := by group
            _ = k⁻¹ * (k * (γ : SL3) * k⁻¹) * k := by rw [hab]
            _ = (γ : SL3) := by group
        rw [hval]; exact γ.2
      have h1 : a⁻¹ • mkX k = b • mkX k := (smul_mkX_eq_iff a⁻¹ b k).mpr hΓ
      rwa [hkx] at h1
    · intro hab_eq
      have h1 : a * b = 1 := by rw [← hab_eq]; group
      have hkb : k * (γ : SL3) * k⁻¹ = 1 := by rw [← hab]; exact h1
      have hγ1 : (γ : SL3) = 1 := by
        have hthis := congrArg (fun y : SL3 => k⁻¹ * y * k) hkb
        have hg2 : k⁻¹ * (k * (γ : SL3) * k⁻¹) * k = (γ : SL3) := by group
        rw [hg2] at hthis
        simpa using hthis
      exact hγne (Subtype.ext hγ1)

end

end DinjAux
end Work.EKLNonExc
