import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.ZJB.NormalizerConj
import Submission.Work.ZJB.ThompsonWeakClosed
import Submission.Work.ZJB2.Step1.normJLeNormZJProp

namespace Work.ZJB2

open Work.GW2
open Subgroup

/-- If `g⁻¹ Z g` centralizes `J`, then `g J g⁻¹` centralizes `Z`.  (The two subgroups
"swap" their centralizing relation under conjugation.) -/
private theorem pconj_le_centralizer_swap {G : Type*} [Group G] (Z J : Subgroup G) (g : G)
    (h : Work.ZJB.pconj Z g ≤ Subgroup.centralizer (J : Set G)) :
    Work.ZJB.pconj J g⁻¹ ≤ Subgroup.centralizer (Z : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz_conj : g⁻¹ * z * g ∈ Work.ZJB.pconj Z g := by
    rw [Work.ZJB.mem_pconj]
    rw [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]
    exact hz
  have hcent : g⁻¹ * z * g ∈ Subgroup.centralizer (J : Set G) := h hz_conj
  have hyJ : g⁻¹ * y * g ∈ J := by
    have := Work.ZJB.mem_pconj.mp hy
    simpa using this
  have hcomm := (Subgroup.mem_centralizer_iff.mp hcent) (g⁻¹ * y * g) hyJ
  calc z * y = g * ((g⁻¹ * z * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * (g⁻¹ * z * g)) * g⁻¹ := by rw [hcomm]
    _ = y * z := by group

/-- `S` lies in the centralizer of its own centre `Z(S) = S ⊓ C_G(S)`. -/
private theorem self_le_centralizer_ZS {G : Type*} [Group G] (p : ℕ) (S : Sylow p G) :
    (S : Subgroup G) ≤ Subgroup.centralizer (Work.ZJB.ZS (S : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp hz.1 s hs).symm

/-- `pconj J g⁻¹ = g J g⁻¹`, rewritten as a `Subgroup.map`. -/
private theorem pconj_inv_eq_map_conj {G : Type*} [Group G] (J : Subgroup G) (g : G) :
    Work.ZJB.pconj J g⁻¹ = J.map (MulAut.conj g).toMonoidHom := by
  unfold Work.ZJB.pconj
  rw [show MulAut.conj (g⁻¹)⁻¹ = MulAut.conj g by ext x; simp [MulAut.conj_apply]]

theorem step2 (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] :
    Work.ZJB.Step2Prop p G := by
  intro S hI g hconj
  have hconj' : Work.ZJB.pconj (Work.ZJB.ZS (S : Subgroup G)) g ≤ (S : Subgroup G) := by
    intro x hx
    have hw : g * x * g⁻¹ ∈ Work.ZJB.ZS (S : Subgroup G) := Work.ZJB.mem_pconj.mp hx
    have hmem := hconj (g * x * g⁻¹) hw
    rw [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hmem
    exact hmem
  have hZJ : Work.ZJB.pconj (Work.ZJB.ZS (S : Subgroup G)) g ≤ ZJ (S : Subgroup G) :=
    hI g hconj'
  have hZJ_C : Work.ZJB.pconj (Work.ZJB.ZS (S : Subgroup G)) g ≤
      Subgroup.centralizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) :=
    hZJ.trans (ZJ_le_centralizer (S : Subgroup G))
  have hA : Work.ZJB.pconj (Work.GW2.thompsonJ (S : Subgroup G)) g⁻¹ ≤
      Subgroup.centralizer (Work.ZJB.ZS (S : Subgroup G) : Set G) :=
    pconj_le_centralizer_swap _ _ g hZJ_C
  have hB : (S : Subgroup G) ≤ Subgroup.centralizer (Work.ZJB.ZS (S : Subgroup G) : Set G) :=
    self_le_centralizer_ZS p S
  have hVp : IsPGroup p ↥(Work.ZJB.pconj (Work.GW2.thompsonJ (S : Subgroup G)) g⁻¹) := by
    have hJp : IsPGroup p ↥(Work.GW2.thompsonJ (S : Subgroup G)) :=
      S.isPGroup'.to_le (Work.GW2.thompsonJ_le (S : Subgroup G))
    have hmap := hJp.map (MulAut.conj g).toMonoidHom
    rwa [pconj_inv_eq_map_conj]
  obtain ⟨m, hmC, hmconj⟩ :=
    Work.ZJB.exists_mem_normalizer_inv_mul_mem (p := p) S hB hA hVp
  have hmap_le : (Work.GW2.thompsonJ (S : Subgroup G)).map
        (MulAut.conj (m⁻¹ * g)).toMonoidHom ≤ (S : Subgroup G) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    change MulAut.conj (m⁻¹ * g) j ∈ (↑S : Set G)
    have hv : g * j * g⁻¹ ∈ Work.ZJB.pconj (Work.GW2.thompsonJ (S : Subgroup G)) g⁻¹ := by
      rw [Work.ZJB.mem_pconj]
      rw [show g⁻¹ * (g * j * g⁻¹) * (g⁻¹)⁻¹ = j by group]
      exact hj
    have hmem := hmconj (g * j * g⁻¹) hv
    rw [show MulAut.conj (m⁻¹ * g) j = m⁻¹ * (g * j * g⁻¹) * m by
      rw [MulAut.conj_apply]; group]
    exact hmem
  have hnJ : m⁻¹ * g ∈ Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact Work.ZJB.thompsonJ_map_conj_eq_of_le (S : Subgroup G) (m⁻¹ * g) hmap_le
  have hnZJ : m⁻¹ * g ∈ Subgroup.normalizer (ZJ (S : Subgroup G) : Set G) := by
    have hF4 := Work.ZJB2.Step1.normalizer_le_normalizer_inf_centralizer
      (Work.GW2.thompsonJ (S : Subgroup G))
    have := hF4 hnJ
    simpa [Work.GW2.ZJ] using this
  exact ⟨m, m⁻¹ * g, hmC, hnZJ, by group⟩

end Work.ZJB2
