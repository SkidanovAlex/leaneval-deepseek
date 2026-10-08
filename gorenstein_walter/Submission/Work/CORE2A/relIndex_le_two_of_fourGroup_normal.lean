import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihedral_index_two

namespace Work.CORE2A

/-- In a finite group `G` with `S ≤ G` dihedral (`S ≃* DihedralGroup n`, `n ≥ 2`) and `S0 ≤ S`
a cyclic subgroup of index two, any four-group `V ≤ S` which is normalised by `S0` and is
**not** contained in `S0` has index at most two in `S` (in fact then `n ≤ 4`).

Useful auxiliary facts: `Work.CORE2A.dihedral_index_two` gives that every element of `S - S0`
has order `2`; from `(s*r)^2 = 1` one gets `s*r*s = r⁻¹` for `r ∈ S0`, `s ∈ S - S0`, whence
`r*s*r⁻¹ = s*r⁻²` and `r² ∈ V` for every `r ∈ S0`, and then `⟨r₀²⟩ ≤ V ⊓ S0` for a generator
`r₀` of the cyclic `S0` gives `[S0 : V ⊓ S0] ≤ 2`, i.e. `V.relIndex S ≤ 2`. -/
theorem relIndex_le_two_of_fourGroup_normal {G : Type} [Group G] [Finite G]
    (S S0 V : Subgroup G) (n : ℕ) (hn : 2 ≤ n) (hD : Nonempty (↥S ≃* DihedralGroup n))
    (h0le : S0 ≤ S) (hcyc : IsCyclic ↥S0) (hidx : S0.relIndex S = 2)
    (hVle : V ≤ S) (hconj : ∀ r ∈ S0, ∀ v ∈ V, r * v * r⁻¹ ∈ V)
    (hV4 : Work.GW2.IsFourGroup V) (hnot : ¬ V ≤ S0) :
    V.relIndex S ≤ 2 := by
  classical
  obtain ⟨e⟩ := hD
  -- `|S| = 2n`, `|S₀| = n`.
  have hcardS : Nat.card S = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hcardS0 : Nat.card S0 = n := by
    have h := Subgroup.relIndex_mul_card S0 S
    rw [hidx, inf_eq_left.mpr h0le] at h
    rw [hcardS] at h
    exact Nat.mul_left_cancel (by norm_num : (0:ℕ) < 2) h
  -- Pick `s ∈ V` outside `S₀`.
  obtain ⟨s, hsV, hs0⟩ : ∃ s ∈ V, s ∉ S0 := by
    by_contra h
    apply hnot
    intro x hx
    by_contra hx0
    exact h ⟨x, hx, hx0⟩
  have hsS : s ∈ S := hVle hsV
  have hs2 : s ^ 2 = 1 := by
    have h := dihedral_index_two n hn S S0 ⟨e⟩ h0le hcyc hidx s hsS hs0
    simpa [h] using pow_orderOf_eq_one s
  -- Every square of an element of `S₀` lies in `V`.
  have hsq : ∀ r ∈ S0, r ^ 2 ∈ V := by
    intro r hr
    have hrS : r ∈ S := h0le hr
    have hrsS : r * s ∈ S := S.mul_mem hrS hsS
    have hrs0 : r * s ∉ S0 := by
      intro hc
      apply hs0
      have : r⁻¹ * (r * s) ∈ S0 := S0.mul_mem (S0.inv_mem hr) hc
      simpa using this
    have hord : orderOf (r * s) = 2 :=
      dihedral_index_two n hn S S0 ⟨e⟩ h0le hcyc hidx (r * s) hrsS hrs0
    have hrs2 : (r * s) ^ 2 = 1 := by simpa [hord] using pow_orderOf_eq_one (r * s)
    -- `r * s * r = s`, from `(r*s)^2 = 1` and `s^2 = 1`.
    have hrsr : r * s * r = s := by
      have hs2' : s * s = 1 := by simpa [pow_two] using hs2
      have h1 : r * s * r * s = 1 := by simpa [pow_two, mul_assoc] using hrs2
      calc r * s * r = r * s * r * (s * s) := by rw [hs2', mul_one]
        _ = (r * s * r * s) * s := by group
        _ = 1 * s := by rw [h1]
        _ = s := one_mul s
    -- `r * s * r⁻¹ = s * (r^2)⁻¹ ∈ V`, hence `r² ∈ V`.
    have hconjeq : r * s * r⁻¹ = s * (r^2)⁻¹ := by
      calc r * s * r⁻¹ = (r * s * r) * (r^2)⁻¹ := by group
        _ = s * (r^2)⁻¹ := by rw [hrsr]
    have hm : s * (r^2)⁻¹ ∈ V := by
      have h := hconj r hr s hsV
      rwa [hconjeq] at h
    have hm2 : (r^2)⁻¹ ∈ V := by
      have h := V.mul_mem (V.inv_mem hsV) hm
      simpa using h
    have hfin := V.inv_mem hm2
    simpa using hfin
  -- A generator of the cyclic `S₀` gives `n ∣ 4`.
  obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top S0).mp hcyc
  have hgS0 : g ∈ S0 := hg ▸ Subgroup.mem_zpowers g
  have hordg : orderOf g = n := by
    rw [← Nat.card_zpowers g, hg]
    exact hcardS0
  have hg2 : g ^ 2 ∈ V := hsq g hgS0
  have h4 : g ^ 4 = 1 := by
    have h := hV4.2 (g ^ 2) hg2
    rw [show (4:ℕ) = 2 * 2 by norm_num, pow_mul]
    exact h
  have hdvd : n ∣ 4 := by
    rw [← hordg]
    exact orderOf_dvd_iff_pow_eq_one.mpr h4
  have hn4 : n ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  -- `|S| = 2n`, `|V| = 4`, so `V.relIndex S = n/2 ≤ 2`.
  have hrel : V.relIndex S * 4 = 2 * n := by
    have h := Subgroup.relIndex_mul_card V S
    rw [inf_eq_left.mpr hVle] at h
    rw [hV4.1, hcardS] at h
    exact h
  omega

end Work.CORE2A
