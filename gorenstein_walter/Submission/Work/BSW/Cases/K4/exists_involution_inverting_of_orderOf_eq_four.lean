import Mathlib
import Submission.Work.BSW.Defs
import Submission.Work.BSW.Cases.K4.Setup

namespace Work.BSW.Cases.K4

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- In the `|K| = 4` case of BSW, an element `d` of order `4` is inverted by an involution outside
`⟨d⟩`: the square `d²` is an involution, hence conjugate to `t`, so `d` is conjugate into
`C_G(t) = K⟨s⟩`, where the elements of order `4` generate `K` and `s` is an involution outside `K`
inverting it.

Sketch (the involution is the conjugate of `s` by the same element that conjugates `d` into `K`):
take `g` with `g * d ^ 2 * g⁻¹ = t` (`Work.BSW.involutions_conj`, `isConj_iff`); put
`y := g * d * g⁻¹`, so `y * y = t`, `orderOf y = 4`, and `y ∈ C_G(t)`.  By
`Work.BSW.Cases.K4.orderOf_dichotomy_of_mem_centralizer_t` and `Work.BSW.Cases.K4.exists_gen_K`,
`y ∈ K` and `⟨y⟩ = K`.  Then `u := g⁻¹ * s * g` satisfies `orderOf u = 2`,
`u * (g⁻¹ * z * g) * u⁻¹ = (g⁻¹ * z * g)⁻¹` for every `z ∈ K` (because `s` inverts `K`), and
`u ∉ ⟨d⟩ = g⁻¹ K g` because `s ∉ K`. -/
theorem exists_involution_inverting_of_orderOf_eq_four {G : Type} [Group G] [Finite G] {t s : G}
    {K : Subgroup G} (h : Work.GW2.BSWHyps2 G t s K) (hK : Nat.card ↥K = 4) (d : G)
    (hd : orderOf d = 4) :
    ∃ u : G, orderOf u = 2 ∧ u ∉ Subgroup.zpowers d ∧
      Work.GW2.Inverts u (Subgroup.zpowers d) := by
  -- `d * d` is an involution, hence conjugate to `t`.
  have hd2 : orderOf (d * d) = 2 := by
    have hh := orderOf_pow (n := 2) d
    rw [hd] at hh
    norm_num at hh
    rwa [pow_two] at hh
  obtain ⟨g, hg⟩ := isConj_iff.mp (Work.BSW.involutions_conj h (d * d) hd2)
  -- `y := g * d * g⁻¹` is an element of order `4` with `y * y = t`.
  set y := g * d * g⁻¹ with hy
  have hyy : y * y = t := by
    rw [hy]
    calc (g * d * g⁻¹) * (g * d * g⁻¹) = g * (d * d) * g⁻¹ := by group
      _ = t := hg
  have hy2 : y ^ 2 = t := by rw [pow_two]; exact hyy
  -- `y` commutes with `t`, since `y * t = y * (y * y) = (y * y) * y = t * y`.
  have hyC : y ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * t = y * (y * y) := by rw [hyy]
      _ = (y * y) * y := by group
      _ = t * y := by rw [hyy]
  -- hence `y ∈ C_G(t) = K ∪ K s`; it cannot lie in the coset `K s`, all of whose elements are
  -- involutions, so `y ∈ K`.
  have hyK : y ∈ K := by
    rcases (Work.BSW.Api.mem_centralizer_iff h y).mp hyC with h1 | ⟨k, hkK, hky⟩
    · exact h1
    · exfalso
      have h1 : y * y = 1 := by rw [hky]; exact Work.BSW.Cases.K4.mul_s_self h hkK
      rw [hyy] at h1
      exact Work.BSW.t_ne_one h h1
  have hy4 : orderOf y = 4 := by
    have hdvd : orderOf y ∣ 4 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      calc y ^ 4 = (y ^ 2) ^ 2 := by rw [show (4:ℕ) = 2*2 by norm_num, pow_mul]
        _ = 1 := by rw [hy2, pow_two, Work.BSW.t_mul_self h]
    have hpow : orderOf y ∣ 2 ^ 2 := by simpa using hdvd
    have hne1 : orderOf y ≠ 1 := by
      intro h1
      have hy1 : y = 1 := orderOf_eq_one_iff.mp h1
      rw [hy1, one_mul] at hyy
      exact Work.BSW.t_ne_one h hyy.symm
    have hne2 : orderOf y ≠ 2 := by
      intro h2
      have h3 : y ^ 2 = 1 := by rw [← h2]; exact pow_orderOf_eq_one y
      rw [hy2] at h3
      exact Work.BSW.t_ne_one h h3
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp hpow
    interval_cases i
    · exact absurd (by simpa using hord) hne1
    · exact absurd (by simpa using hord) hne2
    · simpa using hord
  -- `y` generates `K`, since `|K| = 4 = orderOf y` and `⟨y⟩ ≤ K`.
  have hgen : Subgroup.zpowers y = K := by
    have hle : Subgroup.zpowers y ≤ K := Subgroup.zpowers_le.mpr hyK
    have hcard : Nat.card ↥(Subgroup.zpowers y) = Nat.card ↥K := by
      rw [Nat.card_zpowers, hy4, hK]
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  -- consequently `g ⟨d⟩ g⁻¹ = K`.
  have hconj : (Subgroup.zpowers d).map (MulAut.conj g).toMonoidHom = K := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (g * d * g⁻¹) = K
    rw [← hy]
    exact hgen
  refine ⟨g⁻¹ * s * g, ?_, ?_, ?_⟩
  · -- `g⁻¹ s g` is an involution, as a conjugate of `s`.
    have h1 : g⁻¹ * s * g = (MulAut.conj g⁻¹) s := by rw [MulAut.conj_apply]; group
    rw [h1, MulEquiv.orderOf_eq (MulAut.conj g⁻¹) s, Work.BSW.orderOf_s h]
  · -- `g⁻¹ s g ∉ ⟨d⟩`, since `g (g⁻¹ s g) g⁻¹ = s ∉ K = g ⟨d⟩ g⁻¹`.
    intro hu
    have h1 : (MulAut.conj g).toMonoidHom (g⁻¹ * s * g) ∈ K := by
      have h2 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hu
      rwa [hconj] at h2
    have h2 : (MulAut.conj g).toMonoidHom (g⁻¹ * s * g) = s := by
      change (MulAut.conj g) (g⁻¹ * s * g) = s
      rw [MulAut.conj_apply]; group
    rw [h2] at h1
    exact Work.BSW.s_notMem_K h h1
  · -- `g⁻¹ s g` inverts `⟨d⟩ = g⁻¹ K g`, since `s` inverts `K`.
    intro z hz
    have h1 : (MulAut.conj g).toMonoidHom z ∈ K := by
      have h2 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz
      rwa [hconj] at h2
    have hgz : g * z * g⁻¹ ∈ K := by
      change (MulAut.conj g) z ∈ K at h1
      rwa [MulAut.conj_apply] at h1
    calc (g⁻¹ * s * g) * z * (g⁻¹ * s * g)⁻¹
        = g⁻¹ * (s * (g * z * g⁻¹) * s⁻¹) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹)⁻¹ * g := by rw [Work.BSW.inverts_s_K h (g * z * g⁻¹) hgz]
      _ = z⁻¹ := by group

end Work.BSW.Cases.K4
