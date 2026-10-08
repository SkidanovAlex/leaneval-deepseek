/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, §3 leaves)

# BSW §3.6: a `p'`-subgroup of `N_G(X)` with a nontrivial normal prime-power subgroup

Bender (3.6): if `D ≤ N_G(X)` has a nontrivial normal `r`-subgroup (`r ≠ p` a prime) then `D` is
conjugate into `F = C_G(x)` or into `K`.  Indeed `D ≤ N_G(R) ⊓ N_G(X)`, and
`N_G(X) ⊓ N_G(R)` lies in a conjugate of `K` or of `F`.
-/
import Submission.Work.BSW.S3.s36aux
import Submission.Work.BSW.BSW36.normalizer_inf_normalizer_le_conj_K_or_conj_F

namespace Work.BSW.S3

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G} {x : G} {p : ℕ}

/-- If `D ≤ N_G(X)` has a nontrivial normal `r`-subgroup `R` (`r ≠ p` a prime), then some
conjugate of `D` lies in `C_G(x)` or in `K`. -/
theorem conjSub_le_of_normal_pgroup (h : BSWCase2 G t s K x p) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXp : IsPGroup p X) {D R : Subgroup G} (hD : D ≤ Subgroup.normalizer (X : Set G))
    (hRD : R ≤ D) (hRne : R ≠ ⊥) (hRn : ∀ d ∈ D, ∀ r ∈ R, d * r * d⁻¹ ∈ R) {r : ℕ} (hr : r.Prime)
    (hrp : r ≠ p) (hRp : IsPGroup r R) :
    ∃ g, Work.GW2.conjSub g D ≤ Subgroup.centralizer ({x} : Set G) ∨ Work.GW2.conjSub g D ≤ K := by
  have hDNR : D ≤ Subgroup.normalizer (R : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hRn d hd z hz
    · intro hz
      have h := hRn d⁻¹ (D.inv_mem hd) (d * z * d⁻¹) hz
      simpa [mul_assoc] using h
  have hDN : D ≤ Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (R : Set G) :=
    fun z hz => ⟨hD hz, hDNR hz⟩
  rcases Work.BSW.BSW36.normalizer_inf_normalizer_le_conj_K_or_conj_F h hX hXp hr hrp
    (le_trans hRD hD) hRne hRp with ⟨g, hg⟩ | ⟨g, hg⟩
  · exact ⟨g⁻¹, Or.inr (by
      calc Work.GW2.conjSub g⁻¹ D ≤ Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g K) :=
            conjSub_mono (le_trans hDN hg) g⁻¹
        _ = K := by rw [conjSub_conjSub, show g⁻¹ * g = 1 from by group, conjSub_one])⟩
  · exact ⟨g⁻¹, Or.inl (by
      calc Work.GW2.conjSub g⁻¹ D ≤
            Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g (Subgroup.centralizer ({x} : Set G))) :=
            conjSub_mono (le_trans hDN hg) g⁻¹
        _ = Subgroup.centralizer ({x} : Set G) := by
            rw [conjSub_conjSub, show g⁻¹ * g = 1 from by group, conjSub_one])⟩

end Work.BSW.S3
