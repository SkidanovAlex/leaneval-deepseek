import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Dade.defs
import Submission.Work.BrauerSuzuki.Dade.objects
import Submission.Work.BrauerSuzuki.Dade.involution_structure
import Submission.Work.BrauerSuzuki.Dade.main_computation
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.column_orthogonality_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Dade

/-! **Dade's Theorem 6.8 (Brauer–Suzuki for `|S| ≥ 16`)** = `BrauerSuzukiWeakLarge`.

Source: Dade, *Character theory pertaining to finite simple groups* (1971), §6, journal pp. 269–273;
`REFS/brauer_suzuki.md` §2; authoritative transcription `REFS/vision/dade1971/p0022.md`,
`p0023.md`, `p0024.md`, `p0025.md`; the `|S| > 8` case is also in Gorenstein, *Finite Groups*,
Ch. 12.

Setting: `S : Sylow 2 G`, `d : GenQuaternionData ↥S` with `3 ≤ d.n`, `τ = d.tau`, `σ = τ ^ 2`,
`ι = τ ^ (2 ^ (n-1))`, `H = N_G (⟨σ⟩)`.

The proof follows the route of Dade's §6:

* `Dade/complement_and_sqrtSet` (Lemmas 6.9 + 6.10): `H = S K` with `K ⊴ H` of odd order
  centralizing `σ`, and `√σ = ⟨τ⟩ K \ ⟨τ⁴⟩ K`.
* `Quaternion/characters` (6.3)–(6.7): `λ ∈ Irr ↥S` (`1` on `⟨τ⟩`, `−1` off it) and the degree-2
  `θ` with `θ = 0` off `⟨τ⟩`, `θ (τ^i) = i^i + (−i)^i`, and the four-case table for `1 + λ − θ`.
* `Dade/complement_hom`: `φ : H →* ↥S` is the natural map with kernel `K`; `Dade/alpha_facts`
  shows `α := (1 + λ − θ) ∘ φ` is a virtual character of `H`, `α 1 = 0`, `(α,α)_H = 3` and `α`
  vanishes off `√σ`.
* `TI/cfInner_indFun_eq_of_TISet` (Dade 5.19) with `sqrtSet_isTISet` (5.12): `α^G := indFun H α`
  is a virtual character with `(α^G, α^G) = 3`, and by Frobenius reciprocity its principal
  coefficient is `(α, 1)_H = 1`; `Characters/vchar_of_norm_three` (6.11) gives distinct
  non-principal `Λ, Θ ∈ Irr G` and `ε₁, ε₂ = ±1` with `α^G = 1 + ε₁ Λ − ε₂ Θ`.
* `√σ` contains no involution and `1 ∉ √σ` (`Dade/involution_structure`), and `α^G` vanishes off
  `(√σ)^G`, so (6.12): `1 + ε₁ Λ(1) − ε₂ Θ(1) = 0` and `1 + ε₁ Λ(ι) − ε₂ Θ(ι) = 0`.
* A product of two involutions never lies in `√σ` (`involution_structure`), so every value
  `α^G(x y)` with `x, y` in the class `I = ι^G` vanishes; expanding with
  `Characters/sum_sum_char_eq` (`χ(Ĩ²) = (|I| χ(ι))² / χ(1)`) and using (6.12), `Dade/
  main_computation` yields `Λ(ι) = Λ(1)`.
* Then `ι ∈ ker Λ`, a proper normal subgroup of `G`.  Finally all involutions of `G` are
  conjugate to `ι` (`isConj_iota`), so `ker Λ` contains every involution, which is exactly
  `BrauerSuzukiWeakLarge`'s conclusion. -/
theorem main : Work.BrauerSuzuki.BrauerSuzukiWeakLarge := by
  intro G _ _ S d hn
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨Λ, hΛ, hΛ1, hΛι⟩ := iota_eq_degree S d hn
  have hΛclass : Work.CharCore.IsClassFun Λ := Work.CharCore.isClassFun_of_mem_Irr hΛ
  have hΛtop : Work.CharCore.irrKer Λ hΛ ≠ ⊤ := by
    intro htop
    have hconst : ∀ g : G, Λ g = Λ 1 := fun g =>
      (Work.CharCore.mem_irrKer hΛ).mp (htop ▸ Subgroup.mem_top g)
    have hsum1 : Work.CharCore.cfInner Λ (fun _ => (1 : ℂ)) = Λ 1 := by
      rw [Work.CharCore.cfInner_apply]
      have hsum : (∑ g : G, Λ g * starRingEnd ℂ (1 : ℂ)) = ∑ _ : G, Λ 1 := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        rw [hconst g]
        simp
      rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
    have hsum2 : Work.CharCore.cfInner Λ (fun _ => (1 : ℂ)) = 0 := by
      rw [Work.CharCore.irr_orthonormal Λ (fun _ => (1 : ℂ)) hΛ
        (Work.CharCore.principalChar_mem_Irr (G := G))]
      simp [hΛ1]
    have hΛ1zero : Λ 1 = 0 := by rw [← hsum1, hsum2]
    have hΛ1ne : Λ 1 ≠ 0 := by
      rw [Work.CharCore.irrDeg_spec hΛ]
      exact Work.CharCore.irrDeg_ne_zero hΛ
    exact hΛ1ne hΛ1zero
  refine ⟨Work.CharCore.irrKer Λ hΛ, Work.CharCore.irrKer_normal Λ hΛ, hΛtop, ?_⟩
  intro t ht
  rw [Work.CharCore.mem_irrKer]
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_iota S d ht)
  have ht_eq : t = c⁻¹ * iota S d * c := by rw [← hc]; group
  have h1 : Λ (c⁻¹ * iota S d * c) = Λ (iota S d) := by
    simpa using hΛclass (iota S d) c⁻¹
  rw [ht_eq, h1, hΛι]

end Work.BrauerSuzuki.Dade
