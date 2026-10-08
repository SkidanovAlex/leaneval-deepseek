import Mathlib
import Submission.Work.ZassenhausSuzuki.CoreV2
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausSuzuki.szMuCenter
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_mul_ne_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `TitsDefs` — the unproved-free part of the lead's design file `TitsDesign.lean`

The vocabulary and proved helper lemmas of `NOTES_LEAD_bs_zs_tits.md` / `_design/Tits.lean`,
extracted so that the live modules (the leaves and `TitsAssembly`) do not import the design file,
which still contains the 11 leaf `unproved`s as documentation.  Everything here is proved:
`conjH`, `muPt`, `muPt_congr`, `canon_H8` (the `D`-component of `canon_mul`), and the `SzA`
algebra lemmas `szA_c_eq`, `szA_d_eq`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki.TitsDesign

open Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `h(x) · y · h(x)⁻¹ ∈ Q`. -/
noncomputable def conjH (hsplit : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t)
    (x y : Q) : Q :=
  ⟨hG C x * (y : G) * (hG C x)⁻¹, canon_D_conj_Q_mem hsplit (C.h x) y⟩

noncomputable def muPt (hsplit : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t)
    (x y : Q) : Q :=
  C.g (conjH hsplit C x y)

theorem muPt_congr (hsplit : IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t)
    {x x' : Q} (hx : hG C x = hG C x') (y : Q) : muPt hsplit C x y = muPt hsplit C x' y := by
  unfold muPt conjH
  congr 1
  exact Subtype.ext (by simp only [hx])

/-! ## L0  the `h`-product formula (the `D`-component of `canon_mul`) -/

theorem canon_H8 (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) (x₁ x₂ : Q) (hx₁ : (x₁ : G) ≠ 1) (hx₂ : (x₂ : G) ≠ 1)
    (hx₁₂ : ((x₁ * x₂ : Q) : G) ≠ 1) :
    hG C (x₁ * x₂) = hG C x₁ * hG C (C.f x₁ * C.g x₂) * hG C x₂ := by
  have hcx := canon3_of_C hsplit C hx₁
  have hcy := canon3_of_C hsplit C hx₂
  have hz_ne : ((C.f x₁ * C.g x₂ : Q) : G) ≠ 1 :=
    Work.PSU3.RankOne.canon_mul_ne_one hsplit x₁.2 hx₁ x₂.2 hx₂ hcx hcy hx₁₂
  have hcz := canon3_of_C hsplit C hz_ne
  obtain ⟨hg', hd', hy', heq⟩ := Work.PSU3.RankOne.canon_mul hsplit hcx hcy hcz
  have hres := canon3_eq_C hsplit C (y := x₁ * x₂) hx₁₂ (g := ⟨_, hg'⟩) (d := ⟨_, hd'⟩)
    (z := ⟨_, hy'⟩) heq
  exact congrArg Subtype.val hres.2.2

/-! ## L1  first consequences of H1–H6 (all `x ≠ 1`) -/

/-- `c`: `(∼z_{(1+λ)²})⁻¹ · (∼z_{λ²} · (∼z_1)⁻¹) = z_{1+λ}` in coordinates (proved). -/
theorem szA_c_eq {m : ℕ} (θ : GaloisField 2 m ≃+* GaloisField 2 m) (κ lam : GaloisField 2 m)
    (hfix : θ lam = lam) :
    (⟨1 + lam, κ * (1 + lam) ^ 2⟩ : SzA (GaloisField 2 m) θ)⁻¹
        * ((⟨lam, κ * lam ^ 2⟩ : SzA (GaloisField 2 m) θ) * (⟨1, κ * 1 ^ 2⟩)⁻¹)
      = ⟨0, 1 + lam⟩ := by
  have hc : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero (R := GaloisField 2 m) 2
  ext <;> simp only [SzA.mul_a, SzA.mul_b, SzA.inv_a, SzA.inv_b, map_add, map_one,
    hfix, CharTwo.neg_eq]
  · linear_combination (1 + lam) * hc
  · linear_combination (1 + κ + κ * lam + κ * lam ^ 2 + 2 * lam + lam ^ 2) * hc

/-- `d`: `(∼z_{(1+λ)²})⁻¹ · (∼z_{(1+λ⁻¹)²} · (∼z_{(λ+λ⁻¹)²})⁻¹)⁻¹ = z_{λ+λ⁻¹}` (proved). -/
theorem szA_d_eq {m : ℕ} (θ : GaloisField 2 m ≃+* GaloisField 2 m) (κ lam : GaloisField 2 m)
    (hfix : θ lam = lam) (h0 : lam ≠ 0) :
    (⟨1 + lam, κ * (1 + lam) ^ 2⟩ : SzA (GaloisField 2 m) θ)⁻¹
        * ((⟨1 + lam⁻¹, κ * (1 + lam⁻¹) ^ 2⟩ : SzA (GaloisField 2 m) θ)
            * (⟨lam + lam⁻¹, κ * (lam + lam⁻¹) ^ 2⟩)⁻¹)⁻¹
      = ⟨0, lam + lam⁻¹⟩ := by
  have hc : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero (R := GaloisField 2 m) 2
  have hfi : θ lam⁻¹ = lam⁻¹ := by rw [map_inv₀, hfix]
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ h0
  ext <;> simp only [SzA.mul_a, SzA.mul_b, SzA.inv_a, SzA.inv_b, map_add, map_one,
    hfix, hfi, CharTwo.neg_eq]
  · linear_combination (1 + lam + lam⁻¹) * hc
  · linear_combination (κ * (1 + lam + lam * lam⁻¹ + lam ^ 2 + lam⁻¹ + lam⁻¹ ^ 2)
      + 3 * lam + 3 * lam⁻¹ + 2 * lam ^ 2 + 3 * lam⁻¹ ^ 2 + 6) * hc + 9 * hinv


/-! ## Assembly (complete modulo the leaves above) -/

end Work.ZassenhausSuzuki.TitsDesign
