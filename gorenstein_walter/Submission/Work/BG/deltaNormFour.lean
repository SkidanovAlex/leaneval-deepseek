import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_gram
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.Lambda
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.lemma22EvalWK
import Submission.Work.BG.lemma17_iii_dualC2
import Submission.Work.BG.lemma17_iii_lam2Conj
import Submission.Work.BG.centralValue
import Submission.Work.BG.lemma17_ii_aux

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-! ## Structural facts for the `|S| = 4` case (`D.n = 2`)

`H₀/U ≅ S₀` has order `2` (Bender–Glauberman §4), so `Λ = {1, λ₂}` with `λ₂ = lamCF C β₂`
an involution which is `-1` on every non-identity element of `H₀/U`.  These are the inputs
to the computation of `⟨δ_κ, δ_κ⟩ = 4` (identity (4) of §4; `δ_κ = (κ - λ₂κ)^G`). -/

/-- `lamCF` is the same inflation as `lambdaInf`. -/
theorem lamCF_eq_lambdaInf_dnf {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    (β : quotGroup C.P →* ℂˣ) : lamCF C β = lambdaInf C.P β := rfl

/-- **`|H₀/U| = 2` in the `|S| = 4` case.**  `[H₀ : U] = |S₀| = D.n` (`rem31IndexUin`). -/
theorem quotGroup_card_two_dnf {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) (hn : D.n = 2) :
    Nat.card (quotGroup C.P) = 2 := by
  have h1 : (Work.GW2.C16.Uin C).index = D.n := rem31IndexUin D C hC
  have h2 : (Work.GW2.C16.Uin C).index = Nat.card (↥C.P.H0 ⧸ Work.GW2.C16.Uin C) :=
    Subgroup.index_eq_card (Work.GW2.C16.Uin C)
  have h3 : Nat.card (↥C.P.H0 ⧸ Work.GW2.C16.Uin C) = 2 := by rw [← h2, h1, hn]
  exact h3

/-- `λ₂ = lamCF C β₂` takes the value `-1` at `t`. -/
theorem lamCF_two_apply_t_dnf {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    (β₂ : quotGroup C.P →* ℂˣ)
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    lamCF C β₂ C.t = -1 := by
  rw [lamCF_eq_lambdaInf_dnf C β₂, lambdaInf_apply]
  have hx : quotMk C.P C.t ≠ 1 := by
    intro h
    exact C.t_not_mem_U ((QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) C.t).mp h)
  exact (lemma17_iii_dualC2 C.P h2 hβ).2 (quotMk C.P C.t) hx

/-- Schur for the central involution: `κ(t) ≠ 0` for `κ` irreducible. -/
theorem kappa_t_ne_zero_dnf {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Sec2Ctx G) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκ : Work.GW2.C16.IsKappa D C κ) : κ C.t ≠ 0 := by
  obtain ⟨h1, h0⟩ := centralValue C κ hκ.1
  rcases h1 with h | h
  · rw [h]; exact h0
  · rw [h]; exact neg_ne_zero.mpr h0

/-- `λ₂ κ ≠ κ` for irreducible `κ`. -/
theorem lam_two_mul_ne_self_dnf {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Sec2Ctx G) (β₂ : quotGroup C.P →* ℂˣ)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (hκ : Work.GW2.C16.IsKappa D C κ) :
    lamCF C β₂ * κ ≠ κ := by
  intro h
  have h1 : -κ C.t = κ C.t := by
    have h' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ C.t) h
    rw [ClassFunction.mul_apply, lamCF_two_apply_t_dnf C β₂ h2 hβ] at h'
    simpa using h'
  have hzero : κ C.t = 0 := by
    have h2' : (2 : ℂ) * κ C.t = 0 := by
      rw [two_mul]
      exact neg_eq_iff_add_eq_zero.mp h1
    exact (mul_eq_zero.mp h2').resolve_left (by norm_num)
  exact kappa_t_ne_zero_dnf D C κ hκ hzero

/-- `λ₂ = lamCF C β₂` is fixed by `s`-conjugation (Bender–Glauberman Lemma 1.7(iii)). -/
theorem sconj_lam_two_dnf {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    (β₂ : quotGroup C.P →* ℂˣ) (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1) :
    sconj C (lamCF C β₂) = lamCF C β₂ := by
  show conjByH C.P C.s (lamCF C β₂) = lamCF C β₂
  rw [lamCF_eq_lambdaInf_dnf C β₂]
  exact lemma17_iii_lam2Conj C.P h2 hβ C.s

/-- `s`-conjugation commutes with multiplication by `λ₂`. -/
theorem sconj_lam_two_mul_dnf {G : Type} [Group G] [Finite G] (C : Sec2Ctx G)
    (β₂ : quotGroup C.P →* ℂˣ) (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (lamCF C β₂ * ν) = lamCF C β₂ * sconj C ν := by
  have hs : conjByH C.P C.s (lamCF C β₂) = lamCF C β₂ := by
    show sconj C (lamCF C β₂) = lamCF C β₂
    exact sconj_lam_two_dnf C β₂ h2 hβ
  have hconj : ∀ φ ψ : ClassFunction ↥C.P.H0 ℂ,
      conjByH C.P C.s (φ * ψ) = conjByH C.P C.s φ * conjByH C.P C.s ψ := by
    intro φ ψ
    ext h
    simp only [conjByH_apply, ClassFunction.mul_apply]
  show conjByH C.P C.s (lamCF C β₂ * ν) = lamCF C β₂ * conjByH C.P C.s ν
  rw [hconj, hs]

/-! ## The four values of the Brauer–Suzuki `cH` on the pair `(κ, λ₂κ)` -/

theorem cH_kappa_self_dnf {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Sec2Ctx G) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκ : Work.GW2.C16.IsKappa D C κ) : cH C κ κ = 2 := by
  classical
  first
  | (simp only [cH]; rw [if_pos rfl, if_pos hκ.2.2.1.symm]; norm_num)
  | (unfold cH; rw [if_pos rfl, if_pos hκ.2.2.1.symm]; norm_num)
  | (simp [cH, hκ.2.2.1])

theorem cH_kappa_lam_dnf {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Sec2Ctx G) (β₂ : quotGroup C.P →* ℂˣ)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (hκ : Work.GW2.C16.IsKappa D C κ) : cH C κ (lamCF C β₂ * κ) = 0 := by
  classical
  have hn : lamCF C β₂ * κ ≠ κ := lam_two_mul_ne_self_dnf D C β₂ κ h2 hβ hκ
  have hn2 : ¬ (lamCF C β₂ * κ = sconj C κ) := by rw [hκ.2.2.1]; exact hn
  first
  | (simp only [cH]; rw [if_neg hn, if_neg hn2]; ring)
  | (unfold cH; rw [if_neg hn, if_neg hn2]; ring)
  | (simp [cH, hκ.2.2.1, hn])

theorem cH_lam_kappa_dnf {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Sec2Ctx G) (β₂ : quotGroup C.P →* ℂˣ)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (hκ : Work.GW2.C16.IsKappa D C κ) : cH C (lamCF C β₂ * κ) κ = 0 := by
  classical
  have hn : lamCF C β₂ * κ ≠ κ := lam_two_mul_ne_self_dnf D C β₂ κ h2 hβ hκ
  have hs : sconj C (lamCF C β₂ * κ) = lamCF C β₂ * κ := by
    rw [sconj_lam_two_mul_dnf C β₂ h2 hβ, hκ.2.2.1]
  have hn2 : ¬ (κ = sconj C (lamCF C β₂ * κ)) := by rw [hs]; exact Ne.symm hn
  first
  | (simp only [cH]; rw [if_neg (Ne.symm hn), if_neg hn2]; ring)
  | (unfold cH; rw [if_neg (Ne.symm hn), if_neg hn2]; ring)
  | (simp [cH, hs, hn])

theorem cH_lam_self_dnf {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Sec2Ctx G) (β₂ : quotGroup C.P →* ℂˣ)
    (κ : ClassFunction ↥C.P.H0 ℂ)
    (h2 : Nat.card (quotGroup C.P) = 2) (hβ : β₂ ≠ 1)
    (hκ : Work.GW2.C16.IsKappa D C κ) :
    cH C (lamCF C β₂ * κ) (lamCF C β₂ * κ) = 2 := by
  classical
  have hs : sconj C (lamCF C β₂ * κ) = lamCF C β₂ * κ := by
    rw [sconj_lam_two_mul_dnf C β₂ h2 hβ, hκ.2.2.1]
  first
  | (simp only [cH]; rw [if_pos rfl, if_pos hs.symm]; norm_num)
  | (unfold cH; rw [if_pos rfl, if_pos hs.symm]; norm_num)
  | (simp [cH, hs])

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem deltaNormFour {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hC : Work.GW2.C16.Compat D C) (hn : D.n = 2) (β₂ : Work.BG.quotGroup C.P →* ℂˣ)
    (hβ₂ : β₂ ≠ 1) (κ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)
    (hκ : Work.GW2.C16.IsKappa D C κ) :
    OddOrder.RepresentationTheory.ClassFunction.inner (Work.GW2.C16.delta C β₂ κ)
      (Work.GW2.C16.delta C β₂ κ) = 4 := by
  classical
  -- `|H₀/U| = 2`, so `Λ = {1, λ₂}` with `λ₂` an involution, `-1` on `H₀/U ∖ {1}`
  have h2 : Nat.card (quotGroup C.P) = 2 := quotGroup_card_two_dnf D C hC hn
  -- `λ₂κ ∈ Irr(H₀)` and `κ ∼ λ₂κ`
  have hνirr : IsIrreducibleCharacter (lamCF C β₂ * κ) :=
    lambda_mul_irreducible C.P ⟨β₂, rfl⟩ hκ.1
  have hlam : LamEquiv C κ (lamCF C β₂ * κ) := ⟨β₂, rfl⟩
  -- the Brauer–Suzuki Gram matrix
  have hgram := s02_gram C κ (lamCF C β₂ * κ) κ (lamCF C β₂ * κ)
    hκ.1 hνirr hκ.1 hνirr hlam hlam
  change ClassFunction.inner (ind C (κ - lamCF C β₂ * κ)) (ind C (κ - lamCF C β₂ * κ)) = 4
  rw [hgram, cH_kappa_self_dnf D C κ hκ, cH_kappa_lam_dnf D C β₂ κ h2 hβ₂ hκ,
    cH_lam_kappa_dnf D C β₂ κ h2 hβ₂ hκ, cH_lam_self_dnf D C β₂ κ h2 hβ₂ hκ]
  norm_num

end Work.BG
