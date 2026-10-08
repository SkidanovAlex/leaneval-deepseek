import Submission.Work.ZassenhausSuzuki.TitsDefs
import Submission.Work.ZassenhausSuzuki.e_tilde_sq_fix_zs
import Submission.Work.ZassenhausSuzuki.mu_self_zs
import Submission.Work.ZassenhausSuzuki.mu_fix_center_zs
import Submission.Work.ZassenhausSuzuki.mu_mul_eq_mu_tilde_zs
import Submission.Work.ZassenhausSuzuki.mu_conj_mul_inv_zs
import Submission.Work.ZassenhausSuzuki.tilde_tilde_center_zs
import Submission.Work.ZassenhausSuzuki.g_g_zs
import Submission.Work.ZassenhausSuzuki.hG_tilde
import Submission.Work.ZassenhausSuzuki.hG_tilde_eq
import Submission.Work.ZassenhausSuzuki.suzukiTitsOfFix
import Submission.Work.ZassenhausSuzuki.odd_m_of_isTitsTheta

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `suzukiTitsProp_live`: `SuzukiTitsProp` from the live leaves

This is the lead's design (`TitsDesign.lean`, `NOTES_LEAD_bs_zs_tits.md`) with every leaf
replaced by its proved sibling in this area (`e_tilde_sq_fix_zs`, `mu_self_zs`,
`mu_fix_center_zs`, `mu_mul_eq_mu_tilde_zs`, `mu_conj_mul_inv_zs`, `tilde_tilde_center_zs`,
`g_g_zs`, `hG_tilde`, …) and the assembly replayed verbatim.  The only declarations imported
from `TitsDesign` used here are `szA_c_eq` and `szA_d_eq` (pure `SzA` algebra, proved there).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.ZassenhausSuzuki.TitsDesign

namespace Work.ZassenhausSuzuki

theorem fixTheta_false_final {G : Type} [Group G] [Finite G] (hGs : IsSimpleGroup G)
    (H Q : Subgroup G) (t : G) (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m) (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ)) (e : Q ≃* SzA (GaloisField 2 m) θ)
    (htorus : ∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
      ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧ e y = SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {lam : GaloisField 2 m} (hfix : θ lam = lam) (h0 : lam ≠ 0) (h1 : lam ≠ 1) : False := by
  classical
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  have hc : (2 : GaloisField 2 m) = 0 := CharP.cast_eq_zero (R := GaloisField 2 m) 2
  set C := szCanon hsplit with hCdef
  set T : Q → Q := szTilde hsplit with hTdef
  have hTC : ∀ x, T x = tildeOf C x := fun x => rfl
  set κ := (e (T (zc e 1))).b with hκ
  -- field facts
  have hinv : lam * lam⁻¹ = 1 := mul_inv_cancel₀ h0
  have hfi : θ lam⁻¹ = lam⁻¹ := by rw [map_inv₀, hfix]
  have h1l : 1 + lam ≠ 0 := fun h => h1 (by linear_combination h - hc)
  have h1li : 1 + lam⁻¹ ≠ 0 := fun h => h1 (by
    have : lam⁻¹ = 1 := by linear_combination h - hc
    simpa using congrArg Inv.inv this)
  have hlli : lam + lam⁻¹ ≠ 0 := fun h => h1 (by
    have h' : lam * (lam + lam⁻¹) = 0 := by rw [h, mul_zero]
    have h'' : (lam + 1) ^ 2 = 0 := by linear_combination h' - hinv + lam * hc
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h''
    linear_combination this - hc)
  -- coordinates of `∼` at the squares of fixed elements
  have hE : ∀ μ : GaloisField 2 m, θ μ = μ → μ ≠ 0 →
      e (T (zc e (μ ^ 2))) = (⟨μ, κ * μ ^ 2⟩ : SzA (GaloisField 2 m) θ) :=
    fun μ hμ hμ0 => e_tilde_sq_fix_zs hsplit hzass hθ1 hθodd htorus hμ hμ0
  have hfix1l : θ (1 + lam) = 1 + lam := by rw [map_add, map_one, hfix]
  have hfix1li : θ (1 + lam⁻¹) = 1 + lam⁻¹ := by rw [map_add, map_one, hfi]
  have hfixlli : θ (lam + lam⁻¹) = lam + lam⁻¹ := by rw [map_add, hfix, hfi]
  -- the central involutions
  set a : Q := zc e (1 ^ 2) with ha
  set b : Q := zc e (lam ^ 2) with hb
  set s : Q := zc e ((1 + lam) ^ 2) with hs
  have hab : a * b = s := by
    apply e.injective
    rw [map_mul, ha, hb, hs, zc_coe, zc_coe, zc_coe]
    ext <;> simp only [SzA.mul_a, SzA.mul_b, map_zero, mul_zero, add_zero]
    all_goals linear_combination (-lam) * hc
  have hcen : ∀ u : GaloisField 2 m, zc e u ∈ Subgroup.center Q := fun u => zc_mem_center e u
  have hinvol : ∀ u : GaloisField 2 m, zc e u * zc e u = 1 := fun u => zc_mul_self e u
  have hne1 : ∀ u : GaloisField 2 m, u ≠ 0 → zc e u ≠ 1 := fun u hu => (zc_ne_one_iff e).mpr hu
  have hlam2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 h0
  have h1l2 : (1 + lam) ^ 2 ≠ 0 := pow_ne_zero 2 h1l
  have ha1 : a ≠ 1 := hne1 _ (by norm_num)
  have hb1 : b ≠ 1 := hne1 _ hlam2
  have hs1 : s ≠ 1 := hne1 _ h1l2
  have hane : a ≠ b := by
    intro h
    have h' := zc_injective e h
    have : (lam + 1) ^ 2 = 0 := by linear_combination -h' + (lam + 1) * hc
    exact h1l (by linear_combination (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this))
  -- P and B
  set P : Q := T b * (T a)⁻¹ with hP
  set B : Q := T s with hB
  have heP : e P = (⟨lam, κ * lam ^ 2⟩ : SzA (GaloisField 2 m) θ) * (⟨1, κ * 1 ^ 2⟩)⁻¹ := by
    rw [hP, map_mul, map_inv, hb, ha, hE lam hfix h0, hE 1 (map_one θ) one_ne_zero]
  have heB : e B = (⟨1 + lam, κ * (1 + lam) ^ 2⟩ : SzA (GaloisField 2 m) θ) := by
    rw [hB, hs, hE (1 + lam) hfix1l h1l]
  -- `c := B⁻¹ P = z_{1+λ}`
  have hcP : B⁻¹ * P = zc e (1 + lam) := by
    apply e.injective
    rw [map_mul, map_inv, heP, heB, zc_coe, szA_c_eq θ κ lam hfix]
  have hP1 : (P : G) ≠ 1 := by
    intro h
    have hP' : P = 1 := Subtype.ext h
    have := hcP; rw [hP', mul_one] at this
    have h2' := congrArg (fun x => (e x).a) this
    simp only [map_inv, heB, SzA.inv_a, zc_coe, CharTwo.neg_eq] at h2'
    exact h1l h2'
  have hB1 : (B : G) ≠ 1 := by
    intro h
    have hB' : B = 1 := Subtype.ext h
    have h2' := congrArg (fun x => (e x).a) hB'
    simp only [heB, map_one, SzA.one_a] at h2'
    exact h1l h2'
  have hPB : P ≠ B := by
    intro h
    have := hcP; rw [h, inv_mul_cancel] at this
    exact hne1 _ h1l this.symm
  -- `h P = h s = h B`
  have hhP : hG C P = hG C s := by
    rw [← hab]
    exact (mu_mul_eq_mu_tilde_zs hsplit hzass h2 C ha1 (hinvol _) (hcen _) hb1 (hinvol _)
      (hcen _) hane).symm ▸ rfl
  have hhB : hG C B = hG C s := hG_tilde_eq hsplit hzass h2 C (fun h => hs1 (Subtype.ext h))
  -- BG 3.1 (l) at `(P, B)`
  have hl := mu_conj_mul_inv_zs hsplit hzass h2 C hP1 hB1 hPB (hhP.trans hhB.symm)
  have hmuB : muPt hsplit C P B = B := by
    rw [muPt_congr hsplit C hhP]
    exact mu_fix_center_zs hsplit hzass h2 C hs1 (hinvol _)
  have hmuP : muPt hsplit C P P = (tildeOf C P⁻¹)⁻¹ := mu_self_zs hsplit hzass h2 C hP1
  rw [hmuB, hmuP] at hl
  -- `∼(P⁻¹)` on the fixed field
  have hPinv : P⁻¹ = T (zc e 1) * (T (zc e (lam ^ 2)))⁻¹ := by
    rw [hP, mul_inv_rev, inv_inv, ha, one_pow]
  have htil : tildeOf C P⁻¹
      = T (zc e ((1 + lam⁻¹) ^ 2)) * (T (zc e ((lam + lam⁻¹) ^ 2)))⁻¹ := by
    have htt := tilde_tilde_center_zs hsplit hzass hθ1 hθodd htorus (u := lam ^ 2) (v := 1) hlam2
      one_ne_zero (fun h => hane (by rw [ha, hb, one_pow, h]))
    rw [← hTdef] at htt
    rw [← hTC, hPinv, htt]
    have e1 : (1 : GaloisField 2 m) + 1 ^ 2 / lam ^ 2 = (1 + lam⁻¹) ^ 2 := by
      field_simp; linear_combination (-lam) * hc
    have e2 : (lam ^ 2 + 1) ^ 2 / lam ^ 2 = (lam + lam⁻¹) ^ 2 := by
      field_simp
    rw [e1, e2]
  -- `d := B⁻¹ (∼(P⁻¹))⁻¹ = z_{λ+λ⁻¹}`
  have hdP : B⁻¹ * (tildeOf C P⁻¹)⁻¹ = zc e (lam + lam⁻¹) := by
    apply e.injective
    rw [htil, map_mul, map_inv, map_inv, map_mul, map_inv, heB,
      hE (1 + lam⁻¹) hfix1li h1li, hE (lam + lam⁻¹) hfixlli hlli, zc_coe,
      szA_d_eq θ κ lam hfix h0]
  rw [hcP, hdP] at hl
  -- `h` is injective on `Z(Q)^#`
  have heq := mu_injOn_center hsplit hzass h2 C (hinvol _) (hinvol _) (hne1 _ hlli)
    (hne1 _ h1l) (by rw [hl])
  have := zc_injective e heq
  apply h1
  have h3 : lam⁻¹ = 1 := by linear_combination this
  simpa using congrArg Inv.inv h3

/-- **`SuzukiTitsProp`**, assembled: `fixTheta_false_final` gives `Fix θ = {0,1}`;
`suzukiTitsOfFix` (proved) gives `θ` or `θ⁻¹` Tits; `odd_m_of_isTitsTheta` (proved) gives
`Odd m`.  (`card_fixTheta_le_six`, `fixTheta_cube_of_split`, `suzukiFixTheta`,
`szClassNumber_fixTheta` all follow from `fixTheta_false_final` by `exact (fixTheta_false_final …).elim`.) -/

theorem suzukiTitsProp_live : SuzukiTitsProp := by
  intro G _ _ hGs H Q t hsplit hzass m θ hθ1 hθodd e htorus
  have hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1 := by
    intro x hx
    by_contra hne
    push Not at hne
    exact fixTheta_false_final hGs H Q t hsplit hzass m θ hθ1 hθodd e htorus hx hne.1 hne.2
  rcases suzukiTitsOfFix hGs H Q t hsplit hzass m θ hθ1 hθodd e htorus hfix with h | h
  · exact ⟨odd_m_of_isTitsTheta h hθodd, Or.inl h⟩
  · exact ⟨odd_m_of_isTitsTheta h (orderOf_inv θ ▸ hθodd), Or.inr h⟩


end Work.ZassenhausSuzuki
