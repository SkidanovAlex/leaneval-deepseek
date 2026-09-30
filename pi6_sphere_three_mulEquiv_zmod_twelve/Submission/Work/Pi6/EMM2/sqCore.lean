import Mathlib
import Submission.Work.Pi6.EMM2.Statements
import Submission.Work.Pi6.EMM2.SerreKit
import Submission.Work.Pi6.EMM2.K2F9Kit
import Submission.Work.Pi6.EMM2.K4Kit
import Submission.Work.Pi6.EMM2.botEdgeInj

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.EMM2
namespace K2F9

noncomputable section

/-- **The square-nonvanishing step of the `K(ℤ/2,2)` forcing (threshold `9`)**, page level:
for a multiplicative Serre spectral sequence over `𝔽₂` through total degree `6` whose fibre has
`H⁰ = 𝔽₂`, `H¹ = H³ = H⁵ = 0`, `dim H² = dim H⁴ = 1`, whose base has `H⁰ = 𝔽₂`, `H¹ = 0` and
whose total space has `H³ = H⁵ = 0`: every nonzero `y ∈ H³(B)` has `y ⌣ y ≠ 0`.

This is the forcing computation `d₃(w²) = 2w·d₃w = 0`, `d₃(Z·w) = Z·Z' ≠ 0`, `Z' = c·Z` (so
`Z·Z ≠ 0`), transported through `proj 2 (6,0) (Y·Y) = Z·Z` and `e2 (Y·Y) = (y·y) ⊗ 1`. -/
theorem sq_core
    {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ 6)
    (hB0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 0) = 1)
    (hB1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 1))
    (hF0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 0) = 1)
    (hF1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 1))
    (hF2 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 2) = 1)
    (hF3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 3))
    (hF4 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 4) = 1)
    (hF5 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 5))
    (hFinB : ∀ s : ℕ, s ≤ 6 → FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) B s))
    (hFinF : ∀ q : ℕ, q ≤ 6 → FiniteDimensional (ZMod 2)
      (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) q))
    (hE3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) E 3))
    (hE5 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) E 5))
    (hmc : Work.Pi6.EMM2.MulCommStatement) (hco : Work.Pi6.EMM2.CupOneStatement)
    (f : Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 2) (hf : f ≠ 0)
    (hf2 : Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) 2 2 f f ≠ 0)
    (y : Work.Pi6.Coh (ZMod 2) B 3) (hy : y ≠ 0) :
    Work.Pi6.cup (ZMod 2) B 3 3 y y ≠ 0 := by
  classical
  have hS6 : Work.Pi6.IsSerreMSS S p e₀ 6 := hS
  obtain ⟨e2, hmul, hconv0, hconvdim, hbotedge, hcol⟩ := hS
  -- ============ A. basic facts ============
  have honeF : Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀)) ≠ 0 :=
    K2F9.one_ne_zero hco hF0 (hFinF 0 (by norm_num))
  have honeB : Work.Pi6.one (ZMod 2) B ≠ 0 :=
    K2F9.one_ne_zero hco hB0 (hFinB 0 (by norm_num))
  have hfinrank0B1 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 1) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hB1
  have hfinrank0F1 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) 1) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hF1
  have hfinrank0E3 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) E 3) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hE3
  have hfinrank0E5 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) E 5) = 0 :=
    K2F9.finrank_eq_zero_of_isZero hE5
  -- finiteness of the `E₂` page
  have hfdE2 : ∀ (s q : ℕ), s ≤ 6 → q ≤ 6 →
      FiniteDimensional (ZMod 2) (S.E 2 ((s : ℤ), (q : ℤ))) := by
    intro s q hs hq
    haveI := hFinB s hs
    haveI := hFinF q hq
    exact Module.Finite.equiv (e2 s q hs hq).symm.toLinearEquiv
  have hbox : ∀ a : ℤ × ℤ, 0 ≤ a.1 → 0 ≤ a.2 → a.1 + a.2 ≤ (6 : ℤ) →
      FiniteDimensional (ZMod 2) (S.E 2 a) := by
    intro a h1 h2 h3
    obtain ⟨s, hs⟩ : ∃ s : ℕ, a.1 = (s : ℤ) := ⟨a.1.toNat, by omega⟩
    obtain ⟨q, hq⟩ : ∃ q : ℕ, a.2 = (q : ℤ) := ⟨a.2.toNat, by omega⟩
    have hs6 : s ≤ 6 := by omega
    have hq6 : q ≤ 6 := by omega
    have ha : a = ((s : ℤ), (q : ℤ)) := by ext <;> omega
    rw [ha]
    exact hfdE2 s q hs6 hq6
  -- ============ B. the two classes on the `E₂` page ============
  let Y : S.E 2 ((3 : ℤ), (0 : ℤ)) :=
    (e2 3 0 (by omega) (by omega)).inv.hom
      (y ⊗ₜ[ZMod 2] Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀)))
  let W : S.E 2 ((0 : ℤ), (2 : ℤ)) :=
    (e2 0 2 (by omega) (by omega)).inv.hom
      (Work.Pi6.one (ZMod 2) B ⊗ₜ[ZMod 2] f)
  have hYne : Y ≠ 0 :=
    k4_e2_inv_tmul_ne_zero p e₀ S (e2 3 0 (by omega) (by omega)) hy honeF
  have hWne : W ≠ 0 :=
    k4_e2_inv_tmul_ne_zero p e₀ S (e2 0 2 (by omega) (by omega)) honeB hf
  -- ============ C. cycle conditions ============
  have hYcyc : (S.d 2 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 2)).hom Y = 0 := by
    rw [K2F9.d_row0_eq_zero S 2 (by norm_num) 3]
    simp
  have hWcyc : (S.d 2 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 2)).hom W = 0 := by
    have hz : IsZero (S.E 2 (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 2)) :=
      k4_isZero_E2_right p e₀ S 6 hS6 (s := 2) (q := 1) (by omega) (by omega) hF1
    rw [S.d_eq_zero_of_isZero hz]
    simp
  -- ============ D. the dimensions ============
  have hB3le : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 3) ≤ 1 := by
    have hb := finrank_row0_bound S p e₀ 6 hS6 hFinB hFinF hF0 3 (by norm_num)
    have hs : (∑ r ∈ Finset.range (3 - 1),
        Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B (3 - (r + 2))) *
          Module.finrank (ZMod 2)
            (Work.Pi6.Coh (ZMod 2) (Work.StemsB.fibre p (p e₀)) (r + 1))) = 1 := by
      rw [show (3 : ℕ) - 1 = 2 from rfl]
      rw [Finset.sum_range_succ (n := 1), Finset.sum_range_succ (n := 0),
        Finset.sum_range_zero]
      norm_num
      rw [hfinrank0B1, hfinrank0F1, hB0, hF2]
    rw [hfinrank0E3, zero_add, hs] at hb
    exact hb
  have hdim30 : Module.finrank (ZMod 2) (S.E 2 ((3 : ℤ), (0 : ℤ))) ≤ 1 := by
    have h1 : Module.finrank (ZMod 2) (S.E 2 ((3 : ℤ), (0 : ℤ))) =
        Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 3) := by
      have h2 := e2_finrank S p e₀ 6 hS6 3 0 (by norm_num) (by norm_num)
      rw [hF0, mul_one] at h2
      exact h2
    rw [h1]
    exact hB3le
  -- ============ E. `Z`, `w₃`, `Z'` ============
  have hbot_inj : Function.Injective (S.bot 2 3).hom :=
    bot_injective S 2 (by norm_num) 3 (by
      have hz : IsZero (S.E 2 (((3 : ℤ), (0 : ℤ)) - Work.Pi6.vr 2)) :=
        k4_isZero_E2_left p e₀ S 6 hS6 (s := 1) (q := 1) (by omega) (by omega) hB1
      exact hz)
  have hbot_surj : Function.Surjective (S.bot 2 3).hom := by
    intro z
    obtain ⟨w, hw⟩ := S.proj_surj 2 ((3 : ℤ), (0 : ℤ)) (by norm_num) z
    exact ⟨(w : S.E 2 ((3 : ℤ), (0 : ℤ))),
      by rw [show (S.bot 2 3).hom w = S.proj 2 ((3 : ℤ), (0 : ℤ)) w from
        S.bot_spec 2 3 w (by norm_num)]; exact hw⟩
  let Z : S.E 3 ((3 : ℤ), (0 : ℤ)) := (S.bot 2 3).hom Y
  have hZne : Z ≠ 0 := by
    intro h
    exact hYne (hbot_inj (by rw [map_zero]; exact h))
  have hZspec : Z = S.proj 2 ((3 : ℤ), (0 : ℤ)) ⟨Y, hYcyc⟩ :=
    S.bot_spec 2 3 ⟨Y, hYcyc⟩ (by norm_num)
  let w₃ : S.E 3 ((0 : ℤ), (2 : ℤ)) := S.proj 2 ((0 : ℤ), (2 : ℤ)) ⟨W, hWcyc⟩
  let Z' : S.E 3 ((3 : ℤ), (0 : ℤ)) :=
    (S.d 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)).hom w₃
  -- one-dimensionality of `E₃^{3,0}`
  have hdimE3 : Module.finrank (ZMod 2) (S.E 3 ((3 : ℤ), (0 : ℤ))) ≤ 1 := by
    have hiso : S.E 2 ((3 : ℤ), (0 : ℤ)) ≃ₗ[ZMod 2] S.E 3 ((3 : ℤ), (0 : ℤ)) :=
      LinearEquiv.ofBijective (S.bot 2 3).hom ⟨hbot_inj, hbot_surj⟩
    rw [← LinearEquiv.finrank_eq hiso]
    exact hdim30
  haveI hfd30 : FiniteDimensional (ZMod 2) (S.E 2 ((3 : ℤ), (0 : ℤ))) :=
    hfdE2 3 0 (by norm_num) (by norm_num)
  haveI : FiniteDimensional (ZMod 2) (S.E 3 ((3 : ℤ), (0 : ℤ))) := by
    have hiso : S.E 2 ((3 : ℤ), (0 : ℤ)) ≃ₗ[ZMod 2] S.E 3 ((3 : ℤ), (0 : ℤ)) :=
      LinearEquiv.ofBijective (S.bot 2 3).hom ⟨hbot_inj, hbot_surj⟩
    exact FiniteDimensional.of_injective (hiso.symm : S.E 3 ((3 : ℤ), (0 : ℤ)) →ₗ[ZMod 2]
      S.E 2 ((3 : ℤ), (0 : ℤ))) hiso.symm.injective
  obtain ⟨cZ, hcZ⟩ : ∃ c : ZMod 2, Z' = c • Z :=
    K2F9.exists_smul_eq_of_finrank_le_one hdimE3 hZne
  -- ============ F. the product `Y · W` on the `E₂` page ============
  let YW : S.E 2 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) :=
    S.mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) (by ext <;> simp) Y W
  have hYW_eq : YW = (e2 3 2 (by omega) (by omega)).inv.hom (y ⊗ₜ[ZMod 2] f) := by
    have hm := hmul 3 0 0 2 y (Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀)))
      (Work.Pi6.one (ZMod 2) B) f (by omega) (by omega)
    have h1 : Work.Pi6.cup (ZMod 2) B 3 0 y (Work.Pi6.one (ZMod 2) B) = y :=
      (hco (ZMod 2) 3 y).2
    have h2 : Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) 0 2
        (Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀))) f = f :=
      (hco (ZMod 2) 2 f).1
    rw [h1, h2] at hm
    simp only [Nat.mul_zero, pow_zero, one_smul] at hm
    exact hm
  have hYWne : YW ≠ 0 := by
    rw [hYW_eq]
    exact k4_e2_inv_tmul_ne_zero p e₀ S (e2 3 2 (by omega) (by omega)) hy hf
  have hYWcyc : (S.d 2 ((3 : ℤ), (2 : ℤ)) (((3 : ℤ), (2 : ℤ)) + Work.Pi6.vr 2)).hom YW = 0 := by
    have hleib := S.leibniz 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) (by ext <;> simp) Y W (by norm_num)
    rw [hYcyc, hWcyc] at hleib
    simp at hleib
    exact hleib
  -- ============ G. the class `z₁` on `E₃` ============
  let z₁ : S.E 3 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) :=
    S.mul 3 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) (by ext <;> simp) Z w₃
  have hz1 : S.proj 2 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) ⟨YW, hYWcyc⟩ = z₁ := by
    have hp := S.proj_mul 2 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) (by ext <;> simp) ⟨Y, hYcyc⟩ ⟨W, hWcyc⟩
      ⟨YW, hYWcyc⟩ (by norm_num) rfl
    rw [← hZspec] at hp
    exact hp
  have hz1ne : z₁ ≠ 0 := by
    have hinj := K2F9.proj_injective S 2 (by norm_num)
      (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) (by
        have hz : IsZero (S.E 2 (((3 : ℤ), (2 : ℤ)) - Work.Pi6.vr 2)) :=
          k4_isZero_E2_left p e₀ S 6 hS6 (s := 1) (q := 3) (by omega) (by omega) hB1
        exact hz)
    intro h
    refine hYWne ?_
    have h1 : (⟨YW, hYWcyc⟩ : ↥(LinearMap.ker (S.d 2 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))
        ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 2)).hom)) = 0 := by
      refine hinj ?_
      rw [hz1, h, map_zero]
    exact congrArg Subtype.val h1
  -- ============ H. `E₇^{3,2} = 0` ============
  have hE7 : IsZero (S.E 7 ((3 : ℤ), (2 : ℤ))) := by
    have hsum := hconvdim 5 (by norm_num)
    rw [hfinrank0E5] at hsum
    have hterm : Module.finrank (ZMod 2) (S.E 7 ((3 : ℤ), ((5 - 3 : ℕ) : ℤ))) = 0 :=
      (Finset.sum_eq_zero_iff.mp hsum) 3 (Finset.mem_range.mpr (by norm_num))
    haveI : FiniteDimensional (ZMod 2) (S.E 7 ((3 : ℤ), (2 : ℤ))) :=
      CohSS.finiteDimensional_E S 6 hbox 5 ((3 : ℤ), (2 : ℤ)) (by norm_num) (by norm_num)
        (by norm_num)
    haveI : Subsingleton (S.E 7 ((3 : ℤ), (2 : ℤ))) := K2F9.isZero_of_finrank_eq_zero hterm
    exact ModuleCat.isZero_of_subsingleton _
  -- ============ I. the incoming column `E₃^{0,4}` is killed by `d₃` ============
  have hP : ((0 : ℤ), (2 : ℤ)) + ((0 : ℤ), (2 : ℤ)) =
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) := by ext <;> simp
  let WW : S.E 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) :=
    S.mul 2 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) hP W W
  have hWW_eq : WW = (e2 0 4 (by omega) (by omega)).inv.hom
      (Work.Pi6.one (ZMod 2) B ⊗ₜ[ZMod 2]
        Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) 2 2 f f) := by
    have hm := hmul 0 2 0 2 (Work.Pi6.one (ZMod 2) B) f (Work.Pi6.one (ZMod 2) B) f
      (by omega) (by omega)
    have h1 : Work.Pi6.cup (ZMod 2) B 0 0 (Work.Pi6.one (ZMod 2) B)
        (Work.Pi6.one (ZMod 2) B) = Work.Pi6.one (ZMod 2) B :=
      (hco (ZMod 2) 0 (Work.Pi6.one (ZMod 2) B)).2
    rw [h1] at hm
    simp only [Nat.mul_zero, pow_zero, one_smul] at hm
    exact hm
  have hWWne : WW ≠ 0 := by
    rw [hWW_eq]
    exact k4_e2_inv_tmul_ne_zero p e₀ S (e2 0 4 (by omega) (by omega)) honeB
      (by rw [Work.Pi6.cup]; exact hf2)
  have hWWcyc : (S.d 2 ((0 : ℤ), (4 : ℤ)) (((0 : ℤ), (4 : ℤ)) + Work.Pi6.vr 2)).hom WW = 0 := by
    have hleib := S.leibniz 2 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) hP W W (by norm_num)
    rw [hWcyc] at hleib
    simp at hleib
    exact hleib
  let w₄ : S.E 3 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) :=
    S.proj 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) ⟨WW, hWWcyc⟩
  have hw₄_eq : w₄ = S.mul 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) hP w₃ w₃ := by
    have hp := S.proj_mul 2 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) hP ⟨W, hWcyc⟩ ⟨W, hWcyc⟩
      ⟨WW, hWWcyc⟩ (by norm_num) rfl
    exact hp
  have hw₄ne : w₄ ≠ 0 := by
    have hinj := K2F9.proj_injective S 2 (by norm_num)
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) (by
        have hz : IsZero (S.E 2 ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) - Work.Pi6.vr 2)) :=
          S.quad 2 _ (Or.inl (by simp [Work.Pi6.vr]))
        exact hz)
    intro h
    refine hWWne ?_
    have h1 : (⟨WW, hWWcyc⟩ : ↥(LinearMap.ker (S.d 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))
        ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 2)).hom)) = 0 := by
      refine hinj ?_
      rw [show (S.proj 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) ⟨WW, hWWcyc⟩) = w₄ from rfl,
        h, map_zero]
    exact congrArg Subtype.val h1
  have hdim04 : Module.finrank (ZMod 2) (S.E 3 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))) ≤ 1 := by
    have hsurj := S.proj_surj 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) (by norm_num)
    haveI : FiniteDimensional (ZMod 2) (S.E 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))) := by
      have hc : (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) = (((0 : ℤ)), ((4 : ℤ))) := by
        ext <;> simp
      rw [hc]
      exact hfdE2 0 4 (by norm_num) (by norm_num)
    have h1 : Module.finrank (ZMod 2) (S.E 3 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))) ≤
        Module.finrank (ZMod 2) ↥(LinearMap.ker (S.d 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))
          ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 2)).hom) :=
      LinearMap.finrank_le_finrank_of_surjective hsurj
    have h2 : Module.finrank (ZMod 2) ↥(LinearMap.ker (S.d 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))
          ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 2)).hom) ≤
        Module.finrank (ZMod 2) (S.E 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))) :=
      Submodule.finrank_le _
    have h3 : Module.finrank (ZMod 2) (S.E 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))) = 1 := by
      have hc : (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) = (((0 : ℤ)), ((4 : ℤ))) := by
        ext <;> simp
      rw [hc]
      have h4 := e2_finrank S p e₀ 6 hS6 0 4 (by norm_num) (by norm_num)
      rw [hB0, hF4, one_mul] at h4
      exact h4
    omega
  have hd3w₄ : (S.d 3 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))
      ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)).hom
      (S.mul 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ))
        (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) hP w₃ w₃) = 0 := by
    have hleib := S.leibniz 3 ((0 : ℤ), (2 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) hP w₃ w₃ (by norm_num)
    have hsq : (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3) + ((0 : ℤ), (2 : ℤ)) =
        ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) := by rw [← hP]; abel
    have hsq' : ((0 : ℤ), (2 : ℤ)) + (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3) =
        ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) := by rw [← hP]; abel
    have hcomm := hmc p e₀ 6 S hS6 3 (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3) ((0 : ℤ), (2 : ℤ))
      ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hsq Z' w₃ (by norm_num)
      (by simp [Work.Pi6.vr]) (by simp [Work.Pi6.vr]) (by simp) (by simp)
      (by simp [Work.Pi6.vr]) (by simp [Work.Pi6.vr])
    rw [hcomm] at hleib
    have hconv : S.mul 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
        ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
        (by rw [← hsq]; abel) w₃ Z' =
      S.mul 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
        ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hsq' w₃ Z' :=
      S.mul_congr 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
        ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
        (by rw [← hsq]; abel) hsq' w₃ Z'
    rw [hconv] at hleib
    have hsign : (-1 : ZMod 2) ^ (((0 : ℤ), (2 : ℤ)).1 + ((0 : ℤ), (2 : ℤ)).2).natAbs = 1 := by
      simp <;> decide
    set_option backward.isDefEq.respectTransparency false in set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in set_option backward.isDefEq.respectTransparency.types false in
    rw [hsign, one_smul] at hleib
    have htwo : S.mul 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
          ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hsq' w₃ Z'
        + S.mul 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
          ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hsq' w₃ Z' = 0 := by
      rw [← two_smul (ZMod 2) (S.mul 3 ((0 : ℤ), (2 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
          ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hsq' w₃ Z')]
      rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
    rw [htwo] at hleib
    exact hleib
  have hd3zero : ∀ x : S.E 3 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)),
      (S.d 3 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))
        ((((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)).hom x = 0 := by
    haveI : FiniteDimensional (ZMod 2) (S.E 3 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))) := by
      haveI : FiniteDimensional (ZMod 2) (S.E 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ))) := by
        have hc : (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) = (((0 : ℤ)), ((4 : ℤ))) := by
          ext <;> simp
        rw [hc]
        exact hfdE2 0 4 (by norm_num) (by norm_num)
      exact FiniteDimensional.of_surjective (S.proj 2 _)
        (S.proj_surj 2 (((0 + 0 : ℕ) : ℤ), ((2 + 2 : ℕ) : ℤ)) (by norm_num))
    intro x
    obtain ⟨cc, hcx⟩ := K2F9.exists_smul_eq_of_finrank_le_one hdim04 hw₄ne (x := x)
    rw [hcx, map_smul, hw₄_eq, hd3w₄, smul_zero]
  -- ============ J. `E₄^{3,2} = 0` and `d₃ z₁ ≠ 0` ============
  have hE4zero : IsZero (S.E 4 ((3 : ℤ), (2 : ℤ))) := by
    have aux : ∀ r : ℕ, 4 ≤ r → r ≤ 6 → IsZero (S.E (r + 1) ((3 : ℤ), (2 : ℤ))) →
        IsZero (S.E r ((3 : ℤ), (2 : ℤ))) := by
      intro r hr4 hr6 hnext
      haveI : Subsingleton (S.E (r + 1) ((3 : ℤ), (2 : ℤ))) :=
        ModuleCat.subsingleton_of_isZero hnext
      have hinj : Function.Injective (S.proj r ((3 : ℤ), (2 : ℤ))) := by
        refine K2F9.proj_injective S r (by omega) _ ?_
        exact S.quad r (((3 : ℤ), (2 : ℤ)) - Work.Pi6.vr r)
          (Or.inl (by simp [Work.Pi6.vr]; omega))
      have hzero : ∀ x : S.E r ((3 : ℤ), (2 : ℤ)), x = 0 := by
        intro x
        have hx : (S.d r ((3 : ℤ), (2 : ℤ)) (((3 : ℤ), (2 : ℤ)) + Work.Pi6.vr r)).hom x = 0 := by
          rw [S.d_eq_zero_of_isZero (S.quad r _ (Or.inr (by simp [Work.Pi6.vr]; omega)))]
          simp
        have h2 : (⟨x, hx⟩ : ↥(LinearMap.ker (S.d r ((3 : ℤ), (2 : ℤ))
            (((3 : ℤ), (2 : ℤ)) + Work.Pi6.vr r)).hom)) = 0 := by
          refine hinj ?_
          rw [map_zero]
          exact Subsingleton.elim _ _
        exact congrArg Subtype.val h2
      rw [ModuleCat.isZero_iff_subsingleton]
      exact ⟨fun x y => by rw [hzero x, hzero y]⟩
    exact aux 4 (by norm_num) (by norm_num) (aux 5 (by norm_num) (by norm_num)
      (aux 6 (by norm_num) (by norm_num) hE7))
  have hd3z₁ : (S.d 3 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))
      ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)).hom z₁ ≠ 0 := by
    intro hzero
    have hmem : z₁ ∈ LinearMap.range (S.d 3
        ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) - Work.Pi6.vr 3)
        (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))).hom := by
      haveI : Subsingleton (S.E (3 + 1) (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))) :=
        ModuleCat.subsingleton_of_isZero hE4zero
      have h1 : S.proj 3 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))
          (⟨z₁, hzero⟩ : ↥(LinearMap.ker (S.d 3 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))
            ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)).hom)) = 0 :=
        Subsingleton.elim _ _
      exact (S.proj_ker 3 _ (by norm_num) _).mp h1
    obtain ⟨x, hx⟩ := hmem
    have hx0 : (S.d 3 ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) - Work.Pi6.vr 3)
        (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))).hom x = 0 :=
      hd3zero x
    exact hz1ne (by rw [← hx]; exact hx0)
  -- ============ K. `Z · Z ≠ 0` ============
  have hQ : ((3 : ℤ), (0 : ℤ)) + ((0 : ℤ), (2 : ℤ)) =
      (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) := by ext <;> simp
  have hQv : ((3 : ℤ), (0 : ℤ)) + ((3 : ℤ), (0 : ℤ)) =
      ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) := by
    ext <;> simp [Work.Pi6.vr]
  let ZZ : S.E 3 ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) :=
    S.mul 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
      ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hQv Z Z
  let ZZ' : S.E 3 ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) :=
    S.mul 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
      ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hQv Z Z'
  have hsign : (-1 : ZMod 2) ^ (((3 : ℤ), (0 : ℤ)).1 + ((3 : ℤ), (0 : ℤ)).2).natAbs = 1 := by
    simp <;> decide
  have hd3z1 : (S.d 3 (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ))
      ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)).hom z₁ = ZZ' := by
    have hleib := S.leibniz 3 ((3 : ℤ), (0 : ℤ)) ((0 : ℤ), (2 : ℤ))
      (((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) hQ Z w₃ (by norm_num)
    have hdZ : (S.d 3 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 3)).hom Z = 0 := by
      rw [S.d_eq_zero_of_isZero (S.quad 3 _ (Or.inr (by simp [Work.Pi6.vr])))]
      simp
    have hconvB : S.mul 3 ((3 : ℤ), (0 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
        ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
        (by rw [← hQ]; abel) Z Z' =
      S.mul 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
        ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hQv Z Z' :=
      (S.mul_congr 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
        ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
        (by rw [← hQ]; abel) hQv Z Z').trans rfl
    have hA : S.mul 3 (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 3) ((0 : ℤ), (2 : ℤ))
        ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
        (by rw [← hQ]; abel)
        ((S.d 3 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 3)).hom Z) w₃ = 0 := by
      rw [hdZ, map_zero, LinearMap.zero_apply]
    have hB : (-1 : ZMod 2) ^ (((3 : ℤ), (0 : ℤ)).1 + ((3 : ℤ), (0 : ℤ)).2).natAbs •
        S.mul 3 ((3 : ℤ), (0 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
          ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
          (by rw [← hQ]; abel) Z Z'
        = (-1 : ZMod 2) ^ (((3 : ℤ), (0 : ℤ)).1 + ((3 : ℤ), (0 : ℤ)).2).natAbs • ZZ' :=
      congrArg (fun z => (-1 : ZMod 2) ^ (((3 : ℤ), (0 : ℤ)).1 + ((3 : ℤ), (0 : ℤ)).2).natAbs • z)
        hconvB
    have hRHS : S.mul 3 (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 3) ((0 : ℤ), (2 : ℤ))
          ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
          (by rw [← hQ]; abel)
          ((S.d 3 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 3)).hom Z) w₃
        + (-1 : ZMod 2) ^ (((3 : ℤ), (0 : ℤ)).1 + ((3 : ℤ), (0 : ℤ)).2).natAbs •
          S.mul 3 ((3 : ℤ), (0 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
            ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
            (by rw [← hQ]; abel) Z Z' = ZZ' := by
      have hAB : S.mul 3 (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 3) ((0 : ℤ), (2 : ℤ))
            ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
            (by rw [← hQ]; abel)
            ((S.d 3 ((3 : ℤ), (0 : ℤ)) (((3 : ℤ), (0 : ℤ)) + Work.Pi6.vr 3)).hom Z) w₃
          + (-1 : ZMod 2) ^ (((3 : ℤ), (0 : ℤ)).1 + ((3 : ℤ), (0 : ℤ)).2).natAbs •
            S.mul 3 ((3 : ℤ), (0 : ℤ)) (((0 : ℤ), (2 : ℤ)) + Work.Pi6.vr 3)
              ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3)
              (by rw [← hQ]; abel) Z Z'
          = (0 : S.E 3 ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3))
            + (-1 : ZMod 2) ^ (((3 : ℤ), (0 : ℤ)).1 + ((3 : ℤ), (0 : ℤ)).2).natAbs • ZZ' := by
        rw [hA, hB]
      rw [hAB, hsign, one_smul]
      exact zero_add ZZ'
    exact hleib.trans hRHS
  have hZZne : ZZ ≠ 0 := by
    have hZZ' : ZZ' = cZ • ZZ := by
      have h1 : ZZ' = S.mul 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
          ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hQv Z (cZ • Z) := by
        rw [show ZZ' = S.mul 3 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
          ((((3 + 0 : ℕ) : ℤ), ((0 + 2 : ℕ) : ℤ)) + Work.Pi6.vr 3) hQv Z Z' from rfl, hcZ]
      rw [h1, map_smul]
    intro hz
    exact hd3z₁ (by rw [hd3z1, hZZ', hz, smul_zero])
  -- ============ L. `Y · Y ≠ 0` ============
  let YY : S.E 2 (((3 + 3 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ)) :=
    S.mul 2 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
      (((3 + 3 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ)) (by ext <;> simp) Y Y
  have hYYcyc : (S.d 2 ((6 : ℤ), (0 : ℤ)) (((6 : ℤ), (0 : ℤ)) + Work.Pi6.vr 2)).hom YY = 0 := by
    have hP6 : ((3 : ℤ), (0 : ℤ)) + ((3 : ℤ), (0 : ℤ)) =
        (((3 + 3 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ)) := by ext <;> simp
    have hleib := S.leibniz 2 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
      (((3 + 3 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ)) hP6 Y Y (by norm_num)
    rw [hYcyc] at hleib
    simp at hleib
    exact hleib
  have hYYne : YY ≠ 0 := by
    have hproj : S.proj 2 ((6 : ℤ), (0 : ℤ)) ⟨YY, hYYcyc⟩ = ZZ := by
      have hp := S.proj_mul 2 ((3 : ℤ), (0 : ℤ)) ((3 : ℤ), (0 : ℤ))
        (((3 + 3 : ℕ) : ℤ), ((0 + 0 : ℕ) : ℤ)) (by ext <;> simp) ⟨Y, hYcyc⟩ ⟨Y, hYcyc⟩
        ⟨YY, hYYcyc⟩ (by norm_num) rfl
      rw [← hZspec] at hp
      exact hp
    have hinj := K2F9.proj_injective S 2 (by norm_num) ((6 : ℤ), (0 : ℤ)) (by
      have hz : IsZero (S.E 2 (((6 : ℤ), (0 : ℤ)) - Work.Pi6.vr 2)) := by
        have hc : (((6 : ℤ), (0 : ℤ)) - Work.Pi6.vr 2) = ((4 : ℤ), (1 : ℤ)) := by
          ext <;> simp [Work.Pi6.vr]
        rw [hc]
        exact k4_isZero_E2_right p e₀ S 6 hS6 (s := 4) (q := 1) (by omega) (by omega) hF1
      exact hz)
    intro h
    refine hZZne ?_
    have h1 : (⟨YY, hYYcyc⟩ : ↥(LinearMap.ker (S.d 2 ((6 : ℤ), (0 : ℤ))
        (((6 : ℤ), (0 : ℤ)) + Work.Pi6.vr 2)).hom)) = 0 := Subtype.ext h
    rw [← hproj, h1, map_zero]
    rfl
  -- ============ M. transport to `H⁶(B;𝔽₂)` ============
  have hYYe2 : YY = (e2 6 0 (by omega) (by omega)).inv.hom
      (Work.Pi6.cup (ZMod 2) B 3 3 y y ⊗ₜ[ZMod 2]
        Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀))) := by
    have hm := hmul 3 0 3 0 y (Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀))) y
      (Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀))) (by omega) (by omega)
    have h1 : Work.Pi6.cup (ZMod 2) (Work.StemsB.fibre p (p e₀)) 0 0
        (Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀)))
        (Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀))) =
        Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀)) :=
      (hco (ZMod 2) 0 (Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀)))).2
    rw [h1] at hm
    rw [show (0 * 3 : ℕ) = 0 from rfl, pow_zero, one_smul] at hm
    exact hm
  intro hcup
  refine hYYne ?_
  rw [hYYe2]
  have : Work.Pi6.cup (ZMod 2) B 3 3 y y ⊗ₜ[ZMod 2]
      Work.Pi6.one (ZMod 2) (Work.StemsB.fibre p (p e₀)) = 0 := by
    rw [hcup, TensorProduct.zero_tmul]
  rw [this, map_zero]

end

end K2F9
end Work.Pi6.EMM2


