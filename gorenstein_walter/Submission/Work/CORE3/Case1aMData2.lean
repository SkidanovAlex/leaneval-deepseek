import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.Case1aFrattiniSAct
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.CORE3.Case1aThmCInputs

namespace Work.CORE3

open scoped Pointwise
open Subgroup
open Work.GW2

/-! ## Elementary group theory helpers for `Work.CORE3.Case1aMData2`

`O_p(U)` is abelian (`t₂` inverts it), and an odd-order group acting on a group of order three
acts trivially (`Aut C₃ ≅ C₂`).  Both are used by the `M`-analysis of Bender 1981, §3, p. 223.
-/

/-- An automorphism of a group of cardinality `3` is an involution. -/
theorem mdata2_mulAut_sq_eq_one_of_card_three {H : Type} [Group H] [Finite H]
    (hcard : Nat.card H = 3) (σ : MulAut H) : σ ^ 2 = 1 := by
  ext x
  show σ (σ x) = x
  by_cases hx : x = 1
  · rw [hx, map_one, map_one]
  · have hxord : orderOf x = 3 := by
      have hdvd : orderOf x ∣ Nat.card H := orderOf_dvd_natCard x
      rw [hcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx
      · exact h
    have hx3 : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    have hx3z : x ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hx3]
    have hxne : σ x ≠ 1 := fun h => hx (σ.injective (by rw [h, map_one]))
    have hgen : Subgroup.zpowers x = ⊤ := by
      refine Subgroup.eq_top_of_card_eq _ ?_
      rw [Nat.card_zpowers, hxord, hcard]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (show σ x ∈ Subgroup.zpowers x by rw [hgen]; trivial)
    have hkmod : x ^ (k % 3) = σ x := by rw [← hk, zpow_eq_zpow_emod k hx3z]
    have hσx : σ x = x ∨ σ x = x ^ 2 := by
      have hlo : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
      have hge : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
      have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h3 with h | h | h
      · exfalso; rw [h, zpow_zero] at hkmod; exact hxne hkmod.symm
      · left; rw [h, zpow_one] at hkmod; exact hkmod.symm
      · right
        rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast] at hkmod
        exact hkmod.symm
    rcases hσx with h | h
    · rw [h]; exact h
    · rw [h, map_pow, h, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 from rfl, pow_succ, hx3, one_mul]

/-- An element of odd order normalising a subgroup of order `3` acts trivially on it. -/
theorem mdata2_conj_eq_self_of_odd_of_card_three {G : Type} [Group G] [Finite G]
    {Q : Subgroup G} {b : G} (hb : b ∈ Subgroup.normalizer (Q : Set G))
    (hcard : Nat.card ↥Q = 3) (hodd : Odd (orderOf b)) :
    ∀ a ∈ Q, b * a * b⁻¹ = a := by
  haveI : Finite ↥Q := inferInstance
  have hpow : ∀ k : ℕ, ∀ y : ↥Q,
      (((Work.CORE3.c1aConjMulAut Q hb) ^ k) y : G) = b ^ k * (y : G) * (b ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro y; simp [MulAut.one_apply]
    | succ k ih =>
      intro y
      rw [pow_succ, MulAut.mul_apply, ih, Work.CORE3.c1aConjMulAut_apply, pow_succ]
      group
  have hm : (Work.CORE3.c1aConjMulAut Q hb) ^ (orderOf b) = 1 := by
    ext y
    rw [hpow (orderOf b) y, MulAut.one_apply, pow_orderOf_eq_one b]
    simp
  have h2 : (Work.CORE3.c1aConjMulAut Q hb) ^ 2 = 1 :=
    mdata2_mulAut_sq_eq_one_of_card_three hcard _
  obtain ⟨t, ht⟩ := hodd
  have hone : Work.CORE3.c1aConjMulAut Q hb = 1 := by
    have hprod : (Work.CORE3.c1aConjMulAut Q hb) ^ (2 * t + 1) =
        Work.CORE3.c1aConjMulAut Q hb := by
      rw [pow_succ, pow_mul, h2, one_pow, one_mul]
    rw [← hprod, ← ht]
    exact hm
  intro a ha
  have hval := congrArg (fun z : ↥Q => (z : G))
    (congrArg (fun (σ : MulAut ↥Q) => σ ⟨a, ha⟩) hone)
  simpa [Work.CORE3.c1aConjMulAut_apply] using hval

/-- `V₁ = ⟨t, t₁⟩` has the four elements `1, t, t₁, t·t₁`. -/
theorem mdata2_mem_V1_or {G : Type} [Group G] [Finite G] (hCtx : BenderCtx G)
    (B : BenderSetup G) (D : Case1aData B) :
    ∀ x : G, x ∈ (Work.CORE3.V1 B D : Set G) →
      x = 1 ∨ x = B.t ∨ x = D.t1 ∨ x = B.t * D.t1 := by
  intro x hx
  have hcomm : B.t * D.t1 = D.t1 * B.t :=
    (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B D.t1_mem)) B.t (by simp)
  have hnormalizer : Subgroup.zpowers D.t1 ≤
      Subgroup.normalizer (Subgroup.zpowers B.t : Set G) := by
    have hcen : Subgroup.zpowers D.t1 ≤
        Subgroup.centralizer (Subgroup.zpowers B.t : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left (hcomm : Commute B.t D.t1) k).eq
    exact le_trans hcen (Subgroup.centralizer_le_normalizer _)
  have hcoe : ((Work.CORE3.V1 B D : Subgroup G) : Set G)
      = (Subgroup.zpowers B.t : Set G) * (Subgroup.zpowers D.t1 : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnormalizer
  rw [hcoe, Set.mem_mul] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  have ha' : a = 1 ∨ a = B.t :=
    Work.CORE2A.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two B.t_order ha
  have hb' : b = 1 ∨ b = D.t1 :=
    Work.CORE2A.eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two D.t1_order hb
  rw [← hab]
  rcases ha' with h1 | h1 <;> rcases hb' with h2 | h2 <;> rw [h1, h2]
  · exact Or.inl (one_mul 1)
  · exact Or.inr (Or.inr (Or.inl (one_mul D.t1)))
  · exact Or.inr (Or.inl (mul_one B.t))
  · exact Or.inr (Or.inr (Or.inr rfl))

namespace Work.CORE3

/-- Bender 1981 §3, p. 223, the `M`-analysis of the subcase `Ĥ = H` in the form Bender uses.
Deliverable `Work.CORE3.Case1aMData2Prop`.

The paragraph reads: "Take a maximal subgroup `M` of `G` containing `N_G(P₂)`. … This gives
`B ∩ M = O(M)`, `W = ⟨B ∩ M⟩^E`, `|S| = 8`, `|P₀| = 3`, and `U ∩ M = P₀ × (B ∩ M)`.
Again by Lemma 2.9, `E(N_G(X))` contains and hence equals `E` whenever `1 ≠ X ⊆ B ∩ M`, and this
implies `N_G(X) ⊆ M`.  Applying this to the normal subgroup `X = B ∩ PP^g` of
`C_{F(U)}(t₂) = B·C_{F(U)}(t₂)`, we see that `B ⊆ M` and `C_U(t₁) = B × P`."

Items (i)–(iv) of the conclusion are `hMD : Case1aMDataProp` (hence free); the new content is
(v) `U ∩ M = P₀ × B` read elementwise: `[P₀, B] = 1`; (vi) Bender's `C_U(t₁) = B ⊔ O_p(U)`;
(vii) `[B, O_p(U)] = 1`.  Those are the inputs the provers of `Case1aThmCInputs` and
`Case1aDirect` identified as missing for the `IsInternalDirect` conjunct of `BGThmCProp`
(Bender's `×` in the display, not merely `⊔`).

Available: `hFr` (`P₂ ≠ ⊥`, `N_G(P₁) ⊄ H`), `hAb` (`P ∩ P^g = ⊥`, `P P^g` abelian), `hA7`
(`E(M)/Z ≅ A₇`, `|P₀| = 3`), `hFit` (`B ∩ F(U) = 1`), `hBpf` (`B` fixed-point-free on
`F_{3'}(U)`), `I.h29` (Lemma 2.9). -/
theorem Case1aMData2 (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hMD : Case1aMDataProp)
    (hFit : Case1aBFittingProp) (hBpf : Case1aBFpfProp) : Case1aMData2Prop := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  classical
  haveI : IsSimpleGroup G := hCtx.simple
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  set Pp : Subgroup G := pCoreIn D.p B.U with hPpdef
  obtain ⟨hBM, hBcM, hUM, hNX⟩ :=
    hMD G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  obtain ⟨_hSM, _hV2E, _hiso, _hS8, hP0card⟩ :=
    hA7 G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- ## `D.p = 3`
  have hp3 : D.p = 3 := by
    have hpg : IsPGroup D.p ((pCoreIn D.p B.U ⊓ M) : Subgroup G) :=
      (c1aIsPGroup_pCoreIn D.p B.U).to_le inf_le_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    have hk3 : D.p ^ k = 3 := by rw [← hk, hP0card]
    have hk1 : k ≠ 0 := by rintro rfl; simp at hk3
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk1
    have hd : D.p ∣ 3 := by
      refine ⟨D.p ^ m, ?_⟩
      rw [← hk3, hm, pow_succ']
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact absurd h1 D.hp.ne_one
    · exact h3
  -- ## `Pp = O_p(U)` is abelian: `t₂` inverts it
  have hPpab : ∀ x ∈ Pp, ∀ y ∈ Pp, x * y = y * x := by
    intro x hx y hy
    have hx' : D.t2 * x * D.t2⁻¹ = x⁻¹ := D.inv x hx
    have hy' : D.t2 * y * D.t2⁻¹ = y⁻¹ := D.inv y hy
    have h1 : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
      have hxy1 : D.t2 * (x * y) * D.t2⁻¹ =
          (D.t2 * x * D.t2⁻¹) * (D.t2 * y * D.t2⁻¹) := by group
      have hinv : D.t2 * (x * y) * D.t2⁻¹ = (x * y)⁻¹ :=
        D.inv (x * y) (Subgroup.mul_mem _ hx hy)
      rw [hx', hy'] at hxy1
      rw [← hinv]
      exact hxy1
    have h2 : (x * y)⁻¹ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    have h4 : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := by rw [← h1, h2]
    have h5 : (x⁻¹ * y⁻¹)⁻¹ = (y⁻¹ * x⁻¹)⁻¹ := congrArg Inv.inv h4
    simpa using h5.symm
  -- ## the normalizer facts
  have hBcleNP : Bc ≤ Subgroup.normalizer (Pp : Set G) :=
    ((inf_le_left : Bc ≤ B.U)).trans
      ((Subgroup.le_normalizer (H := B.U)).trans (c1aLe_normalizer_pCoreIn D.p B.U))
  have hnormF : Bc ≤ Subgroup.normalizer ((fittingIn B.U : Subgroup G) : Set G) :=
    ((inf_le_left : Bc ≤ B.U)).trans
      (c1aLe_normalizer_map_subtype (K := B.U) (N := Work.GW2.fitting ↥B.U)
        (Subgroup.normalCore_normal _))
  have hnormF3 : Pp ≤ Subgroup.normalizer ((fittingPiIn ({3}ᶜ : Set ℕ) B.U : Subgroup G) : Set G) :=
    (c1aPcoreIn_le_self D.p B.U).trans
      ((Work.DSTR.M110.le_normalizer_fittingPiIn G ({3}ᶜ) B.U))
  -- ## (vi) Bender: `C_U(t₁) = C_U(S) ⊔ O_p(U)`
  have hCU : B.U ⊓ Subgroup.centralizer ({D.t1} : Set G) = Bc ⊔ Pp := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · intro x hx
      obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxC' : D.t1 * x * D.t1⁻¹ = x := by
        have h := (Subgroup.mem_centralizer_iff.mp hxC) D.t1 (by simp)
        rw [show D.t1 * x = x * D.t1 from h]; group
      -- decompose `x ∈ U = F(U)·B`
      have hU : B.U = fittingIn B.U ⊔ Bc := c1aU_eq_fitting_sup_B I G hFT hCtx B hCase
      have hxsup : x ∈ fittingIn B.U ⊔ Bc := by rw [← hU]; exact hxU
      obtain ⟨f, hf, b, hb, hfb⟩ := Set.mem_mul.mp (show x ∈ (fittingIn B.U : Set G) * ((Bc : Subgroup G) : Set G) from by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left (fittingIn B.U) Bc hnormF]
        exact hxsup)
      have hbC : D.t1 * b * D.t1⁻¹ = b := by
        have h := (Subgroup.mem_centralizer_iff.mp ((inf_le_right : Bc ≤
          Subgroup.centralizer ((B.S : Subgroup G) : Set G)) hb)) D.t1 D.t1_mem
        rw [show D.t1 * b = b * D.t1 from h]; group
      have hfC : D.t1 * f * D.t1⁻¹ = f := by
        have h := hxC'
        rw [← hfb] at h
        -- `t₁ (f b) t₁⁻¹ = f b`
        have : (D.t1 * f * D.t1⁻¹) * b = f * b := by
          calc (D.t1 * f * D.t1⁻¹) * b = (D.t1 * f * D.t1⁻¹) * (D.t1 * b * D.t1⁻¹) := by
                rw [hbC]
            _ = D.t1 * (f * b) * D.t1⁻¹ := by group
            _ = f * b := h
        exact mul_right_cancel this
      -- split `f ∈ F(U) = F_{3'}(U) ⊔ O_p(U)`
      have hF3' : fittingIn B.U = fittingPiIn ({3}ᶜ : Set ℕ) B.U ⊔ Pp := by
        rw [c1aFittingIn_eq_sup_three B.U, show (3 : ℕ) = D.p from hp3.symm, ← hPpdef]
      obtain ⟨f1, hf1, f2, hf2, hf12⟩ := Set.mem_mul.mp
        (show f ∈ (fittingPiIn ({3}ᶜ : Set ℕ) B.U : Set G) * ((Pp : Subgroup G) : Set G) from by
          rw [← Subgroup.coe_mul_of_right_le_normalizer_left
            (fittingPiIn ({3}ᶜ : Set ℕ) B.U) Pp hnormF3]
          rw [← hF3']
          exact hf)
      have hInv1 : Inverts D.t1 (fittingPiIn ({3}ᶜ : Set ℕ) B.U) :=
        ((Case1aBothInvert I hSetup hFr hAb hA7 hBpf) G hFT hCtx B hCase hHhat D).1
      have hf1inv : D.t1 * f1 * D.t1⁻¹ = f1⁻¹ := hInv1 f1 hf1
      have hf2c : D.t1 * f2 * D.t1⁻¹ = f2 := by
        have hcomm : D.t1 * f2 = f2 * D.t1 :=
          (Subgroup.mem_centralizer_iff.mp (D.cent hf2)) D.t1 (by simp)
        rw [show D.t1 * f2 = f2 * D.t1 from hcomm]; group
      have hfeq : f1⁻¹ * f2 = f1 * f2 := by
        rw [← hf12] at hfC
        calc f1⁻¹ * f2 = (D.t1 * f1 * D.t1⁻¹) * (D.t1 * f2 * D.t1⁻¹) := by rw [hf1inv, hf2c]
          _ = D.t1 * (f1 * f2) * D.t1⁻¹ := by group
          _ = f1 * f2 := hfC
      have hf1one : f1 = 1 := by
        have hf1sq : f1 * f1 = 1 := by
          have h := congrArg (fun w => w * f2⁻¹) hfeq
          have hA : f1⁻¹ * f2 * f2⁻¹ = f1⁻¹ := by group
          have hB : f1 * f2 * f2⁻¹ = f1 := by group
          rw [hA, hB] at h
          calc f1 * f1 = f1⁻¹ * f1 := by rw [h]
            _ = 1 := inv_mul_cancel f1
        have h2 : orderOf f1 ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one]
          simpa [pow_two] using hf1sq
        have hodd : Odd (orderOf f1) :=
          Odd.of_dvd_nat (Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B)
            (Subgroup.card_dvd_of_le
              ((bfpf_fittingPiIn_le_fittingIn ({3}ᶜ : Set ℕ) B.U).trans
                (c1aFittingIn_le B.U))))
            (Subgroup.orderOf_dvd_natCard _ hf1)
        rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
        · exact orderOf_eq_one_iff.mp h
        · rw [h] at hodd; exact absurd hodd (by norm_num)
      have hfeq2 : f = f2 := by rw [← hf12, hf1one, one_mul]
      -- conclude `x ∈ Pp ⊔ Bc`
      have hxP : x ∈ (Pp ⊔ Bc : Subgroup G) := by
        show x ∈ ((Pp ⊔ Bc : Subgroup G) : Set G)
        rw [Subgroup.coe_mul_of_right_le_normalizer_left Pp Bc hBcleNP]
        exact Set.mem_mul.mpr ⟨f2, hf2, b, hb, by rw [← hfeq2]; exact hfb⟩
      rwa [sup_comm] at hxP
    · -- `Bc ≤ U ⊓ C(t₁)`
      refine le_inf inf_le_left ?_
      exact (inf_le_right : Bc ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G)).trans
        (Subgroup.centralizer_le (by
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst hz
          exact D.t1_mem))
    · -- `Pp ≤ U ⊓ C(t₁)`
      exact le_inf (c1aPcoreIn_le_self D.p B.U) D.cent
  -- ## (v) `[P₀, B] = 1`
  have hV5 : ∀ a ∈ (pCoreIn D.p B.U ⊓ M : Subgroup G),
      ∀ b ∈ (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)), a * b = b * a := by
    intro a ha b hb
    have hbU : b ∈ B.U := (inf_le_left : Bc ≤ B.U) hb
    have hbP : b ∈ Subgroup.normalizer (Pp : Set G) :=
      ((Subgroup.le_normalizer (H := B.U)).trans (c1aLe_normalizer_pCoreIn D.p B.U)) hbU
    have hbM : b ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.le_normalizer ((hBM : Bc ≤ M) hb)
    have hbQ : b ∈ Subgroup.normalizer ((Pp ⊓ M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact and_congr ((Subgroup.mem_normalizer_iff.mp hbP y))
        ((Subgroup.mem_normalizer_iff.mp hbM y))
    have hcardQ : Nat.card ↥(Pp ⊓ M) = 3 := hP0card
    have hordb : Odd (orderOf b) :=
      Odd.of_dvd_nat
        (Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B)
          (Subgroup.card_dvd_of_le (inf_le_left : Bc ≤ B.U)))
        (Subgroup.orderOf_dvd_natCard _ hb)
    have hconj := mdata2_conj_eq_self_of_odd_of_card_three hbQ hcardQ hordb a ha
    calc a * b = (b * a * b⁻¹) * b := by rw [hconj]
      _ = b * a := by group
  -- ## the crux: `O_p(U) ≤ M`
  -- `V₁ = ⟨t,t₁⟩` is a four-group, and some `g ∈ N_G(V₁) \ H` conjugates `t` to `t₁`
  have hV1 : IsFourGroup (Work.CORE3.V1 B D) := Work.CORE3.Work.CORE3.fourGroup_V1 hCtx B D
  obtain ⟨n, hn2, hdih⟩ := SylowDihedral G hCtx B
  have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN hIdx
    have hcardS : Nat.card (B.S : Subgroup G) = 2 * n := by
      obtain ⟨e⟩ := hdih
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hbot : N ≠ ⊥ := by
      intro hh
      rw [hh, Subgroup.index_bot] at hIdx
      have h2 : 2 * n ≤ Nat.card G := by
        have h := Subgroup.card_le_card_group (B.S : Subgroup G)
        rwa [hcardS] at h
      omega
    have htop : N ≠ ⊤ := by
      intro hh
      rw [hh, Subgroup.index_top] at hIdx
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
    · exact hbot h1
    · exact htop h1
  obtain ⟨g, hgN, hgconj⟩ := (I.T.fus G B.S n hn2 hdih hnoN).2 (Work.CORE3.V1 B D) hV1
    B.t (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
    D.t1 (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1))
    (Work.CORE2A.bSetup_t_ne_one B)
    (by
      intro h
      have h1 : orderOf D.t1 = 1 := by rw [h]; exact orderOf_one
      rw [D.t1_order] at h1
      norm_num at h1)
  have hgH : g ∉ B.H := by
    intro hgH'
    have hcomm : B.t * g = g * B.t :=
      (Subgroup.mem_centralizer_iff.mp hgH') B.t (by simp)
    have h1 : g * B.t * g⁻¹ = B.t := by
      rw [← hcomm]; group
    have ht_eq : B.t = D.t1 := by rw [← hgconj, h1]
    exact D.t1_nmem (ht_eq ▸ B.t_mem)
  obtain ⟨hPg_bot, hPg_comm⟩ := hAb G hFT hCtx B hCase hHhat D g hgN hgH
  have hcommP : ∀ x ∈ Pp, ∀ y ∈ conjSub g Pp, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val ((hPg_comm.is_comm).comm ⟨x, Subgroup.mem_sup_left hx⟩
      ⟨y, Subgroup.mem_sup_right hy⟩)
  -- `Pp^g` lies in `C_U(t₁) = Bc ⊔ Pp`
  have hPg_le : ∀ y ∈ conjSub g Pp, y ∈ B.U ⊓ Subgroup.centralizer ({D.t1} : Set G) := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have hxy' : g * x * g⁻¹ = y := by rw [← hxy]; rfl
    have hxU : x ∈ B.U := c1aPcoreIn_le_self D.p B.U hx
    have hx_t : B.t * x * B.t⁻¹ = x := by
      have hcomm : B.t * x = x * B.t :=
        (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_U_le_H B hxU)) B.t (by simp)
      rw [show B.t * x = x * B.t from hcomm]; group
    have hx_t1 : D.t1 * x * D.t1⁻¹ = x := by
      have hcomm : D.t1 * x = x * D.t1 :=
        (Subgroup.mem_centralizer_iff.mp (D.cent hx)) D.t1 (by simp)
      rw [show D.t1 * x = x * D.t1 from hcomm]; group
    have hy_t1 : D.t1 * y * D.t1⁻¹ = y := by
      rw [← hxy', ← hgconj]
      calc (g * B.t * g⁻¹) * (g * x * g⁻¹) * (g * B.t * g⁻¹)⁻¹
          = g * (B.t * x * B.t⁻¹) * g⁻¹ := by group
        _ = g * x * g⁻¹ := by rw [hx_t]
    have hy_t : B.t * y * B.t⁻¹ = y := by
      set z : G := g * D.t1 * g⁻¹ with hzdef
      have hz_comm : z * y * z⁻¹ = y := by
        rw [hzdef]
        calc (g * D.t1 * g⁻¹) * y * (g * D.t1 * g⁻¹)⁻¹
            = (g * D.t1 * g⁻¹) * (g * x * g⁻¹) * (g * D.t1 * g⁻¹)⁻¹ := by rw [hxy']
          _ = g * (D.t1 * x * D.t1⁻¹) * g⁻¹ := by group
          _ = g * x * g⁻¹ := by rw [hx_t1]
          _ = y := hxy'
      have hz_mem : z ∈ (Work.CORE3.V1 B D : Subgroup G) := by
        have h1 : D.t1 ∈ (Work.CORE3.V1 B D : Subgroup G) :=
          Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t1)
        have h2 := (Subgroup.mem_normalizer_iff.mp hgN) D.t1
        exact (h2.mp h1)
      have hz_ne_one : z ≠ 1 := by
        intro h
        have hmain : g⁻¹ * (g * D.t1 * g⁻¹) * g = D.t1 := by group
        have h1 : D.t1 = 1 := by
          have h2 := congrArg (fun w => g⁻¹ * w * g) h
          rw [hzdef] at h2
          rw [hmain] at h2
          simpa using h2
        have h3 : orderOf D.t1 = 1 := by rw [h1]; exact orderOf_one
        rw [D.t1_order] at h3
        norm_num at h3
      have hz_ne_t1 : z ≠ D.t1 := by
        intro h
        have hz' : g * D.t1 * g⁻¹ = D.t1 := by rw [← hzdef]; exact h
        have h3 : g * (B.t * D.t1) * g⁻¹ = 1 := by
          rw [show g * (B.t * D.t1) * g⁻¹ = (g * B.t * g⁻¹) * (g * D.t1 * g⁻¹) from by
              group, hgconj, hz', show D.t1 * D.t1 = 1 from Work.CORE3.Work.CORE3.t1_sq B D]
        have h4 : B.t * D.t1 = 1 := by
          have hmain : g⁻¹ * (g * (B.t * D.t1) * g⁻¹) * g = B.t * D.t1 := by group
          have h5 := congrArg (fun w => g⁻¹ * w * g) h3
          rw [hmain] at h5
          simpa using h5
        have h6 : B.t = D.t1 := by
          have h7 := eq_inv_of_mul_eq_one_left h4
          rwa [show D.t1⁻¹ = D.t1 from
            inv_eq_of_mul_eq_one_right (Work.CORE3.Work.CORE3.t1_sq B D)] at h7
        exact D.t1_nmem (h6 ▸ B.t_mem)
      have hzy : z * y = y * z := by
        calc z * y = (z * y * z⁻¹) * z := by group
          _ = y * z := by rw [show z * y * z⁻¹ = y from hz_comm]
      rcases mdata2_mem_V1_or hCtx B D z hz_mem with h | h | h | h
      · exact absurd h hz_ne_one
      · rw [← h]
        rw [hzdef]
        exact hz_comm
      · exact absurd h hz_ne_t1
      · have hBt : B.t = z * D.t1 := by
          rw [h, mul_assoc, Work.CORE3.Work.CORE3.t1_sq B D, mul_one]
        rw [hBt]
        calc (z * D.t1) * y * (z * D.t1)⁻¹ = z * (D.t1 * y * D.t1⁻¹) * z⁻¹ := by group
          _ = z * y * z⁻¹ := by rw [hy_t1]
          _ = (g * D.t1 * g⁻¹) * y * (g * D.t1 * g⁻¹)⁻¹ := by rw [hzdef]
          _ = y := hz_comm
    have hyH : y ∈ B.H := by
      rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl]
      exact Subgroup.mem_centralizer_iff.mpr (by
        intro h' hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        calc B.t * y = (B.t * y * B.t⁻¹) * B.t := by group
          _ = y * B.t := by rw [hy_t])
    have hyodd : Odd (orderOf y) := by
      have hdvd : orderOf y ∣ Nat.card ↥(conjSub g Pp) :=
        Subgroup.orderOf_dvd_natCard (conjSub g Pp) hy
      rw [Work.CORE2A.card_conjSub] at hdvd
      exact Odd.of_dvd_nat
        (Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B)
          (Subgroup.card_dvd_of_le (c1aPcoreIn_le_self D.p B.U))) hdvd
    have hyU : y ∈ B.U := by
      have hodd_sub := Work.CORE2A.odd_subgroup_le_oddCoreIn B.H B.U (B.S : Subgroup G)
        (Work.CORE2A.bSetup_U_eq B) (H_eq_U_sup_S G I.T hCtx B) B.S.isPGroup'
      refine hodd_sub (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyH) ?_ (Subgroup.mem_zpowers y)
      rw [Nat.card_zpowers]
      exact hyodd
    exact ⟨hyU, Subgroup.mem_centralizer_iff.mpr (by
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      calc D.t1 * y = (D.t1 * y * D.t1⁻¹) * D.t1 := by group
        _ = y * D.t1 := by rw [hy_t1])⟩
  have hPg_bot' : Pp ⊓ conjSub g Pp = ⊥ := by
    rw [hPpdef]
    exact hPg_bot
  -- a non-trivial element of `Pp`, its conjugate `y₀`, and the element of `Bc` it produces
  have hPp_ne : Pp ≠ ⊥ := by
    intro h
    have h1 : (pCoreIn D.p B.U ⊓ M : Subgroup G) = ⊥ := by
      rw [← hPpdef, h, bot_inf_eq]
    have h2 : Nat.card ↥(pCoreIn D.p B.U ⊓ M) = 1 := by rw [h1]; simp
    rw [hP0card] at h2
    norm_num at h2
  obtain ⟨x0, hx0, hx0ne⟩ : ∃ x, x ∈ Pp ∧ x ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hPp_ne (le_antisymm (fun z hz => Subgroup.mem_bot.mpr (hcon z hz)) bot_le)
  set y0 : G := g * x0 * g⁻¹ with hy0def
  have hy0_mem : y0 ∈ conjSub g Pp := by
    rw [Work.CORE2A.conjSub_eq_map]
    exact Subgroup.mem_map.mpr ⟨x0, hx0, by show g * x0 * g⁻¹ = y0; rw [hy0def]⟩
  have hy0_ne : y0 ≠ 1 := by
    intro h
    have hmain : g⁻¹ * (g * x0 * g⁻¹) * g = x0 := by group
    have h1 : x0 = 1 := by
      have h2 := congrArg (fun w => g⁻¹ * w * g) h
      rw [hy0def] at h2
      rw [hmain] at h2
      simpa using h2
    exact hx0ne h1
  have hy0_in : y0 ∈ Bc ⊔ Pp := by
    rw [← hCU]
    exact hPg_le y0 hy0_mem
  obtain ⟨p, hp, b, hb, hpb⟩ := Set.mem_mul.mp
    (show y0 ∈ ((Pp : Subgroup G) : Set G) * ((Bc : Subgroup G) : Set G) from by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Pp Bc hBcleNP]
      rw [sup_comm]
      exact hy0_in)
  have hb_ne : b ≠ 1 := by
    intro hb1
    have hy0P : y0 ∈ Pp := by rw [← hpb, hb1, mul_one]; exact hp
    have hmem : y0 ∈ Pp ⊓ conjSub g Pp := ⟨hy0P, hy0_mem⟩
    rw [hPg_bot'] at hmem
    exact hy0_ne (Subgroup.mem_bot.mp hmem)
  have hbC : b ∈ Subgroup.centralizer (Pp : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    have hzy : z * y0 = y0 * z := hcommP z hz y0 hy0_mem
    have hzp : z * p = p * z := hPpab z hz p hp
    have hzy' : z * (p * b) = (p * b) * z := by rw [hpb]; exact hzy
    have h1 : p * (z * b) = p * (b * z) := by
      calc p * (z * b) = (p * z) * b := by group
        _ = (z * p) * b := by rw [← hzp]
        _ = z * (p * b) := by group
        _ = (p * b) * z := hzy'
        _ = p * (b * z) := by group
    exact mul_left_cancel h1
  -- so `C_B(O_p(U)) ≠ ⊥`, and it is normalised by `O_p(U)`
  have hCB_ne : (Subgroup.centralizer (Pp : Set G) ⊓ Bc : Subgroup G) ≠ ⊥ := by
    intro h
    have hmem : b ∈ (⊥ : Subgroup G) := by
      rw [← h]
      exact ⟨hbC, hb⟩
    exact hb_ne (Subgroup.mem_bot.mp hmem)
  have hCB_le : (Subgroup.centralizer (Pp : Set G) ⊓ Bc : Subgroup G) ≤ Bc := inf_le_right
  have hPp_le_N : Pp ≤ Subgroup.normalizer
      ((Subgroup.centralizer (Pp : Set G) ⊓ Bc : Subgroup G) : Set G) := by
    have hcp : (Subgroup.centralizer (Pp : Set G) ⊓ Bc : Subgroup G) ≤
        Subgroup.centralizer (Pp : Set G) := inf_le_left
    have h1 : Pp ≤ Subgroup.centralizer
        ((Subgroup.centralizer (Pp : Set G) ⊓ Bc : Subgroup G) : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      exact hcp
    exact h1.trans (Subgroup.centralizer_le_normalizer _)
  have hPp_le_M : Pp ≤ M :=
    hPp_le_N.trans (hNX _ hCB_ne hCB_le)
  have hP0eq : (pCoreIn D.p B.U ⊓ M : Subgroup G) = pCoreIn D.p B.U :=
    inf_eq_left.mpr hPp_le_M
  -- ## assembly
  refine ⟨⟨hBM, hBcM, hUM, hNX, hV5⟩, hCU, ?_⟩
  intro a ha b hb
  exact (hV5 b (by rw [hP0eq]; exact hb) a ha).symm

end Work.CORE3

end Work.CORE3

namespace Work.CORE3

/-- The same lemma, exposed at the namespace of the area (`Work.CORE3`), matching the name the
area asked for (`Work.CORE3.Case1aMData2`). -/
theorem Case1aMData2 (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1aSetupProp)
    (hFr : Work.GW2.Case1aFrattiniProp) (hAb : Work.GW2.Case1aAbelianProp)
    (hA7 : Work.GW2.Case1aA7Prop) (hMD : Work.CORE3.Case1aMDataProp)
    (hFit : Work.CORE3.Case1aBFittingProp) (hBpf : Work.CORE3.Case1aBFpfProp) :
    Work.CORE3.Case1aMData2Prop :=
  _root_.Work.CORE3.Work.CORE3.Case1aMData2 I hSetup hFr hAb hA7 hMD hFit hBpf

end Work.CORE3
