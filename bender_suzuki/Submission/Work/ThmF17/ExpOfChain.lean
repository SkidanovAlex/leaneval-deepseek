import Submission.Work.ThmF.ChV3.Prove.R_abelian_transitivity
import Submission.Work.ThmF.Prove.centDLowerCentralizerS

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF17.ExpOfChain` — `NearFieldExpProp` is not an App. XI input

At its only consumer (`ChV3/Step16Plumbing.lean` l.160) the chain already has step (7)
(`h7 : Ker = P`), `hpf : |P| = o(st)` and step (11)'s `hcomm : R abelian`.  From these the
exponent clause follows by an elementary argument (no near-field):

* `x^p ∈ P` for `x ∈ R` (`C_Q(P)` transitive on `R \ P` mod `P`, `R_abelian_transitivity`);
* `s` inverts `R` mod `P` (`s x s⁻¹ x` is `s`-fixed, `h15.hfpf` with `y = s`);
* so `x^p = s x^p s⁻¹ = (z x⁻¹)^p = x^{-p}`, `x^{2p} = 1`, and `|R| = p^{m+1}` is odd.

This module is the split of `_design17/D4_Exp.lean` (BS design pass 17, item D4); namespace
`Work.ThmF17`.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section
open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

namespace Work.ThmF17

open Work.ThmF.ChV3

/-- **Step (11)'s exponent clause, directly from the chain** (`NearFieldExpProp` at its consumer):
in the standing context, if step (7) (`Ker = P`), `|P| = o(st)` and `R` is abelian, then
`x ^ |P| = 1` for every `x ∈ R`. -/
theorem exp_of_chain {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    {P : Subgroup G} (c : CtxF H Q t s r P) (h15 : Chain15 H Q t s r P)
    (h7 : Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    (hcomm : IsMulCommutative ↥h15.R) :
    ∀ x ∈ h15.R, x ^ Nat.card P = 1 := by
  classical
  set p := Nat.card P with hp_def
  have hpprime : p.Prime := c.P_prime
  have hPR : P ≤ h15.R := fun x hx => h15.hNR (by rw [h7]; exact hx)
  have hRcard : Nat.card h15.R = p ^ (h15.m + 1) := by
    rw [h15.hcardR, h7, ← hpf, pow_succ, mul_comm]
  have hRodd : Odd (Nat.card h15.R) := by
    have hDodd : Odd (Nat.card ↥(twoPoint H t)) :=
      c.split.stronglyEmbedded.2.2 t c.split.not_mem
    have hPD : P ≤ twoPoint H t := c.P_le.trans inf_le_left
    have hpodd : Odd p := hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hPD)
    rw [hRcard]; exact hpodd.pow
  -- commutation in `R`
  have hRc : ∀ a ∈ h15.R, ∀ b ∈ h15.R, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥h15.R) (⟨b, hb⟩ : ↥h15.R))
  -- `s ∈ C_Q(P)`
  have hsP : ∀ z ∈ P, s * z = z * s := by
    intro z hz
    have hzV : z ∈ centD H t := c.P_le hz
    have := Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid hzV
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have hsCQ : s ∈ CQ Q P := by
    refine ⟨c.s_mem, ?_⟩
    show s ∈ Subgroup.centralizer (P : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hsP z hz).symm
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [c.s_inv, pow_two] at h
    exact h
  have hs1 : s ≠ 1 := by
    intro h
    have h2 := c.s_inv
    rw [h, orderOf_one] at h2
    omega
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  -- `C_Q(P)` normalises `R` and centralises `P`
  have hCQR : ∀ y ∈ CQ Q P, ∀ a ∈ h15.R, y * a * y⁻¹ ∈ h15.R := by
    intro y hy a ha
    exact (Subgroup.mem_normalizer_iff.mp (h15.hRn hy.2) a).mp ha
  have hCQP : ∀ y ∈ CQ Q P, ∀ z ∈ P, y * z * y⁻¹ = z := by
    intro y hy z hz
    have := Subgroup.mem_centralizer_iff.mp hy.2 z hz
    rw [← this]; group
  have hzp : ∀ z ∈ P, z ^ p = 1 := by
    intro z hz
    have h : (⟨z, hz⟩ : ↥P) ^ Nat.card ↥P = 1 := pow_card_eq_one'
    have h' := congrArg Subtype.val h
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using h'
  -- ## Step A: `x ^ p ∈ P` for `x ∈ R`
  have hA : ∀ x ∈ h15.R, x ^ p ∈ P := by
    intro x hx
    by_cases hxP : x ∈ P
    · exact P.pow_mem hxP p
    have hex : ∃ j : ℕ, x ^ (p ^ j) ∈ P := by
      refine ⟨h15.m + 1, ?_⟩
      have : x ^ (p ^ (h15.m + 1)) = 1 := by
        rw [← hRcard]
        have h : (⟨x, hx⟩ : ↥h15.R) ^ Nat.card ↥h15.R = 1 := pow_card_eq_one'
        have h' := congrArg Subtype.val h
        simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using h'
      rw [this]; exact P.one_mem
    set j := Nat.find hex with hj
    have hjP : x ^ (p ^ j) ∈ P := Nat.find_spec hex
    have hj0 : j ≠ 0 := by
      intro h0
      apply hxP
      have := hjP
      rw [h0, pow_zero, pow_one] at this
      exact this
    set v := x ^ (p ^ (j - 1)) with hv
    have hvR : v ∈ h15.R := h15.R.pow_mem hx _
    have hvP : v ∉ P := Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos)
    have hvp : v ^ p ∈ P := by
      rw [hv, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
      exact hjP
    obtain ⟨y, hy, hyz⟩ := Work.ThmF.ChV3.Prove.R_abelian_transitivity c h15 h7 hpf
      hvR hx hvP hxP
    -- `y v y⁻¹ x⁻¹ = z ∈ P`, so `x = z⁻¹ * (y v y⁻¹)`
    set z := y * v * y⁻¹ * x⁻¹ with hz
    have hx_eq : x = z⁻¹ * (y * v * y⁻¹) := by rw [hz]; group
    have hzR : z⁻¹ ∈ h15.R := hPR (P.inv_mem hyz)
    have hyvR : y * v * y⁻¹ ∈ h15.R := hCQR y hy v hvR
    have hcm : Commute z⁻¹ (y * v * y⁻¹) := hRc _ hzR _ hyvR
    have hxp : x ^ p = (z⁻¹) ^ p * (y * v * y⁻¹) ^ p := by
      rw [hx_eq, hcm.mul_pow]
    rw [hxp, show (z⁻¹) ^ p = 1 from by rw [inv_pow, hzp z hyz, inv_one], one_mul]
    have hconjpow : (y * v * y⁻¹) ^ p = y * v ^ p * y⁻¹ := by
      have h := map_pow (MulAut.conj y).toMonoidHom v p
      simpa [MulAut.conj_apply] using h
    rw [hconjpow, hCQP y hy _ hvp]
    exact hvp
  -- ## Step B: `s x s⁻¹ x ∈ P`
  have hB : ∀ x ∈ h15.R, s * x * s⁻¹ * x ∈ P := by
    intro x hx
    have hsx : s * x * s⁻¹ ∈ h15.R := hCQR s hsCQ x hx
    have hwR : s * x * s⁻¹ * x ∈ h15.R := h15.R.mul_mem hsx hx
    by_contra hwP
    have hfix : s * (s * x * s⁻¹ * x) * s⁻¹ * (s * x * s⁻¹ * x)⁻¹ ∈ Ker H Q P t := by
      have h1 : s * (s * x * s⁻¹ * x) * s⁻¹ = x * (s * x * s⁻¹) := by
        rw [hsinv]
        calc s * (s * x * s * x) * s = (s * s) * x * (s * x * s) := by group
          _ = x * (s * x * s) := by rw [hs2, one_mul]
      rw [h1, hRc x hx _ hsx, mul_inv_cancel]
      exact (Ker H Q P t).one_mem
    exact hs1 (h15.hfpf _ hwR (by rw [h7]; exact hwP) s hsCQ hfix)
  -- ## Step C
  intro x hx
  have hxpP := hA x hx
  have hsx : s * x * s⁻¹ ∈ h15.R := hCQR s hsCQ x hx
  set z := s * x * s⁻¹ * x with hz
  have hzP : z ∈ P := hB x hx
  have hsx_eq : s * x * s⁻¹ = z * x⁻¹ := by rw [hz]; group
  have hcm : Commute z x⁻¹ := hRc _ (hPR hzP) _ (h15.R.inv_mem hx)
  have h1 : s * x ^ p * s⁻¹ = x ^ p := by
    have := hsP _ hxpP
    rw [this]; group
  have h2 : s * x ^ p * s⁻¹ = (x ^ p)⁻¹ := by
    have hconjpow : s * x ^ p * s⁻¹ = (s * x * s⁻¹) ^ p := by
      have h := map_pow (MulAut.conj s).toMonoidHom x p
      simpa [MulAut.conj_apply] using h.symm
    rw [hconjpow, hsx_eq, hcm.mul_pow, hzp z hzP, one_mul, inv_pow]
  have h2p : x ^ (2 * p) = 1 := by
    have h3 : x ^ p = (x ^ p)⁻¹ := h1.symm.trans h2
    rw [two_mul, pow_add]
    calc x ^ p * x ^ p = x ^ p * (x ^ p)⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel _
  have hordR : orderOf x ∣ p ^ (h15.m + 1) := by
    rw [← hRcard]
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : ↥h15.R)
    rwa [Subgroup.orderOf_mk] at h
  have hodd : Odd (orderOf x) := hRodd.of_dvd_nat (hRcard ▸ hordR)
  have hdvd : orderOf x ∣ 2 * p := orderOf_dvd_of_pow_eq_one h2p
  have hcop : Nat.Coprime (orderOf x) 2 :=
    Nat.Coprime.symm (Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr
      (fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)))
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)

end Work.ThmF17

#print axioms Work.ThmF17.exp_of_chain
