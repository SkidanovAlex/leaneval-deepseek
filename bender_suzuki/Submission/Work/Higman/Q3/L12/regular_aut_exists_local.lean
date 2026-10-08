/-
# A regular automorphism of a two-step group of order `q ^ 3`

This file proves `Work.Higman.Q3.regular_aut_exists`: for the two-step model
`P = TwoStep V W b` of Higman's Suzuki 2-groups of order `q ^ 3` (`q = |W|`, `|V| = q ^ 2`,
all involutions central, `Z(P) = kerFst`) with a cyclic group `⟨ξ⟩` of automorphisms permuting
the involutions transitively, there is an automorphism `ζ` of order `q - 1` which permutes the
involutions transitively and is fixed point free on `P ∖ {1}` (Higman 1963, §2).

The mathematical content is the *crux* `crux_of_powers`: a power `ξ ^ j` of `ξ` which is trivial
on `kerFst` has order coprime to `q - 1`.  The proof of that crux is elementary but
quantitative.  Write `ψ = ξ ^ j`, let `r` be a prime dividing `gcd (orderOf ψ) (q - 1)` and
`ψ₀ = ψ ^ (orderOf ψ / r)`, so that `orderOf ψ₀ = r` is odd.  Let `β` be the automorphism of
`V` induced by `ψ₀` (which exists because `ψ₀` is trivial on `kerFst`), and let `S = {v | β v = v}`.

* `β` preserves the squaring form `Q v = b v v`, whose fibres over the non-zero elements of `W`
  all have cardinality `q + 1` (`fiber_card_sq`) and are permuted transitively by the action of
  `ξ` on `V`;
* since `β` commutes with that action, the number `f` of `β`-fixed points in a fibre `Q⁻¹(w)`
  (`w ≠ 0`) does not depend on `w`, and `|S| = 1 + (q - 1) · f` (`fiber_fixed_card`);
* the `r`-group `⟨β⟩` acts on the `q + 1` elements of such a fibre, so `f ≡ q + 1 ≡ 2 (mod r)`
  (Mathlib's `Equiv.Perm.card_compl_support_modEq`), whence `f ≥ 2`;
* `S` is a subspace of `V`, so `|S| = 2 ^ d` with `d < 2n` (because `β ≠ 1`), while the two
  displayed facts give `2 ^ n - 1 ∣ 2 ^ d - 1`, so `n ∣ d`, and `f ≥ 2` gives `d > n` — a
  contradiction.

The final assembly (any power of `ξ` of order `q - 1` is automatically regular) is the delegated
lemma `Work.Higman.Q3.regular_aut_of_crux`.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Q3.pow_sub_one_dvd_pow_sub_one_iff
import Submission.Work.Higman.Q3.twoStep_action
import Submission.Work.Higman.Q3.L12.fiber_card_sq_local
import Submission.Work.Higman.Q3.L12.fiber_fixed_card_local

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.Higman.Q3

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable {b : V → V → W} [Biadd b]

/-- **The crux.**  A power `ξ ^ j` of `ξ` which is trivial on `kerFst` has order coprime to
`|W| - 1`.  (This is the only place where the hypotheses on `ξ` are used.) -/
theorem crux_of_powers
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (j : ℕ) (hj : ∀ x ∈ TwoStep.kerFst, (ξ ^ j) x = x) :
    Nat.Coprime (orderOf (ξ ^ j)) (Nat.card W - 1) := by
  classical
  haveI : Finite W := finite_of_hW hW
  haveI : Finite V := finite_V_of_hcardV hcardV hW
  obtain ⟨n, hn⟩ := card_W_eq_two_pow (W := W) hW
  have hnpos : 0 < n := by
    by_contra h
    rw [Nat.not_lt, Nat.le_zero] at h
    rw [h, pow_zero] at hn
    omega
  have hn2 : 2 ≤ n := by
    have h2 : 2 ^ 2 ≤ 2 ^ n := by rw [← hn]; exact hW
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h2
  have hodd : Odd (2 ^ n - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ]
    exact ⟨2 ^ m - 1, by omega⟩
  by_contra hnc
  obtain ⟨r, hrp, hrdvd_m, hrdvd_q⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  haveI : Fact (Nat.Prime r) := ⟨hrp⟩
  have hr2 : r ≠ 2 := by
    intro h
    subst h
    have h2dvd : 2 ∣ 2 ^ n - 1 := by rw [← hn]; exact hrdvd_q
    have hm0 : (2 ^ n - 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2dvd
    have hm1 : (2 ^ n - 1) % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hr3 : 3 ≤ r := by have := hrp.two_le; omega
  set ψ : MulAut (TwoStep V W b) := ξ ^ j with hψdef
  set m : ℕ := orderOf ψ with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact orderOf_pos ψ
  have hrdvd : r ∣ m := by rw [hmdef]; exact hrdvd_m
  have hrpos : 0 < r := hrp.pos
  set ψ₀ : MulAut (TwoStep V W b) := ψ ^ (m / r) with hψ₀def
  have hψ₀ker : ∀ x ∈ TwoStep.kerFst, ψ₀ x = x := by
    intro x hx
    have hpow : ∀ k : ℕ, (ψ ^ k) x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, MulAut.mul_apply, hj x hx, ih]
    rw [hψ₀def]
    exact hpow (m / r)
  have hkpos : 0 < m / r := Nat.div_pos (Nat.le_of_dvd hmpos hrdvd) hrpos
  have hψ₀ord : orderOf ψ₀ = r := by
    rw [hψ₀def, orderOf_pow]
    have hgcd : m.gcd (m / r) = m / r := Nat.gcd_eq_right (Nat.div_dvd_of_dvd hrdvd)
    rw [hgcd]
    have hmul : r * (m / r) = m := Nat.mul_div_cancel' hrdvd
    have hcancel : (r * (m / r)) / (m / r) * (m / r) = r * (m / r) :=
      Nat.div_mul_cancel (dvd_mul_left (m / r) r)
    have hkey : (r * (m / r)) / (m / r) = r := Nat.eq_of_mul_eq_mul_right hkpos hcancel
    calc m / (m / r) = (r * (m / r)) / (m / r) := by rw [hmul]
      _ = r := hkey
  have hβQ : ∀ v : V, b (vActEquiv hcenter ψ₀ v) (vActEquiv hcenter ψ₀ v) = b v v :=
    fun v => quad_vActEquiv hcenter ψ₀ hψ₀ker v
  have hβpow : ∀ v : V, (vActFun ψ₀)^[r] v = v := by
    intro v
    rw [vActFun_iterate hcenter ψ₀ r v, ← hψ₀ord, pow_orderOf_eq_one]
    rfl
  have hβne : vActFun ψ₀ ≠ id := by
    intro hid
    have hv : ∀ v : V, (ψ₀ (⟨v, 0⟩ : TwoStep V W b)).fst = v := by
      intro v
      have := congrFun hid v
      simpa [vActFun] using this
    have h2 : ψ₀ ^ 2 = 1 := by
      refine MulEquiv.ext (fun x => ?_)
      have hgen : ∀ (X : V) (w : W), ψ₀ (⟨X, w⟩ : TwoStep V W b) =
          ⟨X, (ψ₀ (⟨X, 0⟩ : TwoStep V W b)).snd + w⟩ := by
        intro X w
        have hsplit : (⟨X, w⟩ : TwoStep V W b) = ⟨X, 0⟩ * ⟨0, w⟩ := by
          ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, Biadd.zero_right]
        rw [hsplit, map_mul, hψ₀ker (⟨0, w⟩ : TwoStep V W b) rfl]
        ext <;> simp [TwoStep.fst_mul, TwoStep.snd_mul, hv, Biadd.zero_right]
      rw [pow_two, MulAut.mul_apply, hgen x.fst x.snd,
        hgen x.fst ((ψ₀ (⟨x.fst, 0⟩ : TwoStep V W b)).snd + x.snd)]
      show (⟨x.fst, _⟩ : TwoStep V W b) = x
      ext
      · rfl
      · show (ψ₀ (⟨x.fst, 0⟩ : TwoStep V W b)).snd +
          ((ψ₀ (⟨x.fst, 0⟩ : TwoStep V W b)).snd + x.snd) = x.snd
        rw [← add_assoc, AddExpTwo.add_self, zero_add]
    have hdiv2 : orderOf ψ₀ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hψ₀ord] at hdiv2
    have := Nat.le_of_dvd (by norm_num) hdiv2
    omega
  -- ## the subspace of fixed points of `β`
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact AddExpTwo.add_self v)
  let F : V →+ V := AddMonoidHom.mk' (vActFun ψ₀) (vActFun_add hcenter ψ₀)
  let βlin : V →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 F
  have hβlin_apply : ∀ v : V, βlin v = vActFun ψ₀ v := fun v => rfl
  let Sv : Submodule (ZMod 2) V := LinearMap.ker (βlin - 1)
  have hone_apply : ∀ v : V, (1 : V →ₗ[ZMod 2] V) v = v := fun v => rfl
  have hmemSv : ∀ v : V, v ∈ Sv ↔ vActFun ψ₀ v = v := by
    intro v
    rw [show v ∈ Sv ↔ (βlin - 1) v = 0 from Iff.rfl,
      LinearMap.sub_apply, hβlin_apply, hone_apply v, sub_eq_zero]
  have hSvne : Sv ≠ ⊤ := by
    intro h
    apply hβne
    funext v
    have hv : v ∈ Sv := by rw [h]; exact Submodule.mem_top
    exact (hmemSv v).mp hv
  have hfrV : Module.finrank (ZMod 2) V = 2 * n := by
    have h1 : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V), Nat.card_zmod]
    have h2 : Nat.card V = 2 ^ (2 * n) := by rw [hcardV, hn, ← pow_mul, Nat.mul_comm]
    have h3 : 2 ^ Module.finrank (ZMod 2) V = 2 ^ (2 * n) := by rw [← h1, h2]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h3
  have hfrSv : Module.finrank (ZMod 2) Sv < 2 * n := by
    rw [← hfrV]
    exact Submodule.finrank_lt hSvne
  have hcardSv : Nat.card Sv = 2 ^ Module.finrank (ZMod 2) Sv := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Sv), Nat.card_zmod]
  have hcardSv' : Nat.card Sv = Nat.card {v : V // vActFun ψ₀ v = v} :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1, (hmemSv x.1).mp x.2⟩
        invFun := fun x => ⟨x.1, (hmemSv x.1).mpr x.2⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun x => Subtype.ext rfl }
  -- ## commutation with `ξ`
  have hψ₀eq : ψ₀ = ξ ^ (j * (m / r)) := by
    rw [hψ₀def, hψdef, ← pow_mul]
  have hcommξ : ψ₀ * ξ = ξ * ψ₀ := by
    rw [hψ₀eq]
    calc ξ ^ (j * (m / r)) * ξ = ξ ^ (j * (m / r) + 1) := by rw [pow_add, pow_one]
      _ = ξ ^ (1 + j * (m / r)) := by rw [Nat.add_comm]
      _ = ξ ^ 1 * ξ ^ (j * (m / r)) := by rw [pow_add]
      _ = ξ * ξ ^ (j * (m / r)) := by rw [pow_one]
  have hcomm : ∀ v : V, (vActEquiv hcenter ψ₀) ((ξ (⟨v, 0⟩ : TwoStep V W b)).fst) =
      (ξ (⟨(vActEquiv hcenter ψ₀) v, 0⟩ : TwoStep V W b)).fst := by
    intro v
    change vActFun ψ₀ (vActFun ξ v) = vActFun ξ (vActFun ψ₀ v)
    rw [← vActFun_mul hcenter ψ₀ ξ v, hcommξ, vActFun_mul hcenter ξ ψ₀ v]
  -- ## a non-zero element of `W`
  haveI : Nontrivial W := by
    refine not_subsingleton_iff_nontrivial.mp (fun hsub => ?_)
    have h1 : Nat.card W = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
    omega
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  -- ## the two counting inputs
  have hfib := fiber_card_sq hcardV hW hinvol hcenter ξ htrans w₀ hw₀
  have hfix := fiber_fixed_card hcardV hW hinvol hcenter ξ htrans (vActEquiv hcenter ψ₀)
    hβQ hcomm w₀ hw₀
  have hfix' : Nat.card {v : V // vActFun ψ₀ v = v} - 1 =
      (Nat.card W - 1) * Nat.card {v : V // b v v = w₀ ∧ vActFun ψ₀ v = v} := by
    simpa [vActEquiv] using hfix
  -- ## the permutation of the fibre
  let X : Type := {v : V // b v v = w₀}
  haveI : Fintype X := Fintype.ofFinite X
  let σ : Equiv.Perm X := (vActEquiv hcenter ψ₀).toEquiv.subtypeEquiv (fun v => by
    rw [show (vActEquiv hcenter ψ₀).toEquiv v = vActEquiv hcenter ψ₀ v from rfl, hβQ v])
  have hσapply : ∀ x : X, (σ x).1 = vActFun ψ₀ x.1 := fun x => rfl
  have hσr : σ ^ r = 1 := by
    refine Equiv.Perm.ext (fun x => ?_)
    rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_one]
    have key : ∀ k : ℕ, ((⇑σ)^[k] x).1 = (vActFun ψ₀)^[k] x.1 := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hσapply, ih]
    refine Subtype.ext ?_
    rw [key r, hβpow x.1]
    rfl  -- ## the number `f` of `β`-fixed points in the fibre over `w₀`
  set f : ℕ := Nat.card {v : V // b v v = w₀ ∧ vActFun ψ₀ v = v} with hfdef
  have hcard_fix : σ.supportᶜ.card = f := by
    have h1 : Nat.card ↥(σ.supportᶜ) = σ.supportᶜ.card := by
      rw [Nat.card_eq_fintype_card]; exact Fintype.card_coe _
    rw [← h1]
    refine Nat.card_congr ?_
    refine
      { toFun := fun x => ⟨x.1.1, x.1.2, ?_⟩
        invFun := fun v => ⟨⟨v.1, v.2.1⟩, ?_⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun v => Subtype.ext rfl }
    · have hx : σ x.1 = x.1 := by
        have h := x.2
        rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at h
        exact h
      have h2 := congrArg Subtype.val hx
      rwa [hσapply x.1] at h2
    · rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not]
      apply Subtype.ext
      rw [hσapply]
      exact v.2.2
  have hmod : f ≡ Nat.card W + 1 [MOD r] := by
    have h1 : σ.supportᶜ.card ≡ Nat.card X [MOD r] := by
      have h := Equiv.Perm.card_compl_support_modEq (p := r) (n := 1) (by simpa using hσr)
      rwa [← Nat.card_eq_fintype_card] at h
    have h2 : f ≡ Nat.card X [MOD r] := by rw [← hcard_fix]; exact h1
    have h3 : Nat.card X = Nat.card W + 1 := by dsimp only [X]; exact hfib
    rw [h3] at h2
    exact h2
  have hW1 : 1 ≡ Nat.card W [MOD r] :=
    (Nat.modEq_iff_dvd' (by omega : 1 ≤ Nat.card W)).mpr hrdvd_q
  have hmod2 : f ≡ 2 [MOD r] := by
    have h := hW1.add_right 1
    exact hmod.trans (by simpa using h.symm)
  have hfge : 2 ≤ f := by
    have h1 : f % r = 2 := by
      have h2 : f % r = 2 % r := hmod2
      rwa [Nat.mod_eq_of_lt (by omega : 2 < r)] at h2
    calc 2 = f % r := h1.symm
      _ ≤ f := Nat.mod_le f r
  -- ## the contradiction
  have hkey : Nat.card {v : V // vActFun ψ₀ v = v} - 1 = (2 ^ n - 1) * f := by
    rw [hfix', hn]
  have hSval : 2 ^ Module.finrank (ZMod 2) Sv = Nat.card {v : V // vActFun ψ₀ v = v} := by
    rw [← hcardSv, hcardSv']
  have hdvd : 2 ^ n - 1 ∣ 2 ^ Module.finrank (ZMod 2) Sv - 1 := by
    rw [hSval]
    exact ⟨f, hkey⟩
  have hnd : n ∣ Module.finrank (ZMod 2) Sv :=
    (pow_sub_one_dvd_pow_sub_one_iff (x := 2) (m := n) (k := Module.finrank (ZMod 2) Sv)
      (by norm_num) hnpos).mp hdvd
  have hdgt : n < Module.finrank (ZMod 2) Sv := by
    have h2 : 2 ^ (n + 1) - 2 ≤ 2 ^ Module.finrank (ZMod 2) Sv - 1 := by
      rw [hSval, hkey]
      have hmul : (2 ^ n - 1) * 2 = 2 ^ (n + 1) - 2 := by rw [pow_succ]; omega
      rw [← hmul]
      exact Nat.mul_le_mul_left _ hfge
    have hpown : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hnpos
    have hpn : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
    have h3 : 2 ^ n < 2 ^ Module.finrank (ZMod 2) Sv := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
  obtain ⟨k, hk⟩ := hnd
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> omega
    · exact h
  have h2n : 2 * n ≤ Module.finrank (ZMod 2) Sv := by
    rw [hk]
    calc 2 * n = n * 2 := by ring
      _ ≤ n * k := Nat.mul_le_mul_left n hk2
  omega

/-- **A power of `ξ` fixing one involution fixes `kerFst` pointwise.**  If `ξ ^ t` fixes an
involution `x`, then for any involution `z` we have `ξ ^ k x = z` for some `k` (transitivity of
`ξ`), and the powers of `ξ` commute, so `(ξ ^ t) z = (ξ ^ k) ((ξ ^ t) x) = (ξ ^ k) x = z`. -/
theorem pow_fixes_kerFst
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (t : ℕ) (x : TwoStep V W b) (hx : orderOf x = 2) (hfix : (ξ ^ t) x = x) :
    ∀ z ∈ TwoStep.kerFst, (ξ ^ t) z = z := by
  intro z hz
  rcases eq_or_ne z 1 with hz1 | hz1
  · rw [hz1, map_one]
  · have hz2 : orderOf z = 2 := by
      refine (orderOf_eq_two_iff hinvol hcenter z).mpr ⟨hz, ?_⟩
      intro hsnd
      exact hz1 (TwoStep.ext_iff hz hsnd)
    obtain ⟨k, hk⟩ := htrans x z hx hz2
    calc (ξ ^ t) z = (ξ ^ t) ((ξ ^ k) x) := by rw [hk]
      _ = ((ξ ^ t) * (ξ ^ k)) x := by rw [MulAut.mul_apply]
      _ = (ξ ^ (t + k)) x := by rw [pow_add]
      _ = (ξ ^ (k + t)) x := by rw [Nat.add_comm]
      _ = ((ξ ^ k) * (ξ ^ t)) x := by rw [pow_add]
      _ = (ξ ^ k) ((ξ ^ t) x) := by rw [MulAut.mul_apply]
      _ = (ξ ^ k) x := by rw [hfix]
      _ = z := hk

/-- **The assembly.**  From the crux `hcrux` one gets a regular automorphism: `ζ := ξ ^ b` with
`b = orderOf ξ / (|W| - 1)` has order `|W| - 1`, its orbits on the involutions are regular (the
stabiliser of an involution is trivial by the crux) and it is fixed point free away from `1`. -/
theorem regular_aut_of_crux_aux
    (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y)
    (hcrux : ∀ j : ℕ, (∀ x ∈ TwoStep.kerFst, (ξ ^ j) x = x) →
      Nat.Coprime (orderOf (ξ ^ j)) (Nat.card W - 1)) :
    ∃ ζ : MulAut (TwoStep V W b),
      orderOf ζ = Nat.card W - 1 ∧
      (∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ζ ^ k) x = y) ∧
      (∀ x : TwoStep V W b, x ≠ 1 → ζ x ≠ x) := by
  classical
  haveI : Finite W := finite_of_hW hW
  haveI : Finite V := finite_V_of_hcardV hcardV hW
  -- the involutions are the non-zero elements of `kerFst`, so there are `|W| - 1` of them
  have hncard : Nat.card {x : TwoStep V W b // orderOf x = 2} = Nat.card W - 1 := by
    have h1 : Nat.card {x : TwoStep V W b // orderOf x = 2} = Nat.card {w : W // w ≠ 0} :=
      Nat.card_congr
        { toFun := fun x => ⟨x.1.snd, ((orderOf_eq_two_iff hinvol hcenter x.1).mp x.2).2⟩
          invFun := fun w => ⟨⟨0, w.1⟩, (orderOf_eq_two_iff hinvol hcenter _).mpr ⟨rfl, w.2⟩⟩
          left_inv := fun x => by
            refine Subtype.ext ?_
            exact TwoStep.ext_iff ((orderOf_eq_two_iff hinvol hcenter x.1).mp x.2).1.symm rfl
          right_inv := fun w => rfl }
    rw [h1, card_subtype_ne_zero]
  have hn2 : 2 ≤ Nat.card W - 1 := by omega
  set n : ℕ := Nat.card W - 1 with hndef
  have hnpos : 0 < n := by omega
  -- an involution of `TwoStep V W b` and its orbit under `⟨ξ⟩`
  haveI : Nontrivial W := by
    refine not_subsingleton_iff_nontrivial.mp (fun hsub => ?_)
    have h1 : Nat.card W = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
    omega
  obtain ⟨w₁, hw₁⟩ := exists_ne (0 : W)
  set u : TwoStep V W b := ⟨0, w₁⟩ with hudef
  have hu : orderOf u = 2 :=
    (orderOf_eq_two_iff hinvol hcenter u).mpr (by rw [hudef]; exact ⟨rfl, hw₁⟩)
  have horbξ : (MulAction.orbit (Subgroup.zpowers ξ) u : Set (TwoStep V W b)) =
      {z | orderOf z = 2} := by
    ext z
    rw [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ψ, rfl⟩
      show orderOf (ψ • u) = 2
      rw [show ψ • u = (ψ : MulAut (TwoStep V W b)) u from rfl, MulEquiv.orderOf_eq, hu]
    · intro hz
      obtain ⟨k, hk⟩ := htrans u z hu hz
      exact ⟨⟨ξ ^ k, Subgroup.pow_mem _ (Subgroup.mem_zpowers ξ) k⟩, hk⟩
  have hdiv : n ∣ orderOf ξ := by
    have hos := Nat.card_congr
      (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers ξ) u)
    rw [Nat.card_prod, Nat.card_zpowers] at hos
    have hcard : Nat.card ↥(MulAction.orbit (Subgroup.zpowers ξ) u) = n := by
      rw [Nat.card_coe_set_eq, horbξ, ← Nat.card_coe_set_eq, hndef]
      exact hncard
    rw [hcard] at hos
    exact ⟨Nat.card ↥(MulAction.stabilizer (Subgroup.zpowers ξ) u), hos.symm⟩
  set m : ℕ := orderOf ξ with hmdef
  have hmpos : 0 < m := by rw [hmdef]; exact orderOf_pos ξ
  have hdiv' : n ∣ m := by rw [hndef, hmdef]; exact hdiv
  set bd : ℕ := m / n with hbdef
  have hnb : n * bd = m := by rw [hbdef]; exact Nat.mul_div_cancel' hdiv'
  have hbpos : 0 < bd := by
    rw [hbdef]
    exact Nat.div_pos (Nat.le_of_dvd hmpos hdiv') hnpos
  set ζ : MulAut (TwoStep V W b) := ξ ^ bd with hζdef
  have hζord : orderOf ζ = n := by
    rw [hζdef, orderOf_pow, hbdef]
    have hg : m.gcd (m / n) = m / n := Nat.gcd_eq_right (Nat.div_dvd_of_dvd hdiv')
    rw [hg]
    have hcancel : (n * (m / n)) / (m / n) * (m / n) = n * (m / n) :=
      Nat.div_mul_cancel (dvd_mul_left (m / n) n)
    have hkey : (n * (m / n)) / (m / n) = n :=
      Nat.eq_of_mul_eq_mul_right (by rw [← hbdef]; exact hbpos) hcancel
    calc m / (m / n) = (n * (m / n)) / (m / n) := by rw [hnb]
      _ = n := hkey
  -- any power of `ζ` fixing an involution `x` is trivial
  have mem_nat : ∀ {ψ : MulAut (TwoStep V W b)}, ψ ∈ Subgroup.zpowers ζ → ∃ k : ℕ, ζ ^ k = ψ := by
    intro ψ hψ
    have hfin : IsOfFinOrder ζ := isOfFinOrder_of_finite ζ
    have h2 := (IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf hfin).mp hψ
    rcases Finset.mem_image.mp h2 with ⟨k, -, hk⟩
    exact ⟨k, hk⟩
  have key2 : ∀ (t : ℕ) (x : TwoStep V W b), orderOf x = 2 → (ζ ^ t) x = x → ζ ^ t = 1 := by
    intro t x hx hfix
    have hζt : ζ ^ t = ξ ^ (bd * t) := by rw [hζdef, ← pow_mul]
    have hfix' : (ξ ^ (bd * t)) x = x := by rw [← hζt]; exact hfix
    have hker := pow_fixes_kerFst hcardV hW hinvol hcenter ξ htrans (bd * t) x hx hfix'
    have hcop : Nat.Coprime (orderOf (ξ ^ (bd * t))) n := by
      rw [hndef]; exact hcrux (bd * t) hker
    have hdvd : orderOf (ξ ^ (bd * t)) ∣ n := by
      rw [← hζt, ← hζord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hone : orderOf (ξ ^ (bd * t)) ∣ 1 := by
      rw [← Nat.Coprime.gcd_eq_one hcop]
      exact Nat.dvd_gcd (dvd_refl _) hdvd
    rw [hζt]
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone)
  have hstabbot : ∀ x : TwoStep V W b, orderOf x = 2 →
      MulAction.stabilizer (Subgroup.zpowers ζ) x = ⊥ := by
    intro x hx
    rw [Subgroup.eq_bot_iff_forall]
    intro ψ hψmem
    have hψ : ψ • x = x := MulAction.mem_stabilizer_iff.mp hψmem
    obtain ⟨k, hk⟩ := mem_nat ψ.2
    have hψx : (ζ ^ k) x = x := by rw [hk]; exact hψ
    have h1 : ζ ^ k = 1 := key2 k x hx hψx
    exact Subtype.ext (by rw [← hk, h1]; rfl)
  refine ⟨ζ, hζord, ?_, ?_⟩
  · -- `ζ` is transitive on the involutions
    intro x y hx hy
    have hcard2 : ({z : TwoStep V W b | orderOf z = 2} : Set (TwoStep V W b)).ncard = n := by
      rw [← Nat.card_coe_set_eq]; exact hncard
    have horb : (MulAction.orbit (Subgroup.zpowers ζ) x : Set (TwoStep V W b)) =
        {z | orderOf z = 2} := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · intro z hz
        rw [MulAction.mem_orbit_iff] at hz
        obtain ⟨ψ, rfl⟩ := hz
        show orderOf (ψ • x) = 2
        rw [show ψ • x = (ψ : MulAut (TwoStep V W b)) x from rfl, MulEquiv.orderOf_eq, hx]
      · have hcard1 : (MulAction.orbit (Subgroup.zpowers ζ) x).ncard = n := by
          rw [← Nat.card_coe_set_eq]
          have hos := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (Subgroup.zpowers ζ) x)
          rw [Nat.card_prod, Nat.card_zpowers, hζord] at hos
          rw [hstabbot x hx, Subgroup.card_bot, mul_one] at hos
          exact hos
        rw [hcard2, hcard1]
    have hy' : y ∈ MulAction.orbit (Subgroup.zpowers ζ) x := by
      rw [horb]; exact hy
    rw [MulAction.mem_orbit_iff] at hy'
    obtain ⟨ψ, hψ⟩ := hy'
    obtain ⟨k, hk⟩ := mem_nat ψ.2
    exact ⟨k, by simpa using (hk ▸ hψ)⟩
  · -- `ζ` is fixed point free away from `1`
    intro x hx1 hfix
    have hx4 : x ^ 4 = 1 := by
      have h2 : x ^ 2 = (⟨0, b x.fst x.fst⟩ : TwoStep V W b) := TwoStep.sq_eq x
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, TwoStep.sq_eq]
      ext <;> simp [Biadd.zero_left]
    have hdvd4 : orderOf x ∣ 4 := orderOf_dvd_iff_pow_eq_one.mpr hx4
    obtain ⟨k, hk2, hkx⟩ := (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp
      (by simpa using hdvd4)
    have hζ1 : ζ = 1 := by
      interval_cases k
      · exact absurd (orderOf_eq_one_iff.mp (by simpa using hkx)) hx1
      · have hx2 : orderOf x = 2 := by simpa using hkx
        have hstab : (⟨ζ, Subgroup.mem_zpowers ζ⟩ : ↥(Subgroup.zpowers ζ)) ∈
            MulAction.stabilizer (Subgroup.zpowers ζ) x := by
          rw [MulAction.mem_stabilizer_iff]; simpa using hfix
        rw [hstabbot x hx2, Subgroup.mem_bot] at hstab
        simpa using congrArg Subtype.val hstab
      · have hx4o : orderOf x = 4 := by simpa using hkx
        have hz2 : orderOf (x ^ 2) = 2 := by
          rw [orderOf_pow, hx4o]; norm_num
        have hzfix : ζ (x ^ 2) = x ^ 2 := by rw [map_pow, hfix]
        have hstab : (⟨ζ, Subgroup.mem_zpowers ζ⟩ : ↥(Subgroup.zpowers ζ)) ∈
            MulAction.stabilizer (Subgroup.zpowers ζ) (x ^ 2) := by
          rw [MulAction.mem_stabilizer_iff]; simpa using hzfix
        rw [hstabbot (x ^ 2) hz2, Subgroup.mem_bot] at hstab
        simpa using congrArg Subtype.val hstab
    rw [hζ1, orderOf_one] at hζord
    omega

/-- **A regular automorphism exists.**  Higman (1963), §2. -/
theorem regular_aut_exists
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2)
    (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∃ ζ : MulAut (TwoStep V W b),
      orderOf ζ = Nat.card W - 1 ∧
      (∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ζ ^ k) x = y) ∧
      (∀ x : TwoStep V W b, x ≠ 1 → ζ x ≠ x) :=
  regular_aut_of_crux_aux hcardV hW hinvol hcenter ξ htrans
    (crux_of_powers hcardV hW hinvol hcenter ξ htrans)

end Work.Higman.Q3
