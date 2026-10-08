import Mathlib
import Submission.Work.ThmF.ChV3.Ctx
import Submission.Work.ThmF.ChV12.prop3_frobenius_power
import Submission.Work.ThmF.ChV12.prop1a
import Submission.Work.ThmF.ChV12.fpf_oddPart
import Submission.Work.ThmF.Bender.cardInvGeTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.step3` — Peterfalvi II, Ch. V §3, step (3)

Source (`REFS/peterfalvi_II_ch5_6.md`, l. 333–345):

> **(3)** For every prime `r` with `r ∣ |Q₁|` there is `i` with `0 ≤ i ≤ p-1` and
> `r ≡ 2^i (mod 2^p - 1)`.  In particular `r ≠ p`.
>
> *Proof.* Let `M` be an elementary abelian `r`-subgroup of `Q₁ = O_{2'}(Q)` normalised by `KP`,
> `M ≠ 1`, minimal for these properties; write `M` additively.  `KP` is a Frobenius group and `K`
> acts fixed-point-freely on `M`, so `C_M(P) ≠ 0` and `C_M(P)` has dimension `1` over `𝔽_r`.  By
> [Is] (15-16), `dim M = p·dim C_M(P) = p`.  By Clifford ([Is] (5-5)), `M` is a direct sum of
> irreducible `𝔽_r[K]`-modules of equal dimension; `dim M` being prime, either `M` has a submodule
> of dimension `1`, or `M` is irreducible as `𝔽_r[K]`-module.  In the first case, since `K` is
> fixed-point-free on `M` and `|K| = 2^p - 1`, `r ≡ 1 (mod 2^p - 1)`.  In the second case, by
> App. V, `M` carries a field structure such that `K ⋊ P` is a group of semilinear maps and
> `P = Aut(M)` since `dim M = p`; so there is `a ∈ P^#` with `x^a = x^r` for all `x ∈ K`, while by
> §1 Prop. 3 there is `i` with `x^a = x^{2^i}`; hence `r ≡ 2^i (mod 2^p − 1)`.

## Status

The paper's argument consumes two inputs that are **not** obtainable from the standing context
`CtxF H Q t s r P` as formalised (they are recorded here so that the gap is explicit):

* **`Q` is nilpotent** (Ch. V §1 Prop. 1 b).  The paper needs it so that `Q₁ = O_{2'}(Q)` is the
  Hall `2'`-subgroup of `Q`, whence its Sylow `r`-subgroups are `KP`-invariant and the minimal
  `M` of the proof exists.  Formally `Work.ThmF.ChV12.prop1b` needs `ThompsonFrobeniusProp`
  (Thompson's theorem on Frobenius kernels, hence Feit–Thompson, the single open hole of this
  project).  The sibling steps that need it carry it as an explicit hypothesis: `step5` and
  `step6` of this directory take `Group.IsNilpotent ↥Q`.
* **`dim C_M(P) = 1`**, which the paper gets from §3 (2) b), i.e. from `C_Q(P) ≅ F^×` for a
  near-field `F` (App. XI Prop. 1).  This is what upgrades the coprime-action dimension formula
  `dim M = p · dim C_M(P)` (Isaacs 15.16 / Wielandt, an external input of this project,
  `Work.ThmF.WielandtFixedPoint`) to `dim M = p`.  Without it the module-theoretic analysis only
  yields `r^{D} ≡ 2^i (mod 2^p - 1)` for `D = dim C_M(P)`, which does not imply the claim.

What is proved in this file (sorry-free) are the context-level preliminaries of the argument:

* `conj_mem_oddPart` — `oddPart Q` is normalised by `H`, hence by `K ≤ D ≤ H` and by `P ≤ V ≤ H`;
* `fpf_Kset_oddPart` — `K#` acts fixed-point-freely on `oddPart Q` (Ch. V §1 Prop. 1 a,
  `prop1a`): the hypothesis `C_M(K) = 1` of the dimension formula;
* `prime_ne_of_modEq_one`, `prime_ne_of_modEq_two_pow` — the number theory behind the last clause
  `r ≠ p` of step (3): a prime `r ≡ 2^i (mod 2^p - 1)` with `i < p` and `p` odd is `≠ p`, and the
  same for `r ≡ 1`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV3

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## `oddPart Q` is normalised by `H` (hence by `K` and by `P`) -/

/-- The set of odd-order elements of `Q` is invariant under conjugation by `H`, hence so is the
subgroup it generates, `oddPart Q`. -/
theorem conj_mem_oddPart {H Q : Subgroup G} {h : G} (hh : h ∈ H)
    (hN : H ≤ Subgroup.normalizer (Q : Set G)) {x : G} (hx : x ∈ oddPart Q) :
    h * x * h⁻¹ ∈ oddPart Q := by
  have hmem : ∀ y ∈ ({y : G | y ∈ Q ∧ Odd (orderOf y)} : Set G),
      (MulAut.conj h) y ∈ ({y : G | y ∈ Q ∧ Odd (orderOf y)} : Set G) := by
    intro y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    refine ⟨?_, ?_⟩
    · rw [MulAut.conj_apply]
      exact ((Subgroup.mem_normalizer_iff.mp (hN hh)) y).mp hy.1
    · have h1 : orderOf ((MulAut.conj h) y) = orderOf y :=
        orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective y
      rw [h1]
      exact hy.2
  have hle : Subgroup.map (MulAut.conj h).toMonoidHom (oddPart Q) ≤ oddPart Q := by
    rw [Subgroup.map_le_iff_le_comap]
    change Subgroup.closure {y : G | y ∈ Q ∧ Odd (orderOf y)} ≤
      Subgroup.comap (MulAut.conj h).toMonoidHom (oddPart Q)
    refine (Subgroup.closure_le _).mpr (fun y hy => ?_)
    show (MulAut.conj h).toMonoidHom y ∈ oddPart Q
    exact Subgroup.subset_closure (hmem y hy)
  have hmem' : (MulAut.conj h).toMonoidHom x ∈ oddPart Q :=
    hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem'

/-! ## `K#` acts fixed-point-freely on `oddPart Q` (Ch. V §1 Prop. 1 a) -/

/-- Ch. V §1 Prop. 1 a) (`Work.ThmF.ChV12.prop1a`), specialised to `oddPart Q`: no non-trivial
element of `K = J(D,t) = Kset H t` has a non-trivial fixed point on `oddPart Q`. -/
theorem fpf_Kset_oddPart (hS : Situation G) (hC4 : ChIIFourProp) {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {x y : G} (hx : x ∈ Kset H t) (hx1 : x ≠ 1)
    (hy : y ∈ oddPart Q) (hcomm : y * x = x * y) : y = 1 :=
  Work.ThmF.ChV12.prop1a hS hC4 H Q t h x hx hx1 y (oddPart_le Q hy) hcomm

/-- In the standing context, `oddPart Q` is invariant under conjugation by `K = J(D,t) ⊆ D ⊆ H`
(`Kset H t ⊆ twoPoint H t ⊆ H`, and `H` normalises `Q`). -/
theorem CtxF.conj_mem_oddPart_Kset {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) {k x : G} (hk : k ∈ Kset H t) (hx : x ∈ oddPart Q) :
    k * x * k⁻¹ ∈ oddPart Q :=
  conj_mem_oddPart (le_trans (Kset_subset H t) inf_le_left hk) c.split.normal hx

/-- In the standing context, `oddPart Q` is invariant under conjugation by `P ≤ V ≤ H`. -/
theorem CtxF.conj_mem_oddPart_P {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) {p x : G} (hp : p ∈ P) (hx : x ∈ oddPart Q) :
    p * x * p⁻¹ ∈ oddPart Q :=
  conj_mem_oddPart (le_trans (le_trans c.P_le inf_le_left) inf_le_left hp) c.split.normal hx

/-- In the standing context `K = J(D,t)` is non-trivial: `|K| = |Inv H| ≥ 2`
(Ch. I §2, `cardKsetEqInv`, and `cardInvGeTwo` applied to the four-group hypothesis of (B0)). -/
theorem CtxF.Kset_nontrivial {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) : ∃ k ∈ Kset H t, k ≠ 1 := by
  have h1 : (Kset H t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv c.split.stronglyEmbedded c.split.invol c.split.not_mem
  have h2 : 2 ≤ (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardInvGeTwo c.split.stronglyEmbedded c.sit.1.1
  by_contra hcon
  push_neg at hcon
  have hsub : Kset H t ⊆ ({1} : Set G) := fun k hk => by
    simp only [Set.mem_singleton_iff]
    exact hcon k hk
  have hle : (Kset H t).ncard ≤ 1 := by
    have h := Set.ncard_le_ncard hsub
    simpa using h
  omega

/-- In the standing context `P ≤ V = C_D(t)` normalises `K = J(D,t)`: for `p ∈ P` and `k ∈ K`,
`p * k * p⁻¹ ∈ K` (as `t` commutes with `p` and inverts `k`).  Consequently `K^p = K` for every
`p ∈ P`, so the Frobenius hypothesis `K ⊓ K^g = ⊥` (`g ∈ P^#`) of `WielandtFixedPoint` — the
fixed-point formula used by step (4) — fails as soon as `P ≠ 1` and `K ≠ 1`. -/
theorem CtxF.mem_Kset_conj_P {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : CtxF H Q t s r P) {p k : G} (hp : p ∈ P) (hk : k ∈ Kset H t) :
    p * k * p⁻¹ ∈ Kset H t := by
  obtain ⟨hkD, hkt⟩ := hk
  have hpD : p ∈ twoPoint H t := (Subgroup.mem_inf.mp (c.P_le hp)).1
  have hpC : p ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp (c.P_le hp)).2
  have htp : t * p = p * t := (Subgroup.mem_centralizer_iff.mp hpC) t (Set.mem_singleton t)
  have hpt : t * p⁻¹ * t⁻¹ = p⁻¹ := by
    have h1 : t * p * t⁻¹ = p := by rw [htp]; group
    calc t * p⁻¹ * t⁻¹ = (t * p * t⁻¹)⁻¹ := by group
      _ = p⁻¹ := by rw [h1]
  refine mem_Kset_iff.mpr ⟨?_, ?_⟩
  · exact (twoPoint H t).mul_mem ((twoPoint H t).mul_mem hpD hkD) ((twoPoint H t).inv_mem hpD)
  · calc t * (p * k * p⁻¹) * t⁻¹ = (t * p * t⁻¹) * (t * k * t⁻¹) * (t * p⁻¹ * t⁻¹) := by group
      _ = p * k⁻¹ * p⁻¹ := by
          rw [show t * p * t⁻¹ = p from by rw [htp]; group, hpt, hkt]
      _ = (p * k * p⁻¹)⁻¹ := by group

/-! ## Number theory: the last clause `r ≠ p` -/

/-- For `0 < p`, `2 * p ≤ 2 ^ p`. -/
private theorem two_mul_le_two_pow {p : ℕ} (hp : 0 < p) : 2 * p ≤ 2 ^ p := by
  have hle : p ≤ 2 ^ (p - 1) := by
    have := Nat.lt_two_pow_self (n := p - 1)
    omega
  have h2 : 2 * 2 ^ (p - 1) = 2 ^ p := by
    rw [mul_comm 2, ← pow_succ, Nat.sub_one_add_one hp.ne']
  calc 2 * p ≤ 2 * 2 ^ (p - 1) := Nat.mul_le_mul_left 2 hle
    _ = 2 ^ p := h2

/-- For a prime `p`, `p < 2 ^ p - 1`. -/
private theorem lt_two_pow_sub_one {p : ℕ} (hp : p.Prime) : p < 2 ^ p - 1 := by
  have h := two_mul_le_two_pow hp.pos
  have h2 : 2 ≤ p := hp.two_le
  omega

/-- `1 < 2 ^ (p - 1)` for `2 ≤ p`. -/
private theorem one_lt_two_pow_pred {p : ℕ} (hp : 2 ≤ p) : 1 < 2 ^ (p - 1) := by
  have h5 : 2 ≤ 2 ^ (p - 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `2 ^ i < 2 ^ p - 1` for `i < p` and `p` an odd prime. -/
private theorem pow_two_lt {p i : ℕ} (hp : p.Prime) (hpo : Odd p) (hi : i < p) :
    2 ^ i < 2 ^ p - 1 := by
  have h1 : 2 ^ i ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_one_add_one (by omega : p ≠ 0)]
  have h5 : 1 < 2 ^ (p - 1) := one_lt_two_pow_pred hp.two_le
  omega

/-- If `r` is a prime congruent to `2 ^ i` modulo `2 ^ p - 1` with `i < p` and `p` an odd prime,
then `r ≠ p` (the last clause of step (3)). -/
theorem prime_ne_of_modEq_two_pow {p i r : ℕ} (hp : p.Prime) (hpo : Odd p) (hi : i < p)
    (h : r ≡ 2 ^ i [MOD 2 ^ p - 1]) : r ≠ p := by
  intro hEq
  have h2 : p ≡ 2 ^ i [MOD 2 ^ p - 1] := hEq ▸ h
  have heq : p = 2 ^ i := Nat.ModEq.eq_of_lt_of_lt h2 (lt_two_pow_sub_one hp) (pow_two_lt hp hpo hi)
  have hodd : Odd (2 ^ i) := heq ▸ hpo
  have h2p : 2 ≤ p := hp.two_le
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    simp only [pow_zero] at heq
    omega
  · have hEven : Even (2 ^ i) :=
      even_iff_two_dvd.mpr ⟨2 ^ (i - 1),
        by rw [mul_comm 2, ← pow_succ, Nat.sub_one_add_one hipos.ne']⟩
    exact (Nat.not_even_iff_odd.mpr hodd) hEven

/-- If `r` is a prime congruent to `1` modulo `2 ^ p - 1` and `p` is a prime, then `r ≠ p`. -/
theorem prime_ne_of_modEq_one {p r : ℕ} (hp : p.Prime) (h : r ≡ 1 [MOD 2 ^ p - 1]) :
    r ≠ p := by
  intro hEq
  have h2 : p ≡ 1 [MOD 2 ^ p - 1] := hEq ▸ h
  have hm : 1 < 2 ^ p - 1 := by
    have h3 : 2 ^ 2 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp.two_le
    omega
  have h2p : 2 ≤ p := hp.two_le
  have := Nat.ModEq.eq_of_lt_of_lt h2 (lt_two_pow_sub_one hp) hm
  omega

/-! ## The target -/


end Work.ThmF.ChV3
