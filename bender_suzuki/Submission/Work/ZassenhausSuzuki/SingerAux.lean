import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerData
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausSuzuki.QSZPrelim
import Submission.Work.ZassenhausSuzuki.Shadow.X5isoPSL2_of
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.twoPoint_conj_inf_eq_bot
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ZassenhausTwoGroup.card_H_eq
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-!
Suzuki 1962, §8, pp. 117–118 (first half): with `S` the Singer-cycle data inside
`X5 H t = ⟨Q₀,K,t⟩ ≅ LF(2,q)` (`q = |Q0sub H|`, `|S.V| = q+1`, `|twoPoint H t| = q-1`) in the
Zassenhaus split rank-one setting with `Q` a non-abelian `2`-group and `σ = ρ`, one has
`C_G(S.V) = S.V` and `|N_G(S.V)| = 2(q + 1)`.

The two hypotheses `hD3`, `hC1` are the two inputs proved elsewhere in this workspace:
`Work.ZassenhausSuzuki.strongly_real_conj_structure` (every strongly real `x` with `x * x ≠ 1`
is conjugate into `Q`, `twoPoint H t` or `S.V`) and
`Work.ZassenhausSuzuki.centralizer_twoPoint_eq` (`C_G(k) = twoPoint H t` for
`k ∈ twoPoint H t`, `k ≠ 1`).

Route (Suzuki pp. 117–118):
1. `|twoPoint H t| = q - 1` (`Work.ZassenhausSuzuki.twoPoint_card_add_one_eq_center_card` plus
   `Q0sub_card_eq_center_card`), `|S.V| = q+1`, and `q = |Q0sub H| ≥ 4`; so `|S.V|` is odd `> 1`.
   Every `v ∈ S.V#` is therefore strongly real with `v * v ≠ 1`, and Proposition 14
   (`Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real`) gives: `C_G(v)` is abelian of
   odd order, and `C_G(z) = C_G(v)` for every `z ∈ C_G(v)#`.
2. `W := C_G(S.V) ≤ C_G(v)`, hence `W` is abelian of odd order.
3. For `ω ∈ W#`: `W ≤ C_G(ω)`, so `C_G(ω) = C_G(v)` by 1; and since `C_G(ω)` is abelian and
   contains `S.V`, it lies in `C_G(S.V) = W`.  Hence `C_G(ω) = W` for all `ω ∈ W#`.
4. Apply `hD3` to `ω ∈ W#` (strongly real, `ω * ω ≠ 1`).  The `Q`-case is impossible
   (`orderOf ω` would divide a power of `2`, while `|W|` is odd), and the `twoPoint H t`-case is
   impossible (`C_G(ω) ≅ C_G(k)` has order `q - 1` by `hC1`, but `q + 1 ≤ |W| = |C_G(ω)|`).  So
   every `ω ∈ W#` is conjugate into `S.V#`.
5. **Count.**  The classes of strongly real elements `≠ 1` of `G` are the class of the
   involutions together with the classes of the products `π τ`, `π ∈ Inv(Q)` (Proposition 13,
   `Work.ThmF.ChV12.exists_conj_eq_inv_mul_t`), of which there are `q - 1` — and a `π τ ~ π' τ`
   iff `π = π'` — so there are exactly `q` such classes.  The `(q-2)/2` classes of
   `(twoPoint H t)#` (paired by inversion, and no further fusion by the argument of
   `centralizer_twoPoint_eq`: a `g` conjugating `k, k' ∈ twoPoint H t` normalises
   `twoPoint H t = D ⊔ ⟨t⟩`-wise, giving `k' = k^{±1}`) and the `q/2` classes meeting
   `S.V#` account for all `q`.  Hence `v ~ v'` for `v, v' ∈ S.V` iff `v' = v^{±1}`, and the
   classes meeting `W#` are exactly those meeting `S.V#`.
6. `N_G(W)` acts freely on `W#` by 3, so the classes meeting `W#` are the `N_G(W)`-orbits and
   number `(w-1)/l`, `w = |W|`, `l = |N_G(W)/W|`; by 4./5. this is `q/2`, i.e. `w - 1 = l q/2`.
7. If `W ≠ S.V`:  `q + 1 ∣ w` (as `S.V ≤ W`); if `q + 1` were composite, a prime `p ∣ q+1`,
   `p < q+1`, together with a conjugate `V' ≠ S.V` with `V' ≤ W` (exists by 4.) yields an element
   of order `q+1` in `W` generating a cyclic group of order `q+1` conjugate to `S.V` but meeting
   `S.V` in a nontrivial subgroup — contradicting 5.  So `q + 1 = p` is prime; every element of
   `W#` has order `p`, so `W` is a `p`-group and `w = p^n`.  `w - 1 = l(p-1)/2` with `l` a power
   of `2` (`N_G(W)/W` is a `2`-group by Proposition 14) gives that `1 + p + ⋯ + p^{n-1}` is a
   power of `2`; the `n` summands being odd, `n` is even; for `n = 2m` the factorisation
   `p^n - 1 = (p^m-1)(p^m+1)` into two almost-coprime even factors forces `p^m - 1 = 2`, i.e.
   `p = 3`, `q = 2`, contradicting `q ≥ 4`.  Hence `n = 1`, `w = q+1`, `W = S.V`.
8. Then `w - 1 = lq/2` with `w = q+1` gives `q = lq/2`, i.e. `l = 2`, so
   `|N_G(S.V)| = |N_G(W)| = l·w = 2(q+1)`.

This file formalises the cardinality inputs, `S.V ∩ H^g = 1`, and the *orbit form* of the
self-centralising step (a geometric argument that bypasses the count of step 5 once one knows
that `C_G(S.V)` permutes the `S.V`-orbits with a fixed point).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-! ## Cardinality inputs -/

/-- `q = |Q0sub H|` is a power of two, `q = 2 ^ n` with `n ≥ 2`. -/
theorem Q0sub_card_eq_two_pow (h : SzHyp H Q t s) :
    ∃ n : ℕ, 2 ≤ n ∧ Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n := by
  obtain ⟨n, hn, hc, -⟩ := Work.ZassenhausSuzuki.Shadow.ChV12.X5isoPSL2_of h
  exact ⟨n, hn, hc⟩

/-- `q = |Q0sub H| ≥ 4`. -/
theorem four_le_Q0sub_card (h : SzHyp H Q t s) : 4 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := by
  obtain ⟨n, hn, hc⟩ := Q0sub_card_eq_two_pow h
  rw [hc]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- `|twoPoint H t| = q - 1`. -/
theorem twoPoint_card_eq_Q0sub_sub_one (h : SzHyp H Q t s) :
    Nat.card ↥(twoPoint H t) = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
  have hd := twoPoint_card_eq_involutions (H := H) (Q := Q) (t := t) h.split h.zass h.two
  have hInvQ : (involutions (Q : Set G)) = (involutions (H : Set G)) := by
    ext x
    constructor
    · intro hx; exact ⟨h.split.le hx.1, hx.2⟩
    · intro hx
      have hx' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h.split h.two x hx)
      exact ⟨hx'.1, hx.2⟩
  rw [hd, hInvQ]
  have hc := Work.ThmF.L5.card_Q0sub_eq (H := H) h.hcomm
  omega

/-- `|H| = |Q| (q - 1)`. -/
theorem card_H_eq' (h : SzHyp H Q t s) :
    Nat.card ↥H = Nat.card ↥Q * (Nat.card ↥(Work.ThmF.Q0sub H) - 1) := by
  rw [Work.ZassenhausTwoGroup.card_H_eq h.split, twoPoint_card_eq_Q0sub_sub_one h]

/-- `q + 1` and `q - 1` are coprime (`q` is even). -/
theorem coprime_Q0sub_add_one_sub_one (h : SzHyp H Q t s) :
    Nat.Coprime (Nat.card ↥(Work.ThmF.Q0sub H) + 1) (Nat.card ↥(Work.ThmF.Q0sub H) - 1) := by
  obtain ⟨n, hn, hc⟩ := Q0sub_card_eq_two_pow h
  have heven : Even (Nat.card ↥(Work.ThmF.Q0sub H)) := by
    rw [hc]
    refine ⟨2 ^ (n - 1), ?_⟩
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega, pow_succ']
    rw [h2, two_mul]
  rw [Nat.coprime_iff_gcd_eq_one]
  have hodd : Odd (Nat.card ↥(Work.ThmF.Q0sub H) + 1) := by
    rcases heven with ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
  have hgodd : Odd (Nat.gcd (Nat.card ↥(Work.ThmF.Q0sub H) + 1)
      (Nat.card ↥(Work.ThmF.Q0sub H) - 1)) := Odd.of_dvd_nat hodd (Nat.gcd_dvd_left _ _)
  have hpos : 1 ≤ Nat.card ↥(Work.ThmF.Q0sub H) := Nat.card_pos
  have hdvd : Nat.gcd (Nat.card ↥(Work.ThmF.Q0sub H) + 1)
      (Nat.card ↥(Work.ThmF.Q0sub H) - 1) ∣ 2 := by
    have h1 := Nat.gcd_dvd_left (Nat.card ↥(Work.ThmF.Q0sub H) + 1)
      (Nat.card ↥(Work.ThmF.Q0sub H) - 1)
    have h2 := Nat.gcd_dvd_right (Nat.card ↥(Work.ThmF.Q0sub H) + 1)
      (Nat.card ↥(Work.ThmF.Q0sub H) - 1)
    have h3 := Nat.dvd_sub h1 h2
    rwa [show (Nat.card ↥(Work.ThmF.Q0sub H) + 1) - (Nat.card ↥(Work.ThmF.Q0sub H) - 1) = 2
      from by omega] at h3
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hh | hh
  · exact hh
  · rw [hh] at hgodd; rcases hgodd with ⟨k, hk⟩; omega

/-- `q + 1` is coprime to `|H| = |Q| (q - 1)`. -/
theorem coprime_Q0sub_add_one_card_H (h : SzHyp H Q t s) :
    Nat.Coprime (Nat.card ↥(Work.ThmF.Q0sub H) + 1) (Nat.card ↥H) := by
  rw [card_H_eq' h]
  refine Nat.Coprime.mul_right ?_ (coprime_Q0sub_add_one_sub_one h)
  obtain ⟨e, he⟩ := h.two.exists_card_eq
  rw [he]
  refine Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr ?_)
  obtain ⟨n, hn, hc⟩ := Q0sub_card_eq_two_pow h
  have heven : Even (Nat.card ↥(Work.ThmF.Q0sub H)) := by
    rw [hc]
    refine ⟨2 ^ (n - 1), ?_⟩
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 from by omega, pow_succ']
    rw [h2, two_mul]
  rcases heven with ⟨k, hk⟩
  exact ⟨k, by omega⟩

/-! ## `S.V` meets every conjugate of `H` trivially -/

/-- `S.V ∩ H^g = ⊥` for every `g`: `|S.V| = q+1` is coprime to `|H|`. -/
theorem singerV_inf_conj_H (h : SzHyp H Q t s) (S : SingerCycle.Data G H t) (g : G) :
    S.V ⊓ Submission.Blueprint.conj g H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxV, hxgH⟩ := Subgroup.mem_inf.mp hx
  have hdvdV : orderOf x ∣ Nat.card ↥S.V := Subgroup.orderOf_dvd_natCard _ hxV
  have hdvdH : orderOf x ∣ Nat.card ↥H := by
    have hcard : Nat.card ↥(Submission.Blueprint.conj g H) = Nat.card ↥H :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective (K := H)
    have h1 := Subgroup.orderOf_dvd_natCard (Submission.Blueprint.conj g H) hxgH
    rwa [hcard] at h1
  have hcop : Nat.Coprime (Nat.card ↥S.V) (Nat.card ↥H) := by
    rw [S.card_V]
    exact coprime_Q0sub_add_one_card_H h
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdV hdvdH)

/-- The points `a • x` for `a ∈ S.V` are pairwise distinct. -/
theorem singerV_smul_mk_injective (h : SzHyp H Q t s) (S : SingerCycle.Data G H t) {x a b : G}
    (ha : a ∈ S.V) (hb : b ∈ S.V)
    (hmk : (QuotientGroup.mk (a * x) : G ⧸ H) = QuotientGroup.mk (b * x)) : a = b := by
  have hmem : (a * x)⁻¹ * (b * x) ∈ H := QuotientGroup.eq.mp hmk
  have hxH : x⁻¹ * (a⁻¹ * b) * x ∈ H := by
    have h1 : (a * x)⁻¹ * (b * x) = x⁻¹ * (a⁻¹ * b) * x := by group
    rwa [h1] at hmem
  have hconj : a⁻¹ * b ∈ Submission.Blueprint.conj x H :=
    (Work.DoubleTransitivity.mem_conj x (a⁻¹ * b) H).mpr hxH
  have hbot : a⁻¹ * b ∈ S.V ⊓ Submission.Blueprint.conj x H :=
    ⟨S.V.mul_mem (S.V.inv_mem ha) hb, hconj⟩
  rw [singerV_inf_conj_H h S x] at hbot
  rw [Subgroup.mem_bot] at hbot
  exact inv_mul_eq_one.mp hbot

/-! ## The orbit form of the self-centralising step -/

/-- **The self-centralising step, orbit form.**  If `w` centralises `S.V` and maps one point
into its `S.V`-orbit, then `w ∈ S.V`.

Geometrically: `v₀⁻¹ w` fixes the whole orbit `S.V • x` (because `w` commutes with `S.V`), and
that orbit has `|S.V| = q + 1 ≥ 3` distinct points, so the Zassenhaus condition forces
`v₀⁻¹ w = 1`. -/
theorem centralizer_mem_of_fixes_orbit (h : SzHyp H Q t s) (S : SingerCycle.Data G H t)
    {w x : G} (hw : w ∈ Subgroup.centralizer (S.V : Set G))
    (hwx : ∃ v ∈ S.V, w • (QuotientGroup.mk x : G ⧸ H) =
      v • (QuotientGroup.mk x : G ⧸ H)) : w ∈ S.V := by
  classical
  obtain ⟨v₀, hv₀, hfix⟩ := hwx
  haveI hcyc : IsCyclic ↥S.V := S.cyclic
  haveI : IsMulCommutative ↥S.V := IsCyclic.isMulCommutative
  -- `v₀⁻¹ * w` fixes every point of the `S.V`-orbit of `x`
  have key : ∀ u ∈ S.V, (v₀⁻¹ * w) • (u • (QuotientGroup.mk x : G ⧸ H)) =
      u • (QuotientGroup.mk x : G ⧸ H) := by
    intro u hu
    have hcomm : u * w = w * u := Subgroup.mem_centralizer_iff.mp hw u hu
    have hcomm' : v₀⁻¹ * (u * v₀) = u := by
      have huv : u * v₀ = v₀ * u := by
        have h2 := mul_comm' (⟨u, hu⟩ : ↥S.V) (⟨v₀, hv₀⟩ : ↥S.V)
        exact congrArg Subtype.val h2
      rw [huv, ← mul_assoc, inv_mul_cancel, one_mul]
    have haux : w • (u • (QuotientGroup.mk x : G ⧸ H)) =
        u • (v₀ • (QuotientGroup.mk x : G ⧸ H)) :=
      calc w • (u • (QuotientGroup.mk x : G ⧸ H))
          = (w * u) • (QuotientGroup.mk x : G ⧸ H) := by rw [mul_smul]
        _ = (u * w) • (QuotientGroup.mk x : G ⧸ H) := by rw [← hcomm]
        _ = u • (w • (QuotientGroup.mk x : G ⧸ H)) := by rw [mul_smul]
        _ = u • (v₀ • (QuotientGroup.mk x : G ⧸ H)) := by rw [hfix]
    calc (v₀⁻¹ * w) • (u • (QuotientGroup.mk x : G ⧸ H))
        = v₀⁻¹ • (w • (u • (QuotientGroup.mk x : G ⧸ H))) := by rw [mul_smul]
      _ = v₀⁻¹ • (u • (v₀ • (QuotientGroup.mk x : G ⧸ H))) := by rw [haux]
      _ = (v₀⁻¹ * (u * v₀)) • (QuotientGroup.mk x : G ⧸ H) := by rw [mul_smul, mul_smul]
      _ = u • (QuotientGroup.mk x : G ⧸ H) := by rw [hcomm']
  -- an element of `S.V` different from `1` and from its inverse
  obtain ⟨n, hn, hc⟩ := Q0sub_card_eq_two_pow h
  have hcardV : 2 ≤ Nat.card ↥S.V := by
    rw [S.card_V, hc]; have := Nat.one_le_two_pow (n := n); omega
  haveI : Fintype ↥S.V := Fintype.ofFinite _
  have hcardV' : 2 ≤ Fintype.card ↥S.V := by rw [← Nat.card_eq_fintype_card]; exact hcardV
  obtain ⟨u₀, hu₀⟩ := Fintype.exists_ne_of_one_lt_card (α := ↥S.V) (by omega) (1 : ↥S.V)
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ S.V, u ≠ 1 := ⟨u₀, u₀.2, fun hcon => hu₀ (Subtype.ext hcon)⟩
  have hoddV : Odd (Nat.card ↥S.V) := by
    rw [S.card_V]
    refine ⟨2 ^ (n - 1), ?_⟩
    have hn1 : n = (n - 1) + 1 := by omega
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      conv_lhs => rw [hn1, pow_succ']
    rw [hc, h2]
  have hoddord : Odd (orderOf u) := hoddV.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hu)
  have hu2 : u * u ≠ 1 := by
    intro hsq
    have hdvd : orderOf u ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
    have h1 : orderOf u = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · exfalso; rw [h] at hoddord; rcases hoddord with ⟨j, hj⟩; omega
    exact hu1 (orderOf_eq_one_iff.mp h1)
  have hu_ne_inv : u ≠ u⁻¹ := fun hcon => hu2 (mul_eq_one_iff_eq_inv.mpr hcon)
  -- the three distinct fixed points
  have hp12 : (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk (u * x) := by
    intro hcon
    have h2 := singerV_smul_mk_injective h S (S.V.one_mem) hu (by simpa using hcon)
    exact hu1 h2.symm
  have hp13 : (QuotientGroup.mk x : G ⧸ H) ≠ QuotientGroup.mk (u⁻¹ * x) := by
    intro hcon
    have h2 := singerV_smul_mk_injective h S (S.V.one_mem) (S.V.inv_mem hu) (by simpa using hcon)
    exact hu1 (inv_eq_one.mp h2.symm)
  have hp23 : (QuotientGroup.mk (u * x) : G ⧸ H) ≠ QuotientGroup.mk (u⁻¹ * x) := by
    intro hcon
    exact hu_ne_inv (singerV_smul_mk_injective h S hu (S.V.inv_mem hu) hcon)
  have hf1 : (v₀⁻¹ * w) • (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x := by
    simpa using key 1 S.V.one_mem
  have hf2 : (v₀⁻¹ * w) • (QuotientGroup.mk (u * x) : G ⧸ H) =
      QuotientGroup.mk (u * x) := by
    simpa using key u hu
  have hf3 : (v₀⁻¹ * w) • (QuotientGroup.mk (u⁻¹ * x) : G ⧸ H) =
      QuotientGroup.mk (u⁻¹ * x) := by
    simpa using key u⁻¹ (S.V.inv_mem hu)
  have h1 : v₀⁻¹ * w = 1 := h.zass _ _ _ hp12 hp13 hp23 _ hf1 hf2 hf3
  have hwv : w = v₀ := by
    have h2 := eq_inv_of_mul_eq_one_left h1
    exact (inv_inj.mp h2).symm
  rw [hwv]; exact hv₀

/-- **Suzuki 1962, Proposition 1 in the `(ZT)` setting.**  In the split rank-one Zassenhaus
configuration with `Q` a `2`-group, the centraliser of *any* involution of `G` is a `2`-group:
every involution is conjugate into `H` (`Work.ThmF.Bender.exists_conj_of_involution`), and the
centraliser of an involution of `H` is contained in the `2`-group `Q`
(`centralizer_le_Q_of_mem_involutions`).

This is the input used by the `N_G(C_G(z))/C_G(z)` is-a-`2`-group clause of Proposition 14: the
odd-order elements of `N_G(A)` are killed by showing they commute with an involution. -/
theorem isPGroup_centralizer_involution (h : SzHyp H Q t s) {u : G} (hu : orderOf u = 2) :
    ∃ e : ℕ, Nat.card ↥(Subgroup.centralizer ({u} : Set G)) = 2 ^ e := by
  obtain ⟨g, hg⟩ :=
    Work.ThmF.Bender.exists_conj_of_involution (H := H) h.split.stronglyEmbedded hu
  have hvH : g⁻¹ * u * g ∈ H := (Work.DoubleTransitivity.mem_conj g u H).mp hg
  have hv2 : orderOf (g⁻¹ * u * g) = 2 := by
    rw [show g⁻¹ * u * g = g⁻¹ * u * (g⁻¹)⁻¹ from by group,
      Work.ThmF.Bender.orderOf_conj_eq]
    exact hu
  have hle := centralizer_le_Q_of_mem_involutions h.split h.zass h.two ⟨hvH, hv2⟩
  have hle' : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.map (MulAut.conj g).toMonoidHom Q := by
    intro x hx
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · refine hle ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      calc (g⁻¹ * x * g) * (g⁻¹ * u * g) = g⁻¹ * (x * u) * g := by group
        _ = g⁻¹ * (u * x) * g := by rw [hx']
        _ = (g⁻¹ * u * g) * (g⁻¹ * x * g) := by group
    · show MulAut.conj g (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group
  obtain ⟨e, he⟩ := h.two.exists_card_eq
  have hdvd : Nat.card ↥(Subgroup.centralizer ({u} : Set G)) ∣ 2 ^ e := by
    have h1 := Subgroup.card_dvd_of_le hle'
    have h2 : Nat.card ↥(Subgroup.map (MulAut.conj g).toMonoidHom Q) = Nat.card ↥Q :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective (K := Q)
    rwa [h2, he] at h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, hk⟩

/-- **Sub-step 1 of the `N_G(A)/A`-is-a-`2`-group clause of Suzuki's Proposition 14.**
Let `z` be strongly real with `z * z ≠ 1`, `A = C_G(z)`, and let `y ∈ N_G(A)` be an involution
with `y ∉ A`.  Then `y` inverts `A`, i.e. `y A y⁻¹` acts on `A` as inversion.  Consequently the
whole coset `yA` consists of involutions.

Proof: if `a ∈ A` with `y a y⁻¹ ≠ a⁻¹`, then `b := a · (y a y⁻¹) ∈ A` satisfies
`b ≠ 1` and `y b y⁻¹ = b` (because `y a y⁻¹ · y (y a y⁻¹) y⁻¹ = (y a y⁻¹)·a` and `A` is abelian),
so `y ∈ C_G(b) = A` by the Prop. 14 clause `C_G(a') = C_G(z)` for `a' ∈ A#` — contradiction. -/
theorem involution_inverts_centralizer (h : SzHyp H Q t s) {z y : G} (hz2 : z * z ≠ 1)
    (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z)
    (hyN : y ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    (hy2 : y * y = 1)
    (hyA : y ∉ Subgroup.centralizer ({z} : Set G)) :
    ∀ a ∈ Subgroup.centralizer ({z} : Set G), y * a * y⁻¹ = a⁻¹ := by
  obtain ⟨hAcom, -, hcent⟩ := centralizer_abelian_of_strongly_real h.split h.zass h.two hz2 hsr
  haveI : IsMulCommutative ↥(Subgroup.centralizer ({z} : Set G)) := hAcom
  intro a ha
  by_contra hne
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hσA : y * a * y⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hyN a).mp ha
  set b : G := a * (y * a * y⁻¹) with hbdef
  have hb : b ∈ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.centralizer ({z} : Set G)).mul_mem ha hσA
  have hb_ne : b ≠ 1 := by
    intro h1
    apply hne
    have h3 : a⁻¹ * b = a⁻¹ := by rw [h1, mul_one]
    rw [hbdef, mul_assoc] at h3
    simpa [mul_assoc] using h3
  have hfix : y * b * y⁻¹ = b := by
    have h5 : y * (y * a * y⁻¹) * y⁻¹ = a := by
      rw [hyinv]
      rw [show y * (y * a * y) * y = (y * y) * a * (y * y) from by group, hy2,
        one_mul, mul_one]
    have hcomm : (y * a * y⁻¹) * a = a * (y * a * y⁻¹) := by
      have h4 := mul_comm' (⟨a, ha⟩ : ↥(Subgroup.centralizer ({z} : Set G)))
        (⟨y * a * y⁻¹, hσA⟩ : ↥(Subgroup.centralizer ({z} : Set G)))
      exact (congrArg Subtype.val h4).symm
    rw [hbdef]
    calc y * (a * (y * a * y⁻¹)) * y⁻¹
        = (y * a * y⁻¹) * (y * (y * a * y⁻¹) * y⁻¹) := by group
      _ = (y * a * y⁻¹) * a := by rw [h5]
      _ = a * (y * a * y⁻¹) := hcomm
  have hcommyb : y * b = b * y := by
    calc y * b = (y * b * y⁻¹) * y := by group
      _ = b * y := by rw [hfix]
  have hmem : y ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcommyb
  rw [(hcent b hb hb_ne).2] at hmem
  exact hyA hmem

/-- **`C_G(C_G(z)) = C_G(z)`**, i.e. an element commuting with everything in `C_G(z)` lies in
`C_G(z)`: test against `z`. -/
theorem mem_centralizer_of_commutes (h : SzHyp H Q t s) {z g : G}
    (hg : ∀ a ∈ Subgroup.centralizer ({z} : Set G), g * a = a * g) :
    g ∈ Subgroup.centralizer ({z} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hg z (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

/-- **Sub-step 2 of the `N_G(A)/A`-is-a-`2`-group clause of Proposition 14.**  Two elements
`y`, `y'` that invert `A = C_G(z)` differ by an element of `A`.  Consequently, for
`x ∈ N_G(A)`, the element `x y x⁻¹` (which again inverts `A`) can be written `y · c` with
`c ∈ A`. -/
theorem inverting_differ_mem_centralizer (h : SzHyp H Q t s) {z y y' : G}
    (hy2 : y * y = 1)
    (hyinv : ∀ a ∈ Subgroup.centralizer ({z} : Set G), y * a * y⁻¹ = a⁻¹)
    (hy'inv : ∀ a ∈ Subgroup.centralizer ({z} : Set G), y' * a * y'⁻¹ = a⁻¹) :
    y⁻¹ * y' ∈ Subgroup.centralizer ({z} : Set G) := by
  refine mem_centralizer_of_commutes h ?_
  intro a ha
  have hyy : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hconj : y⁻¹ * y' * a * (y⁻¹ * y')⁻¹ = a := by
    rw [hyy, mul_inv_rev, hyy]
    calc y * y' * a * (y'⁻¹ * y) = y * (y' * a * y'⁻¹) * y := by group
      _ = y * a⁻¹ * y := by rw [hy'inv a ha]
      _ = a := by
          calc y * a⁻¹ * y = (y * a⁻¹ * y⁻¹) * (y * y) := by group
            _ = (y * a⁻¹ * y⁻¹) * 1 := by rw [hy2]
            _ = a := by
                rw [hyinv a⁻¹ ((Subgroup.centralizer ({z} : Set G)).inv_mem ha), inv_inv,
                  mul_one]
  calc y⁻¹ * y' * a = (y⁻¹ * y' * a * (y⁻¹ * y')⁻¹) * (y⁻¹ * y') := by group
    _ = a * (y⁻¹ * y') := by rw [hconj]

/-- Conjugation by an element of `N_G(A)` preserves the property "inverts `A`". -/
theorem conj_inverts (h : SzHyp H Q t s) {z x y : G}
    (hxN : x ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    (hyinv : ∀ a ∈ Subgroup.centralizer ({z} : Set G), y * a * y⁻¹ = a⁻¹) :
    ∀ a ∈ Subgroup.centralizer ({z} : Set G),
      (x * y * x⁻¹) * a * (x * y * x⁻¹)⁻¹ = a⁻¹ := by
  intro a ha
  have hxinvN : x⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G) :=
    (Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G)).inv_mem hxN
  have hxa : x⁻¹ * a * x ∈ Subgroup.centralizer ({z} : Set G) := by
    simpa using (Subgroup.mem_normalizer_iff.mp hxinvN a).mp ha
  calc (x * y * x⁻¹) * a * (x * y * x⁻¹)⁻¹
      = x * (y * (x⁻¹ * a * x) * y⁻¹) * x⁻¹ := by group
    _ = x * (x⁻¹ * a * x)⁻¹ * x⁻¹ := by rw [hyinv (x⁻¹ * a * x) hxa]
    _ = a⁻¹ := by group

/-- **Sub-step 2, final form.**  If `y` inverts `A` and `x` normalises `A`, then
`x y x⁻¹ = y * c` for some `c ∈ A`. -/
theorem conj_eq_mul_mem (h : SzHyp H Q t s) {z x y : G} (hy2 : y * y = 1)
    (hxN : x ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    (hyinv : ∀ a ∈ Subgroup.centralizer ({z} : Set G), y * a * y⁻¹ = a⁻¹) :
    ∃ c ∈ Subgroup.centralizer ({z} : Set G), x * y * x⁻¹ = y * c := by
  refine ⟨y⁻¹ * (x * y * x⁻¹), ?_, by group⟩
  exact inverting_differ_mem_centralizer h hy2 hyinv (conj_inverts h hxN hyinv)

/-- **Sub-step 3 of the `N_G(A)/A`-is-a-`2`-group clause of Proposition 14.**
For `x ∈ N_G(A)` with `x ∉ A`, the map `A → A`, `a ↦ (x a x⁻¹) · a⁻¹`, is surjective: it is
injective because `(x a x⁻¹) · a⁻¹ = 1` says `x` fixes `a`, and a non-trivial fixed point would
give `x ∈ C_G(a) = A`. -/
theorem conj_mul_inv_surjective (h : SzHyp H Q t s) {z x : G} (hz2 : z * z ≠ 1)
    (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z)
    (hxN : x ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    (hxA : x ∉ Subgroup.centralizer ({z} : Set G)) :
    ∀ c ∈ Subgroup.centralizer ({z} : Set G),
      ∃ a ∈ Subgroup.centralizer ({z} : Set G), (x * a * x⁻¹) * a⁻¹ = c := by
  obtain ⟨-, -, hcent⟩ := centralizer_abelian_of_strongly_real h.split h.zass h.two hz2 hsr
  let f : ↥(Subgroup.centralizer ({z} : Set G)) → ↥(Subgroup.centralizer ({z} : Set G)) :=
    fun a => ⟨(x * (a : G) * x⁻¹) * (a : G)⁻¹,
      (Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.mem_normalizer_iff.mp hxN (a : G)).mp a.2)
        ((Subgroup.centralizer ({z} : Set G)).inv_mem a.2)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : (x * (a : G) * x⁻¹) * (a : G)⁻¹ = (x * (b : G) * x⁻¹) * (b : G)⁻¹ :=
      congrArg Subtype.val hab
    have h2 : (x * (b : G) * x⁻¹)⁻¹ * (x * (a : G) * x⁻¹) = (b : G)⁻¹ * (a : G) := by
      calc (x * (b : G) * x⁻¹)⁻¹ * (x * (a : G) * x⁻¹)
          = (x * (b : G) * x⁻¹)⁻¹ * ((x * (a : G) * x⁻¹) * (a : G)⁻¹) * (a : G) := by group
        _ = (x * (b : G) * x⁻¹)⁻¹ * ((x * (b : G) * x⁻¹) * (b : G)⁻¹) * (a : G) := by
              rw [hab']
        _ = (b : G)⁻¹ * (a : G) := by group
    have key : x * ((b : G)⁻¹ * (a : G)) * x⁻¹ = (b : G)⁻¹ * (a : G) := by
      calc x * ((b : G)⁻¹ * (a : G)) * x⁻¹
          = (x * (b : G) * x⁻¹)⁻¹ * (x * (a : G) * x⁻¹) := by group
        _ = (b : G)⁻¹ * (a : G) := h2
    have hca : (b : G)⁻¹ * (a : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      (Subgroup.centralizer ({z} : Set G)).mul_mem
        ((Subgroup.centralizer ({z} : Set G)).inv_mem b.2) a.2
    by_cases h1 : (b : G)⁻¹ * (a : G) = 1
    · apply Subtype.ext
      have h3 := congrArg (fun u => (b : G) * u) h1
      simpa using h3
    · exfalso
      have hcomm : x * ((b : G)⁻¹ * (a : G)) = ((b : G)⁻¹ * (a : G)) * x := by
        calc x * ((b : G)⁻¹ * (a : G))
            = (x * ((b : G)⁻¹ * (a : G)) * x⁻¹) * x := by group
          _ = ((b : G)⁻¹ * (a : G)) * x := by rw [key]
      have hmem : x ∈ Subgroup.centralizer ({(b : G)⁻¹ * (a : G)} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm
      rw [(hcent _ hca h1).2] at hmem
      exact hxA hmem
  intro c hc
  obtain ⟨a, ha⟩ := Finite.surjective_of_injective hf ⟨c, hc⟩
  exact ⟨a.1, a.2, by have h2 := congrArg Subtype.val ha; simpa using h2⟩

/-- **Uniform order bound.**  If `x` centralises an involution, then `orderOf x ∣ |Q|`, i.e.
`orderOf x` is a power of two.  (`x` lies in the centraliser of the involution, which is contained
in a conjugate of `Q`.) -/
theorem orderOf_dvd_card_Q_of_mem_centralizer_involution (h : SzHyp H Q t s) {u x : G}
    (hu : orderOf u = 2) (hx : x ∈ Subgroup.centralizer ({u} : Set G)) :
    orderOf x ∣ Nat.card ↥Q := by
  obtain ⟨g, hg⟩ :=
    Work.ThmF.Bender.exists_conj_of_involution (H := H) h.split.stronglyEmbedded hu
  have hvH : g⁻¹ * u * g ∈ H := (Work.DoubleTransitivity.mem_conj g u H).mp hg
  have hv2 : orderOf (g⁻¹ * u * g) = 2 := by
    rw [show g⁻¹ * u * g = g⁻¹ * u * (g⁻¹)⁻¹ from by group,
      Work.ThmF.Bender.orderOf_conj_eq]
    exact hu
  have hle := centralizer_le_Q_of_mem_involutions h.split h.zass h.two ⟨hvH, hv2⟩
  have hx' : g⁻¹ * x * g ∈ Subgroup.centralizer ({g⁻¹ * u * g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hx'' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    calc (g⁻¹ * x * g) * (g⁻¹ * u * g) = g⁻¹ * (x * u) * g := by group
      _ = g⁻¹ * (u * x) * g := by rw [hx'']
      _ = (g⁻¹ * u * g) * (g⁻¹ * x * g) := by group
  have h1 : orderOf (g⁻¹ * x * g) ∣ Nat.card ↥Q :=
    Subgroup.orderOf_dvd_natCard Q (hle hx')
  have h2 : orderOf (g⁻¹ * x * g) = orderOf x := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * (g⁻¹)⁻¹ from by group,
      Work.ThmF.Bender.orderOf_conj_eq]
  rwa [h2] at h1

/-- **Sub-step 3, final form.**  For `x ∈ N_G(A)` with `x ∉ A` there is an involution in the
coset `yA` (where `y` inverts `A`) that commutes with `x`: take `a` with
`(x a x⁻¹)·a⁻¹ = c⁻¹` where `xyx⁻¹ = y·c`; then `u := y·a` is an involution and `x u x⁻¹ = u`. -/
theorem exists_involution_commuting_of_notMem (h : SzHyp H Q t s) {z x y : G}
    (hz2 : z * z ≠ 1)
    (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z)
    (hyN : y ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    (hy2 : y * y = 1)
    (hyA : y ∉ Subgroup.centralizer ({z} : Set G))
    (hxN : x ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    (hxA : x ∉ Subgroup.centralizer ({z} : Set G)) :
    ∃ a ∈ Subgroup.centralizer ({z} : Set G),
      (y * a) * (y * a) = 1 ∧ x * (y * a) = (y * a) * x := by
  have hyinv := involution_inverts_centralizer h hz2 hsr hyN hy2 hyA
  obtain ⟨c, hcA, hc⟩ := conj_eq_mul_mem h hy2 hxN hyinv
  obtain ⟨a, haA, ha⟩ := conj_mul_inv_surjective h hz2 hsr hxN hxA c⁻¹
    ((Subgroup.centralizer ({z} : Set G)).inv_mem hcA)
  have hσ : x * a * x⁻¹ = c⁻¹ * a := by
    have h4 := congrArg (fun u => u * a) ha
    simpa [mul_assoc] using h4
  refine ⟨a, haA, ?_, ?_⟩
  · calc (y * a) * (y * a) = (y * a * y⁻¹) * (y * y) * a := by group
      _ = a⁻¹ * 1 * a := by rw [hyinv a haA, hy2]
      _ = 1 := by group
  · calc x * (y * a) = (x * y * x⁻¹) * (x * a * x⁻¹) * x := by group
      _ = (y * c) * (c⁻¹ * a) * x := by rw [hc, hσ]
      _ = (y * a) * x := by group

/-- **The odd-order part of `N_G(A)` is trivial.**  For `x ∈ N_G(A)` one has
`x ^ |Q| ∈ A`, i.e. every element of `N_G(A)/A` has order dividing `|Q| = 2^e` — hence `N_G(A)/A`
is a `2`-group. -/
theorem pow_card_Q_mem_of_mem_normalizer (h : SzHyp H Q t s) {z x y : G} (hz2 : z * z ≠ 1)
    (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z)
    (hyN : y ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G))
    (hy2 : y * y = 1)
    (hyA : y ∉ Subgroup.centralizer ({z} : Set G))
    (hxN : x ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G)) :
    x ^ (Nat.card ↥Q) ∈ Subgroup.centralizer ({z} : Set G) := by
  by_cases hxA : x ∈ Subgroup.centralizer ({z} : Set G)
  · exact (Subgroup.centralizer ({z} : Set G)).pow_mem hxA _
  · obtain ⟨a, haA, hu2, hcomm⟩ :=
      exists_involution_commuting_of_notMem h hz2 hsr hyN hy2 hyA hxN hxA
    have hne1 : y * a ≠ 1 := by
      intro h1
      apply hyA
      rw [eq_inv_of_mul_eq_one_left h1]
      exact (Subgroup.centralizer ({z} : Set G)).inv_mem haA
    have hu_ord : orderOf (y * a) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two]; exact hu2
      · exact hne1
    have hmem : x ∈ Subgroup.centralizer ({(y * a)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    have hdvd := orderOf_dvd_card_Q_of_mem_centralizer_involution h hu_ord hmem
    rw [orderOf_dvd_iff_pow_eq_one] at hdvd
    rw [hdvd]
    exact (Subgroup.centralizer ({z} : Set G)).one_mem

/-- From `z = a₀ * b₀` with `a₀`, `b₀` involutions, `a₀` is an involution lying in
`N_G(A) \ A` for `A = C_G(z)`. -/
theorem inverting_involution_data (h : SzHyp H Q t s) {z a₀ b₀ : G} (hz2 : z * z ≠ 1)
    (ha₀ : a₀ * a₀ = 1) (hb₀ : b₀ * b₀ = 1) (hab : a₀ * b₀ = z) :
    a₀ * a₀ = 1 ∧
      a₀ ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G) ∧
      a₀ ∉ Subgroup.centralizer ({z} : Set G) := by
  have ha₀inv : a₀⁻¹ = a₀ := inv_eq_of_mul_eq_one_right ha₀
  have hb₀inv : b₀⁻¹ = b₀ := inv_eq_of_mul_eq_one_right hb₀
  -- the two conjugation identities around `z`
  have hyz : a₀ * z * a₀⁻¹ = z⁻¹ := by
    calc a₀ * z * a₀⁻¹ = a₀ * (a₀ * b₀) * a₀⁻¹ := by rw [← hab]
      _ = (a₀ * a₀) * b₀ * a₀⁻¹ := by group
      _ = 1 * b₀ * a₀⁻¹ := by rw [ha₀]
      _ = b₀ * a₀ := by rw [ha₀inv]; group
      _ = (a₀ * b₀)⁻¹ := by rw [mul_inv_rev, ha₀inv, hb₀inv]
      _ = z⁻¹ := by rw [hab]
  have hza : a₀ * z = z⁻¹ * a₀ := by
    calc a₀ * z = (a₀ * z * a₀⁻¹) * a₀ := by group
      _ = z⁻¹ * a₀ := by rw [hyz]
  have haz : z * a₀ = a₀ * z⁻¹ := by
    calc z * a₀ = z * a₀⁻¹ := by rw [ha₀inv]
      _ = a₀⁻¹ * (a₀ * z * a₀⁻¹) := by group
      _ = a₀⁻¹ * z⁻¹ := by rw [hyz]
      _ = a₀ * z⁻¹ := by rw [ha₀inv]
  have hzainv : a₀⁻¹ * z * a₀ = z⁻¹ := by
    rw [ha₀inv]
    calc a₀ * z * a₀ = (a₀ * z * a₀⁻¹) * (a₀ * a₀) := by group
      _ = z⁻¹ * 1 := by rw [hyz, ha₀]
      _ = z⁻¹ := by group
  have hza' : a₀ * z⁻¹ * a₀ = z := by
    have h : (a₀⁻¹ * z * a₀)⁻¹ = z := by
      have h2 := congrArg Inv.inv hzainv
      simpa using h2
    calc a₀ * z⁻¹ * a₀ = a₀⁻¹ * z⁻¹ * a₀ := by rw [ha₀inv]
      _ = (a₀⁻¹ * z * a₀)⁻¹ := by group
      _ = z := h
  have hfwd : ∀ d ∈ Subgroup.centralizer ({z} : Set G),
      a₀ * d * a₀⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff] at hd ⊢
    have hdz' : z⁻¹ * d = d * z⁻¹ := by
      have h := congrArg (fun u => z⁻¹ * u * z⁻¹) hd
      simpa [mul_assoc] using h
    calc (a₀ * d * a₀⁻¹) * z
        = a₀ * d * (a₀⁻¹ * z * a₀) * a₀⁻¹ := by group
      _ = a₀ * d * z⁻¹ * a₀⁻¹ := by rw [hzainv]
      _ = a₀ * (d * z⁻¹) * a₀⁻¹ := by group
      _ = a₀ * (z⁻¹ * d) * a₀⁻¹ := by rw [← hdz']
      _ = a₀ * z⁻¹ * a₀ * (a₀ * d * a₀⁻¹) := by
            rw [show a₀ * z⁻¹ * a₀ * (a₀ * d * a₀⁻¹)
                = a₀ * z⁻¹ * (a₀ * a₀) * d * a₀⁻¹ from by group, ha₀, mul_one]
            group
      _ = z * (a₀ * d * a₀⁻¹) := by rw [hza']
  have hrev : ∀ d : G, a₀ * d * a₀⁻¹ ∈ Subgroup.centralizer ({z} : Set G) →
      d ∈ Subgroup.centralizer ({z} : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_singleton_iff] at hd ⊢
    have hd' : z⁻¹ * (a₀ * d * a₀⁻¹) = (a₀ * d * a₀⁻¹) * z⁻¹ := by
      have h := congrArg (fun u => z⁻¹ * u * z⁻¹) hd
      simpa [mul_assoc] using h
    rw [show d = a₀ * (a₀ * d * a₀⁻¹) * a₀ from by
      rw [show a₀ * (a₀ * d * a₀⁻¹) * a₀ = (a₀ * a₀) * d * (a₀⁻¹ * a₀) from by group,
        ha₀, inv_mul_cancel, mul_one, one_mul]]
    calc (a₀ * (a₀ * d * a₀⁻¹) * a₀) * z
        = a₀ * (a₀ * d * a₀⁻¹) * (a₀ * z) := by simp only [mul_assoc]
      _ = a₀ * (a₀ * d * a₀⁻¹) * (z⁻¹ * a₀) := by rw [hza]
      _ = a₀ * ((a₀ * d * a₀⁻¹) * z⁻¹) * a₀ := by simp only [mul_assoc]
      _ = a₀ * (z⁻¹ * (a₀ * d * a₀⁻¹)) * a₀ := by rw [← hd']
      _ = a₀ * z⁻¹ * (a₀ * d * a₀⁻¹) * a₀ := by simp only [mul_assoc]
      _ = z * a₀ * (a₀ * d * a₀⁻¹) * a₀ := by rw [← haz]
      _ = z * (a₀ * (a₀ * d * a₀⁻¹) * a₀) := by simp only [mul_assoc]
  refine ⟨ha₀, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    exact fun d => ⟨hfwd d, hrev d⟩
  · intro hmem
    have hcomm : a₀ * z = z * a₀ := Subgroup.mem_centralizer_singleton_iff.mp hmem
    have h1 : z⁻¹ = z := by
      have h2 : a₀ * z * a₀⁻¹ = z := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hyz] at h2
      exact h2
    have h3 : z * z = z * z⁻¹ := by rw [h1]
    exact hz2 (by rw [h3, mul_inv_cancel])


/-- Conjugation preserves the cardinality of a centraliser: `|C_G(g⁻¹ x g)| = |C_G(x)|`. -/
theorem card_centralizer_conj (g x : G) :
    Nat.card ↥(Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set G)) := by
  have hmap : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    ext y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      rw [← hzy]
      show (g * z * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * z * g⁻¹)
      calc (g * z * g⁻¹) * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
        _ = g * (x * z) * g⁻¹ := by rw [hz]
        _ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group
    · intro hy
      rw [Subgroup.mem_map]
      refine ⟨g⁻¹ * y * g, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
        show (g⁻¹ * y * g) * x = x * (g⁻¹ * y * g)
        calc (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
          _ = x * (g⁻¹ * y * g) := by group
      · show MulAut.conj g (g⁻¹ * y * g) = y
        rw [MulAut.conj_apply]; group
  rw [← hmap, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective (K := Subgroup.centralizer ({x} : Set G))]

/-- **Step 1(a) of Suzuki 1962 §8, p. 118.**  Every non-identity element of `W = C_G(S.V)` is
conjugate into `S.V`: it is strongly real with `ω * ω ≠ 1` (Prop. 14), so `hD3` conjugates it into
`Q`, `twoPoint H t` or `S.V`; the first two fail because `|W|` is odd, resp. because `hC1` gives
`|C_G(ω)| = |twoPoint H t| = q - 1 < q + 1 ≤ |W|`. -/
theorem centralizer_conj_mem_singerV (h : SzHyp H Q t s)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (S : SingerCycle.Data G H t)
    (hD3 : ∀ x : G, x * x ≠ 1 →
      (∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x) →
      (∃ g : G, g * x * g⁻¹ ∈ Q) ∨
        (∃ g : G, g * x * g⁻¹ ∈ Submission.Blueprint.twoPoint H t) ∨
        (∃ g : G, g * x * g⁻¹ ∈ S.V))
    (hC1 : ∀ k : G, k ∈ Submission.Blueprint.twoPoint H t → k ≠ 1 →
      Subgroup.centralizer ({k} : Set G) = Submission.Blueprint.twoPoint H t)
    {ω : G} (hω : ω ∈ Subgroup.centralizer (S.V : Set G)) (hω1 : ω ≠ 1) :
    ∃ g : G, g * ω * g⁻¹ ∈ S.V := by
  obtain ⟨n, hn, hc⟩ := Q0sub_card_eq_two_pow h
  have hoddV : Odd (Nat.card ↥S.V) := by
    rw [S.card_V]
    refine ⟨2 ^ (n - 1), ?_⟩
    have hn1 : n = (n - 1) + 1 := by omega
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by conv_lhs => rw [hn1, pow_succ']
    rw [hc, h2]
  have hcardV : 2 ≤ Nat.card ↥S.V := by
    rw [S.card_V]
    have h4 := four_le_Q0sub_card h
    omega
  haveI : Fintype ↥S.V := Fintype.ofFinite _
  have hcardV' : 2 ≤ Fintype.card ↥S.V := by
    rw [← Nat.card_eq_fintype_card]; exact hcardV
  obtain ⟨v₀, hv₀⟩ := Fintype.exists_ne_of_one_lt_card (α := ↥S.V) (by omega) (1 : ↥S.V)
  obtain ⟨v, hv, hv1⟩ : ∃ v ∈ S.V, v ≠ 1 := ⟨v₀, v₀.2, fun hcon => hv₀ (Subtype.ext hcon)⟩
  have hv2 : v * v ≠ 1 := by
    have hoddord : Odd (orderOf v) := hoddV.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hv)
    intro hsq
    have hdvd : orderOf v ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · exact hv1 (orderOf_eq_one_iff.mp h1)
    · rw [h2'] at hoddord; rcases hoddord with ⟨j, hj⟩; omega
  obtain ⟨hAcom, hAodd, hcent⟩ :=
    centralizer_abelian_of_strongly_real h.split h.zass h.two hv2 (S.stronglyReal v hv)
  haveI hcyc : IsCyclic ↥S.V := S.cyclic
  haveI hVcom : IsMulCommutative ↥S.V := IsCyclic.isMulCommutative
  haveI : IsMulCommutative ↥(Subgroup.centralizer ({v} : Set G)) := hAcom
  have hW : Subgroup.centralizer (S.V : Set G) = Subgroup.centralizer ({v} : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hx v hv).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwv : w ∈ Subgroup.centralizer ({v} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mul_comm' (⟨w, hw⟩ : ↥S.V) (⟨v, hv⟩ : ↥S.V)))
      exact (congrArg Subtype.val
        (mul_comm' (⟨x, hx⟩ : ↥(Subgroup.centralizer ({v} : Set G)))
          (⟨w, hwv⟩ : ↥(Subgroup.centralizer ({v} : Set G))))).symm
  have hωv : ω ∈ Subgroup.centralizer ({v} : Set G) := hW ▸ hω
  have hωsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = ω := (hcent ω hωv hω1).1
  have hωcomm : Subgroup.centralizer ({ω} : Set G) = Subgroup.centralizer ({v} : Set G) :=
    (hcent ω hωv hω1).2
  have hωodd : Odd (orderOf ω) := hAodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hωv)
  have hω2 : ω * ω ≠ 1 := by
    intro hsq
    have hdvd : orderOf ω ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · exact hω1 (orderOf_eq_one_iff.mp h1)
    · rw [h2'] at hωodd; rcases hωodd with ⟨j, hj⟩; omega
  rcases hD3 ω hω2 hωsr with ⟨g, hg⟩ | ⟨g, hg⟩ | hg
  · exfalso
    have hdvdQ : orderOf ω ∣ Nat.card ↥Q := by
      have h1 : orderOf (g * ω * g⁻¹) = orderOf ω := by
        rw [show g * ω * g⁻¹ = MulAut.conj g ω from (MulAut.conj_apply g ω).symm]
        exact MulEquiv.orderOf_eq (MulAut.conj g) ω
      rw [← h1]
      exact Subgroup.orderOf_dvd_natCard Q hg
    obtain ⟨e, he⟩ := h.two.exists_card_eq
    have hcop : Nat.Coprime (orderOf ω) (2 ^ e) :=
      Nat.Coprime.pow_right e (Nat.coprime_two_right.mpr hωodd)
    have h1 : orderOf ω = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (by rwa [he] at hdvdQ)
    exact hω1 (orderOf_eq_one_iff.mp h1)
  · exfalso
    have hg1 : g * ω * g⁻¹ ≠ 1 := by
      intro h1
      apply hω1
      have h3 : ω = g⁻¹ * (g * ω * g⁻¹) * g := by group
      rw [h3, h1]; group
    have hD := hC1 (g * ω * g⁻¹) hg hg1
    have hcard : Nat.card ↥(Subgroup.centralizer ({g * ω * g⁻¹} : Set G)) =
        Nat.card ↥(Subgroup.centralizer ({ω} : Set G)) := card_centralizer_conj g ω
    have hEq : Nat.card ↥(Subgroup.centralizer ({ω} : Set G)) =
        Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
      rw [← hcard, hD]
    have hle : Nat.card ↥S.V ≤ Nat.card ↥(Subgroup.centralizer ({ω} : Set G)) := by
      rw [hωcomm]
      refine Subgroup.card_le_of_le (fun a ha => ?_)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥S.V) (⟨v, hv⟩ : ↥S.V))
    have hq1 : Nat.card ↥S.V = Nat.card ↥(Work.ThmF.Q0sub H) + 1 := S.card_V
    have hDc : Nat.card ↥(Submission.Blueprint.twoPoint H t) =
        Nat.card ↥(Work.ThmF.Q0sub H) - 1 := twoPoint_card_eq_Q0sub_sub_one h
    have h4 := four_le_Q0sub_card h
    rw [hEq, hDc, hq1] at hle
    omega
  · exact hg

end Work.ZassenhausSuzuki
