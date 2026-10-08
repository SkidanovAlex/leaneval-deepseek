import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.no_cent_elt_outside_maximal
import Submission.Work.Higman.H8.orbit_card_ge_omega1_sub_one
import Submission.Work.Higman.H8.c4_sq_a2_card_quot
import Submission.Work.Higman.H8.fixed_coset_imp_fix_all
import Submission.Work.Higman.MSA.centralizer_eq_self
import Submission.Work.Higman.H8.Clean.Nsd
import Submission.Work.Higman.H8.Clean.NsdCore
import Submission.Work.Higman.NSM.redcase
import Submission.Work.Higman.Q3.crux_class_three_jacobi
import Submission.Work.Higman.H8.c4_card_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option maxHeartbeats 1000000

namespace Work.Higman.Q3

variable {P : Type} [Group P] [Finite P]

/-- In the crux configuration the squares generate exactly `A`: `P ^ (2) = A`.

Indeed `P ^ (2) ≤ A` by hypothesis, while `⁅P,P⁆ ≤ P ^ (2)` always (via
`⁅x,y⁆ = x² · (x⁻¹ * y)² · (y²)⁻¹`) and `⁅P,P⁆ = A`. -/
theorem crux_powSub_top_two_eq {A : Subgroup P}
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A) (hsq : ∀ x : P, x ^ 2 ∈ A) :
    Work.Higman.powSub (⊤ : Subgroup P) 2 = A := by
  refine le_antisymm ?_ ?_
  · rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  · rw [← hGs, Subgroup.commutator_le]
    intro x _ y _
    have key : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y ^ 2)⁻¹ := by
      rw [commutatorElement_def, pow_two (a := x), pow_two (a := x⁻¹ * y), pow_two (a := y)]
      group
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Work.Higman.pow_mem_powSub (Subgroup.mem_top x))
      (Work.Higman.pow_mem_powSub (Subgroup.mem_top (x⁻¹ * y))))
      (Subgroup.inv_mem _ (Work.Higman.pow_mem_powSub (Subgroup.mem_top y)))

/-- In the crux configuration, `⁅P,P⁆ ≤ Ω₁(P)` is already contradictory.

`A = ⁅P,P⁆ ≤ Ω₁(P) = A ^ (2) ≤ A` forces `A = A ^ (2)`, i.e. `|A| = |Ω₁(P)|`, whereas
`hcard` gives `|A| = |Ω₁(P)| ^ 2` with `|Ω₁(P)| ≥ 4`.

This shows that the crux statement is *equivalent* to the `C₄`-exclusion
(`⁅P,P⁆ ≤ Ω₁(P)` for every Suzuki 2-group), i.e. to Higman's Lemma 8 endgame. -/
theorem crux_false_of_comm_le_omega1 (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcomm : Bracket.bracket (⊤ : Subgroup P) ⊤ ≤ Work.Higman.omega1 P) : False := by
  have hAle : A ≤ Work.Higman.powSub A 2 := by
    calc A = Bracket.bracket (⊤ : Subgroup P) ⊤ := hGs.symm
      _ ≤ Work.Higman.omega1 P := hcomm
      _ = Work.Higman.powSub A 2 := htop.symm
  have hEq : A = Work.Higman.powSub A 2 :=
    le_antisymm hAle (Work.Higman.powSub_le (A := A) (n := 2) (by norm_num))
  have h1 : Nat.card ↥(Work.Higman.omega1 P) = Nat.card ↥A := by rw [← htop, ← hEq]
  have h2 : Nat.card ↥(Work.Higman.omega1 P)
      = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
    have hh := hcard
    rw [← h1] at hh
    exact hh
  have h4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
  nlinarith [h2, h4]

/-- Consequently, in the crux configuration, `A` does *not* generate `Ω₁(P)`: the
`middle layer` `A / A ^ (2)` is genuinely non-trivial (this is the "class three" shape). -/
theorem crux_A_ne_powSub_two (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    A ≠ Work.Higman.powSub A 2 := by
  intro hEq
  have h1 : Nat.card ↥(Work.Higman.omega1 P) = Nat.card ↥A := by rw [← htop, ← hEq]
  have h2 : Nat.card ↥(Work.Higman.omega1 P)
      = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
    have hh := hcard
    rw [← h1] at hh
    exact hh
  have h4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
  nlinarith [h2, h4]

/-- A non-trivial `ξ`-invariant subgroup of `Ω₁(P)` is all of `Ω₁(P)`: `ξ` is transitive on the
involutions. -/
theorem crux_eq_omega1_of_ne_bot {S : Subgroup P} (h : Work.Higman.IsSuzuki2Grp P)
    (hS : S ≤ Work.Higman.omega1 P) (hSinv : S.map (h.xi : MulAut P).toMonoidHom = S)
    (hne : S ≠ ⊥) : S = Work.Higman.omega1 P := by
  refine le_antisymm hS ?_
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hxS : (x : P) ∈ S := x.2
  have hx1' : (x : P) ≠ 1 := fun hc => hx1 (Subtype.ext hc)
  have hx2 : (x : P) ^ 2 = 1 := h.mem_omega1.mp (hS hxS)
  have hxord : orderOf (x : P) = 2 := by
    have hdvd : orderOf (x : P) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have hle : orderOf (x : P) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf (x : P) := orderOf_pos _
    have hne1 : orderOf (x : P) ≠ 1 := fun hc => hx1' (orderOf_eq_one_iff.mp hc)
    omega
  have hstep : ∀ k : ℕ, ∀ y ∈ S, (h.xi ^ k) y ∈ S := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
        intro y hy
        have hz : (h.xi ^ k) y ∈ S := ih y hy
        have hgoal : (h.xi ^ (k + 1)) y = h.xi ((h.xi ^ k) y) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [hgoal]
        have hmem : h.xi ((h.xi ^ k) y) ∈ S.map (h.xi : MulAut P).toMonoidHom :=
          Subgroup.mem_map_of_mem _ hz
        rwa [hSinv] at hmem
  intro y hy
  rcases eq_or_ne y 1 with rfl | hy1
  · exact S.one_mem
  · have hyord : orderOf y = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp
        (orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hy)) with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hy1
      · exact h2
    obtain ⟨k, hk⟩ := h.trans (x : P) y hxord hyord
    rw [← hk]
    exact hstep k (x : P) hxS

/-- **The bracket pairing takes values in `A ^ (2)`**: `⁅A,D⁆ = A ^ (2)` whenever `A ⊴ P` is
`ξ`-invariant abelian, `A ^ (2) = Ω₁(P)`, `A ^ (4) = 1`, `D` is `ξ`-invariant with `A ≤ D` and
`D` does not centralise `A`.

Unipotence gives `⁅A,D⁆ ≤ A ^ (2)`; `⁅A,D⁆ ≠ ⊥` is the hypothesis that `D` does not centralise
`A`; and `Ω₁(P)` is `ξ`-irreducible, so a non-trivial `ξ`-invariant subgroup of it is all of it.

This is the well-definedness input for the bracket `θ : P/A × A/A² → A²` appearing in Higman's
§4 Lemma 6 configuration. -/
theorem crux_comm_A_D_eq (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hAD : A ≤ D) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hnZ : ¬(∀ e ∈ D, ∀ a ∈ A, e * a = a * e)) :
    Bracket.bracket A D = Work.Higman.powSub A 2 := by
  have hle : Bracket.bracket A D ≤ Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_le]
    intro a ha d _
    have h2 : ⁅a, d⁆ = ⁅d, a⁆⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]; group
    rw [h2]
    exact (Work.Higman.powSub A 2).inv_mem
      (Work.Higman.commutator_mem_powSub_two h hA d a ha)
  have hne : Bracket.bracket A D ≠ ⊥ := by
    intro hbot
    apply hnZ
    intro e he a ha
    have hmem : ⁅a, e⁆ ∈ (⊥ : Subgroup P) := by
      rw [← hbot]
      exact Subgroup.commutator_mem_commutator ha he
    have h1 : ⁅a, e⁆ = 1 := Subgroup.mem_bot.mp hmem
    have h2 : ⁅e, a⁆ = 1 := by
      rw [show ⁅e, a⁆ = ⁅a, e⁆⁻¹ by
        rw [commutatorElement_def, commutatorElement_def]; group, h1, inv_one]
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  have hinv : (Bracket.bracket A D).map (h.xi : MulAut P).toMonoidHom
      = Bracket.bracket A D := by
    rw [Subgroup.map_commutator, hA.map_eq, hDinv]
  have := crux_eq_omega1_of_ne_bot h (htop ▸ hle) hinv hne
  rw [this, ← htop]

/-! ## The `ξ`-fixed-point lemmas

The crux configuration forces `ξ` to act **fixed-point-freely**: no non-trivial element of `A`
and none of `P` is fixed by `ξ`.  This is the input for the `|xξx⁻¹| = |Ω₁(P)|` orbit argument
used in Higman's §4 bookkeeping. -/

/-- `ξ` fixes no non-trivial element of `Ω₁(P)`. -/
theorem crux_xi_fixed_omega1_eq_one (h : Work.Higman.IsSuzuki2Grp P) {z : P}
    (hz : z ∈ Work.Higman.omega1 P) (hfix : h.xi z = z) : z = 1 := by
  by_contra hne
  have hz2 : z ^ 2 = 1 := h.mem_omega1.mp hz
  have hzord : orderOf z = 2 := by
    have hd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h1
  obtain ⟨u, v, hu2, hv2, huv⟩ := h.manyInvol
  have hfixk : ∀ k : ℕ, (h.xi ^ k) z = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hfix]
  have hzu : u = z := by
    obtain ⟨k, hk⟩ := h.trans z u hzord hu2
    rw [← hk]; exact hfixk k
  have hzv : v = z := by
    obtain ⟨k, hk⟩ := h.trans z v hzord hv2
    rw [← hk]; exact hfixk k
  exact huv (hzu.trans hzv.symm)

/-- `C_A(ξ) = 1`. -/
theorem crux_C_A_xi_eq_one (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) {a : P} (ha : a ∈ A)
    (hfix : h.xi a = a) : a = 1 := by
  have ha2A : a ^ 2 ∈ Work.Higman.powSub A 2 := Work.Higman.pow_mem_powSub ha
  rw [htop] at ha2A
  have hfix2 : h.xi (a ^ 2) = a ^ 2 := by rw [map_pow, hfix]
  have h2 : a ^ 2 = 1 := crux_xi_fixed_omega1_eq_one h ha2A hfix2
  exact crux_xi_fixed_omega1_eq_one h (h.mem_omega1.mpr h2) hfix

/-- `C_P(ξ) = 1`. -/
theorem crux_C_P_xi_eq_one (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ A) {x : P} (hfix : h.xi x = x) : x = 1 := by
  have h2 : x ^ 2 = 1 := crux_C_A_xi_eq_one h hA htop (hsq x) (by rw [map_pow, hfix])
  exact crux_xi_fixed_omega1_eq_one h (h.mem_omega1.mpr h2) hfix

/-- If some `x ∉ Ω₁(P)` is fixed by `ξ` **modulo** `Ω₁(P)`, we are done: `x²` is then fixed by
`ξ`, hence trivial, so `x` itself is an involution fixed by `ξ`. -/
theorem crux_false_of_xi_fixed_mod_omega1 (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hx : ∃ x : P, x ∉ Work.Higman.omega1 P ∧ (h.xi x) * x⁻¹ ∈ Work.Higman.omega1 P) :
    False := by
  obtain ⟨x, hxZ, hzmem⟩ := hx
  have hz1 : ((h.xi x) * x⁻¹) * ((h.xi x) * x⁻¹) = 1 := by
    have hh : ((h.xi x) * x⁻¹) ^ 2 = 1 := h.mem_omega1.mp hzmem
    rwa [pow_two] at hh
  have hzc : ∀ y : P, ((h.xi x) * x⁻¹) * y = y * ((h.xi x) * x⁻¹) :=
    fun y => (Subgroup.mem_center_iff.mp (h.omega1_le_center hzmem) y).symm
  have hxx : (h.xi x) * (h.xi x) = x * x := by
    have h1 : ((h.xi x) * x⁻¹) * x = h.xi x := by group
    rw [← h1]
    calc ((h.xi x) * x⁻¹) * x * (((h.xi x) * x⁻¹) * x)
        = ((h.xi x) * x⁻¹) * (x * ((h.xi x) * x⁻¹)) * x := by group
      _ = ((h.xi x) * x⁻¹) * (((h.xi x) * x⁻¹) * x) * x := by
            rw [(hzc x).symm]
      _ = (((h.xi x) * x⁻¹) * ((h.xi x) * x⁻¹)) * (x * x) := by group
      _ = x * x := by rw [hz1, one_mul]
  have hfix2 : h.xi (x ^ 2) = x ^ 2 := by rw [map_pow, pow_two, pow_two]; exact hxx
  have h2 : x ^ 2 = 1 := crux_C_A_xi_eq_one h hA htop (hsq x) hfix2
  exact hxZ (h.mem_omega1.mpr h2)

/-- **Case A of the crux is impossible.**  If some `d ∈ D` outside `A` is fixed by `ξ` modulo
`A`, then `ξ` fixes all of `Ω₁(P)` pointwise
(`Work.Higman.fixed_coset_imp_fix_all`), contradicting the transitivity of `ξ` on the
involutions. -/
theorem crux_false_of_xi_fixed_coset_mod_A (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hx : ∃ d : P, d ∈ D ∧ d ∉ A ∧ (h.xi d) * d⁻¹ ∈ A) : False := by
  obtain ⟨d, -, hdA, hfixd⟩ := hx
  have hNA : Work.Higman.omega1 P ≤ A := htop ▸ Work.Higman.powSub_le (A := A) (by norm_num)
  have hall : ∀ w ∈ Work.Higman.omega1 P, h.xi w = w :=
    Work.Higman.fixed_coset_imp_fix_all h hA.normal hA.map_eq hA.abelian hNA htop hsq
      (k := 1) hdA (by simpa using hfixd)
  obtain ⟨u, v, hu2, hv2, huv⟩ := h.manyInvol
  have hu1 : u ∈ Work.Higman.omega1 P :=
    h.mem_omega1.mpr (hu2 ▸ pow_orderOf_eq_one u)
  have hfixu : h.xi u = u := hall u hu1
  have hfixall : ∀ m : ℕ, (h.xi ^ m) u = u := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, hfixu]
  obtain ⟨j, hj⟩ := h.trans u v hu2 hv2
  exact huv ((hfixall j).symm.trans hj)

/-- **`(P/A)^ξ = 0`.**  No non-trivial coset of `A` is fixed by `ξ`; equivalently `ξ - 1` is a
bijection of `P/A`.  This is the hypothesis that makes the `P/A`-orbit counting sharp and that
excludes the counterexample to the naive `𝔽₂`-module bookkeeping. -/
theorem crux_not_xi_fixed (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ A) :
    ∀ x : P, x ∉ A → (h.xi x) * x⁻¹ ∉ A := by
  intro x hx hfix
  exact crux_false_of_xi_fixed_coset_mod_A h hA htop hsq ⟨x, Subgroup.mem_top x, hx, hfix⟩

/-! ## The `ξ`-action on the two layers of `A`

`A` is a two-step abelian group: `A² = Ω₁(P)` is the elementary abelian *bottom* layer and
`A/A²` the *top* layer.  `ξ` acts on the bottom layer as a Singer cycle (`ξ` is transitive on
the involutions and fixes no non-trivial one).  The top layer is more delicate: `ξ` fixes no
non-trivial element of `A` (`crux_C_A_xi_eq_one`), but the coset `a·A²` *is* moved.

Here we record: (i) `ξ` is not the identity on `A/A²` — otherwise `ξ` would fix `A²` pointwise,
contradicting `crux_xi_fixed_omega1_eq_one`; (ii) `ξ ^ (|Ω₁(P)| - 1)` has square `1` on `A`. -/

/-- Squaring an element of an abelian subgroup. -/
private theorem crux_sq_mul_sq {G : Type*} [Group G] {a c : G} (h : a * c = c * a) :
    (a * c) * (a * c) = (a * a) * (c * c) := by
  calc (a * c) * (a * c) = a * (c * (a * c)) := by rw [mul_assoc]
    _ = a * ((c * a) * c) := by rw [mul_assoc]
    _ = a * ((a * c) * c) := by rw [h]
    _ = a * (a * (c * c)) := by rw [mul_assoc]
    _ = (a * a) * (c * c) := by rw [mul_assoc]

/-- **`ξ` is not the identity on `A / A ^ (2)`.**  There is `a ∈ A` with `ξ a * a⁻¹ ∉ A ^ (2)`.

Indeed, if `ξ a * a⁻¹ ∈ A ^ (2)` for all `a ∈ A`, then `ξ` fixes every square:
`ξ (a * a) = (ξ a) * (ξ a) = (a * c) * (a * c) = (a * a) * (c * c) = a * a` with
`c = ξ a * a⁻¹ ∈ A ^ (2)` (an element of order `2`, `A ^ (2) = Ω₁(P)`).  So `ξ` acts trivially on
`A ^ (2) = Ω₁(P)`, against `crux_xi_fixed_omega1_eq_one`. -/
theorem crux_exists_xi_moved_mod_powSub (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    ∃ a ∈ A, h.xi a * a⁻¹ ∉ Work.Higman.powSub A 2 := by
  by_contra hcon
  push_neg at hcon
  have hfix : ∀ b ∈ Work.Higman.powSub A 2, h.xi b = b := by
    intro b hb
    obtain ⟨a, ha, haeq⟩ := (Work.Higman.mem_powSub_iff hA.abelian (n := 2)).mp hb
    have hxa : h.xi a ∈ A := by
      have hm := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom ha
      rwa [hA.map_eq] at hm
    have hcA : h.xi a * a⁻¹ ∈ A := A.mul_mem hxa (A.inv_mem ha)
    have hc2 : (h.xi a * a⁻¹) * (h.xi a * a⁻¹) = 1 := by
      have hmem : h.xi a * a⁻¹ ∈ Work.Higman.omega1 P := htop ▸ hcon a ha
      have hm := h.mem_omega1.mp hmem
      rwa [pow_two] at hm
    have hcomm : (h.xi a * a⁻¹) * a = a * (h.xi a * a⁻¹) := hA.abelian _ hcA a ha
    have hsq := crux_sq_mul_sq (a := h.xi a * a⁻¹) (c := a) hcomm
    have hxi : h.xi a = (h.xi a * a⁻¹) * a := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [← haeq, map_pow, pow_two, pow_two, hxi, hsq, hc2, one_mul]
  have hne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hbot
    have h4 := h.omega1_card_ge_four
    rw [← htop, hbot] at h4
    simp at h4
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  exact hb1 (Subtype.ext (crux_xi_fixed_omega1_eq_one h (htop ▸ b.2) (hfix b b.2)))

/-- **`ξ ^ (|Ω₁(P)| - 1)` has square `1` on `A`.**  `ξ ^ (|Ω₁(P)| - 1)` fixes `Ω₁(P)` pointwise,
and an automorphism fixing `Ω₁(P)` pointwise has square `1` on `A` whenever `A ^ (2) = Ω₁(P)`
(`Work.Higman.apply_apply_eq_self_of_fixes_omega1`). -/
theorem crux_pow_card_sub_one_sq_fixes_A (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    ∀ a ∈ A, ((h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) ^ 2) a = a := by
  intro a ha
  have hkΩ : ∀ z ∈ Work.Higman.omega1 P,
      (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) z = z :=
    Work.Higman.H8.pow_card_sub_one_fixes_omega1 h
  have hk2 := Work.Higman.apply_apply_eq_self_of_fixes_omega1
    (k := h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1))
    (Work.Higman.map_pow_xi_eq h hA.map_eq (Nat.card ↥(Work.Higman.omega1 P) - 1))
    hA.abelian htop hkΩ
  rw [pow_two, MulAut.mul_apply]
  exact hk2 a ha

/-! ## The size of `D`

In the crux configuration the minimal cover `D` has `|D| = |Ω₁(P)|³`.  This is
`Work.Higman.H8.c4_sq_a2_card_quot` (Higman's `m = n` count, axiom-clean), which gives
`|D/A| = |Ω₁(P)|`, combined with `|A| = |Ω₁(P)|²`. -/
theorem crux_D_card (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hZc : Subgroup.center P = Work.Higman.omega1 P)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A < D)
    (hDmin : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D)
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    (hD2 : ∀ d ∈ D, d ^ 2 ∈ Work.Higman.powSub A 2)
    (hnZ : ¬(∀ e ∈ D, ∀ a ∈ A, e * a = a * e)) :
    Nat.card ↥D = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  haveI hAn : A.Normal := hA.normal
  have hNA : Work.Higman.omega1 P ≤ A := htop ▸ Work.Higman.powSub_le (A := A) (by norm_num)
  have hA2le : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (by norm_num)
  have hnotcenter : ¬ A ≤ Subgroup.center P := by
    intro hc
    have hAle : A ≤ Work.Higman.powSub A 2 :=
      calc A ≤ Subgroup.center P := hc
        _ = Work.Higman.omega1 P := hZc
        _ = Work.Higman.powSub A 2 := htop.symm
    have hEq : A = Work.Higman.powSub A 2 := le_antisymm hAle hA2le
    have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
      congrArg (fun X : Subgroup P => Nat.card ↥X) hEq
    rw [htop, hcard] at h1
    have h4 := h.omega1_card_ge_four
    nlinarith [h1, h4]
  have hcent := Work.Higman.MSA.centralizer_eq_self h hA hmax hNA hGs hsq hA4 htop hcard hnotcenter
  have hDd' : ⁅D, D⁆ = Work.Higman.powSub A 2 := hDd.trans htop.symm
  have hD2le : Work.Higman.powSub D 2 ≤ Work.Higman.powSub A 2 := by
    show Subgroup.closure {y : P | ∃ x ∈ D, x ^ 2 = y} ≤ Work.Higman.powSub A 2
    rw [Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact hD2 x hx
  have hPhi : Work.Higman.powSub D 2 ⊔ ⁅D, D⁆ = Work.Higman.powSub A 2 :=
    le_antisymm (sup_le hD2le (le_of_eq hDd')) ((le_of_eq hDd'.symm).trans le_sup_right)
  have hquot : Nat.card (↥D ⧸ (A.subgroupOf D)) = Nat.card ↥(Work.Higman.omega1 P) :=
    Work.Higman.H8.c4_sq_a2_card_quot h hA hGs hNA htop hcent hDn hDinv (le_of_lt hAD)
      (ne_of_gt hAD) hDd' hPhi hDmin
      (crux_comm_A_D_eq h hA hA4 htop (le_of_lt hAD) hDinv hnZ)
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf D)
  have hsub : Nat.card ↥(A.subgroupOf D) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_of_lt hAD))
  rw [hquot, hsub, hcard] at hlag
  rw [hlag]
  ring

/-- In the crux configuration `D` is a proper subgroup of `P`: `[D,D] = Ω₁(P) ≠ A = [P,P]`. -/
theorem crux_D_ne_top (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    D ≠ ⊤ := by
  intro htop'
  have heq : A = Work.Higman.omega1 P := by
    rw [← hGs, ← htop']
    exact hDd
  have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.omega1 P) := by rw [heq]
  have h2 : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 :=
    h1.symm.trans hcard
  have h4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
  have hq : 0 < Nat.card ↥(Work.Higman.omega1 P) := by omega
  nlinarith [h2, h4]

/-- **The crux configuration violates Higman's Lemma 13.**  Together with `crux_D_card`
(`|D| = |Ω₁(P)|³`) and `crux_D_ne_top` this shows `|P| > |Ω₁(P)|³ = |Z(P)|³`. -/
theorem crux_card_gt (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hZc : Subgroup.center P = Work.Higman.omega1 P)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A < D)
    (hDmin : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D)
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    (hD2 : ∀ d ∈ D, d ^ 2 ∈ Work.Higman.powSub A 2)
    (hnZ : ¬(∀ e ∈ D, ∀ a ∈ A, e * a = a * e)) :
    (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 < Nat.card P := by
  have h1 : Nat.card ↥D = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
    crux_D_card h hA hmax hGs hsq hA4 htop hcard hZc hDn hDinv hAD hDmin hDd hD2 hnZ
  have h2 : Nat.card ↥D < Nat.card P := by
    haveI : Fintype ↥D := Fintype.ofFinite _
    haveI : Fintype P := Fintype.ofFinite P
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    refine Fintype.card_lt_of_injective_not_surjective (fun x : ↥D => (x : P))
      Subtype.coe_injective ?_
    intro hsurj
    apply crux_D_ne_top h hGs hDd hcard
    rw [Subgroup.eq_top_iff']
    intro x
    obtain ⟨y, hy⟩ := hsurj x
    exact hy ▸ y.2
  rw [← h1]
  exact h2

/-- **The crux configuration is impossible as soon as Higman's bound `|P| ≤ |Z(P)|³`
holds** (this is Higman's Lemma 13; `crux_card_gt` is the statement that the crux configuration
violates it). -/
theorem crux_false_of_card_le_cube (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hZc : Subgroup.center P = Work.Higman.omega1 P)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A < D)
    (hDmin : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D)
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    (hD2 : ∀ d ∈ D, d ^ 2 ∈ Work.Higman.powSub A 2)
    (hnZ : ¬(∀ e ∈ D, ∀ a ∈ A, e * a = a * e))
    (hbound : Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3) :
    False :=
  absurd (crux_card_gt h hA hmax hGs hsq hA4 htop hcard hZc hDn hDinv hAD hDmin hDd hD2 hnZ)
    (not_lt.mpr hbound)

/-! ## New structural lemmas (session 5)

The crux configuration has `P / Ω₁(P)` of class two: `⁅A, ⊤⁆ = A ^ (2) = Ω₁(P)`.  This is
Higman's unipotence dichotomy (`nsd_comm_eq_bot_or_omega1`, which says `⁅A,⊤⁆ ∈ {⊥, Ω₁(P)}`)
together with `nsd_comm_eq_bot_false`, which excludes the central case.

Consequently the *commutator pairing* `β x̄ ȳ = ⁅x,y⁆ mod A²` and the *squaring map*
`σ x̄ = x² mod A²` are well defined `𝔽₂`-bilinear/quadratic maps `P/A → A/A²` which are
`ξ`-equivariant — these are Higman's §4 structures in the crux. -/

/-- **The crux has class three**: `⁅A, ⊤⁆ = A ^ (2) = Ω₁(P)`. -/
theorem crux_comm_A_top_eq (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    Bracket.bracket A (⊤ : Subgroup P) = Work.Higman.powSub A 2 := by
  have hNA : Work.Higman.omega1 P ≤ A :=
    htop ▸ Work.Higman.powSub_le (A := A) (by norm_num)
  rcases Work.Higman.H8.Clean.nsd_comm_eq_bot_or_omega1 h hA.map_eq hA.abelian hGs htop with
    hb | hT
  · exact absurd hb (Work.Higman.H8.Clean.nsd_comm_eq_bot_false h hA.abelian hNA hGs hsq htop)
  · rw [hT, htop]

/-- `Ω₁(P) ≤ A` in the crux (the reverse containment to `A ^ (2) = Ω₁(P)`). -/
theorem crux_omega1_le {A : Subgroup P} (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    Work.Higman.omega1 P ≤ A :=
  htop ▸ Work.Higman.powSub_le (A := A) (by norm_num)

/-! ## Higman's Lemma 8 (auxiliary result 8) as a contradiction criterion

`Work.Higman.NSM.sharp8` (axiom-clean) says: in the `C₄` configuration, a *minimal*
`ξ`-invariant normal cover `C > A` with `⁅C,C⁆ = A` is impossible.  We record this in the
crux's vocabulary, together with its `C = ⊤` special case (Higman's Lemma 8 with the cover
`P`, which is `Work.Higman.H8.Clean.nsd_false_of_irreducible`). -/

/-- **Higman's Lemma 8 in the crux.**  A `ξ`-invariant normal `C` with `A < C ≤ P`, no
`ξ`-invariant normal subgroup strictly between `A` and `C`, and `⁅C,C⁆ = A` is impossible. -/
theorem crux_false_of_cover (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (hAC : A < C)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ C → E = A ∨ E = C)
    (hCd : Bracket.bracket C C = A) : False := by
  have hNA : Work.Higman.omega1 P ≤ A := crux_omega1_le htop
  have hC2 : Work.Higman.powSub C 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  exact Work.Higman.NSM.sharp8 h hA.map_eq hA.abelian hNA hGs hsq hA4 htop hcard hCn hCinv
    (le_of_lt hAC) (ne_of_lt hAC) hcover hC2 hCd

/-- **The irreducible case of the crux.**  If `P/A` has no proper non-trivial `ξ`-invariant
normal subgroup then the crux hypotheses are contradictory (Higman's Lemma 8 with `C = ⊤`). -/
theorem crux_false_of_irreducible_P (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hirr : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E = A ∨ E = ⊤) : False :=
  Work.Higman.H8.Clean.nsd_false_of_irreducible h hA.map_eq hA.abelian (crux_omega1_le htop)
    hGs hsq hA4 htop hcard hirr

/-- **Reduction of the crux to the existence of a Lemma-8 cover.**

The crux is contradictory as soon as there is *any* `ξ`-invariant normal subgroup `C` with
`A < C ≤ P`, no `ξ`-invariant normal subgroup strictly between `A` and `C`, and `⁅C,C⁆ = A`. -/
theorem crux_false_of_exists_cover (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hex : ∃ C : Subgroup P, C.Normal ∧ C.map (h.xi : MulAut P).toMonoidHom = C ∧ A < C ∧
      (∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
        A ≤ E → E ≤ C → E = A ∨ E = C) ∧ Bracket.bracket C C = A) : False := by
  obtain ⟨C, hCn, hCinv, hAC, hcover, hCd⟩ := hex
  exact crux_false_of_cover h hA hGs hsq hA4 htop hcard hCn hCinv hAC hcover hCd

/-- `D ^ (2) = A ^ (2)` in the crux: every square of `D` lies in `A ^ (2)` and `A ≤ D`. -/
theorem crux_powSub_D_two_eq {A D : Subgroup P}
    (hD2 : ∀ d ∈ D, d ^ 2 ∈ Work.Higman.powSub A 2) (hAD : A ≤ D) :
    Work.Higman.powSub D 2 = Work.Higman.powSub A 2 := by
  refine le_antisymm ?_ ?_
  · rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, hx, rfl⟩
    exact hD2 x hx
  · exact Work.Higman.powSub_mono hAD

/-- `⁅D,D⁆ = A ^ (2)` in the crux (from `⁅D,D⁆ = Ω₁(P)` and `A ^ (2) = Ω₁(P)`). -/
theorem crux_DD_eq_powSub {A D : Subgroup P}
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    Bracket.bracket D D = Work.Higman.powSub A 2 := hDd.trans htop.symm

/-- **`A ^ (2) ≠ A` in the crux** (they have `q` resp. `q ^ 2` elements, `q ≥ 4`). -/
theorem crux_powSub_two_ne_self (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    Work.Higman.powSub A 2 ≠ A := by
  intro hEq
  have h1 : Nat.card ↥(Work.Higman.powSub A 2) = Nat.card ↥A :=
    congrArg (fun X : Subgroup P => Nat.card ↥X) hEq
  rw [htop, hcard] at h1
  have h4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
  have hq : 0 < Nat.card ↥(Work.Higman.omega1 P) := by omega
  nlinarith [h1, h4]

/-- **The `hPD` hypothesis bites.**  From `⁅⊤,D⁆ = A` we get an element `x` and an element
`d ∈ D` whose commutator is *not* in `A ^ (2)`: otherwise `A = ⁅⊤,D⁆ ≤ A ^ (2) = A`, i.e.
`A = A ^ (2)`, contradicting `|A| = |Ω₁(P)|²` with `|Ω₁(P)| ≥ 4`. -/
theorem crux_exists_comm_not_mem_sq (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hPD : Bracket.bracket (⊤ : Subgroup P) D = A) :
    ∃ x ∈ (⊤ : Subgroup P), ∃ d ∈ D, ⁅x, d⁆ ∉ Work.Higman.powSub A 2 := by
  by_contra hcon
  push_neg at hcon
  have hle : Bracket.bracket (⊤ : Subgroup P) D ≤ Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_le]
    intro x _ d hd
    exact hcon x (Subgroup.mem_top x) d hd
  have hA2le : Work.Higman.powSub A 2 ≤ A :=
    Work.Higman.powSub_le (A := A) (n := 2) (by norm_num)
  have hAeq : A = Work.Higman.powSub A 2 := le_antisymm (hPD ▸ hle) hA2le
  exact crux_powSub_two_ne_self h htop hcard hAeq.symm

/-- **Reduction of the crux to the fleet's `NSM.c4DerivSqCase`.**

The crux hypotheses (without `hmax`, `hZc`, `hDmin`, `hPD`, `hbig`, `hnZ`) already give the full
`C₄`-configuration for the pair `(A,D)`: `A ⊢` abelian `ξ`-invariant, `Ω₁(P) ≤ A`,
`⁅⊤,⊤⁆ = A`, all squares of `P` in `A`, `A⁴ = 1`, `A² = Ω₁(P)`, `|A| = |Ω₁(P)|²`, `D ⊴ P`
`ξ`-invariant, `A < D`, `D² = A²` and `⁅D,D⁆ = A²`.  Hence *any* theorem of the shape of
`Work.Higman.NSM.c4DerivSqCase` (its `sorry` is the fleet's single remaining obligation for
Higman's Theorem 1) yields the crux.  The `hPD`-flavoured extra data
(`∃x, d ∈ D` with `⁅x,d⁆ ∉ A²`, `crux_exists_comm_not_mem_sq` above) is *not* needed for this
reduction — it is precisely the extra input available for proving the `c4DerivSqCase`-shaped
statement in this configuration. -/
theorem crux_case_large_hard_of_c4DerivSqCase
    (hc4 : ∀ {Q : Type} [Group Q] [Finite Q] (hQ : Work.Higman.IsSuzuki2Grp Q)
      {A' D' : Subgroup Q},
      A'.map (hQ.xi : MulAut Q).toMonoidHom = A' →
      (∀ x ∈ A', ∀ y ∈ A', x * y = y * x) →
      Work.Higman.omega1 Q ≤ A' →
      Bracket.bracket (⊤ : Subgroup Q) ⊤ = A' →
      (∀ x : Q, x ^ 2 ∈ A') →
      Work.Higman.powSub A' 4 = ⊥ →
      Work.Higman.powSub A' 2 = Work.Higman.omega1 Q →
      Nat.card ↥A' = (Nat.card ↥(Work.Higman.omega1 Q)) ^ 2 →
      D'.Normal → D'.map (hQ.xi : MulAut Q).toMonoidHom = D' →
      A' ≤ D' → D' ≠ A' →
      Work.Higman.powSub D' 2 = Work.Higman.powSub A' 2 →
      Bracket.bracket D' D' = Work.Higman.powSub A' 2 → False)
    (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) (hAD : A < D)
    (hD2 : ∀ d ∈ D, d ^ 2 ∈ Work.Higman.powSub A 2)
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P) : False :=
  hc4 h hA.map_eq hA.abelian (crux_omega1_le htop) hGs hsq hA4 htop hcard hDn hDinv
    (le_of_lt hAD) (ne_of_lt hAD).symm (crux_powSub_D_two_eq hD2 (le_of_lt hAD))
    (crux_DD_eq_powSub hDd htop)

/-! ## The pairing-level Jacobi relation (Step 4 input)

Since `⁅A,⊤⁆ = A ^ (2) ≤ Z(P)` (`crux_comm_A_top_eq`), `P` has class at most three and the Jacobi
identity (`Work.Higman.Q3.crux_class_three_jacobi`) holds.  For `y, z ∈ D` the commutator
`⁅y,z⁆ ∈ ⁅D,D⁆ = Ω₁(P)` is central, and `⁅z,x⁆ = ⁅x,z⁆⁻¹` with `⁅x,z⁆ ∈ A` whose double
commutators are involutions; hence

    ⁅⁅x,y⁆,z⁆ = ⁅⁅x,z⁆,y⁆        (`x ∈ P`, `y, z ∈ D`),

i.e. `φ(B(x,y),z) = φ(B(y,z),x)` in the notation of the fleet's Step-4 plan
(`NSM/NOTES_redcase_hardcase.md`).  This is the structural input for the resonance computation
that has to close the `c4DerivSqCase`-shaped gap (Higman 1963, Lemma 13, p. 92). -/

/-- An element of a group with `a * a = 1` equals its own inverse. -/
theorem crux_inv_eq_self_of_sq_eq_one {G : Type} [Group G] {a : G} (h : a * a = 1) : a⁻¹ = a := by
  calc a⁻¹ = a⁻¹ * (a * a) := by rw [h, mul_one]
    _ = a := by group

theorem crux_comm_sq_eq_one (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hZc : Subgroup.center P = Work.Higman.omega1 P)
    {b : P} (hb : b ∈ A) (y : P) : ⁅b, y⁆ * ⁅b, y⁆ = 1 := by
  have hc : ⁅b, y⁆ ∈ Subgroup.center P :=
    Work.Higman.Q3.commutatorElement_mem_center_of_mem h hA hGs htop hb y
  have hom : ⁅b, y⁆ ∈ Work.Higman.omega1 P := hZc ▸ hc
  have h2 := h.mem_omega1.mp hom
  rwa [pow_two] at h2

theorem crux_jacobi_rel (h : Work.Higman.IsSuzuki2Grp P) {A D : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hZc : Subgroup.center P = Work.Higman.omega1 P)
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    (x : P) {y z : P} (hy : y ∈ D) (hz : z ∈ D) :
    ⁅⁅x, y⁆, z⁆ = ⁅⁅x, z⁆, y⁆ := by
  have hJ : (⁅⁅x, y⁆, z⁆ * ⁅⁅y, z⁆, x⁆ * ⁅⁅z, x⁆, y⁆ : P) = 1 := by
    simpa only [commutatorElement_def] using
      Work.Higman.Q3.crux_class_three_jacobi h hA hGs hsq htop x y z
  have hyz : ⁅y, z⁆ ∈ Work.Higman.omega1 P := by
    have h1 : ⁅y, z⁆ ∈ Bracket.bracket D D := Subgroup.commutator_mem_commutator hy hz
    rwa [hDd] at h1
  have hyzc : ⁅y, z⁆ ∈ Subgroup.center P := h.omega1_le_center hyz
  have hmid : ⁅⁅y, z⁆, x⁆ = 1 := by
    have h1 : x * ⁅y, z⁆ = ⁅y, z⁆ * x := Subgroup.mem_center_iff.mp hyzc x
    exact commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
  have h2 : ⁅⁅x, y⁆, z⁆ * ⁅⁅z, x⁆, y⁆ = 1 := by
    rw [hmid, mul_one] at hJ
    exact hJ
  have hxzA : ⁅x, z⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top z)
    rwa [hGs] at h1
  have hxyA : ⁅x, y⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rwa [hGs] at h1
  have hzx : ⁅z, x⁆ = ⁅x, z⁆⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]; group
  have hinv : ⁅⁅z, x⁆, y⁆ = ⁅⁅x, z⁆, y⁆ := by
    rw [hzx]
    have hc : ⁅⁅x, z⁆, y⁆ ∈ Subgroup.center P :=
      Work.Higman.Q3.commutatorElement_mem_center_of_mem h hA hGs htop hxzA y
    have hbb : ⁅x, z⁆⁻¹ * ⁅⁅x, z⁆, y⁆⁻¹ = ⁅⁅x, z⁆, y⁆⁻¹ * ⁅x, z⁆⁻¹ := by
      have h1 : (⁅x, z⁆ * ⁅⁅x, z⁆, y⁆)⁻¹ = (⁅⁅x, z⁆, y⁆ * ⁅x, z⁆)⁻¹ := by
        rw [Subgroup.mem_center_iff.mp hc ⁅x, z⁆]
      rw [mul_inv_rev, mul_inv_rev] at h1
      exact h1.symm
    have h6 : ⁅⁅x, z⁆, y⁆⁻¹ = ⁅⁅x, z⁆, y⁆ :=
      crux_inv_eq_self_of_sq_eq_one (crux_comm_sq_eq_one h hA hGs htop hZc hxzA y)
    have hkey : ⁅⁅x, z⁆⁻¹, y⁆ = ⁅x, z⁆⁻¹ * ⁅⁅x, z⁆, y⁆⁻¹ * ⁅x, z⁆ := by
      rw [commutatorElement_def]; group
    rw [hkey, hbb, mul_assoc, inv_mul_cancel, mul_one, h6]
  have h5 : ⁅⁅x, y⁆, z⁆⁻¹ = ⁅⁅x, y⁆, z⁆ :=
    crux_inv_eq_self_of_sq_eq_one (crux_comm_sq_eq_one h hA hGs htop hZc hxyA z)
  have h6 : ⁅⁅x, z⁆, y⁆⁻¹ = ⁅⁅x, z⁆, y⁆ :=
    crux_inv_eq_self_of_sq_eq_one (crux_comm_sq_eq_one h hA hGs htop hZc hxzA y)
  have h4 : ⁅⁅x, y⁆, z⁆ * ⁅⁅x, z⁆, y⁆ = 1 := by rw [← hinv]; exact h2
  have ha : ⁅⁅x, y⁆, z⁆ = (⁅⁅x, z⁆, y⁆)⁻¹ := by
    calc ⁅⁅x, y⁆, z⁆ = ⁅⁅x, y⁆, z⁆ * (⁅⁅x, z⁆, y⁆ * (⁅⁅x, z⁆, y⁆)⁻¹) := by group
      _ = (⁅⁅x, y⁆, z⁆ * ⁅⁅x, z⁆, y⁆) * (⁅⁅x, z⁆, y⁆)⁻¹ := by group
      _ = (⁅⁅x, z⁆, y⁆)⁻¹ := by rw [h4, one_mul]
  rw [ha, h6]

theorem crux_jacobi_D (h : Work.Higman.IsSuzuki2Grp P) {D : Subgroup P}
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    {x y z : P} (hx : x ∈ D) (hy : y ∈ D) (hz : z ∈ D) : ⁅⁅x, y⁆, z⁆ = 1 := by
  have h1 : ⁅x, y⁆ ∈ Work.Higman.omega1 P := by
    have h2 : ⁅x, y⁆ ∈ Bracket.bracket D D := Subgroup.commutator_mem_commutator hx hy
    rwa [hDd] at h2
  have h3 : ⁅x, y⁆ ∈ Subgroup.center P := h.omega1_le_center h1
  have h4 : z * ⁅x, y⁆ = ⁅x, y⁆ * z := Subgroup.mem_center_iff.mp h3 z
  exact commutatorElement_eq_one_iff_mul_comm.mpr h4.symm

theorem crux_case_large_hard {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P} (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) ⊤ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hZc : Subgroup.center P = Work.Higman.omega1 P)
    (hDn : D.Normal) (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A < D)
    (hDmin : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D)
    (hDd : Bracket.bracket D D = Work.Higman.omega1 P)
    (hD2 : ∀ d ∈ D, d ^ 2 ∈ Work.Higman.powSub A 2)
    (hPD : Bracket.bracket (⊤ : Subgroup P) D = A)
    (hbig : ∃ x y : P, x ∈ D ∧ y ∈ D ∧ x ∉ A ∧ y ∉ A ∧ x * y ∉ A)
    (hnZ : ¬(∀ e ∈ D, ∀ a ∈ A, e * a = a * e)) :
    False := by
  by_cases hcase : ∃ d : P, d ∈ D ∧ d ∉ A ∧ (h.xi d) * d⁻¹ ∈ A
  · exact crux_false_of_xi_fixed_coset_mod_A h hA htop hsq hcase
  · -- Remaining case: `ξ` acts on `D/A` without non-zero fixed vectors.
    push_neg at hcase
    sorry

end Work.Higman.Q3
