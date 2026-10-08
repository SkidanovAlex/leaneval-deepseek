import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.quot_center_omega1_iso
import Submission.Work.Higman.pow_two_pow_mul
import Submission.Work.Higman.higman9_exists_new

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-! ## Elementary facts about the centre

The centre is `ξ`-invariant (it is characteristic), and Higman's Lemma 1 applies to it: with
`q = |Ω₁(P)|` there is `e` with `|Z(P)| = q ^ e`, every central element having order dividing
`2 ^ e` and `2 ^ e` attained. -/

/-- The centre is `ξ`-invariant. -/
theorem map_center_xi_new (h : IsSuzuki2Grp P) :
    (Subgroup.center P).map (h.xi : MulAut P).toMonoidHom = Subgroup.center P := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨z, hz, rfl⟩
    exact aut_mem_center (h.xi : MulAut P) hz
  · intro x hx
    refine ⟨(h.xi : MulAut P).symm x, ?_, by simp⟩
    exact aut_mem_center (h.xi : MulAut P).symm hx

/-- **Higman's Lemma 1 for the centre.**  There is `e` with `|Z(P)| = |Ω₁(P)| ^ e`, all central
elements of order dividing `2 ^ e`, and `2 ^ e` attained in the centre. -/
theorem exists_center_exp_new (h : IsSuzuki2Grp P) :
    ∃ e : ℕ, (∀ a ∈ Subgroup.center P, a ^ 2 ^ e = 1) ∧
      (∃ a ∈ Subgroup.center P, orderOf a = 2 ^ e) ∧
      Nat.card ↥(Subgroup.center P) = Nat.card ↥(omega1 P) ^ e := by
  obtain ⟨e, h1, h2, h3⟩ := higman_lemma1 h
    (fun x hx y hy => (Subgroup.mem_center_iff.mp hx y).symm) (map_center_xi_new h)
  refine ⟨e, h1, h2, ?_⟩
  rw [h3, inf_eq_right.mpr h.omega1_le_center]

/-- A maximal `ξ`-invariant abelian normal subgroup of exponent dividing `4` has order at most
`|Ω₁(P)| ^ 2` (Higman's Lemma 1 together with `exp ≤ 4`). -/
theorem card_le_card_omega1_sq_of_exp {A : Subgroup P} (h : IsSuzuki2Grp P)
    (hA : IsXiAbelNormal h A) (hOmA : omega1 P ≤ A) (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    Nat.card ↥A ≤ Nat.card ↥(omega1 P) ^ 2 := by
  obtain ⟨e, he1, he2, he3⟩ := higman_lemma1 h hA.abelian hA.map_eq
  have hinf : A ⊓ (omega1 P : Subgroup P) = omega1 P := inf_eq_right.mpr hOmA
  have hcardA : Nat.card ↥A = Nat.card ↥(omega1 P) ^ e := by rw [he3, hinf]
  have he_le : e ≤ 2 := by
    obtain ⟨a, ha, haord⟩ := he2
    have hdvd : 2 ^ e ∣ 4 := by
      rw [← haord]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact hexp a ha)
    have hle : 2 ^ e ≤ 2 ^ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hq2 : 2 ≤ Nat.card ↥(omega1 P) := by
    have := h.omega1_card_ge_four
    omega
  calc Nat.card ↥A = Nat.card ↥(omega1 P) ^ e := hcardA
    _ ≤ Nat.card ↥(omega1 P) ^ 2 := Nat.pow_le_pow_right (by omega) he_le

/-- **The centre is no bigger than `Ω₁(P)` squared**, given a maximal `ξ`-invariant abelian normal
subgroup of exponent dividing `4` (Higman's Lemma 9). -/
theorem card_center_le_card_omega1_sq (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hA : IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A)
    (hexp : ∀ a ∈ A, a ^ 4 = 1) :
    Nat.card ↥(Subgroup.center P) ≤ Nat.card ↥(omega1 P) ^ 2 :=
  le_trans (Subgroup.card_le_of_le (center_le_of_maximal h hA hmax))
    (card_le_card_omega1_sq_of_exp h hA (omega1_le_of_maximal h hA hmax) hexp)

section OrderQSquaredCase

open scoped commutatorElement

/-! ## Class-two commutator calculus

These are the standard identities in a group of nilpotency class two (all commutators central).
They are restated locally so that this file depends on no module outside the axiom-clean
`Higman` development. -/

section ClassTwo

variable {G : Type*} [Group G]

/-- In a group of class two every commutator is central, and every element commutes with it. -/
theorem loc_cz_commutator_central_comm
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    z * ⁅x, y⁆ = ⁅x, y⁆ * z :=
  Subgroup.mem_center_iff.mp
    (hZ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))) z

/-- `x * y * x⁻¹ = ⁅x, y⁆ * y`. -/
theorem loc_cz_mul_mul_inv_eq_commutator_mul (x y : G) : x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

/-- In class two, `⁅x, y⁆ ^ 2 = ⁅x ^ 2, y⁆`. -/
theorem loc_cz_commutator_sq_eq (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y : G) :
    ⁅x, y⁆ ^ 2 = ⁅x ^ 2, y⁆ := by
  have h1 : x * y * x⁻¹ = ⁅x, y⁆ * y := loc_cz_mul_mul_inv_eq_commutator_mul x y
  have hc : x * ⁅x, y⁆ = ⁅x, y⁆ * x := loc_cz_commutator_central_comm hZ x y x
  have key : ⁅x ^ 2, y⁆ = ⁅x, y⁆ ^ 2 := by
    rw [commutatorElement_def, pow_two (a := x)]
    rw [show (x * x) * y * (x * x)⁻¹ * y⁻¹ = x * (x * y * x⁻¹) * x⁻¹ * y⁻¹ by group]
    rw [h1]
    rw [show x * (⁅x, y⁆ * y) * x⁻¹ * y⁻¹
        = (x * ⁅x, y⁆) * (y * x⁻¹) * y⁻¹ by group]
    rw [hc]
    rw [show (⁅x, y⁆ * x) * (y * x⁻¹) * y⁻¹
        = ⁅x, y⁆ * (x * y * x⁻¹) * y⁻¹ by group]
    rw [h1]
    rw [show ⁅x, y⁆ * (⁅x, y⁆ * y) * y⁻¹ = ⁅x, y⁆ * ⁅x, y⁆ by group]
    rw [pow_two]
  exact key.symm

/-- Class two: `[x * y, z] = [x,z] * [y,z]`. -/
theorem loc_cz_commutator_mul_left (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hcy : ∀ w : G, w * ⁅y, z⁆ = ⁅y, z⁆ * w := loc_cz_commutator_central_comm hZ y z
  have hcx : ∀ w : G, w * ⁅x, z⁆ = ⁅x, z⁆ * w := loc_cz_commutator_central_comm hZ x z
  have h1 : x * z * x⁻¹ = ⁅x, z⁆ * z := loc_cz_mul_mul_inv_eq_commutator_mul x z
  have h2 : y * z * y⁻¹ = ⁅y, z⁆ * z := loc_cz_mul_mul_inv_eq_commutator_mul y z
  rw [commutatorElement_def]
  rw [show x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ by group]
  rw [h2]
  rw [show x * (⁅y, z⁆ * z) * x⁻¹ * z⁻¹ = (x * ⁅y, z⁆) * (z * x⁻¹) * z⁻¹ by group]
  rw [hcy x]
  rw [show (⁅y, z⁆ * x) * (z * x⁻¹) * z⁻¹ = ⁅y, z⁆ * (x * z * x⁻¹) * z⁻¹ by group]
  rw [h1]
  rw [show ⁅y, z⁆ * (⁅x, z⁆ * z) * z⁻¹ = ⁅y, z⁆ * ⁅x, z⁆ by group]
  rw [hcx ⁅y, z⁆]

/-- Class two: `[z, x * y] = [z,x] * [z,y]`. -/
theorem loc_cz_commutator_mul_right (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  have h1 : ⁅z, x * y⁆ = ⁅x * y, z⁆⁻¹ := by rw [← commutatorElement_inv]
  rw [h1, loc_cz_commutator_mul_left hZ x y z, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact (loc_cz_commutator_central_comm hZ z y ⁅z, x⁆).symm

end ClassTwo

/-! ## The order-`q ^ 2` centre case -/

/-- **The order-`q ^ 2` centre case is impossible.**  If a Suzuki 2-group `P` has
`|Z(P)| = q ^ 2` with `q = |Ω₁(P)|`, is of nilpotency class at most `2` (`[P,P] ≤ Z(P)`) and every
square of `P` is central, then `P` is abelian, contradicting the Suzuki hypothesis. -/
theorem loc_center_sq_case_false {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P)
    (hcard : Nat.card ↥(Subgroup.center P) = Nat.card ↥(omega1 P) ^ 2)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P) : False := by
  classical
  have hq4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
  -- ### Step 1: `[P, P] ≤ Ω₁(P)`
  -- In class two `⁅x, y⁆ ^ 2 = ⁅x ^ 2, y⁆ = 1` because `x ^ 2` is central.
  have hcommΩ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    refine h.mem_omega1.mpr ?_
    have hx2 : x ^ 2 * y = y * x ^ 2 := (Subgroup.mem_center_iff.mp (hsq x) y).symm
    rw [loc_cz_commutator_sq_eq hcomm x y, commutatorElement_def, hx2]
    group
  -- ### Step 2: `Z(P) ≠ Ω₁(P)`
  have hne : Subgroup.center P ≠ omega1 P := by
    intro hZeq
    have hq2 : Nat.card ↥(omega1 P) * Nat.card ↥(omega1 P) = Nat.card ↥(omega1 P) := by
      have h' : Nat.card ↥(omega1 P) = Nat.card ↥(omega1 P) ^ 2 := by
        have hc := hcard
        rw [hZeq] at hc
        exact hc
      rw [pow_two] at h'
      exact h'.symm
    have hmul : Nat.card ↥(omega1 P) * (Nat.card ↥(omega1 P) - 1) = 0 := by
      rw [Nat.mul_sub_left_distrib, mul_one, hq2, Nat.sub_self]
    rcases Nat.mul_eq_zero.mp hmul with h1 | h1
    · omega
    · omega
  -- ### Step 3: `P / Z(P) ≃* Ω₁(P)` as `ξ`-modules
  obtain ⟨e, he⟩ := quot_center_omega1_iso h hcommΩ hne
  -- `Ω₁(P)` is abelian
  letI : CommGroup ↥(omega1 P) :=
    { mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }
  -- the action of `ξ` on `Ω₁(P)`
  have hxi_mem : ∀ u : ↥(omega1 P), h.xi (u : P) ∈ omega1 P := fun u => by
    have h1 := map_xi_omega1 h
    have h2 : h.xi (u : P) ∈ (omega1 P).map (h.xi : MulAut P).toMonoidHom :=
      Subgroup.mem_map_of_mem _ u.2
    rwa [h1] at h2
  let ξV : MulAut ↥(omega1 P) :=
    { toFun := fun u => ⟨h.xi u, hxi_mem u⟩
      invFun := fun u =>
        ⟨(h.xi : MulAut P).symm u, symm_mem_of_map_eq h.xi (map_xi_omega1 h) u.2⟩
      left_inv := fun u => by ext; simp
      right_inv := fun u => by ext; simp
      map_mul' := fun u v => by ext; simp }
  have ξV_pow : ∀ (k : ℕ) (u : ↥(omega1 P)), ((ξV ^ k) u : P) = (h.xi ^ k) (u : P) := by
    intro k
    induction k with
    | zero => intro u; simp
    | succ k ih =>
        intro u
        have h1 : ((ξV ^ (k + 1)) u : ↥(omega1 P)) = ξV ((ξV ^ k) u) := by
          rw [pow_succ', MulAut.mul_apply]
        rw [h1]
        show h.xi (((ξV ^ k) u : ↥(omega1 P)) : P) = (h.xi ^ (k + 1)) (u : P)
        rw [ih u, pow_succ', MulAut.mul_apply]
  -- `Ω₁(P)` has exponent two and `ξ` permutes its non-identity elements transitively
  have hΩsq : ∀ a : ↥(omega1 P), a * a = 1 := fun a => by
    rw [← pow_two]
    exact Subtype.ext (h.mem_omega1.mp a.2)
  have htrans : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξV ^ k) a = b := by
    intro a b ha hb
    have key : ∀ u : ↥(omega1 P), u ≠ 1 → orderOf (u : P) = 2 := by
      intro u hu
      have hd : orderOf (u : P) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp u.2)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2'
      · exact absurd (Subtype.ext (orderOf_eq_one_iff.mp h1)) hu
      · exact h2'
    obtain ⟨k, hk⟩ := h.trans (a : P) (b : P) (key a ha) (key b hb)
    exact ⟨k, Subtype.ext (by rw [ξV_pow k a]; exact hk)⟩
  -- ### Step 4: the commutator pairing is a non-trivial alternating `ξ`-equivariant
  -- biadditive map `Ω₁(P) × Ω₁(P) → Ω₁(P)`
  -- a lift of an element of `P/Z(P)` to `P`
  let rep : (P ⧸ Subgroup.center P) → P :=
    fun q => Classical.choose (Quotient.exists_rep q)
  have rep_spec : ∀ q : (P ⧸ Subgroup.center P), QuotientGroup.mk (rep q) = q :=
    fun q => Classical.choose_spec (Quotient.exists_rep q)
  have hc_mem : ∀ x y : P, ⁅x, y⁆ ∈ omega1 P := fun x y =>
    hcommΩ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  let c : ↥(omega1 P) → ↥(omega1 P) → ↥(omega1 P) :=
    fun u v => ⟨⁅rep (e.symm u), rep (e.symm v)⁆, hc_mem _ _⟩
  have hZcent : ∀ z ∈ Subgroup.center P, ∀ x : P, x * z = z * x :=
    fun z hz x => Subgroup.mem_center_iff.mp hz x
  have hcz : ∀ (a b z : P), z ∈ Subgroup.center P → ⁅a * z, b⁆ = ⁅a, b⁆ := by
    intro a b z hz
    rw [commutatorElement_def]
    show a * z * b * (a * z)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹
    rw [show a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * (z⁻¹ * a⁻¹) * b⁻¹ from by group,
      (hZcent z hz b).symm]
    group
  have hcz2 : ∀ (a b z : P), z ∈ Subgroup.center P → ⁅a, b * z⁆ = ⁅a, b⁆ := by
    intro a b z hz
    rw [commutatorElement_def]
    show a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * a⁻¹ * b⁻¹
    rw [show a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ from by group,
      (hZcent z hz a⁻¹).symm]
    group
  have hcongr : ∀ (x x' y y' : P), x⁻¹ * x' ∈ Subgroup.center P →
      y⁻¹ * y' ∈ Subgroup.center P → ⁅x, y⁆ = ⁅x', y'⁆ := by
    intro x x' y y' hx hy
    obtain ⟨z, hz, hzx⟩ : ∃ z ∈ Subgroup.center P, x' = x * z := ⟨x⁻¹ * x', hx, by group⟩
    obtain ⟨w, hw, hwy⟩ : ∃ w ∈ Subgroup.center P, y' = y * w := ⟨y⁻¹ * y', hy, by group⟩
    rw [hzx, hwy, hcz _ _ z hz, hcz2 _ _ w hw]
  have c_mk : ∀ x y : P,
      c (e (QuotientGroup.mk x)) (e (QuotientGroup.mk y)) = ⟨⁅x, y⁆, hc_mem x y⟩ := by
    intro x y
    have hx0 : e.symm (e (QuotientGroup.mk x)) = QuotientGroup.mk x :=
      MulEquiv.symm_apply_apply e _
    have hy0 : e.symm (e (QuotientGroup.mk y)) = QuotientGroup.mk y :=
      MulEquiv.symm_apply_apply e _
    obtain ⟨z1, hz1, h1⟩ : ∃ z ∈ Subgroup.center P, x = rep (QuotientGroup.mk x) * z :=
      ⟨(rep (QuotientGroup.mk x))⁻¹ * x,
        QuotientGroup.eq.mp (rep_spec (QuotientGroup.mk x)), by group⟩
    obtain ⟨z2, hz2, h2⟩ : ∃ z ∈ Subgroup.center P, y = rep (QuotientGroup.mk y) * z :=
      ⟨(rep (QuotientGroup.mk y))⁻¹ * y,
        QuotientGroup.eq.mp (rep_spec (QuotientGroup.mk y)), by group⟩
    have hmain : ⁅x, y⁆ = ⁅rep (QuotientGroup.mk x), rep (QuotientGroup.mk y)⁆ := by
      conv_lhs => rw [h1, h2]
      rw [hcz _ _ z1 hz1, hcz2 _ _ z2 hz2]
    apply Subtype.ext
    show ⁅rep (e.symm (e (QuotientGroup.mk x))), rep (e.symm (e (QuotientGroup.mk y)))⁆
      = ⁅x, y⁆
    rw [hx0, hy0, ← hmain]
  have hmul : ∀ a b d : ↥(omega1 P), c (a * b) d = c a d * c b d := by
    intro a b d
    have h1 : (rep (e.symm (a * b)))⁻¹ * (rep (e.symm a) * rep (e.symm b))
        ∈ Subgroup.center P := by
      have hA : QuotientGroup.mk (rep (e.symm (a * b))) = e.symm (a * b) :=
        rep_spec (e.symm (a * b))
      have hB : QuotientGroup.mk (rep (e.symm a) * rep (e.symm b)) = e.symm (a * b) := by
        rw [QuotientGroup.mk_mul, rep_spec (e.symm a), rep_spec (e.symm b)]
        exact (map_mul e.symm a b).symm
      exact QuotientGroup.eq.mp (hA.trans hB.symm)
    have h2 : rep (e.symm (a * b))
        = rep (e.symm a) * rep (e.symm b)
          * ((rep (e.symm (a * b)))⁻¹ * (rep (e.symm a) * rep (e.symm b)))⁻¹ := by group
    have h3 : ⁅rep (e.symm (a * b)), rep (e.symm d)⁆
        = ⁅rep (e.symm a) * rep (e.symm b), rep (e.symm d)⁆ := by
      rw [h2]
      exact hcz _ _ _ (Subgroup.inv_mem _ h1)
    apply Subtype.ext
    show ⁅rep (e.symm (a * b)), rep (e.symm d)⁆
      = ⁅rep (e.symm a), rep (e.symm d)⁆ * ⁅rep (e.symm b), rep (e.symm d)⁆
    rw [h3, loc_cz_commutator_mul_left hcomm]
  have hmulR : ∀ a b d : ↥(omega1 P), c a (b * d) = c a b * c a d := by
    intro a b d
    have h1 : (rep (e.symm (b * d)))⁻¹ * (rep (e.symm b) * rep (e.symm d))
        ∈ Subgroup.center P := by
      have hA : QuotientGroup.mk (rep (e.symm (b * d))) = e.symm (b * d) :=
        rep_spec (e.symm (b * d))
      have hB : QuotientGroup.mk (rep (e.symm b) * rep (e.symm d)) = e.symm (b * d) := by
        rw [QuotientGroup.mk_mul, rep_spec (e.symm b), rep_spec (e.symm d)]
        exact (map_mul e.symm b d).symm
      exact QuotientGroup.eq.mp (hA.trans hB.symm)
    have h2 : rep (e.symm (b * d))
        = rep (e.symm b) * rep (e.symm d)
          * ((rep (e.symm (b * d)))⁻¹ * (rep (e.symm b) * rep (e.symm d)))⁻¹ := by group
    have h3 : ⁅rep (e.symm a), rep (e.symm (b * d))⁆
        = ⁅rep (e.symm a), rep (e.symm b) * rep (e.symm d)⁆ := by
      rw [h2]
      exact hcz2 _ _ _ (Subgroup.inv_mem _ h1)
    apply Subtype.ext
    show ⁅rep (e.symm a), rep (e.symm (b * d))⁆
      = ⁅rep (e.symm a), rep (e.symm b)⁆ * ⁅rep (e.symm a), rep (e.symm d)⁆
    rw [h3, loc_cz_commutator_mul_right hcomm]
  have halt : ∀ a : ↥(omega1 P), c a a = 1 := by
    intro a
    show (⟨⁅rep (e.symm a), rep (e.symm a)⁆, hc_mem _ _⟩ : ↥(omega1 P)) = 1
    apply Subtype.ext
    show ⁅rep (e.symm a), rep (e.symm a)⁆ = (1 : P)
    rw [commutatorElement_def]; group
  have hrep_eq : ∀ u : ↥(omega1 P),
      (rep (e.symm (ξV u)))⁻¹ * h.xi (rep (e.symm u)) ∈ Subgroup.center P := by
    intro u
    have h1 : QuotientGroup.mk (rep (e.symm (ξV u))) = e.symm (ξV u) :=
      rep_spec (e.symm (ξV u))
    have h2 : e (QuotientGroup.mk (h.xi (rep (e.symm u)))) = ξV u := by
      apply Subtype.ext
      show (e (QuotientGroup.mk (h.xi (rep (e.symm u)))) : P) = (ξV u : P)
      rw [he]
      have h3 : e (QuotientGroup.mk (rep (e.symm u))) = e (e.symm u) := by rw [rep_spec]
      rw [h3, MulEquiv.apply_symm_apply]
      rfl
    have h3 : QuotientGroup.mk (h.xi (rep (e.symm u))) = e.symm (ξV u) :=
      e.injective (by rw [h2, MulEquiv.apply_symm_apply])
    have h4 : (QuotientGroup.mk (rep (e.symm (ξV u))) : P ⧸ Subgroup.center P)
        = QuotientGroup.mk (h.xi (rep (e.symm u))) := by
      rw [rep_spec (e.symm (ξV u)), h3]
    exact QuotientGroup.eq.mp h4
  have heq : ∀ a b : ↥(omega1 P), ξV (c a b) = c (ξV a) (ξV b) := by
    intro a b
    have hra := hrep_eq a
    have hrb := hrep_eq b
    apply Subtype.ext
    show h.xi (⁅rep (e.symm a), rep (e.symm b)⁆)
      = ⁅rep (e.symm (ξV a)), rep (e.symm (ξV b))⁆
    have hcommut : h.xi ⁅rep (e.symm a), rep (e.symm b)⁆
        = ⁅h.xi (rep (e.symm a)), h.xi (rep (e.symm b))⁆ := by
      simp only [commutatorElement_def, map_mul, map_inv]
    rw [hcommut]
    refine hcongr _ _ _ _ ?_ ?_
    · simpa [mul_inv_rev] using Subgroup.inv_mem _ hra
    · simpa [mul_inv_rev] using Subgroup.inv_mem _ hrb
  have key := equivariant_bihom_trivial hΩsq ξV htrans c hmul hmulR halt heq
  -- now every commutator is trivial, contradicting non-commutativity
  obtain ⟨x, y, hxy⟩ := h.noncomm
  have h1 : c (e (QuotientGroup.mk x)) (e (QuotientGroup.mk y)) = 1 := key _ _
  rw [c_mk x y] at h1
  have h3 : ⁅x, y⁆ = 1 := congrArg Subtype.val h1
  exact hxy (by
    rw [commutatorElement_def] at h3
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = 1 * (y * x) := by rw [h3]
      _ = y * x := one_mul _)

end OrderQSquaredCase

/-- **Assembly.**  Given a maximal `ξ`-invariant abelian normal subgroup `A` of exponent dividing
`4` containing `Ω₁(P)`, `[P,P]` and all squares (Higman's Lemma 9, existence form), and given that
the case `|Z(P)| = |Ω₁(P)| ^ 2` with all squares central is impossible, the centre is `Ω₁(P)`.

Indeed `Z(P) ≤ A` and `|A| ≤ q ^ 2` with `q = |Ω₁(P)|`, so `|Z(P)| ≤ q ^ 2`; Higman's Lemma 1
writes `|Z(P)| = q ^ e`, and `Z(P) ≠ Ω₁(P)` forces `e = 2`, whence `A = Z(P)` and the
contradiction hypothesis applies. -/
theorem center_eq_omega1_of_exists (h : IsSuzuki2Grp P)
    (hex : ∃ A : Subgroup P, IsXiAbelNormal h A ∧
      (∀ B : Subgroup P, IsXiAbelNormal h B → A ≤ B → B = A) ∧
      omega1 P ≤ A ∧ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A ∧
      (∀ x : P, x ^ 2 ∈ A) ∧ (∀ a ∈ A, a ^ 4 = 1)) :
    Subgroup.center P = omega1 P := by
  obtain ⟨A, hA, hmax, hOmA, hcommA, hsqA, hexpA⟩ := hex
  have hZA : Subgroup.center P ≤ A := center_le_of_maximal h hA hmax
  have hAcard : Nat.card ↥A ≤ Nat.card ↥(omega1 P) ^ 2 :=
    card_le_card_omega1_sq_of_exp h hA hOmA hexpA
  have hZle : Nat.card ↥(Subgroup.center P) ≤ Nat.card ↥(omega1 P) ^ 2 :=
    le_trans (Subgroup.card_le_of_le hZA) hAcard
  obtain ⟨e, _he1, _he2, heq⟩ := exists_center_exp_new h
  rcases eq_or_ne (Subgroup.center P) (omega1 P) with hcase | hcase
  · exact hcase
  · exfalso
    have hq4 : 4 ≤ Nat.card ↥(omega1 P) := h.omega1_card_ge_four
    have hlt : Nat.card ↥(omega1 P) < Nat.card ↥(Subgroup.center P) :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne h.omega1_le_center (Ne.symm hcase))
    have he2 : e = 2 := by
      have h1 : 1 < e := by
        by_contra hcon
        push_neg at hcon
        interval_cases e
        · rw [heq, pow_zero] at hlt; omega
        · rw [heq, pow_one] at hlt; omega
      have h2 : e ≤ 2 := by
        rw [heq] at hZle
        exact (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card ↥(omega1 P))).mp hZle
      omega
    have hcard2 : Nat.card ↥(Subgroup.center P) = Nat.card ↥(omega1 P) ^ 2 := by rw [heq, he2]
    have hAZ : Subgroup.center P = A := by
      refine Subgroup.eq_of_le_of_card_ge hZA ?_
      rw [hcard2]
      exact hAcard
    exact loc_center_sq_case_false h hcard2 (hAZ ▸ hcommA) (fun x => hAZ ▸ hsqA x)

/-- **Route via exponent `4`.**  If every element of a Suzuki 2-group satisfies `x ^ 4 = 1`, then
`Z(P) = Ω₁(P)`.

Every square is then an involution, so the squaring map `Z(P) → Ω₁(P)` has fibres contained in
cosets of `Ω₁(P)` and `|Z(P)| ≤ q ^ 2`; Higman's Lemma 1 writes `|Z(P)| = q ^ e`, and the case
`e = 2` is impossible: then `Ω₁(P) = Z(P) ^ 2`, so an element `x ∉ Z(P)` has `x ^ 2 ∈ Z(P) ^ 2`,
say `x ^ 2 = z ^ 2` with `z` central, and `(x * z⁻¹) ^ 2 = 1` makes `x * z⁻¹`, hence `x`, central. -/
theorem center_eq_omega1_of_exp_four (h : IsSuzuki2Grp P) (hexp4 : ∀ x : P, x ^ 4 = 1) :
    Subgroup.center P = omega1 P := by
  classical
  -- every square is an involution
  have hsq_om : ∀ x : P, x ^ 2 ∈ omega1 P := by
    intro x
    refine h.mem_omega1.mpr ?_
    have h24 : (x ^ 2) ^ 2 = x ^ 4 := by rw [← pow_mul]
    rw [h24]; exact hexp4 x
  -- the fibres of the squaring map `Z → Ω₁` lie in cosets of `Ω₁`
  have hcard_le : Nat.card ↥(Subgroup.center P) ≤ Nat.card ↥(omega1 P) ^ 2 := by
    haveI : Fintype ↥(Subgroup.center P) := Fintype.ofFinite _
    haveI : Fintype ↥(omega1 P) := Fintype.ofFinite _
    let φ : ↥(Subgroup.center P) → ↥(omega1 P) := fun z => ⟨(z : P) ^ 2, hsq_om (z : P)⟩
    have hfib : ∀ w : ↥(omega1 P),
        Nat.card {z : ↥(Subgroup.center P) // φ z = w} ≤ Nat.card ↥(omega1 P) := by
      intro w
      by_cases hne : ∃ z : ↥(Subgroup.center P), φ z = w
      · obtain ⟨z₀, hz₀⟩ := hne
        refine Nat.card_le_card_of_injective
          (fun z : {z : ↥(Subgroup.center P) // φ z = w} =>
            (⟨(z.1 : P) * (z₀ : P)⁻¹, ?_⟩ : ↥(omega1 P))) ?_
        · have hz2 : (z.1 : P) ^ 2 = (z₀ : P) ^ 2 := by
            have h1 : (z.1 : P) ^ 2 = (w : P) :=
              congrArg (fun t : ↥(omega1 P) => (t : P)) z.2
            have h2 : (z₀ : P) ^ 2 = (w : P) :=
              congrArg (fun t : ↥(omega1 P) => (t : P)) hz₀
            rw [h1, h2]
          have hc : Commute (z.1 : P) ((z₀ : P)⁻¹) :=
            (Subgroup.mem_center_iff.mp z.1.2 ((z₀ : P)⁻¹)).symm
          refine h.mem_omega1.mpr ?_
          rw [hc.mul_pow, inv_pow, ← hz2]
          group
        · intro u v huv
          have huv' : (u.1 : P) * (z₀ : P)⁻¹ = (v.1 : P) * (z₀ : P)⁻¹ :=
            congrArg (fun t : ↥(omega1 P) => (t : P)) huv
          exact Subtype.ext (Subtype.ext (mul_right_cancel huv'))
      · refine Nat.card_le_card_of_injective
          (fun z : {z : ↥(Subgroup.center P) // φ z = w} =>
            (hne ⟨z.1, z.2⟩).elim) ?_
        intro a b _
        exact (hne ⟨a.1, a.2⟩).elim
    have hsum : Nat.card ↥(Subgroup.center P) =
        ∑ w : ↥(omega1 P), Nat.card {z : ↥(Subgroup.center P) // φ z = w} := by
      have h1 : Fintype.card ↥(Subgroup.center P) =
          ∑ w : ↥(omega1 P), Fintype.card {z : ↥(Subgroup.center P) // φ z = w} := by
        rw [← Finset.card_univ]
        rw [Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := φ)
          (fun a _ => Finset.mem_univ (φ a))]
        exact Finset.sum_congr rfl (fun w _ => (Fintype.card_subtype _).symm)
      calc Nat.card ↥(Subgroup.center P) = Fintype.card ↥(Subgroup.center P) := Nat.card_eq_fintype_card
        _ = ∑ w : ↥(omega1 P), Fintype.card {z : ↥(Subgroup.center P) // φ z = w} := h1
        _ = ∑ w : ↥(omega1 P), Nat.card {z : ↥(Subgroup.center P) // φ z = w} :=
              Finset.sum_congr rfl (fun w _ => (Nat.card_eq_fintype_card (α :=
                {z : ↥(Subgroup.center P) // φ z = w})).symm)
    calc Nat.card ↥(Subgroup.center P) =
          ∑ w : ↥(omega1 P), Nat.card {z : ↥(Subgroup.center P) // φ z = w} := hsum
      _ ≤ ∑ _w : ↥(omega1 P), Nat.card ↥(omega1 P) := Finset.sum_le_sum (fun w _ => hfib w)
      _ = Nat.card ↥(omega1 P) * Nat.card ↥(omega1 P) := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]
      _ = Nat.card ↥(omega1 P) ^ 2 := by ring
  obtain ⟨e, he1, he2, heq⟩ := exists_center_exp_new h
  have hq1 : 1 < Nat.card ↥(omega1 P) := by have := h.omega1_card_ge_four; omega
  have he_le : e ≤ 2 := by
    rw [heq] at hcard_le
    exact (Nat.pow_le_pow_iff_right hq1).mp hcard_le
  have hZge : 4 ≤ Nat.card ↥(Subgroup.center P) :=
    le_trans h.omega1_card_ge_four (Subgroup.card_le_of_le h.omega1_le_center)
  rcases (show e = 0 ∨ e = 1 ∨ e = 2 by omega) with h0 | h1 | h2
  · exfalso
    rw [heq, h0] at hZge
    norm_num at hZge
  · exact (Subgroup.eq_of_le_of_card_ge h.omega1_le_center (by rw [heq, h1, pow_one])).symm
  · exfalso
    have hcard2 : Nat.card ↥(Subgroup.center P) = Nat.card ↥(omega1 P) ^ 2 := by rw [heq, h2]
    -- `Ω₁(P) ⊆ Z(P)²`: `ξ` moves a square root of one involution to a square root of any other
    have hZsq_le : omega1 P ≤ powSub (Subgroup.center P) 2 := by
      obtain ⟨a, ha, haord⟩ := he2
      have ha2ne : a ^ 2 ≠ 1 := by
        intro hc
        have h2 : orderOf a = 4 := by rw [haord, h2]; norm_num
        have hd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hc
        rw [h2] at hd
        omega
      have ha2sq : (a ^ 2) ^ 2 = 1 := by
        rw [← pow_mul, show 2 * 2 = 4 from rfl]
        exact hexp4 a
      have ha2ord : orderOf (a ^ 2) = 2 := by
        have hd : orderOf (a ^ 2) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ha2sq
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) ha2ne
        · exact h2
      have hpowmem : ∀ k : ℕ, (h.xi ^ k) a ∈ Subgroup.center P := by
        intro k
        induction k with
        | zero => simpa using ha
        | succ k ih =>
          rw [pow_succ']
          exact aut_mem_center (h.xi : MulAut P) ih
      intro w hw
      rcases eq_or_ne w 1 with rfl | hw1
      · exact Subgroup.one_mem _
      · have hword : orderOf w = 2 := by
          have hd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hw)
          rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
          · exact absurd (orderOf_eq_one_iff.mp h1) hw1
          · exact h2
        obtain ⟨k, hk⟩ := h.trans (a ^ 2) w ha2ord hword
        exact Subgroup.subset_closure ⟨(h.xi ^ k) a, hpowmem k, by rw [← map_pow, hk]⟩
    -- hence `Ω₁(P) = Z(P)²`
    have hZsq : powSub (Subgroup.center P) 2 = omega1 P := by
      refine le_antisymm ?_ hZsq_le
      intro y hy
      obtain ⟨z, hz, rfl⟩ := (mem_powSub_iff
        (fun a ha b hb => (Subgroup.mem_center_iff.mp ha b).symm)).mp hy
      exact hsq_om z
    -- an element outside the centre
    obtain ⟨x, hxZ⟩ : ∃ x : P, x ∉ Subgroup.center P := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨u, v, huv⟩ := h.noncomm
      exact huv ((Subgroup.mem_center_iff.mp (hcon u) v).symm)
    have hx2 : x ^ 2 ∈ powSub (Subgroup.center P) 2 := by rw [hZsq]; exact hsq_om x
    obtain ⟨z, hzZ, hz2⟩ := (mem_powSub_iff
      (fun a ha b hb => (Subgroup.mem_center_iff.mp ha b).symm)).mp hx2
    have hc : Commute x z⁻¹ := by
      have h1 : Commute x z := Subgroup.mem_center_iff.mp hzZ x
      exact h1.inv_right
    have hxz : (x * z⁻¹) ^ 2 = 1 := by
      rw [hc.mul_pow, inv_pow, ← hz2]
      group
    have hmemΩ : x * z⁻¹ ∈ omega1 P := h.mem_omega1.mpr hxz
    have hmemZ : x * z⁻¹ ∈ Subgroup.center P := h.omega1_le_center hmemΩ
    exact hxZ (by
      have h2' : x = (x * z⁻¹) * z := by group
      rw [h2']
      exact Subgroup.mul_mem _ hmemZ hzZ)

/-- In a Suzuki 2-group the centre consists exactly of the elements of order dividing two:
`Z(P) = Ω₁(P)` (Higman 1963, `Ω₁ = Z = Φ = P'`). -/
theorem center_eq_omega1_new {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) : Subgroup.center P = Work.Higman.omega1 P :=
  center_eq_omega1_of_exists h (higman9_exists_new h)

end Work.Higman
