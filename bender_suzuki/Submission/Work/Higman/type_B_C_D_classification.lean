/-
Copyright (c) 2024. All rights reserved.

# Higman's Lemma 12: types `B`, `C`, `D` of order `q ^ 3`

Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), 79--96, Lemma 12
(= Theorem 1 for the order-`q ^ 3` case).

This file proves `Work.Higman.type_B_C_D_classification` **from three facts** which are stated
below and proved elsewhere in this workspace:

* `Work.Higman.center_eq_omega1_new` (`Submission.Work.Higman.center_eq_omega1_new`): in a Suzuki
  2-group `Z(P) = Ω₁(P)`; in particular the centre has exponent two.
* `Work.Higman.sq_mem_center_of_card_eq_center_cube`
  (`Submission.Work.Higman.sq_mem_center_q3`): in a Suzuki 2-group of order `q ^ 3`
  (`q = |Z(P)|`) every square is central, `x ^ 2 ∈ Z(P)` --- the hypothesis of the two-step model.
* `Work.Higman.nonempty_twoStepModel` (`Submission.Work.Higman.nonempty_twoStepModel`): a group
  in which every square is central and whose centre has exponent two is a *two-step* group,
  `P ≃* TwoStep V W b` with `V = P/Z(P)`, `W = Z(P)` and `b` biadditive
  (Higman 1963, §2 and §4).
* the *classification of the cocycle* `Work.Higman.cocycle_normal_form_aux`, which is Higman's
  Lemma 12 in the two-step form: for a biadditive cocycle `b : V → V → W` with `|V| = |W| ^ 2`,
  `b v v ≠ 0` for `v ≠ 0` (anisotropy), `Z(TwoStep V W b) = kerFst` and a cyclic group of
  automorphisms transitive on the involutions, the cocycle is, up to additive coordinate changes
  and a coboundary, one of the three Column V laws `B`, `C`, `D`.  (The statement is
  `Submission.Work.Higman.cocycle_normal_form`; it is proved here as
  `cocycle_normal_form_aux` from the clash-free chain `Q3.L12.dispatch`.)

The assembly (this file) transfers the Suzuki hypotheses to the two-step model, transports the
automorphism `ξ`, and turns the cocycle identity into the required bijection
`e : P ≃ (𝔽_{2ⁿ} × 𝔽_{2ⁿ}) × 𝔽_{2ⁿ}`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.Model
import Submission.Work.Higman.Family
import Submission.Work.Higman.Class
import Submission.Work.Higman.Q3.Defs
-- The two structural inputs `Z(P) = Ω₁(P)` (Higman §§3–5) and "every square is central" are
-- supplied by
-- * `Work.Higman.center_eq_omega1_new` (`Submission.Work.Higman.center_eq_omega1_new`), and
-- * `Work.Higman.sq_mem_center_of_card_eq_center_cube`
--   (`Submission.Work.Higman.sq_mem_center_q3`), which proves `x ^ 2 ∈ Z(P)` for a Suzuki
--   2-group of order `|Z(P)| ^ 3` — the case needed here — from the axiom-clean
--   `Work.Higman.H8.c4_exclusion`; it avoids `Work.Higman.commutator_le_omega1` /
--   `Work.Higman.no_square_derived` (the workspace's open `C₄` case).
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.sq_mem_center_q3
import Submission.Work.Higman.nonempty_twoStepModel
import Submission.Work.Higman.Q3.squaring_form_assembly
import Submission.Work.Higman.Q3.L12.dispatch

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.Higman

open scoped commutatorElement

/-! ## The two-step form of Higman's Lemma 12

This is Higman's Lemma 12 in the two-step form (`= Work.Higman.cocycle_normal_form`).  It is
proved from the clash-free case-analysis chain `Submission.Work.Higman.Q3.L12.dispatch`
(`squaring_form_classification_l12`, which uses `pinned_canonical` and `canonical_dispatch`) and
`Work.Higman.cocycle_normal_form_of_squaring_form` (`Q3/squaring_form_assembly.lean`).

The chain is reproduced under a private name here (rather than imported from
`Submission.Work.Higman.cocycle_normal_form`, which pulls `Q3.induced` → `singer_on_center` and
would clash with `center_eq_omega1` on the declaration `Work.Higman.mulAut_mem_center`). -/

theorem cocycle_normal_form_aux
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    {b : V → V → W} [Biadd b]
    (hcardV : Nat.card V = Nat.card W ^ 2)
    (hW : 4 ≤ Nat.card W)
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (ξ : MulAut (TwoStep V W b))
    (htrans : ∀ x y : TwoStep V W b, orderOf x = 2 → orderOf y = 2 → ∃ k : ℕ, (ξ ^ k) x = y) :
    ∃ (n : ℕ) (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n)
      (c : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n),
      Nat.card W = 2 ^ n ∧ Odd (orderOf θ) ∧
      ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
          ∀ u v : V, ψ (b u v) = bCocycle (GaloisField 2 n) θ ε (φ u) (φ v) +
            (c (φ u) + c (φ v) + c (φ u + φ v)))
        ∨ ((∀ a : GaloisField 2 n, (θ (θ a)) ^ 2 = a) ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
            ∀ u v : V, ψ (b u v) = cCocycle (GaloisField 2 n) θ ε (φ u) (φ v) +
              (c (φ u) + c (φ v) + c (φ u + φ v)))
        ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
            ∀ u v : V, ψ (b u v) = dCocycle (GaloisField 2 n) θ ε (φ u) (φ v) +
              (c (φ u) + c (φ v) + c (φ u + φ v)))) := by
  haveI : Finite V := Work.Higman.finite_V_of_hcardV hcardV hW
  exact Work.Higman.cocycle_normal_form_of_squaring_form
    (Work.Higman.Q3.squaring_form_classification_l12 hcardV hW hinvol hcenter ξ htrans)

/-! ## Assembly -/

/-- **Higman (1963), Theorem 1, types `B`, `C`, `D`** (Lemma 12 of the paper): a Suzuki
2-group whose order equals `q ^ 3` (`q = |Z(P)|`) is `B(n,θ,ε)`, `C(n,ε)` or `D(n,θ,ε)`,
with the excluded values of `ε` of Column III of Higman's table.

The bijection `e : P ≃ (𝔽_{2ⁿ} × 𝔽_{2ⁿ}) × 𝔽_{2ⁿ}` exhibits `P` as a two-step extension of
`𝔽_{2ⁿ}` (`= Z(P)`) by `𝔽_{2ⁿ} × 𝔽_{2ⁿ}` (`= P/Z(P)`); the three disjuncts are the three
laws of Column V. -/
theorem type_B_C_D_classification {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3) :
    ∃ (n : ℕ)
      (e : P ≃ (GaloisField 2 n × GaloisField 2 n) × GaloisField 2 n)
      (θ : GaloisField 2 n ≃+* GaloisField 2 n) (ε : GaloisField 2 n),
      Nat.card ↥(Subgroup.center P) = 2 ^ n ∧ Odd (orderOf θ) ∧
      ((ε ≠ 0 ∧ (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ) ∧
          ∀ x y : P, e (x * y) = ((e x).1 + (e y).1,
            (e x).2 + (e y).2 +
              Work.Higman.bCocycle (GaloisField 2 n) θ ε (e x).1 (e y).1))
        ∨ ((∀ a : GaloisField 2 n, (θ (θ a)) ^ 2 = a) ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ) ∧
            ∀ x y : P, e (x * y) = ((e x).1 + (e y).1,
              (e x).2 + (e y).2 +
                Work.Higman.cCocycle (GaloisField 2 n) θ ε (e x).1 (e y).1))
        ∨ (θ ^ 5 = 1 ∧ θ ≠ RingEquiv.refl _ ∧ 5 ∣ n ∧
            (∀ ρ : GaloisField 2 n, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹) ∧
            ∀ x y : P, e (x * y) = ((e x).1 + (e y).1,
              (e x).2 + (e y).2 +
                Work.Higman.dCocycle (GaloisField 2 n) θ ε (e x).1 (e y).1))) := by
  -- structural facts about Suzuki 2-groups
  have hZ : Subgroup.center P = omega1 P := center_eq_omega1_new h
  have hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P :=
    sq_mem_center_of_card_eq_center_cube h hcard
  have hexp : ∀ z : P, z ∈ Subgroup.center P → z ^ 2 = 1 :=
    fun z hz => h.mem_omega1.mp (hZ ▸ hz)
  -- the two-step model
  obtain ⟨m⟩ := nonempty_twoStepModel hsq hexp
  letI : AddCommGroup m.V := m.addCommGroup_V
  letI : AddExpTwo m.V := m.addExpTwo_V
  letI : AddCommGroup m.W := m.addCommGroup_W
  letI : AddExpTwo m.W := m.addExpTwo_W
  letI : Biadd m.b := m.biadd_b
  haveI hfinV : Finite m.V := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [m.card_V]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  haveI hfinW : Finite m.W := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [m.card_W]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  -- the automorphism transported along the model
  let ξ : MulAut (TwoStep m.V m.W m.b) := m.iso.symm.trans (h.xi.trans m.iso)
  have hξpow : ∀ (k : ℕ) (x : TwoStep m.V m.W m.b),
      (ξ ^ k) x = m.iso ((h.xi ^ k) (m.iso.symm x)) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
        intro x
        have h1 : ξ x = m.iso (h.xi (m.iso.symm x)) := by
          simp [ξ, MulEquiv.trans_apply]
        rw [pow_succ, MulAut.mul_apply, h1, ih, MulEquiv.symm_apply_apply, pow_succ,
          MulAut.mul_apply]
  have htrans : ∀ x y : TwoStep m.V m.W m.b, orderOf x = 2 → orderOf y = 2 →
      ∃ k : ℕ, (ξ ^ k) x = y := by
    intro x y hx hy
    have hx' : orderOf (m.iso.symm x) = 2 := by rw [MulEquiv.orderOf_eq, hx]
    have hy' : orderOf (m.iso.symm y) = 2 := by rw [MulEquiv.orderOf_eq, hy]
    obtain ⟨k, hk⟩ := h.trans (m.iso.symm x) (m.iso.symm y) hx' hy'
    exact ⟨k, by rw [hξpow k x, hk, MulEquiv.apply_symm_apply]⟩
  -- every involution of the model is central (it comes from an involution of `P`)
  have hinvol : ∀ x : TwoStep m.V m.W m.b, x ^ 2 = 1 →
      x ∈ Subgroup.center (TwoStep m.V m.W m.b) := by
    intro x hx
    have hxP : (m.iso.symm x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
    have hmem : m.iso.symm x ∈ Subgroup.center P := by
      rcases eq_or_ne (m.iso.symm x) 1 with hone | hne
      · rw [hone]; exact Subgroup.one_mem _
      · refine h.invol_mem_center ?_
        have hd : orderOf (m.iso.symm x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hxP
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
        · exact absurd (orderOf_eq_one_iff.mp h1) hne
        · exact h2
    rw [← Subgroup.map_center_eq (m.iso), Subgroup.mem_map]
    exact ⟨m.iso.symm x, by simpa using hmem, by simp⟩
  -- the centre of the model is `kerFst`: both have `|W|` elements
  have hcenter : Subgroup.center (TwoStep m.V m.W m.b) = TwoStep.kerFst := by
    refine (Subgroup.eq_of_le_of_card_ge (H := TwoStep.kerFst (A := m.V) (Z := m.W) (b := m.b))
      (K := Subgroup.center (TwoStep m.V m.W m.b)) TwoStep.kerFst_le_center ?_).symm
    have hWc : Nat.card m.W = Nat.card ↥(TwoStep.kerFst (A := m.V) (Z := m.W) (b := m.b)) :=
      TwoStep.card_kerFst.symm
    have hCc : Nat.card ↥(Subgroup.center (TwoStep m.V m.W m.b)) =
        Nat.card ↥(Subgroup.center P) := by
      rw [← Subgroup.map_center_eq (m.iso)]
      exact Nat.card_congr
        ((Subgroup.equivMapOfInjective (Subgroup.center P) (m.iso : P →* TwoStep m.V m.W m.b)
          m.iso.injective).symm.toEquiv)
    rw [← hWc, m.card_W, hCc]
  -- `|V| = |P / Z(P)| = |W| ^ 2`
  have hcardV : Nat.card m.V = Nat.card m.W ^ 2 := by
    have h1 : Nat.card P = Nat.card m.V * Nat.card m.W := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P), ← m.card_V,
        ← m.card_W]
    have h2 : Nat.card m.V * Nat.card m.W = Nat.card m.W ^ 2 * Nat.card m.W := by
      rw [← h1, hcard, ← m.card_W]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos_iff.mpr ⟨⟨0⟩, hfinW⟩) h2
  have hW4 : 4 ≤ Nat.card m.W := by
    rw [m.card_W, hZ]
    exact h.omega1_card_ge_four
  -- Higman's Lemma 12 in the two-step form
  obtain ⟨n, φ, ψ, θ, ε, c, hW2n, hodd, hcase⟩ :=
    cocycle_normal_form_aux hcardV hW4 hinvol hcenter ξ htrans
  -- the assembled bijection, using the coboundary `c` to match the model's section
  let e : P ≃ (GaloisField 2 n × GaloisField 2 n) × GaloisField 2 n :=
    { toFun := fun x => (φ (m.iso x).fst, ψ (m.iso x).snd + c (φ (m.iso x).fst))
      invFun := fun y => m.iso.symm ⟨φ.symm y.1, ψ.symm (y.2 + c y.1)⟩
      left_inv := by
        intro x
        have hcc : (ψ (m.iso x).snd + c (φ (m.iso x).fst)) + c (φ (m.iso x).fst) =
            ψ (m.iso x).snd := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        have harg : (⟨φ.symm (φ (m.iso x).fst),
            ψ.symm (ψ (m.iso x).snd + c (φ (m.iso x).fst) + c (φ (m.iso x).fst))⟩ :
              TwoStep m.V m.W m.b) = m.iso x := by
          rw [hcc, φ.symm_apply_apply, ψ.symm_apply_apply]
        dsimp only
        rw [harg, MulEquiv.symm_apply_apply]
      right_inv := by
        intro y
        have hcc : y.2 + c y.1 + c y.1 = y.2 := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        have harg : m.iso (m.iso.symm (⟨φ.symm y.1, ψ.symm (y.2 + c y.1)⟩ :
              TwoStep m.V m.W m.b)) = ⟨φ.symm y.1, ψ.symm (y.2 + c y.1)⟩ :=
          MulEquiv.apply_symm_apply m.iso _
        dsimp only
        rw [harg]
        dsimp only
        rw [φ.apply_symm_apply, ψ.apply_symm_apply, hcc] }
  have hfst_e : ∀ x : P, (e x).1 = φ (m.iso x).fst := fun x => rfl
  have hsnd_e : ∀ x : P, (e x).2 = ψ (m.iso x).snd + c (φ (m.iso x).fst) := fun x => rfl
  -- the multiplication law, from the cocycle identity
  have hlaw_of : ∀ (b₀ : (GaloisField 2 n × GaloisField 2 n) →
        (GaloisField 2 n × GaloisField 2 n) → GaloisField 2 n),
      (∀ u v : m.V, ψ (m.b u v) =
        b₀ (φ u) (φ v) + (c (φ u) + c (φ v) + c (φ u + φ v))) →
      ∀ x y : P, e (x * y) = ((e x).1 + (e y).1,
        (e x).2 + (e y).2 + b₀ (e x).1 (e y).1) := by
    intro b₀ hb x y
    have hfst : (m.iso (x * y)).fst = (m.iso x).fst + (m.iso y).fst := by
      rw [map_mul, TwoStep.fst_mul]
    have hsnd : (m.iso (x * y)).snd =
        (m.iso x).snd + (m.iso y).snd + m.b (m.iso x).fst (m.iso y).fst := by
      rw [map_mul, TwoStep.snd_mul]
    apply Prod.ext
    · rw [hfst_e (x * y), hfst_e x, hfst_e y, hfst, map_add]
    · simp only [hsnd_e, hfst_e, hsnd, hfst, map_add]
      rw [hb]
      ring_nf
      rw [mul_two, CharTwo.add_self_eq_zero, add_zero]
  refine ⟨n, e, θ, ε, ?_, hodd, ?_⟩
  · rw [← m.card_W]; exact hW2n
  · rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5⟩
    · exact Or.inl ⟨h1, h2, hlaw_of _ h3⟩
    · exact Or.inr (Or.inl ⟨h1, h2, hlaw_of _ h3⟩)
    · exact Or.inr (Or.inr ⟨h1, h2, h3, h4, hlaw_of _ h5⟩)

end Work.Higman
