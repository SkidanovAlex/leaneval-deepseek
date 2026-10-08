import Mathlib
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.SzTildeDefs
import Submission.Work.ZassenhausSuzuki.szTilde_sq
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausSuzuki.DtwoPoint_regular_on_involutions
import Submission.Work.ZassenhausSuzuki.DtwoPoint_sq_injective
import Submission.Work.ZassenhausSuzuki.SzAField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The maps `z ↦ ∼ z` and `z ↦ μ_z` on the central involutions of the root group

This module collects the elementary injectivity facts about the Suzuki reflection `∼` and the
Moufang involution `μ_z = t · h z` on the set `Z(Q)^#` of non-trivial central involutions of the
root group, together with the centrality of the Baumeister–Grüninger element
`c = (∼a)·(∼b)·(∼(ab))⁻¹`.

They are the bookkeeping inputs of BG Lemma 3.3 and of the 5.14 computation (the step
`μ_c = μ_d ⟹ c = d`), and are used by both the reflection-theoretic (BG) and the
character-theoretic routes to `Work.ZassenhausSuzuki.szClassNumber_fixTheta`.

* `center_mul_self_eq_one` — every central element of `Q` is an involution (Suzuki case);
* `szTilde_injOn_center` — `z ↦ ∼ z` is injective on `Z(Q)^#` (immediate from the square rule
  `(∼ z)² = z`, `szTilde_sq` = BG 5.7);
* `mu_injOn_center` — `z ↦ μ_z = t · h z` is injective on `Z(Q)^#` (BG 3.3 for central
  involutions): any two central involutions are `D`-conjugate
  (`DtwoPoint_regular_on_involutions`), and `h(d z d⁻¹) = d⁻² h(z)` (`canon_H6` = HB III XI
  11.10 b) (4)) together with `d² = 1 ⟹ d = 1` (`DtwoPoint_sq_injective`) forces `d = 1`;
* `cruxElem_mem_center` — if `B, C ∈ Q` commute, `B² = a`, `C² = b`, `D² = a·b`, then
  `B·C·D⁻¹ ∈ Z(Q)` (`SzAField.szA_sq_eq_imp_mul_inv_mem_center`): the centrality of BG 5.13's
  element `c`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- A central element of `Q` is non-trivial as an element of `G` iff it is non-trivial in `Q`. -/
theorem center_coe_ne_one {a : Q} (ha : a ≠ 1) : (a : G) ≠ 1 := fun h =>
  ha (Subtype.ext h)

/-- **A central element of the root group is an involution** in the Suzuki case: the centre of
`Q ≃* A(K,θ)` is `{⟨0,b⟩}`, and `⟨0,b⟩² = 1`. -/
theorem center_mul_self_eq_one {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ} {a : Q}
    (ha : a ∈ Subgroup.center Q) : a * a = 1 := by
  rw [mem_center_iff_map e] at ha
  have ha' : (e a).a = 0 := (SzA.mem_center_iff θ hθ1 (e a)).mp ha
  apply e.injective
  rw [map_mul, map_one]
  rw [show e a = (⟨0, (e a).b⟩ : SzA (GaloisField 2 m) θ) from SzA.ext ha' rfl]
  ext <;> simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]

/-- **`∼` is injective on `Z(Q)^#`** (BG 5.7: `(∼ z)² = z`). -/
theorem szTilde_injOn_center (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {a b : Q} (hacen : a ∈ Subgroup.center Q) (hbcen : b ∈ Subgroup.center Q)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (h : szTilde hsplit a = szTilde hsplit b) : a = b := by
  have haa : (e a).a = 0 :=
    (SzA.mem_center_iff θ hθ1 (e a)).mp ((mem_center_iff_map e).mp hacen)
  have hbb : (e b).a = 0 :=
    (SzA.mem_center_iff θ hθ1 (e b)).mp ((mem_center_iff_map e).mp hbcen)
  have hae1 : e a ≠ 1 := fun hc => ha1 (e.injective (by rw [hc, map_one]))
  have hbe1 : e b ≠ 1 := fun hc => hb1 (e.injective (by rw [hc, map_one]))
  have hsa := szTilde_sq hsplit hzass hθ1 hθodd htorus haa hae1
  have hsb := szTilde_sq hsplit hzass hθ1 hθodd htorus hbb hbe1
  rw [h] at hsa
  rw [hsb] at hsa
  exact hsa.symm

/-- **`z ↦ μ_z = t · h z` is injective on `Z(Q)^#`** (BG 3.3 for central involutions).

Any two central involutions `a, b` of `Q` are conjugate by an element `d ∈ D`
(`DtwoPoint_regular_on_involutions`), and `h(d z d⁻¹) = d⁻² h(z)` (`canon_H6`); so
`h a = h b = d⁻² h a` forces `d² = 1`, hence `d = 1` (`DtwoPoint_sq_injective`), hence `a = b`. -/
theorem mu_injOn_center (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {a b : Q}
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (h : t * hG C a = t * hG C b) : a = b := by
  have haG1 : (a : G) ≠ 1 := center_coe_ne_one ha1
  have hhab : hG C a = hG C b := mul_left_cancel h
  obtain ⟨d, hdp, -⟩ :=
    DtwoPoint_regular_on_involutions hsplit hzass h2 ha1 ha2 hb1 hb2
  have hdconj : (d : G) * (a : G) * (d : G)⁻¹ = (b : G) := hdp
  have hdQ : (d : G) * (a : G) * (d : G)⁻¹ ∈ Q := canon_D_conj_Q_mem hsplit d a
  have hH6 := canon_H6 hsplit hzass h2 C d a haG1 hdQ
  have hdEq : (⟨(d : G) * (a : G) * (d : G)⁻¹, hdQ⟩ : Q) = b := Subtype.ext hdconj
  rw [hdEq] at hH6
  have hkey : hG C a = (d : G)⁻¹ * (d : G)⁻¹ * hG C a := by
    conv_lhs => rw [hhab]
    exact hH6
  have hdd : (d : G)⁻¹ * (d : G)⁻¹ = 1 := by
    have h1 : ((d : G)⁻¹ * (d : G)⁻¹ * hG C a) * (hG C a)⁻¹ = hG C a * (hG C a)⁻¹ := by
      rw [← hkey]
    simpa [mul_assoc] using h1
  have hd2 : d * d = 1 := by
    have h2'' : (d : G) * (d : G) = 1 := by
      have := congrArg Inv.inv hdd
      simpa [mul_inv_rev, inv_inv] using this
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    exact h2''
  have hd1 : d = 1 := DtwoPoint_sq_injective hsplit hzass h2 (e' := 1) (by rw [hd2, one_mul])
  rw [hd1, Subgroup.coe_one, one_mul, inv_one, mul_one] at hdconj
  exact Subtype.ext hdconj

/-- **The BG 5.13/5.14 central element.**  If `B, C ∈ Q` commute, `B² = a`, `C² = b` and
`D² = a·b`, then `B·C·D⁻¹ ∈ Z(Q)`: `B·C` also has square `a·b`, so two elements of `Q` with the
same square differ by a central element (`SzAField.szA_sq_eq_imp_mul_inv_mem_center`). -/
theorem cruxElem_mem_center
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθodd : Odd (orderOf θ))
    (e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)
    {B C D : Q} (hcomm : B * C = C * B) {a b : Q}
    (hB : B * B = a) (hC : C * C = b) (hD : D * D = a * b) :
    B * C * D⁻¹ ∈ Subgroup.center Q := by
  have hsq : (B * C) * (B * C) = D * D := by
    have h1 : (B * C) * (B * C) = (B * B) * (C * C) := by
      calc (B * C) * (B * C) = B * (C * B) * C := by group
        _ = B * (B * C) * C := by rw [hcomm]
        _ = (B * B) * (C * C) := by group
    rw [h1, hB, hC, ← hD]
  have hmem : e (B * C) * (e D)⁻¹ ∈ Subgroup.center (SzA (GaloisField 2 m) θ) :=
    szA_sq_eq_imp_mul_inv_mem_center θ hθodd (x := e (B * C)) (y := e D)
      (by rw [← map_mul, hsq, map_mul])
  rw [mem_center_iff_map e]
  have hkey : e (B * C * D⁻¹) = e (B * C) * (e D)⁻¹ := by rw [map_mul, map_inv]
  rw [hkey]
  exact hmem

/-- **BG 5.13, first half (equivalently the usable form of BG 5.10).**  For two *distinct*
non-trivial central involutions `a, b` of `Q`, the element `(∼ a)⁻¹ · (∼ b)` is **not** central.

The proof is the one-line argument of the source: `z ↦ z²` is constant on `Z(Q)`-cosets
(`z ∈ Z(Q) ⟹ z² = 1`, `center_mul_self_eq_one`), and `(∼ x)² = x` (`szTilde_sq` = BG 5.7)
identifies the coset `(∼ x)·Z(Q)` with the squaring map; so `(∼ a)⁻¹(∼ b) ∈ Z(Q)` forces
`a = (∼ a)² = (∼ b)² = b`. -/
theorem szTilde_mul_notMem_center (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {a b : Q} (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b)
    (hacen : a ∈ Subgroup.center Q) (hbcen : b ∈ Subgroup.center Q) :
    (szTilde hsplit a)⁻¹ * (szTilde hsplit b) ∉ Subgroup.center Q := by
  intro hmem
  have haa : (e a).a = 0 :=
    (SzA.mem_center_iff θ hθ1 (e a)).mp ((mem_center_iff_map e).mp hacen)
  have hbb : (e b).a = 0 :=
    (SzA.mem_center_iff θ hθ1 (e b)).mp ((mem_center_iff_map e).mp hbcen)
  have hae1 : e a ≠ 1 := fun hc => ha1 (e.injective (by rw [hc, map_one]))
  have hbe1 : e b ≠ 1 := fun hc => hb1 (e.injective (by rw [hc, map_one]))
  have hsa := szTilde_sq hsplit hzass hθ1 hθodd htorus haa hae1
  have hsb := szTilde_sq hsplit hzass hθ1 hθodd htorus hbb hbe1
  set z : Q := (szTilde hsplit a)⁻¹ * (szTilde hsplit b) with hz
  have hzmem : z ∈ Subgroup.center Q := by rw [hz]; exact hmem
  have hz2 : z * z = 1 := center_mul_self_eq_one (e := e) hθ1 hzmem
  have hcz : ∀ w : Q, w * z = z * w := fun w => Subgroup.mem_center_iff.mp hzmem w
  have hzb : szTilde hsplit b = szTilde hsplit a * z := by rw [hz]; group
  have hsq : (szTilde hsplit b) * (szTilde hsplit b) = a := by
    calc (szTilde hsplit b) * (szTilde hsplit b)
        = (szTilde hsplit a * z) * (szTilde hsplit a * z) := by rw [hzb]
      _ = szTilde hsplit a * ((z * szTilde hsplit a) * z) := by group
      _ = szTilde hsplit a * (szTilde hsplit a * (z * z)) := by
            rw [← hcz (szTilde hsplit a)]; group
      _ = (szTilde hsplit a * szTilde hsplit a) * (z * z) := by group
      _ = a := by rw [hsa, hz2, mul_one]
  exact hne (hsq.symm.trans hsb)

end Work.ZassenhausSuzuki
