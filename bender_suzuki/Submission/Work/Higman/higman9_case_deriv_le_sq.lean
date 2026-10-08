/-
Copyright (c) 2024. All rights reserved.

# Higman (1963), Lemma 7, in the `Φ(C) = A`, `C' ≤ A²` case

Higman, *Suzuki 2-groups*, Illinois J. Math. 7 (1963), 79--96, Lemma 7 (p. 86):

> If `A` is a normal abelian `ξ`-subgroup of `G`, and `C` a normal `ξ`-subgroup which covers
> `A`, and if `A = Φ(C)` (that is `powSub C 2 ⊔ ⁅C,C⁆ = A`) but `C' ≤ A²`, then `C` is abelian.

The argument is the Gorenstein--Thompson step: the squaring map `Φ₂ : C → A ⊓ Ω₁`, `x ↦ x^(2^e)`
(with `2^e` the exponent of `A`) is a `ξ`-equivariant surjection with kernel `A`, and the
commutator pairing `⁅·,·⁆` transported through it gives a non-zero alternating `ξ`-equivariant
biadditive map on `A ⊓ Ω₁ = A^(2^(e-1))`, on which `ξ` is transitive on the non-identity
elements.  Gorenstein--Thompson (`equivariant_bihom_trivial`) forces that pairing to vanish,
whence `C' = (C')²`, and `C' = ⊥` since `C'` has exponent dividing `2^e`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.equivariant_bihom_trivial
import Submission.Work.Higman.higman_lemma7_comm_le
import Submission.Work.Higman.higman_lemma7_phi2
import Submission.Work.Higman.higman_lemma7_psi
import Submission.Work.Higman.card_T_eq_pow
import Submission.Work.Higman.pow_range_eq_torsion

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- Restriction of a `MulAut` of `P` to a subgroup that it preserves. -/
def hg9SubMulAut (φ : MulAut P) (T : Subgroup P) (hT : T.map φ.toMonoidHom = T) : MulAut ↥T where
  toFun t := ⟨φ (t : P), by
    have h := Subgroup.mem_map_of_mem φ.toMonoidHom t.2
    rwa [hT] at h⟩
  invFun t := ⟨φ.symm (t : P), symm_mem_of_map_eq φ hT t.2⟩
  left_inv t := Subtype.ext (by simp)
  right_inv t := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp)

@[simp] theorem hg9SubMulAut_apply (φ : MulAut P) (T : Subgroup P)
    (hT : T.map φ.toMonoidHom = T) (t : ↥T) :
    ((hg9SubMulAut φ T hT t : ↥T) : P) = φ (t : P) := rfl

theorem hg9SubMulAut_pow_apply (φ : MulAut P) (T : Subgroup P)
    (hT : T.map φ.toMonoidHom = T) (k : ℕ) (t : ↥T) :
    (((hg9SubMulAut φ T hT) ^ k) t : P) = (φ ^ k) (t : P) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', MulAut.mul_apply]
      show φ ((((hg9SubMulAut φ T hT) ^ k) t : ↥T) : P) = (φ ^ (k + 1)) (t : P)
      rw [ih, ← MulAut.mul_apply, ← pow_succ']

/-- **Higman 1963, Lemma 7.**  Let `A` be a normal abelian `ξ`-subgroup of a Suzuki 2-group `P`
and let `C` be a normal `ξ`-subgroup covering `A` (i.e. `C/A` is a minimal normal `ξ`-section:
there is no `ξ`-invariant normal `D` with `A ≤ D ≤ C` other than `A` and `C`).  If
`A = Φ(C)` (that is `powSub C 2 ⊔ ⁅C,C⁆ = A`) but `C' ≤ A²`, then `C` is abelian. -/
theorem higman9_case_deriv_le_sq {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A)
    (hCd : ⁅C, C⁆ ≤ Work.Higman.powSub A 2) :
    ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
  classical
  suffices hDbot : ⁅C, C⁆ = ⊥ by
    intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hDbot] at hmem
    exact (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp hmem)).eq
  by_contra hDne
  have hDleA : ⁅C, C⁆ ≤ A := by rw [← hPhi]; exact le_sup_right
  have hDvN : (⁅C, C⁆).Normal := Subgroup.commutator_normal C C
  have hAne : A ≠ ⊥ := fun hbot => hDne (le_bot_iff.mp (hDleA.trans (le_of_eq hbot)))
  -- exponent data for `A`
  obtain ⟨e, he1, he2, hcard⟩ := higman_lemma1 h hA.abelian hA.map_eq
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with he0 | hpos
    · exfalso
      have hbot : A = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro a ha
        have hh := he1 a ha
        simpa [he0] using hh
      exact hAne hbot
    · exact hpos
  -- the subgroup `W = A ∩ Ω₁`
  set W : Subgroup P := A ⊓ Work.Higman.omega1 P with hWdef
  have hWle : W ≤ A := inf_le_left
  have hWmem : ∀ x ∈ A, x ^ 2 = 1 ↔ x ∈ W := by
    intro x hx
    rw [hWdef, Subgroup.mem_inf]
    exact ⟨fun h2 => ⟨hx, h.mem_omega1.mpr h2⟩, fun hh => h.mem_omega1.mp hh.2⟩
  obtain ⟨hcard_pow, hker⟩ := powSub_chain_card W hA.abelian hWle hWmem e he1 hcard
  have hWinv : W.map (h.xi : MulAut P).toMonoidHom = W := by
    rw [hWdef, Subgroup.map_inf _ _ _ (h.xi : MulAut P).injective, hA.map_eq, map_xi_omega1 h]
  have hirr : ∀ T : Subgroup P, T ≤ W → T.map (h.xi : MulAut P).toMonoidHom = T →
      T = ⊥ ∨ T = W := by
    intro T hT hTinv
    have hT' : T ≤ A ⊓ Work.Higman.omega1 P := by rw [← hWdef]; exact hT
    have hgoal := invariant_subgroup_inf_omega1 h A hT' hTinv
    rwa [hWdef]
  have hDinv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator C C (h.xi : MulAut P).toMonoidHom, hCinv]
  obtain ⟨s, hDs⟩ :=
    invariant_subgroup_eq_powSub (φ := h.xi) (W := W) hWinv e A hA.abelian hWmem hirr he1 hcard
      hker ⁅C, C⁆ hDleA hDinv
  have hse : s ≤ e - 1 := by
    by_contra hcon
    push_neg at hcon
    have hes : e ≤ s := by omega
    exact hDne (by rw [hDs, powSub_eq_bot_of_exp hA.abelian hes he1])
  have hs : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with hs0 | hpos
    · exfalso
      have hAD : A = ⁅C, C⁆ := by rw [hDs, hs0, pow_zero, powSub_one_eq]
      have hAle : A ≤ Work.Higman.powSub A 2 := hAD.symm ▸ hCd
      have hA2 : A = Work.Higman.powSub A 2 :=
        le_antisymm hAle (powSub_le (by norm_num))
      have hpow : ∀ k : ℕ, Work.Higman.powSub A (2 ^ k) = A := by
        intro k
        induction k with
        | zero => rw [pow_zero, powSub_one_eq]
        | succ k ih =>
            rw [pow_succ, ← powSub_powSub hA.abelian (2 ^ k) 2, ih]
            exact hA2.symm
      exact hAne (by rw [← hpow e, powSub_eq_bot_of_exp hA.abelian le_rfl he1])
    · exact hpos
  -- ## the auxiliary inputs (Higman's squaring map and its applications)
  have hkeyk : ∀ k ≤ e, ∀ y ∈ A, y ∈ Work.Higman.powSub A (2 ^ k) ↔ y ^ 2 ^ (e - k) = 1 := by
    letI : CommGroup ↥A := { (inferInstance : Group ↥A) with
      mul_comm := fun x y => Subtype.ext (hA.abelian x x.2 y y.2) }
    have hexp' : ∀ a : ↥A, a ^ 2 ^ e = 1 := fun a => Subtype.ext (by simpa using he1 a a.2)
    have hcard' : Nat.card ↥A = (Nat.card {x : ↥A | x ^ 2 = 1}) ^ e := by
      rw [card_twoTorsion_eq_card_inf_omega1 h A]
      exact hcard
    have hT : ∀ j ≤ e, Nat.card {x : ↥A | x ^ 2 ^ j = 1}
        = (Nat.card {x : ↥A | x ^ 2 = 1}) ^ j :=
      card_T_eq_pow (A := ↥A) hexp' hcard'
    have hkey' : ∀ k ≤ e, ∀ y : ↥A, (∃ x : ↥A, x ^ 2 ^ k = y) ↔ y ^ 2 ^ (e - k) = 1 :=
      pow_range_eq_torsion (A := ↥A) hexp' hT hcard'
    intro k hk y hy
    have hk' := hkey' k hk (⟨y, hy⟩ : ↥A)
    rw [mem_powSub_iff hA.abelian]
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxy' : (⟨x, hx⟩ : ↥A) ^ 2 ^ k = (⟨y, hy⟩ : ↥A) := Subtype.ext (by simpa using hxy)
      have h := hk'.mp ⟨⟨x, hx⟩, hxy'⟩
      exact congrArg (Subtype.val : ↥A → P) h
    · intro hy1
      have hy1' : (⟨y, hy⟩ : ↥A) ^ 2 ^ (e - k) = 1 := Subtype.ext (by simpa using hy1)
      obtain ⟨x, hx⟩ := hk'.mpr hy1'
      exact ⟨x.1, x.2, by
        have := congrArg (Subtype.val : ↥A → P) hx
        simpa using this⟩
  have hkey : ∀ y ∈ A, y ∈ Work.Higman.powSub A 2 ↔ y ^ 2 ^ (e - 1) = 1 :=
    fun y hy => hkeyk 1 he y hy
  have hcomm : ⁅A, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 ∧
      ⁅⁅C, C⁆, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 :=
    higman_lemma7_comm_le h hA hCn hAC hPhi hCd hs hse he1 hDs
  obtain ⟨hcommAC, hcommDC⟩ := hcomm
  have hphi2 : (∀ x ∈ C, ∀ y ∈ C, (x * y) ^ 2 ^ e = x ^ 2 ^ e * y ^ 2 ^ e) ∧
      (∀ x ∈ C, x ^ 2 ^ e ∈ A ⊓ Work.Higman.omega1 P) ∧
      (∀ w ∈ A ⊓ Work.Higman.omega1 P, ∃ x ∈ C, x ^ 2 ^ e = w) ∧
      (∀ x ∈ C, x ^ 2 ^ e = 1 ↔ x ∈ A) ∧
      (∀ x ∈ C, (h.xi x) ^ 2 ^ e = h.xi (x ^ 2 ^ e)) :=
    higman_lemma7_phi2 h hA hCn hCinv hAC hCA hcover hPhi hCd hAne he he1 hkey hker
  obtain ⟨hphi2_mul, hphi2_mem, hphi2_surj, hphi2_ker, hphi2_xi⟩ := hphi2
  have hpsi : (∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) ∈ A ⊓ Work.Higman.omega1 P) ∧
      (∀ u ∈ ⁅C, C⁆, ∀ v ∈ ⁅C, C⁆,
        (u * v) ^ 2 ^ (e - 1 - s) = u ^ 2 ^ (e - 1 - s) * v ^ 2 ^ (e - 1 - s)) ∧
      (∀ v ∈ ⁅C, C⁆, v ^ 2 ^ (e - 1 - s) = 1 ↔ v ∈ Work.Higman.powSub ⁅C, C⁆ 2) ∧
      (∀ v ∈ ⁅C, C⁆, h.xi (v ^ 2 ^ (e - 1 - s)) = (h.xi v) ^ 2 ^ (e - 1 - s)) :=
    higman_lemma7_psi h hA hse hkeyk hker hDs
  obtain ⟨hpsi_mem, hpsi_mul, hpsi_ker, hpsi_xi⟩ := hpsi
  -- ## `W` is elementary abelian, and `ξ` acts transitively on `W \ {1}`
  letI hWcomm : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with
      mul_comm := fun u v => Subtype.ext
        (h.omega1_comm (Subgroup.mem_inf.mp (show (u:P) ∈ A ⊓ Work.Higman.omega1 P from u.2)).2
                       (Subgroup.mem_inf.mp (show (v:P) ∈ A ⊓ Work.Higman.omega1 P from v.2)).2) }
  have hWtwo : ∀ a : ↥W, a * a = 1 := by
    intro a
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two,
      h.mem_omega1.mp (Subgroup.mem_inf.mp (show (a:P) ∈ A ⊓ Work.Higman.omega1 P from a.2)).2]
  let ξW : MulAut ↥W := hg9SubMulAut (h.xi : MulAut P) W hWinv
  have hξW_pow : ∀ (k : ℕ) (w : ↥W), (((ξW ^ k) w : ↥W) : P) = (h.xi ^ k) (w : P) :=
    hg9SubMulAut_pow_apply (h.xi : MulAut P) W hWinv
  have htransW : ∀ a b : ↥W, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b := by
    intro a b ha hb
    have ha2 : orderOf (a:P) = 2 := by
      have h2 : (a:P) ^ 2 = 1 := by
        have hh := congrArg (fun t : ↥W => (t:P)) (hWtwo a)
        simpa [pow_two] using hh
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) (fun hc => ha (Subtype.ext hc))
      · exact h1
    have hb2 : orderOf (b:P) = 2 := by
      have h2 : (b:P) ^ 2 = 1 := by
        have hh := congrArg (fun t : ↥W => (t:P)) (hWtwo b)
        simpa [pow_two] using hh
      rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_iff_pow_eq_one.mpr h2) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) (fun hc => hb (Subtype.ext hc))
      · exact h1
    obtain ⟨k, hk⟩ := h.trans (a:P) (b:P) ha2 hb2
    exact ⟨k, Subtype.ext (by rw [hξW_pow]; exact hk)⟩
  -- ## the map `Φ₂ : C → W`, `x ↦ x ^ 2 ^ e`
  let Φ2 : ↥C →* ↥W :=
    { toFun := fun x => ⟨(x : P) ^ 2 ^ e, hphi2_mem (x : P) x.2⟩
      map_one' := Subtype.ext (by show ((1:↥C):P) ^ 2 ^ e = 1; simp)
      map_mul' := fun x y => Subtype.ext (by
        show ((x * y : ↥C) : P) ^ 2 ^ e = ((x:P) ^ 2 ^ e) * ((y:P) ^ 2 ^ e)
        rw [Subgroup.coe_mul]
        exact hphi2_mul (x:P) x.2 (y:P) y.2) }
  have hkerΦ2 : ∀ x : ↥C, Φ2 x = 1 ↔ (x : P) ∈ A := by
    intro x
    have h4 := hphi2_ker (x:P) x.2
    constructor
    · intro hx
      have h := congrArg (fun t : ↥W => (t:P)) hx
      simp only [Subgroup.coe_one] at h
      exact h4.mp h
    · intro hx
      refine Subtype.ext ?_
      show (x:P) ^ 2 ^ e = 1
      exact h4.mpr hx
  have hsurjΦ2 : ∀ w : ↥W, ∃ x : ↥C, Φ2 x = w := by
    intro w
    obtain ⟨x, hxC, hxw⟩ :=
      hphi2_surj (w:P) (show (w:P) ∈ A ⊓ Work.Higman.omega1 P from w.2)
    exact ⟨⟨x, hxC⟩, Subtype.ext hxw⟩
  let lift : ↥W → ↥C := fun w => Classical.choose (hsurjΦ2 w)
  have lift_spec : ∀ w : ↥W, Φ2 (lift w) = w := fun w => Classical.choose_spec (hsurjΦ2 w)
  have lift_val : ∀ w : ↥W, ((lift w : ↥C) : P) ^ 2 ^ e = (w:P) :=
    fun w => congrArg (fun t : ↥W => (t:P)) (lift_spec w)
  let Ψ : ↥(⁅C, C⁆) →* ↥W :=
    { toFun := fun v => ⟨(v : P) ^ 2 ^ (e - 1 - s), hpsi_mem (v : P) v.2⟩
      map_one' := Subtype.ext (by show ((1:↥(⁅C,C⁆)):P) ^ 2 ^ (e-1-s) = 1; simp)
      map_mul' := fun u v => Subtype.ext (by
        show ((u * v : ↥(⁅C, C⁆)) : P) ^ 2 ^ (e - 1 - s)
          = ((u:P) ^ 2 ^ (e - 1 - s)) * ((v:P) ^ 2 ^ (e - 1 - s))
        rw [Subgroup.coe_mul]
        exact hpsi_mul (u:P) u.2 (v:P) v.2) }
  have hΨker : ∀ v : ↥(⁅C, C⁆), Ψ v = 1 ↔ (v : P) ∈ Work.Higman.powSub ⁅C, C⁆ 2 := by
    intro v
    have h := hpsi_ker (v:P) v.2
    constructor
    · intro hv
      have hh := congrArg (fun t : ↥W => (t:P)) hv
      simp only [Subgroup.coe_one] at hh
      exact h.mp hh
    · intro hv
      refine Subtype.ext ?_
      show (v:P) ^ 2 ^ (e - 1 - s) = 1
      exact h.mpr hv
  have hPsi_xi : ∀ v : ↥(⁅C, C⁆),
      Ψ ⟨h.xi (v:P), by
          have hh := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom v.2
          rwa [Subgroup.map_commutator C C (h.xi : MulAut P).toMonoidHom, hCinv] at hh⟩
        = ξW (Ψ v) := by
    intro v
    refine Subtype.ext ?_
    show (h.xi (v:P)) ^ 2 ^ (e - 1 - s) = h.xi ((v:P) ^ 2 ^ (e - 1 - s))
    exact (hpsi_xi (v:P) v.2).symm
  have hΨconj : ∀ (g : P) (hg : g ∈ C) (d : ↥(⁅C, C⁆)),
      Ψ ⟨g * (d:P) * g⁻¹, hDvN.conj_mem (d:P) d.2 g⟩ = Ψ d := by
    intro g hg d
    have hcd : ⁅g, (d:P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator hg (hAC (hDleA d.2))
    have helem : (⟨g * (d:P) * g⁻¹, hDvN.conj_mem (d:P) d.2 g⟩ : ↥(⁅C, C⁆))
        = ⟨⁅g, (d:P)⁆, hcd⟩ * ⟨(d:P), d.2⟩ := by
      refine Subtype.ext ?_
      show g * (d:P) * g⁻¹ = ⁅g, (d:P)⁆ * (d:P)
      rw [commutatorElement_def]; group
    rw [helem, map_mul]
    have hmem_dg : ⁅(d:P), g⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (hAC (hDleA d.2)) hg
    have hone : Ψ ⟨⁅g, (d:P)⁆, hcd⟩ = 1 := by
      have hdg : Ψ (⟨⁅(d:P), g⁆, hmem_dg⟩ : ↥(⁅C, C⁆)) = 1 :=
        (hΨker _).mpr (hcommDC (Subgroup.commutator_mem_commutator d.2 hg))
      have heq2 : (⟨⁅g, (d:P)⁆, hcd⟩ : ↥(⁅C, C⁆))
          = (⟨⁅(d:P), g⁆, hmem_dg⟩ : ↥(⁅C, C⁆))⁻¹ := by
        refine Subtype.ext ?_
        show ⁅g, (d:P)⁆ = ⁅(d:P), g⁆⁻¹
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [heq2, map_inv, hdg, inv_one]
    rw [hone, one_mul]
  -- ## `Ψ (⁅·,·⁆)` depends only on `Φ₂` of the arguments
  have hwd1 : ∀ (x x' z : ↥C), Φ2 x = Φ2 x' →
      Ψ ⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ =
      Ψ ⟨⁅(x':P), (z:P)⁆, Subgroup.commutator_mem_commutator x'.2 z.2⟩ := by
    intro x x' z hxx'
    have hmem : ((x:P) * (x':P)⁻¹) ∈ A := by
      have hk : Φ2 (x * x'⁻¹) = 1 := by rw [map_mul, map_inv, hxx', mul_inv_cancel]
      exact (hkerΦ2 (x * x'⁻¹)).mp hk
    have haC : ((x:P) * (x':P)⁻¹) ∈ C := hAC hmem
    have hxD : ⁅(x':P), (z:P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator x'.2 z.2
    have haD : ⁅((x:P) * (x':P)⁻¹), (z:P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator haC z.2
    have hconjD : ((x:P) * (x':P)⁻¹) * ⁅(x':P), (z:P)⁆ * ((x:P) * (x':P)⁻¹)⁻¹ ∈ ⁅C, C⁆ :=
      hDvN.conj_mem _ hxD ((x:P) * (x':P)⁻¹)
    have helem : (⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ : ↥(⁅C, C⁆))
        = ⟨((x:P) * (x':P)⁻¹) * ⁅(x':P), (z:P)⁆ * ((x:P) * (x':P)⁻¹)⁻¹, hconjD⟩
          * ⟨⁅((x:P) * (x':P)⁻¹), (z:P)⁆, haD⟩ := by
      refine Subtype.ext ?_
      show ⁅(x:P), (z:P)⁆
        = ((x:P) * (x':P)⁻¹) * ⁅(x':P), (z:P)⁆ * ((x:P) * (x':P)⁻¹)⁻¹
          * ⁅((x:P) * (x':P)⁻¹), (z:P)⁆
      conv_lhs => rw [show (x:P) = ((x:P) * (x':P)⁻¹) * (x':P) from by group]
      rw [commutatorElement_mul_left_eq_conj_mul]
    rw [helem, map_mul]
    rw [hΨconj ((x:P) * (x':P)⁻¹) haC ⟨⁅(x':P), (z:P)⁆, hxD⟩]
    have hone : Ψ ⟨⁅((x:P) * (x':P)⁻¹), (z:P)⁆, haD⟩ = 1 :=
      (hΨker _).mpr (hcommAC (Subgroup.commutator_mem_commutator hmem z.2))
    rw [hone, mul_one]
  have hwd2 : ∀ (x z z' : ↥C), Φ2 z = Φ2 z' →
      Ψ ⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ =
      Ψ ⟨⁅(x:P), (z':P)⁆, Subgroup.commutator_mem_commutator x.2 z'.2⟩ := by
    intro x z z' hzz'
    have hmem : ((z:P) * (z':P)⁻¹) ∈ A := by
      have hk : Φ2 (z * z'⁻¹) = 1 := by rw [map_mul, map_inv, hzz', mul_inv_cancel]
      exact (hkerΦ2 (z * z'⁻¹)).mp hk
    have hbC : ((z:P) * (z':P)⁻¹) ∈ C := hAC hmem
    have hxb : ⁅(x:P), ((z:P) * (z':P)⁻¹)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator x.2 hbC
    have hzD : ⁅(x:P), (z':P)⁆ ∈ ⁅C, C⁆ := Subgroup.commutator_mem_commutator x.2 z'.2
    have hconjD : ((z:P) * (z':P)⁻¹) * ⁅(x:P), (z':P)⁆ * ((z:P) * (z':P)⁻¹)⁻¹ ∈ ⁅C, C⁆ :=
      hDvN.conj_mem _ hzD ((z:P) * (z':P)⁻¹)
    have helem : (⟨⁅(x:P), (z:P)⁆, Subgroup.commutator_mem_commutator x.2 z.2⟩ : ↥(⁅C, C⁆))
        = ⟨⁅(x:P), ((z:P) * (z':P)⁻¹)⁆, hxb⟩
          * ⟨((z:P) * (z':P)⁻¹) * ⁅(x:P), (z':P)⁆ * ((z:P) * (z':P)⁻¹)⁻¹, hconjD⟩ := by
      refine Subtype.ext ?_
      show ⁅(x:P), (z:P)⁆
        = ⁅(x:P), ((z:P) * (z':P)⁻¹)⁆
          * (((z:P) * (z':P)⁻¹) * ⁅(x:P), (z':P)⁆ * ((z:P) * (z':P)⁻¹)⁻¹)
      conv_lhs => rw [show (z:P) = ((z:P) * (z':P)⁻¹) * (z':P) from by group]
      rw [commutatorElement_mul_right_eq_mul_conj]
      group
    rw [helem, map_mul]
    rw [hΨconj ((z:P) * (z':P)⁻¹) hbC ⟨⁅(x:P), (z':P)⁆, hzD⟩]
    have hmemC : ⁅((z:P) * (z':P)⁻¹), (x:P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (hAC hmem) x.2
    have hACp : ⁅((z:P) * (z':P)⁻¹), (x:P)⁆ ∈ Work.Higman.powSub ⁅C, C⁆ 2 :=
      hcommAC (Subgroup.commutator_mem_commutator hmem x.2)
    have hone : Ψ ⟨⁅(x:P), ((z:P) * (z':P)⁻¹)⁆, hxb⟩ = 1 := by
      have heq2 : (⟨⁅(x:P), ((z:P) * (z':P)⁻¹)⁆, hxb⟩ : ↥(⁅C, C⁆))
          = (⟨⁅((z:P) * (z':P)⁻¹), (x:P)⁆, hmemC⟩ : ↥(⁅C, C⁆))⁻¹ := by
        refine Subtype.ext ?_
        show ⁅(x:P), ((z:P) * (z':P)⁻¹)⁆ = ⁅((z:P) * (z':P)⁻¹), (x:P)⁆⁻¹
        rw [commutatorElement_def, commutatorElement_def]; group
      rw [heq2, map_inv,
        show Ψ (⟨⁅((z:P) * (z':P)⁻¹), (x:P)⁆, hmemC⟩ : ↥(⁅C, C⁆)) = 1 from
          (hΨker _).mpr hACp, inv_one]
    rw [hone, one_mul]
  -- ## the pairing `c : W → W → W`
  let c : ↥W → ↥W → ↥W := fun w w' =>
    Ψ ⟨⁅((lift w : ↥C) : P), ((lift w' : ↥C) : P)⁆,
      Subgroup.commutator_mem_commutator (lift w).2 (lift w').2⟩
  have hc_apply : ∀ w w' : ↥W, c w w' = Ψ ⟨⁅((lift w : ↥C) : P), ((lift w' : ↥C) : P)⁆,
      Subgroup.commutator_mem_commutator (lift w).2 (lift w').2⟩ := fun _ _ => rfl
  have halt : ∀ a : ↥W, c a a = 1 := by
    intro a
    rw [hc_apply]
    have h1 : (⟨⁅((lift a : ↥C) : P), ((lift a : ↥C) : P)⁆,
        Subgroup.commutator_mem_commutator (lift a).2 (lift a).2⟩ : ↥(⁅C, C⁆)) = 1 := by
      refine Subtype.ext ?_
      show ⁅((lift a : ↥C) : P), ((lift a : ↥C) : P)⁆ = 1
      simp [commutatorElement_def]
    rw [h1, map_one]
  have hmul : ∀ a b d : ↥W, c (a * b) d = c a d * c b d := by
    intro a b d
    have hlift : Φ2 (lift (a * b)) = Φ2 (lift a * lift b) := by
      rw [map_mul, lift_spec, lift_spec, lift_spec]
    have h1 := hwd1 (lift (a * b)) (lift a * lift b) (lift d) hlift
    have hD_b : ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift b).2 (lift d).2
    have hD_a : ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift a).2 (lift d).2
    have hconj_ab : ((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
        * ((lift a : ↥C) : P)⁻¹ ∈ ⁅C, C⁆ := hDvN.conj_mem _ hD_b _
    rw [hc_apply, hc_apply, hc_apply, h1]
    have helem : (⟨⁅(((lift a : ↥C) * (lift b : ↥C) : ↥C) : P), ((lift d : ↥C) : P)⁆,
          Subgroup.commutator_mem_commutator (lift a * lift b).2 (lift d).2⟩ : ↥(⁅C, C⁆))
        = (⟨((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
              * ((lift a : ↥C) : P)⁻¹, hconj_ab⟩ : ↥(⁅C, C⁆))
          * (⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_a⟩ : ↥(⁅C, C⁆)) := by
      refine Subtype.ext ?_
      show ⁅(((lift a : ↥C) * (lift b : ↥C) : ↥C) : P), ((lift d : ↥C) : P)⁆
        = ((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
            * ((lift a : ↥C) : P)⁻¹
          * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
      rw [Subgroup.coe_mul, commutatorElement_mul_left_eq_conj_mul]
    rw [helem, map_mul,
      show Ψ (⟨((lift a : ↥C) : P) * ⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆
            * ((lift a : ↥C) : P)⁻¹, hconj_ab⟩ : ↥(⁅C, C⁆))
          = Ψ (⟨⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_b⟩ : ↥(⁅C, C⁆)) from
        hΨconj ((lift a : ↥C) : P) (lift a).2
          ⟨⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_b⟩,
      mul_comm (Ψ (⟨⁅((lift b : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_b⟩ : ↥(⁅C, C⁆)))
        (Ψ (⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_a⟩ : ↥(⁅C, C⁆)))]
  have hmul' : ∀ a b d : ↥W, c a (b * d) = c a b * c a d := by
    intro a b d
    have hlift : Φ2 (lift (b * d)) = Φ2 (lift b * lift d) := by
      rw [map_mul, lift_spec, lift_spec, lift_spec]
    have h1 := hwd2 (lift a) (lift (b * d)) (lift b * lift d) hlift
    have hD_a : ⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift a).2 (lift b).2
    have hD_d : ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆ ∈ ⁅C, C⁆ :=
      Subgroup.commutator_mem_commutator (lift a).2 (lift d).2
    have hconj_bd : ((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
        * ((lift b : ↥C) : P)⁻¹ ∈ ⁅C, C⁆ := hDvN.conj_mem _ hD_d _
    rw [hc_apply, hc_apply, hc_apply, h1]
    have helem : (⟨⁅((lift a : ↥C) : P), (((lift b : ↥C) * (lift d : ↥C) : ↥C) : P)⁆,
          Subgroup.commutator_mem_commutator (lift a).2 (lift b * lift d).2⟩ : ↥(⁅C, C⁆))
        = (⟨⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆, hD_a⟩ : ↥(⁅C, C⁆))
          * (⟨((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
              * ((lift b : ↥C) : P)⁻¹, hconj_bd⟩ : ↥(⁅C, C⁆)) := by
      refine Subtype.ext ?_
      show ⁅((lift a : ↥C) : P), (((lift b : ↥C) * (lift d : ↥C) : ↥C) : P)⁆
        = ⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆
          * (((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
              * ((lift b : ↥C) : P)⁻¹)
      rw [Subgroup.coe_mul, commutatorElement_mul_right_eq_mul_conj]
      group
    rw [helem, map_mul,
      show Ψ (⟨((lift b : ↥C) : P) * ⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆
            * ((lift b : ↥C) : P)⁻¹, hconj_bd⟩ : ↥(⁅C, C⁆))
          = Ψ (⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_d⟩ : ↥(⁅C, C⁆)) from
        hΨconj ((lift b : ↥C) : P) (lift b).2
          ⟨⁅((lift a : ↥C) : P), ((lift d : ↥C) : P)⁆, hD_d⟩]
  have hxiC : ∀ (x : ↥C), h.xi (x:P) ∈ C := by
    intro x
    have hh := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom x.2
    rwa [hCinv] at hh
  let xiC : ↥C → ↥C := fun x => ⟨h.xi (x:P), hxiC x⟩
  have xiC_val : ∀ x : ↥C, ((xiC x : ↥C) : P) = h.xi (x:P) := fun x => rfl
  have hΦ2xi : ∀ x : ↥C, Φ2 (xiC x) = ξW (Φ2 x) := by
    intro x
    refine Subtype.ext ?_
    have e1 : ((Φ2 (xiC x) : ↥W) : P) = (h.xi (x:P)) ^ 2 ^ e := rfl
    have e2 : ((ξW (Φ2 x) : ↥W) : P) = h.xi ((x:P) ^ 2 ^ e) := rfl
    rw [e1, e2]
    exact hphi2_xi (x:P) x.2
  have heq : ∀ a b : ↥W, ξW (c a b) = c (ξW a) (ξW b) := by
    intro a b
    have h2 := hwd1 (lift (ξW a)) (xiC (lift a)) (lift (ξW b))
      ((lift_spec (ξW a)).trans
        ((congrArg ξW (lift_spec a)).symm.trans (hΦ2xi (lift a)).symm))
    have h3 := hwd2 (xiC (lift a)) (lift (ξW b)) (xiC (lift b))
      ((lift_spec (ξW b)).trans
        ((congrArg ξW (lift_spec b)).symm.trans (hΦ2xi (lift b)).symm))
    have hval : (⟨⁅((xiC (lift a) : ↥C) : P), ((xiC (lift b) : ↥C) : P)⁆,
          Subgroup.commutator_mem_commutator (xiC (lift a)).2 (xiC (lift b)).2⟩ : ↥(⁅C, C⁆))
        = (⟨h.xi (⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆), by
            have hh := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom
              (Subgroup.commutator_mem_commutator (lift a).2 (lift b).2)
            rwa [Subgroup.map_commutator C C (h.xi : MulAut P).toMonoidHom, hCinv] at hh⟩
            : ↥(⁅C, C⁆)) := by
      refine Subtype.ext ?_
      show ⁅((xiC (lift a) : ↥C) : P), ((xiC (lift b) : ↥C) : P)⁆
        = h.xi ⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆
      rw [xiC_val (lift a), xiC_val (lift b)]
      exact (map_commutatorElement (h.xi : MulAut P).toMonoidHom _ _).symm
    rw [hc_apply, hc_apply, h2, h3, hval,
      hPsi_xi (⟨⁅((lift a : ↥C) : P), ((lift b : ↥C) : P)⁆,
        Subgroup.commutator_mem_commutator (lift a).2 (lift b).2⟩ : ↥(⁅C, C⁆)),
      ← hc_apply]
  -- ## Gorenstein--Thompson: the pairing vanishes
  have hDab : ∀ x ∈ ⁅C, C⁆, ∀ y ∈ ⁅C, C⁆, x * y = y * x :=
    fun x hx y hy => hA.abelian x (hDleA hx) y (hDleA hy)
  have hczero : ∀ a b : ↥W, c a b = 1 :=
    equivariant_bihom_trivial hWtwo ξW htransW c hmul hmul' halt heq
  have hΨtriv : ∀ x y : ↥C,
      Ψ ⟨⁅(x:P), (y:P)⁆, Subgroup.commutator_mem_commutator x.2 y.2⟩ = 1 := by
    intro x y
    have h0 := hczero (Φ2 x) (Φ2 y)
    rw [hc_apply] at h0
    have h1 := hwd1 (lift (Φ2 x)) x (lift (Φ2 y)) (by rw [lift_spec])
    have h2' := hwd2 x (lift (Φ2 y)) y (by rw [lift_spec])
    exact (h1.trans h2').symm.trans h0
  have hDsub : ⁅C, C⁆ ≤ Work.Higman.powSub ⁅C, C⁆ 2 := by
    rw [Subgroup.commutator_def, Subgroup.closure_le]
    rintro v ⟨x, hx, y, hy, rfl⟩
    show ⁅x, y⁆ ∈ Work.Higman.powSub ⁅C, C⁆ 2
    exact (hΨker _).mp (hΨtriv ⟨x, hx⟩ ⟨y, hy⟩)
  have hDpow : ⁅C, C⁆ = Work.Higman.powSub ⁅C, C⁆ 2 :=
    le_antisymm hDsub (powSub_le (by norm_num))
  have hpow : ∀ k : ℕ, Work.Higman.powSub ⁅C, C⁆ (2 ^ k) = ⁅C, C⁆ := by
    intro k
    induction k with
    | zero => rw [pow_zero, powSub_one_eq]
    | succ k ih =>
        rw [pow_succ, ← powSub_powSub hDab (2 ^ k) 2, ih]
        exact hDpow.symm
  have hbotpow : Work.Higman.powSub ⁅C, C⁆ (2 ^ e) = ⊥ :=
    le_bot_iff.mp ((powSub_mono hDleA).trans
      (le_of_eq (powSub_eq_bot_of_exp hA.abelian le_rfl he1)))
  exact hDne (by rw [← hpow e, hbotpow])

end Work.Higman
